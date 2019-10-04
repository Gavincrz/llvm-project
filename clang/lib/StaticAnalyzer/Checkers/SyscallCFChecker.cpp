//== SyscallCFChecker.cpp ----------------------------------- -*- C++ -*--=//



#include "Taint.h"
#include "clang/StaticAnalyzer/Checkers/BuiltinCheckerRegistration.h"
#include "clang/AST/Attr.h"
#include "clang/Basic/Builtins.h"
#include "clang/StaticAnalyzer/Core/BugReporter/BugType.h"
#include "clang/StaticAnalyzer/Core/Checker.h"
#include "clang/StaticAnalyzer/Core/CheckerManager.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/CheckerContext.h"
#include "clang/StaticAnalyzer/Core/PathSensitive/ProgramStateTrait.h"
#include "clang/Analysis/Analyses/Dominators.h"
#include <climits>
#include <initializer_list>
#include <utility>

using namespace clang;
using namespace ento;
using namespace taint;

typedef llvm::SmallVector<CFGBlock *, 4> CFGBlockVector;
typedef std::pair<const LocationContext*, SVal> LCSValPair;
REGISTER_MAP_WITH_PROGRAMSTATE(ExprSValMap, const Expr*, LCSValPair)


namespace {
    class SyscallCFChecker
            : public Checker<check::PostStmt<CallExpr>, check::PreStmt<CallExpr>,
                    check::EndFunction, check::BranchCondition> {
    public:
    static void *getTag() {
        static int Tag;
        return &Tag;
    }

    void checkPostStmt(const CallExpr *CE, CheckerContext &C) const;

    void checkPreStmt(const CallExpr *CE, CheckerContext &C) const;

    void printState(raw_ostream &Out, ProgramStateRef State,
                    const char *NL, const char *Sep) const override;

    void checkBranchCondition(const Stmt *Condition, CheckerContext &C) const;

    void checkEndFunction(const ReturnStmt *RS, CheckerContext &C) const;

    private:
    static const unsigned InvalidArgIndex = UINT_MAX;
    /// Denotes the return vale.
    static const unsigned ReturnValueIndex = UINT_MAX - 1;

    mutable std::unique_ptr<BugType> BT;
    void initBugType() const {
        if (!BT)
            BT.reset(new BugType(this, "Control flow to sensitive function is tainted", "Tainted Control Flow"));
    }


    static const char MsgControlFlowTainted[];

    bool generateReportIfCFTainted(CheckerContext &C, CFG *cfg, CFGBlock* cfgBlock) const;

    /// Catch taint related bugs. Check if tainted data is passed to a
    /// system call etc.
    bool checkPre(const CallExpr *CE, CheckerContext &C) const;

    /// Add taint sources on a pre-visit.
    void addSourcesPre(const CallExpr *CE, CheckerContext &C) const;

    /// Propagate taint generated at pre-visit.
    bool propagateFromPre(const CallExpr *CE, CheckerContext &C) const;

    /// Check if the region the expression evaluates to is the standard input,
    /// and thus, is tainted.
    static bool isStdin(const Expr *E, CheckerContext &C);

    /// Given a pointer argument, return the value it points to.
    static Optional<SVal> getPointedToSVal(CheckerContext &C, const Expr *Arg);

/*
    /// Generate a report if the expression is tainted or points to tainted data.
    bool generateReportIfTainted(const Expr *E, const char Msg[],
                                 CheckerContext &C) const;
*/

    using ArgVector = SmallVector<unsigned, 2>;

    /// A struct used to specify taint propagation rules for a function.
    ///
    /// If any of the possible taint source arguments is tainted, all of the
    /// destination arguments should also be tainted. Use InvalidArgIndex in the
    /// src list to specify that all of the arguments can introduce taint. Use
    /// InvalidArgIndex in the dst arguments to signify that all the non-const
    /// pointer and reference arguments might be tainted on return. If
    /// ReturnValueIndex is added to the dst list, the return value will be
    /// tainted.
    struct TaintPropagationRule {
        enum class VariadicType { None, Src, Dst };

        using PropagationFuncType = bool (*)(bool IsTainted, const CallExpr *,
                                             CheckerContext &C);

        /// List of arguments which can be taint sources and should be checked.
        ArgVector SrcArgs;
        /// List of arguments which should be tainted on function return.
        ArgVector DstArgs;
        /// Index for the first variadic parameter if exist.
        unsigned VariadicIndex;
        /// Show when a function has variadic parameters. If it has, it marks all
        /// of them as source or destination.
        VariadicType VarType;
        /// Special function for tainted source determination. If defined, it can
        /// override the default behavior.
        PropagationFuncType PropagationFunc;

        TaintPropagationRule()
                : VariadicIndex(InvalidArgIndex), VarType(VariadicType::None),
                  PropagationFunc(nullptr) {}

        TaintPropagationRule(std::initializer_list<unsigned> &&Src,
                             std::initializer_list<unsigned> &&Dst,
                             VariadicType Var = VariadicType::None,
                             unsigned VarIndex = InvalidArgIndex,
                             PropagationFuncType Func = nullptr)
                : SrcArgs(std::move(Src)), DstArgs(std::move(Dst)),
                  VariadicIndex(VarIndex), VarType(Var), PropagationFunc(Func) {}

        /// Get the propagation rule for a given function.
        static TaintPropagationRule
        getTaintPropagationRule(const FunctionDecl *FDecl, StringRef Name,
                                CheckerContext &C);

        void addSrcArg(unsigned A) { SrcArgs.push_back(A); }
        void addDstArg(unsigned A) { DstArgs.push_back(A); }

        bool isNull() const {
            return SrcArgs.empty() && DstArgs.empty() &&
                   VariadicType::None == VarType;
        }

        bool isDestinationArgument(unsigned ArgNum) const {
            return (llvm::find(DstArgs, ArgNum) != DstArgs.end());
        }

        static bool isTaintedOrPointsToTainted(const Expr *E, ProgramStateRef State,
                                               CheckerContext &C) {
            if (isTainted(State, E, C.getLocationContext()) || isStdin(E, C))
                return true;

            if (!E->getType().getTypePtr()->isPointerType())
                return false;

            Optional<SVal> V = getPointedToSVal(C, E);
            return (V && isTainted(State, *V));
        }

        /// Pre-process a function which propagates taint according to the
        /// taint rule.
        ProgramStateRef process(const CallExpr *CE, CheckerContext &C) const;
    };
};

const unsigned SyscallCFChecker::ReturnValueIndex;
const unsigned SyscallCFChecker::InvalidArgIndex;


const char SyscallCFChecker::MsgControlFlowTainted[] =
        "Control flow to a sensitive function is tainted";


} // end of anonymous namespace

/// A set which is used to pass information from call pre-visit instruction
/// to the call post-visit. The values are unsigned integers, which are either
/// ReturnValueIndex, or indexes of the pointer/reference argument, which
/// points to data, which should be tainted on return.
REGISTER_SET_WITH_PROGRAMSTATE(TaintArgsOnPostVisit, unsigned)

SyscallCFChecker::TaintPropagationRule
SyscallCFChecker::TaintPropagationRule::getTaintPropagationRule(
        const FunctionDecl *FDecl, StringRef Name, CheckerContext &C) {
    // value as tainted even if it's just a pointer, pointing to tainted data.
    // Check for exact name match for functions without builtin substitutes.
    // Mark syscall return values as tainted (only the metadata, no payloads)
    TaintPropagationRule Rule =
            llvm::StringSwitch<TaintPropagationRule>(Name)
                    .Case("socket", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("pread", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("read", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("epoll_wait", TaintPropagationRule({}, {1, ReturnValueIndex}))
                    .Case("open", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("write", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("stat", TaintPropagationRule({}, {1, ReturnValueIndex}))
                    .Case("fstat", TaintPropagationRule({}, {1, ReturnValueIndex}))
                    .Case("poll", TaintPropagationRule({}, {0, ReturnValueIndex}))
                    .Case("lseek", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("pwrite", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("readv", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("writev", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("select", TaintPropagationRule({}, {1, 2, 3, ReturnValueIndex}))
                    .Case("nanosleep", TaintPropagationRule({}, {1, ReturnValueIndex}))
                    .Case("getpid", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("sendfile", TaintPropagationRule({}, {2, ReturnValueIndex}))
                    .Case("accept", TaintPropagationRule({}, {1, 2, ReturnValueIndex}))
                    .Case("sendto", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("recvfrom", TaintPropagationRule({}, {4, 5, ReturnValueIndex}))
                    .Case("sendmsg", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("recvmsg", TaintPropagationRule({}, {1, ReturnValueIndex}))
                    .Case("getsockname", TaintPropagationRule({}, {1, 2, ReturnValueIndex}))
                    .Case("getpeername", TaintPropagationRule({}, {1, 2, ReturnValueIndex}))
                    .Case("socketpair", TaintPropagationRule({}, {3, ReturnValueIndex}))
                    .Case("getsockopt", TaintPropagationRule({}, {3, 4, ReturnValueIndex}))
                    .Case("getdents", TaintPropagationRule({}, {1, ReturnValueIndex}))
                    .Case("readlink", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("gettimeofday", TaintPropagationRule({}, {0, 1, ReturnValueIndex}))
                    .Case("getrlimit", TaintPropagationRule({}, {0, 1, ReturnValueIndex}))
                    .Case("getrusage", TaintPropagationRule({}, {1, ReturnValueIndex}))
                    .Case("sysinfo", TaintPropagationRule({}, {0, ReturnValueIndex}))
                    .Case("times", TaintPropagationRule({}, {0, ReturnValueIndex}))
                    .Case("getuid", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("getgid", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("getegid", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("geteuid", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("getppid", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("getpgrp", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("getresuid", TaintPropagationRule({}, {0, 1, 2, ReturnValueIndex}))
                    .Case("getresgid", TaintPropagationRule({}, {0, 1, 2, ReturnValueIndex}))
                    .Case("getpgid", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("getsid", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("ustat", TaintPropagationRule({}, {1, ReturnValueIndex}))
                    .Case("statfs", TaintPropagationRule({}, {1, ReturnValueIndex}))
                    .Case("fstatfs", TaintPropagationRule({}, {1, ReturnValueIndex}))
                    .Case("getpriority", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("sched_getparam", TaintPropagationRule({}, {1, ReturnValueIndex}))
                    .Case("sched_getscheduler", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("sched_get_priority_max", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("sched_get_priority_min", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("sched_rr_get_interval", TaintPropagationRule({}, {1, ReturnValueIndex}))
                    .Case("getpmsg", TaintPropagationRule({}, {1, 2, 3, 4, ReturnValueIndex}))
                    .Case("gettid", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("getxattr", TaintPropagationRule({}, {2, ReturnValueIndex}))
                    .Case("lgetxattr", TaintPropagationRule({}, {2, ReturnValueIndex}))
                    .Case("fgetxattr", TaintPropagationRule({}, {2, ReturnValueIndex}))
                    .Case("listxattr", TaintPropagationRule({}, {1, ReturnValueIndex}))
                    .Case("llistxattr", TaintPropagationRule({}, {1, ReturnValueIndex}))
                    .Case("flistxattr", TaintPropagationRule({}, {1, ReturnValueIndex}))
                    .Case("time", TaintPropagationRule({}, {0, ReturnValueIndex}))
                    .Case("sched_getaffinity", TaintPropagationRule({}, {2, ReturnValueIndex}))
                    .Case("timer_create", TaintPropagationRule({}, {1, 2, ReturnValueIndex}))
                    .Case("timer_settime", TaintPropagationRule({}, {3, ReturnValueIndex}))
                    .Case("timer_gettime", TaintPropagationRule({}, {1, ReturnValueIndex}))
                    .Case("timer_getoverrun", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("clock_gettime", TaintPropagationRule({}, {1, ReturnValueIndex}))
                    .Case("clock_getres", TaintPropagationRule({}, {1, ReturnValueIndex}))
                    .Case("clock_nanosleep", TaintPropagationRule({}, {3, ReturnValueIndex}))
                    .Case("mq_open", TaintPropagationRule({}, {3, ReturnValueIndex}))
                    .Case("mq_timedreceive", TaintPropagationRule({}, {1, 3, 4, ReturnValueIndex}))
                    .Case("inotify_add_watch", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("fstatat", TaintPropagationRule({}, {2, ReturnValueIndex}))
                    .Case("readlinkat", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("pselect", TaintPropagationRule({}, {1, 2, 3, ReturnValueIndex}))
                    .Case("ppoll", TaintPropagationRule({}, {0, ReturnValueIndex}))
                    .Case("splice", TaintPropagationRule({}, {1, 3, ReturnValueIndex}))
                    .Case("tee", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("vmsplice", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("epoll_pwait", TaintPropagationRule({}, {1, ReturnValueIndex}))
                    .Case("timerfd_settime", TaintPropagationRule({}, {2, ReturnValueIndex}))
                    .Case("timerfd_gettime", TaintPropagationRule({}, {1, ReturnValueIndex}))
                    .Case("accept4", TaintPropagationRule({}, {1, 2, ReturnValueIndex}))
                    .Case("preadv", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("pwritev", TaintPropagationRule({}, {ReturnValueIndex}))
                    .Case("recvmmsg", TaintPropagationRule({}, {1, 4, ReturnValueIndex}))
                    .Case("prlimit", TaintPropagationRule({}, {3, ReturnValueIndex}))
                    .Case("name_to_handle_at", TaintPropagationRule({}, {2, 3, ReturnValueIndex}))
                    .Case("sendmmsg", TaintPropagationRule({}, {1, ReturnValueIndex}))
                    .Default(TaintPropagationRule());

    if (!Rule.isNull())
        return Rule;

    // Check if it's one of the memory setting/copying functions.
    // This check is specialized but faster then calling isCLibraryFunction.
    unsigned BId = 0;
    if ((BId = FDecl->getMemoryFunctionKind()))
        switch (BId) {
            case Builtin::BImemcpy:
            case Builtin::BImemmove:
            case Builtin::BIstrncpy:
            case Builtin::BIstrncat:
                return TaintPropagationRule({1, 2}, {0, ReturnValueIndex});
            case Builtin::BIstrlcpy:
            case Builtin::BIstrlcat:
                return TaintPropagationRule({1, 2}, {0});
            case Builtin::BIstrndup:
                return TaintPropagationRule({0, 1}, {ReturnValueIndex});

            default:
                break;
        };

    // Process all other functions which could be defined as builtins.
    if (Rule.isNull()) {
        if (C.isCLibraryFunction(FDecl, "snprintf"))
            return TaintPropagationRule({1}, {0, ReturnValueIndex}, VariadicType::Src,
                                        3);
        else if (C.isCLibraryFunction(FDecl, "sprintf"))
            return TaintPropagationRule({}, {0, ReturnValueIndex}, VariadicType::Src,
                                        2);
        else if (C.isCLibraryFunction(FDecl, "strcpy") ||
                 C.isCLibraryFunction(FDecl, "stpcpy") ||
                 C.isCLibraryFunction(FDecl, "strcat"))
            return TaintPropagationRule({1}, {0, ReturnValueIndex});
        else if (C.isCLibraryFunction(FDecl, "bcopy"))
            return TaintPropagationRule({0, 2}, {1});
        else if (C.isCLibraryFunction(FDecl, "strdup") ||
                 C.isCLibraryFunction(FDecl, "strdupa"))
            return TaintPropagationRule({0}, {ReturnValueIndex});
        else if (C.isCLibraryFunction(FDecl, "wcsdup"))
            return TaintPropagationRule({0}, {ReturnValueIndex});
    }

    // Skipping the following functions, since they might be used for cleansing
    // or smart memory copy:
    // - memccpy - copying until hitting a special character.

    return TaintPropagationRule();
}

void SyscallCFChecker::checkPreStmt(const CallExpr *CE,
                                       CheckerContext &C) const {
    // Check for taintedness related errors first: system call, uncontrolled
    // format string, tainted buffer size.
    if (checkPre(CE, C))
        return;

    // Marks the function's arguments and/or return value tainted if it present in
    // the list.
    addSourcesPre(CE, C);
}


void SyscallCFChecker::checkPostStmt(const CallExpr *CE,
                                        CheckerContext &C) const {
    // Set the marked values as tainted. The return value only accessible from
    // checkPostStmt.
    propagateFromPre(CE, C);
}

void SyscallCFChecker::checkBranchCondition(const Stmt *Condition,
        CheckerContext &C) const {

    ProgramStateRef State = C.getState();
    const LocationContext* LC =  C.getLocationContext();
    const Expr *expr = cast<Expr>(Condition);

    SVal Val = State->getSVal(expr ,LC);

    LCSValPair value = std::make_pair(LC, Val);
    State = State->set<ExprSValMap>(expr, value);
    C.addTransition(State);
}


void SyscallCFChecker::checkEndFunction(const ReturnStmt *RS,
        CheckerContext &C) const {

    ProgramStateRef State = C.getState();
    const LocationContext* LC =  C.getLocationContext();

    ExprSValMapTy Map = State->get<ExprSValMap>();

    if (Map.isEmpty()) {
        return;
    }

    for (auto &i: Map) {
        const LocationContext* storedLC = i.second.first;
        if (LC == storedLC) {
            State = State->remove<ExprSValMap>(i.first);
        }
    }

    C.addTransition(State);
}



void SyscallCFChecker::printState(raw_ostream &Out, ProgramStateRef State,
                                     const char *NL, const char *Sep) const {
    printTaint(State, Out, NL, Sep);
}

void SyscallCFChecker::addSourcesPre(const CallExpr *CE,
                                        CheckerContext &C) const {
    ProgramStateRef State = nullptr;
    const FunctionDecl *FDecl = C.getCalleeDecl(CE);
    if (!FDecl || FDecl->getKind() != Decl::Function)
        return;

    StringRef Name = C.getCalleeName(FDecl);
    if (Name.empty())
        return;

    // First, try generating a propagation rule for this function.
    TaintPropagationRule Rule =
            TaintPropagationRule::getTaintPropagationRule(FDecl, Name, C);
    if (!Rule.isNull()) {
        State = Rule.process(CE, C);
        if (!State)
            return;
        C.addTransition(State);
        return;
    }

    if (!State)
        return;
    C.addTransition(State);
}

bool SyscallCFChecker::propagateFromPre(const CallExpr *CE,
                                           CheckerContext &C) const {
    ProgramStateRef State = C.getState();

    // Depending on what was tainted at pre-visit, we determined a set of
    // arguments which should be tainted after the function returns. These are
    // stored in the state as TaintArgsOnPostVisit set.
    TaintArgsOnPostVisitTy TaintArgs = State->get<TaintArgsOnPostVisit>();
    if (TaintArgs.isEmpty())
        return false;

    for (unsigned ArgNum : TaintArgs) {
        // Special handling for the tainted return value.
        if (ArgNum == ReturnValueIndex) {
            State = addTaint(State, CE, C.getLocationContext());
            continue;
        }

        // The arguments are pointer arguments. The data they are pointing at is
        // tainted after the call.
        if (CE->getNumArgs() < (ArgNum + 1))
            return false;
        const Expr *Arg = CE->getArg(ArgNum);
        Optional<SVal> V = getPointedToSVal(C, Arg);
        if (V)
            State = addTaint(State, *V);
    }

    // Clear up the taint info from the state.
    State = State->remove<TaintArgsOnPostVisit>();

    if (State != C.getState()) {
        C.addTransition(State);
        return true;
    }
    return false;
}

bool SyscallCFChecker::generateReportIfCFTainted(CheckerContext &C, CFG *cfg, CFGBlock* cfgBlock) const
{
    ProgramStateRef State = C.getState();
    ControlDependencyCalculator Control(cfg);
    CFGBlockVector BLKVector = Control.getControlDependencies(cfgBlock);
    if (BLKVector.empty()) {
        return false;
    }

    for (CFGBlockVector::iterator I = BLKVector.begin(), E = BLKVector.end();
         I != E; ++I) {
        const Expr* lastCondition = (*I)->getLastCondition();
        const LCSValPair *value = State->get<ExprSValMap>(lastCondition);

        if (value == NULL) {
            llvm::errs() << "excuse me ?" << "\n";
            continue;
        }

        SVal Val = value->second;
        if (isTainted(State, Val)) {
            // Generate diagnostic.
            if (ExplodedNode *N = C.generateNonFatalErrorNode()) {
                initBugType();
                auto report = llvm::make_unique<BugReport>(*BT, MsgControlFlowTainted, N);
                report->addRange(lastCondition->getSourceRange());
                report->addVisitor(llvm::make_unique<TaintBugVisitor>(Val));
                C.emitReport(std::move(report));
                return true;
            }
        }
    }
    return false;

}

bool SyscallCFChecker::checkPre(const CallExpr *CE,
                                   CheckerContext &C) const {

    ProgramStateRef State = C.getState();

    // check if any of the branch condition reach to this point is tainted
    const FunctionDecl *FDecl = C.getCalleeDecl(CE);
    if (!FDecl || FDecl->getKind() != Decl::Function)
        return false;

    // TODO: For not only mark any write function as sensitive
    StringRef Name = C.getCalleeName(FDecl);
    if (!Name.equals("write"))
        return false;

    // check if the second argument is a string literal, if so ignore
    Expr *StrArg = const_cast<Expr*>(CE->getArg(1)->IgnoreParenCasts());
    StringLiteral *Literal = dyn_cast<StringLiteral>(StrArg);
    if (Literal && Literal->isAscii()){
        return false;
    }

    // get all the denpended branches
    const LocationContext* LC = C.getLocationContext();
    const StackFrameContext *SC = LC->getStackFrame();

    CFG *cfg = const_cast<CFG *>(LC->getCFG());
    CFGBlock* cfgBlock = const_cast<CFGBlock*>(C.getCFGBlock());

    // recursively check parent dependency
    bool ret = generateReportIfCFTainted(C, cfg, cfgBlock);
    while (!ret && LC->getParent() != NULL) {
        cfgBlock = const_cast<CFGBlock*>(SC->getCallSiteBlock());
        LC = LC->getParent();
        cfg = const_cast<CFG *>(LC->getCFG());
        ret = generateReportIfCFTainted(C, cfg, cfgBlock);
        SC = LC->getStackFrame();
    }

    return ret;

}

Optional<SVal> SyscallCFChecker::getPointedToSVal(CheckerContext &C,
                                                     const Expr *Arg) {
    ProgramStateRef State = C.getState();
    SVal AddrVal = C.getSVal(Arg->IgnoreParens());
    if (AddrVal.isUnknownOrUndef())
        return None;

    Optional<Loc> AddrLoc = AddrVal.getAs<Loc>();
    if (!AddrLoc)
        return None;

    QualType ArgTy = Arg->getType().getCanonicalType();
    if (!ArgTy->isPointerType())
        return None;

    QualType ValTy = ArgTy->getPointeeType();

    // Do not dereference void pointers. Treat them as byte pointers instead.
    // FIXME: we might want to consider more than just the first byte.
    if (ValTy->isVoidType())
        ValTy = C.getASTContext().CharTy;

    return State->getSVal(*AddrLoc, ValTy);
}

ProgramStateRef
SyscallCFChecker::TaintPropagationRule::process(const CallExpr *CE,
                                                   CheckerContext &C) const {
    ProgramStateRef State = C.getState();

    // Check for taint in arguments.
    bool IsTainted = true;
    for (unsigned ArgNum : SrcArgs) {
        if (ArgNum >= CE->getNumArgs())
            return State;
        if ((IsTainted = isTaintedOrPointsToTainted(CE->getArg(ArgNum), State, C)))
            break;
    }

    // Check for taint in variadic arguments.
    if (!IsTainted && VariadicType::Src == VarType) {
        // Check if any of the arguments is tainted
        for (unsigned int i = VariadicIndex; i < CE->getNumArgs(); ++i) {
            if ((IsTainted = isTaintedOrPointsToTainted(CE->getArg(i), State, C)))
                break;
        }
    }

    if (PropagationFunc)
        IsTainted = PropagationFunc(IsTainted, CE, C);

    if (!IsTainted)
        return State;

    // Mark the arguments which should be tainted after the function returns.
    for (unsigned ArgNum : DstArgs) {
        // Should mark the return value?
        if (ArgNum == ReturnValueIndex) {
            State = State->add<TaintArgsOnPostVisit>(ReturnValueIndex);
            continue;
        }

        // Mark the given argument.
        assert(ArgNum < CE->getNumArgs());
        State = State->add<TaintArgsOnPostVisit>(ArgNum);
    }

    // Mark all variadic arguments tainted if present.
    if (VariadicType::Dst == VarType) {
        // For all pointer and references that were passed in:
        //   If they are not pointing to const data, mark data as tainted.
        //   TODO: So far we are just going one level down; ideally we'd need to
        //         recurse here.
        for (unsigned int i = VariadicIndex; i < CE->getNumArgs(); ++i) {
            const Expr *Arg = CE->getArg(i);
            // Process pointer argument.
            const Type *ArgTy = Arg->getType().getTypePtr();
            QualType PType = ArgTy->getPointeeType();
            if ((!PType.isNull() && !PType.isConstQualified()) ||
                (ArgTy->isReferenceType() && !Arg->getType().isConstQualified()))
                State = State->add<TaintArgsOnPostVisit>(i);
        }
    }

    return State;
}


bool SyscallCFChecker::isStdin(const Expr *E, CheckerContext &C) {
    ProgramStateRef State = C.getState();
    SVal Val = C.getSVal(E);

    // stdin is a pointer, so it would be a region.
    const MemRegion *MemReg = Val.getAsRegion();

    // The region should be symbolic, we do not know it's value.
    const SymbolicRegion *SymReg = dyn_cast_or_null<SymbolicRegion>(MemReg);
    if (!SymReg)
        return false;

    // Get it's symbol and find the declaration region it's pointing to.
    const SymbolRegionValue *Sm =
            dyn_cast<SymbolRegionValue>(SymReg->getSymbol());
    if (!Sm)
        return false;
    const DeclRegion *DeclReg = dyn_cast_or_null<DeclRegion>(Sm->getRegion());
    if (!DeclReg)
        return false;

    // This region corresponds to a declaration, find out if it's a global/extern
    // variable named stdin with the proper type.
    if (const auto *D = dyn_cast_or_null<VarDecl>(DeclReg->getDecl())) {
        D = D->getCanonicalDecl();
        if ((D->getName().find("stdin") != StringRef::npos) && D->isExternC()) {
            const auto *PtrTy = dyn_cast<PointerType>(D->getType().getTypePtr());
            if (PtrTy && PtrTy->getPointeeType().getCanonicalType() ==
                         C.getASTContext().getFILEType().getCanonicalType())
                return true;
        }
    }
    return false;
}



void ento::registerSyscallCFChecker(CheckerManager &mgr) {
    mgr.registerChecker<SyscallCFChecker>();
}

bool ento::shouldRegisterSyscallCFChecker(const LangOptions &LO) {
    return true;
}
