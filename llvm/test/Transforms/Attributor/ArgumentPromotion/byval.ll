; NOTE: Assertions have been autogenerated by utils/update_test_checks.py UTC_ARGS: --function-signature --scrub-attributes
; RUN: opt -S -passes='attributor' -aa-pipeline='basic-aa' -attributor-disable=false -attributor-max-iterations-verify -attributor-max-iterations=2 < %s | FileCheck %s

target datalayout = "E-p:64:64:64-a0:0:8-f32:32:32-f64:64:64-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-v64:64:64-v128:128:128"

%struct.ss = type { i32, i64 }

define internal i32 @f(%struct.ss* byval  %b) nounwind  {
; CHECK-LABEL: define {{[^@]+}}@f
; CHECK-SAME: (i32 [[TMP0:%.*]], i64 [[TMP1:%.*]])
; CHECK-NEXT:  entry:
; CHECK-NEXT:    [[B_PRIV:%.*]] = alloca [[STRUCT_SS:%.*]]
; CHECK-NEXT:    [[B_PRIV_CAST:%.*]] = bitcast %struct.ss* [[B_PRIV]] to i32*
; CHECK-NEXT:    store i32 [[TMP0]], i32* [[B_PRIV_CAST]]
; CHECK-NEXT:    [[B_PRIV_0_1:%.*]] = getelementptr [[STRUCT_SS]], %struct.ss* [[B_PRIV]], i32 0, i32 1
; CHECK-NEXT:    store i64 [[TMP1]], i64* [[B_PRIV_0_1]]
; CHECK-NEXT:    [[TMP:%.*]] = getelementptr [[STRUCT_SS]], %struct.ss* [[B_PRIV]], i32 0, i32 0
; CHECK-NEXT:    [[TMP1:%.*]] = load i32, i32* [[TMP]], align 8
; CHECK-NEXT:    [[TMP2:%.*]] = add i32 [[TMP1]], 1
; CHECK-NEXT:    store i32 [[TMP2]], i32* [[TMP]], align 8
; CHECK-NEXT:    ret i32 [[TMP1]]
;
entry:
  %tmp = getelementptr %struct.ss, %struct.ss* %b, i32 0, i32 0
  %tmp1 = load i32, i32* %tmp, align 4
  %tmp2 = add i32 %tmp1, 1
  store i32 %tmp2, i32* %tmp, align 4
  ret i32 %tmp1
}


define internal i32 @g(%struct.ss* byval align 32 %b) nounwind {
; CHECK-LABEL: define {{[^@]+}}@g
; CHECK-SAME: (i32 [[TMP0:%.*]], i64 [[TMP1:%.*]])
; CHECK-NEXT:  entry:
; CHECK-NEXT:    [[B_PRIV:%.*]] = alloca [[STRUCT_SS:%.*]]
; CHECK-NEXT:    [[B_PRIV_CAST:%.*]] = bitcast %struct.ss* [[B_PRIV]] to i32*
; CHECK-NEXT:    store i32 [[TMP0]], i32* [[B_PRIV_CAST]]
; CHECK-NEXT:    [[B_PRIV_0_1:%.*]] = getelementptr [[STRUCT_SS]], %struct.ss* [[B_PRIV]], i32 0, i32 1
; CHECK-NEXT:    store i64 [[TMP1]], i64* [[B_PRIV_0_1]]
; CHECK-NEXT:    [[TMP:%.*]] = getelementptr [[STRUCT_SS]], %struct.ss* [[B_PRIV]], i32 0, i32 0
; CHECK-NEXT:    [[TMP1:%.*]] = load i32, i32* [[TMP]], align 32
; CHECK-NEXT:    [[TMP2:%.*]] = add i32 [[TMP1]], 1
; CHECK-NEXT:    store i32 [[TMP2]], i32* [[TMP]], align 32
; CHECK-NEXT:    ret i32 [[TMP2]]
;
entry:
  %tmp = getelementptr %struct.ss, %struct.ss* %b, i32 0, i32 0
  %tmp1 = load i32, i32* %tmp, align 4
  %tmp2 = add i32 %tmp1, 1
  store i32 %tmp2, i32* %tmp, align 4
  ret i32 %tmp2
}


define i32 @main() nounwind  {
; CHECK-LABEL: define {{[^@]+}}@main()
; CHECK-NEXT:  entry:
; CHECK-NEXT:    [[S:%.*]] = alloca [[STRUCT_SS:%.*]]
; CHECK-NEXT:    [[TMP1:%.*]] = getelementptr [[STRUCT_SS]], %struct.ss* [[S]], i32 0, i32 0
; CHECK-NEXT:    store i32 1, i32* [[TMP1]], align 8
; CHECK-NEXT:    [[TMP4:%.*]] = getelementptr [[STRUCT_SS]], %struct.ss* [[S]], i32 0, i32 1
; CHECK-NEXT:    store i64 2, i64* [[TMP4]], align 4
; CHECK-NEXT:    [[S_CAST:%.*]] = bitcast %struct.ss* [[S]] to i32*
; CHECK-NEXT:    [[TMP0:%.*]] = load i32, i32* [[S_CAST]], align 1
; CHECK-NEXT:    [[S_0_1:%.*]] = getelementptr [[STRUCT_SS]], %struct.ss* [[S]], i32 0, i32 1
; CHECK-NEXT:    [[TMP1:%.*]] = load i64, i64* [[S_0_1]], align 1
; CHECK-NEXT:    [[C0:%.*]] = call i32 @f(i32 [[TMP0]], i64 [[TMP1]])
; CHECK-NEXT:    [[S_CAST1:%.*]] = bitcast %struct.ss* [[S]] to i32*
; CHECK-NEXT:    [[TMP2:%.*]] = load i32, i32* [[S_CAST1]], align 1
; CHECK-NEXT:    [[S_0_12:%.*]] = getelementptr [[STRUCT_SS]], %struct.ss* [[S]], i32 0, i32 1
; CHECK-NEXT:    [[TMP3:%.*]] = load i64, i64* [[S_0_12]], align 1
; CHECK-NEXT:    [[C1:%.*]] = call i32 @g(i32 [[TMP2]], i64 [[TMP3]])
; CHECK-NEXT:    [[A:%.*]] = add i32 [[C0]], [[C1]]
; CHECK-NEXT:    ret i32 [[A]]
;
entry:
  %S = alloca %struct.ss
  %tmp1 = getelementptr %struct.ss, %struct.ss* %S, i32 0, i32 0
  store i32 1, i32* %tmp1, align 8
  %tmp4 = getelementptr %struct.ss, %struct.ss* %S, i32 0, i32 1
  store i64 2, i64* %tmp4, align 4
  %c0 = call i32 @f(%struct.ss* byval %S) nounwind
  %c1 = call i32 @g(%struct.ss* byval %S) nounwind
  %a = add i32 %c0, %c1
  ret i32 %a
}


