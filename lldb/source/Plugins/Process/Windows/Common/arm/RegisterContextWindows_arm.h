//===-- RegisterContextWindows_arm.h ----------------------------*- C++ -*-===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#ifndef liblldb_RegisterContextWindows_arm_H_
#define liblldb_RegisterContextWindows_arm_H_

#if defined(__arm__) || defined(_M_ARM)

#include "RegisterContextWindows.h"
#include "lldb/lldb-forward.h"

namespace lldb_private {

class Thread;

class RegisterContextWindows_arm : public RegisterContextWindows {
public:
  // Constructors and Destructors
  RegisterContextWindows_arm(Thread &thread, uint32_t concrete_frame_idx);

  virtual ~RegisterContextWindows_arm();

  // Subclasses must override these functions
  size_t GetRegisterCount() override;

  const RegisterInfo *GetRegisterInfoAtIndex(size_t reg) override;

  size_t GetRegisterSetCount() override;

  const RegisterSet *GetRegisterSet(size_t reg_set) override;

  bool ReadRegister(const RegisterInfo *reg_info,
                    RegisterValue &reg_value) override;

  bool WriteRegister(const RegisterInfo *reg_info,
                     const RegisterValue &reg_value) override;
};
} // namespace lldb_private

#endif // defined(__arm__) || defined(_M_ARM)

#endif // #ifndef liblldb_RegisterContextWindows_arm_H_
