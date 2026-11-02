/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Carsten Stollmaier
-/

import Arm.Exec

section DPRTest

open BitVec

-- Unit tests for data processing (register) instructions. Encodings were
-- produced by clang; expected values were recorded on a Graviton3 core.

def dpr_init_state (program : Program) : ArmState :=
  { gpr := (fun (_ : BitVec 5) => 0#64),
    sfp := (fun (_ : BitVec 5) => 0#128),
    pc := 0#64,
    pstate := PState.zero,
    mem := (fun (_ : BitVec 64) => 0#8),
    program := program,
    error := StateError.None }

----------------------------------------------------------------------
-- RBIT

def rbit_x_final : ArmState :=
  run 1 (write_gpr 64 1#5 0x0123456789abcdef#64 (dpr_init_state (def_program [ (0x0#64, 0xdac00020#32) ]))) -- rbit x0, x1
example : read_gpr 64 0#5 rbit_x_final = 0xf7b3d591e6a2c480#64 := by native_decide

def rbit_w_final : ArmState :=
  run 1 (write_gpr 64 1#5 0x0123456789abcdef#64 (dpr_init_state (def_program [ (0x0#64, 0x5ac00020#32) ]))) -- rbit w0, w1
example : read_gpr 64 0#5 rbit_w_final = 0xf7b3d591#64 := by native_decide

----------------------------------------------------------------------
-- CLZ

def clz_x (v : BitVec 64) : ArmState :=
  run 1 (write_gpr 64 1#5 v (dpr_init_state (def_program [ (0x0#64, 0xdac01020#32) ]))) -- clz x0, x1
def clz_w (v : BitVec 64) : ArmState :=
  run 1 (write_gpr 64 1#5 v (dpr_init_state (def_program [ (0x0#64, 0x5ac01020#32) ]))) -- clz w0, w1

example : read_gpr 64 0#5 (clz_x 0x10000#64) = 47#64 := by native_decide
example : read_gpr 64 0#5 (clz_x 0#64) = 64#64 := by native_decide
example : read_gpr 64 0#5 (clz_x 0x8000000000000000#64) = 0#64 := by native_decide
example : read_gpr 64 0#5 (clz_w 0#64) = 32#64 := by native_decide
-- only the low 32 bits count
example : read_gpr 64 0#5 (clz_w 0xffffffff00000001#64) = 31#64 := by native_decide

end DPRTest
