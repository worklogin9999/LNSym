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
-- UDIV

def udiv_x (a b : BitVec 64) : ArmState :=
  run 1 (write_gpr 64 1#5 a (write_gpr 64 2#5 b (dpr_init_state (def_program [ (0x0#64, 0x9ac20820#32) ])))) -- udiv x0, x1, x2
def udiv_w (a b : BitVec 64) : ArmState :=
  run 1 (write_gpr 64 1#5 a (write_gpr 64 2#5 b (dpr_init_state (def_program [ (0x0#64, 0x1ac20820#32) ])))) -- udiv w0, w1, w2

example : read_gpr 64 0#5 (udiv_x 1000#64 7#64) = 142#64 := by native_decide
-- 32-bit: high halves of both operands are ignored
example : read_gpr 64 0#5 (udiv_w 0xffffffff00000064#64 0x100000003#64) = 33#64 := by native_decide
-- division by zero yields zero
example : read_gpr 64 0#5 (udiv_x 1000#64 0#64) = 0#64 := by native_decide
example : read_gpr 64 0#5 (udiv_x 0xffffffffffffffff#64 0xffffffff#64) = 0x100000001#64 := by native_decide

-- udiv x0, x1, xzr: `Rm = 31` is XZR (zero divisor), not SP
def udiv_xzr_final : ArmState :=
  run 1 (write_gpr 64 1#5 1000#64 (write_gpr 64 31#5 0xfffff2caafc0#64
    (dpr_init_state (def_program [ (0x0#64, 0x9adf0820#32) ]))))
example : read_gpr 64 0#5 udiv_xzr_final = 0#64 := by native_decide

end DPRTest
