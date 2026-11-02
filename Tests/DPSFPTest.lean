/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Carsten Stollmaier
-/

import Arm.Exec

section DPSFPTest

open BitVec

-- Unit tests for Advanced SIMD instructions. Encodings were produced by
-- clang; expected values were recorded on a Graviton3 core.

def simd_init_state (program : Program) : ArmState :=
  { gpr := (fun (_ : BitVec 5) => 0#64),
    sfp := (fun (_ : BitVec 5) => 0#128),
    pc := 0#64,
    pstate := PState.zero,
    mem := (fun (_ : BitVec 64) => 0#8),
    program := program,
    error := StateError.None }

def simd1 (w : BitVec 32) (v1 : BitVec 128) : BitVec 128 :=
  read_sfp 128 0#5 (run 1 (write_sfp 128 1#5 v1 (simd_init_state (def_program [ (0x0#64, w) ]))))
def simd2 (w : BitVec 32) (v1 v2 : BitVec 128) : BitVec 128 :=
  read_sfp 128 0#5 (run 1 (write_sfp 128 1#5 v1 (write_sfp 128 2#5 v2 (simd_init_state (def_program [ (0x0#64, w) ])))))

----------------------------------------------------------------------
-- CNT: per-byte population count

-- cnt v0.16b, v1.16b
example : simd1 0x4e205820#32 0x810ff01155aa80ff7f3f1f0f07030100#128 = 0x02040402040401080706050403020100#128 := by
  native_decide
-- cnt v0.8b, v1.8b: upper half cleared
example : simd1 0x0e205820#32 0x810ff01155aa80ff7f3f1f0f07030100#128 = 0x00000000000000000706050403020100#128 := by
  native_decide

end DPSFPTest
