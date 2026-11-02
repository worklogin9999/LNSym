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
-- USHL: per-lane shift by the signed low byte of the shift lane; negative
-- shifts right, amounts of at least the element size give zero.

-- ushl v0.16b, v1.16b, v2.16b: every lane 0x81, shifts (lane 0 first)
-- 0, 1, 7, 8, 9, -1, -7, -8, -9, 127, -128, 64, -64, 3, -3, 16
example : simd2 0x6e224420#32 0x81818181818181818181818181818181#128 0x10fd03c040807ff7f8f9ff0908070100#128 =
          0x00100800000000000001400000800281#128 := by native_decide
-- ushl v0.8b, v1.8b, v2.8b: upper half cleared
example : simd2 0x2e224420#32 0x81818181818181818181818181818181#128 0x10fd03c040807ff7f8f9ff0908070100#128 =
          0x00000000000000000001400000800281#128 := by native_decide
-- ushl v0.2d: shifts 63 and -63
example : simd2 0x6ee24420#32 0x80000000000000018000000000000001#128 0xffffffffffffffc1000000000000003f#128 =
          0x00000000000000018000000000000000#128 := by native_decide
-- ushl v0.2d: shift 64 clears; only the low byte of the shift lane counts (0x1ff = -1)
example : simd2 0x6ee24420#32 0x80000000000000018000000000000001#128 0x00000000000001ff0000000000000040#128 =
          0x40000000000000000000000000000000#128 := by native_decide
-- ushl v0.8h: every lane 0x8001, shifts 0, 15, 16, -1, -15, -16, 0x100 (= 0), 0xff01 (= 1)
example : simd2 0x6e624420#32 0x80018001800180018001800180018001#128 0xff010100fff0fff1ffff0010000f0000#128 =
          0x00028001000000014000000080008001#128 := by native_decide

----------------------------------------------------------------------
-- CNT: per-byte population count

-- cnt v0.16b, v1.16b
example : simd1 0x4e205820#32 0x810ff01155aa80ff7f3f1f0f07030100#128 = 0x02040402040401080706050403020100#128 := by
  native_decide
-- cnt v0.8b, v1.8b: upper half cleared
example : simd1 0x0e205820#32 0x810ff01155aa80ff7f3f1f0f07030100#128 = 0x00000000000000000706050403020100#128 := by
  native_decide

----------------------------------------------------------------------
-- UMAXV / UMINV: the scalar result lands in the low lane, the rest is zero.
-- v1 lanes (byte 0 first): 01 02 03 04 05 06 07 08 f1 0a 0b 0c 0d 0e 0f 10

def umv : BitVec 128 := 0x100f0e0d0c0b0af10807060504030201#128

example : simd1 0x6e30a820#32 umv = 0xf1#128 := by native_decide         -- umaxv b0, v1.16b
example : simd1 0x6e31a820#32 umv = 0x01#128 := by native_decide         -- uminv b0, v1.16b
example : simd1 0x2e30a820#32 umv = 0x08#128 := by native_decide         -- umaxv b0, v1.8b
example : simd1 0x6e71a820#32 umv = 0x0201#128 := by native_decide       -- uminv h0, v1.8h
example : simd1 0x2e70a820#32 umv = 0x0807#128 := by native_decide       -- umaxv h0, v1.4h
example : simd1 0x6eb0a820#32 umv = 0x100f0e0d#128 := by native_decide   -- umaxv s0, v1.4s
example : simd1 0x6eb1a820#32 umv = 0x04030201#128 := by native_decide   -- uminv s0, v1.4s

end DPSFPTest
