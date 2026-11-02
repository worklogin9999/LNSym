/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Arm.Exec

/-!
Unit tests for the PC-relative immediate branches (B, BL, B.cond, CBZ/CBNZ).

The architecture computes the offset as `SignExtend(imm:'00', 64)`, i.e. the
two zero bits are appended *before* sign extension; these tests cover offsets
outside the window where shifting at the immediate's own width happens to
agree (|offset| ≥ 32 MiB for B/BL, ≥ 256 KiB for B.cond/CBZ/CBNZ), plus small
and negative offsets. See https://github.com/leanprover/LNSym/issues/250.
-/

section BranchTest

open BitVec

/-- PC after executing the single instruction `word` at PC 0 in the default
state (all registers and flags zero). -/
private def pcAfter (word : BitVec 32) : BitVec 64 :=
  read_pc (run 1 (set_program ArmState.default [(0#64, word)]))

-- B (imm26)
example : pcAfter 0x15000000#32 = 0x4000000#64 := by native_decide            -- b .+64MiB
example : pcAfter 0x14800000#32 = 0x2000000#64 := by native_decide            -- b .+32MiB
example : pcAfter 0x17000000#32 = 0xfffffffffc000000#64 := by native_decide   -- b .-64MiB
example : pcAfter 0x14000001#32 = 0x4#64 := by native_decide                  -- b .+4
example : pcAfter 0x17ffffff#32 = 0xfffffffffffffffc#64 := by native_decide   -- b .-4
-- BL (imm26): same target, and x30 gets the return address
example : pcAfter 0x95000000#32 = 0x4000000#64 := by native_decide            -- bl .+64MiB
example : read_gpr 64 30#5
    (run 1 (set_program ArmState.default [(0#64, 0x95000000#32)])) = 0x4#64 := by
  native_decide
-- B.cond (imm19); AL is always taken
example : pcAfter 0x5440000e#32 = 0x80000#64 := by native_decide              -- b.al .+512KiB
example : pcAfter 0x54c0000e#32 = 0xfffffffffff80000#64 := by native_decide   -- b.al .-512KiB
example : pcAfter 0x54ffffee#32 = 0xfffffffffffffffc#64 := by native_decide   -- b.al .-4
-- CBZ / CBNZ (imm19); x0 = 0 in the default state
example : pcAfter 0xb4400000#32 = 0x80000#64 := by native_decide              -- cbz x0, .+512KiB
example : pcAfter 0xb4c00000#32 = 0xfffffffffff80000#64 := by native_decide   -- cbz x0, .-512KiB
example : pcAfter 0xb5400000#32 = 0x4#64 := by native_decide                  -- cbnz x0 (not taken)

----------------------------------------------------------------------
-- TBZ / TBNZ (imm14, bit position b5:b40). Encodings were produced by clang;
-- taken/not-taken outcomes were recorded on a Graviton3 core.

private def br_init_state (program : Program) : ArmState :=
  set_program ArmState.default program

----------------------------------------------------------------------
-- tbz w0, #3, .+8: taken when bit 3 is clear

def tbz_program : Program :=
  def_program [ (0x0#64, 0x36180040#32) ] -- tbz w0, #3, #8

def tbz_clear_final : ArmState := run 1 (write_gpr 64 0#5 0xf7#64 (br_init_state tbz_program))
def tbz_set_final   : ArmState := run 1 (write_gpr 64 0#5 0x08#64 (br_init_state tbz_program))

example : read_pc tbz_clear_final = 8#64 := by native_decide
example : read_pc tbz_set_final = 4#64 := by native_decide

----------------------------------------------------------------------
-- tbnz x1, #40, .-4: 64-bit bit position (b5 = 1), negative offset

def tbnz_program : Program :=
  def_program [ (0x0#64, 0xd503201f#32),   -- nop
                (0x4#64, 0xb747ffe1#32) ]  -- tbnz x1, #40, #-4

def tbnz_set_final   : ArmState := run 2 (write_gpr 64 1#5 (1#64 <<< 40) (br_init_state tbnz_program))
def tbnz_clear_final : ArmState := run 2 (write_gpr 64 1#5 (1#64 <<< 41) (br_init_state tbnz_program))

example : read_pc tbnz_set_final = 0#64 := by native_decide
example : read_pc tbnz_clear_final = 8#64 := by native_decide

----------------------------------------------------------------------
-- tbz w3, #0, .-32768: the most negative offset (imm14 = 0x2000)

def tbz_far_program : Program :=
  def_program [ (0x8000#64, 0x36040003#32) ] -- tbz w3, #0, #-32768

def tbz_far_final : ArmState :=
  run 1 (write_pc 0x8000#64 (br_init_state tbz_far_program))

example : read_pc tbz_far_final = 0#64 := by native_decide

----------------------------------------------------------------------
-- tbnz w2, #0, .+16: bit 0

def tbnz0_program : Program :=
  def_program [ (0x0#64, 0x37000082#32) ] -- tbnz w2, #0, #16

def tbnz0_final : ArmState := run 1 (write_gpr 64 2#5 0xfffffffffffffffe#64 (br_init_state tbnz0_program))

example : read_pc tbnz0_final = 4#64 := by native_decide
example : read_gpr 64 2#5 tbnz0_final = 0xfffffffffffffffe#64 := by native_decide

end BranchTest
