/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Carsten Stollmaier
-/

import Arm.Exec

section DPITest

open BitVec

-- Unit tests for data processing (immediate) instructions whose behaviour
-- the cosimulation framework cannot observe: it never seeds or compares SP,
-- so SP/XZR confusion for register 31 goes unnoticed there. Encodings were
-- produced by clang; expected values were recorded on a Graviton3 core.

-- `sp = 0x7ff0000`, `x10 = -1`, flags N, C and V set.
def dpi_init_state (program : Program) : ArmState :=
  let s := { gpr := (fun (_ : BitVec 5) => 0#64),
             sfp := (fun (_ : BitVec 5) => 0#128),
             pc := 0#64,
             pstate := { n := 1#1, z := 0#1, c := 1#1, v := 1#1 },
             mem := (fun (_ : BitVec 64) => 0#8),
             program := program,
             error := StateError.None }
  let s := write_gpr 64 31#5 0x7ff0000#64 s
  write_gpr 64 10#5 0xffffffffffffffff#64 s

----------------------------------------------------------------------
-- Logical (immediate): register 31 as the source operand is XZR for every
-- opcode; expected values were confirmed on a Graviton3 (Neoverse V1) core.

-- orr x10, xzr, #7 (an assembler prints this as orr, not mov: MoveWidePreferred)
def orr_xzr_final : ArmState := run 1 (dpi_init_state (def_program [ (0x0#64, 0xb2400bea#32) ]))
example : read_gpr 64 10#5 orr_xzr_final = 7#64 := by native_decide
example : read_gpr 64 31#5 orr_xzr_final = 0x7ff0000#64 := by native_decide

-- orr x10, xzr, #0x0f0f0f0f0f0f0f0f (the mov alias)
def mov_bitmask_final : ArmState := run 1 (dpi_init_state (def_program [ (0x0#64, 0xb200cfea#32) ]))
example : read_gpr 64 10#5 mov_bitmask_final = 0x0f0f0f0f0f0f0f0f#64 := by native_decide

-- and x10, xzr, #0xff
def and_xzr_final : ArmState := run 1 (dpi_init_state (def_program [ (0x0#64, 0x92401fea#32) ]))
example : read_gpr 64 10#5 and_xzr_final = 0#64 := by native_decide

-- eor x10, xzr, #0xff
def eor_xzr_final : ArmState := run 1 (dpi_init_state (def_program [ (0x0#64, 0xd2401fea#32) ]))
example : read_gpr 64 10#5 eor_xzr_final = 0xff#64 := by native_decide

-- ands x10, xzr, #0xffffffffffff: zero result, Z set, N/C/V clear
def ands_xzr_final : ArmState := run 1 (dpi_init_state (def_program [ (0x0#64, 0xf240bfea#32) ]))
example : read_gpr 64 10#5 ands_xzr_final = 0#64 := by native_decide
example : read_flag PFlag.N ands_xzr_final = 0#1 := by native_decide
example : read_flag PFlag.Z ands_xzr_final = 1#1 := by native_decide
example : read_flag PFlag.C ands_xzr_final = 0#1 := by native_decide
example : read_flag PFlag.V ands_xzr_final = 0#1 := by native_decide

-- The destination keeps the SP/ZR distinction: with `x10 = 0x12345679abc`,
-- AND/ORR/EOR with `Rd = 31` write SP, ANDS with `Rd = 31` (TST) discards.
def dpi_x10_state (program : Program) : ArmState :=
  write_gpr 64 10#5 0x12345679abc#64 (dpi_init_state program)

def orr_to_sp_final : ArmState := run 1 (dpi_x10_state (def_program [ (0x0#64, 0xb240015f#32) ])) -- orr sp, x10, #1
example : read_gpr 64 31#5 orr_to_sp_final = 0x12345679abd#64 := by native_decide

def and_to_sp_final : ArmState := run 1 (dpi_x10_state (def_program [ (0x0#64, 0x927c1d5f#32) ])) -- and sp, x10, #0xff0
example : read_gpr 64 31#5 and_to_sp_final = 0xab0#64 := by native_decide

def eor_to_sp_final : ArmState := run 1 (dpi_x10_state (def_program [ (0x0#64, 0xd2401d5f#32) ])) -- eor sp, x10, #0xff
example : read_gpr 64 31#5 eor_to_sp_final = 0x12345679a43#64 := by native_decide

def tst_final : ArmState := run 1 (dpi_x10_state (def_program [ (0x0#64, 0xf240015f#32) ])) -- tst x10, #1
example : read_gpr 64 31#5 tst_final = 0x7ff0000#64 := by native_decide
example : read_flag PFlag.N tst_final = 0#1 := by native_decide
example : read_flag PFlag.Z tst_final = 1#1 := by native_decide
example : read_flag PFlag.C tst_final = 0#1 := by native_decide
example : read_flag PFlag.V tst_final = 0#1 := by native_decide

end DPITest
