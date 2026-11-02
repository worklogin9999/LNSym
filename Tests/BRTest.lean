/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Carsten Stollmaier
-/

import Arm.Exec

section BRTest

open BitVec

-- Unit tests for branch instructions. The cosimulation framework runs a
-- single register-only instruction, so branches are checked here instead.
-- Encodings were produced by clang; taken/not-taken outcomes were recorded
-- on a Graviton3 core.

def br_init_state (program : Program) : ArmState :=
  { gpr := (fun (_ : BitVec 5) => 0#64),
    sfp := (fun (_ : BitVec 5) => 0#128),
    pc := 0#64,
    pstate := PState.zero,
    mem := (fun (_ : BitVec 64) => 0#8),
    program := program,
    error := StateError.None }

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

end BRTest
