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
-- The most negative immediate of each branch form: the top two bits of
-- the immediate must survive the `:'00'` scaling.

-- cbz w0, #-1048576 (imm19 = 0x40000)
def cbz_far_program : Program :=
  def_program [ (0x100000#64, 0x34800000#32) ]

def cbz_far_final : ArmState := run 1 (write_pc 0x100000#64 (br_init_state cbz_far_program))

example : read_pc cbz_far_final = 0#64 := by native_decide

-- b.eq #-1048576 (imm19 = 0x40000); Z is set in the zero PState
def beq_far_program : Program :=
  def_program [ (0x100000#64, 0x54800000#32) ]

def beq_far_final : ArmState :=
  run 1 (write_pc 0x100000#64 (write_flag PFlag.Z 1#1 (br_init_state beq_far_program)))

example : read_pc beq_far_final = 0#64 := by native_decide

-- b #-134217728 (imm26 = 0x2000000)
def b_far_program : Program :=
  def_program [ (0x8000000#64, 0x16000000#32) ]

def b_far_final : ArmState := run 1 (write_pc 0x8000000#64 (br_init_state b_far_program))

example : read_pc b_far_final = 0#64 := by native_decide

end BRTest
