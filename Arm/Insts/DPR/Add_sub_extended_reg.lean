/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Carsten Stollmaier
-/
-- ADD, ADDS, SUB, SUBS (extended register): 32- and 64-bit versions

import Arm.Decode
import Arm.Insts.Common

namespace DPR

open BitVec

/-- `ExtendReg` from the Arm ARM: take the low `8 <<< option[1:0]` bits of `reg`,
zero- or sign-extend them to `n` bits and shift left by `shift`. -/
@[state_simp_rules]
def extend_reg (n : Nat) (reg : BitVec 64) (option : BitVec 3) (shift : Nat) : BitVec n :=
  let unsigned := lsb option 2 = 0#1
  let len := 8 <<< (extractLsb' 0 2 option).toNat
  let len := min len (n - shift)
  let low := zeroExtend len reg
  let ext := if unsigned then zeroExtend n low else signExtend n low
  ext <<< shift

@[state_simp_rules]
def exec_add_sub_extended_reg (inst : Add_sub_extended_reg_cls) (s : ArmState) : ArmState :=
  let datasize := 32 <<< inst.sf.toNat
  if inst.opt ≠ 0b00#2 ∨ inst.imm3.toNat > 4 then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let sub_op := inst.op = 1#1
    let setflags := inst.S = 1#1
    -- Rn = 31 is SP for all forms (CMP/CMN of SP); Rd = 31 is SP only when
    -- flags are not set.
    let operand1 := read_gpr datasize inst.Rn s
    let operand2 := extend_reg datasize (read_gpr_zr 64 inst.Rm s) inst.option inst.imm3.toNat
    let operand2 := if sub_op then ~~~operand2 else operand2
    let carry := if sub_op then 1 else 0
    let (result, pstate) := AddWithCarry operand1 operand2 carry
    let s' := write_pc ((read_pc s) + 4#64) s
    let s' := if setflags then write_pstate pstate s' else s'
    let s' := if setflags then write_gpr_zr datasize inst.Rd result s' else write_gpr datasize inst.Rd result s'
    s'

----------------------------------------------------------------------

/-- Generate random instructions of the DPR.Add_sub_extended_reg class. -/
def Add_sub_extended_reg_cls.rand : Cosim.CosimM (Option (BitVec 32)) := do
  let S := ← BitVec.rand 1
  -- (FIXME) Rn = 31 reads SP and Rd = 31 writes SP unless flags are set; the
  -- cosimulation framework does not account for effects to SP.
  let Rd_hi := if S = 1#1 then 31 else 30
  let inst : Add_sub_extended_reg_cls :=
    { sf     := ← BitVec.rand 1,
      op     := ← BitVec.rand 1,
      S      := S,
      opt    := 0b00#2,
      Rm     := ← GPRIndex.rand,
      option := ← BitVec.rand 3,
      imm3   := ← BitVec.rand 3 (lo := 0) (hi := 4),
      Rn     := ← GPRIndex.rand (lo := 0) (hi := 30),
      Rd     := ← GPRIndex.rand (lo := 0) (hi := Rd_hi) }
  pure (some (inst.toBitVec32))

end DPR
