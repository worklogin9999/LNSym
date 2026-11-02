/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Carsten Stollmaier
-/
-- LDR/STR (register offset, GPR and SIMD&FP)
-- LDRB/STRB (register offset, GPR)

import Arm.Decode
import Arm.Insts.Common
import Arm.Insts.LDST.Reg_imm

----------------------------------------------------------------------

namespace LDST

open BitVec

/-- `ExtendReg` from the Arm ARM: extend the 32- or 64-bit `Rm` operand
according to `option` and shift it left by `shift`. The 32-bit variants
(UXTW, SXTW) use the low 32 bits of `Rm`; the 64-bit ones (LSL/UXTX, SXTX) use
the whole register. -/
@[state_simp_rules]
def reg_reg_offset_extend (option : BitVec 3) (shift : Nat) (rm : BitVec 64) : BitVec 64 :=
  let val : BitVec 64 := match option with
    | 0b010#3 => zeroExtend 64 (extractLsb' 0 32 rm) -- UXTW
    | 0b110#3 => signExtend 64 (extractLsb' 0 32 rm) -- SXTW
    | _       => rm                                  -- LSL/UXTX, SXTX
  val <<< shift

@[state_simp_rules]
def exec_reg_reg_offset (inst : Reg_reg_offset_cls) (s : ArmState) : ArmState :=
  let SIMD? := inst.V = 1#1
  let scale :=
    if SIMD? then ((lsb inst.opc 1) ++ inst.size).toNat
    else inst.size.toNat
  -- option<1> = 0 is a sub-word index register, which is UNDEFINED.
  if lsb inst.option 1 = 0#1 then
    write_err (StateError.Illegal s!"Illegal instruction {inst} encountered!") s
  else if not $ supported_reg_imm inst.size inst.opc SIMD? then
    write_err (StateError.Unimplemented s!"Unsupported instruction {inst} encountered!") s
  else if SIMD? ∧ scale > 4 then
    write_err (StateError.Illegal s!"Illegal instruction {inst} encountered!") s
  else
    let shift := if inst.S = 1#1 then scale else 0
    let offset := reg_reg_offset_extend inst.option shift (read_gpr_zr 64 inst.Rm s)
    let datasize := 8 <<< scale
    let regsize :=
      if SIMD? then none
      else if inst.size = 0b11#2 then some 64 else some 32
    have H : 8 ∣ datasize := by
      simp_all! only [Nat.shiftLeft_eq, Nat.dvd_mul_right, datasize]
    let s' := reg_imm_operation s!"{inst}"
              (lsb inst.opc 0) false false
              SIMD? datasize regsize inst.Rn inst.Rt offset s (H)
    write_pc ((read_pc s) + 4#64) s'

end LDST
