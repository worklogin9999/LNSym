/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Carsten Stollmaier
-/
-- UMAXV, UMINV (unsigned max/min across vector)

import Arm.Decode
import Arm.Insts.Common
import Arm.Insts.CosimM

namespace DPSFP

open BitVec

/-- Fold `op` over the `elems` lanes of `x`, starting from lane 0. -/
def reduce_vector_aux (e : Nat) (elems : Nat) (esize : Nat)
    (op : BitVec esize → BitVec esize → BitVec esize) (x : BitVec n) (acc : BitVec esize) : BitVec esize :=
  if elems ≤ e then acc
  else reduce_vector_aux (e + 1) elems esize op x (op acc (elem_get x e esize))
  termination_by (elems - e)

@[state_simp_rules]
def reduce_vector (esize : Nat) (op : BitVec esize → BitVec esize → BitVec esize) (x : BitVec n) : BitVec esize :=
  reduce_vector_aux 1 (n / esize) esize op x (elem_get x 0 esize)

@[state_simp_rules]
def exec_advanced_simd_across_lanes (inst : Advanced_simd_across_lanes_cls) (s : ArmState) : ArmState :=
  -- size = 11 is reserved; size = 10 requires Q = 1.
  if inst.size = 0b11#2 ∨ (inst.size = 0b10#2 ∧ inst.Q = 0#1) then
    write_err (StateError.Illegal s!"Illegal {inst} encountered!") s
  else
    let datasize := if inst.Q = 1#1 then 128 else 64
    let esize := 8 <<< inst.size.toNat
    let operand := read_sfp datasize inst.Rn s
    let result : Option (BitVec esize) :=
      match inst.U, inst.opcode with
      | 1#1, 0b01010#5 => some (reduce_vector esize (fun a b => if a ≤ b then b else a) operand) -- UMAXV
      | 1#1, 0b11010#5 => some (reduce_vector esize (fun a b => if a ≤ b then a else b) operand) -- UMINV
      | _, _ => none
    match result with
    | none => write_err (StateError.Unimplemented s!"Unsupported {inst} encountered!") s
    | some res =>
      -- The scalar result lands in the low `esize` bits; the rest of the register is zeroed.
      let s := write_sfp 128 inst.Rd (zeroExtend 128 res) s
      write_pc ((read_pc s) + 4#64) s

----------------------------------------------------------------------

/-- UMAXV (opcode 0b01010) and UMINV (opcode 0b11010). -/
def Advanced_simd_across_lanes_cls.umaxminv.rand
  (opcode : BitVec 5) : Cosim.CosimM (Option (BitVec 32)) := do
  let Q := ← BitVec.rand 1
  let size := ← if Q = 0#1 then BitVec.rand 2 (lo := 0) (hi := 1) else BitVec.rand 2 (lo := 0) (hi := 2)
  let inst : Advanced_simd_across_lanes_cls :=
    { Q := Q,
      U := 1#1,
      size := size,
      opcode := opcode,
      Rn := ← BitVec.rand 5,
      Rd := ← BitVec.rand 5 }
  pure (some (inst.toBitVec32))

/-- Generate random instructions of Advanced_simd_across_lanes_cls class. -/
def Advanced_simd_across_lanes_cls.rand : List (Cosim.CosimM (Option (BitVec 32))) :=
  [ Advanced_simd_across_lanes_cls.umaxminv.rand 0b01010#5,
    Advanced_simd_across_lanes_cls.umaxminv.rand 0b11010#5 ]

end DPSFP
