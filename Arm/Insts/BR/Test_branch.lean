/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Carsten Stollmaier
-/

-- TBZ, TBNZ -- 32 and 64-bit variants

import Arm.Decode
import Arm.State
import Arm.Insts.Common
import Arm.BitVec

namespace BR

open BitVec

@[state_simp_rules]
def Test_branch_inst.branch_taken_pc (inst : Test_branch_cls) (pc : BitVec 64) : BitVec 64 :=
  let offset := (signExtend 64 inst.imm14) <<< 2
  pc + offset

@[state_simp_rules]
def Test_branch_inst.condition_holds (inst : Test_branch_cls) (s : ArmState) : Bool :=
  let bit_pos := (inst.b5 ++ inst.b40).toNat
  let operand := read_gpr 64 inst.Rt s
  -- TBZ (op = 0) branches when the bit is clear; TBNZ (op = 1) when it is set.
  operand.getLsbD bit_pos = (inst.op = 1#1)

@[state_simp_rules]
def exec_test_branch (inst : Test_branch_cls) (s : ArmState) : ArmState :=
  let orig_pc := read_pc s
  let next_pc := if Test_branch_inst.condition_holds inst s then
                   Test_branch_inst.branch_taken_pc inst orig_pc
                 else
                   orig_pc + 4#64
  write_pc next_pc s

end BR
