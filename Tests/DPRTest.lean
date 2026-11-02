/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Carsten Stollmaier
-/

import Arm.Exec

section DPRTest

open BitVec

-- Unit tests for data processing (register) instructions. The cosimulation
-- framework never seeds or compares SP, so the SP forms are checked here.
-- Encodings were produced by clang; expected values were recorded on a
-- Graviton3 core.

def dpr_init_state (program : Program) : ArmState :=
  { gpr := (fun (_ : BitVec 5) => 0#64),
    sfp := (fun (_ : BitVec 5) => 0#128),
    pc := 0#64,
    pstate := PState.zero,
    mem := (fun (_ : BitVec 64) => 0#8),
    program := program,
    error := StateError.None }

def nzcv (s : ArmState) : BitVec 4 :=
  read_flag PFlag.N s ++ read_flag PFlag.Z s ++ read_flag PFlag.C s ++ read_flag PFlag.V s

----------------------------------------------------------------------
-- ADD/SUB (extended register): `Rn = 31` is SP for all four forms;
-- `Rd = 31` is SP for ADD/SUB and ZR for ADDS/SUBS (CMP/CMN).
-- `sp = 0xfffff2caafc0`, `x2 = 0x1000`.

def ext_sp_state (program : Program) : ArmState :=
  write_gpr 64 2#5 0x1000#64 (write_gpr 64 31#5 0xfffff2caafc0#64 (dpr_init_state program))

-- add x11, sp, x2, uxtx
def add_sp_final : ArmState := run 1 (ext_sp_state (def_program [ (0x0#64, 0x8b2263eb#32) ]))
example : read_gpr 64 11#5 add_sp_final = 0xfffff2cabfc0#64 := by native_decide

-- cmp sp, x2, uxtx (subs xzr, sp, x2, uxtx): SP is not written, C set
def cmp_sp_final : ArmState := run 1 (ext_sp_state (def_program [ (0x0#64, 0xeb2263ff#32) ]))
example : read_gpr 64 31#5 cmp_sp_final = 0xfffff2caafc0#64 := by native_decide
example : nzcv cmp_sp_final = 0b0010#4 := by native_decide

-- adds x11, sp, w2, uxtw #1
def adds_sp_final : ArmState := run 1 (ext_sp_state (def_program [ (0x0#64, 0xab2247eb#32) ]))
example : read_gpr 64 11#5 adds_sp_final = 0xfffff2cacfc0#64 := by native_decide
example : nzcv adds_sp_final = 0b0000#4 := by native_decide

-- add sp, sp, x2: SP written
def add_to_sp_final : ArmState := run 1 (ext_sp_state (def_program [ (0x0#64, 0x8b2263ff#32) ]))
example : read_gpr 64 31#5 add_to_sp_final = 0xfffff2cabfc0#64 := by native_decide

-- cmn sp, w2, sxtw (adds xzr, sp, w2, sxtw)
def cmn_sp_final : ArmState := run 1 (ext_sp_state (def_program [ (0x0#64, 0xab22c3ff#32) ]))
example : read_gpr 64 31#5 cmn_sp_final = 0xfffff2caafc0#64 := by native_decide
example : nzcv cmn_sp_final = 0b0000#4 := by native_decide

----------------------------------------------------------------------
-- The extensions.

-- add w22, w13, w6, uxth #2: w13 = 0x12345678, w6 = 0xffff8001
def add_uxth_final : ArmState :=
  run 1 (write_gpr 64 13#5 0x12345678#64 (write_gpr 64 6#5 0xffffffffffff8001#64
    (dpr_init_state (def_program [ (0x0#64, 0x0b2629b6#32) ]))))
example : read_gpr 64 22#5 add_uxth_final = 0x1236567c#64 := by native_decide

-- adds x0, x3, w17, sxtw #3: x3 = 0x10, w17 = -16
def adds_sxtw_final : ArmState :=
  run 1 (write_gpr 64 3#5 0x10#64 (write_gpr 64 17#5 0xfffffff0#64
    (dpr_init_state (def_program [ (0x0#64, 0xab31cc60#32) ]))))
example : read_gpr 64 0#5 adds_sxtw_final = 0xffffffffffffff90#64 := by native_decide
example : nzcv adds_sxtw_final = 0b1000#4 := by native_decide

-- sub x0, x1, w2, sxtb: x1 = 0x100, w2 = 0x80 (-128)
def sub_sxtb_final : ArmState :=
  run 1 (write_gpr 64 1#5 0x100#64 (write_gpr 64 2#5 0x80#64
    (dpr_init_state (def_program [ (0x0#64, 0xcb228020#32) ]))))
example : read_gpr 64 0#5 sub_sxtb_final = 0x180#64 := by native_decide

-- sub x0, x1, w2, uxtb #4
def sub_uxtb_final : ArmState :=
  run 1 (write_gpr 64 1#5 0x100#64 (write_gpr 64 2#5 0x80#64
    (dpr_init_state (def_program [ (0x0#64, 0xcb221020#32) ]))))
example : read_gpr 64 0#5 sub_uxtb_final = 0xfffffffffffff900#64 := by native_decide

-- subs x0, x1, xzr, uxtx: `Rm = 31` is XZR; x1 = -1
def subs_xzr_final : ArmState :=
  run 1 (write_gpr 64 1#5 0xffffffffffffffff#64 (write_gpr 64 31#5 0xfffff2caafc0#64
    (dpr_init_state (def_program [ (0x0#64, 0xeb3f6020#32) ]))))
example : read_gpr 64 0#5 subs_xzr_final = 0xffffffffffffffff#64 := by native_decide
example : nzcv subs_xzr_final = 0b1010#4 := by native_decide

----------------------------------------------------------------------
-- RBIT

def rbit_x_final : ArmState :=
  run 1 (write_gpr 64 1#5 0x0123456789abcdef#64 (dpr_init_state (def_program [ (0x0#64, 0xdac00020#32) ]))) -- rbit x0, x1
example : read_gpr 64 0#5 rbit_x_final = 0xf7b3d591e6a2c480#64 := by native_decide

def rbit_w_final : ArmState :=
  run 1 (write_gpr 64 1#5 0x0123456789abcdef#64 (dpr_init_state (def_program [ (0x0#64, 0x5ac00020#32) ]))) -- rbit w0, w1
example : read_gpr 64 0#5 rbit_w_final = 0xf7b3d591#64 := by native_decide

----------------------------------------------------------------------
-- CLZ

def clz_x (v : BitVec 64) : ArmState :=
  run 1 (write_gpr 64 1#5 v (dpr_init_state (def_program [ (0x0#64, 0xdac01020#32) ]))) -- clz x0, x1
def clz_w (v : BitVec 64) : ArmState :=
  run 1 (write_gpr 64 1#5 v (dpr_init_state (def_program [ (0x0#64, 0x5ac01020#32) ]))) -- clz w0, w1

example : read_gpr 64 0#5 (clz_x 0x10000#64) = 47#64 := by native_decide
example : read_gpr 64 0#5 (clz_x 0#64) = 64#64 := by native_decide
example : read_gpr 64 0#5 (clz_x 0x8000000000000000#64) = 0#64 := by native_decide
example : read_gpr 64 0#5 (clz_w 0#64) = 32#64 := by native_decide
-- only the low 32 bits count
example : read_gpr 64 0#5 (clz_w 0xffffffff00000001#64) = 31#64 := by native_decide

----------------------------------------------------------------------
-- UDIV

def udiv_x (a b : BitVec 64) : ArmState :=
  run 1 (write_gpr 64 1#5 a (write_gpr 64 2#5 b (dpr_init_state (def_program [ (0x0#64, 0x9ac20820#32) ])))) -- udiv x0, x1, x2
def udiv_w (a b : BitVec 64) : ArmState :=
  run 1 (write_gpr 64 1#5 a (write_gpr 64 2#5 b (dpr_init_state (def_program [ (0x0#64, 0x1ac20820#32) ])))) -- udiv w0, w1, w2

example : read_gpr 64 0#5 (udiv_x 1000#64 7#64) = 142#64 := by native_decide
-- 32-bit: high halves of both operands are ignored
example : read_gpr 64 0#5 (udiv_w 0xffffffff00000064#64 0x100000003#64) = 33#64 := by native_decide
-- division by zero yields zero
example : read_gpr 64 0#5 (udiv_x 1000#64 0#64) = 0#64 := by native_decide
example : read_gpr 64 0#5 (udiv_x 0xffffffffffffffff#64 0xffffffff#64) = 0x100000001#64 := by native_decide

-- udiv x0, x1, xzr: `Rm = 31` is XZR (zero divisor), not SP
def udiv_xzr_final : ArmState :=
  run 1 (write_gpr 64 1#5 1000#64 (write_gpr 64 31#5 0xfffff2caafc0#64
    (dpr_init_state (def_program [ (0x0#64, 0x9adf0820#32) ]))))
example : read_gpr 64 0#5 udiv_xzr_final = 0#64 := by native_decide

end DPRTest
