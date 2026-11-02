/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author(s): Yan Peng
-/

import Arm.Exec

section LDSTTest

open BitVec

-- This file contains unit tests for LDST instructions
-- The cosimulation tests do not cover instructions related to memory access
-- TODO: use macros to simplify the tests

def set_init_state (program : Program) : ArmState :=
  let s := { gpr := (fun (_ : BitVec 5) => 0#64),
             sfp := (fun (_ : BitVec 5) => 0#128),
             pc := 0#64,
             pstate := PState.zero,
             mem := (fun (_ : BitVec 64) => 0#8),
             program := program,
             error := StateError.None}
  s

----------------------------------------------------------------------
-- test ldr, 32-bit gpr, unsigned offset
def ldr_gpr_unsigned_offset : Program :=
  def_program [ (0x0#64, 0xb9400fe0#32) ]  -- ldr w0, [sp, #12]

def ldr_gpr_unsigned_offset_state : ArmState :=
  let s := set_init_state ldr_gpr_unsigned_offset
  -- write 20 in 4 bytes to address 12
  let s := write_mem_bytes 4 12#64 20#32 s
  s

def ldr_gpr_unsigned_offset_final_state : ArmState := run 1 ldr_gpr_unsigned_offset_state

example : (read_gpr 64 0#5 ldr_gpr_unsigned_offset_final_state) = 20#64 := by native_decide
example : read_pc ldr_gpr_unsigned_offset_final_state = 4#64 := by native_decide

----------------------------------------------------------------------
-- test str, 64-bit gpr, post-index
def str_gpr_post_index : Program :=
  def_program [ (0x0#64, 0xf8003420#32) ] -- str x0, [x1], #3

def str_gpr_post_index_state : ArmState :=
  let s := set_init_state str_gpr_post_index
  -- write 20 in gpr x0
  let s := write_gpr 64 0#5 20#64 s
  -- write 0 in gpr x1
  write_gpr 64 1#5 0#64 s

def str_gpr_post_index_final_state : ArmState := run 1 str_gpr_post_index_state

example : (read_gpr 64 1#5 str_gpr_post_index_final_state) = 3#64 := by native_decide
example : (read_mem_bytes 8 0#64 str_gpr_post_index_final_state) = 20#64 := by native_decide
example : read_pc str_gpr_post_index_final_state = 4#64 := by native_decide

----------------------------------------------------------------------
-- test ldr, 64-bit sfp, post-index
def ldr_sfp_post_index : Program :=
  def_program [ (0x0#64, 0xfc408420#32) ] -- ldr d0, [x1], #8

def ldr_sfp_post_index_state : ArmState :=
  let s := set_init_state ldr_sfp_post_index
  let s := write_mem_bytes 8 0#64 20#64 s
  s

def ldr_sfp_post_index_final_state : ArmState := run 1 ldr_sfp_post_index_state

example : (read_sfp 128 0#5 ldr_sfp_post_index_final_state) = 20#128 := by native_decide
example : (read_gpr 64 1#5 ldr_sfp_post_index_final_state) = 8#64 := by native_decide

----------------------------------------------------------------------
-- test str, 128-bit sfp, unsigned offset
def str_stp_unsigned_offset : Program :=
  def_program [ (0x0#64, 0x3d800420#32) ] -- str q0, [x1, #1]

def str_sfp_unsigned_offset_state : ArmState :=
  let s := set_init_state str_stp_unsigned_offset
  write_sfp 128 0#5 123#128 s

def str_sfp_unsigned_offset_final_state : ArmState := run 1 str_sfp_unsigned_offset_state

example : (read_mem_bytes 16 16#64 str_sfp_unsigned_offset_final_state) = 123#128 := by native_decide

----------------------------------------------------------------------
-- test ldrb, unsigned offset
def ldrb_unsigned_offset : Program :=
  def_program [ (0x0#64, 0x39401020#32) ] -- ldrb x0, [x1, #4]

def ldrb_unsigned_offset_state: ArmState :=
  let s := set_init_state ldrb_unsigned_offset
  write_mem_bytes 1 4#64 20#8 s

def ldrb_unsigned_offset_final_state : ArmState := run 1 ldrb_unsigned_offset_state

example : (read_gpr 64 0#5 ldrb_unsigned_offset_final_state) = 20#64 := by native_decide

----------------------------------------------------------------------
-- test strb, post-index
def strb_post_index : Program :=
  def_program [ (0x0#64, 0x381fc420#32) ] -- strb x0, [x1], #-4

def strb_post_index_state : ArmState :=
  let s := set_init_state strb_post_index
  let s := write_gpr 64 1#5 5#64 s
  write_gpr 64 0#5 20#64 s

def strb_post_index_final_state : ArmState := run 1 strb_post_index_state

example : (read_gpr 64 0#5 strb_post_index_final_state) = 20#64 := by native_decide
example : (read_gpr 64 1#5 strb_post_index_final_state) = 1#64 := by native_decide

----------------------------------------------------------------------
-- test ldp
def ldp_gpr_pre_index : Program :=
  def_program [ (0x0#64, 0xa9c00820#32) ] -- ldp x0, x2, [x1]!

def ldp_gpr_pre_index_state : ArmState :=
  let s := set_init_state ldp_gpr_pre_index
  write_mem_bytes 16 0#64 0x1234000000000000ABCD#128 s

def ldp_gpr_pre_index_final_state : ArmState := run 1 ldp_gpr_pre_index_state

example : (read_gpr 64 0#5 ldp_gpr_pre_index_final_state) = 0xABCD#64 := by native_decide
example : (read_gpr 64 2#5 ldp_gpr_pre_index_final_state) = 0x1234#64 := by native_decide

----------------------------------------------------------------------
-- test stp
def stp_sfp_signed_offset : Program :=
  def_program [ (0x0#64, 0xad008820#32) ] -- stp q0, q2, [q1,#1]

def stp_sfp_signed_offset_state : ArmState :=
  let s := set_init_state stp_sfp_signed_offset
  let s := write_sfp 128 0#5 0x1234#128 s
  write_sfp 128 2#5 0xabcd#128 s


def stp_sfp_signed_offset_final_state : ArmState := run 1 stp_sfp_signed_offset_state

example : (read_mem_bytes 32 16#64 stp_sfp_signed_offset_final_state) =
  0xabcd00000000000000000000000000001234#256 := by native_decide


----------------------------------------------------------------------
-- Register offset forms. Encodings were produced by clang; the loaded and
-- stored values were recorded on a Graviton3 core.

-- test ldr, 64-bit gpr, register offset
def ldr_gpr_reg_offset : Program :=
  def_program [ (0x0#64, 0xf8626820#32) ] -- ldr x0, [x1, x2]

def ldr_gpr_reg_offset_state : ArmState :=
  let s := set_init_state ldr_gpr_reg_offset
  let s := write_gpr 64 1#5 0x100#64 s
  let s := write_gpr 64 2#5 0x18#64 s
  write_mem_bytes 8 0x118#64 0x1122334455667788#64 s

def ldr_gpr_reg_offset_final_state : ArmState := run 1 ldr_gpr_reg_offset_state

example : read_gpr 64 0#5 ldr_gpr_reg_offset_final_state = 0x1122334455667788#64 := by native_decide
example : read_pc ldr_gpr_reg_offset_final_state = 4#64 := by native_decide

----------------------------------------------------------------------
-- test ldr, 32-bit gpr, uxtw with scaled offset: only the low 32 bits of x2 count

def ldr_gpr_uxtw : Program :=
  def_program [ (0x0#64, 0xb8625820#32) ] -- ldr w0, [x1, w2, uxtw #2]

def ldr_gpr_uxtw_state : ArmState :=
  let s := set_init_state ldr_gpr_uxtw
  let s := write_gpr 64 1#5 0x100#64 s
  let s := write_gpr 64 2#5 0xffffffff00000003#64 s
  write_mem_bytes 4 0x10c#64 0xdeadbeef#32 s

def ldr_gpr_uxtw_final_state : ArmState := run 1 ldr_gpr_uxtw_state

example : read_gpr 64 0#5 ldr_gpr_uxtw_final_state = 0xdeadbeef#64 := by native_decide

----------------------------------------------------------------------
-- test str, 128-bit sfp, lsl #4

def str_sfp_lsl : Program :=
  def_program [ (0x0#64, 0x3ca27820#32) ] -- str q0, [x1, x2, lsl #4]

def str_sfp_lsl_state : ArmState :=
  let s := set_init_state str_sfp_lsl
  let s := write_gpr 64 1#5 0x100#64 s
  let s := write_gpr 64 2#5 0x2#64 s
  write_sfp 128 0#5 0x000102030405060708090a0b0c0d0e0f#128 s

def str_sfp_lsl_final_state : ArmState := run 1 str_sfp_lsl_state

example : read_mem_bytes 16 0x120#64 str_sfp_lsl_final_state = 0x000102030405060708090a0b0c0d0e0f#128 := by native_decide
example : read_mem_bytes 16 0x100#64 str_sfp_lsl_final_state = 0#128 := by native_decide

----------------------------------------------------------------------
-- test ldrb, register offset

def ldrb_reg_offset : Program :=
  def_program [ (0x0#64, 0x38626820#32) ] -- ldrb w0, [x1, x2]

def ldrb_reg_offset_state : ArmState :=
  let s := set_init_state ldrb_reg_offset
  let s := write_gpr 64 0#5 0xffffffffffffffff#64 s
  let s := write_gpr 64 1#5 0x100#64 s
  let s := write_gpr 64 2#5 0x5#64 s
  write_mem_bytes 1 0x105#64 0xab#8 s

def ldrb_reg_offset_final_state : ArmState := run 1 ldrb_reg_offset_state

example : read_gpr 64 0#5 ldrb_reg_offset_final_state = 0xab#64 := by native_decide

----------------------------------------------------------------------
-- test strb, sxtw with a negative 32-bit index

def strb_sxtw : Program :=
  def_program [ (0x0#64, 0x3822c820#32) ] -- strb w0, [x1, w2, sxtw]

def strb_sxtw_state : ArmState :=
  let s := set_init_state strb_sxtw
  let s := write_gpr 64 0#5 0x7c#64 s
  let s := write_gpr 64 1#5 0x100#64 s
  write_gpr 64 2#5 0x00000000fffffffe#64 s -- w2 = -2

def strb_sxtw_final_state : ArmState := run 1 strb_sxtw_state

example : read_mem_bytes 1 0xfe#64 strb_sxtw_final_state = 0x7c#8 := by native_decide

----------------------------------------------------------------------
-- test str, 64-bit gpr, sxtx #3

def str_gpr_sxtx : Program :=
  def_program [ (0x0#64, 0xf822f820#32) ] -- str x0, [x1, x2, sxtx #3]

def str_gpr_sxtx_state : ArmState :=
  let s := set_init_state str_gpr_sxtx
  let s := write_gpr 64 0#5 0x0123456789abcdef#64 s
  let s := write_gpr 64 1#5 0x100#64 s
  write_gpr 64 2#5 0xffffffffffffffff#64 s -- x2 = -1

def str_gpr_sxtx_final_state : ArmState := run 1 str_gpr_sxtx_state

example : read_mem_bytes 8 0xf8#64 str_gpr_sxtx_final_state = 0x0123456789abcdef#64 := by native_decide

----------------------------------------------------------------------
-- test ldr, 64-bit sfp, Rm = 31 is XZR, not SP

def ldr_sfp_xzr : Program :=
  def_program [ (0x0#64, 0xfc7f6820#32) ] -- ldr d0, [x1, xzr]

def ldr_sfp_xzr_state : ArmState :=
  let s := set_init_state ldr_sfp_xzr
  let s := write_gpr 64 1#5 0x100#64 s
  let s := write_gpr 64 31#5 0x1000#64 s
  write_mem_bytes 8 0x100#64 0x8877665544332211#64 s

def ldr_sfp_xzr_final_state : ArmState := run 1 ldr_sfp_xzr_state

example : read_sfp 128 0#5 ldr_sfp_xzr_final_state = 0x8877665544332211#128 := by native_decide

end LDSTTest
