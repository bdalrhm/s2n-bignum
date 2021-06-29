(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "LICENSE" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 *)

(* ========================================================================= *)
(* Deduce if a 256-bit bignum is nonzero.                                    *)
(* ========================================================================= *)

(**** print_literal_from_elf "x86/p256/bignum_nonzero_4.o";;
 ****)

let bignum_nonzero_4_mc =
  define_assert_from_elf "bignum_nonzero_4_mc" "x86/p256/bignum_nonzero_4.o"
[
  0x48; 0x8b; 0x07;        (* MOV (% rax) (Memop Quadword (%% (rdi,0))) *)
  0x48; 0x8b; 0x57; 0x08;  (* MOV (% rdx) (Memop Quadword (%% (rdi,8))) *)
  0x48; 0x0b; 0x47; 0x10;  (* OR (% rax) (Memop Quadword (%% (rdi,16))) *)
  0x48; 0x0b; 0x57; 0x18;  (* OR (% rdx) (Memop Quadword (%% (rdi,24))) *)
  0x48; 0x09; 0xd0;        (* OR (% rax) (% rdx) *)
  0xba; 0x01; 0x00; 0x00; 0x00;
                           (* MOV (% edx) (Imm32 (word 1)) *)
  0x48; 0x0f; 0x45; 0xc2;  (* CMOVNE (% rax) (% rdx) *)
  0xc3                     (* RET *)
];;

let BIGNUM_NONZERO_4_EXEC = X86_MK_EXEC_RULE bignum_nonzero_4_mc;;

(* ------------------------------------------------------------------------- *)
(* Correctness proof.                                                        *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_NONZERO_4_CORRECT = prove
 (`!x n pc.
        ensures x86
          (\s. bytes_loaded s (word pc) bignum_nonzero_4_mc /\
               read RIP s = word pc /\
               C_ARGUMENTS [x] s /\
               bignum_from_memory(x,4) s = n)
          (\s. read RIP s = word(pc + 0x1b) /\
               C_RETURN s = if ~(n = 0) then word 1 else word 0)
          (MAYCHANGE [RIP; RAX; RDX] ,,
           MAYCHANGE SOME_FLAGS)`,
  MAP_EVERY X_GEN_TAC [`x:int64`; `n:num`; `pc:num`] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
  REWRITE_TAC[BIGNUM_FROM_MEMORY_BYTES] THEN ENSURES_INIT_TAC "s0" THEN
  BIGNUM_DIGITIZE_TAC "n_" `read (memory :> bytes (x,8 * 4)) s0` THEN
  X86_STEPS_TAC BIGNUM_NONZERO_4_EXEC (1--7) THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "n" THEN REWRITE_TAC[ADD_EQ_0; VAL_EQ_0; WORD_OR_EQ_0] THEN
  REWRITE_TAC[MULT_EQ_0; EXP_EQ_0; ARITH_EQ; VAL_EQ_0] THEN
  REWRITE_TAC[CONJ_ACI; COND_SWAP] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[WORD_OR_0]);;

let BIGNUM_NONZERO_4_SUBROUTINE_CORRECT = prove
 (`!x n pc stackpointer returnaddress.
        ensures x86
          (\s. bytes_loaded s (word pc) bignum_nonzero_4_mc /\
               read RIP s = word pc /\
               read RSP s = stackpointer /\
               read (memory :> bytes64 stackpointer) s = returnaddress /\
               C_ARGUMENTS [x] s /\
               bignum_from_memory(x,4) s = n)
          (\s. read RIP s = returnaddress /\
               read RSP s = word_add stackpointer (word 8) /\
               C_RETURN s = if ~(n = 0) then word 1 else word 0)
          (MAYCHANGE [RIP; RSP; RAX; RDX] ,,
           MAYCHANGE SOME_FLAGS)`,
  X86_ADD_RETURN_NOSTACK_TAC BIGNUM_NONZERO_4_EXEC BIGNUM_NONZERO_4_CORRECT);;
