(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Copying (with truncation or extension) bignums                            *)
(* ========================================================================= *)

needs "arm/proofs/equiv.ml";;
needs "common/relational_n.ml";;
needs "common/bignum_n.ml";;
needs "arm/proofs/arm_n.ml";;

(**** print_literal_from_elf "arm/generic/bignum_copy.o";;
 ****)

let ITE_SAME = prove(`(if b then x else x) = x`, MESON_TAC []);;

let bignum_copy_mc = define_assert_from_elf "bignum_copy_mc" "arm/generic/bignum_copy.o" [
  0xeb02001f;       (* arm_CMP X0 X2 *)
  0x9a823002;       (* arm_CSEL X2 X0 X2 Condition_CC *)
  0xd2800004;       (* arm_MOV X4 (rvalue (word 0)) *)
  0xb40000c2;       (* arm_CBZ X2 (word 24) *)
  0xf8647865;       (* arm_LDR X5 X3 (Shiftreg_Offset X4 3) *)
  0xf8247825;       (* arm_STR X5 X1 (Shiftreg_Offset X4 3) *)
  0x91000484;       (* arm_ADD X4 X4 (rvalue (word 1)) *)
  0xeb02009f;       (* arm_CMP X4 X2 *)
  0x54ffff83;       (* arm_BCC (word 2097136) *)
  0xeb00009f;       (* arm_CMP X4 X0 *)
  0x540000a2;       (* arm_BCS (word 20) *)
  0xf824783f;       (* arm_STR XZR X1 (Shiftreg_Offset X4 3) *)
  0x91000484;       (* arm_ADD X4 X4 (rvalue (word 1)) *)
  0xeb00009f;       (* arm_CMP X4 X0 *)
  0x54ffffa3;       (* arm_BCC (word 2097140) *)
  0xd65f03c0        (* arm_RET X30 *)
];;

let COPY_EXEC = ARM_MK_EXEC_RULE bignum_copy_mc;;

(* Symbolic execution of the two programs, going through n small steps. *)
let straight_line_tac (n:int):tactic =
  ENSURES_N_INIT_TAC "s0" THEN
  REPEAT_N (if n == 0 then 0 else 1) (ARM_STEPS'_TAC COPY_EXEC (1--n) "" []) THEN
  ENSURES_FINAL_STATE'_TAC THEN
  ASM_REWRITE_TAC[WORD_ADD];;

let ENUMERATEL = new_recursive_definition num_RECURSION
  `(ENUMERATEL 0 (f:num->A list) = []) /\
   (ENUMERATEL (SUC n) f = APPEND (f n) (ENUMERATEL n f))`;;

let INIT_CONST_TIME = prove(
    parse_term 
  "!pc k z n x es.
    k < 2 EXP 64 /\ n < 2 EXP 64
    ==> ensures_n arm
      (\s. aligned_bytes_loaded s (word pc) bignum_copy_mc /\ read PC s = word pc /\
           C_ARGUMENTS [word k; z; word n; x] s /\
           read events s = es)
      (\s. aligned_bytes_loaded s (word pc) bignum_copy_mc /\
           (~(0 = MIN k n) /\ read PC s = word (pc + 0x10) \/ 0 = MIN k n /\ read PC s = word (pc + 0x24)) /\
           C_ARGUMENTS [word k; z; word (MIN k n); x; word 0] s /\
           read events s = es)
      (\s s'. T)
      (\s. 4)",
  let finish =
    IMP_REWRITE_TAC [VAL_WORD; DIMINDEX_64; MOD_LT; ITE_SAME] THEN
    COND_CASES_TAC THENL replicate (
      ASM_REWRITE_TAC []) 2 in
  IMP_REWRITE_TAC [C_ARGUMENTS; MIN] THEN
  REPEAT STRIP_TAC THEN
  straight_line_tac 4 THEN
  DISJ_CASES_TAC (SPEC `k < n` EXCLUDED_MIDDLE) THENL [
    ASSUME_TAC (ARITH_RULE `k < n ==> k <= n`) THEN
    finish;
    DISJ_CASES_TAC (SPEC `k:num = n` EXCLUDED_MIDDLE) THENL [
      finish;
      ASSUME_TAC (ARITH_RULE `~(k < n) /\ ~(k = n) ==> ~(k <= n)`) THEN
      finish]]);;

let COPYLOOP_CONST_TIME = prove(
  `!pc k z n x es.
    k < 2 EXP 64 /\ n < 2 EXP 64 /\ ~(0 = MIN k n) /\
    nonoverlapping (word pc, 0x40) (z, 8 * k)
    ==> ensures_n arm
      (\s. aligned_bytes_loaded s (word pc) bignum_copy_mc /\ read PC s = word (pc + 0x10) /\
           C_ARGUMENTS [word k; z; word (MIN k n); x; word 0] s /\
           read events s = es)
      (\s. aligned_bytes_loaded s (word pc) bignum_copy_mc /\ read PC s = word (pc + 0x24) /\
           C_ARGUMENTS [word k; z; word (MIN k n); x; word (MIN k n)] s /\
           read events s = ENUMERATEL (MIN k n) (\i. [EventStore (word_add z (word (8 * i)));
                                                      EventLoad (word_add x (word (8 * i)))]))
      (\s s'. T)
      (\s. 5 * MIN k n)`,
  REWRITE_TAC [C_ARGUMENTS; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_N_WHILE_PUP_TAC `MIN k n` `pc + 0x10` `pc + 0x20`
  `\i s.
      (read X0 s = word k /\ read X1 s = z /\ read X2 s = word (MIN k n) /\ read X3 s = x /\ read X4 s = word i)`
  `\(i:num) s. read CF s <=> MIN k n <= i`
  `\(i:num). 4`
  `0` `1` THEN
  REPEAT CONJ_TAC THENL [
    (* # loop itrs > 0 *)
    ASM_ARITH_TAC;
    (* entrace -> loop header *)
    straight_line_tac 0;
    (* the main loop! *)
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `i < k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `i < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val (word i:64 word) < k` ASSUME_TAC THENL [IMP_REWRITE_TAC [VAL_WORD; DIMINDEX_64; MOD_LT]; ALL_TAC] THEN
    straight_line_tac 4 THEN
    SUBGOAL_THEN `k < 2 EXP 64 /\ n < 2 EXP 64 ==> MIN k n < 2 EXP 64` ASSUME_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VAL_WORD_SUB_EQ_0; GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    IMP_REWRITE_TAC [MOD_LT; ARITH_RULE `i < MIN k n /\ MIN k n < 2 EXP 64 ==> i + 1 < 2 EXP 64`];
    (* backedge *)
    REPEAT STRIP_TAC THEN
    straight_line_tac 1;
    (* postcond to ret *)
    straight_line_tac 1;
    (* counter *)
    REWRITE_TAC[NSUM_CONST_NUMSEG] THEN ASM_ARITH_TAC]);;

let PADDING_CONST_TIME = prove(
  `!pc k z n x es.
    k < 2 EXP 64 /\ n < 2 EXP 64
    ==> ensures_n arm
      (\s. aligned_bytes_loaded s (word pc) bignum_copy_mc /\ read PC s = word (pc + 0x24) /\
           C_ARGUMENTS [word k; z; word (MIN k n); x; word (MIN k n)] s /\
           read events s = es)
      (\s. aligned_bytes_loaded s (word pc) bignum_copy_mc /\
           (~(k <= MIN k n) /\ read PC s = word (pc + 0x2c) \/ k <= MIN k n /\ read PC s = word (pc + 0x3c)) /\
           C_ARGUMENTS [word k; z; word (MIN k n); x; word (MIN k n)] s /\
           read events s = es)
      (\s s'. T)
      (\s. 2)`,
  REWRITE_TAC [C_ARGUMENTS] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `MIN k n < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  straight_line_tac 2 THEN
  DISJ_CASES_TAC (SPEC `k <= MIN k n` EXCLUDED_MIDDLE) THENL [
    IMP_REWRITE_TAC [VAL_WORD; DIMINDEX_64; MOD_LT];
    IMP_REWRITE_TAC [VAL_WORD; DIMINDEX_64; MOD_LT] THEN
    ASM_REWRITE_TAC [GSYM NOT_LE]]);;

let PADLOOP_CONST_TIME = prove(
  `!pc k z n x es.
    k < 2 EXP 64 /\ n < 2 EXP 64 /\ ~(k <= MIN k n) /\
    nonoverlapping (word pc, 0x40) (z, 8 * k)
    ==> ensures_n arm
      (\s. aligned_bytes_loaded s (word pc) bignum_copy_mc /\ read PC s = word (pc + 0x2c) /\
           C_ARGUMENTS [word k; z; word (MIN k n); x; word (MIN k n)] s /\
           read events s = es)
      (\s. aligned_bytes_loaded s (word pc) bignum_copy_mc /\ read PC s = word (pc + 0x3c) /\
           C_ARGUMENTS [word k; z; word (MIN k n); x; word k] s /\
           read events s = ENUMERATEL (k - MIN k n) (\i. [EventStore (word_add z (word (8 * ((MIN k n) + i))))]))
      (\s s'. T)
      (\s. 4 * (k - (MIN k n)))`,
  REWRITE_TAC [C_ARGUMENTS; NONOVERLAPPING_CLAUSES] THEN
  REPEAT STRIP_TAC THEN
  ENSURES_N_WHILE_PAUP_TAC `(MIN k n):num` `k:num` `pc + 0x2c` `pc + 0x38`
  `\i s.
      read X0 s = word k /\ read X1 s = z /\ read X2 s = word (MIN k n) /\ read X3 s = x /\ read X4 s = word i`
  `\(i:num) s. read CF s <=> k <= i`
  `\(i:num). 3`
  `0` `1` THEN
  REPEAT CONJ_TAC THENL [
    (* # loop itrs > 0 *)
    ASM_ARITH_TAC;
    (* entrace -> loop header *)
    straight_line_tac 0;
    (* the main loop! *)
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `i < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `val (word i:64 word) < k` ASSUME_TAC THENL [IMP_REWRITE_TAC [VAL_WORD; DIMINDEX_64; MOD_LT]; ALL_TAC] THEN
    straight_line_tac 3 THEN
    REWRITE_TAC [VAL_WORD_SUB_EQ_0; GSYM WORD_ADD; VAL_WORD; DIMINDEX_64] THEN
    IMP_REWRITE_TAC [MOD_LT; ARITH_RULE `i < n /\ n < 2 EXP 64 ==> i + 1 < 2 EXP 64`];
    (* backedge *)
    REPEAT STRIP_TAC THEN
    straight_line_tac 1;
    (* postcond to ret *)
    straight_line_tac 1;
    (* counter 1 *)
    REWRITE_TAC [NSUM_CONST_NUMSEG] THEN ASM_ARITH_TAC]);;

let events = `\k z n x. APPEND
  (ENUMERATEL (k - MIN k n) (\i. [EventStore (word_add z (word (8 * ((MIN k n) + i))))]))
  (ENUMERATEL (MIN k n) (\i. [EventStore (word_add z (word (8 * i)));
                              EventLoad (word_add x (word (8 * i)))]))`;;

let COPY_CONST_TIME = prove(
  `?f_es. !pc k z n x.
    k < 2 EXP 64 /\ n < 2 EXP 64 /\
    nonoverlapping (word pc, 0x40) (z, 8 * k)
    ==> ensures_n arm
      (\s. aligned_bytes_loaded s (word pc) bignum_copy_mc /\ read PC s = word pc /\
           C_ARGUMENTS [word k; z; word n; x] s /\
           read events s = es)
      (\s. aligned_bytes_loaded s (word pc) bignum_copy_mc /\ read PC s = word (pc + 0x3c) /\
           C_ARGUMENTS [word k; z; word (MIN k n); x; word k] s /\
           read events s = APPEND (f_es k z n x) es)
      ((\s s'. T))
      (\s. 4 + 5 * MIN k n + 2 + 4 * (k - (MIN k n)))`,
  CHOOSE_TAC events THEN
  REPEAT STRIP_TAC THEN
  ONCE_REWRITE_TAC [GSYM (INST_TYPE [`:armstate`, `:B`] COMPONENT_SINK)] THEN
  MATCH_MP_TAC ENSURES_N_TRANS THEN
  META_EXISTS_TAC THEN
  CONJ_TAC THENL [
    MP_TAC (SPEC_ALL INIT_CONST_TIME) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (UNIFY_ACCEPT_TAC [`Q:armstate->bool`]);
    ALL_TAC] THEN
  ONCE_REWRITE_TAC [GSYM (INST_TYPE [`:armstate`, `:B`] COMPONENT_SINK)] THEN
  MATCH_MP_TAC ENSURES_N_TRANS THEN
  META_EXISTS_TAC THEN
  CONJ_TAC THENL [
    DISJ_CASES_TAC (SPEC `0 = MIN k n` EXCLUDED_MIDDLE) THENL [
      REWRITE_TAC [SYM (ASSUME `0 = MIN k n`); MULT_0] THEN
      MATCH_MP_TAC ENSURES_N_TRIVIAL THEN
      CONJ_TAC THENL [
        SUBST1_TAC (ASSUME `0 = MIN k n`) THEN STRIP_TAC THEN DISCH_THEN (UNIFY_ACCEPT_TAC [`Q:armstate->bool`]);
        REWRITE_TAC []];
      ASM_REWRITE_TAC [] THEN
      MP_TAC (SPEC_ALL COPYLOOP_CONST_TIME) THEN
      ASM_REWRITE_TAC []];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC [GSYM (INST_TYPE [`:armstate`, `:B`] COMPONENT_SINK)] THEN
  MATCH_MP_TAC ENSURES_N_TRANS THEN
  META_EXISTS_TAC THEN
  CONJ_TAC THENL [
    MP_TAC (SPEC_ALL PADDING_CONST_TIME) THEN
    ASM_REWRITE_TAC [] THEN
    DISCH_THEN (UNIFY_ACCEPT_TAC [`Q:armstate->bool`]);
    ALL_TAC] THEN
  DISJ_CASES_TAC (SPEC `k <= MIN k n` EXCLUDED_MIDDLE) THENL [
    SUBGOAL_THEN `MIN k n = k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `4 * (k - MIN k n) = 0` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    IMP_REWRITE_TAC [ENSURES_N_TRIVIAL] THEN
    REWRITE_TAC [];
    ASM_REWRITE_TAC [] THEN
    IMP_REWRITE_TAC [PADLOOP_CONST_TIME]]);;

let COPY2_CONST_TIME = prove(
  `!pc1 pc2 k z1 z2 n x1 x2.
    k < 2 EXP 64 /\ n < 2 EXP 64 /\
    nonoverlapping (word pc1, 0x40) (z1, 8 * k) /\ nonoverlapping (word pc2, 0x40) (z2, 8 * k)
    ==> ensures2 arm
      (\(s1,s2). aligned_bytes_loaded s1 (word pc1) bignum_copy_mc /\ read PC s1 = word pc1 /\
                 aligned_bytes_loaded s2 (word pc2) bignum_copy_mc /\ read PC s2 = word pc2 /\
                 C_ARGUMENTS [word k; z1; word n; x1] s1 /\
                 C_ARGUMENTS [word k; z2; word n; x2] s2)
      (\(s1,s2). aligned_bytes_loaded s1 (word pc1) bignum_copy_mc /\ read PC s1 = word (pc1 + 0x3c) /\
                 aligned_bytes_loaded s2 (word pc2) bignum_copy_mc /\ read PC s2 = word (pc2 + 0x3c) /\
                 C_ARGUMENTS [word k; z1; word (MIN k n); x1; word k] s1 /\
                 C_ARGUMENTS [word k; z2; word (MIN k n); x2; word k] s2)
      ((\s s'. T))
      (\s. 4 + 5 * MIN k n + 2 + 4 * (k - (MIN k n)))
      (\s. 4 + 5 * MIN k n + 2 + 4 * (k - (MIN k n)))`,
  let SINGLE_REWRITE_TAC th = ONCE_REWRITE_TAC [th] in
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!s1 s2.
    (aligned_bytes_loaded s1 (word pc1) bignum_copy_mc /\ read PC s1 = word pc1 /\
     aligned_bytes_loaded s2 (word pc2) bignum_copy_mc /\ read PC s2 = word pc2 /\
     C_ARGUMENTS [word k; z1; word n; x1] s1 /\
     C_ARGUMENTS [word k; z2; word n; x2] s2)
    =
    ((\s1. aligned_bytes_loaded s1 (word pc1) bignum_copy_mc /\ read PC s1 = word pc1 /\
           C_ARGUMENTS [word k; z1; word n; x1] s1) s1 /\
     (\s2. aligned_bytes_loaded s2 (word pc2) bignum_copy_mc /\ read PC s2 = word pc2 /\
           C_ARGUMENTS [word k; z2; word n; x2] s2) s2)` SINGLE_REWRITE_TAC THENL [MESON_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `!s1 s2.
    (aligned_bytes_loaded s1 (word pc1) bignum_copy_mc /\ read PC s1 = word (pc1 + 0x3c) /\
     aligned_bytes_loaded s2 (word pc2) bignum_copy_mc /\ read PC s2 = word (pc2 + 0x3c) /\
     C_ARGUMENTS [word k; z1; word (MIN k n); x1; word k] s1 /\
     C_ARGUMENTS [word k; z2; word (MIN k n); x2; word k] s2)
    =
    ((\s1. aligned_bytes_loaded s1 (word pc1) bignum_copy_mc /\ read PC s1 = word (pc1 + 0x3c) /\
           C_ARGUMENTS [word k; z1; word (MIN k n); x1; word k] s1) s1 /\
    (\s2. aligned_bytes_loaded s2 (word pc2) bignum_copy_mc /\ read PC s2 = word (pc2 + 0x3c) /\
          C_ARGUMENTS [word k; z2; word (MIN k n); x2; word k] s2) s2)` SINGLE_REWRITE_TAC THENL [MESON_TAC []; ALL_TAC] THEN
  SUBGOAL_THEN `
    (\s:armstate#armstate s':armstate#armstate. T)
    =
    (\(s:armstate,s2:armstate) (s':armstate,s2':armstate). (\s s'. T) s s' /\ (\s s'. T) s2 s2')` SUBST1_TAC THENL [REWRITE_TAC [LAMBDA_PAIR]; ALL_TAC] THEN
  MATCH_MP_TAC COMBINE_ENSURES_N_ENSURES2 THEN
  CONJ_TAC THENL [
    IMP_REWRITE_TAC [COPY_CONST_TIME];
    IMP_REWRITE_TAC [COPY_CONST_TIME]]);;
