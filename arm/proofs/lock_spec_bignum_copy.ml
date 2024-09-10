(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

(* ========================================================================= *)
(* Copying (with truncation or extension) bignums                            *)
(* ========================================================================= *)

needs "arm/proofs/equiv.ml";;
needs "common/relational_n.ml";;
needs "common/lrelational.ml";;
needs "common/bignum_n.ml";;
needs "arm/proofs/arm_n.ml";;
needs "arm/proofs/larm.ml";;

(**** print_literal_from_elf "arm/generic/bignum_copy.o";;
 ****)

let FIND_FST = new_recursive_definition list_RECURSION
  `(FIND_FST (e:A) [] = 0) /\
   (FIND_FST (e:A) (CONS h t) = if h = e then 0 else (FIND_FST e t) + 1)`;;

let DROP = new_recursive_definition num_RECURSION
  `(DROP 0 (xs:A list) = xs) /\
   (DROP (SUC n) xs = DROP n (TL_OR xs []))`;;

let DROP_ADD1 = prove(
  `!n (xs:A list). DROP (n + 1) xs = DROP n (TL_OR xs [])`,
  REWRITE_TAC[GSYM ADD1; DROP]);;

let DROP1 = prove(
  `!xs:A list. DROP 1 xs = TL_OR xs []`,
  REWRITE_TAC[ONE; DROP]);;

let DROP_DEF = prove(
  `!n xs. (DROP 0 (xs:A list) = xs) /\ (DROP (n + 1) xs = TL_OR (DROP n xs) [])`,
  REWRITE_TAC[DROP; DROP_ADD1] THEN
  INDUCT_TAC THENL [
    REWRITE_TAC[DROP];
    ASM_REWRITE_TAC[DROP]]);;

let TL_OR_DROP_NIL = prove(
  `!n (xs:A list). TL_OR (DROP n xs) [] = DROP n (TL_OR xs [])`,
  INDUCT_TAC THENL [
    REWRITE_TAC[DROP];
    ASM_REWRITE_TAC[DROP]]);;

let DROP_NIL = prove(
  `!n. DROP n [] = []:A list`,
  INDUCT_TAC THENL [
    REWRITE_TAC[DROP];
    ASM_REWRITE_TAC[DROP; TL_OR; NULL]]);;

let DROP_DROP = prove(
  `!m n (ps:A list). DROP m (DROP n ps) = DROP (m + n) ps`,
  INDUCT_TAC THENL [
    REWRITE_TAC[DROP; ARITH_RULE `0 + n = n`];
    ASM_REWRITE_TAC[ADD1; DROP_DEF; ARITH_RULE `(m + 1) + n = (m + n) + 1`]]);;

let HD_OR_DROP_F = prove(
  `!(xs:bool list) n. n < FIND_FST F xs + 1 ==> (HD_OR (DROP n xs) F <=> n + 1 < FIND_FST F xs + 1)`,
  LIST_INDUCT_TAC THENL [
    REWRITE_TAC[DROP_NIL; HD_OR; NULL; FIND_FST] THEN ARITH_TAC;
    INDUCT_TAC THENL [
      REWRITE_TAC[DROP; HD_OR; NULL; HD; FIND_FST] THEN
      BOOL_CASES_TAC `h:bool` THEN REWRITE_TAC[] THEN ARITH_TAC;
      ASM_REWRITE_TAC[DROP; FIND_FST; TL_OR; NULL; TL] THEN
      BOOL_CASES_TAC `h:bool` THEN REWRITE_TAC[] THENL [      
        DISCH_THEN (ASSUME_TAC o MATCH_MP (ARITH_RULE `SUC x < y + 1 ==> x < y`)) THEN
        IMP_REWRITE_TAC[] THEN ARITH_TAC;
        ARITH_TAC]]]);;

let NOT_HD_OR_FIND_FST = prove(
  `!ps. HD_OR ps F ==> FIND_FST F ps = FIND_FST F (DROP 1 ps) + 1`,
  LIST_INDUCT_TAC THENL [
    REWRITE_TAC[HD_OR; NULL];
    SIMP_TAC[HD_OR; NULL; HD; FIND_FST; DROP1; TL_OR; TL]]);;

let NOT_HD_OR_FIND_FST = prove(
  `!ps. ~HD_OR ps F ==> FIND_FST F ps = 0`,
  LIST_INDUCT_TAC THENL [
    REWRITE_TAC[HD_OR; NULL; FIND_FST];
    SIMP_TAC[HD_OR; NULL; HD; FIND_FST]]);;

let HD_OR_FIND_FST = prove(
  `!ps. HD_OR ps F ==> FIND_FST T ps = 0`,
  LIST_INDUCT_TAC THENL [
    REWRITE_TAC[HD_OR; NULL];
    SIMP_TAC[HD_OR; NULL; HD; FIND_FST]]);;

let FIND_FST_LE_LENGTH = prove(
  `!e:A xs. FIND_FST e xs <= LENGTH xs`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL [
    REWRITE_TAC[FIND_FST; LENGTH] THEN ARITH_TAC;
    REWRITE_TAC[FIND_FST; LENGTH] THEN
    COND_CASES_TAC THENL [
      ARITH_TAC;
      ASM_ARITH_TAC]]);;

let FIND_FST_DROP_LE_LENGTH = prove(
  `!n xs e:A. FIND_FST e (DROP n xs) <= LENGTH xs`,
  INDUCT_TAC THENL [
    REWRITE_TAC[DROP; FIND_FST_LE_LENGTH];
    LIST_INDUCT_TAC THEN FIRST_X_ASSUM (fun th -> ALL_TAC) THENL [
      REWRITE_TAC[DROP_NIL; FIND_FST; LENGTH] THEN ARITH_TAC;
      REWRITE_TAC[DROP; TL_OR; NULL; TL; LENGTH] THEN
      GEN_TAC THEN FIRST_X_ASSUM (MP_TAC o SPECL [`t:A list`; `e:A`]) THEN
      ASM_ARITH_TAC]]);;

let ITE_SAME = prove(`(if b then x else x) = x`, MESON_TAC []);;
let WORD_ITE = prove(`word (if b then x else y) = if b then word x else word y`, MESON_TAC []);;

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

let BIGNUM_COPY_EXEC = ARM_MK_EXEC_RULE bignum_copy_mc;;

let BIGNUM_COPY_CONST_TIME = prove(
  `!k z n x ps pc1 pc2.
    2 * LENGTH ps + 2 < 2 EXP 64 /\
    nonoverlapping (word pc1, 0x40) (z, 8 * (2 * LENGTH ps + 2)) /\ nonoverlapping (word pc2, 0x40) (z, 8 * (2 * LENGTH ps + 2))
    ==> ensures (lock arm)
      (\s. aligned_bytes_loaded (FST s) (word pc1) bignum_copy_mc /\ read PC (FST s) = word pc1 /\
           aligned_bytes_loaded (SND s) (word pc2) bignum_copy_mc /\ read PC (SND s) = word pc2 /\
           C_ARGUMENTS [k; z; n; x] (FST s) /\
           C_ARGUMENTS [k; z; n; x] (SND s) /\
           read events (FST s) = read events (SND s) /\
           read preds (FST s) = ps /\ read preds (SND s) = ps)
      (\s. aligned_bytes_loaded (FST s) (word pc1) bignum_copy_mc /\ read PC (FST s) = word (pc1 + 0x3c) /\
           aligned_bytes_loaded (SND s) (word pc2) bignum_copy_mc /\ read PC (SND s) = word (pc2 + 0x3c) /\
           read events (FST s) = read events (SND s))
      (\s s'. T)`,
  REWRITE_TAC[NONOVERLAPPING_CLAUSES] THEN
  REWRITE_TAC[C_ARGUMENTS; C_RETURN] THEN
  W64_GEN_TAC `k:num` THEN X_GEN_TAC `z:int64` THEN
  W64_GEN_TAC `n:num` THEN X_GEN_TAC `x:int64` THEN
  MAP_EVERY X_GEN_TAC [`ps:bool list`; `pc1:num`; `pc2:num`] THEN
  DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  
  (*** Simulate the initial computation of min(n,k) and then
   *** recast the problem with n' = min(n,k) so we can assume
   *** hereafter that n <= k. This makes life a bit easier since
   *** otherwise n can actually be any number < 2^64 without
   *** violating the preconditions.
   ***)

  LENSURES_SEQUENCE_TAC `pc1 + 0xc` `pc2 + 0xc`
   `\s. read X0 (FST s) = word k /\ read X1 (FST s) = z /\ read X2 (FST s) = word(MIN n k) /\
        read X3 (FST s) = x /\ read X4 (FST s) = word 0 /\
        read X0 (SND s) = word k /\ read X1 (SND s) = z /\ read X2 (SND s) = word(MIN n k) /\
        read X3 (SND s) = x /\ read X4 (SND s) = word 0 /\
        read events (FST s) = read events (SND s) /\
        read preds (FST s) = ps /\ read preds (SND s) = ps` THEN
  CONJ_TAC THENL
   [LARM_SIM_TAC BIGNUM_COPY_EXEC (1--3) THEN
    REWRITE_TAC[ARITH_RULE `MIN n k = if k < n then k else n`] THEN
    MESON_TAC[];
    REPEAT(FIRST_X_ASSUM(MP_TAC o check ((!=) [] o intersect [`k:num`; `ps:bool list`] o frees o concl))) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN MP_TAC(ARITH_RULE `MIN n k <= k`) THEN
    SPEC_TAC(`MIN n k`,`n:num`) THEN
    REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    VAL_INT64_TAC `n:num`] THEN

  LENSURES_SEQUENCE_TAC `pc1 + 0x24` `pc2 + 0x24`
   `\s. read X0 (FST s) = word k /\ read X1 (FST s) = z /\ read X4 (FST s) = word (if HD_OR ps F then 0 else FIND_FST F (DROP 1 ps) + 1) /\
        read X0 (SND s) = word k /\ read X1 (SND s) = z /\ read X4 (SND s) = word (if HD_OR ps F then 0 else FIND_FST F (DROP 1 ps) + 1) /\
        read events (FST s) = read events (SND s) /\
        read preds (FST s) = (if HD_OR ps F then DROP 1 ps else DROP (FIND_FST F (DROP 1 ps) + 1) (DROP 1 ps)) /\
        read preds (SND s) = (if HD_OR ps F then DROP 1 ps else DROP (FIND_FST F (DROP 1 ps) + 1) (DROP 1 ps))` THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `HD_OR ps F` THENL
     [REWRITE_TAC[DROP1] THEN
      LARM_SIM_TAC BIGNUM_COPY_EXEC [1];
      ALL_TAC] THEN

    ABBREV_TAC `ps1:bool list = DROP 1 ps` THEN
    ABBREV_TAC `ps2:bool list = if HD_OR ps F then ps1 else DROP (FIND_FST F ps1 + 1) ps1` THEN

    SUBGOAL_THEN `FIND_FST F ps1 + 1 < LENGTH (ps:bool list) + 2` ASSUME_TAC THENL [
      ASSUME_TAC (ISPECL [`1`; `ps:bool list`; `F`] FIND_FST_DROP_LE_LENGTH) THEN
      EXPAND_TAC "ps1" THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `FIND_FST F ps1 + 1 < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN

    LENSURES_WHILE_UP_TAC `FIND_FST F ps1 + 1` `pc1 + 0x10` `pc1 + 0x24` `pc2 + 0x10` `pc2 + 0x24`
     `\i s. read X0 (FST s) = word k /\ read X1 (FST s) = z /\ read X2 (FST s) = word n /\ read X3 (FST s) = x /\ read X4 (FST s) = word i /\
            read X0 (SND s) = word k /\ read X1 (SND s) = z /\ read X2 (SND s) = word n /\ read X3 (SND s) = x /\ read X4 (SND s) = word i /\
            read events (FST s) = read events (SND s) /\
            read preds (FST s) = DROP i ps1 /\
            read preds (SND s) = DROP i ps1` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ARITH_TAC;
      EXPAND_TAC "ps1" THEN REWRITE_TAC[DROP1; DROP] THEN
      LARM_SIM_TAC BIGNUM_COPY_EXEC [1];
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `i:num` THEN
      LARM_SIM_TAC BIGNUM_COPY_EXEC (1--5) THEN
      IMP_REWRITE_TAC[WORD_ITE; WORD_ADD; WORD_ADD_ASSOC; HD_OR_DROP_F; DROP_ADD1; TL_OR_DROP_NIL];
      EXPAND_TAC "ps2" THEN DISCARD_ASSUMPTIONS_TAC (vfree_in `ps2:bool list` o concl) THEN
      IMP_REWRITE_TAC[ENSURES_ALREADY] THEN ASM_SIMP_TAC[LOWDIGITS_SELF; subsumed]];
    ALL_TAC] THEN

  ABBREV_TAC `ps1:bool list = DROP 1 ps` THEN
  ABBREV_TAC `ps2:bool list = if HD_OR ps F then ps1 else DROP (FIND_FST F ps1 + 1) ps1` THEN
  ABBREV_TAC `ps3:bool list = DROP 1 ps2` THEN

  ASM_CASES_TAC `HD_OR ps2 F` THENL [LARM_SIM_TAC BIGNUM_COPY_EXEC (1--2); ALL_TAC] THEN

  SUBGOAL_THEN `(if HD_OR ps F then 0 else FIND_FST F ps1 + 1) + FIND_FST F ps3 + 1 <= 2 * LENGTH ps + 2` ASSUME_TAC THENL [
    COND_CASES_TAC THENL [
      ASSUME_TAC (ISPECL [`2`; `ps:bool list`; `F`] FIND_FST_DROP_LE_LENGTH) THEN
      EXPAND_TAC "ps3" THEN EXPAND_TAC "ps2" THEN EXPAND_TAC "ps1" THEN
      REWRITE_TAC[ASSUME `HD_OR ps F`; DROP_DROP] THEN
      ASM_ARITH_TAC;
      ASSUME_TAC (ISPECL [`1`; `ps:bool list`; `F`] FIND_FST_DROP_LE_LENGTH) THEN
      ASSUME_TAC (ISPECL [`1 + (FIND_FST F (DROP 1 ps) + 1) + 1`; `ps:bool list`; `F`] FIND_FST_DROP_LE_LENGTH) THEN
      EXPAND_TAC "ps3" THEN EXPAND_TAC "ps2" THEN EXPAND_TAC "ps1" THEN
      REWRITE_TAC[ASSUME `~HD_OR ps F`; DROP_DROP] THEN
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(if HD_OR ps F then 0 else FIND_FST F ps1 + 1) + FIND_FST F ps3 + 1 < 2 EXP 64` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN

  LENSURES_WHILE_UP_TAC `FIND_FST F ps3 + 1` `pc1 + 0x2c` `pc1 + 0x3c` `pc2 + 0x2c` `pc2 + 0x3c`
   `\i s. read X0 (FST s) = word k /\ read X1 (FST s) = z /\ read X4 (FST s) = word ((if HD_OR ps F then 0 else FIND_FST F ps1 + 1) + i) /\
          read X0 (SND s) = word k /\ read X1 (SND s) = z /\ read X4 (SND s) = word ((if HD_OR ps F then 0 else FIND_FST F ps1 + 1) + i) /\
          read events (FST s) = read events (SND s) /\
          read preds (FST s) = DROP i ps3 /\
          read preds (SND s) = DROP i ps3` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    EXPAND_TAC "ps3" THEN REWRITE_TAC[DROP1; DROP; ADD_0] THEN
    LARM_SIM_TAC BIGNUM_COPY_EXEC (1--2);
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN VAL_INT64_TAC `(if HD_OR ps F then 0 else FIND_FST F ps1 + 1) + i:num` THEN
    LARM_SIM_TAC BIGNUM_COPY_EXEC (1--4) THEN
    IMP_REWRITE_TAC[WORD_ITE; WORD_ADD; WORD_ADD_ASSOC; HD_OR_DROP_F; DROP_ADD1; TL_OR_DROP_NIL];
    EXPAND_TAC "ps2" THEN DISCARD_ASSUMPTIONS_TAC (vfree_in `ps2:bool list` o concl) THEN
    IMP_REWRITE_TAC[ENSURES_ALREADY] THEN ASM_SIMP_TAC[LOWDIGITS_SELF; subsumed]]);;
