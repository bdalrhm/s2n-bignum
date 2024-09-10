needs "common/relational.ml";;
needs "common/relational2.ml";;

let NSUM_REFLECT' = prove(`!x n. nsum (0..n) (\i. x(n - i)) = nsum (0..n) x`,
  REPEAT GEN_TAC THEN
  SUBST1_TAC (SPECL [`x:num->num`; `0`; `n:num`] NSUM_REFLECT) THEN
  REWRITE_TAC[ARITH_RULE `~(n < 0) /\ (n - 0 = n)`]);;

let ENSURES_N_TRIVIAL = prove(
  `!step q f fn. ensures_n step (\x. F) q f fn`,
  REWRITE_TAC[ensures_n]);;

let ENSURES_N_ALREADY = prove(
  `!(step:A->A->bool) P Q C.
    (!s. P s ==> Q s) /\ (=) subsumed C ==> ensures_n step P Q C (\s. 0)`,
  REWRITE_TAC[ensures_n; subsumed; EVENTUALLY_N_TRIVIAL] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN MESON_TAC[]);;

let ENSURES_N_INIT_TAC sname =
  GEN_REWRITE_TAC I [ensures_n] THEN
  REWRITE_TAC[] (* for general beta reduction *) THEN
  W(fun (asl,w) ->
      let ty = type_of(fst(dest_forall w)) in
      let svar = mk_var(sname,ty) in
      X_GEN_TAC svar THEN
      DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
      ASSUME_TAC(ISPEC svar MAYCHANGE_STARTER));;

let ENSURES_N_BIGNUM_TERMRANGE_TAC =
  let pth = prove
   (`!k m. m < 2 EXP (64 * k) \/ !s x. ~(bignum_from_memory (x,k) s = m)`,
    MESON_TAC[BIGNUM_FROM_MEMORY_BOUND]) in
  fun k m ->
    DISJ_CASES_THEN2
     ASSUME_TAC
     (fun th -> REWRITE_TAC[th; ENSURES_N_TRIVIAL] THEN NO_TAC)
     (SPECL [k; m] pth);;

let EVENTUALLY_EVENTUALLY_N = prove(
  `!(step:S->S->bool). (!x y z. step x y /\ step x z ==> y = z) ==>
   !P s. eventually step P s ==> ?n. eventually_n step n P s`,
  GEN_TAC THEN DISCH_TAC THEN GEN_TAC THEN
  MATCH_MP_TAC eventually_INDUCT THEN
  CONJ_TAC THENL [
    REPEAT STRIP_TAC THEN EXISTS_TAC `0` THEN
    ASM_REWRITE_TAC[EVENTUALLY_N_TRIVIAL];
    INTRO_TAC "!s; (@s'. HS) IH" THEN
    REMOVE_THEN "IH" (fun ih -> USE_THEN "HS" (CHOOSE_TAC o MATCH_MP ih)) THEN
    EXISTS_TAC `1 + n` THEN
    ASM_MESON_TAC[EVENTUALLY_N_STEP]]);;

let ENSURES_ENSURES_N = prove(
  `!(step:S->S->bool) P Q C. (!x y z. step x y /\ step x z ==> y = z) ==>
    ensures step P Q C ==> ?fn. ensures_n step P Q C fn`,
  REWRITE_TAC[ensures; ensures_n; GSYM SKOLEM_THM_GEN] THEN
  SEQ_IMP_REWRITE_TAC[EVENTUALLY_EVENTUALLY_N] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Classic precondition strengthening and postcondition weakening.           *)
(* Implement also (essentially trivial) tactics to apply it.                 *)
(* ------------------------------------------------------------------------- *)

let ENSURES_N_PRECONDITION_THM_GEN = prove
 (`!P P' C C' Q fn.
        (!x. P' x ==> P x) /\
        (!x y. C x y ==> C' x y) /\
        ensures_n step P Q C fn
        ==> ensures_n step P' Q C' fn`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures_n] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[ensures_n] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_N_MONO) THEN
  ASM_SIMP_TAC[]);;

let ENSURES_N_PRECONDITION_THM = prove
 (`!P P' C Q fn.
        (!x. P' x ==> P x) /\
        ensures_n step P Q C fn
        ==> ensures_n step P' Q C fn`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures_n] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[ensures_n] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[]);;

let ENSURES_N_PRECONDITION_TAC p' =
  MATCH_MP_TAC ENSURES_N_PRECONDITION_THM THEN EXISTS_TAC p';;

let ENSURES_N_POSTCONDITION_THM_GEN = prove
 (`!P C C' Q Q' fn.
        (!x. Q x ==> Q' x) /\
        (!x y. C x y ==> C' x y) /\
        ensures_n step P Q C fn
        ==> ensures_n step P Q' C' fn`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[ensures_n] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_N_MONO) THEN
  ASM_SIMP_TAC[]);;

let ENSURES_N_POSTCONDITION_THM = prove
 (`!P C Q Q' fn.
        (!x. Q x ==> Q' x) /\
        ensures_n step P Q C fn
        ==> ensures_n step P Q' C fn`,
  REPEAT GEN_TAC THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[ensures_n] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_N_MONO) THEN
  ASM_SIMP_TAC[]);;

let ENSURES_N_POSTCONDITION_TAC q' =
  MATCH_MP_TAC ENSURES_N_POSTCONDITION_THM THEN EXISTS_TAC q';;

let ENSURES_N_PREPOSTCONDITION_THM = prove
 (`!P P' C Q Q' fn.
        (!x. P' x ==> P x) /\ (!x. Q x ==> Q' x) /\
        ensures_n step P Q C fn
        ==> ensures_n step P' Q' C fn`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures_n] THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[ensures_n] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
  MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_N_MONO) THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The analogous monotonicity result for the frame.                          *)
(* ------------------------------------------------------------------------- *)

let ENSURES_N_FRAME_MONO = prove
 (`!P Q C C' fn.
        (!x y. C x y ==> C' x y) /\
        ensures_n step P Q C fn
        ==> ensures_n step P Q C' fn`,
   REPEAT GEN_TAC THEN
   REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
   REWRITE_TAC[ensures_n] THEN MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
   MATCH_MP_TAC MONO_IMP THEN REWRITE_TAC[] THEN
   ASM_REWRITE_TAC[] THEN
   MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM] EVENTUALLY_N_MONO) THEN
   ASM_SIMP_TAC[]);;
 
let ENSURES_N_FRAME_SUBSUMED = prove
 (`!P Q C C' fn.
        C subsumed C' /\
        ensures_n step P Q C fn
        ==> ensures_n step P Q C' fn`,
   REWRITE_TAC[subsumed; ENSURES_N_FRAME_MONO]);;

(* ------------------------------------------------------------------------- *)
(* Classic Hoare sequencing / Transitivity rule.                             *)
(* ------------------------------------------------------------------------- *)

let ENSURES_N_TRANS = prove(
  `!step (P:S->bool) (Q:S->bool) (R:S->bool) C1 C2 n1 n2.
    ensures_n step P Q C1 (\s. n1) /\ ensures_n step Q R C2 (\s. n2)
    ==> ensures_n step P R (C1 ,, C2) (\s. n1 + n2)`,
  REWRITE_TAC [ensures_n; eventually_n] THEN
  REPEAT_N 11 STRIP_TAC THEN
  CONJ_TAC THENL [
    ASM_MESON_TAC [STEPS_ADD; seq];
    REPEAT STRIP_TAC THEN
    DISJ_CASES_TAC (ARITH_RULE `n' < n1 \/ n' >= n1`) THENL [
      ASM_MESON_TAC [];
      FIRST_X_ASSUM (fun th -> CHOOSE_THEN ASSUME_TAC (REWRITE_RULE [GE; LE_EXISTS] th)) THEN
      ASM_MESON_TAC [LT_ADD_LCANCEL; STEPS_ADD]]]);;

let ENSURES_N_TRANS_SIMPLE = prove(
  `!step (P:S->bool) (Q:S->bool) (R:S->bool) C n1 n2.
    C ,, C = C /\
    ensures_n step P Q C (\s. n1) /\ ensures_n step Q R C (\s. n2)
    ==> ensures_n step P R C (\s. n1 + n2)`,
  MESON_TAC[ENSURES_N_TRANS]);;

let ENSURES_N_SEQUENCE_TAC =
  let pth = prove
   (`!program_decodes pcounter pc' Q n1 n2.
        C ,, C = C /\
        ensures_n step (\s. program_decodes s /\
                          read pcounter s = word pc'' /\
                          P s)
                       (\s. program_decodes s /\
                          read pcounter s = word pc' /\
                          Q s)
                       C (\s. n1) /\
        ensures_n step (\s. program_decodes s /\
                          read pcounter s = word pc' /\
                          Q s)
                       R C (\s. n2)
        ==> ensures_n step (\s. program_decodes s /\
                              read pcounter s = word pc'' /\
                              P s)
                           R C (\s. n1 + n2)`,
    REWRITE_TAC[ENSURES_N_TRANS_SIMPLE]) in
  let tac = MATCH_MP_TAC pth in
  fun n q -> (tac THEN MAP_EVERY EXISTS_TAC [n;q] THEN BETA_TAC THEN
              CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Induction, basically a variant of the usual WHILE rule with a             *)
(* test at the end. Versions for up from 0...k-1, down from k-1...0 and up   *)
(* from a...b-1.                                                             *)
(* ------------------------------------------------------------------------- *)

let ENSURES_N_WHILE_UP_TAC, ENSURES_N_WHILE_DOWN_TAC,
    ENSURES_N_WHILE_AUP_TAC, ENSURES_N_WHILE_ADOWN_TAC =
  let pth = prove(
    `!k pc1 pc2 (loopinvariant:num->A->bool) nsteps_pre f_nsteps nsteps_back nsteps_post.
      C ,, C = C /\ ~(k = 0) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant 0 s)
        C (\s. nsteps_pre) /\
      (!i. i < k /\ ~(i = k) /\ ~(k = 0) /\ 0 < k
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant i s)
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant (i + 1) s)
          C (\s. f_nsteps i)) /\
      (!i. 0 < i /\ i < k /\ ~(i = k) /\ ~(i = 0) /\ ~(k = 0) /\ 0 < k
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant i s)
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant i s)
          C (\s. nsteps_back)) /\
      ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant k s)
          postcondition C (\s. nsteps_post) /\
      nsteps = nsteps_pre + (nsum (0..(k-1)) (\i. f_nsteps i) + (k-1) * nsteps_back) + nsteps_post
      ==>
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        postcondition C (\s. nsteps)`,
    REPEAT STRIP_TAC THEN
    CHOOSE_THEN ASSUME_TAC (GSYM (ISPEC `nsum (0..(k-1)) (\i. f_nsteps i) + (k-1) * nsteps_back` EXISTS_REFL)) THEN
    IMP_REWRITE_TAC [ENSURES_N_TRANS_SIMPLE] THEN
    UNDISCH_THEN `nsum (0..k - 1) (\i. f_nsteps i) + (k - 1) * nsteps_back = x` (fun th -> REWRITE_TAC [SYM th]) THEN
    FIRST_ASSUM (SUBST1_TAC o MATCH_MP (ARITH_RULE `~(k = 0) ==> k = (k - 1) + 1`)) THEN
    UNDISCH_THEN `~(k = 0)` (MP_TAC o MATCH_MP (ARITH_RULE `~(k = 0) ==> k - 1 < k`)) THEN
    SPEC_TAC (`k-1:num`,`j:num`) THEN
    REWRITE_TAC [ARITH_RULE `(j + 1) - 1 = j`] THEN
    INDUCT_TAC THENL [
      STRIP_TAC THEN REWRITE_TAC [NSUM_SING_NUMSEG; ADD_0; MULT] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o SPEC `0`) THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC [NSUM_CLAUSES_NUMSEG; ADD1; ARITH_RULE `0 <= j + 1`] THEN
      ASM_REWRITE_TAC [ARITH_RULE `(nsum (0..j) (\i. f_nsteps i) + f_nsteps (j + 1)) + (j + 1) * nsteps_back = (nsum (0..j) (\i. f_nsteps i) + (j * nsteps_back)) + f_nsteps (j + 1) + nsteps_back`] THEN
      STRIP_TAC THEN
      MATCH_MP_TAC ENSURES_N_TRANS_SIMPLE THEN META_EXISTS_TAC THEN
      ASM_REWRITE_TAC [] THEN
      CONJ_TAC THENL [
        UNDISCH_THEN `j + 1 < k` (MP_TAC o MP (ARITH_RULE `j + 1 < k ==> j < k`)) THEN
        FIRST_X_ASSUM (UNIFY_ACCEPT_TAC [`Q:A->bool`]);
        SUBST1_TAC (ARITH_RULE `f_nsteps (j + 1) + nsteps_back = nsteps_back + f_nsteps (j + 1)`) THEN
        MATCH_MP_TAC ENSURES_N_TRANS_SIMPLE THEN META_EXISTS_TAC THEN
        ASM_REWRITE_TAC [] THEN
        CONJ_TAC THENL [
          UNDISCH_THEN `j + 1 < k` (MP_TAC o MP (ARITH_RULE `j + 1 < k ==> 0 < j + 1 /\ j + 1 < k /\ ~(j + 1 = k) /\ ~(j + 1 = 0) /\ ~(k = 0) /\ 0 < k`)) THEN
          FIRST_X_ASSUM (UNIFY_ACCEPT_TAC [`Q:A->bool`] o SPEC `j + 1`);
          UNDISCH_THEN `j + 1 < k` (MP_TAC o MP (ARITH_RULE `j + 1 < k ==> j + 1 < k /\ ~(j + 1 = k) /\ ~(k = 0) /\ 0 < k`)) THEN
          FIRST_X_ASSUM (UNIFY_ACCEPT_TAC [`Q:A->bool`] o SPEC `j + 1`)]]]) in
  let qth = prove(
    `!k pc1 pc2 (loopinvariant:num->A->bool) nsteps_pre f_nsteps nsteps_back nsteps_post.
      C ,, C = C /\ ~(k = 0) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant k s)
        C (\s. nsteps_pre) /\
      (!i. i < k /\ ~(i = k) /\ ~(k = 0) /\ 0 < k
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant (i + 1) s)
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant i s)
          C (\s. f_nsteps i)) /\
      (!i. 0 < i /\ i < k /\ ~(i = k) /\ ~(i = 0) /\ ~(k = 0) /\ 0 < k
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant i s)
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant i s)
          C (\s. nsteps_back)) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant 0 s)
        postcondition C (\s. nsteps_post) /\
      nsteps = nsteps_pre + (nsum (0..(k-1)) (\i. f_nsteps i) + (k-1) * nsteps_back) + nsteps_post
      ==>
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        postcondition C (\s. nsteps)`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `pc1:num`; `pc2:num`; `\i. (loopinvariant:num->A->bool) (k - i)`; `nsteps_pre:num`; `\i. (f_nsteps:num->num) (k - (i + 1))`; `nsteps_back:num`; `nsteps_post:num`] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[SUB_0; SUB_REFL] THEN
    REPEAT (MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN REWRITE_TAC[]) THENL [
      DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `k - (i + 1)`) THEN
      ASM_SIMP_TAC [ARITH_RULE `i < k ==> k - (i + 1) + 1 = k - i`] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC [ARITH_RULE `k - (i + 1) = (k - 1) - i`; NSUM_REFLECT'; ETA_AX]]) in
  let rth = prove(
    `!a b pc1 pc2 (loopinvariant:num->A->bool) nsteps_pre f_nsteps nsteps_back nsteps_post.
      C ,, C = C /\ a < b /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant a s)
        C (\s. nsteps_pre) /\
      (!i. a <= i /\ i < b /\ ~(i = b) /\ ~(b = 0) /\ 0 < b
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant i s)
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant (i + 1) s)
          C (\s. f_nsteps i)) /\
      (!i. a < i /\ i < b /\ ~(i = b) /\ ~(i = 0) /\ ~(i = a) /\ ~(b = 0) /\ 0 < b
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant i s)
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant i s)
          C (\s. nsteps_back)) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant b s)
        postcondition C (\s. nsteps_post) /\
      nsteps = nsteps_pre + (nsum(a..(b-1)) (\i. f_nsteps i) + (b-1-a) * nsteps_back) + nsteps_post
      ==>
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        postcondition C (\s. nsteps)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [`b - a:num`; `pc1:num`; `pc2:num`; `\i. (loopinvariant:num->A->bool) (a + i)`; `nsteps_pre:num`; `\i. (f_nsteps:num->num) (a + i)`; `nsteps_back:num`; `nsteps_post:num`] THEN
    ASM_REWRITE_TAC [SUB_EQ_0; NOT_LE; ADD_CLAUSES] THEN
    ASM_SIMP_TAC [ARITH_RULE `a:num < b ==> a + b - a = b`] THEN
    REWRITE_TAC [ADD_ASSOC] THEN REPEAT STRIP_TAC THENL [
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC [ARITH_RULE `b - a - 1 = b - 1 - a`] THEN
      ONCE_ASM_REWRITE_TAC [MATCH_MP NSUM_OFFSET_0 (MP (ARITH_RULE `a < b ==> a <= b - 1`) (ASSUME `a < b`))] THEN
      ASM_REWRITE_TAC [ADD_SYM]]) in
  let sth = prove(
    `!a b pc1 pc2 (loopinvariant:num->A->bool) nsteps_pre f_nsteps nsteps_back nsteps_post.
      C ,, C = C /\ a < b /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant b s)
        C (\s. nsteps_pre) /\
      (!i. a <= i /\ i < b /\ ~(i = b) /\ ~(b = 0) /\ 0 < b
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant (i + 1) s)
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant i s)
          C (\s. f_nsteps i)) /\
      (!i. a < i /\ i < b /\ ~(i = a) /\ ~(i = 0) /\ ~(i = b) /\ ~(b = 0) /\ 0 < b
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant i s)
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant i s)
          C (\s. nsteps_back)) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant a s)
        postcondition C (\s. nsteps_post) /\
      nsteps = nsteps_pre + (nsum(a..(b-1)) (\i. f_nsteps i) + (b-1-a) * nsteps_back) + nsteps_post
      ==>
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        postcondition C (\s. nsteps)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC qth THEN
    MAP_EVERY EXISTS_TAC [`b - a:num`; `pc1:num`; `pc2:num`; `\i. (loopinvariant:num->A->bool) (a + i)`; `nsteps_pre:num`; `\i. (f_nsteps:num->num) (a + i)`; `nsteps_back:num`; `nsteps_post:num`] THEN
    ASM_REWRITE_TAC [SUB_EQ_0; NOT_LE; ADD_CLAUSES] THEN
    ASM_SIMP_TAC [ARITH_RULE `a:num < b ==> a + b - a = b`] THEN
    REWRITE_TAC [ADD_ASSOC] THEN REPEAT STRIP_TAC THENL [
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC [ARITH_RULE `b - a - 1 = b - 1 - a`] THEN
      ONCE_ASM_REWRITE_TAC [MATCH_MP NSUM_OFFSET_0 (MP (ARITH_RULE `a < b ==> a <= b - 1`) (ASSUME `a < b`))] THEN
      ASM_REWRITE_TAC [ADD_SYM]]) in
  (fun k pc1 pc2 iv f_nsteps nsteps_pre nsteps_back nsteps_post ->
    MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [k; pc1; pc2; iv; nsteps_pre; f_nsteps; nsteps_back; nsteps_post] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC'; ALL_TAC]),
  (fun k pc1 pc2 iv f_nsteps nsteps_pre nsteps_back nsteps_post ->
    MATCH_MP_TAC qth THEN
    MAP_EVERY EXISTS_TAC [k; pc1; pc2; iv; nsteps_pre; f_nsteps; nsteps_back; nsteps_post] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC'; ALL_TAC]),
  (fun a b pc1 pc2 iv f_nsteps nsteps_pre nsteps_back nsteps_post ->
    MATCH_MP_TAC rth THEN
    MAP_EVERY EXISTS_TAC [a; b; pc1; pc2; iv; nsteps_pre; f_nsteps; nsteps_back; nsteps_post] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC'; ALL_TAC]),
  (fun b a pc1 pc2 iv f_nsteps nsteps_pre nsteps_back nsteps_post ->
    MATCH_MP_TAC sth THEN
    MAP_EVERY EXISTS_TAC [a; b; pc1; pc2; iv; nsteps_pre; f_nsteps; nsteps_back; nsteps_post] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC'; ALL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Variants where there is an extra conjunct in the end state that may       *)
(* not hold at the outset of the zeroth iteration. This is mainly intended   *)
(* for cases where the last arithmetic operation sets flags that are then    *)
(* used to decide the branch.                                                *)
(* ------------------------------------------------------------------------- *)

let ENSURES_N_WHILE_PUP_TAC,ENSURES_N_WHILE_PDOWN_TAC,
    ENSURES_N_WHILE_PAUP_TAC,ENSURES_N_WHILE_PADOWN_TAC =
  let pth = prove(
    `!k pc1 pc2 p (q:num->A->bool) nsteps_pre f_nsteps nsteps_post.
      C ,, C = C /\ ~(k = 0) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ p 0 s)
        C (\s. nsteps_pre) /\
      (!i. i < k /\ ~(i = k) /\ ~(k = 0) /\ 0 < k
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ p i s)
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ p (i + 1) s /\ q (i + 1) s)
          C (\s. f_nsteps i)) /\
      (!i. 0 < i /\ i < k /\ ~(i = k) /\ ~(i = 0) /\ ~(k = 0) /\ 0 < k
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ p i s /\ q i s)
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ p i s)
          C (\s. 1)) /\
      ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ p k s /\ q k s)
          postcondition C (\s. nsteps_post) /\
      nsteps = nsteps_pre + (nsum (0..(k-1)) (\i. f_nsteps i) + (k-1)) + nsteps_post
      ==>
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        postcondition C (\s. nsteps)`,
    REPEAT STRIP_TAC THEN
    CHOOSE_THEN ASSUME_TAC (GSYM (ISPEC `nsum (0..(k-1)) (\i. f_nsteps i) + (k-1)` EXISTS_REFL)) THEN
    IMP_REWRITE_TAC [ENSURES_N_TRANS_SIMPLE] THEN
    UNDISCH_THEN `nsum (0..k - 1) (\i. f_nsteps i) + k - 1 = x` (fun th -> REWRITE_TAC [SYM th]) THEN
    FIRST_ASSUM (SUBST1_TAC o MATCH_MP (ARITH_RULE `~(k = 0) ==> k = (k - 1) + 1`)) THEN
    UNDISCH_THEN `~(k = 0)` (MP_TAC o MATCH_MP (ARITH_RULE `~(k = 0) ==> k - 1 < k`)) THEN
    SPEC_TAC (`k-1:num`,`j:num`) THEN
    REWRITE_TAC [ARITH_RULE `(j + 1) - 1 = j`] THEN
    INDUCT_TAC THENL [
      STRIP_TAC THEN REWRITE_TAC [NSUM_SING_NUMSEG; ADD_0] THEN
      FIRST_X_ASSUM (MATCH_MP_TAC o SPEC `0`) THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC [NSUM_CLAUSES_NUMSEG; ADD1; ARITH_RULE `0 <= j + 1`] THEN
      ASM_REWRITE_TAC [ARITH_RULE `(nsum (0..j) (\i. f_nsteps i) + f_nsteps (j + 1)) + j + 1 = (nsum (0..j) (\i. f_nsteps i) + j) + f_nsteps (j + 1) + 1`] THEN
      STRIP_TAC THEN
      MATCH_MP_TAC ENSURES_N_TRANS_SIMPLE THEN META_EXISTS_TAC THEN
      ASM_REWRITE_TAC [] THEN
      CONJ_TAC THENL [
        UNDISCH_THEN `j + 1 < k` (MP_TAC o MP (ARITH_RULE `j + 1 < k ==> j < k`)) THEN
        FIRST_X_ASSUM (UNIFY_ACCEPT_TAC [`Q:A->bool`]);
        SUBST1_TAC (ARITH_RULE `f_nsteps (j + 1) + 1 = 1 + f_nsteps (j + 1)`) THEN
        MATCH_MP_TAC ENSURES_N_TRANS_SIMPLE THEN META_EXISTS_TAC THEN
        ASM_REWRITE_TAC [] THEN
        CONJ_TAC THENL [
          UNDISCH_THEN `j + 1 < k` (MP_TAC o MP (ARITH_RULE `j + 1 < k ==> 0 < j + 1 /\ j + 1 < k /\ ~(j + 1 = k) /\ ~(j + 1 = 0) /\ ~(k = 0) /\ 0 < k`)) THEN
          FIRST_X_ASSUM (UNIFY_ACCEPT_TAC [`Q:A->bool`] o SPEC `j + 1`);
          UNDISCH_THEN `j + 1 < k` (MP_TAC o MP (ARITH_RULE `j + 1 < k ==> j + 1 < k /\ ~(j + 1 = k) /\ ~(k = 0) /\ 0 < k`)) THEN
          FIRST_X_ASSUM (UNIFY_ACCEPT_TAC [`Q:A->bool`] o SPEC `j + 1`)]]]) in
  let qth = prove(
    `!k pc1 pc2 p (q:num->A->bool) nsteps_pre f_nsteps nsteps_post.
      C ,, C = C /\ ~(k = 0) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ p k s)
        C (\s. nsteps_pre) /\
      (!i. i < k /\ ~(i = k) /\ ~(k = 0) /\ 0 < k
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ p (i + 1) s)
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ p i s /\ q i s)
          C (\s. f_nsteps i)) /\
      (!i. 0 < i /\ i < k /\ ~(i = k) /\ ~(i = 0) /\ ~(k = 0) /\ 0 < k
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ p i s /\ q i s)
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ p i s)
          C (\s. 1)) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc2 /\ p 0 s /\ q 0 s)
        postcondition C (\s. nsteps_post) /\
      nsteps = nsteps_pre + (nsum (0..(k-1)) (\i. f_nsteps i) + (k-1)) + nsteps_post
      ==>
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        postcondition C (\s. nsteps)`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `pc1:num`; `pc2:num`; `\i. (p:num->A->bool) (k - i)`; `\i. (q:num->A->bool) (k - i)`; `nsteps_pre:num`; `\i. (f_nsteps:num->num) (k - (i + 1))`; `nsteps_post:num`] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[SUB_0; SUB_REFL] THEN
    REPEAT (MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN REWRITE_TAC[]) THENL [
      DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `k - (i + 1)`) THEN
      ASM_SIMP_TAC [ARITH_RULE `i < k ==> k - (i + 1) + 1 = k - i`] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC [ARITH_RULE `k - (i + 1) = (k - 1) - i`; NSUM_REFLECT'; ETA_AX]]) in
  let rth = prove(
    `!a b pc1 pc2 p (q:num->A->bool) nsteps_pre f_nsteps nsteps_post.
      C ,, C = C /\ a < b /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ p a s)
        C (\s. nsteps_pre) /\
      (!i. a <= i /\ i < b /\ ~(i = b) /\ ~(b = 0) /\ 0 < b
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ p i s)
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ p (i + 1) s /\ q (i + 1) s)
          C (\s. f_nsteps i)) /\
      (!i. a < i /\ i < b /\ ~(i = b) /\ ~(i = 0) /\ ~(i = a) /\ ~(b = 0) /\ 0 < b
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ p i s /\ q i s)
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ p i s)
          C (\s. 1)) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc2 /\ p b s /\ q b s)
        postcondition C (\s. nsteps_post) /\
      nsteps = nsteps_pre + (nsum(a..(b-1)) (\i. f_nsteps i) + (b-1-a)) + nsteps_post
      ==>
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        postcondition C (\s. nsteps)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [`b - a:num`; `pc1:num`; `pc2:num`; `\i. (p:num->A->bool) (a + i)`; `\i. (q:num->A->bool) (a + i)`; `nsteps_pre:num`; `\i. (f_nsteps:num->num) (a + i)`; `nsteps_post:num`] THEN
    ASM_REWRITE_TAC [SUB_EQ_0; NOT_LE; ADD_CLAUSES] THEN
    ASM_SIMP_TAC [ARITH_RULE `a:num < b ==> a + b - a = b`] THEN
    REWRITE_TAC [ADD_ASSOC] THEN REPEAT STRIP_TAC THENL [
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC [ARITH_RULE `b - a - 1 = b - 1 - a`] THEN
      ONCE_ASM_REWRITE_TAC [MATCH_MP NSUM_OFFSET_0 (MP (ARITH_RULE `a < b ==> a <= b - 1`) (ASSUME `a < b`))] THEN
      ASM_REWRITE_TAC [ADD_SYM]]) in
  let sth = prove(
    `!a b pc1 pc2 p (q:num->A->bool) nsteps_pre f_nsteps nsteps_post.
      C ,, C = C /\ a < b /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ p b s)
        C (\s. nsteps_pre) /\
      (!i. a <= i /\ i < b /\ ~(i = b) /\ ~(b = 0) /\ 0 < b
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ p (i + 1) s)
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ p i s /\ q i s)
          C (\s. f_nsteps i)) /\
      (!i. a < i /\ i < b /\ ~(i = a) /\ ~(i = 0) /\ ~(i = b) /\ ~(b = 0) /\ 0 < b
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ p i s /\ q i s)
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ p i s)
          C (\s. 1)) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc2 /\ p a s /\ q a s)
        postcondition C (\s. nsteps_post) /\
      nsteps = nsteps_pre + (nsum(a..(b-1)) (\i. f_nsteps i) + (b-1-a)) + nsteps_post
      ==>
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        postcondition C (\s. nsteps)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC qth THEN
    MAP_EVERY EXISTS_TAC [`b - a:num`; `pc1:num`; `pc2:num`; `\i. (p:num->A->bool) (a + i)`; `\i. (q:num->A->bool) (a + i)`; `nsteps_pre:num`; `\i. (f_nsteps:num->num) (a + i)`; `nsteps_post:num`] THEN
    ASM_REWRITE_TAC [SUB_EQ_0; NOT_LE; ADD_CLAUSES] THEN
    ASM_SIMP_TAC [ARITH_RULE `a:num < b ==> a + b - a = b`] THEN
    REWRITE_TAC [ADD_ASSOC] THEN REPEAT STRIP_TAC THENL [
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REWRITE_TAC [ARITH_RULE `b - a - 1 = b - 1 - a`] THEN
      ONCE_ASM_REWRITE_TAC [MATCH_MP NSUM_OFFSET_0 (MP (ARITH_RULE `a < b ==> a <= b - 1`) (ASSUME `a < b`))] THEN
      ASM_REWRITE_TAC [ADD_SYM]]) in
  (fun k pc1 pc2 p q f_nsteps nsteps_pre nsteps_post ->
    MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [k; pc1; pc2; p; q; nsteps_pre; f_nsteps; nsteps_post] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC'; ALL_TAC]),
  (fun k pc1 pc2 p q f_nsteps nsteps_pre nsteps_post ->
    MATCH_MP_TAC qth THEN
    MAP_EVERY EXISTS_TAC [k; pc1; pc2; p; q; nsteps_pre; f_nsteps; nsteps_post] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC'; ALL_TAC]),
  (fun a b pc1 pc2 p q f_nsteps nsteps_pre nsteps_post ->
    MATCH_MP_TAC rth THEN
    MAP_EVERY EXISTS_TAC [a; b; pc1; pc2; p; q; nsteps_pre; f_nsteps; nsteps_post] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC'; ALL_TAC]),
  (fun b a pc1 pc2 p q f_nsteps nsteps_pre nsteps_post ->
    MATCH_MP_TAC sth THEN
    MAP_EVERY EXISTS_TAC [a; b; pc1; pc2; p; q; nsteps_pre; f_nsteps; nsteps_post] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC'; ALL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Introduce a new ghost variable for a state component in "ensures".        *)
(* ------------------------------------------------------------------------- *)

let GHOST_INTRO'_TAC =
  let pth = prove
   (`!f P step post frame fn.
         (!a. ensures_n step (\s. P s a /\ f s = a) post frame fn)
         ==> ensures_n step (\s. P s (f s)) post frame fn`,
    REPEAT GEN_TAC THEN REWRITE_TAC[ensures_n] THEN
    GEN_REWRITE_TAC LAND_CONV [SWAP_FORALL_THM] THEN
    REWRITE_TAC[IMP_CONJ_ALT; FORALL_UNWIND_THM1]) in
  fun t comp ->
    MP_TAC(ISPEC comp pth) THEN
    CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV BETA_CONV)) THEN
    DISCH_THEN MATCH_MP_TAC THEN X_GEN_TAC t THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o ABS_CONV o TOP_DEPTH_CONV)
     [GSYM CONJ_ASSOC];;

(* ------------------------------------------------------------------------- *)
(* A way of using a lemma for a subroutine or subcomponent.                  *)
(* Tactic supports the basic templating and leaves two user subgoals.        *)
(* ------------------------------------------------------------------------- *)

let ENSURES_N_SUBLEMMA_THM = prove
 (`!t (P:A->bool) Q R.
        (!s. P s ==> P' s) /\
        R' subsumed R /\
        (!s s'. P s /\ Q' s' /\ R' s s' ==> Q s')
        ==> ensures t P' Q' R' ==> ensures t P Q R`,
  REPEAT GEN_TAC THEN REWRITE_TAC[subsumed] THEN STRIP_TAC THEN
  REWRITE_TAC[ensures] THEN MATCH_MP_TAC MONO_FORALL THEN
  X_GEN_TAC `s:A` THEN DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM]
        EVENTUALLY_MONO) THEN
  ASM_MESON_TAC[]);;

let ENSURES_SUBLEMMA_TAC execth s0 s1 =
  MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [W(fun (asl,w) -> X_GEN_TAC(mk_var(s0,type_of(fst(dest_forall w))))) THEN
    STRIP_TAC;
    CONJ_TAC THENL [SUBSUMED_MAYCHANGE_TAC THEN NO_TAC; ALL_TAC] THEN
    W(fun (asl,w) -> X_GEN_TAC(mk_var(s0,type_of(fst(dest_forall w))))) THEN
    W(fun (asl,w) -> X_GEN_TAC(mk_var(s1,type_of(fst(dest_forall w))))) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
    REWRITE_TAC[GSYM SEQ_ASSOC] THEN
    REWRITE_TAC[ASSIGNS_SEQ] THEN REWRITE_TAC[ASSIGNS_THM] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
    NONSELFMODIFYING_STATE_UPDATE_TAC execth THEN
    ASSUMPTION_STATE_UPDATE_TAC THEN DISCH_THEN(K ALL_TAC)];;

(*** A version that also tries nonmodification for subroutines ***)

let ENSURES_SUBSUBLEMMA_TAC (execth::subths) s0 s1 =
  MATCH_MP_TAC ENSURES_SUBLEMMA_THM THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [W(fun (asl,w) -> X_GEN_TAC(mk_var(s0,type_of(fst(dest_forall w))))) THEN
    STRIP_TAC;
    CONJ_TAC THENL [SUBSUMED_MAYCHANGE_TAC THEN NO_TAC; ALL_TAC] THEN
    W(fun (asl,w) -> X_GEN_TAC(mk_var(s0,type_of(fst(dest_forall w))))) THEN
    W(fun (asl,w) -> X_GEN_TAC(mk_var(s1,type_of(fst(dest_forall w))))) THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
    REWRITE_TAC[GSYM SEQ_ASSOC] THEN
    REWRITE_TAC[ASSIGNS_SEQ] THEN REWRITE_TAC[ASSIGNS_THM] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
    NONSELFMODIFYING_STATE_UPDATE_TAC execth THEN
    MAP_EVERY (TRY o NONSELFMODIFYING_STATE_UPDATE_TAC) subths THEN
    ASSUMPTION_STATE_UPDATE_TAC THEN DISCH_THEN(K ALL_TAC)];;

(* ------------------------------------------------------------------------- *)
(* A way of using a lemma for a subroutine or subcomponent.                  *)
(* Tactic supports the basic templating and leaves two user subgoals.        *)
(* ------------------------------------------------------------------------- *)

let ENSURES_N_SUBLEMMA_THM = prove
  (`!t (P:A->bool) Q R fn.
         (!s. P s ==> P' s) /\
         R' subsumed R /\
         (!s s'. P s /\ Q' s' /\ R' s s' ==> Q s')
         ==> ensures_n t P' Q' R' fn ==> ensures_n t P Q R fn`,
   REPEAT GEN_TAC THEN REWRITE_TAC[subsumed] THEN STRIP_TAC THEN
   REWRITE_TAC[ensures_n] THEN MATCH_MP_TAC MONO_FORALL THEN
   X_GEN_TAC `s:A` THEN DISCH_THEN(fun th -> DISCH_TAC THEN MP_TAC th) THEN
   ASM_SIMP_TAC[] THEN
   MATCH_MP_TAC(REWRITE_RULE[RIGHT_IMP_FORALL_THM]
         EVENTUALLY_N_MONO) THEN
   ASM_MESON_TAC[]);;

let ENSURES_N_ENSURES_TAC th =
  REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC ENSURES_N_ENSURES THEN META_EXISTS_TAC THEN
  MP_TAC (SPEC_ALL th) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN (UNIFY_ACCEPT_TAC [`f_n:armstate->num`]);;

(* ------------------------------------------------------------------------- *)
(* Scrub a "preserved" component from the MAYCHANGE list.                    *)
(* ------------------------------------------------------------------------- *)

let ENSURES_N_MAYCHANGE_PRESERVED = prove
 (`!(c:(A,B)component) t P Q R fn.
        extensionally_valid_component c /\
        (!s s'. R s s' ==> read c s' = read c s) /\
        (!d. ensures_n t (\s. P s /\ read c s = d)
                       (\s. Q s /\ read c s = d)
                       (R ,, MAYCHANGE [c]) fn)
        ==> ensures_n t P Q R fn`,
  REPEAT GEN_TAC THEN REWRITE_TAC[ensures_n; EXTENSIONALLY_VALID_COMPONENT] THEN
  STRIP_TAC THEN X_GEN_TAC `s0:A` THEN DISCH_TAC THEN
  ABBREV_TAC `d = read (c:(A,B)component) s0` THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`d:B`; `s0:A`]) THEN
  ASM_REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
  REWRITE_TAC[ASSIGNS_THM; seq] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s0:A`) THEN
  ABBREV_TAC `fr = (R:A->A->bool) s0` THEN DISCH_TAC THEN
  SPEC_TAC(`(fn:A->num) s0`,`n:num`) THEN SPEC_TAC(`s0:A`,`s0:A`) THEN
  MATCH_MP_TAC EVENTUALLY_N_MONO2 THEN
  X_GEN_TAC `s2:A` THEN REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `s1:A` THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_TAC `y:B`) THEN
  ASM_MESON_TAC[]);;

let ENSURES_N_PRESERVED_TAC pname ctm =
  MATCH_MP_TAC(ISPEC ctm ENSURES_N_MAYCHANGE_PRESERVED) THEN
  CONJ_TAC THENL [CONV_TAC EXTENSIONALLY_VALID_COMPONENT_CONV; ALL_TAC] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
    REWRITE_TAC[GSYM SEQ_ASSOC] THEN
    REWRITE_TAC[ASSIGNS_SEQ] THEN REWRITE_TAC[ASSIGNS_THM] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    CONV_TAC(LAND_CONV(DEPTH_CONV
     COMPONENT_READ_OVER_WRITE_ORTHOGONAL_CONV)) THEN
    REFL_TAC;
    REWRITE_TAC[GSYM CONJ_ASSOC; GSYM SEQ_ASSOC] THEN
    W(fun (asl,w) -> X_GEN_TAC(mk_var(pname,type_of(fst(dest_forall w)))))];;

let ENSURES_N_MAYCHANGE_EXISTING_PRESERVED = prove
 (`!(c:(A,B)component) d t P Q R fn.
        extensionally_valid_component c /\
        (!s s'. R s s' ==> read c s' = read c s) /\
        (!s. P s ==> read c s = d) /\
        ensures_n t P (\s. Q s /\ read c s = d) (R ,, MAYCHANGE [c]) fn
        ==> ensures_n t P Q R fn`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC ENSURES_N_MAYCHANGE_PRESERVED THEN
  EXISTS_TAC `c:(A,B)component` THEN ASM_REWRITE_TAC[] THEN
  ONCE_REWRITE_TAC[TAUT `p /\ q <=> ~(p ==> ~q)`] THEN
  ASM_SIMP_TAC[] THEN X_GEN_TAC `e:B` THEN
  ASM_CASES_TAC `e:B = d` THEN
  ASM_REWRITE_TAC[NOT_IMP; ENSURES_N_TRIVIAL; ETA_AX]);;

let ENSURES_N_EXISTING_PRESERVED_TAC ctm =
  W(fun (asl,w) ->
        MATCH_MP_TAC(ISPEC ctm ENSURES_N_MAYCHANGE_EXISTING_PRESERVED) THEN
        EXISTS_TAC(rand(find (fun e -> is_eq e && free_in ctm (lhand e))
                             (conjuncts(body(lhand(rator w))))))) THEN
  CONJ_TAC THENL [CONV_TAC EXTENSIONALLY_VALID_COMPONENT_CONV; ALL_TAC] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
    REWRITE_TAC[GSYM SEQ_ASSOC] THEN
    REWRITE_TAC[ASSIGNS_SEQ] THEN REWRITE_TAC[ASSIGNS_THM] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    CONV_TAC(LAND_CONV(DEPTH_CONV
     COMPONENT_READ_OVER_WRITE_ORTHOGONAL_CONV)) THEN
    REFL_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN NO_TAC;
    REWRITE_TAC[GSYM CONJ_ASSOC; GSYM SEQ_ASSOC]];;

(* ------------------------------------------------------------------------- *)
(* Refinment of ENSURES_PRESERVED_TAC for special D register handling.       *)
(* ------------------------------------------------------------------------- *)

let ENSURES_N_PRESERVED_DREG_TAC =
  let pth = prove
   (`read (Q8 :> bottomhalf) s = word_zx(read Q8 s) /\
     read (Q9 :> bottomhalf) s = word_zx (read Q9 s) /\
     read (Q10 :> bottomhalf) s = word_zx (read Q10 s) /\
     read (Q11 :> bottomhalf) s = word_zx (read Q11 s) /\
     read (Q12 :> bottomhalf) s = word_zx (read Q12 s) /\
     read (Q13 :> bottomhalf) s = word_zx (read Q13 s) /\
     read (Q14 :> bottomhalf) s = word_zx (read Q14 s) /\
     read (Q15 :> bottomhalf) s = word_zx (read Q15 s)`,
    CONV_TAC(ONCE_DEPTH_CONV COMPONENT_CANON_CONV) THEN
    REWRITE_TAC[READ_COMPONENT_COMPOSE; READ_ZEROTOP_64;
                bottomhalf; subword; read; FUN_EQ_THM] THEN
    REWRITE_TAC[word_zx; DIV_1; EXP; WORD_MOD_SIZE])
  and sth = prove
   (`valid_component c /\
     R ,, R = R /\
     MAYCHANGE [c :> tophalf] subsumed R /\
     ensures_n step P Q (R ,, MAYCHANGE [c]) fn
     ==> ensures_n step P Q (R ,, MAYCHANGE [c :> bottomhalf]) fn`,
    REWRITE_TAC[MAYCHANGE_SING] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] ENSURES_N_FRAME_SUBSUMED) THEN
    FIRST_ASSUM(fun th ->
      GEN_REWRITE_TAC (RAND_CONV o ONCE_DEPTH_CONV) [SYM th]) THEN
    REWRITE_TAC[GSYM SEQ_ASSOC] THEN MATCH_MP_TAC SUBSUMED_SEQ THEN
    REWRITE_TAC[SUBSUMED_REFL] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP ASSIGNS_TOPHALF_BOTTOMHALF) THEN
    MATCH_MP_TAC SUBSUMED_SEQ THEN ASM_REWRITE_TAC[SUBSUMED_REFL]) in
  let alist = zip [`D8`; `D9`; `D10`; `D11`; `D12`; `D13`; `D14`; `D15`]
                  (map (lhand o lhand o concl) (CONJUNCTS pth)) in
  let dregs = map fst alist in
  fun pname ctm ->
    if not (mem ctm dregs) then ENSURES_N_PRESERVED_TAC pname ctm else
    let ctm' = assoc ctm alist in
    ENSURES_N_PRESERVED_TAC pname ctm' THEN REWRITE_TAC[pth] THEN
    TRY(REWRITE_TAC[SEQ_ASSOC] THEN MATCH_MP_TAC sth THEN
        CONJ_TAC THENL [CONV_TAC VALID_COMPONENT_CONV; ALL_TAC] THEN
        CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC; ALL_TAC] THEN
        CONJ_TAC THENL [SUBSUMED_MAYCHANGE_TAC THEN NO_TAC; ALL_TAC] THEN
        REWRITE_TAC[GSYM SEQ_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Induction, a variant of the above WHILE loop tactics where the loop body  *)
(* and backedge proofs are combined.                                         *)
(* ------------------------------------------------------------------------- *)

let ENSURES_N_WHILE_UP_TAC, ENSURES_N_WHILE_DOWN_TAC,
    ENSURES_N_WHILE_AUP_TAC, ENSURES_N_WHILE_ADOWN_TAC =
  let pth = prove(
    `!k pc1 pc2 (loopinvariant:num->A->bool) nsteps_pre f_nsteps nsteps_post.
      C ,, C = C /\ ~(k = 0) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant 0 s)
        C (\s. nsteps_pre) /\
      (!i. i < k /\ ~(i = k) /\ ~(k = 0) /\ 0 < k
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant i s)
          (\s. program_decodes s /\ read pcounter s = word (if i + 1 < k then pc1 else pc2) /\ loopinvariant (i + 1) s)
          C (\s. f_nsteps i)) /\
      ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant k s)
          postcondition C (\s. nsteps_post) /\
      nsteps = nsteps_pre + nsum (0..(k-1)) (\i. f_nsteps i) + nsteps_post
      ==>
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        postcondition C (\s. nsteps)`,
    REPEAT STRIP_TAC THEN
    IMP_REWRITE_TAC [ENSURES_N_TRANS_SIMPLE] THEN
    DISJ_CASES_TAC (SPEC `k = 0 + 1` EXCLUDED_MIDDLE) THENL [
      ASM_REWRITE_TAC[ARITH_RULE `(0 + 1) - 1 = 0`; NSUM_CLAUSES_NUMSEG] THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `0`) THEN
      ASM_REWRITE_TAC[ARITH_RULE `0 < 0 + 1 /\ ~(0 + 1 < 0 + 1)`];
      ALL_TAC] THEN
    SUBGOAL_THEN `k - 1 = SUC (k - 1 - 1)` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `0 <= SUC (k - 1 - 1)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG] THEN
    IMP_REWRITE_TAC [ENSURES_N_TRANS_SIMPLE] THEN
    META_EXISTS_TAC THEN CONJ_TAC THENL [
      ALL_TAC;
      FIRST_X_ASSUM (MP_TAC o SPEC `k:num - 1`) THEN
      SUBGOAL_THEN `k - 1 < k /\ 0 < k /\ ~(k - 1 = k) /\ k - 1 + 1 = k /\ ~(k < k) /\ SUC (k - 1 - 1) = k - 1` (fun th -> ASM_REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN (UNIFY_ACCEPT_TAC [`Q:A->bool`])] THEN
    SUBGOAL_THEN `k - 1 - 1 = k - 2 /\ k - 1 = (k - 2) + 1` (fun th -> ONCE_REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `k - 2 < k - 1` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SPEC_TAC (`k - 2:num`,`j:num`) THEN
    INDUCT_TAC THENL [
      STRIP_TAC THEN REWRITE_TAC[NSUM_SING_NUMSEG; ADD_0; MULT] THEN
      SUBGOAL_THEN `0 < k /\ 0 + 1 < k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `0`) THEN ASM_REWRITE_TAC[];
      STRIP_TAC THEN ASM_REWRITE_TAC[NSUM_CLAUSES_NUMSEG; ADD1; ARITH_RULE `0 <= j + 1`] THEN
      IMP_REWRITE_TAC [ENSURES_N_TRANS_SIMPLE] THEN
      META_EXISTS_TAC THEN CONJ_TAC THENL [
        UNDISCH_THEN `SUC j < k - 1` (MP_TAC o MP (ARITH_RULE `SUC j < k - 1 ==> j < k - 1`)) THEN
        FIRST_X_ASSUM (UNIFY_ACCEPT_TAC [`Q:A->bool`]);
        FIRST_X_ASSUM (MP_TAC o SPEC `j + 1`) THEN
        SUBGOAL_THEN `(j + 1) + 1 < k /\ j + 1 < k /\ ~(j + 1 = k) /\ 0 < k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[]]]) in
  let qth = prove(
    `!k pc1 pc2 (loopinvariant:num->A->bool) nsteps_pre f_nsteps nsteps_post.
      C ,, C = C /\ ~(k = 0) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant k s)
        C (\s. nsteps_pre) /\
      (!i. i < k /\ ~(i = k) /\ ~(k = 0) /\ 0 < k
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant (i + 1) s)
          (\s. program_decodes s /\ read pcounter s = word (if i > 0 then pc1 else pc2) /\ loopinvariant i s)
          C (\s. f_nsteps i)) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant 0 s)
        postcondition C (\s. nsteps_post) /\
      nsteps = nsteps_pre + nsum (0..(k-1)) (\i. f_nsteps i) + nsteps_post
      ==>
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        postcondition C (\s. nsteps)`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `pc1:num`; `pc2:num`; `\i. (loopinvariant:num->A->bool) (k - i)`; `nsteps_pre:num`; `\i. (f_nsteps:num->num) (k - (i + 1))`; `nsteps_post:num`] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[SUB_0; SUB_REFL] THEN
    REPEAT (MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN REWRITE_TAC[]) THENL [
      DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `k - (i + 1)`) THEN
      ASM_SIMP_TAC[ARITH_RULE `i < k ==> k - (i + 1) + 1 = k - i /\ (k - (i + 1) > 0 <=> i + 1 < k)`] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ASM_REWRITE_TAC[ARITH_RULE `k - (i + 1) = (k - 1) - i`; NSUM_REFLECT'; ETA_AX]]) in
  let rth = prove(
    `!a b pc1 pc2 (loopinvariant:num->A->bool) nsteps_pre f_nsteps nsteps_post.
      C ,, C = C /\ a < b /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant a s)
        C (\s. nsteps_pre) /\
      (!i. a <= i /\ i < b /\ ~(i = b) /\ ~(b = 0) /\ 0 < b
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant i s)
          (\s. program_decodes s /\ read pcounter s = word (if i + 1 < b then pc1 else pc2) /\ loopinvariant (i + 1) s)
          C (\s. f_nsteps i)) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant b s)
        postcondition C (\s. nsteps_post) /\
      nsteps = nsteps_pre + nsum(a..(b-1)) (\i. f_nsteps i) + nsteps_post
      ==>
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        postcondition C (\s. nsteps)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [`b - a`; `pc1:num`; `pc2:num`; `\i. (loopinvariant:num->A->bool) (a + i)`; `nsteps_pre:num`; `\i. (f_nsteps:num->num) (a + i)`; `nsteps_post:num`] THEN
    ASM_REWRITE_TAC [SUB_EQ_0; NOT_LE; ADD_CLAUSES] THEN
    ASM_SIMP_TAC [ARITH_RULE `a < b ==> a + b - a = b`] THEN
    REWRITE_TAC [ADD_ASSOC] THEN STRIP_TAC THENL [
      GEN_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC `a + i`) THEN
      REWRITE_TAC[ARITH_RULE `(a + i) + 1 < b <=> i + 1 < b - a`] THEN
      DISCH_THEN (fun th -> IMP_REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
      REWRITE_TAC [ARITH_RULE `b - a - 1 = b - 1 - a`] THEN
      ONCE_ASM_REWRITE_TAC [MATCH_MP NSUM_OFFSET_0 (MP (ARITH_RULE `a < b ==> a <= b - 1`) (ASSUME `a < b`))] THEN
      ASM_REWRITE_TAC [ADD_SYM]]) in
  let sth = prove(
    `!a b pc1 pc2 (loopinvariant:num->A->bool) nsteps_pre f_nsteps nsteps_post.
      C ,, C = C /\ a < b /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant b s)
        C (\s. nsteps_pre) /\
      (!i. a <= i /\ i < b /\ ~(i = b) /\ ~(b = 0) /\ 0 < b
        ==>
        ensures_n step
          (\s. program_decodes s /\ read pcounter s = word pc1 /\ loopinvariant (i + 1) s)
          (\s. program_decodes s /\ read pcounter s = word (if i > a then pc1 else pc2) /\ loopinvariant i s)
          C (\s. f_nsteps i)) /\
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc2 /\ loopinvariant a s)
        postcondition C (\s. nsteps_post) /\
      nsteps = nsteps_pre + nsum(a..(b-1)) (\i. f_nsteps i) + nsteps_post
      ==>
      ensures_n step
        (\s. program_decodes s /\ read pcounter s = word pc /\ precondition s)
        postcondition C (\s. nsteps)`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC qth THEN
    MAP_EVERY EXISTS_TAC [`b - a`; `pc1:num`; `pc2:num`; `\i. (loopinvariant:num->A->bool) (a + i)`; `nsteps_pre:num`; `\i. (f_nsteps:num->num) (a + i)`; `nsteps_post:num`] THEN
    ASM_REWRITE_TAC [SUB_EQ_0; NOT_LE; ADD_CLAUSES] THEN
    ASM_SIMP_TAC [ARITH_RULE `a < b ==> a + b - a = b`] THEN
    REWRITE_TAC [ADD_ASSOC] THEN STRIP_TAC THENL [
      GEN_TAC THEN FIRST_X_ASSUM (MP_TAC o SPEC `a + i`) THEN
      REWRITE_TAC[ARITH_RULE `a + i > a <=> i > 0`] THEN
      DISCH_THEN (fun th -> IMP_REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
      REWRITE_TAC [ARITH_RULE `b - a - 1 = b - 1 - a`] THEN
      ONCE_ASM_REWRITE_TAC [MATCH_MP NSUM_OFFSET_0 (MP (ARITH_RULE `a < b ==> a <= b - 1`) (ASSUME `a < b`))] THEN
      ASM_REWRITE_TAC [ADD_SYM]]) in
  (fun k pc1 pc2 iv f_nsteps nsteps_pre nsteps_post ->
    MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [k; pc1; pc2; iv; nsteps_pre; f_nsteps; nsteps_post] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC'; ALL_TAC]),
  (fun k pc1 pc2 iv f_nsteps nsteps_pre nsteps_post ->
    MATCH_MP_TAC qth THEN
    MAP_EVERY EXISTS_TAC [k; pc1; pc2; iv; nsteps_pre; f_nsteps; nsteps_post] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC'; ALL_TAC]),
  (fun a b pc1 pc2 iv f_nsteps nsteps_pre nsteps_post ->
    MATCH_MP_TAC rth THEN
    MAP_EVERY EXISTS_TAC [a; b; pc1; pc2; iv; nsteps_pre; f_nsteps; nsteps_post] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC'; ALL_TAC]),
  (fun b a pc1 pc2 iv f_nsteps nsteps_pre nsteps_post ->
    MATCH_MP_TAC sth THEN
    MAP_EVERY EXISTS_TAC [a; b; pc1; pc2; iv; nsteps_pre; f_nsteps; nsteps_post] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [MAYCHANGE_IDEMPOT_TAC'; ALL_TAC]);;
