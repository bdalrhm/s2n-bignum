needs "common/relational.ml";;
needs "common/relational2.ml";;
needs "common/relational_n.ml";;

let lock = new_definition(`lock (step:S->S->bool) (s1, s2) (s1', s2') <=> step s1 s1' /\ step s2 s2'`);;

let LOCK_DEF = prove(
  `!step s s'. lock (step:S->S->bool) s s' <=> step (FST s) (FST s') /\ step (SND s) (SND s')`,
  REWRITE_TAC[FORALL_PAIR_THM; lock]);;

let lock_unique_lift = prove(
  `!step:S->S->bool. (!x y z. step x y /\ step x z ==> y = z) ==> !x y z. lock step x y /\ lock step x z ==> y = z`,
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MESON_TAC[lock]);;

let LOCK_STEPS_IS_PROD_OF_STEPS = prove(
  `!step:S->S->bool n s1 s2 s1' s2'. steps (lock step) n (s1, s2) (s1', s2') <=> steps step n s1 s1' /\ steps step n s2 s2'`,
  GEN_TAC THEN INDUCT_TAC THENL [
    SIMP_TAC[STEPS_TRIVIAL; PAIR_EQ];
    REWRITE_TAC[ARITH_RULE `SUC n = 1 + n`; STEPS_STEP; EXISTS_PAIR_THM; lock] THEN
    ASM_MESON_TAC[]]);;

let LEVENTUALLY_N_IS_NESTED_EVENTUALLY_N = prove(
  `!step:S->S->bool. (!x y z. step x y /\ step x z ==> y = z) ==>
   !n P s1 s2. eventually_n (lock step) n P (s1, s2) <=> eventually_n step n (\s1'. eventually_n step n (\s2'. P (s1',s2')) s2) s1`,
  GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THENL [
    REWRITE_TAC[EVENTUALLY_N_TRIVIAL];
    REPEAT GEN_TAC THEN
    REWRITE_TAC[ARITH_RULE `SUC n = 1 + n`; FORALL_PAIR_THM; EXISTS_PAIR_THM; EVENTUALLY_N_STEP; lock; GSYM EVENTUALLY_N_P_INOUT] THEN
    REWRITE_TAC[MESON[] `((?x:A. P x) /\ !x. P x ==> Q /\ R x) <=> (?x. P x) /\ Q /\ !x. P x ==> R x`] THEN
    EQ_TAC THENL [
      INTRO_TAC "(@s1' s2'. H1 H2) H" THEN
      REMOVE_THEN "H" MP_TAC THEN
      SUBGOAL_THEN `!P. (!s'. (step:S->S->bool) s2 s' ==> P s') <=> P s2'` (fun th -> REWRITE_TAC[th]) THENL [
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      ASM_MESON_TAC[];
      INTRO_TAC "(@s1'. H1) (@s2'. H2) H" THEN
      REMOVE_THEN "H" MP_TAC THEN
      SUBGOAL_THEN `!P. (!s'. (step:S->S->bool) s2 s' ==> P s') <=> P s2'` (fun th -> REWRITE_TAC[th]) THENL [
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      ASM_MESON_TAC[]]]);;

(* A slightly more powerful version of ensures2. *)
let ensures2' = new_definition
  `ensures2' (step:S->S->bool) (precond:S#S->bool) (postcond:S#S->bool) (frame:S#S->S#S->bool)
            (step_calc1:S#S->num) (step_calc2:S#S->num) <=>
  !(s1:S) (s2:S). precond (s1,s2)
      ==> eventually_n step (step_calc1 (s1,s2))
            (\s1'. eventually_n step (step_calc2 (s1,s2))
                (\s2'. postcond (s1',s2') /\ frame (s1,s2) (s1',s2')) s2) s1`;;

let LENSURES_N_IS_ENSURES2 = prove(
  `!step:S->S->bool. (!x y z. step x y /\ step x z ==> y = z) ==>
   !P Q C fn. ensures_n (lock step) P Q C fn <=> ensures2' step P Q C fn fn`,
  REWRITE_TAC[ensures_n; ensures2'; FORALL_PAIR_THM; LAMBDA_PAIR_THM] THEN
  IMP_REWRITE_TAC[LEVENTUALLY_N_IS_NESTED_EVENTUALLY_N] THEN
  REWRITE_TAC[] THEN MESON_TAC[]);;

let LESNURES_IS_ENSURES2 = prove(
  `!step:S->S->bool P Q C. (!x y z. step x y /\ step x z ==> y = z) ==>
    ensures (lock step) P Q C ==> ?fn. ensures2' step P Q C fn fn`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?fn:S#S->num. ensures_n (lock step) P Q C fn` CHOOSE_TAC THENL [
    SEQ_IMP_REWRITE_TAC[ENSURES_ENSURES_N; lock_unique_lift];
    ALL_TAC] THEN
  EXISTS_TAC `fn:S#S->num` THEN
  IMP_REWRITE_TAC[GSYM LENSURES_N_IS_ENSURES2]);;


(* A lock-step relational hoare triple version of ENSURES_INIT_TAC. *)
let LENSURES_INIT_TAC sname =
  let s_ty = `:S#S` in
  let sv = mk_var(sname, s_ty)
  and pair_fst = `FST:S#S->S`
  and pair_snd = `SND:S#S->S` in
  ENSURES_INIT_TAC sname THEN
  FIRST_X_ASSUM ((fun th -> ALL_TAC) o check(maychange_term o concl)) THEN
  MAP_EVERY (ASSUME_TAC o Fun.flip ISPEC MAYCHANGE_STARTER) [mk_icomb(pair_fst, sv); mk_icomb(pair_snd, sv)];;

(* ------------------------------------------------------------------------- *)
(* Update unaffected assumptions.                                            *)
(* ------------------------------------------------------------------------- *)

let LSTATE_UPDATE_TAC uth =
  let utm,s' = dest_eq(concl uth) in
  let s = mk_comb (rator s', (repeat rand utm)) in
  let is_stateread tm =
    match tm with
     Comb(Comb(Const("read",_),_),t) -> t = s
    | _ -> false in
  let thack rtm ttac th =
    let rtm' = mk_comb(rator rtm,utm) in
    SUBGOAL_THEN (mk_eq(rtm',rtm)) MP_TAC THENL
     [READ_OVER_WRITE_ORTHOGONAL_TAC; ALL_TAC] THEN
    DISCH_THEN(fun oth ->
       MP_TAC(TRANS (SYM oth) (AP_TERM (rator rtm) uth))) THEN
    DISCH_THEN(fun oth -> ASSUME_TAC(SUBS[oth] th)) in
  fun th ->
    let rtms = find_terms is_stateread (concl th) in
    if rtms = [] then ALL_TAC
    else EVERY_TCL (map thack rtms) ASSUME_TAC th;;

let LASSUMPTION_STATE_UPDATE_TAC =
  DISCH_THEN(fun uth ->
    let update_tac = LSTATE_UPDATE_TAC uth in
    MP_TAC uth THEN
    ASSUM_LIST(MAP_EVERY (fun th g ->
      try update_tac th g
      with Failure s ->
        if !components_print_log then
          if s = "NONOVERLAPPING_TAC: orthogonal_components with identical operands"
          then ALL_TAC g (* Exactly overwrites, e.g., orthogonal_components PC PC *)
          else (Printf.printf
            "Info: assumption `%s` is erased.\n    - Reason: %s\n"
            (string_of_term (concl th)) s; ALL_TAC g)
        else ALL_TAC g)));;

(* ------------------------------------------------------------------------- *)
(* Lock-step Hoare sequencing.                                               *)
(* ------------------------------------------------------------------------- *)

let LENSURES_SEQUENCE_TAC =
  let pth = prove
   (`!program_decodes1 program_decodes2 pcounter pc12 pc22 Q.
        C ,, C = C /\
        ensures step (\s. program_decodes1 (FST s) /\ read pcounter (FST s) = word pc11 /\
                          program_decodes2 (SND s) /\ read pcounter (SND s) = word pc21 /\
                          P s)
                     (\s. program_decodes1 (FST s) /\ read pcounter (FST s) = word pc12 /\
                          program_decodes2 (SND s) /\ read pcounter (SND s) = word pc22 /\
                          Q s)
                     C /\
        ensures step (\s. program_decodes1 (FST s) /\ read pcounter (FST s) = word pc12 /\
                          program_decodes2 (SND s) /\ read pcounter (SND s) = word pc22 /\
                          Q s)
                     R C
        ==> ensures step (\s. program_decodes1 (FST s) /\ read pcounter (FST s) = word pc11 /\
                              program_decodes2 (SND s) /\ read pcounter (SND s) = word pc21 /\
                              P s)
                          R C`,
    REWRITE_TAC[ENSURES_TRANS_SIMPLE]) in
  fun n1 n2 q -> (MATCH_MP_TAC pth THEN MAP_EVERY EXISTS_TAC [n1;n2;q] THEN BETA_TAC THEN
                  CONJ_TAC THENL [REL_MAYCHANGE_IDEMPOT_TAC; ALL_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Lock-step Loop invariants.                                                *)
(* ------------------------------------------------------------------------- *)

let LENSURES_WHILE_UP_TAC, LENSURES_WHILE_DOWN_TAC,
    LENSURES_WHILE_AUP_TAC, LENSURES_WHILE_ADOWN_TAC =
  let pth = prove(
    `!k pc1 pc2 pc11 pc12 pc21 pc22 (loopinvariant:num->S#S->bool). C ,, C = C /\ ~(k = 0) /\
      ensures (lock step)
        (\s. program_decodes1 (FST s) /\ read pcounter (FST s) = word pc1 /\
             program_decodes2 (SND s) /\ read pcounter (SND s) = word pc2 /\
             precondition s)
        (\s. program_decodes1 (FST s) /\ read pcounter (FST s) = word pc11 /\
             program_decodes2 (SND s) /\ read pcounter (SND s) = word pc21 /\
             loopinvariant 0 s)
        C /\
      (!i. i < k /\ ~(i = k) /\ ~(k = 0) /\ 0 < k
        ==>
        ensures (lock step)
          (\s. program_decodes1 (FST s) /\ read pcounter (FST s) = word pc11 /\
               program_decodes2 (SND s) /\ read pcounter (SND s) = word pc21 /\
               loopinvariant i s)
          (\s. program_decodes1 (FST s) /\ read pcounter (FST s) = word (if i + 1 < k then pc11 else pc12) /\
               program_decodes2 (SND s) /\ read pcounter (SND s) = word (if i + 1 < k then pc21 else pc22) /\
               loopinvariant (i + 1) s)
          C) /\
      ensures (lock step)
          (\s. program_decodes1 (FST s) /\ read pcounter (FST s) = word pc12 /\
               program_decodes2 (SND s) /\ read pcounter (SND s) = word pc22 /\
               loopinvariant k s)
          postcondition C
      ==>
      ensures (lock step)
        (\s. program_decodes1 (FST s) /\ read pcounter (FST s) = word pc1:N word /\
             program_decodes2 (SND s) /\ read pcounter (SND s) = word pc2:N word /\
             precondition s)
        postcondition C`,
    REPEAT STRIP_TAC THEN
    MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
    EXISTS_TAC `(\s:S#S. program_decodes1 (FST s) /\ read pcounter (FST s) = word pc11:N word /\
                         program_decodes2 (SND s) /\ read pcounter (SND s) = word pc21:N word /\
                         loopinvariant 0 s)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
    EXISTS_TAC `(\s:S#S. program_decodes1 (FST s) /\ read pcounter (FST s) = word pc12:N word /\
                         program_decodes2 (SND s) /\ read pcounter (SND s) = word pc22:N word /\
                         loopinvariant (k:num) s)` THEN
    ASM_REWRITE_TAC[] THEN
    DISJ_CASES_TAC (SPEC `k = 0 + 1` EXCLUDED_MIDDLE) THENL [
      FIRST_X_ASSUM (MP_TAC o SPEC `0`) THEN
      ASM_REWRITE_TAC[ARITH_RULE `0 < 0 + 1 /\ ~(0 + 1 < 0 + 1)`];
      ALL_TAC] THEN
    MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
    EXISTS_TAC `(\s:S#S. program_decodes1 (FST s) /\ read pcounter (FST s) = word pc11:N word /\
                         program_decodes2 (SND s) /\ read pcounter (SND s) = word pc21:N word /\
                         loopinvariant (k - 1) s)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [
      ALL_TAC;
      FIRST_X_ASSUM (MP_TAC o SPEC `k:num - 1`) THEN
      SUBGOAL_THEN `k - 1 < k /\ 0 < k /\ ~(k - 1 = k) /\ k - 1 + 1 = k /\ ~(k < k)` (fun th -> ASM_REWRITE_TAC[th]) THEN
      ASM_ARITH_TAC] THEN
    SUBGOAL_THEN `k - 1 = (k - 2) + 1` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `k - 2 < k - 1` MP_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SPEC_TAC (`k - 2:num`,`j:num`) THEN
    INDUCT_TAC THENL [
      STRIP_TAC THEN
      SUBGOAL_THEN `0 < k /\ 0 + 1 < k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `0`) THEN ASM_REWRITE_TAC[];
      STRIP_TAC THEN ASM_REWRITE_TAC[ADD1] THEN
      MATCH_MP_TAC ENSURES_TRANS_SIMPLE THEN
      EXISTS_TAC `(\s:S#S. program_decodes1 (FST s) /\ read pcounter (FST s) = word pc11:N word /\
                           program_decodes2 (SND s) /\ read pcounter (SND s) = word pc21:N word /\
                           loopinvariant (j + 1) s)` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [
        IMP_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        FIRST_X_ASSUM (MP_TAC o SPEC `j + 1`) THEN
        SUBGOAL_THEN `(j + 1) + 1 < k /\ j + 1 < k /\ ~(j + 1 = k) /\ 0 < k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[]]]) in
  let qth = prove(
    `!k pc1 pc2 pc11 pc12 pc21 pc22 (loopinvariant:num->S#S->bool). C ,, C = C /\ ~(k = 0) /\
      ensures (lock step)
        (\s. program_decodes1 (FST s) /\ read pcounter (FST s) = word pc1 /\
             program_decodes2 (SND s) /\ read pcounter (SND s) = word pc2 /\
             precondition s)
        (\s. program_decodes1 (FST s) /\ read pcounter (FST s) = word pc11 /\
             program_decodes2 (SND s) /\ read pcounter (SND s) = word pc21 /\
             loopinvariant k s)
        C /\
      (!i. i < k /\ ~(i = k) /\ ~(k = 0) /\ 0 < k
        ==>
        ensures (lock step)
          (\s. program_decodes1 (FST s) /\ read pcounter (FST s) = word pc11 /\
               program_decodes2 (SND s) /\ read pcounter (SND s) = word pc21 /\
               loopinvariant (i + 1) s)
          (\s. program_decodes1 (FST s) /\ read pcounter (FST s) = word (if i > 0 then pc11 else pc12) /\
               program_decodes2 (SND s) /\ read pcounter (SND s) = word (if i > 0 then pc21 else pc22) /\
               loopinvariant i s)
          C) /\
      ensures (lock step)
          (\s. program_decodes1 (FST s) /\ read pcounter (FST s) = word pc12 /\
               program_decodes2 (SND s) /\ read pcounter (SND s) = word pc22 /\
               loopinvariant 0 s)
          postcondition C
      ==>
      ensures (lock step)
        (\s. program_decodes1 (FST s) /\ read pcounter (FST s) = word pc1:N word /\
             program_decodes2 (SND s) /\ read pcounter (SND s) = word pc2:N word /\
             precondition s)
        postcondition C`,
    REPEAT GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [`k:num`; `pc11:num`; `pc12:num`; `pc21:num`; `pc22:num`;
                          `\i. (loopinvariant:num->S#S->bool) (k - i)`] THEN
    POP_ASSUM MP_TAC THEN REWRITE_TAC[SUB_0; SUB_REFL] THEN
    REPEAT (MATCH_MP_TAC MONO_AND THEN CONJ_TAC THEN REWRITE_TAC[]) THENL [
      DISCH_TAC THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPEC `k - (i + 1)`) THEN
      ASM_SIMP_TAC[ARITH_RULE `i < k ==> k - (i + 1) + 1 = k - i /\ (k - (i + 1) > 0 <=> i + 1 < k)`] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC]) in
  let rth = prove(
    `!a b pc1 pc2 pc11 pc12 pc21 pc22 (loopinvariant:num->S#S->bool). C ,, C = C /\ a < b /\
      ensures (lock step)
        (\s. program_decodes1 (FST s) /\ read pcounter (FST s) = word pc1 /\
             program_decodes2 (SND s) /\ read pcounter (SND s) = word pc2 /\
             precondition s)
        (\s. program_decodes1 (FST s) /\ read pcounter (FST s) = word pc11 /\
             program_decodes2 (SND s) /\ read pcounter (SND s) = word pc21 /\
             loopinvariant a s)
        C /\
      (!i. a <= i /\ i < b /\ ~(i = b) /\ ~(b = 0) /\ 0 < b
        ==>
        ensures (lock step)
          (\s. program_decodes1 (FST s) /\ read pcounter (FST s) = word pc11 /\
               program_decodes2 (SND s) /\ read pcounter (SND s) = word pc21 /\
               loopinvariant i s)
          (\s. program_decodes1 (FST s) /\ read pcounter (FST s) = word (if i + 1 < b then pc11 else pc12) /\
               program_decodes2 (SND s) /\ read pcounter (SND s) = word (if i + 1 < b then pc21 else pc22) /\
               loopinvariant (i + 1) s)
          C) /\
      ensures (lock step)
          (\s. program_decodes1 (FST s) /\ read pcounter (FST s) = word pc12 /\
               program_decodes2 (SND s) /\ read pcounter (SND s) = word pc22 /\
               loopinvariant b s)
          postcondition C
      ==>
      ensures (lock step)
        (\s. program_decodes1 (FST s) /\ read pcounter (FST s) = word pc1:N word /\
             program_decodes2 (SND s) /\ read pcounter (SND s) = word pc2:N word /\
             precondition s)
        postcondition C`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [`b - a`; `pc11:num`; `pc12:num`; `pc21:num`; `pc22:num`;
                          `\i. (loopinvariant:num->S#S->bool) (a + i)`] THEN
    ASM_REWRITE_TAC [SUB_EQ_0; NOT_LE; ADD_CLAUSES] THEN
    ASM_SIMP_TAC [ARITH_RULE `a < b ==> a + b - a = b`] THEN
    REWRITE_TAC [ADD_ASSOC] THEN STRIP_TAC THENL [
      FIRST_X_ASSUM (MP_TAC o SPEC `a + i`) THEN
      REWRITE_TAC[ARITH_RULE `(a + i) + 1 < b <=> i + 1 < b - a`] THEN
      DISCH_THEN (fun th -> IMP_REWRITE_TAC[th]) THEN ASM_ARITH_TAC]) in
  let sth = prove(
    `!a b pc1 pc2 pc11 pc12 pc21 pc22 (loopinvariant:num->S#S->bool). C ,, C = C /\ a < b /\
      ensures (lock step)
        (\s. program_decodes1 (FST s) /\ read pcounter (FST s) = word pc1 /\
             program_decodes2 (SND s) /\ read pcounter (SND s) = word pc2 /\
             precondition s)
        (\s. program_decodes1 (FST s) /\ read pcounter (FST s) = word pc11 /\
             program_decodes2 (SND s) /\ read pcounter (SND s) = word pc21 /\
             loopinvariant b s)
        C /\
      (!i. a <= i /\ i < b /\ ~(i = b) /\ ~(b = 0) /\ 0 < b
        ==>
        ensures (lock step)
          (\s. program_decodes1 (FST s) /\ read pcounter (FST s) = word pc11 /\
               program_decodes2 (SND s) /\ read pcounter (SND s) = word pc21 /\
               loopinvariant (i + 1) s)
          (\s. program_decodes1 (FST s) /\ read pcounter (FST s) = word (if i > a then pc11 else pc12) /\
               program_decodes2 (SND s) /\ read pcounter (SND s) = word (if i > a then pc21 else pc22) /\
               loopinvariant i s)
          C) /\
      ensures (lock step)
          (\s. program_decodes1 (FST s) /\ read pcounter (FST s) = word pc12 /\
               program_decodes2 (SND s) /\ read pcounter (SND s) = word pc22 /\
               loopinvariant a s)
          postcondition C
      ==>
      ensures (lock step)
        (\s. program_decodes1 (FST s) /\ read pcounter (FST s) = word pc1:N word /\
             program_decodes2 (SND s) /\ read pcounter (SND s) = word pc2:N word /\
             precondition s)
        postcondition C`,
    REPEAT STRIP_TAC THEN MATCH_MP_TAC qth THEN
    MAP_EVERY EXISTS_TAC [`b - a`; `pc11:num`; `pc12:num`; `pc21:num`; `pc22:num`;
                          `\i. (loopinvariant:num->S#S->bool) (a + i)`] THEN
    ASM_REWRITE_TAC [SUB_EQ_0; NOT_LE; ADD_CLAUSES] THEN
    ASM_SIMP_TAC [ARITH_RULE `a < b ==> a + b - a = b`] THEN
    REWRITE_TAC [ADD_ASSOC] THEN STRIP_TAC THENL [
      FIRST_X_ASSUM (MP_TAC o SPEC `a + i`) THEN
      REWRITE_TAC[ARITH_RULE `a + i > a <=> i > 0`] THEN
      DISCH_THEN (fun th -> IMP_REWRITE_TAC[th]) THEN ASM_ARITH_TAC]) in
  (fun k pc11 pc12 pc21 pc22 iv ->
    MATCH_MP_TAC pth THEN
    MAP_EVERY EXISTS_TAC [k; pc11; pc12; pc21; pc22; iv] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [REL_MAYCHANGE_IDEMPOT_TAC; ALL_TAC]),
  (fun k pc11 pc12 pc21 pc22 iv ->
    MATCH_MP_TAC qth THEN
    MAP_EVERY EXISTS_TAC [k; pc11; pc12; pc21; pc22; iv] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [REL_MAYCHANGE_IDEMPOT_TAC; ALL_TAC]),
 (fun a b pc11 pc12 pc21 pc22 iv ->
    MATCH_MP_TAC rth THEN
    MAP_EVERY EXISTS_TAC [a; b; pc11; pc12; pc21; pc22; iv] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [REL_MAYCHANGE_IDEMPOT_TAC; ALL_TAC]),
 (fun b a pc11 pc12 pc21 pc22 iv ->
    MATCH_MP_TAC sth THEN
    MAP_EVERY EXISTS_TAC [a; b; pc11; pc12; pc21; pc22; iv] THEN
    BETA_TAC THEN
    CONJ_TAC THENL [REL_MAYCHANGE_IDEMPOT_TAC; ALL_TAC]);;
