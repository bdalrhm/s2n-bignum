let ARM_VERBOSE_STEP'_TAC (exth1,exth2) sname g =
  Format.print_string("Stepping to state "^sname); Format.print_newline();
  ARM_STEP'_TAC (exth1,exth2) [] sname None g;;

(* ------------------------------------------------------------------------- *)
(* More convenient stepping tactics, optionally with accumulation.           *)
(* ------------------------------------------------------------------------- *)

let ARM_SINGLE_STEP'_TAC th s =
  time (ARM_VERBOSE_STEP'_TAC th s) THEN
  DISCARD_OLDSTATE_TAC s THEN
  CLARIFY_TAC;;

(* ARM_GEN_ACCSTEP'_TAC runs acc_preproc before ACCUMULATE_ARITH_TAC. This is
   useful when the output goal of ARM_SINGLE_STEP'_TAC needs additional rewrites
   for accumulator to recognize it. *)
let ARM_GEN_ACCSTEP'_TAC acc_preproc th aflag s =
  ARM_SINGLE_STEP'_TAC th s THEN
  (if aflag then acc_preproc THEN TRY(ACCUMULATE_ARITH_TAC s THEN CLARIFY_TAC)
   else ALL_TAC);;

(* ARM_GEN_ACCSTEPS'_TAC runs acc_preproc before ACCUMULATE_ARITH_TAC.
   acc_preproc is a function from string (which is a state name) to tactic. *)
let ARM_GEN_ACCSTEPS'_TAC acc_preproc th anums snums =
  MAP_EVERY
    (fun n ->
      let state_name = "s"^string_of_int n in
      ARM_GEN_ACCSTEP'_TAC (acc_preproc state_name) th (mem n anums) state_name)
    snums;;

let ARM_ACCSTEPS'_TAC th anums snums =
  ARM_GEN_ACCSTEPS'_TAC (fun _ -> ALL_TAC) th anums snums;;

let ARM_QUICKSTEP'_TAC th pats =
  let pats' =
   [`nonoverlapping_modulo a b c`; `aligned_bytes_loaded a b c`;
    `MAYCHANGE a b c`; `(a ,, b) c d`; `read PC s = x`; `steps arm i s0 si`] @ pats in
  fun s -> time (ARM_VERBOSE_STEP'_TAC th s) THEN
           DISCARD_NONMATCHING_ASSUMPTIONS pats' THEN
           DISCARD_OLDSTATE_TAC s THEN CLARIFY_TAC;;

let ARM_QUICKSTEPS'_TAC th pats snums =
  MAP_EVERY (ARM_QUICKSTEP'_TAC th pats) (statenames "s" snums);;

let ARM_QUICKSIM'_TAC execth pats snums =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_N_INIT_TAC "s0" THEN ARM_QUICKSTEPS'_TAC execth pats snums THEN
  ENSURES_FINAL_STATE'_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* More convenient wrappings of basic simulation flow.                       *)
(* ------------------------------------------------------------------------- *)

let ARM_SIM'_TAC execth snums =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  ENSURES_N_INIT_TAC "s0" THEN ARM_STEPS'_TAC execth snums "" [] THEN
  ENSURES_FINAL_STATE'_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* Simulate through a lemma in ?- ensures step P Q C ==> eventually R s      *)
(* ------------------------------------------------------------------------- *)

let (ARM_BIGSTEP'_TAC:(thm*thm option array)->string->tactic) =
  let lemma = prove
   (`P s /\ (!s':S. Q s' /\ C s s' ==> eventually_n step n2 R s')
     ==> ensures_n step P Q C (\s. n1) ==> eventually_n step (n1 + n2) R s`,
    STRIP_TAC THEN GEN_REWRITE_TAC LAND_CONV [ensures_n] THEN
    DISCH_THEN(MP_TAC o SPEC `s:S`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(MESON[]
     `(!s:S n1. eventually_n step n1 P s ==> eventually_n step (n1 + n2) Q s)
      ==> eventually_n step n1 P s ==> eventually_n step (n1 + n2) Q s`) THEN
    GEN_REWRITE_TAC I [EVENTUALLY_N_IMP_EVENTUALLY_N] THEN
    ASM_REWRITE_TAC[]) in
  fun (execth1,_) sname (asl,w) ->
    let sv = mk_var(sname,type_of(rand(rand w))) in
    (GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
      (!simulation_precanon_thms) THEN
     MATCH_MP_TAC lemma THEN CONJ_TAC THENL
      [BETA_TAC THEN ASM_REWRITE_TAC[];
       BETA_TAC THEN X_GEN_TAC sv THEN
       REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [MAYCHANGE; SEQ_ID] THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [GSYM SEQ_ASSOC] THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_SEQ] THEN
       GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV) [ASSIGNS_THM] THEN
       REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
       NONSELFMODIFYING_STATE_UPDATE_TAC
        (MATCH_MP aligned_bytes_loaded_update execth1) THEN
       ASSUMPTION_STATE_UPDATE_TAC THEN
       MAYCHANGE_STATE_UPDATE_TAC THEN
       DISCH_THEN(K ALL_TAC) THEN DISCARD_OLDSTATE_TAC sname])
    (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Fix up call/return boilerplate given core correctness.                    *)
(* ------------------------------------------------------------------------- *)

let ARM_ADD_RETURN_NOSTACK'_TAC =
  let lemma1 = prove
   (`ensures_n step P Q R fn /\
     (!s s'. P s /\ Q s' /\ R s s' ==> Q' s')
     ==> ensures_n step P (\s. Q s /\ Q' s) R fn`,
    ONCE_REWRITE_TAC[IMP_CONJ_ALT] THEN DISCH_TAC THEN
    MATCH_MP_TAC ENSURES_N_SUBLEMMA_THM THEN
    REWRITE_TAC[SUBSUMED_REFL] THEN ASM_MESON_TAC[]) in
  let ENSURES_N_TRANS_SUBSUMED = prove(`!P Q R C C' n1 n2.
        C ,, C = C /\ C subsumed C' /\
        ensures_n step P Q C (\s. n1) /\ ensures_n step Q R C (\s. n2)
        ==> ensures_n step P R C' (\s. n1 + n2)`,
    REPEAT STRIP_TAC THEN
    ASM_MESON_TAC[ENSURES_N_TRANS_SIMPLE; ENSURES_N_FRAME_SUBSUMED]) in
  let lemma2 = prove
   (`C ,, C = C /\ C subsumed C' /\
     (!s s'. program_decodes s /\ pcdata s /\ returndata s /\ P s /\
             Q s' /\ C s s'
             ==> program_decodes s' /\ returndata s') /\
     ensures_n step (\s. program_decodes s /\ returndata s /\ Q s) R C (\s. 1)
     ==> ensures_n step (\s. program_decodes s /\ pcdata s /\ P s) Q C (\s. n)
          ==> ensures_n step
               (\s. program_decodes s /\ pcdata s /\ returndata s /\ P s) R C' (\s. n + 1)`,
    ONCE_REWRITE_TAC[TAUT
     `a /\ p /\ subsm /\ q ==> r ==> s <=>
      a ==> p ==> subsm ==> r ==> q ==> s`] THEN
    DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN DISCH_TAC THEN
    MATCH_MP_TAC(ONCE_REWRITE_RULE
     [TAUT `p /\ q /\ r /\ r2 ==> s <=> p /\ q /\ r ==> r2 ==> s`]
     ENSURES_N_TRANS_SUBSUMED) THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC (RATOR_CONV o LAND_CONV o BINDER_CONV)
     [TAUT `p /\ q /\ r <=> r /\ p /\ q`] THEN
    MATCH_MP_TAC lemma1 THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ_ALT]
          ENSURES_N_PRECONDITION_THM)) THEN
    SIMP_TAC[]) in
  fun execth coreth ->
    REWRITE_TAC[MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    MP_TAC coreth THEN
    REPEAT(MATCH_MP_TAC MONO_FORALL THEN GEN_TAC) THEN
    REWRITE_TAC[NONOVERLAPPING_CLAUSES; ALLPAIRS; ALL] THEN
    REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS;
      MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    DISCH_THEN(fun th ->
      REPEAT GEN_TAC THEN
      TRY(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
      MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    TRY(ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN ALIGNED_16_TAC THEN
      TRY DISJ2_TAC THEN NONOVERLAPPING_TAC;
      ALL_TAC]) THEN
    MATCH_MP_TAC lemma2 THEN REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MAYCHANGE_IDEMPOT_TAC;
      SUBSUMED_MAYCHANGE_TAC;
      REPEAT GEN_TAC THEN REWRITE_TAC(!simulation_precanon_thms) THEN
      REPEAT(DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC)) THEN
      REWRITE_TAC[MAYCHANGE; SEQ_ID] THEN
      REWRITE_TAC[GSYM SEQ_ASSOC] THEN
      REWRITE_TAC[ASSIGNS_SEQ] THEN REWRITE_TAC[ASSIGNS_THM] THEN
      REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN REPEAT GEN_TAC THEN
      NONSELFMODIFYING_STATE_UPDATE_TAC
       (MATCH_MP aligned_bytes_loaded_update (fst execth)) THEN
      ASSUMPTION_STATE_UPDATE_TAC THEN
      DISCH_THEN(K ALL_TAC) THEN ASM_REWRITE_TAC[] THEN NO_TAC;
      REWRITE_TAC(!simulation_precanon_thms) THEN
      ENSURES_N_INIT_TAC "s0" THEN
      REPEAT(FIRST_X_ASSUM(DISJ_CASES_TAC o check
       (can (term_match [] `read PC s = a \/ Q` o concl)))) THEN
      ARM_STEPS'_TAC execth [1] "" [] THEN
      ENSURES_FINAL_STATE'_TAC THEN ASM_REWRITE_TAC[]];;

(* ------------------------------------------------------------------------- *)
(* Version with register save/restore and stack adjustment.                  *)
(* ------------------------------------------------------------------------- *)

let ARM_ADD_RETURN_STACK'_TAC =
  let mono2lemma = MESON[]
   `(!x. (!y. P x y) ==> (!y. Q x y)) ==> (!x y. P x y) ==> (!x y. Q x y)`
  and sp_tm = `SP` and x30_tm = `X30`
  and dqd_thm = WORD_BLAST `(word_zx:int128->int64)(word_zx(x:int64)) = x` in
  fun execth coreth reglist stackoff ->
    let regs = dest_list reglist in
    let n = let n0 = length regs / 2 in
            if 16 * n0 = stackoff then n0 else n0 + 1 in
    MP_TAC coreth THEN
    REWRITE_TAC [MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REPEAT(MATCH_MP_TAC mono2lemma THEN GEN_TAC) THEN
    (if vfree_in sp_tm (concl coreth) then
      DISCH_THEN(fun th -> WORD_FORALL_OFFSET_TAC stackoff THEN MP_TAC th) THEN
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC
     else
      MATCH_MP_TAC MONO_FORALL THEN GEN_TAC THEN
      DISCH_THEN(fun th ->
        WORD_FORALL_OFFSET_TAC stackoff THEN MP_TAC th)) THEN
    REWRITE_TAC[NONOVERLAPPING_CLAUSES; PAIRWISE; ALLPAIRS; ALL] THEN
    REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS] THEN
    DISCH_THEN(fun th ->
      REPEAT GEN_TAC THEN
      TRY(DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC)) THEN
      MP_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    TRY(ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN ALIGNED_16_TAC THEN
      TRY DISJ2_TAC THEN NONOVERLAPPING_TAC;
      ALL_TAC]) THEN
    DISCH_THEN(fun th ->
      ENSURES_N_EXISTING_PRESERVED_TAC sp_tm THEN
      (if mem x30_tm regs then ENSURES_N_EXISTING_PRESERVED_TAC x30_tm
       else ALL_TAC) THEN
      MAP_EVERY (fun c -> ENSURES_N_PRESERVED_DREG_TAC
                            ("init_"^fst(dest_const c)) c)
                (subtract regs [x30_tm]) THEN
      REWRITE_TAC(!simulation_precanon_thms) THEN ENSURES_N_INIT_TAC "s0" THEN
      ARM_STEPS'_TAC execth (1--n) "" [] THEN
      MP_TAC th) THEN
    ARM_BIGSTEP'_TAC execth ("s"^string_of_int(n+1)) THEN
    REWRITE_TAC(!simulation_precanon_thms) THEN
    ARM_STEPS'_TAC execth ((n+2)--(2*n+2)) "" [] THEN
    ENSURES_FINAL_STATE'_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[dqd_thm];;

(* ------------------------------------------------------------------------- *)
(* Simulate a subroutine, instantiating it from the state.                   *)
(* ------------------------------------------------------------------------- *)

let ARM_SUBROUTINE_SIM'_TAC (machinecode,execth,offset,submachinecode,subth) =
  let subimpth =
    let th = MATCH_MP aligned_bytes_loaded_of_append3
      (TRANS machinecode
         (N_SUBLIST_CONV (SPEC_ALL submachinecode) offset
                         (rhs(concl machinecode)))) in
    let len = rand (lhand (concl th)) in
    let th = REWRITE_RULE [
      (REWRITE_CONV [LENGTH] THENC NUM_REDUCE_CONV) len] th in
    MP th (EQT_ELIM (NUM_DIVIDES_CONV (lhand (concl th)))) in
  fun ilist0 n ->
    let sname = "s"^string_of_int(n-1)
    and sname' = "s"^string_of_int n in
    let svar = mk_var(sname,`:armstate`)
    and svar0 = mk_var("s",`:armstate`) in
    let ilist = map (vsubst[svar,svar0]) ilist0 in
    MP_TAC(TWEAK_PC_OFFSET(SPECL ilist subth)) THEN
    ASM_REWRITE_TAC[C_ARGUMENTS; C_RETURN; SOME_FLAGS;
                    MAYCHANGE_REGS_AND_FLAGS_PERMITTED_BY_ABI] THEN
    REWRITE_TAC[ALLPAIRS; ALL; PAIRWISE; NONOVERLAPPING_CLAUSES] THEN
    ANTS_TAC THENL
     [CONV_TAC(ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV) THEN
      ALIGNED_16_TAC THEN REPEAT CONJ_TAC THEN
      TRY(CONV_TAC(DEPTH_CONV WORD_NUM_RED_CONV) THEN NO_TAC) THEN
      NONOVERLAPPING_TAC;
      CONV_TAC(LAND_CONV(ONCE_DEPTH_CONV
       NORMALIZE_RELATIVE_ADDRESS_CONV)) THEN
      ASM_REWRITE_TAC[]] THEN
    ARM_BIGSTEP'_TAC execth sname' THENL
     [MATCH_MP_TAC subimpth THEN FIRST_X_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    RULE_ASSUM_TAC(CONV_RULE(TRY_CONV
     (GEN_REWRITE_CONV I [MESON[ADD_ASSOC]
      `read PC s = word((pc + m) + n) <=>
       read PC s = word(pc + m + n)`] THENC
     funpow 3 RAND_CONV NUM_ADD_CONV)));;

let ARM_SUBROUTINE_SIM_ABBREV'_TAC tupper ilist0 =
  let tac = ARM_SUBROUTINE_SIM'_TAC tupper ilist0 in
  fun comp0 abn n (asl,w) ->
    let svar0 = mk_var("s",`:armstate`)
    and svar0' = mk_var("s'",`:armstate`)
    and svar = mk_var("s"^string_of_int(n-1),`:armstate`)
    and svar' = mk_var("s"^string_of_int n,`:armstate`) in
    let comp1 =
      rand(concl(PURE_ONCE_REWRITE_CONV (map snd asl)
        (vsubst[svar,svar0;svar',svar0'] comp0))) in
    (tac n THEN
     ABBREV_TAC(mk_eq(mk_var(abn,type_of comp1),comp1))) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Tactics to deal with microarchitectural events.                           *)
(* ------------------------------------------------------------------------- *)

let DROP_EVENTS_COND = prove(
  `!P Q C fn. (?es'. !es. ensures_n arm (\s. P s /\ read events s = es)
                                        (\s. Q s /\ read events s = APPEND es' es) C fn) ==>
    ensures_n arm (\s. P s) (\s. Q s) C fn`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!es. ensures_n arm (\s. P s /\ read events s = es) (\s. Q s) C fn` ASSUME_TAC THENL [
    REPEAT GEN_TAC THEN
    MATCH_MP_TAC ENSURES_N_POSTCONDITION_THM THEN
    META_EXISTS_TAC THEN ONCE_REWRITE_TAC [TAUT `!P Q. P /\ Q <=> Q /\ P`] THEN
    CONJ_TAC THENL [
      FIRST_X_ASSUM (MP_TAC o SPEC_ALL) THEN
      DISCH_THEN (UNIFY_ACCEPT_TAC [`Q':armstate->bool`]);
      MESON_TAC[]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (RATOR_CONV o RATOR_CONV o LAND_CONV o ONCE_DEPTH_CONV) [MESON[] `P s <=> P s /\ ?es. read events s = es`] THEN
  ASM_MESON_TAC[ensures_n]);;

let DROP_EVENTS_COND_TAC th =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[CONJ_ASSOC] THEN
  MATCH_MP_TAC DROP_EVENTS_COND THEN
  CHOOSE_THEN (MP_TAC o GEN `es:armevent list` o SPEC_ALL) th THEN
  ASM_REWRITE_TAC[GSYM CONJ_ASSOC] THEN
  DISCH_THEN (fun th ->
    META_EXISTS_TAC THEN UNIFY_ACCEPT_TAC [`es':armevent list`] th);;
