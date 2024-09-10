(*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: Apache-2.0 OR ISC OR MIT-0
 *)

let ARM_LESNURES_IS_ENSURES2 = prove(
  `!P Q C. ensures (lock arm) P Q C ==> ?fn. ensures2' arm P Q C fn fn`,
  SEQ_IMP_REWRITE_TAC[LESNURES_IS_ENSURES2; arm_unique]);;

(*** decode_ths is an array from int offset i to
 ***   Some `|- !s pc. aligned_bytes_loaded s pc *_mc
 ***            ==> arm_decode s (word (pc+i)) (..inst..)`
 *** .. if it is a valid byte sequence, or None otherwise.
 ***)

let LARM_CONV (decode_ths:thm option array) (ths:thm list) tm =
  let pc_th = find
    (fun th -> (* do not use term_match because it is slow. *)
      let c = concl th in
      is_eq c && is_read_pc (lhs c) && rand (lhs c) = lhand tm)
    ths in
  let eth = tryfind (fun loaded_mc_th ->
      GEN_REWRITE_CONV I [ARM_THM decode_ths loaded_mc_th pc_th] tm) ths in
 (K eth THENC
  ONCE_DEPTH_CONV ARM_EXEC_CONV THENC
  REWRITE_CONV[XREG_NE_SP; SEQ; condition_semantics] THENC
  ALIGNED_16_CONV ths THENC
  REWRITE_CONV[SEQ; condition_semantics] THENC
  GEN_REWRITE_CONV ONCE_DEPTH_CONV [assign] THENC
  REWRITE_CONV[] THENC
  TOP_DEPTH_CONV COMPONENT_READ_OVER_WRITE_CONV THENC
  GEN_REWRITE_CONV TOP_DEPTH_CONV [WRITE_RVALUE] THENC
  ONCE_REWRITE_CONV [WORD_SUB_ADD] THENC
  ONCE_DEPTH_CONV
   (REWR_CONV (GSYM ADD_ASSOC) THENC RAND_CONV NUM_REDUCE_CONV) THENC
  ONCE_DEPTH_CONV
   (GEN_REWRITE_CONV I [GSYM WORD_ADD] THENC
    GEN_REWRITE_CONV (RAND_CONV o TOP_DEPTH_CONV) [GSYM ADD_ASSOC] THENC
    RAND_CONV NUM_REDUCE_CONV) THENC
  TOP_DEPTH_CONV COMPONENT_WRITE_OVER_WRITE_CONV THENC
  GEN_REWRITE_CONV (SUB_COMPONENTS_CONV o TOP_DEPTH_CONV) ths THENC
  GEN_REWRITE_CONV TOP_DEPTH_CONV [WORD_VAL] THENC
  ONCE_DEPTH_CONV WORD_PC_PLUS_CONV THENC
  ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV THENC
  ONCE_DEPTH_CONV NORMALIZE_RELATIVE_ADDRESS_CONV
 ) tm;;

let EQ_CONJ_TRANS = prove(
  `(t <=> p /\ q) ==> (p <=> r) ==> (q <=> s) ==> (t <=> r /\ s)`,
  ITAUT_TAC);;

let PAIR_EQ_FST_SND = prove(
  `!x:A y:B p. x = (FST p) /\ y = (SND p) <=> (x, y) = p`,
  REWRITE_TAC[FORALL_PAIR_THM; PAIR_EQ]);;

let LARM_BASIC_STEP_TAC =
  let arm_tm = `arm` and arm_ty = `:armstate#armstate`
  and pair_fst = `FST:armstate#armstate->armstate`
  and pair_snd = `SND:armstate#armstate->armstate` in
  fun (decode_ths: thm option array) sname (asl,w) ->
    let sv = rand w and sv' = mk_var(sname,arm_ty) in
    let sv1 = mk_comb(pair_fst,sv) and sv1' = mk_comb(pair_fst,sv') in
    let atm1 = mk_comb(mk_comb(arm_tm,sv1),sv1') in
    let eth1 = LARM_CONV decode_ths (map snd asl) atm1 in
    let sv2 = mk_comb(pair_snd,sv) and sv2' = mk_comb(pair_snd,sv') in
    let atm2 = mk_comb(mk_comb(arm_tm,sv2),sv2') in
    let eth2 = LARM_CONV decode_ths (map snd asl) atm2 in
    let eth = MATCH_MP (MATCH_MP (MATCH_MP EQ_CONJ_TRANS (ISPECL [arm_tm; sv; sv'] LOCK_DEF)) eth1) eth2 in
    (GEN_REWRITE_TAC I [eventually_CASES] THEN DISJ2_TAC THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC (REPEATC o BINDER_CONV) [eth; PAIR_EQ_FST_SND] THEN CONV_TAC EXISTS_NONTRIVIAL_CONV;
      X_GEN_TAC sv' THEN GEN_REWRITE_TAC LAND_CONV [eth] THEN GEN_REWRITE_TAC I [IMP_CONJ]]) (asl,w);;

let LARM_STEP_TAC (mc_length_th,decode_ths) (subths:thm list) sname =
  (*** This does the basic decoding setup ***)
  LARM_BASIC_STEP_TAC decode_ths sname THEN

  REPEAT_N 2 (
  (*** This part shows the code isn't self-modifying ***)
  W(NONSELFMODIFYING_STATE_UPDATE_TAC o Fun.flip SPEC
    (MATCH_MP aligned_bytes_loaded_update mc_length_th) o (rhs o lhand o snd)) THEN

  (*** Attempt also to show subroutines aren't modified, if applicable ***)

  MAP_EVERY (fun th -> W(TRY o NONSELFMODIFYING_STATE_UPDATE_TAC o Fun.flip SPEC
    (MATCH_MP aligned_bytes_loaded_update (CONJUNCT1 th)) o (rhs o lhand o snd))) subths THEN

  (*** This part produces any updated versions of existing asms ***)

  LASSUMPTION_STATE_UPDATE_TAC THEN

  (*** Produce updated "MAYCHANGE" assumption ***)

  MAYCHANGE_STATE_UPDATE_TAC THEN

  (*** This adds state component theorems for the updates ***)
  (*** Could also assume th itself but I throw it away   ***)

  DISCH_THEN(fun th ->
    let thl = STATE_UPDATE_NEW_RULE th in
    if thl = [] then ALL_TAC else
    MP_TAC(end_itlist CONJ thl) THEN
    ASSEMBLER_SIMPLIFY_TAC THEN
    STRIP_TAC));;

let LARM_VERBOSE_STEP_TAC (exth1,exth2) sname g =
  Format.print_string("Stepping to state "^sname); Format.print_newline();
  LARM_STEP_TAC (exth1,exth2) [] sname g;;

let LARM_VERBOSE_SUBSTEP_TAC (exth1,exth2) subths sname g =
  Format.print_string("Stepping to state "^sname); Format.print_newline();
  LARM_STEP_TAC (exth1,exth2) subths sname g;;

(* ------------------------------------------------------------------------- *)
(* Throw away assumptions according to patterns.                             *)
(* ------------------------------------------------------------------------- *)

let LDISCARD_OLDSTATE_TAC s =
  let v = mk_var(s,`:armstate#armstate`) in
  let rec unbound_statevars_of_read bound_svars tm =
    match tm with
      Comb(Comb(Const("read",_),cmp),s) ->
        subtract (frees s) bound_svars
    | Comb(a,b) -> union (unbound_statevars_of_read bound_svars a)
                         (unbound_statevars_of_read bound_svars b)
    | Abs(v,t) -> unbound_statevars_of_read (v::bound_svars) t
    | _ -> [] in
  let is_read (tm:term): bool =
    match tm with
    Comb(Comb(Const("read",_),_),s) -> true
    | _ -> false in
    DISCARD_ASSUMPTIONS_TAC(
      fun thm ->
        let us = unbound_statevars_of_read [] (concl thm) in
        if us = [] || us = [v] then false
        else if not(mem v us) then true
        else is_eq (concl thm) && is_read (rand (concl thm)));;

(* ------------------------------------------------------------------------- *)
(* More convenient stepping tactics, optionally with accumulation.           *)
(* ------------------------------------------------------------------------- *)

let LARM_SINGLE_STEP_TAC th s =
  time (LARM_VERBOSE_STEP_TAC th s) THEN
  LDISCARD_OLDSTATE_TAC s THEN
  CLARIFY_TAC;;

let LARM_VACCSTEP_TAC th aflag s =
  LARM_VERBOSE_STEP_TAC th s THEN
  (if aflag then TRY(ACCUMULATE_ARITH_TAC s THEN CLARIFY_TAC) else ALL_TAC);;

let LARM_XACCSTEP_TAC th excs aflag s =
  LARM_SINGLE_STEP_TAC th s THEN
  (if aflag then TRY(ACCUMULATEX_ARITH_TAC excs s THEN CLARIFY_TAC)
   else ALL_TAC);;

(* LARM_GEN_ACCSTEP_TAC runs acc_preproc before ACCUMULATE_ARITH_TAC. This is
   useful when the output goal of LARM_SINGLE_STEP_TAC needs additional rewrites
   for accumulator to recognize it. *)
let LARM_GEN_ACCSTEP_TAC acc_preproc th aflag s =
  LARM_SINGLE_STEP_TAC th s THEN
  (if aflag then acc_preproc THEN TRY(ACCUMULATE_ARITH_TAC s THEN CLARIFY_TAC)
   else ALL_TAC);;

let LARM_ACCSTEP_TAC th aflag s = LARM_GEN_ACCSTEP_TAC ALL_TAC th aflag s;;

let LARM_VSTEPS_TAC th snums =
  MAP_EVERY (LARM_VERBOSE_STEP_TAC th) (statenames "s" snums);;

let LARM_STEPS_TAC th snums =
  MAP_EVERY (LARM_SINGLE_STEP_TAC th) (statenames "s" snums);;

let LARM_VACCSTEPS_TAC th anums snums =
  MAP_EVERY (fun n -> LARM_VACCSTEP_TAC th (mem n anums) ("s"^string_of_int n))
            snums;;

let LARM_XACCSTEPS_TAC th excs anums snums =
  MAP_EVERY
   (fun n -> LARM_XACCSTEP_TAC th excs (mem n anums) ("s"^string_of_int n))
   snums;;

(* LARM_GEN_ACCSTEPS_TAC runs acc_preproc before ACCUMULATE_ARITH_TAC.
   acc_preproc is a function from string (which is a state name) to tactic. *)
let LARM_GEN_ACCSTEPS_TAC acc_preproc th anums snums =
  MAP_EVERY
    (fun n ->
      let state_name = "s"^string_of_int n in
      LARM_GEN_ACCSTEP_TAC (acc_preproc state_name) th (mem n anums) state_name)
    snums;;

let LARM_ACCSTEPS_TAC th anums snums =
  LARM_GEN_ACCSTEPS_TAC (fun _ -> ALL_TAC) th anums snums;;

let LARM_QUICKSTEP_TAC th pats =
  let pats' =
   [`nonoverlapping_modulo a b c`; `aligned_bytes_loaded a b c`;
    `MAYCHANGE a b c`; `(a ,, b) c d`; `read PC s = x`] @ pats in
  fun s -> time (LARM_VERBOSE_STEP_TAC th s) THEN
           DISCARD_NONMATCHING_ASSUMPTIONS pats' THEN
           DISCARD_OLDSTATE_TAC s THEN CLARIFY_TAC;;

let LARM_QUICKSTEPS_TAC th pats snums =
  MAP_EVERY (LARM_QUICKSTEP_TAC th pats) (statenames "s" snums);;

let LARM_QUICKSIM_TAC execth pats snums =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  LENSURES_INIT_TAC "s0" THEN LARM_QUICKSTEPS_TAC execth pats snums THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[];;

(* ------------------------------------------------------------------------- *)
(* More convenient wrappings of basic simulation flow.                       *)
(* ------------------------------------------------------------------------- *)

let LARM_SIM_TAC execth snums =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  LENSURES_INIT_TAC "s0" THEN LARM_STEPS_TAC execth snums THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[];;

let LARM_ACCSIM_TAC execth anums snums =
  REWRITE_TAC(!simulation_precanon_thms) THEN
  LENSURES_INIT_TAC "s0" THEN LARM_ACCSTEPS_TAC execth anums snums THEN
  ENSURES_FINAL_STATE_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[VAL_WORD_SUB_EQ_0] THEN ASM_REWRITE_TAC[];;
