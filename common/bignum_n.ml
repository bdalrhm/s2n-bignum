(* ------------------------------------------------------------------------- *)
(* Get ranges of bignum abbreviation out of precondition.                    *)
(* ------------------------------------------------------------------------- *)

let BIGNUM_TERMRANGE'_TAC =
  let pth = prove
   (`!k m. m < 2 EXP (64 * k) \/ !s x. ~(bignum_from_memory (x,k) s = m)`,
    MESON_TAC[BIGNUM_FROM_MEMORY_BOUND]) in
  fun k m ->
    DISJ_CASES_THEN2
     ASSUME_TAC
     (fun th -> REWRITE_TAC[th; ENSURES_N_TRIVIAL] THEN NO_TAC)
     (SPECL [k; m] pth);;

let BIGNUM_RANGE'_TAC =
  let pth = prove
   (`!k m. m < 2 EXP (64 * k) \/ !s x. ~(bignum_from_memory (x,k) s = m)`,
    MESON_TAC[BIGNUM_FROM_MEMORY_BOUND])
  and nty = `:num` in
  fun k m ->
    DISJ_CASES_THEN2
     ASSUME_TAC
     (fun th -> REWRITE_TAC[th; ENSURES_N_TRIVIAL] THEN NO_TAC)
     (SPECL [mk_var(k,nty); mk_var(m,nty)] pth);;
