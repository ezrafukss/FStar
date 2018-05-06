module Unbound

open FStar.Tactics

let tau () : Tac unit =
    split ();
    let x = bv_of_binder (implies_intro ()) in
    squash_intro (); exact (pack (Tv_Var x));
    // `x` is unbound in this environment, we should fail
    // (if it succeeds: is the use_bv_sorts flag on? it should be off)
    squash_intro (); exact (pack (Tv_Var x))

[@(fail_errs [23])]
let _ = assert_by_tactic ((False ==> False) /\ False) tau
