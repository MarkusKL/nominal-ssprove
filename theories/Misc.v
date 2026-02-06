From NominalSSP Require Import Options.

Notation dist := (code emptym [interface]).

(*
#[export] Hint Extern 9 (ValidCode ?L ?I ?c.(prog)) =>
  eapply valid_scheme ; eapply c.(prog_valid)
  : typeclass_instances ssprove_valid_db.  *)

Ltac ssp_prhl invar :=
  ssprove_share; eapply prove_perfect;
  eapply (eq_rel_perf_ind _ _ invar);
  [ ssprove_invariant; try done |
    let arg := fresh "arg" in simplify_eq_rel arg
  ].

Ltac ssp_restore :=
  (ssprove_restore_mem; [ ssprove_invariant; try done |]) ||
  (ssprove_restore_pre; [ ssprove_invariant; try done |]) ||
  ssprove_forget_all.

Ltac ssp_ret := ssp_restore; [ .. | apply r_ret; try done ].
