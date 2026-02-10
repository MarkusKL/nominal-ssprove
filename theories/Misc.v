From NominalSSP Require Import Options.

Notation dist := (code emptym [interface]).

(*
#[export] Hint Extern 9 (ValidCode ?L ?I ?c.(prog)) =>
  eapply valid_scheme ; eapply c.(prog_valid)
  : typeclass_instances ssprove_valid_db.  *)

Ltac ssp_simpl :=
  repeat (ssprove_code_simpl; simpl; ssprove_code_simpl_more).

Ltac ssp_prhl inv :=
  ssprove_share; eapply prove_perfect;
  eapply (eq_rel_perf_ind _ _ inv);
  [ ssprove_invariant; try done
  | let arg := fresh "arg" in simplify_eq_rel arg
  ].

Ltac ssp_prhl_eq :=
  ssprove_share; eapply prove_perfect;
  eapply eq_rel_perf_ind_eq;
  let arg := fresh "arg" in simplify_eq_rel arg.

Ltac ssp_restore :=
  (ssprove_restore_mem; [ ssprove_invariant; try done |]) ||
  (ssprove_restore_pre; [ ssprove_invariant; try done |]) ||
  ssprove_forget_all.

Ltac ssp_ret := ssp_restore; [ .. | apply r_ret; try done ].

Notation uniformZ n := (uniform (Zp_trunc n).+2).

(* Unused for now
Notation "n .-bits" := (n.-tuple 'Z_2).

Definition xor {n : nat} : n.-bits → n.-bits → n.-bits :=
  λ x y, [tuple tnth x i + tnth y i | i < n ].

Notation "x ⊕ y" := (xor x y) (at level 40).
 *)

Section ExtraLemmas.
  Lemma codomm_set {T S : ordType} (L : {fmap T → S}) t s
    : t \notin domm L → codomm (setm L t s) = s |: codomm L.
  Proof.
    intros H'.
    apply eq_fset => s'. rewrite in_fsetU1.
    apply Bool.eq_iff_eq_true. split.
    - move=> /codommP [t' H].
      rewrite setmE in H.
      destruct (t' == t)%B.
      + injection H => ->. by rewrite eq_refl.
      + apply /orP; right. apply /codommP. by exists t'.
    - move=> /orP [/eqP {s'}->| /codommP [t' H]]; apply /codommP.
      + exists t. by rewrite setmE eq_refl.
      + exists t'. rewrite setmE.
        destruct (t' == t)%B eqn:E; [| done ].
        by move: E H' H => /eqP -> /dommPn ->.
  Qed.
End ExtraLemmas.
