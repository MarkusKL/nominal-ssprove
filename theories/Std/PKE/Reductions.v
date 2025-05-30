Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8 Lia.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.
Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

From NominalSSP Require Import Prelude.
Import PackageNotation.
#[local] Open Scope package_scope.

From NominalSSP.Std Require Import Math.Group Assumptions.DDH PKE.Scheme Hybrid.

Import PKE GroupScope.

Section Reductions.

  Context (P : scheme).

  Definition mpk_loc' : Location := ('option P.(Pub); 45%N).
  Definition count_loc' : Location := ('nat; 66%N).

  Definition SLIDE n i :
    module (I_CPA P) (I_CPA P) :=
    [module fset
      [:: count_loc' ; mpk_loc' ] ;
      [ GEN ] : { 'unit ~> P.(Pub) } 'tt {
        pk ← call GEN 'unit P.(Pub) tt ;;
        #put mpk_loc' := Some pk ;;
        ret pk
      } ;
      [ QUERY ] : { P.(Mes) ~> P.(Cip) } (m) {
        count ← get count_loc' ;; 
        #assert (count < n)%N ;;
        #put count_loc' := count.+1 ;;
        pk ← getSome mpk_loc' ;;
        if (count < i)%N then
          c ← P.(sample_Cip) ;; ret c
        else if (i < count)%N then
          c ← P.(enc) pk m ;; ret c
        else 
          call QUERY P.(Mes) P.(Cip) m
      }
    ].

Definition R (i : 'nat) (c : 'nat) (c' : 'nat)
  := (if (c' > i)%N then (c == 1%N)%B else (c == 0%N)%B).

Notation inv i := (
  heap_ignore (fset [:: mpk_loc' ; count_loc ; count_loc' ])
  ⋊ couple_cross (mpk_loc P) mpk_loc' eq 
  ⋊ couple_cross count_loc count_loc' eq
  ⋊ couple_rhs count_loc count_loc' (R i)
).

Lemma PK_CPA_SLIDE_perfect {n} b : perfect (I_CPA P)
  (MT_CPA P n b) (SLIDE n (if b then 0 else n) ∘ OT_CPA P true).
Proof.
  nssprove_share.
  eapply prove_perfect.
  apply (eq_rel_perf_ind _ _ (inv (if b then 0 else n))).
  1: simpl; ssprove_invariant; try done; fset_solve.
  simplify_eq_rel m.
  - destruct m; simpl.
    simplify_linking.
    rewrite 2!cast_fun_K.
    ssprove_code_simpl.
    simplify_linking.
    rewrite cast_fun_K.
    ssprove_code_simpl.
    eapply rsame_head_alt.  1-3: by try apply prog_valid.
    intros [_ pk].
    apply r_put_vs_put.
    apply r_put_rhs.
    ssprove_restore_pre.
    2: by apply r_ret.
    ssprove_invariant.
    1,2: intros s0 s1 h'; unfold couple_cross; simpl; by get_heap_simpl.

  - ssprove_code_simpl; simpl.
    ssprove_code_simpl_more.
    eapply r_get_vs_get_cross.
    1: do 1 apply Cross_conj_left; apply Cross_conj_right, Cross_couple_cross.
    intros ? c ?; subst.
    apply (r_rem_rhs count_loc) => cr.
    ssprove_sync => H.
    ssprove_swap_lhs 0%N; ssprove_swap_rhs 0%N.
    eapply r_get_vs_get_cross.
    1: do 5 apply Cross_conj_left; apply Cross_conj_right, Cross_couple_cross.
    intros ? mpk ?; subst.
    ssprove_swap_lhs 0%N; ssprove_swap_rhs 0%N.
    ssprove_sync => H'.
    destruct mpk as [pk|] => //= {H'}.
    destruct b; [ destruct c | ]; simpl.
    + ssprove_code_simpl_more.
      ssprove_code_simpl.
      ssprove_code_simpl_more.
      ssprove_swap_rhs 0%N.
      eapply (r_get_remind_rhs).
      1: exact _.
      eapply (r_rem_couple_rhs count_loc count_loc').
      1,2,3: exact _.
      unfold R; simpl; move=> /eqP -> {cr} //=.
      ssprove_swap_seq_rhs [:: 1%N ; 0%N ].
      eapply r_get_remind_rhs.
      1: eapply Remembers_rhs_from_tracked_lhs.
      1: exact _.
      1: ssprove_invariant.
      apply r_put_rhs.
      apply r_put_vs_put => //=.
      eapply rsame_head_alt.
      1-3: by try apply prog_valid.
      intros x.
      ssprove_restore_mem.
      2: by apply r_ret.
      ssprove_invariant.
      3: done.
      1-2: intros s0 s1 h'; unfold couple_cross, couple_rhs; simpl; get_heap_simpl.
      2: done.
      1: destruct h' as [[[[[H1 H2] H3] H4] H5] H6]; rewrite H5 H6 //.

    + apply r_put_vs_put.
      eapply rsame_head_alt.
      1-3: by try apply prog_valid.
      intros x.
      ssprove_restore_mem.
      2: by apply r_ret.
      ssprove_invariant.
      1-3: intros s0 s1 h'; unfold couple_cross, couple_rhs; simpl; get_heap_simpl.
      2: done.
      1: destruct h' as [[[[[H1 H2] H3] H4] H5] H6]; rewrite H5 H6 //.
      destruct h' as [[[[[H1 H2] H3] H4] H5] H6].
      rewrite /couple_rhs //= /R in H1.
      rewrite H3 //= in H1.
    + rewrite H.
      apply r_put_vs_put.
      eapply rsame_head_alt.
      1-3: by try apply prog_valid.
      intros x.
      ssprove_restore_mem.
      2: by apply r_ret.
      ssprove_invariant.
      1-3: intros s0 s1 h'; unfold couple_cross, couple_rhs; simpl; get_heap_simpl.
      2: done.
      1: destruct h' as [[[[[H1 H2] H3] H4] H5] H6]; rewrite H5 H6 //.
      destruct h' as [[[[[H1 H2] H3] H4] H5] H6].
      rewrite /couple_rhs //= /R in H1.
      unfold R.
      rewrite ltnNge H //=.
      rewrite H3 ltnNge (ltnW H) // in H1.
Qed.

Notation inv' i := (
  heap_ignore (fset [:: count_loc ])
  ⋊ couple_lhs (mpk_loc P) mpk_loc' eq
  ⋊ couple_rhs (mpk_loc P) mpk_loc' eq
  ⋊ couple_lhs count_loc count_loc' (R i%N)
  ⋊ couple_rhs count_loc count_loc' (R i.+1)
).

Ltac replace_true e :=
  replace e with true in * by (symmetry; apply /ltP; lia).

Ltac replace_false e :=
  replace e with false in * by (symmetry; apply /ltP; lia).

Lemma SLIDE_succ_perfect {n} {i} : perfect (I_CPA P)
  (SLIDE n i ∘ OT_CPA P false) (SLIDE n i.+1 ∘ OT_CPA P true).
Proof.
  nssprove_share.
  eapply prove_perfect.
  apply (eq_rel_perf_ind _ _ (inv' i)).
  1: simpl; ssprove_invariant; try done; fset_solve.
  simplify_eq_rel m.
  - destruct m; simpl.
    simplify_linking.
    rewrite 2!cast_fun_K.
    ssprove_code_simpl.
    simplify_linking.
    rewrite cast_fun_K.
    ssprove_code_simpl.
    eapply rsame_head_alt. 1-3: by try apply prog_valid.
    move=> [_ pk].
    apply r_put_vs_put.
    apply r_put_vs_put.
    ssprove_restore_pre.
    2: by apply r_ret.
    by ssprove_invariant.

  - apply r_get_vs_get_remember.
    1: ssprove_invariant.
    intros c.
    ssprove_code_simpl.
    ssprove_sync => /ltP H.
    ssprove_swap_lhs 0%N; ssprove_swap_rhs 0%N.
    apply r_get_vs_get_remember.
    1: ssprove_invariant.
    intros mpk.
    ssprove_swap_lhs 0%N; ssprove_swap_rhs 0%N.
    ssprove_sync => H'.

    destruct (c < i)%N eqn:E1; move: E1 => /ltP E1.
    { replace_true (c < i.+1).
      apply r_put_vs_put.
      eapply rsame_head_alt. 1-3: by try apply prog_valid.
      intros x.
      ssprove_restore_mem.
      2: by apply r_ret.
      ssprove_invariant.
      + move=> h0 h1 //= [[[[H0 H1] _] _] _].
        rewrite /R /couple_lhs H1 in H0 |- *.
        get_heap_simpl.
        replace_false (i < c).
        by replace_false (i < c.+1).
      + move=> h0 h1 //= [[[[H0 _] H1] _] _].
        rewrite /R /couple_rhs H1 in H0 |- *.
        get_heap_simpl.
        replace_false (i.+1 < c).
        by replace_false (i.+1 < c.+1).
    }
    destruct (c == i)%B eqn:E2; move: E2 => /eqP E2.
    { subst; replace_false (i < i).
      ssprove_code_simpl.
      ssprove_swap_lhs 0%N.
      apply r_get_remember_lhs => c'.
      eapply (r_rem_couple_lhs count_loc count_loc').
      1-3: exact _.
      rewrite //= /R.
      replace_false (i < i).
      move=> /eqP -> {c'}.
      ssprove_code_simpl_more.
      ssprove_code_simpl.
      ssprove_code_simpl_more.
      ssprove_swap_seq_lhs [:: 1%N ; 0%N ].
      apply r_get_remember_lhs => mpk'.
      eapply (r_rem_couple_lhs (mpk_loc P) mpk_loc').
      1-3: exact _.
      intros; subst.
      apply r_put_vs_put.
      apply r_put_lhs.
      rewrite H' //=.
      replace_true (i < i.+1).
      eapply rsame_head_alt. 1-3: by try apply prog_valid.
      intros x.
      ssprove_restore_mem.
      2: by apply r_ret.
      ssprove_invariant.
      + by replace_true (eqn (i.+1 - i.+1)%Nrec 0).
      + move=> h0 h1 //= [[[[[[H0 _] H1] _] _] _] _].
        rewrite /R /couple_rhs H1 in H0 |- *.
        get_heap_simpl.
        replace_false (eqn (i.+2 - i.+1)%Nrec 0).
        by replace_false (eqn (i.+2 - i)%Nrec 0).
    }
    destruct (c == i.+1)%B eqn:E3; move: E3 => /eqP E3.
    { subst; replace_true (i < i.+1).
      replace_false (i.+1 < i.+1).
      ssprove_code_simpl.
      ssprove_swap_rhs 0%N.
      apply r_get_remember_rhs => c'.
      eapply (r_rem_couple_rhs count_loc count_loc').
      1-3: exact _.
      rewrite //= /R.
      replace (i.+1 < i.+1) with false by (symmetry; apply /ltP; lia).
      move=> /eqP -> {c'}.
      ssprove_code_simpl_more.
      ssprove_code_simpl.
      ssprove_code_simpl_more.
      destruct mpk as [pk|] => //=.
      ssprove_swap_seq_rhs [:: 1%N ; 0%N ].
      apply r_get_remember_rhs => mpk'.
      eapply (r_rem_couple_rhs (mpk_loc P) mpk_loc').
      1-3: exact _.
      move=> -> //= {mpk'}.
      apply r_put_vs_put.
      apply r_put_rhs.
      eapply rsame_head_alt.  1-3: by try apply prog_valid.
      intros x.
      ssprove_restore_mem.
      2: by apply r_ret.
      ssprove_invariant.
      + move=> h0 h1 //= [[[[[[H0 H1] _] _] _] _] _].
        rewrite /R /couple_lhs H1 in H0 |- *.
        get_heap_simpl.
        replace_true (eqn (i.+1 - i.+2)%Nrec 0).
        by replace_true (eqn (i.+1 - i.+1)%Nrec 0).
      + by replace_true (eqn (i.+2 - i.+2)%Nrec 0).
    }
    destruct (c > i.+1)%N eqn:E4; move: E4 => /ltP E4; [| lia ].
    { replace_true (i < c).
      replace_false (c < i.+1).
      apply r_put_vs_put.
      rewrite bind_ret.
      ssprove_restore_mem.
      2: eapply r_reflexivity_alt; [ apply prog_valid | |]; done.
      ssprove_invariant.
      + move=> h0 h1 //= [[[[H0 H1] _] _] _].
        rewrite /R /couple_lhs H1 in H0 |- *.
        get_heap_simpl.
        replace_true (i < c.+1).
        by replace_true (i < c).
      + move=> h0 h1 //= [[[[H0 _] H1] _] _].
        rewrite /R /couple_rhs H1 in H0 |- *.
        get_heap_simpl.
        replace_true (i.+1 < c).
        by replace_true (i.+1 < c.+1).
    }
Qed.

#[local] Open Scope ring_scope.

Theorem Adv_CPA_OT {n} (A : adversary (I_CPA P)) :
  AdvFor (MT_CPA P n) A <= \sum_(i < n) AdvFor (OT_CPA P) (A ∘ SLIDE n i).
Proof.
  apply: (@hybrid_reduction _ A (λ n b, {game _ ; MT_CPA P n b }) (SLIDE n)).
  2,3: apply: PK_CPA_SLIDE_perfect.
  apply: @SLIDE_succ_perfect.
Qed.

End Reductions.
