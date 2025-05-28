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

From NominalSSP.Std Require Import Math.Group Assumptions.DDH PKE.Scheme.

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
    ssprove_sync => H.
    ssprove_swap_lhs 0%N; ssprove_swap_rhs 0%N.
    apply r_get_vs_get_remember.
    1: ssprove_invariant.
    intros mpk.
    ssprove_swap_lhs 0%N; ssprove_swap_rhs 0%N.
    ssprove_sync => H'.

    destruct (c < i)%N eqn:E1.
    { rewrite ltnS (ltnW E1) bind_ret.
      apply r_put_vs_put.
      ssprove_restore_mem.
      2: eapply r_reflexivity_alt; [ apply prog_valid | |]; done.
      move: H E1 => /ltP H /ltP E1.
      ssprove_invariant.
      + move=> h0 h1 //= [[[[H0 H1] _] _] _].
        rewrite /R /couple_lhs H1 in H0 |- *.
        get_heap_simpl.
        replace (i < c) with false in H0 by (symmetry; apply /ltP; lia).
        by replace (i < c.+1) with false by (symmetry; apply /ltP; lia).
      + move=> h0 h1 //= [[[[H0 _] H1] _] _].
        rewrite /R /couple_rhs H1 in H0 |- *.
        get_heap_simpl.
        replace (i.+1 < c) with false in H0 by (symmetry; apply /ltP; lia).
        by replace (i.+1 < c.+1) with false by (symmetry; apply /ltP; lia).
    }
    destruct (c == i)%B eqn:E2.
    { move: E2 => /eqP ->.
      rewrite ltnn ltnS leqnn.
      ssprove_code_simpl.
      ssprove_swap_lhs 0%N.
      apply r_get_remember_lhs => c'.
      eapply (r_rem_couple_lhs count_loc count_loc').
      1-3: exact _.
      rewrite //= /R.
      replace (i < i) with false by (symmetry; apply /ltP; lia).
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
      eapply rsame_head_alt.  1-3: by try apply prog_valid.
      intros x.
      ssprove_restore_mem.
      2: by apply r_ret.
      ssprove_invariant.
      + by replace (eqn (i.+1 - i.+1)%Nrec 0) with true by (symmetry; apply /ltP; lia).
      + move=> h0 h1 //= [[[[[[H0 _] H1] _] _] _] _].
        rewrite /R /couple_rhs H1 in H0 |- *.
        get_heap_simpl.
        admit.
    }
    destruct (c == i.+1)%B eqn:E3.
    { move: E3 => /eqP ->.
      rewrite ltnn ltnS leqnn.
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
      + admit.
      + by replace (eqn (i.+2 - i.+2)%Nrec 0) with true by (symmetry; apply /ltP; lia).
    }
    destruct (c > i.+1)%N eqn:E4.
    { replace (i < c)%N with true.
      2: rewrite ltnW //.
      replace (c < i.+1)%N with false.
      2: rewrite ltnNge ltnW //.
      apply r_put_vs_put.
      rewrite bind_ret.
      ssprove_restore_mem.
      2: eapply r_reflexivity_alt; [ apply prog_valid | |]; done.
      ssprove_invariant.
      + admit.
      + admit.
    }
    move: E1 E2 E3 E4 => /ltP E1 /eqP E2 /eqP E3 /ltP E4.
    lia.
Admitted.

#[local] Open Scope ring_scope.

Theorem Hybrid_lemma' {I}
  {G : bool → game I} {A : adversary I} (H : nat → module I I) :
    (∀ i, perfect I (H i ∘ G false) (H i.+1 ∘ G true)) →
  ∀ n,
    Adv (H 0 ∘ G true) (H n ∘ G true) A <= \sum_(0 <= i < n) AdvFor G (A ∘ H i).
Proof.
  intros H' n.
  elim: n => [|j IH].
  - rewrite Adv_same big_nil //.
  - rewrite big_nat_recr //=.
    nssprove_adv_trans (H j ∘ G true)%sep.
    apply Num.Theory.lerD; [ apply IH |].
    rewrite -(Adv_perfect_r (H' j)) Adv_sep_link //.
Qed.

Theorem Hybrid_lemma {I}
  {G : nat → bool → game I} {A : adversary I} (H : nat → module I I) :
    (∀ i, perfect I (H i ∘ G 1 false) (H i.+1 ∘ G 1 true)) →
  ∀ n,
    perfect I (G n true) (H 0 ∘ G 1 true) →
    perfect I (G n false) (H n ∘ G 1 true) →
    AdvFor (G n) A <= \sum_(0 <= i < n) AdvFor (G 1) (A ∘ H i).
Proof.
  intros H' n Hl Hr.
  rewrite /AdvFor (Adv_perfect_l Hl) (Adv_perfect_r Hr).
  clear Hl Hr.
  apply: (Hybrid_lemma' H).
  apply H'.
Qed.

Theorem Hybrid_lemma_any {I} {p}
  {G : nat → bool → game I} {A : adversary I} (H : nat → module I I) :
    (∀ i, perfect I (H i ∘ G 1 false) (H i.+1 ∘ G 1 true)) →
    (∀ i, AdvFor (G 1) (A ∘ H i) <= p) →
  ∀ n,
    perfect I (G n true) (H 0 ∘ G 1 true) →
    perfect I (G n false) (H n ∘ G 1 true) →
    AdvFor (G n) A <= p *+ n.
Proof.
  intros H1 H2 n H3 H4.
  eapply Order.le_trans; [ apply Hybrid_lemma |].
  1: apply H1.
  1: apply H3.
  1: apply H4.
  eapply Order.le_trans.
  - apply Num.Theory.ler_sum => i _. apply H2.
  - rewrite GRing.sumr_const_nat subn0 //.
Qed.

Theorem Adv_CPA_OT {n} (A : adversary (I_CPA P)) :
  AdvFor (MT_CPA P n) A <= \sum_(0 <= i < n) AdvFor (OT_CPA P) (A ∘ SLIDE n i).
Proof.
  apply: (@Hybrid_lemma _ (λ n b, {game _ ; MT_CPA P n b }) A (SLIDE n)).
  2,3: apply: PK_CPA_SLIDE_perfect.
  apply: @SLIDE_succ_perfect.
Qed.
