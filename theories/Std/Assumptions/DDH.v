Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra
  fingroup reals distr realsum.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.
Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

From NominalSSP Require Import Prelude
  Std.Math.Group Std.Assumptions.Async.
Import PackageNotation.
#[local] Open Scope package_scope.

Import Num.Def Num.Theory Order.POrderTheory.
#[local] Open Scope ring_scope.
Import GroupScope GRing.Theory.

Import GroupScope.

Section DDH.

  Context (G : CyclicGroup).

  Definition GETA := 50%N.
  Definition GETBC := 51%N.
  Definition GETABC := 52%N.

  Definition I_DDH :=
    [interface
      [ GETABC  ] : { 'unit ~> 'el G × 'el G × 'el G }
    ].

  Definition DDH bit :
    game I_DDH :=
    [module no_locs ;
      [ GETABC ] : { 'unit ~> 'el G × 'el G × 'el G } 'tt {
        a ← sample uniform #|exp G| ;;
        b ← sample uniform #|exp G| ;;
        if bit then
          @ret ('el G × 'el G × 'el G) (('g ^ a, 'g ^ b), ('g ^ a) ^ b)%pack
        else
          c ← sample uniform #|exp G| ;;
          @ret ('el G × 'el G × 'el G) ('g ^ a, 'g ^ b, 'g ^ c)%pack
      }
    ].


  (* Lazy DDH *)

  Definition I_LDDH :=
    [interface
      [ GETA  ] : { 'unit ~> 'el G } ;
      [ GETBC ] : { 'unit ~> 'el G × 'el G }
    ].

  Definition mga_loc : Location := ('option 'el G; 3%N).

  Definition LDDH bit :
    game I_LDDH :=
    [module fset [:: mga_loc ] ;
      [ GETA ] : { 'unit ~> 'el G } 'tt {
        a ← sample uniform #|exp G| ;;
        #put mga_loc := Some ('g ^ a)%pack ;;
        ret ('g ^ a)%pack
      } ;
      [ GETBC ] : { 'unit ~> 'el G × 'el G } 'tt {
        ga ← getSome mga_loc ;;
        #put mga_loc := None ;;
        b ← sample uniform #|exp G| ;;
        if bit then
          @ret ('el G × 'el G) ('g ^ b, ga ^ b)%pack
        else
          c ← sample uniform #|exp G| ;;
          @ret ('el G × 'el G) ('g ^ b, 'g ^ c)%pack
      }
    ].

End DDH.


Section Reductions.
  Context (G : CyclicGroup).

  Definition HYB1 bit :
    module (I_ASYNC (exp G)) (I_LDDH G) :=
    [module fset [:: mga_loc G ] ;
      [ GETA ] : { 'unit ~> 'el G } 'tt {
        a ← sample uniform #|exp G| ;;
        #put mga_loc G := Some ('g ^ a)%pack ;;
        call SETUP 'unit 'unit tt ;;
        ret ('g ^ a)%pack
      } ;
      [ GETBC ] : { 'unit ~> 'el G × 'el G } 'tt {
        ga ← getSome mga_loc G ;;
        #put mga_loc G := None ;;
        b ← call POP 'unit ('exp G) tt ;;
        if bit then
          @ret ('el G × 'el G) ('g ^ b, ga ^ b)%pack
        else
          c ← sample uniform #|exp G| ;;
          @ret ('el G × 'el G) ('g ^ b, 'g ^ c)%pack
      }
    ].

  Lemma HYB1_perf bit : perfect (I_LDDH G) (LDDH G bit) (HYB1 bit ∘ LAZY (exp G)).
  Proof.
    nssprove_share.
    eapply prove_perfect.
    apply (eq_rel_perf_ind _ _
      (heap_ignore (fset [:: loc (exp G) ])
      ⋊ couple_rhs (mga_loc G) (loc (exp G)) (λ mga mb, isSome mga = isSome mb))).
    1: simpl; ssprove_invariant; try auto; fset_solve.
    simplify_eq_rel m; destruct m.
    - simpl. simplify_linking.
      ssprove_sync => a.
      apply r_put_vs_put.
      apply r_put_rhs.
      ssprove_restore_pre.
      2: by apply r_ret.
      by ssprove_invariant.
    - simpl. ssprove_code_simpl.
      apply r_get_vs_get_remember.
      1: ssprove_invariant.
      intros ga.
      ssprove_sync => H.
      destruct ga as [ga|] => //=.
      ssprove_swap_rhs 0%N.
      apply r_get_remember_rhs => b0.
      eapply (r_rem_couple_rhs (mga_loc G) (loc (exp G))).
      1,2,3: exact _.
      intros H'.
      destruct b0 as [b0|] => //=.
      apply r_put_vs_put.
      apply r_put_rhs.
      ssprove_sync => b.
      ssprove_restore_mem.
      1: by ssprove_invariant.
      destruct bit.
      + by apply r_ret.
      + ssprove_sync => ?.
        by apply r_ret.
  Qed.

  Definition mgb_loc : Location := ('option 'el G; 50%N).
  Definition mgc_loc : Location := ('option 'el G; 51%N).

  Definition LRED :
    module (I_DDH G) (I_LDDH G) :=
    [module fset [:: mga_loc G ; mgb_loc ; mgc_loc ] ;
      [ GETA ] : { 'unit ~> 'el G } 'tt {
        '(ga, gb, gc) ← call GETABC 'unit ('el G × 'el G × 'el G) tt ;;
        #put mga_loc G := Some ga ;;
        #put mgb_loc := Some gb ;;
        #put mgc_loc := Some gc ;;
        ret ga
      } ;
      [ GETBC ] : { 'unit ~> 'el G × 'el G } 'tt {
        _ ← getSome mga_loc G ;;
        #put mga_loc G := None ;;
        gb ← getSome mgb_loc ;;
        #put mgb_loc := None ;;
        gc ← getSome mgc_loc ;;
        #put mgc_loc := None ;;
        @ret ('el G × 'el G) (gb, gc)
      }
    ].

  Definition e (x : 'exp G) : 'el G := ('g ^ x)%pack.

  Definition R (mga mgb mgc : 'option 'el G) : Prop :=
    match mga, mgb with
    | Some ga, Some gb => mgc = Some (ga ^ fto (log (otf gb)))%pack
    | _, _ => True
    end.

  Lemma HYB1_DDH_true : perfect (I_LDDH G) (HYB1 true ∘ EAGER (exp G)) (LRED ∘ DDH G true).
  Proof.
    nssprove_share.
    eapply prove_perfect.
    apply (eq_rel_perf_ind _ _
      (heap_ignore (fset [:: loc (exp G) ; mgb_loc ; mgc_loc ])
      ⋊ couple_cross (loc (exp G)) mgb_loc (λ mb mgb, omap e mb = mgb)
      ⋊ triple_rhs (mga_loc G) mgb_loc mgc_loc R
    )).
    1: simpl; ssprove_invariant.
    1: fset_solve.
    1: done.
    1: done.
    
    simplify_eq_rel m; destruct m.
    - simpl. simplify_linking.
      ssprove_sync => a.
      ssprove_swap_lhs 0%N.
      ssprove_sync => b.
      apply r_put_vs_put.
      apply r_put_lhs.
      apply r_put_rhs.
      apply r_put_rhs.
      ssprove_restore_pre.
      1: ssprove_invariant.
      1: intros s0 s1 h.
      1: unfold couple_cross; simpl.
      1: by get_heap_simpl.
      1: rewrite -3!expgnE.
      1: simpl.
      1: rewrite 4!otf_fto.
      1: erewrite expg_log; [| reflexivity ]; done.
      by apply r_ret.
    - simpl. ssprove_code_simpl.
      ssprove_code_simpl_more.
      apply r_get_vs_get_remember.
      1: ssprove_invariant; fset_solve.
      intros a.
      ssprove_sync => H.
      destruct a as [a|] => //=.
      ssprove_swap_lhs 0%N.
      ssprove_swap_seq_rhs [:: 0%N ; 3%N ; 2%N ; 1%N ].
      eapply r_get_vs_get_cross.
      1: do 3 apply Cross_conj_left; apply Cross_conj_right, Cross_couple_cross.
      intros b gb h.
      ssprove_swap_lhs 0%N.
      ssprove_swap_seq_rhs [:: 1%N ; 0%N ].
      destruct b as [b|]; destruct gb as [gb|] => //=.
      2: eapply (r_fail ('el G × 'el G) ('el G × 'el G)).
      apply r_get_remember_rhs => c.
      eapply rpre_learn.
      1: intros s0 s1 [[[[[[[H0 H1] H2] H3] H4] H5] H6] H7].
      1: move: H2; unfold triple_rhs.
      1: rewrite H4 H6 H7 => H'.
      1: move: H1; unfold couple_cross.
      1: rewrite H5 H6 => H''.
      1: exact (H', H'').
      move=> //= [H' H''].
      noconf H''; subst.
      apply r_put_vs_put.
      apply r_put_lhs.
      do 2 apply r_put_rhs.
      simpl.
      erewrite expg_log.
      2: rewrite /e 2!otf_fto //.
      rewrite /e 2!otf_fto.
      ssprove_restore_mem.
      2: by apply r_ret.
      ssprove_invariant.
      2: apply I.
      intros s0 s1 h'.
      unfold couple_cross.
      simpl.
      by get_heap_simpl.
  Qed.

  Definition HYB2 :
    module (I_ASYNC (exp G)) (I_LDDH G) :=
    [module fset [:: mga_loc G ; mgb_loc ] ;
      [ GETA ] : { 'unit ~> 'el G } 'tt {
        a ← sample uniform #|exp G| ;;
            (*   #put mga_loc G := Some ('g ^ a)%pack ;;*)
        b ← sample uniform #|exp G| ;;
        #put mgb_loc := Some ('g ^ b)%pack ;;
        call SETUP 'unit 'unit tt ;;
        ret ('g ^ a)%pack
      } ;
      [ GETBC ] : { 'unit ~> 'el G × 'el G } 'tt {
        (*ga ← getSome mga_loc G ;;
           #put mga_loc G := None ;;*)
        gb ← getSome mgb_loc ;;
        #put mgb_loc := None ;;
        c ← call POP 'unit ('exp G) tt ;;
        @ret ('el G × 'el G) (gb, 'g ^ c)%pack
      }
    ].

  Lemma HYB2_LDDH_true : perfect (I_LDDH G) (HYB1 false ∘ EAGER (exp G)) (HYB2 ∘ LAZY (exp G)).
  Proof.
    nssprove_share.
    eapply prove_perfect.
    apply (eq_rel_perf_ind _ _
      (heap_ignore (fset [:: loc (exp G) ; mga_loc G ; mgb_loc ])
      ⋊ couple_lhs (mga_loc G) (loc (exp G)) (λ mga mb, isSome mga = isSome mb)
      ⋊ couple_rhs mgb_loc (loc (exp G)) (λ mgb mc, isSome mgb = isSome mc)
      ⋊ couple_cross (loc (exp G)) (mgb_loc) (λ mb mgb, mgb = omap e mb)
    )).
    1: simpl; ssprove_invariant.
    1: fset_solve.
    1,2,3: done.

    simplify_eq_rel m; destruct m.
    - simpl. simplify_linking.
      ssprove_sync => a.
      ssprove_swap_lhs 0%N.
      ssprove_sync => b.
      do 2 apply r_put_vs_put.
      ssprove_restore_pre.
      2: by apply r_ret.
      ssprove_invariant.
      1,2: done.
      intros s0 s1 h'.
      unfold couple_cross.
      simpl.
      by get_heap_simpl.
  - simpl. ssprove_code_simpl.
    ssprove_code_simpl_more.
    ssprove_swap_seq_lhs [:: 2 ; 1 ; 0 ]%N.
    eapply r_get_vs_get_cross.
    1: apply Cross_conj_right, Cross_couple_cross.
    move=> mb mgb //= H.
    ssprove_swap_seq_lhs [:: 2 ; 1 ; 0 ]%N.
    destruct mb as [b|]; destruct mgb as [gb|] => //=.
    2: eapply (r_fail ('el G × 'el G) ('el G × 'el G)).
    apply r_get_remember_lhs => mga.
    ssprove_swap_rhs 0%N.
    apply r_get_remember_rhs => mc.
    eapply (r_rem_couple_lhs (mga_loc G) (loc (exp G))).
    1,2,3: exact _.
    intros H'.
    eapply (r_rem_couple_rhs mgb_loc (loc (exp G))).
    1,2,3: exact _.
    intros H''.
    destruct mga as [ga|] => //.
    destruct mc as [c0|] => //=.
    noconf H.
    apply r_put_vs_put.
    apply r_put_vs_put.
    ssprove_sync => c.
    ssprove_restore_mem.
    2: by apply r_ret.
    ssprove_invariant.
    1,2: done.
    intros s0 s1 h'.
    unfold couple_cross.
    simpl.
    by get_heap_simpl.
  Qed.

  Lemma HYB2_LRED_false : perfect (I_LDDH G) (HYB2 ∘ EAGER (exp G)) (LRED ∘ DDH G false).
  Proof.
    nssprove_share.
    eapply prove_perfect.
    apply (eq_rel_perf_ind _ _
      (heap_ignore (fset [:: loc (exp G) ; mga_loc G ; mgc_loc ])
      ⋊ couple_rhs (mga_loc G) (mgb_loc) (λ mga mb, isSome mga = isSome mb)
      ⋊ couple_cross (loc (exp G)) (mgc_loc) (λ mc mgc, mgc = omap e mc)
    )).
    1: simpl; ssprove_invariant.
    1: fset_solve.
    1,2: done.

    simplify_eq_rel m; destruct m.
    - simpl. simplify_linking.
      ssprove_sync => a.
      ssprove_sync => b.
      ssprove_swap_lhs 0%N.
      ssprove_sync => c.
      apply r_put_rhs.
      apply r_put_vs_put.
      apply r_put_vs_put.
      ssprove_restore_pre.
      2: by apply r_ret.
      ssprove_invariant.
      1: done.
      intros s0 s1 h'.
      unfold couple_cross.
      simpl.
      by get_heap_simpl.
    - simpl. ssprove_code_simpl.
      ssprove_code_simpl_more.
      ssprove_swap_seq_lhs [:: 2 ; 1 ; 0 ]%N.
      ssprove_swap_seq_rhs [:: 5 ; 4 ; 3 ; 2 ; 1 ; 0 ]%N.
      eapply r_get_vs_get_cross.
      1: apply Cross_conj_right, Cross_couple_cross.
      move=> mc mgc //= H.

      apply r_get_remember_rhs => mga.
      ssprove_swap_seq_rhs [:: 1 ; 0 ; 2 ; 1 ]%N.
      apply r_get_vs_get_remember.
      1: ssprove_invariant; fset_solve.
      intros mgb.
      ssprove_sync => H'.
      destruct mgb as [gb|] => //=.
      eapply (r_rem_couple_rhs (mga_loc G) mgb_loc).
      1,2,3: exact _.
      intros H''.
      destruct mga as [ga|] => //=.
      apply r_put_rhs.
      apply r_put_vs_put.
      destruct mc as [c|] ; destruct mgc as [gc|] => //=.
      2: eapply (r_fail ('el G × 'el G) ('el G × 'el G)).
      apply r_put_vs_put.
      noconf H.
      ssprove_restore_mem.
      2: by apply r_ret.
      ssprove_invariant.
      1: done.
      intros s0 s1 h'.
      unfold couple_cross.
      simpl.
      by get_heap_simpl.
  Qed.

  Theorem LDDH_DDH (A : adversary (I_LDDH G)) :
    AdvFor (LDDH G) A
    <= AdvFor (ASYNC (exp G)) (A ∘ HYB1 true)
     + AdvFor (DDH G) (A ∘ LRED)
     + AdvFor (ASYNC (exp G)) (A ∘ HYB2)
     + AdvFor (ASYNC (exp G)) (A ∘ HYB1 false).
  Proof.
    rewrite (AdvFor_perfect HYB1_perf).
    nssprove_adv_etrans.
    rewrite -!addrA.
    apply lerD; [ apply eq_ler; rewrite /AdvFor -Adv_sep_link Adv_sym // |].
    rewrite (Adv_perfect_l HYB1_DDH_true).
    nssprove_adv_etrans.
    apply lerD; [ apply eq_ler; rewrite /AdvFor -Adv_sep_link // |].
    rewrite -(Adv_perfect_l HYB2_LRED_false).
    nssprove_adv_etrans.
    apply lerD; [ apply eq_ler; rewrite /AdvFor -Adv_sep_link // |].
    rewrite -(Adv_perfect_l HYB2_LDDH_true).
    rewrite Adv_sep_link //.
  Qed.

  Theorem LDDH_DDH0 (A : adversary (I_LDDH G)) :
    perfect (I_ASYNC (exp G)) (EAGER (exp G)) (LAZY (exp G))
    → AdvFor (LDDH G) A <= AdvFor (DDH G) (A ∘ LRED).
  Proof.
    intros H.
    eapply le_trans; [ apply LDDH_DDH |].
    unfold AdvFor.
    by erewrite -> H, H, H, GRing.add0r, GRing.addr0, GRing.addr0
      by nssprove_valid.
  Qed.

End Reductions.
