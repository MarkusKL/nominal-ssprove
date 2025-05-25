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
  Std.Math.Group Std.Assumptions.Async
  Std.Assumptions.DDH.
Import PackageNotation.
#[local] Open Scope package_scope.

Import Num.Def Num.Theory Order.POrderTheory.
#[local] Open Scope ring_scope.
Import GroupScope GRing.Theory.

Import GroupScope.

Section CDH.

  Context (G : CyclicGroup).

  Definition SETUP := 60%N.
  Definition GUESS := 61%N.

  Definition I_CDH :=
    [interface
      [ SETUP  ] : { 'unit ~> 'el G × 'el G } ;
      [ GUESS ] : { 'el G ~> 'bool }
    ].

  Definition mgab_loc : Location := ('option 'el G; 48%N).

  Definition CDH bit :
    game I_CDH :=
    [module fset [:: mgab_loc ] ;
      [ SETUP ] : { 'unit ~> 'el G × 'el G } 'tt {
        a ← sample uniform #|exp G| ;;
        b ← sample uniform #|exp G| ;;
        #put mgab_loc := Some (('g ^ a) ^ b)%pack ;;
        @ret ('el G × 'el G) ('g ^ a, 'g ^ b)%pack
      } ;
      [ GUESS ] : { 'el G ~> 'bool } (g) {
        gab ← getSome mgab_loc ;;
        @ret 'bool (bit && (g == gab)%B)
      }
    ].


  Definition RDDH :
    module (I_DDH G) I_CDH :=
    [module fset [:: mgab_loc ] ;
      [ SETUP ] : { 'unit ~> 'el G × 'el G } 'tt {
        '(ga, gb, gc) ← call DDH.GETABC 'unit ('el G × 'el G × 'el G) tt ;;
        #put mgab_loc := Some gc ;;
        @ret ('el G × 'el G) (ga, gb)%pack
      } ;
      [ GUESS ] : { 'el G ~> 'bool } (g) {
        gab ← getSome mgab_loc ;;
        @ret 'bool (g == gab)%B
      }
    ].

  Lemma RDDH_perf : perfect I_CDH (CDH true) (RDDH ∘ DDH G true).
  Proof.
    nssprove_share.
    eapply prove_perfect.
    apply (eq_rel_perf_ind_eq).
    simplify_eq_rel m.
    - destruct m.
      simpl. simplify_linking.
      apply r_refl.
    - ssprove_code_simpl.
      apply r_refl.
  Qed.

  Definition I_GUESSES :=
    [interface
      [ SETUP ] : { 'unit ~> 'unit } ;
      [ GUESS ] : { 'el G ~> 'bool }
    ].

  Definition GUESSES b :
    game I_GUESSES :=
    [module fset [:: mgab_loc ] ;
      [ SETUP ] : { 'unit ~> 'unit } 'tt {
        gc ← sample uniform #|el G| ;;
        #put mgab_loc := Some gc ;;
        @ret 'unit tt
      } ;
      [ GUESS ] : { 'el G ~> 'bool } (g) {
        gab ← getSome mgab_loc ;;
        @ret 'bool (b && (g == gab))%B
      }
    ].

  Definition RGUESSES :
    module I_GUESSES I_CDH :=
    [module no_locs ;
      [ SETUP ] : { 'unit ~> 'el G × 'el G } 'tt {
        a ← sample uniform #|exp G| ;;
        b ← sample uniform #|exp G| ;;
        call SETUP 'unit 'unit tt ;;
        @ret ('el G × 'el G) ('g ^ a, 'g ^ b)%pack
      } ;
      [ GUESS ] : { 'el G ~> 'bool } (g) {
        b ← call GUESS 'el G 'bool g ;;
        @ret 'bool b
      }
    ].

  Lemma RDDH_RASYNC_perf
    : perfect I_CDH (RDDH ∘ DDH G false) (RGUESSES ∘ GUESSES true).
  Proof.
    nssprove_share.
    eapply prove_perfect.
    apply (eq_rel_perf_ind_eq).
    simplify_eq_rel m.
    - destruct m.
      simpl. simplify_linking.
      ssprove_sync_eq => a.
      ssprove_sync_eq => b.
      eapply r_uniform_bij.
      1: shelve.
      intros c.
      apply r_refl.
      Unshelve.
      exists (λ gc, fto (log (otf gc))).
      + intros x.
        rewrite 2!otf_fto.
        erewrite expg_log => //.
        rewrite fto_otf //.
      + intros x.
        rewrite 2!otf_fto.
        erewrite log_expg => //.
        rewrite fto_otf //.
    - ssprove_code_simpl.
      simplify_linking.
      ssprove_code_simpl_more.
      apply r_refl.
  Qed.

  Lemma RGUESSES_CDH_perf
    : perfect I_CDH (RGUESSES ∘ GUESSES false) (CDH false).
  Proof.
    nssprove_share.
    eapply prove_perfect.
    apply (eq_rel_perf_ind _ _
      (heap_ignore (fset [:: mgab_loc ])
      ⋊ couple_cross mgab_loc mgab_loc (λ mgab mgab', mgab = mgab' :> bool)
    )).
    1: simpl; ssprove_invariant; try auto; fset_solve.
    simplify_eq_rel m.
    - destruct m.
      simpl. simplify_linking.
      ssprove_sync => a.
      ssprove_sync => b.
      apply r_const_sample_L.
      1: apply LosslessOp_uniform.
      intros c.
      apply r_put_vs_put.
      ssprove_restore_pre.
      2: by apply r_ret.
      ssprove_invariant.
      intros s0 s1 h'.
      unfold couple_cross.
      simpl.
      by get_heap_simpl.
    - simplify_linking.
      ssprove_code_simpl_more.
      eapply r_get_vs_get_cross.
      1: apply Cross_conj_right, Cross_couple_cross.
      intros mc mc' H.
      destruct mc; destruct mc' => //=.
      2: apply r_fail.
      1: apply r_forget_rhs, r_forget_lhs.
      1: by apply r_ret.
  Qed.

  Theorem CDH_DDH (A : adversary I_CDH) :
    AdvFor CDH A
    <= AdvFor (DDH G) (A ∘ RDDH)
     + AdvFor GUESSES (A ∘ RGUESSES).
  Proof.
    unfold AdvFor.
    erewrite (Adv_perfect_l RDDH_perf).
    nssprove_adv_etrans.
    apply lerD; [ rewrite -Adv_sep_link; by apply eq_ler |].
    erewrite (Adv_perfect_l RDDH_RASYNC_perf).
    rewrite -Adv_sep_link.
    by rewrite (Adv_perfect_r RGUESSES_CDH_perf).
  Qed.

End CDH.
