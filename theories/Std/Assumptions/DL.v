Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra fingroup.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8.
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

From NominalSSP.Std Require Import
  Math.Group Assumptions.CDH.

Section DL.

  Context (G : CyclicGroup).

  Definition SETUP := 668%N.
  Definition GUESS := 667%N.

  Definition I_DL :=
    [interface
      [ SETUP  ] : { 'unit ~> 'el G } ;
      [ GUESS ] : { 'exp G ~> 'bool }
    ].

  Definition mga_loc : Location := ('option 'el G; 84%N).

  Definition DL bit :
    game I_DL :=
    [module fset [:: mga_loc ] ;
      [ SETUP ] : { 'unit ~> 'el G } 'tt {
        a ← sample uniform #|exp G| ;;
        #put mga_loc := Some ('g ^ a)%pack ;;
        @ret ('el G) ('g ^ a)%pack
      } ;
      [ GUESS ] : { 'exp G ~> 'bool } (a') {
        ga ← getSome mga_loc ;;
        @ret 'bool (bit && ('g ^ a' == ga)%B)
      }
    ].

  Definition RCDH :
    module (I_CDH G) I_DL :=
    [module fset [:: mga_loc ] ;
      [ SETUP ] : { 'unit ~> 'el G } 'tt {
        '(ga, gb) ← call CDH.SETUP 'unit ('el G × 'el G) tt ;;
        #put mga_loc := Some ga ;;
        @ret ('el G) gb
      } ;
      [ GUESS ] : { 'exp G ~> 'bool } (b) {
        ga ← getSome mga_loc ;;
        b ← call CDH.GUESS ('el G) 'bool (ga ^ b)%pack ;;
        @ret 'bool b
      }
    ].

  Lemma RDDH_perf bit : perfect I_DL (DL bit) (RCDH ∘ CDH G bit).
  Proof.
    nssprove_share.
    eapply prove_perfect.
    apply (eq_rel_perf_ind _ _
      (heap_ignore (fset [:: mgab_loc G ; mga_loc ])
      ⋊ couple_rhs (mgab_loc G) mga_loc (λ mgab mga, isSome mgab = isSome mga)
      ⋊ couple_cross mga_loc mga_loc (λ m m', isSome m = isSome m')
    )).
    1: simpl; ssprove_invariant; try auto; fset_solve.
    simplify_eq_rel m.
    - destruct m.
      simpl. simplify_linking.
      apply r_const_sample_R.
      1: apply LosslessOp_uniform.
      intros a.
      ssprove_sync => b.
      apply r_put_rhs.
      apply r_put_vs_put.
      ssprove_restore_pre.
      2: by apply r_ret.
      ssprove_invariant.
      1: done.
      intros s0 s1 h'.
      unfold couple_cross.
      simpl.
      by get_heap_simpl.
    - ssprove_code_simpl.
      ssprove_code_simpl_more.
      eapply r_get_vs_get_cross.
      1: apply Cross_conj_right, Cross_couple_cross.
      intros mb mb' H.
      destruct mb; destruct mb' => //.
      2: apply r_fail.
      apply r_get_remember_rhs => a.
  Admitted.

End DL.
