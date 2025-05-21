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

From NominalSSP Require Import Prelude
  Std.Math.Group Std.Assumptions.Async.
Import PackageNotation.
#[local] Open Scope package_scope.

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

  Definition LRED bit :
    module (I_DDH G) (I_LDDH G) :=
    [module fset [:: mgb_loc ; mgc_loc ] ;
      [ GETA ] : { 'unit ~> 'el G } 'tt {
        '(ga, gb, gc) ← call GETABC 'unit ('el G × 'el G × 'el G) tt ;;
        #put mgb_loc := Some gb ;;
        #put mgc_loc := Some gc ;;
        ret ga
      } ;
      [ GETBC ] : { 'unit ~> 'el G × 'el G } 'tt {
        gb ← getSome mgb_loc G ;;
        #put mgb_loc := None ;;
        gc ← getSome mgc_loc G ;;
        #put mgc_loc := None ;;
        if bit then
          @ret ('el G × 'el G) ('g ^ b, ga ^ b)%pack
        else
          @ret ('el G × 'el G) ('g ^ b, 'g ^ c)%pack
      }
    ].

  Lemma HYB1_DDH_true : perfect (I_LDDH G) (HYB1 true ∘ EAGER (exp G)) (LRED true ∘ DDH true).
  Proof.
  Lemma HYB1_DDH_true : perfect (I_LDDH G) (HYB1 true) (HYB1 bit ∘ LAZY (exp G)).
  Proof.




  Definition HYB2 bit :
    module (I_ASYNC (exp G)) (I_LDDH G) :=
    [module fset [:: mga_loc G ; mb_loc ] ;
      [ GETA ] : { 'unit ~> 'el G } 'tt {
        a ← sample uniform #|exp G| ;;
        #put mga_loc G := Some ('g ^ a)%pack ;;
        b ← sample uniform #|exp G| ;;
        #put mb_loc := Some b ;;
        call SETUP 'unit 'unit tt ;;
        ret ('g ^ a)%pack
      } ;
      [ GETBC ] : { 'unit ~> 'el G × 'el G } 'tt {
        ga ← getSome mga_loc G ;;
        #put mga_loc G := None ;;
        b ← getSome mb_loc ;;
        #put mb_loc := None ;;
        if bit then
          @ret ('el G × 'el G) ('g ^ b, ga ^ b)%pack
        else
          c ← call POP 'unit ('exp G) tt ;;
          @ret ('el G × 'el G) ('g ^ b, 'g ^ c)%pack
      }
    ].

