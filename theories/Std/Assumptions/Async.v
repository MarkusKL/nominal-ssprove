Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra.
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

Section Async.
  Context (F : finType).
  Context `{Positive #|F|}.

  Notation " 'F " := 'fin #|F|
    (at level 3) : package_scope.

  Definition SETUP := 30%N.
  Definition POP := 31%N.

  Definition I_ASYNC :=
    [interface
      [ SETUP  ] : { 'unit ~> 'unit } ;
      [ POP ] : { 'unit ~> 'F }
    ].

  Definition loc : Location := ('option 'F; 8%N).

  Definition EAGER :
    game I_ASYNC :=
    [module fset [:: loc ] ;
      [ SETUP ] : { 'unit ~> 'unit } 'tt {
        r ← sample uniform #|F| ;;
        #put loc := Some r ;;
        ret tt
      } ;
      [ POP ] : { 'unit ~> 'F } 'tt {
        r ← getSome loc ;;
        #put loc := None ;;
        @ret 'F r
      }
    ].

  Definition LAZY :
    game I_ASYNC :=
    [module fset [:: loc ] ;
      [ SETUP ] : { 'unit ~> 'unit } 'tt {
        #put loc := Some (chCanonical 'F) ;;
        ret tt
      } ;
      [ POP ] : { 'unit ~> 'F } 'tt {
        _ ← getSome loc ;;
        #put loc := None ;;
        r ← sample uniform #|F| ;;
        @ret 'F r
      }
    ].

  Definition ASYNC b := if b then EAGER else LAZY.

End Async.
