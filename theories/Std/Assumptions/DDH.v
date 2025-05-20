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

From NominalSSP Require Import Prelude Std.Math.Group.
Import PackageNotation.
#[local] Open Scope package_scope.

Import GroupScope.

Section DDH.

  Context (G : CyclicGroup).

  Definition GETA := 0%N.
  Definition GETBC := 1%N.

  Definition I_DDH :=
    [interface
      [ GETA  ] : { 'unit ~> 'el G } ;
      [ GETBC ] : { 'unit ~> 'el G × 'el G }
    ].

  Definition mga_loc : Location := ('option 'el G; 3%N).

  Definition DDH bit :
    game I_DDH :=
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
