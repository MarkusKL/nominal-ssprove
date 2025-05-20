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


Module PKE.

Record scheme :=
  { Sec : choice_type
  ; Pub : choice_type
  ; Mes : choice_type
  ; Cip : choice_type
  ; sample_Cip :
    code fset0 [interface] Cip
  ; keygen :
      code fset0 [interface] (Sec × Pub)
  ; enc : ∀ (k : Pub) (m : Mes),
      code fset0 [interface] Cip
  ; dec : ∀ (k : Sec) (c : Cip),
      code fset0 [interface] Mes
  }.

Section Defs.
  Context (P : scheme).

  Definition ENCDEC := 0%N.

  Definition I_CORR :=
    [interface [ ENCDEC ] : { P.(Mes) ~> P.(Mes) } ].

  Definition CORR0 :
    game I_CORR :=
    [module no_locs ;
      [ ENCDEC ] : { P.(Mes) ~> P.(Mes) } (m) {
        '(sk, pk) ← P.(keygen) ;;
        c ← P.(enc) pk m ;;
        m' ← P.(dec) sk c ;;
        ret m'
      }
    ].

  Definition CORR1 :
    game I_CORR :=
    [module no_locs ;
      [ ENCDEC ] : { P.(Mes) ~> P.(Mes) } (m) {
        ret m
      }
    ].

  Definition CORR b := if b then CORR0 else CORR1.


  Definition flag_loc : Location := ('option 'unit; 0%N).
  Definition mpk_loc : Location := ('option P.(Pub); 1%N).
  Definition INIT := 0%N.
  Definition GET := 1%N.
  Definition QUERY := 2%N.

  Definition I_PK_OTSR :=
    [interface
      [ INIT ] : { 'unit ~> 'unit } ;
      [ GET ] : { 'unit ~> P.(Pub) } ;
      [ QUERY ] : { P.(Mes) ~> P.(Cip) }
    ].

  Definition PK_OTSR b :
    game I_PK_OTSR :=
    [module fset
      [:: mpk_loc ; flag_loc ] ;
      [ INIT ] : { 'unit ~> 'unit } 'tt {
        '(_, pk) ← P.(keygen) ;;
        #put mpk_loc := Some pk ;;
        ret tt
      } ;
      [ GET ] : { 'unit ~> P.(Pub) } 'tt {
        pk ← getSome mpk_loc ;;
        ret pk
      } ;
      [ QUERY ] : { P.(Mes) ~> P.(Cip) } (m) {
        pk ← getSome mpk_loc ;;
        getNone flag_loc ;;
        #put flag_loc := Some tt ;;
        if b then
          P.(enc) pk m
        else
          P.(sample_Cip)
      }
    ].

End Defs.

End PKE.
