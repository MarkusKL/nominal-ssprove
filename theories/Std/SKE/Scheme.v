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


Module SKE.

Record scheme :=
  { Key : choice_type
  ; Mes : choice_type
  ; Cip : choice_type
  ; sample_Cip :
    code fset0 [interface] Cip
  ; keygen :
      code fset0 [interface] Key
  ; enc : ∀ (k : Key) (m : Mes),
      code fset0 [interface] Cip
  ; dec : ∀ (k : Key) (c : Cip),
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
        k ← P.(keygen) ;;
        c ← P.(enc) k m ;;
        m' ← P.(dec) k c ;;
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


  Definition QUERY := 5%N.

  Definition I_OTSR :=
    [interface [ QUERY ] : { P.(Mes) ~> P.(Cip) } ].

  Definition OTSR b :
    game I_OTSR :=
    [module no_locs ;
      [ QUERY ] : { P.(Mes) ~> P.(Cip) } (m) {
        if b then
          k ← P.(keygen) ;; (* run keygen only in real? *)
          P.(enc) k m
        else
          P.(sample_Cip)
      }
    ].
End Defs.

End SKE.
