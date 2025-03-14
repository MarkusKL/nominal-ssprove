Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
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
#[local] Open Scope ring_scope.
#[local] Open Scope package_scope.


Module PKScheme.


(* Public-key encryption schemes *)

Record pk_scheme :=
  { Sec : choice_type
  ; Pub : choice_type
  ; Mes : choice_type
  ; Cip : choice_type
  ; sample_Cip :
    code fset0 [interface] Cip
  ; keygen :
      code fset0 [interface] (Sec × Pub)
  ; enc : ∀ (pk : Pub) (m : Mes),
      code fset0 [interface] Cip
  ; dec : ∀ (sk : Sec) (c : Cip),
      code fset0 [interface] Mes
  }.

Notation " 'sec p " := (Sec p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'sec p " := (Sec p)
  (at level 3) : package_scope.

Notation " 'pub p " := (Pub p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'pub p " := (Pub p)
  (at level 3) : package_scope.

Notation " 'mes p " := (Mes p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'mes p " := (Mes p)
  (at level 3) : package_scope.

Notation " 'cip p " := (Cip p)
  (in custom pack_type at level 2, p constr at level 20).

Notation " 'cip p " := (Cip p)
  (at level 3) : package_scope.


(* Correctness property *)

Definition ENCDEC := 0%N.

Definition I_CORR (P : pk_scheme) :=
  [interface #val #[ ENCDEC ]
    : 'mes P → 'mes P ].

Definition CORR0 (P : pk_scheme) :
  game (I_CORR P) :=
  [module no_locs ;
    #def #[ ENCDEC ] (m : 'mes P)
        : ('mes P) {
      '(sk, pk) ← P.(keygen) ;;
      c ← P.(enc) pk m ;;
      m' ← P.(dec) sk c ;;
      ret m'
    }
  ].

Definition CORR1 (P : pk_scheme) :
  game (I_CORR P) :=
  [module no_locs ;
    #def #[ ENCDEC ] (m : 'mes P)
        : ('mes P) {
      ret m
    }
  ].

Definition CORR P b := if b then CORR0 P else CORR1 P.


(* Initialization code and rules *)

Definition init_loc (P : pk_scheme) : Location := ('option ('pub P); 1%N).

Definition init P : raw_code ('pub P) :=
  locked (
    mpk ← get init_loc P ;;
    match mpk with
    | None => 
      '(_, pk) ← P.(keygen) ;;
      #put init_loc P := Some pk ;;
      ret pk
    | Some pk => ret pk
    end ).

#[export] Instance init_valid {P} {L : {fset Location}} {I : Interface}
  : init_loc P \in L → ValidCode L I (init P).
Proof.
  intros H.
  rewrite /init -lock.
  ssprove_valid.
Qed.


(* Public-Key One-Time Secrecy Random ($) *)

Definition flag_loc : Location := ('option 'unit; 0%N).
Definition GET := 0%N.
Definition QUERY := 1%N.

Definition I_PK_OTSR (P : pk_scheme) :=
  [interface
    #val #[ GET ] : 'unit → 'pub P ;
    #val #[ QUERY ] : 'mes P → 'cip P
  ].

Definition PK_OTSR (P : pk_scheme) b :
  game (I_PK_OTSR P) :=
  [module fset
    [:: init_loc P ; flag_loc ] ;
    #def #[ GET ] (_ : 'unit)
        : ('pub P) {
      pk ← init P ;;
      ret pk
    } ;
    #def #[ QUERY ] (m : 'mes P)
        : ('cip P) {
      pk ← init P ;;
      getNone flag_loc ;;
      #put flag_loc := Some tt ;;
      if b then
        P.(enc) pk m
      else
        P.(sample_Cip)
    }
  ].


(* Public-Key One-Time Secrecy *)

Definition I_PK_OTS (P : pk_scheme) :=
  [interface
    #val #[ GET ] : 'unit → 'pub P ;
    #val #[ QUERY ] : 'mes P × 'mes P → 'cip P
  ].

Definition PK_OTS (P : pk_scheme) b :
  game (I_PK_OTS P) :=
  [module fset
    [:: init_loc P ; flag_loc ] ;
    #def #[ GET ] (_ : 'unit)
        : ('pub P) {
      pk ← init P ;;
      ret pk
    } ;
    #def #[ QUERY ] ('(m, m')
        : 'mes P × 'mes P) : ('cip P) {
      pk ← init P ;; 
      getNone flag_loc ;;
      #put flag_loc := Some tt ;;
      P.(enc) pk (if b then m else m')
    }
  ].


(* Public-Key n-time Chosen Plaintext Attack *)

Definition I_PK_CPA (P : pk_scheme) :=
  [interface
    #val #[ GET ] : 'unit → 'pub P ;
    #val #[ QUERY ] : 'mes P × 'mes P → 'cip P
  ].

Definition count_loc : Location := ('nat; 3%N).

Definition PK_CPA (P : pk_scheme) n b :
  game (I_PK_CPA P) :=
  [module fset
    [:: init_loc P ; count_loc ] ;
    #def #[ GET ] (_ : 'unit)
        : ('pub P) {
      pk ← init P ;;
      ret pk
    } ;
    #def #[ QUERY ] ('(m, m')
        : 'mes P × 'mes P) : ('cip P) {
      pk ← init P ;;
      count ← get count_loc ;; 
      #assert (count < n)%N ;;
      #put count_loc := count.+1 ;;
      P.(enc) pk (if b then m else m')
    }
  ].

End PKScheme.
