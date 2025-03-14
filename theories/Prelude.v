Set Warnings "-notation-overridden,-ambiguous-paths,-notation-incompatible-format".
From mathcomp Require Import all_ssreflect all_algebra reals distr
  fingroup.fingroup realsum ssrnat ssreflect ssrfun ssrbool ssrnum eqtype choice
  seq.
Set Warnings "notation-overridden,ambiguous-paths,notation-incompatible-format".

From Coq Require Import Utf8 Lia.
From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

From extructures Require Import ord fset fmap fperm.

From Crypt Require Export pkg_composition Prelude Package.

From NominalSSP Require Export FsetSolve Nominal Fresh Pr NomPackage Disjoint SSProve.
Export FsetSolve.


Import PackageNotation.
#[local] Open Scope ring_scope.
#[local] Open Scope package_scope.


Hint Extern 10 (ValidCode ?L ?I ?c.(prog)) =>
  eapply valid_injectLocations;
    [| eapply valid_injectMap;
      [| eapply prog_valid ]]; fset_solve
  : typeclass_instances ssprove_valid_db.

Hint Extern 10 (ValidCode ?L ?I (?p ∙ ?c.(prog))) =>
  eapply valid_injectLocations;
    [| eapply valid_injectMap;
      [| eapply mcode_valid, prog_valid ]]; fset_solve
  : typeclass_instances ssprove_valid_db.

Hint Extern 10 (is_true (_ \in _)) =>
  fset_solve : typeclass_insatnces ssprove_valid_db.


Lemma idents_cons {n a b}
  : idents (fset (cons (n, a) b)) = n |: idents (fset b).
Proof. 
  unfold idents.
  rewrite 2!imfset_fset //=.
  rewrite fset_cons //.
Qed.

(* add rule based on idents fset0? *)
Lemma idents0 : idents fset0 = fset0.
Proof. by rewrite /idents imfset0. Qed.

#[export] Hint Rewrite @idents_cons @idents0 : in_fset_eq.

#[export] Hint Rewrite @domm_set @domm0 @domm_ID : in_fset_eq.

Lemma domm_link {P Q} : domm (link P Q) = domm P.
Proof. apply domm_map. Qed.

Lemma domm_par {P Q} : domm (par P Q) = domm P :|: domm Q.
Proof. apply domm_union. Qed.

#[export] Hint Rewrite @domm_link @domm_par : in_fset_eq.

#[export] Hint Unfold Location : in_fset_eq.


(* Location disjointness hints *)

Lemma supp1 {X : nomOrdType} {x : X} : supp (fset1 x) = supp x.
Proof. apply fsetSupp1. Qed.

Lemma supp_cons {X : nomOrdType} {x : X} {xs}
  : supp (fset (cons x xs)) = supp x :|: supp (fset xs).
Proof. by rewrite fset_cons supp_fsetU supp1. Qed.

Lemma supp_nil {X : nomOrdType}
  : supp (fset (@nil X)) = fset0.
Proof. by rewrite -fset0E supp0. Qed.

Lemma supp_Location (l : Location) : supp l = fset1 (atomize l.π2).
Proof. destruct l. rewrite /supp //. Qed.

#[export] Hint Rewrite @supp_cons @supp_nil @supp_Location : in_fset_eq.

Lemma rename_fset0 {X : actionOrdType} {π} : π ∙ fset0 = @fset0 X.
Proof. rewrite /rename /= imfset0 //. Qed.

#[export] Hint Rewrite <- @supp_equi : in_fset_eq.
#[export] Hint Rewrite @rename_fset0 @supp0 : in_fset_eq.

Lemma supp_mod {I E} (P : module I E)
  : supp (mod P) = supp (module_locs P).
Proof.
  done.
Qed.

#[export] Hint Rewrite @supp_mod : in_fset_eq.

Lemma supp_raw_module (P : raw_module) : supp P = supp (loc P).
Proof. done. Qed.
(* this hint does not reduce nicely with fset_solve
#[export] Hint Rewrite @supp_raw_module : in_fset_eq.
 *)

#[export] Hint Rewrite @s_share_par @s_share_link : in_fset_eq.

Create HintDb disj_db.
#[export] Hint Resolve disj_share_link disj_share_link2 : disj_db.
#[export] Hint Resolve disj_ID_r disj_ID_l : disj_db.

Lemma disj_par_link {X : nomType} {P Q} {x : X}
  : disj x P → disj x Q → disj x (P || Q)%share.
Proof.
  apply disj_equi2, equi_share_par.
Qed.

Lemma disj_par_link2 {X : nomType} {P Q} {x : X}
  : disj P x → disj Q x → disj (P || Q)%share x.
Proof.
  rewrite disjC (disjC Q x).
  apply disj_equi2', equi_share_par.
Qed.

#[export] Hint Resolve disj_par_link disj_par_link2 : disj_db.


Ltac nssprove_abstract_help :=
  match goal with
  | [ H : is_true (disj _ _) |- _ ] => move: H; nssprove_abstract_help
  | _ => idtac (*unfold disj; fset_solve*)
  end.

#[export] Hint Extern 5 (is_true (disj _ _)) =>
  nssprove_abstract_help;
  unfold disj;
  repeat rewrite -supp_equi;
  rewrite !supp_mod //=;
  fset_solve
  : disj_db.

Ltac nssprove_separate_solve :=
  auto with disj_db nocore.
(*
  match goal with
  | [ H : is_true (disj _ _) |- _ ] => move: H; nssprove_separate_solve
  | _ => auto with disj_db (*unfold disj; fset_solve*)
  end.
 *)

Ltac nssprove_separate_once :=
  (rewrite -> share_link_sep_link by nssprove_separate_solve)
  || (rewrite -> share_par_sep_par by nssprove_separate_solve)
  || (rewrite -> rename_alpha)
  || reflexivity.

Ltac nssprove_separate :=
  repeat nssprove_separate_once.


Ltac nssprove_share_once :=
  (rewrite <- share_link_sep_link by nssprove_separate_solve)
  || (rewrite <- share_par_sep_par by nssprove_separate_solve)
  || (rewrite -> rename_alpha)
  || reflexivity.

Ltac nssprove_share :=
  repeat nssprove_share_once.


(* rename simplification *)

Lemma rename_bind {A B} {π} {c : raw_code A} {k : A → raw_code B}
  : π ∙ bind c k = bind (π ∙ c) (λ a, π ∙ k a).
Proof.
  rewrite /rename //=.
  induction c => //=.
  all: f_equal => //=.
  all: apply functional_extensionality => y //=.
Qed.

Lemma rename_ret {A : choiceType} {π} (a : A) :
  π ∙ ret a = ret a.
Proof. done. Qed.

Lemma rename_assert {A} {π : {fperm atom}} {b k}
  : π ∙ @assertD A b k = assertD b (λ x, π ∙ (k x)).
Proof.
  destruct b; done.
Qed.

Lemma rename_let {A B C : choiceType} {π} (ab : prod A B) (f : A → B → raw_code C) :
  π ∙ (let '(a, b) := ab in f a b) = let '(a, b) := ab in π ∙ f a b.
Proof. by destruct ab. Qed.

Lemma rename_code {π} {A L I} {c : code L I A} : π ∙ prog c = {code π ∙ c}.
Proof. done. Qed.

Lemma rename_scheme {I A} (c : code fset0 I A) π
  : π ∙ prog c = prog c.
Proof.
  destruct c as [c V].
  simpl.
  induction V => //=.
  - etransitivity.
    2: apply f_equal.
    2: apply functional_extensionality, H1.
    done.
  - etransitivity.
    2: apply f_equal.
    2: apply functional_extensionality, H0.
    done.
Qed.


#[export] Hint Extern 50 (_ = code_link _ _) =>
  rewrite code_link_scheme
  : ssprove_code_simpl.

#[export] Hint Extern 50 (_ = rename _ (@assertD ?A _ _)) =>
  rewrite (@rename_assert A)
  : ssprove_code_simpl.

#[export] Hint Extern 50 (_ = rename _ (bind _ _)) =>
  rewrite rename_bind
  : ssprove_code_simpl.

#[export] Hint Extern 50 (_ = rename _ (ret _)) =>
  rewrite rename_ret
  : ssprove_code_simpl.

#[export] Hint Extern 50 (_ = rename _ (let '(_, _) := _ in _)) =>
  rewrite rename_let
  : ssprove_code_simpl.

Notation call n S T a
  := (#import (mkopsig n S T) as F ;; b ← F a ;; ret b).

Notation "'getNone' n ;; c" :=
  ( v ← get n ;;
    #assert (v == None) ;;
    c
  )
  (at level 100, n at next level, right associativity,
  format "getNone  n  ;;  '//' c")
  : package_scope.

Notation "x ← 'getSome' n ;; c" :=
  ( v ← get n ;;
    #assert (isSome v) as vSome ;;
    let x := getSome v vSome in
    c
  )
  (at level 100, n at next level, right associativity,
  format "x  ←  getSome  n  ;;  '//' c")
  : package_scope.

#[export] Hint Extern 10 (is_true (_ \in _)) =>
  fset_solve : ssprove_invariant.
