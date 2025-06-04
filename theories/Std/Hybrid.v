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
#[local] Open Scope package_scope.
#[local] Open Scope ring_scope.

Lemma hybrid_argument' {I}
  {A : adversary I} (H : nat → game I) ε :
  (∀ i, Adv (H i) (H i.+1) A <= ε i) →
  ∀ n, Adv (H 0) (H n) A <= \sum_(i < n) ε i.
Proof.
  intros P; elim.
  - rewrite Adv_same big_ord0 //.
  - move=> i IH. rewrite big_ord_recr //=.
    nssprove_adv_trans (H i)%sep.
    by apply Num.Theory.lerD.
Qed.

Theorem hybrid_argument {I} {A : adversary I}
  {G G' : game I} (H : nat → game I) ε n :
  perfect I G  (H 0) →
  (∀ i, Adv (H i) (H i.+1) A <= ε i) →
  perfect I G' (H n) →
  Adv G G' A <= \sum_(i < n) ε i.
Proof.
  intros H1 H2 H3.
  rewrite (Adv_perfect_l H1).
  rewrite (Adv_perfect_r H3).
  by apply hybrid_argument'.
Qed.

Theorem hybrid_reduction {I} {A : adversary I}
  {G : nat → bool → game I}
  (H : nat → module I I) n :
    (∀ i, perfect I (H i ∘ G 1 false)
                    (H i.+1 ∘ G 1 true)) →
    perfect I (G n true) (H 0 ∘ G 1 true) →
    perfect I (G n false) (H n ∘ G 1 true) →
    AdvFor (G n) A <=
      \sum_(i < n) AdvFor (G 1) (A ∘ H i).
Proof.
  intros H1 H2 H3.
  pose (H' := λ i, {game I; H i ∘ G 1 true}).
  apply (hybrid_argument H'
    (λ i, AdvFor (G 1) (A ∘ H i))).
  1: apply H2.
  2: apply H3.
  intros i; rewrite /AdvFor -Adv_sep_link.
  rewrite (Adv_perfect_r (H1 i)) //.
Qed.
