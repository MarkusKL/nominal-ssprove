Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_core_definition choice_type pkg_composition pkg_rhl
  Package Prelude RandomOracle.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.

Import PackageNotation.

#[local] Open Scope ring_scope.


(* specialized theorems *)

Definition rel_jdg_replace_l
  (A B : choiceType) (pre : precond) (post : postcond A B) (l l' : raw_code A) (r : raw_code B)
    (Rest : ⊢ ⦃ pre ⦄ l ≈ r ⦃ post ⦄)
    (Left : l = l')
     : ⊢ ⦃ pre ⦄ l' ≈ r ⦃ post ⦄ :=
  (rel_jdg_replace _ _ _ _ _ _ _ _ Rest Left Logic.eq_refl).

Definition rel_jdg_replace_r
  (A B : choiceType) (pre : precond) (post : postcond A B) (l : raw_code A) (r r' : raw_code B)
    (Rest : ⊢ ⦃ pre ⦄ l ≈ r ⦃ post ⦄)
    (Right : r = r')
     : ⊢ ⦃ pre ⦄ l ≈ r' ⦃ post ⦄ :=
  (rel_jdg_replace _ _ _ _ _ _ _ _ Rest Logic.eq_refl Right).

Definition rel_jdg_replace_sem_l
  (A B : choiceType) (pre : precond) (post : postcond A B) (l l' : raw_code A) (r : raw_code B)
    (Rest : ⊢ ⦃ pre ⦄ l ≈ r ⦃ post ⦄)
    (Left : ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄ l ≈ l' ⦃ eq ⦄)
     : ⊢ ⦃ pre ⦄ l' ≈ r ⦃ post ⦄ :=
  (rel_jdg_replace_sem _ _ _ _ _ _ _ _ Rest Left (rreflexivity_rule _)).

Definition rel_jdg_replace_sem_r
  (A B : choiceType) (pre : precond) (post : postcond A B) (l : raw_code A) (r r' : raw_code B)
    (Rest : ⊢ ⦃ pre ⦄ l ≈ r ⦃ post ⦄)
    (Right : ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄ r ≈ r' ⦃ eq ⦄)
     : ⊢ ⦃ pre ⦄ l ≈ r' ⦃ post ⦄ :=
  (rel_jdg_replace_sem _ _ _ _ _ _ _ _ Rest (rreflexivity_rule _) Right).

Lemma r_refl {A : choiceType} : ∀ c : raw_code A,
  ⊢ ⦃ λ '(s₀, s₁), s₀ = s₁ ⦄ c ≈ c ⦃ λ '(a₀, s₀) '(a₁, s₁), a₀ = a₁ ∧ s₀ = s₁ ⦄.
Proof.
  intros c.
  eapply rpost_weaken_rule.
  1: apply rreflexivity_rule.
  intros [? ?] [? ?] ?.
  injection H => ? ?.
  by subst.
Qed.

Lemma rsame_head_ignore_prog :
  ∀ (A B : choiceType) (L0 L1 : {fset Location}) (m : code L0 (fset [::]) A) (f₀ f₁ : A → raw_code B) (post : postcond B B),
    fdisjoint L0 L1 →
    (∀ a : A, ⊢ ⦃ fun '(s0, s1) => heap_ignore L1 (s0, s1) ⦄ f₀ a ≈ f₁ a ⦃ post ⦄) →
    ⊢ ⦃ heap_ignore L1 ⦄ x ← m ;; f₀ x ≈ x ← m ;; f₁ x ⦃ post ⦄.
Proof.
  move => A B L0 L1 m f0 f1 post /fdisjointP Disj.
  eapply rsame_head_alt.
  + apply prog_valid.
  + intros l H.
    apply get_pre_cond_heap_ignore.
    by apply Disj.
  + intros l v _; apply put_pre_cond_heap_ignore.
Qed.

Lemma rpre_learn {A₀ A₁ : choiceType} {P : Type}
  : ∀ (m₀ : raw_code A₀) (m₁ : raw_code A₁)
      (pre : precond) (post : postcond A₀ A₁),
      (∀ s₀ s₁, pre (s₀, s₁) → P)
      → (P → ⊢ ⦃ pre ⦄ m₀ ≈ m₁ ⦃ post ⦄)
      → ⊢ ⦃ pre ⦄ m₀ ≈ m₁ ⦃ post ⦄.
Proof.
  intros m0 m1 pre post H1 H2.
  apply rpre_hypothesis_rule => s0 s1 H3.
  specialize (H1 s0 s1 H3).
  specialize (H2 H1).
  eapply rpre_weaken_rule; [ apply H2 |] => s0' s1' //= [H4 H5].
  by subst.
Qed.

Lemma r_rem_lhs {A₀ A₁ : choiceType}
  : ∀ (l : Location) (m₀ : raw_code A₀) (m₁ : raw_code A₁)
      (pre : precond) (post : postcond A₀ A₁),
      (∀ v, ⊢ ⦃ λ '(s0, s1), (pre ⋊ rem_lhs l v) (s0, s1) ⦄ m₀ ≈ m₁ ⦃ post ⦄)
      → ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄ m₀ ≈ m₁ ⦃ post ⦄.
Proof.
  intros l m0 m1 pre post H.
  apply rpre_hypothesis_rule => s0 s1 H'.
  eapply rpre_weaken_rule; [ apply H |].
  instantiate (1 := get_heap s0 l).
  move=> s0' s1' [H1 H2]; subst.
  split; auto.
  reflexivity.
Qed.

Lemma r_rem_rhs {A₀ A₁ : choiceType}
  : ∀ (l : Location) (m₀ : raw_code A₀) (m₁ : raw_code A₁)
      (pre : precond) (post : postcond A₀ A₁),
      (∀ v, ⊢ ⦃ λ '(s0, s1), (pre ⋊ rem_rhs l v) (s0, s1) ⦄ m₀ ≈ m₁ ⦃ post ⦄)
      → ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄ m₀ ≈ m₁ ⦃ post ⦄.
Proof.
  intros l m0 m1 pre post H.
  apply rpre_hypothesis_rule => s0 s1 H'.
  eapply rpre_weaken_rule; [ apply H |].
  instantiate (1 := get_heap s1 l).
  move=> s0' s1' [H1 H2]; subst.
  split; auto.
  reflexivity.
Qed.

Lemma r_remembers_lhs {A₀ A₁ : choiceType}
  : ∀ (l : Location) (m₀ : raw_code A₀) (m₁ : raw_code A₁)
      (pre : precond) (post : postcond A₀ A₁) v,
      Remembers_lhs l v pre
      → ⊢ ⦃ λ '(s0, s1), (pre ⋊ rem_lhs l v) (s0, s1) ⦄ m₀ ≈ m₁ ⦃ post ⦄
      → ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄ m₀ ≈ m₁ ⦃ post ⦄.
Proof.
  intros l m0 m1 pre post v H H'.
  eapply rpre_weaken_rule; [ apply H' |].
  split; auto.
Qed.

Lemma r_remembers_rhs {A₀ A₁ : choiceType}
  : ∀ (l : Location) (m₀ : raw_code A₀) (m₁ : raw_code A₁)
      (pre : precond) (post : postcond A₀ A₁) v,
      Remembers_rhs l v pre
      → ⊢ ⦃ λ '(s0, s1), (pre ⋊ rem_rhs l v) (s0, s1) ⦄ m₀ ≈ m₁ ⦃ post ⦄
      → ⊢ ⦃ λ '(s0, s1), pre (s0, s1) ⦄ m₀ ≈ m₁ ⦃ post ⦄.
Proof.
  intros l m0 m1 pre post v H H'.
  eapply rpre_weaken_rule; [ apply H' |].
  split; auto.
Qed.

Lemma r_bind_eq {A B₀ B₁ : choiceType}
  : ∀ (m₀ m₁ : raw_code A) (f₀ : A → raw_code B₀) (f₁ : A → raw_code B₁)
      (pre : precond) (post : postcond B₀ B₁),
      ⊢ ⦃ pre ⦄ m₀ ≈ m₁ ⦃ λ '(a₀, s₀) '(a₁, s₁), a₀ = a₁ ∧ pre (s₀, s₁) ⦄
      → (∀ (a : A), ⊢ ⦃ pre ⦄ f₀ a ≈ f₁ a ⦃ post ⦄)
      → ⊢ ⦃ pre ⦄ x ← m₀ ;; f₀ x ≈ x ← m₁ ;; f₁ x ⦃ post ⦄.
Proof.
  intros m0 m1 f0 f1 pre post R R'.
  eapply r_bind; [ apply R |] => a0 a1 //=.
  apply rpre_hypothesis_rule => s0 s1 [H0 H1].
  subst.
  eapply rpre_weaken_rule; [ apply R' |].
  move => s0' s1' //= [H2 H3].
  by subst.
Qed.



(* swap independent pieces of code *)

Lemma disjoint_neq (f1 f2 : {fset Location}) (l1 l2 : Location) : l1 \in f1 -> l2 \in f2 -> fdisjoint f1 f2 -> l1 != l2.
Proof.
  move => ? ? /fdisjointP H.
  apply /eqP => ?; subst.
  apply /negP; [ eapply H |]; eassumption.
Qed.

Lemma swap_code_aux :
  ∀ A B (c₀ : raw_code A) (c₁ : raw_code B) (L₀ L₁ : {fset Location}),
    fdisjoint L₀ L₁ →
    ValidCode L₀ [interface] c₀ →
    ValidCode L₁ [interface] c₁ →
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
        a₀ ← c₀ ;; a₁ ← c₁ ;; ret (a₀, a₁) ≈ a₁ ← c₁ ;; a₀ ← c₀ ;; ret (a₀, a₁)
      ⦃ eq ⦄.
Proof.
  move=> A B c₀ c₁ L₀ L₁ Disj V₀ V₁.
  induction V₀.
  all: ssprove_code_simpl; simpl.
  - apply rreflexivity_rule.
  - rewrite -fset0E // in H.
  - ssprove_swap_rhs 0%N.
    2: ssprove_sync_eq; apply H1.
    eapply (r_get_remember_lhs l _ _ (λ '(h₀, h₁), h₀ = h₁)) => v.
    apply r_bind_eq.
    1: eapply r_reflexivity_alt.
    1: eassumption.
    1: intros l' H'.
    1: ssprove_invariant.
    1: intros s0 s1 ->; done.
    1: intros l' v' H' s0 s1 [-> H''].
    1: split; [ done |].
    1: unfold rem_lhs.
    1: rewrite get_set_heap_neq.
    1: apply H''.
    1: eapply disjoint_neq; eassumption.
    intros x.
    eapply (r_get_remember_rhs l _ _
      ((λ '(h₀, h₁), h₀ = h₁) ⋊ rem_lhs l v)%pack _).
    intros v'.
    apply r_ret.
    intros s₀ s₁ [[H₀ H₁] H₂].
    rewrite !pair_equal_spec.
    repeat split.
    2: apply H₀.
    by rewrite -H₁ -H₂ H₀.

  - ssprove_swap_rhs 0%N.
    2: ssprove_sync_eq; apply IHV₀.
    apply (r_put_lhs l _ _ _ (λ '(h₀, h₁), h₀ = h₁)%pack _).
    apply r_bind_eq.
    1: eapply r_reflexivity_alt.
    1: eassumption.
    1: intros ll H₀ s₀ s₁ [s₀' [H₁ H₂]].
    1: rewrite H₂ -H₁.
    1: symmetry.
    1: apply get_heap_set_heap.
    1: eapply disjoint_neq; [| | rewrite fdisjointC ]; eassumption.
    1: intros ll x H₀ s₀ s₁ [s₀' [H₁ H₂]].
    1: exists (set_heap s₁ ll x).
    1: split.
    1: reflexivity.
    1: rewrite -H₁ H₂.
    1: apply set_heap_commut.
    1: eapply disjoint_neq; [| | exact Disj ]; assumption.
    intros x.
    apply r_put_rhs.
    apply r_ret.
    intros s₀ s₁ [s₁' [[s₀' [H₀ H₁]] H₂]].
    by rewrite H₁ H₀ -H₂.

  - ssprove_swap_rhs 0%N.
    ssprove_sync_eq => v.
    apply H0.
Qed.

Theorem swap_code :
  ∀ A B C (c₀ : raw_code A) (c₁ : raw_code B) (r : A -> B -> raw_code C) (L₀ L₁ : {fset Location}),
    fdisjoint L₀ L₁ →
    ValidCode L₀ [interface] c₀ →
    ValidCode L₁ [interface] c₁ →
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄
        a₀ ← c₀ ;; a₁ ← c₁ ;; r a₀ a₁ ≈ a₁ ← c₁ ;; a₀ ← c₀ ;; r a₀ a₁
      ⦃ eq ⦄.
Proof.
  intros A B C c0 c1 r L0 L1 Disj V0 V1.
  eapply rswap_ruleR.
  1: easy.
  1: intros a0 a1; apply rsym_pre; [ easy | apply rreflexivity_rule ].
  eapply swap_code_aux.
  1: exact Disj.
  all: easy.
Qed.

Class Cross (l l' : Location) R pre :=
  is_cross : ∀ s₀ s₁, pre (s₀, s₁) → R (get_heap s₀ l) (get_heap s₁ l').

Lemma Remembers_Cross {l l'} {a a'} {R} {pre} :
  Remembers_lhs l a pre →
  Remembers_rhs l' a' pre →
  Cross l l' R pre →
  ∀ s, pre s →
  R a a'.
Proof.
  intros H1 H2 H3 [s0 s1] H4.
  rewrite -(H1 _ _ H4) -(H2 _ _ H4).
  apply H3, H4.
Qed.

Lemma Cross_conj_right {l l' R} {pre spre : precond} :
  Cross l l' R spre → Cross l l' R (pre ⋊ spre).
Proof.
  intros C s0 s1 [H0 H1].
  by apply C.
Qed.

Lemma Cross_conj_left {l l' R} {pre spre : precond} :
  Cross l l' R pre → Cross l l' R (pre ⋊ spre).
Proof.
  intros C s0 s1 [H0 H1].
  by apply C.
Qed.

Lemma r_get_vs_get_cross
   : ∀ {A B} (l l' : Location) (r₀ : Value l.π1 → raw_code A) 
       (r₁ : Value l'.π1 → raw_code B) (pre : precond) R
       (post : postcond A B),
       Cross l l' R pre →
         (∀ (x : Value l.π1) (x' : Value l'.π1), R x x' →
           ⊢ ⦃ λ '(s₀, s₁), (pre ⋊ rem_lhs l x ⋊ rem_rhs l' x') (s₀, s₁) ⦄
             r₀ x ≈ r₁ x'
             ⦃ post ⦄)
       → ⊢ ⦃ λ '(s₀, s₁), pre (s₀, s₁) ⦄
            x ← get l ;; r₀ x  ≈  x ← get l' ;; r₁ x
           ⦃ post ⦄.
Proof.
  intros A B l l' r₀ r₁ pre R post H1 H2.
  eapply r_get_remember_lhs => x.
  eapply r_get_remember_rhs => x'.
  eapply rpre_learn.
  + intros s0 s1.
    eapply Remembers_Cross.
    - apply Remembers_lhs_conj_left.
      apply Remembers_lhs_conj_right.
      apply Remembers_lhs_rem_lhs.
    - apply Remembers_rhs_conj_right.
      apply Remembers_rhs_rem_rhs.
    - apply Cross_conj_left, Cross_conj_left, H1.
  + apply H2.
Qed.


Inductive NoFail {A} : raw_code A → Prop :=
  | NoFail_ret : ∀ x,
      NoFail (ret x)
  | NoFail_sampler : ∀ op k,
      LosslessOp op →
      (∀ v, NoFail (k v)) →
      NoFail (pkg_core_definition.sampler op k).

Lemma r_NoFail_L {A B : choiceType} (c : raw_code B) (c₀ : B → raw_code A) (c₁ : raw_code A)
    (pre : precond) (post : postcond A A) :
    NoFail c →
    (∀ x : B, ⊢ ⦃ pre ⦄ c₀ x ≈ c₁ ⦃ post ⦄) →
    ⊢ ⦃ pre ⦄ x ← c ;; c₀ x ≈ c₁ ⦃ post ⦄.
Proof.
  intros H H'.
  elim: H; intros.
  + apply H'.
  + by apply r_const_sample_L.
Qed.

Lemma r_NoFail_R {A B : choiceType} (c : raw_code B) (c₀ : raw_code A) (c₁ : B → raw_code A)
    (pre : precond) (post : postcond A A) :
    NoFail c →
    (∀ x : B, ⊢ ⦃ pre ⦄ c₀ ≈ c₁ x ⦃ post ⦄) →
    ⊢ ⦃ pre ⦄ c₀ ≈ x ← c ;; c₁ x ⦃ post ⦄.
Proof.
  intros H H'.
  elim: H; intros.
  + apply H'.
  + by apply r_const_sample_R.
Qed.
