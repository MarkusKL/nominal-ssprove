Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Mon Require Import SPropBase.

From Crypt Require Import Axioms ChoiceAsOrd SubDistr Couplings
  UniformDistrLemmas FreeProbProg Theta_dens RulesStateProb UniformStateProb
  pkg_core_definition choice_type pkg_composition pkg_rhl Package Prelude
  SigmaProtocol.

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.



Local Open Scope ring_scope.
Import GroupScope GRing.Theory.


Import Num.Def.
Import Num.Theory.
Import Order.POrderTheory.
Require Import Btauto.

Import PackageNotation.

From extructures Require Import ffun fperm.

From NominalSSP Require Import
  Nominal Fresh FsetSolve Pr NomPackage.

Import FsetSolve.

(* sep_link Section *)

Declare Scope sep_scope.
Delimit Scope sep_scope with sep.
Bind Scope sep_scope with raw_module.
Open Scope sep.


Definition sep_link (P P' : raw_module)
  := share_link P (move P P').

Notation "p1 ∘ p2" :=
  (sep_link p1 p2) (right associativity, at level 20) : sep_scope.
  

Lemma rename_alpha {X : actionType} {O : X} {π} : π ∙ O ≡ O.
Proof.
  exists (π^-1)%fperm.
  rewrite renameK //.
Qed.

Lemma rename_alpha_both {X : actionType} {O : X} {π π'} : π ∙ O ≡ π' ∙ O.
Proof.
  setoid_rewrite rename_alpha.
  setoid_reflexivity.
Qed.

Add Parametric Morphism : sep_link with
  signature alpha ==> alpha ==> alpha as sep_link_mor.
Proof.
  intros P P' EP Q Q' EQ.
  unfold sep_link.
  apply share_link_congr.
  1: apply (move_disj P Q).
  1: apply (move_disj P' Q').
  1: assumption.
  by setoid_rewrite rename_alpha.
Qed.

Lemma disj_rename {X Y : nomType} {x : X} {y : Y} {π} :
  disj x y → disj (π ∙ x) (π ∙ y).
Proof.
  intros H.
  rewrite -(equi2_use _ disj_equi) H //.
Qed.

Lemma equi_fresh_disj {X Y Z W : nomType} {x : X} {y : Y} :
  ∀ {f : X → Z} {g : Y → W},
  equivariant f →
  equivariant g →
  disj (fresh y x ∙ (f x)) (g y).
Proof.
  intros f g Ef Eg.
  rewrite Ef.
  rewrite equi_disj //.
  rewrite disjC equi_disj //.
  apply: fresh_disjoint.
Qed.

Lemma fsetUl : ∀ [T : ordType] (s1 s2 s3 : {fset T}),
  fsubset s1 s2 → fsubset s1 (s2 :|: s3).
Proof.
  intros T s1 s2 s3 H.
  eapply fsubset_trans.
  + apply fsubsetUl.
  + by apply fsetSU.
Qed.

Lemma fsetUr : ∀ [T : ordType] (s1 s2 s3 : {fset T}),
  fsubset s1 s3 → fsubset s1 (s2 :|: s3).
Proof.
  intros T s1 s2 s3 H.
  eapply fsubset_trans.
  + apply fsubsetUr.
  + by apply fsetUS.
Qed.


Lemma subs_equi {X Y : nomType} {x : X} {f : X → Y} :
  equivariant f → subs (f x) x.
Proof.
  intros E.
  by apply supp_fsubset.
Qed.

Lemma subs_equi_eq {X Y : nomType} {x : X} {y : Y} {f : X → Y} :
  equivariant f → y = f x → subs y x.
Proof.
  intros Ef eq.
  rewrite eq.
  by apply subs_equi.
Qed.

Lemma subs_fresh_disj {X Y Z W : nomType} {x : X} {x' : Z} {y : Y} {y' : W} :
  subs x' x →
  subs y' y →
  disj (fresh y x ∙ x') y'.
Proof.
  intros subsx subsy.
  erewrite <- absorb in subsx.
  rewrite -> equi2_use in subsx.
  2: apply subsE.
  eapply fdisjoint_trans.
  1: apply subsx.
  rewrite fdisjointC.
  eapply fdisjoint_trans.
  1: apply subsy.
  apply fresh_disjoint.
Qed.

Lemma subs_fresh_disj_2 {X Y Z W : nomType} {x : X} {x' : Z} {y : Y} {y' : W} :
  subs x' x →
  subs y' y →
  disj y' (fresh y x ∙ x').
Proof.
  rewrite disjC.
  apply subs_fresh_disj.
Qed.

Create HintDb alpha_db.
#[export] Hint Resolve subs_fresh_disj subs_fresh_disj_2 : alpha_db.
#[export] Hint Resolve disj_rename : alpha_db.

Lemma subs_supp_fsetUl {X Y Z W : nomType} {x : X} {y z} {f : Y → Z → W}
  : supp (f y z) = supp y :|: supp z → subs x y → subs x (f y z).
Proof.
  intros H H'.
  rewrite /subs H.
  apply (fsubset_trans H').
  apply fsubsetUl.
Qed.

Lemma subs_supp_fsetUr {X Y Z W : nomType} {x : X} {y z} {f : Y → Z → W}
  : supp (f y z) = supp y :|: supp z → subs x z → subs x (f y z).
Proof.
  intros H H'.
  rewrite /subs H.
  apply (fsubset_trans H').
  apply fsubsetUr.
Qed.

#[export] Hint Resolve subs_supp_fsetUl subs_supp_fsetUr : alpha_db.

Lemma supp_pair {X Y : nomType} {x : X} {y : Y}
  : supp (pair x y) = supp x :|: supp y.
Proof. done. Qed.

#[export] Hint Resolve s_share_link s_share_par supp_pair : alpha_db.


Lemma subs_refl {X : nomType} {x : X} : subs x x.
Proof.
  apply fsubsetxx.
Qed.

#[export] Hint Resolve subs_refl : alpha_db.

Lemma disj_share_link {X : nomType} {x : X} {P Q}
  : disj x P → disj x Q → disj x (P ∘ Q)%share.
Proof.
  intros dP dQ.
  unfold disj.
  rewrite s_share_link.
  rewrite fdisjointUr.
  apply /andP.
  by split.
Qed.

Lemma disj_share_link2 {X : nomType} {x : X} {P Q}
  : disj P x → disj Q x → disj (P ∘ Q)%share x.
Proof.
  intros dP dQ.
  rewrite disjC.
  rewrite disj_share_link //; rewrite disjC //.
Qed.

Lemma disj_equi2 {X Y Z W : nomType} {x : X} {y : Y} {z : Z} {f}
  : equivariant (f : Y → Z → W) → disj x y → disj x z → disj x (f y z).
Proof.
  intros E D1 D2.
  rewrite disjC.
  change (f y z) with (uncurry f (y, z)).
  eapply fdisjoint_trans.
  + eapply supp_fsubset.
    intros π [x' y'].
    rewrite //= (equi2_use _ E) //.
  + rewrite fdisjointUl.
    apply /andP.
    split; rewrite fdisjointC //.
Qed.

Lemma disj_equi2' {X Y Z W : nomType} {x : X} {y : Y} {z : Z} {f}
  : equivariant (f : Y → Z → W) → disj x y → disj x z → disj (f y z) x.
Proof.
  intros E D1 D2.
  rewrite disjC.
  by apply disj_equi2.
Qed.

Lemma equi_share_link : equivariant share_link.
Proof.
  apply equi2_prove => π x y.
  apply rename_share_link.
Qed.

Lemma equi_share_par : equivariant share_par.
Proof.
  apply equi2_prove => π x y.
  apply rename_share_par.
Qed.

Lemma supp0 {X : nomOrdType} : supp (@fset0 X) = fset0.
Proof.
  rewrite /supp //= fsetSupp0 //.
Qed.

Lemma disj_ID_l {X : nomType} {x : X} {I} : disj (ID I) x.
Proof.
  rewrite /disj /supp //= supp0.
  apply fdisjoint0s.
Qed.

Lemma disj_ID_r {X : nomType} {x : X} {I} : disj x (ID I).
Proof.
  rewrite /disj /supp //= supp0.
  apply fdisjoints0.
Qed.

#[export] Hint Resolve disj_ID_l disj_ID_r : alpha_db.

(* #[export] Hint Resolve disj_link disj_link2 : alpha_db. *)
#[export] Hint Resolve disj_equi2 disj_equi2' : alpha_db.
#[export] Hint Resolve equi_share_link equi_share_par : alpha_db.

#[export] Hint Resolve share_link_congr share_par_congr : alpha_db.

#[export] Hint Extern 1 (alpha (rename _ _) _) =>
  rewrite rename_alpha : alpha_db.

#[export] Hint Extern 1 (alpha _ (rename _ _)) =>
  rewrite rename_alpha : alpha_db.

#[export] Hint Extern 10 (alpha _ _) =>
  reflexivity : alpha_db.

Lemma sep_link_assoc (p1 p2 p3 : raw_module)
  : p1 ∘ p2 ∘ p3 ≡ (p1 ∘ p2) ∘ p3.
Proof.
  rewrite /sep_link /move rename_share_link share_link_assoc.
  auto with alpha_db nocore.
Qed.


(* ID *)

Lemma share_link_adj {P P'} {π}
  : (P ∘ (π ∙ P'))%share ≡ ((π^-1 ∙ P)%fperm ∘ P')%share.
Proof.
  exists (π^-1)%fperm.
  rewrite rename_share_link.
  rewrite renameK //.
Qed.

Lemma rename_trimmed {E π p} : trimmed E p → trimmed E (π ∙ p).
Proof.
  unfold rename; simpl.
  intros tr0.
  unfold trimmed in tr0 |- *.
  rewrite -{2}tr0.
  unfold trim.
  apply eq_fmap => n.
  rewrite filtermE 2!mapmE filtermE.
  destruct (p n).
  2: done.
  destruct t as [S [T m]].
  unfold rename; simpl.
  destruct ((n, (S, T)) \in E) eqn:eq; rewrite eq //.
Qed.

Lemma sep_link_id {L I E} (P : raw_module) :
  ValidPackage L I E P → flat I → trimmed E P → P ∘ (ID I) ≡ P.
Proof.
  intros V F T.
  rewrite /sep_link /move -{3}(share_link_id F T).
  auto with alpha_db nocore.
Qed.

Lemma id_sep_link {L I E} (P : raw_module) (V : ValidPackage L I E P)
  : trimmed E P → ID E ∘ P ≡ P.
Proof.
  intros T.
  rewrite /sep_link /move -{3}(id_share_link T).
  auto with alpha_db nocore.
Qed.


(* sep_par *)

Definition sep_par (P P' : raw_module)
  := share_par P (move P P').

Notation "p1 || p2" :=
  (sep_par p1 p2) : sep_scope.

Add Parametric Morphism : sep_par with
  signature alpha ==> alpha ==> alpha as sep_par_mor.
Proof.
  intros P P' EP Q Q' EQ.
  unfold sep_par, move.
  auto with alpha_db nocore.
Qed.

#[export]
Instance Parable_rename_l {p1 p2 π} : Parable p1 p2 → Parable (π ∙ p1) p2.
Proof.
  unfold Parable, domm, unzip1.
  unfold rename; simpl.
  unfold rename; simpl.
  rewrite -map_comp.
  replace (fst \o (λ p,  (p.1, mtyped π p.2)))
    with (@fst nat typed_raw_function).
  { done. }
  apply functional_extensionality => x.
  destruct x as [n T]; done.
Qed.

#[export]
Instance Parable_rename_r {p1 p2 π} : Parable p1 p2 → Parable p1 (π ∙ p2).
Proof.
  unfold Parable, domm, unzip1.
  unfold rename; simpl.
  unfold rename; simpl.
  rewrite -map_comp.
  replace (fst \o (λ p,  (p.1, mtyped π p.2)))
    with (@fst nat typed_raw_function).
  { done. }
  apply functional_extensionality => x.
  destruct x as [n T]; done.
Qed.

Lemma sep_par_commut (p1 p2 : raw_module) (P : Parable p1 p2)
  : (p1 || p2) ≡ (p2 || p1).
Proof.
  unfold sep_par, move.
  rewrite share_par_commut.
  auto with alpha_db nocore.
Qed.

Lemma sep_par_assoc {P1 P2 P3 : raw_module}
  : (P1 || (P2 || P3)) ≡ ((P1 || P2) || P3).
Proof.
  rewrite /sep_par /move rename_share_par share_par_assoc.
  auto with alpha_db nocore.
Qed.

Lemma sep_interchange {A B C D E F} {L1 L2 L3 L4} (p1 p2 p3 p4 : raw_module) :
  ValidPackage L1 B A p1 → ValidPackage L2 E D p2 →
  ValidPackage L3 C B p3 → ValidPackage L4 F E p4 →
  trimmed A p1 → trimmed D p2 → Parable p3 p4 → 
  (p1 ∘ p3) || (p2 ∘ p4) ≡ (p1 || p2) ∘  (p3 || p4).
Proof.
  intros V1 V2 V3 V4 tr1 tr2 P34.
  rewrite /sep_par /sep_link /move
    rename_share_par rename_share_link share_interchange.
  2: assumption.
  2: by apply rename_trimmed.
  auto 10 with alpha_db nocore.
Qed.


(* Adv *)

Definition Pr' : raw_module → R := λ P, Pr P true.

Definition Adv (G G' A : raw_module) : R
  := `| Pr' (A ∘ G) - Pr' (A ∘ G')|.

Add Parametric Morphism : val with
  signature alpha ==> alpha as val_mor.
Proof.
  intros x y [π E].
  rewrite -E.
  exists π.
  reflexivity.
Qed.

Add Parametric Morphism : Pr' with
  signature alpha ==> eq as Pr'_mor.
Proof.
  intros x y [π' H0].
  unfold Pr'.
  rewrite -H0.
  apply Pr_rename.
Qed.

Lemma Pr'_def {P} : Pr' P = Pr (val P) true.
Proof. done. Qed.

Add Parametric Morphism : Adv with
  signature alpha ==> alpha ==> alpha ==> eq as Adv_mor.
Proof.
  intros.
  unfold Adv.
  rewrite H H0 H1 //.
Qed.

(*
Add Parametric Morphism : (@GRing.add R) with
  signature ler ++> ler ++> ler as add_mor.
Proof.
  intros.
  by apply ler_add.
Qed.
 *)


Lemma alpha_equi {X Y : actionType} {P P'} {f : X → Y}
: equivariant f → P ≡ P' → f P ≡ f P'.
Proof.
  intros equif [π eq].
  exists π.
  rewrite equif.
  f_equal.
  apply eq.
Qed.

#[export]
Instance share_link_valid {L L' I M E} {P P' : raw_module} :
  ValidPackage L M E P → ValidPackage L' I M P' →
  ValidPackage (L :|: L') I E (P ∘ P')%share.
Proof. by apply valid_link. Qed.

#[export]
Instance sep_link_valid {L L' I M E} {P P' : raw_module} :
  ValidPackage L M E P → ValidPackage L' I M P' →
  ValidPackage (L :|: fresh P P' ∙ L') I E (P ∘ P')%sep.
Proof.
  intros V1 V2.
  eapply (valid_link _ _ _ _ _ _ _ V1).
  apply rename_valid.
  apply V2.
Qed.

#[export]
Instance share_par_valid {L L' I I' E E'} {P P' : raw_module} :
  Parable P P' →
  ValidPackage L I E P → ValidPackage L' I' E' P' →
  ValidPackage (L :|: L') (I :|: I') (E :|: E') (P || P')%share.
Proof. by apply valid_par. Qed.

#[export]
Instance share_par_valid_same_import {L L' I E E'} {P P' : raw_module} :
  Parable P P' →
  ValidPackage L I E P → ValidPackage L' I E' P' →
  ValidPackage (L :|: L') I (E :|: E') (P || P')%share.
Proof.
  intros Par V1 V2.
  rewrite -(fsetUid I).
  by apply share_par_valid.
Qed.

#[export]
Instance sep_par_valid {L L' I I' E E'} {P P' : raw_module} :
  Parable P P' → 
  ValidPackage L I E P → ValidPackage L' I' E' P' →
  ValidPackage (L :|: fresh P P' ∙ L') (I :|: I') (E :|: E') (P || P')%sep.
Proof.
  intros Par V1 V2.
  simpl.
  eapply valid_par.
  + apply Parable_rename_r, Par.
  + apply V1.
  + apply rename_valid, V2.
Qed.

#[export]
Instance sep_par_valid_r {L L' I I' E E'} {P P' : raw_module} :
  Parable P' P → 
  ValidPackage L I E P → ValidPackage L' I' E' P' →
  ValidPackage (L :|: fresh P P' ∙ L') (I' :|: I) (E' :|: E) (P || P')%sep.
Proof.
  intros Par V1 V2.
  rewrite (fsetUC I') (fsetUC E').
  apply sep_par_valid; try assumption.
  rewrite /Parable fdisjointC //.
Qed.

#[export]
Instance sep_par_valid_same_import {L L' I E E'} {P P' : raw_module} :
  Parable P P' → 
  ValidPackage L I E P → ValidPackage L' I E' P' →
  ValidPackage (L :|: fresh P P' ∙ L') I (E :|: E') (P || P')%sep.
Proof.
  intros Par V1 V2.
  rewrite -(fsetUid I).
  by apply sep_par_valid.
Qed.

Lemma Adv_triangle {G1 G2 G3 : raw_module} A
  : Adv G1 G3 A <= Adv G1 G2 A + Adv G2 G3 A.
Proof. unfold Adv, Pr'. apply Advantage_triangle. Qed.

Ltac nssprove_adv_etrans :=
  eapply le_trans;
    [ eapply Adv_triangle |].

Ltac nssprove_adv_trans M :=
  eapply le_trans;
    [ eapply (@Adv_triangle _ M%sep) |].

Lemma Adv_same (G A : raw_module) : Adv G G A = 0.
Proof. rewrite /Adv addrN. rewrite normr0 //. Qed.

Lemma Adv_sym (G G' A : raw_module) : Adv G G' A = Adv G' G A.
Proof. apply: distrC. Qed.

Lemma Adv_alpha (G G' A : raw_module)
  : G ≡ G' → Adv G G' A = 0.
Proof.
  intros Eq.
  rewrite Eq.
  apply Adv_same.
Qed.

Lemma Adv_sep_link (G G' D A : raw_module) :
  Adv (D ∘ G) (D ∘ G') A = Adv G G' (A ∘ D).
Proof.
  unfold Adv.
  erewrite sep_link_assoc.
  erewrite sep_link_assoc.
  done.
Qed.

Lemma share_link_sep_link {P P' : raw_module} :
  disj P P' →
  (P ∘ P')%share ≡ (P ∘ P').
Proof.
  intros D.
  unfold sep_link, move.
  auto with alpha_db nocore.
Qed.

Lemma link_sep_link {P P' : raw_module} :
  disj P P' →
  (P ∘ P')%pack ≡ val (P ∘ P').
Proof.
  intros D.
  change (link P P') with (val (share_link P P')).
  apply alpha_equi; [ done |].
  apply share_link_sep_link, D.
Qed.

Lemma share_par_sep_par {P P' : raw_module} :
  disj P P' →
  (P || P')%share ≡ (P || P').
Proof.
  intros D.
  unfold sep_par, move.
  auto with alpha_db nocore.
Qed.

Lemma par_sep_par {P P' : raw_module} :
  disj P P' →
  (par P P' : raw_package) ≡ val (P || P').
Proof.
  intros D.
  change (par P P') with (val (share_par P P')).
  apply alpha_equi; [ done |].
  apply share_par_sep_par, D.
Qed.

Lemma Adv_AdvantageE (G G' A : raw_module) :
  disj A G ->
  disj A G' ->
  Adv G G' A = AdvantageE G G' A.
Proof.
  intros D1 D2.
  unfold Adv, AdvantageE.
  rewrite link_sep_link ?link_sep_link //.
Qed.

Lemma equi_pair {X Y : actionType} : equivariant (@pair X Y).
Proof.
  by apply equi2_prove => π x y.
Qed.

#[export] Hint Resolve equi_pair : alpha_db.

(* simple apply @subs_equi2_l fails when used near {fset Location}, so this
   is registered as a workaround *)

#[export] Hint Extern 7 (is_true (subs _ (_ _ _))) =>
  simple apply subs_supp_fsetUl : alpha_db.

#[export] Hint Extern 7 (is_true (subs _ (_ _ _))) =>
  simple apply subs_supp_fsetUr : alpha_db.

Lemma imfset_fdisjoint {T S : ordType} {A B : {fset T}} (f : T → S) : f @: A :#: f @: B → A :#: B.
Proof.
  move => /fdisjointP H.
  apply /fdisjointP => x H'.
  specialize (H (f x)).
  rewrite mem_imfset // in H.
  specialize (H Logic.eq_refl).
  move: H => /negP H.
  apply /negP => H''.
  apply H.
  by apply mem_imfset.
Qed.

(*
Lemma supp_imfset_Locations {S} {X : SuppOrd.type S} {A : {fset X}} {f : X → atom}
  : (∀ x, supp x = fset1 (f x)) → supp @: A = supp A.
Proof.
 *)

Lemma supp_fdisjoint {A B : {fset Location}} : disj A B → A :#: B.
Proof.
  intros D.
  rewrite /disj /supp //= in D.
  move: D => /fdisjointP D.
  apply /fdisjointP => x H.
  destruct x as [c n].
  apply /negP => H'.
  specialize (D (atomize n)).
  assert (atomize n \in fsetSupp A).
  { unfold fsetSupp.
    apply /bigcupP.
    eapply BigCupSpec.
    + apply H.
    + done.
    + rewrite in_fset1 //.
  }
  specialize (D H0).
  move: D => /negP D.
  apply D.
  unfold fsetSupp.
  apply /bigcupP.
  eapply BigCupSpec.
  + apply H'.
  + done.
  + rewrite in_fset1 //.
Qed.


Lemma Adv_adv_equiv {L L' E} {G G' : raw_module} {ε : raw_package → R}
  {V1 : ValidPackage L Game_import E G} {V2 : ValidPackage L' Game_import E G'} :
  equivariant ε →
  G ≈[ ε ] G' →
  ∀ {LA} (A : raw_module), ValidPackage LA E A_export A → Adv G G' A = ε A.
Proof.
  intros equieps adv LA A VA.
  pose (π := fresh ((L, G), (L', G')) (LA, A)).
  setoid_rewrite <- (@rename_alpha _ A π).
  rewrite Adv_AdvantageE.
  1: rewrite -(absorb π (ε A)).
  1: rewrite equieps.
  1: rewrite adv //.
  all: unfold π => {π}.
  1,2: apply supp_fdisjoint.
  1-4: auto with alpha_db nocore.
Qed.

Lemma Adv_perf {L L' E} {G G' : raw_module}
  {V1 : ValidPackage L Game_import E G} {V2 : ValidPackage L' Game_import E G'} :
  G ≈₀ G' →
  ∀ {LA} (A : raw_module), ValidPackage LA E A_export A → Adv G G' A = 0.
Proof.
  intros adv LA A VA.
  eapply (Adv_adv_equiv (ε := λ _, 0)).
  1: done.
  1: apply adv.
  apply VA.
Qed.

Lemma Adv_perf_l {P P' Q A : raw_module} {LP LP' LA E}
  {V1 : ValidPackage LP Game_import E P}
  {V2 : ValidPackage LP' Game_import E P'}
  {V3 : ValidPackage LA E A_export A} :
  P ≈₀ P' → Adv P Q A = Adv P' Q A.
Proof.
  intros Indish.
  apply le_anti.
  apply /andP; split.
  - nssprove_adv_etrans.
    erewrite (Adv_perf Indish).
    + rewrite GRing.add0r //.
    + eassumption.
  - nssprove_adv_etrans.
    erewrite (Adv_perf (adv_equiv_sym _ _ _ _ _ _ _ _ Indish)).
    + rewrite GRing.add0r //.
    + eassumption.
Qed.

Lemma Adv_perf_r {P P' Q A : raw_module} {LP LP' LA E}
  {V1 : ValidPackage LP Game_import E P}
  {V2 : ValidPackage LP' Game_import E P'}
  {V3 : ValidPackage LA E A_export A} :
  P ≈₀ P' → Adv Q P A = Adv Q P' A.
Proof.
  intros Indish.
  rewrite Adv_sym.
  erewrite Adv_perf_l; [| done].
  rewrite Adv_sym //.
Qed.


Definition perfect I G G' :=
  ∀ LA (A : raw_module) (VA : ValidPackage LA I A_export A), Adv G G' A = 0.

Lemma perfect_refl {I G} : perfect I G G.
Proof. intros LA A VA. rewrite Adv_same //. Qed.

Lemma perfect_sym {I G G'} : perfect I G' G → perfect I G G'.
Proof. intros H LA A VA. rewrite Adv_sym H //. Qed.

Add Parametric Morphism : perfect with
  signature eq ==> alpha ==> alpha ==> iff as perfect_mor.
Proof.
  intros I G0 G0' H0 G1 G1' H1.
  split.
  + intros H LA A VA.
    rewrite -H0 -H1 H //.
  + intros H LA A VA.
    rewrite H0 H1 H //.
Qed.

Lemma Adv_perfect_l {L E} {P P' Q A : raw_module}
  {V : ValidPackage L E A_export A} :
  perfect E P P' → Adv P Q A = Adv P' Q A.
Proof.
  intros H.
  apply le_anti.
  apply /andP; split.
  - nssprove_adv_trans P'.
    rewrite H GRing.add0r //.
  - nssprove_adv_trans P.
    rewrite Adv_sym H GRing.add0r //.
Qed.

Lemma Adv_perfect_r {L E} {P P' Q A : raw_module}
  {V : ValidPackage L E A_export A} :
  perfect E P P' → Adv Q P A = Adv Q P' A.
Proof. intros H. rewrite Adv_sym (Adv_perfect_l H) Adv_sym //. Qed.

Lemma perfect_trans {I G G' G''}
  : perfect I G G' → perfect I G' G'' → perfect I G G''.
Proof. intros H1 H2 LA A VA. rewrite (Adv_perfect_l H1) H2 //. Qed.

Lemma prove_perfect {L L'} {E} {G G' : raw_module} :
  ∀ (V  : ValidPackage L  Game_import E G )
    (V' : ValidPackage L' Game_import E G'),
    G ≈₀ G' → perfect E G G'.
Proof. intros V V' H LA A VA. apply (Adv_perf H _ VA). Qed.


(* NOM and automation *)

Definition exports : raw_package → Interface :=
  λ p, codomm (mapim (λ n '(X; Y; _), (n, (X, Y))) p).

Lemma exports_trimmed {p} : trimmed (exports p) p.
Proof.
  apply eq_fmap => n.
  unfold trimmed, trim, exports.
  rewrite filtermE.
  destruct (p n) eqn:eq; rewrite eq; [ simpl | done ].
  destruct t as [X [Y k]].
  rewrite (introT codommP); [ done |].
  exists n.
  rewrite mapimE eq //.
Qed.

Definition nom {L I} p {V : ValidPackage L I (exports p) p} : raw_module
  := module_from_trimmed p exports_trimmed.


Lemma s_nom {L I p} {V : ValidPackage L I (exports p) p} : supp (nom p) = supp L.
Proof. done. Qed.
#[export] Hint Rewrite @s_nom : in_fset_eq.


#[export]
Instance nom_valid {L I p} (V : ValidPackage L I (exports p) p)
  : ValidPackage L I (exports p) (nom p).
Proof. apply V. Qed.

#[export]
Instance ID_valid {I} : flat I → ValidPackage fset0 I I (ID I).
Proof.
  apply valid_ID.
Qed.

Lemma val_nom {L I} p {V : ValidPackage L I (exports p) p}
  : val (nom p) = p.
Proof. done. Qed.


Lemma Game_import_flat : flat Game_import.
Proof.
  unfold Game_import, flat.
  rewrite -fset0E.
  intros n u v H.
  rewrite in_fset0 // in H.
Qed.

Lemma Parable_commut {P1 P2} : Parable P2 P1 → Parable P1 P2.
Proof. rewrite /Parable fdisjointC //. Qed.

Lemma Parable_nom_l {L I p' p} {V : ValidPackage L I (exports p) p}
  : Parable p p' → Parable (nom p) p'.
Proof. rewrite val_nom //. Qed.

Lemma Parable_nom_r {L I p p'} {V : ValidPackage L I (exports p') p'}
  : Parable p p' → Parable p (nom p').
Proof. rewrite val_nom //. Qed.

Lemma Parable_ID_l {E p}
  : Parable (pkg_composition.ID E) p → Parable (ID E) p.
Proof. done. Qed.

Lemma Parable_ID_r {E p}
  : Parable p (pkg_composition.ID E) → Parable p (ID E).
Proof. done. Qed.

Ltac nssprove_rec :=
  lazymatch goal with
  | |- (ValidPackage ?L ?I ?E (val ?P)) =>
      tryif assert_fails (is_evar I)
        then (eapply valid_package_inject_import; nssprove_rec) else
      tryif assert_fails (is_evar E)
        then (eapply valid_package_inject_export; nssprove_rec) else
      lazymatch P with
      | (share_link ?P1 ?P2) => eapply valid_link; nssprove_rec
      | (share_par ?P1 ?P2) => eapply valid_par; nssprove_rec
      | (sep_link ?P1 ?P2) => eapply sep_link_valid; nssprove_rec
      | (sep_par ?P1 ?P2) => eapply sep_par_valid; nssprove_rec
      | (ID ?I1) => eapply ID_valid; nssprove_rec
      | (rename ?pi ?P1) => eapply rename_valid; nssprove_rec
      | (mod ?P1) => eapply module_valid
          (* | (nom (pack ?P1)) => apply pack_valid
      | (nom ?P1) => apply nom_valid
          (* apply valid_trim; apply (pack_valid P1) *)
           *)
      | _ => try eassumption
      end
    (*
  | |- (ValidPackage ?L ?I ?E (val (sep_link ?P1 ?P2))) =>
      eapply sep_link_valid;
      [ eapply valid_package_inject_export |];
      nssprove_rec
  | |- (ValidPackage ?L ?I ?E (val (sep_par ?P1 ?P2))) =>
      eapply sep_par_valid_same_import;
      [ | eapply valid_package_inject_import
        | eapply valid_package_inject_import ] ;
            nssprove_rec
  | |- (ValidPackage ?L ?I ?E (val (ID ?M))) =>
      eapply ID_valid; nssprove_rec
  | |- (ValidPackage ?L ?I ?E (val (nom ?M))) =>
      apply valid_trim; apply (pack_valid M)
  | |- (ValidPackage ?L ?I ?E (val ?P)) =>
      try eassumption
     *)

  | |- is_true ( fsubset ?A ?B ) =>
      try assumption
  | |- (Parable (val (nom ?P1)) ?P2) =>
      apply Parable_nom_l ; nssprove_rec
  | |- (Parable ?P1 (val (nom ?P2))) =>
      apply Parable_nom_r ; nssprove_rec
  | |- (Parable (val (ID ?E1)) ?P2) =>
      apply Parable_ID_l ; nssprove_rec
  | |- (Parable ?P1 (val (ID ?E2))) =>
      apply Parable_ID_r ; nssprove_rec
  | |- (Parable ?P1 ?P2) =>
      try (assumption || (apply Parable_commut ; assumption)) ;
      try (unfold Parable; simpl; fset_solve)
      (* try ssprove_valid *)
  | |- (flat Game_import) =>
      apply Game_import_flat
  | |- (flat ?E) =>
      assumption || (eapply flat_valid_package; eassumption) || (try ssprove_valid)
  | |- (trimmed ?E1 (val (ID ?E2))) =>
      apply trimmed_ID
  | |- (trimmed ?E ?P) =>
      (try assumption) || (try apply module_trimmed) || nssprove_trimmed
  | |- ?x =>
      done ||
      (* idtac x ; *)
      fail "What do I do with this?"
  end.
    
Ltac nssprove_valid :=
  (* try unfold Game_import ; *)
  nssprove_rec ;
  try (fset_solve; fail).


Class Trimmed (E : Interface) (p : raw_module) := tr : trimmed E p.

Arguments tr {_ _} _.

Notation "{ 'module' I ; E ; m }" :=
  (@Build_module I E (loc m%sep) (mkpackage m%sep _) (tr _))
  (only parsing) : sep_scope.

Notation "{ 'game' E ; m }" :=
  (@Build_module Game_import E (loc m%sep) (mkpackage m%sep _) (tr _))
  (only parsing) : sep_scope.

Notation "{ 'adversary' I ; m }" :=
  (@Build_module I A_export (loc m%sep) (mkpackage m%sep _) (tr _))
  (only parsing) : sep_scope.

Instance Trimmed_link {E P Q} : Trimmed E P → Trimmed E (P ∘ Q)%sep.
Proof. apply trimmed_link. Qed.

Instance Trimmed_module {I E} {P : module I E} : Trimmed E P.
Proof. apply module_trimmed. Qed.


Lemma valid_idents {L I E} P {V : ValidPackage L I E P} : fsubset (idents E) (domm P).
Proof.
  destruct V.
  apply /fsubsetP.
  move => n /imfsetP H'.
  destruct H'.
  specialize (H x H0).
  destruct x as [m [S T]].
  destruct H as [f [H _]].
  subst; simpl in *.
  apply /dommP.
  exists (S; T; f).
  apply H.
Qed.

Lemma swish {L L' : {fset Location}} {I I' E E' : Interface} {P P' : raw_module} :
  ValidPackage L I E P → ValidPackage L' I' E' P' → Parable (ID I) P' →
  flat I → trimmed E P → trimmed E' P' →
  (P || P') ≡ (P || ID E') ∘ (ID I || P').
Proof.
  intros V1 V2 V3.
  intros fl tr tr'.
  erewrite <- sep_interchange; try nssprove_valid.
  rewrite id_sep_link //.
  rewrite sep_link_id //.
  setoid_reflexivity.
Qed.

Lemma swash {L L' I I' E E'} {P P' : raw_module} :
  ValidPackage L I E P → ValidPackage L' I' E' P' → Parable P (ID I') →
  flat I' → trimmed E P → trimmed E' P' →
  (P || P') ≡ (ID E || P') ∘ (P || ID I').
Proof.
  intros V1 V2 V3.
  intros fl tr tr'.
  erewrite <- sep_interchange; try nssprove_valid.
  rewrite id_sep_link //.
  rewrite sep_link_id //.
  reflexivity.
Qed.

Lemma Game_import_empty : pkg_composition.ID (Game_import) = emptym.
Proof. rewrite /pkg_composition.ID /Game_import -fset0E //. Qed.

Lemma sep_par_empty_l {P} : (ID (Game_import) || P) ≡ P.
Proof.
  exists (fresh (ID Game_import) P)^-1%fperm.
  unfold sep_par.
  rewrite rename_share_par renameK.
  apply eq_raw_module.
  1,2: unfold rename; simpl.
  + unfold rename; simpl.
    rewrite imfset0 fset0U //.
  + rewrite Game_import_empty.
    unfold rename, par; simpl.
    apply eq_fmap => n.
    rewrite unionmE //.
Qed.

Lemma sep_par_empty_r {P} : (P || ID (Game_import)) ≡ P.
Proof.
  rewrite -> sep_par_commut.
  + apply sep_par_empty_l.
  + apply Parable_ID_r.
    rewrite Game_import_empty.
    rewrite /Parable /domm //= -fset0E.
    apply fdisjoints0.
Qed.

#[export]
Hint Unfold Game_import : in_fset_eq.

#[export]
Hint Rewrite <- fset0E : in_fset_eq.

Lemma domm_ID {E} : domm (pkg_composition.ID E) = idents E.
Proof. rewrite //= domm_ID //. Qed.

#[export] Instance Parable_Game_import_l {P} : Parable (ID Game_import) P.
Proof.
  unfold Parable, Game_import.
  rewrite /Parable domm_ID /idents -fset0E imfset0 fdisjoint0s //.
Qed.

#[export] Instance Parable_Game_import_r {P} : Parable P (ID Game_import).
Proof.
  unfold Parable, Game_import.
  rewrite /Parable domm_ID /idents -fset0E imfset0 fdisjoints0 //.
Qed.

Lemma sep_par_game_l {LP LQ LR EP EQ ER IQ} {P Q R : raw_module}
  {VP : ValidPackage LP EQ EP P}
  {VQ : ValidPackage LQ IQ EQ Q}
  {VR : ValidPackage LR Game_import ER R}
  {trP : trimmed EP P}
  {trR : trimmed ER R} :
  ((P ∘ Q) || R) ≡ (P || R) ∘ Q.
Proof.
  rewrite -{2}(@sep_par_empty_r Q).
  erewrite <- sep_interchange.
  2-7: nssprove_valid.
  2: apply Parable_Game_import_r.
  rewrite sep_link_id; [ reflexivity | | assumption ].
  apply Game_import_flat.
Qed.

Lemma sep_par_game_r {LP LQ LR EP EQ ER IQ} {P Q R : raw_module}
  {VP : ValidPackage LP EQ EP P}
  {VQ : ValidPackage LQ IQ EQ Q}
  {VR : ValidPackage LR Game_import ER R}
  {trP : trimmed EP P}
  {trR : trimmed ER R} :
  (R || (P ∘ Q)) ≡ (R || P) ∘ Q.
Proof.
  rewrite -{2}(@sep_par_empty_l Q).
  erewrite <- sep_interchange.
  2-7: nssprove_valid.
  2: apply Parable_Game_import_l.
  rewrite sep_link_id; [ reflexivity | | assumption ].
  apply Game_import_flat.
Qed.

Lemma Adv_par_link_r (P₀ P₁ P₁' G G' A : raw_module)
  {LP₀ LP₁ LP₁'} {I₀ I₁ E₀ E₁}
  {V1 : ValidPackage LP₀ I₀ E₀ P₀}
  {V2 : ValidPackage LP₁ I₁ E₁ P₁}
  {V3 : ValidPackage LP₁' I₁ E₁ P₁'}
  {P1 : Parable (ID I₀) P₁}
  {P2 : Parable (ID I₀) P₁'} :
  flat I₀ → trimmed E₀ P₀ → trimmed E₁ P₁ → trimmed E₁ P₁' →
  Adv ((P₀ || P₁) ∘ G) ((P₀ || P₁') ∘ G') A
    = Adv ((ID I₀ || P₁) ∘ G) ((ID I₀ || P₁') ∘ G') (A ∘ (P₀ || (ID E₁))).
Proof.
  intros fl0 tr0 tr1 tr2.
  rewrite <- Adv_sep_link.
  erewrite sep_link_assoc.
  erewrite sep_link_assoc.
  erewrite <- @swish, <- @swish.
  all: nssprove_valid.
Qed.

Lemma Adv_par_r (G₀ G₁ G₁' A : raw_module)
  {L₀ L₁ L₁' : {fset Location}} {E₀ E₁}
  {V1 : ValidPackage L₀ Game_import E₀ G₀}
  {V2 : ValidPackage L₁ Game_import E₁ G₁}
  {V3 : ValidPackage L₁' Game_import E₁ G₁'} :
  trimmed E₀ G₀ → trimmed E₁ G₁ → trimmed E₁ G₁' →
  Adv (G₀ || G₁) (G₀ || G₁') A = Adv G₁ G₁' (A ∘ (G₀ || ID E₁)).
Proof.
  intros tr0 tr1 tr2.
  rewrite -Adv_sep_link.
  rewrite swish.
  2-4: try nssprove_valid.
  rewrite sep_par_empty_l.
  rewrite swish.
  2-4: try nssprove_valid.
  rewrite sep_par_empty_l.
  reflexivity.
Qed.

Lemma domm_idents {L I E P} {V : ValidPackage L I E P} : trimmed E P → domm P = idents E.
Proof.
  intros tr.
  apply reflection_nonsense.
  rewrite eqEfsubset.
  rewrite valid_idents.
  rewrite domm_trimmed //.
Qed.

Lemma Adv_par_link_l (P₀ P₀' P₁ G G' A : raw_module)
  {LP₀ LP₀' LP₁} {I₀ I₁ E₀ E₁}
  {V1 : ValidPackage LP₀ I₀ E₀ P₀}
  {V2 : ValidPackage LP₀' I₀ E₀ P₀'}
  {V3 : ValidPackage LP₁ I₁ E₁ P₁}
  {P1 : Parable P₀ (ID I₁)}
  {P2 : Parable P₀' (ID I₁)} :
  flat I₁ → trimmed E₀ P₀ → trimmed E₀ P₀' → trimmed E₁ P₁ →
  Adv ((P₀ || P₁) ∘ G) ((P₀' || P₁) ∘ G') A
    = Adv ((P₀ || ID I₁) ∘ G) ((P₀' || ID I₁) ∘ G') (A ∘ (ID E₀ || P₁)).
Proof.
  intros fl1 tr0 tr1 tr2.
  (* Why do these have to be erewrite? And other places *)
  erewrite <- Adv_sep_link.
  erewrite sep_link_assoc, sep_link_assoc.
  erewrite <- @swash, <- @swash.
  all: nssprove_valid.
Qed.

Lemma Adv_par_l (G₀ G₀' G₁ A : raw_module) {L₀ L₀'  L₁} {E₀ E₁}
  {V1 : ValidPackage L₀ Game_import E₀ G₀}
  {V2 : ValidPackage L₀' Game_import E₀ G₀'}
  {V3 : ValidPackage L₁ Game_import E₁ G₁}
  {P : Parable (ID E₀) G₁} :
  trimmed E₀ G₀ → trimmed E₁ G₁ → trimmed E₀ G₀' →
  Adv (G₀ || G₁) (G₀' || G₁) A = Adv G₀ G₀' (A ∘ (ID E₀ || G₁)).
Proof.
  intros tr0 tr1 tr2.
  rewrite -Adv_sep_link.
  rewrite swash.
  2-4: try nssprove_valid.
  rewrite sep_par_empty_r.
  rewrite swash.
  2-4: try nssprove_valid.
  rewrite sep_par_empty_r.
  reflexivity.
Qed.


Definition AdvFor GG A : R := Adv (GG true) (GG false) A.

Lemma AdvFor_perfect {L E} {G G'} {A : raw_module}
  {V : ValidPackage L E A_export A} :
  (∀ b : bool, perfect E (G b) (G' b)) →
  AdvFor G A = Adv (G' true) (G' false) A.
Proof.
  intros H.
  rewrite /AdvFor (Adv_perfect_r (H false)).
  rewrite (Adv_perfect_l (H true)) //.
Qed.
