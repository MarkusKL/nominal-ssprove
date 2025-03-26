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

Import PackageNotation.

From NominalSSP Require Import FsetSolve Group Nominal NomPackage Disjoint Sigma.

Module Schnorr (GP : GroupParam).

Module GT := GroupTheorems GP.
Import GP GT.

#[export] Instance Positive_el : Positive #|el|.
Proof. apply /card_gt0P. by exists g. Qed.

#[export] Instance Positive_exp : Positive #|exp|.
Proof. apply /card_gt0P. by exists 0. Qed.

Definition commit_loc : Location := ('fin #|exp|; 0%N).

Definition raw_schnorr : raw_sigma :=
  {| Statement := 'fin #|el|
   ; Witness := 'fin #|exp|
   ; Message := 'fin #|el|
   ; State := 'fin #|exp|
   ; Challenge := 'fin #|exp|
   ; Response := 'fin #|exp|

   ; R :=
      (λ h w, otf h == (g ^+ otf w))%bool
   ; commit := λ h w,
     {code
       r ← sample uniform #|exp| ;;
       ret (fto (g ^+ otf r), r)
     }
   ; response := λ h w a r e,
     {code
       ret (fto (otf r + otf w * otf e))
     }
   ; simulate := λ h e,
     {code
       z ← sample uniform #|exp| ;;
       ret (fto (g ^+ otf z * (otf h ^- otf e)), z)
     }
   ; verify := λ h a e z,
     (g ^+ otf z == otf a * otf h ^+ otf e)%bool
   ; extractor := λ h a e e' z z',
     Some (fto ((otf z - otf z') / (otf e - otf e')))
  |}.

#[local] Open Scope package_scope.

(*
Lemma heap_ignore_locs :
  Invariant raw_schnorr.(locs) fset0 (heap_ignore raw_schnorr.(locs)).
Proof. ssprove_invariant. apply fsubsetUl. Qed.
 *)

Theorem schnorr_Correct : Adv_Correct raw_schnorr (λ _, 0).
Proof.
  intros A.
  apply eq_ler.
  eapply Adv_perf; [| apply module_valid ].
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel hwe.
  move: hwe => [[h w] e].
  ssprove_sync => /eqP -> {h}.
  apply r_const_sample_L => [|a].
  1: apply LosslessOp_uniform.
  apply r_ret => s0 s1 H.
  split; [| assumption ].
  apply /eqP.
  rewrite !otf_fto expg_modq expgD expg_modq expgM //.
Qed.

#[local] Definition f (e w : 'witness raw_schnorr) :
  Arit (uniform #|exp|) → Arit (uniform #|exp|) :=
  λ z, fto (otf z + otf e * otf w).

Lemma bij_f w e : bijective (f w e).
Proof.
  unfold f.
  exists (λ x, fto (otf x - otf w * otf e)).
  1,2: intros x; rewrite otf_fto ?addrK ?subrK fto_otf //.
Qed.

Theorem schnorr_SHVZK : Adv_SHVZK raw_schnorr (λ _, 0).
Proof.
  intros A.
  apply eq_ler.
  eapply Adv_perf; [| apply module_valid ].
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel hwe.
  destruct hwe as [[h w] e].
  rewrite -(fto_otf h) -(fto_otf e).
  move: (otf w) (otf h) (otf e) => {}w {}h {}e.
  rewrite 2!otf_fto.
  ssprove_sync_eq => /eqP -> {h}.
  eapply r_uniform_bij with (1 := bij_f (fto w) (fto e)) => z.
  apply r_ret.

  intros s₀ s₁ Hs.
  split; [| assumption ].
  do 4 f_equal.
  1,2: rewrite /f !otf_fto //=.
  rewrite expg_modq expgD -mulgA -expgM expg_modq mulgV mulg1 //.
Qed.

Lemma schnorr_Special_Soundness : Adv_Special_Soundness raw_schnorr (λ _, 0).
Proof.
  intros A.
  apply eq_ler.
  eapply Adv_perf; [| apply module_valid ].
  eapply eq_rel_perf_ind_eq.
  simplify_eq_rel h.
  destruct h as [[h R] [[e1 z1] [e2 z2]]].
  ssprove_sync => /eqP H1.
  ssprove_sync => /eqP H2.
  ssprove_sync => /eqP H3.
  apply r_ret => s0 s1 H.
  split; [| assumption ].

  symmetry.
  apply /eqP.
  rewrite otf_fto expg_frac expg_sub.
  rewrite mulgC.
  rewrite H1 H2 invMg.
  rewrite mulgA.
  rewrite -(mulgA _ _ (otf R)) mulVg mulg1.
  rewrite (mulgC _ (_ ^+ _)).
  rewrite -expg_sub -expg_frac.
  rewrite expg_fracgg //.
  apply /eqP => H4.
  apply subr0_eq in H4.
  apply (f_equal fto) in H4.
  rewrite 2!fto_otf // in H4.
Qed.

End Schnorr.
