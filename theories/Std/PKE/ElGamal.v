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

From NominalSSP Require Import Prelude.
Import PackageNotation.
#[local] Open Scope package_scope.

From NominalSSP.Std Require Import Math.Group Assumptions.DDH PKE.Scheme.

Import PKE GroupScope.

Section ElGamal.

Context (G : CyclicGroup).

Definition elgamal : scheme := {|
    Sec := 'exp G
  ; Pub := 'el G
  ; Mes := 'el G
  ; Cip := 'el G × 'el G
  ; sample_Cip :=
    {code
      c₁ ← sample uniform #|el G| ;;
      c₂ ← sample uniform #|el G| ;;
      ret (c₁, c₂)
    }
  ; keygen :=
    {code
      sk ← sample uniform #|exp G| ;;
      ret (sk, 'g ^ sk)%pack
    }
  ; enc := λ pk m,
    {code
      r ← sample uniform #|exp G| ;;
      ret ('g ^ r, m * (pk ^ r))%pack
    }
  ; dec := λ sk '(c₁, c₂),
    {code
      ret (c₂ * (c₁ ^- sk))%pack
    }
  |}.

Theorem correct_elgamal
  : perfect (I_CORR elgamal) (CORR0 elgamal) (CORR1 elgamal).
Proof.
  eapply prove_perfect.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel m.
  apply r_const_sample_L.
  1: apply LosslessOp_uniform.
  intros sk.
  apply r_const_sample_L.
  1: apply LosslessOp_uniform.
  intros r.
  apply r_ret => s0 s1.
  split; subst; [| done ].
  rewrite !otf_fto expgAC -mulgA mulgV mulg1 fto_otf //.
Qed.


Lemma bij_op_exp : bijective (λ a : 'exp G, 'g ^ a : 'el G)%pack.
Proof.
  eexists (λ a, fto (log (otf a))).
  + intros x.
    rewrite 2!otf_fto -{2}(fto_otf x).
    f_equal.
    by apply expg_log.
  + intros x.
    rewrite 2!otf_fto -{2}(fto_otf x).
    f_equal.
    by apply log_expg.
Qed.

Lemma bij_op_mult_op_exp m : bijective (λ b : 'exp G, m * ('g ^ b) : 'el G)%pack.
Proof.
  eexists (λ a, fto (log ((otf m)^-1 * otf a))).
  + intros x.
    rewrite 3!otf_fto -{2}(fto_otf x).
    f_equal.
    rewrite mulKg.
    by apply expg_log.
  + intros x.
    rewrite 3!otf_fto -{2}(fto_otf x).
    f_equal.
    rewrite -{2}(mulKVg (otf m) (otf x)).
    f_equal.
    by apply log_expg.
Qed.

Definition RED :
  module (I_LDDH G) (I_PK_OTSR elgamal) :=
  [module fset
    [:: flag_loc ; mpk_loc elgamal ] ;
    [ INIT ] : { 'unit ~> 'unit } 'tt {
      pk ← (#import [ GETA ] : { 'unit ~> 'el G } tt) ;;
      #put mpk_loc elgamal := Some pk ;;
      ret tt
    } ;
    [ GET ] : { 'unit ~> 'el G } 'tt {
      pk ← getSome mpk_loc elgamal ;;
      @ret 'el G pk
    } ;
    [ QUERY ] : { 'el G ~> 'el G × 'el G } (m) {
      _ ← getSome mpk_loc elgamal ;;
      getNone flag_loc ;;
      #put flag_loc := Some tt ;;
      '(r, sh) ← (#import [ GETBC ] : { 'unit ~> 'el G × 'el G } tt) ;;
      @ret ('el G × 'el G) (r, m * sh)%pack
    }
  ].

Notation inv0 := (
  heap_ignore (fset [:: mga_loc G ])
  ⋊ triple_rhs flag_loc (mpk_loc elgamal) (mga_loc G)
      (λ f pk ga, ~~ f → pk = ga)
).

Lemma PK_OTSR_RED_DDH_perfect b :
  perfect (I_PK_OTSR elgamal) (PK_OTSR elgamal b) (RED ∘ LDDH G b).
Proof.
  nssprove_share. eapply prove_perfect.
  apply (eq_rel_perf_ind _ _ inv0).
  1: ssprove_invariant.
  1-4: simpl.
  1: fset_solve.
  1: right; left; fset_solve.
  1: left; fset_solve.
  1: right; right; fset_solve.
  1: done.

  simplify_eq_rel m.
  - destruct m.
    simpl; simplify_linking.
    ssprove_sync => a.
    apply r_put_rhs.
    apply r_put_vs_put.
    ssprove_restore_pre.
    2: by apply r_ret.
    ssprove_invariant.
    intros h0 h1 H f.
    by get_heap_simpl.

  - destruct m; simpl.
    ssprove_code_simpl.
    ssprove_sync => ?.
    ssprove_sync => ?.
    by apply r_ret.

  - apply r_get_vs_get_remember.  1: ssprove_invariant.  move=> //= mpk.
    ssprove_code_simpl.
    ssprove_sync => H.
    destruct mpk as [pk|] => //= {H}.
    apply r_get_vs_get_remember. 1: ssprove_invariant. move=> //= flag.
    ssprove_sync => H.
    destruct flag => //= {H}.
    ssprove_swap_rhs 0%N.
    apply r_get_remember_rhs => mga.
    eapply (r_rem_triple_rhs flag_loc (mpk_loc elgamal) (mga_loc G)).
    1-4: exact _.
    move=> //= H'.
    rewrite -H' => //= {mga} {H'}.
    apply r_put_vs_put.
    apply r_put_rhs.
    ssprove_restore_mem.
    1: {
      ssprove_invariant.
      intros h0 h1 [[[[[H0 H1] H2] H3] H4] H5].
      rewrite //= /triple_rhs.
      by get_heap_simpl.
    }

    destruct b; simpl.
    + ssprove_sync => b.
      by apply r_ret.
    + eapply rsymmetry.
      eapply (r_uniform_bij _ _ _ _ _ _ _ bij_op_exp) => c1.
      eapply (r_uniform_bij _ _ _ _ _ _ _ (bij_op_mult_op_exp m)) => c2.
      by eapply r_ret.
Qed.

Lemma OTSR_elgamal (A : adversary (I_PK_OTSR elgamal)) :
  AdvFor (PK_OTSR elgamal) A = AdvFor (LDDH G) (A ∘ RED).
Proof. rewrite (AdvFor_perfect PK_OTSR_RED_DDH_perfect) Adv_sep_link //. Qed.

End ElGamal.
