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

From NominalSSP Require Import Prelude Group.
Import Num.Def Num.Theory Order.POrderTheory.
Import PackageNotation.
#[local] Open Scope ring_scope.
#[local] Open Scope package_scope.
Import GroupScope GRing.Theory.

From NominalSSP Require Import DDH Scheme Reductions.


Module ElGamal (GP : GroupParam).

Module DDH' := DDH GP.
Import PKScheme PKReductions DDH'.

Module GT := GroupTheorems GP.
Import GP GT.

Definition elgamal : pk_scheme := {|
    Sec := 'fin #|exp|
  ; Pub := 'fin #|el|
  ; Mes := 'fin #|el|
  ; Cip := 'fin #|el| × 'fin #|el|
  ; sample_Cip :=
    {code
      c₁ ← sample uniform #|el| ;;
      c₂ ← sample uniform #|el| ;;
      ret (c₁, c₂)
    }
  ; keygen :=
    {code
      sk ← sample uniform #|exp| ;;
      ret (sk, op_exp op_g sk)
    }
  ; enc := λ pk m,
    {code
      r ← sample uniform #|exp| ;;
      ret (op_exp op_g r, op_mul m (op_exp pk r))
    }
  ; dec := λ sk c,
    {code
      ret (op_mul (snd c) (op_expn (fst c) sk))
    }
  |}.


Theorem correct_elgamal : perfect (I_CORR elgamal) (CORR0 elgamal) (CORR1 elgamal).
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
  unfold op_mul, op_exp, op_g, op_expn.
  rewrite !otf_fto expgAC -mulgA mulgV mulg1 fto_otf //.
Qed.

Notation init' := (
  mpk ← get init_loc elgamal ;;
  match mpk with
  | None => 
    pk ← call GETA 'unit 'el tt ;;
    #put init_loc elgamal := Some pk ;;
    ret pk
  | Some pk =>
    ret pk
  end).

Definition RED :
  module I_DDH (I_PK_OTSR elgamal) :=
  [module fset
    [:: flag_loc; init_loc elgamal ] ;
    #def #[ GET ] (_ : 'unit) : 'el {
      pk ← init' ;;
      @ret 'el pk
    } ;
    #def #[ QUERY ] (m : 'el)
        : 'el × 'el {
      _ ← init' ;;
      getNone flag_loc ;;
      #put flag_loc := Some tt ;;
      '(r, sh) ← call
        GETBC 'unit ('el × 'el) tt ;;
      @ret ('el × 'el) (r, op_mul m sh)
    }
  ].

Notation inv0 := (
  heap_ignore (fset [:: mga_loc ])
  ⋊ triple_rhs flag_loc (PKScheme.init_loc elgamal) mga_loc
      (λ f pk ga, ~~ f → pk = ga)
).

Lemma PK_OTSR_RED_DDH_perfect b :
  perfect (I_PK_OTSR elgamal) (PK_OTSR elgamal b) (RED ∘ DDH b).
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
  - rewrite /init -lock //=.
    apply r_get_vs_get_remember.
    1: ssprove_invariant.
    move=> //= pk.
    destruct pk.
    1: {
      rewrite code_link_bind //=.
      apply r_ret.
      intros s0 s1 H.
      split; [ done | apply H ].
    }
    ssprove_code_simpl; simpl.
    ssprove_sync => a.
    apply r_put_rhs.
    apply r_put_vs_put.
    ssprove_restore_mem.
    2: by apply r_ret.
    ssprove_invariant.
    intros h0 h1 H f.
    by get_heap_simpl.

  - rewrite /init -lock //=.
    apply r_get_vs_get_remember.
    1: ssprove_invariant.
    move=> //= pk.
    destruct pk as [pk|].
    1,2: ssprove_code_simpl; simpl.
    + apply r_get_vs_get_remember.
      1: ssprove_invariant.
      intros f.
      ssprove_sync => H.
      ssprove_swap_rhs 0%N.
      apply r_get_remember_rhs => ga.
      eapply (r_rem_triple_rhs flag_loc (PKScheme.init_loc elgamal) mga_loc).
      1-4: exact _.
      move: H => /eqP H //= H'.
      rewrite H //= in H'.
      rewrite -H' //= => {H'} {ga}.
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
      * ssprove_sync => b.
        by apply r_ret.
      * eapply rsymmetry.
        eapply (r_uniform_bij _ _ _ _ _ _ _ bij_op_exp) => c1.
        eapply (r_uniform_bij _ _ _ _ _ _ _ (bij_op_mult_op_exp m)) => c2.
        by eapply r_ret.
    + apply r_forget_rhs, r_forget_lhs.
      ssprove_sync => a.
      ssprove_swap_lhs 0%N.
      ssprove_swap_rhs 1%N.
      ssprove_swap_rhs 0%N.
      apply r_get_vs_get_remember.
      1: ssprove_invariant.
      move=> //= pk.
      ssprove_swap_seq_rhs [:: 3%N; 2%N; 1%N ].
      ssprove_contract_put_get_rhs.
      ssprove_swap_lhs 0%N.
      ssprove_swap_rhs 1%N.
      ssprove_swap_rhs 0%N.
      ssprove_sync => /eqP -> {pk}.
      ssprove_code_simpl; simpl.
      ssprove_swap_rhs 2%N.
      ssprove_swap_rhs 1%N.
      ssprove_contract_put_rhs.
      apply r_put_rhs.
      do 2 apply r_put_vs_put.
      ssprove_restore_mem.
      1: by ssprove_invariant.
      destruct b; simpl.
      * ssprove_sync => b.
        by apply r_ret.
      * eapply rsymmetry.
        eapply (r_uniform_bij _ _ _ _ _ _ _ bij_op_exp) => c1.
        eapply (r_uniform_bij _ _ _ _ _ _ _ (bij_op_mult_op_exp m)) => c2.
        by eapply r_ret.
Qed.


Lemma OTSR_elgamal (A : adversary (I_PK_OTSR elgamal)) :
  AdvFor (PK_OTSR elgamal) A = AdvFor DDH (A ∘ RED).
Proof. rewrite (AdvFor_perfect PK_OTSR_RED_DDH_perfect) Adv_sep_link //. Qed.


Theorem CPA_elgamal {n} {p} (A : adversary (I_PK_CPA elgamal)) :
  (∀ i b, AdvFor DDH (A ∘ SLIDE elgamal i n ∘ CHOOSE elgamal b ∘ RED) <= p) →
  AdvFor (PK_CPA elgamal n) A <= p *+ 2 *+ n.
Proof.
  intros H.  apply Adv_CPA_OTSR_p => i b. 
  eapply le_trans; [ apply eq_ler | apply (H i b) ].
  rewrite /AdvFor 2!(sep_link_assoc _ _ RED).  apply (OTSR_elgamal
    {adversary (I_PK_OTSR elgamal) ; A ∘ SLIDE elgamal i n ∘ CHOOSE elgamal b}).
Qed.

End ElGamal.
