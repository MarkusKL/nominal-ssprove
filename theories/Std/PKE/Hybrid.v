Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra
  reals distr realsum.
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

From NominalSSP.Std Require Import PKE.Scheme SKE.Scheme.

#[local] Open Scope ring_scope.
Import GRing.Theory.
Import Num.Def Num.Theory Order.POrderTheory.


Record inj A B :=
  { encode : A → B
  ; decode : B → A
  ; cancels : cancel encode decode
  }.

Arguments encode {_ _} _.
Arguments decode {_ _} _.
Arguments cancels {_ _} _.


Section Hybrid.
  Context (pke : PKE.scheme) (ske : SKE.scheme)
    (i : inj ske.(SKE.Key) pke.(PKE.Mes)).

  Definition hybrid : PKE.scheme := {|
      PKE.Sec := pke.(PKE.Sec)
    ; PKE.Pub := pke.(PKE.Pub)
    ; PKE.Mes := ske.(SKE.Mes)
    ; PKE.Cip := pke.(PKE.Cip) × ske.(SKE.Cip)
    ; PKE.sample_Cip :=
      {code
        c1 ← pke.(PKE.sample_Cip) ;;
        c2 ← ske.(SKE.sample_Cip) ;;
        ret (c1, c2)
      }
    ; PKE.keygen := pke.(PKE.keygen)
    ; PKE.enc := λ pk m,
      {code
        k ← ske.(SKE.keygen) ;;
        ek ← pke.(PKE.enc) pk (i.(encode) k) ;;
        c ← ske.(SKE.enc) k m ;;
        ret (ek, c)
      }
    ; PKE.dec := λ sk '(ek, c),
      {code
        k ← pke.(PKE.dec) sk ek ;;
        m ← ske.(SKE.dec) (i.(decode) k) c ;;
        ret m
      }
    |}.

  Definition CORR_RED :
    module (PKE.I_CORR pke) (PKE.I_CORR hybrid) :=
    [module no_locs ;
      [ PKE.ENCDEC ] : { hybrid.(PKE.Mes) ~> hybrid.(PKE.Mes) } (m) {
        k ← ske.(SKE.keygen) ;;
        k' ← call PKE.ENCDEC (pke.(PKE.Mes)) (pke.(PKE.Mes)) (i.(encode) k) ;;
        c ← ske.(SKE.enc) k m ;;
        m ← ske.(SKE.dec) (i.(decode) k') c ;;
        ret m
      }
    ].

  Lemma correct_hybrid_1
    : perfect (PKE.I_CORR hybrid) (PKE.CORR0 hybrid) (CORR_RED ∘ PKE.CORR0 pke).
  Proof.
    nssprove_share.
    eapply prove_perfect.
    apply eq_rel_perf_ind_eq.
    simplify_eq_rel m.
    ssprove_code_simpl.
    rewrite cast_fun_K.
    ssprove_code_simpl.
    eapply rel_jdg_replace_sem_r; simpl.
    2: eapply swap_code; ssprove_valid; apply (fdisjoint0s fset0).
    apply rsame_head => [[sk pk]].
    apply rsame_head => k.
    apply rsame_head => ek.
    eapply rel_jdg_replace_sem_l; simpl.
    2: eapply swap_code; ssprove_valid; apply (fdisjoint0s fset0).
    apply rsame_head => k'.
    apply rsame_head => c.
    apply rsame_head => m'.
    by apply r_ret.
  Qed.

  Lemma correct_hybrid_2 : perfect (PKE.I_CORR hybrid)
    (CORR_RED ∘ PKE.CORR1 pke) (SKE.CORR0 ske).
  Proof.
    nssprove_share.
    eapply prove_perfect.
    apply eq_rel_perf_ind_eq.
    simplify_eq_rel m.
    ssprove_code_simpl.
    apply rsame_head => ?.
    apply rsame_head => ?.
    rewrite cancels.
    apply rsame_head => ?.
    by apply r_ret.
  Qed.

  Theorem correct_hybrid (A : adversary (PKE.I_CORR hybrid)) :
    AdvFor (PKE.CORR hybrid) A
      <= AdvFor (PKE.CORR pke) (A ∘ CORR_RED)
      +  AdvFor (SKE.CORR ske) A.
  Proof.
    rewrite /AdvFor (Adv_perfect_l correct_hybrid_1).
    nssprove_adv_trans (CORR_RED ∘ PKE.CORR1 pke)%sep.
    apply lerD.
    + rewrite Adv_sep_link //.
    + rewrite (Adv_perfect_l correct_hybrid_2) //.
  Qed.

  Definition OTS_STAGE1 :
    module (PKE.I_PK_OTSR pke) (PKE.I_PK_OTSR hybrid) :=
    [module no_locs ;
      [ PKE.INIT ] : { 'unit ~> 'unit } 'tt {
        pk ← call PKE.INIT 'unit 'unit tt ;;
        ret pk
      } ;
      [ PKE.GET ] : { 'unit ~> hybrid.(PKE.Pub) } 'tt {
        pk ← call PKE.GET 'unit pke.(PKE.Pub) tt ;;
        ret pk
      } ;
      [ PKE.QUERY ] : { hybrid.(PKE.Mes) ~> hybrid.(PKE.Cip) } (m) {
        k ← ske.(SKE.keygen) ;;
        ek ← call PKE.QUERY pke.(PKE.Mes) pke.(PKE.Cip) (i.(encode) k) ;;
        c ← ske.(SKE.enc) k m ;;
        ret (ek, c)
      }
    ].

  Definition OTS_STAGE2 :
    module (SKE.I_OTSR ske) (PKE.I_PK_OTSR hybrid) :=
    [module fset [:: PKE.mpk_loc pke ; PKE.flag_loc ] ;
      [ PKE.INIT ] : { 'unit ~> 'unit } 'tt {
        '(_, pk) ← pke.(PKE.keygen) ;;
        #put PKE.mpk_loc pke := Some pk ;;
        ret tt
      } ;
      [ PKE.GET ] : { 'unit ~> hybrid.(PKE.Pub) } 'tt {
        pk ← getSome (PKE.mpk_loc pke) ;;
        ret pk
      } ;
      [ PKE.QUERY ] : { hybrid.(PKE.Mes) ~> hybrid.(PKE.Cip) } (m) {
        _ ← getSome (PKE.mpk_loc pke) ;;
        getNone PKE.flag_loc ;;
        #put PKE.flag_loc := Some tt ;;
        ek ← pke.(PKE.sample_Cip) ;;
        c ← call SKE.QUERY ske.(SKE.Mes) ske.(SKE.Cip) m ;;
        @ret (_ × _) (ek, c)
      }
    ].

  Lemma OTSR_hybrid_1
    : perfect (PKE.I_PK_OTSR hybrid)
      (PKE.PK_OTSR hybrid true) (OTS_STAGE1 ∘ PKE.PK_OTSR pke true).
  Proof.
    nssprove_share.
    eapply prove_perfect.
    apply eq_rel_perf_ind_eq.
    simplify_eq_rel m.
    - destruct m; simpl.
      simplify_linking.
      rewrite cast_fun_K.
      ssprove_code_simpl.
      apply r_refl.
    - destruct m; simpl.
      simplify_linking.
      ssprove_code_simpl_more.
      apply r_refl.
    - ssprove_code_simpl.
  Admitted.

  Lemma OTSR_hybrid_2
    : perfect (PKE.I_PK_OTSR hybrid)
      (OTS_STAGE1 ∘ PKE.PK_OTSR pke false)
      (OTS_STAGE2 ∘ SKE.OTSR ske true).
  Proof.
    nssprove_share.
    eapply prove_perfect.
    apply eq_rel_perf_ind_eq.
    simplify_eq_rel m.
    - destruct m; simpl.
      simplify_linking.
      ssprove_code_simpl.
      rewrite cast_fun_K bind_ret.
      apply r_refl.
    - destruct m; simpl.
      simplify_linking.
      ssprove_code_simpl_more.
      ssprove_code_simpl.
      apply r_refl.
    - ssprove_code_simpl.
      rewrite cast_fun_K.
      ssprove_code_simpl.
  Admitted.

  Lemma OTSR_hybrid_3
    : perfect (PKE.I_PK_OTSR hybrid)
      (OTS_STAGE2 ∘ SKE.OTSR ske false)
      (PKE.PK_OTSR hybrid false).
  Proof.
    nssprove_share.
    eapply prove_perfect.
    apply eq_rel_perf_ind_eq.
    simplify_eq_rel m.
    - destruct m; simpl.
      ssprove_code_simpl.
      apply r_refl.
    - destruct m; simpl.
      ssprove_code_simpl.
      apply r_refl.
    - ssprove_code_simpl.
      ssprove_code_simpl.
  Admitted.

  Theorem Adv_PK_OTSR (A : adversary (PKE.I_PK_OTSR hybrid)) :
    AdvFor (PKE.PK_OTSR hybrid) A
      <= AdvFor (PKE.PK_OTSR pke) (A ∘ OTS_STAGE1)
      +  AdvFor (SKE.OTSR ske) (A ∘ OTS_STAGE2).
  Proof.
    unfold AdvFor.
    rewrite (Adv_perfect_l OTSR_hybrid_1).
    rewrite -(Adv_perfect_r OTSR_hybrid_3).
    nssprove_adv_trans (OTS_STAGE2 ∘ SKE.OTSR ske true)%sep.
    apply lerD.
    + rewrite -(Adv_perfect_r OTSR_hybrid_2) Adv_sep_link //.
    + rewrite Adv_sep_link //.
  Qed.

End Hybrid.


From NominalSSP.Std Require Import Math.Group Assumptions.DDH PKE.ElGamal SKE.OTP.

Context (G : CyclicGroup).

Program Definition id_inj (A : Type) : inj A A := {|
 encode := id ;
 decode := id
 |}.
Obligation 1. done. Qed.

Let scheme := hybrid (elgamal G) (@otp (gT G)) (id_inj _).

Theorem Adv_scheme (A : adversary (PKE.I_PK_OTSR scheme)) :
  AdvFor (PKE.PK_OTSR scheme) A
  <= AdvFor (DDH G) (A ∘ OTS_STAGE1 (elgamal G) (@otp (gT G)) (id_inj _) ∘ RED G) + 0.
Proof.
  eapply le_trans.
  1: apply Adv_PK_OTSR.
  apply lerD.
  1: admit.
  rewrite /AdvFor otsr_otp //.
Admitted.

