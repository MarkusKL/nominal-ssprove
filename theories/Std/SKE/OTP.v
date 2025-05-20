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

From NominalSSP Require Import Prelude Std.SKE.Scheme.
Import PackageNotation.
#[local] Open Scope package_scope.

Import GroupScope.

Import SKE.


Section OTP.

  Context {F : finGroupType}.

  #[export] Instance F_pos : Positive #|F|.
  Proof.
    apply /card_gt0P. by exists 1.
  Qed.

  Definition otp : scheme := {|
      Key := 'fin #|F|
    ; Mes := 'fin #|F|
    ; Cip := 'fin #|F|
    ; sample_Cip :=
      {code
        r ← sample uniform #|F| ;;
        ret r
      }
    ; keygen :=
      {code
        k ← sample uniform #|F| ;;
        ret k
      }
    ; enc := λ k m,
      {code
        ret (fto (otf m * otf k)) 
      }
    ; dec := λ k c,
      {code
        ret (fto (otf c * (otf k)^-1))
      }
    |}.

  Theorem correct_otp : perfect (I_CORR otp) (CORR0 otp) (CORR1 otp).
  Proof.
    eapply prove_perfect.
    apply eq_rel_perf_ind_eq.
    simplify_eq_rel m.
    apply r_const_sample_L.
    1: apply LosslessOp_uniform.
    intros k.
    rewrite otf_fto mulgK fto_otf.
    by apply r_ret.
  Qed.

  Lemma bijective_add {m : 'fin #|F|} : bijective (λ k, fto (otf m * otf k)).
  Proof.
    exists (λ k, fto ((otf m)^-1 * otf k)).
    - intros x. rewrite otf_fto mulKg fto_otf //.
    - intros x. rewrite otf_fto mulKVg fto_otf //.
  Qed.

  Theorem otsr_otp : perfect (I_OTSR otp) (OTSR otp true) (OTSR otp false).
  Proof.
    eapply prove_perfect.
    apply eq_rel_perf_ind_eq.
    simplify_eq_rel m.
    eapply (r_uniform_bij _ _ _ _ _ _ _ bijective_add) => c1.
    apply r_ret => s0 s1 ->.
    split; [| done ].
    reflexivity.
  Qed.

End OTP.
