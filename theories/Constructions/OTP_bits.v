From NominalSSP Require Import Options Misc.
From NominalSSP.Primitives Require Import SKE.

Section OTP. (* Ordinal based One-Time Pad *)

  Context (n : nat).

  Definition OTP : SKE := {|
      Key := n.-bits
    ; Mes := n.-bits
    ; Cip := n.-bits
    ; KeyDist := {code
        k ← sample uniform_bits n ;;
        ret k
      }
    ; Enc := λ k m, {code
        ret (m ⊕ k)
      }
    ; Dec := λ k c, Some (c ⊕ k)
    ; CipDist := {code
        r ← sample uniform_bits n ;;
        ret r
      }
    |}.

  Theorem correct_OTP : perfect (I_CORR OTP) (CORR0 OTP) (CORR1 OTP).
  Proof.
    ssp_prhl_eq.
    apply r_const_sample_L; [ exact _ |] => k.
    rewrite xorbK. ssp_ret.
  Qed.
  
  Theorem OTS_OTP : perfect (I_OTS OTP) (OTS OTP true) (OTS OTP false).
  Proof.
    ssp_prhl_eq.
    eapply r_uniform_bij; [ apply (xor_bij arg) |] => c1.
    ssp_ret.
  Qed.

End OTP.
