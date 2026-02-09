From NominalSSP Require Import Options Misc.
From NominalSSP.Primitives Require Import SKE.

Section OTP. (* Ordinal based One-Time Pad *)

  Context (n : nat).

  Definition OTP : SKE := {|
      Key := 'Z_n
    ; Mes := 'Z_n
    ; Cip := 'Z_n
    ; CipDist := {code
        r ← sample uniformZ n ;;
        ret r
      }
    ; KeyDist := {code
        k ← sample uniformZ n ;;
        ret k
      }
    ; Enc := λ k m, {code
        ret (m + k)
      }
    ; Dec := λ k c, Some (c - k)
    |}.

  Theorem correct_OTP : perfect (I_CORR OTP) (CORR0 OTP) (CORR1 OTP).
  Proof.
    ssp_prhl_eq.
    apply r_const_sample_L; [ exact _ |] => k.
    rewrite GRing.addrK. ssp_ret.
  Qed.
  
  Lemma add_bij (m : 'Z_n) : bijective (λ k, m + k).
  Proof.
    exists (λ k, - m + k) => k; [ by rewrite GRing.addKr | ].
    by rewrite GRing.addrA GRing.subrr GRing.add0r.
  Qed.

  Theorem OTS_OTP : perfect (I_OTS OTP) (OTS OTP true) (OTS OTP false).
  Proof.
    ssp_prhl_eq.
    eapply r_uniform_bij; [ apply (add_bij arg) |] => c1.
    ssp_ret.
  Qed.

End OTP.
