From NominalSSP Require Import Options Misc Replacement PRF PRP.

Section PRPPRF.
  Context (N K : nat) (F : 'Z_K → 'Z_N → 'Z_N).
  
  Definition MOD_PRF : package (I_PRP N) (I_PRF N) :=
    [package emptym ;
      [ INIT ] (_) { 
        _ ← call [ INIT ] tt ;;
        ret tt
      } ;
      [ QUERY ] (x) {
        '(y, _) ← call [ QUERY ] x ;;
        ret y
      }
    ].

  Definition MOD_Replacement : package (I_SAMPLE N) (I_PRP N) :=
    [package [fmap lazy_map_loc N ] ;
      [ INIT ] (_) {
        ret tt
      } ;
      [ QUERY ] (x) {
        L ← get lazy_map_loc N ;;
        if L x is Some y then
          ret (y, true)
        else
          '(y', n) ← call [ SAMPLE ] tt ;;
          #put lazy_map_loc N := setm L x y' ;;
          ret (y', n)
      }
    ].

  Lemma codomm_set {T S : ordType} (L : {fmap T → S}) t s
    : codomm (setm L t s) = s |: codomm L.
  Proof.
  Admitted.  (*
    apply /fsubsetP => s' H.
    rewrite in_fsetU in_fset1.
    apply /orP.
    move: H => /codommP [t' H].
    rewrite setmE in H.
    destruct (t' == t)%B.
    - injection H => ->. rewrite eq_refl. by left.
    - right. apply /codommP. by exists t'.
  Qed. *)

  Lemma PRP_MOD_Replacement : perfect
    (I_PRP N) (PRP1 N) (MOD_Replacement ∘ NotReplaced N).
  Proof.
    ssp_prhl (heap_ignore [fmap prev_loc N ]
      ⋊ couple_rhs (lazy_map_loc N) (prev_loc N) (λ L prev, fset prev = codomm L)).
    - ssp_ret.
    - ssprove_code_simpl; simpl.
      ssprove_code_simpl_more. (* Why is this line necessary? *)
      apply r_get_vs_get_remember => L.
      destruct (L arg) eqn:E; rewrite E; [ ssp_ret |].
      ssprove_sync => y.
      apply r_get_remember_rhs => prev.
      ssprove_rem_rel 0%N => <-.
      rewrite in_fset.
      destruct (y \in prev) eqn:E'; rewrite E'.
      + apply r_put_vs_put.
        ssp_ret. rewrite codomm_set => <-.
        symmetry. apply /fsetUidPr.
        by rewrite fsub1set in_fset.
      + apply r_put_rhs, r_put_vs_put.
        ssp_ret. rewrite codomm_set => <-.
        by rewrite fset_cons.
  Qed.

  Lemma PRF_MOD_Replacement : perfect
    (I_PRF N) (PRF1 N) (MOD_PRF ∘ MOD_Replacement ∘ Replaced N).
  Proof.
    ssp_prhl_eq.
    - ssp_ret.
    - ssprove_sync_eq => L.
      destruct (L arg) eqn:E; rewrite E; [ ssp_ret |].
      ssprove_code_simpl; simpl.
      ssprove_sync_eq => y.
      ssprove_sync_eq.
      ssp_ret.
  Qed.

  Theorem Switching A {VA : ValidPackage (loc A) (I_PRF N) A_export A}
    : Adv (PRF1 N) (MOD_PRF ∘ PRP1 N) A <=
      AdvOf (Replacement N) (A ∘ MOD_PRF ∘ MOD_Replacement).
  Proof.
    rewrite (Adv_perfect_l PRF_MOD_Replacement) Adv_reduction.
    rewrite (Adv_perfect_r PRP_MOD_Replacement) Adv_reduction.
    by rewrite sep_link_assoc.
  Qed.

  Lemma PRF_PRP_real : perfect (I_PRF N) (PRF0 K N F) (MOD_PRF ∘ PRP0 K N F).
  Proof.
    ssp_prhl (heap_ignore emptym). (* Why can this not be eq invariant *)
    - ssprove_sync => k.
      apply r_put_vs_put.
      ssp_ret.
    - ssprove_sync => o_k.
      ssprove_code_simpl_more.
      ssprove_sync => Hk.
      ssp_ret.
  Qed.

  Theorem PRP_PRF A {VA : ValidPackage (loc A) (I_PRF N) A_export A}
    : AdvOf (PRF K N F) A
      <= AdvOf (PRP K N F) (A ∘ MOD_PRF)
       + AdvOf (Replacement N) (A ∘ MOD_PRF ∘ MOD_Replacement).
  Proof.
    rewrite (Adv_perfect_l PRF_PRP_real).
    ssprove_hop (MOD_PRF ∘ PRP1 N).
    rewrite Adv_reduction.
    apply lerD => [ // |]. (* // in both with lociking? *)
    rewrite Adv_sym. by apply Switching.
  Qed.
End PRPPRF.
