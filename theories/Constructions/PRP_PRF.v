From NominalSSP Require Import Options Misc Replacement PRF PRP.

Section PRPPRF.
  Context (N K : nat) (F : K.-bits → N.-bits → N.-bits).
  
  Definition MOD_Replacement : package (I_Sample (2 ^ N)) (I_PRP N) :=
    [package [fmap lazy_map_loc N ] ;
      [ INIT ] (_) {
        getNone lazy_map_loc N ;;
        #put lazy_map_loc N := Some emptym ;;
        ret tt
      } ;
      [ QUERY ] (x) {
        L ← getSome lazy_map_loc N ;;
        if L x is Some y then
          ret y
        else
          y' ← call [ SAMPLE ] tt ;;
          #put lazy_map_loc N := Some (setm L x y') ;;
          ret y'
      }
    ].

  Lemma PRP_MOD_Replacement : perfect
    (I_PRP N) (PRP1 N) (MOD_Replacement ∘ NotReplaced (2 ^ N)).
  Proof.
    ssp_prhl (heap_ignore [fmap prev_loc (2 ^ N) ] ⋊
      couple_rhs (lazy_map_loc N) (prev_loc (2 ^ N))
        (λ L prev, fset prev = codomm (odflt emptym L))).
    - apply: r_get_vs_get_remember => L.
      rewrite code_link_assertD. (* ?? *)
      ssprove_sync => /eqP {L}->.
      (* ssprove_code_simpl_more.  "No applicable tactic." error *)
      apply r_put_vs_put. ssp_ret.
    - ssp_simpl. 
      apply r_get_vs_get_remember => L.
      ssprove_sync => HL. destruct L as [L|] => //= {HL}.
      destruct (L arg) eqn:E; rewrite E; [ ssp_ret |].
      apply r_get_remember_rhs => prev.
      ssprove_rem_rel 0%N => <-.
      ssprove_sync => y.
      move=> /dommPn in E.
      apply r_put_rhs, r_put_vs_put.
      ssp_ret. rewrite codomm_set // => <-.
      by rewrite fset_cons.
  Qed.

  Lemma PRF_MOD_Replacement : perfect
    (I_PRF N) (PRF1 N) (MOD_Replacement ∘ Replaced (2 ^ N)).
  Proof.
    ssp_prhl_eq.
    - apply: r_get_vs_get_remember => L.
      rewrite code_link_assertD. (* ?? *)
      ssprove_sync => /eqP {L}->.
      (* ssprove_code_simpl_more.  "No applicable tactic." error *)
      apply r_put_vs_put. ssp_ret.
    - ssprove_sync_eq => L.
      rewrite code_link_assertD.
      ssprove_sync_eq => HL. destruct L as [L|] => //= {HL}.
      destruct (L arg) eqn:E; rewrite E; [ ssp_ret |].
      ssp_simpl.
      ssprove_sync_eq => y.
      ssprove_sync_eq.
      ssp_ret.
  Qed.

  Theorem Switching A {VA : ValidPackage (loc A) (I_PRF N) A_export A}
    : Adv (PRF1 N) (PRP1 N) A <=
      AdvOf (Replacement (2 ^ N)) (A ∘ MOD_Replacement).
  Proof.
    rewrite (Adv_perfect_l PRF_MOD_Replacement).
    by rewrite (Adv_perfect_r PRP_MOD_Replacement) Adv_reduction.
  Qed.

  Lemma PRF_PRP_real : perfect (I_PRF N) (PRF0 K N F) (PRP0 K N F).
  Proof.
    ssp_prhl (heap_ignore emptym). (* Why can this not be eq invariant *)
    - ssprove_sync => k.
      ssprove_sync => {k}_.
      ssprove_sync => k.
      apply r_put_vs_put.
      ssp_ret.
    - ssprove_sync => o_k.
      ssp_simpl.
      ssprove_sync => Hk.
      ssp_ret.
  Qed.

  Theorem PRP_PRF A {VA : ValidPackage (loc A) (I_PRF N) A_export A}
    : AdvOf (PRF K N F) A
      <= AdvOf (PRP K N F) A
       + AdvOf (Replacement (2 ^ N)) (A ∘ MOD_Replacement).
  Proof.
    rewrite (Adv_perfect_l PRF_PRP_real).
    ssprove_hop (PRP1 N).
    apply lerD => [ // |]. (* // in both with lociking? *)
    rewrite Adv_sym. by apply Switching.
  Qed.
End PRPPRF.
