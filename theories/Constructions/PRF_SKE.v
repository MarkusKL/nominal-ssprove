From NominalSSP Require Import Options Misc Nonce PRF SKE.

Section PRFSKE.
  Context (K N : nat) (F : K.-bits → N.-bits → N.-bits).

  Definition PRFSKE := {|
      Key := K.-bits
    ; Mes := N.-bits
    ; Cip := N.-bits × N.-bits
    ; KeyDist := {code
        k ← sample uniform_bits K ;; ret k
      }
    ; Enc := λ k m, {code 
        r ← sample uniform_bits N ;;
        ret (r, m ⊕ F k r)
      }
    ; Dec := λ k '(r, c), Some (c ⊕ F k r)
    ; CipDist := {code
        r ← sample uniform_bits N ;;
        c ← sample uniform_bits N ;;
        ret (r, c)
    }
    |}.

  Theorem correct_PRFSKE : perfect (I_CORR PRFSKE) (CORR0 PRFSKE) (CORR1 PRFSKE).
  Proof.
    ssp_prhl_eq.
    apply r_const_sample_L; [ exact _ |] => k.
    apply r_const_sample_L; [ exact _ |] => r.
    rewrite xorbK. ssp_ret.
  Qed.

  Definition MOD_CPA : package (unionm (I_PRF N) (I_Nonce (2 ^ N))) (I_CPA PRFSKE) :=
    [package emptym ;
      [ GEN ] (_) {
        _ ← call [ INIT ] tt ;;
        ret tt
      } ;
      [ QUERY ] (m) {
        '(r, n) ← call [ NONCE ] : { unit ~> N.-bits × bool } tt ;;
        v ← call [ QUERY ] : { N.-bits ~> N.-bits } r ;;
        if n then 
          ret (r, v ⊕ m)
        else
          a ← sample uniform_bits N ;;
          ret (r, a)
      }
    ].

  Lemma CPA_PRFSKE_1 : perfect (I_CPA PRFSKE)
    (CPA0 PRFSKE) (MOD_CPA ∘ (PRF0 _ _ F || Nonce0 (2 ^ N))).
  Proof.
    ssp_prhl (heap_ignore [fmap key_loc PRFSKE; PRF.key_loc K ]
      ⋊ couple_cross (key_loc PRFSKE) (PRF.key_loc K) eq).
    - ssprove_sync => k. apply r_put_vs_put. ssp_ret.
    - ssprove_swap_seq_lhs [:: 1%N; 0%N ].
      ssprove_sync => r.
      eapply r_get_remember_lhs => k.
      eapply r_get_remember_rhs => k'.
      ssprove_rem_rel 0%N => {k'}<-. ssp_simpl.
      destruct k; [ rewrite //= xorC; ssp_ret | apply r_fail ].
  Qed.

  Lemma CPA_PRFSKE_2 : perfect (I_CPA PRFSKE)
    (MOD_CPA ∘ (PRF1 N || Nonce1 (2 ^ N))) (CPA1 PRFSKE).
  Proof.
    ssp_prhl (heap_ignore [fmap nonce_loc (2 ^ N); lazy_map_loc N]
      ⋊ couple_lhs (nonce_loc (2 ^ N)) (lazy_map_loc N) (λ prev L, fset prev = domm L)).
    - ssp_ret.
    - ssp_simpl. ssprove_sync => r.
      apply r_get_remember_lhs => prev.
      destruct (r \in prev) eqn:E; rewrite E /=.
      + apply r_get_remember_lhs => L.
        ssprove_rem_rel 0%N => Hprev.
        rewrite -in_fset Hprev in E.
        move: E => /dommP [v ->] /=.
        ssprove_sync => ?. ssp_ret.
      + ssprove_swap_lhs 0%N.
        apply r_get_remember_lhs => L.
        ssprove_rem_rel 0%N => Hprev.
        rewrite -in_fset Hprev in E.
        move: E => /dommPn ->.
        ssprove_swap_lhs 0%N.
        eapply r_uniform_bij; [ apply (xor_bij arg) |] => c1 /=.
        rewrite xorC. do 2 apply r_put_lhs.
        ssp_ret. intros H. by rewrite domm_set fset_cons H.
  Qed.

  Theorem CPA_PRFSKE A {VA : ValidPackage (loc A) (I_CPA PRFSKE) A_export A}
    : AdvOf (CPA PRFSKE) A <=
      AdvOf (PRF K N F) (A ∘ MOD_CPA ∘ (ID (I_PRF N) || Nonce0 (2 ^ N))) +
      AdvOf (Nonce (2 ^ N)) (A ∘ MOD_CPA ∘ (PRF1 N || ID (I_Nonce (2 ^ N)))).
  Proof.
    rewrite (Adv_perfect_l CPA_PRFSKE_1) -(Adv_perfect_r CPA_PRFSKE_2).
    rewrite Adv_reduction.
    ssprove_hop (PRF1 N || Nonce0 (2 ^ N)).
    by rewrite Adv_par_l Adv_par_r -2!sep_link_assoc.
  Qed.
End PRFSKE.
