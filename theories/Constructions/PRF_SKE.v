From NominalSSP Require Import Options Misc Replacement PRF SKE.

Section PRFSKE.

  Context (K N : nat) (F : 'Z_K → 'Z_N → 'Z_N).

  Definition PRFSKE := {|
      Key := 'Z_K
    ; Mes := 'Z_N
    ; Cip := 'Z_N × 'Z_N
    ; KeyDist := {code
        k ← sample uniformZ K ;; ret k
      }
    ; Enc := λ k m, {code 
        r ← sample uniformZ N ;;
        ret (r, m + F k r)
      }
    ; Dec := λ k '(r, c), Some (c - F k r)
    ; CipDist := {code
        r ← sample uniformZ N ;;
        c ← sample uniformZ N ;;
        ret (r, c)
    }
    |}.

  Theorem correct_PRFSKE : perfect (I_CORR PRFSKE) (CORR0 PRFSKE) (CORR1 PRFSKE).
  Proof.
    ssp_prhl_eq.
    apply r_const_sample_L; [ exact _ |] => k.
    apply r_const_sample_L; [ exact _ |] => r.
    rewrite GRing.addrK. ssp_ret.
  Qed.

  Lemma add_bij {n} (m : 'Z_n) : bijective (λ k, m + k).
  Proof.
    exists (λ k, - m + k) => k; [ by rewrite GRing.addKr | ].
    by rewrite GRing.addrA GRing.subrr GRing.add0r.
  Qed.

  Definition MOD_CPA : package (unionm (I_PRF N) (I_SAMPLE N)) (I_CPA PRFSKE) :=
    [package emptym ;
      [ GEN ] (_) {
        _ ← call [ INIT ] tt ;;
        ret tt
      } ;
      [ QUERY ] (m) {
        '(r, n) ← call [ SAMPLE ] : { unit ~> 'Z_N × bool } tt ;;
        v ← call [ QUERY ] : { 'Z_N ~> 'Z_N } r ;;
        if n then 
          ret (r, v + m)
        else
          a ← sample uniformZ N ;;
          ret (r, a)
      }
    ].

  Lemma CPA_PRFSKE_1 : perfect (I_CPA PRFSKE)
    (CPA0 PRFSKE) (MOD_CPA ∘ (PRF0 _ _ F || Replaced N)).
  Proof.
    ssp_prhl (heap_ignore [fmap key_loc PRFSKE; PRF.key_loc (Zp_trunc K).+2 ]
      ⋊ couple_cross (key_loc PRFSKE) (PRF.key_loc _) eq).
    - ssprove_sync => k.
      apply r_put_vs_put.
      ssp_ret.
    - ssprove_swap_seq_lhs [:: 1%N; 0%N ].
      ssprove_sync => r.
      eapply r_get_remember_lhs => k.
      eapply r_get_remember_rhs => k'.
      ssprove_rem_rel 0%N => {k'}<-.
      ssprove_code_simpl_more.
      destruct k; [ simpl | apply r_fail ].
      rewrite GRing.addrC. ssp_ret.
  Qed.

  Lemma CPA_PRFSKE_2 : perfect (I_CPA PRFSKE)
    (MOD_CPA ∘ (PRF1 N || NotReplaced N)) (CPA1 PRFSKE).
  Proof.
    ssp_prhl (heap_ignore [fmap prev_loc N; lazy_map_loc N]
      ⋊ couple_lhs (prev_loc N) (lazy_map_loc N) (λ prev L, fset prev = domm L)).
    - ssp_ret.
    - ssprove_code_simpl; simpl.
      ssprove_sync => r.
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
        eapply r_uniform_bij; [ apply (add_bij arg) |] => c1 /=.
        rewrite GRing.addrC. do 2 apply r_put_lhs.
        ssp_ret. intros H. by rewrite domm_set fset_cons H.
  Qed.

  Theorem CPA_PRFSKE A {VA : ValidPackage (loc A) (I_CPA PRFSKE) A_export A}
    : AdvOf (CPA PRFSKE) A <=
      AdvOf (PRF K N F) (A ∘ MOD_CPA ∘ (ID (I_PRF N) || Replaced N)) +
      AdvOf (Replacement N) (A ∘ MOD_CPA ∘ (PRF1 N || ID (I_SAMPLE N))).
  Proof.
    rewrite (Adv_perfect_l CPA_PRFSKE_1) -(Adv_perfect_r CPA_PRFSKE_2).
    rewrite Adv_reduction.
    ssprove_hop (PRF1 N || Replaced N).
    by rewrite Adv_par_l Adv_par_r -2!sep_link_assoc.
  Qed.
End PRFSKE.
