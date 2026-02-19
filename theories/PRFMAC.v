(* This file is based on the PRFMAC example given in SSProve.
  https://github.com/SSProve/ssprove/blob/main/theories/Crypt/examples/PRFMAC.v
 *)
(**
  This formalises Claim 10.4 from "The Joy of Cryptography" (p. 188).
  Most of it is fairly straight forward, the longest part being
  [TAG_GUESS_equiv_3].

  It would also be nice to formalise Claim 10.3 (p. 186), but its argument
  depends on the adversary only having polynomial time, and how to formulate
  that is unclear.

  The final statement ([security_based_on_prf]) is similar to that of PRF.v,
  stating that the advantage is bounded by a [prf_epsilon] and a
  [statistical_gap]. It would be particularly nice to simply state that it is
  negligible in [n].
*)

From NominalSSP Require Import Options Misc.

(**
  We can't use sets directly in [choice_type] so instead we use a map to units.
  We can then use [domm] to get the domain, which is a set.
*)
Definition chSet t := chMap t 'unit.

Notation " 'set t " := (chSet t) (in custom pack_type at level 2).
Notation " 'set t " := (chSet t) (at level 2): package_scope.

Definition tt := Datatypes.tt.

Section PRFMAC_example.

Variable (n: nat).

Definition Word_N: nat := 2^n.
Definition Word : choice_type := 'I_Word_N.

Notation " 'word " := (Word) (in custom pack_type at level 2).
Notation " 'word " := (Word) (at level 2): package_scope.

Definition k_loc: Location := mkloc 0 (None : 'option 'word).
Definition T_loc: Location := mkloc 1 (emptym : chMap 'word 'word).
Definition S_loc: Location := mkloc 2 (emptym : 'set ('word × 'word)).
Definition lookup: nat := 3.
Definition encrypt: nat := 4.
Definition gettag: nat := 5.
Definition checktag: nat := 6.
Definition guess: nat := 7.

Context (PRF: Word -> Word -> Word).

Definition EVAL_locs_tt := [fmap k_loc].
Definition EVAL_locs_ff := [fmap T_loc].

Definition kgen: raw_code 'word :=
  k_init ← get k_loc ;;
  match k_init with
  | None =>
      k <$ uniform Word_N ;;
      #put k_loc := Some k ;;
      ret k
  | Some k => ret k
  end.

Lemma kgen_valid {L I}:
  fhas L k_loc ->
  ValidCode L I kgen.
Proof.
  move=> H.
  apply: valid_getr => [// | [k|]].
  1: by apply: valid_ret.
  apply: valid_sampler => k.
  apply: valid_putr => //.
  by apply: valid_ret => //.
Qed.

Hint Extern 1 (ValidCode ?L ?I kgen) =>
  eapply kgen_valid ; fmap_solve
  : typeclass_instances ssprove_valid_db.

Definition EVAL_pkg_tt:
  game [interface #val #[lookup]: 'word → 'word ] :=
  [package EVAL_locs_tt ;
    #def #[lookup] (m: 'word): 'word {
      k ← kgen ;;
      ret (PRF k m)
    }
  ].

Definition EVAL_pkg_ff:
  game [interface #val #[lookup]: 'word → 'word ] :=
  [package EVAL_locs_ff ;
    #def #[lookup] (m: 'word): 'word {
      T ← get T_loc ;;
      match getm T m with
      | None =>
          r <$ uniform Word_N ;;
          #put T_loc := setm T m r ;;
          ret r
      | Some r => ret r
      end
    }
  ].

Definition EVAL b := if b then EVAL_pkg_tt else EVAL_pkg_ff.


Definition GUESS_locs := [fmap T_loc].

Definition GUESS_pkg_tt:
  game [interface
      #val #[lookup]: 'word → 'word ;
      #val #[guess]: 'word × 'word → 'bool
  ] :=
  [package GUESS_locs ;
    #def #[lookup] (m: 'word): 'word {
      T ← get T_loc ;;
      match getm T m with
      | None =>
          t <$ uniform Word_N ;;
          #put T_loc := setm T m t ;;
          ret t
      | Some t => ret t
      end
    } ;
    #def #[guess] ('(m, t): 'word × 'word): 'bool {
      T ← get T_loc ;;
      r ← match getm T m with
      | None =>
          r <$ uniform Word_N ;;
          #put T_loc := setm T m r ;;
          ret r
      | Some r => ret r
      end ;;
      ret (t == r)%B 
    }
  ].


Definition GUESS_pkg_ff:
  game [interface
    #val #[lookup]: 'word → 'word ;
    #val #[guess]: 'word × 'word → 'bool
  ] :=
  [package GUESS_locs ;
    #def #[lookup] (m: 'word): 'word {
      T ← get T_loc ;;
      match getm T m with
      | None =>
          t <$ uniform Word_N ;;
          #put T_loc := setm T m t ;;
          ret t
      | Some t => ret t
      end
    } ;
    #def #[guess] ('(m, t): 'word × 'word): 'bool {
      T ← get T_loc ;;
      ret (Some t == getm T m)%B
    }
  ].


Definition GUESS b := if b then GUESS_pkg_tt else GUESS_pkg_ff.

Definition TAG_locs_tt := [fmap k_loc].
Definition TAG_locs_ff := [fmap k_loc; S_loc].

Definition TAG_pkg_tt:
  game [interface
      #val #[gettag]: 'word → 'word ;
      #val #[checktag]: 'word × 'word → 'bool
  ] :=
  [package TAG_locs_tt ;
    #def #[gettag] (m: 'word): 'word {
      k ← kgen ;;
      ret (PRF k m)
    } ;
    #def #[checktag] ('(m, t): 'word × 'word): 'bool {
      k ← kgen ;;
      ret (t == PRF k m)%B
    }
  ].

Definition TAG_pkg_ff:
  game [interface
    #val #[gettag]: 'word → 'word ;
    #val #[checktag]: 'word × 'word → 'bool
  ] :=
  [package TAG_locs_ff ;
    #def #[gettag] (m: 'word): 'word {
      S ← get S_loc ;;
      k ← kgen ;;
      let t := PRF k m in
      #put S_loc := setm S (m, t) tt ;;
      ret t
    } ;
    #def #[checktag] ('(m, t): 'word × 'word): 'bool {
      S ← get S_loc ;;
      ret ((m, t) \in domm S)
    }
  ].

Definition TAG b := if b then TAG_pkg_tt else TAG_pkg_ff.

Definition TAG_EVAL_locs_ff := [fmap S_loc].

Definition TAG_EVAL_pkg_tt:
  package [interface #val #[lookup]: 'word → 'word ] [interface
      #val #[gettag]: 'word → 'word ;
      #val #[checktag]: 'word × 'word → 'bool
  ] :=
  [package emptym ;
    #def #[gettag] (m: 'word): 'word {
      #import {sig #[lookup]: 'word → 'word } as lookup ;;
      t ← lookup m ;;
      ret t
    } ;
    #def #[checktag] ('(m, t): 'word × 'word): 'bool {
      #import {sig #[lookup]: 'word → 'word } as lookup ;;
      r ← lookup m ;;
      ret (t == r)%B
    }
  ].

Definition TAG_EVAL_pkg_ff:
  package [interface #val #[lookup]: 'word → 'word] [interface
      #val #[gettag]: 'word → 'word ;
      #val #[checktag]: 'word × 'word → 'bool
  ] :=
  [package TAG_EVAL_locs_ff ;
    #def #[gettag] (m: 'word): 'word {
      #import {sig #[lookup]: 'word → 'word } as lookup ;;
      S ← get S_loc ;;
      t ← lookup m ;;
      #put S_loc := setm S (m, t) tt ;;
      ret t
    } ;
    #def #[checktag] ('(m, t): 'word × 'word): 'bool {
      S ← get S_loc ;;
      ret ((m, t) \in domm S)
    }
  ].

Definition TAG_GUESS_locs := [fmap S_loc ].

Definition TAG_GUESS_pkg:
  package
    [interface
      #val #[lookup]: 'word → 'word ;
      #val #[guess]: 'word × 'word → 'bool ]
    [interface
      #val #[gettag]: 'word → 'word ;
      #val #[checktag]: 'word × 'word → 'bool ] :=
  [package TAG_GUESS_locs ;
    #def #[gettag] (m: 'word): 'word {
      #import {sig #[lookup]: 'word → 'word } as lookup ;;
      S ← get S_loc ;;
      t ← lookup m ;;
      #put S_loc := setm S (m, t) tt ;;
      ret t
    } ;
    #def #[checktag] ('(m, t): 'word × 'word): 'bool {
      #import {sig #[guess]: 'word × 'word → 'bool } as guess ;;
      r ← guess (m, t) ;;
      ret r
    }
  ].

Lemma TAG_equiv_true:
  perfect
    [interface #val #[gettag] : 'word → 'word ;
               #val #[checktag] : ('word) × ('word) → 'bool ]
    (TAG true) (TAG_EVAL_pkg_tt ∘ (EVAL true)). 
Proof.
  ssp_prhl_eq.
  all: apply rpost_weaken_rule with eq;
    last by move=> [? ?] [? ?] [].
  2: case: arg => [m t].
  all: simplify_linking.
  all: simplify_linking.
  all: ssprove_sync_eq.
  all: case => [k|].
  all: by apply: rreflexivity_rule.
Qed.

Lemma TAG_EVAL_equiv_true:
  perfect
    [interface #val #[gettag] : 'word → 'word ;
               #val #[checktag] : ('word) × ('word) → 'bool ]
    (TAG_EVAL_pkg_tt ∘ EVAL false)(TAG_GUESS_pkg ∘ GUESS true).
Proof.
  ssp_prhl (heap_ignore [fmap S_loc]).
  2: case: arg => [m t].
  all: simplify_linking.
  all: simplify_linking.
  all: ssprove_code_simpl.
  all: ssprove_code_simpl_more.
  2: {
    apply: (@r_reflexivity_alt _ ([fmap T_loc])).
    all: by ssprove_invariant.
  }
  1: apply: r_get_remember_rhs => S.
  ssprove_sync=> T.
  case (getm T _) => [t|].
  2: ssprove_sync=> t.
  2: ssprove_sync.
  all: apply: r_put_rhs.
  all: ssp_ret.
Qed.

(**
  The first function ([gettag]) is exactly the same in both packages.
  It turns out, however, to be pretty complicated since we need to prove the
  invariant holds.
*)
Lemma TAG_EVAL_equiv_false:
  perfect
    [interface #val #[gettag] : 'word → 'word ;
               #val #[checktag] : ('word) × ('word) → 'bool ]
    (TAG_GUESS_pkg ∘ GUESS false) (TAG_EVAL_pkg_ff ∘ EVAL false).
Proof.
  ssp_prhl (
    heap_ignore emptym ⋊
    couple_rhs T_loc S_loc
      (fun T S => forall m t,
        ((m, t) \in domm S) = (Some t == getm T m)%B)
  ).
  1: move=> /= m t; by rewrite domm0 in_fset0 emptymE.
  1: move: arg => m.
  2: case: arg => [m t].
  all: simplify_linking.
  all: simplify_linking.
  - apply: r_get_vs_get_remember => S.
    apply: r_get_vs_get_remember => T.
    destruct (getm T m) as [t|] eqn:Heqt.
    all: rewrite Heqt /=.
    + apply: r_put_vs_put.
      ssp_ret => H1 m' t'.
      rewrite domm_set in_fsetU in_fset1 H1.
      destruct ((m', t') == (m, t))%B eqn:E; rewrite E //=.
      move: E => /eqP E. apply pair_equal_spec in E as [E1 E2].
      subst. by rewrite Heqt /= eq_refl.
    + ssprove_sync=> k.
      ssprove_rem_rel 0%N => Hinv.
      apply: r_put_vs_put.
      apply: r_put_vs_put.
      ssp_ret => Hinv' m' k'.
      rewrite domm_set in_fsetU in_fset1 setmE.
      destruct ((m', k') == (m, k))%B eqn:E; rewrite E //=.
      * move: E => /eqP E.
        apply pair_equal_spec in E as [E1 E2].
        subst. by rewrite eq_refl /= eq_refl.
      * rewrite xpair_eqE in E.
        destruct (m' == m)%B eqn:Em; rewrite Em //=.
        rewrite -(inj_eq Some_inj) /= in E.
        move=> /eqP in Em.
        by rewrite E Hinv Em Heqt.
  - ssprove_code_simpl.
    ssprove_code_simpl_more.
    apply: r_get_remember_lhs => T.
    apply: r_get_remember_rhs => S.
    ssprove_rem_rel 0%N => ->.
    ssp_ret.
Qed.

Lemma TAG_equiv_false:
  perfect
    [interface #val #[gettag] : 'word → 'word ;
               #val #[checktag] : ('word) × ('word) → 'bool ]
    (TAG_EVAL_pkg_ff ∘ EVAL true) (TAG false).
Proof.
  ssp_prhl_eq.
  all: apply rpost_weaken_rule with eq;
    last by move=> [? ?] [? ?] [].
  2: case: arg => [m t].
  all: simplify_linking.
  all: ssprove_sync_eq=> S.
  1: ssprove_sync_eq.
  1: case => [k|].
  all: by apply: rreflexivity_rule.
Qed.

Local Open Scope ring_scope.

(**
  The advantage an adversary can gain over the PRF, i.e. the chance by
  which an adversary can distinguish the PRF from a truly random function.
  Negligible by assumption.
*)
Definition prf_epsilon A := AdvOf EVAL A.

(**
  The advantage an adversary can gain in the [GUESS] game.
  This is negligible, but not yet provable in SSProve.
*)
Definition statistical_gap := Adv
  (TAG_GUESS_pkg ∘ (GUESS true))
  (TAG_GUESS_pkg ∘ (GUESS false)).


Theorem security_based_on_prf :
  forall (A : adversary [interface
    #val #[gettag]: 'word → 'word ;
    #val #[checktag]: 'word × 'word → 'bool
  ]),
  AdvOf TAG A <=
  prf_epsilon (A ∘ TAG_EVAL_pkg_tt) +
  statistical_gap A +
  prf_epsilon (A ∘ TAG_EVAL_pkg_ff).
Proof.
  intros A. simpl.
  unfold prf_epsilon, statistical_gap.
  erewrite <- (Adv_perfect_r TAG_equiv_false).
  ssprove_hop (TAG_EVAL_pkg_ff ∘ EVAL false).
  apply lerD; [| by rewrite Adv_reduction Adv_sym ].
  erewrite <- (Adv_perfect_r TAG_EVAL_equiv_false).
  ssprove_hop (TAG_GUESS_pkg ∘ GUESS true).
  apply lerD; [| by rewrite Adv_reduction Adv_sym ].
  erewrite (Adv_perfect_l TAG_equiv_true).
  erewrite <- (Adv_perfect_r TAG_EVAL_equiv_true).
  by rewrite Adv_reduction.
Qed.

End PRFMAC_example.
