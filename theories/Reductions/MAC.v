From NominalSSP Require Import Options Misc PRF Replacement.
(* Modelling PRF based MACs *)

Section MAC.
  Context (K N : nat).
  Context (F : K.-bits → N.-bits → N.-bits).

  Definition INIT := 30%N.
  Definition GUESS := 31%N.
  Definition REVEAL := 32%N.

  Definition I_MAC := [interface
    [ INIT ] : { unit ~> unit } ;
    [ GUESS ] : { N.-bits × N.-bits ~> bool } ;
    [ REVEAL ] : { N.-bits ~> N.-bits } ].

  Definition MAC0 : game I_MAC :=
    [package [fmap key_loc K];
      [ INIT ] (_) {
        getNone key_loc K ;;
        k ← sample uniform_bits K ;;
        #put key_loc K := Some k ;;
        ret tt
      } ;
      [ GUESS ] '(x, y) {
        k ← getSome key_loc K ;;
        ret (y == F k x)%B
      } ;
      [ REVEAL ] (x) {
        k ← getSome key_loc K ;;
        ret (F k x)
      }
    ].

  Definition MAC1 : game I_MAC :=
    [package [fmap lazy_map_loc N];
      [ INIT ] (_) {
        getNone lazy_map_loc N ;;
        #put lazy_map_loc N := Some emptym ;;
        ret tt
      } ;
      [ GUESS ] '(x, y) {
        L ← getSome lazy_map_loc N ;;
        ret (Some y == L x)%B
      } ;
      [ REVEAL ] (x) {
        L ← getSome lazy_map_loc N ;;
        if L x is Some y then
          ret y
        else
          y ← sample uniform_bits N ;;
          #put lazy_map_loc N := Some (setm L x y) ;;
          ret y
      }
    ].

  Definition MAC b := if b then MAC0 else MAC1.

  Definition R_PRF : package (I_PRF N) I_MAC :=
    [package emptym;
      [ INIT ] (_) {
        _ ← call [ PRF.INIT ] tt ;;
        ret tt
      } ;
      [ GUESS ] '(x, y) {
        y' ← call [ QUERY ] x ;;
        ret (y == y')%B
      } ;
      [ REVEAL ] (x) {
        y ← call [ QUERY ] x ;;
        ret y
      }
    ].

  Ltac ssp_refl := 
    ssp_simpl; eapply rpost_weaken_rule;
      [ apply rreflexivity_rule
      | move=> [? ?] [? ?]; apply pair_equal_spec ].

  Lemma MAC0_R_MAC1 : perfect I_MAC MAC0 (R_PRF ∘ PRF0 K N F).
  Proof.
    ssp_prhl_eq.
    2: destruct arg as [x y].
    1-3: ssp_refl.
  Qed.

  Definition I_GUESS_MANY := [interface
    [ GUESS ] : { N.-bits × N.-bits ~> 'bool } ;
    [ REVEAL ] : { N.-bits ~> N.-bits } ].

  Definition guess_map_loc := mkloc 31%N (emptym : {fmap N.-bits → N.-bits}).

  Definition GuessMany0 : game I_GUESS_MANY :=
    [package [fmap guess_map_loc] ;
      [ GUESS ] '(x, y) {
        L ← get guess_map_loc ;;
        if L x is Some y' then
          ret (y == y')%B
        else
          y' ← sample uniform_bits N ;;
          #put guess_map_loc := setm L x y' ;;
          ret (y == y')%B
      } ;
      [ REVEAL ] (x) {
        L ← get guess_map_loc ;;
        if L x is Some y' then
          #put guess_map_loc := remm L x ;;
          ret y'
        else
          y' ← sample uniform_bits N ;;
          ret y'
      }
    ].

  Definition GuessMany1 : game I_GUESS_MANY :=
    [package emptym ;
      [ GUESS ] (x) {
        ret false
      } ;
      [ REVEAL ] (x) {
        r ← sample uniform_bits N ;;
        ret r
      }
    ].

  Definition GuessMany b := if b then GuessMany0 else GuessMany1.

  Definition R_Guess : package I_GUESS_MANY I_MAC :=
    [package [fmap lazy_map_loc N];
      [ INIT ] (_) {
        getNone lazy_map_loc N ;;
        #put lazy_map_loc N := Some emptym ;;
        ret tt
      } ;
      [ GUESS ] '(x, y) {
        L ← getSome lazy_map_loc N ;;
        if L x is Some y' then
          ret (y == y')%B
        else
          b ← call [ GUESS ] (x, y) ;;
          ret b
      } ;
      [ REVEAL ] (x) {
        L ← getSome lazy_map_loc N ;;
        if L x is Some y then
          ret y
        else
          y ← call [ REVEAL ] x ;;
          #put lazy_map_loc N := Some (setm L x y) ;;
          ret y
      }
    ].

  Lemma R_PRF_Guess : perfect I_MAC (R_PRF ∘ PRF1 N) (R_Guess ∘ GuessMany0).
  Proof.
    ssp_prhl (heap_ignore [fmap lazy_map_loc N; guess_map_loc] ⋊
      couple_cross (lazy_map_loc N) (lazy_map_loc N)
        (λ L L', sameSome L' L ∧ fsubmap (odflt emptym L') (odflt emptym L)) ⋊
      rel_app [:: (lhs, lazy_map_loc N); (rhs, lazy_map_loc N);
        (rhs, guess_map_loc) ] (λ L L' G, odflt emptym L = unionm (odflt emptym L') G)).
    - ssp_simpl.
      apply r_get_remember_lhs => L.
      apply r_get_remember_rhs => L'.
      ssprove_rem_rel 1%N => [[/eqP H _]].
      destruct L, L' => //=; [ apply: r_sample_null |].
      apply r_matchNone => _.
      apply r_put_vs_put. ssp_ret.
    - destruct arg as [x y].
      ssp_simpl.
      apply r_get_remember_lhs => L.
      apply r_get_remember_rhs => L'.
      ssprove_rem_rel 1%N => [[/eqP H' H]].
      destruct L as [L|], L' as [L'|] => //=; [| apply: r_sample_null ].
      apply: r_matchSome_lhs. apply: r_matchSome_rhs.
      destruct (L' x) eqn:E'; rewrite E'.
      + rewrite -fhas_fsubmap in H.
        specialize (H (x, s)).
        rewrite H //.
        ssp_ret.
      + apply r_get_remember_rhs => G.
        ssprove_rem_rel 0%N => /=.
        destruct (L x) eqn:E => {}H; rewrite E.
        * rewrite H unionmE E' /= in E.
          rewrite E. ssp_ret.
        * rewrite H unionmE E' /= in E.
          rewrite E /=.
          ssprove_sync => r.
          apply r_put_vs_put.
          ssp_ret.
          -- move=> [_ {}H']. split => //.
             apply (fsubmap_trans _ _ _ H').
             apply fhas_fsubmap => [[k v]].
             rewrite /fhas setmE => H''.
             destruct (k == x)%B eqn:E'' => //.
             move=> /eqP in E''; subst.
             rewrite unionmE E' E // in H''.
          -- move=> /= ->. subst. apply eq_fmap => i.
             rewrite setmE 2!unionmE setmE.
             destruct (i == x)%B eqn:E'' => //.
             move=> /eqP in E''; subst. by rewrite E'.
    - ssp_simpl. move: arg => x.
      apply r_get_remember_lhs => L.
      apply r_get_remember_rhs => L'.
      ssprove_rem_rel 1%N => [[/eqP H' H]].
      destruct L as [L|], L' as [L'|] => //=; [| apply: r_sample_null ].
      apply: r_matchSome_lhs. apply: r_matchSome_rhs.
      destruct (L' x) eqn:E'; rewrite E'.
      + rewrite -fhas_fsubmap in H.
        specialize (H (x, s)).
        rewrite H //.
        ssp_ret.
      + apply r_get_remember_rhs => G.
        ssprove_rem_rel 0%N => /=.
        destruct (L x) eqn:E => {}H; rewrite E.
        * rewrite H unionmE E' /= in E.
          rewrite E.
          apply r_put_rhs, r_put_rhs.
          ssp_ret.
          -- subst => _. split => //.
             apply fhas_fsubmap => [[k v]] /= H.
             rewrite setmE in H.
             rewrite unionmE .
             destruct (k == x)%B eqn:E''.
             ++ move=> /eqP in E''. subst.
                by rewrite E' -H.
             ++ by rewrite H.
          -- move=> _. rewrite H. apply eq_fmap => i.
             rewrite 2!unionmE setmE remmE.
             destruct (i == x)%B eqn:E'' => //=.
             move=> /eqP in E''. subst. by rewrite E'.
        * rewrite H unionmE E' /= in E.
          rewrite E /=.
          ssprove_sync => r.
          apply r_put_vs_put.
          ssp_ret.
          -- move=> [_ {}H']. split => //.
             apply fhas_fsubmap => [[k v] H''] .
             rewrite /fhas 2!setmE in H'' |- *.
             rewrite -fhas_fsubmap in H'.
             destruct (k == x)%B => //.
             by apply (H' (k, v)).
          -- move=> /= ->. subst. apply eq_fmap => i.
             rewrite setmE 2!unionmE setmE.
             destruct (i == x)%B eqn:E'' => //.
  Qed.

  Lemma MAC1_R_Guess : perfect I_MAC (R_Guess ∘ GuessMany1) MAC1.
  Proof.
    ssp_prhl_eq.
    - ssp_simpl. ssp_refl.
    - destruct arg as [x y].
      ssp_simpl.
      ssprove_sync_eq => oL.
      apply r_matchSome => L {oL}_.
      destruct (L x) eqn:E; rewrite E; ssp_ret.
    - ssp_refl.
  Qed.

  Theorem Adv_MAC {A} `{ValidPackage A.(loc) I_MAC A_export A}
    : AdvOf MAC A <=
      AdvOf (PRF K N F) (A ∘ R_PRF) + AdvOf GuessMany (A ∘ R_Guess).
  Proof.
    rewrite (Adv_perfect_l MAC0_R_MAC1).
    rewrite -(Adv_perfect_r MAC1_R_Guess).
    ssprove_hop (R_Guess ∘ GuessMany0).
    rewrite -{1}(Adv_perfect_r R_PRF_Guess).
    by rewrite 2!Adv_reduction.
  Qed.
End MAC.
