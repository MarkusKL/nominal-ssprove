Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect all_algebra reals distr realsum
  fingroup.fingroup solvable.cyclic prime ssrnat ssreflect ssrfun ssrbool ssrnum
  eqtype choice seq.
Set Warnings "notation-overridden,ambiguous-paths".

From Coq Require Import Utf8.
From extructures Require Import ord fset fmap fperm.

From Equations Require Import Equations.
Require Equations.Prop.DepElim.

Set Equations With UIP.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".
Set Primitive Projections.

From NominalSSP Require Import Prelude.
Import Num.Def Num.Theory Order.POrderTheory.
Import PackageNotation.
#[local] Open Scope ring_scope.
#[local] Open Scope package_scope.

From NominalSSP Require Import Group Sigma.
From Mon Require Import SPropBase.
Set Equations Transparent.
Import GroupScope GRing.Theory.


Module SigmaOR (GP : GroupParam).

Module GT := GroupTheorems GP.
Import GP GT.


Definition challenge_loc p : Location := ('challenge p; 1%N).
Definition response_loc p : Location := ('response p; 2%N).

Definition Extra_locs_lr l r : {fset Location} :=
  fset [:: challenge_loc l ; response_loc l ; challenge_loc r ; response_loc r ].

#[export] Instance Positive_exp : Positive #|exp|.
Proof. apply /card_gt0P. by exists 0. Qed.

Record or_params :=
  { left : raw_sigma
  ; right : raw_sigma
  ; left_challenge : 'challenge left = 'fin #|exp|
  ; right_challenge : 'challenge right = 'fin #|exp|
  }.

Implicit Type (p : or_params).

Definition Extra_locs p : {fset Location} :=
  Extra_locs_lr p.(left) p.(right).

Definition pad p : 'fin #|exp| → 'challenge p.(left) → 'challenge p.(right).
Proof.
  rewrite p.(left_challenge) p.(right_challenge) => c c1.
  exact (fto (otf c1 + otf c)).
Defined.

Definition unpad p : 'fin #|exp| → 'challenge p.(right) → 'challenge p.(left).
Proof.
  rewrite p.(left_challenge) p.(right_challenge) => c c2.
  exact (fto (otf c2 - otf c)).
Defined.

Definition into {T S : choice_type} (H : S = T) : T → S.
Proof. rewrite H. exact id. Defined.

#[global] Hint Unfold Extra_locs Extra_locs_lr : in_fset_eq.

Definition l p : {fperm atom}
  := fresh (Extra_locs p) p.(left).(locs).
Definition r p : {fperm atom}
  := fresh (dpair (Extra_locs p) p.(left).(locs)) p.(right).(locs).

#[tactic=ssprove_valid]
Equations raw_or p : raw_sigma :=
  raw_or p :=
  {| Statement := 'statement p.(left) × 'statement p.(right)
   ; Witness := 'bool × ('witness p.(left) × 'witness p.(right))
   ; Message := 'message p.(left) × 'message p.(right)
   ; Challenge := 'fin #|exp|
   ; Response :=
       (('challenge p.(left) × 'response p.(left))
       × 'challenge p.(right)) × 'response p.(right)

   ; locs :=
        Extra_locs p
         :|: l p ∙ p.(left).(locs)
         :|: r p ∙ p.(right).(locs)

   ; R := λ '(h1, h2) '(wb, (w1, w2)),
       if wb then p.(left).(R) h1 w1 else p.(right).(R) h2 w2

   ; commit := λ '(h1, h2) '(wb, (w1, w2)),
      {code
        if wb then
          R1 ← l p ∙ p.(left).(commit) h1 w1 ;;
          c2 ← sample uniform #|exp| ;;
          let c2 := into p.(right_challenge) c2 in
          '(R2, s2) ← p.(right).(simulate) h2 c2 ;;
          #put challenge_loc p.(right) := c2 ;;
          #put response_loc p.(right) := s2 ;;
          ret (R1, R2)
        else
          R2 ← r p ∙ p.(right).(commit) h2 w2 ;;
          c1 ← sample uniform #|exp| ;;
          let c1 := into p.(left_challenge) c1 in
          '(R1, s1) ← p.(left).(simulate) h1 c1 ;;
          #put challenge_loc p.(left) := c1 ;;
          #put response_loc p.(left) := s1 ;;
          ret (R1, R2)
      }
   ; response := λ '(h1, h2) '(wb, (w1, w2)) '(a1, a2) c,
      {code
        if wb then
          c2 ← get challenge_loc p.(right) ;;
          s2 ← get response_loc p.(right) ;;
          let c1 := unpad p c c2 in
          s1 ← l p ∙ p.(left).(response) h1 w1 a1 c1 ;;
          ret (c1, s1, c2, s2)
        else
          c1 ← get challenge_loc p.(left) ;;
          s1 ← get response_loc p.(left) ;;
          let c2 := pad p c c1 in
          s2 ← r p ∙ p.(right).(response) h2 w2 a2 c2 ;;
          ret (c1, s1, c2, s2)
      }
   ; simulate := λ '(h1, h2) c,
     {code
       c1 ← sample uniform #|exp| ;;
       let c1 := into p.(left_challenge) c1 in
       let c2 := pad p c c1 in
       '(R1, s1) ← p.(left).(simulate) h1 c1 ;;
       '(R2, s2) ← p.(right).(simulate) h2 c2 ;;
       ret ((R1, R2), (c1, s1, c2, s2))
     }
   ; verify := λ '(h1, h2) '(R1, R2) c z,
      let '(c1, s1, c2, s2) := z in
      p.(left).(verify) h1 R1 c1 s1
      && p.(right).(verify) h2 R2 c2 s2
      && (pad p c c1 == c2)
   ; extractor := λ '(h1, h2) '(R1, R2) e e' z z',
      let '(c1, s1, c2, s2) := z in
      let '(c1', s1', c2', s2') := z' in
      if c1 != c1' then
        omap (λ w1 : 'witness p.(left), (true, (w1, @chCanonical p.(right).(Witness))))
          (p.(left).(extractor) h1 R1 c1 c1' s1 s1')
      else
        omap (λ w2 : 'witness p.(right), (false, (@chCanonical p.(left).(Witness), w2)))
          (p.(right).(extractor) h2 R2 c2 c2' s2 s2')
  |}.


Definition Aux n m S T :=
  (@Build_module
    (fset ((m, (S, T)) :: [::]))
    (fset ((n, (S, T)) :: [::]))
    fset0
    (mkpackage (mkfmap ( 
      (n, mkdef S T
        (λ x, opr (m, (S, T)) x (λ y, ret y))
      )
    :: [::])) _)
    (trimmed_package_cons _ _ _ _ _ _ trimmed_empty_package)
  ).

Definition LEFT := 0%N.
Definition RIGHT := 1%N.

Definition AuxL p :=
  (Aux LEFT TRANSCRIPT
    (chInput p.(left))
    (chTranscript p.(left) )
  ).

Definition AuxR p :=
  (Aux RIGHT TRANSCRIPT
    (chInput p.(right))
    (chTranscript p.(right))
  ).

#[tactic=ssprove_valid] Equations SHVZK_call p :
  module
    [interface
       #val #[ LEFT ] : ('input p.(left)) → 'transcript p.(left) ;
       #val #[ RIGHT ] : ('input p.(right)) → 'transcript p.(right)
    ]
    [interface #val #[ TRANSCRIPT ] : ('input (raw_or p)) → 'transcript (raw_or p)] :=
  SHVZK_call p := [module no_locs ;
    #def #[ TRANSCRIPT ] (hwe : 'input (raw_or p)) : ('transcript (raw_or p)) {
      #import {sig #[ LEFT ] :
        ('input p.(left)) → 'transcript p.(left)} as LeftTranscript ;;
      #import {sig #[ RIGHT ] :
        ('input p.(right)) → 'transcript p.(right)} as RightTranscript ;;

      let '(h, w, c) := hwe in
      let '(h1, h2) := h in
      let '(wb, (w1, w2)) := w in
      c1 ← sample uniform #|exp| ;;
      let c1 := into p.(left_challenge) c1 in
      let c2 := pad p c c1 in
      if wb then
        '(_, R1, _, s1) ← LeftTranscript (h1, w1, c1) ;;
        '(R2, s2) ← p.(right).(simulate) h2 c2 ;;
        ret ((h1, h2), (R1, R2), c, (c1, s1, c2, s2))
      else
        '(R1, s1) ← p.(left).(simulate) h1 c1 ;;
        '(_, R2, _, s2) ← RightTranscript (h2, w2, c2) ;;
        ret ((h1, h2), (R1, R2), c, (c1, s1, c2, s2))
    }
  ].

Definition CALL p (L R : raw_module) : raw_module :=
  ( (SHVZK_call p) ∘ ( (AuxL p ∘ (l p ∙ L)) || (AuxR p ∘ (r p ∙ R))) )%share.

#[local] Instance call_valid p :
  ∀ (L R : raw_module),
    ValidPackage L.(loc) [interface] (Transcript p.(left)) L →
    ValidPackage R.(loc) [interface] (Transcript p.(right)) R →
    ValidPackage (CALL p L R).(loc) [interface] (Transcript (raw_or p))
      (CALL p L R).
Proof. move => L R VL VR. unfold CALL. nssprove_valid. Qed.

Lemma destruct_let_pair : ∀ A B C (xy : A * B) (f : A → B → C), (let (x, y) := xy in f x y) = f xy.1 xy.2.
Proof.
  intros A B C xy f.
  destruct xy.
  by simpl.
Qed.

Definition call_real_real p
  := CALL p (SHVZK_real p.(left)) (SHVZK_real p.(right)).
Definition call_ideal_real p
  := CALL p (SHVZK_ideal p.(left)) (SHVZK_real p.(right)).
Definition call_ideal_ideal p
  := CALL p (SHVZK_ideal p.(left)) (SHVZK_ideal p.(right)).

Lemma invariant_ignore_extra p :
  Invariant (SHVZK_real (raw_or p)).(loc)
    (call_real_real p).(loc)
    (heap_ignore (Extra_locs p)).
Proof.
  ssprove_invariant.
  simpl.
  fset_solve.
Qed.


Definition iso p (c : 'fin #|exp|) : Arit (uniform #|exp|) → Arit (uniform #|exp|)
  := λ c2, fto (otf c2 - otf c).

Lemma into_iso p c c2
  : into p.(left_challenge) (iso p c c2) = unpad p c (into p.(right_challenge) c2).
Proof.
  unfold into, unpad, iso, eq_rect_r.
  move: (Logic.eq_sym p.(left_challenge)) (Logic.eq_sym p.(right_challenge)).
  rewrite p.(left_challenge) p.(right_challenge) => H1 H2.
  rewrite -4!Eqdep.EqdepTheory.eq_rect_eq //.
Qed.

Lemma pad_unpad p c c2 : pad p c (unpad p c c2) = c2.
Proof.
  unfold pad, unpad, eq_rect_r.
  move: c2 (Logic.eq_sym p.(left_challenge)) (Logic.eq_sym p.(right_challenge)).
  rewrite p.(left_challenge) p.(right_challenge) => c2 H1 H2.
  rewrite -4!Eqdep.EqdepTheory.eq_rect_eq.
  rewrite otf_fto addrNK fto_otf //.
Qed.

Lemma iso_bij p c : bijective (iso p c).
Proof.
  unfold iso.
  exists (λ c1, fto (otf c1 + otf c)) => [c2|c1].
  + rewrite otf_fto addrNK fto_otf //.
  + rewrite otf_fto addrK fto_otf //.
Qed.


Lemma d_left p : disj (l p ∙ p.(left).(locs)) (Extra_locs p).
Proof.  unfold l.  auto with alpha_db nocore.  Qed.

Lemma d_right p : disj (r p ∙ p.(right).(locs)) (Extra_locs p).
Proof.  unfold r, dpair.  auto with alpha_db nocore.  Qed.

Lemma commit_call p :
    SHVZK_real (raw_or p) ≈₀ call_real_real p.
Proof.
  eapply eq_rel_perf_ind.
  1: apply invariant_ignore_extra.
  simplify_eq_rel hwe.
  destruct hwe as [[[h1 h2] [[] [w1 w2]]] c].
  1,2: simpl; ssprove_code_simpl.
  1,2: simplify_linking.
  1,2: ssprove_code_simpl; simpl.
  1,2: rewrite !cast_fun_K.
  1,2: ssprove_code_simpl; simpl.
  + ssprove_swap_lhs 1%N.
    ssprove_swap_lhs 0%N.
    eapply r_uniform_bij with (1 := iso_bij p c) => c2.

    ssprove_code_simpl.

    rewrite into_iso pad_unpad.
    move: (into p.(right_challenge) c2) => {}c2.
    ssprove_code_simpl_more.
    ssprove_sync => H.
    ssprove_code_simpl; simpl.
    rewrite rename_code. 
    apply rsame_head_ignore_prog.
    1: apply supp_fdisjoint, d_left.
    move => a.
    ssprove_code_simpl; simpl.
    eapply rel_jdg_replace_sem_r; simpl.
    2: eapply swap_code; ssprove_valid; eapply fdisjoint0s.
    apply rsame_head_ignore_prog; [ fset_solve |].
    intros [R1 s1].
    ssprove_swap_lhs 1%N.
    ssprove_contract_put_get_lhs.
    apply r_put_lhs.
    ssprove_contract_put_get_lhs.
    apply r_put_lhs.
    ssprove_restore_pre; [ ssprove_invariant |].
    rewrite rename_code.
    apply rsame_head_ignore_prog.
    1: apply supp_fdisjoint, d_left.
    move=> s2.
    by apply r_ret.
  + ssprove_swap_lhs 1%N.
    ssprove_swap_lhs 0%N.
    ssprove_sync => c1.
    eapply rel_jdg_replace_sem_r; simpl.
    2: {
      eapply rsame_head => x.
      rewrite destruct_let_pair.
      eapply rreflexivity_rule.
    }
    ssprove_code_simpl.
    eapply rel_jdg_replace_sem_r; simpl.
    2: eapply swap_code; ssprove_valid.
    3: rewrite rename_bind; ssprove_valid; apply valid_ret.
    2: apply fdisjoints0.
    ssprove_code_simpl_more.
    ssprove_code_simpl; simpl.
    ssprove_sync => H.
    rewrite rename_code.
    apply rsame_head_ignore_prog.
    1: apply supp_fdisjoint, d_right.
    move => vr. 

    eapply rel_jdg_replace_sem_r; simpl.
    2: eapply swap_code; ssprove_valid;
      [ apply fdisjoint0s | apply valid_ret ].

    apply rsame_head_ignore_prog; [ fset_solve |].
    intros [R1 z1].
    ssprove_swap_lhs 1%N.
    ssprove_contract_put_get_lhs.
    apply r_put_lhs.
    ssprove_contract_put_get_lhs.
    apply r_put_lhs.
    ssprove_restore_pre; [ ssprove_invariant |].
    ssprove_code_simpl.
    rewrite rename_code.
    apply rsame_head_ignore_prog.
    1: apply supp_fdisjoint, d_right.
    intros s2.
    by apply r_ret.
Qed.


Lemma simulate_call p :
  call_ideal_ideal p ≈₀ SHVZK_ideal (raw_or p).
Proof.
  apply eq_rel_perf_ind_eq.
  simplify_eq_rel hwe.
  destruct hwe as [[[h1 h2] [[] [w1 w2]]] c].
  1,2: ssprove_code_simpl; simpl.
  1,2: simplify_linking.
  1,2: ssprove_code_simpl; simpl.
  1,2: rewrite !cast_fun_K.
  1,2: ssprove_code_simpl; simpl.
  1,2: ssprove_swap_rhs 0%N; ssprove_sync_eq => cl.
  + ssprove_code_simpl_more.
    ssprove_sync => P.
    ssprove_code_simpl.
    ssprove_code_simpl.
    rewrite rename_scheme.
    eapply rsame_head => t1.
    move: t1 => [l1 l2].
    simpl.
    eapply rsame_head => t2.
    move: t2 => [r1 r2].
    by eapply r_ret.

  + eapply rel_jdg_replace_sem_l.
    2: eapply rel_jdg_replace_r.
    3: setoid_rewrite destruct_let_pair; reflexivity.
    2: eapply swap_code.
    3,4: ssprove_valid.
    3: rewrite rename_bind rename_scheme; ssprove_valid.
    3: destruct x0; apply valid_ret.
    2: instantiate (1 := fset0); apply fdisjoint0s.
    ssprove_code_simpl_more.
    ssprove_sync => H.
    ssprove_code_simpl; simpl.
    move: (into p.(left_challenge) cl) => {}cl.

    ssprove_code_simpl; simpl.
    rewrite rename_scheme.
    eapply rel_jdg_replace_sem_l.
    2: ssprove_code_simpl.
    2: eapply rel_jdg_replace_r.
    3: setoid_rewrite destruct_let_pair; reflexivity.
    2: eapply swap_code.
    3,4: ssprove_valid; apply prog_valid.
    2: instantiate (1 := fset0); apply fdisjoint0s.

    eapply rsame_head => t1.
    move: t1 => [l1 l2].
    eapply rsame_head => t2.
    move: t2 => [r1 r2].
    by eapply r_ret.
Qed.


Local Obligation Tactic := notac.

Program Definition A_left p (A : adversary (Transcript (raw_or p)))
  : adversary (Transcript (left p)) :=
  {adversary _ ; ((A ∘ SHVZK_call p) ∘ (AuxL p || (AuxR p ∘ SHVZK_real (right p)))) }.
Obligation 1.
  intros p A. nssprove_valid.
Qed.

Program Definition A_right p (A : adversary (Transcript (raw_or p)))
  : adversary (Transcript (right p)) :=
  {adversary _ ; ((A ∘ SHVZK_call p) ∘ ((AuxL p ∘ SHVZK_ideal (left p)) || AuxR p)) }.
Obligation 1.
  intros p A. nssprove_valid.
Qed.


Lemma d_left_right p : disj (l p ∙ p.(left).(locs)) (r p ∙ p.(right).(locs)).
Proof.  unfold l, r, dpair.  auto with alpha_db nocore.  Qed.


Theorem OR_SHVZK p :
  ∀ ε₁ ε₂ : raw_module → Axioms.R,
    Adv_SHVZK p.(left) ε₁ →
    Adv_SHVZK p.(right) ε₂ →
    Adv_SHVZK (raw_or p) (λ A, ε₁ (A_left p A) + ε₂ (A_right p A)).
Proof.
  intros ε₀ ε₁ AdvL AdvR A.
  unfold AdvFor, SHVZK.
  erewrite (Adv_perf_l (commit_call p)).
  erewrite <- (Adv_perf_r (simulate_call p)).

  unfold call_real_real, call_ideal_ideal, CALL.
  move: (d_left_right p) => H; nssprove_separate.

  nssprove_adv_trans (call_ideal_real p).

  apply lerD.
  1,2: unfold call_ideal_real, CALL.
  + move: (d_left p) => {}H; nssprove_separate.
    rewrite Adv_sep_link.
    erewrite @sep_par_game_l, @sep_par_game_l; try nssprove_valid.
    rewrite Adv_sep_link.
    apply (AdvL (A_left p A)).

  + move: (d_right p) => {}H; nssprove_separate.
    rewrite Adv_sep_link.
    erewrite @sep_par_game_r, @sep_par_game_r; try nssprove_valid.
    rewrite Adv_sep_link.
    apply (AdvR (A_right p A)).
Qed.

End SigmaOR.
