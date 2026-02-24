From NominalSSP Require Import Options.

Notation dist := (code emptym [interface]).

(*
#[export] Hint Extern 9 (ValidCode ?L ?I ?c.(prog)) =>
  eapply valid_scheme ; eapply c.(prog_valid)
  : typeclass_instances ssprove_valid_db.  *)

Ltac ssp_prhl inv :=
  ssprove_share; eapply prove_perfect;
  eapply (eq_rel_perf_ind _ _ inv);
  [ ssprove_invariant; try done
  | let arg := fresh "arg" in simplify_eq_rel arg
  ].

Ltac ssp_prhl_eq :=
  ssprove_share; eapply prove_perfect;
  eapply eq_rel_perf_ind_eq;
  let arg := fresh "arg" in simplify_eq_rel arg.

Ltac ssprove_restore_pre ::=
  update_pre_fold ;
  eapply r_restore_pre.

Ltac ssprove_restore_mem ::=
  update_pre_fold ;
  remember_pre_fold ;
  eapply r_restore_mem.

Ltac ssp_restore :=
  (ssprove_restore_mem; [ ssprove_invariant; try done |]) ||
  (ssprove_restore_pre; [ ssprove_invariant; try done |]) ||
  ssprove_forget_all.

Ltac ssp_ret := ssp_restore; [ .. | apply r_ret; try done ].


Notation uniformZ n := (uniform (Zp_trunc n).+2).

Notation "n .-bits" := ('I_(2 ^ n)).
Notation uniform_bits n := (uniform (2 ^ n)).

Section Bits.

#[local] Obligation Tactic := idtac.

Program Definition lower {n m} : 'I_(n * m) → 'I_n
  := λ x, @Ordinal _ (x %% n)%N _.
Obligation 1.
  move=> [|n] m x.
  - exfalso. rewrite mul0n in x. by destruct x.
  - by apply ltn_pmod.
Qed.

Program Definition upper {n m} : 'I_(n * m) → 'I_m
  := λ x, @Ordinal _ (x %/ n)%N _.
Obligation 1.
  move=> [|n] m x.
  - exfalso. rewrite mul0n in x. by destruct x.
  - by rewrite ltn_divLR // (mulnC m).
Qed.

Program Definition stitch {n m} : 'I_n → 'I_m → 'I_(n * m)
  := λ x y, @Ordinal _ (x + y * n) _.
Obligation 1.
  move=> [|n] m x y; [ by destruct x |].
  rewrite (mulnC n.+1 m) -ltn_divLR // divnDMl //.
  rewrite divn_small // add0n //.
Qed.

Definition stitchK {n m} (x : 'I_(n * m)) : stitch (lower x) (upper x) = x.
Proof. apply ord_inj => /=. by rewrite addnC -divn_eq. Qed.

Definition lowerK {n m} (x : 'I_n) (y : 'I_m) : lower (stitch x y) = x.
Proof.
  apply ord_inj => /=.
  rewrite -modnDm modnMl addn0.
  destruct n; [ by destruct x |]; by rewrite 2!modZp.
Qed.

Definition upperK {n m} (x : 'I_n) (y : 'I_m) : upper (stitch x y) = y.
Proof.
  apply ord_inj => /=.
  destruct n; [ by destruct x |].
  rewrite divnDMl // divn_small //.
Qed.


Definition nilb : 0.-bits := ord0.

Definition headb {n} : n.+1.-bits → 'Z_2 :=
  λ x, lower (cast_ord (expnS _ _) x).

Definition tailb {n} : n.+1.-bits → n.-bits :=
  λ x, upper (cast_ord (expnS _ _) x).

Definition consb {n} : 'Z_2 → n.-bits → n.+1.-bits :=
  λ h t, cast_ord (esym (expnS _ _)) (stitch h t).

Lemma consbK {n} (x : n.+1.-bits) : consb (headb x) (tailb x) = x.
Proof. by rewrite /consb /headb /tailb stitchK cast_ordK. Qed.

Lemma headbK {n} b (x : n.-bits) : headb (consb b x) = b.
Proof. by rewrite /consb /headb cast_ordKV lowerK. Qed.

Lemma tailbK {n} b (x : n.-bits) : tailb (consb b x) = x.
Proof. by rewrite /consb /tailb cast_ordKV upperK. Qed.


Fixpoint bitwise {n} (f : 'Z_2 → 'Z_2 → 'Z_2) : n.-bits → n.-bits → n.-bits :=
  match n with
  | n'.+1 => λ x y, consb (f (headb x) (headb y)) (bitwise f (tailb x) (tailb y))
  | 0 => λ x y, nilb
  end.

Definition xor {n : nat} : n.-bits → n.-bits → n.-bits := bitwise +%R.

Notation "x ⊕ y" := (xor x y) (at level 40).

Fixpoint bits0 {n} : n.-bits :=
  match n with
  | n'.+1 => consb 0 bits0
  | 0 => nilb
  end.

Lemma bit_add_sub (x y : 'Z_2) : x + y = x - y.
Proof.
  apply ord_inj => //=.
  destruct x, y. unfold Zp_trunc in *. simpl in *.
  destruct m, m0 => //; destruct m0 => //. 
Qed.

Lemma eq_nilb x : x = nilb.
Proof. by rewrite 2!ord1. Qed.

Lemma xorA {n} (x y z : n.-bits) : (x ⊕ y) ⊕ z = x ⊕ (y ⊕ z).
Proof.
  unfold xor. induction n => //=.
  by rewrite 2!headbK 2!tailbK GRing.addrA IHn.
Qed.

Lemma xorC {n} (x y : n.-bits) : x ⊕ y = y ⊕ x.
Proof.
  unfold xor. induction n => //=.
  by rewrite GRing.addrC IHn.
Qed.

Lemma xorbb {n} (x : n.-bits) : x ⊕ x = bits0.
Proof.
  unfold xor. induction n => //=.
  by rewrite bit_add_sub /xor IHn //= GRing.subrr.
Qed.

Lemma xor0b {n} (x : n.-bits) : bits0 ⊕ x = x.
Proof.
  unfold xor. induction n => //=; [ symmetry; apply eq_nilb |].
  by rewrite headbK tailbK GRing.add0r IHn consbK.
Qed.

Lemma xorb0 {n} (x : n.-bits) : x ⊕ bits0 = x.
Proof.
  unfold xor. induction n => //=; [ symmetry; apply eq_nilb |].
  by rewrite headbK tailbK GRing.addr0 IHn consbK.
Qed.

Lemma xorKb {n} (x y : n.-bits) : x ⊕ (x ⊕ y) = y.
Proof. by rewrite -xorA xorbb xor0b. Qed.

Lemma xorbK {n} (x y : n.-bits) : (y ⊕ x) ⊕ x = y.
Proof. by rewrite xorA xorbb xorb0. Qed.

Lemma xor_bij {n} (x : n.-bits) : bijective (λ y, x ⊕ y).
Proof. exists (λ y, x ⊕ y) => y; by rewrite xorKb. Qed.

End Bits.

Notation "x ⊕ y" := (xor x y) (at level 40).


Section ExtraLemmas.
  Definition compl {N} (R : {fset 'I_N}) : {fset 'I_N} :=
    fset (ord_enum N) :\: R.

  Lemma in_compl {N} (a : 'I_N) (A : {fset 'I_N}):
    (a \in compl A) = (a \notin A).
  Proof. by rewrite in_fsetD in_fset mem_ord_enum andbC. Qed.

  Program Definition bump {N} (l : {fset 'I_N}) : 'I_(N - size l) → 'I_N
    := λ r, nth _ (compl l) r.
  Obligation 1. destruct l. destruct fsval => //. by rewrite /= subn0 in r. Qed.

  Lemma codomm_set {T S : ordType} (L : {fmap T → S}) t s
    : t \notin domm L → codomm (setm L t s) = s |: codomm L.
  Proof.
    intros H'.
    apply eq_fset => s'. rewrite in_fsetU1.
    apply Bool.eq_iff_eq_true. split.
    - move=> /codommP [t' H].
      rewrite setmE in H.
      destruct (t' == t)%B.
      + injection H => ->. by rewrite eq_refl.
      + apply /orP; right. apply /codommP. by exists t'.
    - move=> /orP [/eqP {s'}->| /codommP [t' H]]; apply /codommP.
      + exists t. by rewrite setmE eq_refl.
      + exists t'. rewrite setmE.
        destruct (t' == t)%B eqn:E; [| done ].
        by move: E H' H => /eqP -> /dommPn ->.
  Qed.
End ExtraLemmas.


(* Experimental Code Simpl *)

Lemma destruct_pair {A B C} {z : A * B} {f : A → B → C}
  : (let (x, y) := z in f x y) = f z.1 z.2.
Proof. by destruct z. Qed.

Lemma code_link_if_Some (T A : choiceType) :
  ∀ (c₀ : T → raw_code A) (c₁ : raw_code A)
  (p : raw_package) (b : option T),
  code_link (if b is Some x then c₀ x else c₁) p =
  (if b is Some x then code_link (c₀ x) p else code_link c₁ p).
Proof. by intros ? ? ? []. Qed.

Definition hints :=
  ( @destruct_pair
  , @code_link_assertD
  , @code_link_bind
  , @code_link_if
  , @code_link_if_Some
  , @bind_assoc
  , @resolve_set
  , @resolve_link
  , @resolve_ID_set
  , @coerce_kleisliE
  ).

Ltac ssprove_simpl_more := idtac.

Ltac ssprove_simpl := simpl ; repeat (first
  [ (rewrite hints //=)
  | (rewrite -> (code_link_scheme _ _ (_.(prog))) by apply prog_valid)
  | (eapply r_transR ; [ eapply r_bind_assertD_sym | ])
  | ssprove_simpl_more
  ]).

Lemma r_if_case_rule :
  ∀ {A₀ A₁ : choiceType} (c₀ c₀' : raw_code A₀)
    (c₁ c₁' : raw_code A₁) {b : bool} {pre : precond}
    {post : postcond A₀ A₁}
    , ⊢ ⦃ pre ⦄ c₀ ≈ c₁ ⦃ post ⦄
    → ⊢ ⦃ pre ⦄ c₀' ≈ c₁' ⦃ post ⦄
    → ⊢ ⦃ pre ⦄ if b then c₀ else c₀' ≈
           if b then c₁ else c₁' ⦃ post ⦄.
Proof. by intros ? ? ? ? ? ? []. Qed.

Lemma r_if_case_rule_Some :
  ∀ {T A₀ A₁ : choiceType} (c₀ : T → raw_code A₀) (c₀' : raw_code A₀)
    (c₁ : T → raw_code A₁) (c₁' : raw_code A₁) {b : option T} {pre : precond}
    {post : postcond A₀ A₁}
    , (∀ t, ⊢ ⦃ pre ⦄ c₀ t ≈ c₁ t ⦃ post ⦄)
    → ⊢ ⦃ pre ⦄ c₀' ≈ c₁' ⦃ post ⦄
    → ⊢ ⦃ pre ⦄ if b is Some x then c₀ x else c₀' ≈
           if b is Some x then c₁ x else c₁' ⦃ post ⦄.
Proof. by intros ? ? ? ? ? ? ? []. Qed.

Lemma rsame_head_eq :
  ∀ {A B : choiceType} {f₀ f₁ : A → raw_code B}
    {m₀ m₁ : raw_code A},
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄ m₀ ≈ m₁ ⦃ eq ⦄ →
    (∀ a, ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄ f₀ a ≈ f₁ a ⦃ eq ⦄) →
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄ x ← m₀ ;; f₀ x ≈ x ← m₁ ;; f₁ x ⦃ eq ⦄.
Proof.
  intros A B f₀ f₁ m₀ m₁ Hm Hf.
  eapply r_bind; [ apply Hm |] => a₀ a₁.
  eapply rpre_hypothesis_rule => s₀ s H.
  injection H => ? ? {H}; subst.
  eapply rpre_weaken_rule; [ apply Hf |] => s₀ s₁ /= [? ?].
  by subst.
Qed.

Lemma rsame_head_sample :
  ∀ {B : choiceType} {op : Op} {f₀ f₁ : Arit op → raw_code B}
    (post : postcond B B),
    (∀ a : Arit op, ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄ f₀ a ≈ f₁ a ⦃ post ⦄)
    → ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄ x ← sample op ;; f₀ x ≈ x ← sample op ;; f₁ x ⦃ post ⦄.
Proof. intros. by apply (rsame_head_cmd (cmd_sample op)). Qed.

Lemma rsame_head_get :
  ∀ {B : choiceType} {l : Location} {f₀ f₁ : l → raw_code B}
    (post : postcond B B),
    (∀ a : l, ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄ f₀ a ≈ f₁ a ⦃ post ⦄)
    → ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄ x ← get l ;; f₀ x ≈ x ← get l ;; f₁ x ⦃ post ⦄.
Proof. intros. by apply (rsame_head_cmd (cmd_get l)). Qed.

Lemma rsame_head_put :
  ∀ {B : choiceType} {l : Location} {a : l} {f₀ f₁ : raw_code B}
    (post : postcond B B),
    ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄ f₀ ≈ f₁ ⦃ post ⦄
    → ⊢ ⦃ λ '(h₀, h₁), h₀ = h₁ ⦄ #put l := a ;; f₀ ≈ #put l := a ;; f₁ ⦃ post ⦄.
Proof. intros. by apply (@rsame_head_cmd _ _ (λ _, _) (λ _, _) (cmd_put l a)). Qed.

Ltac ssprove_rel_cong_rhs_extra c :=
  idtac "failed to traverse:" c.

Ltac ssprove_rel_cong_rhs :=
  lazymatch goal with
  | |- ⊢ ⦃ _ ⦄ ?lhs ≈ ?c ⦃ _ ⦄ =>
    lazymatch c with
    | x ← sample ?op ;; _ =>
      let n := fresh x in
      tryif is_evar lhs
        then instantiate (1 := sampler _ (λ n, _)) else idtac ;
      eapply (@rsame_head_sample _ op (λ n, _)) (*; intros ?*)
    | #put ?ℓ := ?v ;; _ =>
      eapply rsame_head_put
    | x ← get ?ℓ ;; _ =>
      let n := fresh x in
      tryif is_evar lhs
        then instantiate (1 := getr _ (λ n, _)) else idtac ;
      eapply (@rsame_head_get _ ℓ (λ n, _)) (*; intros ?*)
    | @assertD ?A ?b (λ x, _) =>
      let n := fresh x in
      tryif is_evar lhs
        then instantiate (1 := assertD _ (λ n, _)) else idtac ;
      eapply (@r_assertD_same A b _ _ (λ n, _)) (*; intros ?*)
    | @bind ?A ?B _ (λ x, _) =>
      let n := fresh x in
      tryif is_evar lhs
        then instantiate (1 := @bind A B _ (λ n, _)) else idtac ;
      eapply (@rsame_head_eq A B (λ n, _)) (*; [| intros ? ]*)
    | if ?e then _ else _ =>
      eapply r_if_case_rule
    | if ?e is Some _ then _ else _ =>
      eapply r_if_case_rule_Some
    | fail =>
      eapply @rreflexivity_rule
    | ret _ =>
      eapply @rreflexivity_rule
    | prog _ =>
      eapply @rreflexivity_rule
    | c => ssprove_rel_cong_rhs_extra c
    end
  end.

Ltac ssprove_sync_eq ::= ssprove_rel_cong_rhs.

Ltac ssp_simpl :=
  lazymatch goal with
  | |- ⊢ ⦃ _ ⦄ _ ≈ _ ⦃ _ ⦄ =>
    eapply rel_jdg_replace_sem ; [
    | (*solve [*) repeat (ssprove_simpl ; ssprove_rel_cong_rhs ; intros)
    | (*solve [*) repeat (ssprove_simpl ; ssprove_rel_cong_rhs ; intros)
    ]
  | |- _ =>
    fail "ssprove_code_simpl_more: goal should be syntactic judgment"
  end.


Definition matchNone {T : choice_type} (v : option T) : Op
  := ('unit; if v is None then dunit tt else dnull).

Definition matchSome {T : choice_type} (v : option T) : Op
  := (T; if v is Some a then dunit a else dnull).

#[export] Instance LosslessOp_dunit {T : choice_type} (t : T)
  : LosslessOp (T; dunit t).
Proof. apply Couplings.psum_SDistr_unit. Qed.

Lemma r_unit_ret :
  ∀ {T : choice_type} (v : T),
    ⊢ ⦃ λ '(s0, s1), s0 = s1 ⦄ ret v ≈ x ← sample (T; dunit v) ;; ret x ⦃ eq ⦄.
Proof.
  intros.
  eapply from_sem_jdg.
  move=> [h1 h2] /= a [hpre hpost].
  exists (dunit ((v, h1), (v, h2))). split.
  - unfold Couplings.coupling, Couplings.lmg, Couplings.rmg. split.
    + by rewrite dmarginE dlet_unit_ext.
    + by rewrite /SDistr_bind dmarginE 2!dlet_unit_ext.
  - move=> [a1 h1'] [a2 h2'] H /=.
    apply hpost.
    rewrite dunit1E in H.
    destruct (_ == _)%B eqn:E; move=> /eqP in E.
    + apply pair_equal_spec in E as [E1 E2].
      apply pair_equal_spec in E1, E2.
      destruct E1, E2. by subst.
    + by rewrite ltxx in H.
Qed.

Lemma r_unit_lhs :
  ∀ {A A' : choiceType} {T : choice_type} (v : T) (c₀ : T → raw_code A)
    (c₁ : raw_code A') (pre : precond) (post : postcond A A'),
    (⊢ ⦃ pre ⦄ c₀ v ≈ c₁ ⦃ post ⦄) → ⊢ ⦃ pre ⦄
       x ← sample (T; dunit v) ;; c₀ x ≈ c₁ ⦃ post ⦄.
Proof.
  intros.
  eapply r_transL; [| apply H ].
  eapply (r_bind (ret v) (y ← sample (T; dunit v) ;; ret y));
    [ apply r_unit_ret |].
  move=> a a'. eapply rpre_hypothesis_rule.
  move=> s0 s1 H'. apply pair_equal_spec in H' as [H1 H2].
  subst. eapply rpre_weaken_rule.
  - eapply rreflexivity_rule.
  - move=> s0' s1' /= [H1 H2]. by subst.
Qed.

Lemma r_unit_rhs :
  ∀ {A A' : choiceType} {T : choice_type} (v : T) (c₀ : raw_code A)
    (c₁ : T → raw_code A') (pre : precond) (post : postcond A A'),
    (⊢ ⦃ pre ⦄ c₀ ≈ c₁ v ⦃ post ⦄) → ⊢ ⦃ pre ⦄
       c₀ ≈ x ← sample (T; dunit v) ;; c₁ x ⦃ post ⦄.
Proof.
  intros.
  eapply r_transR; [| apply H ].
  eapply (r_bind (ret v) (y ← sample (T; dunit v) ;; ret y));
    [ apply r_unit_ret |].
  move=> a a'. eapply rpre_hypothesis_rule.
  move=> s0 s1 H'. apply pair_equal_spec in H' as [H1 H2].
  subst. eapply rpre_weaken_rule.
  - eapply rreflexivity_rule.
  - move=> s0' s1' /= [H1 H2]. by subst.
Qed.

Lemma r_sample_null :
  ∀ {A A' : choiceType} {T T' : choice_type}
    (c₀ : T → raw_code A) (c₁ : T' → raw_code A')
    (pre : precond) (post : postcond A A'),
    ⊢ ⦃ pre ⦄ x ← sample (T; dnull) ;; c₀ x
            ≈ x ← sample (T'; dnull) ;; c₁ x ⦃ post ⦄.
Proof.
  intros. eapply (r_bind fail fail _ _ _ (λ _ _, False));
    [ apply r_fail | intros; by apply rpre_hypothesis_rule ].
Qed.

Lemma r_matchNone_lhs :
  ∀ {A A' : choiceType} {T : choice_type} (c₀ : unit → raw_code A)
    (c₁ : raw_code A') (pre : precond) (post : postcond A A'),
    ⊢ ⦃ pre ⦄ c₀ tt ≈ c₁ ⦃ post ⦄ →
    ⊢ ⦃ pre ⦄ x ← sample (@matchNone T None) ;; c₀ x ≈ c₁ ⦃ post ⦄.
Proof. intros. by apply (r_unit_lhs tt). Qed.

Lemma r_matchNone_rhs :
  ∀ {A A' : choiceType} {T : choice_type} (c₀ : raw_code A)
    (c₁ : unit → raw_code A') (pre : precond) (post : postcond A A'),
    ⊢ ⦃ pre ⦄ c₀ ≈ c₁ tt ⦃ post ⦄ →
    ⊢ ⦃ pre ⦄ c₀ ≈ x ← sample (@matchNone T None) ;; c₁ x ⦃ post ⦄.
Proof. intros. by apply (r_unit_rhs tt). Qed.

Lemma r_matchNone :
  ∀ {A A' : choiceType} {T : choice_type} (v : option T)
    (c₀ : unit → raw_code A) (c₁ : unit → raw_code A')
    (pre : precond) (post : postcond A A'),
    (v = None → ⊢ ⦃ pre ⦄ c₀ tt ≈ c₁ tt ⦃ post ⦄) →
    ⊢ ⦃ pre ⦄ x ← sample (@matchNone T v) ;; c₀ x
            ≈ x ← sample (@matchNone T v) ;; c₁ x ⦃ post ⦄.
Proof.
  intros. destruct v; [ eapply r_sample_null |].
  by apply r_matchNone_lhs, r_matchNone_rhs, H.
Qed.

Lemma r_matchSome_lhs :
  ∀ {A A' : choiceType} {T : choice_type} (v : T) (c₀ : T → raw_code A)
    (c₁ : raw_code A') (pre : precond) (post : postcond A A'),
    ⊢ ⦃ pre ⦄ c₀ v ≈ c₁ ⦃ post ⦄ →
    ⊢ ⦃ pre ⦄ x ← sample (matchSome (Some v)) ;; c₀ x ≈ c₁ ⦃ post ⦄.
Proof. intros. by apply r_unit_lhs. Qed.

Lemma r_matchSome_rhs :
  ∀ {A A' : choiceType} {T : choice_type} (v : T) (c₀ : raw_code A)
    (c₁ : T → raw_code A') (pre : precond) (post : postcond A A'),
    ⊢ ⦃ pre ⦄ c₀ ≈ c₁ v ⦃ post ⦄ →
    ⊢ ⦃ pre ⦄ c₀ ≈ x ← sample (matchSome (Some v)) ;; c₁ x ⦃ post ⦄.
Proof. intros. by apply r_unit_rhs. Qed.

Lemma r_matchSome :
  ∀ {A A' : choiceType} {T : choice_type} (v : option T)
    (c₀ : T → raw_code A) (c₁ : T → raw_code A')
    (pre : precond) (post : postcond A A'),
    (∀ v', v = Some v' → ⊢ ⦃ pre ⦄ c₀ v' ≈ c₁ v' ⦃ post ⦄) →
    ⊢ ⦃ pre ⦄ x ← sample (matchSome v) ;; c₀ x
            ≈ x ← sample (matchSome v) ;; c₁ x ⦃ post ⦄.
Proof.
  intros. destruct v; [| apply r_sample_null ].
  by apply r_matchSome_lhs, r_matchSome_rhs, H.
Qed.

Notation "'getNone' n ;; c" :=
  ( v ← get n ;;
    _ ← sample (matchNone v) ;;
    c )
  (at level 100, n at next level, right associativity,
  format "getNone  n  ;;  '//' c")
  : package_scope.

Notation "x ← 'getSome' n ;; c" :=
  ( v ← get n ;;
    x ← sample (matchSome v) ;;
    c )
  (at level 100, n at next level, right associativity,
  format "x  ←  getSome  n  ;;  '//' c")
  : package_scope.
