(* This file is based on the KEM-DEM example given in SSProve.
   https://github.com/SSProve/ssprove/blob/main/theories/Crypt/examples/KEMDEM.v
 *)
(** KEM-DEM example

  In this example, we follow the original SSP paper available at:
  https://eprint.iacr.org/2018/306

  In this file we first define the KEY pacakges and prove the single key lemma
  of the SSP paper. We then proceed to define the KEM-DEM packages and proving
  its security relative to that of the KEM and the DEM.
*)

From NominalSSP Require Import Options Misc.

Section KEMDEM.

  (** We open a section in order to make local changes to global settings
      in the unlikely event that this module is imported somewhere else.
  *)
  Set Equations Transparent.

  (** In the SSP paper, bitstrings are used for the different data types.
      Instead we go for a more abstract types.
      In the cases where we need to be able to sample on these data types,
      we will first assume we have a (lossless) sub-distribution, and then
      define the types as the domain of these sub-distributions.
  *)

  (** Symmetric key *)
  Context (keyD : Op).
  Definition key := keyD.π1.

  (** Public and secret key *)
  Context (pkey skey : choice_type).

  (** Plain text *)
  Context (plain : choice_type).

  (** We additionally require a "zero" in chPlain.

    Note that we don't require any structure on chPlain so this "zero" is only
    a "zero" in name a priori. Can be thought of as the 0 bitstring.
  *)
  Context (plain0 : plain).

  (** Encrypted key

    This corresponds to the type of symmetric keys once encrypted.
  *)
  Context (ekeyD : Op).
  Definition ekey := ekeyD.π1.

  (** Cipher text *)
  Context (cipherD : Op).
  Definition cipher := cipherD.π1.

  (** Procedure names

    Under the hood, procedures are identified by natural numbers so we abstract
    them away by using distrinct coq-level identifiers.
  *)

  (* KEY *)
  Definition GEN := 0%N.
  Definition SET := 1%N.
  Definition GET := 2%N.

  (* KEM-CCA *)
  Definition KEMGEN := 6%N.
  Definition ENCAP := 7%N.
  Definition DECAP := 8%N.

  (* DEM-CCA *)
  Definition ENC := 9%N.
  Definition DEC := 10%N.

  (* PKE-CCA / MOD-CCA *)
  Definition PKGEN := 3%N.
  Definition PKENC := 4%N.
  Definition PKDEC := 5%N.

  (** Memory locations *)
  Definition k_loc : Location := mkloc 0 (None : option key).
  Definition pk_loc : Location := mkloc 1 (None : option pkey).
  Definition sk_loc : Location := mkloc 2 (None : option skey).
  Definition ek_loc : Location := mkloc 3 (None : option ekey).
  Definition c_loc : Location := mkloc 4 (None : option cipher).

  Definition pk_m_loc : Location := mkloc 5 (None : option pkey).
  Definition ek_m_loc : Location := mkloc 6 (None : option ekey).
  Definition c_m_loc : Location := mkloc 7 (None : option cipher).

  (** Some shorthands *)
  Definition IGEN := [interface [ GEN ] : { unit ~> unit } ].
  Definition ISET := [interface [ SET ] : { key  ~> unit } ].
  Definition IGET := [interface [ GET ] : { unit ~> key  } ].

  (** PKE scheme

    A public-key encryption scheme comes with a key generation (a public and
    private key pair) and an encryption procedures (in the sense that they can
    use effects, typically sampling for the key generation procedure). It also
    comes with a pure (in particular deterministric) decryption function.
    The purity is denoted by the abscence of [code] in the return type.
  *)

  Record PKE_scheme := {
    PKE_kgen : dist (pkey × skey) ;
    PKE_enc : pkey → plain → dist (ekey × cipher) ;
    PKE_dec : skey → chProd ekey cipher → plain
  }.

  (** KEM scheme

    A key encapsulation mechanism comes with a key generation
    (public/private pair) and an encapsulation procedures as well as with a
    pure / deterministic decapsulation function.
  *)

  Record KEM_scheme := {
    KEM_kgen : dist (pkey × skey) ;
    KEM_encap : pkey → dist (key × ekey) ;
    KEM_decap : skey → ekey → key
  }.

  (** DEM scheme

    A data encapsulation mechanism comes with deterministric pure encryption
    and decryption functions. Both use a symmetric key.
  *)

  Record DEM_scheme := {
    DEM_enc : key → plain → cipher ;
    DEM_dec : key → cipher → plain
  }.

  (** We assume we are given a KEM and DEM schemes. *)
  Context (η : KEM_scheme).
  Context (θ : DEM_scheme).

  (** Specification of assumed schemes

    We assume the existence of a relation capturing which public key corresponds
    to which secret key. We furthermore require KEM_kgen to ensure that the
    keys it generates verify this relation.

    We use this relation to state the correctness of KEM_encap.

    The [⊢ₛ _ ⦃ _ ⦄] notation corresponds to unary specifications with only a
    post-condition on the result. They correspond to the diagonal of relational
    specifications, with the addition that state must be preserved.
  *)

  Context (pkey_pair : (chProd pkey skey) → Prop).
  Context (KEM_kgen_spec : ⊢ₛ η.(KEM_kgen) ⦃ pkey_pair ⦄).

  Definition encap_spec (pk : pkey) (kek : chProd key ekey) : Prop :=
    ∀ sk, pkey_pair (pk, sk) → η.(KEM_decap) sk kek.2 = kek.1.

  Context (KEM_encap_spec : ∀ pk, ⊢ₛ η.(KEM_encap) pk ⦃ encap_spec pk ⦄).

  (** KEY package *)

  (** The KEY package will only use one location: [k_loc] corresponding the
    stored key.
  *)
  Definition KEY_loc :=
    [fmap k_loc ].

  (** Similarly, we define the export / output interface of the KEY package.

    The KEY package can generate a key [GEN] and then store its result in the
    location [k_loc] or alternatively it can set [SET] a key provided by the
    caller, finally in can return the stored key using [GET].
  *)
  Definition KEY_out :=
    [interface
      [ GEN ] : { unit ~> unit } ;
      [ SET ] : { key  ~> unit } ;
      [ GET ] : { unit ~> key  }
    ].

  (** Definition of the KEY package *)
  Definition KEY : game KEY_out :=
    [package KEY_loc ;
      [ GEN ] (_) {
        k ← get k_loc ;;
        #assert (k == None) ;;
        k ← sample keyD ;;
        #put k_loc := Some k ;;
        @ret 'unit tt
      } ;
      [ SET ] (k) {
        k' ← get k_loc ;;
        #assert (k' == None) ;;
        #put k_loc := Some k ;;
        @ret 'unit tt
      } ;
      [ GET ] (_) {
        k ← get k_loc ;;
        #assert (isSome k) as kSome ;;
        ret (getSome k kSome)
      }
    ].

  (** KEM package *)

  (** The KEM pacakge can refer to locations corresponding to a public and
    private asymetric keys, and to an encrypted symmetric key.
  *)
  Definition KEM_loc := [fmap pk_loc ; sk_loc ; ek_loc ].

  (** The KEM packaee is parametrised by a boolean [b] depedning on which
    its import interface differs. If [b] is [true] it will be able to call
    the [SET] procedure, and if [b] is [false] it will be able to call the
    [GEN] one. In the paper [KEM true] corresponds to KEM⁰, while [KEM false]
    corresponds to KEM¹.
  *)
  Definition KEM_in b :=
    if b then ISET else IGEN.

  (** The KEM package will export a public and private key generation procedure
    [KEMGEM] that only returns the public one, an ecapsulation procedure [ENCAP]
    which will generate and encrypt a symmetric key, and a decpasulation
    procedure [DECAP] which returns a symmetric key given its encryption.
  *)
  Definition KEM_out :=
    [interface
      [ KEMGEN ] : { unit ~> pkey } ;
      [ ENCAP ]  : { unit ~> ekey } ;
      [ DECAP ]  : { ekey ~> key  }
    ].

  Definition KEM (b : bool) : package (KEM_in b) KEM_out :=
    [package KEM_loc ;
      [ KEMGEN ] : {'unit ~> pkey} '_ {
        sk ← get sk_loc ;;
        #assert (sk == None) ;;
        '(pk, sk) ← η.(KEM_kgen) ;;
        #put pk_loc := Some pk ;;
        #put sk_loc := Some sk ;;
        ret pk
      } ;
      [ ENCAP ] : {'unit ~> ekey} '_ {
        pk ← get pk_loc ;;
        #assert (isSome pk) as pkSome ;;
        let pk := getSome pk pkSome in
        ek ← get ek_loc ;;
        #assert (ek == None) ;;
        '(k, ek) ← η.(KEM_encap) pk ;;
        #put ek_loc := Some ek ;;
        if b then 
          _ ← call [ SET ] : { key ~> unit } k ;;
          ret ek
        else 
          _ ← call [ GEN ] : { unit ~> unit } tt ;;
          ret ek
      } ;
      [ DECAP ] : {ekey ~> key} (ek') {
        sk ← get sk_loc ;;
        #assert (isSome sk) as skSome ;;
        let sk := getSome sk skSome in
        ek ← get ek_loc ;;
        #assert (ek != Some ek') ;;
        ret (η.(KEM_decap) sk ek')
      }
    ].

  (** KEM-CCA game

    The KEM-CCA game is obtained by composing the KEM and KEY packages, as well
    as the identity package. A game pair is described using a boolean-indexed
    function. Here, the only part that changes is the KEM package which is
    already indexed by a boolean.

    KEM-CCAᵇ = (KEMᵇ || ID) ∘ KEY
  *)

  Definition KEM_CCA_out :=
    [interface
      [ KEMGEN ] : { unit ~> pkey } ;
      [ ENCAP ]  : { unit ~> ekey } ;
      [ DECAP ]  : { ekey ~> key  } ;
      [ GET ]    : { unit ~> key  }
    ].

  Definition KEM_CCA_loc :=
    unionm KEM_loc KEY_loc.

  (** Here we use Equations to generate a goal corresponding to the validity of
    the composed package as it is not inferred automatically.
    We call [ssprove_valid] which progresses as much as possible and then asks
    us to prove the remanining bits.

    Here and afterwards we use #[tactic=notac] to tell Equations not to
    preprocess the generated goals.
  *)
  Definition KEM_CCA b := (KEM b || ID IGET) ∘ KEY.


  #[export] Instance KEM_CCA_valid {b}
    : ValidPackage (loc (KEM_CCA b)) Game_import KEM_CCA_out (KEM_CCA b).
  Proof. unfold KEM_CCA. ssprove_valid. Qed.


  (** DEM package *)

  (** The DEM package only stores a cipher. *)
  Definition DEM_loc := [fmap c_loc ].

  (** The DEM package can refer to the [GET] procedure. *)
  Definition DEM_in := IGET.

  (** The DEM package, produced from the DEM scheme θ, exports an encryption
    and a decryption procedures.
  *)
  Definition DEM_out :=
    [interface
      [ ENC ] : { plain  ~> cipher } ;
      [ DEC ] : { cipher ~> plain  }
    ].

  Definition DEM (b : bool) : package DEM_in DEM_out :=
    [package DEM_loc ;
      [ ENC ] : {plain ~> cipher} (m) {
        c ← get c_loc ;;
        #assert (c == None) ;;
        k ← call [ GET ] : { unit ~> key } tt ;;
        let c := θ.(DEM_enc) k (if b then m else plain0) in
        #put c_loc := Some c ;;
        ret c
      } ;
      [ DEC ] : {cipher ~> plain} (c') {
        c ← get c_loc ;;
        #assert (c != Some c') ;;
        k ← call [ GET ] : { unit ~> key } tt ;;
        ret (θ.(DEM_dec) k c')
      }
    ].

  (** DEM-CCA game

    The DEM-CCA game is obtained by composing the DEM and KEY packages, as
    well as the indentity package.

    DEM-CCAᵇ = (DEMᵇ || ID) ∘ KEY
  *)

  Definition DEM_CCA_out :=
    [interface
      [ GEN ] : { unit   ~> unit   } ;
      [ ENC ] : { plain  ~> cipher } ;
      [ DEC ] : { cipher ~> plain  }
    ].

  Definition DEM_CCA_loc :=
    unionm DEM_loc KEY_loc.

  Definition DEM_CCA b :=
    (ID IGEN || DEM b) ∘ KEY.

  #[export] Instance DEM_CCA_valid {b}
    : ValidPackage (loc (DEM_CCA b)) Game_import DEM_CCA_out (DEM_CCA b).
  Proof. unfold DEM_CCA. ssprove_valid. Qed.


  (** PKE-CCA *)

  Definition PKE_CCA_loc := [fmap pk_loc ; sk_loc ; c_loc ; ek_loc ].

  Definition PKE_CCA_out :=
    [interface
      [ PKGEN ] : { unit ~> pkey } ;
      [ PKENC ] : { plain ~> ekey × cipher } ;
      [ PKDEC ] : { ekey × cipher ~> plain }
    ].

  Definition PKE_CCA (ζ : PKE_scheme) b : game PKE_CCA_out :=
    [package PKE_CCA_loc ;
      [ PKGEN ] : { unit ~> pkey } (_) {
        sk ← get sk_loc ;;
        #assert (sk == None) ;;
        '(pk, sk) ← ζ.(PKE_kgen) ;;
        #put pk_loc := Some pk ;;
        #put sk_loc := Some sk ;;
        ret pk
      } ;
      [ PKENC ] : { plain ~> ekey × cipher } (m) {
        pk ← get pk_loc ;;
        #assert (isSome pk) as pkSome ;;
        let pk := getSome pk pkSome in
        ek ← get ek_loc ;;
        #assert (ek == None) ;;
        c ← get c_loc ;;
        #assert (c == None) ;;
        '(ek, c) ← ζ.(PKE_enc) pk (if b then m else plain0) ;;
        #put ek_loc := Some ek ;;
        #put c_loc := Some c ;;
        ret (ek, c)
      } ;
      [ PKDEC ] : { ekey × cipher ~> plain } (c') {
        sk ← get sk_loc ;;
        #assert (isSome sk) as skSome ;;
        let sk := getSome sk skSome in
        ek ← get ek_loc ;;
        c ← get c_loc ;;
        #assert ((ek, c) != (Some c'.1, Some c'.2)) ;;
        ret (ζ.(PKE_dec) sk c')
      }
    ].

  (** MOD-CCA *)

  Definition MOD_CCA_loc :=
    fset [:: pk_m_loc ; c_m_loc ; ek_m_loc ].

  Definition MOD_CCA_in :=
    [interface
      [ KEMGEN ] : {'unit ~> pkey} ;
      [ ENCAP ] : {'unit ~> ekey} ;
      [ DECAP ] : {ekey ~> key} ;
      [ ENC ] : {plain ~> cipher} ;
      [ DEC ] : {cipher ~> plain}
    ].

  Definition MOD_CCA_out :=
    PKE_CCA_out.

  Definition MOD_CCA (ζ : PKE_scheme) :
    module MOD_CCA_in MOD_CCA_out :=
    [module MOD_CCA_loc ;
      [ PKGEN ] : {'unit ~> pkey} '_ {
        let KEMGEN := #import [ KEMGEN ] : {'unit ~> pkey} in
        pk ← get pk_m_loc ;;
        #assert (pk == None) ;;
        pk ← KEMGEN tt ;;
        #put pk_m_loc := Some pk ;;
        ret pk
      } ;
      [ PKENC ] : {plain ~> ekey × cipher} (m) {
        let ENCAP := #import [ENCAP] : {'unit ~> ekey} in
        let ENC := #import [ENC] : {plain ~> cipher} in
        pk ← get pk_m_loc ;;
        #assert (isSome pk) ;;
        ek ← get ek_m_loc ;;
        #assert (ek == None) ;;
        c ← get c_m_loc ;;
        #assert (c ==  None) ;;
        ek ← ENCAP tt ;;
        #put ek_m_loc := Some ek ;;
        c ← ENC m ;;
        #put c_m_loc := Some c ;;
        @ret (chProd _ _) (ek, c)
      } ;
      [ PKDEC ] : {ekey × cipher ~> plain} '(ek', c') {
        let DECAP := #import [DECAP] : {ekey ~> key} in
        let DEC := #import [DEC] : {cipher ~> plain} in
        pk ← get pk_m_loc ;;
        #assert (isSome pk) ;;
        ek ← get ek_m_loc ;;
        c ← get c_m_loc ;;
        #assert ((ek, c) != (Some ek', Some c')) ;;
        if ek == Some ek'
        then (
          DEC c'
        )
        else (
          k' ← DECAP ek' ;;
          ret (θ.(DEM_dec) k' c')
        )
      }
    ].

  (** PKE scheme instance *)
  Definition KEM_DEM : PKE_scheme := {|
    PKE_kgen := η.(KEM_kgen) ;
    PKE_enc := λ pk m, {code
      '(k, ek) ← η.(KEM_encap) pk ;;
      let c := θ.(DEM_enc) k m in
      ret (ek, c)
    } ;
    PKE_dec := λ sk c,
      let '(ek, c) := c in
      let k := η.(KEM_decap) sk ek in
      θ.(DEM_dec) k c
  |}.

  (** Single key lemma *)

  (** Corresponds to Lemma 19.a in the SSP paper *)
  Lemma single_key_a {EK ED}:
    ∀ (CD₀ : module IGET ED)
      (CD₁ : module IGET ED)
      (CK₀ : module ISET EK)
      (CK₁ : module IGEN EK)
      (A : raw_module),
      let K₀ := (CK₀ || ID IGET) ∘ KEY in
      let K₁ := (CK₁ || ID IGET) ∘ KEY in
      let D₀ := (ID IGEN || CD₀) ∘ KEY in
      let D₁ := (ID IGEN || CD₁) ∘ KEY in
      Parable CK₀ (ID IGET) →
      Parable CK₁ (ID IGET) →
      Parable (ID IGEN) CD₀ →
      Parable (ID IGEN) CD₁ →
      Adv ((CK₀ || CD₀) ∘ KEY) ((CK₁ || CD₁) ∘ KEY) A <=
      Adv K₀ K₁ (A ∘ (ID EK || CD₀)) +
      Adv D₀ D₁ (A ∘ (CK₁ || ID ED)).
  Proof.
    intros CD₀ CD₁ CK₀ CK₁ A.
    intros.
    nssprove_adv_trans ((CK₁ || CD₀) ∘ KEY).
    erewrite ->
      (@Adv_par_link_l _ _ _ _ _ _ _ _ _ (ISET :|: IGEN) IGET).
    (* why do we loop on first goal? with nssprove_valid? *)
    2-10: nssprove_valid.
    erewrite -> (@Adv_par_link_r _ _ _ _ _ _ _ _ _ IGEN IGET)
      ; nssprove_valid.
  Qed.

  (** Corresponds to Lemma 19.b in the SSP paper *)
  Lemma single_key_b  {EK ED} :
    ∀ (CD₀ : module IGET ED)
      (CD₁ : module IGET ED)
      (CK₀ : module ISET EK)
      (CK₁ : module IGEN EK)
      (A : raw_module),
      let K₀ := (CK₀ || ID IGET) ∘ KEY in
      let K₁ := (CK₁ || ID IGET) ∘ KEY in
      let D₀ := (ID IGEN || CD₀) ∘ KEY in
      let D₁ := (ID IGEN || CD₁) ∘ KEY in
      Parable CK₀ (ID IGET) →
      Parable CK₁ (ID IGET) →
      Parable (ID IGEN) CD₀ →
      Parable (ID IGEN) CD₁ →
      Adv ((CK₀ || CD₀) ∘ KEY) ((CK₀ || CD₁) ∘ KEY) A <=
      Adv K₀ K₁ (A ∘ (ID EK || CD₀)) +
      Adv D₀ D₁ (A ∘ (CK₁ || ID ED)) +
      Adv K₀ K₁ (A ∘ (ID EK || CD₁)).
  Proof.
    intros CD₀ CD₁ CK₀ CK₁ A.
    intros.
    nssprove_adv_trans ((CK₁ || CD₁) ∘ KEY).
    eapply lerD.
    - eapply @single_key_a. all: eauto.
    (* De-idealising the core keying package *)
    - erewrite Adv_sym.
      erewrite -> (@Adv_par_link_l _ _ _ _ _ _ _ _ _ (ISET :|: IGEN) IGET)
        ; nssprove_valid.
  Qed.

  (** Perfect indistinguishability with PKE-CCA

    We show that the package given by
    MOD_CCA KEM_DEM ∘ (KEM⁰ || DEMᵇ) ∘ KEY
    and which we call [Aux b], is perfectly indistinguishable from
    [PKE_CCA KEM_DEM b], which is the PKE-CCA game instantiated with the
    KEM-DEM instance we have.
  *)

  Definition Aux_loc :=
    MOD_CCA_loc :|: (KEM_loc :|: DEM_loc :|: KEY_loc).

  Definition Aux b :=
    (MOD_CCA KEM_DEM ∘ (((KEM true) || (DEM b)) ∘ KEY))%sep.

  #[export] Instance Aux_valid {b : bool}
    : ValidPackage (loc (Aux b)) Game_import PKE_CCA_out (Aux b).
  Proof. unfold Aux. nssprove_valid. Qed.

  (** We extend ssprove_code_simpl to use code_link_scheme.
    It says that linking a scheme with anything results in the scheme itself
    as a scheme does not import anything.
  *)
  Hint Extern 50 (_ = code_link _ _) =>
    rewrite code_link_scheme
    : ssprove_code_simpl.

  (** We extend swapping to schemes.
    This means that the ssprove_swap tactic will be able to swap any command
    with a scheme without asking a proof from the user.
  *)
  Hint Extern 40 (⊢ ⦃ _ ⦄ x ← ?s ;; y ← cmd _ ;; _ ≈ _ ⦃ _ ⦄) =>
    eapply r_swap_scheme_cmd ; ssprove_valid
    : ssprove_swap.

  (** Program equivalences

    In order to prove these equivalences, we will use an invariant that
    dismisses any changes made to the symmetric key location as it is only
    modified in one of the packages. This will be the [heap_ignore KEY_loc] bit
    in the following [inv] invariant.
    We need to extend this invariant with knowlegde about how the contents of
    some locations are related.
    With [triple_rhs pk_loc k_loc ek_loc PKE_inv] we say that the values
    corresponding to the public key, symmetric key and the encrypted symmetric
    key are always related by [PKE_inv] (described below).
    Similarly, [couple_lhs pk_loc sk_loc (sameSomeRel PkeyPair)] relates the
    public and secret keys by the relation [sameSomeRel PkeyPair]. It states
    that both must be [None], or both must be [Some pk] and [Some sk] such
    that [pk] and [sk] are related by [PkeyPair pk sk].
  *)

  (** This rephrasing of [pkey_pair] simply states that the stored public
    and private keys are indeed part of the same key pair, according to the
    specification of the KEM.
  *)
  Definition PkeyPair :=
    λ (pk : pkey) (sk : skey), pkey_pair (pk, sk).

  (** This states two things:
    - [k] and [ek] must both be set ([Some]) or unset ([None]);
    - whenever they are set, then the public key [pk] must as well and the three
    should be related by the functional specification [encap_spec] stating that
    [ek] is indeed the encryption of [k] using public key [pk].
  *)
  Definition PKE_inv (pk : 'option pkey) (k : 'option key) (ek : 'option ekey) :=
    match pk, k, ek with
    | Some pk, Some k, Some ek => encap_spec pk (k, ek)
    | Some pk, None, None => True
    | None, None, None => True
    | _, _, _ => False
    end.

  Notation inv := (
    heap_ignore (MOD_CCA_loc :|: KEY_loc) ⋊
    couple_rhs pk_loc pk_m_loc eq ⋊
    couple_rhs ek_loc ek_m_loc eq ⋊
    couple_rhs c_loc c_m_loc eq ⋊
    triple_rhs pk_m_loc k_loc ek_loc PKE_inv ⋊
    couple_lhs pk_loc sk_loc (sameSomeRel PkeyPair)
  ).

  (** We have to show that [inv] is a valid invariant and while the
    [ssprove_invariant] does most of the work for us we still have some
    properties regarding the sets involved to prove
    (otherwise type inference would have solved it).
  *)
  Instance Invariant_inv : Invariant PKE_CCA_loc Aux_loc inv.
  Proof.
    unfold Aux_loc; simpl.
    ssprove_invariant; try done; fset_solve.
  Qed.


  (** We show perfect equivalence in the general case where [b] stay abstract.
    This spares us the burden of proving roughly the same equivalence twice.
  *)
  Lemma PKE_CCA_perf :
    ∀ b, perfect PKE_CCA_out (PKE_CCA KEM_DEM b) (Aux b).
  Proof.
    intro b. unfold Aux.
    nssprove_share. eapply prove_perfect.
    Unshelve.
    3: nssprove_valid.
    (* We go to the relational logic with our invariant. *)
    eapply eq_rel_perf_ind with (inv := inv). 1: exact _.
    simplify_eq_rel m.
    all: ssprove_code_simpl.
    (* We are now in the realm of program logic *)
    - ssprove_code_simpl_more.
      ssprove_code_simpl.
      ssprove_swap_seq_rhs [:: 1 ; 0 ; 2 ; 1 ]%N.
      eapply r_get_vs_get_remember.
      1: ssprove_invariant; fset_solve. intro sk.
      ssprove_sync. intro skNone.
      eapply r_get_remember_rhs. intro pk.
      eapply (r_rem_couple_lhs pk_loc sk_loc). 1,3: exact _.
      1:{
        eapply Remembers_lhs_from_tracked_rhs.
        2: ssprove_invariant; fset_solve.
        intros s0 s1 [preH remH].
        do 6 move: preH => [preH _].
        move: preH => [_ preH].
        rewrite /rem_rhs preH remH //.
      }
      intro eps. destruct sk. 1: discriminate.
      destruct pk. 1: contradiction. simpl.
      eapply r_scheme_bind_spec. 1: eapply KEM_kgen_spec. intros [pk' sk'] pps.
      eapply r_put_vs_put.
      eapply r_put_vs_put.
      eapply r_put_rhs.
      ssprove_restore_mem.
      2: apply r_ret; auto.
      ssprove_invariant; try auto.
      + rewrite -fset_cat. ssprove_invariant.
      + intros s0 s1 H.
        rewrite /triple_rhs //= in H |- *.
        destruct H as [[[hi ?] ?] e].
        rewrite e in hi.
        get_heap_simpl.
        by destruct (get_heap s1 k_loc), (get_heap s1 ek_loc).
    - ssprove_code_simpl_more.
      ssprove_code_simpl.
      ssprove_swap_seq_rhs [:: 5 ; 4 ; 3 ; 2 ; 1 ]%N.
      eapply r_get_remember_rhs => pk_m.
      eapply r_get_vs_get_remember. 1: ssprove_invariant; fset_solve. intro pk.
      eapply (r_rem_couple_rhs pk_loc pk_m_loc). 1,2,3: exact _.
      intros Eq; symmetry in Eq; subst.
      ssprove_sync. intro pkSome.
      destruct pk as [pk|]. 2: discriminate.
      simpl.
      ssprove_swap_seq_rhs [:: 3 ; 2 ; 1 ; 0 ]%N.
      eapply r_get_vs_get_remember. 1: ssprove_invariant; fset_solve. intro ek.
      eapply r_get_remind_rhs.
      1: {
        intros s0 s1 [[[[[[[[[_ H] _] _] _] _] _] _] _] H'].
        rewrite /rem_rhs -H H' //.
      }
      ssprove_sync => /eqP -> {ek}.
      
      eapply r_get_remember_rhs => c'.
      eapply (r_rem_rhs c_loc) => c''.
      eapply (r_rem_couple_rhs c_loc c_m_loc).
      1,2,3: exact _. move=> <- {c'}.
      eapply (r_get_remind_lhs c_loc).
      1: eapply Remembers_lhs_from_tracked_rhs.
      2: ssprove_invariant; fset_solve.
      1: exact _.
      ssprove_sync => /eqP -> {c''}.

      eapply r_scheme_bind_spec. 1: eapply KEM_encap_spec. intros [k' ek'] hkek.
      ssprove_code_simpl_more. ssprove_code_simpl.
      ssprove_code_simpl_more.
      ssprove_swap_seq_rhs [:: 3 ; 2 ; 1 ]%N.
      (* ssprove_contract_put_rhs. *)
      ssprove_swap_seq_rhs [:: 4 ; 3 ; 2 ; 1 ; 0 ]%N.
      eapply r_get_remind_rhs.
      1: exact _.
      ssprove_swap_seq_rhs [:: 1 ; 0 ]%N.
      eapply r_get_remember_rhs. intros k.
      eapply (r_rem_triple_rhs pk_m_loc k_loc ek_loc). 1-4: exact _. intro hpke.
      destruct k. 1: contradiction.
      simpl.
      ssprove_swap_seq_rhs [:: 1 ; 2 ; 0 ; 1 ]%N.
      ssprove_contract_put_get_rhs. simpl.
      apply r_put_rhs.
      apply r_put_vs_put.
      apply r_put_rhs.
      apply r_put_vs_put.
      apply r_put_rhs.
      ssprove_restore_mem.
      2: apply r_ret; auto.
      ssprove_invariant.
      2,3: reflexivity.
      + rewrite -fset_cat. ssprove_invariant.
      + intros s₀ s₁ hh. unfold triple_rhs in *. simpl in *.
        destruct hh as [[[[[[[[hi epk] ?] ?] ?] ?] ?] ?] ?]. simpl in *.
        get_heap_simpl.
        rewrite epk. simpl. auto.
    - destruct m as [ek' c']. simpl.
      ssprove_swap_seq_rhs [:: 1 ; 0 ; 2 ; 1 ]%N.
      ssprove_swap_seq_lhs [:: 1 ; 0 ; 2 ; 1 ]%N.

      eapply r_get_remember_rhs => ek.
      eapply (r_rem_rhs ek_loc) => ek''.
      eapply (r_rem_couple_rhs ek_loc ek_m_loc).
      1,2,3: exact _. move=> -> {ek''}.
      eapply (r_get_remind_lhs ek_loc).
      1: eapply Remembers_lhs_from_tracked_rhs.
      2: ssprove_invariant; fset_solve.
      1: exact _.

      eapply r_get_remember_rhs => c.
      eapply (r_rem_rhs c_loc) => c''.
      eapply (r_rem_couple_rhs c_loc c_m_loc).
      1,2,3: exact _. move=> -> {c''}.
      eapply (r_get_remind_lhs c_loc).
      1: eapply Remembers_lhs_from_tracked_rhs.
      2: ssprove_invariant; fset_solve.
      1: exact _.

      eapply r_get_remember_rhs. intro pk.
      eapply r_get_remember_lhs. intro sk.
      eapply (r_rem_couple_lhs pk_loc sk_loc pk). 1,3: exact _.
      1: eapply Remembers_lhs_from_tracked_rhs.
      2: ssprove_invariant; fset_solve.
      1: {
        intros s0 s1 [[[[[[[[[[[_ H] _] _] _] _] _] _] _] _] H'] _].
        rewrite /rem_rhs H H' //.
      }

      intro eps.
      eapply sameSomeRel_sameSome in eps as eps'. rewrite eps'.
      ssprove_sync. intro skSome.
      ssprove_sync. intro neq.
      move: neq => /eqP neq.

      destruct (ek == Some ek')%bool eqn:eek.
      + move: eek => /eqP eek. subst ek.
        destruct (c != Some c') eqn:e.
        2:{ move: e => /eqP e. subst. contradiction. }
        rewrite eq_refl; simpl.
        eapply r_get_remind_rhs.
        1: exact _.
        rewrite e.
        ssprove_code_simpl. simpl.
        ssprove_code_simpl. ssprove_code_simpl_more.
        eapply r_get_remember_rhs. intro k.
        eapply (r_rem_triple_rhs pk_m_loc k_loc ek_loc). 1,2,3: exact _.
        1: exact _.
        intro hpke.
        destruct sk as [sk|]. 2: discriminate.
        destruct pk as [pk|]. 2: contradiction.
        destruct k as [k|]. 2: contradiction.
        simpl. simpl in hpke. simpl in eps. unfold PkeyPair in eps.
        eapply hpke in eps as h. simpl in h. subst.
        ssprove_forget_all.
        apply r_ret. auto.
      + rewrite eek. ssprove_code_simpl_more.
        eapply r_get_remind_rhs.
        1: apply Remembers_rhs_from_tracked_lhs.
        1: exact _.
        1: ssprove_invariant; fset_solve.
        destruct sk as [sk|]. 2: discriminate.
        simpl.
        eapply r_get_remind_rhs.
        1: exact _.
        rewrite eek.
        simpl.
        ssprove_forget_all.
        apply r_ret; auto.
  Qed.


  (** Security theorem *)

  Theorem PKE_security :
    ∀ (A : module PKE_CCA_out A_export),
      AdvFor (PKE_CCA KEM_DEM) A <=
      AdvFor KEM_CCA (A ∘ (MOD_CCA KEM_DEM ∘ (ID KEM_out || DEM true))) +
      AdvFor DEM_CCA (A ∘ (MOD_CCA KEM_DEM ∘ (KEM false || ID DEM_out))) +
      AdvFor KEM_CCA (A ∘ (MOD_CCA KEM_DEM ∘ (ID KEM_out || DEM false))).
  Proof.
    intros A.
    rewrite (AdvFor_perfect PKE_CCA_perf) /Aux /AdvFor.
    erewrite Adv_sep_link.
    eapply le_trans.
    + eapply (single_key_b _ _ _ (KEM false)).
      all: nssprove_valid.
    + by erewrite sep_link_assoc, sep_link_assoc, sep_link_assoc.
  Qed.
End KEMDEM.
