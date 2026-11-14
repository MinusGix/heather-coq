(** * Presupposition: indexed families with infinitary children (M19a)

    [PresupIWf]'s lemmas for [IWi]: the signature has a domain [D] under
    the shape and the position, and the child index [C] lives under it; a
    child is a [Π] over the domain ([iwiFam]), at [iwiL] by [lconv]. The
    declarative rules state the induction hypothesis's type a premise and
    β's induction hypothesis typed (M19_DESIGN.md), so nothing here types
    [dnth]. The generic lemmas ([mv_ty], [IWf_id1], [IWf_id2],
    [IWf_single_eq], …) are [PresupIWf]'s. *)
From DeLaM.Typing Require Export PresupIWf.

(** ** Equations of the telescope *)

Lemma IWi_E_ren3 (X : ty) : X⟨↑⟩⟨↑⟩⟨↑⟩⟨rlift (rlift (rlift ↑))⟩ = X⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩.
Proof. ren_comm. Qed.
Lemma IWi_E_C (X : ty) a : nfty X -> X⟨↑⟩⟨↑⟩⟨↑⟩[llift (llift (lsingle a))] = X⟨↑⟩⟨↑⟩.
Proof. intros NX. teq_core. Qed.
Lemma IWi_E_mot l lp li (X A : ty) (N : tm) (D : ty) (Ot C m : tm) :
  nfty X -> nfty A -> nftm N -> nfty D -> nftm Ot -> nftm C ->
  (iwimotty l lp li X A N D Ot C)[lsingle m] = tyIWi l lp li X A N D Ot C m.
Proof. intros. push_subst. f_equal. all: teq_core. Qed.
Lemma IWi_E5 l lp li (X A : ty) (N : tm) (D : ty) (Ot C a : tm) :
  nfty X -> nfty A -> nftm N -> nfty D -> nftm Ot -> nftm C ->
  (iwicsty l lp li X A N D Ot C)[lsingle a] = tyDVec (iwiL l lp li) N[lsingle a] (iwiFam l lp li X A N D Ot C a).
Proof.
  intros. unfold iwiFam, iwiFamCod. push_subst. f_equal. all: try teq_core.
  all: f_equal. all: try teq_core. all: f_equal. all: teq_core.
Qed.
Lemma IWi_E6 l lp li (X A : ty) (N : tm) (D : ty) (Ot C : tm) (M : ty) a cs h :
  nfty X -> nfty A -> nftm N -> nfty D -> nftm Ot -> nftm C ->
  (iwistepty l lp li X A N D Ot C M)[lsingle3 a cs h] = M[lsingle2 Ot[lsingle a] (tmSupii l lp li X A N D Ot C a cs)].
Proof.
  intros NX NA NN ND NO NC.
  set (s := tmSupii l lp li X⟨↑⟩⟨↑⟩⟨↑⟩ A⟨↑⟩⟨↑⟩⟨↑⟩ N⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩
             D⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩ Ot⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩
             C⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩ (var 2) (var 1)).
  assert (Es : s[lsingle3 a cs h] = tmSupii l lp li X A N D Ot C a cs).
  { subst s. push_subst. f_equal; try teq_core; pw. }
  assert (Eo : Ot⟨↑⟩⟨↑⟩[lsingle3 a cs h] = Ot[lsingle a]) by teq_core.
  rewrite subst_comp_ty, !ren_ren_comp_ty,
    (ren_subst_ty M _ _ (lsingle2 Ot[lsingle a] (tmSupii l lp li X A N D Ot C a cs))); auto.
  intros [|[|n]]; pw.
  all: first [exact Es | exact (eq_sym Es) | exact Eo | exact (eq_sym Eo) | idtac].
Qed.

(** The motive's scrutinee type, weakened past one local under its binder. *)
Lemma IWi_mot_ren l lp li (X A : ty) (N : tm) (D : ty) (Ot C : tm) :
  (iwimotty l lp li X A N D Ot C)⟨rlift ↑⟩
  = iwimotty l lp li X⟨↑⟩ A⟨↑⟩ N⟨rlift ↑⟩ D⟨rlift (rlift ↑)⟩ Ot⟨rlift ↑⟩ C⟨rlift (rlift (rlift ↑))⟩.
Proof. push_ren. f_equal; ren_comm. Qed.
(** The children's entry, seen from the step's context. *)
Lemma IWi_E_var1 l lp li (X A : ty) (N : tm) (D : ty) (Ot C : tm) :
  (iwicsty l lp li X A N D Ot C)⟨↑⟩⟨↑⟩ =
  tyDVec (iwiL l lp li) (N⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩)[lsingle (var 2)]
    (iwiFam l lp li X⟨↑⟩⟨↑⟩⟨↑⟩ A⟨↑⟩⟨↑⟩⟨↑⟩ N⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩
       D⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩ Ot⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩
       C⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩ (var 2)).
Proof.
  rewrite Wf_E2. unfold iwiFam, iwiFamCod. push_ren. push_subst.
  f_equal. all: try teq_core. all: f_equal. all: try teq_core. all: f_equal. all: teq_core.
Qed.

(** A child's level: [Π^{lp, iwiL}] is at [iwiL]. *)
Lemma iwiL_pi L l lp li : lwf L l -> lwf L lp -> lwf L li ->
  lequiv L (iwiL l lp li) (lmax lp (iwiL l lp li)).
Proof. intros. repeat split; cbn; auto. intros; lia. Qed.

Section IWiAux.
Context {G : gctx} {i : layer} (Hi : typeof i = i) (Hv : i <> lV).

(** The signature: the index type, the shapes, the arity, the domain, the
    output index and the child index. *)
Definition IWiSig Γ l lp li X A N D Ot C : Prop :=
  lwf (gL G) l /\ lwf (gL G) lp /\ lwf (gL G) li /\
  [ G ; Γ ⊢[ i ] X @ li ] /\ [ G ; Γ ⊢[ i ] A @ l ] /\
  [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] /\
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] D @ lp ] /\
  [ G ; Γ ,, A @ l ⊢[ i ] Ot : X⟨↑⟩ @ li ] /\
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp ⊢[ i ] C : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ].

(** Two signatures along equal components: the left one, the equations, and
    the right components typed in the left contexts. *)
Definition IWiEq Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' : Prop :=
  lequiv (gL G) l k /\ lequiv (gL G) lp kp /\ lequiv (gL G) li ki /\ IWiSig Γ l lp li X A N D Ot C /\
  [ G ; Γ ⊢[ i ] X ≅ X' @ li ] /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l ] /\
  [ G ; Γ ,, A @ l ⊢[ i ] N ≅ N' : tyNat @ lzero ] /\
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] D ≅ D' @ lp ] /\
  [ G ; Γ ,, A @ l ⊢[ i ] Ot ≅ Ot' : X⟨↑⟩ @ li ] /\
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp ⊢[ i ] C ≅ C' : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] /\
  [ G ; Γ ⊢[ i ] X' @ li ] /\ [ G ; Γ ⊢[ i ] A' @ l ] /\
  [ G ; Γ ,, A @ l ⊢[ i ] N' : tyNat @ lzero ] /\
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] D' @ lp ] /\
  [ G ; Γ ,, A @ l ⊢[ i ] Ot' : X⟨↑⟩ @ li ] /\
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp ⊢[ i ] C' : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ].

(** [IWiEq] with its equations first, so that a proof search solving the
    premises in order fixes the left components from them. *)
Lemma IWiEq_intro {Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C'} :
  lequiv (gL G) l k -> lequiv (gL G) lp kp -> lequiv (gL G) li ki ->
  [ G ; Γ ⊢[ i ] X ≅ X' @ li ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N ≅ N' : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] D ≅ D' @ lp ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] Ot ≅ Ot' : X⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp ⊢[ i ] C ≅ C' : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] ->
  lwf (gL G) l -> lwf (gL G) lp -> lwf (gL G) li ->
  [ G ; Γ ⊢[ i ] X @ li ] -> [ G ; Γ ⊢[ i ] A @ l ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] D @ lp ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] Ot : X⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp ⊢[ i ] C : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] ->
  [ G ; Γ ⊢[ i ] X' @ li ] -> [ G ; Γ ⊢[ i ] A' @ l ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N' : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] D' @ lp ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] Ot' : X⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp ⊢[ i ] C' : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] ->
  IWiEq Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C'.
Proof using. intros. unfold IWiEq, IWiSig. tauto. Qed.

Lemma IWiSig_nf {Γ l lp li X A N D Ot C} : IWiSig Γ l lp li X A N D Ot C ->
  nfty X /\ nfty A /\ nftm N /\ nfty D /\ nftm Ot /\ nftm C.
Proof using.
  intros (_ & _ & _ & HX & HA & HN & HD & HO & HC).
  repeat split; first [exact (wf_ty_nf HX) | exact (wf_ty_nf HA) | exact (wf_tm_nf HN)
                      | exact (wf_ty_nf HD) | exact (wf_tm_nf HO) | exact (wf_tm_nf HC)].
Qed.

Lemma IWiSig_ctx {Γ l lp li X A N D Ot C} : IWiSig Γ l lp li X A N D Ot C -> [ G ; Γ ⊢[ i ] ].
Proof using Hi. intros (_ & _ & _ & HX & _). exact (ctx_of_wf_ty Hi HX). Qed.

(** The type at an index. *)
Lemma IWi_ty_wf {Γ l lp li X A N D Ot C m} : IWiSig Γ l lp li X A N D Ot C -> [ G ; Γ ⊢[ i ] m : X @ li ] ->
  [ G ; Γ ⊢[ i ] tyIWi l lp li X A N D Ot C m @ iwiL l lp li ].
Proof using Hi Hv.
  intros (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC) Hm. apply wft_iwi; auto.
Qed.

(** The output index at a shape. *)
Lemma IWi_ot_wf {Γ l lp li X A N D Ot C a} : IWiSig Γ l lp li X A N D Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] Ot[lsingle a] : X @ li ].
Proof using Hi.
  intros (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC) Ha.
  pose proof (wf_tm_single Hi HO Ha) as X0. rewrite IWf_E_ot in X0 by exact (wf_ty_nf HX). exact X0.
Qed.

(** The weakening under the signature's three binders. *)
Lemma wkr_up3 {Δ Γ Y ly A l N D lp} :
  [ G ; Γ ,, Y @ ly ,, A⟨↑⟩ @ l ,, tyFin N⟨rlift ↑⟩ @ lzero ,, D⟨rlift (rlift ↑)⟩ @ lp ⊢[ i ] ] ->
  Δ = Γ ,, Y @ ly ,, A⟨↑⟩ @ l ,, tyFin N⟨rlift ↑⟩ @ lzero ,, D⟨rlift (rlift ↑)⟩ @ lp ->
  wkr (rlift (rlift (rlift ↑))) Δ (Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp).
Proof using.
  intros _ ->. eapply wkr_up'; [eapply wkr_up'; [eapply wkr_up'; [apply wkr_shift1 | reflexivity] | reflexivity]
                               | reflexivity].
Qed.
Lemma wkr_up2 {Γ Y ly A l N} :
  wkr (rlift (rlift ↑)) (Γ ,, Y @ ly ,, A⟨↑⟩ @ l ,, tyFin N⟨rlift ↑⟩ @ lzero) (Γ ,, A @ l ,, tyFin N @ lzero).
Proof using.
  eapply wkr_up'; [eapply wkr_up'; [apply wkr_shift1 | reflexivity] | reflexivity].
Qed.

(** Weakening under one more local. *)
Lemma IWiSig_wk1 {Γ Y ly l lp li X A N D Ot C} : IWiSig Γ l lp li X A N D Ot C -> [ G ; Γ ,, Y @ ly ⊢[ i ] ] ->
  IWiSig (Γ ,, Y @ ly) l lp li X⟨↑⟩ A⟨↑⟩ N⟨rlift ↑⟩ D⟨rlift (rlift ↑)⟩ Ot⟨rlift ↑⟩ C⟨rlift (rlift (rlift ↑))⟩.
Proof using Hi Hv.
  intros (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC) HΓY.
  assert (HA1 : [ G ; Γ ,, Y @ ly ⊢[ i ] A⟨↑⟩ @ l ]) by exact (wk1_ty G i Hi _ _ _ _ _ HΓY HA).
  assert (HΓYA : [ G ; Γ ,, Y @ ly ,, A⟨↑⟩ @ l ⊢[ i ] ]) by exact (ext_wf Hi HA1 Hl).
  assert (HN1 : [ G ; Γ ,, Y @ ly ,, A⟨↑⟩ @ l ⊢[ i ] N⟨rlift ↑⟩ : tyNat @ lzero ])
    by exact (wk_under_tm Hi HΓYA HN).
  assert (HΘ : [ G ; Γ ,, Y @ ly ,, A⟨↑⟩ @ l ,, tyFin N⟨rlift ↑⟩ @ lzero ⊢[ i ] ])
    by (apply (ext_wf Hi); [apply wft_fin; [exact Hv | exact HN1] | exact I]).
  assert (HD1 : [ G ; Γ ,, Y @ ly ,, A⟨↑⟩ @ l ,, tyFin N⟨rlift ↑⟩ @ lzero ⊢[ i ] D⟨rlift (rlift ↑)⟩ @ lp ])
    by (eapply weakening_r; [exact HD | exact Hi | exact wkr_up2 | exact HΘ]).
  assert (HΘ3 : [ G ; Γ ,, Y @ ly ,, A⟨↑⟩ @ l ,, tyFin N⟨rlift ↑⟩ @ lzero ,, D⟨rlift (rlift ↑)⟩ @ lp ⊢[ i ] ])
    by exact (ext_wf Hi HD1 Hlp).
  refine (conj Hl (conj Hlp (conj Hli (conj (wk1_ty G i Hi _ _ _ _ _ HΓY HX)
            (conj HA1 (conj HN1 (conj HD1 (conj _ _)))))))).
  - eapply wf_tm_retype; [exact (wk_under_tm Hi HΓYA HO) | apply IWf_E_ren].
  - eapply wf_tm_retype; [eapply weakening_r; [exact HC | exact Hi | exact (wkr_up3 HΘ3 eq_refl) | exact HΘ3]
                         | apply IWi_E_ren3].
Qed.

Lemma IWiEq_wk1 {Γ Y ly l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C'} :
  IWiEq Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' -> [ G ; Γ ,, Y @ ly ⊢[ i ] ] ->
  IWiEq (Γ ,, Y @ ly) l lp li k kp ki X⟨↑⟩ X'⟨↑⟩ A⟨↑⟩ A'⟨↑⟩ N⟨rlift ↑⟩ N'⟨rlift ↑⟩
    D⟨rlift (rlift ↑)⟩ D'⟨rlift (rlift ↑)⟩ Ot⟨rlift ↑⟩ Ot'⟨rlift ↑⟩
    C⟨rlift (rlift (rlift ↑))⟩ C'⟨rlift (rlift (rlift ↑))⟩.
Proof using Hi Hv.
  intros (Hlk & Hlpk & Hlik & HS & HXX & HAA & HNN & HDD & HOO & HCC & HX' & HA' & HN' & HD' & HO' & HC') HΓY.
  pose proof (IWiSig_wk1 HS HΓY) as HS1.
  pose proof HS1 as (_ & _ & _ & _ & HA1 & HN1 & HD1 & _).
  destruct HS as (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC).
  assert (HΓYA : [ G ; Γ ,, Y @ ly ,, A⟨↑⟩ @ l ⊢[ i ] ]) by exact (ext_wf Hi HA1 Hl).
  assert (HΘ : [ G ; Γ ,, Y @ ly ,, A⟨↑⟩ @ l ,, tyFin N⟨rlift ↑⟩ @ lzero ⊢[ i ] ])
    by (apply (ext_wf Hi); [apply wft_fin; [exact Hv | exact HN1] | exact I]).
  assert (HΘ3 : [ G ; Γ ,, Y @ ly ,, A⟨↑⟩ @ l ,, tyFin N⟨rlift ↑⟩ @ lzero ,, D⟨rlift (rlift ↑)⟩ @ lp ⊢[ i ] ])
    by exact (ext_wf Hi HD1 Hlp).
  pose proof (wkr_up3 HΘ3 eq_refl) as Hr3.
  refine (conj Hlk (conj Hlpk (conj Hlik (conj HS1 _)))).
  repeat split.
  - exact (wk1_eqty G i Hi _ _ _ _ _ _ HΓY HXX).
  - exact (wk1_eqty G i Hi _ _ _ _ _ _ HΓY HAA).
  - exact (wk_under_eqtm Hi HΓYA HNN).
  - eapply weakening_r; [exact HDD | exact Hi | exact wkr_up2 | exact HΘ].
  - eapply eq_tm_retype; [exact (wk_under_eqtm Hi HΓYA HOO) | apply IWf_E_ren].
  - eapply eq_tm_retype; [eapply weakening_r; [exact HCC | exact Hi | exact Hr3 | exact HΘ3] | apply IWi_E_ren3].
  - exact (wk1_ty G i Hi _ _ _ _ _ HΓY HX').
  - exact (wk1_ty G i Hi _ _ _ _ _ HΓY HA').
  - exact (wk_under_tm Hi HΓYA HN').
  - eapply weakening_r; [exact HD' | exact Hi | exact wkr_up2 | exact HΘ].
  - eapply wf_tm_retype; [exact (wk_under_tm Hi HΓYA HO') | apply IWf_E_ren].
  - eapply wf_tm_retype; [eapply weakening_r; [exact HC' | exact Hi | exact Hr3 | exact HΘ3] | apply IWi_E_ren3].
Qed.

(** The identity from converted shape, arity and domain entries. *)
Lemma IWi_id3 {Γ l k lp kp A A' N N' D D'} : [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ⊢[ i ] A' @ l ] -> lequiv (gL G) l k ->
  [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] -> [ G ; Γ ,, A @ l ⊢[ i ] N ≅ N' : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N' : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] D @ lp ] -> [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] D ≅ D' @ lp ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] D' @ lp ] -> lequiv (gL G) lp kp ->
  [ G ; Γ ,, A' @ k ,, tyFin N' @ lzero ,, D' @ kp ⊢[ i ] lshift 0 : Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp ].
Proof using Hi Hv.
  intros HA HAA HA' Hlk HN HNN HN' HD HDD HD' Hlp.
  exact (proj2 (ctx_conv_ext Hi (IWf_id2 Hi Hv HA HAA HA' Hlk HN HNN HN') HD HDD HD' Hlp)).
Qed.

(** The right signature, in its own contexts. *)
Lemma IWiEq_sig_r {Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C'} :
  IWiEq Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' -> IWiSig Γ k kp ki X' A' N' D' Ot' C'.
Proof using Hi Hv.
  intros (Hlk & Hlpk & Hlik & (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC) & HXX & HAA & HNN & HDD & HOO & HCC
          & HX' & HA' & HN' & HD' & HO' & HC').
  pose proof (lequiv_wf_r _ _ _ Hlk) as Hk. pose proof (lequiv_wf_r _ _ _ Hlpk) as Hkp.
  pose proof (lequiv_wf_r _ _ _ Hlik) as Hki.
  pose proof (IWf_id1 Hi HA HAA HA' Hlk) as Hid1.
  pose proof (IWf_id2 Hi Hv HA HAA HA' Hlk HN HNN HN') as Hid2.
  pose proof (IWi_id3 HA HAA HA' Hlk HN HNN HN' HD HDD HD' Hlpk) as Hid3.
  assert (HΓA : [ G ; Γ ,, A @ l ⊢[ i ] ]) by exact (ext_wf Hi HA Hl).
  assert (EX1 : [ G ; Γ ,, A @ l ⊢[ i ] X'⟨↑⟩ ≅ X⟨↑⟩ @ li ])
    by exact (wk1_eqty G i Hi _ _ _ _ _ _ HΓA (eqty_sym _ _ _ _ _ _ HXX)).
  assert (HΓAN : [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] ])
    by (apply (ext_wf Hi); [apply wft_fin; assumption | exact I]).
  assert (EX2 : [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] X'⟨↑⟩⟨↑⟩ ≅ X⟨↑⟩⟨↑⟩ @ li ])
    by exact (wk1_eqty G i Hi _ _ _ _ _ _ HΓAN EX1).
  assert (HΓAND : [ G ; Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp ⊢[ i ] ]) by exact (ext_wf Hi HD Hlp).
  assert (EX3 : [ G ; Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp ⊢[ i ] X'⟨↑⟩⟨↑⟩⟨↑⟩ ≅ X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ])
    by exact (wk1_eqty G i Hi _ _ _ _ _ _ HΓAND EX2).
  refine (conj Hk (conj Hkp (conj Hki (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
  - eapply wft_lconv; [exact HX' | apply lequiv_sym, Hlik].
  - eapply wft_lconv; [exact HA' | apply lequiv_sym, Hlk].
  - exact (mv_tm Hi Hid1 HN').
  - eapply wft_lconv; [exact (mv_ty Hi Hid2 HD') | apply lequiv_sym, Hlpk].
  - eapply wf_lconv; [| apply lequiv_sym, Hlik]. exact (mv_tm Hi Hid1 (conv_tm' Hi HO' EX1)).
  - eapply wf_lconv; [| apply lequiv_sym, Hlik]. exact (mv_tm Hi Hid3 (conv_tm' Hi HC' EX3)).
Qed.

(** The types along equal components. *)
Lemma IWi_ty_eq {Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' m m'} :
  IWiEq Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' -> [ G ; Γ ⊢[ i ] m ≅ m' : X @ li ] ->
  [ G ; Γ ⊢[ i ] tyIWi l lp li X A N D Ot C m ≅ tyIWi k kp ki X' A' N' D' Ot' C' m' @ iwiL l lp li ].
Proof using Hi Hv.
  intros (Hlk & Hlpk & Hlik & (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC) & HXX & HAA & HNN & HDD & HOO & HCC & _) Hmm.
  apply eqty_iwi; auto.
Qed.

Lemma IWi_lvl_eq {l lp li k kp ki} : lequiv (gL G) l k -> lequiv (gL G) lp kp -> lequiv (gL G) li ki ->
  lequiv (gL G) (iwiL l lp li) (iwiL k kp ki).
Proof using. intros. repeat apply lequiv_max; assumption. Qed.

Lemma pre_iwi_r {Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' m'} :
  IWiEq Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' -> [ G ; Γ ⊢[ i ] m' : X @ li ] ->
  [ G ; Γ ⊢[ i ] tyIWi k kp ki X' A' N' D' Ot' C' m' @ iwiL l lp li ].
Proof using Hi Hv.
  intros HE Hm'. pose proof (IWiEq_sig_r HE) as HS'.
  destruct HE as (Hlk & Hlpk & Hlik & _ & HXX & _).
  eapply wft_lconv; [| exact (IWi_lvl_eq Hlk Hlpk Hlik)].
  apply (IWi_ty_wf HS').
  eapply wf_lconv; [eapply (conv_tm' Hi); [exact Hm' | exact (eqty_sym _ _ _ _ _ _ HXX)] | apply lequiv_sym, Hlik].
Qed.

(** The substitution [llift (lsingle a)] into the arity's context, and its
    lift past the domain. *)
Lemma IWi_sub1 {Γ l lp li X A N D Ot C a} : IWiSig Γ l lp li X A N D Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] llift (lsingle a) : Γ ,, A @ l ,, tyFin N @ lzero ].
Proof using Hi Hv.
  intros (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC) Ha.
  eapply (lsub_wf_lift' G i Hi); [exact (lsub_wf_single G i Hi _ _ _ _ (ctx_of_wf_tm Hi Ha) Ha)
                                  | apply wft_fin; [exact Hv | exact (wf_tm_single Hi HN Ha)] | exact I
                                  | reflexivity].
Qed.

Lemma IWi_dom_wf {Γ l lp li X A N D Ot C a} : IWiSig Γ l lp li X A N D Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] D[llift (lsingle a)] @ lp ].
Proof using Hi Hv.
  intros HS Ha. pose proof HS as (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC).
  exact (wf_ty_subst Hi HD (IWi_sub1 HS Ha)).
Qed.

Lemma IWi_sub2 {Γ l lp li X A N D Ot C a} : IWiSig Γ l lp li X A N D Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, D[llift (lsingle a)] @ lp ⊢[ i ] llift (llift (lsingle a))
      : Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp ].
Proof using Hi Hv.
  intros HS Ha. pose proof HS as (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC).
  eapply (lsub_wf_lift' G i Hi); [exact (IWi_sub1 HS Ha) | exact (IWi_dom_wf HS Ha) | exact Hlp | reflexivity].
Qed.

(** The child index at a shape, in [Γ, k : Fin N[a/x], y : D[a/x, k]]. *)
Lemma IWi_ci_wf {Γ l lp li X A N D Ot C a} : IWiSig Γ l lp li X A N D Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, D[llift (lsingle a)] @ lp ⊢[ i ]
      C[llift (llift (lsingle a))] : X⟨↑⟩⟨↑⟩ @ li ].
Proof using Hi Hv.
  intros HS Ha. pose proof HS as (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC).
  pose proof (wf_tm_subst Hi HC (IWi_sub2 HS Ha)) as X0.
  rewrite IWi_E_C in X0 by exact (wf_ty_nf HX). exact X0.
Qed.

(** The children's family at a shape, and along equal components. *)
Lemma IWi_famcod_wf {Γ l lp li X A N D Ot C a} : IWiSig Γ l lp li X A N D Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, D[llift (lsingle a)] @ lp ⊢[ i ]
      iwiFamCod l lp li X A N D Ot C a @ iwiL l lp li ].
Proof using Hi Hv.
  intros HS Ha. pose proof HS as (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC).
  assert (HΓ1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] ])
    by (apply (ext_wf Hi); [apply wft_fin; [exact Hv | exact (wf_tm_single Hi HN Ha)] | exact I]).
  assert (HΓ2 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, D[llift (lsingle a)] @ lp ⊢[ i ] ])
    by exact (ext_wf Hi (IWi_dom_wf HS Ha) Hlp).
  unfold iwiFamCod. apply (IWi_ty_wf (IWiSig_wk1 (IWiSig_wk1 HS HΓ1) HΓ2)).
  exact (IWi_ci_wf HS Ha).
Qed.

Lemma IWi_fam_wf {Γ l lp li X A N D Ot C a} : IWiSig Γ l lp li X A N D Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] iwiFam l lp li X A N D Ot C a @ iwiL l lp li ].
Proof using Hi Hv.
  intros HS Ha. pose proof HS as (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC).
  eapply wft_lconv; [| exact (iwiL_pi _ _ _ _ Hl Hlp Hli)].
  unfold iwiFam. apply wft_pi; [exact Hv | exact Hlp | cbn; auto | exact (IWi_dom_wf HS Ha) |].
  exact (IWi_famcod_wf HS Ha).
Qed.

Lemma IWi_fam_eq {Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' a a'} :
  IWiEq Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' ->
  [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] a' : A @ l ] -> [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] ->
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ]
      iwiFam l lp li X A N D Ot C a ≅ iwiFam k kp ki X' A' N' D' Ot' C' a' @ iwiL l lp li ].
Proof using Hi Hv.
  intros HE Ha Ha' Haa.
  pose proof HE as (Hlk & Hlpk & Hlik & HS & HXX & HAA & HNN & HDD & HOO & HCC & HX' & HA' & HN' & HD' & HO' & HC').
  pose proof HS as (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC).
  assert (HNa : [ G ; Γ ⊢[ i ] N[lsingle a] : tyNat @ lzero ]) by exact (wf_tm_single Hi HN Ha).
  assert (HΓ1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] ])
    by (apply (ext_wf Hi); [apply wft_fin; assumption | exact I]).
  assert (HFa : [ G ; Γ ⊢[ i ] tyFin N[lsingle a] @ lzero ]) by (apply wft_fin; assumption).
  assert (EFa : [ G ; Γ ⊢[ i ] (tyFin N)[lsingle a] ≅ (tyFin N)[lsingle a'] @ lzero ])
    by (cbn; apply eqty_fin; [exact Hv | exact (IWf_single_eq Hi (B := tyNat) I HN (eqtm_refl _ _ _ _ _ _ HN) Ha Ha' Haa)]).
  assert (Edd : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] llift (lsingle a) ≅ llift (lsingle a')
                  : Γ ,, A @ l ,, tyFin N @ lzero ])
    by (eapply (lsub_eq_lift Hi); [exact (lsub_eq_single Hi Ha Ha' Haa) | exact HFa | exact I | exact EFa | reflexivity]).
  pose proof (IWi_dom_wf HS Ha) as HDa.
  assert (EDa : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] D[llift (lsingle a)] ≅ D[llift (lsingle a')] @ lp ])
    by exact (wf_ty_func Hi HD Edd).
  assert (EDD : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] D[llift (lsingle a)] ≅ D'[llift (lsingle a')] @ lp ])
    by (eapply eqty_trans; [exact (eqty_subst Hi HDD (lsub_eq_l Edd)) | exact (wf_ty_func Hi HD' Edd)]).
  assert (Edd2 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, D[llift (lsingle a)] @ lp ⊢[ i ]
                   llift (llift (lsingle a)) ≅ llift (llift (lsingle a')) : Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp ])
    by (eapply (lsub_eq_lift Hi); [exact Edd | exact HDa | exact Hlp | exact EDa | reflexivity]).
  assert (HΓ2 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, D[llift (lsingle a)] @ lp ⊢[ i ] ])
    by exact (ext_wf Hi HDa Hlp).
  eapply eqty_lconv; [| exact (iwiL_pi _ _ _ _ Hl Hlp Hli)].
  unfold iwiFam. apply eqty_pi; [exact Hv | exact Hlpk | exact (IWi_lvl_eq Hlk Hlpk Hlik) | exact HDa | exact EDD |].
  unfold iwiFamCod. apply (IWi_ty_eq (IWiEq_wk1 (IWiEq_wk1 HE HΓ1) HΓ2)).
  eapply eqtm_trans.
  - pose proof (eqtm_subst Hi HCC (lsub_eq_l Edd2)) as X0. rewrite IWi_E_C in X0 by exact (wf_ty_nf HX). exact X0.
  - pose proof (wf_tm_func Hi HC' Edd2) as X0. rewrite IWi_E_C in X0 by exact (wf_ty_nf HX). exact X0.
Qed.

(** [sup]'s children's type, and along equal components. *)
Lemma IWi_csa_wf {Γ l lp li X A N D Ot C a} : IWiSig Γ l lp li X A N D Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] tyDVec (iwiL l lp li) N[lsingle a] (iwiFam l lp li X A N D Ot C a) @ iwiL l lp li ].
Proof using Hi Hv.
  intros HS Ha. pose proof HS as (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC).
  apply wft_dvec; [exact Hv | cbn; auto | exact (wf_tm_single Hi HN Ha) | exact (IWi_fam_wf HS Ha)].
Qed.

Lemma IWi_csa_eq {Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' a a'} :
  IWiEq Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' ->
  [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] a' : A @ l ] -> [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] tyDVec (iwiL l lp li) N[lsingle a] (iwiFam l lp li X A N D Ot C a)
      ≅ tyDVec (iwiL k kp ki) N'[lsingle a'] (iwiFam k kp ki X' A' N' D' Ot' C' a') @ iwiL l lp li ].
Proof using Hi Hv.
  intros HE Ha Ha' Haa. pose proof HE as (Hlk & Hlpk & Hlik & HS & HXX & HAA & HNN & _).
  pose proof HS as (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC).
  apply eqty_dvec; [exact Hv | exact (IWi_lvl_eq Hlk Hlpk Hlik) | exact (wf_tm_single Hi HN Ha)
                   | exact (IWf_single_eq Hi (B := tyNat) I HN HNN Ha Ha' Haa)
                   | exact (IWi_fam_wf HS Ha) | exact (IWi_fam_eq HE Ha Ha' Haa)].
Qed.

(** [sup]'s type, and its congruence's right-hand side. *)
Lemma pre_supii_ty {Γ l lp li X A N D Ot C a} : IWiSig Γ l lp li X A N D Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] tyIWi l lp li X A N D Ot C Ot[lsingle a] @ iwiL l lp li ].
Proof using Hi Hv. intros HS Ha. exact (IWi_ty_wf HS (IWi_ot_wf HS Ha)). Qed.

Lemma pre_supii_r {Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' a a' cs'} :
  IWiEq Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' ->
  [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] a' : A @ l ] -> [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] cs' : tyDVec (iwiL l lp li) N[lsingle a] (iwiFam l lp li X A N D Ot C a) @ iwiL l lp li ] ->
  [ G ; Γ ⊢[ i ] tmSupii k kp ki X' A' N' D' Ot' C' a' cs' : tyIWi l lp li X A N D Ot C Ot[lsingle a] @ iwiL l lp li ].
Proof using Hi Hv.
  intros HE Ha Ha' Haa Hcs'. pose proof (IWiEq_sig_r HE) as HS'.
  pose proof HE as (Hlk & Hlpk & Hlik & HS & HXX & HAA & HNN & HDD & HOO & _).
  pose proof HS as (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC).
  pose proof (IWi_lvl_eq Hlk Hlpk Hlik) as HLK.
  assert (Ha'k : [ G ; Γ ⊢[ i ] a' : A' @ k ])
    by (eapply wf_lconv; [eapply (conv_tm' Hi); [exact Ha' | exact (eqty_sym _ _ _ _ _ _ HAA)] | apply lequiv_sym, Hlk]).
  assert (Hcs'k : [ G ; Γ ⊢[ i ] cs' : tyDVec (iwiL k kp ki) N'[lsingle a'] (iwiFam k kp ki X' A' N' D' Ot' C' a') @ iwiL k kp ki ])
    by (eapply wf_lconv; [eapply (conv_tm' Hi); [exact Hcs' | exact (eqty_sym _ _ _ _ _ _ (IWi_csa_eq HE Ha Ha' Haa))]
                         | apply lequiv_sym, HLK]).
  pose proof HS' as (Hk & Hkp & Hki & HX'' & HA'' & HN'' & HD'' & HO'' & HC'').
  eapply wf_lconv; [| exact HLK].
  eapply (conv_tm' Hi); [apply wf_supii; auto |].
  eapply eqty_lconv; [| apply lequiv_sym, HLK].
  eapply (IWi_ty_eq HE).
  eapply (IWf_single_eq Hi); [exact (wf_ty_nf HX) | exact HO | exact HOO | exact Ha | exact Ha' | exact Haa].
Qed.

(** The type at equal indices. *)
Lemma IWi_ty_eq_idx {Γ l lp li X A N D Ot C m m'} : IWiSig Γ l lp li X A N D Ot C ->
  [ G ; Γ ⊢[ i ] m ≅ m' : X @ li ] ->
  [ G ; Γ ⊢[ i ] tyIWi l lp li X A N D Ot C m ≅ tyIWi l lp li X A N D Ot C m' @ iwiL l lp li ].
Proof using Hi Hv.
  intros (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC) Hmm.
  apply eqty_iwi; auto using lequiv_refl, eqty_refl, eqtm_refl.
Qed.

(** The motive's scrutinee type, and along equal components. *)
Lemma IWi_mot_wf {Γ l lp li X A N D Ot C} : IWiSig Γ l lp li X A N D Ot C ->
  [ G ; Γ ,, X @ li ⊢[ i ] iwimotty l lp li X A N D Ot C @ iwiL l lp li ].
Proof using Hi Hv.
  intros HS. pose proof HS as (Hl & Hlp & Hli & HX & _).
  pose proof (ext_wf Hi HX Hli) as HΓX.
  exact (IWi_ty_wf (IWiSig_wk1 HS HΓX) (IWf_var0 Hi HΓX)).
Qed.

Lemma IWi_mot_eq {Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C'} :
  IWiEq Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' ->
  [ G ; Γ ,, X @ li ⊢[ i ] iwimotty l lp li X A N D Ot C ≅ iwimotty k kp ki X' A' N' D' Ot' C' @ iwiL l lp li ].
Proof using Hi Hv.
  intros HE. pose proof HE as (_ & _ & _ & (Hl & Hlp & Hli & HX & _) & _).
  pose proof (ext_wf Hi HX Hli) as HΓX.
  exact (IWi_ty_eq (IWiEq_wk1 HE HΓX) (eqtm_refl _ _ _ _ _ _ (IWf_var0 Hi HΓX))).
Qed.

Lemma IWi_mot_r {Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C'} :
  IWiEq Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' ->
  [ G ; Γ ,, X @ li ⊢[ i ] iwimotty k kp ki X' A' N' D' Ot' C' @ iwiL l lp li ].
Proof using Hi Hv.
  intros HE. pose proof HE as (Hlk & Hlpk & Hlik & (Hl & Hlp & Hli & HX & _) & HXX & _ & _ & _ & _ & _ & HX' & _).
  exact (mv_ty Hi (IWf_id1_rev Hi HX HXX HX' Hlik)
           (wft_lconv _ _ _ _ _ _ (IWi_mot_wf (IWiEq_sig_r HE)) (IWi_lvl_eq Hlk Hlpk Hlik))).
Qed.

(** The children's tuple type in the shape's context, and along equal
    components. *)
Lemma IWi_cs_wf {Γ l lp li X A N D Ot C} : IWiSig Γ l lp li X A N D Ot C ->
  [ G ; Γ ,, A @ l ⊢[ i ] iwicsty l lp li X A N D Ot C @ iwiL l lp li ].
Proof using Hi Hv.
  intros HS. pose proof HS as (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC).
  pose proof (ext_wf Hi HA Hl) as HΓA.
  assert (HΓAF : [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] ])
    by (apply (ext_wf Hi); [apply wft_fin; assumption | exact I]).
  pose proof (ext_wf Hi HD Hlp) as HΓAFD.
  apply wft_dvec; [exact Hv | cbn; auto | exact HN |].
  eapply wft_lconv; [| exact (iwiL_pi _ _ _ _ Hl Hlp Hli)].
  apply wft_pi; [exact Hv | exact Hlp | cbn; auto | exact HD |].
  exact (IWi_ty_wf (IWiSig_wk1 (IWiSig_wk1 (IWiSig_wk1 HS HΓA) HΓAF) HΓAFD) HC).
Qed.

Lemma IWi_cs_eq {Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C'} :
  IWiEq Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' ->
  [ G ; Γ ,, A @ l ⊢[ i ] iwicsty l lp li X A N D Ot C ≅ iwicsty k kp ki X' A' N' D' Ot' C' @ iwiL l lp li ].
Proof using Hi Hv.
  intros HE. pose proof HE as (Hlk & Hlpk & Hlik & HS & HXX & HAA & HNN & HDD & HOO & HCC & _).
  pose proof HS as (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC).
  pose proof (ext_wf Hi HA Hl) as HΓA.
  assert (HΓAF : [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] ])
    by (apply (ext_wf Hi); [apply wft_fin; assumption | exact I]).
  pose proof (ext_wf Hi HD Hlp) as HΓAFD.
  pose proof (IWi_lvl_eq Hlk Hlpk Hlik) as HLK.
  apply eqty_dvec; [exact Hv | exact HLK | exact HN | exact HNN | |].
  - eapply wft_lconv; [| exact (iwiL_pi _ _ _ _ Hl Hlp Hli)].
    apply wft_pi; [exact Hv | exact Hlp | cbn; auto | exact HD |].
    exact (IWi_ty_wf (IWiSig_wk1 (IWiSig_wk1 (IWiSig_wk1 HS HΓA) HΓAF) HΓAFD) HC).
  - eapply eqty_lconv; [| exact (iwiL_pi _ _ _ _ Hl Hlp Hli)].
    apply eqty_pi; [exact Hv | exact Hlpk | exact HLK | exact HD | exact HDD |].
    exact (IWi_ty_eq (IWiEq_wk1 (IWiEq_wk1 (IWiEq_wk1 HE HΓA) HΓAF) HΓAFD) HCC).
Qed.

Lemma IWi_cs_r {Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C'} :
  IWiEq Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' ->
  [ G ; Γ ,, A @ l ⊢[ i ] iwicsty k kp ki X' A' N' D' Ot' C' @ iwiL l lp li ].
Proof using Hi Hv.
  intros HE. pose proof HE as (Hlk & Hlpk & Hlik & (Hl & Hlp & Hli & HX & HA & _) & _ & HAA & _ & _ & _ & _ & _ & HA' & _).
  exact (mv_ty Hi (IWf_id1_rev Hi HA HAA HA' Hlk)
           (wft_lconv _ _ _ _ _ _ (IWi_cs_wf (IWiEq_sig_r HE)) (IWi_lvl_eq Hlk Hlpk Hlik))).
Qed.

(** The motive weakened past one local, under its two binders. *)
Lemma IWi_M_wk1 {Γ Y ly l lp li X A N D Ot C M l'} : IWiSig Γ l lp li X A N D Ot C -> [ G ; Γ ,, Y @ ly ⊢[ i ] ] ->
  [ G ; Γ ,, X @ li ,, iwimotty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, Y @ ly ,, X⟨↑⟩ @ li ,, iwimotty l lp li X⟨↑⟩ A⟨↑⟩ N⟨rlift ↑⟩ D⟨rlift (rlift ↑)⟩ Ot⟨rlift ↑⟩ C⟨rlift (rlift (rlift ↑))⟩ @ iwiL l lp li
      ⊢[ i ] M⟨rlift (rlift ↑)⟩ @ l' ].
Proof using Hi Hv.
  intros HS HΓY HM. pose proof (IWiSig_wk1 HS HΓY) as HS1. pose proof HS as (Hl & Hlp & Hli & _).
  eapply weakening_r; [exact HM | exact Hi | | apply (ext_wf Hi); [exact (IWi_mot_wf HS1) | cbn; auto]].
  eapply wkr_up'; [eapply wkr_up'; [apply wkr_shift1 | reflexivity] | symmetry; apply IWi_mot_ren].
Qed.
Lemma IWi_M_wk1_eq {Γ Y ly l lp li X A N D Ot C M M' l'} : IWiSig Γ l lp li X A N D Ot C -> [ G ; Γ ,, Y @ ly ⊢[ i ] ] ->
  [ G ; Γ ,, X @ li ,, iwimotty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ] M ≅ M' @ l' ] ->
  [ G ; Γ ,, Y @ ly ,, X⟨↑⟩ @ li ,, iwimotty l lp li X⟨↑⟩ A⟨↑⟩ N⟨rlift ↑⟩ D⟨rlift (rlift ↑)⟩ Ot⟨rlift ↑⟩ C⟨rlift (rlift (rlift ↑))⟩ @ iwiL l lp li
      ⊢[ i ] M⟨rlift (rlift ↑)⟩ ≅ M'⟨rlift (rlift ↑)⟩ @ l' ].
Proof using Hi Hv.
  intros HS HΓY HM. pose proof (IWiSig_wk1 HS HΓY) as HS1. pose proof HS as (Hl & Hlp & Hli & _).
  eapply weakening_r; [exact HM | exact Hi | | apply (ext_wf Hi); [exact (IWi_mot_wf HS1) | cbn; auto]].
  eapply wkr_up'; [eapply wkr_up'; [apply wkr_shift1 | reflexivity] | symmetry; apply IWi_mot_ren].
Qed.

(** The step's type along equal components, in the left telescope (with
    any induction-hypothesis entry). *)
Lemma IWi_step_eq {Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' M M' l' I lI} :
  IWiEq Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' ->
  [ G ; Γ ,, X @ li ,, iwimotty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, X @ li ,, iwimotty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ] M ≅ M' @ l' ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ,, I @ lI ⊢[ i ] ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ,, I @ lI ⊢[ i ]
      iwistepty l lp li X A N D Ot C M ≅ iwistepty k kp ki X' A' N' D' Ot' C' M' @ l' ].
Proof using Hi Hv.
  intros HE HM HMM HΘ. pose proof (ctx_pre HΘ) as H2. pose proof (ctx_pre H2) as H1.
  pose proof HE as (Hlk & Hlpk & Hlik & HS & _).
  pose proof (IWiSig_wk1 (IWiSig_wk1 (IWiSig_wk1 HS H1) H2) HΘ) as HS3.
  pose proof (IWiEq_wk1 (IWiEq_wk1 (IWiEq_wk1 HE H1) H2) HΘ) as HE3.
  pose proof (IWiSig_nf HS3) as (NX & NA & NN & ND & NO & NC).
  pose proof HS3 as (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC).
  pose proof HE3 as (_ & _ & _ & _ & HXX & HAA & HNN & HDD & HOO & HCC & HX' & HA' & HN' & HD' & HO' & HC').
  assert (Hv2 : [ G ; _ ⊢[ i ] var 2 : A⟨↑⟩⟨↑⟩⟨↑⟩ @ l ]) by (apply wf_var; [rewrite Hi; exact HΘ | do 3 constructor]).
  assert (Hv1 : [ G ; _ ⊢[ i ] var 1 : tyDVec (iwiL l lp li) (N⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩)[lsingle (var 2)]
                    (iwiFam l lp li X⟨↑⟩⟨↑⟩⟨↑⟩ A⟨↑⟩⟨↑⟩⟨↑⟩ N⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩
                       D⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩ Ot⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩
                       C⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩ (var 2)) @ iwiL l lp li ])
    by (eapply wf_tm_retype; [apply wf_var; [rewrite Hi; exact HΘ | do 2 constructor] | apply IWi_E_var1]).
  pose proof (wf_supii _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hv Hl Hlp Hli HX HA HN HD HO HC Hv2 Hv1) as Hs.
  pose proof (pre_supii_r HE3 Hv2 Hv2 (eqtm_refl _ _ _ _ _ _ Hv2) Hv1) as Hs'.
  pose proof (eqtm_supii _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hv Hlk Hlpk Hlik HX HXX HA HAA HN HNN
                HD HDD HO HOO HC HCC (eqtm_refl _ _ _ _ _ _ Hv2) (eqtm_refl _ _ _ _ _ _ Hv1)) as Hss.
  pose proof (IWi_ot_wf HS3 Hv2) as Ho.
  pose proof (IWf_single_eq Hi NX HO HOO Hv2 Hv2 (eqtm_refl _ _ _ _ _ _ Hv2)) as Hoo.
  pose proof (wf_tm_single Hi HO' Hv2) as Ho'. rewrite IWf_E_ot in Ho' by exact NX.
  rewrite ?Wf_E2 in Hs, Hs', Hss, Ho, Hoo, Ho'. rewrite (Wf_E2 Ot') in Hoo.
  pose proof (IWi_M_wk1 (IWiSig_wk1 (IWiSig_wk1 HS H1) H2) HΘ
                (IWi_M_wk1 (IWiSig_wk1 HS H1) H2 (IWi_M_wk1 HS H1 HM))) as HM3.
  pose proof (IWi_M_wk1_eq (IWiSig_wk1 (IWiSig_wk1 HS H1) H2) HΘ
                (IWi_M_wk1_eq (IWiSig_wk1 HS H1) H2 (IWi_M_wk1_eq HS H1 HMM))) as HMM3.
  assert (Hs'o : [ G ; _ ⊢[ i ] tmSupii k kp ki X'⟨↑⟩⟨↑⟩⟨↑⟩ A'⟨↑⟩⟨↑⟩⟨↑⟩ N'⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩
                    D'⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩
                    Ot'⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ C'⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩ (var 2) (var 1)
                    : tyIWi l lp li X⟨↑⟩⟨↑⟩⟨↑⟩ A⟨↑⟩⟨↑⟩⟨↑⟩ N⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩
                        D⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩ Ot⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩
                        C⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩ Ot'⟨↑⟩⟨↑⟩ @ iwiL l lp li ])
    by exact (conv_tm' Hi Hs' (eqty_sym' (IWi_ty_eq_idx HS3 Hoo))).
  eapply eqty_trans.
  - eapply (wf_ty_func Hi HM3). eapply (lsub_eq_single2 Hi Ho Ho' Hoo); rewrite IWi_E_mot by assumption; [exact Hs | exact Hs'o | exact Hss].
  - apply (eqty_subst Hi HMM3). apply (lsub_wf_single2' Hi HΘ Ho'). rewrite IWi_E_mot by assumption. exact Hs'o.
Qed.

(** [elim_IWi]'s type. *)
Lemma pre_elimIWi_ty {Γ l lp li X A N D Ot C M l' m t} : IWiSig Γ l lp li X A N D Ot C ->
  [ G ; Γ ,, X @ li ,, iwimotty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ⊢[ i ] m : X @ li ] -> [ G ; Γ ⊢[ i ] t : tyIWi l lp li X A N D Ot C m @ iwiL l lp li ] ->
  [ G ; Γ ⊢[ i ] M[lsingle2 m t] @ l' ].
Proof using Hi Hv.
  intros HS HM Hm Ht. pose proof (IWiSig_nf HS) as (NX & NA & NN & ND & NO & NC).
  eapply (wf_ty_subst Hi HM). apply (lsub_wf_single2' Hi (ctx_of_wf_tm Hi Hm) Hm).
  rewrite IWi_E_mot by assumption. exact Ht.
Qed.

(** [elim_IWi]'s type along equal motives, indices and scrutinees. *)
Lemma IWi_mot_inst_eq {Γ l lp li X A N D Ot C M M' l' m m' t t'} : IWiSig Γ l lp li X A N D Ot C ->
  [ G ; Γ ,, X @ li ,, iwimotty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, X @ li ,, iwimotty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ] M ≅ M' @ l' ] ->
  [ G ; Γ ⊢[ i ] m : X @ li ] -> [ G ; Γ ⊢[ i ] m' : X @ li ] -> [ G ; Γ ⊢[ i ] m ≅ m' : X @ li ] ->
  [ G ; Γ ⊢[ i ] t : tyIWi l lp li X A N D Ot C m @ iwiL l lp li ] ->
  [ G ; Γ ⊢[ i ] t' : tyIWi l lp li X A N D Ot C m @ iwiL l lp li ] ->
  [ G ; Γ ⊢[ i ] t ≅ t' : tyIWi l lp li X A N D Ot C m @ iwiL l lp li ] ->
  [ G ; Γ ⊢[ i ] M[lsingle2 m t] ≅ M'[lsingle2 m' t'] @ l' ].
Proof using Hi Hv.
  intros HS HM HMM Hm Hm' Hmm Ht Ht' Htt. pose proof (IWiSig_nf HS) as (NX & NA & NN & ND & NO & NC).
  assert (Ht'm : [ G ; Γ ⊢[ i ] t' : tyIWi l lp li X A N D Ot C m' @ iwiL l lp li ])
    by exact (conv_tm' Hi Ht' (eqty_sym' (IWi_ty_eq_idx HS Hmm))).
  eapply eqty_trans.
  - eapply (wf_ty_func Hi HM). eapply (lsub_eq_single2 Hi Hm Hm' Hmm); rewrite IWi_E_mot by assumption;
      [exact Ht | exact Ht'm | exact Htt].
  - apply (eqty_subst Hi HMM). apply (lsub_wf_single2' Hi (ctx_of_wf_tm Hi Hm) Hm').
    rewrite IWi_E_mot by assumption. exact Ht'm.
Qed.

(** [elim_IWi]'s congruence, right-hand side: the primed telescope is
    formed, the motive, the induction hypothesis's type and the step moved
    into it along the identity, and the type converted. *)
Lemma pre_elimIWi_r {Γ l lp li l' k kp ki k' X X' A A' N N' D D' Ot Ot' C C' M M' c' m m' t t'} :
  IWiEq Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' -> lequiv (gL G) l' k' ->
  [ G ; Γ ,, X @ li ,, iwimotty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, X @ li ,, iwimotty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ] M ≅ M' @ l' ] ->
  [ G ; Γ ,, X @ li ,, iwimotty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ] M' @ l' ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ]
      iwiihty l lp li l' X A N D Ot C M @ lmax lzero (lmax lp l') ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ]
      iwiihty l lp li l' X A N D Ot C M ≅ iwiihty k kp ki k' X' A' N' D' Ot' C' M' @ lmax lzero (lmax lp l') ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ]
      iwiihty k kp ki k' X' A' N' D' Ot' C' M' @ lmax lzero (lmax lp l') ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ,, iwiihty l lp li l' X A N D Ot C M @ lmax lzero (lmax lp l')
      ⊢[ i ] c' : iwistepty l lp li X A N D Ot C M @ l' ] ->
  [ G ; Γ ⊢[ i ] m : X @ li ] -> [ G ; Γ ⊢[ i ] m' : X @ li ] -> [ G ; Γ ⊢[ i ] m ≅ m' : X @ li ] ->
  [ G ; Γ ⊢[ i ] t : tyIWi l lp li X A N D Ot C m @ iwiL l lp li ] ->
  [ G ; Γ ⊢[ i ] t' : tyIWi l lp li X A N D Ot C m @ iwiL l lp li ] ->
  [ G ; Γ ⊢[ i ] t ≅ t' : tyIWi l lp li X A N D Ot C m @ iwiL l lp li ] ->
  [ G ; Γ ⊢[ i ] tmElimIWi k kp ki k' X' A' N' D' Ot' C' M' c' m' t' : M[lsingle2 m t] @ l' ].
Proof using Hi Hv.
  intros HE H' HM HMM HM' HI EI HI' Hc' Hm Hm' Hmm Ht Ht' Htt.
  pose proof (IWiEq_sig_r HE) as HS'.
  pose proof HE as (Hlk & Hlpk & Hlik & HS & HXX & HAA & HNN & HDD & HOO & HCC & HX' & HA' & HN' & HD' & HO' & HC').
  pose proof HS as (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC).
  pose proof HS' as (Hk & Hkp & Hki & HX'' & HA'' & HN'' & HD'' & HO'' & HC'').
  pose proof (IWiSig_nf HS) as (NX & NA & NN & ND & NO & NC).
  pose proof (lequiv_wf_l _ _ _ H') as Hl'. pose proof (lequiv_wf_r _ _ _ H') as Hk'.
  pose proof (ctx_of_wf_ty Hi HX) as HΓ.
  pose proof (IWi_lvl_eq Hlk Hlpk Hlik) as HLK.
  assert (HLI : lequiv (gL G) (lmax lzero (lmax lp l')) (lmax lzero (lmax kp k')))
    by (apply lequiv_max; [apply lequiv_refl; exact I | apply lequiv_max; assumption]).
  (* the motive *)
  pose proof (proj2 (ctx_conv_ext Hi (IWf_id1 Hi HX HXX HX' Hlik) (IWi_mot_wf HS) (IWi_mot_eq HE) (IWi_mot_r HE) HLK))
    as Hidm.
  assert (HM'p : [ G ; Γ ,, X' @ ki ,, iwimotty k kp ki X' A' N' D' Ot' C' @ iwiL k kp ki ⊢[ i ] M' @ k' ])
    by (eapply wft_lconv; [exact (mv_ty Hi Hidm HM') | exact (lequiv_sym _ _ _ H')]).
  (* the induction hypothesis's type and the step *)
  pose proof (proj2 (ctx_conv_ext Hi (IWf_id1 Hi HA HAA HA' Hlk) (IWi_cs_wf HS) (IWi_cs_eq HE) (IWi_cs_r HE) HLK))
    as Hid2.
  assert (HI'p : [ G ; Γ ,, A' @ k ,, iwicsty k kp ki X' A' N' D' Ot' C' @ iwiL k kp ki ⊢[ i ]
                   iwiihty k kp ki k' X' A' N' D' Ot' C' M' @ lmax lzero (lmax kp k') ])
    by (eapply wft_lconv; [exact (mv_ty Hi Hid2 HI') | exact (lequiv_sym _ _ _ HLI)]).
  pose proof (proj2 (ctx_conv_ext Hi Hid2 HI EI HI' HLI)) as Hid3.
  assert (HΘ : [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li
                 ,, iwiihty l lp li l' X A N D Ot C M @ lmax lzero (lmax lp l') ⊢[ i ] ])
    by (apply (ext_wf Hi); [exact HI | cbn; auto]).
  pose proof (IWi_step_eq HE HM HMM HΘ) as ES.
  assert (Hc'p : [ G ; Γ ,, A' @ k ,, iwicsty k kp ki X' A' N' D' Ot' C' @ iwiL k kp ki
                   ,, iwiihty k kp ki k' X' A' N' D' Ot' C' M' @ lmax lzero (lmax kp k')
                   ⊢[ i ] c' : iwistepty k kp ki X' A' N' D' Ot' C' M' @ k' ]).
  { pose proof (wf_tm_subst Hi Hc' Hid3) as X0.
    pose proof (eqty_subst Hi ES Hid3) as Y0.
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 typed_nf)))) _ _ _ _ _ _ ES) as [N1 N2].
    rewrite nf_id in X0 by exact (wf_tm_nf Hc').
    rewrite (nf_id_ty (iwistepty l lp li X A N D Ot C M)) in X0, Y0 by exact N1.
    rewrite (nf_id_ty (iwistepty k kp ki X' A' N' D' Ot' C' M')) in Y0 by exact N2.
    eapply wf_lconv; [eapply (conv_tm' Hi); [exact X0 | exact (eqty_sym' Y0)] | exact (lequiv_sym _ _ _ H')]. }
  (* the index and the scrutinee *)
  assert (Hm'p : [ G ; Γ ⊢[ i ] m' : X' @ ki ])
    by (eapply wf_lconv; [exact (conv_tm' Hi Hm' (eqty_sym' HXX)) | exact (lequiv_sym _ _ _ Hlik)]).
  assert (Ht'p : [ G ; Γ ⊢[ i ] t' : tyIWi k kp ki X' A' N' D' Ot' C' m' @ iwiL k kp ki ])
    by (eapply wf_lconv; [exact (conv_tm' Hi Ht' (eqty_sym' (IWi_ty_eq HE Hmm))) | exact (lequiv_sym _ _ _ HLK)]).
  assert (Ht'm : [ G ; Γ ⊢[ i ] t' : tyIWi l lp li X A N D Ot C m' @ iwiL l lp li ])
    by exact (conv_tm' Hi Ht' (eqty_sym' (IWi_ty_eq_idx HS Hmm))).
  eapply wf_lconv with (l' := k'); [| exact H'].
  eapply (conv_tm' Hi (T' := M'[lsingle2 m' t'])).
  - apply wf_elimIWi; auto.
    + exact (IWi_mot_wf HS').
    + exact (IWi_cs_wf HS').
  - eapply eqty_lconv; [| apply lequiv_sym, H'].
    eapply eqty_trans.
    + eapply (wf_ty_func Hi HM). eapply (lsub_eq_single2 Hi Hm Hm' Hmm); rewrite IWi_E_mot by assumption;
        [exact Ht | exact Ht'm | exact Htt].
    + apply (eqty_subst Hi HMM). apply (lsub_wf_single2' Hi HΓ Hm'). rewrite IWi_E_mot by assumption. exact Ht'm.
Qed.

(** β: the left-hand side, and the reduct at the motive's instance. *)
Lemma pre_elimIWi_beta_l {Γ l lp li l' X A N D Ot C M c a cs} : IWiSig Γ l lp li X A N D Ot C -> lwf (gL G) l' ->
  [ G ; Γ ,, X @ li ,, iwimotty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ]
      iwiihty l lp li l' X A N D Ot C M @ lmax lzero (lmax lp l') ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ,, iwiihty l lp li l' X A N D Ot C M @ lmax lzero (lmax lp l')
      ⊢[ i ] c : iwistepty l lp li X A N D Ot C M @ l' ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] cs : tyDVec (iwiL l lp li) N[lsingle a] (iwiFam l lp li X A N D Ot C a) @ iwiL l lp li ] ->
  [ G ; Γ ⊢[ i ] tmElimIWi l lp li l' X A N D Ot C M c Ot[lsingle a] (tmSupii l lp li X A N D Ot C a cs)
      : M[lsingle2 Ot[lsingle a] (tmSupii l lp li X A N D Ot C a cs)] @ l' ].
Proof using Hi Hv.
  intros HS Hl' HM HI Hc Ha Hcs. pose proof HS as (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC).
  apply wf_elimIWi; auto.
  - exact (IWi_mot_wf HS).
  - exact (IWi_cs_wf HS).
  - exact (IWi_ot_wf HS Ha).
  - apply wf_supii; auto.
Qed.

Lemma pre_elimIWi_beta_ty {Γ l lp li X A N D Ot C M l' a cs} : IWiSig Γ l lp li X A N D Ot C ->
  [ G ; Γ ,, X @ li ,, iwimotty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] cs : tyDVec (iwiL l lp li) N[lsingle a] (iwiFam l lp li X A N D Ot C a) @ iwiL l lp li ] ->
  [ G ; Γ ⊢[ i ] M[lsingle2 Ot[lsingle a] (tmSupii l lp li X A N D Ot C a cs)] @ l' ].
Proof using Hi Hv.
  intros HS HM Ha Hcs. pose proof HS as (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC).
  apply (pre_elimIWi_ty HS HM (IWi_ot_wf HS Ha)). apply wf_supii; auto.
Qed.

Lemma pre_elimIWi_beta {Γ l lp li l' X A N D Ot C M c a cs} : IWiSig Γ l lp li X A N D Ot C ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ,, iwiihty l lp li l' X A N D Ot C M @ lmax lzero (lmax lp l')
      ⊢[ i ] c : iwistepty l lp li X A N D Ot C M @ l' ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] cs : tyDVec (iwiL l lp li) N[lsingle a] (iwiFam l lp li X A N D Ot C a) @ iwiL l lp li ] ->
  [ G ; Γ ⊢[ i ] iwiIH l lp li l' X A N D Ot C M c a cs
      : (iwiihty l lp li l' X A N D Ot C M)[lsingle2 a cs] @ lmax lzero (lmax lp l') ] ->
  [ G ; Γ ⊢[ i ] c[lsingle3 a cs (iwiIH l lp li l' X A N D Ot C M c a cs)]
      : M[lsingle2 Ot[lsingle a] (tmSupii l lp li X A N D Ot C a cs)] @ l' ].
Proof using Hi Hv.
  intros HS Hc Ha Hcs HIH. pose proof (IWiSig_nf HS) as (NX & NA & NN & ND & NO & NC).
  rewrite <- (IWi_E6 l lp li X A N D Ot C M a cs (iwiIH l lp li l' X A N D Ot C M c a cs)) by assumption.
  eapply (wf_tm_subst Hi Hc). unfold lsingle3, lsingle2.
  apply lsub_wf_cons; [apply lsub_wf_cons; [apply lsub_wf_cons |] |].
  - eapply lsub_wf_id; eauto using ctx_of_wf_tm.
  - rewrite nf_id_ty by exact NA. exact Ha.
  - change (lcons (lshift 0) a) with (lsingle a). rewrite IWi_E5 by assumption. exact Hcs.
  - change (lcons (lcons (lshift 0) a) cs) with (lsingle2 a cs). exact HIH.
Qed.

(** ** Signatures along equal signatures (the relation)

    [IWiEq] is a partial equivalence, as [IWfEq]. *)

Lemma IWiEq_refl {Γ l lp li X A N D Ot C} : IWiSig Γ l lp li X A N D Ot C ->
  IWiEq Γ l lp li l lp li X X A A N N D D Ot Ot C C.
Proof using.
  intros HS. pose proof HS as (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC).
  apply IWiEq_intro; auto using lequiv_refl, eqty_refl, eqtm_refl.
Qed.

(** The annotations [D1] of a [sup] at the signature [D], moved to an
    equal signature [D']. *)
Lemma IWiEq_flip {Γ l lp li k kp ki k1 kp1 ki1 X X' X1 A A' A1 N N' N1 D D' D1 Ot Ot' O1 C C' C1} :
  IWiEq Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' ->
  IWiEq Γ l lp li k1 kp1 ki1 X X1 A A1 N N1 D D1 Ot O1 C C1 ->
  IWiEq Γ k kp ki k1 kp1 ki1 X' X1 A' A1 N' N1 D' D1 Ot' O1 C' C1.
Proof using Hi Hv.
  intros E E1. pose proof (IWiEq_sig_r E) as HS'.
  destruct E as (Hlk & Hlpk & Hlik & (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC) & HXX & HAA & HNN & HDD & HOO & HCC
                 & HX' & HA' & HN' & HD' & HO' & HC').
  destruct E1 as (Hl1 & Hlp1 & Hli1 & _ & HX1 & HA1 & HN1 & HD1 & HO1 & HC1 & HX1' & HA1' & HN1' & HD1' & HO1' & HC1').
  pose proof (lequiv_sym _ _ _ Hlk) as Hkl. pose proof (lequiv_sym _ _ _ Hlpk) as Hkpl.
  pose proof (lequiv_sym _ _ _ Hlik) as Hkli.
  pose proof (IWf_id1 Hi HA HAA HA' Hlk) as Hid1.
  pose proof (IWf_id2 Hi Hv HA HAA HA' Hlk HN HNN HN') as Hid2.
  pose proof (IWi_id3 HA HAA HA' Hlk HN HNN HN' HD HDD HD' Hlpk) as Hid3.
  assert (HΓA : [ G ; Γ ,, A @ l ⊢[ i ] ]) by exact (ext_wf Hi HA Hl).
  assert (EX1 : [ G ; Γ ,, A @ l ⊢[ i ] X'⟨↑⟩ ≅ X⟨↑⟩ @ li ])
    by exact (wk1_eqty G i Hi _ _ _ _ _ _ HΓA (eqty_sym _ _ _ _ _ _ HXX)).
  assert (HΓAN : [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] ])
    by (apply (ext_wf Hi); [apply wft_fin; assumption | exact I]).
  assert (EX2 : [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] X'⟨↑⟩⟨↑⟩ ≅ X⟨↑⟩⟨↑⟩ @ li ])
    by exact (wk1_eqty G i Hi _ _ _ _ _ _ HΓAN EX1).
  assert (HΓAND : [ G ; Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp ⊢[ i ] ]) by exact (ext_wf Hi HD Hlp).
  assert (EX3 : [ G ; Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp ⊢[ i ] X'⟨↑⟩⟨↑⟩⟨↑⟩ ≅ X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ])
    by exact (wk1_eqty G i Hi _ _ _ _ _ _ HΓAND EX2).
  pose proof HS' as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9).
  apply IWiEq_intro; try assumption.
  - exact (lequiv_trans _ _ _ _ Hkl Hl1).
  - exact (lequiv_trans _ _ _ _ Hkpl Hlp1).
  - exact (lequiv_trans _ _ _ _ Hkli Hli1).
  - eapply eqty_lconv; [eapply eqty_trans; [apply eqty_sym, HXX | exact HX1] | exact Hkli].
  - eapply eqty_lconv; [eapply eqty_trans; [apply eqty_sym, HAA | exact HA1] | exact Hkl].
  - apply (mv_eqtm Hi Hid1). eapply eqtm_trans; [apply eqtm_sym, HNN | exact HN1].
  - eapply eqty_lconv; [| exact Hkpl]. apply (mv_eqty Hi Hid2). eapply eqty_trans; [apply eqty_sym, HDD | exact HD1].
  - eapply eqtm_lconv; [| exact Hkli]. apply (mv_eqtm Hi Hid1), (conv_eqtm' Hi (T' := X⟨↑⟩)); [| exact EX1].
    eapply eqtm_trans; [apply eqtm_sym, HOO | exact HO1].
  - eapply eqtm_lconv; [| exact Hkli]. apply (mv_eqtm Hi Hid3), (conv_eqtm' Hi (T' := X⟨↑⟩⟨↑⟩⟨↑⟩)); [| exact EX3].
    eapply eqtm_trans; [apply eqtm_sym, HCC | exact HC1].
  - eapply wft_lconv; [exact HX1' | exact Hkli].
  - eapply wft_lconv; [exact HA1' | exact Hkl].
  - exact (mv_tm Hi Hid1 HN1').
  - eapply wft_lconv; [exact (mv_ty Hi Hid2 HD1') | exact Hkpl].
  - eapply wf_lconv; [| exact Hkli]. exact (mv_tm Hi Hid1 (conv_tm' Hi HO1' EX1)).
  - eapply wf_lconv; [| exact Hkli]. exact (mv_tm Hi Hid3 (conv_tm' Hi HC1' EX3)).
Qed.

Lemma IWiEq_sym {Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C'} :
  IWiEq Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' -> IWiEq Γ k kp ki l lp li X' X A' A N' N D' D Ot' Ot C' C.
Proof using Hi Hv.
  intros E. pose proof E as (_ & _ & _ & HS & _). exact (IWiEq_flip E (IWiEq_refl HS)).
Qed.

Lemma IWiEq_trans {Γ l lp li k kp ki k1 kp1 ki1 X X' X1 A A' A1 N N' N1 D D' D1 Ot Ot' O1 C C' C1} :
  IWiEq Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' ->
  IWiEq Γ k kp ki k1 kp1 ki1 X' X1 A' A1 N' N1 D' D1 Ot' O1 C' C1 ->
  IWiEq Γ l lp li k1 kp1 ki1 X X1 A A1 N N1 D D1 Ot O1 C C1.
Proof using Hi Hv. intros E E1. exact (IWiEq_flip (IWiEq_sym E) E1). Qed.

End IWiAux.
