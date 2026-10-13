(** * Presupposition: indexed finitary trees (M17b)

    The per-former lemmas of [presupposition]'s [IWf] cases, as
    [PresupAux]'s [Wf] section: the equations of the step telescope, the
    signature's weakenings, the right-hand sides of the congruences and
    β's reduct. [elim_IWf]'s congruence states its induction hypotheses'
    types equal, and β its induction hypothesis typed (M17_DESIGN.md), so
    nothing here types [dnth]. *)
From DeLaM.Typing Require Export PresupAux.

(** [PresupAux]' comparison of composite substitutions (local to its section). *)
Ltac teq_core := repeat first [ rewrite ren_as_r2l_ty | rewrite ren_as_r2l ];
  repeat first [ rewrite subst_comp_ty | rewrite subst_comp ];
  first [ apply subst_ext_ty | apply subst_ext
        | apply subst_id_ty; [assumption|] | apply subst_id; [assumption|]
        | symmetry; apply subst_id_ty; [assumption|] | symmetry; apply subst_id; [assumption|] ];
  intros [|[|[|[|[|[|[|[|?n]]]]]]]]; unfold lsucc; pw;
  try solve [apply ren_as_r2l | symmetry; apply ren_as_r2l].

(** ** Equations of the telescope *)

Lemma IWf_E_ot (X : ty) a : nfty X -> X⟨↑⟩[lsingle a] = X.
Proof. apply shift_single_ty. Qed.
Lemma IWf_E_C (X : ty) a : nfty X -> X⟨↑⟩⟨↑⟩[llift (lsingle a)] = X⟨↑⟩.
Proof. intros NX. teq_core. Qed.
Lemma IWf_E_ren (X : ty) : X⟨↑⟩⟨rlift ↑⟩ = X⟨↑⟩⟨↑⟩.
Proof. ren_comm. Qed.
Lemma IWf_E_ren2 (X : ty) : X⟨↑⟩⟨↑⟩⟨rlift (rlift ↑)⟩ = X⟨↑⟩⟨↑⟩⟨↑⟩.
Proof. ren_comm. Qed.
Lemma IWf_E_mot l li (X A : ty) (N Ot C m : tm) : nfty X -> nfty A -> nftm N -> nftm Ot -> nftm C ->
  (tyIWf l li X⟨↑⟩ A⟨↑⟩ N⟨rlift ↑⟩ Ot⟨rlift ↑⟩ C⟨rlift (rlift ↑)⟩ (var 0))[lsingle m] = tyIWf l li X A N Ot C m.
Proof. intros. push_subst. f_equal. all: teq_core. Qed.
Lemma IWf_E5 l li (X A : ty) (N Ot C a : tm) : nfty X -> nfty A -> nftm N -> nftm Ot -> nftm C ->
  (iwfcsty l li X A N Ot C)[lsingle a] = tyDVec (lmax l li) N[lsingle a] (iwfFam l li X A N Ot C a).
Proof. intros. unfold iwfFam. push_subst. f_equal. all: try teq_core. all: f_equal. all: teq_core. Qed.
Lemma IWf_E2fam l li (X A : ty) (N Ot C : tm) :
  iwfFam l li X⟨↑⟩⟨↑⟩⟨↑⟩ A⟨↑⟩⟨↑⟩⟨↑⟩ N⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ Ot⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩
    C⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩ (var 2)
  = (tyIWf l li X⟨↑⟩⟨↑⟩ A⟨↑⟩⟨↑⟩ N⟨rlift ↑⟩⟨rlift ↑⟩ Ot⟨rlift ↑⟩⟨rlift ↑⟩
        C⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩ C)⟨rlift ↑⟩⟨rlift ↑⟩.
Proof. unfold iwfFam. push_ren. f_equal; try teq_core. Qed.
Lemma IWf_E_mot3 l li (X A : ty) (N Ot C : tm) : nfty X -> nfty A -> nftm N -> nftm Ot -> nftm C ->
  (tyIWf l li X⟨↑⟩ A⟨↑⟩ N⟨rlift ↑⟩ Ot⟨rlift ↑⟩ C⟨rlift (rlift ↑)⟩ (var 0))⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩
    [lsingle Ot⟨↑⟩⟨↑⟩]
  = tyIWf l li X⟨↑⟩⟨↑⟩⟨↑⟩ A⟨↑⟩⟨↑⟩⟨↑⟩ N⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ Ot⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩
      C⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩ Ot⟨↑⟩⟨↑⟩.
Proof. intros. push_ren. push_subst. f_equal. all: teq_core. Qed.
Lemma IWf_E6 l li (X A : ty) (N Ot C : tm) (M : ty) a cs h :
  nfty X -> nfty A -> nftm N -> nftm Ot -> nftm C ->
  (iwfstepty l li X A N Ot C M)[lsingle3 a cs h] = M[lsingle2 Ot[lsingle a] (tmSupi l li X A N Ot C a cs)].
Proof.
  intros NX NA NN NO NC.
  set (s := tmSupi l li X⟨↑⟩⟨↑⟩⟨↑⟩ A⟨↑⟩⟨↑⟩⟨↑⟩ N⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ Ot⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩
             C⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩ (var 2) (var 1)).
  assert (Es : s[lsingle3 a cs h] = tmSupi l li X A N Ot C a cs).
  { subst s. push_subst. f_equal; try teq_core; pw. }
  assert (Eo : Ot⟨↑⟩⟨↑⟩[lsingle3 a cs h] = Ot[lsingle a]) by teq_core.
  rewrite subst_comp_ty, !ren_ren_comp_ty,
    (ren_subst_ty M _ _ (lsingle2 Ot[lsingle a] (tmSupi l li X A N Ot C a cs))); auto.
  intros [|[|n]]; pw.
  all: first [exact Es | exact (eq_sym Es) | exact Eo | exact (eq_sym Eo) | idtac].
Qed.

(** The motive's scrutinee type, weakened past one local under its binder. *)
Lemma IWf_mot_ren l li (X A : ty) (N Ot C : tm) :
  (iwfmotty l li X A N Ot C)⟨rlift ↑⟩ = iwfmotty l li X⟨↑⟩ A⟨↑⟩ N⟨rlift ↑⟩ Ot⟨rlift ↑⟩ C⟨rlift (rlift ↑)⟩.
Proof. push_ren. f_equal; ren_comm. Qed.
(** The children's entry, seen from the step's context. *)
Lemma IWf_E_var1 l li (X A : ty) (N Ot C : tm) :
  (iwfcsty l li X A N Ot C)⟨↑⟩⟨↑⟩ =
  tyDVec (lmax l li) (N⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩)[lsingle (var 2)]
    (iwfFam l li X⟨↑⟩⟨↑⟩⟨↑⟩ A⟨↑⟩⟨↑⟩⟨↑⟩ N⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ Ot⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩
       C⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩ (var 2)).
Proof. rewrite Wf_E2, IWf_E2fam. reflexivity. Qed.

Section IWfAux.
Context {G : gctx} {i : layer} (Hi : typeof i = i) (Hv : i <> lV).

(** The signature: the index type, the shapes, the arity, the output
    index and the child index. *)
Definition IWfSig Γ l li X A N Ot C : Prop :=
  lwf (gL G) l /\ lwf (gL G) li /\
  [ G ; Γ ⊢[ i ] X @ li ] /\ [ G ; Γ ⊢[ i ] A @ l ] /\
  [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] /\ [ G ; Γ ,, A @ l ⊢[ i ] Ot : X⟨↑⟩ @ li ] /\
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] C : X⟨↑⟩⟨↑⟩ @ li ].

(** Two signatures along equal components: the left one, the equations, and
    the right components typed in the left contexts. *)
Definition IWfEq Γ l li k ki X X' A A' N N' Ot Ot' C C' : Prop :=
  lequiv (gL G) l k /\ lequiv (gL G) li ki /\ IWfSig Γ l li X A N Ot C /\
  [ G ; Γ ⊢[ i ] X ≅ X' @ li ] /\ [ G ; Γ ⊢[ i ] A ≅ A' @ l ] /\
  [ G ; Γ ,, A @ l ⊢[ i ] N ≅ N' : tyNat @ lzero ] /\ [ G ; Γ ,, A @ l ⊢[ i ] Ot ≅ Ot' : X⟨↑⟩ @ li ] /\
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] C ≅ C' : X⟨↑⟩⟨↑⟩ @ li ] /\
  [ G ; Γ ⊢[ i ] X' @ li ] /\ [ G ; Γ ⊢[ i ] A' @ l ] /\
  [ G ; Γ ,, A @ l ⊢[ i ] N' : tyNat @ lzero ] /\ [ G ; Γ ,, A @ l ⊢[ i ] Ot' : X⟨↑⟩ @ li ] /\
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] C' : X⟨↑⟩⟨↑⟩ @ li ].

(** [IWfEq] with its equations first, so that a proof search solving the
    premises in order fixes the left components from them. *)
Lemma IWfEq_intro {Γ l li k ki X X' A A' N N' Ot Ot' C C'} :
  lequiv (gL G) l k -> lequiv (gL G) li ki ->
  [ G ; Γ ⊢[ i ] X ≅ X' @ li ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N ≅ N' : tyNat @ lzero ] -> [ G ; Γ ,, A @ l ⊢[ i ] Ot ≅ Ot' : X⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] C ≅ C' : X⟨↑⟩⟨↑⟩ @ li ] ->
  lwf (gL G) l -> lwf (gL G) li ->
  [ G ; Γ ⊢[ i ] X @ li ] -> [ G ; Γ ⊢[ i ] A @ l ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] -> [ G ; Γ ,, A @ l ⊢[ i ] Ot : X⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] C : X⟨↑⟩⟨↑⟩ @ li ] ->
  [ G ; Γ ⊢[ i ] X' @ li ] -> [ G ; Γ ⊢[ i ] A' @ l ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N' : tyNat @ lzero ] -> [ G ; Γ ,, A @ l ⊢[ i ] Ot' : X⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] C' : X⟨↑⟩⟨↑⟩ @ li ] ->
  IWfEq Γ l li k ki X X' A A' N N' Ot Ot' C C'.
Proof using. intros. unfold IWfEq, IWfSig. tauto. Qed.

Lemma IWfSig_nf {Γ l li X A N Ot C} : IWfSig Γ l li X A N Ot C ->
  nfty X /\ nfty A /\ nftm N /\ nftm Ot /\ nftm C.
Proof using.
  intros (_ & _ & HX & HA & HN & HO & HC).
  repeat split; first [exact (wf_ty_nf HX) | exact (wf_ty_nf HA) | exact (wf_tm_nf HN)
                      | exact (wf_tm_nf HO) | exact (wf_tm_nf HC)].
Qed.

Lemma IWfSig_ctx {Γ l li X A N Ot C} : IWfSig Γ l li X A N Ot C -> [ G ; Γ ⊢[ i ] ].
Proof using Hi. intros (_ & _ & HX & _). exact (ctx_of_wf_ty Hi HX). Qed.

(** The type at an index. *)
Lemma IWf_ty_wf {Γ l li X A N Ot C m} : IWfSig Γ l li X A N Ot C -> [ G ; Γ ⊢[ i ] m : X @ li ] ->
  [ G ; Γ ⊢[ i ] tyIWf l li X A N Ot C m @ lmax l li ].
Proof using Hi Hv.
  intros (Hl & Hli & HX & HA & HN & HO & HC) Hm. apply wft_iwf; auto using compt_self.
Qed.

(** The output index at a shape. *)
Lemma IWf_ot_wf {Γ l li X A N Ot C a} : IWfSig Γ l li X A N Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] Ot[lsingle a] : X @ li ].
Proof using Hi.
  intros (Hl & Hli & HX & HA & HN & HO & HC) Ha.
  pose proof (wf_tm_single Hi HO Ha) as X0. rewrite IWf_E_ot in X0 by exact (wf_ty_nf HX). exact X0.
Qed.

(** Weakening under one more local. *)
Lemma IWfSig_wk1 {Γ Y ly l li X A N Ot C} : IWfSig Γ l li X A N Ot C -> [ G ; Γ ,, Y @ ly ⊢[ i ] ] ->
  IWfSig (Γ ,, Y @ ly) l li X⟨↑⟩ A⟨↑⟩ N⟨rlift ↑⟩ Ot⟨rlift ↑⟩ C⟨rlift (rlift ↑)⟩.
Proof using Hi Hv.
  intros (Hl & Hli & HX & HA & HN & HO & HC) HΓY.
  assert (HA1 : [ G ; Γ ,, Y @ ly ⊢[ i ] A⟨↑⟩ @ l ]) by exact (wk1_ty G i Hi _ _ _ _ _ HΓY HA).
  assert (HΓYA : [ G ; Γ ,, Y @ ly ,, A⟨↑⟩ @ l ⊢[ i ] ]) by exact (ext_wf Hi HA1 Hl).
  assert (HN1 : [ G ; Γ ,, Y @ ly ,, A⟨↑⟩ @ l ⊢[ i ] N⟨rlift ↑⟩ : tyNat @ lzero ])
    by exact (wk_under_tm Hi HΓYA HN).
  refine (conj Hl (conj Hli (conj (wk1_ty G i Hi _ _ _ _ _ HΓY HX) (conj HA1 (conj HN1 (conj _ _)))))).
  - eapply wf_tm_retype; [exact (wk_under_tm Hi HΓYA HO) | apply IWf_E_ren].
  - assert (HΘ : [ G ; Γ ,, Y @ ly ,, A⟨↑⟩ @ l ,, tyFin N⟨rlift ↑⟩ @ lzero ⊢[ i ] ])
      by (apply (ext_wf Hi); [apply wft_fin; [exact Hv | exact HN1] | exact I]).
    eapply wf_tm_retype; [eapply weakening_r; [exact HC | exact Hi | | exact HΘ] | apply IWf_E_ren2].
    eapply wkr_up'; [eapply wkr_up'; [apply wkr_shift1 | reflexivity] | reflexivity].
Qed.

Lemma IWfEq_wk1 {Γ Y ly l li k ki X X' A A' N N' Ot Ot' C C'} :
  IWfEq Γ l li k ki X X' A A' N N' Ot Ot' C C' -> [ G ; Γ ,, Y @ ly ⊢[ i ] ] ->
  IWfEq (Γ ,, Y @ ly) l li k ki X⟨↑⟩ X'⟨↑⟩ A⟨↑⟩ A'⟨↑⟩ N⟨rlift ↑⟩ N'⟨rlift ↑⟩ Ot⟨rlift ↑⟩ Ot'⟨rlift ↑⟩
    C⟨rlift (rlift ↑)⟩ C'⟨rlift (rlift ↑)⟩.
Proof using Hi Hv.
  intros (Hlk & Hlik & HS & HXX & HAA & HNN & HOO & HCC & HX' & HA' & HN' & HO' & HC') HΓY.
  pose proof (IWfSig_wk1 HS HΓY) as HS1.
  destruct HS as (Hl & Hli & HX & HA & HN & HO & HC).
  assert (HA1 : [ G ; Γ ,, Y @ ly ⊢[ i ] A⟨↑⟩ @ l ]) by exact (wk1_ty G i Hi _ _ _ _ _ HΓY HA).
  assert (HΓYA : [ G ; Γ ,, Y @ ly ,, A⟨↑⟩ @ l ⊢[ i ] ]) by exact (ext_wf Hi HA1 Hl).
  assert (HN1 : [ G ; Γ ,, Y @ ly ,, A⟨↑⟩ @ l ⊢[ i ] N⟨rlift ↑⟩ : tyNat @ lzero ])
    by exact (wk_under_tm Hi HΓYA HN).
  assert (HΘ : [ G ; Γ ,, Y @ ly ,, A⟨↑⟩ @ l ,, tyFin N⟨rlift ↑⟩ @ lzero ⊢[ i ] ])
    by (apply (ext_wf Hi); [apply wft_fin; [exact Hv | exact HN1] | exact I]).
  assert (Hr2 : wkr (rlift (rlift ↑)) (Γ ,, Y @ ly ,, A⟨↑⟩ @ l ,, tyFin N⟨rlift ↑⟩ @ lzero)
                  (Γ ,, A @ l ,, tyFin N @ lzero))
    by (eapply wkr_up'; [eapply wkr_up'; [apply wkr_shift1 | reflexivity] | reflexivity]).
  refine (conj Hlk (conj Hlik (conj HS1 _))).
  repeat split.
  - exact (wk1_eqty G i Hi _ _ _ _ _ _ HΓY HXX).
  - exact (wk1_eqty G i Hi _ _ _ _ _ _ HΓY HAA).
  - exact (wk_under_eqtm Hi HΓYA HNN).
  - eapply eq_tm_retype; [exact (wk_under_eqtm Hi HΓYA HOO) | apply IWf_E_ren].
  - eapply eq_tm_retype; [eapply weakening_r; [exact HCC | exact Hi | exact Hr2 | exact HΘ] | apply IWf_E_ren2].
  - exact (wk1_ty G i Hi _ _ _ _ _ HΓY HX').
  - exact (wk1_ty G i Hi _ _ _ _ _ HΓY HA').
  - exact (wk_under_tm Hi HΓYA HN').
  - eapply wf_tm_retype; [exact (wk_under_tm Hi HΓYA HO') | apply IWf_E_ren].
  - eapply wf_tm_retype; [eapply weakening_r; [exact HC' | exact Hi | exact Hr2 | exact HΘ] | apply IWf_E_ren2].
Qed.

(** Moving a judgment along the identity between converted contexts. *)
Lemma mv_ty {Δ Δ' T k} : [ G ; Δ' ⊢[ i ] lshift 0 : Δ ] -> [ G ; Δ ⊢[ i ] T @ k ] -> [ G ; Δ' ⊢[ i ] T @ k ].
Proof using Hi.
  intros Hid H. pose proof (wf_ty_subst Hi H Hid) as X. rewrite nf_id_ty in X by exact (wf_ty_nf H). exact X.
Qed.
Lemma mv_tm {Δ Δ' t T k} : [ G ; Δ' ⊢[ i ] lshift 0 : Δ ] -> [ G ; Δ ⊢[ i ] t : T @ k ] ->
  [ G ; Δ' ⊢[ i ] t : T @ k ].
Proof using Hi.
  intros Hid H. pose proof (wf_tm_subst Hi H Hid) as X.
  rewrite nf_id in X by exact (wf_tm_nf H). rewrite nf_id_ty in X by exact (wf_tm_nf_ty H). exact X.
Qed.
Lemma mv_eqty {Δ Δ' T T' k} : [ G ; Δ' ⊢[ i ] lshift 0 : Δ ] -> [ G ; Δ ⊢[ i ] T ≅ T' @ k ] ->
  [ G ; Δ' ⊢[ i ] T ≅ T' @ k ].
Proof using Hi.
  intros Hid H. pose proof (eqty_subst Hi H Hid) as X.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 typed_nf)))) _ _ _ _ _ _ H) as [N1 N2].
  rewrite !nf_id_ty in X by assumption. exact X.
Qed.

(** The identity from a converted shape entry, and from a converted arity
    under it. *)
Lemma IWf_id1 {Γ l k A A'} : [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ⊢[ i ] A' @ l ] -> lequiv (gL G) l k ->
  [ G ; Γ ,, A' @ k ⊢[ i ] lshift 0 : Γ ,, A @ l ].
Proof using Hi.
  intros HA HAA HA' Hlk.
  assert (Hid0 : [ G ; Γ ⊢[ i ] lshift 0 : Γ ]) by (eapply lsub_wf_id; eauto using ctx_of_wf_ty).
  exact (proj2 (ctx_conv_ext Hi Hid0 HA HAA HA' Hlk)).
Qed.
Lemma IWf_id2 {Γ l k A A' N N'} : [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ⊢[ i ] A' @ l ] -> lequiv (gL G) l k ->
  [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] -> [ G ; Γ ,, A @ l ⊢[ i ] N ≅ N' : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N' : tyNat @ lzero ] ->
  [ G ; Γ ,, A' @ k ,, tyFin N' @ lzero ⊢[ i ] lshift 0 : Γ ,, A @ l ,, tyFin N @ lzero ].
Proof using Hi Hv.
  intros HA HAA HA' Hlk HN HNN HN'.
  pose proof (IWf_id1 HA HAA HA' Hlk) as Hid1.
  refine (proj2 (ctx_conv_ext Hi Hid1 _ _ _ (lequiv_refl (gL G) lzero I))).
  - apply wft_fin; assumption.
  - apply eqty_fin; assumption.
  - apply wft_fin; assumption.
Qed.

(** The right signature, in its own contexts. *)
Lemma IWfEq_sig_r {Γ l li k ki X X' A A' N N' Ot Ot' C C'} :
  IWfEq Γ l li k ki X X' A A' N N' Ot Ot' C C' -> IWfSig Γ k ki X' A' N' Ot' C'.
Proof using Hi Hv.
  intros (Hlk & Hlik & (Hl & Hli & HX & HA & HN & HO & HC) & HXX & HAA & HNN & HOO & HCC
          & HX' & HA' & HN' & HO' & HC').
  pose proof (lequiv_wf_r _ _ _ Hlk) as Hk. pose proof (lequiv_wf_r _ _ _ Hlik) as Hki.
  pose proof (ctx_of_wf_ty Hi HA) as HΓ.
  pose proof (IWf_id1 HA HAA HA' Hlk) as Hid1.
  pose proof (IWf_id2 HA HAA HA' Hlk HN HNN HN') as Hid2.
  assert (HΓA : [ G ; Γ ,, A @ l ⊢[ i ] ]) by exact (ext_wf Hi HA Hl).
  assert (EX1 : [ G ; Γ ,, A @ l ⊢[ i ] X'⟨↑⟩ ≅ X⟨↑⟩ @ li ])
    by exact (wk1_eqty G i Hi _ _ _ _ _ _ HΓA (eqty_sym _ _ _ _ _ _ HXX)).
  assert (HΓAN : [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] ])
    by (apply (ext_wf Hi); [apply wft_fin; assumption | exact I]).
  assert (EX2 : [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] X'⟨↑⟩⟨↑⟩ ≅ X⟨↑⟩⟨↑⟩ @ li ])
    by exact (wk1_eqty G i Hi _ _ _ _ _ _ HΓAN EX1).
  refine (conj Hk (conj Hki (conj _ (conj _ (conj _ (conj _ _)))))).
  - eapply wft_lconv; [exact HX' | apply lequiv_sym, Hlik].
  - eapply wft_lconv; [exact HA' | apply lequiv_sym, Hlk].
  - exact (mv_tm Hid1 HN').
  - eapply wf_lconv; [| apply lequiv_sym, Hlik]. exact (mv_tm Hid1 (conv_tm' Hi HO' EX1)).
  - eapply wf_lconv; [| apply lequiv_sym, Hlik]. exact (mv_tm Hid2 (conv_tm' Hi HC' EX2)).
Qed.

(** The types along equal components. *)
Lemma IWf_ty_eq {Γ l li k ki X X' A A' N N' Ot Ot' C C' m m'} :
  IWfEq Γ l li k ki X X' A A' N N' Ot Ot' C C' -> [ G ; Γ ⊢[ i ] m ≅ m' : X @ li ] ->
  [ G ; Γ ⊢[ i ] tyIWf l li X A N Ot C m ≅ tyIWf k ki X' A' N' Ot' C' m' @ lmax l li ].
Proof using Hi Hv.
  intros (Hlk & Hlik & (Hl & Hli & HX & HA & HN & HO & HC) & HXX & HAA & HNN & HOO & HCC & _) Hmm.
  apply eqty_iwf; auto using compt_self.
Qed.

Lemma pre_iwf_r {Γ l li k ki X X' A A' N N' Ot Ot' C C' m'} :
  IWfEq Γ l li k ki X X' A A' N N' Ot Ot' C C' -> [ G ; Γ ⊢[ i ] m' : X @ li ] ->
  [ G ; Γ ⊢[ i ] tyIWf k ki X' A' N' Ot' C' m' @ lmax l li ].
Proof using Hi Hv.
  intros HE Hm'. pose proof (IWfEq_sig_r HE) as HS'.
  destruct HE as (Hlk & Hlik & _ & HXX & _).
  eapply wft_lconv; [| apply lequiv_max; [exact Hlk | exact Hlik]].
  apply (IWf_ty_wf HS').
  eapply wf_lconv; [eapply (conv_tm' Hi); [exact Hm' | exact (eqty_sym _ _ _ _ _ _ HXX)] | apply lequiv_sym, Hlik].
Qed.

(** An instance at equal shapes, for the output index and the arity. *)
Lemma IWf_single_eq {Γ A B N N' a a' l k} : nfty B ->
  [ G ; Γ ,, A @ l ⊢[ i ] N : B⟨↑⟩ @ k ] -> [ G ; Γ ,, A @ l ⊢[ i ] N ≅ N' : B⟨↑⟩ @ k ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] a' : A @ l ] -> [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] N[lsingle a] ≅ N'[lsingle a'] : B @ k ].
Proof using Hi.
  intros NB HN HNN Ha Ha' Haa. eapply eqtm_trans.
  - pose proof (wf_tm_func Hi HN (lsub_eq_single Hi Ha Ha' Haa)) as X. rewrite IWf_E_ot in X by exact NB. exact X.
  - pose proof (eqtm_subst Hi HNN (lsub_wf_single G i Hi _ _ _ _ (ctx_of_wf_tm Hi Ha') Ha')) as X.
    rewrite IWf_E_ot in X by exact NB. exact X.
Qed.

(** The children's family at a shape, and along equal components. *)
Lemma IWf_fam_wf {Γ l li X A N Ot C a} : IWfSig Γ l li X A N Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] iwfFam l li X A N Ot C a @ lmax l li ].
Proof using Hi Hv.
  intros HS Ha. pose proof HS as (Hl & Hli & HX & HA & HN & HO & HC).
  assert (HNa : [ G ; Γ ⊢[ i ] N[lsingle a] : tyNat @ lzero ]) by exact (wf_tm_single Hi HN Ha).
  assert (HΓ1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] ])
    by (apply (ext_wf Hi); [apply wft_fin; assumption | exact I]).
  unfold iwfFam. apply (IWf_ty_wf (IWfSig_wk1 HS HΓ1)).
  assert (Hd : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] llift (lsingle a) : Γ ,, A @ l ,, tyFin N @ lzero ])
    by (eapply (lsub_wf_lift' G i Hi); [exact (lsub_wf_single G i Hi _ _ _ _ (ctx_of_wf_tm Hi Ha) Ha)
                                        | apply wft_fin; assumption | exact I | reflexivity]).
  pose proof (wf_tm_subst Hi HC Hd) as X0. rewrite IWf_E_C in X0 by exact (wf_ty_nf HX). exact X0.
Qed.

Lemma IWf_fam_eq {Γ l li k ki X X' A A' N N' Ot Ot' C C' a a'} :
  IWfEq Γ l li k ki X X' A A' N N' Ot Ot' C C' ->
  [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] a' : A @ l ] -> [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] ->
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ]
      iwfFam l li X A N Ot C a ≅ iwfFam k ki X' A' N' Ot' C' a' @ lmax l li ].
Proof using Hi Hv.
  intros HE Ha Ha' Haa. pose proof HE as (Hlk & Hlik & HS & HXX & HAA & HNN & HOO & HCC & HX' & HA' & HN' & HO' & HC').
  pose proof HS as (Hl & Hli & HX & HA & HN & HO & HC).
  assert (HNa : [ G ; Γ ⊢[ i ] N[lsingle a] : tyNat @ lzero ]) by exact (wf_tm_single Hi HN Ha).
  assert (HΓ1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] ])
    by (apply (ext_wf Hi); [apply wft_fin; assumption | exact I]).
  assert (HΓ : [ G ; Γ ⊢[ i ] ]) by exact (ctx_of_wf_tm Hi Ha).
  assert (HFa : [ G ; Γ ⊢[ i ] tyFin N[lsingle a] @ lzero ]) by (apply wft_fin; assumption).
  assert (EFa : [ G ; Γ ⊢[ i ] (tyFin N)[lsingle a] ≅ (tyFin N)[lsingle a'] @ lzero ])
    by (cbn; apply eqty_fin; [exact Hv | exact (IWf_single_eq (B := tyNat) I HN (eqtm_refl _ _ _ _ _ _ HN) Ha Ha' Haa)]).
  assert (Edd : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] llift (lsingle a) ≅ llift (lsingle a')
                  : Γ ,, A @ l ,, tyFin N @ lzero ])
    by (eapply (lsub_eq_lift Hi); [exact (lsub_eq_single Hi Ha Ha' Haa) | exact HFa | exact I | exact EFa | reflexivity]).
  unfold iwfFam. apply (IWf_ty_eq (IWfEq_wk1 HE HΓ1)).
  eapply eqtm_trans.
  - pose proof (eqtm_subst Hi HCC (lsub_eq_l Edd)) as X0. rewrite IWf_E_C in X0 by exact (wf_ty_nf HX). exact X0.
  - pose proof (wf_tm_func Hi HC' Edd) as X0. rewrite IWf_E_C in X0 by exact (wf_ty_nf HX). exact X0.
Qed.

(** [sup_i]'s children's type, and along equal components. *)
Lemma IWf_csa_wf {Γ l li X A N Ot C a} : IWfSig Γ l li X A N Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] tyDVec (lmax l li) N[lsingle a] (iwfFam l li X A N Ot C a) @ lmax l li ].
Proof using Hi Hv.
  intros HS Ha. pose proof HS as (Hl & Hli & HX & HA & HN & HO & HC).
  apply wft_dvec; auto using compt_self, lwf_max.
  - exact (wf_tm_single Hi HN Ha).
  - exact (IWf_fam_wf HS Ha).
Qed.

Lemma IWf_csa_eq {Γ l li k ki X X' A A' N N' Ot Ot' C C' a a'} :
  IWfEq Γ l li k ki X X' A A' N N' Ot Ot' C C' ->
  [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] a' : A @ l ] -> [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] tyDVec (lmax l li) N[lsingle a] (iwfFam l li X A N Ot C a)
      ≅ tyDVec (lmax k ki) N'[lsingle a'] (iwfFam k ki X' A' N' Ot' C' a') @ lmax l li ].
Proof using Hi Hv.
  intros HE Ha Ha' Haa. pose proof HE as (Hlk & Hlik & HS & HXX & HAA & HNN & _).
  pose proof HS as (Hl & Hli & HX & HA & HN & HO & HC).
  apply eqty_dvec; auto using compt_self.
  - apply lequiv_max; assumption.
  - exact (wf_tm_single Hi HN Ha).
  - exact (IWf_single_eq (B := tyNat) I HN HNN Ha Ha' Haa).
  - exact (IWf_fam_wf HS Ha).
  - exact (IWf_fam_eq HE Ha Ha' Haa).
Qed.

(** [sup_i]'s type, and its congruence's right-hand side. *)
Lemma pre_supi_ty {Γ l li X A N Ot C a} : IWfSig Γ l li X A N Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] tyIWf l li X A N Ot C Ot[lsingle a] @ lmax l li ].
Proof using Hi Hv. intros HS Ha. exact (IWf_ty_wf HS (IWf_ot_wf HS Ha)). Qed.

Lemma pre_supi_r {Γ l li k ki X X' A A' N N' Ot Ot' C C' a a' cs'} :
  IWfEq Γ l li k ki X X' A A' N N' Ot Ot' C C' ->
  [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] a' : A @ l ] -> [ G ; Γ ⊢[ i ] a ≅ a' : A @ l ] ->
  [ G ; Γ ⊢[ i ] cs' : tyDVec (lmax l li) N[lsingle a] (iwfFam l li X A N Ot C a) @ lmax l li ] ->
  [ G ; Γ ⊢[ i ] tmSupi k ki X' A' N' Ot' C' a' cs' : tyIWf l li X A N Ot C Ot[lsingle a] @ lmax l li ].
Proof using Hi Hv.
  intros HE Ha Ha' Haa Hcs'. pose proof (IWfEq_sig_r HE) as HS'.
  pose proof HE as (Hlk & Hlik & HS & HXX & HAA & HNN & HOO & _ & _ & _ & _ & HO' & _).
  pose proof HS as (Hl & Hli & HX & HA & HN & HO & HC).
  assert (HLK : lequiv (gL G) (lmax l li) (lmax k ki)) by (apply lequiv_max; assumption).
  assert (Ha'k : [ G ; Γ ⊢[ i ] a' : A' @ k ])
    by (eapply wf_lconv; [eapply (conv_tm' Hi); [exact Ha' | exact (eqty_sym _ _ _ _ _ _ HAA)] | apply lequiv_sym, Hlk]).
  assert (Hcs'k : [ G ; Γ ⊢[ i ] cs' : tyDVec (lmax k ki) N'[lsingle a'] (iwfFam k ki X' A' N' Ot' C' a') @ lmax k ki ])
    by (eapply wf_lconv; [eapply (conv_tm' Hi); [exact Hcs' | exact (eqty_sym _ _ _ _ _ _ (IWf_csa_eq HE Ha Ha' Haa))]
                         | apply lequiv_sym, HLK]).
  pose proof HS' as (Hk & Hki & HX'' & HA'' & HN'' & HO'' & HC'').
  eapply wf_lconv; [| exact HLK].
  eapply (conv_tm' Hi); [apply wf_supi; auto using compt_self |].
  eapply eqty_lconv; [| apply lequiv_sym, HLK].
  eapply (IWf_ty_eq HE).
  eapply IWf_single_eq; [exact (wf_ty_nf HX) | exact HO | exact HOO | exact Ha | exact Ha' | exact Haa].
Qed.

(** The type at equal indices. *)
Lemma IWf_ty_eq_idx {Γ l li X A N Ot C m m'} : IWfSig Γ l li X A N Ot C ->
  [ G ; Γ ⊢[ i ] m ≅ m' : X @ li ] ->
  [ G ; Γ ⊢[ i ] tyIWf l li X A N Ot C m ≅ tyIWf l li X A N Ot C m' @ lmax l li ].
Proof using Hi Hv.
  intros (Hl & Hli & HX & HA & HN & HO & HC) Hmm.
  apply eqty_iwf; auto using compt_self, lequiv_refl, eqty_refl, eqtm_refl.
Qed.

(** The identity back from a converted shape entry. *)
Lemma IWf_id1_rev {Γ l k A A'} : [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ⊢[ i ] A' @ l ] -> lequiv (gL G) l k ->
  [ G ; Γ ,, A @ l ⊢[ i ] lshift 0 : Γ ,, A' @ k ].
Proof using Hi.
  intros HA HAA HA' Hlk. pose proof (lequiv_sym _ _ _ Hlk) as Hkl.
  apply (IWf_id1 (l := k) (k := l)); [eapply wft_lconv; [exact HA' | exact Hkl]
                                     | apply eqty_sym; eapply eqty_lconv; [exact HAA | exact Hkl]
                                     | eapply wft_lconv; [exact HA | exact Hkl] | exact Hkl].
Qed.

(** The motive's scrutinee type, and along equal components. *)
Lemma IWf_var0 {Γ X l} : [ G ; Γ ,, X @ l ⊢[ i ] ] -> [ G ; Γ ,, X @ l ⊢[ i ] var 0 : X⟨↑⟩ @ l ].
Proof using Hi. intros H. apply wf_var; [rewrite Hi; exact H | constructor]. Qed.

Lemma IWf_mot_wf {Γ l li X A N Ot C} : IWfSig Γ l li X A N Ot C ->
  [ G ; Γ ,, X @ li ⊢[ i ] iwfmotty l li X A N Ot C @ lmax l li ].
Proof using Hi Hv.
  intros HS. pose proof HS as (Hl & Hli & HX & _).
  pose proof (ext_wf Hi HX Hli) as HΓX.
  exact (IWf_ty_wf (IWfSig_wk1 HS HΓX) (IWf_var0 HΓX)).
Qed.

Lemma IWf_mot_eq {Γ l li k ki X X' A A' N N' Ot Ot' C C'} :
  IWfEq Γ l li k ki X X' A A' N N' Ot Ot' C C' ->
  [ G ; Γ ,, X @ li ⊢[ i ] iwfmotty l li X A N Ot C ≅ iwfmotty k ki X' A' N' Ot' C' @ lmax l li ].
Proof using Hi Hv.
  intros HE. pose proof HE as (_ & _ & (Hl & Hli & HX & _) & _).
  pose proof (ext_wf Hi HX Hli) as HΓX.
  exact (IWf_ty_eq (IWfEq_wk1 HE HΓX) (eqtm_refl _ _ _ _ _ _ (IWf_var0 HΓX))).
Qed.

Lemma IWf_mot_r {Γ l li k ki X X' A A' N N' Ot Ot' C C'} :
  IWfEq Γ l li k ki X X' A A' N N' Ot Ot' C C' ->
  [ G ; Γ ,, X @ li ⊢[ i ] iwfmotty k ki X' A' N' Ot' C' @ lmax l li ].
Proof using Hi Hv.
  intros HE. pose proof HE as (Hlk & Hlik & (Hl & Hli & HX & _) & HXX & _ & _ & _ & _ & HX' & _).
  pose proof (ext_wf Hi HX Hli) as HΓX.
  exact (mv_ty (IWf_id1_rev HX HXX HX' Hlik) (wft_lconv _ _ _ _ _ _ (IWf_mot_wf (IWfEq_sig_r HE)) (lequiv_max _ _ _ _ _ Hlk Hlik))).
Qed.

(** The children's tuple type in the shape's context, and along equal
    components. *)
Lemma IWf_cs_wf {Γ l li X A N Ot C} : IWfSig Γ l li X A N Ot C ->
  [ G ; Γ ,, A @ l ⊢[ i ] iwfcsty l li X A N Ot C @ lmax l li ].
Proof using Hi Hv.
  intros HS. pose proof HS as (Hl & Hli & HX & HA & HN & HO & HC).
  pose proof (ext_wf Hi HA Hl) as HΓA.
  assert (HΓAF : [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] ])
    by (apply (ext_wf Hi); [apply wft_fin; assumption | exact I]).
  apply wft_dvec; auto using compt_self, lwf_max.
  exact (IWf_ty_wf (IWfSig_wk1 (IWfSig_wk1 HS HΓA) HΓAF) HC).
Qed.

Lemma IWf_cs_eq {Γ l li k ki X X' A A' N N' Ot Ot' C C'} :
  IWfEq Γ l li k ki X X' A A' N N' Ot Ot' C C' ->
  [ G ; Γ ,, A @ l ⊢[ i ] iwfcsty l li X A N Ot C ≅ iwfcsty k ki X' A' N' Ot' C' @ lmax l li ].
Proof using Hi Hv.
  intros HE. pose proof HE as (Hlk & Hlik & HS & HXX & HAA & HNN & HOO & HCC & _).
  pose proof HS as (Hl & Hli & HX & HA & HN & HO & HC).
  pose proof (ext_wf Hi HA Hl) as HΓA.
  assert (HΓAF : [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] ])
    by (apply (ext_wf Hi); [apply wft_fin; assumption | exact I]).
  apply eqty_dvec; auto using compt_self, lequiv_max.
  - exact (IWf_ty_wf (IWfSig_wk1 (IWfSig_wk1 HS HΓA) HΓAF) HC).
  - exact (IWf_ty_eq (IWfEq_wk1 (IWfEq_wk1 HE HΓA) HΓAF) HCC).
Qed.

Lemma IWf_cs_r {Γ l li k ki X X' A A' N N' Ot Ot' C C'} :
  IWfEq Γ l li k ki X X' A A' N N' Ot Ot' C C' ->
  [ G ; Γ ,, A @ l ⊢[ i ] iwfcsty k ki X' A' N' Ot' C' @ lmax l li ].
Proof using Hi Hv.
  intros HE. pose proof HE as (Hlk & Hlik & (Hl & Hli & HX & HA & _) & _ & HAA & _ & _ & _ & _ & HA' & _).
  exact (mv_ty (IWf_id1_rev HA HAA HA' Hlk) (wft_lconv _ _ _ _ _ _ (IWf_cs_wf (IWfEq_sig_r HE)) (lequiv_max _ _ _ _ _ Hlk Hlik))).
Qed.

(** The motive weakened past one local, under its two binders. *)
Lemma IWf_M_wk1 {Γ Y ly l li X A N Ot C M l'} : IWfSig Γ l li X A N Ot C -> [ G ; Γ ,, Y @ ly ⊢[ i ] ] ->
  [ G ; Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, Y @ ly ,, X⟨↑⟩ @ li ,, iwfmotty l li X⟨↑⟩ A⟨↑⟩ N⟨rlift ↑⟩ Ot⟨rlift ↑⟩ C⟨rlift (rlift ↑)⟩ @ lmax l li
      ⊢[ i ] M⟨rlift (rlift ↑)⟩ @ l' ].
Proof using Hi Hv.
  intros HS HΓY HM. pose proof (IWfSig_wk1 HS HΓY) as HS1. pose proof HS as (Hl & Hli & _).
  eapply weakening_r; [exact HM | exact Hi | | apply (ext_wf Hi); [exact (IWf_mot_wf HS1) | exact (lwf_max Hl Hli)]].
  eapply wkr_up'; [eapply wkr_up'; [apply wkr_shift1 | reflexivity] | symmetry; apply IWf_mot_ren].
Qed.
Lemma IWf_M_wk1_eq {Γ Y ly l li X A N Ot C M M' l'} : IWfSig Γ l li X A N Ot C -> [ G ; Γ ,, Y @ ly ⊢[ i ] ] ->
  [ G ; Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li ⊢[ i ] M ≅ M' @ l' ] ->
  [ G ; Γ ,, Y @ ly ,, X⟨↑⟩ @ li ,, iwfmotty l li X⟨↑⟩ A⟨↑⟩ N⟨rlift ↑⟩ Ot⟨rlift ↑⟩ C⟨rlift (rlift ↑)⟩ @ lmax l li
      ⊢[ i ] M⟨rlift (rlift ↑)⟩ ≅ M'⟨rlift (rlift ↑)⟩ @ l' ].
Proof using Hi Hv.
  intros HS HΓY HM. pose proof (IWfSig_wk1 HS HΓY) as HS1. pose proof HS as (Hl & Hli & _).
  eapply weakening_r; [exact HM | exact Hi | | apply (ext_wf Hi); [exact (IWf_mot_wf HS1) | exact (lwf_max Hl Hli)]].
  eapply wkr_up'; [eapply wkr_up'; [apply wkr_shift1 | reflexivity] | symmetry; apply IWf_mot_ren].
Qed.

(** The step's type along equal components, in the left telescope (with
    any induction-hypothesis entry). *)
Lemma IWf_step_eq {Γ l li k ki X X' A A' N N' Ot Ot' C C' M M' l' I lI} :
  IWfEq Γ l li k ki X X' A A' N N' Ot Ot' C C' ->
  [ G ; Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li ⊢[ i ] M ≅ M' @ l' ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ,, I @ lI ⊢[ i ] ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ,, I @ lI ⊢[ i ]
      iwfstepty l li X A N Ot C M ≅ iwfstepty k ki X' A' N' Ot' C' M' @ l' ].
Proof using Hi Hv.
  intros HE HM HMM HΘ. pose proof (ctx_pre HΘ) as H2. pose proof (ctx_pre H2) as H1.
  pose proof HE as (Hlk & Hlik & HS & _).
  pose proof (IWfSig_wk1 (IWfSig_wk1 (IWfSig_wk1 HS H1) H2) HΘ) as HS3.
  pose proof (IWfEq_wk1 (IWfEq_wk1 (IWfEq_wk1 HE H1) H2) HΘ) as HE3.
  pose proof (IWfSig_nf HS3) as (NX & NA & NN & NO & NC).
  pose proof HS3 as (Hl & Hli & HX & HA & HN & HO & HC).
  pose proof HE3 as (_ & _ & _ & HXX & HAA & HNN & HOO & HCC & HX' & HA' & HN' & HO' & HC').
  assert (Hv2 : [ G ; _ ⊢[ i ] var 2 : A⟨↑⟩⟨↑⟩⟨↑⟩ @ l ]) by (apply wf_var; [rewrite Hi; exact HΘ | do 3 constructor]).
  assert (Hv1 : [ G ; _ ⊢[ i ] var 1 : tyDVec (lmax l li) (N⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩)[lsingle (var 2)]
                    (iwfFam l li X⟨↑⟩⟨↑⟩⟨↑⟩ A⟨↑⟩⟨↑⟩⟨↑⟩ N⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ Ot⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩
                       C⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩ (var 2)) @ lmax l li ])
    by (eapply wf_tm_retype; [apply wf_var; [rewrite Hi; exact HΘ | do 2 constructor] | apply IWf_E_var1]).
  pose proof (wf_supi _ _ _ _ _ _ _ _ _ _ _ _ (compt_self Hi Hv) Hl Hli HX HA HN HO HC Hv2 Hv1) as Hs.
  pose proof (pre_supi_r HE3 Hv2 Hv2 (eqtm_refl _ _ _ _ _ _ Hv2) Hv1) as Hs'.
  pose proof (eqtm_supi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (compt_self Hi Hv) Hlk Hlik HX HXX HA HAA HN HNN HO HOO HC HCC
                (eqtm_refl _ _ _ _ _ _ Hv2) (eqtm_refl _ _ _ _ _ _ Hv1)) as Hss.
  pose proof (IWf_ot_wf HS3 Hv2) as Ho.
  pose proof (IWf_single_eq NX HO HOO Hv2 Hv2 (eqtm_refl _ _ _ _ _ _ Hv2)) as Hoo.
  pose proof (wf_tm_single Hi HO' Hv2) as Ho'. rewrite IWf_E_ot in Ho' by exact NX.
  rewrite ?Wf_E2 in Hs, Hs', Hss, Ho, Hoo, Ho'. rewrite (Wf_E2 Ot') in Hoo.
  pose proof (IWf_M_wk1 (IWfSig_wk1 (IWfSig_wk1 HS H1) H2) HΘ
                (IWf_M_wk1 (IWfSig_wk1 HS H1) H2 (IWf_M_wk1 HS H1 HM))) as HM3.
  pose proof (IWf_M_wk1_eq (IWfSig_wk1 (IWfSig_wk1 HS H1) H2) HΘ
                (IWf_M_wk1_eq (IWfSig_wk1 HS H1) H2 (IWf_M_wk1_eq HS H1 HMM))) as HMM3.
  assert (Hs'o : [ G ; _ ⊢[ i ] tmSupi k ki X'⟨↑⟩⟨↑⟩⟨↑⟩ A'⟨↑⟩⟨↑⟩⟨↑⟩ N'⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩
                    Ot'⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ C'⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩ (var 2) (var 1)
                    : tyIWf l li X⟨↑⟩⟨↑⟩⟨↑⟩ A⟨↑⟩⟨↑⟩⟨↑⟩ N⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ Ot⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩
                        C⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩ Ot'⟨↑⟩⟨↑⟩ @ lmax l li ])
    by exact (conv_tm' Hi Hs' (eqty_sym' (IWf_ty_eq_idx HS3 Hoo))).
  eapply eqty_trans.
  - eapply (wf_ty_func Hi HM3). eapply (lsub_eq_single2 Hi Ho Ho' Hoo); rewrite IWf_E_mot by assumption; [exact Hs | exact Hs'o | exact Hss].
  - apply (eqty_subst Hi HMM3). apply (lsub_wf_single2' Hi HΘ Ho'). rewrite IWf_E_mot by assumption. exact Hs'o.
Qed.

(** [elim_IWf]'s type. *)
Lemma pre_elimIWf_ty {Γ l li X A N Ot C M l' m t} : IWfSig Γ l li X A N Ot C ->
  [ G ; Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ⊢[ i ] m : X @ li ] -> [ G ; Γ ⊢[ i ] t : tyIWf l li X A N Ot C m @ lmax l li ] ->
  [ G ; Γ ⊢[ i ] M[lsingle2 m t] @ l' ].
Proof using Hi Hv.
  intros HS HM Hm Ht. pose proof (IWfSig_nf HS) as (NX & NA & NN & NO & NC).
  eapply (wf_ty_subst Hi HM). apply (lsub_wf_single2' Hi (ctx_of_wf_tm Hi Hm) Hm).
  rewrite IWf_E_mot by assumption. exact Ht.
Qed.

(** [elim_IWf]'s congruence, right-hand side: the primed telescope is
    formed, the motive, the induction hypothesis's type and the step moved
    into it along the identity, and the type converted. *)
Lemma pre_elimIWf_r {Γ l li l' k ki k' X X' A A' N N' Ot Ot' C C' M M' c' m m' t t'} :
  IWfEq Γ l li k ki X X' A A' N N' Ot Ot' C C' -> lequiv (gL G) l' k' ->
  [ G ; Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li ⊢[ i ] M ≅ M' @ l' ] ->
  [ G ; Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li ⊢[ i ] M' @ l' ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ⊢[ i ] iwfihty l li l' X A N Ot C M @ lmax lzero l' ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ⊢[ i ]
      iwfihty l li l' X A N Ot C M ≅ iwfihty k ki k' X' A' N' Ot' C' M' @ lmax lzero l' ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ⊢[ i ] iwfihty k ki k' X' A' N' Ot' C' M' @ lmax lzero l' ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ,, iwfihty l li l' X A N Ot C M @ lmax lzero l'
      ⊢[ i ] c' : iwfstepty l li X A N Ot C M @ l' ] ->
  [ G ; Γ ⊢[ i ] m : X @ li ] -> [ G ; Γ ⊢[ i ] m' : X @ li ] -> [ G ; Γ ⊢[ i ] m ≅ m' : X @ li ] ->
  [ G ; Γ ⊢[ i ] t : tyIWf l li X A N Ot C m @ lmax l li ] ->
  [ G ; Γ ⊢[ i ] t' : tyIWf l li X A N Ot C m @ lmax l li ] ->
  [ G ; Γ ⊢[ i ] t ≅ t' : tyIWf l li X A N Ot C m @ lmax l li ] ->
  [ G ; Γ ⊢[ i ] tmElimIWf k ki k' X' A' N' Ot' C' M' c' m' t' : M[lsingle2 m t] @ l' ].
Proof using Hi Hv.
  intros HE H' HM HMM HM' HI EI HI' Hc' Hm Hm' Hmm Ht Ht' Htt.
  pose proof (IWfEq_sig_r HE) as HS'.
  pose proof HE as (Hlk & Hlik & HS & HXX & HAA & HNN & HOO & HCC & HX' & HA' & HN' & HO' & HC').
  pose proof HS as (Hl & Hli & HX & HA & HN & HO & HC).
  pose proof HS' as (Hk & Hki & HX'' & HA'' & HN'' & HO'' & HC'').
  pose proof (IWfSig_nf HS) as (NX & NA & NN & NO & NC).
  pose proof (lequiv_wf_l _ _ _ H') as Hl'. pose proof (lequiv_wf_r _ _ _ H') as Hk'.
  pose proof (ctx_of_wf_ty Hi HX) as HΓ.
  assert (HLK : lequiv (gL G) (lmax l li) (lmax k ki)) by (apply lequiv_max; assumption).
  assert (HLI : lequiv (gL G) (lmax lzero l') (lmax lzero k'))
    by (apply lequiv_max; [apply lequiv_refl; exact I | exact H']).
  (* the motive *)
  pose proof (proj2 (ctx_conv_ext Hi (IWf_id1 HX HXX HX' Hlik) (IWf_mot_wf HS) (IWf_mot_eq HE) (IWf_mot_r HE) HLK))
    as Hidm.
  assert (HM'p : [ G ; Γ ,, X' @ ki ,, iwfmotty k ki X' A' N' Ot' C' @ lmax k ki ⊢[ i ] M' @ k' ])
    by (eapply wft_lconv; [exact (mv_ty Hidm HM') | exact (lequiv_sym _ _ _ H')]).
  (* the induction hypothesis's type and the step *)
  pose proof (proj2 (ctx_conv_ext Hi (IWf_id1 HA HAA HA' Hlk) (IWf_cs_wf HS) (IWf_cs_eq HE) (IWf_cs_r HE) HLK))
    as Hid2.
  assert (HI'p : [ G ; Γ ,, A' @ k ,, iwfcsty k ki X' A' N' Ot' C' @ lmax k ki ⊢[ i ]
                   iwfihty k ki k' X' A' N' Ot' C' M' @ lmax lzero k' ])
    by (eapply wft_lconv; [exact (mv_ty Hid2 HI') | exact (lequiv_sym _ _ _ HLI)]).
  pose proof (proj2 (ctx_conv_ext Hi Hid2 HI EI HI' HLI)) as Hid3.
  assert (HΘ : [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ,, iwfihty l li l' X A N Ot C M @ lmax lzero l' ⊢[ i ] ])
    by (apply (ext_wf Hi); [exact HI | apply lwf_max; [exact I | exact Hl']]).
  pose proof (IWf_step_eq HE HM HMM HΘ) as ES.
  assert (Hc'p : [ G ; Γ ,, A' @ k ,, iwfcsty k ki X' A' N' Ot' C' @ lmax k ki ,, iwfihty k ki k' X' A' N' Ot' C' M' @ lmax lzero k'
                   ⊢[ i ] c' : iwfstepty k ki X' A' N' Ot' C' M' @ k' ]).
  { pose proof (wf_tm_subst Hi Hc' Hid3) as X0.
    pose proof (eqty_subst Hi ES Hid3) as Y0.
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 typed_nf)))) _ _ _ _ _ _ ES) as [N1 N2].
    rewrite nf_id in X0 by exact (wf_tm_nf Hc').
    rewrite (nf_id_ty (iwfstepty l li X A N Ot C M)) in X0, Y0 by exact N1.
    rewrite (nf_id_ty (iwfstepty k ki X' A' N' Ot' C' M')) in Y0 by exact N2.
    eapply wf_lconv; [eapply (conv_tm' Hi); [exact X0 | exact (eqty_sym' Y0)] | exact (lequiv_sym _ _ _ H')]. }
  (* the index and the scrutinee *)
  assert (Hm'p : [ G ; Γ ⊢[ i ] m' : X' @ ki ])
    by (eapply wf_lconv; [exact (conv_tm' Hi Hm' (eqty_sym' HXX)) | exact (lequiv_sym _ _ _ Hlik)]).
  assert (Ht'p : [ G ; Γ ⊢[ i ] t' : tyIWf k ki X' A' N' Ot' C' m' @ lmax k ki ])
    by (eapply wf_lconv; [exact (conv_tm' Hi Ht' (eqty_sym' (IWf_ty_eq HE Hmm))) | exact (lequiv_sym _ _ _ HLK)]).
  assert (Ht'm : [ G ; Γ ⊢[ i ] t' : tyIWf l li X A N Ot C m' @ lmax l li ])
    by exact (conv_tm' Hi Ht' (eqty_sym' (IWf_ty_eq_idx HS Hmm))).
  eapply wf_lconv with (l' := k'); [| exact H'].
  eapply (conv_tm' Hi (T' := M'[lsingle2 m' t'])).
  - apply wf_elimIWf; auto using compt_self.
    + exact (IWf_mot_wf HS').
    + exact (IWf_cs_wf HS').
  - eapply eqty_lconv; [| apply lequiv_sym, H'].
    eapply eqty_trans.
    + eapply (wf_ty_func Hi HM). eapply (lsub_eq_single2 Hi Hm Hm' Hmm); rewrite IWf_E_mot by assumption; [exact Ht | exact Ht'm | exact Htt].
    + apply (eqty_subst Hi HMM). apply (lsub_wf_single2' Hi HΓ Hm'). rewrite IWf_E_mot by assumption. exact Ht'm.
Qed.

(** β: the left-hand side, and the reduct at the motive's instance. *)
Lemma pre_elimIWf_beta_l {Γ l li l' X A N Ot C M c a cs} : IWfSig Γ l li X A N Ot C -> lwf (gL G) l' ->
  [ G ; Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ⊢[ i ] iwfihty l li l' X A N Ot C M @ lmax lzero l' ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ,, iwfihty l li l' X A N Ot C M @ lmax lzero l'
      ⊢[ i ] c : iwfstepty l li X A N Ot C M @ l' ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] cs : tyDVec (lmax l li) N[lsingle a] (iwfFam l li X A N Ot C a) @ lmax l li ] ->
  [ G ; Γ ⊢[ i ] tmElimIWf l li l' X A N Ot C M c Ot[lsingle a] (tmSupi l li X A N Ot C a cs)
      : M[lsingle2 Ot[lsingle a] (tmSupi l li X A N Ot C a cs)] @ l' ].
Proof using Hi Hv.
  intros HS Hl' HM HI Hc Ha Hcs. pose proof HS as (Hl & Hli & HX & HA & HN & HO & HC).
  apply wf_elimIWf; auto using compt_self.
  - exact (IWf_mot_wf HS).
  - exact (IWf_cs_wf HS).
  - exact (IWf_ot_wf HS Ha).
  - apply wf_supi; auto using compt_self.
Qed.

Lemma pre_elimIWf_beta_ty {Γ l li X A N Ot C M l' a cs} : IWfSig Γ l li X A N Ot C ->
  [ G ; Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] cs : tyDVec (lmax l li) N[lsingle a] (iwfFam l li X A N Ot C a) @ lmax l li ] ->
  [ G ; Γ ⊢[ i ] M[lsingle2 Ot[lsingle a] (tmSupi l li X A N Ot C a cs)] @ l' ].
Proof using Hi Hv.
  intros HS HM Ha Hcs. pose proof HS as (Hl & Hli & HX & HA & HN & HO & HC).
  apply (pre_elimIWf_ty HS HM (IWf_ot_wf HS Ha)). apply wf_supi; auto using compt_self.
Qed.

Lemma pre_elimIWf_beta {Γ l li l' X A N Ot C M c a cs} : IWfSig Γ l li X A N Ot C ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ,, iwfihty l li l' X A N Ot C M @ lmax lzero l'
      ⊢[ i ] c : iwfstepty l li X A N Ot C M @ l' ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] cs : tyDVec (lmax l li) N[lsingle a] (iwfFam l li X A N Ot C a) @ lmax l li ] ->
  [ G ; Γ ⊢[ i ] iwfIH l li l' X A N Ot C M c a cs : (iwfihty l li l' X A N Ot C M)[lsingle2 a cs] @ lmax lzero l' ] ->
  [ G ; Γ ⊢[ i ] c[lsingle3 a cs (iwfIH l li l' X A N Ot C M c a cs)]
      : M[lsingle2 Ot[lsingle a] (tmSupi l li X A N Ot C a cs)] @ l' ].
Proof using Hi Hv.
  intros HS Hc Ha Hcs HIH. pose proof (IWfSig_nf HS) as (NX & NA & NN & NO & NC).
  pose proof HS as (Hl & Hli & HX & HA & HN & HO & HC).
  rewrite <- (IWf_E6 l li X A N Ot C M a cs (iwfIH l li l' X A N Ot C M c a cs)) by assumption.
  eapply (wf_tm_subst Hi Hc). unfold lsingle3, lsingle2.
  apply lsub_wf_cons; [apply lsub_wf_cons; [apply lsub_wf_cons |] |].
  - eapply lsub_wf_id; eauto using ctx_of_wf_tm.
  - rewrite nf_id_ty by exact NA. exact Ha.
  - change (lcons (lshift 0) a) with (lsingle a). rewrite IWf_E5 by assumption. exact Hcs.
  - change (lcons (lcons (lshift 0) a) cs) with (lsingle2 a cs). exact HIH.
Qed.

End IWfAux.
