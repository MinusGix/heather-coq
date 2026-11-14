(** * The relation at [IWf]: syntax in Kripke worlds, and the signature
      in a world (M17b)

    What the laws of [IWfRel] (symmetry, transitivity, weakening) share:
    the formers and the canonical positions commute with a world, the
    children's family [iwfFamT] meets [DVec]'s head and tail, and
    [IWfEq] holds in every world. *)
From DeLaM.LogRel Require Export Escape.
From DeLaM.Typing Require Export DVecEq.

Lemma gwa_tyIWf γ l li X A N Ot C m :
  (tyIWf l li X A N Ot C m)⟦γ⟧ = tyIWf l li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧ m⟦γ⟧.
Proof. now destruct γ. Qed.
Lemma gwa_supi γ l li X A N Ot C a cs :
  (tmSupi l li X A N Ot C a cs)⟦γ⟧ = tmSupi l li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧ a⟦γ⟧ cs⟦γ⟧.
Proof. now destruct γ. Qed.

Section IWfAux.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

Lemma ren_wk_comp_lift2 (t : tm) (ρ ρ' : wk) :
  t⟨rlift (rlift ρ)⟩⟨rlift (rlift ρ')⟩ = t⟨rlift (rlift (wk_comp ρ' ρ))⟩.
Proof using .
  apply ren_ren; intros [|[|n]]; rewrite ?rlk_rlift; cbn; rewrite ?rlk_rlift; auto. now rewrite rlk_wk_comp.
Qed.
Lemma ktmll_comp {G Γ} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) t :
  ktmll (kw_comp ρ ρ') t = ktmll ρ' (ktmll ρ t).
Proof using . unfold ktmll; rewrite kw_γ_comp, kw_r_comp. now rewrite gwa_ren, gwa_comp_tm, ren_wk_comp_lift2. Qed.

(** ** The children's family *)

(** At a position, and moved to the tail. *)
Lemma iwfFamT_single l li (X A : ty) (N Ot C c p : tm) : nfty X -> nfty A -> nftm N -> nftm Ot -> nftm C ->
  (iwfFamT l li X A N Ot C c)[lsingle p] = tyIWf l li X A N Ot C c[lsingle p].
Proof using . intros. unfold iwfFamT. push_subst. f_equal. all: teq_core. Qed.

Lemma iwfFamT_mv l li (X A : ty) (N Ot C c m : tm) :
  dvecMv m (iwfFamT l li X A N Ot C c) = iwfFamT l li X A N Ot C (posMv m c).
Proof using . unfold dvecMv, iwfFamT, posMv, posTl. push_ren. push_subst. f_equal. all: teq_core. Qed.

(** [C] at a shape, then at a position. *)
Lemma llift_single_single (C a p : tm) : nftm a -> C[llift (lsingle a)][lsingle p] = C[lsingle2 a p].
Proof using .
  intros Ha. apply subst_subst. intros [|[|n]]; cbn; rewrite ?llk_llift; cbn; auto.
  - change (ren_tm ?x ?r) with x⟨r⟩. now rewrite shift_single by exact Ha.
  - replace (n + 0 + 1) with (S n) by lia. cbn. now rewrite !Nat.add_0_r.
Qed.

(** A family moved to the tail, at a position. *)
Lemma posMv_single m (c p : tm) : nftm m ->
  (posMv m c)[lsingle p] = c[lsingle (posTl m p)].
Proof using .
  intros Hm. unfold posMv, posTl.
  rewrite (subst_subst _ _ _ (lcons (lsingle p) (tmInr lzero lzero (tyUnit lzero) (tyFin m) p))).
  - apply ren_subst. intros [|k]; rlk_simpl; cbn; reflexivity.
  - intros [|k]; cbn; [| now rewrite Nat.add_0_r].
    change (subst_tm ?x ?d) with x[d]. now rewrite shift_single.
Qed.

Section KwIWf.
Context {G : gctx} {Γ : ctx} (ρ : kwk G Γ).

Lemma kty_tyIWf l li X A N Ot C m :
  kty ρ (tyIWf l li X A N Ot C m) = tyIWf l li (kty ρ X) (kty ρ A) (ktml ρ N) (ktml ρ Ot) (ktmll ρ C) (ktm ρ m).
Proof using . unfold kty, ktm, ktml, ktmll; now rewrite gwa_tyIWf. Qed.
Lemma ktm_supi l li X A N Ot C a cs :
  ktm ρ (tmSupi l li X A N Ot C a cs) =
  tmSupi l li (kty ρ X) (kty ρ A) (ktml ρ N) (ktml ρ Ot) (ktmll ρ C) (ktm ρ a) (ktm ρ cs).
Proof using . unfold kty, ktm, ktml, ktmll; now rewrite gwa_supi. Qed.

Lemma ktm_posHd m : ktm ρ (posHd m) = posHd (ktm ρ m).
Proof using . unfold posHd. rewrite ktm_inl, kty_tyUnit, kty_tyFin. unfold ktm. now rewrite gwa_triv. Qed.
Lemma ktm_posTl m p : ktm ρ (posTl m p) = posTl (ktm ρ m) (ktm ρ p).
Proof using . unfold posTl. now rewrite ktm_inr, kty_tyUnit, kty_tyFin. Qed.

Lemma ktyl_shift' (T : ty) : ktyl ρ T⟨↑⟩ = (kty ρ T)⟨↑⟩.
Proof using . unfold kty, ktyl. now rewrite gwa_ren_ty, shift_lift_ty. Qed.

(** The child index at a shape, in a world. *)
Lemma ktmll_llift_single (C a : tm) : (ktmll ρ C)[llift (lsingle (ktm ρ a))] = ktml ρ C[llift (lsingle a)].
Proof using .
  unfold ktmll, ktml, ktm. rewrite gwa_subst.
  rewrite (subst_ext _ (llift (lsingle a))⟦kw_γ ρ⟧ (llift (lsingle a)⟦kw_γ ρ⟧)) by apply llk_llift_gwa.
  rewrite gwa_lsingle, llift_lsingle_ren. reflexivity.
Qed.

Lemma ktml_posMv m c : ktml ρ (posMv m c) = posMv (ktm ρ m) (ktml ρ c).
Proof using .
  unfold posMv, posTl, ktml, ktm.
  rewrite gwa_subst, gwa_lsingle, lsingle_ren, gwa_ren, liftshift_lift. f_equal. f_equal.
  unfold gwa; destruct (kw_γ ρ); cbn; f_equal; f_equal;
    change (ren_tm ?x ?r) with x⟨r⟩; rewrite ?shift_lift; try reflexivity.
  all: change (gren_tm ?x ?y) with x⟪y⟫; rewrite gren_ren, shift_lift; reflexivity.
Qed.

Lemma ktml_posMv_single m c p : nftm m ->
  (ktml ρ (posMv m c))[lsingle p] = (ktml ρ c)[lsingle (posTl (ktm ρ m) p)].
Proof using . intros Hm. rewrite ktml_posMv. apply posMv_single. unfold ktm; apply ren_nf. Qed.

(** ** The signature in a world *)

Lemma kw_wkr_ll {A l N} :
  wkr (rlift (rlift (kw_r ρ))) (kw_Δ ρ ,, kty ρ A @ l ,, tyFin (ktml ρ N) @ lzero)
    ((Γ ,, A @ l ,, tyFin N @ lzero)⟦kw_γ ρ⟧).
Proof using . rewrite gwa_cext, gwa_tyFin. eapply wkr_up'; [exact (kw_wkr_l ρ) | reflexivity]. Qed.

Lemma kw_tm_l' {A l t T l'} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l ->
  [ G ; Γ ,, A @ l ⊢g t : T @ l' ] -> [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ⊢g ktml ρ t : ktyl ρ T @ l' ].
Proof using . intros HA Hl H. exact (kw_tm_l ρ HA Hl H). Qed.
Lemma kw_eqtm_l {A l t t' T l'} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l ->
  [ G ; Γ ,, A @ l ⊢g t ≅ t' : T @ l' ] ->
  [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ⊢g ktml ρ t ≅ ktml ρ t' : ktyl ρ T @ l' ].
Proof using .
  intros HA Hl H. eapply weakening_r; [exact (gwa_eqtm (kw_gok ρ) (kw_glob ρ) H) | exact ge_typeof
                                      | exact (kw_wkr_l ρ) | exact (kw_ext ρ HA Hl)].
Qed.

Lemma kw_ext2 {A l N} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l -> [ G ; Γ ,, A @ l ⊢g N : tyNat @ lzero ] ->
  [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ,, tyFin (ktml ρ N) @ lzero ⊢g ].
Proof using .
  intros HA Hl HN. apply ext_wf_g; [| exact I]. apply wft_fin; [exact ge_notV|].
  exact (kw_tm_nat_l ρ HA Hl HN).
Qed.

Lemma kw_tm_ll {A l N t T l'} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l -> [ G ; Γ ,, A @ l ⊢g N : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢g t : T @ l' ] ->
  [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ,, tyFin (ktml ρ N) @ lzero ⊢g ktmll ρ t : T⟦kw_γ ρ⟧⟨rlift (rlift (kw_r ρ))⟩ @ l' ].
Proof using .
  intros HA Hl HN H. eapply weakening_r; [exact (gwa_tm (kw_gok ρ) (kw_glob ρ) H) | exact ge_typeof
                                         | exact kw_wkr_ll | exact (kw_ext2 HA Hl HN)].
Qed.
Lemma kw_eqtm_ll {A l N t t' T l'} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l -> [ G ; Γ ,, A @ l ⊢g N : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢g t ≅ t' : T @ l' ] ->
  [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ,, tyFin (ktml ρ N) @ lzero ⊢g ktmll ρ t ≅ ktmll ρ t'
      : T⟦kw_γ ρ⟧⟨rlift (rlift (kw_r ρ))⟩ @ l' ].
Proof using .
  intros HA Hl HN H. eapply weakening_r; [exact (gwa_eqtm (kw_gok ρ) (kw_glob ρ) H) | exact ge_typeof
                                         | exact kw_wkr_ll | exact (kw_ext2 HA Hl HN)].
Qed.

(** The generic equivalence under one and two binders. *)
Lemma kw_geq_tm_l {A l t t' T l'} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l ->
  [ G ; Γ ,, A @ l ⊢ t ≈ t' : T @ l' ] ->
  [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ⊢ ktml ρ t ≈ ktml ρ t' : ktyl ρ T @ l' ].
Proof using EL.
  intros HA Hl H. exact (geq_tm_wk (kw_wkr_l ρ) (kw_ext ρ HA Hl) (geq_tm_gwa (kw_gok ρ) (kw_glob ρ) H)).
Qed.
Lemma kw_geq_tm_ll {A l N t t' T l'} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l -> [ G ; Γ ,, A @ l ⊢g N : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢ t ≈ t' : T @ l' ] ->
  [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ,, tyFin (ktml ρ N) @ lzero ⊢ ktmll ρ t ≈ ktmll ρ t'
      : T⟦kw_γ ρ⟧⟨rlift (rlift (kw_r ρ))⟩ @ l' ].
Proof using EL.
  intros HA Hl HN H. exact (geq_tm_wk kw_wkr_ll (kw_ext2 HA Hl HN) (geq_tm_gwa (kw_gok ρ) (kw_glob ρ) H)).
Qed.

Lemma ktyll_shift2 (T : ty) : T⟨↑⟩⟨↑⟩⟦kw_γ ρ⟧⟨rlift (rlift (kw_r ρ))⟩ = (kty ρ T)⟨↑⟩⟨↑⟩.
Proof using . unfold kty. now rewrite !gwa_ren_ty, !shift_lift_ty. Qed.

Lemma IWfEq_kw {l li k ki X X' A A' N N' Ot Ot' C C'} :
  IWfEq (G := G) (i := ge_layer) Γ l li k ki X X' A A' N N' Ot Ot' C C' ->
  IWfEq (G := kw_G ρ) (i := ge_layer) (kw_Δ ρ) l li k ki (kty ρ X) (kty ρ X') (kty ρ A) (kty ρ A')
    (ktml ρ N) (ktml ρ N') (ktml ρ Ot) (ktml ρ Ot') (ktmll ρ C) (ktmll ρ C').
Proof using .
  intros (Hlk & Hlik & (Hl & Hli & HX & HA & HN & HO & HC) & HXX & HAA & HNN & HOO & HCC
          & HX' & HA' & HN' & HO' & HC').
  pose proof (kw_eqtm_l HA Hl HNN) as HNN1. unfold ktyl in HNN1. rewrite gwa_tyNat in HNN1.
  change (tyNat⟨?r⟩) with tyNat in HNN1.
  pose proof (kw_eqtm_l HA Hl HOO) as HOO1. fold (ktyl ρ X⟨↑⟩) in HOO1. rewrite ktyl_shift' in HOO1.
  pose proof (kw_tm_l' HA Hl HO) as HO1. rewrite ktyl_shift' in HO1.
  pose proof (kw_tm_l' HA Hl HO') as HO1'. rewrite ktyl_shift' in HO1'.
  pose proof (kw_eqtm_ll HA Hl HN HCC) as HCC1. rewrite ktyll_shift2 in HCC1.
  pose proof (kw_tm_ll HA Hl HN HC) as HC1. rewrite ktyll_shift2 in HC1.
  pose proof (kw_tm_ll HA Hl HN HC') as HC1'. rewrite ktyll_shift2 in HC1'.
  apply IWfEq_intro; auto using kw_lequiv, kw_lwf, kw_ty, kw_eqty, kw_tm_nat_l.
Qed.

End KwIWf.

(** Kripke worlds composed under a shape: the arity and the child index. *)
Lemma ktm_comp_single {G Γ} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) (N a : tm) :
  ktm ρ' (ktml ρ N)[lsingle (ktm ρ a)] = (ktml (kw_comp ρ ρ') N)[lsingle (ktm (kw_comp ρ ρ') a)].
Proof using . now rewrite ktm_single, ktml_comp, ktm_comp. Qed.

Lemma ktml_comp_child {G Γ} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) (C a p : tm) :
  (ktml ρ' (ktmll ρ C)[llift (lsingle (ktm ρ a))])[lsingle p] =
  (ktmll (kw_comp ρ ρ') C)[lsingle2 (ktm (kw_comp ρ ρ') a) p].
Proof using .
  rewrite <- ktmll_llift_single, <- ktmll_comp, <- ktm_comp.
  apply llift_single_single. unfold ktm; apply ren_nf.
Qed.

Lemma kw_tmred_succ {G Γ k m} : [ G ; Γ ⊢g k ⤳* succ m : tyNat @ lzero ] ->
  forall ρ : kwk G Γ, [ kw_G ρ ; kw_Δ ρ ⊢g ktm ρ k ⤳* succ (ktm ρ m) : tyNat @ lzero ].
Proof using . intros H ρ. pose proof (kw_tmred ρ H) as R. rewrite ktm_succ, kty_tyNat in R. exact R. Qed.

(** The predecessors of two lengths related in every world are. *)
Lemma NatRel_kw_pred {G Γ k k' m m'} :
  (forall ρ : kwk G Γ, NatRel (kw_G ρ) (kw_Δ ρ) (ktm ρ k) (ktm ρ k')) ->
  [ G ; Γ ⊢g k ⤳* succ m : tyNat @ lzero ] -> [ G ; Γ ⊢g k' ⤳* succ m' : tyNat @ lzero ] ->
  forall ρ : kwk G Γ, NatRel (kw_G ρ) (kw_Δ ρ) (ktm ρ m) (ktm ρ m').
Proof using EL.
  intros HW Hk Hk' ρ.
  pose proof (kw_tmred_succ Hk ρ) as R. pose proof (kw_tmred_succ Hk' ρ) as R'.
  destruct (NatRel_inv_succ (HW ρ) R) as (m2 & R2 & Hm).
  assert (Es : succ m2 = succ (ktm ρ m')) by (eapply tmred_whnf_det; [exact R2 | exact R' | constructor ..]).
  injection Es as ->. exact Hm.
Qed.

End IWfAux.

Lemma liftshift_single_var (t : tm) : nftm t -> t⟨rlift ↑⟩[lsingle (var 0)] = t.
Proof.
  intros Ht. rewrite (ren_subst _ _ _ (lshift 0)).
  - apply subst_id; auto. intros; cbn; f_equal; lia.
  - intros [|n]; rlk_simpl; cbn; f_equal; lia.
Qed.

(** ** The children's types, generically equal (M17b)

    The spine's projections are annotated generically ([DVecISp]), so
    moving a spine to another family (symmetry, transitivity, levels)
    needs the two families' heads and tails generically equal: by the
    former's congruence at the child indices, which the index relation's
    escape gives at related positions. *)
Section IWfGeq.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

(** Families under [Fin n] moved to [Fin w] at [n ≅ w]. *)
Lemma fin_stab_eqty {G Γ n w T T' L} : [ G ; Γ ⊢g n ≅ w : tyNat @ lzero ] ->
  [ G ; Γ ,, tyFin n @ lzero ⊢g T ≅ T' @ L ] -> [ G ; Γ ,, tyFin w @ lzero ⊢g T ≅ T' @ L ].
Proof using .
  intros Ek H. refine (stab_eqty ge_typeof _ (lequiv_refl (gL G) lzero I) _ H).
  - apply eqty_fin; [exact ge_notV | exact Ek].
  - apply ext_wf_g; [| exact I]. apply wft_fin; [exact ge_notV |]. exact (eqtm_wf_r ge_typeof Ek).
Qed.

Lemma iwfFamT_nf l li X A N Ot C c : nfty (iwfFamT l li X A N Ot C c) -> nftm c.
Proof using . unfold iwfFamT; cbn; tauto. Qed.

(** The components of two signatures, generically equal. *)
Definition IWfGeq G Γ l li (X X' A A' : ty) (N N' Ot Ot' C C' : tm) :=
  [ G ; Γ ⊢ X ≈ X' @ li ] /\ [ G ; Γ ⊢ A ≈ A' @ l ] /\ [ G ; Γ ,, A @ l ⊢ N ≈ N' : tyNat @ lzero ] /\
  [ G ; Γ ,, A @ l ⊢ Ot ≈ Ot' : X⟨↑⟩ @ li ] /\ [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢ C ≈ C' : X⟨↑⟩⟨↑⟩ @ li ].

Lemma IWfGeq_kw {G Γ l li k ki X X' A A' N N' Ot Ot' C C'} (ρ : kwk G Γ) :
  IWfEq (G := G) (i := ge_layer) Γ l li k ki X X' A A' N N' Ot Ot' C C' ->
  IWfGeq G Γ l li X X' A A' N N' Ot Ot' C C' ->
  IWfGeq (kw_G ρ) (kw_Δ ρ) l li (kty ρ X) (kty ρ X') (kty ρ A) (kty ρ A')
    (ktml ρ N) (ktml ρ N') (ktml ρ Ot) (ktml ρ Ot') (ktmll ρ C) (ktmll ρ C').
Proof using EL.
  intros (_ & _ & (Hl & Hli & HX & HA & HN & _) & _) (GX & GA & GN & GO & GC).
  refine (conj (kw_geq_ty ρ GX) (conj (kw_geq_ty ρ GA) (conj (kw_geq_nat_l ρ HA Hl GN) (conj _ _)))).
  - pose proof (kw_geq_tm_l ρ HA Hl GO) as Y. rewrite ktyl_shift' in Y. exact Y.
  - pose proof (kw_geq_tm_ll ρ HA Hl HN GC) as Y. rewrite ktyll_shift2 in Y. exact Y.
Qed.

(** The formers at generically equal indices. *)
Lemma iwf_geq_at {G Γ l li k ki X X' A A' N N' Ot Ot' C C' c c'} :
  IWfEq (G := G) (i := ge_layer) Γ l li k ki X X' A A' N N' Ot Ot' C C' ->
  IWfGeq G Γ l li X X' A A' N N' Ot Ot' C C' ->
  [ G ; Γ ⊢ c ≈ c' : X @ li ] ->
  [ G ; Γ ⊢ tyIWf l li X A N Ot C c ≈ tyIWf k ki X' A' N' Ot' C' c' @ lmax l li ].
Proof using EL.
  intros (Hlk & Hlik & (Hl & Hli & HX & HA & HN & HO & HC) & _) (GX & GA & GN & GO & GC) Hc.
  exact (geq_ty_iwf Hlk Hlik HX GX HA GA HN GN HO GO HC GC Hc).
Qed.

(** The children's [DVec] types at related lengths, along families whose
    child indices are generically equal at related positions in every
    world: by induction on the lengths' relation, the head by the
    former's congruence, the tail along the moved families, and at a
    neutral length the family itself, at the position variable. *)
Lemma iwf_dvec_geq {G Γ l li k ki X X' A A' N N' Ot Ot' C C'} :
  IWfEq (G := G) (i := ge_layer) Γ l li k ki X X' A A' N N' Ot Ot' C C' ->
  IWfGeq G Γ l li X X' A A' N N' Ot Ot' C C' ->
  forall n n', NatRel G Γ n n' -> forall c c',
  [ G ; Γ ,, tyFin n @ lzero ⊢g iwfFamT l li X A N Ot C c ≅ iwfFamT k ki X' A' N' Ot' C' c' @ lmax l li ] ->
  (forall (ρ : kwk G Γ) p p', PosRel (kw_G ρ) (kw_Δ ρ) (ktm ρ n) (ktm ρ n') p p' ->
     [ kw_G ρ ; kw_Δ ρ ⊢ (ktml ρ c)[lsingle p] ≈ (ktml ρ c')[lsingle p'] : kty ρ X @ li ]) ->
  [ G ; Γ ⊢ tyDVec (lmax l li) n (iwfFamT l li X A N Ot C c)
      ≈ tyDVec (lmax k ki) n' (iwfFamT k ki X' A' N' Ot' C' c') @ lmax l li ].
Proof using EL.
  intros HE HG.
  pose proof HE as (Hlk & Hlik & (Wl & Wli & HX & HA & HN & HO & HC) & _ & _ & _ & _ & _
                    & HX' & HA' & HN' & HO' & HC').
  assert (HL : lwf (gL G) (lmax l li)) by (split; assumption).
  assert (HLL : lequiv (gL G) (lmax l li) (lmax k ki)) by now apply lequiv_max.
  assert (HL' : lwf (gL G) (lmax k ki)) by exact (lequiv_wf_r _ _ _ HLL).
  assert (Step : forall n n' w w' T T', [ G ; Γ ⊢g n ⤳* w : tyNat @ lzero ] -> [ G ; Γ ⊢g n' ⤳* w' : tyNat @ lzero ] ->
            [ G ; Γ ⊢g n ≅ n' : tyNat @ lzero ] -> [ G ; Γ ,, tyFin n @ lzero ⊢g T ≅ T' @ lmax l li ] ->
            [ G ; Γ ⊢ tyDVec (lmax l li) w T ≈ tyDVec (lmax k ki) w' T' @ lmax l li ] ->
            [ G ; Γ ⊢ tyDVec (lmax l li) n T ≈ tyDVec (lmax k ki) n' T' @ lmax l li ]).
  { intros n n' w w' T T' Hn Hn' Enn HT H.
    assert (HT' : [ G ; Γ ,, tyFin n' @ lzero ⊢g T' @ lmax k ki ]).
    { eapply wft_lconv; [| exact (lequiv_sym _ _ _ HLL)].
      exact (eqty_wf_r ge_typeof (fin_stab_eqty Enn HT)). }
    eapply geq_ty_exp; [exact (tyred_dvec HL (eqty_wf_l ge_typeof HT) Hn) | | exact H].
    exact (tyred_lconv _ _ _ _ (tyred_dvec HL' HT' Hn') HLL). }
  apply (NatRel_mut G Γ
    (fun n n' _ => forall c c',
       [ G ; Γ ,, tyFin n @ lzero ⊢g iwfFamT l li X A N Ot C c ≅ iwfFamT k ki X' A' N' Ot' C' c' @ lmax l li ] ->
       (forall (ρ : kwk G Γ) p p', PosRel (kw_G ρ) (kw_Δ ρ) (ktm ρ n) (ktm ρ n') p p' ->
          [ kw_G ρ ; kw_Δ ρ ⊢ (ktml ρ c)[lsingle p] ≈ (ktml ρ c')[lsingle p'] : kty ρ X @ li ]) ->
       [ G ; Γ ⊢ tyDVec (lmax l li) n (iwfFamT l li X A N Ot C c)
           ≈ tyDVec (lmax k ki) n' (iwfFamT k ki X' A' N' Ot' C' c') @ lmax l li ])
    (fun w w' _ => forall n n', [ G ; Γ ⊢g n ⤳* w : tyNat @ lzero ] -> [ G ; Γ ⊢g n' ⤳* w' : tyNat @ lzero ] ->
       forall c c',
       [ G ; Γ ,, tyFin n @ lzero ⊢g iwfFamT l li X A N Ot C c ≅ iwfFamT k ki X' A' N' Ot' C' c' @ lmax l li ] ->
       (forall (ρ : kwk G Γ) p p', PosRel (kw_G ρ) (kw_Δ ρ) (ktm ρ n) (ktm ρ n') p p' ->
          [ kw_G ρ ; kw_Δ ρ ⊢ (ktml ρ c)[lsingle p] ≈ (ktml ρ c')[lsingle p'] : kty ρ X @ li ]) ->
       [ G ; Γ ⊢ tyDVec (lmax l li) n (iwfFamT l li X A N Ot C c)
           ≈ tyDVec (lmax k ki) n' (iwfFamT k ki X' A' N' Ot' C' c') @ lmax l li ])).
  - intros t t' w w' Ht Ht' _ _ IH. exact (IH t t' Ht Ht').
  - (* zero *)
    intros n n' Hn Hn' c c' HF _.
    pose proof (tmred_eq _ _ _ _ _ _ _ Hn) as En. pose proof (tmred_eq _ _ _ _ _ _ _ Hn') as En'.
    assert (Enn : [ G ; Γ ⊢g n ≅ n' : tyNat @ lzero ]) by (eapply eqtm_trans; [exact En | apply eqtm_sym, En']).
    apply (Step n n' zero zero _ _ Hn Hn' Enn HF).
    pose proof (fin_stab_eqty En HF) as HF0.
    assert (HF0' : [ G ; Γ ,, tyFin zero @ lzero ⊢g iwfFamT k ki X' A' N' Ot' C' c' @ lmax k ki ])
      by (eapply wft_lconv; [exact (eqty_wf_r ge_typeof HF0) | exact (lequiv_sym _ _ _ HLL)]).
    eapply geq_ty_exp; [exact (tyred_dvec_zero HL (eqty_wf_l ge_typeof HF0))
                       | exact (tyred_lconv _ _ _ _ (tyred_dvec_zero HL' HF0') HLL) |].
    exact (geq_ty_unit (ctx_of_tm (eqtm_wf_l ge_typeof En)) HLL).
  - (* successor *)
    intros s s' Hss IH n n' Hn Hn' c c' HF HP.
    pose proof (tmred_eq _ _ _ _ _ _ _ Hn) as En. pose proof (tmred_eq _ _ _ _ _ _ _ Hn') as En'.
    pose proof (geq_tm_sound (NatRel_geq Hss)) as Es.
    assert (Enn : [ G ; Γ ⊢g n ≅ n' : tyNat @ lzero ]).
    { eapply eqtm_trans; [exact En | eapply eqtm_trans; [apply eqtm_succ; [exact ge_notV | exact Es] | apply eqtm_sym, En']]. }
    pose proof (eqtm_wf_l ge_typeof Es) as Hs. pose proof (eqtm_wf_r ge_typeof Es) as Hs'.
    pose proof (ctx_of_tm Hs) as HΓ.
    apply (Step n n' (succ s) (succ s') _ _ Hn Hn' Enn HF).
    pose proof (fin_stab_eqty En HF) as HF1. pose proof (eqty_wf_l ge_typeof HF1) as HF1w.
    assert (HF1' : [ G ; Γ ,, tyFin (succ s') @ lzero ⊢g iwfFamT k ki X' A' N' Ot' C' c' @ lmax k ki ]).
    { eapply wft_lconv; [| exact (lequiv_sym _ _ _ HLL)].
      assert (Y : [ G ; Γ ⊢g n ≅ succ s' : tyNat @ lzero ]) by (eapply eqtm_trans; [exact Enn | exact En']).
      exact (eqty_wf_r ge_typeof (fin_stab_eqty Y HF)). }
    eapply geq_ty_exp; [exact (tyred_dvec_succ HL HF1w Hs) | exact (tyred_lconv _ _ _ _ (tyred_dvec_succ HL' HF1' Hs') HLL) |].
    assert (HH : [ G ; Γ ⊢g dvecHd s (iwfFamT l li X A N Ot C c) @ lmax l li ])
      by exact (wf_ty_single ge_typeof HF1w (fin_inl_wf ge_typeof ge_notV ge_compt Hs)).
    assert (HΓH : [ G ; Γ ,, dvecHd s (iwfFamT l li X A N Ot C c) @ lmax l li ⊢g ]) by exact (ext_wf_g HH HL).
    eapply geq_ty_lconv; [apply geq_ty_sig; [exact HLL | exact HLL | exact HH | |] | apply lequiv_sym, lmax_idem, HL].
    + rewrite !iwfFamT_single by eauto using wf_ty_nf, wf_tm_nf.
      apply (iwf_geq_at HE HG).
      pose proof (HP (kw_self HΓ) (posHd s) (posHd s')) as Y.
      pose proof (iwfFamT_nf _ _ _ _ _ _ _ _ (wf_ty_nf (eqty_wf_l ge_typeof HF))) as Nc.
      pose proof (iwfFamT_nf _ _ _ _ _ _ _ _ (wf_ty_nf (eqty_wf_r ge_typeof HF))) as Nc'.
      pose proof (wf_tm_nf (eqtm_wf_l ge_typeof Enn)) as Nn. pose proof (wf_tm_nf (eqtm_wf_r ge_typeof Enn)) as Nn'.
      rewrite !ktm_self, !ktml_self, kty_self in Y by eauto using wf_ty_nf.
      apply Y. apply pos_hd; [exact Hn | exact Hn' | exact Hss].
    + rewrite !dvecTl_eq, !iwfFamT_mv.
      apply (geq_ty_wk (wkr_shift1 _ _ _) HΓH). apply IH.
      * rewrite <- !iwfFamT_mv. exact (dvecMv_eqty ge_typeof ge_notV ge_compt Hs Hs' Es HF1w HF1).
      * intros ρ p p' Hp. rewrite !ktml_posMv_single by eauto using wf_tm_nf. apply HP.
        apply pos_tl; [exact (kw_tmred_succ Hn ρ) | exact (kw_tmred_succ Hn' ρ) | exact Hp].
  - (* neutral *)
    intros ν ν' Hνν n n' Hn Hn' c c' HF HP.
    pose proof (tmred_eq _ _ _ _ _ _ _ Hn) as En. pose proof (tmred_eq _ _ _ _ _ _ _ Hn') as En'.
    pose proof (geq_tm_sound (gne_tm_geq Hνν)) as Eν.
    assert (Enn : [ G ; Γ ⊢g n ≅ n' : tyNat @ lzero ]).
    { eapply eqtm_trans; [exact En | eapply eqtm_trans; [exact Eν | apply eqtm_sym, En']]. }
    apply (Step n n' ν ν' _ _ Hn Hn' Enn HF).
    pose proof (fin_stab_eqty En HF) as HFν. pose proof (eqty_wf_l ge_typeof HFν) as HFνw.
    pose proof (ctx_of_ty HFνw) as HΓν.
    apply gne_ty_geq, (gne_ty_dvec HLL Hνν HFνw).
    set (ρ1 := kw_wk1 HΓν).
    assert (Hc : [ kw_G ρ1 ; kw_Δ ρ1 ⊢ c ≈ c' : kty ρ1 X @ li ]).
    { pose proof (iwfFamT_nf _ _ _ _ _ _ _ _ (wf_ty_nf (eqty_wf_l ge_typeof HF))) as Nc.
      pose proof (iwfFamT_nf _ _ _ _ _ _ _ _ (wf_ty_nf (eqty_wf_r ge_typeof HF))) as Nc'.
      assert (E1 : forall t, nftm t -> (ktml ρ1 t)[lsingle (var 0)] = t).
      { intros t Ht. unfold ktml, ρ1, kw_wk1, kw_loc; cbn [kw_γ kw_gk kw_r kw_rk gwa kw_mk]. change (wk_ren wk1) with ↑.
        now apply liftshift_single_var. }
      assert (HΓν' : [ G ; Γ ,, tyFin ν @ lzero ⊢[ typeof ge_layer ] ]) by (rewrite ge_typeof; exact HΓν).
      pose proof (HP ρ1 (var 0) (var 0)) as Y. rewrite !E1 in Y by assumption. apply Y.
      unfold ktm, ρ1, kw_wk1, kw_loc; cbn [kw_G kw_Δ kw_γ kw_gk kw_r kw_rk gwa kw_mk]. change (wk_ren wk1) with ↑.
      apply pos_ne.
      - exact (wk1_eqtm_g _ _ _ _ _ _ _ _ _ HΓν' Enn).
      - apply gne_tm_var. eapply wf_conv; [exact (var0_wf_g _ _ _ _ _ HΓν') |].
        rewrite ge_typeof. change (tyFin n⟨↑⟩) with (tyFin n)⟨↑⟩. apply (wk1_eqty_g _ _ _ _ _ _ _ _ HΓν').
        apply eqty_fin; [exact ge_notV | exact En]. }
    pose proof (iwf_geq_at (IWfEq_kw ρ1 HE) (IWfGeq_kw ρ1 HE HG) Hc) as Y.
    unfold kty, ktml, ktmll, ρ1, kw_wk1, kw_loc in Y; cbn [kw_G kw_Δ kw_γ kw_gk kw_r kw_rk gwa kw_mk] in Y.
    change (wk_ren wk1) with ↑ in Y. exact Y.
Qed.

(** At a successor: the head's and the tail's types (the tail in any
    context extending [Γ] by one entry). *)
Lemma iwf_succ_geq {G Γ l li k ki X X' A A' N N' Ot Ot' C C' n n' m m' c c'} :
  IWfEq (G := G) (i := ge_layer) Γ l li k ki X X' A A' N N' Ot Ot' C C' ->
  IWfGeq G Γ l li X X' A A' N N' Ot Ot' C C' ->
  [ G ; Γ ⊢g n ⤳* succ m : tyNat @ lzero ] -> [ G ; Γ ⊢g n' ⤳* succ m' : tyNat @ lzero ] -> NatRel G Γ m m' ->
  [ G ; Γ ,, tyFin n @ lzero ⊢g iwfFamT l li X A N Ot C c ≅ iwfFamT k ki X' A' N' Ot' C' c' @ lmax l li ] ->
  (forall (ρ : kwk G Γ) p p', PosRel (kw_G ρ) (kw_Δ ρ) (ktm ρ n) (ktm ρ n') p p' ->
     [ kw_G ρ ; kw_Δ ρ ⊢ (ktml ρ c)[lsingle p] ≈ (ktml ρ c')[lsingle p'] : kty ρ X @ li ]) ->
  [ G ; Γ ⊢ dvecHd m (iwfFamT l li X A N Ot C c) ≈ dvecHd m' (iwfFamT k ki X' A' N' Ot' C' c') @ lmax l li ] /\
  (forall H lh, [ G ; Γ ,, H @ lh ⊢g ] ->
     [ G ; Γ ,, H @ lh ⊢ dvecTl (lmax l li) m (iwfFamT l li X A N Ot C c)
         ≈ dvecTl (lmax k ki) m' (iwfFamT k ki X' A' N' Ot' C' c') @ lmax l li ]).
Proof using EL.
  intros HE HG Hn Hn' Hmm HF HP.
  pose proof HE as (Hlk & Hlik & (Wl & Wli & HX & HA & HN & HO & HC) & _ & _ & _ & _ & _
                    & HX' & HA' & HN' & HO' & HC').
  pose proof (tmred_eq _ _ _ _ _ _ _ Hn) as En. pose proof (tmred_eq _ _ _ _ _ _ _ Hn') as En'.
  pose proof (geq_tm_sound (NatRel_geq Hmm)) as Em.
  pose proof (eqtm_wf_l ge_typeof Em) as Hm. pose proof (eqtm_wf_r ge_typeof Em) as Hm'.
  pose proof (ctx_of_tm Hm) as HΓ.
  pose proof (fin_stab_eqty En HF) as HF1. pose proof (eqty_wf_l ge_typeof HF1) as HF1w.
  split.
  - rewrite !iwfFamT_single by eauto using wf_ty_nf, wf_tm_nf.
    apply (iwf_geq_at HE HG).
    pose proof (HP (kw_self HΓ) (posHd m) (posHd m')) as Y.
    pose proof (iwfFamT_nf _ _ _ _ _ _ _ _ (wf_ty_nf (eqty_wf_l ge_typeof HF))) as Nc.
    pose proof (iwfFamT_nf _ _ _ _ _ _ _ _ (wf_ty_nf (eqty_wf_r ge_typeof HF))) as Nc'.
    pose proof (wf_tm_nf (eqtm_wf_l ge_typeof En)) as Nn. pose proof (wf_tm_nf (eqtm_wf_l ge_typeof En')) as Nn'.
    rewrite !ktm_self, !ktml_self, kty_self in Y by eauto using wf_ty_nf.
    apply Y. apply pos_hd; [exact Hn | exact Hn' | exact Hmm].
  - intros H lh HΓH. rewrite !dvecTl_eq, !iwfFamT_mv.
    apply (geq_ty_wk (wkr_shift1 _ _ _) HΓH). apply (iwf_dvec_geq HE HG _ _ Hmm).
    + rewrite <- !iwfFamT_mv. exact (dvecMv_eqty ge_typeof ge_notV ge_compt Hm Hm' Em HF1w HF1).
    + intros ρ p p' Hp. rewrite !ktml_posMv_single by eauto using wf_tm_nf. apply HP.
      apply pos_tl; [exact (kw_tmred_succ Hn ρ) | exact (kw_tmred_succ Hn' ρ) | exact Hp].
Qed.

End IWfGeq.
