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
Proof.
  apply ren_ren; intros [|[|n]]; rewrite ?rlk_rlift; cbn; rewrite ?rlk_rlift; auto. now rewrite rlk_wk_comp.
Qed.
Lemma ktmll_comp {G Γ} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) t :
  ktmll (kw_comp ρ ρ') t = ktmll ρ' (ktmll ρ t).
Proof. unfold ktmll; cbn. now rewrite gwa_ren, gwa_comp_tm, ren_wk_comp_lift2. Qed.

(** ** The children's family *)

(** At a position, and moved to the tail. *)
Lemma iwfFamT_single l li (X A : ty) (N Ot C c p : tm) : nfty X -> nfty A -> nftm N -> nftm Ot -> nftm C ->
  (iwfFamT l li X A N Ot C c)[lsingle p] = tyIWf l li X A N Ot C c[lsingle p].
Proof. intros. unfold iwfFamT. push_subst. f_equal. all: teq_core. Qed.

Lemma iwfFamT_mv l li (X A : ty) (N Ot C c m : tm) :
  dvecMv m (iwfFamT l li X A N Ot C c) = iwfFamT l li X A N Ot C (posMv m c).
Proof. unfold dvecMv, iwfFamT, posMv, posTl. push_ren. push_subst. f_equal. all: teq_core. Qed.

(** [C] at a shape, then at a position. *)
Lemma llift_single_single (C a p : tm) : nftm a -> C[llift (lsingle a)][lsingle p] = C[lsingle2 a p].
Proof.
  intros Ha. apply subst_subst. intros [|[|n]]; cbn; rewrite ?llk_llift; cbn; auto.
  - change (ren_tm ?x ?r) with x⟨r⟩. now rewrite shift_single by exact Ha.
  - replace (n + 0 + 1) with (S n) by lia. cbn. now rewrite !Nat.add_0_r.
Qed.

(** A family moved to the tail, at a position. *)
Lemma posMv_single m (c p : tm) : nftm m ->
  (posMv m c)[lsingle p] = c[lsingle (posTl m p)].
Proof.
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
Proof. unfold kty, ktm, ktml, ktmll; now rewrite gwa_tyIWf. Qed.
Lemma ktm_supi l li X A N Ot C a cs :
  ktm ρ (tmSupi l li X A N Ot C a cs) =
  tmSupi l li (kty ρ X) (kty ρ A) (ktml ρ N) (ktml ρ Ot) (ktmll ρ C) (ktm ρ a) (ktm ρ cs).
Proof. unfold kty, ktm, ktml, ktmll; now rewrite gwa_supi. Qed.

Lemma ktm_posHd m : ktm ρ (posHd m) = posHd (ktm ρ m).
Proof. unfold posHd. rewrite ktm_inl, kty_tyUnit, kty_tyFin. unfold ktm. now rewrite gwa_triv. Qed.
Lemma ktm_posTl m p : ktm ρ (posTl m p) = posTl (ktm ρ m) (ktm ρ p).
Proof. unfold posTl. now rewrite ktm_inr, kty_tyUnit, kty_tyFin. Qed.

Lemma ktyl_shift' (T : ty) : ktyl ρ T⟨↑⟩ = (kty ρ T)⟨↑⟩.
Proof. unfold kty, ktyl. now rewrite gwa_ren_ty, shift_lift_ty. Qed.

(** The child index at a shape, in a world. *)
Lemma ktmll_llift_single (C a : tm) : (ktmll ρ C)[llift (lsingle (ktm ρ a))] = ktml ρ C[llift (lsingle a)].
Proof.
  unfold ktmll, ktml, ktm. rewrite gwa_subst.
  rewrite (subst_ext _ (llift (lsingle a))⟦kw_γ ρ⟧ (llift (lsingle a)⟦kw_γ ρ⟧)) by apply llk_llift_gwa.
  rewrite gwa_lsingle, llift_lsingle_ren. reflexivity.
Qed.

Lemma ktml_posMv m c : ktml ρ (posMv m c) = posMv (ktm ρ m) (ktml ρ c).
Proof.
  unfold posMv, posTl, ktml, ktm.
  rewrite gwa_subst, gwa_lsingle, lsingle_ren, gwa_ren, liftshift_lift. f_equal. f_equal.
  unfold gwa; destruct (kw_γ ρ); cbn; f_equal; f_equal;
    change (ren_tm ?x ?r) with x⟨r⟩; rewrite ?shift_lift; try reflexivity.
  all: change (gren_tm ?x ?y) with x⟪y⟫; rewrite gren_ren, shift_lift; reflexivity.
Qed.

Lemma ktml_posMv_single m c p : nftm m ->
  (ktml ρ (posMv m c))[lsingle p] = (ktml ρ c)[lsingle (posTl (ktm ρ m) p)].
Proof. intros Hm. rewrite ktml_posMv. apply posMv_single. unfold ktm; apply ren_nf. Qed.

(** ** The signature in a world *)

Lemma kw_wkr_ll {A l N} :
  wkr (rlift (rlift (kw_r ρ))) (kw_Δ ρ ,, kty ρ A @ l ,, tyFin (ktml ρ N) @ lzero)
    ((Γ ,, A @ l ,, tyFin N @ lzero)⟦kw_γ ρ⟧).
Proof. rewrite gwa_cext, gwa_tyFin. eapply wkr_up'; [exact (kw_wkr_l ρ) | reflexivity]. Qed.

Lemma kw_tm_l' {A l t T l'} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l ->
  [ G ; Γ ,, A @ l ⊢g t : T @ l' ] -> [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ⊢g ktml ρ t : ktyl ρ T @ l' ].
Proof. intros HA Hl H. exact (kw_tm_l ρ HA Hl H). Qed.
Lemma kw_eqtm_l {A l t t' T l'} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l ->
  [ G ; Γ ,, A @ l ⊢g t ≅ t' : T @ l' ] ->
  [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ⊢g ktml ρ t ≅ ktml ρ t' : ktyl ρ T @ l' ].
Proof.
  intros HA Hl H. eapply weakening_r; [exact (gwa_eqtm (kw_gok ρ) (kw_glob ρ) H) | exact ge_typeof
                                      | exact (kw_wkr_l ρ) | exact (kw_ext ρ HA Hl)].
Qed.

Lemma kw_ext2 {A l N} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l -> [ G ; Γ ,, A @ l ⊢g N : tyNat @ lzero ] ->
  [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ,, tyFin (ktml ρ N) @ lzero ⊢g ].
Proof.
  intros HA Hl HN. apply ext_wf_g; [| exact I]. apply wft_fin; [exact ge_notV|].
  exact (kw_tm_nat_l ρ HA Hl HN).
Qed.

Lemma kw_tm_ll {A l N t T l'} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l -> [ G ; Γ ,, A @ l ⊢g N : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢g t : T @ l' ] ->
  [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ,, tyFin (ktml ρ N) @ lzero ⊢g ktmll ρ t : T⟦kw_γ ρ⟧⟨rlift (rlift (kw_r ρ))⟩ @ l' ].
Proof.
  intros HA Hl HN H. eapply weakening_r; [exact (gwa_tm (kw_gok ρ) (kw_glob ρ) H) | exact ge_typeof
                                         | exact kw_wkr_ll | exact (kw_ext2 HA Hl HN)].
Qed.
Lemma kw_eqtm_ll {A l N t t' T l'} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l -> [ G ; Γ ,, A @ l ⊢g N : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢g t ≅ t' : T @ l' ] ->
  [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ,, tyFin (ktml ρ N) @ lzero ⊢g ktmll ρ t ≅ ktmll ρ t'
      : T⟦kw_γ ρ⟧⟨rlift (rlift (kw_r ρ))⟩ @ l' ].
Proof.
  intros HA Hl HN H. eapply weakening_r; [exact (gwa_eqtm (kw_gok ρ) (kw_glob ρ) H) | exact ge_typeof
                                         | exact kw_wkr_ll | exact (kw_ext2 HA Hl HN)].
Qed.

Lemma ktyll_shift2 (T : ty) : T⟨↑⟩⟨↑⟩⟦kw_γ ρ⟧⟨rlift (rlift (kw_r ρ))⟩ = (kty ρ T)⟨↑⟩⟨↑⟩.
Proof. unfold kty. now rewrite !gwa_ren_ty, !shift_lift_ty. Qed.

Lemma IWfEq_kw {l li k ki X X' A A' N N' Ot Ot' C C'} :
  IWfEq (G := G) (i := ge_layer) Γ l li k ki X X' A A' N N' Ot Ot' C C' ->
  IWfEq (G := kw_G ρ) (i := ge_layer) (kw_Δ ρ) l li k ki (kty ρ X) (kty ρ X') (kty ρ A) (kty ρ A')
    (ktml ρ N) (ktml ρ N') (ktml ρ Ot) (ktml ρ Ot') (ktmll ρ C) (ktmll ρ C').
Proof.
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
Proof. now rewrite ktm_single, ktml_comp, ktm_comp. Qed.

Lemma ktml_comp_child {G Γ} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) (C a p : tm) :
  (ktml ρ' (ktmll ρ C)[llift (lsingle (ktm ρ a))])[lsingle p] =
  (ktmll (kw_comp ρ ρ') C)[lsingle2 (ktm (kw_comp ρ ρ') a) p].
Proof.
  rewrite <- ktmll_llift_single, <- ktmll_comp, <- ktm_comp.
  apply llift_single_single. unfold ktm; apply ren_nf.
Qed.

Lemma kw_tmred_succ {G Γ k m} : [ G ; Γ ⊢g k ⤳* succ m : tyNat @ lzero ] ->
  forall ρ : kwk G Γ, [ kw_G ρ ; kw_Δ ρ ⊢g ktm ρ k ⤳* succ (ktm ρ m) : tyNat @ lzero ].
Proof. intros H ρ. pose proof (kw_tmred ρ H) as R. rewrite ktm_succ, kty_tyNat in R. exact R. Qed.

(** The predecessors of two lengths related in every world are. *)
Lemma NatRel_kw_pred {G Γ k k' m m'} :
  (forall ρ : kwk G Γ, NatRel (kw_G ρ) (kw_Δ ρ) (ktm ρ k) (ktm ρ k')) ->
  [ G ; Γ ⊢g k ⤳* succ m : tyNat @ lzero ] -> [ G ; Γ ⊢g k' ⤳* succ m' : tyNat @ lzero ] ->
  forall ρ : kwk G Γ, NatRel (kw_G ρ) (kw_Δ ρ) (ktm ρ m) (ktm ρ m').
Proof.
  intros HW Hk Hk' ρ.
  pose proof (kw_tmred_succ Hk ρ) as R. pose proof (kw_tmred_succ Hk' ρ) as R'.
  destruct (NatRel_inv_succ (HW ρ) R) as (m2 & R2 & Hm).
  assert (Es : succ m2 = succ (ktm ρ m')) by (eapply tmred_whnf_det; [exact R2 | exact R' | constructor ..]).
  injection Es as ->. exact Hm.
Qed.

End IWfAux.
