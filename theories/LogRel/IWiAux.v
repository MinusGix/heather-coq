(** * The relation at [IWi]: syntax in Kripke worlds, the signature in a
      world, and the field types generically equal (M19b)

    [IWfAux]'s, with a domain family under the position binder and a
    child index under the position and domain binders. Positions reached
    by a spine are canonical ([PosCan]): a canonical position is the only
    one related to its partner ([PosCan_det_l], [PosCan_det_r]), which is
    how a spine's argument relation, read against some right position,
    meets the right type's. *)
From DeLaM.LogRel Require Export IWfAux MAux.

Lemma gwa_tyIWi γ l lp li X A N D Ot C m :
  (tyIWi l lp li X A N D Ot C m)⟦γ⟧ = tyIWi l lp li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ D⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧ m⟦γ⟧.
Proof. now destruct γ. Qed.
Lemma gwa_supii γ l lp li X A N D Ot C a cs :
  (tmSupii l lp li X A N D Ot C a cs)⟦γ⟧ = tmSupii l lp li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ D⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧ a⟦γ⟧ cs⟦γ⟧.
Proof. now destruct γ. Qed.

(** A field's type at a position: its domain [d0] and its child index
    [c0] under the domain binder. *)
Definition iwiFieldT (l lp li : lvl) (X A : ty) (N : tm) (D : ty) (Ot C : tm) (d0 : ty) (c0 : tm) : ty :=
  tyPi lp (iwiL l lp li) d0
    (tyIWi l lp li X⟨↑⟩ A⟨↑⟩ N⟨rlift ↑⟩ D⟨rlift (rlift ↑)⟩ Ot⟨rlift ↑⟩ C⟨rlift (rlift (rlift ↑))⟩ c0).

Lemma iwiFamT_single l lp li (X A : ty) (N : tm) (D : ty) (Ot C : tm) (d : ty) (c p : tm) :
  nfty X -> nfty A -> nftm N -> nfty D -> nftm Ot -> nftm C ->
  (iwiFamT l lp li X A N D Ot C d c)[lsingle p] = iwiFieldT l lp li X A N D Ot C d[lsingle p] c[llift (lsingle p)].
Proof. intros. unfold iwiFamT, iwiFamCodT, iwiFieldT. push_subst. f_equal. f_equal. all: teq_core. Qed.

Lemma posMvT_dvecMv m d : posMvT m d = dvecMv m d.
Proof. reflexivity. Qed.

Lemma iwiFamT_mv l lp li (X A : ty) (N : tm) (D : ty) (Ot C : tm) (d : ty) (c m : tm) :
  dvecMv m (iwiFamT l lp li X A N D Ot C d c) = iwiFamT l lp li X A N D Ot C (posMvT m d) (posMv2 m c).
Proof.
  unfold dvecMv, iwiFamT, iwiFamCodT, posMvT, posMv2, posTl. push_ren. push_subst. f_equal. f_equal. all: teq_core.
Qed.

(** A domain family, and a family of child indices, at the position
    variable of their binder, and moved to the tail at a position. *)
Lemma liftshift_single_var_ty (T : ty) : nfty T -> T⟨rlift ↑⟩[lsingle (var 0)] = T.
Proof.
  intros HT. rewrite (ren_subst_ty _ _ _ (lshift 0)).
  - apply subst_id_ty; auto. intros; cbn; f_equal; lia.
  - intros [|n]; rlk_simpl; cbn; f_equal; lia.
Qed.

Lemma lift2shift_llift_single_var (t : tm) : nftm t -> t⟨rlift (rlift ↑)⟩[llift (lsingle (var 0))] = t.
Proof.
  intros Ht. rewrite (ren_subst _ _ _ (lshift 0)).
  - apply subst_id; auto. intros; cbn; f_equal; lia.
  - intros [|[|n]]; rlk_simpl; cbn; rewrite ?llk_llift; cbn; f_equal; lia.
Qed.

Lemma posMvT_single m (d : ty) (p : tm) : nftm m -> (posMvT m d)[lsingle p] = d[lsingle (posTl m p)].
Proof.
  intros Hm. unfold posMvT, posTl.
  rewrite (subst_subst_ty _ _ _ (lcons (lsingle p) (tmInr lzero lzero (tyUnit lzero) (tyFin m) p))).
  - apply ren_subst_ty. intros [|k]; rlk_simpl; cbn; reflexivity.
  - intros [|k]; cbn; [| now rewrite Nat.add_0_r].
    change (subst_tm ?x ?d) with x[d]. now rewrite shift_single.
Qed.

Lemma posMv2_single m (c p : tm) : nftm m -> (posMv2 m c)[llift (lsingle p)] = c[llift (lsingle (posTl m p))].
Proof.
  intros Hm. unfold posMv2, posTl. teq_core. f_equal.
  change (ren_ty ?x ?r) with x⟨r⟩. change (ren_tm ?x ?r) with x⟨r⟩. change (subst_ty ?x ?d) with x[d].
  cbn. f_equal. change (ren_tm ?x ?r) with x⟨r⟩. change (subst_tm ?x ?d) with x[d]. teq_core.
Qed.

(** ** Canonical related positions

    [PosRel] without its neutral clause: what a spine reaches. *)
Inductive PosCan `{GenericEq} (G : gctx) (Γ : ctx) : tm -> tm -> tm -> tm -> Prop :=
| pc_hd k k' m m' :
    [ G ; Γ ⊢g k ⤳* succ m : tyNat @ lzero ] -> [ G ; Γ ⊢g k' ⤳* succ m' : tyNat @ lzero ] ->
    NatRel G Γ m m' -> PosCan G Γ k k' (posHd m) (posHd m')
| pc_tl k k' m m' p p' :
    [ G ; Γ ⊢g k ⤳* succ m : tyNat @ lzero ] -> [ G ; Γ ⊢g k' ⤳* succ m' : tyNat @ lzero ] ->
    PosCan G Γ m m' p p' -> PosCan G Γ k k' (posTl m p) (posTl m' p').

Section IWiAux.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

Lemma PosCan_rel {G Γ k k' p p'} : PosCan G Γ k k' p p' -> PosRel G Γ k k' p p'.
Proof using . induction 1; [apply pos_hd | apply pos_tl]; assumption. Qed.

(** A canonical position is the only one related to its partner. *)
Lemma PosCan_det_r {G Γ k k' p p'} : PosCan G Γ k k' p p' -> forall q, PosRel G Γ k k' p q -> q = p'.
Proof using EL.
  induction 1 as [k k' m m' Hk Hk' _ | k k' m m' p p' Hk Hk' _ IH]; intros q Hq;
    inversion Hq as [k2 k2' m2 m2' Hk2 Hk2' _ | k2 k2' m2 m2' p2 p2' Hk2 Hk2' Hp2 | k2 k2' p2 p2' _ Hp2]; subst.
  all: try solve [pose proof (gne_tm_whne_l Hp2) as X; inversion X].
  - assert (Es : succ _ = succ _) by (eapply tmred_whnf_det; [exact Hk2' | exact Hk' | constructor ..]).
    now injection Es as ->.
  - assert (Es : succ _ = succ _) by (eapply tmred_whnf_det; [exact Hk2' | exact Hk' | constructor ..]).
    injection Es as ->. f_equal. exact (IH _ Hp2).
Qed.

Lemma PosCan_det_l {G Γ k k' p p'} : PosCan G Γ k k' p p' -> forall q, PosRel G Γ k k' q p' -> q = p.
Proof using EL.
  induction 1 as [k k' m m' Hk Hk' _ | k k' m m' p p' Hk Hk' _ IH]; intros q Hq;
    inversion Hq as [k2 k2' m2 m2' Hk2 Hk2' _ | k2 k2' m2 m2' p2 p2' Hk2 Hk2' Hp2 | k2 k2' p2 p2' _ Hp2]; subst.
  all: try solve [pose proof (gne_tm_whne_r Hp2) as X; inversion X].
  - assert (Es : succ _ = succ _) by (eapply tmred_whnf_det; [exact Hk2 | exact Hk | constructor ..]).
    now injection Es as ->.
  - assert (Es : succ _ = succ _) by (eapply tmred_whnf_det; [exact Hk2 | exact Hk | constructor ..]).
    injection Es as ->. f_equal. exact (IH _ Hp2).
Qed.

Section KwIWi.
Context {G : gctx} {Γ : ctx} (ρ : kwk G Γ).

Lemma kty_tyIWi l lp li X A N D Ot C m :
  kty ρ (tyIWi l lp li X A N D Ot C m) =
  tyIWi l lp li (kty ρ X) (kty ρ A) (ktml ρ N) (ktyll ρ D) (ktml ρ Ot) (ktmlll ρ C) (ktm ρ m).
Proof using . unfold kty, ktm, ktml, ktyll, ktmlll; now rewrite gwa_tyIWi. Qed.
Lemma ktm_supii l lp li X A N D Ot C a cs :
  ktm ρ (tmSupii l lp li X A N D Ot C a cs) =
  tmSupii l lp li (kty ρ X) (kty ρ A) (ktml ρ N) (ktyll ρ D) (ktml ρ Ot) (ktmlll ρ C) (ktm ρ a) (ktm ρ cs).
Proof using . unfold kty, ktm, ktml, ktyll, ktmlll; now rewrite gwa_supii. Qed.

Lemma ktyl_iwiFamT l lp li X A N D Ot C d c :
  ktyl ρ (iwiFamT l lp li X A N D Ot C d c) =
  iwiFamT l lp li (kty ρ X) (kty ρ A) (ktml ρ N) (ktyll ρ D) (ktml ρ Ot) (ktmlll ρ C) (ktyl ρ d) (ktmll ρ c).
Proof using .
  unfold iwiFamT, iwiFamCodT, ktyl, kty, ktml, ktyll, ktmll, ktmlll.
  rewrite gwa_tyPi, gwa_tyIWi, !gwa_ren_ty, !gwa_ren. cbn. f_equal. f_equal. all: teq_core.
Qed.

Lemma ktyl_posMvT m d : ktyl ρ (posMvT m d) = posMvT (ktm ρ m) (ktyl ρ d).
Proof using .
  unfold posMvT, posTl, ktyl, ktm.
  rewrite gwa_subst_ty, gwa_lsingle, lsingle_ren_ty, gwa_ren_ty, liftshift_lift_ty.
  f_equal. f_equal. unfold gwa; destruct (kw_γ ρ); cbn; f_equal; f_equal;
    change (ren_tm ?x ?r) with x⟨r⟩; rewrite ?shift_lift; try reflexivity.
  all: change (gren_tm ?x ?y) with x⟪y⟫; rewrite gren_ren, shift_lift; reflexivity.
Qed.
Lemma ktmll_posMv2 m c : ktmll ρ (posMv2 m c) = posMv2 (ktm ρ m) (ktmll ρ c).
Proof using .
  unfold posMv2, posTl, ktmll, ktm. rewrite gwa_subst.
  rewrite (subst_ext _ (llift (lsingle (tmInr lzero lzero (tyUnit lzero) (tyFin m⟨↑⟩) (var 0))))⟦kw_γ ρ⟧
             (llift (lsingle (tmInr lzero lzero (tyUnit lzero) (tyFin m⟨↑⟩) (var 0)))⟦kw_γ ρ⟧)) by apply llk_llift_gwa.
  rewrite gwa_lsingle, llift_lsingle_ren, gwa_ren.
  assert (L : forall (t : tm) r, t⟨rlift (rlift ↑)⟩⟨rlift (rlift (rlift r))⟩ = t⟨rlift (rlift r)⟩⟨rlift (rlift ↑)⟩).
  { intros t r. rewrite !ren_ren_comp. apply ren_ext_tm; intros [|[|n]]; rlk_simpl; auto; lia. }
  rewrite L. f_equal. f_equal. f_equal. unfold gwa; destruct (kw_γ ρ); cbn; f_equal; f_equal;
    change (ren_tm ?x ?r) with x⟨r⟩; rewrite ?shift_lift; try reflexivity.
  all: change (gren_tm ?x ?y) with x⟪y⟫; rewrite gren_ren, shift_lift; reflexivity.
Qed.

Lemma ktmll_self {G' Γ'} (HΓ : [ G' ; Γ' ⊢g ]) t : nftm t -> ktmll (kw_self HΓ) t = t.
Proof using .
  intros H. unfold ktmll, kw_self, kw_loc; cbn [kw_γ kw_gk kw_r kw_rk gwa wk_ren kw_mk].
  rewrite <- (ren_id_tm t H) at 2. apply ren_ext_tm. intros [|[|n]]; rlk_simpl; cbn; lia.
Qed.
End KwIWi.

(** ** The signature under its binders, in a world *)
Section KwIWiB.
Context {G : gctx} {Γ : ctx} (ρ : kwk G Γ).

Lemma kw_ty_ll {A l N T l'} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l -> [ G ; Γ ,, A @ l ⊢g N : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢g T @ l' ] ->
  [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ,, tyFin (ktml ρ N) @ lzero ⊢g ktyll ρ T @ l' ].
Proof using .
  intros HA Hl HN H. eapply weakening_r; [exact (gwa_ty (kw_gok ρ) (kw_glob ρ) H) | exact ge_typeof
                                         | exact (kw_wkr_ll ρ) | exact (kw_ext2 ρ HA Hl HN)].
Qed.
Lemma kw_eqty_ll {A l N T T' l'} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l -> [ G ; Γ ,, A @ l ⊢g N : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢g T ≅ T' @ l' ] ->
  [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ,, tyFin (ktml ρ N) @ lzero ⊢g ktyll ρ T ≅ ktyll ρ T' @ l' ].
Proof using .
  intros HA Hl HN H. eapply weakening_r; [exact (gwa_eqty (kw_gok ρ) (kw_glob ρ) H) | exact ge_typeof
                                         | exact (kw_wkr_ll ρ) | exact (kw_ext2 ρ HA Hl HN)].
Qed.
Lemma kw_geq_ty_ll {A l N T T' l'} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l -> [ G ; Γ ,, A @ l ⊢g N : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢ T ≈ T' @ l' ] ->
  [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ,, tyFin (ktml ρ N) @ lzero ⊢ ktyll ρ T ≈ ktyll ρ T' @ l' ].
Proof using EL.
  intros HA Hl HN H. exact (geq_ty_wk (kw_wkr_ll ρ) (kw_ext2 ρ HA Hl HN) (geq_ty_gwa (kw_gok ρ) (kw_glob ρ) H)).
Qed.

Lemma kw_wkr_lll {A l N D lp} :
  wkr (rlift (rlift (rlift (kw_r ρ))))
    (kw_Δ ρ ,, kty ρ A @ l ,, tyFin (ktml ρ N) @ lzero ,, ktyll ρ D @ lp)
    ((Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp)⟦kw_γ ρ⟧).
Proof using .
  pose proof (kw_wkr_ll ρ (A := A) (l := l) (N := N)) as W.
  rewrite (gwa_cext _ (Γ ,, A @ l ,, tyFin N @ lzero)).
  eapply wkr_up'; [exact W | reflexivity].
Qed.

Lemma kw_ext3 {A l N D lp} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l -> [ G ; Γ ,, A @ l ⊢g N : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢g D @ lp ] -> lwf (gL G) lp ->
  [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ,, tyFin (ktml ρ N) @ lzero ,, ktyll ρ D @ lp ⊢g ].
Proof using . intros HA Hl HN HD Hlp. apply ext_wf_g; [exact (kw_ty_ll HA Hl HN HD) | exact (kw_lwf ρ Hlp)]. Qed.

Lemma kw_tm_lll {A l N D lp t T l'} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l -> [ G ; Γ ,, A @ l ⊢g N : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢g D @ lp ] -> lwf (gL G) lp ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp ⊢g t : T @ l' ] ->
  [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ,, tyFin (ktml ρ N) @ lzero ,, ktyll ρ D @ lp ⊢g ktmlll ρ t
      : T⟦kw_γ ρ⟧⟨rlift (rlift (rlift (kw_r ρ)))⟩ @ l' ].
Proof using .
  intros HA Hl HN HD Hlp H. eapply weakening_r; [exact (gwa_tm (kw_gok ρ) (kw_glob ρ) H) | exact ge_typeof
                                                | exact kw_wkr_lll | exact (kw_ext3 HA Hl HN HD Hlp)].
Qed.
Lemma kw_eqtm_lll {A l N D lp t t' T l'} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l -> [ G ; Γ ,, A @ l ⊢g N : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢g D @ lp ] -> lwf (gL G) lp ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp ⊢g t ≅ t' : T @ l' ] ->
  [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ,, tyFin (ktml ρ N) @ lzero ,, ktyll ρ D @ lp ⊢g ktmlll ρ t ≅ ktmlll ρ t'
      : T⟦kw_γ ρ⟧⟨rlift (rlift (rlift (kw_r ρ)))⟩ @ l' ].
Proof using .
  intros HA Hl HN HD Hlp H. eapply weakening_r; [exact (gwa_eqtm (kw_gok ρ) (kw_glob ρ) H) | exact ge_typeof
                                                | exact kw_wkr_lll | exact (kw_ext3 HA Hl HN HD Hlp)].
Qed.
Lemma kw_geq_tm_lll {A l N D lp t t' T l'} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l ->
  [ G ; Γ ,, A @ l ⊢g N : tyNat @ lzero ] -> [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢g D @ lp ] -> lwf (gL G) lp ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp ⊢ t ≈ t' : T @ l' ] ->
  [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ,, tyFin (ktml ρ N) @ lzero ,, ktyll ρ D @ lp ⊢ ktmlll ρ t ≈ ktmlll ρ t'
      : T⟦kw_γ ρ⟧⟨rlift (rlift (rlift (kw_r ρ)))⟩ @ l' ].
Proof using EL.
  intros HA Hl HN HD Hlp H.
  exact (geq_tm_wk kw_wkr_lll (kw_ext3 HA Hl HN HD Hlp) (geq_tm_gwa (kw_gok ρ) (kw_glob ρ) H)).
Qed.

Lemma IWiEq_kw {l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C'} :
  IWiEq (G := G) (i := ge_layer) Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' ->
  IWiEq (G := kw_G ρ) (i := ge_layer) (kw_Δ ρ) l lp li k kp ki (kty ρ X) (kty ρ X') (kty ρ A) (kty ρ A')
    (ktml ρ N) (ktml ρ N') (ktyll ρ D) (ktyll ρ D') (ktml ρ Ot) (ktml ρ Ot') (ktmlll ρ C) (ktmlll ρ C').
Proof using .
  intros (Hlk & Hlpk & Hlik & (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC) & HXX & HAA & HNN & HDD & HOO & HCC
          & HX' & HA' & HN' & HD' & HO' & HC').
  pose proof (kw_eqtm_l ρ HA Hl HNN) as HNN1. unfold ktyl in HNN1. rewrite gwa_tyNat in HNN1.
  change (tyNat⟨?r⟩) with tyNat in HNN1.
  pose proof (kw_eqtm_l ρ HA Hl HOO) as HOO1. fold (ktyl ρ X⟨↑⟩) in HOO1. rewrite ktyl_shift' in HOO1.
  pose proof (kw_tm_l' ρ HA Hl HO) as HO1. rewrite ktyl_shift' in HO1.
  pose proof (kw_tm_l' ρ HA Hl HO') as HO1'. rewrite ktyl_shift' in HO1'.
  pose proof (kw_ty_ll HA Hl HN HD) as HD1. pose proof (kw_ty_ll HA Hl HN HD') as HD1'.
  pose proof (kw_eqty_ll HA Hl HN HDD) as HDD1.
  pose proof (kw_eqtm_lll HA Hl HN HD Hlp HCC) as HCC1. rewrite kty_shift3 in HCC1.
  pose proof (kw_tm_lll HA Hl HN HD Hlp HC) as HC1. rewrite kty_shift3 in HC1.
  pose proof (kw_tm_lll HA Hl HN HD Hlp HC') as HC1'. rewrite kty_shift3 in HC1'.
  apply IWiEq_intro; auto using kw_lequiv, kw_lwf, kw_ty, kw_eqty, kw_tm_nat_l.
Qed.

End KwIWiB.

(** ** The field types, generically equal *)

Definition IWiGeq G Γ l lp li (X X' A A' : ty) (N N' : tm) (D D' : ty) (Ot Ot' C C' : tm) :=
  [ G ; Γ ⊢ X ≈ X' @ li ] /\ [ G ; Γ ⊢ A ≈ A' @ l ] /\ [ G ; Γ ,, A @ l ⊢ N ≈ N' : tyNat @ lzero ] /\
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢ D ≈ D' @ lp ] /\
  [ G ; Γ ,, A @ l ⊢ Ot ≈ Ot' : X⟨↑⟩ @ li ] /\
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp ⊢ C ≈ C' : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ].

Lemma IWiGeq_kw {G Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C'} (ρ : kwk G Γ) :
  IWiEq (G := G) (i := ge_layer) Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' ->
  IWiGeq G Γ l lp li X X' A A' N N' D D' Ot Ot' C C' ->
  IWiGeq (kw_G ρ) (kw_Δ ρ) l lp li (kty ρ X) (kty ρ X') (kty ρ A) (kty ρ A')
    (ktml ρ N) (ktml ρ N') (ktyll ρ D) (ktyll ρ D') (ktml ρ Ot) (ktml ρ Ot') (ktmlll ρ C) (ktmlll ρ C').
Proof using EL.
  intros (_ & _ & _ & (Hl & Hlp & Hli & HX & HA & HN & HD & _) & _) (GX & GA & GN & GD & GO & GC).
  refine (conj (kw_geq_ty ρ GX) (conj (kw_geq_ty ρ GA) (conj (kw_geq_nat_l ρ HA Hl GN)
            (conj (kw_geq_ty_ll ρ HA Hl HN GD) (conj _ _))))).
  - pose proof (kw_geq_tm_l ρ HA Hl GO) as Y. rewrite ktyl_shift' in Y. exact Y.
  - pose proof (kw_geq_tm_lll ρ HA Hl HN HD Hlp GC) as Y. rewrite kty_shift3 in Y. exact Y.
Qed.

Lemma IWiGeq_wk1 {G Γ Y ly l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C'} :
  IWiEq (G := G) (i := ge_layer) Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' ->
  IWiGeq G Γ l lp li X X' A A' N N' D D' Ot Ot' C C' -> [ G ; Γ ,, Y @ ly ⊢g ] ->
  IWiGeq G (Γ ,, Y @ ly) l lp li X⟨↑⟩ X'⟨↑⟩ A⟨↑⟩ A'⟨↑⟩ N⟨rlift ↑⟩ N'⟨rlift ↑⟩
    D⟨rlift (rlift ↑)⟩ D'⟨rlift (rlift ↑)⟩ Ot⟨rlift ↑⟩ Ot'⟨rlift ↑⟩
    C⟨rlift (rlift (rlift ↑))⟩ C'⟨rlift (rlift (rlift ↑))⟩.
Proof using EL.
  intros HE (GX & GA & GN & GD & GO & GC) HΓY.
  pose proof (IWiEq_wk1 ge_typeof ge_notV HE HΓY) as (_ & _ & _ & (Hl & Hlp & _ & _ & HA1 & HN1 & HD1 & _) & _).
  assert (HΓYA : [ G ; Γ ,, Y @ ly ,, A⟨↑⟩ @ l ⊢g ]) by exact (ext_wf_g HA1 Hl).
  assert (HΘ : [ G ; Γ ,, Y @ ly ,, A⟨↑⟩ @ l ,, tyFin N⟨rlift ↑⟩ @ lzero ⊢g ])
    by (apply ext_wf_g; [apply wft_fin; [exact ge_notV | exact HN1] | exact I]).
  assert (HΘ3 : [ G ; Γ ,, Y @ ly ,, A⟨↑⟩ @ l ,, tyFin N⟨rlift ↑⟩ @ lzero ,, D⟨rlift (rlift ↑)⟩ @ lp ⊢g ])
    by exact (ext_wf_g HD1 Hlp).
  assert (W1 : wkr (rlift ↑) (Γ ,, Y @ ly ,, A⟨↑⟩ @ l) (Γ ,, A @ l))
    by (eapply wkr_up'; [apply wkr_shift1 | reflexivity]).
  refine (conj (geq_ty_wk (wkr_shift1 _ _ _) HΓY GX) (conj (geq_ty_wk (wkr_shift1 _ _ _) HΓY GA)
            (conj (geq_tm_wk W1 HΓYA GN) (conj (geq_ty_wk wkr_up2 HΘ GD) (conj _ _))))).
  - pose proof (geq_tm_wk W1 HΓYA GO) as Z. rewrite IWf_E_ren in Z. exact Z.
  - pose proof (geq_tm_wk (wkr_up3 HΘ3 eq_refl) HΘ3 GC) as Z. rewrite IWi_E_ren3 in Z. exact Z.
Qed.

Lemma iwi_geq_at {G Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' c c'} :
  IWiEq (G := G) (i := ge_layer) Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' ->
  IWiGeq G Γ l lp li X X' A A' N N' D D' Ot Ot' C C' ->
  [ G ; Γ ⊢ c ≈ c' : X @ li ] ->
  [ G ; Γ ⊢ tyIWi l lp li X A N D Ot C c ≈ tyIWi k kp ki X' A' N' D' Ot' C' c' @ iwiL l lp li ].
Proof using EL.
  intros (Hlk & Hlpk & Hlik & (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC) & _) (GX & GA & GN & GD & GO & GC) Hc.
  exact (geq_ty_iwi Hlk Hlpk Hlik HX GX HA GA HN GN HD GD HO GO HC GC Hc).
Qed.

(** A field's type: a [Π] over the domain into the family at the child
    index. *)
Lemma iwi_field_geq {G Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' d0 d0' c0 c0'} :
  IWiEq (G := G) (i := ge_layer) Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' ->
  IWiGeq G Γ l lp li X X' A A' N N' D D' Ot Ot' C C' ->
  [ G ; Γ ⊢g d0 @ lp ] -> [ G ; Γ ⊢ d0 ≈ d0' @ lp ] ->
  [ G ; Γ ,, d0 @ lp ⊢ c0 ≈ c0' : X⟨↑⟩ @ li ] ->
  [ G ; Γ ⊢ iwiFieldT l lp li X A N D Ot C d0 c0 ≈ iwiFieldT k kp ki X' A' N' D' Ot' C' d0' c0' @ iwiL l lp li ].
Proof using EL.
  intros HE HG Hd Gd Gc. pose proof HE as (Hlk & Hlpk & Hlik & (Hl & Hlp & Hli & _) & _).
  assert (HΓd : [ G ; Γ ,, d0 @ lp ⊢g ]) by exact (ext_wf_g Hd Hlp).
  eapply geq_ty_lconv; [| exact (iwiL_pi _ _ _ _ Hl Hlp Hli)].
  unfold iwiFieldT. apply geq_ty_pi; [exact Hlpk | exact (IWi_lvl_eq Hlk Hlpk Hlik) | exact Hd | exact Gd |].
  exact (iwi_geq_at (IWiEq_wk1 ge_typeof ge_notV HE HΓd) (IWiGeq_wk1 HE HG HΓd) Gc).
Qed.

(** The domains and the child indices of two field families, generically
    equal at related positions, in every world. *)
Definition IWiPosGeq G Γ lp li (X : ty) (k k' : tm) (d d' : ty) (c c' : tm) :=
  forall (ρ : kwk G Γ) p p', PosRel (kw_G ρ) (kw_Δ ρ) (ktm ρ k) (ktm ρ k') p p' ->
    [ kw_G ρ ; kw_Δ ρ ⊢g (ktyl ρ d)[lsingle p] @ lp ] /\
    [ kw_G ρ ; kw_Δ ρ ⊢ (ktyl ρ d)[lsingle p] ≈ (ktyl ρ d')[lsingle p'] @ lp ] /\
    [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ d)[lsingle p] @ lp
        ⊢ (ktmll ρ c)[llift (lsingle p)] ≈ (ktmll ρ c')[llift (lsingle p')] : (kty ρ X)⟨↑⟩ @ li ].

Lemma IWiPosGeq_tl {G Γ lp li X k k' m m' d d' c c'} :
  IWiPosGeq G Γ lp li X k k' d d' c c' ->
  [ G ; Γ ⊢g k ⤳* succ m : tyNat @ lzero ] -> [ G ; Γ ⊢g k' ⤳* succ m' : tyNat @ lzero ] ->
  IWiPosGeq G Γ lp li X m m' (posMvT m d) (posMvT m' d') (posMv2 m c) (posMv2 m' c').
Proof using .
  intros HP Hk Hk' ρ p p' Hp.
  rewrite !ktyl_posMvT, !ktmll_posMv2, !posMvT_single, !posMv2_single by (unfold ktm; apply ren_nf).
  apply HP. apply pos_tl; [exact (kw_tmred_succ Hk ρ) | exact (kw_tmred_succ Hk' ρ) | exact Hp].
Qed.

Lemma iwiFamT_nf l lp li X A N D Ot C d c : nfty (iwiFamT l lp li X A N D Ot C d c) -> nfty d /\ nftm c.
Proof using . unfold iwiFamT, iwiFamCodT; cbn; tauto. Qed.


(** The children's [DVec] types at related lengths, along field families
    generically equal at related positions in every world: by induction
    on the lengths' relation, the head by [iwi_field_geq], the tail along
    the moved families, and at a neutral length the family itself, at the
    position variable. *)
Lemma iwi_dvec_geq {G Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C'} :
  IWiEq (G := G) (i := ge_layer) Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' ->
  IWiGeq G Γ l lp li X X' A A' N N' D D' Ot Ot' C C' ->
  forall n n', NatRel G Γ n n' -> forall d d' c c',
  [ G ; Γ ,, tyFin n @ lzero ⊢g iwiFamT l lp li X A N D Ot C d c
      ≅ iwiFamT k kp ki X' A' N' D' Ot' C' d' c' @ iwiL l lp li ] ->
  IWiPosGeq G Γ lp li X n n' d d' c c' ->
  [ G ; Γ ⊢ tyDVec (iwiL l lp li) n (iwiFamT l lp li X A N D Ot C d c)
      ≈ tyDVec (iwiL k kp ki) n' (iwiFamT k kp ki X' A' N' D' Ot' C' d' c') @ iwiL l lp li ].
Proof using EL.
  intros HE HG.
  pose proof HE as (Hlk & Hlpk & Hlik & HS & _ & _ & _ & _ & _ & _ & HX' & HA' & HN' & HD' & HO' & HC').
  pose proof HS as (Wl & Wlp & Wli & HX & HA & HN & HD & HO & HC).
  pose proof (IWiSig_nf HS) as (NX & NA & NN & ND & NO & NC).
  assert (HL : lwf (gL G) (iwiL l lp li)) by (repeat split; cbn; auto).
  assert (HLL : lequiv (gL G) (iwiL l lp li) (iwiL k kp ki)) by exact (IWi_lvl_eq Hlk Hlpk Hlik).
  assert (HL' : lwf (gL G) (iwiL k kp ki)) by exact (lequiv_wf_r _ _ _ HLL).
  assert (Step : forall n n' w w' T T', [ G ; Γ ⊢g n ⤳* w : tyNat @ lzero ] -> [ G ; Γ ⊢g n' ⤳* w' : tyNat @ lzero ] ->
            [ G ; Γ ⊢g n ≅ n' : tyNat @ lzero ] -> [ G ; Γ ,, tyFin n @ lzero ⊢g T ≅ T' @ iwiL l lp li ] ->
            [ G ; Γ ⊢ tyDVec (iwiL l lp li) w T ≈ tyDVec (iwiL k kp ki) w' T' @ iwiL l lp li ] ->
            [ G ; Γ ⊢ tyDVec (iwiL l lp li) n T ≈ tyDVec (iwiL k kp ki) n' T' @ iwiL l lp li ]).
  { intros n n' w w' T T' Hn Hn' Enn HT H.
    assert (HT' : [ G ; Γ ,, tyFin n' @ lzero ⊢g T' @ iwiL k kp ki ]).
    { eapply wft_lconv; [| exact (lequiv_sym _ _ _ HLL)].
      exact (eqty_wf_r ge_typeof (fin_stab_eqty Enn HT)). }
    eapply geq_ty_exp; [exact (tyred_dvec HL (eqty_wf_l ge_typeof HT) Hn) | | exact H].
    exact (tyred_lconv _ _ _ _ (tyred_dvec HL' HT' Hn') HLL). }
  apply (NatRel_mut G Γ
    (fun n n' _ => forall d d' c c',
       [ G ; Γ ,, tyFin n @ lzero ⊢g iwiFamT l lp li X A N D Ot C d c
           ≅ iwiFamT k kp ki X' A' N' D' Ot' C' d' c' @ iwiL l lp li ] ->
       IWiPosGeq G Γ lp li X n n' d d' c c' ->
       [ G ; Γ ⊢ tyDVec (iwiL l lp li) n (iwiFamT l lp li X A N D Ot C d c)
           ≈ tyDVec (iwiL k kp ki) n' (iwiFamT k kp ki X' A' N' D' Ot' C' d' c') @ iwiL l lp li ])
    (fun w w' _ => forall n n', [ G ; Γ ⊢g n ⤳* w : tyNat @ lzero ] -> [ G ; Γ ⊢g n' ⤳* w' : tyNat @ lzero ] ->
       forall d d' c c',
       [ G ; Γ ,, tyFin n @ lzero ⊢g iwiFamT l lp li X A N D Ot C d c
           ≅ iwiFamT k kp ki X' A' N' D' Ot' C' d' c' @ iwiL l lp li ] ->
       IWiPosGeq G Γ lp li X n n' d d' c c' ->
       [ G ; Γ ⊢ tyDVec (iwiL l lp li) n (iwiFamT l lp li X A N D Ot C d c)
           ≈ tyDVec (iwiL k kp ki) n' (iwiFamT k kp ki X' A' N' D' Ot' C' d' c') @ iwiL l lp li ])).
  - intros t t' w w' Ht Ht' _ _ IH. exact (IH t t' Ht Ht').
  - (* zero *)
    intros n n' Hn Hn' d d' c c' HF _.
    pose proof (tmred_eq _ _ _ _ _ _ _ Hn) as En. pose proof (tmred_eq _ _ _ _ _ _ _ Hn') as En'.
    assert (Enn : [ G ; Γ ⊢g n ≅ n' : tyNat @ lzero ]) by (eapply eqtm_trans; [exact En | apply eqtm_sym, En']).
    apply (Step n n' zero zero _ _ Hn Hn' Enn HF).
    pose proof (fin_stab_eqty En HF) as HF0.
    assert (HF0' : [ G ; Γ ,, tyFin zero @ lzero ⊢g iwiFamT k kp ki X' A' N' D' Ot' C' d' c' @ iwiL k kp ki ])
      by (eapply wft_lconv; [exact (eqty_wf_r ge_typeof HF0) | exact (lequiv_sym _ _ _ HLL)]).
    eapply geq_ty_exp; [exact (tyred_dvec_zero HL (eqty_wf_l ge_typeof HF0))
                       | exact (tyred_lconv _ _ _ _ (tyred_dvec_zero HL' HF0') HLL) |].
    exact (geq_ty_unit (ctx_of_tm (eqtm_wf_l ge_typeof En)) HLL).
  - (* successor *)
    intros s s' Hss IH n n' Hn Hn' d d' c c' HF HP.
    pose proof (tmred_eq _ _ _ _ _ _ _ Hn) as En. pose proof (tmred_eq _ _ _ _ _ _ _ Hn') as En'.
    pose proof (geq_tm_sound (NatRel_geq Hss)) as Es.
    assert (Enn : [ G ; Γ ⊢g n ≅ n' : tyNat @ lzero ]).
    { eapply eqtm_trans; [exact En | eapply eqtm_trans; [apply eqtm_succ; [exact ge_notV | exact Es] | apply eqtm_sym, En']]. }
    pose proof (eqtm_wf_l ge_typeof Es) as Hs. pose proof (eqtm_wf_r ge_typeof Es) as Hs'.
    pose proof (ctx_of_tm Hs) as HΓ.
    apply (Step n n' (succ s) (succ s') _ _ Hn Hn' Enn HF).
    pose proof (fin_stab_eqty En HF) as HF1. pose proof (eqty_wf_l ge_typeof HF1) as HF1w.
    assert (HF1' : [ G ; Γ ,, tyFin (succ s') @ lzero ⊢g iwiFamT k kp ki X' A' N' D' Ot' C' d' c' @ iwiL k kp ki ]).
    { eapply wft_lconv; [| exact (lequiv_sym _ _ _ HLL)].
      assert (Y : [ G ; Γ ⊢g n ≅ succ s' : tyNat @ lzero ]) by (eapply eqtm_trans; [exact Enn | exact En']).
      exact (eqty_wf_r ge_typeof (fin_stab_eqty Y HF)). }
    eapply geq_ty_exp; [exact (tyred_dvec_succ HL HF1w Hs) | exact (tyred_lconv _ _ _ _ (tyred_dvec_succ HL' HF1' Hs') HLL) |].
    assert (HH : [ G ; Γ ⊢g dvecHd s (iwiFamT l lp li X A N D Ot C d c) @ iwiL l lp li ])
      by exact (wf_ty_single ge_typeof HF1w (fin_inl_wf ge_typeof ge_notV ge_compt Hs)).
    assert (HΓH : [ G ; Γ ,, dvecHd s (iwiFamT l lp li X A N D Ot C d c) @ iwiL l lp li ⊢g ]) by exact (ext_wf_g HH HL).
    eapply geq_ty_lconv; [apply geq_ty_sig; [exact HLL | exact HLL | exact HH | |] | apply lequiv_sym, lmax_idem, HL].
    + pose proof (iwiFamT_nf _ _ _ _ _ _ _ _ _ _ _ (wf_ty_nf (eqty_wf_l ge_typeof HF))) as (Nd & Nc).
      pose proof (iwiFamT_nf _ _ _ _ _ _ _ _ _ _ _ (wf_ty_nf (eqty_wf_r ge_typeof HF))) as (Nd' & Nc').
      pose proof (wf_tm_nf (eqtm_wf_l ge_typeof Enn)) as Nn. pose proof (wf_tm_nf (eqtm_wf_r ge_typeof Enn)) as Nn'.
      rewrite !iwiFamT_single by eauto using wf_ty_nf, wf_tm_nf.
      destruct (HP (kw_self HΓ) (posHd s) (posHd s')) as (Hd0 & Gd & Gc).
      { rewrite !ktm_self by assumption. apply pos_hd; [exact Hn | exact Hn' | exact Hss]. }
      rewrite ktyl_self in Hd0 by assumption. rewrite !ktyl_self in Gd by assumption.
      rewrite ktyl_self, !ktmll_self, kty_self in Gc by assumption.
      exact (iwi_field_geq HE HG Hd0 Gd Gc).
    + rewrite !dvecTl_eq, !iwiFamT_mv.
      apply (geq_ty_wk (wkr_shift1 _ _ _) HΓH). apply IH.
      * rewrite <- !iwiFamT_mv. exact (dvecMv_eqty ge_typeof ge_notV ge_compt Hs Hs' Es HF1w HF1).
      * exact (IWiPosGeq_tl HP Hn Hn').
  - (* neutral *)
    intros ν ν' Hνν n n' Hn Hn' d d' c c' HF HP.
    pose proof (tmred_eq _ _ _ _ _ _ _ Hn) as En. pose proof (tmred_eq _ _ _ _ _ _ _ Hn') as En'.
    pose proof (geq_tm_sound (gne_tm_geq Hνν)) as Eν.
    assert (Enn : [ G ; Γ ⊢g n ≅ n' : tyNat @ lzero ]).
    { eapply eqtm_trans; [exact En | eapply eqtm_trans; [exact Eν | apply eqtm_sym, En']]. }
    apply (Step n n' ν ν' _ _ Hn Hn' Enn HF).
    pose proof (fin_stab_eqty En HF) as HFν. pose proof (eqty_wf_l ge_typeof HFν) as HFνw.
    pose proof (ctx_of_ty HFνw) as HΓν.
    apply gne_ty_geq, (gne_ty_dvec HLL Hνν HFνw).
    pose proof (iwiFamT_nf _ _ _ _ _ _ _ _ _ _ _ (wf_ty_nf (eqty_wf_l ge_typeof HF))) as (Nd & Nc).
    pose proof (iwiFamT_nf _ _ _ _ _ _ _ _ _ _ _ (wf_ty_nf (eqty_wf_r ge_typeof HF))) as (Nd' & Nc').
    set (ρ1 := kw_wk1 HΓν).
    assert (HΓν' : [ G ; Γ ,, tyFin ν @ lzero ⊢[ typeof ge_layer ] ]) by (rewrite ge_typeof; exact HΓν).
    destruct (HP ρ1 (var 0) (var 0)) as (Hd0 & Gd & Gc).
    { unfold ktm, ρ1, kw_wk1, kw_loc; cbn [kw_G kw_Δ kw_γ kw_gk kw_r kw_rk gwa kw_mk]. change (wk_ren wk1) with ↑.
      apply pos_ne.
      - exact (wk1_eqtm_g _ _ _ _ _ _ _ _ _ HΓν' Enn).
      - apply gne_tm_var. eapply wf_conv; [exact (var0_wf_g _ _ _ _ _ HΓν') |].
        rewrite ge_typeof. change (tyFin n⟨↑⟩) with (tyFin n)⟨↑⟩. apply (wk1_eqty_g _ _ _ _ _ _ _ _ HΓν').
        apply eqty_fin; [exact ge_notV | exact En]. }
    unfold ktyl, ktmll, kty, ρ1, kw_wk1, kw_loc in Hd0, Gd, Gc;
      cbn [kw_G kw_Δ kw_γ kw_gk kw_r kw_rk gwa kw_mk] in Hd0, Gd, Gc.
    change (wk_ren wk1) with ↑ in Hd0, Gd, Gc.
    rewrite !liftshift_single_var_ty in Hd0, Gd, Gc by assumption.
    rewrite (liftshift_single_var_ty d') in Gd by assumption.
    rewrite !lift2shift_llift_single_var in Gc by assumption.
    exact (iwi_field_geq (IWiEq_wk1 ge_typeof ge_notV HE HΓν) (IWiGeq_wk1 HE HG HΓν) Hd0 Gd Gc).
Qed.

(** At a successor: the head's and the tail's types (the tail in any
    context extending [Γ] by one entry). *)
Lemma iwi_succ_geq {G Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' n n' m m' d d' c c'} :
  IWiEq (G := G) (i := ge_layer) Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' ->
  IWiGeq G Γ l lp li X X' A A' N N' D D' Ot Ot' C C' ->
  [ G ; Γ ⊢g n ⤳* succ m : tyNat @ lzero ] -> [ G ; Γ ⊢g n' ⤳* succ m' : tyNat @ lzero ] -> NatRel G Γ m m' ->
  [ G ; Γ ,, tyFin n @ lzero ⊢g iwiFamT l lp li X A N D Ot C d c
      ≅ iwiFamT k kp ki X' A' N' D' Ot' C' d' c' @ iwiL l lp li ] ->
  IWiPosGeq G Γ lp li X n n' d d' c c' ->
  [ G ; Γ ⊢ dvecHd m (iwiFamT l lp li X A N D Ot C d c)
      ≈ dvecHd m' (iwiFamT k kp ki X' A' N' D' Ot' C' d' c') @ iwiL l lp li ] /\
  (forall H lh, [ G ; Γ ,, H @ lh ⊢g ] ->
     [ G ; Γ ,, H @ lh ⊢ dvecTl (iwiL l lp li) m (iwiFamT l lp li X A N D Ot C d c)
         ≈ dvecTl (iwiL k kp ki) m' (iwiFamT k kp ki X' A' N' D' Ot' C' d' c') @ iwiL l lp li ]).
Proof using EL.
  intros HE HG Hn Hn' Hmm HF HP.
  pose proof HE as (_ & _ & _ & HS & _).
  pose proof (IWiSig_nf HS) as (NX & NA & NN & ND & NO & NC).
  pose proof (IWiSig_nf (IWiEq_sig_r ge_typeof ge_notV HE)) as (NX' & NA' & NN' & ND' & NO' & NC').
  pose proof (tmred_eq _ _ _ _ _ _ _ Hn) as En. pose proof (tmred_eq _ _ _ _ _ _ _ Hn') as En'.
  pose proof (geq_tm_sound (NatRel_geq Hmm)) as Em.
  pose proof (eqtm_wf_l ge_typeof Em) as Hm. pose proof (eqtm_wf_r ge_typeof Em) as Hm'.
  pose proof (ctx_of_tm Hm) as HΓ.
  pose proof (fin_stab_eqty En HF) as HF1. pose proof (eqty_wf_l ge_typeof HF1) as HF1w.
  split.
  - pose proof (iwiFamT_nf _ _ _ _ _ _ _ _ _ _ _ (wf_ty_nf (eqty_wf_l ge_typeof HF))) as (Nd & Nc).
    pose proof (iwiFamT_nf _ _ _ _ _ _ _ _ _ _ _ (wf_ty_nf (eqty_wf_r ge_typeof HF))) as (Nd' & Nc').
    pose proof (wf_tm_nf (eqtm_wf_l ge_typeof En)) as Nn. pose proof (wf_tm_nf (eqtm_wf_l ge_typeof En')) as Nn'.
    rewrite !iwiFamT_single by assumption.
    destruct (HP (kw_self HΓ) (posHd m) (posHd m')) as (Hd0 & Gd & Gc).
    { rewrite !ktm_self by assumption. apply pos_hd; [exact Hn | exact Hn' | exact Hmm]. }
    rewrite ktyl_self in Hd0 by assumption. rewrite !ktyl_self in Gd by assumption.
      rewrite ktyl_self, !ktmll_self, kty_self in Gc by assumption.
    exact (iwi_field_geq HE HG Hd0 Gd Gc).
  - intros H lh HΓH. rewrite !dvecTl_eq, !iwiFamT_mv.
    apply (geq_ty_wk (wkr_shift1 _ _ _) HΓH). apply (iwi_dvec_geq HE HG _ _ Hmm).
    + rewrite <- !iwiFamT_mv. exact (dvecMv_eqty ge_typeof ge_notV ge_compt Hm Hm' Em HF1w HF1).
    + exact (IWiPosGeq_tl HP Hn Hn').
Qed.

End IWiAux.
