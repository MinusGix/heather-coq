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
End KwIWi.
End IWiAux.
