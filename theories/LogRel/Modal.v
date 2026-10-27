(** * The contextual-type cases of the relation ([j = M], 07a:686–765)

    What the properties of the relation need about [ModRel]: conversion of
    the right-hand side, irrelevance, symmetry, transitivity and Kripke
    weakening.  Only the laws of the payload ([VPLaws]) are used. *)
From DeLaM.LogRel Require Export Basics.

Section Modal.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

(** ** Normal forms *)

Lemma CTypNf_whnf_l {G Γ Δ k w w'} : CTypNf G Γ Δ k w w' -> whnf w.
Proof. destruct 1 as [T1 T1' Hc | ν ν' Hn]; [apply whnf_boxT | exact (whnf_ne _ (gne_tm_whne_l Hn))]. Qed.
Lemma CTypNf_whnf_r {G Γ Δ k w w'} : CTypNf G Γ Δ k w w' -> whnf w'.
Proof. destruct 1 as [T1 T1' Hc | ν ν' Hn]; [apply whnf_boxT | exact (whnf_ne _ (gne_tm_whne_r Hn))]. Qed.
Lemma CTrmNf_whnf_l {G Γ Δ A k w w'} : CTrmNf G Γ Δ A k w w' -> whnf w.
Proof. destruct 1 as [t1 t1' Hc | ν ν' Hn]; [apply whnf_boxt | exact (whnf_ne _ (gne_tm_whne_l Hn))]. Qed.
Lemma CTrmNf_whnf_r {G Γ Δ A k w w'} : CTrmNf G Γ Δ A k w w' -> whnf w'.
Proof. destruct 1 as [t1 t1' Hc | ν ν' Hn]; [apply whnf_boxt | exact (whnf_ne _ (gne_tm_whne_r Hn))]. Qed.

Lemma CTypNf_sym {G Γ Δ k w w'} : CTypNf G Γ Δ k w w' -> CTypNf G Γ Δ k w' w.
Proof.
  destruct 1 as [T1 T1' Hc | ν ν' Hn]; constructor; [now apply vpl_tyc_sym | now apply gne_tm_sym].
Qed.
Lemma CTrmNf_sym {G Γ Δ A k w w'} : CTrmNf G Γ Δ A k w w' -> CTrmNf G Γ Δ A k w' w.
Proof.
  destruct 1 as [t1 t1' Hc | ν ν' Hn]; constructor; [now apply vpl_tmc_sym | now apply gne_tm_sym].
Qed.

Lemma CTypNf_trans {G Γ Δ k w1 w2 w3} :
  CTypNf G Γ Δ k w1 w2 -> CTypNf G Γ Δ k w2 w3 -> CTypNf G Γ Δ k w1 w3.
Proof.
  destruct 1 as [T1 T2 H12 | ν1 ν2 H12]; intros H23.
  - inversion H23 as [T2' T3 H23' | ν2 ν3 H23']; subst.
    + constructor. eapply vpl_tyc_trans; eassumption.
    + pose proof (gne_tm_whne_l H23') as Hw. inversion Hw.
  - inversion H23 as [T2 T3 H23' | ν2' ν3 H23']; subst.
    + pose proof (gne_tm_whne_r H12) as Hw. inversion Hw.
    + constructor. eapply gne_tm_trans; eassumption.
Qed.
Lemma CTrmNf_trans {G Γ Δ A k w1 w2 w3} :
  CTrmNf G Γ Δ A k w1 w2 -> CTrmNf G Γ Δ A k w2 w3 -> CTrmNf G Γ Δ A k w1 w3.
Proof.
  destruct 1 as [t1 t2 H12 | ν1 ν2 H12]; intros H23.
  - inversion H23 as [t2' t3 H23' | ν2 ν3 H23']; subst.
    + constructor. eapply vpl_tmc_trans; eassumption.
    + pose proof (gne_tm_whne_l H23') as Hw. inversion Hw.
  - inversion H23 as [t2 t3 H23' | ν2' ν3 H23']; subst.
    + pose proof (gne_tm_whne_r H12) as Hw. inversion Hw.
    + constructor. eapply gne_tm_trans; eassumption.
Qed.

(** Conversion to a related context (and type, and annotation). *)
Lemma CTypNf_conv {G Γ Δ Δ' k k' w w'} :
  vp_ctx lr_vp G Δ Δ' -> lequiv (gL G) k k' ->
  [ G ; Γ ⊢g tyCTyp Δ k ≅ tyCTyp Δ' k' @ lzero ] ->
  CTypNf G Γ Δ k w w' -> CTypNf G Γ Δ' k' w w'.
Proof.
  intros HΔ Hk HC. destruct 1 as [T1 T1' Hc | ν ν' Hn]; constructor.
  - eapply vpl_tyc_lconv; [exact Hk | eapply vpl_tyc_ctx; eassumption].
  - eapply gne_tm_conv; eassumption.
Qed.
Lemma CTrmNf_conv {G Γ Δ Δ' A A' k k' w w'} :
  vp_ctx lr_vp G Δ Δ' -> vp_ty lr_vp G Δ A A' k -> lequiv (gL G) k k' ->
  [ G ; Γ ⊢g tyCTrm Δ A k ≅ tyCTrm Δ' A' k' @ lzero ] ->
  CTrmNf G Γ Δ A k w w' -> CTrmNf G Γ Δ' A' k' w w'.
Proof.
  intros HΔ HA Hk HC. destruct 1 as [t1 t1' Hc | ν ν' Hn]; constructor.
  - eapply vpl_tmc_lconv; [exact Hk|]. eapply vpl_tmc_ctx; [exact HΔ|].
    eapply vpl_tmc_ty; eassumption.
  - eapply gne_tm_conv; eassumption.
Qed.

(** ** Term relations *)

Lemma CTypRel_conv_r {G Γ Δ Δ' Δ'' k k' k'' t t'} :
  vp_ctx lr_vp G Δ' Δ'' -> lequiv (gL G) k' k'' ->
  [ G ; Γ ⊢g tyCTyp Δ' k' ≅ tyCTyp Δ'' k'' @ lzero ] ->
  CTypRel G Γ Δ Δ' k k' t t' -> CTypRel G Γ Δ Δ'' k k'' t t'.
Proof.
  intros HΔ Hk HC (w & w' & Hw & Hw' & Heq & Heq' & Hn & Hn').
  exists w, w'. refine (conj Hw (conj _ (conj Heq (conj _ (conj Hn _))))).
  - eapply tmred_conv; [apply ge_typeof | exact Hw' | exact HC].
  - eapply geq_tm_conv; eassumption.
  - exact (CTypNf_conv HΔ Hk HC Hn').
Qed.

Lemma CTrmRel_conv_r {G Γ Δ Δ' Δ'' A A' A'' k k' k'' t t'} :
  vp_ctx lr_vp G Δ' Δ'' -> vp_ty lr_vp G Δ' A' A'' k' -> lequiv (gL G) k' k'' ->
  [ G ; Γ ⊢g tyCTrm Δ' A' k' ≅ tyCTrm Δ'' A'' k'' @ lzero ] ->
  CTrmRel G Γ Δ Δ' A A' k k' t t' -> CTrmRel G Γ Δ Δ'' A A'' k k'' t t'.
Proof.
  intros HΔ HA Hk HC (w & w' & Hw & Hw' & Heq & Heq' & Hn & Hn').
  exists w, w'. refine (conj Hw (conj _ (conj Heq (conj _ (conj Hn _))))).
  - eapply tmred_conv; [apply ge_typeof | exact Hw' | exact HC].
  - eapply geq_tm_conv; eassumption.
  - exact (CTrmNf_conv HΔ HA Hk HC Hn').
Qed.

Lemma CTypRel_sym {G Γ Δ Δ' k k' t t'} :
  CTypRel G Γ Δ Δ' k k' t t' -> CTypRel G Γ Δ' Δ k' k t' t.
Proof.
  intros (w & w' & Hw & Hw' & Heq & Heq' & Hn & Hn').
  exists w', w. refine (conj Hw' (conj Hw (conj (geq_tm_sym Heq') (conj (geq_tm_sym Heq) _)))).
  exact (conj (CTypNf_sym Hn') (CTypNf_sym Hn)).
Qed.

Lemma CTrmRel_sym {G Γ Δ Δ' A A' k k' t t'} :
  CTrmRel G Γ Δ Δ' A A' k k' t t' -> CTrmRel G Γ Δ' Δ A' A k' k t' t.
Proof.
  intros (w & w' & Hw & Hw' & Heq & Heq' & Hn & Hn').
  exists w', w. refine (conj Hw' (conj Hw (conj (geq_tm_sym Heq') (conj (geq_tm_sym Heq) _)))).
  exact (conj (CTrmNf_sym Hn') (CTrmNf_sym Hn)).
Qed.

(** Composition, the second pair being at the right-hand index of the first. *)
Lemma CTypRel_trans {G Γ Δ1 Δ2 Δ3 k1 k2 k3 t1 t2 t3} :
  vp_ctx lr_vp G Δ2 Δ1 -> lequiv (gL G) k2 k1 ->
  [ G ; Γ ⊢g tyCTyp Δ2 k2 ≅ tyCTyp Δ1 k1 @ lzero ] ->
  vp_ctx lr_vp G Δ3 Δ2 -> lequiv (gL G) k3 k2 ->
  [ G ; Γ ⊢g tyCTyp Δ3 k3 ≅ tyCTyp Δ2 k2 @ lzero ] ->
  CTypRel G Γ Δ1 Δ2 k1 k2 t1 t2 -> CTypRel G Γ Δ2 Δ3 k2 k3 t2 t3 -> CTypRel G Γ Δ1 Δ2 k1 k2 t1 t3.
Proof.
  intros HΔ Hk HC HΔ3 Hk3 HC3 H12 H23. apply (CTypRel_conv_r HΔ3 Hk3 HC3) in H23.
  revert H12 H23.
  intros (w1 & w2 & Hw1 & Hw2 & E1 & E1' & N1 & N1') (w2' & w3 & Hw2' & Hw3 & E2 & E2' & N2 & N2').
  assert (w2' = w2) as ->
    by (eapply tmred_whnf_det; [exact Hw2' | exact Hw2 | exact (CTypNf_whnf_l N2) | exact (CTypNf_whnf_r N1)]).
  exists w1, w3. refine (conj Hw1 (conj Hw3 (conj _ (conj _ (conj _ _))))).
  - eapply geq_tm_trans; [exact E1 | eapply geq_tm_conv; eassumption].
  - eapply geq_tm_trans; eassumption.
  - eapply CTypNf_trans; [exact N1 | exact (CTypNf_conv HΔ Hk HC N2)].
  - eapply CTypNf_trans; eassumption.
Qed.

Lemma CTrmRel_trans {G Γ Δ1 Δ2 Δ3 A1 A2 A3 k1 k2 k3 t1 t2 t3} :
  vp_ctx lr_vp G Δ2 Δ1 -> vp_ty lr_vp G Δ2 A2 A1 k2 -> lequiv (gL G) k2 k1 ->
  [ G ; Γ ⊢g tyCTrm Δ2 A2 k2 ≅ tyCTrm Δ1 A1 k1 @ lzero ] ->
  vp_ctx lr_vp G Δ3 Δ2 -> vp_ty lr_vp G Δ3 A3 A2 k3 -> lequiv (gL G) k3 k2 ->
  [ G ; Γ ⊢g tyCTrm Δ3 A3 k3 ≅ tyCTrm Δ2 A2 k2 @ lzero ] ->
  CTrmRel G Γ Δ1 Δ2 A1 A2 k1 k2 t1 t2 -> CTrmRel G Γ Δ2 Δ3 A2 A3 k2 k3 t2 t3 ->
  CTrmRel G Γ Δ1 Δ2 A1 A2 k1 k2 t1 t3.
Proof.
  intros HΔ HA Hk HC HΔ3 HA3 Hk3 HC3 H12 H23. apply (CTrmRel_conv_r HΔ3 HA3 Hk3 HC3) in H23.
  revert H12 H23.
  intros (w1 & w2 & Hw1 & Hw2 & E1 & E1' & N1 & N1') (w2' & w3 & Hw2' & Hw3 & E2 & E2' & N2 & N2').
  assert (w2' = w2) as ->
    by (eapply tmred_whnf_det; [exact Hw2' | exact Hw2 | exact (CTrmNf_whnf_l N2) | exact (CTrmNf_whnf_r N1)]).
  exists w1, w3. refine (conj Hw1 (conj Hw3 (conj _ (conj _ (conj _ _))))).
  - eapply geq_tm_trans; [exact E1 | eapply geq_tm_conv; eassumption].
  - eapply geq_tm_trans; eassumption.
  - eapply CTrmNf_trans; [exact N1 | exact (CTrmNf_conv HΔ HA Hk HC N2)].
  - eapply CTrmNf_trans; eassumption.
Qed.

(** ** The two derivations of a left type agree *)

Ltac mod_agree :=
  match goal with
  | H1 : tyred ?G ?i ?Γ ?T ?W1 ?l, H2 : tyred ?G ?i ?Γ ?T ?W2 ?l' |- _ =>
      let Heq := fresh "Heq" in
      assert (Heq : W1 = W2) by (eapply tyred_whnf_det; [exact H1 | exact H2 | constructor | constructor]);
      clear H2; first [discriminate Heq | injection Heq; intros; subst]
  end.

Lemma ModRel_irrel {G Γ T T' T'' l R R'} :
  ModRel G Γ T T' l R -> ModRel G Γ T T'' l R' -> releq R R'.
Proof.
  destruct 1 as [T T' l Δ Δ' k k' R Hl Hk HT HT' HΔ Hgeq HR
                | T T' l Δ Δ' A A' k k' R Hl Hk HT HT' HΔ HA HA' Hgeq HR];
    destruct 1 as [? T'' ? Δ2 Δ'' k2 k'' R' Hl2 Hk2 HT2 HT'' HΔ2 Hgeq2 HR2
                  | ? T'' ? Δ2 Δ'' A2 A'' k2 k'' R' Hl2 Hk2 HT2 HT'' HΔ2 HA2 HA2' Hgeq2 HR2];
    mod_agree.
  - assert (HΔ' : vp_ctx lr_vp G Δ' Δ'') by (eapply vpl_ctx_trans; [apply vpl_ctx_sym|]; eassumption).
    assert (Hk' : lequiv (gL G) k' k'') by (eapply lequiv_trans; [apply lequiv_sym|]; eassumption).
    assert (HC : [ G ; Γ ⊢g tyCTyp Δ' k' ≅ tyCTyp Δ'' k'' @ lzero ])
      by (eapply eqty_trans; [apply eqty_sym|]; apply geq_ty_sound; eassumption).
    intros t t'; rewrite (HR t t'), (HR2 t t'); split.
    + apply CTypRel_conv_r; assumption.
    + apply CTypRel_conv_r; [now apply vpl_ctx_sym | solve [apply lequiv_sym; assumption] | now apply eqty_sym].
  - assert (HΔ' : vp_ctx lr_vp G Δ' Δ'') by (eapply vpl_ctx_trans; [apply vpl_ctx_sym|]; eassumption).
    assert (Hk' : lequiv (gL G) k' k'') by (eapply lequiv_trans; [apply lequiv_sym|]; eassumption).
    assert (HC : [ G ; Γ ⊢g tyCTrm Δ' A' k' ≅ tyCTrm Δ'' A'' k'' @ lzero ])
      by (eapply eqty_trans; [apply eqty_sym|]; apply geq_ty_sound; eassumption).
    (* [A' ≈ A''] at [Δ], moved to [Δ'] and [k'] *)
    assert (HAA : vp_ty lr_vp G Δ' A' A'' k').
    { eapply vpl_ty_lconv; [exact Hk|]. eapply vpl_ty_ctx; [exact HΔ|].
      eapply vpl_ty_trans; [apply vpl_ty_sym|]; eassumption. }
    intros t t'; rewrite (HR t t'), (HR2 t t'); split.
    + apply CTrmRel_conv_r; assumption.
    + apply CTrmRel_conv_r; [now apply vpl_ctx_sym | | solve [apply lequiv_sym; assumption] | now apply eqty_sym].
      eapply vpl_ty_lconv; [exact Hk'|]. eapply vpl_ty_ctx; [exact HΔ'|]. now apply vpl_ty_sym.
Qed.

(** The right-hand type reduces to a contextual type. *)
Lemma ModRel_red_r {G Γ T T' l R} : ModRel G Γ T T' l R ->
  (exists Δ k, [ G ; Γ ⊢g T' ⤳* tyCTyp Δ k @ l ]) \/
  (exists Δ A k, [ G ; Γ ⊢g T' ⤳* tyCTrm Δ A k @ l ]).
Proof. destruct 1; eauto. Qed.

(** ** Symmetry *)

Lemma ModRel_sym {G Γ T T' l R} :
  ModRel G Γ T T' l R -> ModRel G Γ T' T l (fun t t' => R t' t).
Proof.
  destruct 1 as [T T' l Δ Δ' k k' R Hl Hk HT HT' HΔ Hgeq HR
                | T T' l Δ Δ' A A' k k' R Hl Hk HT HT' HΔ HA HA' Hgeq HR].
  - eapply (MRctyp _ _ _ _ _ Δ' Δ k' k); auto using lequiv_sym, vpl_ctx_sym, geq_ty_sym.
    intros t t'; rewrite (HR t' t); split; apply CTypRel_sym.
  - eapply (MRctrm _ _ _ _ _ Δ' Δ A' A k' k); auto using lequiv_sym, vpl_ctx_sym, geq_ty_sym.
    intros t t'; rewrite (HR t' t); split; apply CTrmRel_sym.
Qed.

(** ** Transitivity *)

Lemma ModRel_trans {G Γ T1 T2 T3 l R12 R23} :
  ModRel G Γ T1 T2 l R12 -> ModRel G Γ T2 T3 l R23 ->
  ModRel G Γ T1 T3 l R12 /\ (forall t1 t2 t3, R12 t1 t2 -> R23 t2 t3 -> R12 t1 t3).
Proof.
  destruct 1 as [T1 T2 l Δ1 Δ2 k1 k2 R12 Hl Hk HT1 HT2 HΔ Hgeq HR
                | T1 T2 l Δ1 Δ2 A1 A2 k1 k2 R12 Hl Hk HT1 HT2 HΔ HA HA' Hgeq HR];
    destruct 1 as [? T3 ? Δ2' Δ3 k2' k3 R23 Hl' Hk' HT2' HT3 HΔ' Hgeq' HR'
                  | ? T3 ? Δ2' Δ3 A2' A3 k2' k3 R23 Hl' Hk' HT2' HT3 HΔ' HB HB' Hgeq' HR'];
    mod_agree.
  - pose proof (geq_ty_sound Hgeq') as HC23.
    pose proof (eqty_sym _ _ _ _ _ _ (geq_ty_sound Hgeq)) as HC21.
    split.
    + eapply (MRctyp _ _ _ _ _ Δ1 Δ3 k1 k3).
      * exact Hl.
      * eapply lequiv_trans; eassumption.
      * exact HT1.
      * exact HT3.
      * eapply vpl_ctx_trans; eassumption.
      * eapply geq_ty_trans; eassumption.
      * intros t t'; rewrite (HR t t'); split.
        -- apply CTypRel_conv_r; auto.
        -- apply CTypRel_conv_r; [now apply vpl_ctx_sym | solve [apply lequiv_sym; assumption] | now apply eqty_sym].
    + intros t1 t2 t3 H12 H23. apply HR in H12. apply HR' in H23. apply HR.
      exact (CTypRel_trans (vpl_ctx_sym HΔ) (lequiv_sym _ _ _ Hk) HC21
               (vpl_ctx_sym HΔ') (lequiv_sym _ _ _ Hk') (eqty_sym _ _ _ _ _ _ HC23) H12 H23).
  - pose proof (geq_ty_sound Hgeq') as HC23.
    pose proof (eqty_sym _ _ _ _ _ _ (geq_ty_sound Hgeq)) as HC21.
    split.
    + eapply (MRctrm _ _ _ _ _ Δ1 Δ3 A1 A3 k1 k3).
      * exact Hl.
      * eapply lequiv_trans; eassumption.
      * exact HT1.
      * exact HT3.
      * eapply vpl_ctx_trans; eassumption.
      * (* [A1 ≈ A2] at [Δ1], [A2 ≈ A3] at [Δ2] *)
        eapply vpl_ty_trans; [exact HA|].
        eapply vpl_ty_lconv; [apply lequiv_sym, Hk|]. eapply vpl_ty_ctx; [apply vpl_ctx_sym, HΔ | exact HB].
      * eapply vpl_ty_trans; [exact HB'|].
        eapply vpl_ty_lconv; [exact Hk'|]. eapply vpl_ty_ctx; [exact HΔ' | exact HA'].
      * eapply geq_ty_trans; eassumption.
      * intros t t'; rewrite (HR t t'); split.
        -- apply CTrmRel_conv_r; auto.
        -- apply CTrmRel_conv_r; [now apply vpl_ctx_sym | | solve [apply lequiv_sym; assumption] | now apply eqty_sym].
           eapply vpl_ty_lconv; [exact Hk'|]. eapply vpl_ty_ctx; [exact HΔ' | now apply vpl_ty_sym].
    + intros t1 t2 t3 H12 H23. apply HR in H12. apply HR' in H23. apply HR.
      exact (CTrmRel_trans (vpl_ctx_sym HΔ) HA' (lequiv_sym _ _ _ Hk) HC21
               (vpl_ctx_sym HΔ') HB' (lequiv_sym _ _ _ Hk') (eqty_sym _ _ _ _ _ _ HC23) H12 H23).
Qed.

(** ** Kripke weakening *)

Section KwMod.
Context {G : gctx} {Γ : ctx} (ρ : kwk G Γ).

Lemma kty_tyCTyp Δ k : kty ρ (tyCTyp Δ k) = tyCTyp Δ⟦kw_γ ρ⟧ k.
Proof. unfold kty; now rewrite gwa_tyCTyp. Qed.
Lemma kty_tyCTrm Δ A k : kty ρ (tyCTrm Δ A k) = tyCTrm Δ⟦kw_γ ρ⟧ A⟦kw_γ ρ⟧ k.
Proof. unfold kty; now rewrite gwa_tyCTrm. Qed.
Lemma ktm_boxT T : ktm ρ (boxT T) = boxT T⟦kw_γ ρ⟧.
Proof. unfold ktm; now destruct (kw_γ ρ). Qed.
Lemma ktm_boxt t : ktm ρ (boxt t) = boxt t⟦kw_γ ρ⟧.
Proof. unfold ktm; now destruct (kw_γ ρ). Qed.

Lemma CTypNf_kw {Δ k w w'} : CTypNf G Γ Δ k w w' ->
  CTypNf (kw_G ρ) (kw_Δ ρ) Δ⟦kw_γ ρ⟧ k (ktm ρ w) (ktm ρ w').
Proof.
  destruct 1 as [T1 T1' Hc | ν ν' Hn].
  - rewrite !ktm_boxT. constructor. exact (vpl_tyc_gwk (kw_gok ρ) (kw_glob ρ) Hc).
  - constructor. pose proof (kw_gne_tm ρ Hn) as X. now rewrite kty_tyCTyp in X.
Qed.
Lemma CTrmNf_kw {Δ A k w w'} : CTrmNf G Γ Δ A k w w' ->
  CTrmNf (kw_G ρ) (kw_Δ ρ) Δ⟦kw_γ ρ⟧ A⟦kw_γ ρ⟧ k (ktm ρ w) (ktm ρ w').
Proof.
  destruct 1 as [t1 t1' Hc | ν ν' Hn].
  - rewrite !ktm_boxt. constructor. exact (vpl_tmc_gwk (kw_gok ρ) (kw_glob ρ) Hc).
  - constructor. pose proof (kw_gne_tm ρ Hn) as X. now rewrite kty_tyCTrm in X.
Qed.

Lemma CTypRel_kw {Δ Δ' k k' t t'} : CTypRel G Γ Δ Δ' k k' t t' ->
  CTypRel (kw_G ρ) (kw_Δ ρ) Δ⟦kw_γ ρ⟧ Δ'⟦kw_γ ρ⟧ k k' (ktm ρ t) (ktm ρ t').
Proof.
  intros (w & w' & Hw & Hw' & Heq & Heq' & Hn & Hn').
  exists (ktm ρ w), (ktm ρ w').
  pose proof (kw_tmred ρ Hw) as X1. pose proof (kw_tmred ρ Hw') as X2.
  pose proof (kw_geq_tm ρ Heq) as X3. pose proof (kw_geq_tm ρ Heq') as X4.
  repeat rewrite kty_tyCTyp in X1; repeat rewrite kty_tyCTyp in X2;
  repeat rewrite kty_tyCTyp in X3; repeat rewrite kty_tyCTyp in X4.
  exact (conj X1 (conj X2 (conj X3 (conj X4 (conj (CTypNf_kw Hn) (CTypNf_kw Hn')))))).
Qed.
Lemma CTrmRel_kw {Δ Δ' A A' k k' t t'} : CTrmRel G Γ Δ Δ' A A' k k' t t' ->
  CTrmRel (kw_G ρ) (kw_Δ ρ) Δ⟦kw_γ ρ⟧ Δ'⟦kw_γ ρ⟧ A⟦kw_γ ρ⟧ A'⟦kw_γ ρ⟧ k k' (ktm ρ t) (ktm ρ t').
Proof.
  intros (w & w' & Hw & Hw' & Heq & Heq' & Hn & Hn').
  exists (ktm ρ w), (ktm ρ w').
  pose proof (kw_tmred ρ Hw) as X1. pose proof (kw_tmred ρ Hw') as X2.
  pose proof (kw_geq_tm ρ Heq) as X3. pose proof (kw_geq_tm ρ Heq') as X4.
  repeat rewrite kty_tyCTrm in X1; repeat rewrite kty_tyCTrm in X2;
  repeat rewrite kty_tyCTrm in X3; repeat rewrite kty_tyCTrm in X4.
  exact (conj X1 (conj X2 (conj X3 (conj X4 (conj (CTrmNf_kw Hn) (CTrmNf_kw Hn')))))).
Qed.

Lemma ModRel_kwk {T T' l R} : ModRel G Γ T T' l R ->
  exists R', ModRel (kw_G ρ) (kw_Δ ρ) (kty ρ T) (kty ρ T') l R' /\
    forall t t', R t t' -> R' (ktm ρ t) (ktm ρ t').
Proof.
  pose proof (kw_gok ρ) as Hγ. pose proof (kw_glob ρ) as HG'.
  destruct 1 as [T T' l Δ Δ' k k' R Hl Hk HT HT' HΔ Hgeq HR
                | T T' l Δ Δ' A A' k k' R Hl Hk HT HT' HΔ HA HA' Hgeq HR].
  - exists (CTypRel (kw_G ρ) (kw_Δ ρ) Δ⟦kw_γ ρ⟧ Δ'⟦kw_γ ρ⟧ k k'). split.
    + pose proof (kw_tyred ρ HT) as X1. pose proof (kw_tyred ρ HT') as X2.
      pose proof (kw_geq_ty ρ Hgeq) as X3.
      repeat rewrite kty_tyCTyp in X1; repeat rewrite kty_tyCTyp in X2; repeat rewrite kty_tyCTyp in X3.
      eapply MRctyp; [exact (kw_lequiv ρ Hl) | exact (kw_lequiv ρ Hk) | exact X1 | exact X2
                     | exact (vpl_ctx_gwk Hγ HG' HΔ) | exact X3 | apply releq_refl].
    + intros t t' Ht. apply HR in Ht. exact (CTypRel_kw Ht).
  - exists (CTrmRel (kw_G ρ) (kw_Δ ρ) Δ⟦kw_γ ρ⟧ Δ'⟦kw_γ ρ⟧ A⟦kw_γ ρ⟧ A'⟦kw_γ ρ⟧ k k'). split.
    + pose proof (kw_tyred ρ HT) as X1. pose proof (kw_tyred ρ HT') as X2.
      pose proof (kw_geq_ty ρ Hgeq) as X3.
      repeat rewrite kty_tyCTrm in X1; repeat rewrite kty_tyCTrm in X2; repeat rewrite kty_tyCTrm in X3.
      eapply MRctrm; [exact (kw_lequiv ρ Hl) | exact (kw_lequiv ρ Hk) | exact X1 | exact X2
                     | exact (vpl_ctx_gwk Hγ HG' HΔ) | exact (vpl_ty_gwk Hγ HG' HA)
                     | exact (vpl_ty_gwk Hγ HG' HA') | exact X3 | apply releq_refl].
    + intros t t' Ht. apply HR in Ht. exact (CTrmRel_kw Ht).
Qed.

End KwMod.

End Modal.
