(** * Validity along level permutations (M3_DESIGN.md E14)

    Related substitutions and the relation's validity forms are stable
    under level permutations ([LR_perm]); worlds of the permuted global
    context are pulled back along the inverse. This gives the parameters
    of the [□] cases at M ([vpM]) along permutations, hence [LR_perm] and
    [LR_uwk] for the relation at M. *)
From DeLaM.Validity Require Export Payload.
From DeLaM.LogRel Require Export UPermLR.

Section UPermV.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe} `{VPP : VPPerm lr_vp}.

Lemma LRtm_perm {π πi l G Γ T T' t t'} : uperm π πi (gL G) -> LRtm l G Γ T T' t t' ->
  LRtm (lvsubst l (pφ π)) (Gp π G) Γ[pφ π]ᵤ T[pφ π]ᵤ T'[pφ π]ᵤ t[pφ π]ᵤ t'[pφ π]ᵤ.
Proof.
  unfold LRtm, LRrel. intros Hp (R & H & Ht). rewrite lmeasure_perm.
  destruct (LR_perm _ _ _ _ _ _ _ H _ _ Hp) as (R' & H' & Ek). exists R'. split; [exact H' |].
  destruct (LR_rel_dnf H _ _ Ht) as [N N']. exact (proj1 (Ek _ _ N N') Ht).
Qed.
Lemma LRty_perm {π πi l G Γ T T'} : uperm π πi (gL G) -> LRty l G Γ T T' ->
  LRty (lvsubst l (pφ π)) (Gp π G) Γ[pφ π]ᵤ T[pφ π]ᵤ T'[pφ π]ᵤ.
Proof.
  unfold LRty, LogRel. intros Hp (R & H). rewrite lmeasure_perm.
  destruct (LR_perm _ _ _ _ _ _ _ H _ _ Hp) as (R' & H' & _). exists R'. exact H'.
Qed.

Lemma SubRel_perm {π πi G} (Hp : uperm π πi (gL G)) Γ : forall Δ d d', SubRel G Γ Δ d d' ->
  SubRel (Gp π G) Γ[pφ π]ᵤ Δ[pφ π]ᵤ d[pφ π]ᵤ d'[pφ π]ᵤ.
Proof.
  induction Γ as [| g | Γ IH A l]; intros Δ d d'.
  1-2: cbn [SubRel usubst USubst_ctx ucsubst]; intros (HΔ & N1 & N2 & T1 & T2);
    refine (conj (pg_ctx Hp HΔ) (conj _ (conj _ (conj (lsub_tail_usubst _ _ _ _ T1) (lsub_tail_usubst _ _ _ _ T2)))));
    intros n; cbn [usubst USubst_lsub]; rewrite llk_ulsubst; apply dnf_us_tm.
  - cbn [SubRel usubst USubst_ctx ucsubst]. intros [Ht Hh]. split.
    + refine (SubRel_ext _ _ _ _ _ _ _ _ _ (IH _ _ _ Ht));
        intros n; cbn [usubst USubst_lsub]; rewrite !llk_ldrop, !llk_ulsubst, llk_ldrop; reflexivity.
    + pose proof (LRtm_perm Hp Hh) as X. rewrite !usubst_subst_ty in X.
      rewrite (subst_ext_ty A[pφ π]ᵤ (ldrop 1 d)[pφ π]ᵤ (ldrop 1 d[pφ π]ᵤ)),
        (subst_ext_ty A[pφ π]ᵤ (ldrop 1 d')[pφ π]ᵤ (ldrop 1 d'[pφ π]ᵤ)) in X
        by (intros n; cbn [usubst USubst_lsub]; rewrite !llk_ldrop, !llk_ulsubst, llk_ldrop; reflexivity).
      cbn [usubst USubst_lsub USubst_tm] in X |- *. rewrite !llk_ulsubst. exact X.
Qed.

(** ** Worlds of the permuted context, pulled back *)

Lemma gwk_pull {π πi G G'' γ} : uperm π πi (gL G) -> [ ⊢ G ] -> gwk_ok γ G'' (Gp π G) ->
  gwk_ok γ (Gp πi G'') G.
Proof.
  intros Hp HG Hγ. split; [exact (proj1 Hγ) |].
  pose proof (gwk_wf_usubst _ _ _ (pφ πi) (proj2 Hγ)) as X.
  unfold Gp, G_us, gctx_usubst in X |- *; cbn [gΨ] in X |- *.
  now rewrite (rt_gdecls (proj1 Hp) _ (wfg_dnf _ HG)) in X.
Qed.

Lemma VTy_pull {π πi G G'' γ Γ T T' l} : uperm π πi (gL G) -> gwk_ok γ G'' (Gp π G) -> dnfctx Γ ->
  VTy (Gp πi G'') Γ⟦γ⟧ T⟦γ⟧ T'⟦γ⟧ l ->
  VTy G'' Γ[pφ π]ᵤ⟦γ⟧ T[pφ π]ᵤ⟦γ⟧ T'[pφ π]ᵤ⟦γ⟧ (lvsubst l (pφ π)).
Proof.
  intros Hp Hγ NΓ HV Δ d d' HS.
  pose proof (ctx_glob _ _ _ (SubRel_ctx HS)) as HG''.
  pose proof (uperm_grow _ _ _ _ (proj1 Hγ) (uperm_inv _ _ _ Hp)) as Hpi''.
  pose proof (uperm_grow _ _ _ _ (proj1 Hγ) Hp) as Hp''.
  destruct (SubRel_dnf _ _ _ _ _ HS) as [Nd Nd']. pose proof (wf_ctx_dnf (SubRel_ctx HS)) as NΔ.
  pose proof (SubRel_perm (G := G'') Hpi'' _ _ _ _ HS) as HS1.
  rewrite usubst_gwa_ctx, (rt_ctx (proj1 Hp) _ NΓ) in HS1.
  pose proof (LRty_perm (G := Gp πi G'') Hp'' (HV _ _ _ HS1)) as Y.
  rewrite (Gp_rt Hpi'' HG''), (rt_ctx (proj1 (proj2 Hp)) _ NΔ) in Y.
  rewrite !usubst_subst_ty, !usubst_gwa_ty in Y.
  rewrite (subst_ext_ty _ d[pφ πi]ᵤ[pφ π]ᵤ d), (subst_ext_ty _ d'[pφ πi]ᵤ[pφ π]ᵤ d') in Y
    by (intros n; cbn [usubst USubst_lsub]; rewrite !llk_ulsubst; exact (rt_tm (proj1 (proj2 Hp)) _ (Nd n)) ||
        exact (rt_tm (proj1 (proj2 Hp)) _ (Nd' n))).
  exact Y.
Qed.

Lemma VTm_pull {π πi G G'' γ Γ t t' T l} : uperm π πi (gL G) -> gwk_ok γ G'' (Gp π G) -> dnfctx Γ ->
  VTm (Gp πi G'') Γ⟦γ⟧ t⟦γ⟧ t'⟦γ⟧ T⟦γ⟧ l ->
  VTm G'' Γ[pφ π]ᵤ⟦γ⟧ t[pφ π]ᵤ⟦γ⟧ t'[pφ π]ᵤ⟦γ⟧ T[pφ π]ᵤ⟦γ⟧ (lvsubst l (pφ π)).
Proof.
  intros Hp Hγ NΓ HV Δ d d' HS.
  pose proof (ctx_glob _ _ _ (SubRel_ctx HS)) as HG''.
  pose proof (uperm_grow _ _ _ _ (proj1 Hγ) (uperm_inv _ _ _ Hp)) as Hpi''.
  pose proof (uperm_grow _ _ _ _ (proj1 Hγ) Hp) as Hp''.
  destruct (SubRel_dnf _ _ _ _ _ HS) as [Nd Nd']. pose proof (wf_ctx_dnf (SubRel_ctx HS)) as NΔ.
  pose proof (SubRel_perm (G := G'') Hpi'' _ _ _ _ HS) as HS1.
  rewrite usubst_gwa_ctx, (rt_ctx (proj1 Hp) _ NΓ) in HS1.
  pose proof (LRtm_perm (G := Gp πi G'') Hp'' (HV _ _ _ HS1)) as Y.
  rewrite (Gp_rt Hpi'' HG''), (rt_ctx (proj1 (proj2 Hp)) _ NΔ) in Y.
  rewrite !usubst_subst_ty, !usubst_subst, !usubst_gwa_ty, !usubst_gwa_tm in Y.
  rewrite (subst_ext_ty _ d[pφ πi]ᵤ[pφ π]ᵤ d), (subst_ext_ty _ d'[pφ πi]ᵤ[pφ π]ᵤ d'),
    (subst_ext _ d[pφ πi]ᵤ[pφ π]ᵤ d), (subst_ext _ d'[pφ πi]ᵤ[pφ π]ᵤ d') in Y
    by (intros n; cbn [usubst USubst_lsub]; rewrite !llk_ulsubst; exact (rt_tm (proj1 (proj2 Hp)) _ (Nd n)) ||
        exact (rt_tm (proj1 (proj2 Hp)) _ (Nd' n))).
  exact Y.
Qed.

Lemma VTyG_perm {π πi G Γ T T' l} : uperm π πi (gL G) -> [ ⊢ G ] -> dnfctx Γ -> VTyG G Γ T T' l ->
  VTyG (Gp π G) Γ[pφ π]ᵤ T[pφ π]ᵤ T'[pφ π]ᵤ (lvsubst l (pφ π)).
Proof. intros Hp HG NΓ HV G'' γ Hγ. exact (VTy_pull Hp Hγ NΓ (HV _ _ (gwk_pull Hp HG Hγ))). Qed.
Lemma VTmG_perm {π πi G Γ t t' T l} : uperm π πi (gL G) -> [ ⊢ G ] -> dnfctx Γ -> VTmG G Γ t t' T l ->
  VTmG (Gp π G) Γ[pφ π]ᵤ t[pφ π]ᵤ t'[pφ π]ᵤ T[pφ π]ᵤ (lvsubst l (pφ π)).
Proof. intros Hp HG NΓ HV G'' γ Hγ. exact (VTm_pull Hp Hγ NΓ (HV _ _ (gwk_pull Hp HG Hγ))). Qed.

Lemma CtxRel_pull {π πi G G'' γ} : uperm π πi (gL G) -> gwk_ok γ G'' (Gp π G) ->
  forall Γ Γ', dnfctx Γ -> dnfctx Γ' -> CtxRel (Gp πi G'') Γ⟦γ⟧ Γ'⟦γ⟧ ->
  CtxRel G'' Γ[pφ π]ᵤ⟦γ⟧ Γ'[pφ π]ᵤ⟦γ⟧.
Proof.
  intros Hp Hγ. pose proof (uperm_grow _ _ _ _ (proj1 Hγ) Hp) as Hp''.
  induction Γ as [| g | Γ IH A l]; intros [| g' | Γ' A' l'] NΓ NΓ'; cbn [usubst USubst_ctx ucsubst];
    rewrite ?gwa_cext, ?gwa_cnil, ?gwa_cvar; cbn [CtxRel]; try tauto.
  cbn in NΓ, NΓ'. intros (HΓ & Hl & HA & HA'). refine (conj (IH Γ' ltac:(tauto) ltac:(tauto) HΓ) (conj _ (conj _ _))).
  - exact (lequiv_lvsubst _ _ _ _ _ (uperm_usub_ok Hp'') Hl).
  - exact (VTy_pull (Γ := Γ) Hp Hγ ltac:(tauto) HA).
  - exact (VTy_pull (Γ := Γ') Hp Hγ ltac:(tauto) HA').
Qed.

Lemma CtxRelG_perm {π πi G Γ Γ'} : uperm π πi (gL G) -> [ ⊢ G ] -> dnfctx Γ -> dnfctx Γ' ->
  CtxRelG G Γ Γ' -> CtxRelG (Gp π G) Γ[pφ π]ᵤ Γ'[pφ π]ᵤ.
Proof.
  intros Hp HG NΓ NΓ' H G'' γ Hγ.
  exact (CtxRel_pull Hp Hγ _ _ NΓ NΓ' (H _ _ (gwk_pull Hp HG Hγ))).
Qed.

(** ** Universe weakening of validity: growth by one level, then the
    rotation (M3_DESIGN.md E14) *)

Section Uwk.
Context {L : nat} {Ψ : list gdecl} (HG : [ ⊢ mkG L Ψ ]).
Let Hgrow : gwk_ok gwk_id (mkG (S L) Ψ) (mkG L Ψ) := conj (le_S _ _ (le_n _)) (gwkwf_id _).
Let HG' : [ ⊢ mkG (S L) Ψ ] := wfg_grow L (S L) Ψ (le_S _ _ (le_n _)) HG.
Let EG : Gp (rot L) (mkG (S L) Ψ) = gctx_uwk 1 (mkG L Ψ).
Proof. unfold Gp, G_us, gctx_usubst, gctx_uwk; cbn. f_equal. exact (rot_decls L Ψ (wfg_lwf _ HG)). Qed.
Let Eag : forall m, m < L -> pφ (rot L) m = pφ (ush 1) m := fun m Hm => rot_ush L m Hm.

Lemma VTyG_uwk {Γ T T' l} : dnfctx Γ -> ctx_lwf L Γ -> ty_lwf L T -> ty_lwf L T' -> lwf L l ->
  VTyG (mkG L Ψ) Γ T T' l ->
  VTyG (gctx_uwk 1 (mkG L Ψ)) Γ⟨ush 1⟩ᵤ T⟨ush 1⟩ᵤ T'⟨ush 1⟩ᵤ (lvren l (ush 1)).
Proof.
  intros NΓ WΓ WT WT' Wl HV. pose proof (VTyG_gwk HV Hgrow) as X; cbn [gwa] in X.
  pose proof (VTyG_perm (G := mkG (S L) Ψ) (uperm_rot L) HG' NΓ X) as Y.
  rewrite EG, (lwf_us_ext_ctx WΓ Eag), (lwf_us_ext_ty WT Eag), (lwf_us_ext_ty WT' Eag),
    (lvsubst_ext_lwf _ _ _ _ Wl Eag), <- !uren_us_ty, <- uren_us_ctx,
    <- (lvren_as_lvsubst _ _ (pφ (ush 1))) in Y by reflexivity.
  exact Y.
Qed.

Lemma VTmG_uwk {Γ t t' T l} : dnfctx Γ -> ctx_lwf L Γ -> tm_lwf L t -> tm_lwf L t' -> ty_lwf L T -> lwf L l ->
  VTmG (mkG L Ψ) Γ t t' T l ->
  VTmG (gctx_uwk 1 (mkG L Ψ)) Γ⟨ush 1⟩ᵤ t⟨ush 1⟩ᵤ t'⟨ush 1⟩ᵤ T⟨ush 1⟩ᵤ (lvren l (ush 1)).
Proof.
  intros NΓ WΓ Wt Wt' WT Wl HV. pose proof (VTmG_gwk HV Hgrow) as X; cbn [gwa] in X.
  pose proof (VTmG_perm (G := mkG (S L) Ψ) (uperm_rot L) HG' NΓ X) as Y.
  rewrite EG, (lwf_us_ext_ctx WΓ Eag), (lwf_us_ext_tm Wt Eag), (lwf_us_ext_tm Wt' Eag),
    (lwf_us_ext_ty WT Eag), (lvsubst_ext_lwf _ _ _ _ Wl Eag), <- !uren_us_tm, <- uren_us_ty, <- uren_us_ctx,
    <- (lvren_as_lvsubst _ _ (pφ (ush 1))) in Y by reflexivity.
  exact Y.
Qed.

Lemma CtxRelG_uwk {Γ Γ'} : dnfctx Γ -> dnfctx Γ' -> ctx_lwf L Γ -> ctx_lwf L Γ' ->
  CtxRelG (mkG L Ψ) Γ Γ' -> CtxRelG (gctx_uwk 1 (mkG L Ψ)) Γ⟨ush 1⟩ᵤ Γ'⟨ush 1⟩ᵤ.
Proof.
  intros NΓ NΓ' WΓ WΓ' HV. pose proof (CtxRelG_gwk HV Hgrow) as X; cbn [gwa] in X.
  pose proof (CtxRelG_perm (G := mkG (S L) Ψ) (uperm_rot L) HG' NΓ NΓ' X) as Y.
  rewrite EG, (lwf_us_ext_ctx WΓ Eag), (lwf_us_ext_ctx WΓ' Eag), <- !uren_us_ctx in Y.
  exact Y.
Qed.

End Uwk.

Section Uwkn.
Context {n L : nat} {Ψ : list gdecl} (HG : [ ⊢ mkG L Ψ ]).
Let Hgrow : gwk_ok gwk_id (mkG (n + L) Ψ) (mkG L Ψ) := conj (Nat.le_add_l _ _) (gwkwf_id _).
Let HG' : [ ⊢ mkG (n + L) Ψ ] := wfg_grow L (n + L) Ψ (Nat.le_add_l _ _) HG.
Let EG : Gp (rotn n L) (mkG (n + L) Ψ) = gctx_uwk n (mkG L Ψ).
Proof. unfold Gp, G_us, gctx_usubst, gctx_uwk; cbn. f_equal. exact (rotn_decls n L Ψ (wfg_lwf _ HG)). Qed.
Let Eag : forall m, m < L -> pφ (rotn n L) m = pφ (ush n) m := fun m Hm => rotn_ush n L m Hm.

Lemma VTyG_uwkn {Γ T T' l} : dnfctx Γ -> ctx_lwf L Γ -> ty_lwf L T -> ty_lwf L T' -> lwf L l ->
  VTyG (mkG L Ψ) Γ T T' l ->
  VTyG (gctx_uwk n (mkG L Ψ)) Γ⟨ush n⟩ᵤ T⟨ush n⟩ᵤ T'⟨ush n⟩ᵤ (lvren l (ush n)).
Proof.
  intros NΓ WΓ WT WT' Wl HV. pose proof (VTyG_gwk HV Hgrow) as X; cbn [gwa] in X.
  pose proof (VTyG_perm (G := mkG (n + L) Ψ) (uperm_rotn n L) HG' NΓ X) as Y.
  rewrite EG, (lwf_us_ext_ctx WΓ Eag), (lwf_us_ext_ty WT Eag), (lwf_us_ext_ty WT' Eag),
    (lvsubst_ext_lwf _ _ _ _ Wl Eag), <- !uren_us_ty, <- uren_us_ctx,
    <- (lvren_as_lvsubst _ _ (pφ (ush n))) in Y by reflexivity.
  exact Y.
Qed.

Lemma VTmG_uwkn {Γ t t' T l} : dnfctx Γ -> ctx_lwf L Γ -> tm_lwf L t -> tm_lwf L t' -> ty_lwf L T -> lwf L l ->
  VTmG (mkG L Ψ) Γ t t' T l ->
  VTmG (gctx_uwk n (mkG L Ψ)) Γ⟨ush n⟩ᵤ t⟨ush n⟩ᵤ t'⟨ush n⟩ᵤ T⟨ush n⟩ᵤ (lvren l (ush n)).
Proof.
  intros NΓ WΓ Wt Wt' WT Wl HV. pose proof (VTmG_gwk HV Hgrow) as X; cbn [gwa] in X.
  pose proof (VTmG_perm (G := mkG (n + L) Ψ) (uperm_rotn n L) HG' NΓ X) as Y.
  rewrite EG, (lwf_us_ext_ctx WΓ Eag), (lwf_us_ext_tm Wt Eag), (lwf_us_ext_tm Wt' Eag),
    (lwf_us_ext_ty WT Eag), (lvsubst_ext_lwf _ _ _ _ Wl Eag), <- !uren_us_tm, <- uren_us_ty, <- uren_us_ctx,
    <- (lvren_as_lvsubst _ _ (pφ (ush n))) in Y by reflexivity.
  exact Y.
Qed.

Lemma CtxRelG_uwkn {Γ Γ'} : dnfctx Γ -> dnfctx Γ' -> ctx_lwf L Γ -> ctx_lwf L Γ' ->
  CtxRelG (mkG L Ψ) Γ Γ' -> CtxRelG (gctx_uwk n (mkG L Ψ)) Γ⟨ush n⟩ᵤ Γ'⟨ush n⟩ᵤ.
Proof.
  intros NΓ NΓ' WΓ WΓ' HV. pose proof (CtxRelG_gwk HV Hgrow) as X; cbn [gwa] in X.
  pose proof (CtxRelG_perm (G := mkG (n + L) Ψ) (uperm_rotn n L) HG' NΓ NΓ' X) as Y.
  rewrite EG, (lwf_us_ext_ctx WΓ Eag), (lwf_us_ext_ctx WΓ' Eag), <- !uren_us_ctx in Y.
  exact Y.
Qed.

End Uwkn.

Lemma lsub_wf_lwf {G i Δ d Γ} : [ G ; Δ ⊢[ i ] d : Γ ] -> LK (tm_lwf (gL G)) d.
Proof.
  intros Hd n. destruct (lt_dec n (clen Γ)) as [Hlt|Hge].
  - destruct (in_ctx_of_lt _ _ Hlt) as (A & k & Hin). exact (wf_tm_lwf (lsw_var _ _ _ _ _ Hd _ _ _ Hin)).
  - replace n with (clen Γ + (n - clen Γ)) by lia. rewrite (proj2 (lsw_tail _ _ _ _ _ Hd)). exact I.
Qed.



End UPermV.

(** ** The parameters at M along permutations *)

Section VPM.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM}.

#[export] Instance vpM_perm : VPPerm (vpM EP EM).
Proof.
  constructor.
  - intros π πi G Δ Δ' Hp HG (Heq & HP & HM). cbn.
    destruct (eqctx_dnf Heq) as [N N'].
    refine (conj _ (conj (CtxRelG_perm (E := EP) (LP := LR_P) Hp HG N N' HP)
                         (CtxRelG_perm (E := EM) (LP := LR_P) Hp HG N N' HM))).
    exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 usubstitution))))) _ _ _ _ Heq _ _ (uperm_usub_ok Hp)).
  - intros π πi G Δ T T' l Hp HG (Heq & HP & HM). cbn.
    pose proof (eqty_dnf_ctx Heq) as N.
    exact (conj (p_eqty Hp Heq) (conj (VTyG_perm (E := EP) (LP := LR_P) Hp HG N HP)
                                      (VTyG_perm (E := EM) (LP := LR_P) Hp HG N HM))).
  - intros π πi G Δ T T' l Hp HG (Eq & H1 & H2 & HP & HM). cbn.
    pose proof (wf_ty_dnf_ctx H1) as N.
    refine (conj _ (conj (p_ty Hp H1) (conj (p_ty Hp H2) (conj (VTyG_perm (E := EP) (LP := LR_P) Hp HG N HP)
                                                              (VTyG_perm (E := EM) (LP := LR_P) Hp HG N HM))))).
    apply (proj1 leq_usubst_all); [intros; apply leqv_refl | exact Eq].
  - intros π πi G Δ A t t' l Hp HG (Eq & H1 & H2 & HP & HM). cbn.
    pose proof (wf_tm_dnf_ctx H1) as N.
    refine (conj _ (conj (p_tm Hp H1) (conj (p_tm Hp H2) (conj (VTmG_perm (E := EP) (LP := LR_P) Hp HG N HP)
                                                              (VTmG_perm (E := EM) (LP := LR_P) Hp HG N HM))))).
    apply (proj1 (proj2 leq_usubst_all)); [intros; apply leqv_refl | exact Eq].
  (* the meta-functions' arguments are deep-normal *)
  - intros G Δ Δ' (Heq & _ & _). exact (eqctx_dnf Heq).
  - intros G Δ A A' l (Heq & _ & _). exact (eqty_dnf Heq).
Qed.

End VPM.
