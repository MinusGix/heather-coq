(** * Instances of the meta-functions' bodies (M5_DESIGN.md G2)

    A judgment under a new global binding (a context variable, or a type
    variable at layer P), instantiated at a well-formed context or type,
    holds in the original scope: the global substitution lemma at
    [gsingle o]. The η rules' bodies are the instances, at the bound
    variable, of the function weakened under the binder; on typed syntax
    that instance is the identity ([equiv_gsubst]). Presuppositions of the
    new rules. *)
From DeLaM.Typing Require Export UInst GSubstitution GStatic TypedRed.

(** ** Single global substitutions *)

Lemma gcren_S_gsingle (Γ : ctx) o : dnfctx Γ -> Γ⟪S⟫⦃gsingle o⦄ = Γ.
Proof.
  intros HΓ. rewrite (gsubst_gren_ctx _ _ _ (fun j => GId j)) by reflexivity.
  apply gsubst_id_ctx; auto.
Qed.

Section Inst.
Context {G : gctx} {Γ : ctx} (HΓ : [ G ; Γ ⊢[ lM ] ]).

Lemma gsub_wf_single' {D o} : dnfo o -> dnf_decl D -> gobj_wf G o D -> [ G ⊢ gsingle o : gext G D ].
Proof.
  intros Ho HD Hwf. apply gsub_wf_single; [exact (ctx_glob _ _ _ HΓ) | exact Ho |].
  rewrite gdecl_gsubst_ren_single by exact HD. exact Hwf.
Qed.

Lemma inst_ty {D o T l} : dnfo o -> dnf_decl D -> gobj_wf G o D ->
  [ gext G D ; Γ⟪S⟫ ⊢[ lM ] T @ l ] -> [ G ; Γ ⊢[ lM ] T⦃gsingle o⦄ @ l ].
Proof.
  intros Ho HD Hwf HT.
  pose proof (proj1 (proj2 (proj2 gsubstitution)) _ _ _ _ _ HT (gΨ G) _ (gsub_wf_single' Ho HD Hwf)) as X.
  unfold gwk_to in X; cbn in X. rewrite gcren_S_gsingle in X by exact (wf_ctx_dnf HΓ). exact X.
Qed.
Lemma inst_tm {D o t T l} : dnfo o -> dnf_decl D -> gobj_wf G o D ->
  [ gext G D ; Γ⟪S⟫ ⊢[ lM ] t : T @ l ] -> [ G ; Γ ⊢[ lM ] t⦃gsingle o⦄ : T⦃gsingle o⦄ @ l ].
Proof.
  intros Ho HD Hwf Ht.
  pose proof (proj1 (proj2 (proj2 (proj2 gsubstitution))) _ _ _ _ _ _ Ht (gΨ G) _ (gsub_wf_single' Ho HD Hwf)) as X.
  unfold gwk_to in X; cbn in X. rewrite gcren_S_gsingle in X by exact (wf_ctx_dnf HΓ). exact X.
Qed.

Lemma inst_eqty {D o T T' l} : dnfo o -> dnf_decl D -> gobj_wf G o D ->
  [ gext G D ; Γ⟪S⟫ ⊢[ lM ] T ≅ T' @ l ] -> [ G ; Γ ⊢[ lM ] T⦃gsingle o⦄ ≅ T'⦃gsingle o⦄ @ l ].
Proof.
  intros Ho HD Hwf HT.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 gsubstitution)))) _ _ _ _ _ _ HT (gΨ G) _
                (gsub_wf_single' Ho HD Hwf)) as X.
  unfold gwk_to in X; cbn in X. rewrite gcren_S_gsingle in X by exact (wf_ctx_dnf HΓ). exact X.
Qed.

(** At a context and at a type of layer P. *)
Lemma inst_c_ty {Δ T l} : [ G ; Δ ⊢[ lD ] ] -> [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T @ l ] ->
  [ G ; Γ ⊢[ lM ] T⦃gsingle (GCtx Δ)⦄ @ l ].
Proof. intros HΔ; apply inst_ty; [exact (wf_ctx_dnf HΔ) | exact I | exact HΔ]. Qed.
Lemma inst_c_tm {Δ t T l} : [ G ; Δ ⊢[ lD ] ] -> [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] t : T @ l ] ->
  [ G ; Γ ⊢[ lM ] t⦃gsingle (GCtx Δ)⦄ : T⦃gsingle (GCtx Δ)⦄ @ l ].
Proof. intros HΔ; apply inst_tm; [exact (wf_ctx_dnf HΔ) | exact I | exact HΔ]. Qed.
Lemma inst_c_eqty {Δ T T' l} : [ G ; Δ ⊢[ lD ] ] -> [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T ≅ T' @ l ] ->
  [ G ; Γ ⊢[ lM ] T⦃gsingle (GCtx Δ)⦄ ≅ T'⦃gsingle (GCtx Δ)⦄ @ l ].
Proof. intros HΔ; apply inst_eqty; [exact (wf_ctx_dnf HΔ) | exact I | exact HΔ]. Qed.
Lemma inst_t_eqty {Δ A l T T' l'} : [ G ; Δ ⊢[ lD ] A @ l ] ->
  [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] T ≅ T' @ l' ] ->
  [ G ; Γ ⊢[ lM ] T⦃gsingle (GTy A)⦄ ≅ T'⦃gsingle (GTy A)⦄ @ l' ].
Proof. intros HA; apply inst_eqty; [exact (wf_ty_dnf HA) | exact (wf_ty_dnf_ctx HA) | exact HA]. Qed.
Lemma inst_t_ty {Δ A l T l'} : [ G ; Δ ⊢[ lD ] A @ l ] ->
  [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] T @ l' ] -> [ G ; Γ ⊢[ lM ] T⦃gsingle (GTy A)⦄ @ l' ].
Proof. intros HA; apply inst_ty; [exact (wf_ty_dnf HA) | exact (wf_ty_dnf_ctx HA) | exact HA]. Qed.
Lemma inst_t_tm {Δ A l t T l'} : [ G ; Δ ⊢[ lD ] A @ l ] ->
  [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] t : T @ l' ] ->
  [ G ; Γ ⊢[ lM ] t⦃gsingle (GTy A)⦄ : T⦃gsingle (GTy A)⦄ @ l' ].
Proof. intros HA; apply inst_tm; [exact (wf_ty_dnf HA) | exact (wf_ty_dnf_ctx HA) | exact HA]. Qed.

End Inst.

(** ** η: the instance at the bound variable is the identity *)

Lemma eta_inst_ty {G Γ D o T l} :
  (forall j, in_gctx (D :: gΨ G) 0 j -> obj_equiv j (GId 0) o) -> dnfo o ->
  [ gext G D ; Γ⟪S⟫ ⊢[ lM ] T @ l ] -> T⟪gupr S⟫⦃gsingle o⦄ = T.
Proof.
  intros Ho Hd HT.
  rewrite (gsubst_gren_ty _ _ _ (fun i => match i with 0 => o | S i => GId (S i) end))
    by (intros [|i]; reflexivity).
  transitivity T⦃fun i => GId i⦄; [| apply gsubst_id_ty; [exact (wf_ty_dnf HT) | reflexivity]].
  symmetry. eapply (proj1 (proj2 (proj2 equiv_gsubst))); [exact HT | |].
  - intros n D0 Hin. destruct n as [|n]; [exact (Ho _ Hin) | left; reflexivity].
  - intros [|n]; cbn; auto.
Qed.

Lemma eta_c_ty {G Γ T l} : [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T @ l ] ->
  T⟪gupr S⟫⦃gsingle (GCtx (cvar 0))⦄ = T.
Proof.
  apply eta_inst_ty; [| exact I].
  intros j Hin. inversion Hin; subst. right; right. exists 0; repeat split.
Qed.

Lemma eta_t_ty {G Γ Δ l T l'} : [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] T @ l' ] ->
  T⟪gupr S⟫⦃gsingle (GTy (tyGvar 0 (lshift 0)))⦄ = T.
Proof.
  apply eta_inst_ty; [| exact I].
  intros j Hin. inversion Hin; subst. right; left. exists 0; split; reflexivity.
Qed.

Lemma eta_inst_tm {G Γ D o t T l} :
  (forall j, in_gctx (D :: gΨ G) 0 j -> obj_equiv j (GId 0) o) -> dnfo o ->
  [ gext G D ; Γ⟪S⟫ ⊢[ lM ] t : T @ l ] -> t⟪gupr S⟫⦃gsingle o⦄ = t.
Proof.
  intros Ho Hd Ht.
  rewrite (gsubst_gren_tm _ _ _ (fun i => match i with 0 => o | S i => GId (S i) end))
    by (intros [|i]; reflexivity).
  transitivity t⦃fun i => GId i⦄; [| apply gsubst_id; [exact (wf_tm_dnf Ht) | reflexivity]].
  symmetry. eapply (proj1 (proj2 (proj2 (proj2 equiv_gsubst)))); [exact Ht | |].
  - intros n D0 Hin. destruct n as [|n]; [exact (Ho _ Hin) | left; reflexivity].
  - intros [|n]; cbn; auto.
Qed.

Lemma eta_c_tm {G Γ t T l} : [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] t : T @ l ] ->
  t⟪gupr S⟫⦃gsingle (GCtx (cvar 0))⦄ = t.
Proof.
  apply eta_inst_tm; [| exact I].
  intros j Hin. inversion Hin; subst. right; right. exists 0; repeat split.
Qed.

Lemma eta_t_tm {G Γ Δ l t T l'} : [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] t : T @ l' ] ->
  t⟪gupr S⟫⦃gsingle (GTy (tyGvar 0 (lshift 0)))⦄ = t.
Proof.
  apply eta_inst_tm; [| exact I].
  intros j Hin. inversion Hin; subst. right; left. exists 0; split; reflexivity.
Qed.

(** ** Weakening under the binder *)

Section Under.
Context {G : gctx} {D : gdecl} (HGD : [ ⊢ gext G D ]).

Lemma gwk_ok_step : gwk_ok (gwk_step gwk_id) (gext G D) G.
Proof. split; [apply le_n | constructor; constructor]. Qed.

Lemma gwk_ok_up_step D' : gwk_ok (gwk_up (gwk_step gwk_id)) (gext (gext G D') (gdecl_ren D S)) (gext G D).
Proof. split; [apply le_n | apply gwkwf_up; constructor; constructor]. Qed.

End Under.

(** ** Presuppositions of the new rules *)

Section Pre.
Context {G : gctx} {Γ : ctx}.

Lemma pre_cpi_r {l l' T'} : [ G ; Γ ⊢[ lM ] ] -> lequiv (gL G) l l' ->
  [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T' @ l ] -> [ G ; Γ ⊢[ lM ] tyCPi l' T' @ l ].
Proof.
  intros HΓ Hl HT. eapply wft_lconv; [| exact Hl].
  apply wft_cpi; [exact HΓ | exact (lequiv_wf_r _ _ _ Hl) |].
  eapply wft_lconv; [exact HT | apply lequiv_sym, Hl].
Qed.

Lemma pre_tpi_r {Δ' l1 l2 l3 l4 T'} : [ G ; Γ ⊢[ lM ] ] -> [ G ; Δ' ⊢[ lD ] ] ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ gext G (gdTy Δ' lD l3) ; Γ⟪S⟫ ⊢[ lM ] T' @ l4 ] -> [ G ; Γ ⊢[ lM ] tyTPi Δ' l3 l4 T' @ l2 ].
Proof.
  intros HΓ HΔ H13 H24 HT. eapply wft_lconv; [| exact H24].
  apply wft_tpi; [exact HΓ | exact HΔ | exact (lequiv_wf_r _ _ _ H13) | exact (lequiv_wf_r _ _ _ H24) | exact HT].
Qed.

Lemma pre_clam_r {l l' T T' t'} : [ G ; Γ ⊢[ lM ] ] -> lequiv (gL G) l l' ->
  [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T @ l ] -> [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T' @ l ] ->
  [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T ≅ T' @ l ] -> [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] t' : T @ l ] ->
  [ G ; Γ ⊢[ lM ] clam l' T' t' : tyCPi l T @ l ].
Proof.
  intros HΓ Hl HT HT' HTT Ht. eapply wf_conv.
  - eapply wf_lconv; [| exact Hl].
    apply wf_clam; [exact HΓ | exact (lequiv_wf_r _ _ _ Hl) | |].
    + eapply wft_lconv; [exact HT' | apply lequiv_sym, Hl].
    + eapply wf_lconv; [| apply lequiv_sym, Hl]. eapply wf_conv; [exact Ht | apply eqty_sym, HTT].
  - cbn [typeof]. apply eqty_cpi; [exact HΓ | exact Hl | exact HT | exact HTT].
Qed.

Lemma pre_tlam_r {Δ Δ' l1 l2 l3 l4 T T' t'} : [ G ; Γ ⊢[ lM ] ] -> [ G ; Δ ⊢[ lD ] ] ->
  [ G ; Δ' ⊢[ lD ] ] -> [ G ⊢[ lD ] Δ ≅ Δ' ] ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ gext G (gdTy Δ lD l1) ; Γ⟪S⟫ ⊢[ lM ] T @ l2 ] ->
  [ gext G (gdTy Δ lD l1) ; Γ⟪S⟫ ⊢[ lM ] T ≅ T' @ l2 ] ->
  [ gext G (gdTy Δ' lD l3) ; Γ⟪S⟫ ⊢[ lM ] T' @ l4 ] ->
  [ gext G (gdTy Δ' lD l3) ; Γ⟪S⟫ ⊢[ lM ] t' : T' @ l4 ] ->
  [ G ; Γ ⊢[ lM ] tlam Δ' l3 l4 T' t' : tyTPi Δ l1 l2 T @ l2 ].
Proof.
  intros HΓ HΔ HΔ' HΔΔ H13 H24 HT HTT HT' Ht. eapply wf_conv.
  - eapply wf_lconv; [| exact H24].
    apply wf_tlam; [exact HΓ | exact HΔ' | exact (lequiv_wf_r _ _ _ H13) | exact (lequiv_wf_r _ _ _ H24)
                   | exact HT' | exact Ht].
  - cbn [typeof]. eapply eqty_tpi; [exact HΓ | exact HΔ | exact HΔ' | exact HΔΔ | exact H13 | exact H24
                                  | exact HT | exact HTT | exact HT'].
Qed.

Lemma pre_capp_r {l T t' Δ Δ'} : lwf (gL G) l -> [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T @ l ] ->
  [ G ; Δ' ⊢[ lD ] ] -> [ G ; Γ ⊢[ lM ] t' : tyCPi l T @ l ] ->
  [ G ; Γ ⊢[ lM ] T⦃gsingle (GCtx Δ)⦄ ≅ T⦃gsingle (GCtx Δ')⦄ @ l ] ->
  [ G ; Γ ⊢[ lM ] T⦃gsingle (GCtx Δ')⦄ @ l ] ->
  [ G ; Γ ⊢[ lM ] capp t' Δ' : T⦃gsingle (GCtx Δ)⦄ @ l ].
Proof.
  intros Hl HT HΔ' Ht HE HT'. eapply wf_conv; [| exact HE].
  apply wf_capp; assumption.
Qed.

Lemma pre_tapp_r {Δ l l' T t' A A'} : [ G ; Γ ⊢[ lM ] t' : tyTPi Δ l l' T @ l' ] ->
  [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) l -> lwf (gL G) l' ->
  [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] T @ l' ] -> [ G ; Δ ⊢[ lD ] A' @ l ] ->
  [ G ; Γ ⊢[ lM ] T⦃gsingle (GTy A)⦄ ≅ T⦃gsingle (GTy A')⦄ @ l' ] ->
  [ G ; Γ ⊢[ lM ] T⦃gsingle (GTy A')⦄ @ l' ] ->
  [ G ; Γ ⊢[ lM ] tapp t' A' : T⦃gsingle (GTy A)⦄ @ l' ].
Proof.
  intros Ht HΔ Hl Hl' HT HA HE HT'. eapply wf_conv; [| exact HE].
  apply wf_tapp with (Δ := Δ) (l := l); assumption.
Qed.

Lemma pre_cbeta_l {l T t Δ} : [ G ; Γ ⊢[ lM ] ] -> lwf (gL G) l ->
  [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T @ l ] -> [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] t : T @ l ] ->
  [ G ; Δ ⊢[ lD ] ] -> [ G ; Γ ⊢[ lM ] capp (clam l T t) Δ : T⦃gsingle (GCtx Δ)⦄ @ l ].
Proof.
  intros HΓ Hl HT Ht HΔ. apply wf_capp; [exact Hl | exact HT | exact HΔ | | exact (inst_c_ty HΓ HΔ HT)].
  apply wf_clam; assumption.
Qed.

Lemma pre_tbeta_l {Δ l l' T t A} : [ G ; Γ ⊢[ lM ] ] -> [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) l -> lwf (gL G) l' ->
  [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] T @ l' ] -> [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] t : T @ l' ] ->
  [ G ; Δ ⊢[ lD ] A @ l ] -> [ G ; Γ ⊢[ lM ] tapp (tlam Δ l l' T t) A : T⦃gsingle (GTy A)⦄ @ l' ].
Proof.
  intros HΓ HΔ Hl Hl' HT Ht HA.
  apply wf_tapp with (Δ := Δ) (l := l); [apply wf_tlam; assumption | assumption .. | exact (inst_t_ty HΓ HA HT)].
Qed.

(** η: the body [t⟪↑⟫ g] (resp. [t⟪↑⟫ U^id]) has the body type. *)
(** The η bodies: the weakened function at the bound variable. *)
Lemma wf_ceta_body {l T t} : lwf (gL G) l -> [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T @ l ] ->
  [ G ; Γ ⊢[ lM ] t : tyCPi l T @ l ] ->
  [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] capp t⟪S⟫ (cvar 0) : T @ l ].
Proof.
  intros Hl HT Ht.
  pose proof (ctx_glob _ _ _ (ctx_of_wf_ty (i := lM) eq_refl HT)) as HG1.
  assert (HG2 : [ ⊢ gext (gext G gdCtx) gdCtx ]) by (apply wfg_ctx, HG1).
  pose proof (eta_c_ty HT) as E. rewrite <- E at 1.
  apply wf_capp; [exact Hl | | apply wfc_var; [exact HG1 | reflexivity] | | rewrite E; exact HT].
  - pose proof (gwk_ty (gwk_ok_up_step (G := G) (D := gdCtx) gdCtx) HG2 HT) as X.
    change (wf_ty (gext (gext G gdCtx) gdCtx) lM (Γ⟪S⟫⟪gupr S⟫) T⟪gupr S⟫ l) in X.
    rewrite gcren_shift_up in X. exact X.
  - exact (gwk_tm (gwk_ok_step (G := G) (D := gdCtx)) HG1 Ht).
Qed.

Lemma wf_teta_body {Δ l l' T t} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) l -> lwf (gL G) l' ->
  [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] T @ l' ] ->
  [ G ; Γ ⊢[ lM ] t : tyTPi Δ l l' T @ l' ] ->
  [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] tapp t⟪S⟫ (tyGvar 0 (lshift 0)) : T @ l' ].
Proof.
  intros HΔ Hl Hl' HT Ht.
  pose proof (ctx_glob _ _ _ (ctx_of_wf_ty (i := lM) eq_refl HT)) as HG1.
  pose proof (gwk_ctx (gwk_ok_step (G := G) (D := gdTy Δ lD l)) HG1 HΔ) as HΔ1.
  assert (HG2 : [ ⊢ gext (gext G (gdTy Δ lD l)) (gdTy Δ⟪S⟫ lD l) ])
    by (apply wfg_ty; [exact HG1 | exact HΔ1 | right; reflexivity | exact Hl]).
  pose proof (eta_t_ty HT) as E. rewrite <- E at 1.
  apply wf_tapp with (Δ := Δ⟪S⟫) (l := l); [ | exact HΔ1 | exact Hl | exact Hl' | | | rewrite E; exact HT].
  - exact (gwk_tm (gwk_ok_step (G := G) (D := gdTy Δ lD l)) HG1 Ht).
  - pose proof (gwk_ty (gwk_ok_up_step (G := G) (D := gdTy Δ lD l) (gdTy Δ lD l)) HG2 HT) as X.
    change (wf_ty (gext (gext G (gdTy Δ lD l)) (gdTy Δ⟪S⟫ lD l)) lM (Γ⟪S⟫⟪gupr S⟫) T⟪gupr S⟫ l') in X.
    rewrite gcren_shift_up in X. exact X.
  - eapply wf_gv with (Δ := Δ⟪S⟫) (i' := lD);
      [discriminate | exact HΔ1 | exact (ing_here (gΨ G) (gdTy Δ lD l)) | apply lle_refl | reflexivity].
Qed.

Lemma pre_ceta_l {l T t} : lwf (gL G) l -> [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T @ l ] ->
  [ G ; Γ ⊢[ lM ] t : tyCPi l T @ l ] ->
  [ G ; Γ ⊢[ lM ] clam l T (capp t⟪S⟫ (cvar 0)) : tyCPi l T @ l ].
Proof.
  intros Hl HT Ht. pose proof (ctx_of_wf_tm (i := lM) eq_refl Ht) as HΓ.
  apply wf_clam; [exact HΓ | exact Hl | exact HT | exact (wf_ceta_body Hl HT Ht)].
Qed.

Lemma pre_teta_l {Δ l l' T t} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) l -> lwf (gL G) l' ->
  [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] T @ l' ] ->
  [ G ; Γ ⊢[ lM ] t : tyTPi Δ l l' T @ l' ] ->
  [ G ; Γ ⊢[ lM ] tlam Δ l l' T (tapp t⟪S⟫ (tyGvar 0 (lshift 0))) : tyTPi Δ l l' T @ l' ].
Proof.
  intros HΔ Hl Hl' HT Ht. pose proof (ctx_of_wf_tm (i := lM) eq_refl Ht) as HΓ.
  apply wf_tlam; [exact HΓ | exact HΔ | exact Hl | exact Hl' | exact HT | exact (wf_teta_body HΔ Hl Hl' HT Ht)].
Qed.

(** ** Typed reductions of the applications (layer M) *)

Lemma tmred_cbeta_M {l B b Δ} : [ G ; Γ ⊢[ lM ] ] -> lwf (gL G) l ->
  [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] B @ l ] -> [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] b : B @ l ] -> [ G ; Δ ⊢[ lD ] ] ->
  [ G ; Γ ⊢[ lM ] capp (clam l B b) Δ ⤳* b⦃gsingle (GCtx Δ)⦄ : B⦃gsingle (GCtx Δ)⦄ @ l ].
Proof.
  intros HΓ Hl HB Hb HΔ. constructor.
  - exact (pre_cbeta_l HΓ Hl HB Hb HΔ).
  - econstructor; [apply red_cbeta | constructor].
  - apply eqtm_cbeta; assumption.
Qed.

Lemma tmred_tbeta_M {Δ l l' B b A} : [ G ; Γ ⊢[ lM ] ] -> [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) l -> lwf (gL G) l' ->
  [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] B @ l' ] -> [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] b : B @ l' ] ->
  [ G ; Δ ⊢[ lD ] A @ l ] ->
  [ G ; Γ ⊢[ lM ] tapp (tlam Δ l l' B b) A ⤳* b⦃gsingle (GTy A)⦄ : B⦃gsingle (GTy A)⦄ @ l' ].
Proof.
  intros HΓ HΔ Hl Hl' HB Hb HA. constructor.
  - exact (pre_tbeta_l HΓ HΔ Hl Hl' HB Hb HA).
  - econstructor; [apply red_tbeta | constructor].
  - eapply eqtm_tbeta; eassumption.
Qed.

Lemma tmred_capp_M {l B t w Δ} : lwf (gL G) l -> [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] B @ l ] -> [ G ; Δ ⊢[ lD ] ] ->
  [ G ; Γ ⊢[ lM ] B⦃gsingle (GCtx Δ)⦄ @ l ] ->
  [ G ; Γ ⊢[ lM ] t ⤳* w : tyCPi l B @ l ] ->
  [ G ; Γ ⊢[ lM ] capp t Δ ⤳* capp w Δ : B⦃gsingle (GCtx Δ)⦄ @ l ].
Proof.
  intros Hl HB HΔ HI [Ht Hr He]. constructor.
  - apply wf_capp; assumption.
  - apply reds_capp, Hr.
  - apply eqtm_capp; [exact Hl | exact HB | exact HΔ | exact HΔ | apply eqc_refl, HΔ | apply eqty_refl, HI | exact He].
Qed.

Lemma tmred_tapp_M {Δ l l' B t w A} : [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) l -> lwf (gL G) l' ->
  [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] B @ l' ] -> [ G ; Δ ⊢[ lD ] A @ l ] ->
  [ G ; Γ ⊢[ lM ] B⦃gsingle (GTy A)⦄ @ l' ] ->
  [ G ; Γ ⊢[ lM ] t ⤳* w : tyTPi Δ l l' B @ l' ] ->
  [ G ; Γ ⊢[ lM ] tapp t A ⤳* tapp w A : B⦃gsingle (GTy A)⦄ @ l' ].
Proof.
  intros HΔ Hl Hl' HB HA HI [Ht Hr He]. constructor.
  - apply wf_tapp with (Δ := Δ) (l := l); assumption.
  - apply reds_tapp, Hr.
  - eapply eqtm_tapp; [exact He | exact HΔ | exact Hl | exact Hl' | exact HB | exact HA | apply eqty_refl, HA
                      | apply eqty_refl, HI].
Qed.

End Pre.

(** η's body: [(Λg. b)⟪↑⟫ g] reduces to [b]. *)
Lemma tmred_ceta_body {G Γ l B b} : [ G ; Γ ⊢[ lM ] ] -> lwf (gL G) l ->
  [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] B @ l ] -> [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] b : B @ l ] ->
  [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] capp (clam l B b)⟪S⟫ (cvar 0) ⤳* b : B @ l ].
Proof.
  intros HΓ Hl HB Hb.
  pose proof (ctx_glob _ _ _ (ctx_of_wf_ty (i := lM) eq_refl HB)) as HG1.
  assert (HG2 : [ ⊢ gext (gext G gdCtx) gdCtx ]) by (apply wfg_ctx, HG1).
  pose proof (ctx_of_wf_ty (i := lM) eq_refl HB) as HΓ1.
  pose proof (gwk_ty (gwk_ok_up_step (G := G) (D := gdCtx) gdCtx) HG2 HB) as XB.
  change (wf_ty (gext (gext G gdCtx) gdCtx) lM (Γ⟪S⟫⟪gupr S⟫) B⟪gupr S⟫ l) in XB.
  rewrite gcren_shift_up in XB.
  pose proof (gwk_tm (gwk_ok_up_step (G := G) (D := gdCtx) gdCtx) HG2 Hb) as Xb.
  change (wf_tm (gext (gext G gdCtx) gdCtx) lM (Γ⟪S⟫⟪gupr S⟫) b⟪gupr S⟫ B⟪gupr S⟫ l) in Xb.
  rewrite gcren_shift_up in Xb.
  pose proof (tmred_cbeta_M (G := gext G gdCtx) (Γ := Γ⟪S⟫) (Δ := cvar 0) HΓ1 Hl XB Xb
                (wfc_var _ _ 0 HG1 eq_refl)) as X.
  rewrite (eta_c_tm Hb), (eta_c_ty HB) in X. exact X.
Qed.

(** At an ambient binding of an equivalent level. *)
Lemma tmred_teta_body_lv {G Γ Δ l k k' B b} : [ G ; Γ ⊢[ lM ] ] -> [ G ; Δ ⊢[ lD ] ] ->
  lequiv (gL G) l k -> lwf (gL G) k' ->
  [ gext G (gdTy Δ lD k) ; Γ⟪S⟫ ⊢[ lM ] B @ k' ] -> [ gext G (gdTy Δ lD k) ; Γ⟪S⟫ ⊢[ lM ] b : B @ k' ] ->
  [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] tapp (tlam Δ k k' B b)⟪S⟫ (tyGvar 0 (lshift 0)) ⤳* b : B @ k' ].
Proof.
  intros HΓ HΔ Hlk Hk' HB Hb.
  pose proof (lequiv_wf_l _ _ _ Hlk) as Hl. pose proof (lequiv_wf_r _ _ _ Hlk) as Hk.
  pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (HG1 : [ ⊢ gext G (gdTy Δ lD l) ])
    by (apply wfg_ty; [exact HG | exact HΔ | right; reflexivity | exact Hl]).
  pose proof (gwk_ctx (gwk_ok_step (G := G) (D := gdTy Δ lD l)) HG1 HΓ) as HΓ1.
  pose proof (gwk_ctx (gwk_ok_step (G := G) (D := gdTy Δ lD l)) HG1 HΔ) as HΔ1.
  assert (HG2 : [ ⊢ gext (gext G (gdTy Δ lD l)) (gdTy Δ⟪S⟫ lD k) ])
    by (apply wfg_ty; [exact HG1 | exact HΔ1 | right; reflexivity | exact Hk]).
  pose proof (gwk_ty (gwk_ok_up_step (G := G) (D := gdTy Δ lD k) (gdTy Δ lD l)) HG2 HB) as XB.
  change (wf_ty (gext (gext G (gdTy Δ lD l)) (gdTy Δ⟪S⟫ lD k)) lM (Γ⟪S⟫⟪gupr S⟫) B⟪gupr S⟫ k') in XB.
  rewrite gcren_shift_up in XB.
  pose proof (gwk_tm (gwk_ok_up_step (G := G) (D := gdTy Δ lD k) (gdTy Δ lD l)) HG2 Hb) as Xb.
  change (wf_tm (gext (gext G (gdTy Δ lD l)) (gdTy Δ⟪S⟫ lD k)) lM (Γ⟪S⟫⟪gupr S⟫) b⟪gupr S⟫ B⟪gupr S⟫ k') in Xb.
  rewrite gcren_shift_up in Xb.
  assert (HU : [ gext G (gdTy Δ lD l) ; Δ⟪S⟫ ⊢[ lD ] tyGvar 0 (lshift 0) @ k ]).
  { eapply wft_lconv; [| exact (lequiv_sym _ _ _ Hlk)].
    eapply wf_gv with (Δ := Δ⟪S⟫) (i' := lD);
      [discriminate | exact HΔ1 | exact (ing_here (gΨ G) (gdTy Δ lD l)) | apply lle_refl | reflexivity]. }
  pose proof (tmred_tbeta_M (G := gext G (gdTy Δ lD l)) (Γ := Γ⟪S⟫) HΓ1 HΔ1 Hk Hk' XB Xb HU) as X.
  rewrite (eta_t_tm Hb), (eta_t_ty HB) in X. exact X.
Qed.

Lemma tmred_teta_body {G Γ Δ l l' B b} : [ G ; Γ ⊢[ lM ] ] -> [ G ; Δ ⊢[ lD ] ] -> lwf (gL G) l -> lwf (gL G) l' ->
  [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] B @ l' ] -> [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] b : B @ l' ] ->
  [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] tapp (tlam Δ l l' B b)⟪S⟫ (tyGvar 0 (lshift 0)) ⤳* b : B @ l' ].
Proof. intros HΓ HΔ Hl Hl'. exact (tmred_teta_body_lv HΓ HΔ (lequiv_refl _ _ Hl) Hl'). Qed.

