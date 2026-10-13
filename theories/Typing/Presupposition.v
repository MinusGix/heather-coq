(** * Presupposition (syntactic validity, ch. 5)

    Every judgment's components are well formed: the type of a typed term,
    both sides of a type equality, both sides of a term equality (and its
    type).  For layers with [typeof i = i]. *)
From DeLaM.Typing Require Export PresupAux MInst.

(** ** Global variables

    The rest of [presupposition]'s per-former lemmas are in [PresupAux]. *)

Section AuxG.
Context {G : gctx} {i : layer} (Hi : typeof i = i) (Hv : i <> lV).

Lemma pre_gvar_ty {Γ u Δ i' T l d} :
  [ G ; Γ ⊢[ i ] ] -> in_gctx (gΨ G) u (gdTm Δ i' T l) -> [ G ; Γ ⊢[ i ] d : Δ ] ->
  [ G ; Γ ⊢[ i ] T[d] @ l ].
Proof using Hi Hv.
  intros HΓ Hin Hd. destruct (gctx_decl_ok _ _ _ (ctx_glob _ _ _ HΓ) Hin) as (_ & HT & _).
  exact (wf_ty_subst_g (lift_ty HT (lle_D_i Hi Hv)) Hd).
Qed.

Lemma pre_gvar_r {Γ u Δ i' T l d d'} :
  [ G ; Γ ⊢[ i ] ] -> in_gctx (gΨ G) u (gdTm Δ i' T l) -> lle i' i ->
  [ G ; Γ ⊢[ i ] d : Δ ] -> lsub_tail d' Δ Γ -> dnfl d' ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d' n : A[d'] @ k ]) ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n ≅ llk d' n : A[d] @ k ]) ->
  [ G ; Γ ⊢[ i ] gvar u d' : T[d] @ l ].
Proof using Hi Hv.
  intros HΓ Hin Hi' Hd Ht' Hn' Hv' He.
  destruct (gctx_decl_ok _ _ _ (ctx_glob _ _ _ HΓ) Hin) as (_ & HT & _).
  pose proof (lsub_wf_prem Hi HΓ Ht' Hn' Hv') as Hd'.
  eapply (conv_tm' Hi).
  - eapply wf_gvar; [rewrite Hi; exact HΓ | exact Hin | exact Hi' | exact Ht' | exact Hn' | exact Hv'].
  - exact (proj1 (proj2 (proj2 functionality_all)) _ _ _ _ _ (lift_ty HT (lle_D_i Hi Hv)) _ _ _
             (conj Hd (conj Hd' He))).
Qed.

(** Defined globals (M9): as [gvar], their declaration at a definition. *)
Lemma pre_gdef_ty {Γ u Δ T l t d} :
  [ G ; Γ ⊢[ i ] ] -> in_gctx (gΨ G) u (gdDef Δ T l t) -> [ G ; Γ ⊢[ i ] d : Δ ] ->
  [ G ; Γ ⊢[ i ] T[d] @ l ].
Proof using Hi Hv.
  intros HΓ Hin Hd. destruct (gctx_decl_ok _ _ _ (ctx_glob _ _ _ HΓ) Hin) as (_ & HT & _).
  exact (wf_ty_subst_g (lift_ty HT (lle_D_i Hi Hv)) Hd).
Qed.

Lemma pre_gdef_r {Γ u Δ T l t0 t' d d'} :
  [ G ; Γ ⊢[ i ] ] -> in_gctx (gΨ G) u (gdDef Δ T l t0) -> tm_leq t0 t' -> lle lC i ->
  [ G ; Γ ⊢[ i ] d : Δ ] -> lsub_tail d' Δ Γ -> dnfl d' ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d' n : A[d'] @ k ]) ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n ≅ llk d' n : A[d] @ k ]) ->
  [ G ; Δ ⊢[ i ] t' : T @ l ] ->
  [ G ; Γ ⊢[ i ] gdef u t' d' : T[d] @ l ].
Proof using Hi Hv.
  intros HΓ Hin Hle Hi' Hd Ht' Hn' Hv' He Hb.
  destruct (gctx_decl_ok _ _ _ (ctx_glob _ _ _ HΓ) Hin) as (_ & HT & _).
  pose proof (lsub_wf_prem Hi HΓ Ht' Hn' Hv') as Hd'.
  eapply (conv_tm' Hi).
  - eapply wf_gdef; [rewrite Hi; exact HΓ | exact Hin | exact Hle | exact Hi' | exact Ht' | exact Hn' | exact Hv' | exact Hb].
  - exact (proj1 (proj2 (proj2 functionality_all)) _ _ _ _ _ (lift_ty HT (lle_D_i Hi Hv)) _ _ _
             (conj Hd (conj Hd' He))).
Qed.

End AuxG.



(** ** Contextual types and letbox (layer M) *)

Lemma lM_notV : lM <> lV.
Proof. discriminate. Qed.

Lemma ctx_of_ext {G i Γ A l} : [ G ; Γ ,, A @ l ⊢[ i ] ] -> [ G ; Γ ⊢[ i ] ].
Proof. inversion 1; auto. Qed.

Lemma pre_CTrm_r {G Γ Δ Δ' T' l l'} :
  [ G ; Γ ⊢[ lM ] ] -> [ G ; Δ' ⊢[ lD ] ] -> [ G ; Δ' ⊢[ lD ] lshift 0 : Δ ] ->
  [ G ; Δ ⊢[ lD ] T' @ l ] -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ lM ] tyCTrm Δ' T' l' @ lzero ].
Proof.
  intros HΓ HΔ' Hid HT' Hl. apply wft_CTrm; eauto using lequiv_wf_r.
  pose proof (wf_ty_subst (i := lD) eq_refl HT' Hid) as X. rewrite nf_id_ty in X by exact (wf_ty_nf HT').
  eapply wft_lconv; [exact X | now apply lequiv_sym].
Qed.

Lemma pre_letbox_ty {G Γ l1 l2 A M M' t t0} :
  [ G ; Γ ,, A @ l2 ⊢[ lM ] M ≅ M' @ l1 ] -> [ G ; Γ ,, A @ l2 ⊢[ lM ] M' @ l1 ] ->
  [ G ; Γ ⊢[ lM ] t ≅ t0 : A @ l2 ] -> [ G ; Γ ⊢[ lM ] t : A @ l2 ] -> [ G ; Γ ⊢[ lM ] t0 : A @ l2 ] ->
  [ G ; Γ ⊢[ lM ] M[lsingle t] ≅ M'[lsingle t0] @ l1 ].
Proof.
  intros HMM HM' Htt Ht Ht0. eapply eqty_trans.
  - exact (eqty_single (i := lM) eq_refl HMM Ht).
  - apply (wf_ty_func (i := lM) eq_refl HM' (d' := lsingle t0)).
    now apply (lsub_eq_single (i := lM) eq_refl).
Qed.

Lemma pre_letboxT_r {G Γ l1 l2 l3 l4 Δ Δ' M M' t2 t t0} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 -> [ G ; Δ' ⊢[ lD ] ] -> [ G ⊢[ lD ] Δ ≅ Δ' ] ->
  [ G ; Γ ,, tyCTyp Δ l2 @ lzero ⊢[ lM ] M ≅ M' @ l1 ] ->
  [ G ; Γ ,, tyCTyp Δ l2 @ lzero ⊢[ lM ] M' @ l1 ] ->
  [ G ; Γ ,, tyCTyp Δ' l4 @ lzero ⊢[ lM ] M' @ l3 ] ->
  [ gext G (gdTy Δ' lC l4) ; Γ⟪S⟫ ⊢[ lM ] t2 : M'⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))] @ l3 ] ->
  [ G ; Γ ⊢[ lM ] t ≅ t0 : tyCTyp Δ l2 @ lzero ] ->
  [ G ; Γ ⊢[ lM ] t : tyCTyp Δ l2 @ lzero ] -> [ G ; Γ ⊢[ lM ] t0 : tyCTyp Δ l2 @ lzero ] ->
  [ G ; Γ ⊢[ lM ] letboxT l3 l4 Δ' M' t2 t0 : M[lsingle t] @ l1 ].
Proof.
  intros H13 H24 HΔ' Hc HMM HM' HM'3 Ht2 Htt Ht Ht0.
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Ht) as HΓ.
  assert (HCC : [ G ; Γ ⊢[ lM ] tyCTyp Δ l2 ≅ tyCTyp Δ' l4 @ lzero ]) by (apply eqty_CTyp; auto).
  eapply wf_lconv with (l' := l3); [|exact H13].
  eapply (conv_tm' (i := lM) eq_refl (T' := M'[lsingle t0])).
  - apply wf_letboxT; eauto using lequiv_wf_r.
    eapply (conv_tm' (i := lM) eq_refl); [exact Ht0 | now apply eqty_sym].
  - eapply eqty_lconv; [exact (pre_letbox_ty HMM HM' Htt Ht Ht0) | now apply lequiv_sym].
Qed.

Lemma pre_letboxt_r {G Γ l1 l2 l3 l4 Δ Δ' T T' M M' t2 t t0} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 -> [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ' ⊢[ lD ] ] ->
  [ G ⊢[ lD ] Δ ≅ Δ' ] -> [ G ; Δ ⊢[ lD ] T @ l2 ] -> [ G ; Δ' ⊢[ lD ] T' @ l4 ] ->
  [ G ; Δ ⊢[ lD ] T ≅ T' @ l2 ] ->
  [ G ; Γ ,, tyCTrm Δ T l2 @ lzero ⊢[ lM ] M ≅ M' @ l1 ] ->
  [ G ; Γ ,, tyCTrm Δ T l2 @ lzero ⊢[ lM ] M' @ l1 ] ->
  [ G ; Γ ,, tyCTrm Δ' T' l4 @ lzero ⊢[ lM ] M' @ l3 ] ->
  [ gext G (gdTm Δ' lC T' l4) ; Γ⟪S⟫ ⊢[ lM ] t2 : M'⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))] @ l3 ] ->
  [ G ; Γ ⊢[ lM ] t ≅ t0 : tyCTrm Δ T l2 @ lzero ] ->
  [ G ; Γ ⊢[ lM ] t : tyCTrm Δ T l2 @ lzero ] -> [ G ; Γ ⊢[ lM ] t0 : tyCTrm Δ T l2 @ lzero ] ->
  [ G ; Γ ⊢[ lM ] letboxt l3 l4 Δ' T' M' t2 t0 : M[lsingle t] @ l1 ].
Proof.
  intros H13 H24 HΔ HΔ' Hc HT HT' HTT HMM HM' HM'3 Ht2 Htt Ht Ht0.
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Ht) as HΓ.
  assert (HCC : [ G ; Γ ⊢[ lM ] tyCTrm Δ T l2 ≅ tyCTrm Δ' T' l4 @ lzero ]) by (apply eqty_CTrm; auto).
  eapply wf_lconv with (l' := l3); [|exact H13].
  eapply (conv_tm' (i := lM) eq_refl (T' := M'[lsingle t0])).
  - apply wf_letboxt; eauto using lequiv_wf_r.
    eapply (conv_tm' (i := lM) eq_refl); [exact Ht0 | now apply eqty_sym].
  - eapply eqty_lconv; [exact (pre_letbox_ty HMM HM' Htt Ht Ht0) | now apply lequiv_sym].
Qed.

(** letbox β: the contractum is typed by the global substitution lemma. *)
Lemma pre_letbox_beta_r {G Γ D o t' M b b' l'} :
  [ G ; Γ ⊢[ lM ] ] -> dnfo o -> gobj_wf G o (gdecl_gsubst (gdecl_ren D S) (gsingle o)) ->
  b⦃gsingle o⦄ = b' -> dnfty M ->
  [ gext G D ; Γ⟪S⟫ ⊢[ lM ] t' : M⟪S⟫[lsingle b] @ l' ] ->
  [ G ; Γ ⊢[ lM ] t'⦃gsingle o⦄ : M[lsingle b'] @ l' ].
Proof.
  intros HΓ Ho Hwf Hb HM Ht'.
  pose proof (gsub_wf_single G D o (ctx_glob _ _ _ HΓ) Ho Hwf) as Hσ.
  pose proof (proj1 (proj2 (proj2 (proj2 gsubstitution))) _ _ _ _ _ _ Ht' (gΨ G) _ Hσ) as X.
  unfold gwk_to in X; cbn in X.
  rewrite (gsubst_gren_ctx _ _ _ (fun j => GId j)), gsubst_id_ctx in X
    by first [reflexivity | exact (wf_ctx_dnf HΓ) | auto].
  rewrite gs_single_ty, Hb, (gsubst_gren_ty _ _ _ (fun j => GId j)), gsubst_id_ty in X
    by first [reflexivity | auto].
  exact X.
Qed.

Lemma pre_letboxT_beta_r {G Γ l' l Δ M t' T} :
  [ G ; Γ ,, tyCTyp Δ l @ lzero ⊢[ lM ] M @ l' ] -> [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lC ] T @ l ] ->
  [ gext G (gdTy Δ lC l) ; Γ⟪S⟫ ⊢[ lM ] t' : M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))] @ l' ] ->
  [ G ; Γ ⊢[ lM ] t'⦃gsingle (GTy T)⦄ : M[lsingle (boxT T)] @ l' ].
Proof.
  intros HM HΔ HT Ht'.
  eapply pre_letbox_beta_r; [ | | | | exact (wf_ty_dnf HM) | exact Ht'].
  - exact (ctx_of_ext (ctx_of_wf_ty (i := lM) eq_refl HM)).
  - exact (wf_ty_dnf HT).
  - rewrite gdecl_gsubst_ren_single by exact (wf_ctx_dnf HΔ). exact HT.
  - cbn. change (subst_ty T (glsubst (lshift 0) (gsingle (GTy T)))) with T[lshift 0].
    now rewrite nf_id_ty by exact (wf_ty_nf HT).
Qed.

Lemma pre_letboxt_beta_r {G Γ l' l Δ T M t' t} :
  [ G ; Γ ,, tyCTrm Δ T l @ lzero ⊢[ lM ] M @ l' ] -> [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lD ] T @ l ] ->
  [ G ; Δ ⊢[ lC ] t : T @ l ] ->
  [ gext G (gdTm Δ lC T l) ; Γ⟪S⟫ ⊢[ lM ] t' : M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))] @ l' ] ->
  [ G ; Γ ⊢[ lM ] t'⦃gsingle (GTm t)⦄ : M[lsingle (boxt t)] @ l' ].
Proof.
  intros HM HΔ HT Ht Ht'.
  eapply pre_letbox_beta_r; [ | | | | exact (wf_ty_dnf HM) | exact Ht'].
  - exact (ctx_of_ext (ctx_of_wf_ty (i := lM) eq_refl HM)).
  - exact (wf_tm_dnf Ht).
  - rewrite gdecl_gsubst_ren_single by (cbn; split; [exact (wf_ctx_dnf HΔ) | exact (wf_ty_dnf HT)]).
    exact Ht.
  - cbn. change (subst_tm t (glsubst (lshift 0) (gsingle (GTm t)))) with t[lshift 0].
    now rewrite nf_id by exact (wf_tm_nf Ht).
Qed.

Lemma typeof_self_notV i : typeof i = i -> i <> lV.
Proof. destruct i; cbn; congruence. Qed.

Lemma ctx_of_tm_M {G Γ t T l} : [ G ; Γ ⊢[ lM ] t : T @ l ] -> [ G ; Γ ⊢[ lM ] ].
Proof. exact (ctx_of_wf_tm (i := lM) eq_refl). Qed.
Lemma ctx_of_ty_M {G Γ T l} : [ G ; Γ ⊢[ lM ] T @ l ] -> [ G ; Γ ⊢[ lM ] ].
Proof. exact (ctx_of_wf_ty (i := lM) eq_refl). Qed.
Lemma ctx_of_eqtm_M {G Γ t t' T l} : [ G ; Γ ⊢[ lM ] t ≅ t' : T @ l ] -> [ G ; Γ ⊢[ lM ] ].
Proof. exact (ctx_of_eqtm (i := lM) eq_refl). Qed.

(** ** The recursors (layer M): the congruences' right-hand sides, typed at
    their own data and converted along the instance equation (E10). *)

Lemma pre_elimT_r {G Γ l1 l2 l1' l2' MT MT' Mt' bs' l l' Δ Δ' t t'} :
  [ G ; Γ ⊢[ lM ] motT (wrapMT MT) l Δ t ≅ motT (wrapMT MT') l' Δ' t' @ l1 ] ->
  [ G ; Γ ⊢[ lM ] motT (wrapMT MT') l' Δ' t' @ l1 ] ->
  lequiv (gL G) l1 l1' -> lequiv (gL G) l2 l2' -> lequiv (gL G) l l' ->
  [ G ; Δ' ⊢[ lD ] ] -> [ G ⊢[ lD ] Δ ≅ Δ' ] ->
  [ recGT G ; recΓT Γ ⊢[ lM ] MT' @ lvren l1' (ush 1) ] ->
  [ recGt G ; recΓt Γ ⊢[ lM ] Mt' @ lvren l2' (ush 1) ] ->
  (forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ] ]) ->
  (forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ]
                         bs' k : brRes k (wrapMT MT') (wrapMt Mt') @ brLv k l1' l2' ]) ->
  [ G ; Γ ⊢[ lM ] t' : tyCTyp Δ l @ lzero ] ->
  [ G ; Γ ⊢[ lM ] elimT l1' l2' (mkrb MT' Mt' bs') l' Δ' t' : motT (wrapMT MT) l Δ t @ l1 ].
Proof.
  intros HM HM' H1 H2 H3 HΔ' HΔΔ HMT' HMt' Hc Hb Ht'.
  eapply wf_conv; [| exact HM]. eapply wf_lconv; [| exact H1].
  apply wf_elimT; eauto using lequiv_wf_r.
  - eapply wft_lconv; [exact HM' | now apply lequiv_sym].
  - eapply wf_conv; [exact Ht' |]. apply eqty_sym, eqty_CTyp; [exact (ctx_of_tm_M Ht') | exact HΔΔ | exact H3].
Qed.

Lemma pre_elimt_r {G Γ l1 l2 l1' l2' MT' Mt Mt' bs' l l' Δ Δ' T T' t t'} :
  [ G ; Γ ⊢[ lM ] mott (wrapMt Mt) l Δ T t ≅ mott (wrapMt Mt') l' Δ' T' t' @ l2 ] ->
  [ G ; Γ ⊢[ lM ] mott (wrapMt Mt') l' Δ' T' t' @ l2 ] ->
  lequiv (gL G) l1 l1' -> lequiv (gL G) l2 l2' -> lequiv (gL G) l l' ->
  [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ' ⊢[ lD ] ] -> [ G ⊢[ lD ] Δ ≅ Δ' ] ->
  [ G ; Δ ⊢[ lD ] T @ l ] -> [ G ; Δ' ⊢[ lD ] T' @ l' ] -> [ G ; Δ ⊢[ lD ] T ≅ T' @ l ] ->
  [ recGT G ; recΓT Γ ⊢[ lM ] MT' @ lvren l1' (ush 1) ] ->
  [ recGt G ; recΓt Γ ⊢[ lM ] Mt' @ lvren l2' (ush 1) ] ->
  (forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ] ]) ->
  (forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ]
                         bs' k : brRes k (wrapMT MT') (wrapMt Mt') @ brLv k l1' l2' ]) ->
  [ G ; Γ ⊢[ lM ] t' : tyCTrm Δ T l @ lzero ] ->
  [ G ; Γ ⊢[ lM ] elimt l1' l2' (mkrb MT' Mt' bs') l' Δ' T' t' : mott (wrapMt Mt) l Δ T t @ l2 ].
Proof.
  intros HM HM' H1 H2 H3 HΔ HΔ' HΔΔ HT HT' HTT HMT' HMt' Hc Hb Ht'.
  eapply wf_conv; [| exact HM]. eapply wf_lconv; [| exact H2].
  apply wf_elimt; eauto using lequiv_wf_r.
  - eapply wft_lconv; [exact HM' | now apply lequiv_sym].
  - eapply wf_conv; [exact Ht' |]. apply eqty_sym, eqty_CTrm; [exact (ctx_of_tm_M Ht') | assumption ..].
Qed.

Lemma ctx_conv_ext1 {G i} (Hi : typeof i = i) {Γ Γ' A A' l l'} :
  [ G ; Γ' ⊢[ i ] lshift 0 : Γ ] -> [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ⊢[ i ] A' @ l ] -> lequiv (gL G) l l' -> [ G ; Γ' ,, A' @ l' ⊢[ i ] ].
Proof. intros H1 H2 H3 H4 H5; exact (proj1 (ctx_conv_ext Hi H1 H2 H3 H4 H5)). Qed.
Lemma ctx_conv_ext2 {G i} (Hi : typeof i = i) {Γ Γ' A A' l l'} :
  [ G ; Γ' ⊢[ i ] lshift 0 : Γ ] -> [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ⊢[ i ] A' @ l ] -> lequiv (gL G) l l' -> [ G ; Γ' ,, A' @ l' ⊢[ i ] lshift 0 : Γ ,, A @ l ].
Proof. intros H1 H2 H3 H4 H5; exact (proj2 (ctx_conv_ext Hi H1 H2 H3 H4 H5)). Qed.

#[export] Hint Resolve wft_nat wft_pi wft_U wft_El wf_code_nat wf_code_U wf_code_pi wf_zero
  wf_succ wf_natrec wf_lam wf_app wfc_ext in_ctx_wf wf_ty_single wf_tm_single
  wft_sig wf_code_sig wf_pair wf_fst wf_snd wft_seq wf_srefl wf_elimSEmpty wft_id wf_idrefl wf_J wf_code_id wf_code_seq wf_elimEmpty wft_sum wf_inl wf_inr
  wft_sq wf_sq wf_elimSq ctx_of_wf_ty ctx_of_wf_tm ctx_of_eqty ctx_of_eqtm lequiv_wf_l lequiv_wf_r compt_notV : presup.
#[export] Hint Extern 1 (lwf _ _) =>
  solve [cbn; repeat split; eauto using lequiv_wf_l, lequiv_wf_r] : presup.
#[export] Hint Extern 1 =>
  match goal with Hi : typeof ?i = ?i |- context [typeof ?i] => rewrite Hi end : presup.

Theorem presupposition :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> True) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> True) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> typeof i = i ->
     [ G ; Γ ⊢[ i ] T @ l ]) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> typeof i = i ->
     [ G ; Γ ⊢[ i ] T @ l ] /\ [ G ; Γ ⊢[ i ] T' @ l ]) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> typeof i = i ->
     [ G ; Γ ⊢[ i ] t : T @ l ] /\ [ G ; Γ ⊢[ i ] t' : T @ l ] /\ [ G ; Γ ⊢[ i ] T @ l ]) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> typeof i = i ->
     [ G ; Γ ⊢[ i ] ] /\ [ G ; Γ' ⊢[ i ] ] /\ [ G ; Γ' ⊢[ i ] lshift 0 : Γ ]).
Proof.
  apply typing_mut; intros; try exact I;
    match goal with Hi : typeof ?i = ?i |- _ => rewrite ?Hi in * end;
    repeat match goal with IH : ?i = ?i -> _ |- _ => specialize (IH eq_refl) end;
    repeat match goal with IH : typeof ?j = ?j -> _ |- _ => specialize (IH eq_refl) end;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    try match goal with c : compt ?i |- _ => pose proof (compt_notV _ c) end.
  all: repeat match goal with |- _ /\ _ => split end.
  (* depth 3 here, 4 only for the few goals left at the end: failing
     depth-4 searches on the goals the passes below close cost most *)
  all: try solve [eauto 3 with presup].
  (* level and type conversions *)
  all: try solve [eapply wft_lconv; eassumption].
  all: try solve [eapply wf_lconv; eassumption].
  all: try solve [eapply conv_tm'; eassumption].
  (* contexts *)
  all: try solve [apply wfc_nil; auto | apply wfc_var; auto].
  all: try solve [eapply lsub_wf_id; eauto using wfc_nil, wfc_var].
  all: try solve [eapply ext_wf; eauto].
  all: try solve [match goal with
                  | Hid : lsub_wf _ _ ?Γ' _ ?Γ, HAA : eq_ty _ _ ?Γ ?A ?A' ?l, HA : wf_ty _ _ ?Γ ?A ?l,
                    HA' : wf_ty _ _ ?Γ ?A' ?l, Hl : lequiv _ ?l ?l', Hi : typeof ?i = ?i
                    |- _ => first [exact (ctx_conv_ext1 Hi Hid HA HAA HA' Hl)
                                 | exact (ctx_conv_ext2 Hi Hid HA HAA HA' Hl)]
                  end].
  (* global variables *)
  all: try solve [first [eapply wft_gvar | eapply wf_gvar | eapply wf_gdef]; eauto;
                  match goal with Hi : typeof ?i = ?i |- _ => rewrite Hi end; eauto].
  all: try solve [eapply pre_gvar_ty; eauto using typeof_self_notV;
                  eapply lsub_wf_prem; eauto using typeof_self_notV].
  all: try solve [eapply pre_gdef_ty; eauto using typeof_self_notV;
                  eapply lsub_wf_prem; eauto using typeof_self_notV].
  all: try solve [eapply pre_gvar_r; eauto using typeof_self_notV, lsub_wf_prem].
  (* defined globals (M9): the other instance, and δ's reduct *)
  all: try solve [eapply pre_gdef_r; eauto using typeof_self_notV, lsub_wf_prem].
  all: try solve [eapply wf_gdef; eauto using compt_lle_C;
                  match goal with Hi : typeof ?i = ?i |- _ => rewrite Hi end; eauto].
  all: try solve [eapply wf_tm_subst_g; [eassumption | eapply lsub_wf_prem; eauto using typeof_self_notV]].
  (* contextual types, box, letbox *)
  all: try solve [eapply wft_CTyp; eauto using lequiv_wf_l, lequiv_wf_r, ctx_of_tm_M, ctx_of_eqtm_M].
  all: try solve [eapply wft_CTrm; eauto using lequiv_wf_l, lequiv_wf_r, ctx_of_tm_M, ctx_of_eqtm_M].
  all: try solve [eapply pre_CTrm_r; eauto].
  all: try solve [eapply (wf_ty_single (i := lM) eq_refl); [eassumption|];
                  first [eapply wf_boxT | eapply wf_boxt]; eauto using ctx_of_ext, ctx_of_ty_M].
  all: try solve [first [eapply wf_boxT | eapply wf_boxt]; eauto].
  all: try solve [first [eapply wf_letboxT | eapply wf_letboxt]; eauto using lequiv_wf_l, lequiv_wf_r;
                  first [eapply wf_boxT | eapply wf_boxt]; eauto using ctx_of_ext, ctx_of_ty_M].
  all: try solve [eapply pre_letboxT_r; eauto].
  all: try solve [match goal with |- wf_tm _ _ _ (letboxt _ _ ?D' ?T' _ _ _) _ _ =>
                    match goal with Hc : eq_ctx _ _ ?D ?D', HTT : eq_ty _ _ ?D ?T ?T' _ |- _ =>
                      eapply (pre_letboxt_r (Δ := D) (T := T)); eauto end end].
  all: try solve [eapply pre_letboxT_beta_r; eauto].
  all: try solve [eapply pre_letboxt_beta_r; eauto].
  (* the recursors *)
  all: try solve [first [eapply wf_elimT | eapply wf_elimt]; eauto using lequiv_wf_l;
                  (* the branches, from the branch equations *)
                  intros ?k ?Hk; match goal with IH : forall k, k < nbr -> _ = _ -> _ /\ _ |- _ =>
                    exact (proj1 (IH k Hk eq_refl)) end].
  all: try solve [first [eapply pre_elimT_r | eapply pre_elimt_r]; eassumption].
  (* universe polymorphism (UInst) *)
  all: try solve [first [ solve [eapply wft_upi; eauto using lequiv_wf_l]
                        | solve [eapply pre_upi_r; eauto] | solve [eapply pre_ulam_r; eauto]
                        | solve [eapply wf_ulam; eauto using lequiv_wf_l]
                        | solve [eapply wf_uapp; eauto using lequivs_lwf_l] | solve [eapply pre_uapp_r; eauto]
                        | solve [eapply pre_ubeta_l; eauto] | solve [eapply pre_ubeta_r; eauto]
                        | solve [eapply pre_ueta_l; eauto] ]].
  all: try solve [eapply pre_uapp_l; eauto using lequivs_lwf_l; eapply wf_ulam; eassumption].
  (* meta-functions (MInst) *)
  all: try solve [first
         [ solve [eapply wft_cpi; eauto using lequiv_wf_l] | solve [eapply wft_tpi; eauto using lequiv_wf_l]
         | solve [eapply wf_clam; eauto using lequiv_wf_l] | solve [eapply wf_tlam; eauto using lequiv_wf_l]
         | solve [eapply wf_capp; eauto] | solve [eapply wf_tapp; eauto]
         | solve [eapply pre_cpi_r; eauto] | solve [eapply pre_tpi_r; eauto]
         | solve [eapply pre_clam_r; eauto] | solve [eapply pre_tlam_r; eauto]
         | solve [eapply pre_capp_r; eauto] | solve [eapply pre_tapp_r; eauto]
         | solve [eapply pre_cbeta_l; eauto] | solve [eapply pre_tbeta_l; eauto]
         | solve [eapply pre_ceta_l; eauto] | solve [eapply pre_teta_l; eauto]
         | solve [eapply inst_c_ty; eauto] | solve [eapply inst_c_tm; eauto]
         | solve [eapply inst_t_ty; eauto] | solve [eapply inst_t_tm; eauto] ]].
  (* right-hand sides of congruences *)
  (* the rules' right-hand-side lemmas first: a failing [eauto 4] costs
     more than all of them *)
  all: try solve [first [ eapply pre_pi_r; eassumption
                        | eapply pre_El_r; eassumption
                        | eapply pre_codepi_r; eassumption
                        | eapply pre_natrec_r; eassumption
                        | eapply pre_lam_r; eassumption
                        | eapply pre_app_r; eassumption
                        | eapply pre_natrec_succ; eassumption
                        | eapply pre_eta_l; eassumption
                        | eapply pre_sig_r; eassumption
                        | eapply pre_codesig_r; eassumption
                        | eapply pre_pair_r; eassumption
                        | eapply pre_fst_r; eassumption
                        | eapply pre_snd_r; eassumption
                        | eapply pre_snd_beta_l; eassumption
                        | eapply pre_sig_eta_l; eassumption
                        | eapply pre_snd_ty; eassumption
                        | eapply pre_El_unit; eassumption
                        | eapply pre_seq_r; eassumption
                        | eapply pre_srefl_r; eassumption
                        | eapply pre_elimSEmpty_r; eassumption
                        | eapply pre_id_r; eassumption
                        | eapply pre_idrefl_r; eassumption
                        | eapply pre_J_ty; eassumption
                        | eapply pre_J_r; eassumption
                        | eapply pre_codeid_r; eassumption
                        | eapply pre_codeseq_r; eassumption
                        | eapply pre_El_sempty; eassumption
                        | eapply pre_elimEmpty_r; eassumption
                        | eapply pre_sum_r; eassumption
                        | eapply pre_inl_r; eassumption
                        | eapply pre_inr_r; eassumption
                        | eapply pre_case_r; eassumption
                        | eapply pre_case_inl_rhs; eassumption
                        | eapply pre_case_inr_rhs; eassumption
                        | eapply pre_El_empty; eassumption
                        | eapply pre_codesum_r; eassumption
                        | eapply pre_W_r; eassumption
                        | eapply pre_sup_r; eassumption
                        | eapply pre_elimW_r; eassumption
                        | eapply pre_elimW_beta; eassumption
                        | eapply pre_codeW_r; eassumption
                        | eapply pre_vec_r; eassumption
                        | eapply pre_codevec_r; eassumption
                        | eapply pre_wf_r; eassumption
                        | eapply pre_supf_r; eassumption
                        | eapply pre_elimWf_r; eassumption
                        | eapply pre_elimWf_beta; eassumption
                        | eapply pre_codewf_r; eassumption
                        | eapply pre_tySq_r; eassumption
                        | eapply pre_sq_r; eassumption
                        | eapply pre_elimSq_r; eassumption
                        | eapply pre_elimSq_sq_rhs; eassumption ]].
  all: try solve [eauto 4 with presup].
  all: first [ solve [eapply pre_pi_r; eassumption] | solve [eapply pre_U_r; eauto with presup]
             | solve [eapply pre_El_r; eassumption] | solve [eapply pre_codeU_r; eauto with presup]
             | solve [eapply pre_codepi_r; eassumption]
             | solve [eapply pre_natrec_r; eassumption]
             | solve [eapply pre_lam_r; eassumption] | solve [eapply pre_app_r; eassumption]
             | solve [eapply pre_natrec_succ; eassumption]
             | solve [eapply pre_eta_l; eassumption]
             | solve [eapply wf_natrec; eauto 4 with presup]
             (* dependent pairs (M8) *)
             | solve [eapply pre_sig_r; eassumption] | solve [eapply pre_codesig_r; eassumption]
             | solve [eapply pre_pair_r; eassumption] | solve [eapply pre_fst_r; eassumption]
             | solve [eapply pre_snd_r; eassumption] | solve [eapply pre_snd_beta_l; eassumption]
             | solve [eapply pre_sig_eta_l; eassumption] | solve [eapply pre_snd_ty; eassumption]
             | solve [eapply wf_ty_single; [eassumption|]; eapply wf_fst; eassumption]
             | solve [eapply wft_El; eauto with presup; eapply wf_code_sig; eassumption]
             (* the unit type (M8c) *)
             | solve [eapply pre_unit_r; eauto using lequiv_refl, lequiv_wf_l]
             | solve [eapply pre_El_unit; eassumption]
             | solve [eapply pre_codeunit_r; eauto using lequiv_refl, lequiv_wf_l]
             | solve [eapply pre_triv_r; eauto using lequiv_refl, lequiv_wf_l]
             (* strict equality (M10a) *)
             | solve [eapply pre_seq_r; eassumption]
             | solve [eapply pre_sempty_r; eauto using lequiv_refl, lequiv_wf_l]
             | solve [eapply pre_srefl_r; eassumption]
             | solve [eapply pre_elimSEmpty_r; eassumption]
             (* the identity type (M11a) *)
             | solve [eapply pre_id_r; eassumption]
             | solve [eapply pre_idrefl_r; eassumption]
             | solve [eapply pre_J_ty; eassumption]
             | solve [eapply pre_J_r; eassumption]
             | solve [eapply wf_J; eauto 3 with presup]
             (* the identity type's code (M11b) *)
             | solve [eapply pre_codeid_r; eassumption]
             | solve [eapply wft_El; eauto with presup; eapply wf_code_id; eassumption]
             | solve [eapply wft_id; eauto with presup; apply wft_El; eauto with presup]
             (* strict equality's codes (M10c) *)
             | solve [eapply pre_codeseq_r; eassumption]
             | solve [eapply wft_El; eauto with presup; eapply wf_code_seq; eassumption]
             | solve [eapply wft_seq; eauto with presup; apply wft_El; eauto with presup]
             | solve [eapply pre_El_sempty; eassumption]
             | solve [eapply pre_codesempty_r; eauto using lequiv_refl, lequiv_wf_l]
             (* the empty type (M12a) *)
             | solve [eapply pre_empty_r; eauto using lequiv_refl, lequiv_wf_l]
             | solve [eapply pre_elimEmpty_r; eassumption]
             | solve [eapply wf_elimEmpty; eauto 3 with presup]
             (* binary sums (M12b) *)
             | solve [eapply pre_sum_r; eassumption]
             | solve [eapply pre_inl_r; eassumption] | solve [eapply pre_inr_r; eassumption]
             | solve [eapply pre_case_r; eassumption]
             | solve [eapply pre_case_inl_rhs; eassumption] | solve [eapply pre_case_inr_rhs; eassumption]
             | solve [eapply wf_case; eauto 3 with presup]
             | solve [eapply wf_ty_single; [eassumption|]; first [eapply wf_inl | eapply wf_inr]; eauto using compt_self]
             (* the codes of Empty and + (M12c) *)
             | solve [eapply pre_El_empty; eassumption]
             | solve [eapply pre_codeempty_r; eauto using lequiv_refl, lequiv_wf_l]
             | solve [eapply pre_codesum_r; eassumption]
             | solve [eapply wf_code_sum; eauto 3 with presup]
             | solve [eapply wft_El; eauto with presup; eapply wf_code_sum; eassumption]
             | solve [eapply wft_sum; eauto with presup; apply wft_El; eauto with presup]
             (* well-founded trees (M13a) *)
             | solve [eapply pre_W_r; eassumption]
             | solve [eapply pre_sup_r; eassumption]
             | solve [eapply pre_elimW_r; eassumption]
             | solve [eapply pre_elimW_beta; eassumption]
             | solve [apply wft_W; eauto 3 using compt_self with presup]
             | solve [eapply wf_sup; eauto 3 using compt_self with presup]
             | solve [eapply wf_elimW; eauto 3 using compt_self with presup]
             | solve [eapply wf_elimW; try eassumption; eapply wf_sup; eauto using compt_self]
             | solve [eapply wf_ty_single; try eassumption; eapply wf_sup; eauto using compt_self]
             (* the code of W (M13b) *)
             | solve [eapply pre_codeW_r; eassumption]
             | solve [eapply wf_code_W; eauto 3 with presup]
             | solve [eapply wft_El; eauto with presup; eapply wf_code_W; eassumption]
             | solve [apply wft_W; eauto 3 using compt_self with presup; apply wft_El; eauto with presup]
             (* length-indexed tuples and finite indices (M14a) *)
             | solve [eapply pre_vec_r; eassumption]
             | solve [apply wft_fin; assumption]
             | solve [apply wft_vec; eauto using lequiv_wf_l]
             | solve [eapply proj1;
                      first [eapply pre_vec_zero | eapply pre_vec_succ | eapply pre_fin_zero | eapply pre_fin_succ];
                      eassumption]
             | solve [eapply proj2;
                      first [eapply pre_vec_zero | eapply pre_vec_succ | eapply pre_fin_zero | eapply pre_fin_succ];
                      eassumption]
             (* the codes of Vec and Fin (M14b) *)
             | solve [eapply pre_codevec_r; eassumption]
             | solve [eapply wf_code_vec; eauto 3 with presup]
             | solve [eapply wf_code_fin; eauto 3 with presup]
             | solve [eapply wft_El; eauto with presup; first [eapply wf_code_vec | eapply wf_code_fin]; eassumption]
             | solve [apply wft_vec; eauto 3 with presup; apply wft_El; eauto with presup]
             (* finitary well-founded trees (M15a) *)
             | solve [eapply pre_wf_r; eassumption]
             | solve [eapply pre_supf_r; eassumption]
             | solve [eapply pre_elimWf_r; eassumption]
             | solve [eapply pre_elimWf_beta; eassumption]
             | solve [apply wft_wf; eauto 3 using compt_self with presup]
             (* the code of Wf (M15b) *)
             | solve [eapply pre_codewf_r; eassumption]
             | solve [eapply wf_code_wf; eauto 3 with presup]
             | solve [eapply wft_El; eauto with presup; eapply wf_code_wf; eassumption]
             | solve [apply wft_wf; eauto 3 using compt_self with presup; apply wft_El; eauto with presup]
             | solve [eapply wf_supf; eauto 3 using compt_self with presup]
             | solve [eapply wf_elimWf; eauto 3 using compt_self with presup]
             | solve [eapply wf_elimWf; try eassumption; eapply wf_supf; eauto using compt_self]
             | solve [eapply wf_ty_single; try eassumption; eapply wf_supf; eauto using compt_self]
             (* propositional truncation (M16a) *)
             | solve [eapply pre_tySq_r; eassumption]
             | solve [eapply pre_sq_r; eassumption]
             | solve [eapply pre_elimSq_r; eassumption]
             | solve [eapply pre_elimSq_sq_rhs; eassumption]
             | solve [apply wft_sq; eauto 3 with presup]
             | solve [eapply wf_elimSq; eauto 3 with presup]
             | solve [apply wft_sq; try eassumption; try solve [eauto with presup];
                      eapply wf_ty_single; try eassumption; eapply wf_sq; eassumption]
             | solve [eapply wf_elimSq; try eassumption; eapply wf_sq; eassumption] ].
Qed.

Section Named.
Context {G : gctx} {i : layer} (Hi : typeof i = i).

Let P4 := proj1 (proj2 (proj2 (proj2 presupposition))).
Let P5 := proj1 (proj2 (proj2 (proj2 (proj2 presupposition)))).
Let P6 := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 presupposition))))).
Let P7 := proj2 (proj2 (proj2 (proj2 (proj2 (proj2 presupposition))))).

Lemma wf_tm_ty {Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Γ ⊢[ i ] T @ l ].
Proof using Hi. intros H; exact (P4 _ _ _ _ _ _ H Hi). Qed.
Lemma eqty_wf_l {Γ T T' l} : [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> [ G ; Γ ⊢[ i ] T @ l ].
Proof using Hi. intros H; exact (proj1 (P5 _ _ _ _ _ _ H Hi)). Qed.
Lemma eqty_wf_r {Γ T T' l} : [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> [ G ; Γ ⊢[ i ] T' @ l ].
Proof using Hi. intros H; exact (proj2 (P5 _ _ _ _ _ _ H Hi)). Qed.
Lemma eqtm_wf_l {Γ t t' T l} : [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> [ G ; Γ ⊢[ i ] t : T @ l ].
Proof using Hi. intros H; exact (proj1 (P6 _ _ _ _ _ _ _ H Hi)). Qed.
Lemma eqtm_wf_r {Γ t t' T l} : [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> [ G ; Γ ⊢[ i ] t' : T @ l ].
Proof using Hi. intros H; exact (proj1 (proj2 (P6 _ _ _ _ _ _ _ H Hi))). Qed.
Lemma eqtm_wf_ty {Γ t t' T l} : [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> [ G ; Γ ⊢[ i ] T @ l ].
Proof using Hi. intros H; exact (proj2 (proj2 (P6 _ _ _ _ _ _ _ H Hi))). Qed.

Lemma eqctx_wf_l {Γ Γ'} : [ G ⊢[ i ] Γ ≅ Γ' ] -> [ G ; Γ ⊢[ i ] ].
Proof using Hi. intros H; exact (proj1 (P7 _ _ _ _ H Hi)). Qed.
Lemma eqctx_wf_r {Γ Γ'} : [ G ⊢[ i ] Γ ≅ Γ' ] -> [ G ; Γ' ⊢[ i ] ].
Proof using Hi. intros H; exact (proj1 (proj2 (P7 _ _ _ _ H Hi))). Qed.
(** Context conversion: the identity substitution between equivalent contexts. *)
Lemma eqctx_id {Γ Γ'} : [ G ⊢[ i ] Γ ≅ Γ' ] -> [ G ; Γ' ⊢[ i ] lshift 0 : Γ ].
Proof using Hi. intros H; exact (proj2 (proj2 (P7 _ _ _ _ H Hi))). Qed.

End Named.
