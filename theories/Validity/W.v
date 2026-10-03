(** * Validity of well-founded trees (M13_DESIGN.md, M13a)

    Formation of [W], [sup], [elim_W] and its β rule. The term relation at
    [W] is [WRel]: a term reduces to a [sup] whose shapes are related and
    whose children are related at [W] in every weakening, or to a neutral.
    [elim_W] is related by induction on [WRel] ([elimW_core]): at a [sup]
    both sides step to the step at the shape, the child function and the
    synthesized induction hypothesis, a λ whose applications step to
    [elim_W] at the children, related by the induction hypothesis of the
    children's premise; at a neutral, [elim_W] is neutral. *)
From DeLaM.Validity Require Export Sum.

Section W.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

(** ** Syntax *)

Section KwSyntax.
Context {G : gctx} {Γ : ctx} (ρ : kwk G Γ).

Lemma kty_single (T : ty) a : kty ρ T[lsingle a] = (ktyl ρ T)[lsingle (ktm ρ a)].
Proof. unfold kty, ktyl, ktm. now rewrite gwa_subst_ty, gwa_lsingle, lsingle_ren_ty. Qed.

Lemma ktyl_shift (T : ty) : ktyl ρ T⟨↑⟩ = (kty ρ T)⟨↑⟩.
Proof. unfold kty, ktyl. now rewrite gwa_ren_ty, shift_lift_ty. Qed.

End KwSyntax.

Section Telescope.
Context (d : lsub) (Hd : LK nftm d).

Lemma wfty_llift l l' (A B : ty) : (wfty l l' A B)[llift d] = wfty l l' A[d] B[llift d].
Proof. sub_eqW. Qed.

Lemma wihty_llift2 l l' l'' (A B M : ty) :
  (wihty l l' l'' A B M)[llift (llift d)] = wihty l l' l'' A[d] B[llift d] M[llift d].
Proof. sub_eqW. Qed.

Lemma wstepty_llift3 l l' (A B M : ty) :
  (wstepty l l' A B M)[llift (llift (llift d))] = wstepty l l' A[d] B[llift d] M[llift d].
Proof. sub_eqW. Qed.

Lemma shift3_single3 (u a f h : tm) : nftm u -> u⟨↑⟩⟨↑⟩⟨↑⟩[lsingle3 a f h] = u.
Proof.
  intros Nu. rewrite !ren_ren_comp, (ren_subst _ _ _ (lshift 0)).
  - apply subst_id; [exact Nu | intros; cbn; f_equal; lia].
  - intros n; pw.
Qed.

Lemma lift_single2_ty (T : ty) a f : T[llift (llift d)][lsingle2 a f] = T[lcons (lcons d a) f].
Proof.
  apply subst_subst_ty. intros [|[|m]]; rewrite !llk_llift; [reflexivity | reflexivity |].
  change (ren_tm (ren_tm ?x ?r) ?r') with x⟨r⟩⟨r'⟩. cbn [llk]. now rewrite shift2_single2 by apply Hd.
Qed.

Lemma lift_single3_ty (T : ty) a f h :
  T[llift (llift (llift d))][lsingle3 a f h] = T[lcons (lcons (lcons d a) f) h].
Proof.
  apply subst_subst_ty. intros [|[|[|m]]]; rewrite !llk_llift; [reflexivity .. |].
  change (ren_tm (ren_tm (ren_tm ?x ?r) ?r') ?r'') with x⟨r⟩⟨r'⟩⟨r''⟩. cbn [llk].
  now rewrite shift3_single3 by apply Hd.
Qed.

Lemma lift_single3 (t a f h : tm) :
  t[llift (llift (llift d))][lsingle3 a f h] = t[lcons (lcons (lcons d a) f) h].
Proof.
  apply subst_subst. intros [|[|[|m]]]; rewrite !llk_llift; [reflexivity .. |].
  change (ren_tm (ren_tm (ren_tm ?x ?r) ?r') ?r'') with x⟨r⟩⟨r'⟩⟨r''⟩. cbn [llk].
  now rewrite shift3_single3 by apply Hd.
Qed.

End Telescope.

(** The telescope and the induction hypothesis under global weakenings. *)
Lemma gwa_wfty γ l l' (A B : ty) : (wfty l l' A B)⟦γ⟧ = wfty l l' A⟦γ⟧ B⟦γ⟧.
Proof. repeat rewrite ?gwa_tyPi, ?gwa_ren_ty, ?gwa_tyW. reflexivity. Qed.
Lemma gwa_wihty γ l l' l'' (A B M : ty) : (wihty l l' l'' A B M)⟦γ⟧ = wihty l l' l'' A⟦γ⟧ B⟦γ⟧ M⟦γ⟧.
Proof.
  repeat rewrite ?gwa_tyPi, ?gwa_subst_ty, ?gwa_lsingle, ?gwa_app, ?gwa_var, ?gwa_ren_ty, ?gwa_ren, ?gwa_tyW.
  reflexivity.
Qed.
Lemma gwa_wstepty γ l l' (A B M : ty) : (wstepty l l' A B M)⟦γ⟧ = wstepty l l' A⟦γ⟧ B⟦γ⟧ M⟦γ⟧.
Proof.
  repeat rewrite ?gwa_subst_ty, ?gwa_lsingle, ?gwa_sup, ?gwa_var, ?gwa_ren_ty, ?gwa_ren. reflexivity.
Qed.
Lemma gwa_lsingle3 (a f h : tm) γ : (lsingle3 a f h)⟦γ⟧ = lsingle3 a⟦γ⟧ f⟦γ⟧ h⟦γ⟧.
Proof. now destruct γ. Qed.
Lemma gwa_wIH γ l l' l'' (A B M : ty) (c a f : tm) :
  (wIH l l' l'' A B M c a f)⟦γ⟧ = wIH l l' l'' A⟦γ⟧ B⟦γ⟧ M⟦γ⟧ c⟦γ⟧ a⟦γ⟧ f⟦γ⟧.
Proof. destruct γ; cbn [gwa]; [reflexivity | apply gren_wIH ..]. Qed.

(** Kripke weakenings under three binders, and under substitutions. *)
Definition ktm3 {G Δ} (ρ : kwk G Δ) (t : tm) : tm := t⟦kw_γ ρ⟧⟨rlift (rlift (rlift (kw_r ρ)))⟩.

Section KwSubst.
Context {G : gctx} {Δ : ctx} (ρ : kwk G Δ) (e : lsub).

Lemma ktyl_subst_lift (T : ty) : ktyl ρ T[llift e] = T⟦kw_γ ρ⟧[llift (kwsub ρ e)].
Proof.
  unfold ktyl, kwsub. rewrite gwa_subst_ty, subst_ren_lren_ty.
  apply subst_ext_ty. intros n. rewrite llk_lren, llk_llift_gwa.
  destruct n; rewrite !llk_llift; [reflexivity|].
  rewrite llk_lren. change (ren_tm ?x ?r') with x⟨r'⟩. now rewrite shift_lift.
Qed.

Lemma ktm3_subst_lift (t : tm) :
  ktm3 ρ t[llift (llift (llift e))] = t⟦kw_γ ρ⟧[llift (llift (llift (kwsub ρ e)))].
Proof.
  unfold ktm3, kwsub. rewrite gwa_subst, subst_ren_lren.
  apply subst_ext. intros n. rewrite llk_lren.
  destruct n as [|[|[|n]]]; repeat rewrite ?llk_llift_gwa, ?llk_llift, ?llk_lren; try reflexivity.
  change (ren_tm ?x ?r') with x⟨r'⟩. rewrite !ren_ren_comp. apply ren_ext_tm. intros k. rlk_simpl. lia.
Qed.

End KwSubst.

Lemma ktm_wIH {G Δ} (ρ : kwk G Δ) l l' l'' (A B M : ty) (c a f : tm) :
  ktm ρ (wIH l l' l'' A B M c a f) =
  wIH l l' l'' (kty ρ A) (ktyl ρ B) (ktyl ρ M) (ktm3 ρ c) (ktm ρ a) (ktm ρ f).
Proof. unfold ktm, kty, ktyl, ktm3. now rewrite gwa_wIH, ren_wIH. Qed.

(** The induction hypothesis's body and codomain at a position. *)
Lemma liftshift_llift_single_ty (T : ty) y : nfty T -> T⟨rlift ↑⟩[llift (lsingle y)] = T.
Proof.
  intros NT. rewrite (ren_subst_ty _ _ _ (lshift 0)).
  - apply subst_id_ty; [exact NT | intros; cbn; f_equal; lia].
  - intros [|n]; pw.
Qed.
Lemma lift3shift_llift3_single (t y : tm) : nftm t ->
  t⟨rlift (rlift (rlift ↑))⟩[llift (llift (llift (lsingle y)))] = t.
Proof.
  intros Nt. rewrite (ren_subst _ _ _ (lshift 0)).
  - apply subst_id; [exact Nt | intros; cbn; f_equal; lia].
  - intros [|[|[|n]]]; pw.
Qed.

Lemma wbody_single l l' l'' (A B M : ty) (c a f y : tm) :
  nfty A -> nfty B -> nfty M -> nftm c -> nftm a -> nftm f ->
  (wbody l l' l'' A B M c a f)[lsingle y] =
  tmElimW l l' l'' A B M c (app f l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩ y).
Proof.
  intros NA NB NM Nc Na Nf. rewrite subst_elimW, subst_app.
  assert (NBa : nfty B[lsingle a]) by (apply subst_nf_ty; [exact NB | intros [|n]; cbn; auto]).
  rewrite shift_single_ty, !liftshift_llift_single_ty, lift3shift_llift3_single, shift_single, shift_single_ty
    by first [assumption | apply ren_nf_ty | solve [cbn; auto]].
  reflexivity.
Qed.

Lemma wcod_single l l' (A B M : ty) (a f y : tm) :
  nfty A -> nfty B -> nfty M -> nftm a -> nftm f -> nftm y ->
  (wcod l l' A B M a f)[lsingle y] = M[lsingle (app f l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩ y)].
Proof.
  intros NA NB NM Na Nf Ny.
  rewrite (single_subst_ty (lsingle y)) by (intros [|n]; cbn; auto).
  assert (NBa : nfty B[lsingle a]) by (apply subst_nf_ty; [exact NB | intros [|n]; cbn; auto]).
  rewrite liftshift_llift_single_ty by exact NM. rewrite subst_app.
  rewrite liftshift_llift_single_ty, shift_single, shift_single_ty
    by first [assumption | apply ren_nf_ty | solve [cbn; auto]].
  reflexivity.
Qed.

(** ** Formation *)

Section WTy.
Context {G : gctx} {Γ : ctx} {l l' l3 l4 : lvl} {A A' B B' : ty}
  (Hwl : lwf (gL G) l) (Hwl' : lwf (gL G) l')
  (H3 : lequiv (gL G) l3 l) (H4 : lequiv (gL G) l4 l')
  (HB : [ G ; Γ ,, A @ l ⊢g B @ l' ])
  (VA : VTyG G Γ A A' l) (VB : VTyG G (Γ ,, A @ l) B B' l').

Lemma LR_W_here Δ d d' : SubRel G Γ Δ d d' ->
  LogRel (lmax l l') G Δ (tyW l l' A B)[d] (tyW l3 l4 A' B')[d'] (lmax l l')
    (WRel G Δ l l' A[d] B[llift d]
       (piDom (A := A) (A' := A') (l := l) (l' := l') Δ d d')
       (piCod (A := A) (A' := A') (B := B) (B' := B') (l := l) (l' := l') Δ d d')).
Proof.
  intros Hd.
  destruct (poly_here (F := tyW) (A := A) (A' := A') (B := B) (B' := B') Hwl Hwl' H3 H4 HB VA VB Δ d d'
              ltac:(intros; apply wft_W; auto using ge_compt) ltac:(reflexivity) Hd) as (P & Hdom & Hcod).
  exact (LRw _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ P Hdom Hcod (releq_refl _)).
Qed.

Lemma V_W : VTy G Γ (tyW l l' A B) (tyW l3 l4 A' B') (lmax l l').
Proof. intros Δ d d' Hd. eexists. exact (LR_W_here _ _ _ Hd). Qed.

End WTy.

(** ** Kripke helpers *)

Lemma WhRel_kw {G Δ T l t t'} (ρ : kwk G Δ) : WhRel G Δ T l t t' ->
  WhRel (kw_G ρ) (kw_Δ ρ) (kty ρ T) l (ktm ρ t) (ktm ρ t').
Proof.
  intros (w & w' & H & H' & N & N' & Ew). exists (ktm ρ w), (ktm ρ w').
  exact (conj (kw_tmred ρ H) (conj (kw_tmred ρ H') (conj (whnf_kw ρ _ N) (conj (whnf_kw ρ _ N')
           (kw_geq_tm ρ Ew))))).
Qed.

(** The type of a [sup]'s children, weakened. *)
Lemma kty_fty {G Δ} (ρ : kwk G Δ) l l' (A B : ty) a :
  kty ρ (tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩)
  = tyPi l' (lmax l l') (ktyl ρ B)[lsingle (ktm ρ a)] (tyW l l' (kty ρ A) (ktyl ρ B))⟨↑⟩.
Proof. now rewrite kty_tyPi, kty_single, ktyl_shift, kty_tyW. Qed.

(** An application's reduction in its function, through equivalent
    annotations. *)
Lemma tmred_app_annot {G Γ l l' la lb A0 B0 A1 B1 t w s} :
  lwf (gL G) l -> lwf (gL G) l' -> lequiv (gL G) la l -> lequiv (gL G) lb l' ->
  [ G ; Γ ⊢g A0 @ l ] -> [ G ; Γ ,, A0 @ l ⊢g B0 @ l' ] -> [ G ; Γ ⊢g s : A0 @ l ] ->
  [ G ; Γ ⊢g A0 ≅ A1 @ l ] -> [ G ; Γ ,, A0 @ l ⊢g B0 ≅ B1 @ l' ] ->
  [ G ; Γ ⊢g t ⤳* w : tyPi l l' A0 B0 @ lmax l l' ] ->
  [ G ; Γ ⊢g app t la lb A1 B1 s ⤳* app w la lb A1 B1 s : B0[lsingle s] @ l' ].
Proof.
  intros Hl Hl' H1 H2 HA0 HB0 Hs HA1 HB1 [Ht Hr Heq].
  pose proof (eqtm_wf_r ge_typeof Heq) as Hw.
  assert (Ann : forall u, [ G ; Γ ⊢g u : tyPi l l' A0 B0 @ lmax l l' ] ->
            [ G ; Γ ⊢g app u l l' A0 B0 s ≅ app u la lb A1 B1 s : B0[lsingle s] @ l' ])
    by (intros u Hu; apply eqtm_app; auto using ge_notV, lequiv_sym, eqtm_refl).
  assert (Mid : [ G ; Γ ⊢g app t l l' A0 B0 s ≅ app w l l' A0 B0 s : B0[lsingle s] @ l' ])
    by (apply eqtm_app; auto using ge_notV, lequiv_refl, eqty_refl, eqtm_refl).
  split.
  - exact (eqtm_wf_r ge_typeof (Ann t Ht)).
  - now apply reds_app.
  - eapply eqtm_trans; [apply eqtm_sym, (Ann t Ht)|]. eapply eqtm_trans; [exact Mid | exact (Ann w Hw)].
Qed.

(** [WRel] is closed under anti-reduction. *)
Lemma WRel_red {G Δ l1 l2 A B d c t t' u u'} :
  WRel G Δ l1 l2 A B d c u u' -> [ G ; Δ ⊢g t ⤳* u : tyW l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Δ ⊢g t' ⤳* u' : tyW l1 l2 A B @ lmax l1 l2 ] -> WRel G Δ l1 l2 A B d c t t'.
Proof.
  intros H Ht Ht'. destruct (WRel_inv H) as (w & w' & Hw & Hw' & Ew & Nw).
  econstructor; [exact (tmred_trans _ _ _ _ _ Ht Hw) | exact (tmred_trans _ _ _ _ _ Ht' Hw')
                | exact Ew | exact Nw].
Qed.

Lemma ktml_wbody {G Δ} (ρ : kwk G Δ) l l' l'' (A B M : ty) (c a f : tm) :
  ktml ρ (wbody l l' l'' A B M c a f) =
  wbody l l' l'' (kty ρ A) (ktyl ρ B) (ktyl ρ M) (ktm3 ρ c) (ktm ρ a) (ktm ρ f).
Proof.
  pose proof (ktm_wIH ρ l l' l'' A B M c a f) as X. unfold wIH in X. rewrite ktm_lam in X.
  injection X as _ X. exact X.
Qed.

Lemma ktyl_wcod {G Δ} (ρ : kwk G Δ) l l' (A B M : ty) (a f : tm) :
  ktyl ρ (wcod l l' A B M a f) = wcod l l' (kty ρ A) (ktyl ρ B) (ktyl ρ M) (ktm ρ a) (ktm ρ f).
Proof.
  unfold ktyl, kty, ktm.
  repeat rewrite ?gwa_subst_ty, ?gwa_lsingle, ?gwa_app, ?gwa_ren_ty, ?gwa_ren, ?gwa_var, ?gwa_tyW.
  rewrite lsingle_ren_ty. f_equal.
  - rewrite !ren_ren_comp_ty. apply ren_ext_ty. intros [|n]; rlk_simpl; reflexivity.
  - f_equal. push_ren. f_equal.
    + now rewrite shift_lift.
    + now rewrite shift_lift_ty, lsingle_ren_ty.
    + repeat progress (push_ren; rewrite ?ren_ren_comp_ty).
      f_equal; apply ren_ext_ty; intros [|n]; rlk_simpl; reflexivity.
Qed.

(** Kripke weakenings after a global weakening and a substitution. *)
Lemma kγ_ty {G Δ} (ρ : kwk G Δ) (T : ty) γ e : kty ρ T⟦γ⟧[e] = T⟦gwk_comp (kw_γ ρ) γ⟧[kwsub ρ e].
Proof. now rewrite kty_subst, gwa_comp_ty. Qed.
Lemma kγ_tyl {G Δ} (ρ : kwk G Δ) (T : ty) γ e :
  ktyl ρ T⟦γ⟧[llift e] = T⟦gwk_comp (kw_γ ρ) γ⟧[llift (kwsub ρ e)].
Proof. now rewrite ktyl_subst_lift, gwa_comp_ty. Qed.
Lemma kγ_tm3 {G Δ} (ρ : kwk G Δ) (t : tm) γ e :
  ktm3 ρ t⟦γ⟧[llift (llift (llift e))] = t⟦gwk_comp (kw_γ ρ) γ⟧[llift (llift (llift (kwsub ρ e)))].
Proof. now rewrite ktm3_subst_lift, gwa_comp_tm. Qed.

(** A reduction towards a whnf is on the way to it; so [WRel] is closed
    under reduction too. *)
Lemma reds_to_whnf t u w : reds t u -> reds t w -> whnf w -> reds u w.
Proof.
  intros H; revert w; induction H as [t|t v u Htv Hvu IH]; intros w Hw Nw; [exact Hw|].
  destruct Hw as [|y z Hr Hrs].
  - exfalso; exact (whnf_no_red _ _ Nw Htv).
  - apply IH; [| exact Nw]. now rewrite (red_det _ _ _ Htv Hr).
Qed.

Lemma tmred_to_whnf {G Δ t u w T l} : [ G ; Δ ⊢g t ⤳* u : T @ l ] -> [ G ; Δ ⊢g t ⤳* w : T @ l ] -> whnf w ->
  [ G ; Δ ⊢g u ⤳* w : T @ l ].
Proof.
  intros [Ht Hr Heq] [_ Hr' Heq'] Nw. split.
  - exact (eqtm_wf_r ge_typeof Heq).
  - exact (reds_to_whnf _ _ _ Hr Hr' Nw).
  - eapply eqtm_trans; [apply eqtm_sym, Heq | exact Heq'].
Qed.

Lemma WRel_red_fwd {G Δ l1 l2 A B d c t t' u u'} :
  WRel G Δ l1 l2 A B d c t t' -> [ G ; Δ ⊢g t ⤳* u : tyW l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Δ ⊢g t' ⤳* u' : tyW l1 l2 A B @ lmax l1 l2 ] -> WRel G Δ l1 l2 A B d c u u'.
Proof.
  intros H Hu Hu'. destruct (WRel_inv H) as (w & w' & Hw & Hw' & Ew & Nw).
  econstructor; [exact (tmred_to_whnf Hu Hw (WNf_whnf_l Nw)) | exact (tmred_to_whnf Hu' Hw' (WNf_whnf_r Nw))
                | exact Ew | exact Nw].
Qed.

(** Kripke facts at the identity world. *)
Lemma rel_at_id {G Δ X Y x y n l} {dR : DomRel G Δ} (HΔ : [ G ; Δ ⊢g ]) :
  nfty X -> nfty Y -> nftm x -> nftm y -> lmeasure l <= n ->
  (forall ρ, LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kty ρ X) (kty ρ Y) l (dR ρ)) ->
  dR (kw_loc wk_id (wkwf_id Δ) HΔ) (ktm (kw_loc wk_id (wkwf_id Δ) HΔ) x) (ktm (kw_loc wk_id (wkwf_id Δ) HΔ) y) ->
  LRtm l G Δ X Y x y.
Proof.
  intros NX NY Nx Ny Hn HD h. pose proof (HD (kw_loc wk_id (wkwf_id Δ) HΔ)) as X0.
  unfold kty, ktm, kw_loc in X0, h; cbn [kw_G kw_Δ kw_γ kw_r gwa wk_ren] in X0, h.
  rewrite !ren_id_ty in X0 by assumption. rewrite !ren_id_tm in h by assumption.
  exact (LRtm_of (proj2 (LogRel_stage _ _ _ _ _ _ _ Hn) X0) h).
Qed.

Lemma WhRel_at_id {G Δ T l t t'} (HΔ : [ G ; Δ ⊢g ]) : nfty T -> nftm t -> nftm t' ->
  WhRel (kw_G (kw_loc wk_id (wkwf_id Δ) HΔ)) (kw_Δ (kw_loc wk_id (wkwf_id Δ) HΔ))
    (kty (kw_loc wk_id (wkwf_id Δ) HΔ) T) l
    (ktm (kw_loc wk_id (wkwf_id Δ) HΔ) t) (ktm (kw_loc wk_id (wkwf_id Δ) HΔ) t') ->
  WhRel G Δ T l t t'.
Proof.
  intros NT Nt Nt' H. unfold kty, ktm, kw_loc in H; cbn [kw_G kw_Δ kw_γ kw_r gwa wk_ren] in H.
  now rewrite ren_id_ty, !ren_id_tm in H.
Qed.

(** [WRel] at two data, each the relations of some derivations at the
    same left types in every weakening, are the same relation. *)
Lemma WRel_canon {G Δ l1 l2 A B A1 B1 A2 B2 n} {d1 d2 : DomRel G Δ} {c1 : CodRel G Δ d1} {c2 : CodRel G Δ d2} :
  (forall ρ, LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kty ρ A) (kty ρ A1) l1 (d1 ρ)) ->
  (forall ρ x y h, LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (ktyl ρ B)[lsingle x] (ktyl ρ B1)[lsingle y] l2 (c1 ρ x y h)) ->
  (forall ρ, LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (kty ρ A) (kty ρ A2) l1 (d2 ρ)) ->
  (forall ρ x y h, LR n (LRbelow n) (kw_G ρ) (kw_Δ ρ) (ktyl ρ B)[lsingle x] (ktyl ρ B2)[lsingle y] l2 (c2 ρ x y h)) ->
  releq (WRel G Δ l1 l2 A B d1 c1) (WRel G Δ l1 l2 A B d2 c2).
Proof.
  intros D1 C1 D2 C2. apply WRel_releq.
  - intros ρ. exact (LR_irrel _ _ _ _ _ _ _ _ _ _ (D1 ρ) (D2 ρ)).
  - intros ρ x y h h'. exact (LR_irrel _ _ _ _ _ _ _ _ _ _ (C1 ρ x y h) (C2 ρ x y h')).
Qed.

(** ** [sup] *)

Section SupV.
Context {G : gctx} {Γ : ctx} {l l' l3 l4 : lvl} {A A' B B' : ty} {a a' f f' : tm}
  (Hwl : lwf (gL G) l) (Hwl' : lwf (gL G) l')
  (H3 : lequiv (gL G) l3 l) (H4 : lequiv (gL G) l4 l')
  (HB : [ G ; Γ ,, A @ l ⊢g B @ l' ])
  (VA : VTyG G Γ A A' l) (VB : VTyG G (Γ ,, A @ l) B B' l')
  (Va : VTm G Γ a a' A l)
  (Vf : VTm G Γ f f' (tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩) (lmax l' (lmax l l'))).

Lemma V_sup : VTm G Γ (tmSup l l' A B a f) (tmSup l3 l4 A' B' a' f') (tyW l l' A B) (lmax l l').
Proof.
  intros Δ d d' Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  pose proof (VTyG_loc VA) as VAl. pose proof (VTyG_loc VB) as VBl.
  pose proof (VTy_refl_l VAl) as VAA. pose proof (VTy_refl_l VBl) as VBB.
  pose proof (lwf_max Hwl Hwl') as HwL.
  (* the relation at [W], with the left data, and the data's derivations *)
  pose proof (LR_W_here Hwl Hwl' (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwl') HB
                (VTyG_refl_l VA) (VTyG_refl_l VB) _ _ _ Hd) as HW.
  destruct (poly_here (F := tyW) (A := A) (A' := A) (B := B) (B' := B) Hwl Hwl'
              (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwl') HB (VTyG_refl_l VA) (VTyG_refl_l VB) Δ d d'
              ltac:(intros; apply wft_W; auto using ge_compt) ltac:(reflexivity) Hd) as (_ & Hdom & Hcod).
  eapply LRtm_of; [exact HW|]. push_subst.
  (* escapes *)
  destruct (VAl _ _ _ Hd) as [RA HRA]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HAd & _ & EA).
  destruct (VAA _ _ _ Hd) as [RA0 HRA0]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA0) as (_ & _ & EAA0).
  assert (EAA : [ G ; Δ ⊢ A[d] ≈ A[d] @ l ]) by exact (geq_ty_trans EAA0 (geq_ty_sym EAA0)).
  assert (Hlift : SubRel G (Γ ,, A @ l) (Δ ,, A[d] @ l) (llift d) (llift d'))
    by exact (SubRel_lift Hd VAA HAd Hwl).
  assert (Hliftd : SubRel G (Γ ,, A @ l) (Δ ,, A[d] @ l) (llift d) (llift d))
    by exact (SubRel_lift (SubRel_refl_l Hd) VAA HAd Hwl).
  destruct (VBl _ _ _ Hlift) as [RB HRB]. destruct (escape_ty _ _ _ _ _ _ _ _ HRB) as (HBd & _ & EB).
  destruct (VBB _ _ _ Hliftd) as [RB0 HRB0]. destruct (escape_ty _ _ _ _ _ _ _ _ HRB0) as (_ & _ & EBB).
  pose proof (Va _ _ _ Hd) as Xa. pose proof (LRtm_geq Xa) as Ea.
  pose proof (Vf _ _ _ Hd) as Xf.
  rewrite !subst_tyPi, !single_subst_ty, !shift_llift_ty, !subst_tyW in Xf by assumption.
  pose proof (LRtm_geq Xf) as Ef.
  pose proof (geq_tm_sup (lequiv_sym _ _ _ H3) (lequiv_sym _ _ _ H4) HAd EA HBd EB Ea Ef) as Dsup.
  pose proof (geq_tm_sound Dsup) as Dsup'.
  (* the child function's [PiRel] *)
  destruct Xf as (Rf & HRf & Hff).
  destruct (escape_ty _ _ _ _ _ _ _ _ HRf) as (HPi & _ & _).
  destruct (LR_inv_pi HRf (tyred_refl _ _ HPi)) as (m3 & m4 & C' & D' & domR & codR & P & domAd & codAd & HRR).
  apply HRR in Hff. destruct Hff as (wf & wf' & Hr & Hr' & Nw & Nw' & Ew & _ & K).
  destruct P as [_ Hm3 Hm4 _ _ _ _ HBa HCw HWu _ HCC HDD].
  assert (EPi : [ G ; Δ ⊢g tyPi m3 m4 C' D' ≅ tyPi l' (lmax l l') B[llift d][lsingle a[d]]
                                          (tyW l l' A[d] B[llift d])⟨↑⟩ @ lmax l' (lmax l l') ])
    by (apply eqty_sym, geq_ty_sound, geq_ty_pi; auto using lequiv_sym).
  assert (Hr'' : [ G ; Δ ⊢g f'[d'] ⤳* wf' : tyPi l' (lmax l l') B[llift d][lsingle a[d]]
                                             (tyW l l' A[d] B[llift d])⟨↑⟩ @ lmax l' (lmax l l') ])
    by (eapply tmred_conv; [apply ge_typeof | exact Hr' | exact EPi]).
  apply (wrel _ _ _ _ _ _ _ _ _ _ (tmSup l l' A[d] B[llift d] a[d] f[d]) (tmSup l3 l4 A'[d'] B'[llift d'] a'[d'] f'[d'])).
  - exact (tmred_refl _ _ _ (eqtm_wf_l ge_typeof Dsup')).
  - exact (tmred_refl _ _ _ (eqtm_wf_r ge_typeof Dsup')).
  - exact Dsup.
  - apply wnf_sup.
    + now apply lequiv_refl.
    + now apply lequiv_refl.
    + exact H3.
    + exact H4.
    + exact EAA.
    + exact EA.
    + exact EBB.
    + exact EB.
    + intros ρ. unfold piDom. apply (LRtm_stage (l := l)); [rewrite lmeasure_max; lia | exact (LRtm_kw ρ Xa)].
    + intros ρ. rewrite <- kty_fty. apply WhRel_kw.
      exists wf, wf'. exact (conj Hr (conj Hr'' (conj Nw (conj Nw' Ew)))).
    + intros ρ ha b b' Hbb la lb A1 B1 la' lb' A1' B1' H1 H2 H1' H2' HA1 HB1 HA1' HB1'.
      pose proof (kw_lwf ρ Hwl') as Hwl'ρ. pose proof (kw_lwf ρ HwL) as HwLρ.
      assert (Hle1 : lmeasure l' <= lmeasure (lmax l' (lmax l l'))) by (rewrite !lmeasure_max; lia).
      assert (Hle2 : lmeasure (lmax l l') <= lmeasure (lmax l' (lmax l l'))) by (rewrite !lmeasure_max; lia).
      assert (Hle3 : lmeasure l' <= lmeasure (lmax l l')) by (rewrite !lmeasure_max; lia).
      (* the positions, in the function's domain relation *)
      pose proof (domAd ρ) as DOM. rewrite kty_single in DOM.
      apply (proj2 (LogRel_stage _ _ _ _ _ _ _ Hle1)) in DOM.
      apply (proj2 (LRtm_stage Hle3)) in Hbb.
      pose proof (LRtm_inv DOM (LRtm_irrel_r Hbb (ex_intro _ _ DOM))) as hb.
      destruct (LRtm_escape Hbb) as [Hb Hb'].
      (* the annotations, moved to the function's types *)
      pose proof (kw_geq_ty ρ HCC) as KC. rewrite kty_single in KC.
      pose proof (kw_geq_ty_l ρ HBa Hwl' HDD) as KD. rewrite kty_single, ktyl_shift, kty_tyW in KD.
      pose proof (kw_ty ρ HCw) as HCwρ.
      assert (HA1c : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ C' ≈ A1' @ l' ])
        by exact (geq_ty_trans (geq_ty_sym KC) HA1').
      assert (HB1c : [ kw_G ρ ; kw_Δ ρ ,, kty ρ C' @ l' ⊢ ktyl ρ D' ≈ B1' @ lmax l l' ]).
      { eapply geq_ty_ctxconv; [exact (geq_ty_sound KC) | now apply lequiv_refl
                               | apply ext_wf_g; [exact HCwρ | exact Hwl'ρ] |].
        exact (geq_ty_trans (geq_ty_sym KD) HB1'). }
      pose proof (K ρ b b' hb la lb la' lb' A1 B1 A1' B1' H1 H2 H1' H2') as K1.
      rewrite kty_single, ktyl_shift, kty_tyW in K1.
      pose proof (K1 HA1 HB1 HA1c HB1c) as C0.
      (* the codomain relation is [WRel], at the composed data *)
      pose proof (codAd ρ b b' hb) as COD.
      pose proof (kw_ty ρ HPi) as HPiρ. rewrite kty_fty in HPiρ.
      assert (HWρ : [ kw_G ρ ; kw_Δ ρ ⊢g tyW l l' (kty ρ A[d]) (ktyl ρ B[llift d]) @ lmax l l' ]).
      { destruct (escape_ty _ _ _ _ _ _ _ _ HW) as (HWd & _ & _). rewrite subst_tyW in HWd.
        pose proof (kw_ty ρ HWd) as Z. rewrite kty_tyW in Z. exact Z. }
      rewrite ktyl_shift, kty_tyW, shift_single_ty in COD by exact (wf_ty_nf HWρ).
      apply (proj2 (LogRel_stage _ _ _ _ _ _ _ Hle2)) in COD.
      destruct (LR_inv_W COD (tyred_refl _ _ HWρ)) as (n3 & n4 & C'' & D'' & domR0 & codR0 & _ & domAd0 & codAd0 & HR0).
      pose proof (proj1 (HR0 _ _) C0) as X0.
      assert (D2 : forall ρ' : kwk (kw_G ρ) (kw_Δ ρ),
                 LR (lmeasure (lmax l l')) (LRbelow (lmeasure (lmax l l'))) (kw_G ρ') (kw_Δ ρ')
                   (kty ρ' (kty ρ A[d])) (kty ρ' (kty ρ A[d'])) l
                   (piDom (A := A) (A' := A) (l := l) (l' := l') Δ d d' (kw_comp ρ ρ'))).
      { intros ρ'. pose proof (Hdom (kw_comp ρ ρ')) as Y. rewrite !kty_comp in Y. exact Y. }
      assert (C2 : forall (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) x y
                   (h : piDom (A := A) (A' := A) (l := l) (l' := l') Δ d d' (kw_comp ρ ρ') x y),
                 LR (lmeasure (lmax l l')) (LRbelow (lmeasure (lmax l l'))) (kw_G ρ') (kw_Δ ρ')
                   (ktyl ρ' (ktyl ρ B[llift d]))[lsingle x] (ktyl ρ' (ktyl ρ B[llift d']))[lsingle y] l'
                   (piCod (A := A) (A' := A) (B := B) (B' := B) (l := l) (l' := l') Δ d d' (kw_comp ρ ρ') x y h)).
      { intros ρ' x y h. pose proof (Hcod (kw_comp ρ ρ') x y h) as Y. rewrite !ktyl_comp in Y. exact Y. }
      pose proof (proj1 (WRel_canon domAd0 codAd0 D2 C2 _ _) X0) as X1.
      (* back from the whnfs of the child functions *)
      pose proof (kw_ty ρ HBa) as HBaρ. rewrite kty_single in HBaρ.
      pose proof (kw_ty_l ρ HBa Hwl' HWu) as HWuρ. rewrite kty_single, ktyl_shift, kty_tyW in HWuρ.
      pose proof (kw_tmred ρ Hr) as Rρ. rewrite kty_fty in Rρ.
      pose proof (kw_tmred ρ Hr'') as Rρ'. rewrite kty_fty in Rρ'.
      pose proof (tmred_app_annot Hwl'ρ HwLρ (kw_lequiv ρ H1) (kw_lequiv ρ H2) HBaρ HWuρ Hb
                    (geq_ty_sound HA1) (geq_ty_sound HB1) Rρ) as Y.
      pose proof (tmred_app_annot Hwl'ρ HwLρ (kw_lequiv ρ H1') (kw_lequiv ρ H2') HBaρ HWuρ Hb'
                    (geq_ty_sound HA1') (geq_ty_sound HB1') Rρ') as Y'.
      rewrite shift_single_ty in Y, Y' by exact (wf_ty_nf HWρ).
      exact (WRel_red X1 Y Y').
Qed.

End SupV.

(** ** The code of [W] (M13b) and its decoding, as Σ's *)

(** Decoding a [W] code, with annotations [k1 k2] equivalent to the levels
    [l1 l2] at which the premises are typed. *)
Lemma tyred_El_W {G Δ la l1 l2 k1 k2 s t} :
  lequiv (gL G) k1 l1 -> lequiv (gL G) k2 l2 ->
  [ G ; Δ ⊢g s : tyU l1 @ lsuc l1 ] -> [ G ; Δ ,, tyEl k1 s @ l1 ⊢g t : tyU l2 @ lsuc l2 ] ->
  lequiv (gL G) la (lmax l1 l2) ->
  [ G ; Δ ⊢g tyEl la (tmW k1 k2 s t) ⤳* tyW k1 k2 (tyEl k1 s) (tyEl k2 t) @ lmax l1 l2 ].
Proof.
  intros H1 H2 Hs Ht Hla.
  pose proof (conv_U' Hs (lequiv_sym _ _ _ H1)) as Hs1.
  destruct (El_annot Hs H1) as [HA _].
  assert (HΓ : [ G ; Δ ,, tyEl k1 s @ k1 ⊢g ])
    by (apply ext_wf_g; [eapply lconv_ty; [exact HA | now apply lequiv_sym] | eauto using lequiv_wf_l]).
  pose proof (stab_tm ge_typeof (eqty_refl _ _ _ _ _ HA) (lequiv_sym _ _ _ H1) HΓ Ht) as Ht1.
  pose proof (conv_U' Ht1 (lequiv_sym _ _ _ H2)) as Ht2.
  assert (Hc : [ G ; Δ ⊢g tmW k1 k2 s t : tyU (lmax k1 k2) @ lsuc (lmax k1 k2) ])
    by (apply wf_code_W; eauto using ge_compt, ge_notV, lequiv_wf_l).
  assert (Hm : lequiv (gL G) (lmax l1 l2) (lmax k1 k2)) by (apply lequiv_max; now apply lequiv_sym).
  destruct (El_annot Hc (lequiv_trans _ _ _ _ Hla Hm)) as [HEl HEq].
  eapply tyred_lconv; [|exact Hm].
  apply tyred_step; [exact HEl | constructor |].
  eapply eqty_trans; [exact HEq|].
  apply eqty_sym, eqty_El_W; eauto using ge_compt, ge_notV, lequiv_wf_l.
Qed.

Section CodeWV.
Context {G : gctx} {Γ : ctx} {l1 l2 l3 l4 : lvl} {s s' t t' : tm}
  (Hw1 : lwf (gL G) l1) (Hw2 : lwf (gL G) l2)
  (H13 : lequiv (gL G) l1 l3) (H24 : lequiv (gL G) l2 l4)
  (Hs : [ G ; Γ ⊢g s : tyU l1 @ lsuc l1 ])
  (Ht : [ G ; Γ ,, tyEl l1 s @ l1 ⊢g t : tyU l2 @ lsuc l2 ])
  (Vs : VTmG G Γ s s' (tyU l1) (lsuc l1))
  (Vt : VTmG G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) (lsuc l2)).

Lemma V_code_W :
  VTm G Γ (tmW l1 l2 s t) (tmW l3 l4 s' t') (tyU (lmax l1 l2)) (lsuc (lmax l1 l2)).
Proof.
  (* facts in [Γ] *)
  destruct (El_annot Hs (lequiv_refl _ _ Hw1)) as [HA _].
  destruct (El_annot Ht (lequiv_refl _ _ Hw2)) as [HB _].
  pose proof (V_ElG Hw1 H13 Vs) as VA. pose proof (V_ElG Hw2 H24 Vt) as VB.
  (* at a pair of related substitutions *)
  intros Δ d d' Hd. pose proof (SubRel_ctx Hd) as HΔ.
  pose proof (SubRel_wf_l _ _ _ _ _ Hd) as Hwd.
  pose proof (wf_ty_subst ge_typeof HA Hwd) as HAd.
  pose proof (wf_tm_subst ge_typeof Hs Hwd) as Hsd.
  pose proof (wf_tm_subst ge_typeof Ht (lsub_wf_lift _ _ ge_typeof _ _ _ _ _ Hwd HAd Hw1)) as Htd.
  rewrite !subst_tyU, !subst_tyEl in *.
  assert (Hlift : SubRel G (Γ ,, tyEl l1 s @ l1) (Δ ,, tyEl l1 s[d] @ l1) (llift d) (llift d'))
    by exact (SubRel_lift Hd (VTy_refl_l (VTyG_loc VA)) HAd Hw1).
  pose proof (VTmG_loc Vt _ _ _ Hlift) as Xt. pose proof (VTmG_loc Vs _ _ _ Hd) as Xs. rewrite !subst_tyU in Xs, Xt.
  (* the right-hand codes, by escape *)
  pose proof (proj2 (LRtm_escape Xs)) as Hs'd'.
  destruct (El_annot Hs'd' (lequiv_sym _ _ _ H13)) as [HA'd' _].
  assert (HAA'd : [ G ; Δ ⊢g tyEl l1 s[d] ≅ tyEl l3 s'[d'] @ l1 ])
    by exact (eqty_El _ _ _ _ _ _ _ ge_notV H13 (geq_tm_sound (LRtm_geq Xs))).
  assert (HΔA' : [ G ; Δ ,, tyEl l3 s'[d'] @ l1 ⊢g ]) by now apply ext_wf_g.
  pose proof (stab_tm ge_typeof HAA'd (lequiv_refl _ _ Hw1) HΔA' (proj2 (LRtm_escape Xt))) as Ht'd'.
  assert (Hgeq : [ G ; Δ ⊢ tmW l1 l2 s[d] t[llift d] ≈ tmW l3 l4 s'[d'] t'[llift d']
                     : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ])
    by exact (geq_tm_code_W H13 H24 Hsd (LRtm_geq Xs) (LRtm_geq Xt)).
  pose proof (geq_tm_sound Hgeq) as Hgeq'.
  push_subst. apply (LRtm_U (lwf_max Hw1 Hw2)).
  exists (tmW l1 l2 s[d] t[llift d]), (tmW l3 l4 s'[d'] t'[llift d']).
  refine (conj (tmred_refl _ _ _ (eqtm_wf_l ge_typeof Hgeq'))
           (conj (tmred_refl _ _ _ (eqtm_wf_r ge_typeof Hgeq'))
           (conj (whnf_tmW _ _ _ _) (conj (whnf_tmW _ _ _ _) (conj Hgeq _))))).
  intros la lb Hla Hlb. rewrite LRbelow_spec by (rewrite ?lmeasure_suc; lia).
  eexists. eapply LR_red_ty;
    [exact (LR_W_here Hw1 Hw2 (lequiv_sym _ _ _ H13) (lequiv_sym _ _ _ H24) HB VA VB _ _ _ Hd)
    | | ]; push_subst.
  - apply tyred_El_W; auto using lequiv_refl.
  - apply tyred_El_W; auto using lequiv_sym.
Qed.

End CodeWV.

Lemma V_El_W {G Γ l l' s t} :
  lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢g s : tyU l @ lsuc l ] -> [ G ; Γ ,, tyEl l s @ l ⊢g t : tyU l' @ lsuc l' ] ->
  VTmG G Γ s s (tyU l) (lsuc l) -> VTmG G (Γ ,, tyEl l s @ l) t t (tyU l') (lsuc l') ->
  VTy G Γ (tyW l l' (tyEl l s) (tyEl l' t)) (tyEl (lmax l l') (tmW l l' s t)) (lmax l l').
Proof.
  intros Hw Hw' Hs Ht Vs Vt Δ d d' Hd.
  destruct (El_annot Hs (lequiv_refl _ _ Hw)) as [HA _].
  destruct (El_annot Ht (lequiv_refl _ _ Hw')) as [HB _].
  pose proof (V_ElG Hw (lequiv_refl _ _ Hw) Vs) as VA. pose proof (V_ElG Hw' (lequiv_refl _ _ Hw') Vt) as VB.
  pose proof (LR_W_here Hw Hw' (lequiv_refl _ _ Hw) (lequiv_refl _ _ Hw') HB VA VB _ _ _ Hd) as HP.
  destruct (escape_ty _ _ _ _ _ _ _ _ HP) as (HPd & _ & _).
  pose proof (SubRel_wf_r Hd) as Hwd'.
  pose proof (wf_ty_subst ge_typeof HA Hwd') as HAd'.
  pose proof (wf_tm_subst ge_typeof Hs Hwd') as Hsd'.
  pose proof (wf_tm_subst ge_typeof Ht (lsub_wf_lift _ _ ge_typeof _ _ _ _ _ Hwd' HAd' Hw)) as Htd'.
  rewrite !subst_tyU, !subst_tyEl in *.
  eexists. eapply LR_red_ty; [exact HP | apply tyred_refl, HPd |]. push_subst.
  apply tyred_El_W; auto using lequiv_refl, lwf_max.
Qed.

End W.
