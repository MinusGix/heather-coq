(** * Validity of Heather's indexed [M] (M18_DESIGN.md, M18b)

    Formation of [M], [out] and [corec], and β. As [IWf]'s (M17b), the
    index type's, the shapes' and the positions' relations live at the
    stage of the [M] type's level [mlvl l l' li] ([mIdx], [mSh], [mPos]),
    canonical there. *)
From DeLaM.Validity Require Export W Sigma.
From DeLaM.LogRel Require Import MAux.
From DeLaM.Typing Require Import PresupM.

Section MV.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

(** ** Syntax *)

Lemma kwsub_nf {G Δ} (ρ : kwk G Δ) d : LK nftm d -> LK nftm (kwsub ρ d).
Proof using . intros _ n. rewrite llk_kwsub. unfold ktm. apply ren_nf. Qed.

Section KwSubst.
Context {G : gctx} {Δ : ctx} (ρ : kwk G Δ) (e : lsub).

Lemma ktyll_subst_lift' (T : ty) : ktyll ρ T[llift (llift e)] = T⟦kw_γ ρ⟧[llift (llift (kwsub ρ e))].
Proof using .
  unfold ktyll, kwsub. rewrite gwa_subst_ty, subst_ren_lren_ty.
  apply subst_ext_ty. intros n. rewrite llk_lren.
  destruct n as [|[|n]]; repeat rewrite ?llk_llift_gwa, ?llk_llift, ?llk_lren; try reflexivity.
  change (ren_tm ?x ?r') with x⟨r'⟩. rewrite !ren_ren_comp. apply ren_ext_tm. intros k. rlk_simpl. lia.
Qed.
Lemma ktmlll_subst_lift (t : tm) :
  ktmlll ρ t[llift (llift (llift e))] = t⟦kw_γ ρ⟧[llift (llift (llift (kwsub ρ e)))].
Proof using . exact (ktm3_subst_lift ρ e t). Qed.

End KwSubst.

Section Lifts.
Context (D : lsub) (HD : LK nftm D).

Lemma lift2_lift_single_ty (T : ty) x : T[llift (llift D)][llift (lsingle x)] = T[llift (lcons D x)].
Proof using HD.
  apply subst_subst_ty. intros [|[|m]]; rewrite ?llk_llift; cbn [llk]; cbn; rewrite ?llk_llift; cbn; try reflexivity.
  change (ren_tm ?y ?r) with y⟨r⟩. rewrite shift_llift, shift_single by apply HD.
  reflexivity.
Qed.

Lemma lift3_lift2_single (t : tm) x :
  t[llift (llift (llift D))][llift (llift (lsingle x))] = t[llift (llift (lcons D x))].
Proof using HD.
  apply subst_subst. intros [|[|[|m]]]; rewrite ?llk_llift; cbn [llk]; cbn; rewrite ?llk_llift; cbn;
    rewrite ?llk_llift; cbn; try reflexivity.
  change (ren_tm ?y ?r) with y⟨r⟩. rewrite !shift_llift, shift_single by apply HD.
  reflexivity.
Qed.

Lemma lift3_lift_single2 (t : tm) x a :
  t[llift (llift (llift D))][llift (lsingle2 x a)] = t[llift (lcons (lcons D x) a)].
Proof using HD.
  apply subst_subst. intros [|[|[|m]]]; rewrite ?llk_llift; cbn [llk]; cbn; rewrite ?llk_llift; cbn;
    try reflexivity.
  change (ren_tm ?y ?r) with y⟨r⟩. rewrite !shift_llift, shift2_single2 by apply HD.
  reflexivity.
Qed.

End Lifts.

Lemma shift_cons_ty' (T : ty) d a : T⟨↑⟩[lcons d a] = T[d].
Proof using . apply ren_subst_ty; intros n; now rewrite rlk_shift1. Qed.

(** The signature's components in a world, at a substitution and at an
    index, a shape and a position. *)
Section KwInst.
Context {G : gctx} {Δ : ctx} (ρ : kwk G Δ) (d : lsub) (Hd : LK nftm d).

Lemma ktyll_subst_single2 (T : ty) x a :
  (ktyll ρ T[llift (llift d)])[lsingle2 x a] = T⟦kw_γ ρ⟧[lcons (lcons (kwsub ρ d) x) a].
Proof using Hd. rewrite ktyll_subst_lift'. exact (lift_single2_ty _ (kwsub_nf ρ d Hd) _ _ _). Qed.

Lemma ktmlll_subst_single3 (t : tm) x a p :
  (ktmlll ρ t[llift (llift (llift d))])[lsingle3 x a p] = t⟦kw_γ ρ⟧[lcons (lcons (lcons (kwsub ρ d) x) a) p].
Proof using Hd. rewrite ktmlll_subst_lift. exact (lift_single3 _ (kwsub_nf ρ d Hd) _ _ _ _). Qed.

Lemma ktyll_subst_lift_single (T : ty) x :
  (ktyll ρ T[llift (llift d)])[llift (lsingle x)] = T⟦kw_γ ρ⟧[llift (lcons (kwsub ρ d) x)].
Proof using Hd. rewrite ktyll_subst_lift'. exact (lift2_lift_single_ty _ (kwsub_nf ρ d Hd) _ _). Qed.

Lemma ktmlll_subst_lift2_single (t : tm) x :
  (ktmlll ρ t[llift (llift (llift d))])[llift (llift (lsingle x))] =
  t⟦kw_γ ρ⟧[llift (llift (lcons (kwsub ρ d) x))].
Proof using Hd. rewrite ktmlll_subst_lift. exact (lift3_lift2_single _ (kwsub_nf ρ d Hd) _ _). Qed.

Lemma ktmlll_subst_lift_single2 (t : tm) x a :
  (ktmlll ρ t[llift (llift (llift d))])[llift (lsingle2 x a)] =
  t⟦kw_γ ρ⟧[llift (lcons (lcons (kwsub ρ d) x) a)].
Proof using Hd. rewrite ktmlll_subst_lift. exact (lift3_lift_single2 _ (kwsub_nf ρ d Hd) _ _ _). Qed.

End KwInst.

(** A canonical relation, read at a type related to the left one. *)
Lemma LRrel_iff {n l G' Δ T T' T'' t t'} : lmeasure l <= n ->
  LRty l G' Δ T T' -> LRty l G' Δ T T'' ->
  LRrel n G' Δ T T' l t t' <-> LRtm l G' Δ T T'' t t'.
Proof using EL VL VN.
  intros Hn H1 H2. split; intros H.
  - apply (LRtm_stage Hn) in H. exact (LRtm_irrel_r H H2).
  - apply (LRtm_stage Hn). exact (LRtm_irrel_r H H1).
Qed.

(** ** Formation *)

Section MTy.
Context {G : gctx} {Γ : ctx} {l l' li k k' ki : lvl} {X X' A A' B B' : ty} {C C' : tm}
  (Hwl : lwf (gL G) l) (Hwl' : lwf (gL G) l') (Hwli : lwf (gL G) li)
  (Hk : lequiv (gL G) k l) (Hk' : lequiv (gL G) k' l') (Hki : lequiv (gL G) ki li)
  (VX : VTyG G Γ X X' li) (VA : VTyG G (Γ ,, X @ li) A A' l)
  (VB : VTyG G (Γ ,, X @ li ,, A @ l) B B' l')
  (VC : VTmG G (Γ ,, X @ li ,, A @ l ,, B @ l') C C' X⟨↑⟩⟨↑⟩⟨↑⟩ li).

Let K := lmeasure (mlvl l l' li).
Lemma K_l : lmeasure l <= K.
Proof using . unfold K; rewrite !lmeasure_max; lia. Qed.
Lemma K_l' : lmeasure l' <= K.
Proof using . unfold K; rewrite !lmeasure_max; lia. Qed.
Lemma K_li : lmeasure li <= K.
Proof using . unfold K; rewrite !lmeasure_max; lia. Qed.

(** The index type's, the shapes' and the positions' relations, in every
    world. *)
Definition mIdx Δ d d' : DomRel G Δ :=
  fun ρ => LRrel K (kw_G ρ) (kw_Δ ρ) (kty ρ X[d]) (kty ρ X'[d']) li.
Definition mSh Δ d d' : MShRel G Δ :=
  fun ρ x x' => LRrel K (kw_G ρ) (kw_Δ ρ) (ktyl ρ A[llift d])[lsingle x] (ktyl ρ A'[llift d'])[lsingle x'] l.
Definition mPos Δ d d' : MPosRel G Δ :=
  fun ρ x x' a a' => LRrel K (kw_G ρ) (kw_Δ ρ) (ktyll ρ B[llift (llift d)])[lsingle2 x a]
    (ktyll ρ B'[llift (llift d')])[lsingle2 x' a'] l'.

Section At.
Context {Δ : ctx} {d d' : lsub} (Hd : SubRel G Γ Δ d d') (ρ : kwk G Δ).

Let Hdρ := SubRel_kw _ _ _ ρ _ _ Hd.
Let Nd := proj1 (SubRel_nf _ _ _ _ _ Hd).
Let Nd' := proj2 (SubRel_nf _ _ _ _ _ Hd).

Lemma VA_kw : VTy (kw_G ρ) (Γ⟦kw_γ ρ⟧ ,, X⟦kw_γ ρ⟧ @ li) A⟦kw_γ ρ⟧ A'⟦kw_γ ρ⟧ l.
Proof using VA. pose proof (VA _ _ (kw_gok ρ)) as Y. now rewrite gwa_cext in Y. Qed.
Lemma VB_kw : VTy (kw_G ρ) (Γ⟦kw_γ ρ⟧ ,, X⟦kw_γ ρ⟧ @ li ,, A⟦kw_γ ρ⟧ @ l) B⟦kw_γ ρ⟧ B'⟦kw_γ ρ⟧ l'.
Proof using VB. pose proof (VB _ _ (kw_gok ρ)) as Y. now rewrite !gwa_cext in Y. Qed.
Lemma VC_kw : VTm (kw_G ρ) (Γ⟦kw_γ ρ⟧ ,, X⟦kw_γ ρ⟧ @ li ,, A⟦kw_γ ρ⟧ @ l ,, B⟦kw_γ ρ⟧ @ l')
  C⟦kw_γ ρ⟧ C'⟦kw_γ ρ⟧ X⟦kw_γ ρ⟧⟨↑⟩⟨↑⟩⟨↑⟩ li.
Proof using VC. pose proof (VC _ _ (kw_gok ρ)) as Y. now rewrite !gwa_cext, !gwa_ren_ty in Y. Qed.

Lemma mIdx_iff x x' :
  mIdx Δ d d' ρ x x' <-> LRtm li (kw_G ρ) (kw_Δ ρ) (kty ρ X[d]) (kty ρ X[d']) x x'.
Proof using EL VL VN VX Hd.
  exact (LRrel_iff K_li (VTyG_kw ρ VX Hd) (VTyG_kw ρ (VTyG_refl_l VX) Hd)).
Qed.

Lemma mIdx_sub x x' : mIdx Δ d d' ρ x x' ->
  SubRel (kw_G ρ) (Γ⟦kw_γ ρ⟧ ,, X⟦kw_γ ρ⟧ @ li) (kw_Δ ρ) (lcons (kwsub ρ d) x) (lcons (kwsub ρ d') x').
Proof using EL VL VN VX Hd.
  intros hx. apply SubRel_cons; [exact Hdρ|]. apply mIdx_iff in hx. now rewrite !kty_subst in hx.
Qed.

Lemma mSh_iff x x' a a' : mIdx Δ d d' ρ x x' ->
  mSh Δ d d' ρ x x' a a' <->
  LRtm l (kw_G ρ) (kw_Δ ρ) (ktyl ρ A[llift d])[lsingle x] (ktyl ρ A[llift d'])[lsingle x'] a a'.
Proof using EL VL VN VX VA Hd.
  intros hx. unfold mSh. rewrite !ktyl_subst_single.
  exact (LRrel_iff K_l (VA_kw _ _ _ (mIdx_sub x x' hx)) (VTy_refl_l VA_kw _ _ _ (mIdx_sub x x' hx))).
Qed.

Lemma mSh_sub x x' a a' : mIdx Δ d d' ρ x x' -> mSh Δ d d' ρ x x' a a' ->
  SubRel (kw_G ρ) (Γ⟦kw_γ ρ⟧ ,, X⟦kw_γ ρ⟧ @ li ,, A⟦kw_γ ρ⟧ @ l) (kw_Δ ρ)
    (lcons (lcons (kwsub ρ d) x) a) (lcons (lcons (kwsub ρ d') x') a').
Proof using EL VL VN VX VA Hd.
  intros hx ha. apply SubRel_cons; [exact (mIdx_sub x x' hx)|].
  apply (mSh_iff x x' a a' hx) in ha. now rewrite !ktyl_subst_single in ha.
Qed.

Lemma mPos_iff x x' a a' p p' : mIdx Δ d d' ρ x x' -> mSh Δ d d' ρ x x' a a' ->
  mPos Δ d d' ρ x x' a a' p p' <->
  LRtm l' (kw_G ρ) (kw_Δ ρ) (ktyll ρ B[llift (llift d)])[lsingle2 x a]
    (ktyll ρ B[llift (llift d')])[lsingle2 x' a'] p p'.
Proof using EL VL VN VX VA VB Hd.
  intros hx ha. unfold mPos. rewrite !(ktyll_subst_single2 ρ d Nd), !(ktyll_subst_single2 ρ d' Nd').
  exact (LRrel_iff K_l' (VB_kw _ _ _ (mSh_sub x x' a a' hx ha)) (VTy_refl_l VB_kw _ _ _ (mSh_sub x x' a a' hx ha))).
Qed.

Lemma mPos_sub x x' a a' p p' : mIdx Δ d d' ρ x x' -> mSh Δ d d' ρ x x' a a' -> mPos Δ d d' ρ x x' a a' p p' ->
  SubRel (kw_G ρ) (Γ⟦kw_γ ρ⟧ ,, X⟦kw_γ ρ⟧ @ li ,, A⟦kw_γ ρ⟧ @ l ,, B⟦kw_γ ρ⟧ @ l') (kw_Δ ρ)
    (lcons (lcons (lcons (kwsub ρ d) x) a) p) (lcons (lcons (lcons (kwsub ρ d') x') a') p').
Proof using EL VL VN VX VA VB Hd.
  intros hx ha hp. apply SubRel_cons; [exact (mSh_sub x x' a a' hx ha)|].
  apply (mPos_iff x x' a a' p p' hx ha) in hp.
  now rewrite (ktyll_subst_single2 ρ d Nd), (ktyll_subst_single2 ρ d' Nd') in hp.
Qed.

(** Canonical at the stage of [M]'s level. *)
Lemma mIdx_canon : LR K (LRbelow K) (kw_G ρ) (kw_Δ ρ) (kty ρ X[d]) (kty ρ X'[d']) li (mIdx Δ d d' ρ).
Proof using EL VL VN VX Hd.
  destruct (VTyG_kw ρ VX Hd) as [R HR]. exact (LR_canon _ _ _ _ _ _ _ (LogRel_up K_li HR)).
Qed.

Lemma mSh_canon x x' : mIdx Δ d d' ρ x x' ->
  LR K (LRbelow K) (kw_G ρ) (kw_Δ ρ) (ktyl ρ A[llift d])[lsingle x] (ktyl ρ A'[llift d'])[lsingle x'] l
    (mSh Δ d d' ρ x x').
Proof using EL VL VN VX VA Hd.
  intros hx. destruct (VA_kw _ _ _ (mIdx_sub x x' hx)) as [R HR].
  rewrite <- !ktyl_subst_single in HR. exact (LR_canon _ _ _ _ _ _ _ (LogRel_up K_l HR)).
Qed.

Lemma mPos_canon x x' a a' : mIdx Δ d d' ρ x x' -> mSh Δ d d' ρ x x' a a' ->
  LR K (LRbelow K) (kw_G ρ) (kw_Δ ρ) (ktyll ρ B[llift (llift d)])[lsingle2 x a]
    (ktyll ρ B'[llift (llift d')])[lsingle2 x' a'] l' (mPos Δ d d' ρ x x' a a').
Proof using EL VL VN VX VA VB Hd.
  intros hx ha. destruct (VB_kw _ _ _ (mSh_sub x x' a a' hx ha)) as [R HR].
  rewrite <- (ktyll_subst_single2 ρ d Nd), <- (ktyll_subst_single2 ρ d' Nd') in HR.
  exact (LR_canon _ _ _ _ _ _ _ (LogRel_up K_l' HR)).
Qed.

(** The child index. *)
Lemma m_ch x x' a a' p p' : mIdx Δ d d' ρ x x' -> mSh Δ d d' ρ x x' a a' -> mPos Δ d d' ρ x x' a a' p p' ->
  mIdx Δ d d' ρ (ktmlll ρ C[llift (llift (llift d))])[lsingle3 x a p]
    (ktmlll ρ C'[llift (llift (llift d'))])[lsingle3 x' a' p'].
Proof using EL VL VN VX VA VB VC Hd.
  intros hx ha hp. pose proof (VC_kw _ _ _ (mPos_sub x x' a a' p p' hx ha hp)) as Y.
  rewrite !shift_cons_ty', <- !kty_subst in Y.
  rewrite <- (ktmlll_subst_single3 ρ d Nd), <- (ktmlll_subst_single3 ρ d' Nd') in Y.
  exact (proj2 (mIdx_iff _ _) Y).
Qed.

(** The signature's families at a related index (and shape), generically
    equal under their remaining binders: the substitution lifted past
    them. *)
Lemma m_lift1 x x' (hx : mIdx Δ d d' ρ x x') :
  [ kw_G ρ ; kw_Δ ρ ⊢g A⟦kw_γ ρ⟧[lcons (kwsub ρ d) x] @ l ] /\
  SubRel (kw_G ρ) (Γ⟦kw_γ ρ⟧ ,, X⟦kw_γ ρ⟧ @ li ,, A⟦kw_γ ρ⟧ @ l) (kw_Δ ρ ,, A⟦kw_γ ρ⟧[lcons (kwsub ρ d) x] @ l)
    (llift (lcons (kwsub ρ d) x)) (llift (lcons (kwsub ρ d') x')).
Proof using EL VL VN VX VA Hd Hwl.
  pose proof (mIdx_sub x x' hx) as Hs. destruct (VA_kw _ _ _ Hs) as [R HR].
  destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (HAd & _ & _).
  exact (conj HAd (SubRel_lift Hs (VTy_refl_l VA_kw) HAd (kw_lwf ρ Hwl))).
Qed.

Lemma m_gB x x' : mIdx Δ d d' ρ x x' ->
  [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ A[llift d])[lsingle x] @ l
      ⊢ (ktyll ρ B[llift (llift d)])[llift (lsingle x)] ≈ (ktyll ρ B'[llift (llift d')])[llift (lsingle x')] @ l' ].
Proof using EL VL VN VX VA VB Hd Hwl.
  intros hx. destruct (m_lift1 x x' hx) as [_ Hs].
  destruct (VB_kw _ _ _ Hs) as [R HR]. destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (_ & _ & EB).
  rewrite ktyl_subst_single, (ktyll_subst_lift_single ρ d Nd), (ktyll_subst_lift_single ρ d' Nd'). exact EB.
Qed.

Lemma m_gC x x' : mIdx Δ d d' ρ x x' ->
  [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ A[llift d])[lsingle x] @ l ,, (ktyll ρ B[llift (llift d)])[llift (lsingle x)] @ l'
      ⊢ (ktmlll ρ C[llift (llift (llift d))])[llift (llift (lsingle x))]
        ≈ (ktmlll ρ C'[llift (llift (llift d'))])[llift (llift (lsingle x'))] : (kty ρ X[d])⟨↑⟩⟨↑⟩ @ li ].
Proof using EL VL VN VX VA VB VC Hd Hwl Hwl'.
  intros hx. destruct (m_lift1 x x' hx) as [_ Hs].
  destruct (VB_kw _ _ _ Hs) as [R HR]. destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (HBd & _ & _).
  pose proof (SubRel_lift Hs (VTy_refl_l VB_kw) HBd (kw_lwf ρ Hwl')) as Hs2.
  pose proof (LRtm_geq (VC_kw _ _ _ Hs2)) as EC.
  rewrite !shift_llift_ty, shift_cons_ty', <- kty_subst in EC.
  rewrite ktyl_subst_single, (ktyll_subst_lift_single ρ d Nd), (ktmlll_subst_lift2_single ρ d Nd),
    (ktmlll_subst_lift2_single ρ d' Nd'). exact EC.
Qed.

Lemma m_gCa x x' a a' : mIdx Δ d d' ρ x x' -> mSh Δ d d' ρ x x' a a' ->
  [ kw_G ρ ; kw_Δ ρ ,, (ktyll ρ B[llift (llift d)])[lsingle2 x a] @ l'
      ⊢ (ktmlll ρ C[llift (llift (llift d))])[llift (lsingle2 x a)]
        ≈ (ktmlll ρ C'[llift (llift (llift d'))])[llift (lsingle2 x' a')] : (kty ρ X[d])⟨↑⟩ @ li ].
Proof using EL VL VN VX VA VB VC Hd Hwl'.
  intros hx ha. pose proof (mSh_sub x x' a a' hx ha) as Hs.
  destruct (VB_kw _ _ _ Hs) as [R HR]. destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (HBd & _ & _).
  pose proof (SubRel_lift Hs (VTy_refl_l VB_kw) HBd (kw_lwf ρ Hwl')) as Hs2.
  pose proof (LRtm_geq (VC_kw _ _ _ Hs2)) as EC.
  rewrite !shift_llift_ty, !shift_cons_ty', <- kty_subst in EC.
  rewrite (ktyll_subst_single2 ρ d Nd), (ktmlll_subst_lift_single2 ρ d Nd), (ktmlll_subst_lift_single2 ρ d' Nd').
  exact EC.
Qed.

End At.

(** Kripke monotonicity. *)
Lemma m_imon {Δ d d'} (Hd : SubRel G Γ Δ d d') (ρ : kwk G Δ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) x x' :
  mIdx Δ d d' ρ x x' -> mIdx Δ d d' (kw_comp ρ ρ') (ktm ρ' x) (ktm ρ' x').
Proof using EL VL VN VX.
  intros hx. apply (mIdx_iff Hd). pose proof (LRtm_kw ρ' (proj1 (mIdx_iff Hd ρ _ _) hx)) as Y.
  now rewrite <- !kty_comp in Y.
Qed.

Lemma m_shmon {Δ d d'} (Hd : SubRel G Γ Δ d d') (ρ : kwk G Δ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) x x' a a' :
  mIdx Δ d d' ρ x x' -> mSh Δ d d' ρ x x' a a' ->
  mSh Δ d d' (kw_comp ρ ρ') (ktm ρ' x) (ktm ρ' x') (ktm ρ' a) (ktm ρ' a').
Proof using EL VL VN VX VA.
  intros hx ha. apply (mSh_iff Hd _ _ _ _ _ (m_imon Hd ρ ρ' x x' hx)).
  pose proof (LRtm_kw ρ' (proj1 (mSh_iff Hd ρ x x' a a' hx) ha)) as Y.
  now rewrite !kty_lsingle, <- !ktyl_comp in Y.
Qed.

Lemma m_posmon {Δ d d'} (Hd : SubRel G Γ Δ d d') (ρ : kwk G Δ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) x x' a a' p p' :
  mIdx Δ d d' ρ x x' -> mSh Δ d d' ρ x x' a a' -> mPos Δ d d' ρ x x' a a' p p' ->
  mPos Δ d d' (kw_comp ρ ρ') (ktm ρ' x) (ktm ρ' x') (ktm ρ' a) (ktm ρ' a') (ktm ρ' p) (ktm ρ' p').
Proof using EL VL VN VX VA VB.
  intros hx ha hp.
  apply (mPos_iff Hd _ _ _ _ _ _ _ (m_imon Hd ρ ρ' x x' hx) (m_shmon Hd ρ ρ' x x' a a' hx ha)).
  pose proof (LRtm_kw ρ' (proj1 (mPos_iff Hd ρ x x' a a' p p' hx ha) hp)) as Y.
  now rewrite !kty_lsingle2, <- !ktyll_comp in Y.
Qed.

(** The former at a related index, at a related substitution. *)
Lemma LR_M_at Δ d d' mm mm' : SubRel G Γ Δ d d' -> LRtm li G Δ X[d] X[d'] mm mm' ->
  LogRel (mlvl l l' li) G Δ
    (tyM l l' li X[d] A[llift d] B[llift (llift d)] C[llift (llift (llift d))] mm)
    (tyM k k' ki X'[d'] A'[llift d'] B'[llift (llift d')] C'[llift (llift (llift d'))] mm') (mlvl l l' li)
    (MR G Δ l l' li X[d] A[llift d] B[llift (llift d)] C[llift (llift (llift d))]
       k k' ki X'[d'] A'[llift d'] B'[llift (llift d')] C'[llift (llift (llift d'))]
       (mSh Δ d d') (mPos Δ d d') mm mm').
Proof using EL VL VN VX VA VB VC Hwl Hwl' Hwli Hk Hk' Hki.
  intros Hd Xm.
  destruct (VTyG_loc VX _ _ _ Hd) as [RX HRX]. destruct (escape_ty _ _ _ _ _ _ _ _ HRX) as (HXd & HX'd & EX).
  pose proof (SubRel_lift Hd (VTy_refl_l (VTyG_loc VX)) HXd Hwli) as Hl1.
  destruct (VTyG_loc VA _ _ _ Hl1) as [RA HRA]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HAd & HA'd & EA).
  pose proof (SubRel_lift Hl1 (VTy_refl_l (VTyG_loc VA)) HAd Hwl) as Hl2.
  destruct (VTyG_loc VB _ _ _ Hl2) as [RB HRB]. destruct (escape_ty _ _ _ _ _ _ _ _ HRB) as (HBd & HB'd & EB).
  pose proof (SubRel_lift Hl2 (VTy_refl_l (VTyG_loc VB)) HBd Hwl') as Hl3.
  pose proof (VTmG_loc VC _ _ _ Hl3) as XC. rewrite !shift_llift_ty in XC.
  destruct (LRtm_escape XC) as [HCd HC'd]. pose proof (LRtm_geq XC) as EC.
  destruct (LRtm_escape Xm) as [Hmd Hm'd]. pose proof (LRtm_geq Xm) as Em.
  assert (HE : MEq (G := G) (i := ge_layer) Δ l l' li k k' ki X[d] X'[d'] A[llift d] A'[llift d']
                 B[llift (llift d)] B'[llift (llift d')] C[llift (llift (llift d))] C'[llift (llift (llift d'))]).
  { apply MEq_intro; auto using geq_ty_sound, geq_tm_sound, lequiv_sym. }
  assert (HE0 : MEq (G := G) (i := ge_layer) Δ l l' li l l' li X[d] X'[d'] A[llift d] A'[llift d']
                 B[llift (llift d)] B'[llift (llift d')] C[llift (llift (llift d))] C'[llift (llift (llift d'))]).
  { apply MEq_intro; auto using geq_ty_sound, geq_tm_sound, lequiv_refl. }
  destruct (MEq_sig_r ge_typeof ge_notV HE0) as (_ & _ & _ & HX'r & HA'r & HB'r & HC'r).
  pose proof (proj1 (proj2 (proj2 (proj2 HE)))) as HS.
  eapply LRm with (l1 := l) (l2 := l') (li := li) (idxR := mIdx Δ d d') (shR := mSh Δ d d') (posR := mPos Δ d d').
  - apply lequiv_refl, lwf_max; [apply lwf_max|]; assumption.
  - exact Hk.
  - exact Hk'.
  - exact Hki.
  - exact Hwl.
  - exact Hwl'.
  - exact Hwli.
  - apply tyred_refl, (M_ty_wf ge_typeof ge_notV HS Hmd).
  - apply tyred_refl, (pre_M_r ge_typeof ge_notV HE Hm'd).
  - exact HXd.
  - exact HX'r.
  - exact HAd.
  - exact HA'r.
  - exact HBd.
  - exact HB'r.
  - exact HCd.
  - exact HC'r.
  - exact Hmd.
  - eapply wf_conv; [exact Hm'd | rewrite ge_typeof; apply eqty_sym, geq_ty_sound, EX].
  - exact EX.
  - exact EA.
  - exact EB.
  - exact EC.
  - exact Em.
  - exact (mIdx_canon Hd).
  - intros ρ x x' hx. exact (mSh_canon Hd ρ x x' hx).
  - intros ρ x x' a a' hx ha. exact (mPos_canon Hd ρ x x' a a' hx ha).
  - intros ρ x x' a a' p p' hx ha hp. exact (m_ch Hd ρ x x' a a' p p' hx ha hp).
  - intros ρ x x' hx. exact (m_gB Hd ρ x x' hx).
  - intros ρ x x' hx. exact (m_gC Hd ρ x x' hx).
  - intros ρ x x' a a' hx ha. exact (m_gCa Hd ρ x x' a a' hx ha).
  - intros ρ ρ' x x' hx. exact (m_imon Hd ρ ρ' x x' hx).
  - intros ρ ρ' x x' a a' hx ha. exact (m_shmon Hd ρ ρ' x x' a a' hx ha).
  - intros ρ ρ' x x' a a' p p' hx ha hp. exact (m_posmon Hd ρ ρ' x x' a a' p p' hx ha hp).
  - intros ρ. exact (proj2 (mIdx_iff Hd ρ _ _) (LRtm_kw ρ Xm)).
  - apply releq_refl.
Qed.

Lemma V_M_at {m m'} (Vm : VTm G Γ m m' X li) :
  VTy G Γ (tyM l l' li X A B C m) (tyM k k' ki X' A' B' C' m') (mlvl l l' li).
Proof using EL VL VN VX VA VB VC Hwl Hwl' Hwli Hk Hk' Hki.
  intros Δ d d' Hd. eexists. rewrite !subst_tyM. exact (LR_M_at Δ d d' _ _ Hd (Vm _ _ _ Hd)).
Qed.

End MTy.

Lemma V_M {G Γ l l' li k k' ki X X' A A' B B' C C' m m'} :
  lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) li ->
  lequiv (gL G) k l -> lequiv (gL G) k' l' -> lequiv (gL G) ki li ->
  VTyG G Γ X X' li -> VTyG G (Γ ,, X @ li) A A' l -> VTyG G (Γ ,, X @ li ,, A @ l) B B' l' ->
  VTmG G (Γ ,, X @ li ,, A @ l ,, B @ l') C C' X⟨↑⟩⟨↑⟩⟨↑⟩ li -> VTm G Γ m m' X li ->
  VTy G Γ (tyM l l' li X A B C m) (tyM k k' ki X' A' B' C' m') (mlvl l l' li).
Proof using EL VL VN. intros; eapply V_M_at; eassumption. Qed.

End MV.
