(** * Validity of β and η *)
From DeLaM.Validity Require Export Lam.

Section PiComp.
Context `{E : GenericEq} `{EL : !GenericEqLaws}.

(** ** Syntax *)

Lemma lift_single_tm (b : tm) d a : LK nftm d -> b[llift d][lsingle a] = b[lcons d a].
Proof.
  intros Hd. apply subst_subst. intros [|n]; rewrite llk_llift; cbn; [reflexivity|].
  change (ren_tm ?x ?r) with x⟨r⟩. symmetry; apply shift_single, Hd.
Qed.

Lemma liftshift_single_ty (B : ty) a : nfty B -> B⟨rlift ↑⟩[llift (lsingle a)] = B.
Proof.
  intros HB. rewrite (ren_subst_ty _ _ _ (lshift 0)).
  - apply subst_id_ty; auto. intros; cbn; f_equal; lia.
  - intros [|n]; rewrite llk_llift; rlk_simpl; cbn; auto. f_equal; lia.
Qed.

(** The η-body applied: [(t⟨↑⟩ x)[a/x] = t a]. *)
Lemma eta_body_single (t : tm) l l' (A B : ty) a : nftm t -> nfty A -> nfty B ->
  (app t⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0))[lsingle a] = app t l l' A B a.
Proof.
  intros Ht HA HB. push_subst. rewrite shift_single, shift_single_ty, liftshift_single_ty by auto.
  reflexivity.
Qed.

Lemma eta_body_subst_ren (t : tm) l l' (A B : ty) d (ρ : rsub) :
  (app t⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0))[llift d]⟨rlift ρ⟩ =
  app t[d]⟨ρ⟩⟨↑⟩ l l' A[d]⟨ρ⟩⟨↑⟩ B[llift d]⟨rlift ρ⟩⟨rlift ↑⟩ (var 0).
Proof.
  push_subst. rewrite llk_llift0, shift_llift, shift_llift_ty, liftshift_llift_ty.
  push_ren. rewrite shift_lift, shift_lift_ty, liftshift_lift_ty. reflexivity.
Qed.

(** ** Extensionality from the Kripke clause *)

Section Funext.
Context {G : gctx} {Γ : ctx} {l l' : lvl} {A B : ty}
  (Hwl : lwf (gL G) l) (Hwl' : lwf (gL G) l')
  (HB : [ G ; Γ ,, A @ l ⊢g B @ l' ])
  (VA : VTy G Γ A A l) (VB : VTy G (Γ ,, A @ l) B B l').

Definition PiK Δ d d' w w' :=
  forall Δ' (ρ : wk) (Hρ : ρ : Δ' ≤ Δ) (HΔ' : [ G ; Δ' ⊢g ]) a a'
    (ha : @piDom E G l l' A A Δ d d' Δ' ρ Hρ HΔ' a a') la lb la' lb' A1 B1 A1' B1',
    lequiv (gL G) la l -> lequiv (gL G) lb l' ->
    lequiv (gL G) la' l -> lequiv (gL G) lb' l' ->
    [ G ; Δ' ⊢ A[d]⟨ρ⟩ ≈ A1 @ l ] -> [ G ; Δ' ,, A[d]⟨ρ⟩ @ l ⊢ B[llift d]⟨rlift ρ⟩ ≈ B1 @ l' ] ->
    [ G ; Δ' ⊢ A[d']⟨ρ⟩ ≈ A1' @ l ] -> [ G ; Δ' ,, A[d']⟨ρ⟩ @ l ⊢ B[llift d']⟨rlift ρ⟩ ≈ B1' @ l' ] ->
    @piCod E G l l' A A B B Δ d d' Δ' ρ Hρ HΔ' a a' ha
      (app w⟨ρ⟩ la lb A1 B1 a) (app w'⟨ρ⟩ la' lb' A1' B1' a').

Lemma funext_K Δ d d' w w' : SubRel G Γ Δ d d' ->
  [ G ; Δ ⊢g w : tyPi l l' A[d] B[llift d] @ lmax l l' ] ->
  [ G ; Δ ⊢g w' : tyPi l l' A[d] B[llift d] @ lmax l l' ] ->
  PiK Δ d d' w w' -> [ G ; Δ ⊢ w ≈ w' : tyPi l l' A[d] B[llift d] @ lmax l l' ].
Proof.
  intros Hd Hw Hw' K. pose proof (SubRel_ctx Hd) as HΔ.
  destruct (VA _ _ _ Hd) as [RA0 HRA0]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA0) as (HAd & HAd' & HAdd').
  pose proof (SubRel_wf_l _ _ _ _ _ Hd) as Hwd.
  assert (HΔA : [ G ; Δ ,, A[d] @ l ⊢g ]) by now apply ext_wf_g.
  assert (Hld : lsub_wf G ge_layer (Δ ,, A[d] @ l) (llift d) (Γ ,, A @ l))
    by now apply (lsub_wf_lift _ _ ge_typeof).
  pose proof (wf_ty_subst ge_typeof HB Hld) as HBd.
  assert (Hlift : SubRel G (Γ ,, A @ l) (Δ ,, A[d] @ l) (llift d) (llift d'))
    by (apply SubRel_lift; [exact Hd | exact VA | exact HAd | exact Hwl]).
  assert (Hliftd : SubRel G (Γ ,, A @ l) (Δ ,, A[d] @ l) (llift d) (llift d))
    by (apply SubRel_lift; [exact (SubRel_refl_l Hd) | exact VA | exact HAd | exact Hwl]).
  destruct (VB _ _ _ Hlift) as [RB HRB]. destruct (escape_ty _ _ _ _ _ _ _ _ HRB) as (_ & _ & HBdd').
  destruct (VB _ _ _ Hliftd) as [RB0 HRB0]. destruct (escape_ty _ _ _ _ _ _ _ _ HRB0) as (_ & _ & HBdd).
  assert (Hw1 : wk1 : (Δ ,, A[d] @ l) ≤ Δ) by (constructor; constructor).
  assert (Hr1 : wkr ↑ (Δ ,, A[d] @ l) Δ) by exact (wkr_shift1 _ _ _).
  assert (ha0 : LRrel (lmeasure (lmax l l')) G (Δ ,, A[d] @ l) A[d]⟨wk1⟩ A[d']⟨wk1⟩ l (var 0) (var 0)).
  { apply (LRtm_stage (l := l)); [rewrite lmeasure_max; lia|].
    change (wk_ren wk1) with ↑. apply var0_LRtm; [|exact HΔA].
    pose proof (VA _ _ _ (SubRel_wk _ _ _ _ _ _ _ Hw1 HΔA Hd)) as HV.
    now rewrite <- !subst_ren_lren_ty in HV. }
  assert (RAd : [ G ; Δ ⊢ A[d] ≈ A[d] @ l ])
    by (eapply geq_ty_trans; [exact HAdd' | apply geq_ty_sym, HAdd']).
  assert (HΔAA : [ G ; Δ ,, A[d] @ l ,, A[d]⟨↑⟩ @ l ⊢g ])
    by (apply ext_wf_g; [exact (wf_ty_wkr Hr1 HΔA HAd) | exact Hwl]).
  assert (HΔAA' : [ G ; Δ ,, A[d] @ l ,, A[d']⟨↑⟩ @ l ⊢g ])
    by (apply ext_wf_g; [exact (wf_ty_wkr Hr1 HΔA HAd') | exact Hwl]).
  apply geq_tm_funext; [exact Hwl | exact Hwl' | exact HAd | exact HBd | exact Hw | exact Hw' |].
  unshelve epose proof (K _ wk1 Hw1 HΔA (var 0) (var 0) ha0 l l' l l'
                A[d]⟨↑⟩ B[llift d]⟨rlift ↑⟩ A[d]⟨↑⟩ B[llift d]⟨rlift ↑⟩
                (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwl') (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwl')
                (geq_ty_wk Hr1 HΔA RAd)
                (geq_ty_wk (wkr_up _ _ _ _ _ Hr1) HΔAA HBdd)
                (geq_ty_wk Hr1 HΔA (geq_ty_sym HAdd')) _) as K1.
  - eapply geq_ty_ctxconv; [| apply lequiv_refl, Hwl | exact HΔAA' |].
    + apply geq_ty_sound. exact (geq_ty_wk Hr1 HΔA HAdd').
    + apply geq_ty_sym. exact (geq_ty_wk (wkr_up _ _ _ _ _ Hr1) HΔAA HBdd').
  - unfold piCod in K1. change (wk_ren wk1) with ↑ in K1.
    destruct K1 as (R1 & HR1 & HK1).
    destruct (escape_tm _ _ _ _ _ _ _ _ HR1 _ _ HK1) as (_ & _ & Hg).
    now rewrite liftshift_single_var_ty in Hg by exact (wf_ty_nf HBd).
Qed.

End Funext.

(** ** β *)

Section Beta.
Context {G : gctx} {Γ : ctx} {l l' : lvl} {A B : ty} {t s : tm}
  (Hwl : lwf (gL G) l) (Hwl' : lwf (gL G) l')
  (HB : [ G ; Γ ,, A @ l ⊢g B @ l' ]) (Ht : [ G ; Γ ,, A @ l ⊢g t : B @ l' ])
  (VA : VTy G Γ A A l) (Vt : VTm G (Γ ,, A @ l) t t B l') (Vs : VTm G Γ s s A l).

Lemma V_beta : VTm G Γ (app (lam l l' A t) l l' A B s) t[lsingle s] B[lsingle s] l'.
Proof.
  intros Δ d d' Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  pose proof (Vs _ _ _ Hd) as Hs. destruct (LRtm_escape Hs) as [Hsd _].
  pose proof (Vt _ _ _ (SubRel_cons Hd Hs)) as X.
  rewrite <- (lift_single_ty _ d), <- (lift_single_ty _ d'), <- (lift_single_tm _ d),
          <- (lift_single_tm _ d') in X by assumption.
  push_subst. rewrite !single_subst_ty, !single_subst by assumption.
  destruct X as (R & HR & HX). exists R; split; [exact HR|].
  destruct (VA _ _ _ Hd) as [RA HRA]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HAd & _ & _).
  assert (Hld : lsub_wf G ge_layer (Δ ,, A[d] @ l) (llift d) (Γ ,, A @ l))
    by (apply (lsub_wf_lift _ _ ge_typeof); auto; exact (SubRel_wf_l _ _ _ _ _ Hd)).
  pose proof (wf_ty_subst ge_typeof HB Hld) as HBd.
  pose proof (wf_tm_subst ge_typeof Ht Hld) as Htd.
  destruct (escape_tm _ _ _ _ _ _ _ _ HR _ _ HX) as (_ & Ht2 & _).
  destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (_ & _ & HBB).
  eapply LR_red_tm; [exact HR | exact HX | |].
  - apply tmred_beta; auto using lequiv_refl, eqty_refl.
  - apply tmred_refl. eapply wf_conv; [exact Ht2 | rewrite ge_typeof].
    apply eqty_sym, geq_ty_sound, HBB.
Qed.

End Beta.

(** ** η *)

Section Eta.
Context {G : gctx} {Γ : ctx} {l l' : lvl} {A B : ty} {t : tm}
  (Hwl : lwf (gL G) l) (Hwl' : lwf (gL G) l')
  (HA : [ G ; Γ ⊢g A @ l ]) (HB : [ G ; Γ ,, A @ l ⊢g B @ l' ])
  (Ht : [ G ; Γ ⊢g t : tyPi l l' A B @ lmax l l' ])
  (VA : VTy G Γ A A l) (VB : VTy G (Γ ,, A @ l) B B l')
  (Vt : VTm G Γ t t (tyPi l l' A B) (lmax l l')).

Lemma V_eta : VTm G Γ (lam l l' A (app t⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0))) t
                (tyPi l l' A B) (lmax l l').
Proof.
  intros Δ d d' Hd. pose proof (SubRel_ctx Hd) as HΔ.
  pose proof (SubRel_wf_l _ _ _ _ _ Hd) as Hsd.
  pose proof (LR_pi_here Hwl Hwl' (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwl') HB HB VA VB
                _ _ _ Hd) as HP.
  eapply LRtm_of; [exact HP|].
  pose proof (LRtm_inv HP (Vt _ _ _ Hd)) as Hti.
  destruct Hti as (wd & w' & Hwd & Hw' & Hnfd & Hnf' & _ & _ & Kt).
  (* typing of the substituted η-expansion *)
  pose proof (wf_tm_subst ge_typeof (pre_eta_l ge_typeof ge_notV Hwl Hwl' HA HB Ht) Hsd) as HL.
  rewrite subst_lam in HL |- *. rewrite subst_tyPi in HL.
  destruct (VA _ _ _ Hd) as [RA HRA]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HAd & _ & _).
  assert (Hld : lsub_wf G ge_layer (Δ ,, A[d] @ l) (llift d) (Γ ,, A @ l))
    by now apply (lsub_wf_lift _ _ ge_typeof).
  pose proof (wf_ty_subst ge_typeof HB Hld) as HBd.
  pose proof (wf_tm_subst ge_typeof Ht Hsd) as Htd. rewrite subst_tyPi in Htd.
  destruct (escape_ty _ _ _ _ _ _ _ _ HP) as (_ & _ & HPi). rewrite !subst_tyPi in HPi.
  pose proof (geq_ty_sound HPi) as HPiEq.
  assert (Hw'Π : [ G ; Δ ⊢g w' : tyPi l l' A[d] B[llift d] @ lmax l l' ]).
  { eapply wf_conv; [exact (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hw')) | rewrite ge_typeof].
    exact HPiEq. }
  set (L := lam l l' A[d] (app t⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0))[llift d]).
  assert (K : @PiK G l l' A B Δ d d' L w').
  { intros Δ' ρ Hρ HΔ' a a' ha la lb la' lb' A1 B1 A1' B1' Hla Hlb Hla' Hlb' HA1 HB1 HA1' HB1'.
    pose proof (wk_wf_wkr _ _ _ Hρ) as Hr.
    assert (HAdρ : [ G ; Δ' ⊢g A[d]⟨ρ⟩ @ l ]) by exact (wf_ty_wk Hρ HΔ' HAd).
    assert (HΔ'A : [ G ; Δ' ,, A[d]⟨ρ⟩ @ l ⊢g ]) by now apply ext_wf_g.
    assert (RAρ : [ G ; Δ' ⊢ A[d]⟨ρ⟩ ≈ A[d]⟨ρ⟩ @ l ]).
    { destruct (VA _ _ _ (SubRel_wk _ _ _ _ _ _ _ Hρ HΔ' (SubRel_refl_l Hd))) as [R0 HR0].
      rewrite <- !subst_ren_lren_ty in HR0. apply (escape_ty _ _ _ _ _ _ _ _ HR0). }
    assert (RBρ : [ G ; Δ' ,, A[d]⟨ρ⟩ @ l ⊢ B[llift d]⟨rlift ρ⟩ ≈ B[llift d]⟨rlift ρ⟩ @ l' ]).
    { assert (Hliftd : SubRel G (Γ ,, A @ l) (Δ ,, A[d] @ l) (llift d) (llift d))
        by (apply SubRel_lift; [exact (SubRel_refl_l Hd) | exact VA | exact HAd | exact Hwl]).
      destruct (VB _ _ _ Hliftd) as [RB0 HRB0].
      apply (geq_ty_wk (wkr_lift Hρ) HΔ'A (proj2 (proj2 (escape_ty _ _ _ _ _ _ _ _ HRB0)))). }
    pose proof (Kt Δ' ρ Hρ HΔ' a a' ha l l' la' lb' A[d]⟨ρ⟩ B[llift d]⟨rlift ρ⟩ A1' B1'
                  (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwl') Hla' Hlb' RAρ RBρ HA1' HB1') as X.
    unfold piCod in X |- *. destruct X as (R & HR & HX). exists R; split; [exact HR|].
    unfold piDom in ha.
    assert (Ha0 : LRtm l G Δ' A[d]⟨ρ⟩ A[d']⟨ρ⟩ a a')
      by (apply (LRtm_stage (n := lmeasure (lmax l l'))); [rewrite lmeasure_max; lia | exact ha]).
    destruct (LRtm_escape Ha0) as [Haρ _].
    destruct (escape_tm _ _ _ _ _ _ _ _ HR _ _ HX) as (_ & Hx2 & _).
    destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (_ & _ & HBB).
    eapply LR_red_tm; [exact HR | exact HX | |].
    - (* β, then the head reduction of [t[d]] *)
      eapply tmred_trans.
      + subst L. push_ren. apply tmred_beta; auto.
        * exact (wf_ty_wkr (wkr_lift Hρ) HΔ'A HBd).
        * eapply (wf_tm_wkr (wkr_lift Hρ) HΔ'A).
          exact (wf_tm_subst ge_typeof (pre_eta_body ge_typeof ge_notV Hwl Hwl' HA HB Ht) Hld).
        * now apply geq_ty_sound.
        * now apply geq_ty_sound.
      + rewrite eta_body_subst_ren, eta_body_single by auto using ren_nf, ren_nf_ty.
        apply tmred_app_cong; auto.
        * exact (wf_ty_wkr (wkr_lift Hρ) HΔ'A HBd).
        * exact (tmred_wk' Hρ HΔ' Hwd).
    - apply tmred_refl. eapply wf_conv; [exact Hx2 | rewrite ge_typeof].
      apply eqty_sym, geq_ty_sound, HBB. }
  exists L, w'.
  pose proof (funext_K Hwl Hwl' HB VA VB _ _ _ _ _ Hd HL Hw'Π K) as GEQ.
  refine (conj (tmred_refl _ _ _ HL) (conj Hw' (conj (whnf_lam _ _ _ _) (conj Hnf'
            (conj GEQ (conj _ K)))))).
  eapply geq_tm_conv; [exact GEQ | exact HPiEq].
Qed.

End Eta.

End PiComp.
