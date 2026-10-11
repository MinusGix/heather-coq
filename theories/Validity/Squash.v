(** * Validity of propositional truncation (M16_DESIGN.md, M16a)

    Formation of [∥·∥], [squash], [ind_∥∥], its β rule and proof
    irrelevance. The term relation at [∥A∥] is [SqRel]: each side reduces,
    on its own, to a [squash] of a payload related to itself, or to a
    neutral related to itself, and the two sides are never compared. So
    every lemma here works one side at a time ([SqG], the unary predicate
    at the carrier's canonical relation), and irrelevance is immediate.
    [ind_∥∥] steps to its step at a [squash], whose motive instance is
    moved to the scrutinee's (the two are related, being good alone); at a
    neutral, [ind_∥∥] is neutral. *)
From DeLaM.Validity Require Export WfElim.

(** ** Syntax: the step's type *)

Lemma sqb_llift (M : ty) l A d : LK nftm d ->
  (M⟨rlift ↑⟩[lsingle (tmSq l A⟨↑⟩ (var 0))])[llift d]
  = M[llift d]⟨rlift ↑⟩[lsingle (tmSq l A[d]⟨↑⟩ (var 0))].
Proof.
  intros Hd. rewrite (single_subst_ty _ (lk_llift _ Hd)), liftshift_llift_ty, subst_sq, !shift_llift_ty,
    subst_var, llk_llift. reflexivity.
Qed.

Lemma sqb_cons (M : ty) l A d a : LK nftm d -> nfty A[d] ->
  (M⟨rlift ↑⟩[lsingle (tmSq l A⟨↑⟩ (var 0))])[lcons d a] = M[lcons d (tmSq l A[d] a)].
Proof.
  intros Hd NA. rewrite <- (lift_single_ty _ _ a Hd), (sqb_llift _ _ _ _ Hd).
  rewrite sq_single by assumption. apply lift_single_ty, Hd.
Qed.

Section Squash.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

(** ** One side at a time *)

(** A term good at [∥X∥^l], at the canonical relation of [X]. *)
Definition SqG (G : gctx) (Δ : ctx) (l : lvl) (X : ty) (t : tm) : Prop :=
  SqU G Δ l X (LRtm l G Δ X X) t.

(** A relation of a pair with left side [X], on its diagonal, is the
    canonical one. *)
Lemma LR_diag {l G Δ X X' R} : LogRel l G Δ X X' l R -> forall a, R a a <-> LRtm l G Δ X X a a.
Proof.
  intros H a; split.
  - intros Ha. exists R; split; [exact (LR_refl_l _ _ _ _ _ _ _ H) | exact Ha].
  - intros (R' & H' & Ha). exact (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ H H' a a) Ha).
Qed.

Lemma SqU_mono {G Δ l X RA RA' t} : (forall a, RA a a -> RA' a a) ->
  SqU G Δ l X RA t -> SqU G Δ l X RA' t.
Proof.
  intros E0 (w & Hw & Hn). exists w; split; [exact Hw|].
  destruct Hn as [k C a Hk HC Ha | ν Hν]; [apply sqnf_sq; auto | apply sqnf_ne; exact Hν].
Qed.

(** Related terms at a squash are each good. *)
Lemma LRtm_sq_inv {l G Δ X Y t t'} : LRtm l G Δ (tySq l X) Y t t' -> SqG G Δ l X t /\ SqG G Δ l X t'.
Proof.
  intros (R & H & Ht).
  destruct (escape_ty _ _ _ _ _ _ _ _ H) as (HT & _ & _).
  destruct (LR_inv_sq H (tyred_refl _ _ HT)) as (m2 & C' & RC & _ & _ & _ & _ & _ & _ & _ & HRC & _ & _ & HR).
  apply HR in Ht. destruct Ht as [H1 H2]. pose proof (LR_diag HRC) as D.
  split; (eapply SqU_mono; [intros a; exact (proj1 (D a)) | assumption]).
Qed.

(** Two good terms at a squash are related. *)
Lemma LRtm_sq_of {l G Δ X Y t t'} : LRty l G Δ (tySq l X) Y -> SqG G Δ l X t -> SqG G Δ l X t' ->
  LRtm l G Δ (tySq l X) Y t t'.
Proof.
  intros [R H] Ht Ht'. exists R; split; [exact H|].
  destruct (escape_ty _ _ _ _ _ _ _ _ H) as (HT & _ & _).
  destruct (LR_inv_sq H (tyred_refl _ _ HT)) as (m2 & C' & RC & _ & _ & _ & _ & _ & _ & _ & HRC & _ & _ & HR).
  apply HR. pose proof (LR_diag HRC) as D.
  split; (eapply SqU_mono; [intros a; exact (proj2 (D a)) | assumption]).
Qed.

(** Along related carriers. *)
Lemma SqG_conv {l G Δ X Z t} : lwf (gL G) l -> LRty l G Δ X Z -> SqG G Δ l X t -> SqG G Δ l Z t.
Proof.
  intros Hw [R H] Ht. destruct (escape_ty _ _ _ _ _ _ _ _ H) as (HX & _ & EX).
  eapply (SqU_conv (lequiv_refl _ _ Hw) HX EX); [|exact Ht].
  intros a Ha. apply (proj1 (LR_diag (LR_sym _ _ _ _ _ _ _ H) a)). exact (proj2 (LR_diag H a) Ha).
Qed.

Lemma SqG_ne {l G Δ X ν} : [ G ; Δ ⊢ ν ~ ν : tySq l X @ l ] -> SqG G Δ l X ν.
Proof. intros H. exists ν. split; [exact (tmred_refl _ _ _ (gne_tm_typed_l H)) | apply sqnf_ne, H]. Qed.

Lemma SqG_red {l G Δ X t u} : [ G ; Δ ⊢g t ⤳* u : tySq l X @ l ] -> SqG G Δ l X u -> SqG G Δ l X t.
Proof. intros Hr (w & Hw & Hn). exists w. split; [eapply tmred_trans; eassumption | exact Hn]. Qed.

(** ** Formation and [squash] *)

Lemma LR_sq_here {G Δ l l' A A' RA} : lwf (gL G) l -> lequiv (gL G) l l' ->
  [ G ; Δ ⊢g A @ l ] -> [ G ; Δ ⊢ A ≈ A' @ l ] -> LogRel l G Δ A A' l RA ->
  LogRel l G Δ (tySq l A) (tySq l' A') l (SqRel G Δ l A RA).
Proof.
  intros Hw Hl HA HAA HRA.
  pose proof (geq_ty_sound (geq_ty_sq Hl HA HAA)) as EV.
  destruct (LR_tm_per _ _ _ _ _ _ _ HRA) as [Sy Tr].
  eapply (LRsq _ _ _ _ _ _ _ l l' A A' RA).
  - now apply lequiv_refl.
  - now apply lequiv_sym.
  - exact Hw.
  - apply tyred_refl, (eqty_wf_l ge_typeof EV).
  - apply tyred_refl, (eqty_wf_r ge_typeof EV).
  - exact HA.
  - exact HAA.
  - exact HRA.
  - exact Sy.
  - exact Tr.
  - apply releq_refl.
Qed.

Lemma V_sq {G Γ l l' A A'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTy G Γ A A' l -> VTy G Γ (tySq l A) (tySq l' A') l.
Proof.
  intros Hw Hl VA Δ d d' Hd. rewrite !subst_tySq.
  destruct (VA _ _ _ Hd) as [RA HRA]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HA & _ & EA).
  eexists; exact (LR_sq_here Hw Hl HA EA HRA).
Qed.

Lemma V_sq_intro {G Γ l l' A A' a a'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTy G Γ A A' l -> VTm G Γ a a' A l -> VTm G Γ (tmSq l A a) (tmSq l' A' a') (tySq l A) l.
Proof.
  intros Hw Hl VA Va Δ d d' Hd. rewrite !subst_tySq, !subst_sq.
  pose proof (VTy_refl_l VA _ _ _ Hd) as XA. destruct XA as [RA HRA].
  destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HA & _ & EAA).
  destruct (VA _ _ _ Hd) as [RA' HRA']. destruct (escape_ty _ _ _ _ _ _ _ _ HRA') as (_ & _ & EA).
  pose proof (Va _ _ _ Hd) as Xa.
  assert (HS : [ G ; Δ ⊢g tmSq l A[d] a[d] ≅ tmSq l' A'[d'] a'[d'] : tySq l A[d] @ l ])
    by (apply eqtm_sq; [exact ge_compt | exact Hl | exact HA | exact (geq_ty_sound EA)
                       | exact (geq_tm_sound (LRtm_geq Xa))]).
  apply LRtm_sq_of; [eexists; exact (LR_sq_here Hw (lequiv_refl _ _ Hw) HA EAA HRA) | |].
  - exists (tmSq l A[d] a[d]). split; [exact (tmred_refl _ _ _ (eqtm_wf_l ge_typeof HS)) |].
    apply sqnf_sq; [now apply lequiv_refl | exact (geq_ty_refl_l EAA) |].
    exact (LRtm_trans Xa (LRtm_sym Xa)).
  - exists (tmSq l' A'[d'] a'[d']). split; [exact (tmred_refl _ _ _ (eqtm_wf_r ge_typeof HS)) |].
    apply sqnf_sq; [now apply lequiv_sym | exact EA |].
    eapply LRtm_irrel_r; [| exact (VTy_refl_l VA _ _ _ (SubRel_refl_l Hd))].
    eapply LRtm_conv_l; [exact (LRtm_trans (LRtm_sym Xa) Xa) | exact (ex_intro _ _ HRA)].
Qed.

(** Irrelevance: the left sides of the two validities, related. *)
Lemma V_sq_irr {G Γ l A t t1 t' t1'} : lwf (gL G) l ->
  VTm G Γ t t1 (tySq l A) l -> VTm G Γ t' t1' (tySq l A) l -> VTm G Γ t t1' (tySq l A) l.
Proof.
  intros _ Vt Vt' Δ d d' Hd. pose proof (Vt _ _ _ Hd) as X. pose proof (Vt' _ _ _ Hd) as X'.
  rewrite !subst_tySq in X, X' |- *.
  destruct (LRtm_sq_inv X) as [H1 _]. destruct (LRtm_sq_inv X') as [_ H2].
  exact (LRtm_sq_of (LRtm_ty X) H1 H2).
Qed.

(** ** [ind_∥∥] *)

Section ElimSqAt.
Context {G : gctx} {Γ : ctx} {l1 l2 : lvl} {A A' M M' : ty} {c c' : tm}
  (Hw1 : lwf (gL G) l1) (Hw2 : lwf (gL G) l2)
  (VA : VTy G Γ A A' l1) (VM : VTy G (Γ ,, tySq l1 A @ l1) M M' l2)
  (Vc : VTm G (Γ ,, A @ l1) c c' (tySq l2 M⟨rlift ↑⟩[lsingle (tmSq l1 A⟨↑⟩ (var 0))]) l2).

(** The premises of [ind_∥∥], at related substitutions. *)
Lemma sq_at {Δ d d'} : SubRel G Γ Δ d d' ->
  [ G ; Δ ⊢g A[d] @ l1 ] /\ [ G ; Δ ⊢ A[d] ≈ A'[d'] @ l1 ] /\
  [ G ; Δ ,, tySq l1 A[d] @ l1 ⊢g M[llift d] @ l2 ] /\
  [ G ; Δ ,, tySq l1 A[d] @ l1 ⊢ M[llift d] ≈ M'[llift d'] @ l2 ] /\
  [ G ; Δ ,, A[d] @ l1 ⊢ c[llift d] ≈ c'[llift d']
      : tySq l2 M[llift d]⟨rlift ↑⟩[lsingle (tmSq l1 A[d]⟨↑⟩ (var 0))] @ l2 ].
Proof.
  intros Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  destruct (VA _ _ _ Hd) as [RA HRA]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HA & _ & EA).
  pose proof (V_sq Hw1 (lequiv_refl _ _ Hw1) (VTy_refl_l VA)) as VS.
  assert (HS : [ G ; Δ ⊢g (tySq l1 A)[d] @ l1 ]).
  { destruct (VS _ _ _ Hd) as [RS HRS]. exact (proj1 (escape_ty _ _ _ _ _ _ _ _ HRS)). }
  pose proof (SubRel_lift Hd VS HS Hw1) as HdS.
  destruct (VM _ _ _ HdS) as [RM HRM]. destruct (escape_ty _ _ _ _ _ _ _ _ HRM) as (HM & _ & EM).
  pose proof (LRtm_geq (Vc _ _ _ (SubRel_lift Hd (VTy_refl_l VA) HA Hw1))) as Ec.
  rewrite subst_tySq in HM, EM.
  rewrite subst_tySq, (sqb_llift _ _ _ _ Nd) in Ec.
  repeat split; assumption.
Qed.

Lemma V_elimSq {l3 l4 t t'} : lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  VTm G Γ t t' (tySq l1 A) l1 ->
  VTm G Γ (tmElimSq l1 l2 A M c t) (tmElimSq l3 l4 A' M' c' t') (tySq l2 M[lsingle t]) l2.
Proof.
  intros H13 H24 Vt Δ d d' Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  rewrite !subst_tySq, !single_subst_ty by assumption. push_subst.
  pose proof (SubRel_refl_l Hd) as Hdd.
  destruct (sq_at Hd) as (HA & EA & HM & EM & Ec).
  pose proof (wf_ty_nf HA) as NA.
  pose proof (VTm_trans Vt (VTm_sym Vt)) as Vtt.
  pose proof (V_sq Hw1 (lequiv_refl _ _ Hw1) (VTy_refl_l VA)) as VS.
  (* both scrutinees are good *)
  pose proof (Vt _ _ _ Hd) as Xt. rewrite !subst_tySq in Xt.
  destruct (LRtm_sq_inv Xt) as [Gt Gt'].
  (* the motive at any two good scrutinees *)
  assert (Mat : forall x y, SqG G Δ l1 A[d] x -> SqG G Δ l1 A[d] y ->
            LRty l2 G Δ M[llift d][lsingle x] M[llift d][lsingle y]).
  { intros x y Hx Hy.
    assert (Xxy : LRtm l1 G Δ (tySq l1 A)[d] (tySq l1 A)[d] x y).
    { rewrite !subst_tySq. apply LRtm_sq_of; [| exact Hx | exact Hy].
      destruct (VS _ _ _ Hdd) as [R HR]. rewrite !subst_tySq in HR. now exists R. }
    pose proof (VTy_refl_l VM _ _ _ (SubRel_cons Hdd Xxy)) as Y.
    rewrite <- !lift_single_ty in Y by exact Nd. exact Y. }
  (* the two eliminators, at the left's motive *)
  assert (HCC : forall s, [ G ; Δ ⊢g s : tySq l1 A[d] @ l1 ] ->
            [ G ; Δ ⊢g tmElimSq l1 l2 A[d] M[llift d] c[llift d] s
                ≅ tmElimSq l3 l4 A'[d'] M'[llift d'] c'[llift d'] s : tySq l2 M[llift d][lsingle s] @ l2 ]).
  { intros s Hs. apply eqtm_elimSq; [exact ge_compt | exact H13 | exact H24 | exact HA
                                    | exact (geq_ty_sound EA) | exact HM | exact (geq_ty_sound EM)
                                    | exact (geq_tm_sound Ec) | now apply eqtm_refl]. }
  assert (Hne : forall ν, [ G ; Δ ⊢ ν ~ ν : tySq l1 A[d] @ l1 ] ->
            [ G ; Δ ⊢ tmElimSq l1 l2 A[d] M[llift d] c[llift d] ν
                ~ tmElimSq l3 l4 A'[d'] M'[llift d'] c'[llift d'] ν : tySq l2 M[llift d][lsingle ν] @ l2 ])
    by (intros ν Hν; exact (gne_tm_elimSq H13 H24 HA EA HM EM Ec Hν Hν)).
  (* one side: good at its scrutinee's motive instance *)
  assert (Side : forall k1 k2 A0 M0 c0 s,
            (forall s0, [ G ; Δ ⊢g s0 : tySq l1 A[d] @ l1 ] ->
               [ G ; Δ ⊢g tmElimSq k1 k2 A0 M0 c0 s0 : tySq l2 M[llift d][lsingle s0] @ l2 ]) ->
            (forall a, LRtm l1 G Δ A[d] A[d] a a ->
               SqG G Δ l2 M[llift d][lsingle (tmSq l1 A[d] a)] c0[lsingle a]) ->
            (forall ν, [ G ; Δ ⊢ ν ~ ν : tySq l1 A[d] @ l1 ] ->
               [ G ; Δ ⊢ tmElimSq k1 k2 A0 M0 c0 ν ~ tmElimSq k1 k2 A0 M0 c0 ν
                   : tySq l2 M[llift d][lsingle ν] @ l2 ]) ->
            SqG G Δ l1 A[d] s -> SqG G Δ l2 M[llift d][lsingle s] (tmElimSq k1 k2 A0 M0 c0 s)).
  { intros k1 k2 A0 M0 c0 s Hty Hc Hn Gs.
    pose proof Gs as (w & Hr & Hw).
    pose proof (Hty _ (tmred_wf _ _ _ _ _ _ _ Hr)) as He.
    assert (Gw : SqG G Δ l1 A[d] w)
      by (exists w; split; [apply tmred_refl, (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hr)) | exact Hw]).
    destruct Hw as [k C a Hk HC Ha | ν Hν].
    - (* a [squash]: β, then the step at the payload *)
      pose proof (proj1 (LRtm_escape Ha)) as Ha0.
      assert (Gsq : SqG G Δ l1 A[d] (tmSq l1 A[d] a)).
      { exists (tmSq l1 A[d] a). split; [apply tmred_refl, wf_sq; [exact ge_compt | exact Hw1 | exact HA | exact Ha0] |].
        apply sqnf_sq; [now apply lequiv_refl | exact (geq_ty_refl_l EA) | exact Ha]. }
      pose proof (SqG_conv Hw2 (LRty_sym (Mat _ _ Gs Gsq)) (Hc a Ha)) as Gc.
      eapply SqG_red; [| exact Gc].
      split; [exact He | |].
      + eapply reds_trans; [apply reds_elimSq, (tmred_red _ _ _ _ _ _ _ Hr)|].
        econstructor; [apply red_elimSq_sq | constructor].
      + apply eqtm_sq_irr; [exact ge_compt | exact Hw2 | exact He | exact (SqU_wf Gc)].
    - (* a neutral: [ind_∥∥] is neutral *)
      destruct (Mat _ _ Gw Gs) as [Rν HRν]. destruct (escape_ty _ _ _ _ _ _ _ _ HRν) as (HMν & _ & EMν).
      pose proof (gne_tm_conv (Hn ν Hν) (geq_ty_sound (geq_ty_sq (lequiv_refl _ _ Hw2) HMν EMν))) as Hνν.
      exists (tmElimSq k1 k2 A0 M0 c0 ν). split; [| apply sqnf_ne; exact Hνν].
      split; [exact He | apply reds_elimSq, (tmred_red _ _ _ _ _ _ _ Hr) |].
      apply eqtm_sq_irr; [exact ge_compt | exact Hw2 | exact He | exact (gne_tm_typed_l Hνν)]. }
  (* the result's relation, at the left's motive at both scrutinees *)
  pose proof (VTy_refl_l VM _ _ _ (SubRel_cons Hd (Vtt _ _ _ Hd))) as XT.
  rewrite <- !lift_single_ty in XT by assumption.
  destruct XT as [RM HRM]. destruct (escape_ty _ _ _ _ _ _ _ _ HRM) as (HMt & _ & EMt).
  apply LRtm_sq_of; [eexists; exact (LR_sq_here Hw2 (lequiv_refl _ _ Hw2) HMt EMt HRM) | |].
  - (* the left side *)
    apply (Side l1 l2 A[d] M[llift d] c[llift d] t[d]); [| | | exact Gt].
    + intros s0 Hs0. exact (eqtm_wf_l ge_typeof (HCC s0 Hs0)).
    + intros a Ha. pose proof (Vc _ _ _ (SubRel_cons Hdd Ha)) as Xc.
      rewrite !subst_tySq, (sqb_cons _ _ _ _ _ Nd NA) in Xc.
      rewrite <- !lift_single_tm in Xc by exact Nd. rewrite <- !lift_single_ty in Xc by exact Nd.
      exact (proj1 (LRtm_sq_inv Xc)).
    + intros ν Hν. exact (gne_tm_refl_l (Hne ν Hν)).
  - (* the right side, at its own scrutinee's instance, then moved *)
    apply (SqG_conv Hw2 (Mat _ _ Gt' Gt)).
    apply (Side l3 l4 A'[d'] M'[llift d'] c'[llift d'] t'[d']); [| | | exact Gt'].
    + intros s0 Hs0. exact (eqtm_wf_r ge_typeof (HCC s0 Hs0)).
    + intros a Ha.
      destruct (VTy_refl_l VA _ _ _ Hd) as [RA2 HRA2]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA2) as (_ & HA2 & _).
      assert (Xa : LRtm l1 G Δ A[d] A[d'] a a) by exact (LRtm_irrel_r Ha (ex_intro _ _ HRA2)).
      pose proof (Vc _ _ _ (SubRel_cons Hd Xa)) as Xc.
      rewrite !subst_tySq, (sqb_cons _ _ _ _ _ Nd NA), (sqb_cons _ _ _ _ _ Nd' (wf_ty_nf HA2)) in Xc.
      rewrite <- !lift_single_tm in Xc by assumption. rewrite <- !lift_single_ty in Xc by assumption.
      exact (proj2 (LRtm_sq_inv Xc)).
    + intros ν Hν. exact (gne_tm_refl_r (Hne ν Hν)).
Qed.

(** β, the scrutinee a [squash] with the eliminator's annotations. *)
Lemma V_elimSq_sq {a} :
  VTm G (Γ ,, A @ l1) c c (tySq l2 M⟨rlift ↑⟩[lsingle (tmSq l1 A⟨↑⟩ (var 0))]) l2 -> VTm G Γ a a A l1 ->
  VTm G Γ (tmElimSq l1 l2 A M c (tmSq l1 A a)) c[lsingle a] (tySq l2 M[lsingle (tmSq l1 A a)]) l2.
Proof.
  intros Vcc Va Δ d d' Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  destruct (sq_at Hd) as (HA & _ & HM & _ & Ec).
  destruct (VTy_refl_l VA _ _ _ Hd) as [RA2 HRA2]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA2) as (_ & HA' & _).
  pose proof (Va _ _ _ Hd) as Xa. pose proof (proj1 (LRtm_escape Xa)) as Ha.
  pose proof (Vcc _ _ _ (SubRel_cons Hd Xa)) as X.
  rewrite !subst_tySq, (sqb_cons _ _ _ _ _ Nd (wf_ty_nf HA)), (sqb_cons _ _ _ _ _ Nd' (wf_ty_nf HA')) in X.
  rewrite <- !lift_single_tm in X by assumption.
  rewrite !subst_tySq, !single_subst_ty, !single_subst by assumption. push_subst.
  rewrite !lift_single_ty by assumption.
  eapply LRtm_red_l; [exact X|].
  pose proof (eqtm_wf_l ge_typeof (geq_tm_sound Ec)) as Hc.
  pose proof (eqtm_elimSq_sq _ _ _ _ _ _ _ _ _ ge_compt Hw1 Hw2 HA HM Hc Ha) as Hb.
  rewrite lift_single_ty in Hb by assumption.
  split; [exact (eqtm_wf_l ge_typeof Hb) | | exact Hb].
  econstructor; [apply red_elimSq_sq | constructor].
Qed.

End ElimSqAt.

End Squash.
