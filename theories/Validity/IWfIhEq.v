(** * [elim_IWf]'s induction hypothesis types along equal signatures

    ELIM_CONGRUENCE.md, "What is not forced": two eliminations whose
    signatures are equal (which the scrutinee's type forces) and whose
    motives are equal have equal induction hypothesis types. The two types
    are [Π(i : Fin N). M[C, dnth(N; k. IWf(C); cs; i)]] at either
    signature: the domains are [Fin] at the arities, and the codomains are
    the motives at the child indices and at [dnth]s whose length and family
    differ. [dnth]'s index lemma ([V_dnth], M17a) already relates [dnth] at
    related lengths and families, and [elimIWf_Vdnth] instantiates it at
    the children's tuple; here it is composed with the motive's validity
    ([VG_iwfihty]), then turned into a declarative equation by the
    fundamental theorem and escape, at P and at M ([IWf_ihty_eq]), the
    layers the algorithm works at.

    So the algorithm's [actmne_elimIWf] does not compare the induction
    hypothesis types. The declarative [eqtm_elimIWf] keeps its premise:
    its metatheory (presupposition, the fundamental theorem itself) comes
    before this lemma, and at layer C there is no relation to derive it
    from. *)
From DeLaM.Validity Require Export DeclConsequences.
From DeLaM.Validity Require Import IWfElim Id.
From DeLaM.Typing Require Import IWfIH.

(** ** Syntax *)

Lemma lift1x3_cons_ty (T : ty) d a :
  T⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lcons d a] = T[lcons (ldrop 1 (ldrop 1 (ldrop 1 d))) a].
Proof.
  rewrite !ren_ren_comp_ty. apply ren_subst_ty.
  intros [|m]; rlk_simpl; cbn [llk]; rewrite ?llk_ldrop; try reflexivity; f_equal; lia.
Qed.

Lemma lift2x3_cons_ty (T : ty) d a b :
  T⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩[lcons (lcons d a) b] =
  T[lcons (lcons (ldrop 1 (ldrop 1 (ldrop 1 d))) a) b].
Proof.
  rewrite !ren_ren_comp_ty. apply ren_subst_ty.
  intros [|[|m]]; rlk_simpl; cbn [llk]; rewrite ?llk_ldrop; try reflexivity; f_equal; lia.
Qed.

Section Valid.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

(** ** A type under two binders, weakened past three entries and
    instantiated at related terms *)

Lemma VTy_wk3_s2 {G Γ P Q B B' D1 D2 D3 k1 k2 k3 kp kq l u u' v v'} :
  VTy G (Γ ,, P @ kp ,, Q @ kq) B B' l -> VTy G (Γ ,, P @ kp) Q Q kq ->
  VTm G (Γ ,, D1 @ k1 ,, D2 @ k2 ,, D3 @ k3) u u' P⟨↑⟩⟨↑⟩⟨↑⟩ kp ->
  VTm G (Γ ,, D1 @ k1 ,, D2 @ k2 ,, D3 @ k3) v v' Q⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle u] kq ->
  VTy G (Γ ,, D1 @ k1 ,, D2 @ k2 ,, D3 @ k3)
    B⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩[lsingle2 u v]
    B'⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩[lsingle2 u' v'] l.
Proof using EL VL.
  intros HB HQ Hu Hv Δ d d' Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  pose proof Hd as Hd0. cbn [SubRel] in Hd0. destruct Hd0 as (((Hd3 & _) & _) & _).
  pose proof (Hu _ _ _ Hd) as Xu. rewrite !shift_subst_ty in Xu.
  pose proof (Hv _ _ _ Hd) as Xv. rewrite !single_subst_ty, !lift_single_ty, !lift1x3_cons_ty in Xv by assumption.
  pose proof (LRtm_irrel_r Xv (HQ _ _ _ (SubRel_cons Hd3 Xu))) as Xv'.
  rewrite !single2_subst_ty, !lift2_single2_ty, !lift2x3_cons_ty by assumption.
  exact (HB _ _ _ (SubRel_cons (SubRel_cons Hd3 Xu) Xv')).
Qed.

Lemma VG_wk3_s2 {G Γ P Q B B' D1 D2 D3 k1 k2 k3 kp kq l u u' v v'} :
  VTyG G (Γ ,, P @ kp ,, Q @ kq) B B' l -> VTyG G (Γ ,, P @ kp) Q Q kq ->
  VTmG G (Γ ,, D1 @ k1 ,, D2 @ k2 ,, D3 @ k3) u u' P⟨↑⟩⟨↑⟩⟨↑⟩ kp ->
  VTmG G (Γ ,, D1 @ k1 ,, D2 @ k2 ,, D3 @ k3) v v' Q⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle u] kq ->
  VTyG G (Γ ,, D1 @ k1 ,, D2 @ k2 ,, D3 @ k3)
    B⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩[lsingle2 u v]
    B'⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩[lsingle2 u' v'] l.
Proof using EL VL. intros. gl_lift. eapply VTy_wk3_s2; eassumption. Qed.

(** ** The induction hypothesis types at related signatures and motives *)

Lemma VG_iwfihty {G Γ l li l' l3 li3 l4 X X' A A' N N' Ot Ot' C C' M M'} :
  lwf (gL G) l -> lwf (gL G) li -> lwf (gL G) l' ->
  lequiv (gL G) l l3 -> lequiv (gL G) li li3 -> lequiv (gL G) l' l4 ->
  IWfSig (G := G) (i := ge_layer) Γ l li X A N Ot C ->
  [ G ; Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li ⊢g M @ l' ] ->
  VTyG G Γ X X' li -> VTyG G Γ A A' l -> VTmG G (Γ ,, A @ l) N N' tyNat lzero ->
  VTmG G (Γ ,, A @ l) Ot Ot' X⟨↑⟩ li -> VTmG G (Γ ,, A @ l ,, tyFin N @ lzero) C C' X⟨↑⟩⟨↑⟩ li ->
  VTyG G (Γ ,, X @ li) (iwfmotty l li X A N Ot C) (iwfmotty l li X A N Ot C) (lmax l li) ->
  VTyG G (Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li) M M' l' ->
  VTyG G (Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li)
    (iwfihty l li l' X A N Ot C M) (iwfihty l3 li3 l4 X' A' N' Ot' C' M') (lmax lzero l').
Proof using EL VL VN.
  intros Hwl Hwli Hwl' H13 Hi3 H24 HS HM VX VA VNt VO VC Vmot VM.
  pose proof (IWf_ihty_wf ge_typeof ge_notV HS Hwl' HM) as HI.
  destruct (inv_ty_pi HI) as ((_ & _ & _ & _ & HB) & _).
  pose proof (IWfSig_nf HS) as (NX & NA & NN & NO & NC).
  apply VG_pi; [exact I | exact Hwl' | apply lequiv_refl; exact I | exact (lequiv_sym _ _ _ H24) | exact HB | |].
  - apply VG_fin. eapply VTmG_retype; [exact (VG_shift_tm VNt) | reflexivity].
  - eapply VG_wk3_s2; [exact VM | exact Vmot | |].
    + eapply VTmG_retype; [exact (VG_lift1_tm (D := iwfcsty l li X A N Ot C) (kd := lmax l li) VC) |].
      ren_comm.
    + eapply VTmG_retype; [exact (elimIWf_Vdnth Hwl Hwli H13 Hi3 HS VX VA VNt VO VC) |].
      push_ren. push_subst. f_equal.
      1-5: rewrite ?ren_ren_comp_ty, ?ren_ren_comp, ?ren_as_r2l_ty, ?ren_as_r2l;
        first [apply subst2_eq_ty | apply subst2_eq]; intros [|[|[|[|[|n]]]]]; pw.
      rlk_simpl. cbn [llk lsingle]. rewrite ren_ren_comp, (ren_as_r2l C (rlift ↑)).
      apply ren_subst. intros [|[|n]]; pw.
Qed.

End Valid.

(** ** Through the fundamental theorem: validity with global substitutions
    at the identity, then escape *)

Section Core.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM}.
Context {E : GenericEq} {EL : GenericEqLaws} {LP : LRParams} {VL : VPLaws lr_vp} {VN : VPNe}.

Lemma VTyS_gid {G Γ T T' l} : [ ⊢ G ] -> dnfctx Γ -> dnfty T -> dnfty T' ->
  @VTyS EP EM E LP G Γ T T' l -> VTyG G Γ T T' l.
Proof.
  intros HG NΓ NT NT' H. pose proof (H _ _ _ (GSubRel_gid EP EM HG)) as X.
  rewrite gsubst_id_ctx, !gsubst_id_ty in X by first [assumption | intros; reflexivity]. exact X.
Qed.

Lemma VTmS_gid {G Γ t t' T l} : [ ⊢ G ] -> dnfctx Γ -> dnftm t -> dnftm t' -> dnfty T ->
  @VTmS EP EM E LP G Γ t t' T l -> VTmG G Γ t t' T l.
Proof.
  intros HG NΓ Nt Nt' NT H. pose proof (H _ _ _ (GSubRel_gid EP EM HG)) as X.
  rewrite gsubst_id_ctx, !gsubst_id_ty, !gsubst_id in X by first [assumption | intros; reflexivity]. exact X.
Qed.

Lemma IWf_ihty_geq {G Γ l li l' l3 li3 l4 X X' A A' N N' Ot Ot' C C' M M'} :
  lwf (gL G) l -> lwf (gL G) li -> lwf (gL G) l' ->
  lequiv (gL G) l l3 -> lequiv (gL G) li li3 -> lequiv (gL G) l' l4 ->
  IWfSig (G := G) (i := ge_layer) Γ l li X A N Ot C ->
  [ G ; Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li ⊢g M @ l' ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ⊢g
      iwfihty l3 li3 l4 X' A' N' Ot' C' M' @ lmax lzero l' ] ->
  @VCtxS EP EM E LP G (Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li) ->
  VTyG G Γ X X' li -> VTyG G Γ A A' l -> VTmG G (Γ ,, A @ l) N N' tyNat lzero ->
  VTmG G (Γ ,, A @ l) Ot Ot' X⟨↑⟩ li -> VTmG G (Γ ,, A @ l ,, tyFin N @ lzero) C C' X⟨↑⟩⟨↑⟩ li ->
  VTyG G (Γ ,, X @ li) (iwfmotty l li X A N Ot C) (iwfmotty l li X A N Ot C) (lmax l li) ->
  VTyG G (Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li) M M' l' ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ⊢g
      iwfihty l li l' X A N Ot C M ≅ iwfihty l3 li3 l4 X' A' N' Ot' C' M' @ lmax lzero l' ].
Proof.
  intros Hwl Hwli Hwl' H13 Hi3 H24 HS HM HIr VΘ VX VA VNt VO VC Vmot VM.
  pose proof (IWf_ihty_wf ge_typeof ge_notV HS Hwl' HM) as HI.
  pose proof (VG_iwfihty Hwl Hwli Hwl' H13 Hi3 H24 HS HM VX VA VNt VO VC Vmot VM) as V.
  pose proof (ctx_of_ty HI) as HΘ. pose proof (ctx_glob _ _ _ HΘ) as HG.
  pose proof (VΘ _ _ _ (GSubRel_gid EP EM HG) _ _ (gwk_ok_id G)) as X0. cbn [gwa] in X0.
  rewrite gsubst_id_ctx in X0 by first [exact (wf_ctx_dnf HΘ) | intros; reflexivity].
  pose proof (VTyG_loc V _ _ _ (SubRel_id_rel _ _ X0 HΘ)) as Z.
  rewrite (subst_id_ty _ _ (wf_ty_nf HI) lshift0_id), (subst_id_ty _ _ (wf_ty_nf HIr) lshift0_id) in Z.
  destruct Z as [R HR]. destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (_ & _ & Hg). exact (geq_ty_sound Hg).
Qed.

End Core.

(** ** At P and at M *)

Section Decl.

Local Notation DEP := (DeclEq lD compt_D).
Local Notation DEM := (DeclEq lM compt_M).
Local Notation LRM := (LR_M DEP DEM).

Local Instance DeclEqM_inst' : GenericEqM DEP DEM := DeclEqM.
Local Instance LRM_laws' : VPLaws (@lr_vp LRM) := vpM_laws DEP DEM.

Local Ltac dnfs := first [ eapply wf_ctx_dnf; eassumption | eapply wf_ty_dnf; eassumption
  | eapply wf_tm_dnf; eassumption | eapply wf_ty_dnf_ctx; eassumption | eapply wf_tm_dnf_ctx; eassumption
  | eapply wf_tm_dnf_ty; eassumption | reflexivity ].

(** The premises' typings, from the signatures' equation and the motives'. *)
Local Ltac prems HE EM H3 i0 :=
  assert (Hi : typeof i0 = i0) by reflexivity;
  pose proof HE as (E1 & E2 & HS & EX & EA & EN & EO & EC & HX' & HA' & HN' & HO' & HC');
  pose proof HS as (Hl & Hli & HX & HA & HN & HO & HC);
  pose proof (eqty_wf_l Hi EM); pose proof (eqty_wf_r Hi EM);
  pose proof (IWf_mot_wf Hi ltac:(discriminate) HS);
  pose proof (lequiv_wf_l _ _ _ H3) as Hl';
  pose proof (IWf_ihty_wf Hi ltac:(discriminate) HS Hl' (eqty_wf_l Hi EM)) as HI;
  pose proof (ctx_of_wf_ty Hi HI) as HΘ; pose proof (ctx_glob _ _ _ HΘ) as HG;
  pose proof (eqty_wf_r Hi EX); pose proof (eqty_wf_r Hi EA);
  pose proof (eqtm_wf_r Hi EN); pose proof (eqtm_wf_r Hi EO); pose proof (eqtm_wf_r Hi EC).

Lemma decl_IWf_ihty_eq {G Γ l li k ki l' k' X X' A A' N N' Ot Ot' C C' M M'} :
  IWfEq (G := G) (i := lD) Γ l li k ki X X' A A' N N' Ot Ot' C C' -> lequiv (gL G) l' k' ->
  [ G ; Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li ⊢[ lD ] M ≅ M' @ l' ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ⊢[ lD ]
      iwfihty k ki k' X' A' N' Ot' C' M' @ lmax lzero l' ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ⊢[ lD ]
      iwfihty l li l' X A N Ot C M ≅ iwfihty k ki k' X' A' N' Ot' C' M' @ lmax lzero l' ].
Proof.
  intros HE H3 EM HIr. prems HE EM H3 lD.
  pose proof (fundamentalS DEP DEM) as FT.
  destruct (proj1 (proj2 FT) _ _ _ HΘ eq_refl) as (_ & VΘ & _).
  destruct (proj1 (proj2 (proj2 (proj2 (proj2 FT)))) _ _ _ _ _ _ EX eq_refl) as (_ & VX & _).
  destruct (proj1 (proj2 (proj2 (proj2 (proj2 FT)))) _ _ _ _ _ _ EA eq_refl) as (_ & VA & _).
  destruct (proj1 (proj2 (proj2 (proj2 (proj2 FT)))) _ _ _ _ _ _ EM eq_refl) as (_ & VM & _).
  destruct (proj1 (proj2 (proj2 FT)) _ _ _ _ _ (IWf_mot_wf (i := lD) eq_refl ltac:(discriminate) HS) eq_refl)
    as (_ & Vmot & _).
  destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 FT))))) _ _ _ _ _ _ _ EN eq_refl) as (_ & _ & _ & VN & _).
  destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 FT))))) _ _ _ _ _ _ _ EO eq_refl) as (_ & _ & _ & VO & _).
  destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 FT))))) _ _ _ _ _ _ _ EC eq_refl) as (_ & _ & _ & VC & _).
  refine (IWf_ihty_geq DEP DEM (E := DEP) (LP := LR_P) Hl Hli Hl' E1 E2 H3 HS (eqty_wf_l eq_refl EM) HIr VΘ
            (VTyS_gid DEP DEM HG _ _ _ VX) (VTyS_gid DEP DEM HG _ _ _ VA) (VTmS_gid DEP DEM HG _ _ _ _ VN)
            (VTmS_gid DEP DEM HG _ _ _ _ VO) (VTmS_gid DEP DEM HG _ _ _ _ VC) (VTyS_gid DEP DEM HG _ _ _ Vmot)
            (VTyS_gid DEP DEM HG _ _ _ VM)); dnfs.
Qed.

Lemma declM_IWf_ihty_eq {G Γ l li k ki l' k' X X' A A' N N' Ot Ot' C C' M M'} :
  IWfEq (G := G) (i := lM) Γ l li k ki X X' A A' N N' Ot Ot' C C' -> lequiv (gL G) l' k' ->
  [ G ; Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li ⊢[ lM ] M ≅ M' @ l' ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ⊢[ lM ]
      iwfihty k ki k' X' A' N' Ot' C' M' @ lmax lzero l' ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ⊢[ lM ]
      iwfihty l li l' X A N Ot C M ≅ iwfihty k ki k' X' A' N' Ot' C' M' @ lmax lzero l' ].
Proof.
  intros HE H3 EM HIr. prems HE EM H3 lM.
  assert (HL : lwf (gL G) (lmax l li)) by (split; assumption).
  pose proof (fundamentalM DEP DEM) as FT.
  destruct (proj1 (proj2 FT) _ _ _ HΘ eq_refl) as (_ & VΘ).
  destruct (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 FT)))) _ _ _ _ _ _ EX eq_refl) Hli) as (_ & VX).
  destruct (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 FT)))) _ _ _ _ _ _ EA eq_refl) Hl) as (_ & VA).
  destruct (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 FT)))) _ _ _ _ _ _ EM eq_refl) Hl') as (_ & VM).
  destruct (proj1 (proj1 (proj2 (proj2 FT)) _ _ _ _ _ (IWf_mot_wf (i := lM) eq_refl ltac:(discriminate) HS) eq_refl) HL)
    as (_ & Vmot).
  destruct (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 FT))))) _ _ _ _ _ _ _ EN eq_refl) I) as (_ & _ & VN).
  destruct (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 FT))))) _ _ _ _ _ _ _ EO eq_refl) Hli) as (_ & _ & VO).
  destruct (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 FT))))) _ _ _ _ _ _ _ EC eq_refl) Hli) as (_ & _ & VC).
  refine (IWf_ihty_geq DEP DEM (E := DEM) (LP := LRM) Hl Hli Hl' E1 E2 H3 HS (eqty_wf_l eq_refl EM) HIr VΘ
            (VTyS_gid DEP DEM HG _ _ _ VX) (VTyS_gid DEP DEM HG _ _ _ VA) (VTmS_gid DEP DEM HG _ _ _ _ VN)
            (VTmS_gid DEP DEM HG _ _ _ _ VO) (VTmS_gid DEP DEM HG _ _ _ _ VC) (VTyS_gid DEP DEM HG _ _ _ Vmot)
            (VTyS_gid DEP DEM HG _ _ _ VM)); dnfs.
Qed.

End Decl.

(** The equation at the computing layers, as the algorithm uses it. *)
Lemma IWf_ihty_eq {G i Γ l li k ki l' k' X X' A A' N N' Ot Ot' C C' M M'} : compt i ->
  IWfEq (G := G) (i := i) Γ l li k ki X X' A A' N N' Ot Ot' C C' -> lequiv (gL G) l' k' ->
  [ G ; Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li ⊢[ i ] M ≅ M' @ l' ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ⊢[ i ]
      iwfihty k ki k' X' A' N' Ot' C' M' @ lmax lzero l' ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ⊢[ i ]
      iwfihty l li l' X A N Ot C M ≅ iwfihty k ki k' X' A' N' Ot' C' M' @ lmax lzero l' ].
Proof. intros Hc. destruct Hc as [-> | ->]; [exact decl_IWf_ihty_eq | exact declM_IWf_ihty_eq]. Qed.
