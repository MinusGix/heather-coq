(** * [elim_IWi]'s induction hypothesis types along equal signatures (M19b)

    As [IWfIhEq]'s: two eliminations whose signatures and motives are
    equal have equal induction hypothesis types,
    [Π(i : Fin N). Π(y : D[i]). M[C[i, y], app(dnth(cs; i), y)]], by the
    validity of the type ([VG_iwiihty], from [elimIWi_Vdnth] and the
    application's validity), the fundamental theorem and escape, at P and
    at M. So the algorithm's [actmne_elimIWi] does not compare them. *)
From DeLaM.Validity Require Export DeclConsequences.
From DeLaM.Validity Require Import IWfIhEq IWiElimDnth Id.
From DeLaM.Typing Require Import IWiIH.

(** ** Syntax *)

Lemma lift1x4_cons_ty (T : ty) d a :
  T⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lcons d a] = T[lcons (ldrop 1 (ldrop 1 (ldrop 1 (ldrop 1 d)))) a].
Proof.
  rewrite !ren_ren_comp_ty. apply ren_subst_ty.
  intros [|m]; rlk_simpl; cbn [llk]; rewrite ?llk_ldrop; try reflexivity; f_equal; lia.
Qed.

Lemma lift2x4_cons_ty (T : ty) d a b :
  T⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩[lcons (lcons d a) b] =
  T[lcons (lcons (ldrop 1 (ldrop 1 (ldrop 1 (ldrop 1 d)))) a) b].
Proof.
  rewrite !ren_ren_comp_ty. apply ren_subst_ty.
  intros [|[|m]]; rlk_simpl; cbn [llk]; rewrite ?llk_ldrop; try reflexivity; f_equal; lia.
Qed.

Section Valid.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

(** ** A type under two binders, weakened past four entries and
    instantiated at related terms *)

Lemma VTy_wk4_s2 {G Γ P Q B B' D1 D2 D3 D4 k1 k2 k3 k4 kp kq l u u' v v'} :
  VTy G (Γ ,, P @ kp ,, Q @ kq) B B' l -> VTy G (Γ ,, P @ kp) Q Q kq ->
  VTm G (Γ ,, D1 @ k1 ,, D2 @ k2 ,, D3 @ k3 ,, D4 @ k4) u u' P⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ kp ->
  VTm G (Γ ,, D1 @ k1 ,, D2 @ k2 ,, D3 @ k3 ,, D4 @ k4) v v' Q⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle u] kq ->
  VTy G (Γ ,, D1 @ k1 ,, D2 @ k2 ,, D3 @ k3 ,, D4 @ k4)
    B⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩[lsingle2 u v]
    B'⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩[lsingle2 u' v'] l.
Proof using EL VL.
  intros HB HQ Hu Hv Δ d d' Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  pose proof Hd as Hd0. cbn [SubRel] in Hd0. destruct Hd0 as ((((Hd4 & _) & _) & _) & _).
  pose proof (Hu _ _ _ Hd) as Xu. rewrite !shift_subst_ty in Xu.
  pose proof (Hv _ _ _ Hd) as Xv. rewrite !single_subst_ty, !lift_single_ty, !lift1x4_cons_ty in Xv by assumption.
  pose proof (LRtm_irrel_r Xv (HQ _ _ _ (SubRel_cons Hd4 Xu))) as Xv'.
  rewrite !single2_subst_ty, !lift2_single2_ty, !lift2x4_cons_ty by assumption.
  exact (HB _ _ _ (SubRel_cons (SubRel_cons Hd4 Xu) Xv')).
Qed.

Lemma VG_wk4_s2 {G Γ P Q B B' D1 D2 D3 D4 k1 k2 k3 k4 kp kq l u u' v v'} :
  VTyG G (Γ ,, P @ kp ,, Q @ kq) B B' l -> VTyG G (Γ ,, P @ kp) Q Q kq ->
  VTmG G (Γ ,, D1 @ k1 ,, D2 @ k2 ,, D3 @ k3 ,, D4 @ k4) u u' P⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ kp ->
  VTmG G (Γ ,, D1 @ k1 ,, D2 @ k2 ,, D3 @ k3 ,, D4 @ k4) v v' Q⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle u] kq ->
  VTyG G (Γ ,, D1 @ k1 ,, D2 @ k2 ,, D3 @ k3 ,, D4 @ k4)
    B⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩[lsingle2 u v]
    B'⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩[lsingle2 u' v'] l.
Proof using EL VL. intros. gl_lift. eapply VTy_wk4_s2; eassumption. Qed.

(** ** The induction hypothesis types at related signatures and motives *)

Lemma VG_iwiihty {G Γ l lp li l' l3 lp3 li3 l4 X X' A A' N N' D D' Ot Ot' C C' M M'} :
  lwf (gL G) l -> lwf (gL G) lp -> lwf (gL G) li -> lwf (gL G) l' ->
  lequiv (gL G) l l3 -> lequiv (gL G) lp lp3 -> lequiv (gL G) li li3 -> lequiv (gL G) l' l4 ->
  IWiSig (G := G) (i := ge_layer) Γ l lp li X A N D Ot C ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ⊢g
      iwiihty l lp li l' X A N D Ot C M @ lmax lzero (lmax lp l') ] ->
  VTyG G Γ X X' li -> VTyG G Γ A A' l -> VTmG G (Γ ,, A @ l) N N' tyNat lzero ->
  VTyG G (Γ ,, A @ l ,, tyFin N @ lzero) D D' lp ->
  VTmG G (Γ ,, A @ l) Ot Ot' X⟨↑⟩ li -> VTmG G (Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp) C C' X⟨↑⟩⟨↑⟩⟨↑⟩ li ->
  VTyG G (Γ ,, X @ li) (iwimotty l lp li X A N D Ot C) (iwimotty l lp li X A N D Ot C) (iwiL l lp li) ->
  VTyG G (Γ ,, X @ li ,, iwimotty l lp li X A N D Ot C @ iwiL l lp li) M M' l' ->
  VTyG G (Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li)
    (iwiihty l lp li l' X A N D Ot C M) (iwiihty l3 lp3 li3 l4 X' A' N' D' Ot' C' M') (lmax lzero (lmax lp l')).
Proof using EL VL VN.
  intros Hwl Hwlp Hwli Hwl' H13 Hp3 Hi3 H24 HS HI VX VA VNt VD VO VC Vmot VM.
  destruct (inv_ty_pi HI) as ((_ & _ & _ & HF0 & HB1) & _).
  destruct (inv_ty_pi HB1) as ((_ & _ & _ & HD1 & HB2) & _).
  pose proof (elimIWi_Vdnth Hwl Hwlp Hwli H13 Hp3 Hi3 HS VX VA VNt VD VO VC) as Vdn.
  apply VG_pi; [exact I | split; assumption | apply lequiv_refl; exact I | apply lequiv_sym, lequiv_max; assumption | exact HB1 | |].
  - apply VG_fin. eapply VTmG_retype; [exact (VG_shift_tm VNt) | reflexivity].
  - apply VG_pi; [exact Hwlp | exact Hwl' | apply lequiv_sym; exact Hp3 | apply lequiv_sym; exact H24 | exact HB2 | exact (VG_lift1 VD) |].
    eapply VG_wk4_s2; [exact VM | exact Vmot | |].
    + eapply VTmG_retype; [exact (VG_lift2_tm (D := iwicsty l lp li X A N D Ot C) (kd := iwiL l lp li) VC) |]. ren_comm.
    + assert (VEQ : forall Δ t1 t1' T1 t t' T k, VTmG G Δ t1 t1' T1 k -> t1 = t -> t1' = t' -> T1 = T -> VTmG G Δ t t' T k)
        by (intros; subst; assumption).
      eapply VTmG_retype; [eapply VG_app |].
      1: exact Hwlp.
      1: repeat split; assumption.
      1: apply lequiv_sym; exact Hp3.
      1: apply lequiv_sym; repeat apply lequiv_max; assumption.
      2: exact (VG_shift (VG_lift1 VD)).
      2: { apply VG_iwi; [exact Hwl | exact Hwlp | exact Hwli | exact (lequiv_sym _ _ _ H13) | exact (lequiv_sym _ _ _ Hp3)
                        | exact (lequiv_sym _ _ _ Hi3)
                        | exact (VG_shift (VG_shift (VG_shift (VG_shift (VG_shift VX)))))
                        | exact (VG_shift (VG_shift (VG_shift (VG_shift (VG_shift VA))))) | | | | |].
          + eapply VTmG_retype; [exact (VG_lift1_tm (VG_lift1_tm (VG_lift1_tm (VG_lift1_tm (VG_lift1_tm VNt))))) | reflexivity].
          + exact (VG_lift2_ty (VG_lift2_ty (VG_lift2_ty (VG_lift2_ty (VG_lift2_ty VD))))).
          + eapply VTmG_retype; [exact (VG_lift1_tm (VG_lift1_tm (VG_lift1_tm (VG_lift1_tm (VG_lift1_tm VO))))) |].
            now rewrite !IWf_E_ren.
          + eapply VTmG_retype; [exact (VG_lift3_tm (VG_lift3_tm (VG_lift3_tm (VG_lift3_tm (VG_lift3_tm VC))))) |].
            now rewrite !IWi_E_ren3.
          + eapply VTmG_retype; [exact (VG_lift1_tm (VG_lift2_tm VC)) |]. ren_comm. }
      3: { eapply VG_var; [repeat constructor | reflexivity]. }
      3: solve [cbn; f_equal; meq].
      2: eapply VEQ; [eapply VTmG_lconv; [exact (VG_shift_tm (B := D⟨rlift ↑⟩) (k := lp) Vdn) | apply lequiv_sym, iwiL_pi; assumption] | | |].
      (* the shifted [dnth] is the type's, and so is its type *)
      2: { rewrite ren_tmDNth; unfold iwiFam, iwiFamCod; f_equal.
           rewrite iwi_d3_single, iwi_c3_single; push_ren; f_equal; f_equal; ren_comm. }
      2: { rewrite ren_tmDNth; unfold iwiFam, iwiFamCod; f_equal.
           rewrite iwi_d3_single, iwi_c3_single; push_ren; f_equal; f_equal; ren_comm. }
      2: { unfold iwiFam, iwiFamCod.
           rewrite iwi_d3_single, iwi_c3_single; push_subst; push_ren; f_equal; f_equal; meq. }
      (* the codomain typed, from the children's family at the bound index *)
      1: { pose proof (proj1 (elimIWi_VF Hwl Hwlp Hwli H13 Hp3 Hi3 HS VX VA VNt VD VO VC)) as HFam.
           pose proof (ctx_of_ty HB1) as HΘ1.
           assert (Hv0 : [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ,, tyFin N⟨↑⟩ @ lzero
                           ⊢g var 0 : tyFin N⟨↑⟩⟨↑⟩ @ lzero ])
             by (eapply wf_tm_retype; [eapply wf_var; [rewrite ge_typeof; exact HΘ1 | constructor] | reflexivity]).
           pose proof (wf_ty_single ge_typeof HFam Hv0) as H1.
           pose proof (wk1_ty _ _ ge_typeof _ _ _ _ _ (ext_wf_g HD1 Hwlp) H1) as H2.
           match goal with |- [ _ ; _ ⊢g ?Cod @ _ ] =>
             assert (ET : ((iwiFc l lp li X A N D Ot C)[lsingle (var 0)])⟨↑⟩ = tyPi lp (iwiL l lp li) (D⟨rlift ↑⟩)⟨↑⟩ Cod) end.
           { unfold iwiFam, iwiFamCod. rewrite iwi_d3_single, iwi_c3_single; push_subst; push_ren; f_equal; f_equal; meq. }
           rewrite ET in H2. destruct (inv_ty_pi H2) as ((_ & _ & _ & _ & HCod) & _). exact HCod. }
Qed.

End Valid.

(** ** Through the fundamental theorem, as [IWf_ihty_geq] *)

Section Core.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM}.
Context {E : GenericEq} {EL : GenericEqLaws} {LP : LRParams} {VL : VPLaws lr_vp} {VN : VPNe}.

Lemma IWi_ihty_geq {G Γ l lp li l' l3 lp3 li3 l4 X X' A A' N N' D D' Ot Ot' C C' M M'} :
  lwf (gL G) l -> lwf (gL G) lp -> lwf (gL G) li -> lwf (gL G) l' ->
  lequiv (gL G) l l3 -> lequiv (gL G) lp lp3 -> lequiv (gL G) li li3 -> lequiv (gL G) l' l4 ->
  IWiSig (G := G) (i := ge_layer) Γ l lp li X A N D Ot C ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ⊢g
      iwiihty l lp li l' X A N D Ot C M @ lmax lzero (lmax lp l') ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ⊢g
      iwiihty l3 lp3 li3 l4 X' A' N' D' Ot' C' M' @ lmax lzero (lmax lp l') ] ->
  @VCtxS EP EM E LP G (Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li) ->
  VTyG G Γ X X' li -> VTyG G Γ A A' l -> VTmG G (Γ ,, A @ l) N N' tyNat lzero ->
  VTyG G (Γ ,, A @ l ,, tyFin N @ lzero) D D' lp ->
  VTmG G (Γ ,, A @ l) Ot Ot' X⟨↑⟩ li -> VTmG G (Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp) C C' X⟨↑⟩⟨↑⟩⟨↑⟩ li ->
  VTyG G (Γ ,, X @ li) (iwimotty l lp li X A N D Ot C) (iwimotty l lp li X A N D Ot C) (iwiL l lp li) ->
  VTyG G (Γ ,, X @ li ,, iwimotty l lp li X A N D Ot C @ iwiL l lp li) M M' l' ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ⊢g
      iwiihty l lp li l' X A N D Ot C M ≅ iwiihty l3 lp3 li3 l4 X' A' N' D' Ot' C' M' @ lmax lzero (lmax lp l') ].
Proof using EL VL VN.
  intros Hwl Hwlp Hwli Hwl' H13 Hp3 Hi3 H24 HS HI HIr VΘ VX VA VNt VD VO VC Vmot VM.
  pose proof (VG_iwiihty Hwl Hwlp Hwli Hwl' H13 Hp3 Hi3 H24 HS HI VX VA VNt VD VO VC Vmot VM) as V.
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
Local Ltac prems HE EM HI i0 :=
  assert (Hi : typeof i0 = i0) by reflexivity;
  pose proof HE as (E1 & E2 & E3 & HS & EX & EA & EN & ED & EO & EC & HX' & HA' & HN' & HD' & HO' & HC');
  pose proof HS as (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC);
  pose proof (eqty_wf_l Hi EM); pose proof (eqty_wf_r Hi EM);
  pose proof (IWi_mot_wf Hi ltac:(discriminate) HS);
  pose proof (ctx_of_wf_ty Hi HI) as HΘ; pose proof (ctx_glob _ _ _ HΘ) as HG;
  pose proof (eqty_wf_r Hi EX); pose proof (eqty_wf_r Hi EA); pose proof (eqty_wf_r Hi ED);
  pose proof (eqtm_wf_r Hi EN); pose proof (eqtm_wf_r Hi EO); pose proof (eqtm_wf_r Hi EC).

Lemma decl_IWi_ihty_eq {G Γ l lp li k kp ki l' k' X X' A A' N N' D D' Ot Ot' C C' M M'} :
  IWiEq (G := G) (i := lD) Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' -> lequiv (gL G) l' k' ->
  [ G ; Γ ,, X @ li ,, iwimotty l lp li X A N D Ot C @ iwiL l lp li ⊢[ lD ] M ≅ M' @ l' ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ⊢[ lD ]
      iwiihty l lp li l' X A N D Ot C M @ lmax lzero (lmax lp l') ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ⊢[ lD ]
      iwiihty k kp ki k' X' A' N' D' Ot' C' M' @ lmax lzero (lmax lp l') ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ⊢[ lD ]
      iwiihty l lp li l' X A N D Ot C M ≅ iwiihty k kp ki k' X' A' N' D' Ot' C' M' @ lmax lzero (lmax lp l') ].
Proof.
  intros HE H3 EM HI HIr. prems HE EM HI lD.
  pose proof (lequiv_wf_l _ _ _ H3) as Hl'.
  pose proof (fundamentalS DEP DEM) as FT.
  destruct (proj1 (proj2 FT) _ _ _ HΘ eq_refl) as (_ & VΘ & _).
  destruct (proj1 (proj2 (proj2 (proj2 (proj2 FT)))) _ _ _ _ _ _ EX eq_refl) as (_ & VX & _).
  destruct (proj1 (proj2 (proj2 (proj2 (proj2 FT)))) _ _ _ _ _ _ EA eq_refl) as (_ & VA & _).
  destruct (proj1 (proj2 (proj2 (proj2 (proj2 FT)))) _ _ _ _ _ _ ED eq_refl) as (_ & VD & _).
  destruct (proj1 (proj2 (proj2 (proj2 (proj2 FT)))) _ _ _ _ _ _ EM eq_refl) as (_ & VM & _).
  destruct (proj1 (proj2 (proj2 FT)) _ _ _ _ _ (IWi_mot_wf (i := lD) eq_refl ltac:(discriminate) HS) eq_refl)
    as (_ & Vmot & _).
  destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 FT))))) _ _ _ _ _ _ _ EN eq_refl) as (_ & _ & _ & VN & _).
  destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 FT))))) _ _ _ _ _ _ _ EO eq_refl) as (_ & _ & _ & VO & _).
  destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 FT))))) _ _ _ _ _ _ _ EC eq_refl) as (_ & _ & _ & VC & _).
  refine (IWi_ihty_geq DEP DEM (E := DEP) (LP := LR_P) Hl Hlp Hli Hl' E1 E2 E3 H3 HS HI HIr VΘ
            (VTyS_gid DEP DEM HG _ _ _ VX) (VTyS_gid DEP DEM HG _ _ _ VA) (VTmS_gid DEP DEM HG _ _ _ _ VN)
            (VTyS_gid DEP DEM HG _ _ _ VD)
            (VTmS_gid DEP DEM HG _ _ _ _ VO) (VTmS_gid DEP DEM HG _ _ _ _ VC) (VTyS_gid DEP DEM HG _ _ _ Vmot)
            (VTyS_gid DEP DEM HG _ _ _ VM)); dnfs.
Qed.

Lemma declM_IWi_ihty_eq {G Γ l lp li k kp ki l' k' X X' A A' N N' D D' Ot Ot' C C' M M'} :
  IWiEq (G := G) (i := lM) Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' -> lequiv (gL G) l' k' ->
  [ G ; Γ ,, X @ li ,, iwimotty l lp li X A N D Ot C @ iwiL l lp li ⊢[ lM ] M ≅ M' @ l' ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ⊢[ lM ]
      iwiihty l lp li l' X A N D Ot C M @ lmax lzero (lmax lp l') ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ⊢[ lM ]
      iwiihty k kp ki k' X' A' N' D' Ot' C' M' @ lmax lzero (lmax lp l') ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ⊢[ lM ]
      iwiihty l lp li l' X A N D Ot C M ≅ iwiihty k kp ki k' X' A' N' D' Ot' C' M' @ lmax lzero (lmax lp l') ].
Proof.
  intros HE H3 EM HI HIr. prems HE EM HI lM.
  pose proof (lequiv_wf_l _ _ _ H3) as Hl'.
  assert (HL : lwf (gL G) (iwiL l lp li)) by (repeat split; assumption).
  pose proof (fundamentalM DEP DEM) as FT.
  destruct (proj1 (proj2 FT) _ _ _ HΘ eq_refl) as (_ & VΘ).
  destruct (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 FT)))) _ _ _ _ _ _ EX eq_refl) Hli) as (_ & VX).
  destruct (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 FT)))) _ _ _ _ _ _ EA eq_refl) Hl) as (_ & VA).
  destruct (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 FT)))) _ _ _ _ _ _ ED eq_refl) Hlp) as (_ & VD).
  destruct (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 FT)))) _ _ _ _ _ _ EM eq_refl) Hl') as (_ & VM).
  destruct (proj1 (proj1 (proj2 (proj2 FT)) _ _ _ _ _ (IWi_mot_wf (i := lM) eq_refl ltac:(discriminate) HS) eq_refl) HL)
    as (_ & Vmot).
  destruct (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 FT))))) _ _ _ _ _ _ _ EN eq_refl) I) as (_ & _ & VN).
  destruct (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 FT))))) _ _ _ _ _ _ _ EO eq_refl) Hli) as (_ & _ & VO).
  destruct (proj1 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 FT))))) _ _ _ _ _ _ _ EC eq_refl) Hli) as (_ & _ & VC).
  refine (IWi_ihty_geq DEP DEM (E := DEM) (LP := LRM) Hl Hlp Hli Hl' E1 E2 E3 H3 HS HI HIr VΘ
            (VTyS_gid DEP DEM HG _ _ _ VX) (VTyS_gid DEP DEM HG _ _ _ VA) (VTmS_gid DEP DEM HG _ _ _ _ VN)
            (VTyS_gid DEP DEM HG _ _ _ VD)
            (VTmS_gid DEP DEM HG _ _ _ _ VO) (VTmS_gid DEP DEM HG _ _ _ _ VC) (VTyS_gid DEP DEM HG _ _ _ Vmot)
            (VTyS_gid DEP DEM HG _ _ _ VM)); dnfs.
Qed.

End Decl.

(** The equation at the computing layers, as the algorithm uses it. *)
Lemma IWi_ihty_eq {G i Γ l lp li k kp ki l' k' X X' A A' N N' D D' Ot Ot' C C' M M'} : compt i ->
  IWiEq (G := G) (i := i) Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' -> lequiv (gL G) l' k' ->
  [ G ; Γ ,, X @ li ,, iwimotty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ] M ≅ M' @ l' ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ]
      iwiihty l lp li l' X A N D Ot C M @ lmax lzero (lmax lp l') ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ]
      iwiihty k kp ki k' X' A' N' D' Ot' C' M' @ lmax lzero (lmax lp l') ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ]
      iwiihty l lp li l' X A N D Ot C M ≅ iwiihty k kp ki k' X' A' N' D' Ot' C' M' @ lmax lzero (lmax lp l') ].
Proof. intros Hc. destruct Hc as [-> | ->]; [exact decl_IWi_ihty_eq | exact declM_IWi_ihty_eq]. Qed.
