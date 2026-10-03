(** * Validity of [elim_W] (M13_DESIGN.md, M13a)

    By induction on [WRel] ([elimW_core]), at every global weakening and
    related substitution, so that a [sup]'s children, which live at Kripke
    weakenings, are covered by the induction hypothesis. At a [sup], both
    sides step to the step at the shape, the child function and the
    synthesized induction hypothesis [wIH]; the child function is related
    as a function by [WRel]'s [WhRel] premise and its children, and [wIH]
    is a λ whose applications step to [elim_W] at the children, related by
    the induction hypothesis. At a neutral, [elim_W] is neutral. *)
From DeLaM.Validity Require Export W.

Section WElim.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

Section ElimAt.
Context {G : gctx} {Γ : ctx} {l l' l'' l4 l5 l6 : lvl} {A A' B B' M M' : ty} {c c' : tm}
  (Hwl : lwf (gL G) l) (Hwl' : lwf (gL G) l') (Hwl'' : lwf (gL G) l'')
  (H14 : lequiv (gL G) l l4) (H25 : lequiv (gL G) l' l5) (H36 : lequiv (gL G) l'' l6)
  (HB : [ G ; Γ ,, A @ l ⊢g B @ l' ])
  (VA : VTyG G Γ A A' l) (VB : VTyG G (Γ ,, A @ l) B B' l')
  (VM : VTyG G (Γ ,, tyW l l' A B @ lmax l l') M M' l'')
  (Vfty : VTyG G (Γ ,, A @ l) (wfty l l' A B) (wfty l l' A B) (lmax l' (lmax l l')))
  (Vih : VTyG G (Γ ,, A @ l ,, wfty l l' A B @ lmax l' (lmax l l'))
           (wihty l l' l'' A B M) (wihty l l' l'' A B M) (lmax l' l''))
  (Vc : VTmG G (Γ ,, A @ l ,, wfty l l' A B @ lmax l' (lmax l l') ,, wihty l l' l'' A B M @ lmax l' l'')
          c c' (wstepty l l' A B M) l'').

(** The premises at a global weakening, localized. *)
Lemma elimW_loc {G0 γ} : gwk_ok γ G0 G -> [ ⊢ G0 ] ->
  [ G0 ; Γ⟦γ⟧ ,, A⟦γ⟧ @ l ⊢g B⟦γ⟧ @ l' ] /\
  VTyG G0 Γ⟦γ⟧ A⟦γ⟧ A'⟦γ⟧ l /\ VTyG G0 (Γ⟦γ⟧ ,, A⟦γ⟧ @ l) B⟦γ⟧ B'⟦γ⟧ l' /\
  VTy G0 (Γ⟦γ⟧ ,, tyW l l' A⟦γ⟧ B⟦γ⟧ @ lmax l l') M⟦γ⟧ M'⟦γ⟧ l'' /\
  VTy G0 (Γ⟦γ⟧ ,, A⟦γ⟧ @ l) (wfty l l' A⟦γ⟧ B⟦γ⟧) (wfty l l' A⟦γ⟧ B⟦γ⟧) (lmax l' (lmax l l')) /\
  VTy G0 (Γ⟦γ⟧ ,, A⟦γ⟧ @ l ,, wfty l l' A⟦γ⟧ B⟦γ⟧ @ lmax l' (lmax l l'))
    (wihty l l' l'' A⟦γ⟧ B⟦γ⟧ M⟦γ⟧) (wihty l l' l'' A⟦γ⟧ B⟦γ⟧ M⟦γ⟧) (lmax l' l'') /\
  VTm G0 (Γ⟦γ⟧ ,, A⟦γ⟧ @ l ,, wfty l l' A⟦γ⟧ B⟦γ⟧ @ lmax l' (lmax l l')
            ,, wihty l l' l'' A⟦γ⟧ B⟦γ⟧ M⟦γ⟧ @ lmax l' l'')
    c⟦γ⟧ c'⟦γ⟧ (wstepty l l' A⟦γ⟧ B⟦γ⟧ M⟦γ⟧) l''.
Proof.
  intros Hγ HG0. pose proof (gwa_ty Hγ HG0 HB) as HBγ. rewrite gwa_cext in HBγ.
  pose proof (VTyG_gwk VA Hγ) as VAγ. pose proof (VTyG_gwk VB Hγ) as VBγ. rewrite gwa_cext in VBγ.
  pose proof (VM _ _ Hγ) as VMγ. rewrite !gwa_cext, gwa_tyW in VMγ.
  pose proof (Vfty _ _ Hγ) as Vftyγ. rewrite !gwa_cext, gwa_wfty in Vftyγ.
  pose proof (Vih _ _ Hγ) as Vihγ. rewrite !gwa_cext, gwa_wfty, gwa_wihty in Vihγ.
  pose proof (Vc _ _ Hγ) as Vcγ. rewrite !gwa_cext, gwa_wfty, gwa_wihty, gwa_wstepty in Vcγ.
  repeat split; assumption.
Qed.

(** The premises at a related substitution after a global weakening. *)
Lemma elimW_at {G0 γ Δ0 e e'} : gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' ->
  [ G0 ; Δ0 ⊢g A⟦γ⟧[e] @ l ] /\ [ G0 ; Δ0 ⊢ A⟦γ⟧[e] ≈ A'⟦γ⟧[e'] @ l ] /\
  [ G0 ; Δ0 ,, A⟦γ⟧[e] @ l ⊢g B⟦γ⟧[llift e] @ l' ] /\
  [ G0 ; Δ0 ,, A⟦γ⟧[e] @ l ⊢ B⟦γ⟧[llift e] ≈ B'⟦γ⟧[llift e'] @ l' ] /\
  [ G0 ; Δ0 ,, tyW l l' A⟦γ⟧[e] B⟦γ⟧[llift e] @ lmax l l' ⊢g M⟦γ⟧[llift e] @ l'' ] /\
  [ G0 ; Δ0 ,, tyW l l' A⟦γ⟧[e] B⟦γ⟧[llift e] @ lmax l l' ⊢ M⟦γ⟧[llift e] ≈ M'⟦γ⟧[llift e'] @ l'' ] /\
  [ G0 ; Δ0 ,, A⟦γ⟧[e] @ l ⊢g wfty l l' A⟦γ⟧[e] B⟦γ⟧[llift e] @ lmax l' (lmax l l') ] /\
  [ G0 ; Δ0 ,, A⟦γ⟧[e] @ l ,, wfty l l' A⟦γ⟧[e] B⟦γ⟧[llift e] @ lmax l' (lmax l l')
      ⊢g wihty l l' l'' A⟦γ⟧[e] B⟦γ⟧[llift e] M⟦γ⟧[llift e] @ lmax l' l'' ] /\
  [ G0 ; Δ0 ,, A⟦γ⟧[e] @ l ,, wfty l l' A⟦γ⟧[e] B⟦γ⟧[llift e] @ lmax l' (lmax l l')
      ,, wihty l l' l'' A⟦γ⟧[e] B⟦γ⟧[llift e] M⟦γ⟧[llift e] @ lmax l' l''
      ⊢ c⟦γ⟧[llift (llift (llift e))] ≈ c'⟦γ⟧[llift (llift (llift e'))]
      : wstepty l l' A⟦γ⟧[e] B⟦γ⟧[llift e] M⟦γ⟧[llift e] @ l'' ].
Proof.
  intros Hγ He. pose proof (ctx_glob _ _ _ (SubRel_ctx He)) as HG0.
  destruct (SubRel_nf _ _ _ _ _ He) as [Ne Ne'].
  destruct (elimW_loc Hγ HG0) as (HBγ & VAγ & VBγ & VMγ & Vftyγ & Vihγ & Vcγ).
  pose proof (VTyG_loc VAγ) as VAl. pose proof (VTy_refl_l VAl) as VAA.
  pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwl) as Hwl0.
  pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwl') as Hwl'0.
  pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwl'') as Hwl''0.
  pose proof (lwf_max Hwl0 Hwl'0) as HwL.
  pose proof (lwf_max Hwl'0 HwL) as HwF. pose proof (lwf_max Hwl'0 Hwl''0) as HwI.
  destruct (VAl _ _ _ He) as [RA HRA]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HA0 & _ & EA).
  pose proof (SubRel_lift He VAA HA0 Hwl0) as H1.
  destruct (VTyG_loc VBγ _ _ _ H1) as [RB HRB]. destruct (escape_ty _ _ _ _ _ _ _ _ HRB) as (HB0 & _ & EB).
  (* the motive, under [W] *)
  pose proof (V_W Hwl0 Hwl'0 (lequiv_refl _ _ Hwl0) (lequiv_refl _ _ Hwl'0) HBγ (VTyG_refl_l VAγ) (VTyG_refl_l VBγ))
    as VW.
  destruct (VW _ _ _ He) as [RW HRW]. destruct (escape_ty _ _ _ _ _ _ _ _ HRW) as (HW0 & _ & _).
  pose proof (SubRel_lift He VW HW0 HwL) as HW1.
  destruct (VMγ _ _ _ HW1) as [RM HRM]. destruct (escape_ty _ _ _ _ _ _ _ _ HRM) as (HM0 & _ & EM).
  rewrite subst_tyW in HM0, EM.
  (* the step's telescope *)
  destruct (Vftyγ _ _ _ H1) as [RF HRF]. destruct (escape_ty _ _ _ _ _ _ _ _ HRF) as (HF0 & _ & _).
  pose proof (SubRel_lift H1 Vftyγ HF0 HwF) as H2.
  destruct (Vihγ _ _ _ H2) as [RI HRI]. destruct (escape_ty _ _ _ _ _ _ _ _ HRI) as (HI0 & _ & _).
  pose proof (SubRel_lift H2 Vihγ HI0 HwI) as H3.
  pose proof (LRtm_geq (Vcγ _ _ _ H3)) as Ec.
  rewrite wfty_llift in HF0, HI0, Ec by exact Ne.
  rewrite wihty_llift2 in HI0, Ec by exact Ne.
  rewrite wstepty_llift3 in Ec by exact Ne.
  repeat split; assumption.
Qed.

(** [elim_W]'s congruence and typed reductions in the scrutinee. *)
Section Cong.
Context {G0 γ Δ0 e e'} (Hγ : gwk_ok γ G0 G) (He : SubRel G0 Γ⟦γ⟧ Δ0 e e').

Lemma elimW_cong {t t'} :
  [ G0 ; Δ0 ⊢g t ≅ t' : tyW l l' A⟦γ⟧[e] B⟦γ⟧[llift e] @ lmax l l' ] ->
  [ G0 ; Δ0 ⊢g tmElimW l l' l'' A⟦γ⟧[e] B⟦γ⟧[llift e] M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))] t
             ≅ tmElimW l4 l5 l6 A'⟦γ⟧[e'] B'⟦γ⟧[llift e'] M'⟦γ⟧[llift e'] c'⟦γ⟧[llift (llift (llift e'))] t'
             : M⟦γ⟧[llift e][lsingle t] @ l'' ].
Proof.
  intros Ht. destruct (elimW_at Hγ He) as (HA0 & EA & HB0 & EB & HM0 & EM & HF0 & HI0 & Ec).
  apply eqtm_elimW; first [exact ge_notV | exact ge_compt | apply (lequiv_weaken _ _ _ _ (proj1 Hγ)); assumption
                          | apply geq_ty_sound; assumption | apply geq_tm_sound; assumption | assumption].
Qed.

Lemma elimW_cong_l {t t'} :
  [ G0 ; Δ0 ⊢g t ≅ t' : tyW l l' A⟦γ⟧[e] B⟦γ⟧[llift e] @ lmax l l' ] ->
  [ G0 ; Δ0 ⊢g tmElimW l l' l'' A⟦γ⟧[e] B⟦γ⟧[llift e] M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))] t
             ≅ tmElimW l l' l'' A⟦γ⟧[e] B⟦γ⟧[llift e] M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))] t'
             : M⟦γ⟧[llift e][lsingle t] @ l'' ].
Proof.
  intros Ht. destruct (elimW_at Hγ He) as (HA0 & EA & HB0 & EB & HM0 & EM & HF0 & HI0 & Ec).
  pose proof (eqtm_wf_l ge_typeof (geq_tm_sound Ec)) as Hc0.
  apply eqtm_elimW; first [exact ge_notV | exact ge_compt | apply lequiv_refl, (lwf_weaken _ _ _ (proj1 Hγ)); assumption
                          | apply eqty_refl; assumption | apply eqtm_refl; assumption | assumption].
Qed.

Lemma elimW_red_l {t w} : [ G0 ; Δ0 ⊢g t ⤳* w : tyW l l' A⟦γ⟧[e] B⟦γ⟧[llift e] @ lmax l l' ] ->
  [ G0 ; Δ0 ⊢g tmElimW l l' l'' A⟦γ⟧[e] B⟦γ⟧[llift e] M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))] t
             ⤳* tmElimW l l' l'' A⟦γ⟧[e] B⟦γ⟧[llift e] M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))] w
             : M⟦γ⟧[llift e][lsingle t] @ l'' ].
Proof.
  intros Hr. pose proof (elimW_cong_l (tmred_eq _ _ _ _ _ _ _ Hr)) as X.
  split; [exact (eqtm_wf_l ge_typeof X) | apply reds_elimW, (tmred_red _ _ _ _ _ _ _ Hr) | exact X].
Qed.

Lemma elimW_red_r {t t' w'} :
  [ G0 ; Δ0 ⊢g t ≅ t' : tyW l l' A⟦γ⟧[e] B⟦γ⟧[llift e] @ lmax l l' ] ->
  [ G0 ; Δ0 ⊢g t' ⤳* w' : tyW l l' A⟦γ⟧[e] B⟦γ⟧[llift e] @ lmax l l' ] ->
  [ G0 ; Δ0 ⊢g tmElimW l4 l5 l6 A'⟦γ⟧[e'] B'⟦γ⟧[llift e'] M'⟦γ⟧[llift e'] c'⟦γ⟧[llift (llift (llift e'))] t'
             ⤳* tmElimW l4 l5 l6 A'⟦γ⟧[e'] B'⟦γ⟧[llift e'] M'⟦γ⟧[llift e'] c'⟦γ⟧[llift (llift (llift e'))] w'
             : M⟦γ⟧[llift e][lsingle t] @ l'' ].
Proof.
  intros Htt Hr. pose proof (elimW_cong Htt) as X1.
  pose proof (elimW_cong (eqtm_trans _ _ _ _ _ _ _ _ Htt (tmred_eq _ _ _ _ _ _ _ Hr))) as X2.
  split; [exact (eqtm_wf_r ge_typeof X1) | apply reds_elimW, (tmred_red _ _ _ _ _ _ _ Hr) |].
  eapply eqtm_trans; [apply eqtm_sym, X1 | exact X2].
Qed.

End Cong.

(** The relation at [W] and at the motive, at a related substitution. *)
Lemma elimW_WLR {G0 γ Δ0 e e'} : gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' ->
  LogRel (lmax l l') G0 Δ0 (tyW l l' A⟦γ⟧[e] B⟦γ⟧[llift e]) (tyW l l' A⟦γ⟧[e'] B⟦γ⟧[llift e']) (lmax l l')
    (WRel G0 Δ0 l l' A⟦γ⟧[e] B⟦γ⟧[llift e]
       (piDom (A := A⟦γ⟧) (A' := A⟦γ⟧) (l := l) (l' := l') Δ0 e e')
       (piCod (A := A⟦γ⟧) (A' := A⟦γ⟧) (B := B⟦γ⟧) (B' := B⟦γ⟧) (l := l) (l' := l') Δ0 e e')) /\
  (forall ρ : kwk G0 Δ0,
     LR (lmeasure (lmax l l')) (LRbelow (lmeasure (lmax l l'))) (kw_G ρ) (kw_Δ ρ)
       (kty ρ A⟦γ⟧[e]) (kty ρ A⟦γ⟧[e']) l
       (piDom (A := A⟦γ⟧) (A' := A⟦γ⟧) (l := l) (l' := l') Δ0 e e' ρ)) /\
  (forall (ρ : kwk G0 Δ0) x y h,
     LR (lmeasure (lmax l l')) (LRbelow (lmeasure (lmax l l'))) (kw_G ρ) (kw_Δ ρ)
       (ktyl ρ B⟦γ⟧[llift e])[lsingle x] (ktyl ρ B⟦γ⟧[llift e'])[lsingle y] l'
       (piCod (A := A⟦γ⟧) (A' := A⟦γ⟧) (B := B⟦γ⟧) (B' := B⟦γ⟧) (l := l) (l' := l') Δ0 e e' ρ x y h)).
Proof.
  intros Hγ He. pose proof (ctx_glob _ _ _ (SubRel_ctx He)) as HG0.
  destruct (elimW_loc Hγ HG0) as (HBγ & VAγ & VBγ & _).
  pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwl) as Hwl0.
  pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwl') as Hwl'0.
  pose proof (LR_W_here Hwl0 Hwl'0 (lequiv_refl _ _ Hwl0) (lequiv_refl _ _ Hwl'0) HBγ
                (VTyG_refl_l VAγ) (VTyG_refl_l VBγ) _ _ _ He) as HW.
  destruct (poly_here (F := tyW) (A := A⟦γ⟧) (A' := A⟦γ⟧) (B := B⟦γ⟧) (B' := B⟦γ⟧) Hwl0 Hwl'0
              (lequiv_refl _ _ Hwl0) (lequiv_refl _ _ Hwl'0) HBγ (VTyG_refl_l VAγ) (VTyG_refl_l VBγ) Δ0 e e'
              ltac:(intros; apply wft_W; auto using ge_compt, ge_notV) ltac:(reflexivity) He) as (_ & Hdom & Hcod).
  rewrite !subst_tyW in HW. exact (conj HW (conj Hdom Hcod)).
Qed.

Lemma elimW_mot {G0 γ Δ0 e e' x x'} : gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' ->
  LRtm (lmax l l') G0 Δ0 (tyW l l' A⟦γ⟧[e] B⟦γ⟧[llift e]) (tyW l l' A⟦γ⟧[e'] B⟦γ⟧[llift e']) x x' ->
  LRty l'' G0 Δ0 M⟦γ⟧[llift e][lsingle x] M⟦γ⟧[llift e'][lsingle x'].
Proof.
  intros Hγ He Hx. pose proof (ctx_glob _ _ _ (SubRel_ctx He)) as HG0.
  destruct (SubRel_nf _ _ _ _ _ He) as [Ne Ne'].
  destruct (elimW_loc Hγ HG0) as (_ & _ & _ & VMγ & _).
  rewrite <- !subst_tyW in Hx.
  pose proof (VTy_refl_l VMγ _ _ _ (SubRel_cons He Hx)) as X.
  now rewrite <- !lift_single_ty in X.
Qed.

(** ** The core: related eliminations at related trees *)

(** The motive at a tree: at every global weakening and related
    substitution of the premises' context, at the shape and position types
    and data of the relation at [W] there. *)
Definition elimW_mrel G0 Δ0 k1 k2 A0 B0 (dR : DomRel G0 Δ0) (cR : CodRel G0 Δ0 dR) (t t' : tm) : Prop :=
  forall γ e e', gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' ->
  k1 = l -> k2 = l' -> A0 = A⟦γ⟧[e] -> B0 = B⟦γ⟧[llift e] ->
  (forall ρ : kwk G0 Δ0, LR (lmeasure (lmax l l')) (LRbelow (lmeasure (lmax l l'))) (kw_G ρ) (kw_Δ ρ)
     (kty ρ A0) (kty ρ A⟦γ⟧[e']) l (dR ρ)) ->
  (forall (ρ : kwk G0 Δ0) x y h, LR (lmeasure (lmax l l')) (LRbelow (lmeasure (lmax l l'))) (kw_G ρ) (kw_Δ ρ)
     (ktyl ρ B0)[lsingle x] (ktyl ρ B⟦γ⟧[llift e'])[lsingle y] l' (cR ρ x y h)) ->
  LRtm l'' G0 Δ0 M⟦γ⟧[llift e][lsingle t] M⟦γ⟧[llift e][lsingle t]
    (tmElimW l l' l'' A0 B0 M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))] t)
    (tmElimW l4 l5 l6 A'⟦γ⟧[e'] B'⟦γ⟧[llift e'] M'⟦γ⟧[llift e'] c'⟦γ⟧[llift (llift (llift e'))] t').

(** At a [sup] pair, given the motive at the children: the steps at the
    shapes, the child functions and the synthesized induction hypotheses
    are related, and both [elim_W]s step to them. *)
Lemma elimW_step {G0 Δ0} {dR : DomRel G0 Δ0} {cR : CodRel G0 Δ0 dR} {m1 m2 m1' m2' C D C' D' a a' f f' γ e e'} :
  lequiv (gL G0) m1 l -> lequiv (gL G0) m2 l' -> lequiv (gL G0) m1' l -> lequiv (gL G0) m2' l' ->
  [ G0 ; Δ0 ⊢ A⟦γ⟧[e] ≈ C @ l ] -> [ G0 ; Δ0 ⊢ A⟦γ⟧[e] ≈ C' @ l ] ->
  [ G0 ; Δ0 ,, A⟦γ⟧[e] @ l ⊢ B⟦γ⟧[llift e] ≈ D @ l' ] -> [ G0 ; Δ0 ,, A⟦γ⟧[e] @ l ⊢ B⟦γ⟧[llift e] ≈ D' @ l' ] ->
  (forall ρ : kwk G0 Δ0, dR ρ (ktm ρ a) (ktm ρ a')) ->
  (forall ρ : kwk G0 Δ0, WhRel (kw_G ρ) (kw_Δ ρ)
     (tyPi l' (lmax l l') (ktyl ρ B⟦γ⟧[llift e])[lsingle (ktm ρ a)] (tyW l l' (kty ρ A⟦γ⟧[e]) (ktyl ρ B⟦γ⟧[llift e]))⟨↑⟩)
     (lmax l' (lmax l l')) (ktm ρ f) (ktm ρ f')) ->
  (forall (ρ : kwk G0 Δ0) (ha : dR ρ (ktm ρ a) (ktm ρ a')) b b', cR ρ (ktm ρ a) (ktm ρ a') ha b b' ->
     forall la lb A1 B1 la' lb' A1' B1',
     lequiv (gL G0) la l' -> lequiv (gL G0) lb (lmax l l') ->
     lequiv (gL G0) la' l' -> lequiv (gL G0) lb' (lmax l l') ->
     [ kw_G ρ ; kw_Δ ρ ⊢ (ktyl ρ B⟦γ⟧[llift e])[lsingle (ktm ρ a)] ≈ A1 @ l' ] ->
     [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ B⟦γ⟧[llift e])[lsingle (ktm ρ a)] @ l'
         ⊢ (tyW l l' (kty ρ A⟦γ⟧[e]) (ktyl ρ B⟦γ⟧[llift e]))⟨↑⟩ ≈ B1 @ lmax l l' ] ->
     [ kw_G ρ ; kw_Δ ρ ⊢ (ktyl ρ B⟦γ⟧[llift e])[lsingle (ktm ρ a)] ≈ A1' @ l' ] ->
     [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ B⟦γ⟧[llift e])[lsingle (ktm ρ a)] @ l'
         ⊢ (tyW l l' (kty ρ A⟦γ⟧[e]) (ktyl ρ B⟦γ⟧[llift e]))⟨↑⟩ ≈ B1' @ lmax l l' ] ->
     WRel (kw_G ρ) (kw_Δ ρ) l l' (kty ρ A⟦γ⟧[e]) (ktyl ρ B⟦γ⟧[llift e])
       (fun ρ' => dR (kw_comp ρ ρ')) (fun ρ' x x' h => cR (kw_comp ρ ρ') x x' h)
       (app (ktm ρ f) la lb A1 B1 b) (app (ktm ρ f') la' lb' A1' B1' b')) ->
  (forall (ρ : kwk G0 Δ0) (ha : dR ρ (ktm ρ a) (ktm ρ a')) b b', cR ρ (ktm ρ a) (ktm ρ a') ha b b' ->
     forall la lb A1 B1 la' lb' A1' B1',
     lequiv (gL G0) la l' -> lequiv (gL G0) lb (lmax l l') ->
     lequiv (gL G0) la' l' -> lequiv (gL G0) lb' (lmax l l') ->
     [ kw_G ρ ; kw_Δ ρ ⊢ (ktyl ρ B⟦γ⟧[llift e])[lsingle (ktm ρ a)] ≈ A1 @ l' ] ->
     [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ B⟦γ⟧[llift e])[lsingle (ktm ρ a)] @ l'
         ⊢ (tyW l l' (kty ρ A⟦γ⟧[e]) (ktyl ρ B⟦γ⟧[llift e]))⟨↑⟩ ≈ B1 @ lmax l l' ] ->
     [ kw_G ρ ; kw_Δ ρ ⊢ (ktyl ρ B⟦γ⟧[llift e])[lsingle (ktm ρ a)] ≈ A1' @ l' ] ->
     [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ B⟦γ⟧[llift e])[lsingle (ktm ρ a)] @ l'
         ⊢ (tyW l l' (kty ρ A⟦γ⟧[e]) (ktyl ρ B⟦γ⟧[llift e]))⟨↑⟩ ≈ B1' @ lmax l l' ] ->
     elimW_mrel (kw_G ρ) (kw_Δ ρ) l l' (kty ρ A⟦γ⟧[e]) (ktyl ρ B⟦γ⟧[llift e])
       (fun ρ' => dR (kw_comp ρ ρ')) (fun ρ' x x' h => cR (kw_comp ρ ρ') x x' h)
       (app (ktm ρ f) la lb A1 B1 b) (app (ktm ρ f') la' lb' A1' B1' b')) ->
  gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' ->
  nftm (tmSup m1 m2 C D a f) -> nftm (tmSup m1' m2' C' D' a' f') ->
  (forall ρ : kwk G0 Δ0, LR (lmeasure (lmax l l')) (LRbelow (lmeasure (lmax l l'))) (kw_G ρ) (kw_Δ ρ)
     (kty ρ A⟦γ⟧[e]) (kty ρ A⟦γ⟧[e']) l (dR ρ)) ->
  (forall (ρ : kwk G0 Δ0) x y h, LR (lmeasure (lmax l l')) (LRbelow (lmeasure (lmax l l'))) (kw_G ρ) (kw_Δ ρ)
     (ktyl ρ B⟦γ⟧[llift e])[lsingle x] (ktyl ρ B⟦γ⟧[llift e'])[lsingle y] l' (cR ρ x y h)) ->
  LRtm l'' G0 Δ0 M⟦γ⟧[llift e][lsingle (tmSup m1 m2 C D a f)] M⟦γ⟧[llift e][lsingle (tmSup m1 m2 C D a f)]
    c⟦γ⟧[llift (llift (llift e))][lsingle3 a f
      (wIH l l' l'' A⟦γ⟧[e] B⟦γ⟧[llift e] M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))] a f)]
    c'⟦γ⟧[llift (llift (llift e'))][lsingle3 a' f'
      (wIH l4 l5 l6 A'⟦γ⟧[e'] B'⟦γ⟧[llift e'] M'⟦γ⟧[llift e'] c'⟦γ⟧[llift (llift (llift e'))] a' f')] /\
  [ G0 ; Δ0 ⊢g tmElimW l l' l'' A⟦γ⟧[e] B⟦γ⟧[llift e] M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))]
                 (tmSup m1 m2 C D a f)
             ⤳* c⟦γ⟧[llift (llift (llift e))][lsingle3 a f
                  (wIH l l' l'' A⟦γ⟧[e] B⟦γ⟧[llift e] M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))] a f)]
             : M⟦γ⟧[llift e][lsingle (tmSup m1 m2 C D a f)] @ l'' ] /\
  [ G0 ; Δ0 ⊢g tmElimW l4 l5 l6 A'⟦γ⟧[e'] B'⟦γ⟧[llift e'] M'⟦γ⟧[llift e'] c'⟦γ⟧[llift (llift (llift e'))]
                 (tmSup m1' m2' C' D' a' f')
             ⤳* c'⟦γ⟧[llift (llift (llift e'))][lsingle3 a' f'
                  (wIH l4 l5 l6 A'⟦γ⟧[e'] B'⟦γ⟧[llift e'] M'⟦γ⟧[llift e'] c'⟦γ⟧[llift (llift (llift e'))] a' f')]
             : M⟦γ⟧[llift e][lsingle (tmSup m1 m2 C D a f)] @ l'' ].
Proof.
  intros Hk1 Hk2 Hk1' Hk2' HC0 HC0' HD0 HD0' Ha Hwf Hf IH Hγ He Nw Nw' HD HC.
  cbn in Nw, Nw'. destruct Nw as (_ & _ & Na & Nf). destruct Nw' as (_ & _ & Na' & Nf').
  pose proof (SubRel_ctx He) as HΔ0. pose proof (ctx_glob _ _ _ HΔ0) as HG0.
  destruct (SubRel_nf _ _ _ _ _ He) as [Ne Ne'].
  destruct (elimW_loc Hγ HG0) as (HBγ & VAγ & VBγ & VMγ & Vftyγ & Vihγ & Vcγ).
  destruct (elimW_at Hγ He) as (HA0 & EA & HB0 & EB & HM0 & EM & HF0 & HI0 & Ec).
  pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwl) as Hwl0.
  pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwl') as Hwl'0.
  pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwl'') as Hwl''0.
  pose proof (lwf_max Hwl0 Hwl'0) as HwL. pose proof (lwf_max Hwl'0 HwL) as HwF.
  pose proof (lwf_max Hwl'0 Hwl''0) as HwI.
  assert (HleN : forall k, lmeasure k <= lmeasure (lmax k (lmax l l'))) by (intros; rewrite !lmeasure_max; lia).
  destruct (VTy_refl_l (VTyG_loc VAγ) _ _ _ (SubRel_refl_r He)) as [RA' HRA'].
  destruct (escape_ty _ _ _ _ _ _ _ _ HRA') as (HA0' & _ & _).
  pose proof (wf_ty_nf HA0) as NA. pose proof (wf_ty_nf HA0') as NA'.
  pose proof (wf_ty_nf HB0) as NB. pose proof (wf_ty_nf HM0) as NM.
  (* the shapes, at the identity world *)
  assert (Xa : LRtm l G0 Δ0 A⟦γ⟧[e] A⟦γ⟧[e'] a a').
  { refine (rel_at_id HΔ0 NA NA' Na Na' _ HD (Ha _)). rewrite lmeasure_max; lia. }
  pose proof (LRtm_geq Xa) as Ea. destruct (LRtm_escape Xa) as [Hat Ha't].
  pose proof (SubRel_cons He Xa) as HS1.
  (* the child functions: related at the children's type, as [PiRel] *)
  destruct (Vftyγ _ _ _ HS1) as [RF HRF].
  rewrite <- (lift_single_ty _ e a Ne), <- (lift_single_ty _ e' a' Ne'), (wfty_llift e), (wfty_llift e'),
    !W_E5 in HRF.
  destruct (escape_ty _ _ _ _ _ _ _ _ HRF) as (HFT & _ & _).
  destruct (LR_inv_pi HRF (tyred_refl _ _ HFT)) as (n3 & n4 & P1 & Q1 & domRf & codRf & Pf & domAdf & codAdf & HRRf).
  pose proof (Hwf (kw_loc wk_id (wkwf_id Δ0) HΔ0)) as Wι. rewrite <- kty_fty in Wι.
  pose proof (WhRel_at_id HΔ0 (wf_ty_nf HFT) Nf Nf' Wι) as (wf & wf' & Hr & Hr' & Nwf & Nwf' & Ewf).
  destruct Pf as [_ Hn3 Hn4 _ _ _ _ HBa HP1 HWu HQ1 HPP HQQ].
  assert (EPi : [ G0 ; Δ0 ⊢g tyPi l' (lmax l l') B⟦γ⟧[llift e][lsingle a] (tyW l l' A⟦γ⟧[e] B⟦γ⟧[llift e])⟨↑⟩
                    ≅ tyPi n3 n4 P1 Q1 @ lmax l' (lmax l l') ])
    by (apply geq_ty_sound, geq_ty_pi; auto using lequiv_sym).
  assert (HleL : lmeasure (lmax l l') <= lmeasure (lmax l' (lmax l l'))) by (rewrite !lmeasure_max; lia).
  assert (Hle' : lmeasure l' <= lmeasure (lmax l l')) by (rewrite !lmeasure_max; lia).
  assert (Kf : forall (ρ : kwk G0 Δ0) b b' (hb : domRf ρ b b') la lb la' lb' A1 B1 A1' B1',
            lequiv (gL G0) la l' -> lequiv (gL G0) lb (lmax l l') ->
            lequiv (gL G0) la' l' -> lequiv (gL G0) lb' (lmax l l') ->
            [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ B⟦γ⟧[llift e][lsingle a] ≈ A1 @ l' ] ->
            [ kw_G ρ ; kw_Δ ρ ,, kty ρ B⟦γ⟧[llift e][lsingle a] @ l'
                ⊢ ktyl ρ (tyW l l' A⟦γ⟧[e] B⟦γ⟧[llift e])⟨↑⟩ ≈ B1 @ lmax l l' ] ->
            [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ P1 ≈ A1' @ l' ] ->
            [ kw_G ρ ; kw_Δ ρ ,, kty ρ P1 @ l' ⊢ ktyl ρ Q1 ≈ B1' @ lmax l l' ] ->
            codRf ρ b b' hb (app (ktm ρ wf) la lb A1 B1 b) (app (ktm ρ wf') la' lb' A1' B1' b')).
  { intros ρ b b' hb la lb la' lb' A1 B1 A1' B1' H1 H2 H1' H2' HA1 HB1 HA1' HB1'.
    pose proof (kw_lwf ρ Hwl'0) as Hwl'ρ. pose proof (kw_lwf ρ HwL) as HwLρ.
    (* the positions, in the codomain relation of the shapes *)
    pose proof (domAdf ρ) as DOM. rewrite kty_single in DOM.
    apply (proj2 (LogRel_stage _ _ _ _ _ _ _ (HleN l'))) in DOM.
    pose proof (HC ρ _ _ (Ha ρ)) as COD0. apply (proj2 (LogRel_stage _ _ _ _ _ _ _ Hle')) in COD0.
    pose proof (proj1 (LR_irrel _ _ _ _ _ _ _ _ _ _ DOM COD0 b b') hb) as Hbb.
    destruct (escape_tm _ _ _ _ _ _ _ _ COD0 _ _ Hbb) as (Hb & Hb' & _).
    (* the annotations, moved to the shapes' types *)
    rewrite kty_single in HA1, HB1. rewrite ktyl_shift, kty_tyW in HB1.
    pose proof (kw_geq_ty ρ HPP) as KP. rewrite kty_single in KP.
    pose proof (kw_geq_ty_l ρ HBa Hwl'0 HQQ) as KQ. rewrite kty_single, ktyl_shift, kty_tyW in KQ.
    pose proof (kw_ty ρ HBa) as HBaρ. rewrite kty_single in HBaρ.
    assert (HA1'x : [ kw_G ρ ; kw_Δ ρ ⊢ (ktyl ρ B⟦γ⟧[llift e])[lsingle (ktm ρ a)] ≈ A1' @ l' ])
      by exact (geq_ty_trans KP HA1').
    assert (HB1'x : [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ B⟦γ⟧[llift e])[lsingle (ktm ρ a)] @ l'
                      ⊢ (tyW l l' (kty ρ A⟦γ⟧[e]) (ktyl ρ B⟦γ⟧[llift e]))⟨↑⟩ ≈ B1' @ lmax l l' ]).
    { eapply geq_ty_trans; [exact KQ|].
      eapply geq_ty_ctxconv; [apply eqty_sym, geq_ty_sound, KP | now apply lequiv_refl
                             | apply ext_wf_g; [exact HBaρ | exact Hwl'ρ] | exact HB1']. }
    (* the children, by the tree's premise, then at the whnfs of the functions *)
    pose proof (Hf ρ (Ha ρ) b b' Hbb la lb A1 B1 la' lb' A1' B1' H1 H2 H1' H2' HA1 HB1 HA1'x HB1'x) as Y.
    pose proof (kw_ty_l ρ HBa Hwl'0 HWu) as HWuρ. rewrite kty_single, ktyl_shift, kty_tyW in HWuρ.
    pose proof (kw_tmred ρ Hr) as Rρ. rewrite kty_fty in Rρ.
    pose proof (kw_tmred ρ Hr') as Rρ'. rewrite kty_fty in Rρ'.
    assert (NWρ : nfty (tyW l l' (kty ρ A⟦γ⟧[e]) (ktyl ρ B⟦γ⟧[llift e]))).
    { cbn; split; [exact (wf_ty_nf (kw_ty ρ HA0)) | exact (wf_ty_nf (kw_ty_l ρ HA0 Hwl0 HB0))]. }
    pose proof (tmred_app_annot Hwl'ρ HwLρ (kw_lequiv ρ H1) (kw_lequiv ρ H2) HBaρ HWuρ Hb
                  (geq_ty_sound HA1) (geq_ty_sound HB1) Rρ) as Yr.
    pose proof (tmred_app_annot Hwl'ρ HwLρ (kw_lequiv ρ H1') (kw_lequiv ρ H2') HBaρ HWuρ Hb'
                  (geq_ty_sound HA1'x) (geq_ty_sound HB1'x) Rρ') as Yr'.
    rewrite shift_single_ty in Yr, Yr' by exact NWρ.
    pose proof (WRel_red_fwd Y Yr Yr') as Y'.
    (* the codomain relation is [WRel], at the composed data *)
    pose proof (codAdf ρ b b' hb) as COD. rewrite ktyl_shift, kty_tyW, shift_single_ty in COD by exact NWρ.
    apply (proj2 (LogRel_stage _ _ _ _ _ _ _ HleL)) in COD.
    destruct (escape_ty _ _ _ _ _ _ _ _ COD) as (HWρ & _ & _).
    destruct (LR_inv_W COD (tyred_refl _ _ HWρ)) as (j3 & j4 & C3 & D3 & domR1 & codR1 & _ & domAd1 & codAd1 & HR1).
    apply (proj2 (HR1 _ _)).
    assert (D2 : forall ρ' : kwk (kw_G ρ) (kw_Δ ρ),
               LR (lmeasure (lmax l l')) (LRbelow (lmeasure (lmax l l'))) (kw_G ρ') (kw_Δ ρ')
                 (kty ρ' (kty ρ A⟦γ⟧[e])) (kty ρ' (kty ρ A⟦γ⟧[e'])) l (dR (kw_comp ρ ρ'))).
    { intros ρ'. pose proof (HD (kw_comp ρ ρ')) as Z. rewrite !kty_comp in Z. exact Z. }
    assert (C2 : forall (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) x y (h : dR (kw_comp ρ ρ') x y),
               LR (lmeasure (lmax l l')) (LRbelow (lmeasure (lmax l l'))) (kw_G ρ') (kw_Δ ρ')
                 (ktyl ρ' (ktyl ρ B⟦γ⟧[llift e]))[lsingle x] (ktyl ρ' (ktyl ρ B⟦γ⟧[llift e']))[lsingle y] l'
                 (cR (kw_comp ρ ρ') x y h)).
    { intros ρ' x y h. pose proof (HC (kw_comp ρ ρ') x y h) as Z. rewrite !ktyl_comp in Z. exact Z. }
    exact (proj1 (WRel_canon D2 C2 domAd1 codAd1 _ _) Y'). }
  assert (PRf : PiRel G0 Δ0 l' (lmax l l') n3 n4 B⟦γ⟧[llift e][lsingle a] (tyW l l' A⟦γ⟧[e] B⟦γ⟧[llift e])⟨↑⟩
                  P1 Q1 domRf codRf f f').
  { exists wf, wf'. refine (conj Hr (conj _ (conj Nwf (conj Nwf' (conj Ewf (conj _ Kf)))))).
    - eapply tmred_conv; [apply ge_typeof | exact Hr' | exact EPi].
    - eapply geq_tm_conv; [exact Ewf | exact EPi]. }
  pose proof (LRtm_of HRF (proj2 (HRRf f f') PRf)) as Xf.
  pose proof (LRtm_geq Xf) as Ef. destruct (LRtm_escape Xf) as [Hft Hf't].
  (* the synthesized induction hypotheses, related at the [ih] entry's type *)
  assert (Xf0 : LRtm (lmax l' (lmax l l')) G0 Δ0 (wfty l l' A⟦γ⟧ B⟦γ⟧)[lcons e a]
                  (wfty l l' A⟦γ⟧ B⟦γ⟧)[lcons e' a'] f f').
  { rewrite <- (lift_single_ty _ e a Ne), <- (lift_single_ty _ e' a' Ne'), (wfty_llift e), (wfty_llift e'), !W_E5.
    exact Xf. }
  pose proof (SubRel_cons HS1 Xf0) as HS2.
  destruct (Vihγ _ _ _ HS2) as [RI HRI].
  rewrite <- (lift_single2_ty e Ne _ a f), <- (lift_single2_ty e' Ne' _ a' f'), !wihty_llift2, !W_E4 in HRI
    by assumption.
  destruct (escape_ty _ _ _ _ _ _ _ _ HRI) as (HIT & _ & _).
  destruct (LR_inv_pi HRI (tyred_refl _ _ HIT)) as (p3 & p4 & P2 & Q2 & domRi & codRi & Pi & domAdi & codAdi & HRRi).
  destruct Pi as [_ Hp3 Hp4 _ _ _ _ HBa2 HP2 HCod HQ2 HPP2 HQQ2].
  pose proof (lequiv_weaken _ _ _ _ (proj1 Hγ) H14) as H14'.
  pose proof (lequiv_weaken _ _ _ _ (proj1 Hγ) H25) as H25'.
  pose proof (lequiv_weaken _ _ _ _ (proj1 Hγ) H36) as H36'.
  pose proof (W_IH_eq ge_typeof ge_notV Hwl0 Hwl'0 Hwl''0 H14' H25' H36' HA0 (geq_ty_sound EA) HB0
                (geq_ty_sound EB) HM0 (geq_ty_sound EM) (geq_tm_sound Ec) Hat Ha't (geq_tm_sound Ea)
                (geq_tm_sound Ef)) as Dih.
  pose proof (W_IH_body_eq ge_typeof ge_notV Hwl0 Hwl'0 Hwl''0 H14' H25' H36' HA0 (geq_ty_sound EA) HB0
                (geq_ty_sound EB) HM0 (geq_ty_sound EM) (geq_tm_sound Ec) Hat Ha't (geq_tm_sound Ea)
                (geq_tm_sound Ef)) as Dbody.
  rewrite W_E4 in Dih.
  pose proof (eqtm_wf_l ge_typeof Dbody) as Hbody. pose proof (eqtm_wf_r ge_typeof Dbody) as Hbody'.
  (* the shapes' types at the positions, left and right *)
  destruct (VTyG_loc VBγ _ _ _ HS1) as [RBa HRBa]. destruct (escape_ty _ _ _ _ _ _ _ _ HRBa) as (_ & HB'a & EBa).
  rewrite <- (lift_single_ty _ e' a' Ne') in HB'a.
  rewrite <- (lift_single_ty _ e a Ne), <- (lift_single_ty _ e' a' Ne') in EBa.
  pose proof (geq_ty_W H14' H25' HA0 EA EB) as EW0.
  assert (HleI : lmeasure l' <= lmeasure (lmax l' l'')) by (rewrite !lmeasure_max; lia).
  assert (HleI' : lmeasure l'' <= lmeasure (lmax l' l'')) by (rewrite !lmeasure_max; lia).
  pose proof (lequiv_wf_r _ _ _ H25') as Hwl5. pose proof (lequiv_wf_r _ _ _ H36') as Hwl6.
  assert (HB'a5 : [ G0 ; Δ0 ⊢g B'⟦γ⟧[llift e'][lsingle a'] @ l5 ])
    by (eapply lconv_ty; [exact HB'a | exact H25']).
  assert (Ki : forall (ρ : kwk G0 Δ0) y y' (hy : domRi ρ y y') la lb la' lb' A1 B1 A1' B1',
            lequiv (gL G0) la l' -> lequiv (gL G0) lb l'' -> lequiv (gL G0) la' l' -> lequiv (gL G0) lb' l'' ->
            [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ B⟦γ⟧[llift e][lsingle a] ≈ A1 @ l' ] ->
            [ kw_G ρ ; kw_Δ ρ ,, kty ρ B⟦γ⟧[llift e][lsingle a] @ l'
                ⊢ ktyl ρ (wcod l l' A⟦γ⟧[e] B⟦γ⟧[llift e] M⟦γ⟧[llift e] a f) ≈ B1 @ l'' ] ->
            [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ P2 ≈ A1' @ l' ] ->
            [ kw_G ρ ; kw_Δ ρ ,, kty ρ P2 @ l' ⊢ ktyl ρ Q2 ≈ B1' @ l'' ] ->
            codRi ρ y y' hy
              (app (ktm ρ (wIH l l' l'' A⟦γ⟧[e] B⟦γ⟧[llift e] M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))] a f))
                 la lb A1 B1 y)
              (app (ktm ρ (wIH l4 l5 l6 A'⟦γ⟧[e'] B'⟦γ⟧[llift e'] M'⟦γ⟧[llift e'] c'⟦γ⟧[llift (llift (llift e'))] a' f'))
                 la' lb' A1' B1' y')).
  { intros ρ y y' hy la lb la' lb' A1 B1 A1' B1' H1 H2 H1' H2' HA1 HB1 HA1' HB1'.
    pose proof (kw_lwf ρ Hwl'0) as Hwl'ρ. pose proof (kw_lwf ρ Hwl''0) as Hwl''ρ.
    pose proof (kw_lwf ρ HwL) as HwLρ.
    (* the positions, in the shapes' codomain relation *)
    pose proof (domAdi ρ) as DOM. rewrite kty_single in DOM.
    apply (proj2 (LogRel_stage _ _ _ _ _ _ _ HleI)) in DOM.
    pose proof (HC ρ _ _ (Ha ρ)) as COD0. apply (proj2 (LogRel_stage _ _ _ _ _ _ _ Hle')) in COD0.
    pose proof (proj1 (LR_irrel _ _ _ _ _ _ _ _ _ _ DOM COD0 y y') hy) as Hyy.
    destruct (escape_tm _ _ _ _ _ _ _ _ COD0 _ _ Hyy) as (Hy & Hy' & Eyy).
    (* the children's annotations in the bodies *)
    pose proof (kw_geq_ty ρ EBa) as EBρ. rewrite !kty_single in EBρ.
    pose proof (kw_ty ρ HBa2) as HBaρ. rewrite kty_single in HBaρ.
    assert (EWρ : [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ B⟦γ⟧[llift e])[lsingle (ktm ρ a)] @ l'
                    ⊢ (tyW l l' (kty ρ A⟦γ⟧[e]) (ktyl ρ B⟦γ⟧[llift e]))⟨↑⟩
                      ≈ (tyW l4 l5 (kty ρ A'⟦γ⟧[e']) (ktyl ρ B'⟦γ⟧[llift e']))⟨↑⟩ @ lmax l l' ]).
    { pose proof (kw_geq_ty ρ EW0) as Z. rewrite !kty_tyW in Z.
      exact (geq_ty_wk (wkr_shift1 _ _ _) (ext_wf_g HBaρ Hwl'ρ) Z). }
    pose proof (IH ρ (Ha ρ) y y' Hyy l' (lmax l l') ((ktyl ρ B⟦γ⟧[llift e])[lsingle (ktm ρ a)])
                  ((tyW l l' (kty ρ A⟦γ⟧[e]) (ktyl ρ B⟦γ⟧[llift e]))⟨↑⟩)
                  l5 (lmax l4 l5) ((ktyl ρ B'⟦γ⟧[llift e'])[lsingle (ktm ρ a')])
                  ((tyW l4 l5 (kty ρ A'⟦γ⟧[e']) (ktyl ρ B'⟦γ⟧[llift e']))⟨↑⟩)
                  (lequiv_refl _ _ Hwl'0) (lequiv_refl _ _ HwL) (lequiv_sym _ _ _ H25')
                  (lequiv_sym _ _ _ (lequiv_max _ _ _ _ _ H14' H25'))
                  (geq_ty_trans EBρ (geq_ty_sym EBρ)) (geq_ty_trans EWρ (geq_ty_sym EWρ)) EBρ EWρ) as IH1.
    assert (He1 : SubRel (kw_G ρ) Γ⟦gwk_comp (kw_γ ρ) γ⟧ (kw_Δ ρ) (kwsub ρ e) (kwsub ρ e')).
    { pose proof (SubRel_kw _ _ _ ρ _ _ He) as Z. now rewrite gwa_comp_ctx in Z. }
    assert (D2 : forall ρ' : kwk (kw_G ρ) (kw_Δ ρ),
               LR (lmeasure (lmax l l')) (LRbelow (lmeasure (lmax l l'))) (kw_G ρ') (kw_Δ ρ')
                 (kty ρ' (kty ρ A⟦γ⟧[e])) (kty ρ' A⟦gwk_comp (kw_γ ρ) γ⟧[kwsub ρ e']) l (dR (kw_comp ρ ρ'))).
    { intros ρ'. pose proof (HD (kw_comp ρ ρ')) as Z. rewrite !kty_comp, (kγ_ty ρ A γ e') in Z. exact Z. }
    assert (C2 : forall (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) x x' (h : dR (kw_comp ρ ρ') x x'),
               LR (lmeasure (lmax l l')) (LRbelow (lmeasure (lmax l l'))) (kw_G ρ') (kw_Δ ρ')
                 (ktyl ρ' (ktyl ρ B⟦γ⟧[llift e]))[lsingle x]
                 (ktyl ρ' B⟦gwk_comp (kw_γ ρ) γ⟧[llift (kwsub ρ e')])[lsingle x'] l'
                 (cR (kw_comp ρ ρ') x x' h)).
    { intros ρ' x x' h. pose proof (HC (kw_comp ρ ρ') x x' h) as Z. rewrite !ktyl_comp, (kγ_tyl ρ B γ e') in Z.
      exact Z. }
    pose proof (IH1 (gwk_comp (kw_γ ρ) γ) (kwsub ρ e) (kwsub ρ e') (gwk_ok_comp (kw_gok ρ) Hγ) He1
                  eq_refl eq_refl (kγ_ty ρ A γ e) (kγ_tyl ρ B γ e) D2 C2) as X.
    rewrite <- (kγ_tyl ρ M γ e), <- (kγ_tm3 ρ c γ e), <- (kγ_ty ρ A' γ e'), <- (kγ_tyl ρ B' γ e'),
      <- (kγ_tyl ρ M' γ e'), <- (kγ_tm3 ρ c' γ e') in X.
    (* the λs' codomain relation, at the children's elimination *)
    pose proof (eqty_wf_l ge_typeof (geq_ty_sound EW0)) as HWd.
    assert (NAρ : nfty (kty ρ A⟦γ⟧[e])) by apply ren_nf_ty.
    assert (NBρ : nfty (ktyl ρ B⟦γ⟧[llift e])) by apply ren_nf_ty.
    assert (NMρ : nfty (ktyl ρ M⟦γ⟧[llift e])) by apply ren_nf_ty.
    assert (Naρ : nftm (ktm ρ a)) by apply ren_nf. assert (Nfρ : nftm (ktm ρ f)) by apply ren_nf.
    assert (Ncρ : nftm (ktm3 ρ c⟦γ⟧[llift (llift (llift e))])) by apply ren_nf.
    pose proof (wf_tm_nf Hy) as Ny. pose proof (wf_tm_nf Hy') as Ny'.
    pose proof (codAdi ρ y y' hy) as COD. apply LR_refl_l in COD.
    rewrite ktyl_wcod, wcod_single in COD by assumption.
    pose proof (LRtm_inv (proj2 (LogRel_stage _ _ _ _ _ _ _ HleI') COD) X) as Rx.
    apply (LR_red_tm _ _ _ _ _ _ _ _ COD _ _ _ _ Rx).
    - (* the left λ steps to the children's elimination *)
      unfold wIH. rewrite ktm_lam, ktml_wbody, kty_single.
      pose proof (kw_tm_l ρ HBa2 Hwl'0 Hbody) as Hbρ. rewrite kty_single, ktml_wbody, ktyl_wcod in Hbρ.
      pose proof (kw_ty_l ρ HBa2 Hwl'0 HCod) as HCρ. rewrite kty_single, ktyl_wcod in HCρ.
      rewrite kty_single in HA1. rewrite kty_single, ktyl_wcod in HB1.
      pose proof (tmred_beta Hwl'ρ Hwl''ρ (kw_lequiv ρ H1) (kw_lequiv ρ H2) HBaρ HCρ Hbρ Hy
                    (geq_ty_sound HA1) (geq_ty_sound HB1)) as Z.
      rewrite wbody_single, wcod_single in Z by assumption. exact Z.
    - (* the right λ too, its body moved to the left domain's type *)
      unfold wIH. rewrite ktm_lam, ktml_wbody, kty_single.
      pose proof (kw_lwf ρ Hwl5) as Hwl5ρ. pose proof (kw_lwf ρ Hwl6) as Hwl6ρ.
      pose proof (kw_lequiv ρ H25') as H25ρ. pose proof (kw_lequiv ρ H36') as H36ρ.
      assert (HΔ5 : [ G0 ; Δ0 ,, B'⟦γ⟧[llift e'][lsingle a'] @ l5 ⊢g ]) by exact (ext_wf_g HB'a5 Hwl5).
      pose proof (stab_tm ge_typeof (geq_ty_sound EBa) H25' HΔ5 Hbody') as Hb'.
      apply (fun H => wf_lconv _ _ _ _ _ _ _ H (lequiv_sym _ _ _ H36')) in Hb'.
      pose proof (kw_tm_l ρ HB'a5 Hwl5 Hb') as Hb'ρ. rewrite kty_single, ktml_wbody, ktyl_wcod in Hb'ρ.
      pose proof (stab_ty ge_typeof (geq_ty_sound EBa) H25' HΔ5 HCod) as HC'.
      apply (fun H => lconv_ty H H36') in HC'.
      pose proof (kw_ty_l ρ HB'a5 Hwl5 HC') as HC'ρ. rewrite kty_single, ktyl_wcod in HC'ρ.
      pose proof (kw_ty ρ HB'a5) as HB'aρ. rewrite kty_single in HB'aρ.
      assert (Hy'5 : [ kw_G ρ ; kw_Δ ρ ⊢g y' : (ktyl ρ B'⟦γ⟧[llift e'])[lsingle (ktm ρ a')] @ l5 ]).
      { eapply wf_lconv; [eapply wf_conv; [exact Hy' | rewrite ge_typeof; apply eqty_sym, geq_ty_sound, EBρ]
                         | exact (lequiv_sym _ _ _ H25ρ)]. }
      pose proof (kw_geq_ty ρ HPP2) as KP2. rewrite kty_single in KP2.
      assert (HA1c : [ kw_G ρ ; kw_Δ ρ ⊢g (ktyl ρ B'⟦γ⟧[llift e'])[lsingle (ktm ρ a')] ≅ A1' @ l5 ]).
      { eapply eqty_lconv; [|exact (lequiv_sym _ _ _ H25ρ)].
        apply geq_ty_sound. eapply geq_ty_trans; [apply geq_ty_sym, EBρ|]. exact (geq_ty_trans KP2 HA1'). }
      pose proof (kw_geq_ty_l ρ HBa2 Hwl'0 HQQ2) as KQ2. rewrite kty_single, ktyl_wcod in KQ2.
      assert (HB1c : [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ B'⟦γ⟧[llift e'])[lsingle (ktm ρ a')] @ l5
                       ⊢g wcod l l' (kty ρ A⟦γ⟧[e]) (ktyl ρ B⟦γ⟧[llift e]) (ktyl ρ M⟦γ⟧[llift e]) (ktm ρ a) (ktm ρ f)
                          ≅ B1' @ l6 ]).
      { eapply eqty_lconv; [|exact (lequiv_sym _ _ _ H36ρ)].
        eapply (stab_eqty ge_typeof (geq_ty_sound EBρ) H25ρ (ext_wf_g HB'aρ Hwl5ρ)).
        apply geq_ty_sound. eapply geq_ty_trans; [exact KQ2|].
        eapply geq_ty_ctxconv; [apply eqty_sym, geq_ty_sound, KP2 | now apply lequiv_refl
                               | apply ext_wf_g; [exact HBaρ | exact Hwl'ρ] | exact HB1']. }
      pose proof (tmred_beta Hwl5ρ Hwl6ρ (kw_lequiv ρ (lequiv_trans _ _ _ _ H1' H25'))
                    (kw_lequiv ρ (lequiv_trans _ _ _ _ H2' H36')) HB'aρ HC'ρ Hb'ρ Hy'5 HA1c HB1c) as Z.
      assert (NA'ρ : nfty (kty ρ A'⟦γ⟧[e'])) by apply ren_nf_ty.
      assert (NB'ρ : nfty (ktyl ρ B'⟦γ⟧[llift e'])) by apply ren_nf_ty.
      assert (NM'ρ : nfty (ktyl ρ M'⟦γ⟧[llift e'])) by apply ren_nf_ty.
      assert (Na'ρ : nftm (ktm ρ a')) by apply ren_nf. assert (Nf'ρ : nftm (ktm ρ f')) by apply ren_nf.
      assert (Nc'ρ : nftm (ktm3 ρ c'⟦γ⟧[llift (llift (llift e'))])) by apply ren_nf.
      rewrite wbody_single, wcod_single in Z by assumption.
      pose proof (kw_ty_l ρ HBa2 Hwl'0 HCod) as HCρ. rewrite kty_single, ktyl_wcod in HCρ.
      pose proof (wf_ty_func ge_typeof HCρ (lsub_eq_single ge_typeof Hy' Hy (eqtm_sym _ _ _ _ _ _ _ (geq_tm_sound Eyy))))
        as Ecod.
      rewrite !wcod_single in Ecod by assumption.
      eapply tmred_lconv; [eapply tmred_conv; [apply ge_typeof | exact Z |] | exact H36ρ].
      eapply eqty_lconv; [exact Ecod | exact (lequiv_sym _ _ _ H36ρ)]. }
  (* the λs, generically equal by extensionality at the position *)
  assert (EPi2 : [ G0 ; Δ0 ⊢g tyPi l' l'' B⟦γ⟧[llift e][lsingle a] (wcod l l' A⟦γ⟧[e] B⟦γ⟧[llift e] M⟦γ⟧[llift e] a f)
                     ≅ tyPi p3 p4 P2 Q2 @ lmax l' l'' ])
    by (apply geq_ty_sound, geq_ty_pi; auto using lequiv_sym).
  pose proof (eqtm_wf_l ge_typeof Dih) as Hλ. pose proof (eqtm_wf_r ge_typeof Dih) as Hλ'.
  assert (Hw1 : wk1 : (Δ0 ,, B⟦γ⟧[llift e][lsingle a] @ l') ≤ Δ0) by (constructor; constructor).
  assert (Hr1 : wkr ↑ (Δ0 ,, B⟦γ⟧[llift e][lsingle a] @ l') Δ0) by exact (wkr_shift1 _ _ _).
  pose proof (ext_wf_g HBa2 Hwl'0) as HΔa.
  pose proof (domAdi (kw_loc wk1 Hw1 HΔa)) as DOM1.
  unfold kty, kw_loc in DOM1; cbn [kw_G kw_Δ kw_γ kw_r gwa] in DOM1; change (wk_ren wk1) with ↑ in DOM1.
  apply (proj2 (LogRel_stage _ _ _ _ _ _ _ HleI)) in DOM1.
  pose proof (LRtm_inv DOM1 (var0_LRtm (ex_intro _ _ DOM1) HΔa)) as hv.
  assert (RBa0 : [ G0 ; Δ0 ⊢ B⟦γ⟧[llift e][lsingle a] ≈ B⟦γ⟧[llift e][lsingle a] @ l' ])
    by exact (geq_ty_trans HPP2 (geq_ty_sym HPP2)).
  assert (RCod : [ G0 ; Δ0 ,, B⟦γ⟧[llift e][lsingle a] @ l'
                   ⊢ wcod l l' A⟦γ⟧[e] B⟦γ⟧[llift e] M⟦γ⟧[llift e] a f
                     ≈ wcod l l' A⟦γ⟧[e] B⟦γ⟧[llift e] M⟦γ⟧[llift e] a f @ l'' ])
    by exact (geq_ty_trans HQQ2 (geq_ty_sym HQQ2)).
  assert (HΔaa : [ G0 ; Δ0 ,, B⟦γ⟧[llift e][lsingle a] @ l' ,, B⟦γ⟧[llift e][lsingle a]⟨↑⟩ @ l' ⊢g ])
    by (apply ext_wf_g; [exact (wf_ty_wkr Hr1 HΔa HBa2) | exact Hwl'0]).
  assert (HΔaP : [ G0 ; Δ0 ,, B⟦γ⟧[llift e][lsingle a] @ l' ,, P2⟨↑⟩ @ l' ⊢g ])
    by (apply ext_wf_g; [exact (wf_ty_wkr Hr1 HΔa HP2) | exact Hwl'0]).
  pose proof (Ki (kw_loc wk1 Hw1 HΔa) (var 0) (var 0) hv l' l'' l' l''
                B⟦γ⟧[llift e][lsingle a]⟨↑⟩ (wcod l l' A⟦γ⟧[e] B⟦γ⟧[llift e] M⟦γ⟧[llift e] a f)⟨rlift ↑⟩
                B⟦γ⟧[llift e][lsingle a]⟨↑⟩ (wcod l l' A⟦γ⟧[e] B⟦γ⟧[llift e] M⟦γ⟧[llift e] a f)⟨rlift ↑⟩
                (lequiv_refl _ _ Hwl'0) (lequiv_refl _ _ Hwl''0) (lequiv_refl _ _ Hwl'0) (lequiv_refl _ _ Hwl''0))
    as K0.
  unfold kty, ktyl, ktm, kw_loc in K0; cbn [kw_G kw_Δ kw_γ kw_r gwa] in K0; change (wk_ren wk1) with ↑ in K0.
  pose proof (K0 (geq_ty_wk Hr1 HΔa RBa0) (geq_ty_wk (wkr_up _ _ _ _ _ Hr1) HΔaa RCod)
                (geq_ty_wk Hr1 HΔa (geq_ty_sym HPP2))) as K1.
  unshelve epose proof (K1 _) as K2.
  { eapply geq_ty_ctxconv; [| apply lequiv_refl, Hwl'0 | exact HΔaP |].
    - apply geq_ty_sound. exact (geq_ty_wk Hr1 HΔa HPP2).
    - apply geq_ty_sym. exact (geq_ty_wk (wkr_up _ _ _ _ _ Hr1) HΔaa HQQ2). }
  pose proof (codAdi (kw_loc wk1 Hw1 HΔa) (var 0) (var 0) hv) as COD1.
  unfold ktyl, kw_loc in COD1; cbn [kw_G kw_Δ kw_γ kw_r gwa] in COD1; change (wk_ren wk1) with ↑ in COD1.
  destruct (escape_tm _ _ _ _ _ _ _ _ COD1 _ _ K2) as (_ & _ & Hg).
  rewrite liftshift_single_var_ty in Hg by exact (wf_ty_nf HCod).
  pose proof (geq_tm_funext Hwl'0 Hwl''0 HBa2 HCod Hλ Hλ' Hg) as GEQ.
  assert (PRih : PiRel G0 Δ0 l' l'' p3 p4 B⟦γ⟧[llift e][lsingle a]
                   (wcod l l' A⟦γ⟧[e] B⟦γ⟧[llift e] M⟦γ⟧[llift e] a f) P2 Q2 domRi codRi
                   (wIH l l' l'' A⟦γ⟧[e] B⟦γ⟧[llift e] M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))] a f)
                   (wIH l4 l5 l6 A'⟦γ⟧[e'] B'⟦γ⟧[llift e'] M'⟦γ⟧[llift e'] c'⟦γ⟧[llift (llift (llift e'))] a' f')).
  { eexists _, _. refine (conj (tmred_refl _ _ _ Hλ) (conj _ (conj _ (conj _ (conj GEQ (conj _ Ki)))))).
    - apply tmred_refl. eapply wf_conv; [exact Hλ' | rewrite ge_typeof; apply eqty_sym, EPi2].
    - unfold wIH; apply whnf_lam.
    - unfold wIH; apply whnf_lam.
    - eapply geq_tm_conv; [exact GEQ | exact EPi2]. }
  pose proof (LRtm_of HRI (proj2 (HRRi _ _) PRih)) as Xh.
  (* the step, at the shape, the child function and the induction hypothesis *)
  assert (Xh0 : LRtm (lmax l' l'') G0 Δ0 (wihty l l' l'' A⟦γ⟧ B⟦γ⟧ M⟦γ⟧)[lcons (lcons e a) f]
                  (wihty l l' l'' A⟦γ⟧ B⟦γ⟧ M⟦γ⟧)[lcons (lcons e' a') f']
                  (wIH l l' l'' A⟦γ⟧[e] B⟦γ⟧[llift e] M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))] a f)
                  (wIH l4 l5 l6 A'⟦γ⟧[e'] B'⟦γ⟧[llift e'] M'⟦γ⟧[llift e'] c'⟦γ⟧[llift (llift (llift e'))] a' f')).
  { rewrite <- (lift_single2_ty e Ne _ a f), <- (lift_single2_ty e' Ne' _ a' f'), !wihty_llift2, !W_E4
      by assumption.
    exact Xh. }
  pose proof (Vcγ _ _ _ (SubRel_cons HS2 Xh0)) as Xc.
  rewrite <- (lift_single3_ty e Ne), <- (lift_single3_ty e' Ne'), <- (lift_single3 e Ne), <- (lift_single3 e' Ne'),
    !wstepty_llift3, !W_E6 in Xc by first [assumption | exact (wf_ty_nf HA0') | exact (wf_ty_nf HB'a)].
  (* the [sup] at the [elim_W]'s annotations, related to the trees *)
  destruct (elimW_WLR Hγ (SubRel_refl_l He)) as (HWee & Hdee & Hcee).
  pose proof (WRel_canon HD HC Hdee Hcee) as Canon.
  destruct (LR_tm_per _ _ _ _ _ _ _ HWee) as [Sy Tr].
  pose proof (geq_tm_refl_l Ea) as Eaa. pose proof (geq_tm_refl_l Ef) as Eff.
  assert (RAA : [ G0 ; Δ0 ⊢ A⟦γ⟧[e] ≈ A⟦γ⟧[e] @ l ]) by exact (geq_ty_trans EA (geq_ty_sym EA)).
  assert (RBB : [ G0 ; Δ0 ,, A⟦γ⟧[e] @ l ⊢ B⟦γ⟧[llift e] ≈ B⟦γ⟧[llift e] @ l' ])
    by exact (geq_ty_trans EB (geq_ty_sym EB)).
  pose proof (geq_tm_sup (lequiv_sym _ _ _ Hk1) (lequiv_sym _ _ _ Hk2) HA0 HC0 HB0 HD0 Eaa Eff) as Dw.
  pose proof (geq_tm_sup (lequiv_sym _ _ _ Hk1') (lequiv_sym _ _ _ Hk2') HA0 HC0' HB0 HD0' Ea Ef) as Dw'.
  pose proof (geq_tm_trans (geq_tm_sym Dw) Dw') as Dww'.
  pose proof (eqtm_wf_l ge_typeof (geq_tm_sound Dw)) as Hsc. pose proof (eqtm_wf_r ge_typeof (geq_tm_sound Dw)) as Hw0.
  pose proof (eqtm_wf_r ge_typeof (geq_tm_sound Dw')) as Hw0'.
  assert (Nsup : WNf G0 Δ0 l l' A⟦γ⟧[e] B⟦γ⟧[llift e] dR cR
                   (tmSup l l' A⟦γ⟧[e] B⟦γ⟧[llift e] a f) (tmSup m1' m2' C' D' a' f'))
    by (apply wnf_sup; first [now apply lequiv_refl | assumption]).
  assert (Nww : WNf G0 Δ0 l l' A⟦γ⟧[e] B⟦γ⟧[llift e] dR cR
                  (tmSup m1 m2 C D a f) (tmSup m1' m2' C' D' a' f'))
    by (apply wnf_sup; assumption).
  pose proof (proj1 (Canon _ _) (wrel _ _ _ _ _ _ _ _ _ _ _ _ (tmred_refl _ _ _ Hsc) (tmred_refl _ _ _ Hw0') Dw' Nsup))
    as Rsw'.
  pose proof (proj1 (Canon _ _) (wrel _ _ _ _ _ _ _ _ _ _ _ _ (tmred_refl _ _ _ Hw0) (tmred_refl _ _ _ Hw0') Dww' Nww))
    as Rww'.
  pose proof (Tr _ _ _ Rsw' (Sy _ _ Rww')) as Rsw. pose proof (Tr _ _ _ Rww' (Sy _ _ Rww')) as Rww.
  pose proof (elimW_mot Hγ (SubRel_refl_l He) (LRtm_of HWee Rsw)) as XTsw.
  pose proof (elimW_mot Hγ (SubRel_refl_l He) (LRtm_of HWee Rww)) as XTww.
  pose proof (LRtm_irrel_r (LRtm_conv_l Xc (LRty_sym XTsw)) XTww) as X2.
  (* both sides step to the step *)
  pose proof (eqtm_wf_l ge_typeof (geq_tm_sound Ec)) as Hc0.
  pose proof (eqtm_elimW_sup _ _ _ _ _ _ _ _ _ _ _ _ ge_compt Hwl0 Hwl'0 Hwl''0 HA0 HB0 HM0 HF0 HI0 Hc0 Hat Hft)
    as Beta.
  destruct XTsw as [RS HRS]. destruct (escape_ty _ _ _ _ _ _ _ _ HRS) as (_ & _ & ESW).
  pose proof (elimW_cong_l Hγ He (eqtm_sym _ _ _ _ _ _ _ (geq_tm_sound Dw))) as Cw.
  assert (Leq : [ G0 ; Δ0 ⊢g tmElimW l l' l'' A⟦γ⟧[e] B⟦γ⟧[llift e] M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))]
                               (tmSup m1 m2 C D a f)
                  ≅ c⟦γ⟧[llift (llift (llift e))][lsingle3 a f
                      (wIH l l' l'' A⟦γ⟧[e] B⟦γ⟧[llift e] M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))] a f)]
                  : M⟦γ⟧[llift e][lsingle (tmSup m1 m2 C D a f)] @ l'' ]).
  { eapply eqtm_trans; [exact Cw|]. eapply eqtm_conv; [exact Beta | rewrite ge_typeof; apply eqty_sym, geq_ty_sound, ESW]. }
  pose proof (elimW_cong Hγ He (geq_tm_sound Dww')) as Cww'.
  refine (conj X2 (conj _ _)).
  + split; [exact (eqtm_wf_l ge_typeof Leq) | econstructor; [apply red_elimW_sup | constructor] | exact Leq].
  + split; [exact (eqtm_wf_r ge_typeof Cww') | econstructor; [apply red_elimW_sup | constructor] |].
    eapply eqtm_trans; [apply eqtm_sym, Cww'|]. eapply eqtm_trans; [exact Leq|].
    exact (geq_tm_sound (LRtm_geq X2)).
Qed.


Lemma elimW_core :
  forall G0 Δ0 k1 k2 A0 B0 (dR : DomRel G0 Δ0) (cR : CodRel G0 Δ0 dR) t t',
  WRel G0 Δ0 k1 k2 A0 B0 dR cR t t' ->
  forall γ e e', gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' ->
  k1 = l -> k2 = l' -> A0 = A⟦γ⟧[e] -> B0 = B⟦γ⟧[llift e] ->
  (forall ρ : kwk G0 Δ0, LR (lmeasure (lmax l l')) (LRbelow (lmeasure (lmax l l'))) (kw_G ρ) (kw_Δ ρ)
     (kty ρ A0) (kty ρ A⟦γ⟧[e']) l (dR ρ)) ->
  (forall (ρ : kwk G0 Δ0) x y h, LR (lmeasure (lmax l l')) (LRbelow (lmeasure (lmax l l'))) (kw_G ρ) (kw_Δ ρ)
     (ktyl ρ B0)[lsingle x] (ktyl ρ B⟦γ⟧[llift e'])[lsingle y] l' (cR ρ x y h)) ->
  LRtm l'' G0 Δ0 M⟦γ⟧[llift e][lsingle t] M⟦γ⟧[llift e][lsingle t]
    (tmElimW l l' l'' A0 B0 M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))] t)
    (tmElimW l4 l5 l6 A'⟦γ⟧[e'] B'⟦γ⟧[llift e'] M'⟦γ⟧[llift e'] c'⟦γ⟧[llift (llift (llift e'))] t').
Proof.
  apply (WRel_mut
    (fun G0 Δ0 k1 k2 A0 B0 dR cR t t' _ =>
      forall γ e e', gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' ->
      k1 = l -> k2 = l' -> A0 = A⟦γ⟧[e] -> B0 = B⟦γ⟧[llift e] ->
      (forall ρ : kwk G0 Δ0, LR (lmeasure (lmax l l')) (LRbelow (lmeasure (lmax l l'))) (kw_G ρ) (kw_Δ ρ)
         (kty ρ A0) (kty ρ A⟦γ⟧[e']) l (dR ρ)) ->
      (forall (ρ : kwk G0 Δ0) x y h, LR (lmeasure (lmax l l')) (LRbelow (lmeasure (lmax l l'))) (kw_G ρ) (kw_Δ ρ)
         (ktyl ρ B0)[lsingle x] (ktyl ρ B⟦γ⟧[llift e'])[lsingle y] l' (cR ρ x y h)) ->
      LRtm l'' G0 Δ0 M⟦γ⟧[llift e][lsingle t] M⟦γ⟧[llift e][lsingle t]
        (tmElimW l l' l'' A0 B0 M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))] t)
        (tmElimW l4 l5 l6 A'⟦γ⟧[e'] B'⟦γ⟧[llift e'] M'⟦γ⟧[llift e'] c'⟦γ⟧[llift (llift (llift e'))] t'))
    (fun G0 Δ0 k1 k2 A0 B0 dR cR t t' _ =>
      forall γ e e', gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' -> nftm t -> nftm t' ->
      k1 = l -> k2 = l' -> A0 = A⟦γ⟧[e] -> B0 = B⟦γ⟧[llift e] ->
      (forall ρ : kwk G0 Δ0, LR (lmeasure (lmax l l')) (LRbelow (lmeasure (lmax l l'))) (kw_G ρ) (kw_Δ ρ)
         (kty ρ A0) (kty ρ A⟦γ⟧[e']) l (dR ρ)) ->
      (forall (ρ : kwk G0 Δ0) x y h, LR (lmeasure (lmax l l')) (LRbelow (lmeasure (lmax l l'))) (kw_G ρ) (kw_Δ ρ)
         (ktyl ρ B0)[lsingle x] (ktyl ρ B⟦γ⟧[llift e'])[lsingle y] l' (cR ρ x y h)) ->
      LRtm l'' G0 Δ0 M⟦γ⟧[llift e][lsingle t] M⟦γ⟧[llift e][lsingle t]
        (tmElimW l l' l'' A0 B0 M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))] t)
        (tmElimW l4 l5 l6 A'⟦γ⟧[e'] B'⟦γ⟧[llift e'] M'⟦γ⟧[llift e'] c'⟦γ⟧[llift (llift (llift e'))] t'))).
  - (* a tree: through its whnfs *)
    intros G0 Δ0 k1 k2 A0 B0 dR cR t t' w w' Hw Hw' Heq Hn IH γ e e' Hγ He E1 E2 E3 E4 HD HC.
    pose proof (IH γ e e' Hγ He (wf_tm_nf (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hw)))
                  (wf_tm_nf (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hw'))) E1 E2 E3 E4 HD HC) as X.
    subst k1 k2 A0 B0.
    destruct (elimW_WLR Hγ (SubRel_refl_l He)) as (HWee & Hdee & Hcee).
    pose proof (WRel_canon HD HC Hdee Hcee) as Canon.
    destruct (LR_tm_per _ _ _ _ _ _ _ HWee) as [Sy Tr].
    pose proof (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hw)) as Hwt.
    pose proof (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hw')) as Hw't.
    assert (Hww' := proj1 (Canon w w') (wrel _ _ _ _ _ _ _ _ _ _ _ _ (tmred_refl _ _ _ Hwt) (tmred_refl _ _ _ Hw't) Heq Hn)).
    assert (Htw' := proj1 (Canon t w') (wrel _ _ _ _ _ _ _ _ _ _ _ _ Hw (tmred_refl _ _ _ Hw't) Heq Hn)).
    pose proof (Tr _ _ _ Htw' (Sy _ _ Hww')) as Htw. pose proof (Tr _ _ _ Htw (Sy _ _ Htw)) as Htt.
    pose proof (elimW_mot Hγ (SubRel_refl_l He) (LRtm_of HWee Htw)) as XT.
    pose proof (elimW_mot Hγ (SubRel_refl_l He) (LRtm_of HWee Htt)) as XTT.
    pose proof (LRtm_irrel_r (LRtm_conv_l X XT) XTT) as X2.
    assert (Htt' : [ G0 ; Δ0 ⊢g t ≅ t' : tyW l l' A⟦γ⟧[e] B⟦γ⟧[llift e] @ lmax l l' ]).
    { eapply eqtm_trans; [exact (tmred_eq _ _ _ _ _ _ _ Hw)|].
      eapply eqtm_trans; [exact (geq_tm_sound Heq) | apply eqtm_sym, (tmred_eq _ _ _ _ _ _ _ Hw')]. }
    exact (LRtm_red X2 (elimW_red_l Hγ He Hw) (elimW_red_r Hγ He Htt' Hw')).
  - (* a [sup]: both sides step to the step *)
    intros G0 Δ0 k1 k2 A0 B0 dR cR m1 m2 m1' m2' C D C' D' a a' f f' Hk1 Hk2 Hk1' Hk2' HC0 HC0' HD0 HD0'
      Ha Hwf Hf IH γ e e' Hγ He Nw Nw' E1 E2 E3 E4 HD HC.
    subst k1 k2 A0 B0.
    destruct (elimW_step Hk1 Hk2 Hk1' Hk2' HC0 HC0' HD0 HD0' Ha Hwf Hf IH Hγ He Nw Nw' HD HC) as (X2 & Lred & Rred).
    exact (LRtm_red X2 Lred Rred).
  - (* a neutral: [elim_W] is neutral *)
    intros G0 Δ0 k1 k2 A0 B0 dR cR ν ν' Hν γ e e' Hγ He _ _ E1 E2 E3 E4 HD HC. subst k1 k2 A0 B0.
    destruct (elimW_at Hγ He) as (HA0 & EA & HB0 & EB & HM0 & EM & HF0 & HI0 & Ec).
    pose proof (gne_tm_elimW (lequiv_weaken _ _ _ _ (proj1 Hγ) H14) (lequiv_weaken _ _ _ _ (proj1 Hγ) H25)
                  (lequiv_weaken _ _ _ _ (proj1 Hγ) H36) HA0 EA HB0 EB HM0 EM Ec Hν) as Hne.
    destruct (elimW_WLR Hγ (SubRel_refl_l He)) as (HWee & _ & _).
    pose proof (gne_tm_refl_l Hν) as Hνν.
    pose proof (eqtm_wf_l ge_typeof (geq_tm_sound (gne_tm_geq Hνν))) as Hνt.
    assert (Rνν : WRel G0 Δ0 l l' A⟦γ⟧[e] B⟦γ⟧[llift e]
                    (piDom (A := A⟦γ⟧) (A' := A⟦γ⟧) (l := l) (l' := l') Δ0 e e)
                    (piCod (A := A⟦γ⟧) (A' := A⟦γ⟧) (B := B⟦γ⟧) (B' := B⟦γ⟧) (l := l) (l' := l') Δ0 e e) ν ν)
      by exact (wrel _ _ _ _ _ _ _ _ _ _ _ _ (tmred_refl _ _ _ Hνt) (tmred_refl _ _ _ Hνt)
                  (gne_tm_geq Hνν) (wnf_ne _ _ _ _ _ _ _ _ _ _ Hνν)).
    destruct (elimW_mot Hγ (SubRel_refl_l He) (LRtm_of HWee Rνν)) as [RL HRL].
    exact (LRtm_of HRL (LR_neutral _ _ _ _ _ _ _ HRL _ _ Hne Hne)).
Qed.

(** ** [elim_W] and its β rule *)

Lemma V_elimW {t t'} : VTm G Γ t t' (tyW l l' A B) (lmax l l') ->
  VTm G Γ (tmElimW l l' l'' A B M c t) (tmElimW l4 l5 l6 A' B' M' c' t') M[lsingle t] l''.
Proof.
  intros Vt Δ d d' Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  rewrite !single_subst_ty by assumption. push_subst.
  destruct (elimW_WLR (gwk_ok_id G) Hd) as (HW & Hdom & Hcod). cbn [gwa] in HW, Hdom, Hcod.
  pose proof (Vt _ _ _ Hd) as Xt0. pose proof Xt0 as Xt. rewrite !subst_tyW in Xt.
  pose proof (LRtm_inv HW Xt) as Rt.
  pose proof (elimW_core _ _ _ _ _ _ _ _ _ _ Rt gwk_id d d' (gwk_ok_id G) Hd eq_refl eq_refl eq_refl eq_refl
                Hdom Hcod) as X.
  cbn [gwa] in X.
  eapply LRtm_irrel_r; [exact X|].
  pose proof (VTm_trans Vt (VTm_sym Vt) _ _ _ Hd) as Xtt.
  pose proof (VTy_refl_l (VTyG_loc VM) _ _ _ (SubRel_cons Hd Xtt)) as Y.
  now rewrite <- !lift_single_ty in Y by assumption.
Qed.

(** β, the right-hand side built from the right pieces. *)
Lemma V_elimW_sup {a a' f f'} : VTm G Γ a a' A l ->
  VTm G Γ f f' (tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩) (lmax l' (lmax l l')) ->
  VTm G Γ (tmElimW l l' l'' A B M c (tmSup l l' A B a f)) c'[lsingle3 a' f' (wIH l4 l5 l6 A' B' M' c' a' f')]
    M[lsingle (tmSup l l' A B a f)] l''.
Proof.
  intros Va Vf Δ d d' Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  pose proof (V_sup Hwl Hwl' (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwl') HB (VTyG_refl_l VA) (VTyG_refl_l VB) Va Vf)
    as Vs.
  pose proof (Vs _ _ _ Hd) as Xs0. pose proof Xs0 as Xs. rewrite !subst_tyW, !subst_sup in Xs.
  rewrite !single_subst_ty, single3_subst, subst_wIH by assumption. push_subst.
  destruct (elimW_WLR (gwk_ok_id G) Hd) as (HW & Hdom & Hcod). cbn [gwa] in HW, Hdom, Hcod.
  pose proof (LRtm_inv HW Xs) as Rs.
  destruct (WRel_inv Rs) as (w & w' & Hw & Hw' & _ & Hn).
  assert (w = tmSup l l' A[d] B[llift d] a[d] f[d]) as ->.
  { eapply tmred_whnf_det; [exact Hw | apply tmred_refl, (tmred_wf _ _ _ _ _ _ _ Hw) | exact (WNf_whnf_l Hn)
                           | apply whnf_sup]. }
  assert (w' = tmSup l l' A[d'] B[llift d'] a'[d'] f'[d']) as ->.
  { eapply tmred_whnf_det; [exact Hw' | apply tmred_refl, (tmred_wf _ _ _ _ _ _ _ Hw') | exact (WNf_whnf_r Hn)
                           | apply whnf_sup]. }
  destruct (WNf_sup_inv Hn) as (k1' & k2' & C' & D' & a0 & f0 & Heq & Hk1 & Hk2 & Hk1' & Hk2' & HC0 & HC0' & HD0 & HD0'
                                & Ha & Hwf & Hf).
  injection Heq as <- <- <- <- <- <-.
  pose proof (fun ρ ha b b' Hbb la lb A1 B1 la' lb' A1' B1' H1 H2 H3 H4 H5 H6 H7 H8 =>
                elimW_core _ _ _ _ _ _ _ _ _ _ (Hf ρ ha b b' Hbb la lb A1 B1 la' lb' A1' B1' H1 H2 H3 H4 H5 H6 H7 H8))
    as IH.
  assert (Nw : nftm (tmSup l l' A[d] B[llift d] a[d] f[d]))
    by exact (wf_tm_nf (tmred_wf _ _ _ _ _ _ _ Hw)).
  assert (Nw' : nftm (tmSup l l' A[d'] B[llift d'] a'[d'] f'[d']))
    by exact (wf_tm_nf (tmred_wf _ _ _ _ _ _ _ Hw')).
  destruct (elimW_step (γ := gwk_id) Hk1 Hk2 Hk1' Hk2' HC0 HC0' HD0 HD0' Ha Hwf Hf IH (gwk_ok_id G) Hd Nw Nw' Hdom Hcod)
    as (X2 & Lred & Rred).
  cbn [gwa] in X2, Lred, Rred.
  pose proof (LRtm_red X2 Lred (tmred_refl _ _ _ (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Rred)))) as X.
  eapply LRtm_irrel_r; [exact X|].
  pose proof (VTm_trans Vs (VTm_sym Vs) _ _ _ Hd) as Xss.
  pose proof (VTy_refl_l (VTyG_loc VM) _ _ _ (SubRel_cons Hd Xss)) as Y.
  rewrite <- !lift_single_ty in Y by assumption. now rewrite !subst_sup in Y.
Qed.

End ElimAt.

End WElim.
