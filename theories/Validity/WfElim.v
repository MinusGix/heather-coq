(** * Validity of [elim_Wf] (M15_DESIGN.md, M15a)

    As [elim_W]'s ([WElim]), by induction on [WfRel] ([elimWf_core]), at
    every global weakening and related substitution. The children of a
    [sup_f] are a spine ([VecSp]) rather than a function, so the motive at
    the spine is stated at an [nth] into it: at a length [k], a tuple [cs]
    and related indices [i ≈ i' : Fin k], any two terms related at [Wf]
    that reduce to [nth(cs; i)] and [nth(cs'; i')] have related
    eliminations. At a successor length and an [inl] index, [nth] reduces
    to the head, related by [WfRel]; at an [inr], to [nth] at the tail and
    the predecessor index; at a zero or neutral length or a neutral index,
    to a neutral, and so does the related term, whose elimination is then
    neutral. At a [sup_f], both sides step to the step at the shape, the
    children and the synthesized induction hypothesis [wfIH], a λ whose
    applications step to [elim_Wf] at an [nth] into the children, related
    at [Wf] by MX §13's index lemma ([V_nth]) and by the spine's motive. *)
From DeLaM.Validity Require Export WfNth.

Section WfElim.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

(** ** Syntax *)

Lemma gwa_tmNth γ l T k cs i : (tmNth l T k cs i)⟦γ⟧ = tmNth l T⟦γ⟧ k⟦γ⟧ cs⟦γ⟧ i⟦γ⟧.
Proof. destruct γ; cbn [gwa]; [reflexivity | apply gren_tmNth ..]. Qed.
Lemma gwa_wfIH γ l l' A N M c a cs :
  (wfIH l l' A N M c a cs)⟦γ⟧ = wfIH l l' A⟦γ⟧ N⟦γ⟧ M⟦γ⟧ c⟦γ⟧ a⟦γ⟧ cs⟦γ⟧.
Proof. destruct γ; cbn [gwa]; [reflexivity | apply gren_wfIH ..]. Qed.

Lemma gwa_wfcsty γ l (A : ty) (N : tm) : (wfcsty l A N)⟦γ⟧ = wfcsty l A⟦γ⟧ N⟦γ⟧.
Proof. now rewrite gwa_tyVec, gwa_ren_ty, gwa_tyWf. Qed.
Lemma gwa_wfihty γ l l' (A : ty) (N : tm) (M : ty) : (wfihty l l' A N M)⟦γ⟧ = wfihty l l' A⟦γ⟧ N⟦γ⟧ M⟦γ⟧.
Proof.
  repeat rewrite ?gwa_tyPi, ?gwa_tyFin, ?gwa_subst_ty, ?gwa_lsingle, ?gwa_tmNth, ?gwa_var, ?gwa_ren_ty, ?gwa_ren,
    ?gwa_tyWf.
  reflexivity.
Qed.
Lemma gwa_wfstepty γ l (A : ty) (N : tm) (M : ty) : (wfstepty l A N M)⟦γ⟧ = wfstepty l A⟦γ⟧ N⟦γ⟧ M⟦γ⟧.
Proof. repeat rewrite ?gwa_subst_ty, ?gwa_lsingle, ?gwa_supf, ?gwa_var, ?gwa_ren_ty, ?gwa_ren. reflexivity. Qed.

Section Telescope.
Context (d : lsub) (Hd : LK nftm d).

Lemma wfcsty_llift l (A : ty) (N : tm) : (wfcsty l A N)[llift d] = wfcsty l A[d] N[llift d].
Proof. sub_eqW. Qed.
Lemma wfihty_llift2 l l' (A : ty) (N : tm) (M : ty) :
  (wfihty l l' A N M)[llift (llift d)] = wfihty l l' A[d] N[llift d] M[llift d].
Proof. sub_eqW. Qed.
Lemma wfstepty_llift3 l (A : ty) (N : tm) (M : ty) :
  (wfstepty l A N M)[llift (llift (llift d))] = wfstepty l A[d] N[llift d] M[llift d].
Proof. sub_eqW. Qed.

End Telescope.

(** The synthesized induction hypothesis's body and codomain, in
    [Γ, j : Fin N[a/x]] (as in [Presupposition]). *)
Local Notation wfnth l A N a cs := (tmNth l (tyWf l A N)⟨↑⟩ N[lsingle a]⟨↑⟩ cs⟨↑⟩ (var 0)).
Local Notation wfbody l l' A N M c a cs :=
  (tmElimWf l l' A⟨↑⟩ N⟨rlift ↑⟩ M⟨rlift ↑⟩ c⟨rlift (rlift (rlift ↑))⟩ (wfnth l A N a cs)).
Local Notation wfcod l A N M a cs := (M⟨rlift ↑⟩[lsingle (wfnth l A N a cs)]).

Lemma ktm_wfIH {G Δ} (ρ : kwk G Δ) l l' A N M c a cs :
  ktm ρ (wfIH l l' A N M c a cs) =
  wfIH l l' (kty ρ A) (ktml ρ N) (ktyl ρ M) (ktm3 ρ c) (ktm ρ a) (ktm ρ cs).
Proof. unfold ktm, kty, ktyl, ktml, ktm3. now rewrite gwa_wfIH, ren_wfIH. Qed.

Lemma liftshift_llift_single (t y : tm) : nftm t -> t⟨rlift ↑⟩[llift (lsingle y)] = t.
Proof.
  intros Nt. rewrite (ren_subst _ _ _ (lshift 0)).
  - apply subst_id; [exact Nt | intros; cbn; f_equal; lia].
  - intros [|n]; pw.
Qed.

Lemma wfnth_single l (A : ty) (N : tm) (a cs y : tm) : nfty (tyWf l A N) -> nftm a -> nftm cs ->
  (wfnth l A N a cs)[lsingle y] = tmNth l (tyWf l A N) N[lsingle a] cs y.
Proof.
  intros NW Na Ncs. rewrite subst_tmNth.
  assert (NNa : nftm N[lsingle a]).
  { inversion NW as [NA NN]. apply subst_nf; [exact NN | intros [|n]; cbn; auto]. }
  rewrite shift_single_ty, !shift_single by assumption. reflexivity.
Qed.

Lemma wfbody_single l l' (A : ty) (N : tm) (M : ty) (c a cs y : tm) :
  nfty (tyWf l A N) -> nfty M -> nftm c -> nftm a -> nftm cs ->
  (wfbody l l' A N M c a cs)[lsingle y] = tmElimWf l l' A N M c (tmNth l (tyWf l A N) N[lsingle a] cs y).
Proof.
  intros NW NM Nc Na Ncs. pose proof NW as [NA NN].
  rewrite subst_elimWf, (wfnth_single l A N a cs y NW Na Ncs).
  rewrite shift_single_ty, liftshift_llift_single_ty, liftshift_llift_single, lift3shift_llift3_single
    by assumption.
  reflexivity.
Qed.

Lemma wfcod_single l (A : ty) (N : tm) (M : ty) (a cs y : tm) :
  nfty (tyWf l A N) -> nfty M -> nftm a -> nftm cs -> nftm y ->
  (wfcod l A N M a cs)[lsingle y] = M[lsingle (tmNth l (tyWf l A N) N[lsingle a] cs y)].
Proof.
  intros NW NM Na Ncs Ny.
  rewrite (single_subst_ty (lsingle y)) by (intros [|n]; cbn; auto).
  rewrite liftshift_llift_single_ty by exact NM.
  now rewrite (wfnth_single l A N a cs y NW Na Ncs).
Qed.

Lemma ktml_wfbody {G Δ} (ρ : kwk G Δ) l l' (A : ty) (N : tm) (M : ty) (c a cs : tm) :
  ktml ρ (wfbody l l' A N M c a cs) =
  wfbody l l' (kty ρ A) (ktml ρ N) (ktyl ρ M) (ktm3 ρ c) (ktm ρ a) (ktm ρ cs).
Proof.
  pose proof (ktm_wfIH ρ l l' A N M c a cs) as X. unfold wfIH in X. rewrite ktm_lam in X.
  injection X as _ X. exact X.
Qed.

Lemma ktyl_wfcod {G Δ} (ρ : kwk G Δ) l (A : ty) (N : tm) (M : ty) (a cs : tm) :
  ktyl ρ (wfcod l A N M a cs) = wfcod l (kty ρ A) (ktml ρ N) (ktyl ρ M) (ktm ρ a) (ktm ρ cs).
Proof.
  unfold ktyl, kty, ktm, ktml.
  repeat first [rewrite gwa_subst_ty | rewrite gwa_lsingle | rewrite gwa_tmNth | rewrite gwa_ren_ty
               | rewrite gwa_ren | rewrite gwa_var | rewrite gwa_tyWf | rewrite gwa_subst].
  rewrite lsingle_ren_ty. f_equal.
  - rewrite !ren_ren_comp_ty. apply ren_ext_ty. intros [|n]; rlk_simpl; reflexivity.
  - f_equal. rewrite ren_tmNth. f_equal.
    + now rewrite shift_lift_ty, ren_tyWf.
    + now rewrite shift_lift, lsingle_ren.
    + now rewrite shift_lift.
Qed.

(** ** The eliminator at related premises *)

Section ElimAt.
Context {G : gctx} {Γ : ctx} {l l' l3 l4 : lvl} {A A' : ty} {N N' : tm} {M M' : ty} {c c' : tm}
  (Hwl : lwf (gL G) l) (Hwl' : lwf (gL G) l') (H13 : lequiv (gL G) l l3) (H24 : lequiv (gL G) l' l4)
  (HN : [ G ; Γ ,, A @ l ⊢g N : tyNat @ lzero ])
  (VA : VTyG G Γ A A' l) (VNt : VTmG G (Γ ,, A @ l) N N' tyNat lzero)
  (VM : VTyG G (Γ ,, tyWf l A N @ l) M M' l')
  (Vcs : VTyG G (Γ ,, A @ l) (wfcsty l A N) (wfcsty l A N) l)
  (Vih : VTyG G (Γ ,, A @ l ,, wfcsty l A N @ l) (wfihty l l' A N M) (wfihty l l' A N M) (lmax lzero l'))
  (Vc : VTmG G (Γ ,, A @ l ,, wfcsty l A N @ l ,, wfihty l l' A N M @ lmax lzero l') c c'
          (wfstepty l A N M) l').

(** The premises at a global weakening, localized. *)
Lemma elimWf_loc {G0 γ} : gwk_ok γ G0 G -> [ ⊢ G0 ] ->
  [ G0 ; Γ⟦γ⟧ ,, A⟦γ⟧ @ l ⊢g N⟦γ⟧ : tyNat @ lzero ] /\
  VTyG G0 Γ⟦γ⟧ A⟦γ⟧ A'⟦γ⟧ l /\ VTmG G0 (Γ⟦γ⟧ ,, A⟦γ⟧ @ l) N⟦γ⟧ N'⟦γ⟧ tyNat lzero /\
  VTy G0 (Γ⟦γ⟧ ,, tyWf l A⟦γ⟧ N⟦γ⟧ @ l) M⟦γ⟧ M'⟦γ⟧ l' /\
  VTy G0 (Γ⟦γ⟧ ,, A⟦γ⟧ @ l) (wfcsty l A⟦γ⟧ N⟦γ⟧) (wfcsty l A⟦γ⟧ N⟦γ⟧) l /\
  VTy G0 (Γ⟦γ⟧ ,, A⟦γ⟧ @ l ,, wfcsty l A⟦γ⟧ N⟦γ⟧ @ l)
    (wfihty l l' A⟦γ⟧ N⟦γ⟧ M⟦γ⟧) (wfihty l l' A⟦γ⟧ N⟦γ⟧ M⟦γ⟧) (lmax lzero l') /\
  VTm G0 (Γ⟦γ⟧ ,, A⟦γ⟧ @ l ,, wfcsty l A⟦γ⟧ N⟦γ⟧ @ l ,, wfihty l l' A⟦γ⟧ N⟦γ⟧ M⟦γ⟧ @ lmax lzero l')
    c⟦γ⟧ c'⟦γ⟧ (wfstepty l A⟦γ⟧ N⟦γ⟧ M⟦γ⟧) l'.
Proof.
  intros Hγ HG0. pose proof (gwa_tm Hγ HG0 HN) as HNγ. rewrite gwa_cext, gwa_tyNat in HNγ.
  pose proof (VTyG_gwk VA Hγ) as VAγ. pose proof (VTmG_gwk VNt Hγ) as VNγ. rewrite gwa_cext, gwa_tyNat in VNγ.
  pose proof (VM _ _ Hγ) as VMγ. rewrite !gwa_cext, gwa_tyWf in VMγ.
  pose proof (Vcs _ _ Hγ) as Vcsγ. rewrite !gwa_cext, gwa_wfcsty in Vcsγ.
  pose proof (Vih _ _ Hγ) as Vihγ. rewrite !gwa_cext, gwa_wfcsty, gwa_wfihty in Vihγ.
  pose proof (Vc _ _ Hγ) as Vcγ. rewrite !gwa_cext, gwa_wfcsty, gwa_wfihty, gwa_wfstepty in Vcγ.
  repeat split; assumption.
Qed.

(** The premises at a related substitution after a global weakening. *)
Lemma elimWf_at {G0 γ Δ0 e e'} : gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' ->
  [ G0 ; Δ0 ⊢g A⟦γ⟧[e] @ l ] /\ [ G0 ; Δ0 ⊢ A⟦γ⟧[e] ≈ A'⟦γ⟧[e'] @ l ] /\
  [ G0 ; Δ0 ,, A⟦γ⟧[e] @ l ⊢g N⟦γ⟧[llift e] : tyNat @ lzero ] /\
  [ G0 ; Δ0 ,, A⟦γ⟧[e] @ l ⊢ N⟦γ⟧[llift e] ≈ N'⟦γ⟧[llift e'] : tyNat @ lzero ] /\
  [ G0 ; Δ0 ,, tyWf l A⟦γ⟧[e] N⟦γ⟧[llift e] @ l ⊢g M⟦γ⟧[llift e] @ l' ] /\
  [ G0 ; Δ0 ,, tyWf l A⟦γ⟧[e] N⟦γ⟧[llift e] @ l ⊢ M⟦γ⟧[llift e] ≈ M'⟦γ⟧[llift e'] @ l' ] /\
  [ G0 ; Δ0 ,, A⟦γ⟧[e] @ l ⊢g wfcsty l A⟦γ⟧[e] N⟦γ⟧[llift e] @ l ] /\
  [ G0 ; Δ0 ,, A⟦γ⟧[e] @ l ,, wfcsty l A⟦γ⟧[e] N⟦γ⟧[llift e] @ l
      ⊢g wfihty l l' A⟦γ⟧[e] N⟦γ⟧[llift e] M⟦γ⟧[llift e] @ lmax lzero l' ] /\
  [ G0 ; Δ0 ,, A⟦γ⟧[e] @ l ,, wfcsty l A⟦γ⟧[e] N⟦γ⟧[llift e] @ l
      ,, wfihty l l' A⟦γ⟧[e] N⟦γ⟧[llift e] M⟦γ⟧[llift e] @ lmax lzero l'
      ⊢ c⟦γ⟧[llift (llift (llift e))] ≈ c'⟦γ⟧[llift (llift (llift e'))]
      : wfstepty l A⟦γ⟧[e] N⟦γ⟧[llift e] M⟦γ⟧[llift e] @ l' ].
Proof.
  intros Hγ He. pose proof (ctx_glob _ _ _ (SubRel_ctx He)) as HG0.
  destruct (SubRel_nf _ _ _ _ _ He) as [Ne Ne'].
  destruct (elimWf_loc Hγ HG0) as (HNγ & VAγ & VNγ & VMγ & Vcsγ & Vihγ & Vcγ).
  pose proof (VTyG_loc VAγ) as VAl. pose proof (VTy_refl_l VAl) as VAA.
  pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwl) as Hwl0.
  pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwl') as Hwl'0.
  assert (HwI : lwf (gL G0) (lmax lzero l')) by (apply lwf_max; [exact I | exact Hwl'0]).
  destruct (VAl _ _ _ He) as [RA HRA]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HA0 & _ & EA).
  pose proof (SubRel_lift He VAA HA0 Hwl0) as H1.
  pose proof (VTmG_loc VNγ _ _ _ H1) as XN. rewrite !subst_tyNat in XN.
  destruct (LRtm_escape XN) as [HN0 _]. pose proof (LRtm_geq XN) as EN.
  (* the motive, under [Wf] *)
  pose proof (V_wf Hwl0 (lequiv_refl _ _ Hwl0) (VTyG_refl_l VAγ) (VTmG_refl_l VNγ)) as VW.
  destruct (VW _ _ _ He) as [RW HRW]. destruct (escape_ty _ _ _ _ _ _ _ _ HRW) as (HW0 & _ & _).
  pose proof (SubRel_lift He VW HW0 Hwl0) as HW1.
  destruct (VMγ _ _ _ HW1) as [RM HRM]. destruct (escape_ty _ _ _ _ _ _ _ _ HRM) as (HM0 & _ & EM).
  rewrite subst_tyWf in HM0, EM.
  (* the step's telescope *)
  destruct (Vcsγ _ _ _ H1) as [RC HRC]. destruct (escape_ty _ _ _ _ _ _ _ _ HRC) as (HC0 & _ & _).
  pose proof (SubRel_lift H1 Vcsγ HC0 Hwl0) as H2.
  destruct (Vihγ _ _ _ H2) as [RI HRI]. destruct (escape_ty _ _ _ _ _ _ _ _ HRI) as (HI0 & _ & _).
  pose proof (SubRel_lift H2 Vihγ HI0 HwI) as H3.
  pose proof (LRtm_geq (Vcγ _ _ _ H3)) as Ec.
  rewrite wfcsty_llift in HC0, HI0, Ec by exact Ne.
  rewrite wfihty_llift2 in HI0, Ec by exact Ne.
  rewrite wfstepty_llift3 in Ec by exact Ne.
  repeat split; assumption.
Qed.

(** [elim_Wf]'s congruence and typed reductions in the scrutinee. *)
Section Cong.
Context {G0 γ Δ0 e e'} (Hγ : gwk_ok γ G0 G) (He : SubRel G0 Γ⟦γ⟧ Δ0 e e').

Lemma elimWf_cong {t t'} :
  [ G0 ; Δ0 ⊢g t ≅ t' : tyWf l A⟦γ⟧[e] N⟦γ⟧[llift e] @ l ] ->
  [ G0 ; Δ0 ⊢g tmElimWf l l' A⟦γ⟧[e] N⟦γ⟧[llift e] M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))] t
             ≅ tmElimWf l3 l4 A'⟦γ⟧[e'] N'⟦γ⟧[llift e'] M'⟦γ⟧[llift e'] c'⟦γ⟧[llift (llift (llift e'))] t'
             : M⟦γ⟧[llift e][lsingle t] @ l' ].
Proof.
  intros Ht. destruct (elimWf_at Hγ He) as (HA0 & EA & HN0 & EN & HM0 & EM & HC0 & HI0 & Ec).
  apply eqtm_elimWf; first [exact ge_compt | apply (lequiv_weaken _ _ _ _ (proj1 Hγ)); assumption
                           | apply geq_ty_sound; assumption | apply geq_tm_sound; assumption | assumption].
Qed.

Lemma elimWf_cong_l {t t'} :
  [ G0 ; Δ0 ⊢g t ≅ t' : tyWf l A⟦γ⟧[e] N⟦γ⟧[llift e] @ l ] ->
  [ G0 ; Δ0 ⊢g tmElimWf l l' A⟦γ⟧[e] N⟦γ⟧[llift e] M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))] t
             ≅ tmElimWf l l' A⟦γ⟧[e] N⟦γ⟧[llift e] M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))] t'
             : M⟦γ⟧[llift e][lsingle t] @ l' ].
Proof.
  intros Ht. destruct (elimWf_at Hγ He) as (HA0 & EA & HN0 & EN & HM0 & EM & HC0 & HI0 & Ec).
  pose proof (eqtm_wf_l ge_typeof (geq_tm_sound Ec)) as Hc0.
  apply eqtm_elimWf; first [exact ge_compt | apply lequiv_refl, (lwf_weaken _ _ _ (proj1 Hγ)); assumption
                           | apply eqty_refl; assumption | apply eqtm_refl; assumption | assumption].
Qed.

Lemma elimWf_red_l {t w} : [ G0 ; Δ0 ⊢g t ⤳* w : tyWf l A⟦γ⟧[e] N⟦γ⟧[llift e] @ l ] ->
  [ G0 ; Δ0 ⊢g tmElimWf l l' A⟦γ⟧[e] N⟦γ⟧[llift e] M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))] t
             ⤳* tmElimWf l l' A⟦γ⟧[e] N⟦γ⟧[llift e] M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))] w
             : M⟦γ⟧[llift e][lsingle t] @ l' ].
Proof.
  intros Hr. pose proof (elimWf_cong_l (tmred_eq _ _ _ _ _ _ _ Hr)) as X.
  split; [exact (eqtm_wf_l ge_typeof X) | apply reds_elimWf, (tmred_red _ _ _ _ _ _ _ Hr) | exact X].
Qed.

Lemma elimWf_red_r {t t' w'} :
  [ G0 ; Δ0 ⊢g t ≅ t' : tyWf l A⟦γ⟧[e] N⟦γ⟧[llift e] @ l ] ->
  [ G0 ; Δ0 ⊢g t' ⤳* w' : tyWf l A⟦γ⟧[e] N⟦γ⟧[llift e] @ l ] ->
  [ G0 ; Δ0 ⊢g tmElimWf l3 l4 A'⟦γ⟧[e'] N'⟦γ⟧[llift e'] M'⟦γ⟧[llift e'] c'⟦γ⟧[llift (llift (llift e'))] t'
             ⤳* tmElimWf l3 l4 A'⟦γ⟧[e'] N'⟦γ⟧[llift e'] M'⟦γ⟧[llift e'] c'⟦γ⟧[llift (llift (llift e'))] w'
             : M⟦γ⟧[llift e][lsingle t] @ l' ].
Proof.
  intros Htt Hr. pose proof (elimWf_cong Htt) as X1.
  pose proof (elimWf_cong (eqtm_trans _ _ _ _ _ _ _ _ Htt (tmred_eq _ _ _ _ _ _ _ Hr))) as X2.
  split; [exact (eqtm_wf_r ge_typeof X1) | apply reds_elimWf, (tmred_red _ _ _ _ _ _ _ Hr) |].
  eapply eqtm_trans; [apply eqtm_sym, X1 | exact X2].
Qed.

End Cong.

(** The relation at [Wf] and at the motive, at a related substitution. *)
Lemma elimWf_WLR {G0 γ Δ0 e e'} : gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' ->
  LogRel l G0 Δ0 (tyWf l A⟦γ⟧[e] N⟦γ⟧[llift e]) (tyWf l A⟦γ⟧[e'] N⟦γ⟧[llift e']) l
    (WfRel G0 Δ0 l A⟦γ⟧[e] N⟦γ⟧[llift e] (wfDom (G := G0) (l := l) (A := A⟦γ⟧) (A' := A⟦γ⟧) Δ0 e e')) /\
  WfDom G0 Δ0 l A⟦γ⟧[e] (wfDom (G := G0) (l := l) (A := A⟦γ⟧) (A' := A⟦γ⟧) Δ0 e e').
Proof.
  intros Hγ He. pose proof (ctx_glob _ _ _ (SubRel_ctx He)) as HG0.
  destruct (elimWf_loc Hγ HG0) as (_ & VAγ & VNγ & _).
  pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwl) as Hwl0.
  pose proof (LR_Wf_here Hwl0 (lequiv_refl _ _ Hwl0) (VTyG_refl_l VAγ) (VTmG_refl_l VNγ) _ _ _ He) as HW.
  rewrite !subst_tyWf in HW. split; [exact HW|].
  exact (WfDom_of (wfDom_canon (VTyG_refl_l VAγ) He)).
Qed.

Lemma elimWf_mot {G0 γ Δ0 e e' x x'} : gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' ->
  LRtm l G0 Δ0 (tyWf l A⟦γ⟧[e] N⟦γ⟧[llift e]) (tyWf l A⟦γ⟧[e'] N⟦γ⟧[llift e']) x x' ->
  LRty l' G0 Δ0 M⟦γ⟧[llift e][lsingle x] M⟦γ⟧[llift e'][lsingle x'].
Proof.
  intros Hγ He Hx. pose proof (ctx_glob _ _ _ (SubRel_ctx He)) as HG0.
  destruct (SubRel_nf _ _ _ _ _ He) as [Ne Ne'].
  destruct (elimWf_loc Hγ HG0) as (_ & _ & _ & VMγ & _).
  rewrite <- !subst_tyWf in Hx.
  pose proof (VTy_refl_l VMγ _ _ _ (SubRel_cons He Hx)) as X.
  now rewrite <- !lift_single_ty in X.
Qed.

(** [WfRel] at a canonical shape relation is the relation at [Wf]. *)
Lemma elimWf_rel {G0 γ Δ0 e e'} {dR : DomRel G0 Δ0} {s s'} : gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' ->
  WfDom G0 Δ0 l A⟦γ⟧[e] dR -> WfRel G0 Δ0 l A⟦γ⟧[e] N⟦γ⟧[llift e] dR s s' ->
  LRtm l G0 Δ0 (tyWf l A⟦γ⟧[e] N⟦γ⟧[llift e]) (tyWf l A⟦γ⟧[e] N⟦γ⟧[llift e]) s s'.
Proof.
  intros Hγ He HD Hs. destruct (elimWf_WLR Hγ (SubRel_refl_l He)) as [HW HD0].
  eapply LRtm_of; [exact HW|]. eapply (proj1 WfRel_dir_all); [exact Hs|].
  exact (WfDom_releq HD HD0).
Qed.

(** The elimination at related terms, from the elimination at their whnfs. *)
Lemma elimWf_back {G0 γ Δ0 e e'} {dR : DomRel G0 Δ0} {s s' w w'} :
  gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' -> WfDom G0 Δ0 l A⟦γ⟧[e] dR ->
  WfRel G0 Δ0 l A⟦γ⟧[e] N⟦γ⟧[llift e] dR s s' ->
  [ G0 ; Δ0 ⊢g s ⤳* w : tyWf l A⟦γ⟧[e] N⟦γ⟧[llift e] @ l ] ->
  [ G0 ; Δ0 ⊢g s' ⤳* w' : tyWf l A⟦γ⟧[e] N⟦γ⟧[llift e] @ l ] -> whnf w -> whnf w' ->
  LRtm l' G0 Δ0 M⟦γ⟧[llift e][lsingle w] M⟦γ⟧[llift e][lsingle w]
    (tmElimWf l l' A⟦γ⟧[e] N⟦γ⟧[llift e] M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))] w)
    (tmElimWf l3 l4 A'⟦γ⟧[e'] N'⟦γ⟧[llift e'] M'⟦γ⟧[llift e'] c'⟦γ⟧[llift (llift (llift e'))] w') ->
  LRtm l' G0 Δ0 M⟦γ⟧[llift e][lsingle s] M⟦γ⟧[llift e][lsingle s]
    (tmElimWf l l' A⟦γ⟧[e] N⟦γ⟧[llift e] M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))] s)
    (tmElimWf l3 l4 A'⟦γ⟧[e'] N'⟦γ⟧[llift e'] M'⟦γ⟧[llift e'] c'⟦γ⟧[llift (llift (llift e'))] s').
Proof.
  intros Hγ He HD Hss Hs Hs' Nw Nw' X.
  destruct (WfRel_inv Hss) as (w0 & w0' & Hw0 & Hw0' & Ew & Nn).
  assert (w0 = w) as -> by (eapply tmred_whnf_det; [exact Hw0 | exact Hs | exact (WfNf_whnf_l Nn) | exact Nw]).
  assert (w0' = w') as -> by (eapply tmred_whnf_det; [exact Hw0' | exact Hs' | exact (WfNf_whnf_r Nn) | exact Nw']).
  pose proof (tmred_wf _ _ _ _ _ _ _ Hs') as _.
  pose proof (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hs)) as Hwt.
  pose proof (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hs')) as Hw't.
  pose proof (elimWf_rel Hγ He HD (wfrel _ _ _ _ _ _ _ _ _ _ Hs (tmred_refl _ _ _ Hw't) Ew Nn)) as Xsw'.
  pose proof (elimWf_rel Hγ He HD (wfrel _ _ _ _ _ _ _ _ _ _ (tmred_refl _ _ _ Hwt) (tmred_refl _ _ _ Hw't) Ew Nn))
    as Xww'.
  pose proof (LRtm_trans Xsw' (LRtm_sym Xww')) as Xsw. pose proof (LRtm_trans Xsw (LRtm_sym Xsw)) as Xss.
  pose proof (elimWf_mot Hγ (SubRel_refl_l He) Xsw) as XT.
  pose proof (elimWf_mot Hγ (SubRel_refl_l He) Xss) as XTT.
  pose proof (LRtm_irrel_r (LRtm_conv_l X XT) XTT) as X2.
  pose proof (geq_tm_sound (LRtm_geq (elimWf_rel Hγ He HD Hss))) as Hss'.
  exact (LRtm_red X2 (elimWf_red_l Hγ He Hs) (elimWf_red_r Hγ He Hss' Hs')).
Qed.

(** At a term reducing to a neutral, the elimination is neutral. *)
Lemma elimWf_ne {G0 γ Δ0 e e'} {dR : DomRel G0 Δ0} {s s' X} :
  gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' -> WfDom G0 Δ0 l A⟦γ⟧[e] dR ->
  WfRel G0 Δ0 l A⟦γ⟧[e] N⟦γ⟧[llift e] dR s s' -> reds s X -> whne X ->
  LRtm l' G0 Δ0 M⟦γ⟧[llift e][lsingle s] M⟦γ⟧[llift e][lsingle s]
    (tmElimWf l l' A⟦γ⟧[e] N⟦γ⟧[llift e] M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))] s)
    (tmElimWf l3 l4 A'⟦γ⟧[e'] N'⟦γ⟧[llift e'] M'⟦γ⟧[llift e'] c'⟦γ⟧[llift (llift (llift e'))] s').
Proof.
  intros Hγ He HD Hss HX NX.
  destruct (WfRel_inv Hss) as (w & w' & Hw & Hw' & Ew & Nn).
  assert (w = X) as ->.
  { eapply reds_whnf_det; [exact (tmred_red _ _ _ _ _ _ _ Hw) | exact HX | exact (WfNf_whnf_l Nn)
                          | now apply whnf_ne]. }
  pose proof (WfNf_ne_inv NX Nn) as Hne.
  destruct (elimWf_at Hγ He) as (HA0 & EA & HN0 & EN & HM0 & EM & HC0 & HI0 & Ec).
  pose proof (gne_tm_elimWf (lequiv_weaken _ _ _ _ (proj1 Hγ) H13) (lequiv_weaken _ _ _ _ (proj1 Hγ) H24)
                HA0 EA HN0 EN HM0 EM Ec Hne) as HE.
  pose proof (gne_tm_refl_l Hne) as HXX.
  pose proof (eqtm_wf_l ge_typeof (geq_tm_sound (gne_tm_geq HXX))) as HXt.
  assert (RXX : WfRel G0 Δ0 l A⟦γ⟧[e] N⟦γ⟧[llift e] dR X X)
    by exact (wfrel _ _ _ _ _ _ _ _ _ _ (tmred_refl _ _ _ HXt) (tmred_refl _ _ _ HXt)
                (gne_tm_geq HXX) (wfnf_ne _ _ _ _ _ _ _ _ HXX)).
  destruct (elimWf_mot Hγ (SubRel_refl_l He) (elimWf_rel Hγ He HD RXX)) as [RL HRL].
  eapply elimWf_back; [exact Hγ | exact He | exact HD | exact Hss | exact Hw | exact Hw'
                      | now apply whnf_ne | exact (WfNf_whnf_r Nn) |].
  exact (LRtm_of HRL (LR_neutral _ _ _ _ _ _ _ HRL _ _ HE HE)).
Qed.

End ElimAt.

End WfElim.