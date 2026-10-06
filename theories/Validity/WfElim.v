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

(** ** Helpers *)

Ltac gwkn H := first [ exact H | eapply (wk1_ty _ _ ge_typeof); [eassumption | gwkn H]
                     | eapply (wk1_tm _ _ ge_typeof); [eassumption | gwkn H] ].
Ltac vvar := eapply VG_var; [repeat constructor | cbn; try reflexivity].

Lemma reds_refl t : reds t t.
Proof. constructor. Qed.

Lemma ktml_kid {G Δ} (HΔ : [ G ; Δ ⊢g ]) (t : tm) : nftm t -> ktml (kid HΔ) t = t.
Proof.
  intros Nt. unfold ktml, kid, kw_loc; cbn [kw_γ kw_r gwa wk_ren].
  rewrite <- (ren_id_tm t Nt) at 2. apply ren_ext_tm. intros n. rewrite rlk_rlift. destruct n; cbn; lia.
Qed.

Lemma ktml_subst_lift {G Δ} (ρ : kwk G Δ) (t : tm) e :
  ktml ρ t[llift e] = t⟦kw_γ ρ⟧[llift (kwsub ρ e)].
Proof.
  unfold ktml, kwsub. rewrite gwa_subst, subst_ren_lren.
  apply subst_ext. intros n. rewrite llk_lren, llk_llift_gwa.
  destruct n; rewrite !llk_llift; [reflexivity|].
  rewrite llk_lren. change (ren_tm ?x ?r') with x⟨r'⟩. now rewrite shift_lift.
Qed.
Lemma kγ_tml {G Δ} (ρ : kwk G Δ) (t : tm) γ e :
  ktml ρ t⟦γ⟧[llift e] = t⟦gwk_comp (kw_γ ρ) γ⟧[llift (kwsub ρ e)].
Proof. now rewrite ktml_subst_lift, gwa_comp_tm. Qed.

(** An index into [Fin] at a zero length is neutral. *)
Lemma fin_idx_zero {G Δ k k' i i'} : LRtm lzero G Δ (tyFin k) (tyFin k') i i' ->
  [ G ; Δ ⊢g k ⤳* zero : tyNat @ lzero ] -> exists ν, reds i ν /\ whne ν.
Proof.
  intros (R & HR & Hii) Hk. pose proof (ctx_of_tm (tmred_wf _ _ _ _ _ _ _ Hk)) as HΔ.
  destruct (LR_inv_empty HR (tyred_trans _ _ _ _ (tyred_fin Hk) (tyred_fin_zero HΔ))) as (l2 & _ & _ & _ & _ & HR').
  apply HR' in Hii. destruct Hii as (w & w' & Hw & _ & Hne).
  exists w. split; [exact (tmred_red _ _ _ _ _ _ _ Hw) | exact (gne_tm_whne_l Hne)].
Qed.

(** An index into [Fin] at a successor length is an [inl], an [inr] of an
    index at the predecessor, or neutral. *)
Lemma fin_idx_succ {G Δ k k' m m' i i'} : LRtm lzero G Δ (tyFin k) (tyFin k') i i' ->
  [ G ; Δ ⊢g k ⤳* succ m : tyNat @ lzero ] -> NatRel G Δ m m' ->
  (exists k1 k2 C D u k1' k2' C' D' u', reds i (tmInl k1 k2 C D u) /\ reds i' (tmInl k1' k2' C' D' u')) \/
  (exists k1 k2 C D j k1' k2' C' D' j', reds i (tmInr k1 k2 C D j) /\ reds i' (tmInr k1' k2' C' D' j') /\
     LRtm lzero G Δ (tyFin m) (tyFin m') j j') \/
  (exists ν, reds i ν /\ whne ν).
Proof.
  intros (R & HR & Hii) Hk Hmm. pose proof (ctx_of_tm (tmred_wf _ _ _ _ _ _ _ Hk)) as HΔ.
  destruct (NatRel_escape Hmm) as (Hm & _ & _).
  destruct (LR_inv_sum HR (tyred_trans _ _ _ _ (tyred_fin Hk) (tyred_fin_succ Hm)))
    as (l3 & l4 & X' & Y' & RA & RB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRB & _ & _ & _ & _ & HR').
  apply HR' in Hii. destruct Hii as (w & w' & Hw & Hw' & _ & Nn).
  apply tmred_red in Hw, Hw'.
  destruct Nn as [k1 k2 k1' k2' C D C' D' u u' _ _ _ _ _ _ _ _ _
                 |k1 k2 k1' k2' C D C' D' j j' _ _ _ _ _ _ _ _ Hj
                 |ν ν' Hν].
  - left. do 10 eexists. split; eassumption.
  - right; left. do 10 eexists. split; [eassumption | split; [eassumption|]].
    eapply LRtm_irrel_r; [exact (ex_intro _ RB (conj HRB Hj)) | exact (LR_fin_nat HΔ Hmm)].
  - right; right. exists ν. split; [exact Hw | exact (gne_tm_whne_l Hν)].
Qed.

(** Spine to relation at the spine's own world, from the spine in every
    world. *)
Lemma LR_of_VecSp_own {G Δ l A N} {domR : DomRel G Δ} {k k' cs cs'} :
  lwf (gL G) l -> [ G ; Δ ⊢g tyWf l A N @ l ] -> WfDom G Δ l A domR -> NatRel G Δ k k' ->
  nftm cs -> nftm cs' ->
  (forall ρ : kwk G Δ, VecSp (kw_G ρ) (kw_Δ ρ) l (kty ρ A) (ktml ρ N) (fun ρ' => domR (kw_comp ρ ρ'))
                       (ktm ρ k) (ktm ρ cs) (ktm ρ cs')) ->
  forall T' R, LogRel l G Δ (tyVec l (tyWf l A N) k) T' l R -> R cs cs'.
Proof.
  intros Hwl HWf HD Hkk Ncs Ncs' Hsp T' R H.
  pose proof (ctx_of_ty HWf) as HΔ. pose proof (wf_ty_nf HWf) as NW. inversion NW as [NA NN].
  destruct (NatRel_escape Hkk) as (Hk & _ & _). pose proof (wf_tm_nf Hk) as Nk.
  pose proof (LR_of_VecSp_all Hwl HWf HD k k' Hkk (kid HΔ)) as X. unfold VecQ in X.
  rewrite (kty_kid HΔ _ NA), (ktml_kid HΔ _ NN), (ktm_kid HΔ _ Nk) in X.
  apply (X T' R H cs cs'). split.
  - pose proof (Hsp (kid HΔ)) as Y.
    rewrite (kty_kid HΔ _ NA), (ktml_kid HΔ _ NN), (ktm_kid HΔ _ Nk), (ktm_kid HΔ _ Ncs), (ktm_kid HΔ _ Ncs')
      in Y.
    exact Y.
  - intros ρ. pose proof (Hsp (kw_comp (kid HΔ) ρ)) as Y.
    rewrite kty_comp, ktml_comp, !ktm_comp, (kty_kid HΔ _ NA), (ktml_kid HΔ _ NN), (ktm_kid HΔ _ Nk),
      (ktm_kid HΔ _ Ncs), (ktm_kid HΔ _ Ncs') in Y.
    eapply (proj2 (proj2 WfRel_dir_all)); [exact Y|].
    intros ρ0. exact (WfDom_assoc HD (kid HΔ) ρ ρ0).
Qed.

Lemma lift_single_tm (t : tm) d a : LK nftm d -> t[llift d][lsingle a] = t[lcons d a].
Proof.
  intros Hd. apply subst_subst. intros [|n]; rewrite llk_llift; cbn; [reflexivity|].
  change (ren_tm ?x ?r) with x⟨r⟩. symmetry; apply shift_single, Hd.
Qed.

(** The [nth] in the induction hypothesis's type, and its domain, at a
    substitution. *)
Lemma nthv_subst l (A : ty) (N : tm) d a cs y : LK nftm d ->
  (tmNth l (tyWf l A N)⟨↑⟩⟨↑⟩⟨↑⟩ N⟨↑⟩⟨↑⟩ (var 1) (var 0))[lcons (lcons (lcons d a) cs) y] =
  tmNth l (tyWf l A[d] N[llift d]) N[llift d][lsingle a] cs y.
Proof.
  intros Hd. rewrite subst_tmNth, !shift_subst_ty, !shift_subst_tm. cbn [ldrop].
  now rewrite lift_single_tm by exact Hd.
Qed.
Lemma finv_subst (N : tm) d a cs : LK nftm d ->
  (tyFin N⟨↑⟩)[lcons (lcons d a) cs] = tyFin N[llift d][lsingle a].
Proof.
  intros Hd. rewrite subst_tyFin, shift_subst_tm. cbn [ldrop].
  now rewrite lift_single_tm by exact Hd.
Qed.

Lemma VG_wf {G Γ l l' A A' N N'} : lwf (gL G) l -> lequiv (gL G) l' l ->
  VTyG G Γ A A' l -> VTmG G (Γ ,, A @ l) N N' tyNat lzero -> VTyG G Γ (tyWf l A N) (tyWf l' A' N') l.
Proof. intros. gl_lift. eapply V_wf; eassumption. Qed.

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

(** MX §13's index lemma at the [ih] entry's [nth]. *)
Lemma elimWf_Vnth :
  VTmG G (Γ ,, A @ l ,, wfcsty l A N @ l ,, tyFin N⟨↑⟩ @ lzero)
    (tmNth l (tyWf l A N)⟨↑⟩⟨↑⟩⟨↑⟩ N⟨↑⟩⟨↑⟩ (var 1) (var 0))
    (tmNth l3 (tyWf l3 A' N')⟨↑⟩⟨↑⟩⟨↑⟩ N'⟨↑⟩⟨↑⟩ (var 1) (var 0)) (tyWf l A N)⟨↑⟩⟨↑⟩⟨↑⟩ l.
Proof.
  pose proof (ctx_of_tm HN) as HΓA.
  assert (HA : [ G ; Γ ⊢g A @ l ]) by (inversion HΓA; assumption).
  pose proof (ctx_of_ty HA) as HΓ.
  assert (HW : [ G ; Γ ⊢g tyWf l A N @ l ]) by (apply wft_wf; auto using ge_compt).
  pose proof (Wf_cs_wf ge_typeof ge_notV Hwl HW HN) as HC.
  assert (H2 : [ G ; Γ ,, A @ l ,, wfcsty l A N @ l ⊢g ]) by exact (ext_wf_g HC Hwl).
  assert (HN1 : [ G ; Γ ,, A @ l ,, wfcsty l A N @ l ⊢g N⟨↑⟩ : tyNat @ lzero ])
    by (eapply wf_tm_retype; [gwkn HN | reflexivity]).
  assert (HF : [ G ; Γ ,, A @ l ,, wfcsty l A N @ l ⊢g tyFin N⟨↑⟩ @ lzero ]) by (apply wft_fin; auto using ge_notV).
  assert (H3 : [ G ; Γ ,, A @ l ,, wfcsty l A N @ l ,, tyFin N⟨↑⟩ @ lzero ⊢g ]) by (apply ext_wf_g; cbn; auto).
  assert (HN2 : [ G ; Γ ,, A @ l ,, wfcsty l A N @ l ,, tyFin N⟨↑⟩ @ lzero ⊢g N⟨↑⟩⟨↑⟩ : tyNat @ lzero ])
    by (eapply wf_tm_retype; [gwkn HN1 | reflexivity]).
  assert (HW3 : [ G ; Γ ,, A @ l ,, wfcsty l A N @ l ,, tyFin N⟨↑⟩ @ lzero ⊢g (tyWf l A N)⟨↑⟩⟨↑⟩⟨↑⟩ @ l ])
    by (gwkn HW).
  pose proof (VG_wf Hwl (lequiv_sym _ _ _ H13) VA VNt) as VW.
  apply (V_nth Hwl H13 HW3 (VG_shift (VG_shift (VG_shift VW))) HN2).
  - eapply VTmG_retype; [exact (VG_shift_tm (VG_shift_tm VNt)) | reflexivity].
  - vvar.
  - vvar.
Qed.

(** ** The core: related eliminations at related trees *)

(** The eliminations at two terms, after a global weakening and at a
    related substitution, related at the motive. *)
Definition elimWf_goal G0 Δ0 γ e e' s s' : Prop :=
  LRtm l' G0 Δ0 M⟦γ⟧[llift e][lsingle s] M⟦γ⟧[llift e][lsingle s]
    (tmElimWf l l' A⟦γ⟧[e] N⟦γ⟧[llift e] M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))] s)
    (tmElimWf l3 l4 A'⟦γ⟧[e'] N'⟦γ⟧[llift e'] M'⟦γ⟧[llift e'] c'⟦γ⟧[llift (llift (llift e'))] s').

(** The relation's indices are the premises' at a global weakening and a
    related substitution, and its shape relation is canonical. *)
Definition elimWf_hyp G0 Δ0 k1 A0 N0 (dR : DomRel G0 Δ0) γ e e' : Prop :=
  gwk_ok γ G0 G /\ SubRel G0 Γ⟦γ⟧ Δ0 e e' /\ k1 = l /\ A0 = A⟦γ⟧[e] /\ N0 = N⟦γ⟧[llift e] /\
  WfDom G0 Δ0 l A0 dR.

(** The motive at a tree: any two terms related at [Wf] reducing to it
    have related eliminations. *)
Definition elimWf_mrel G0 Δ0 k1 A0 N0 (dR : DomRel G0 Δ0) (t t' : tm) : Prop :=
  forall γ e e', elimWf_hyp G0 Δ0 k1 A0 N0 dR γ e e' ->
  forall s s', WfRel G0 Δ0 l A0 N0 dR s s' -> reds s t -> reds s' t' -> elimWf_goal G0 Δ0 γ e e' s s'.

(** The motive at a spine: at any tuples reducing to it and related
    indices, any two terms related at [Wf] reducing to the [nth]s have
    related eliminations. *)
Definition elimWf_mspine G0 Δ0 k1 A0 N0 (dR : DomRel G0 Δ0) (k cs cs' : tm) : Prop :=
  forall γ e e', elimWf_hyp G0 Δ0 k1 A0 N0 dR γ e e' ->
  forall c0 c0', nftm c0 -> nftm c0' -> reds c0 cs -> reds c0' cs' ->
  forall k' i i', NatRel G0 Δ0 k k' -> LRtm lzero G0 Δ0 (tyFin k) (tyFin k') i i' ->
  forall s s', WfRel G0 Δ0 l A0 N0 dR s s' ->
  reds s (tmNth l (tyWf l A0 N0) k c0 i) ->
  reds s' (tmNth l3 (tyWf l3 A'⟦γ⟧[e'] N'⟦γ⟧[llift e']) k' c0' i') ->
  elimWf_goal G0 Δ0 γ e e' s s'.

Lemma elimWf_c_rel {G0 Δ0 k1 A0 N0} {dR : DomRel G0 Δ0} {t t' w w'} :
  [ G0 ; Δ0 ⊢g t ⤳* w : tyWf k1 A0 N0 @ k1 ] -> [ G0 ; Δ0 ⊢g t' ⤳* w' : tyWf k1 A0 N0 @ k1 ] ->
  elimWf_mrel G0 Δ0 k1 A0 N0 dR w w' -> elimWf_mrel G0 Δ0 k1 A0 N0 dR t t'.
Proof.
  intros Hw Hw' IH γ e e' Hh s s' Hss Hs Hs'. apply (IH γ e e' Hh s s' Hss).
  - exact (reds_trans _ _ _ Hs (tmred_red _ _ _ _ _ _ _ Hw)).
  - exact (reds_trans _ _ _ Hs' (tmred_red _ _ _ _ _ _ _ Hw')).
Qed.

Lemma elimWf_c_ne {G0 Δ0 k1 A0 N0} {dR : DomRel G0 Δ0} {ν ν'} :
  [ G0 ; Δ0 ⊢ ν ~ ν' : tyWf k1 A0 N0 @ k1 ] -> elimWf_mrel G0 Δ0 k1 A0 N0 dR ν ν'.
Proof.
  intros Hν γ e e' (Hγ & He & E1 & E2 & E3 & HD) s s' Hss Hs _. subst k1 A0 N0.
  exact (elimWf_ne Hγ He HD Hss Hs (gne_tm_whne_l Hν)).
Qed.

Lemma elimWf_c_zero {G0 Δ0 k1 A0 N0} {dR : DomRel G0 Δ0} {k cs cs'} :
  [ G0 ; Δ0 ⊢g k ⤳* zero : tyNat @ lzero ] -> elimWf_mspine G0 Δ0 k1 A0 N0 dR k cs cs'.
Proof.
  intros Hk γ e e' (Hγ & He & E1 & E2 & E3 & HD) c0 c0' _ _ _ _ k' i i' _ Hi s s' Hss Hs _. subst k1 A0 N0.
  destruct (fin_idx_zero Hi Hk) as (ν & Hiν & Nν).
  destruct (nth_reds_zero l (tyWf l A⟦γ⟧[e] N⟦γ⟧[llift e]) (c0 := c0) (tmred_red _ _ _ _ _ _ _ Hk) Hiν Nν)
    as (X & HX & NX).
  exact (elimWf_ne Hγ He HD Hss (reds_trans _ _ _ Hs HX) NX).
Qed.

Lemma elimWf_c_vne {G0 Δ0 k1 A0 N0} {dR : DomRel G0 Δ0} {k ν cs cs'} :
  [ G0 ; Δ0 ⊢g k ⤳* ν : tyNat @ lzero ] -> [ G0 ; Δ0 ⊢ ν ~ ν : tyNat @ lzero ] ->
  elimWf_mspine G0 Δ0 k1 A0 N0 dR k cs cs'.
Proof.
  intros Hk Hν γ e e' (Hγ & He & E1 & E2 & E3 & HD) c0 c0' _ _ _ _ k' i i' _ Hi s s' Hss Hs _. subst k1 A0 N0.
  destruct (nth_reds_ne l (tyWf l A⟦γ⟧[e] N⟦γ⟧[llift e]) (c0 := c0) (i := i) (tmred_red _ _ _ _ _ _ _ Hk)
              (gne_tm_whne_l Hν)) as (X & HX & NX).
  exact (elimWf_ne Hγ He HD Hss (reds_trans _ _ _ Hs HX) NX).
Qed.

Lemma elimWf_c_succ {G0 Δ0 k1 A0 N0} {dR : DomRel G0 Δ0} {k m cs cs' w w'} :
  [ G0 ; Δ0 ⊢g k ⤳* succ m : tyNat @ lzero ] ->
  [ G0 ; Δ0 ⊢g cs ⤳* w : tySig k1 k1 (tyWf k1 A0 N0) (tyVec k1 (tyWf k1 A0 N0)⟨↑⟩ m⟨↑⟩) @ lmax k1 k1 ] ->
  [ G0 ; Δ0 ⊢g cs' ⤳* w' : tySig k1 k1 (tyWf k1 A0 N0) (tyVec k1 (tyWf k1 A0 N0)⟨↑⟩ m⟨↑⟩) @ lmax k1 k1 ] ->
  (forall la lb A1 B1 la' lb' A1' B1',
     lequiv (gL G0) la k1 -> lequiv (gL G0) lb k1 -> lequiv (gL G0) la' k1 -> lequiv (gL G0) lb' k1 ->
     [ G0 ; Δ0 ⊢ tyWf k1 A0 N0 ≈ A1 @ k1 ] ->
     [ G0 ; Δ0 ,, tyWf k1 A0 N0 @ k1 ⊢ tyVec k1 (tyWf k1 A0 N0)⟨↑⟩ m⟨↑⟩ ≈ B1 @ k1 ] ->
     [ G0 ; Δ0 ⊢ tyWf k1 A0 N0 ≈ A1' @ k1 ] ->
     [ G0 ; Δ0 ,, tyWf k1 A0 N0 @ k1 ⊢ tyVec k1 (tyWf k1 A0 N0)⟨↑⟩ m⟨↑⟩ ≈ B1' @ k1 ] ->
     elimWf_mrel G0 Δ0 k1 A0 N0 dR (tmFst la lb A1 B1 w) (tmFst la' lb' A1' B1' w')) ->
  (forall la lb A1 B1 la' lb' A1' B1',
     lequiv (gL G0) la k1 -> lequiv (gL G0) lb k1 -> lequiv (gL G0) la' k1 -> lequiv (gL G0) lb' k1 ->
     [ G0 ; Δ0 ⊢ tyWf k1 A0 N0 ≈ A1 @ k1 ] ->
     [ G0 ; Δ0 ,, tyWf k1 A0 N0 @ k1 ⊢ tyVec k1 (tyWf k1 A0 N0)⟨↑⟩ m⟨↑⟩ ≈ B1 @ k1 ] ->
     [ G0 ; Δ0 ⊢ tyWf k1 A0 N0 ≈ A1' @ k1 ] ->
     [ G0 ; Δ0 ,, tyWf k1 A0 N0 @ k1 ⊢ tyVec k1 (tyWf k1 A0 N0)⟨↑⟩ m⟨↑⟩ ≈ B1' @ k1 ] ->
     elimWf_mspine G0 Δ0 k1 A0 N0 dR m (tmSnd la lb A1 B1 w) (tmSnd la' lb' A1' B1' w')) ->
  elimWf_mspine G0 Δ0 k1 A0 N0 dR k cs cs'.
Proof.
  intros Hk Hcs Hcs' IHf IHs γ e e' Hh c0 c0' Nc0 Nc0' Hc0 Hc0' k' i i' Hkk Hi s s' Hss Hs Hs'.
  pose proof Hh as (Hγ & He & E1 & E2 & E3 & HD). subst k1 A0 N0.
  pose proof (ctx_glob _ _ _ (SubRel_ctx He)) as HG0.
  destruct (elimWf_loc Hγ HG0) as (_ & VAγ & VNγ & _).
  destruct (elimWf_at Hγ He) as (HA0 & EA & HN0 & EN & _).
  pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwl) as Hwl0.
  pose proof (lequiv_weaken _ _ _ _ (proj1 Hγ) H13) as H13'.
  destruct (NatRel_inv_succ Hkk Hk) as (m' & Hk' & Hmm).
  destruct (NatRel_escape Hmm) as (Hm & Hm' & _).
  pose proof (wf_tm_nf Hm) as Nm. pose proof (wf_tm_nf Hm') as Nm'.
  (* the annotations of the two sides' [nth]s *)
  destruct (V_wf Hwl0 (lequiv_sym _ _ _ H13') VAγ VNγ _ _ _ He) as [RW HRW].
  rewrite !subst_tyWf in HRW.
  destruct (escape_ty _ _ _ _ _ _ _ _ HRW) as (HW0 & HW0' & ET).
  pose proof (wf_ty_nf HW0) as NT. pose proof (wf_ty_nf HW0') as NT'.
  destruct (LR_vec_nat Hwl0 H13' (ex_intro _ _ HRW) Hmm) as [RV HRV].
  destruct (escape_ty _ _ _ _ _ _ _ _ HRV) as (_ & _ & EV0).
  pose proof (geq_ty_wk (wkr_shift1 _ _ _) (ext_wf_g HW0 Hwl0) EV0) as EV.
  pose proof (geq_ty_trans ET (geq_ty_sym ET)) as ETl. pose proof (geq_ty_trans EV (geq_ty_sym EV)) as EVl.
  pose proof (lequiv_refl _ _ Hwl0) as Hll. pose proof (lequiv_sym _ _ _ H13') as H31.
  pose proof (reds_trans _ _ _ Hc0 (tmred_red _ _ _ _ _ _ _ Hcs)) as Hc0w.
  pose proof (reds_trans _ _ _ Hc0' (tmred_red _ _ _ _ _ _ _ Hcs')) as Hc0w'.
  destruct (fin_idx_succ Hi Hk Hmm)
    as [(k2 & k3 & C & D & u & k2' & k3' & C' & D' & u' & Hi1 & Hi1')
       |[(k2 & k3 & C & D & j & k2' & k3' & C' & D' & j' & Hi1 & Hi1' & Hjj) | (ν & Hiν & Nν)]].
  - (* [inl]: the heads *)
    eapply (IHf l l _ _ l3 l3 _ _ Hll Hll H31 H31 ETl EVl ET EV γ e e' Hh s s' Hss).
    + eapply reds_trans; [exact Hs|]. eapply reds_trans; [exact (nth_reds_inl l _ NT Nm Nc0 (tmred_red _ _ _ _ _ _ _ Hk) Hi1)|].
      apply reds_fst, Hc0w.
    + eapply reds_trans; [exact Hs'|].
      eapply reds_trans; [exact (nth_reds_inl l3 _ NT' Nm' Nc0' (tmred_red _ _ _ _ _ _ _ Hk') Hi1')|].
      apply reds_fst, Hc0w'.
  - (* [inr]: [nth] at the tails *)
    eapply (IHs l l _ _ l3 l3 _ _ Hll Hll H31 H31 ETl EVl ET EV γ e e' Hh _ _ _ _
              (reds_snd _ _ _ _ _ _ Hc0w) (reds_snd _ _ _ _ _ _ Hc0w') m' j j' Hmm Hjj s s' Hss).
    + eapply reds_trans; [exact Hs|]. exact (nth_reds_inr l _ NT Nm Nc0 (tmred_red _ _ _ _ _ _ _ Hk) Hi1).
    + eapply reds_trans; [exact Hs'|]. exact (nth_reds_inr l3 _ NT' Nm' Nc0' (tmred_red _ _ _ _ _ _ _ Hk') Hi1').
  - (* a neutral index *)
    destruct (nth_reds_case_ne l (tyWf l A⟦γ⟧[e] N⟦γ⟧[llift e]) Nm Nc0 (tmred_red _ _ _ _ _ _ _ Hk) Hiν Nν) as (X & HX & NX).
    exact (elimWf_ne Hγ He HD Hss (reds_trans _ _ _ Hs HX) NX).
  Unshelve. all: cbn; repeat split; auto using ren_nf_ty, ren_nf.
  all: first [exact (proj1 NT) | exact (proj2 NT) | exact (proj1 NT') | exact (proj2 NT')].
Qed.

(** The [nth] in the induction hypothesis's body at a Kripke weakening of
    the shape and children's substitution, at related indices. *)
Lemma kwsub_cons3 {G0 Δ0} (ρ : kwk G0 Δ0) d a cs y n :
  llk (lcons (kwsub ρ (lcons (lcons d a) cs)) y) n = llk (lcons (lcons (lcons (kwsub ρ d) (ktm ρ a)) (ktm ρ cs)) y) n.
Proof. destruct n as [|[|[|n]]]; cbn; rewrite ?llk_kwsub; reflexivity. Qed.
Lemma kwsub_cons2 {G0 Δ0} (ρ : kwk G0 Δ0) d a cs n :
  llk (kwsub ρ (lcons (lcons d a) cs)) n = llk (lcons (lcons (kwsub ρ d) (ktm ρ a)) (ktm ρ cs)) n.
Proof. destruct n as [|[|n]]; rewrite llk_kwsub; cbn; rewrite ?llk_kwsub; reflexivity. Qed.

Lemma elimWf_nth_kw {G0 γ Δ0 e e' a a' cs cs'} (ρ : kwk G0 Δ0) {y y'} :
  gwk_ok γ G0 G ->
  SubRel G0 (Γ⟦γ⟧ ,, A⟦γ⟧ @ l ,, wfcsty l A⟦γ⟧ N⟦γ⟧ @ l) Δ0 (lcons (lcons e a) cs) (lcons (lcons e' a') cs') ->
  LRtm lzero (kw_G ρ) (kw_Δ ρ) (tyFin (ktml ρ N⟦γ⟧[llift e])[lsingle (ktm ρ a)])
    (tyFin (ktml ρ N⟦γ⟧[llift e'])[lsingle (ktm ρ a')]) y y' ->
  LRtm l (kw_G ρ) (kw_Δ ρ) (tyWf l (kty ρ A⟦γ⟧[e]) (ktml ρ N⟦γ⟧[llift e]))
    (tyWf l (kty ρ A⟦γ⟧[e']) (ktml ρ N⟦γ⟧[llift e']))
    (tmNth l (tyWf l (kty ρ A⟦γ⟧[e]) (ktml ρ N⟦γ⟧[llift e])) (ktml ρ N⟦γ⟧[llift e])[lsingle (ktm ρ a)] (ktm ρ cs) y)
    (tmNth l3 (tyWf l3 (kty ρ A'⟦γ⟧[e']) (ktml ρ N'⟦γ⟧[llift e'])) (ktml ρ N'⟦γ⟧[llift e'])[lsingle (ktm ρ a')]
       (ktm ρ cs') y').
Proof.
  intros Hγ HS Hy.
  pose proof (SubRel_kw _ _ _ ρ _ _ HS) as HSρ.
  rewrite !gwa_cext, gwa_wfcsty, gwa_comp_ctx, !gwa_comp_ty, gwa_comp_tm in HSρ.
  pose proof (elimWf_Vnth _ _ (gwk_ok_comp (kw_gok ρ) Hγ)) as Vn.
  rewrite !gwa_cext, gwa_wfcsty in Vn.
  repeat first [rewrite gwa_tyFin in Vn | rewrite gwa_tmNth in Vn | rewrite gwa_ren_ty in Vn | rewrite gwa_ren in Vn
               | rewrite gwa_tyWf in Vn | rewrite gwa_var in Vn].
  assert (Ne : LK nftm (kwsub ρ e)) by (intros n; rewrite llk_kwsub; apply ren_nf).
  assert (Ne' : LK nftm (kwsub ρ e')) by (intros n; rewrite llk_kwsub; apply ren_nf).
  assert (Xy : LRtm lzero (kw_G ρ) (kw_Δ ρ) (tyFin N⟦gwk_comp (kw_γ ρ) γ⟧⟨↑⟩)[kwsub ρ (lcons (lcons e a) cs)]
                 (tyFin N⟦gwk_comp (kw_γ ρ) γ⟧⟨↑⟩)[kwsub ρ (lcons (lcons e' a') cs')] y y').
  { rewrite (subst_ext_ty _ _ _ (kwsub_cons2 ρ e a cs)), (subst_ext_ty _ _ _ (kwsub_cons2 ρ e' a' cs')).
    rewrite !finv_subst, <- !kγ_tml by assumption. exact Hy. }
  pose proof (Vn _ _ _ (SubRel_cons HSρ Xy)) as X.
  rewrite (subst_ext_ty _ _ _ (kwsub_cons3 ρ e a cs y)), (subst_ext_ty _ _ _ (kwsub_cons3 ρ e' a' cs' y')),
    (subst_ext _ _ _ (kwsub_cons3 ρ e a cs y)), (subst_ext _ _ _ (kwsub_cons3 ρ e' a' cs' y')) in X.
  rewrite !nthv_subst, !shift_subst_ty in X by assumption. cbn [ldrop] in X.
  rewrite !subst_tyWf, <- !kγ_ty, <- !kγ_tml in X.
  exact X.
Qed.

(** At a [sup_f] pair, given the motive at the children's spine: the steps
    at the shape, the children and the synthesized induction hypotheses are
    related, and both [elim_Wf]s step to them. *)
Lemma elimWf_step {G0 Δ0} {dR : DomRel G0 Δ0} {k k' C C' P P' a a' cs cs' γ e e'} :
  gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' -> WfDom G0 Δ0 l A⟦γ⟧[e] dR ->
  lequiv (gL G0) k l -> lequiv (gL G0) k' l ->
  [ G0 ; Δ0 ⊢ A⟦γ⟧[e] ≈ C @ l ] -> [ G0 ; Δ0 ⊢ A⟦γ⟧[e] ≈ C' @ l ] ->
  [ G0 ; Δ0 ,, A⟦γ⟧[e] @ l ⊢ N⟦γ⟧[llift e] ≈ P : tyNat @ lzero ] ->
  [ G0 ; Δ0 ,, A⟦γ⟧[e] @ l ⊢ N⟦γ⟧[llift e] ≈ P' : tyNat @ lzero ] ->
  (forall ρ : kwk G0 Δ0, dR ρ (ktm ρ a) (ktm ρ a')) ->
  (forall ρ : kwk G0 Δ0,
     VecSp (kw_G ρ) (kw_Δ ρ) l (kty ρ A⟦γ⟧[e]) (ktml ρ N⟦γ⟧[llift e]) (fun ρ' => dR (kw_comp ρ ρ'))
       (ktml ρ N⟦γ⟧[llift e])[lsingle (ktm ρ a)] (ktm ρ cs) (ktm ρ cs')) ->
  (forall ρ : kwk G0 Δ0,
     elimWf_mspine (kw_G ρ) (kw_Δ ρ) l (kty ρ A⟦γ⟧[e]) (ktml ρ N⟦γ⟧[llift e]) (fun ρ' => dR (kw_comp ρ ρ'))
       (ktml ρ N⟦γ⟧[llift e])[lsingle (ktm ρ a)] (ktm ρ cs) (ktm ρ cs')) ->
  nftm (tmSupf k C P a cs) -> nftm (tmSupf k' C' P' a' cs') ->
  LRtm l' G0 Δ0 M⟦γ⟧[llift e][lsingle (tmSupf k C P a cs)] M⟦γ⟧[llift e][lsingle (tmSupf k C P a cs)]
    c⟦γ⟧[llift (llift (llift e))][lsingle3 a cs
      (wfIH l l' A⟦γ⟧[e] N⟦γ⟧[llift e] M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))] a cs)]
    c'⟦γ⟧[llift (llift (llift e'))][lsingle3 a' cs'
      (wfIH l3 l4 A'⟦γ⟧[e'] N'⟦γ⟧[llift e'] M'⟦γ⟧[llift e'] c'⟦γ⟧[llift (llift (llift e'))] a' cs')] /\
  [ G0 ; Δ0 ⊢g tmElimWf l l' A⟦γ⟧[e] N⟦γ⟧[llift e] M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))]
                 (tmSupf k C P a cs)
             ⤳* c⟦γ⟧[llift (llift (llift e))][lsingle3 a cs
                  (wfIH l l' A⟦γ⟧[e] N⟦γ⟧[llift e] M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))] a cs)]
             : M⟦γ⟧[llift e][lsingle (tmSupf k C P a cs)] @ l' ] /\
  [ G0 ; Δ0 ⊢g tmElimWf l3 l4 A'⟦γ⟧[e'] N'⟦γ⟧[llift e'] M'⟦γ⟧[llift e'] c'⟦γ⟧[llift (llift (llift e'))]
                 (tmSupf k' C' P' a' cs')
             ⤳* c'⟦γ⟧[llift (llift (llift e'))][lsingle3 a' cs'
                  (wfIH l3 l4 A'⟦γ⟧[e'] N'⟦γ⟧[llift e'] M'⟦γ⟧[llift e'] c'⟦γ⟧[llift (llift (llift e'))] a' cs')]
             : M⟦γ⟧[llift e][lsingle (tmSupf k C P a cs)] @ l' ].
Proof.
  intros Hγ He HD Hk Hk' HC HC' HP HP' Ha Hsp IH Nw Nw'.
  cbn in Nw, Nw'. destruct Nw as (_ & _ & Na & Ncs). destruct Nw' as (_ & _ & Na' & Ncs').
  pose proof (SubRel_ctx He) as HΔ0. pose proof (ctx_glob _ _ _ HΔ0) as HG0.
  destruct (SubRel_nf _ _ _ _ _ He) as [Ne Ne'].
  destruct (elimWf_loc Hγ HG0) as (HNγ & VAγ & VNγ & VMγ & Vcsγ & Vihγ & Vcγ).
  destruct (elimWf_at Hγ He) as (HA0 & EA & HN0 & EN & HM0 & EM & HC0 & HI0 & Ec).
  pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwl) as Hwl0.
  pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwl') as Hwl'0.
  assert (Hwlz : lwf (gL G0) lzero) by exact I.
  pose proof (lequiv_weaken _ _ _ _ (proj1 Hγ) H13) as H13'.
  pose proof (lequiv_weaken _ _ _ _ (proj1 Hγ) H24) as H24'.
  destruct (V_wf Hwl0 (lequiv_refl _ _ Hwl0) (VTyG_refl_l VAγ) (VTmG_refl_l VNγ) _ _ _ He) as [RW HRW].
  rewrite !subst_tyWf in HRW. destruct (escape_ty _ _ _ _ _ _ _ _ HRW) as (HW0 & HW0' & _).
  pose proof (wf_ty_nf HW0) as NW. pose proof (wf_ty_nf HW0') as NW'.
  pose proof (wf_ty_nf HA0) as NA. pose proof (wf_ty_nf HM0) as NM.
  pose proof (wf_tm_nf (eqtm_wf_l ge_typeof (geq_tm_sound Ec))) as Nc.
  (* the shape, at the identity world *)
  assert (Xa : LRtm l G0 Δ0 A⟦γ⟧[e] A⟦γ⟧[e'] a a').
  { destruct (HD (kid HΔ0)) as [A1 HA1]. pose proof (Ha (kid HΔ0)) as Haa.
    rewrite (kty_kid HΔ0 _ NA) in HA1. rewrite (ktm_kid HΔ0 _ Na), (ktm_kid HΔ0 _ Na') in Haa.
    eapply LRtm_irrel_r; [exact (LRtm_of HA1 Haa) | exact (VTy_refl_l (VTyG_loc VAγ) _ _ _ He)]. }
  pose proof (LRtm_geq Xa) as Ea. destruct (LRtm_escape Xa) as [Hat Ha't].
  pose proof (SubRel_cons He Xa) as HS1.
  (* the arity at the shape *)
  pose proof (VTmG_loc VNγ _ _ _ HS1) as XN. rewrite !subst_tyNat in XN.
  apply LRtm_nat in XN. rewrite <- !lift_single_tm in XN by assumption. rename XN into Hkk.
  pose proof (VTmG_loc (VTmG_refl_l VNγ) _ _ _ HS1) as XN. rewrite !subst_tyNat in XN.
  apply LRtm_nat in XN. rewrite <- !lift_single_tm in XN by assumption. rename XN into Hkk0.
  (* the children, at [Vec] *)
  assert (Xcs0 : LRtm l G0 Δ0 (wfcsty l A⟦γ⟧ N⟦γ⟧)[lcons e a] (wfcsty l A⟦γ⟧ N⟦γ⟧)[lcons e' a'] cs cs').
  { destruct (Vcsγ _ _ _ HS1) as [RC HRC]. exists RC; split; [exact HRC|].
    rewrite <- (lift_single_ty _ e a Ne), <- (lift_single_ty _ e' a' Ne'), !wfcsty_llift, !Wf_E5 in HRC
      by assumption.
    refine (LR_of_VecSp_own Hwl0 HW0 HD Hkk Ncs Ncs' _ _ _ HRC).
    intros ρ. rewrite ktm_single. exact (Hsp ρ). }
  pose proof Xcs0 as Xcs.
  rewrite <- (lift_single_ty _ e a Ne), <- (lift_single_ty _ e' a' Ne'), !wfcsty_llift, !Wf_E5 in Xcs
    by assumption.
  pose proof (LRtm_geq Xcs) as Ecs. destruct (LRtm_escape Xcs) as [Hcst Hcs't].
  pose proof (SubRel_cons HS1 Xcs0) as HS2.
  (* the induction hypothesis's type *)
  destruct (Vihγ _ _ _ HS2) as [RI HRI].
  rewrite <- (lift_single2_ty e Ne _ a cs), <- (lift_single2_ty e' Ne' _ a' cs'), !wfihty_llift2, !Wf_E4 in HRI
    by assumption.
  destruct (escape_ty _ _ _ _ _ _ _ _ HRI) as (HIT & _ & _).
  destruct (LR_inv_pi HRI (tyred_refl _ _ HIT)) as (p3 & p4 & P2 & Q2 & domRi & codRi & Pi & domAdi & codAdi & HRRi).
  destruct Pi as [_ Hp3 Hp4 _ _ _ _ HBa2 HP2 HCod HQ2 HPP2 HQQ2].
  pose proof (Wf_IH_eq ge_typeof ge_notV H13' H24' HA0 (geq_ty_sound EA) HN0 (geq_tm_sound EN) HM0
                (geq_ty_sound EM) (geq_tm_sound Ec) Hat Ha't (geq_tm_sound Ea) Hcst (geq_tm_sound Ecs)) as Dih.
  pose proof (Wf_IH_body_eq ge_typeof ge_notV H13' H24' HA0 (geq_ty_sound EA) HN0 (geq_tm_sound EN) HM0
                (geq_ty_sound EM) (geq_tm_sound Ec) Hat Ha't (geq_tm_sound Ea) Hcst (geq_tm_sound Ecs)) as Dbody.
  rewrite Wf_E4 in Dih by exact NW.
  pose proof (eqtm_wf_l ge_typeof Dbody) as Hbody. pose proof (eqtm_wf_r ge_typeof Dbody) as Hbody'.

  (* the arity's [Fin] at the shape, left and right *)
  destruct (LR_fin_nat HΔ0 Hkk) as [RF HRF]. destruct (escape_ty _ _ _ _ _ _ _ _ HRF) as (_ & HF' & EF).
  pose proof (lequiv_wf_r _ _ _ H24') as Hwl4.
  assert (HleI : lmeasure lzero <= lmeasure (lmax lzero l')) by (rewrite !lmeasure_max; lia).
  assert (HleI' : lmeasure l' <= lmeasure (lmax lzero l')) by (rewrite !lmeasure_max; lia).
  assert (Ki : forall (ρ : kwk G0 Δ0) y y' (hy : domRi ρ y y') la lb la' lb' A1 B1 A1' B1',
            lequiv (gL G0) la lzero -> lequiv (gL G0) lb l' -> lequiv (gL G0) la' lzero -> lequiv (gL G0) lb' l' ->
            [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ (tyFin N⟦γ⟧[llift e][lsingle a]) ≈ A1 @ lzero ] ->
            [ kw_G ρ ; kw_Δ ρ ,, kty ρ (tyFin N⟦γ⟧[llift e][lsingle a]) @ lzero
                ⊢ ktyl ρ (wfcod l A⟦γ⟧[e] N⟦γ⟧[llift e] M⟦γ⟧[llift e] a cs) ≈ B1 @ l' ] ->
            [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ P2 ≈ A1' @ lzero ] ->
            [ kw_G ρ ; kw_Δ ρ ,, kty ρ P2 @ lzero ⊢ ktyl ρ Q2 ≈ B1' @ l' ] ->
            codRi ρ y y' hy
              (app (ktm ρ (wfIH l l' A⟦γ⟧[e] N⟦γ⟧[llift e] M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))] a cs))
                 la lb A1 B1 y)
              (app (ktm ρ (wfIH l3 l4 A'⟦γ⟧[e'] N'⟦γ⟧[llift e'] M'⟦γ⟧[llift e'] c'⟦γ⟧[llift (llift (llift e'))]
                             a' cs'))
                 la' lb' A1' B1' y')).
  { intros ρ y y' hy la lb la' lb' A1 B1 A1' B1' H1 H2 H1' H2' HA1 HB1 HA1' HB1'.
    pose proof (kw_lwf ρ Hwl'0) as Hwl'ρ. pose proof (kw_lwf ρ Hwl4) as Hwl4ρ.
    pose proof (kw_lequiv ρ H24') as H24ρ.
    (* the indices *)
    pose proof (domAdi ρ) as DOM. apply (proj2 (LogRel_stage _ _ _ _ _ _ _ HleI)) in DOM.
    pose proof (LRtm_of DOM hy) as Y. rewrite kty_tyFin, ktm_single in Y.
    pose proof (NatRel_kw ρ _ _ Hkk0) as Hkk0ρ. pose proof (NatRel_kw ρ _ _ Hkk) as Hkkρ.
    rewrite !ktm_single in Hkk0ρ, Hkkρ.
    pose proof (LRtm_irrel_r Y (LR_fin_nat (kw_ctx ρ) Hkk0ρ)) as Y0.
    pose proof (LRtm_irrel_r Y (LR_fin_nat (kw_ctx ρ) Hkkρ)) as Y1.
    destruct (LRtm_escape Y) as [Hy Hy']. pose proof (LRtm_geq Y) as Eyy.
    (* the [nth]s, related at [Wf] *)
    destruct (elimWf_nth_kw ρ Hγ HS2 Y0) as (RN & HRN & Hn).
    apply (proj1 (LR_wf_rel HRN (WfDom_comp ρ HD) _ _)) in Hn.
    (* the spine's motive there *)
    assert (He1 : SubRel (kw_G ρ) Γ⟦gwk_comp (kw_γ ρ) γ⟧ (kw_Δ ρ) (kwsub ρ e) (kwsub ρ e')).
    { pose proof (SubRel_kw _ _ _ ρ _ _ He) as Z. now rewrite gwa_comp_ctx in Z. }
    assert (Hh : elimWf_hyp (kw_G ρ) (kw_Δ ρ) l (kty ρ A⟦γ⟧[e]) (ktml ρ N⟦γ⟧[llift e])
                   (fun ρ' => dR (kw_comp ρ ρ')) (gwk_comp (kw_γ ρ) γ) (kwsub ρ e) (kwsub ρ e')).
    { refine (conj (gwk_ok_comp (kw_gok ρ) Hγ) (conj He1 (conj eq_refl (conj (kγ_ty ρ A γ e)
                (conj (kγ_tml ρ N γ e) _))))).
      exact (WfDom_comp ρ HD). }
    assert (Ncsρ : nftm (ktm ρ cs)) by apply ren_nf. assert (Ncs'ρ : nftm (ktm ρ cs')) by apply ren_nf.
    assert (Hr' : reds (tmNth l3 (tyWf l3 (kty ρ A'⟦γ⟧[e']) (ktml ρ N'⟦γ⟧[llift e']))
                          (ktml ρ N'⟦γ⟧[llift e'])[lsingle (ktm ρ a')] (ktm ρ cs') y')
                       (tmNth l3 (tyWf l3 A'⟦gwk_comp (kw_γ ρ) γ⟧[kwsub ρ e'] N'⟦gwk_comp (kw_γ ρ) γ⟧[llift (kwsub ρ e')])
                          (ktml ρ N'⟦γ⟧[llift e'])[lsingle (ktm ρ a')] (ktm ρ cs') y'))
      by (rewrite <- kγ_ty, <- kγ_tml; apply reds_refl).
    pose proof (IH ρ _ _ _ Hh (ktm ρ cs) (ktm ρ cs') Ncsρ Ncs'ρ (reds_refl _) (reds_refl _)
                  _ _ _ Hkkρ Y1 _ _ Hn (reds_refl _) Hr') as X.
    unfold elimWf_goal in X.
    rewrite <- (kγ_tyl ρ M γ e), <- (kγ_ty ρ A γ e), <- (kγ_tml ρ N γ e), <- (kγ_tm3 ρ c γ e),
      <- (kγ_ty ρ A' γ e'), <- (kγ_tml ρ N' γ e'), <- (kγ_tyl ρ M' γ e'), <- (kγ_tm3 ρ c' γ e') in X.
    (* the λs' codomain relation, at the children's elimination *)
    assert (NWρ : nfty (tyWf l (kty ρ A⟦γ⟧[e]) (ktml ρ N⟦γ⟧[llift e]))) by (cbn; split; [apply ren_nf_ty | apply ren_nf]).
    assert (NW'ρ : nfty (tyWf l3 (kty ρ A'⟦γ⟧[e']) (ktml ρ N'⟦γ⟧[llift e'])))
      by (cbn; split; [apply ren_nf_ty | apply ren_nf]).
    assert (NMρ : nfty (ktyl ρ M⟦γ⟧[llift e])) by apply ren_nf_ty.
    assert (NM'ρ : nfty (ktyl ρ M'⟦γ⟧[llift e'])) by apply ren_nf_ty.
    assert (Naρ : nftm (ktm ρ a)) by apply ren_nf. assert (Na'ρ : nftm (ktm ρ a')) by apply ren_nf.
    assert (Ncρ : nftm (ktm3 ρ c⟦γ⟧[llift (llift (llift e))])) by apply ren_nf.
    assert (Nc'ρ : nftm (ktm3 ρ c'⟦γ⟧[llift (llift (llift e'))])) by apply ren_nf.
    pose proof (wf_tm_nf Hy) as Ny. pose proof (wf_tm_nf Hy') as Ny'.
    pose proof (codAdi ρ y y' hy) as COD. apply LR_refl_l in COD.
    rewrite ktyl_wfcod, wfcod_single in COD by assumption.
    pose proof (LRtm_inv (proj2 (LogRel_stage _ _ _ _ _ _ _ HleI') COD) X) as Rx.
    apply (LR_red_tm _ _ _ _ _ _ _ _ COD _ _ _ _ Rx).
    - (* the left λ steps to the children's elimination *)
      unfold wfIH. rewrite ktm_lam, ktml_wfbody, kty_tyFin, ktm_single.
      pose proof (kw_tm_l ρ HBa2 Hwlz Hbody) as Hbρ. rewrite kty_tyFin, ktm_single, ktml_wfbody, ktyl_wfcod in Hbρ.
      pose proof (kw_ty_l ρ HBa2 Hwlz HCod) as HCρ. rewrite kty_tyFin, ktm_single, ktyl_wfcod in HCρ.
      pose proof (kw_ty ρ HBa2) as HBaρ. rewrite kty_tyFin, ktm_single in HBaρ.
      rewrite kty_tyFin, ktm_single in HA1, HB1. rewrite ktyl_wfcod in HB1.
      pose proof (tmred_beta (kw_lwf ρ Hwlz) Hwl'ρ (kw_lequiv ρ H1) (kw_lequiv ρ H2) HBaρ HCρ Hbρ Hy
                    (geq_ty_sound HA1) (geq_ty_sound HB1)) as Z.
      rewrite wfbody_single, wfcod_single in Z by assumption. exact Z.
    - (* the right λ too, its body moved to the left domain's type *)
      unfold wfIH. rewrite ktm_lam, ktml_wfbody, kty_tyFin, ktm_single.
      assert (HΔ5 : [ G0 ; Δ0 ,, tyFin N'⟦γ⟧[llift e'][lsingle a'] @ lzero ⊢g ]) by exact (ext_wf_g HF' Hwlz).
      pose proof (stab_tm ge_typeof (geq_ty_sound EF) (lequiv_refl _ _ Hwlz) HΔ5 Hbody') as Hb'.
      apply (fun H => wf_lconv _ _ _ _ _ _ _ H (lequiv_sym _ _ _ H24')) in Hb'.
      pose proof (kw_tm_l ρ HF' Hwlz Hb') as Hb'ρ. rewrite kty_tyFin, ktm_single, ktml_wfbody, ktyl_wfcod in Hb'ρ.
      pose proof (stab_ty ge_typeof (geq_ty_sound EF) (lequiv_refl _ _ Hwlz) HΔ5 HCod) as HCd'.
      apply (fun H => lconv_ty H H24') in HCd'.
      pose proof (kw_ty_l ρ HF' Hwlz HCd') as HC'ρ. rewrite kty_tyFin, ktm_single, ktyl_wfcod in HC'ρ.
      pose proof (kw_ty ρ HF') as HF'ρ. rewrite kty_tyFin, ktm_single in HF'ρ.
      pose proof (kw_geq_ty ρ EF) as EFρ. rewrite !kty_tyFin, !ktm_single in EFρ.
      assert (Hy'5 : [ kw_G ρ ; kw_Δ ρ ⊢g y' : tyFin (ktml ρ N'⟦γ⟧[llift e'])[lsingle (ktm ρ a')] @ lzero ]).
      { eapply wf_conv; [exact Hy' | rewrite ge_typeof;
          first [apply eqty_sym, geq_ty_sound, EFρ | apply geq_ty_sound, EFρ]]. }
      pose proof (kw_geq_ty ρ HPP2) as KP2. rewrite kty_tyFin, ktm_single in KP2.
      assert (HA1c : [ kw_G ρ ; kw_Δ ρ ⊢g tyFin (ktml ρ N'⟦γ⟧[llift e'])[lsingle (ktm ρ a')] ≅ A1' @ lzero ]).
      { apply geq_ty_sound. eapply geq_ty_trans; [apply geq_ty_sym, EFρ|]. exact (geq_ty_trans KP2 HA1'). }
      pose proof (kw_geq_ty_l ρ HBa2 Hwlz HQQ2) as KQ2. rewrite kty_tyFin, ktm_single, ktyl_wfcod in KQ2.
      pose proof (kw_ty ρ HBa2) as HBaρ. rewrite kty_tyFin, ktm_single in HBaρ.
      assert (HB1c : [ kw_G ρ ; kw_Δ ρ ,, tyFin (ktml ρ N'⟦γ⟧[llift e'])[lsingle (ktm ρ a')] @ lzero
                       ⊢g wfcod l (kty ρ A⟦γ⟧[e]) (ktml ρ N⟦γ⟧[llift e]) (ktyl ρ M⟦γ⟧[llift e]) (ktm ρ a) (ktm ρ cs)
                          ≅ B1' @ l4 ]).
      { eapply eqty_lconv; [|exact (lequiv_sym _ _ _ H24ρ)].
        eapply (stab_eqty ge_typeof (geq_ty_sound EFρ) (lequiv_refl _ _ (kw_lwf ρ Hwlz)) (ext_wf_g HF'ρ (kw_lwf ρ Hwlz))).
        apply geq_ty_sound. eapply geq_ty_trans; [exact KQ2|].
        eapply geq_ty_ctxconv; [apply eqty_sym, geq_ty_sound, KP2 | now apply lequiv_refl
                               | apply ext_wf_g; [exact HBaρ | exact (kw_lwf ρ Hwlz)] | exact HB1']. }
      pose proof (tmred_beta (kw_lwf ρ Hwlz) Hwl4ρ (kw_lequiv ρ H1') (kw_lequiv ρ (lequiv_trans _ _ _ _ H2' H24'))
                    HF'ρ HC'ρ Hb'ρ Hy'5 HA1c HB1c) as Z.
      assert (NA'ρ : nfty (kty ρ A'⟦γ⟧[e'])) by apply ren_nf_ty.
      rewrite wfbody_single, wfcod_single in Z by assumption.
      pose proof (kw_ty_l ρ HBa2 Hwlz HCod) as HCρ. rewrite kty_tyFin, ktm_single, ktyl_wfcod in HCρ.
      pose proof (wf_ty_func ge_typeof HCρ (lsub_eq_single ge_typeof Hy' Hy (eqtm_sym _ _ _ _ _ _ _ (geq_tm_sound Eyy))))
        as Ecod.
      rewrite !wfcod_single in Ecod by assumption.
      eapply tmred_lconv; [eapply tmred_conv; [apply ge_typeof | exact Z |] | exact H24ρ].
      eapply eqty_lconv; [exact Ecod | exact (lequiv_sym _ _ _ H24ρ)]. }

  (* the λs, generically equal by extensionality at the index *)
  assert (EPi2 : [ G0 ; Δ0 ⊢g tyPi lzero l' (tyFin N⟦γ⟧[llift e][lsingle a])
                     (wfcod l A⟦γ⟧[e] N⟦γ⟧[llift e] M⟦γ⟧[llift e] a cs) ≅ tyPi p3 p4 P2 Q2 @ lmax lzero l' ])
    by (apply geq_ty_sound, geq_ty_pi; auto using lequiv_sym).
  pose proof (eqtm_wf_l ge_typeof Dih) as Hλ. pose proof (eqtm_wf_r ge_typeof Dih) as Hλ'.
  assert (Hw1 : wk1 : (Δ0 ,, tyFin N⟦γ⟧[llift e][lsingle a] @ lzero) ≤ Δ0) by (constructor; constructor).
  assert (Hr1 : wkr ↑ (Δ0 ,, tyFin N⟦γ⟧[llift e][lsingle a] @ lzero) Δ0) by exact (wkr_shift1 _ _ _).
  pose proof (ext_wf_g HBa2 Hwlz) as HΔa.
  pose proof (domAdi (kw_loc wk1 Hw1 HΔa)) as DOM1.
  unfold kty, kw_loc in DOM1; cbn [kw_G kw_Δ kw_γ kw_r gwa] in DOM1; change (wk_ren wk1) with ↑ in DOM1.
  apply (proj2 (LogRel_stage _ _ _ _ _ _ _ HleI)) in DOM1.
  pose proof (LRtm_inv DOM1 (var0_LRtm (ex_intro _ _ DOM1) HΔa)) as hv.
  assert (RBa0 : [ G0 ; Δ0 ⊢ tyFin N⟦γ⟧[llift e][lsingle a] ≈ tyFin N⟦γ⟧[llift e][lsingle a] @ lzero ])
    by exact (geq_ty_trans HPP2 (geq_ty_sym HPP2)).
  assert (RCod : [ G0 ; Δ0 ,, tyFin N⟦γ⟧[llift e][lsingle a] @ lzero
                   ⊢ wfcod l A⟦γ⟧[e] N⟦γ⟧[llift e] M⟦γ⟧[llift e] a cs
                     ≈ wfcod l A⟦γ⟧[e] N⟦γ⟧[llift e] M⟦γ⟧[llift e] a cs @ l' ])
    by exact (geq_ty_trans HQQ2 (geq_ty_sym HQQ2)).
  assert (HΔaa : [ G0 ; Δ0 ,, tyFin N⟦γ⟧[llift e][lsingle a] @ lzero
                     ,, (tyFin N⟦γ⟧[llift e][lsingle a])⟨↑⟩ @ lzero ⊢g ])
    by (apply ext_wf_g; [exact (wf_ty_wkr Hr1 HΔa HBa2) | exact Hwlz]).
  assert (HΔaP : [ G0 ; Δ0 ,, tyFin N⟦γ⟧[llift e][lsingle a] @ lzero ,, P2⟨↑⟩ @ lzero ⊢g ])
    by (apply ext_wf_g; [exact (wf_ty_wkr Hr1 HΔa HP2) | exact Hwlz]).
  pose proof (Ki (kw_loc wk1 Hw1 HΔa) (var 0) (var 0) hv lzero l' lzero l'
                (tyFin N⟦γ⟧[llift e][lsingle a])⟨↑⟩ (wfcod l A⟦γ⟧[e] N⟦γ⟧[llift e] M⟦γ⟧[llift e] a cs)⟨rlift ↑⟩
                (tyFin N⟦γ⟧[llift e][lsingle a])⟨↑⟩ (wfcod l A⟦γ⟧[e] N⟦γ⟧[llift e] M⟦γ⟧[llift e] a cs)⟨rlift ↑⟩
                (lequiv_refl _ _ Hwlz) (lequiv_refl _ _ Hwl'0) (lequiv_refl _ _ Hwlz) (lequiv_refl _ _ Hwl'0))
    as K0.
  unfold kty, ktyl, ktm, kw_loc in K0; cbn [kw_G kw_Δ kw_γ kw_r gwa] in K0; change (wk_ren wk1) with ↑ in K0.
  pose proof (K0 (geq_ty_wk Hr1 HΔa RBa0) (geq_ty_wk (wkr_up _ _ _ _ _ Hr1) HΔaa RCod)
                (geq_ty_wk Hr1 HΔa (geq_ty_sym HPP2))) as K1.
  unshelve epose proof (K1 _) as K2.
  { eapply geq_ty_ctxconv; [| apply lequiv_refl, Hwlz | exact HΔaP |].
    - apply geq_ty_sound. exact (geq_ty_wk Hr1 HΔa HPP2).
    - apply geq_ty_sym. exact (geq_ty_wk (wkr_up _ _ _ _ _ Hr1) HΔaa HQQ2). }
  pose proof (codAdi (kw_loc wk1 Hw1 HΔa) (var 0) (var 0) hv) as COD1.
  unfold ktyl, kw_loc in COD1; cbn [kw_G kw_Δ kw_γ kw_r gwa] in COD1; change (wk_ren wk1) with ↑ in COD1.
  destruct (escape_tm _ _ _ _ _ _ _ _ COD1 _ _ K2) as (_ & _ & Hg).
  rewrite liftshift_single_var_ty in Hg by exact (wf_ty_nf HCod).
  pose proof (geq_tm_funext Hwlz Hwl'0 HBa2 HCod Hλ Hλ' Hg) as GEQ.
  assert (PRih : PiRel G0 Δ0 lzero l' p3 p4 (tyFin N⟦γ⟧[llift e][lsingle a])
                   (wfcod l A⟦γ⟧[e] N⟦γ⟧[llift e] M⟦γ⟧[llift e] a cs) P2 Q2 domRi codRi
                   (wfIH l l' A⟦γ⟧[e] N⟦γ⟧[llift e] M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))] a cs)
                   (wfIH l3 l4 A'⟦γ⟧[e'] N'⟦γ⟧[llift e'] M'⟦γ⟧[llift e'] c'⟦γ⟧[llift (llift (llift e'))] a' cs')).
  { eexists _, _. refine (conj (tmred_refl _ _ _ Hλ) (conj _ (conj _ (conj _ (conj GEQ (conj _ Ki)))))).
    - apply tmred_refl. eapply wf_conv; [exact Hλ' | rewrite ge_typeof; apply eqty_sym, EPi2].
    - unfold wfIH; apply whnf_lam.
    - unfold wfIH; apply whnf_lam.
    - eapply geq_tm_conv; [exact GEQ | exact EPi2]. }
  pose proof (LRtm_of HRI (proj2 (HRRi _ _) PRih)) as Xh.
  (* the step, at the shape, the children and the induction hypothesis *)
  assert (Xh0 : LRtm (lmax lzero l') G0 Δ0 (wfihty l l' A⟦γ⟧ N⟦γ⟧ M⟦γ⟧)[lcons (lcons e a) cs]
                  (wfihty l l' A⟦γ⟧ N⟦γ⟧ M⟦γ⟧)[lcons (lcons e' a') cs']
                  (wfIH l l' A⟦γ⟧[e] N⟦γ⟧[llift e] M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))] a cs)
                  (wfIH l3 l4 A'⟦γ⟧[e'] N'⟦γ⟧[llift e'] M'⟦γ⟧[llift e'] c'⟦γ⟧[llift (llift (llift e'))] a' cs')).
  { rewrite <- (lift_single2_ty e Ne _ a cs), <- (lift_single2_ty e' Ne' _ a' cs'), !wfihty_llift2, !Wf_E4
      by assumption.
    exact Xh. }
  pose proof (Vcγ _ _ _ (SubRel_cons HS2 Xh0)) as Xc.
  rewrite <- (lift_single3_ty e Ne), <- (lift_single3_ty e' Ne'), <- (lift_single3 e Ne), <- (lift_single3 e' Ne'),
    !wfstepty_llift3, !Wf_E6 in Xc by assumption.
  (* the [sup_f] at the [elim_Wf]'s annotations, related to the trees *)
  pose proof (geq_tm_refl_l Ea) as Eaa. pose proof (geq_tm_refl_l Ecs) as Ecscs.
  assert (RAA : [ G0 ; Δ0 ⊢ A⟦γ⟧[e] ≈ A⟦γ⟧[e] @ l ]) by exact (geq_ty_trans EA (geq_ty_sym EA)).
  assert (RNN : [ G0 ; Δ0 ,, A⟦γ⟧[e] @ l ⊢ N⟦γ⟧[llift e] ≈ N⟦γ⟧[llift e] : tyNat @ lzero ])
    by exact (geq_tm_trans EN (geq_tm_sym EN)).
  pose proof (geq_tm_supf (lequiv_sym _ _ _ Hk) HA0 HC HN0 HP Eaa Ecscs) as Dw.
  pose proof (geq_tm_supf (lequiv_sym _ _ _ Hk') HA0 HC' HN0 HP' Ea Ecs) as Dw'.
  pose proof (geq_tm_trans (geq_tm_sym Dw) Dw') as Dww'.
  pose proof (eqtm_wf_l ge_typeof (geq_tm_sound Dw)) as Hsc. pose proof (eqtm_wf_r ge_typeof (geq_tm_sound Dw)) as Hw0.
  pose proof (eqtm_wf_r ge_typeof (geq_tm_sound Dw')) as Hw0'.
  assert (Nsup : WfNf G0 Δ0 l A⟦γ⟧[e] N⟦γ⟧[llift e] dR
                   (tmSupf l A⟦γ⟧[e] N⟦γ⟧[llift e] a cs) (tmSupf k' C' P' a' cs'))
    by (apply wfnf_sup; first [now apply lequiv_refl | assumption]).
  assert (Nww : WfNf G0 Δ0 l A⟦γ⟧[e] N⟦γ⟧[llift e] dR (tmSupf k C P a cs) (tmSupf k' C' P' a' cs'))
    by (apply wfnf_sup; assumption).
  pose proof (elimWf_rel Hγ He HD (wfrel _ _ _ _ _ _ _ _ _ _ (tmred_refl _ _ _ Hsc) (tmred_refl _ _ _ Hw0') Dw' Nsup))
    as Rsw'.
  pose proof (elimWf_rel Hγ He HD (wfrel _ _ _ _ _ _ _ _ _ _ (tmred_refl _ _ _ Hw0) (tmred_refl _ _ _ Hw0') Dww' Nww))
    as Rww'.
  pose proof (LRtm_trans Rsw' (LRtm_sym Rww')) as Rsw. pose proof (LRtm_trans Rww' (LRtm_sym Rww')) as Rww.
  pose proof (elimWf_mot Hγ (SubRel_refl_l He) Rsw) as XTsw.
  pose proof (elimWf_mot Hγ (SubRel_refl_l He) Rww) as XTww.
  pose proof (LRtm_irrel_r (LRtm_conv_l Xc (LRty_sym XTsw)) XTww) as X2.
  (* both sides step to the step *)
  pose proof (eqtm_wf_l ge_typeof (geq_tm_sound Ec)) as Hc0.
  pose proof (eqtm_elimWf_supf _ _ _ _ _ _ _ _ _ _ _ ge_compt Hwl0 Hwl'0 HA0 HN0 HM0 HC0 HI0 Hc0 Hat Hcst) as Beta.
  destruct XTsw as [RS HRS]. destruct (escape_ty _ _ _ _ _ _ _ _ HRS) as (_ & _ & ESW).
  pose proof (elimWf_cong_l Hγ He (eqtm_sym _ _ _ _ _ _ _ (geq_tm_sound Dw))) as Cw.
  assert (Leq : [ G0 ; Δ0 ⊢g tmElimWf l l' A⟦γ⟧[e] N⟦γ⟧[llift e] M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))]
                               (tmSupf k C P a cs)
                  ≅ c⟦γ⟧[llift (llift (llift e))][lsingle3 a cs
                      (wfIH l l' A⟦γ⟧[e] N⟦γ⟧[llift e] M⟦γ⟧[llift e] c⟦γ⟧[llift (llift (llift e))] a cs)]
                  : M⟦γ⟧[llift e][lsingle (tmSupf k C P a cs)] @ l' ]).
  { eapply eqtm_trans; [exact Cw|].
    eapply eqtm_conv; [exact Beta | rewrite ge_typeof; apply eqty_sym, geq_ty_sound, ESW]. }
  pose proof (elimWf_cong Hγ He (geq_tm_sound Dww')) as Cww'.
  refine (conj X2 (conj _ _)).
  + split; [exact (eqtm_wf_l ge_typeof Leq) | econstructor; [apply red_elimWf_supf | constructor] | exact Leq].
  + split; [exact (eqtm_wf_r ge_typeof Cww') | econstructor; [apply red_elimWf_supf | constructor] |].
    eapply eqtm_trans; [apply eqtm_sym, Cww'|]. eapply eqtm_trans; [exact Leq|].
    exact (geq_tm_sound (LRtm_geq X2)).
Qed.

End ElimAt.

End WfElim.