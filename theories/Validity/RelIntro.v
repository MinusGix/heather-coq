(** * [Π]'s and [Σ]'s relations from their Kripke clauses

    A λ or a pair (any whnfs typed at both sides' types) is related as
    soon as its Kripke clause holds: the generic equality the relation
    also asks for follows from the clause itself, at the world of one
    more local for [Π] (extensionality at the variable) and at the
    identity world for [Σ] (extensionality by the projections), given
    that the component relations escape. [V_lam] and [V_pair] make this
    argument inline; [M]'s observations make it for their [Π] and [Σ]
    at relations that are not [LR]'s. *)
From DeLaM.Validity Require Export App.

Section RelIntro.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

(** The identity world acts trivially on normal forms. *)
Lemma kwid_ty {G Δ HΔ} (T : ty) : nfty T -> kty (kw_loc (G := G) wk_id (wkwf_id Δ) HΔ) T = T.
Proof using . intros NT; unfold kty, kw_loc; cbn [kw_γ kw_gk kw_r kw_rk gwa wk_ren kw_mk]; now apply ren_id_ty. Qed.
Lemma kwid_tyl {G Δ HΔ} (T : ty) : nfty T -> ktyl (kw_loc (G := G) wk_id (wkwf_id Δ) HΔ) T = T.
Proof using . intros NT; unfold ktyl, kw_loc; cbn [kw_γ kw_gk kw_r kw_rk gwa wk_ren kw_mk]; now apply ren_lift_id_ty. Qed.
Lemma kwid_tm {G Δ HΔ} (t : tm) : nftm t -> ktm (kw_loc (G := G) wk_id (wkwf_id Δ) HΔ) t = t.
Proof using . intros Nt; unfold ktm, kw_loc; cbn [kw_γ kw_gk kw_r kw_rk gwa wk_ren kw_mk]; now apply ren_id_tm. Qed.

(** The Kripke clause of [Π]'s relation. *)
Definition PiK {G Δ} (l1 l2 : lvl) (A B A' B' : ty) (domR : DomRel G Δ) (codR : CodRel G Δ domR) (w w' : tm) : Prop :=
  forall (ρ : kwk G Δ) a a' (ha : domR ρ a a') la lb la' lb' A1 B1 A1' B1',
    lequiv (gL G) la l1 -> lequiv (gL G) lb l2 ->
    lequiv (gL G) la' l1 -> lequiv (gL G) lb' l2 ->
    [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A ≈ A1 @ l1 ] ->
    [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l1 ⊢ ktyl ρ B ≈ B1 @ l2 ] ->
    [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A' ≈ A1' @ l1 ] ->
    [ kw_G ρ ; kw_Δ ρ ,, kty ρ A' @ l1 ⊢ ktyl ρ B' ≈ B1' @ l2 ] ->
    codR ρ a a' ha (app (ktm ρ w) la lb A1 B1 a) (app (ktm ρ w') la' lb' A1' B1' a').

Lemma PiRel_intro {G Δ l1 l2 l3 l4 A B A' B'} {domR : DomRel G Δ} {codR : CodRel G Δ domR} {w w'} (HΔ : [ G ; Δ ⊢g ]) :
  lwf (gL G) l1 -> lwf (gL G) l2 ->
  [ G ; Δ ⊢g A @ l1 ] -> [ G ; Δ ,, A @ l1 ⊢g B @ l2 ] -> [ G ; Δ ⊢g A' @ l1 ] ->
  [ G ; Δ ⊢ A ≈ A @ l1 ] -> [ G ; Δ ,, A @ l1 ⊢ B ≈ B @ l2 ] ->
  [ G ; Δ ⊢ A' ≈ A @ l1 ] -> [ G ; Δ ,, A' @ l1 ⊢ B' ≈ B @ l2 ] ->
  [ G ; Δ ⊢g tyPi l1 l2 A B ≅ tyPi l3 l4 A' B' @ lmax l1 l2 ] ->
  [ G ; Δ ⊢g w : tyPi l1 l2 A B @ lmax l1 l2 ] -> [ G ; Δ ⊢g w' : tyPi l3 l4 A' B' @ lmax l1 l2 ] ->
  whnf w -> whnf w' ->
  (forall (Hw1 : wk1 : (Δ ,, A @ l1) ≤ Δ) (HΔA : [ G ; Δ ,, A @ l1 ⊢g ]),
     domR (kw_loc wk1 Hw1 HΔA) (var 0) (var 0)) ->
  (forall ρ a a' h u u', codR ρ a a' h u u' -> [ kw_G ρ ; kw_Δ ρ ⊢ u ≈ u' : (ktyl ρ B)[lsingle a] @ l2 ]) ->
  PiK l1 l2 A B A' B' domR codR w w' ->
  PiRel G Δ l1 l2 l3 l4 A B A' B' domR codR w w'.
Proof using EL.
  intros Hl1 Hl2 HA HB HA' RA RB RA' RB' ES Hw Hw' Nw Nw' Hv Ec K.
  pose proof (wf_ty_nf HB) as NB.
  assert (HΔA : [ G ; Δ ,, A @ l1 ⊢g ]) by exact (ext_wf_g HA Hl1).
  assert (Hw1 : wk1 : (Δ ,, A @ l1) ≤ Δ) by (constructor; constructor).
  assert (Hr1 : wkr ↑ (Δ ,, A @ l1) Δ) by exact (wkr_shift1 _ _ _).
  assert (HΔAA : [ G ; Δ ,, A @ l1 ,, A⟨↑⟩ @ l1 ⊢g ])
    by (apply ext_wf_g; [exact (wf_ty_wkr Hr1 HΔA HA) | exact Hl1]).
  assert (HΔAA' : [ G ; Δ ,, A @ l1 ,, A'⟨↑⟩ @ l1 ⊢g ])
    by (apply ext_wf_g; [exact (wf_ty_wkr Hr1 HΔA HA') | exact Hl1]).
  pose proof (K (kw_loc wk1 Hw1 HΔA) (var 0) (var 0) (Hv Hw1 HΔA) l1 l2 l1 l2
                A⟨↑⟩ B⟨rlift ↑⟩ A⟨↑⟩ B⟨rlift ↑⟩
                (lequiv_refl _ _ Hl1) (lequiv_refl _ _ Hl2) (lequiv_refl _ _ Hl1) (lequiv_refl _ _ Hl2)
                (geq_ty_wk Hr1 HΔA RA)
                (geq_ty_wk (wkr_up _ _ _ _ _ Hr1) HΔAA RB)
                (geq_ty_wk Hr1 HΔA RA')
                (geq_ty_wk (wkr_up _ _ _ _ _ Hr1) HΔAA' RB')) as K1.
  apply Ec in K1.
  unfold ktyl, ktm, kty, kw_loc in K1; cbn [kw_G kw_Δ kw_γ kw_gk kw_r kw_rk gwa kw_mk] in K1.
  change (wk_ren wk1) with ↑ in K1. rewrite liftshift_single_var_ty in K1 by exact NB.
  assert (Hw'l : [ G ; Δ ⊢g w' : tyPi l1 l2 A B @ lmax l1 l2 ])
    by (eapply wf_conv; [exact Hw' | rewrite ge_typeof; first [exact ES | exact (eqty_sym _ _ _ _ _ _ ES)]]).
  assert (GEQ : [ G ; Δ ⊢ w ≈ w' : tyPi l1 l2 A B @ lmax l1 l2 ])
    by exact (geq_tm_funext Hl1 Hl2 HA HB Hw Hw'l K1).
  exists w, w'.
  refine (conj (tmred_refl _ _ _ Hw) (conj (tmred_refl _ _ _ Hw') (conj Nw (conj Nw' (conj GEQ (conj _ K)))))).
  eapply geq_tm_conv; [exact GEQ | exact ES].
Qed.

(** The Kripke clause of [Σ]'s relation. *)
Definition SigK {G Δ} (l1 l2 : lvl) (A B A' B' : ty) (domR : DomRel G Δ) (codR : CodRel G Δ domR) (w w' : tm) : Prop :=
  forall (ρ : kwk G Δ) la lb la' lb' A1 B1 A1' B1',
    lequiv (gL G) la l1 -> lequiv (gL G) lb l2 ->
    lequiv (gL G) la' l1 -> lequiv (gL G) lb' l2 ->
    [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A ≈ A1 @ l1 ] ->
    [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l1 ⊢ ktyl ρ B ≈ B1 @ l2 ] ->
    [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A' ≈ A1' @ l1 ] ->
    [ kw_G ρ ; kw_Δ ρ ,, kty ρ A' @ l1 ⊢ ktyl ρ B' ≈ B1' @ l2 ] ->
    exists h : domR ρ (tmFst la lb A1 B1 (ktm ρ w)) (tmFst la' lb' A1' B1' (ktm ρ w')),
      codR ρ _ _ h (tmSnd la lb A1 B1 (ktm ρ w)) (tmSnd la' lb' A1' B1' (ktm ρ w')).

Lemma SigRel_intro {G Δ l1 l2 l3 l4 A B A' B'} {domR : DomRel G Δ} {codR : CodRel G Δ domR} {w w'} (HΔ : [ G ; Δ ⊢g ]) :
  lwf (gL G) l1 -> lwf (gL G) l2 ->
  [ G ; Δ ⊢g A @ l1 ] -> [ G ; Δ ,, A @ l1 ⊢g B @ l2 ] -> [ G ; Δ ⊢g A' @ l1 ] -> [ G ; Δ ,, A' @ l1 ⊢g B' @ l2 ] ->
  [ G ; Δ ⊢ A ≈ A @ l1 ] -> [ G ; Δ ,, A @ l1 ⊢ B ≈ B @ l2 ] ->
  [ G ; Δ ⊢ A' ≈ A @ l1 ] -> [ G ; Δ ,, A' @ l1 ⊢ B' ≈ B @ l2 ] ->
  [ G ; Δ ⊢g tySig l1 l2 A B ≅ tySig l3 l4 A' B' @ lmax l1 l2 ] ->
  [ G ; Δ ⊢g w : tySig l1 l2 A B @ lmax l1 l2 ] -> [ G ; Δ ⊢g w' : tySig l3 l4 A' B' @ lmax l1 l2 ] ->
  whnf w -> whnf w' ->
  (forall ρ x x', domR ρ x x' -> [ kw_G ρ ; kw_Δ ρ ⊢ x ≈ x' : kty ρ A @ l1 ]) ->
  (forall ρ x x' h u u', codR ρ x x' h u u' -> [ kw_G ρ ; kw_Δ ρ ⊢ u ≈ u' : (ktyl ρ B)[lsingle x] @ l2 ]) ->
  SigK l1 l2 A B A' B' domR codR w w' ->
  SigRel G Δ l1 l2 l3 l4 A B A' B' domR codR w w'.
Proof using EL.
  intros Hl1 Hl2 HA HB HA' HB' RA RB RA' RB' ES Hw Hw' Nw Nw' Ed Ec K.
  pose proof (wf_ty_nf HA) as NA. pose proof (wf_ty_nf HA') as NA'.
  pose proof (wf_ty_nf HB) as NB. pose proof (wf_ty_nf HB') as NB'.
  pose proof (wf_tm_nf Hw) as Nt. pose proof (wf_tm_nf Hw') as Nt'.
  set (ρ0 := kw_loc wk_id (wkwf_id Δ) HΔ).
  destruct (K ρ0 l1 l2 l1 l2 A B A B
              (lequiv_refl _ _ Hl1) (lequiv_refl _ _ Hl2) (lequiv_refl _ _ Hl1) (lequiv_refl _ _ Hl2))
    as (h & c).
  1-4: change (kw_G ρ0) with G; change (kw_Δ ρ0) with Δ; unfold ρ0;
    rewrite ?(kwid_ty _ NA), ?(kwid_ty _ NA'), ?(kwid_tyl _ NB), ?(kwid_tyl _ NB'); assumption.
  pose proof (Ed _ _ _ h) as Ef. pose proof (Ec _ _ _ h _ _ c) as Es.
  change (kw_G ρ0) with G in Ef, Es; change (kw_Δ ρ0) with Δ in Ef, Es; unfold ρ0 in Ef, Es.
  rewrite (kwid_ty _ NA), (kwid_tm _ Nt), (kwid_tm _ Nt') in Ef.
  rewrite (kwid_tyl _ NB), (kwid_tm _ Nt), (kwid_tm _ Nt') in Es.
  assert (Hw'l : [ G ; Δ ⊢g w' : tySig l1 l2 A B @ lmax l1 l2 ])
    by (eapply wf_conv; [exact Hw' | rewrite ge_typeof; first [exact ES | exact (eqty_sym _ _ _ _ _ _ ES)]]).
  assert (GEQ : [ G ; Δ ⊢ w ≈ w' : tySig l1 l2 A B @ lmax l1 l2 ])
    by exact (geq_tm_sig_ext Hl1 Hl2 HA HB Hw Hw'l Ef Es).
  exists w, w'.
  refine (conj (tmred_refl _ _ _ Hw) (conj (tmred_refl _ _ _ Hw') (conj Nw (conj Nw' (conj GEQ (conj _ K)))))).
  eapply geq_tm_conv; [exact GEQ | exact ES].
Qed.

(** Anti-reduction, as [SigRel_red]. *)
Lemma PiRel_red {G Γ l1 l2 l3 l4 A B A' B' domR codR t t' u u'} :
  PiRel G Γ l1 l2 l3 l4 A B A' B' domR codR u u' ->
  [ G ; Γ ⊢g t ⤳* u : tyPi l1 l2 A B @ lmax l1 l2 ] -> [ G ; Γ ⊢g t' ⤳* u' : tyPi l3 l4 A' B' @ lmax l1 l2 ] ->
  PiRel G Γ l1 l2 l3 l4 A B A' B' domR codR t t'.
Proof using .
  intros (w & w' & R1 & R2 & Hrest) H1 H2. exists w, w'.
  exact (conj (tmred_trans _ _ _ _ _ H1 R1) (conj (tmred_trans _ _ _ _ _ H2 R2) Hrest)).
Qed.

(** Related functions escape at the left type, given the two types' equality. *)
Lemma PiRel_geq {G Γ l1 l2 l3 l4 A B A' B'} {domR : DomRel G Γ} {codR : CodRel G Γ domR} {t t'} :
  PiRel G Γ l1 l2 l3 l4 A B A' B' domR codR t t' ->
  [ G ; Γ ⊢g tyPi l1 l2 A B ≅ tyPi l3 l4 A' B' @ lmax l1 l2 ] ->
  [ G ; Γ ⊢ t ≈ t' : tyPi l1 l2 A B @ lmax l1 l2 ].
Proof using EL.
  intros (w & w' & R1 & R2 & _ & _ & E1 & _) ES.
  eapply geq_tm_exp; [exact R1 | exact (tmred_conv _ _ _ _ _ ge_typeof R2 (eqty_sym _ _ _ _ _ _ ES)) | exact E1].
Qed.

(** The world of one more local acts as the shift. *)
Lemma kwk1_ty {G Δ A l} (Hw1 : wk1 : (Δ ,, A @ l) ≤ Δ) HΔA (T : ty) : kty (kw_loc (G := G) wk1 Hw1 HΔA) T = T⟨↑⟩.
Proof using . unfold kty, kw_loc; cbn [kw_γ kw_gk kw_r kw_rk gwa kw_mk]. reflexivity. Qed.

End RelIntro.
