(** * [elim_IWi]'s validity: syntax and general lemmas (M19_DESIGN.md, M19b)

    The step telescope under global weakenings and substitutions; the
    positions an index of [Fin] reaches ([fin_pos_hd], [fin_pos_tl]), which
    the motive at the spine reads its argument relation at; applications
    of joinable functions ([join_app]); and λ-introduction into the
    relation at a [Π] from related bodies in every world ([LRtm_lam_K]),
    which builds the induction hypothesis's two λs. *)
From DeLaM.Validity Require Export IWi IWfElim.
From DeLaM.Typing Require Import IWiIH.
From DeLaM.LogRel Require Import IWfAux IWiAux.
From DeLaM.Validity Require Import DNthReds MCorec.

(** ** Syntax *)

Local Ltac gwpush := repeat first [ rewrite gwa_tyPi | rewrite gwa_tyFin | rewrite gwa_subst_ty | rewrite gwa_subst
  | rewrite gwa_lsingle | rewrite gwa_lsingle2 | rewrite gwa_tmDNth | rewrite gwa_var | rewrite gwa_ren_ty
  | rewrite gwa_ren | rewrite gwa_tyIWi | rewrite gwa_tyDVec | rewrite gwa_supii | rewrite gwa_app
  | rewrite gwa_iwiFam | rewrite gwa_iwiFamCod ].

Lemma gwa_iwimotty γ l lp li X A N D Ot C :
  (iwimotty l lp li X A N D Ot C)⟦γ⟧ = iwimotty l lp li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ D⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧.
Proof using . gwpush. reflexivity. Qed.
Lemma gwa_iwicsty γ l lp li X A N D Ot C :
  (iwicsty l lp li X A N D Ot C)⟦γ⟧ = iwicsty l lp li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ D⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧.
Proof using . gwpush. reflexivity. Qed.
Lemma gwa_iwiihty γ l lp li l' X A N D Ot C (M : ty) :
  (iwiihty l lp li l' X A N D Ot C M)⟦γ⟧ = iwiihty l lp li l' X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ D⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧ M⟦γ⟧.
Proof using . gwpush. reflexivity. Qed.
Lemma gwa_iwistepty γ l lp li X A N D Ot C (M : ty) :
  (iwistepty l lp li X A N D Ot C M)⟦γ⟧ = iwistepty l lp li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ D⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧ M⟦γ⟧.
Proof using . gwpush. reflexivity. Qed.

Section Telescope.
Context (d : lsub) (Hd : LK nftm d).

Local Ltac tsub := push_subst;
  repeat first [ rewrite subst_tmDNth by (repeat apply lk_llift; exact Hd) | progress push_subst
               | match goal with |- context [@subst ty _ (@subst ty _ ?M (lsingle2 ?t ?q)) ?e] =>
                   rewrite (single2_subst_ty e ltac:(repeat apply lk_llift; exact Hd) M t q) end
               | rewrite shift_llift_ty | rewrite shift_llift | rewrite liftshift_llift_ty | rewrite liftshift_llift
               | rewrite lift2shift_llift | rewrite lift2shift_llift_ty | rewrite lift3shift_llift ];
  rewrite ?llk_llift_S, ?llk_llift0; push_ren; rlk_simpl; try reflexivity.

Lemma iwimotty_llift l lp li (X A : ty) (N : tm) (D : ty) (Ot C : tm) :
  (iwimotty l lp li X A N D Ot C)[llift d] =
  iwimotty l lp li X[d] A[d] N[llift d] D[llift (llift d)] Ot[llift d] C[llift (llift (llift d))].
Proof using Hd. tsub. Qed.
Lemma iwicsty_llift l lp li (X A : ty) (N : tm) (D : ty) (Ot C : tm) :
  (iwicsty l lp li X A N D Ot C)[llift d] =
  iwicsty l lp li X[d] A[d] N[llift d] D[llift (llift d)] Ot[llift d] C[llift (llift (llift d))].
Proof using Hd. tsub. Qed.
Lemma iwiihty_llift2 l lp li l' (X A : ty) (N : tm) (D : ty) (Ot C : tm) (M : ty) :
  (iwiihty l lp li l' X A N D Ot C M)[llift (llift d)] =
  iwiihty l lp li l' X[d] A[d] N[llift d] D[llift (llift d)] Ot[llift d] C[llift (llift (llift d))]
    M[llift (llift d)].
Proof using Hd. tsub. Qed.
Lemma iwistepty_llift3 l lp li (X A : ty) (N : tm) (D : ty) (Ot C : tm) (M : ty) :
  (iwistepty l lp li X A N D Ot C M)[llift (llift (llift d))] =
  iwistepty l lp li X[d] A[d] N[llift d] D[llift (llift d)] Ot[llift d] C[llift (llift (llift d))]
    M[llift (llift d)].
Proof using Hd. tsub. Qed.

End Telescope.

Section IWiElim.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

(** An index of [Fin] reducing to an [inl] is related to the head
    position. *)
Lemma fin_pos_hd {G Δ k k' m i i' k1 k2 C1 D1 u} : LRtm lzero G Δ (tyFin k) (tyFin k') i i' ->
  [ G ; Δ ⊢g k ⤳* succ m : tyNat @ lzero ] -> NatRel G Δ k k' -> reds i (tmInl k1 k2 C1 D1 u) ->
  LRtm lzero G Δ (tyFin k) (tyFin k') i (posHd m).
Proof using EL VL VN.
  intros (R & HR & Hii) Hk Hkk Hi.
  destruct (NatRel_inv_succ Hkk Hk) as (m' & Hk' & Hmm).
  destruct (NatRel_escape Hmm) as (Hm & _ & _).
  destruct (LR_inv_sum HR (tyred_trans _ _ _ _ (tyred_fin Hk) (tyred_fin_succ Hm)))
    as (l3 & l4 & X' & Y' & RA & RB & _ & _ & _ & _ & _ & _ & HXu & _ & _ & _ & HRA & _ & _ & _ & _ & _ & HR').
  destruct (LR_inv_unit HRA (tyred_refl _ _ HXu)) as (_ & _ & _ & _ & _ & HRAu).
  pose proof (LRtm_inv HR (PosRel_LRtm (pos_hd _ _ _ _ _ _ Hk Hk' Hmm) Hkk)) as Hpp.
  apply HR' in Hpp. destruct Hpp as (wp & wp' & Hwp & _ & _ & Np).
  assert (wp = posHd m) as ->.
  { eapply reds_whnf_det; [exact (tmred_red _ _ _ _ _ _ _ Hwp) | apply reds_refl | exact (SumNf_whnf_l Np)
                          | apply whnf_inl]. }
  apply HR' in Hii. destruct Hii as (w & w' & Hw & _ & _ & Nn).
  assert (w = tmInl k1 k2 C1 D1 u) as ->.
  { eapply reds_whnf_det; [exact (tmred_red _ _ _ _ _ _ _ Hw) | exact Hi | exact (SumNf_whnf_l Nn) | apply whnf_inl]. }
  exists R; split; [exact HR|]. apply HR'.
  exists (tmInl k1 k2 C1 D1 u), (posHd m).
  refine (conj Hw (conj Hwp _)).
  inversion Nn as [? ? ? ? C D ? ? ? ? Q1 Q2 _ _ EC _ ED _ Ru | | ν ν' Hν]; subst.
  2: { exfalso. pose proof (gne_tm_whne_l Hν) as Z. inversion Z. }
  apply HRAu in Ru. destruct Ru as (wu & _ & Hu & _ & Nwu & _).
  inversion Np as [? ? ? ? ? ? ? ? ? ? _ _ _ _ _ _ _ _ Rt | | ? ? Hν2]; subst;
    [|exfalso; pose proof (gne_tm_whne_l Hν2) as Z; inversion Z].
  apply HRAu in Rt. destruct Rt as (wt & _ & Ht & _ & Nwt & _).
  pose proof (tmred_wf _ _ _ _ _ _ _ Hu) as Hut. pose proof (tmred_wf _ _ _ _ _ _ _ Ht) as Htt.
  assert (Hz : lequiv (gL G) lzero lzero) by (apply lequiv_refl; exact I).
  split.
  - apply geq_tm_sym. apply (geq_tm_inl (lequiv_sym _ _ _ Q1) (lequiv_sym _ _ _ Q2) EC ED).
    exact (geq_tm_unit_eta (l := lzero) ltac:(exact I) Htt Hut).
  - apply sumnf_inl; try assumption.
    + exact (geq_ty_trans EC (geq_ty_sym EC)).
    + exact (geq_ty_trans ED (geq_ty_sym ED)).
    + apply HRAu. exists wu, wt. exact (conj Hu (conj Ht (conj Nwu Nwt))).
Qed.

(** An index of [Fin] reducing to an [inr] of an index related to [p] is
    related to the tail position at [p]. *)
Lemma fin_pos_tl {G Δ k k' m i i' k1 k2 C1 D1 j p} : LRtm lzero G Δ (tyFin k) (tyFin k') i i' ->
  [ G ; Δ ⊢g k ⤳* succ m : tyNat @ lzero ] -> NatRel G Δ k k' -> reds i (tmInr k1 k2 C1 D1 j) ->
  LRtm lzero G Δ (tyFin m) (tyFin m) j p ->
  LRtm lzero G Δ (tyFin k) (tyFin k') i (posTl m p).
Proof using EL VL VN.
  intros (R & HR & Hii) Hk Hkk Hi Xjp.
  pose proof (ctx_of_tm (tmred_wf _ _ _ _ _ _ _ Hk)) as HΔ.
  destruct (NatRel_inv_succ Hkk Hk) as (m' & Hk' & Hmm).
  destruct (NatRel_escape Hmm) as (Hm & _ & _).
  destruct (LR_inv_sum HR (tyred_trans _ _ _ _ (tyred_fin Hk) (tyred_fin_succ Hm)))
    as (l3 & l4 & X' & Y' & RA & RB & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HRB & _ & _ & _ & _ & HR').
  apply HR' in Hii. destruct Hii as (w & w' & Hw & _ & _ & Nn).
  assert (w = tmInr k1 k2 C1 D1 j) as ->.
  { eapply reds_whnf_det; [exact (tmred_red _ _ _ _ _ _ _ Hw) | exact Hi | exact (SumNf_whnf_l Nn) | apply whnf_inr]. }
  assert (Hz : lequiv (gL G) lzero lzero) by (apply lequiv_refl; exact I).
  pose proof (LRtm_geq Xjp) as Ejp. pose proof (geq_tm_trans (geq_tm_sym Ejp) Ejp) as Epp.
  pose proof (geq_ty_unit HΔ Hz) as EU.
  destruct (LRtm_ty Xjp) as [RF HRF]. destruct (escape_ty _ _ _ _ _ _ _ _ HRF) as (_ & _ & EF).
  pose proof (geq_tm_sound (geq_tm_inr (A := tyUnit lzero) Hz Hz EU EF Epp)) as Dp.
  exists R; split; [exact HR|]. apply HR'.
  exists (tmInr k1 k2 C1 D1 j), (posTl m p).
  refine (conj Hw (conj (tmred_refl _ _ _ (eqtm_wf_l ge_typeof Dp)) _)).
  inversion Nn as [| ? ? ? ? C D ? ? ? ? Q1 Q2 _ _ EC _ ED _ Rj | ν ν' Hν]; subst.
  2: { exfalso. pose proof (gne_tm_whne_l Hν) as Z. inversion Z. }
  split.
  - apply geq_tm_sym. exact (geq_tm_inr (lequiv_sym _ _ _ Q1) (lequiv_sym _ _ _ Q2) EC ED (geq_tm_sym Ejp)).
  - apply sumnf_inr; try assumption.
    exact (LRtm_inv HRB (LRtm_irrel_r Xjp (ex_intro _ RB HRB))).
Qed.

(** Joinable functions have joinable applications. *)
Lemma join_app f1 f2 la lb A B y : Join f1 f2 -> Join (app f1 la lb A B y) (app f2 la lb A B y).
Proof using .
  intros [(x & H1 & H2)|(x & x' & H1 & H2 & N1 & N2)].
  - left. exists (app x la lb A B y). split; apply reds_app; assumption.
  - right. exists (app x la lb A B y), (app x' la lb A B y).
    refine (conj (reds_app _ _ _ _ _ _ _ H1) (conj (reds_app _ _ _ _ _ _ _ H2) (conj _ _))); apply whne_app; assumption.
Qed.

(** λ-introduction into the relation at a [Π]: two λs whose bodies are
    related at related arguments in every world are related. *)
Lemma LRtm_lam_K {L G Δ l1 l2 l3 l4 A A' B T b b'} :
  LRty L G Δ (tyPi l1 l2 A B) T ->
  lequiv (gL G) l3 l1 -> lequiv (gL G) l4 l2 -> [ G ; Δ ⊢ A ≈ A' @ l1 ] -> nftm b -> nftm b' ->
  (forall (ρ : kwk G Δ) y y' T1, LRtm l1 (kw_G ρ) (kw_Δ ρ) (kty ρ A) T1 y y' ->
     LRtm l2 (kw_G ρ) (kw_Δ ρ) (ktyl ρ B)[lsingle y] (ktyl ρ B)[lsingle y]
       (ktml ρ b)[lsingle y] (ktml ρ b')[lsingle y']) ->
  LRtm L G Δ (tyPi l1 l2 A B) T (lam l1 l2 A b) (lam l3 l4 A' b').
Proof using EL VL VN.
  intros [R HR] H3 H4 EA Nb Nb' HK.
  destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (HPi & _ & _).
  destruct (LR_inv_pi HR (tyred_refl _ _ HPi)) as (p3 & p4 & P2 & Q2 & domR & codR & PF & domAd & codAd & HRR).
  destruct PF as [Hlv Hp3 Hp4 Hw1 Hw2 _ _ HA HP2 HB HQ2 HAP HBQ].
  pose proof (ctx_of_ty HA) as HΔ.
  pose proof (lmeasure_le_l Hlv) as Hle1. pose proof (lmeasure_le_r Hlv) as Hle2.
  pose proof (wf_ty_nf HB) as NB.
  (* the bodies, typed: the Kripke hypothesis at the variable *)
  assert (Hw1k : wk1 : (Δ ,, A @ l1) ≤ Δ) by (constructor; constructor).
  assert (Hr1 : wkr ↑ (Δ ,, A @ l1) Δ) by exact (wkr_shift1 _ _ _).
  pose proof (ext_wf_g HA Hw1) as HΔa.
  pose proof (domAd (kw_loc wk1 Hw1k HΔa)) as DOM1.
  unfold kty, kw_loc in DOM1; cbn [kw_G kw_Δ kw_γ kw_gk kw_r kw_rk gwa kw_mk] in DOM1; change (wk_ren wk1) with ↑ in DOM1.
  apply (proj2 (LogRel_stage _ _ _ _ _ _ _ Hle1)) in DOM1.
  pose proof (var0_LRtm (ex_intro _ _ DOM1) HΔa) as Y0.
  pose proof (HK (kw_loc wk1 Hw1k HΔa) (var 0) (var 0) _ Y0) as Xb0.
  unfold ktyl, ktml, kw_loc in Xb0; cbn [kw_G kw_Δ kw_γ kw_gk kw_r kw_rk gwa kw_mk] in Xb0;
    change (wk_ren wk1) with ↑ in Xb0.
  rewrite liftshift_single_var_ty, !liftshift_single_var in Xb0 by assumption.
  destruct (LRtm_escape Xb0) as [Hb Hb'A].
  (* the right λ, at its annotations and at the left Π *)
  pose proof (geq_ty_sound EA) as DA. pose proof (eqty_wf_r ge_typeof DA) as HA'.
  pose proof (lequiv_wf_l _ _ _ H3) as Hw3. pose proof (lequiv_wf_l _ _ _ H4) as Hw4.
  assert (HA'3 : [ G ; Δ ⊢g A' @ l3 ]) by (eapply lconv_ty; [exact HA' | exact (lequiv_sym _ _ _ H3)]).
  assert (HΔA'3 : [ G ; Δ ,, A' @ l3 ⊢g ]) by exact (ext_wf_g HA'3 Hw3).
  assert (Hb'3 : [ G ; Δ ,, A' @ l3 ⊢g b' : B @ l4 ]).
  { eapply (wf_lconv _ _ _ _ _ _ l2); [|exact H4].
    exact (stab_tm ge_typeof DA (lequiv_sym _ _ _ H3) HΔA'3 Hb'A). }
  assert (HB3 : [ G ; Δ ,, A' @ l3 ⊢g B @ l4 ]).
  { eapply (lconv_ty (l := l2)); [|exact (lequiv_sym _ _ _ H4)].
    exact (stab_ty ge_typeof DA (lequiv_sym _ _ _ H3) HΔA'3 HB). }
  assert (HF : [ G ; Δ ⊢g lam l1 l2 A b : tyPi l1 l2 A B @ lmax l1 l2 ])
    by (apply wf_lam; auto using ge_notV).
  assert (HPiEq' : [ G ; Δ ⊢g tyPi l1 l2 A B ≅ tyPi l3 l4 A' B @ lmax l1 l2 ])
    by (apply eqty_pi; auto using ge_notV, lequiv_sym, eqty_refl).
  assert (HF' : [ G ; Δ ⊢g lam l3 l4 A' b' : tyPi l1 l2 A B @ lmax l1 l2 ]).
  { eapply wf_conv; [|rewrite ge_typeof; exact HPiEq'].
    eapply (wf_lconv _ _ _ _ _ _ (lmax l3 l4)); [|apply lequiv_max; solve [apply lequiv_sym; assumption]].
    apply wf_lam; auto using ge_notV. }
  (* the Kripke clause: β on both sides *)
  assert (Ki : forall (ρ : kwk G Δ) y y' (hy : domR ρ y y') la lb la' lb' A2 B2 A2' B2',
            lequiv (gL G) la l1 -> lequiv (gL G) lb l2 -> lequiv (gL G) la' l1 -> lequiv (gL G) lb' l2 ->
            [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A ≈ A2 @ l1 ] ->
            [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l1 ⊢ ktyl ρ B ≈ B2 @ l2 ] ->
            [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ P2 ≈ A2' @ l1 ] ->
            [ kw_G ρ ; kw_Δ ρ ,, kty ρ P2 @ l1 ⊢ ktyl ρ Q2 ≈ B2' @ l2 ] ->
            codR ρ y y' hy (app (ktm ρ (lam l1 l2 A b)) la lb A2 B2 y)
              (app (ktm ρ (lam l3 l4 A' b')) la' lb' A2' B2' y')).
  { intros ρ y y' hy la lb la' lb' A2 B2 A2' B2' H1 H2 H1' H2' HA2 HB2 HA2' HB2'.
    pose proof (domAd ρ) as DOM. apply (proj2 (LogRel_stage _ _ _ _ _ _ _ Hle1)) in DOM.
    pose proof (LRtm_of DOM hy) as Y.
    destruct (LRtm_escape Y) as [Hy Hy']. pose proof (LRtm_geq Y) as Eyy.
    pose proof (HK ρ y y' _ Y) as Xb.
    pose proof (codAd ρ y y' hy) as COD. apply LR_refl_l in COD.
    pose proof (LRtm_inv (proj2 (LogRel_stage _ _ _ _ _ _ _ Hle2) COD) Xb) as Rx.
    apply (LR_red_tm _ _ _ _ _ _ _ _ COD _ _ _ _ Rx); rewrite ktm_lam.
    - exact (tmred_beta (kw_lwf ρ Hw1) (kw_lwf ρ Hw2) (kw_lequiv ρ H1) (kw_lequiv ρ H2) (kw_ty ρ HA)
               (kw_ty_l ρ HA Hw1 HB) (kw_tm_l ρ HA Hw1 Hb) Hy (geq_ty_sound HA2) (geq_ty_sound HB2)).
    - pose proof (kw_tm_l ρ HA'3 Hw3 Hb'3) as Hb'ρ. pose proof (kw_ty_l ρ HA'3 Hw3 HB3) as HBρ'.
      pose proof (kw_ty ρ HA'3) as HA'ρ. pose proof (kw_geq_ty ρ EA) as EAρ.
      pose proof (kw_geq_ty ρ HAP) as EPρ.
      assert (EA'P : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A' ≈ kty ρ P2 @ l1 ]) by exact (geq_ty_trans (geq_ty_sym EAρ) EPρ).
      assert (Hy'3 : [ kw_G ρ ; kw_Δ ρ ⊢g y' : kty ρ A' @ l3 ]).
      { eapply (wf_lconv _ _ _ _ _ _ l1); [|exact (kw_lequiv ρ H3)].
        eapply wf_conv; [exact Hy' | rewrite ge_typeof; apply geq_ty_sound, geq_ty_sym, EAρ]. }
      assert (HA1c : [ kw_G ρ ; kw_Δ ρ ⊢g kty ρ A' ≅ A2' @ l3 ]).
      { eapply eqty_lconv; [|exact (kw_lequiv ρ H3)]. apply geq_ty_sound. exact (geq_ty_trans EA'P HA2'). }
      pose proof (kw_ty ρ HA) as HAρ.
      pose proof (kw_geq_ty_l ρ HA Hw1 HBQ) as KQ.
      assert (HB1c : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A' @ l3 ⊢g ktyl ρ B ≅ B2' @ l4 ]).
      { eapply eqty_lconv; [|exact (kw_lequiv ρ H4)].
        eapply (stab_eqty ge_typeof (geq_ty_sound EAρ) (lequiv_sym _ _ _ (kw_lequiv ρ H3))
                  (ext_wf_g HA'ρ (kw_lwf ρ Hw3))).
        apply geq_ty_sound. eapply geq_ty_trans; [exact KQ|].
        eapply geq_ty_ctxconv; [apply eqty_sym, geq_ty_sound, EPρ | now apply lequiv_refl, kw_lwf
                               | apply ext_wf_g; [exact HAρ | exact (kw_lwf ρ Hw1)] | exact HB2']. }
      pose proof (tmred_beta (kw_lwf ρ Hw3) (kw_lwf ρ Hw4) (lequiv_trans _ _ _ _ (kw_lequiv ρ H1') (lequiv_sym _ _ _ (kw_lequiv ρ H3)))
                    (lequiv_trans _ _ _ _ (kw_lequiv ρ H2') (lequiv_sym _ _ _ (kw_lequiv ρ H4)))
                    HA'ρ HBρ' Hb'ρ Hy'3 HA1c HB1c) as Z.
      pose proof (kw_ty_l ρ HA Hw1 HB) as HBρ.
      pose proof (wf_ty_func ge_typeof HBρ (lsub_eq_single ge_typeof Hy' Hy (eqtm_sym _ _ _ _ _ _ _ (geq_tm_sound Eyy))))
        as Ecod.
      eapply tmred_lconv; [eapply tmred_conv; [apply ge_typeof | exact Z |] | exact (lequiv_sym _ _ _ (kw_lequiv ρ H4))].
      eapply eqty_lconv; [exact Ecod | exact (kw_lequiv ρ H4)]. }
  (* the generic equality of the two λs, by extensionality *)
  assert (EPi2 : [ G ; Δ ⊢g tyPi l1 l2 A B ≅ tyPi p3 p4 P2 Q2 @ lmax l1 l2 ])
    by (apply geq_ty_sound, geq_ty_pi; auto using lequiv_sym).
  pose proof (LRtm_inv DOM1 Y0) as hv.
  assert (RA0 : [ G ; Δ ⊢ A ≈ A @ l1 ]) by exact (geq_ty_trans HAP (geq_ty_sym HAP)).
  assert (RB0 : [ G ; Δ ,, A @ l1 ⊢ B ≈ B @ l2 ]) by exact (geq_ty_trans HBQ (geq_ty_sym HBQ)).
  assert (HΔaa : [ G ; Δ ,, A @ l1 ,, A⟨↑⟩ @ l1 ⊢g ])
    by (apply ext_wf_g; [exact (wf_ty_wkr Hr1 HΔa HA) | exact Hw1]).
  assert (HΔaP : [ G ; Δ ,, A @ l1 ,, P2⟨↑⟩ @ l1 ⊢g ])
    by (apply ext_wf_g; [exact (wf_ty_wkr Hr1 HΔa HP2) | exact Hw1]).
  pose proof (Ki (kw_loc wk1 Hw1k HΔa) (var 0) (var 0) hv l1 l2 l1 l2 A⟨↑⟩ B⟨rlift ↑⟩ A⟨↑⟩ B⟨rlift ↑⟩
                (lequiv_refl _ _ Hw1) (lequiv_refl _ _ Hw2) (lequiv_refl _ _ Hw1) (lequiv_refl _ _ Hw2)) as K0.
  unfold kty, ktyl, ktm, kw_loc in K0; cbn [kw_G kw_Δ kw_γ kw_gk kw_r kw_rk gwa kw_mk] in K0;
    change (wk_ren wk1) with ↑ in K0.
  pose proof (K0 (geq_ty_wk Hr1 HΔa RA0) (geq_ty_wk (wkr_up _ _ _ _ _ Hr1) HΔaa RB0)
                (geq_ty_wk Hr1 HΔa (geq_ty_sym HAP))) as K1.
  unshelve epose proof (K1 _) as K2.
  { eapply geq_ty_ctxconv; [| apply lequiv_refl, Hw1 | exact HΔaP |].
    - apply geq_ty_sound. exact (geq_ty_wk Hr1 HΔa HAP).
    - apply geq_ty_sym. exact (geq_ty_wk (wkr_up _ _ _ _ _ Hr1) HΔaa HBQ). }
  pose proof (codAd (kw_loc wk1 Hw1k HΔa) (var 0) (var 0) hv) as COD1.
  unfold ktyl, kw_loc in COD1; cbn [kw_G kw_Δ kw_γ kw_gk kw_r kw_rk gwa kw_mk] in COD1;
    change (wk_ren wk1) with ↑ in COD1.
  destruct (escape_tm _ _ _ _ _ _ _ _ COD1 _ _ K2) as (_ & _ & Hg).
  rewrite liftshift_single_var_ty in Hg by exact NB.
  pose proof (geq_tm_funext Hw1 Hw2 HA HB HF HF' Hg) as GEQ.
  assert (PR : PiRel G Δ l1 l2 p3 p4 A B P2 Q2 domR codR (lam l1 l2 A b) (lam l3 l4 A' b')).
  { eexists _, _. refine (conj (tmred_refl _ _ _ HF) (conj _ (conj (whnf_lam _ _ _ _)
                     (conj (whnf_lam _ _ _ _) (conj GEQ (conj _ Ki)))))).
    - apply tmred_refl. eapply wf_conv; [exact HF' | rewrite ge_typeof; apply eqty_sym, EPi2].
    - eapply geq_tm_conv; [exact GEQ | exact EPi2]. }
  exists R. split; [exact HR | exact (proj2 (HRR _ _) PR)].
Qed.

End IWiElim.
