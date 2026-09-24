(** * Validity of the code of Π and of its decoding *)
From DeLaM.Validity Require Export Natrec.

Section CodePi.
Context `{E : GenericEq} `{EL : !GenericEqLaws}.

Lemma lwf_max {G l l'} : lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) (lmax l l').
Proof. intros; eapply lequiv_wf_l, lequiv_max; now apply lequiv_refl. Qed.

(** Decoding a Π code, with annotations [k1 k2] equivalent to the levels
    [l1 l2] at which the premises are typed. *)
Lemma tyred_El_pi {G Δ la l1 l2 k1 k2 s t} :
  lequiv (gL G) k1 l1 -> lequiv (gL G) k2 l2 ->
  [ G ; Δ ⊢g s : tyU l1 @ lsuc l1 ] -> [ G ; Δ ,, tyEl k1 s @ l1 ⊢g t : tyU l2 @ lsuc l2 ] ->
  lequiv (gL G) la (lmax l1 l2) ->
  [ G ; Δ ⊢g tyEl la (tmPi k1 k2 s t) ⤳* tyPi k1 k2 (tyEl k1 s) (tyEl k2 t) @ lmax l1 l2 ].
Proof.
  intros H1 H2 Hs Ht Hla.
  pose proof (conv_U' Hs (lequiv_sym _ _ _ H1)) as Hs1.
  destruct (El_annot Hs H1) as [HA _].
  assert (HΓ : [ G ; Δ ,, tyEl k1 s @ k1 ⊢g ])
    by (apply ext_wf_g; [eapply lconv_ty; [exact HA | now apply lequiv_sym] | eauto using lequiv_wf_l]).
  pose proof (stab_tm ge_typeof (eqty_refl _ _ _ _ _ HA) (lequiv_sym _ _ _ H1) HΓ Ht) as Ht1.
  pose proof (conv_U' Ht1 (lequiv_sym _ _ _ H2)) as Ht2.
  assert (Hc : [ G ; Δ ⊢g tmPi k1 k2 s t : tyU (lmax k1 k2) @ lsuc (lmax k1 k2) ])
    by (apply wf_code_pi; eauto using ge_notV, lequiv_wf_l).
  assert (Hm : lequiv (gL G) (lmax l1 l2) (lmax k1 k2)) by (apply lequiv_max; now apply lequiv_sym).
  destruct (El_annot Hc (lequiv_trans _ _ _ _ Hla Hm)) as [HEl HEq].
  eapply tyred_lconv; [|exact Hm].
  apply tyred_step; [exact HEl | constructor |].
  eapply eqty_trans; [exact HEq|].
  apply eqty_sym, eqty_El_pi; eauto using ge_compt, lequiv_wf_l.
Qed.

(** Decoding under global weakenings. *)
Lemma V_ElG {G Γ l l' t t'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTmG G Γ t t' (tyU l) (lsuc l) -> VTyG G Γ (tyEl l t) (tyEl l' t') l.
Proof.
  intros Hwl Hl Ht G' γ Hγ. rewrite !gwa_tyEl.
  pose proof (Ht _ _ Hγ) as X. rewrite gwa_tyU in X.
  destruct Hγ as [HL _]. apply V_El; [rewrite HL; exact Hwl | rewrite HL; exact Hl | exact X].
Qed.

(** ** The code of Π *)

Section CodePiV.
Context {G : gctx} {Γ : ctx} {l1 l2 l3 l4 : lvl} {s s' t t' : tm}
  (Hw1 : lwf (gL G) l1) (Hw2 : lwf (gL G) l2)
  (H13 : lequiv (gL G) l1 l3) (H24 : lequiv (gL G) l2 l4)
  (Hs : [ G ; Γ ⊢g s : tyU l1 @ lsuc l1 ]) (Hs' : [ G ; Γ ⊢g s' : tyU l1 @ lsuc l1 ])
  (Hss : [ G ; Γ ⊢g s ≅ s' : tyU l1 @ lsuc l1 ])
  (Ht : [ G ; Γ ,, tyEl l1 s @ l1 ⊢g t : tyU l2 @ lsuc l2 ])
  (Ht' : [ G ; Γ ,, tyEl l1 s @ l1 ⊢g t' : tyU l2 @ lsuc l2 ])
  (Vs : VTmG G Γ s s' (tyU l1) (lsuc l1))
  (Vt : VTmG G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) (lsuc l2)).

Lemma V_code_pi :
  VTm G Γ (tmPi l1 l2 s t) (tmPi l3 l4 s' t') (tyU (lmax l1 l2)) (lsuc (lmax l1 l2)).
Proof.
  (* facts in [Γ] *)
  destruct (El_annot Hs (lequiv_refl _ _ Hw1)) as [HA _].
  destruct (El_annot Hs' (lequiv_sym _ _ _ H13)) as [HA' _].
  assert (HAA' : [ G ; Γ ⊢g tyEl l1 s ≅ tyEl l3 s' @ l1 ]) by (apply eqty_El; auto using ge_notV).
  assert (HΓA' : [ G ; Γ ,, tyEl l3 s' @ l1 ⊢g ]) by now apply ext_wf_g.
  pose proof (stab_tm ge_typeof HAA' (lequiv_refl _ _ Hw1) HΓA' Ht') as Ht''.
  destruct (El_annot Ht (lequiv_refl _ _ Hw2)) as [HB _].
  destruct (El_annot Ht'' (lequiv_sym _ _ _ H24)) as [HB' _].
  pose proof (V_ElG Hw1 H13 Vs) as VA. pose proof (V_ElG Hw2 H24 Vt) as VB.
  (* at a pair of related substitutions *)
  intros Δ d d' Hd. pose proof (SubRel_ctx Hd) as HΔ.
  pose proof (SubRel_wf_l _ _ _ _ _ Hd) as Hwd. pose proof (SubRel_wf_r Hd) as Hwd'.
  pose proof (wf_ty_subst ge_typeof HA Hwd) as HAd. pose proof (wf_ty_subst ge_typeof HA' Hwd') as HA'd'.
  pose proof (wf_tm_subst ge_typeof Hs Hwd) as Hsd. pose proof (wf_tm_subst ge_typeof Hs' Hwd') as Hs'd'.
  pose proof (wf_tm_subst ge_typeof Ht (lsub_wf_lift _ _ ge_typeof _ _ _ _ _ Hwd HAd Hw1)) as Htd.
  pose proof (wf_tm_subst ge_typeof Ht'' (lsub_wf_lift _ _ ge_typeof _ _ _ _ _ Hwd' HA'd' Hw1)) as Ht'd'.
  rewrite !subst_tyU, !subst_tyEl in *.
  assert (Hlift : SubRel G (Γ ,, tyEl l1 s @ l1) (Δ ,, tyEl l1 s[d] @ l1) (llift d) (llift d'))
    by exact (SubRel_lift Hd (VTy_refl_l (VTyG_loc VA)) HAd Hw1).
  pose proof (VTmG_loc Vt _ _ _ Hlift) as Xt. pose proof (VTmG_loc Vs _ _ _ Hd) as Xs. rewrite !subst_tyU in Xs, Xt.
  assert (Hgeq : [ G ; Δ ⊢ tmPi l1 l2 s[d] t[llift d] ≈ tmPi l3 l4 s'[d'] t'[llift d']
                     : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ])
    by exact (geq_tm_code_pi H13 H24 Hsd (LRtm_geq Xs) (LRtm_geq Xt)).
  pose proof (geq_tm_sound Hgeq) as Hgeq'.
  push_subst. apply (LRtm_U (lwf_max Hw1 Hw2)).
  exists (tmPi l1 l2 s[d] t[llift d]), (tmPi l3 l4 s'[d'] t'[llift d']).
  refine (conj (tmred_refl _ _ _ (eqtm_wf_l ge_typeof Hgeq'))
           (conj (tmred_refl _ _ _ (eqtm_wf_r ge_typeof Hgeq'))
           (conj (whnf_tmPi _ _ _ _) (conj (whnf_tmPi _ _ _ _) (conj Hgeq _))))).
  intros la lb Hla Hlb. rewrite LRbelow_spec by (rewrite ?lmeasure_suc; lia).
  eexists. eapply LR_red_ty;
    [exact (LR_pi_here Hw1 Hw2 (lequiv_sym _ _ _ H13) (lequiv_sym _ _ _ H24) HB HB' VA VB _ _ _ Hd)
    | | ]; push_subst.
  - apply tyred_El_pi; auto using lequiv_refl.
  - apply tyred_El_pi; auto using lequiv_sym.
Qed.

End CodePiV.

(** ** [Π (El s) (El t) ≅ El ⌜Π s t⌝] *)

Lemma V_El_pi {G Γ l l' s t} :
  lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢g s : tyU l @ lsuc l ] -> [ G ; Γ ,, tyEl l s @ l ⊢g t : tyU l' @ lsuc l' ] ->
  VTmG G Γ s s (tyU l) (lsuc l) -> VTmG G (Γ ,, tyEl l s @ l) t t (tyU l') (lsuc l') ->
  VTy G Γ (tyPi l l' (tyEl l s) (tyEl l' t)) (tyEl (lmax l l') (tmPi l l' s t)) (lmax l l').
Proof.
  intros Hw Hw' Hs Ht Vs Vt Δ d d' Hd.
  destruct (El_annot Hs (lequiv_refl _ _ Hw)) as [HA _].
  destruct (El_annot Ht (lequiv_refl _ _ Hw')) as [HB _].
  pose proof (V_ElG Hw (lequiv_refl _ _ Hw) Vs) as VA. pose proof (V_ElG Hw' (lequiv_refl _ _ Hw') Vt) as VB.
  pose proof (LR_pi_here Hw Hw' (lequiv_refl _ _ Hw) (lequiv_refl _ _ Hw') HB HB VA VB _ _ _ Hd) as HP.
  destruct (escape_ty _ _ _ _ _ _ _ _ HP) as (HPd & _ & _).
  pose proof (SubRel_wf_r Hd) as Hwd'.
  pose proof (wf_ty_subst ge_typeof HA Hwd') as HAd'.
  pose proof (wf_tm_subst ge_typeof Hs Hwd') as Hsd'.
  pose proof (wf_tm_subst ge_typeof Ht (lsub_wf_lift _ _ ge_typeof _ _ _ _ _ Hwd' HAd' Hw)) as Htd'.
  rewrite !subst_tyU, !subst_tyEl in *.
  eexists. eapply LR_red_ty; [exact HP | apply tyred_refl, HPd |]. push_subst.
  apply tyred_El_pi; auto using lequiv_refl, lwf_max.
Qed.

End CodePi.
