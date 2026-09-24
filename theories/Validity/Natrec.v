(** * Validity of the natural-number eliminator *)
From DeLaM.Validity Require Export PiComp.

Section Natrec.
Context `{E : GenericEq} `{EL : !GenericEqLaws}.

(** ** Syntax *)

Lemma lsucc_cons2_ty (M : ty) d n r :
  LK nftm d -> M[lsucc][lcons (lcons d n) r] = M[llift d][lsingle (succ n)].
Proof.
  intros Hd. rewrite lift_single_ty by exact Hd.
  apply subst_subst_ty. intros [|m]; cbn; auto. replace (m + 2) with (S (S m)) by lia. reflexivity.
Qed.

Lemma lift2_single2 (z : tm) d n r :
  LK nftm d -> z[llift (llift d)][lsingle2 n r] = z[lcons (lcons d n) r].
Proof.
  intros Hd. apply subst_subst. intros [|[|m]].
  - rewrite !llk_llift. reflexivity.
  - rewrite !llk_llift. change (ren_tm ?x ?r) with x⟨r⟩. reflexivity.
  - rewrite !llk_llift. change (ren_tm (ren_tm ?x ?r) ?r') with x⟨r⟩⟨r'⟩.
    cbn [llk]. rewrite shift2_single2 by apply Hd. reflexivity.
Qed.

(** ** Changing either type of a term relation to a related one *)

Lemma LRtm_conv_l {l G Γ T T' T2 t t'} :
  LRtm l G Γ T T' t t' -> LRty l G Γ T2 T -> LRtm l G Γ T2 T' t t'.
Proof.
  intros (R & H & Ht) [R2 H2].
  destruct (LR_trans _ _ _ _ _ _ _ H2 _ _ H) as [H3 Hc].
  pose proof (LR_refl_l _ _ _ _ _ _ _ H) as HTT.
  pose proof (LR_irrel_left _ _ _ _ _ _ _ _ _ H2 HTT) as E2.
  exists R2; split; [exact H3|].
  apply (Hc t t t'); [apply E2, (LR_tm_refl_l _ _ _ _ _ _ _ _ _ H Ht) | exact Ht].
Qed.

Lemma LRtm_conv_r {l G Γ T T' T2 t t'} :
  LRtm l G Γ T T' t t' -> LRty l G Γ T' T2 -> LRtm l G Γ T T2 t t'.
Proof.
  intros (R & H & Ht) [R2 H2].
  exists R; split; [exact (proj1 (LR_trans _ _ _ _ _ _ _ H _ _ H2)) | exact Ht].
Qed.

(** ** Natural numbers: reflexivity *)

Lemma NatRel_refl_l G Γ : forall t t', NatRel G Γ t t' -> NatRel G Γ t t.
Proof.
  apply (NatRel_mut G Γ (fun t t' _ => NatRel G Γ t t) (fun w w' _ => NatNf G Γ w w)).
  - intros t t' w w' Hw Hw' Heq _ IH.
    econstructor; [exact Hw | exact Hw | eapply geq_tm_trans; [exact Heq | now apply geq_tm_sym] | exact IH].
  - constructor.
  - intros; now constructor.
  - intros ν ν' H; constructor. eapply gne_tm_trans; [exact H | now apply gne_tm_sym].
Qed.

Lemma NatRel_refl_r {G Γ t t'} : NatRel G Γ t t' -> NatRel G Γ t' t'.
Proof. intros H; exact (NatRel_refl_l _ _ _ _ (NatRel_sym _ _ _ _ H)). Qed.

(** A natural number is related to its normal form. *)
Lemma NatRel_to_nf {G Γ t w w'} :
  [ G ; Γ ⊢g t ⤳* w : tyNat @ lzero ] -> [ G ; Γ ⊢ w ≈ w' : tyNat @ lzero ] -> NatNf G Γ w w' ->
  NatRel G Γ t w.
Proof.
  intros Hw Heq Hnf.
  assert (Hww : NatRel G Γ w w).
  { assert (Hnf0 : NatRel G Γ w w').
    { econstructor; [| |exact Heq|exact Hnf].
      - apply tmred_refl. exact (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hw)).
      - apply tmred_refl. exact (eqtm_wf_r ge_typeof (geq_tm_sound Heq)). }
    exact (NatRel_refl_l _ _ _ _ Hnf0). }
  inversion Hww as [? ? w1 w2 Hw1 Hw2 Heq12 Hnf12]; subst.
  econstructor; [exact (tmred_trans _ _ _ _ _ Hw Hw1) | exact Hw2 | exact Heq12 | exact Hnf12].
Qed.

(** ** Typed reductions of the eliminator *)

Section NatrecRed.
Context {G : gctx} {Δ : ctx} {l : lvl} {M : ty} {s z : tm}
  (Hwl : lwf (gL G) l) (HM : [ G ; Δ ,, tyNat @ lzero ⊢g M @ l ])
  (Hs : [ G ; Δ ⊢g s : M[lsingle zero] @ l ])
  (Hz : [ G ; Δ ,, tyNat @ lzero ,, M @ l ⊢g z : M[lsucc] @ l ]).

Lemma wf_natrec_g {n} : [ G ; Δ ⊢g n : tyNat @ lzero ] ->
  [ G ; Δ ⊢g natrec l M s z n : M[lsingle n] @ l ].
Proof. intros; apply wf_natrec; auto using ge_notV. Qed.

Lemma tmred_natrec_cong {n w} : [ G ; Δ ⊢g n ⤳* w : tyNat @ lzero ] ->
  [ G ; Δ ⊢g natrec l M s z n ⤳* natrec l M s z w : M[lsingle n] @ l ].
Proof.
  intros [Hn Hr Heq]. split.
  - now apply wf_natrec_g.
  - now apply reds_natrec.
  - apply eqtm_natrec; auto using ge_notV, lequiv_refl, eqty_refl, eqtm_refl.
Qed.

Lemma tmred_natrec_zero : [ G ; Δ ⊢g natrec l M s z zero ⤳* s : M[lsingle zero] @ l ].
Proof.
  split.
  - apply wf_natrec_g, wf_zero; [exact ge_notV | rewrite ge_typeof; eapply ctx_of_tm, Hs].
  - econstructor; [constructor | constructor].
  - apply eqtm_natrec_zero; auto using ge_compt.
Qed.

Lemma tmred_natrec_succ {n} : [ G ; Δ ⊢g n : tyNat @ lzero ] ->
  [ G ; Δ ⊢g natrec l M s z (succ n) ⤳* z[lsingle2 n (natrec l M s z n)] : M[lsingle (succ n)] @ l ].
Proof.
  intros Hn. split.
  - apply wf_natrec_g, wf_succ; auto using ge_notV.
  - econstructor; [constructor | constructor].
  - apply eqtm_natrec_succ; auto using ge_compt.
Qed.

End NatrecRed.

End Natrec.
