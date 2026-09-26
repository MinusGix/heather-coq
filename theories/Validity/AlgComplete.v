(** * Completeness of algorithmic conversion (08:222)

    The fundamental theorems with the algorithmic pair of instances, and
    escape: declaratively equal types and terms are algorithmically
    convertible. At ω (M), both sides are [UΠ]s and the bodies are at a
    well-formed level. *)
From DeLaM.Validity Require Export AlgInstance.

Section Complete.

Local Notation EP := (AlgEq lD compt_D).
Local Notation EM := (AlgEq lM compt_M).
#[local] Instance ELP : @GenericEqLaws EP := AlgEqLaws lD compt_D.
#[local] Instance ELM : @GenericEqLaws EM := AlgEqLaws lM compt_M.
#[local] Instance EMl : GenericEqM EP EM := AlgEqM.

Lemma complete_ty_D {G Γ T T' l} : [ G ; Γ ⊢[ lD ] T ≅ T' @ l ] -> ac_ty G Γ T T'.
Proof.
  intros H. destruct (proj1 (reducibleP_eqty EP EM H)) as [R HR].
  destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (_ & _ & (_ & D)). exact D.
Qed.

Lemma complete_tm_D {G Γ t t' T l} : [ G ; Γ ⊢[ lD ] t ≅ t' : T @ l ] -> ac_tm G Γ t t' T.
Proof.
  intros H. destruct (proj1 (reducibleP_eqtm EP EM H)) as (R & HR & Ht).
  destruct (escape_tm _ _ _ _ _ _ _ _ HR _ _ Ht) as (_ & _ & (_ & D)). exact D.
Qed.

Lemma complete_ty_M_lwf {G Γ T T' l} : [ G ; Γ ⊢[ lM ] T ≅ T' @ l ] -> lwf (gL G) l -> ac_ty G Γ T T'.
Proof.
  intros H Hl. destruct (reducibleM_eqty EP EM H Hl) as [R HR].
  destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (_ & _ & (_ & D)). exact D.
Qed.

Lemma complete_tm_M_lwf {G Γ t t' T l} : [ G ; Γ ⊢[ lM ] t ≅ t' : T @ l ] -> lwf (gL G) l -> ac_tm G Γ t t' T.
Proof.
  intros H Hl. destruct (reducibleM_eqtm EP EM H Hl) as (R & HR & Ht).
  destruct (escape_tm _ _ _ _ _ _ _ _ HR _ _ Ht) as (_ & _ & (_ & D)). exact D.
Qed.

End Complete.

(** ** At ω *)

Lemma lequivs_refl L ls : Forall (lwf L) ls -> Forall2 (lequiv L) ls ls.
Proof. induction 1; constructor; auto using lequiv_refl. Qed.

(** The bodies of [UΠ]'s η, of equal terms, are equal (as [wf_ueta_body]). *)
Lemma ueta_body_eq {G Γ n l T t t'} : lwf (n + gL G) l ->
  [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] T @ l ] -> [ G ; Γ ⊢[ lM ] t ≅ t' : tyUPi n l T @ lomega ] ->
  [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] uapp t⟨ush n⟩ᵤ (ubvars n) ≅ uapp t'⟨ush n⟩ᵤ (ubvars n) : T @ l ].
Proof.
  intros Hl HT H. pose proof (wf_ty_dnf HT) as HTd.
  pose proof (uwk_eqtm n H) as X. cbn [uren_ty lvren] in X.
  pose proof (uwk_under_ty n HT) as HT2.
  assert (Hl2 : lwf (n + gL (gctx_uwk n G)) (lvren l (uuprn n (ush n))))
    by (eapply lwf_lvren; [apply uwk_under_ok | exact Hl]).
  pose proof (eqtm_uapp _ _ _ _ _ _ _ (ubvars n) (ubvars n) Hl2 HT2 (ubvars_length n)
                (lequivs_refl _ _ (lwfs_ubvars n _)) X) as Y.
  rewrite ueta_ty, ueta_lvl in Y by exact HTd. exact Y.
Qed.

Lemma complete_ty_M_ω {G Γ T T'} : [ G ; Γ ⊢[ lM ] T ≅ T' @ lomega ] -> ac_ty G Γ T T'.
Proof.
  intros H. destruct (omegaM_red_l H) as (n & l & A & HR). destruct (omegaM_red_r H) as (n' & l' & A' & HR').
  assert (E : [ G ; Γ ⊢[ lM ] tyUPi n l A ≅ tyUPi n' l' A' @ lomega ]).
  { eapply eqty_trans; [exact (eqty_sym _ _ _ _ _ _ (tyred_eq _ _ _ _ _ _ HR)) |].
    eapply eqty_trans; [exact H | exact (tyred_eq _ _ _ _ _ _ HR')]. }
  destruct (declM_upi_inj E) as (-> & Hl & EA).
  eapply act_red; [exact (tyred_red _ _ _ _ _ _ HR) | exact (tyred_red _ _ _ _ _ _ HR') | apply whnf_tyUPi
                  | apply whnf_tyUPi |].
  exact (actnf_upi _ _ _ _ _ _ _ (lequiv_leqv _ _ _ Hl) (complete_ty_M_lwf EA (lequiv_wf_l _ _ _ Hl))).
Qed.

Lemma complete_tm_M_ω {G Γ t t' T} : [ G ; Γ ⊢[ lM ] t ≅ t' : T @ lomega ] -> ac_tm G Γ t t' T.
Proof.
  intros H. pose proof (eqtm_wf_ty (i := lM) eq_refl H) as HT.
  destruct (omegaM_red_l (eqty_refl _ _ _ _ _ HT)) as (n & l & A & HR).
  pose proof (tyred_eq _ _ _ _ _ _ HR) as EU.
  destruct (inv_ty_upi (eqty_wf_r (i := lM) eq_refl EU)) as ((_ & _ & _ & W & HA) & _).
  assert (H1 : [ G ; Γ ⊢[ lM ] t ≅ t' : tyUPi n l A @ lomega ])
    by (eapply eqtm_conv; [exact H | exact (eqty_sym _ _ _ _ _ _ EU)]).
  pose proof (complete_tm_M_lwf (ueta_body_eq W HA H1) W) as D.
  destruct (tgt_whnf_tm lM compt_M (eqtm_wf_l (i := lM) eq_refl H1)) as (w & Hr & Hw).
  destruct (tgt_whnf_tm lM compt_M (eqtm_wf_r (i := lM) eq_refl H1)) as (w' & Hr' & Hw').
  eapply actm_red; [exact (tyred_red _ _ _ _ _ _ HR) | apply whnf_tyUPi | exact Hr | exact Hr' | exact Hw | exact Hw' |].
  apply actmnf_ueta.
  eapply ac_tm_red_r; [eapply ac_tm_red_l; [exact D |] |]; apply reds_uapp, reds_uren_ush; assumption.
Qed.

(** ** Completeness *)

Theorem ac_complete_ty {G i Γ T T' l} : compt i -> [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> ac_ty G Γ T T'.
Proof.
  intros [-> | ->] H; [exact (complete_ty_D H) |].
  destruct (lvlM_eqty H) as [Hl | ->]; [exact (complete_ty_M_lwf H Hl) | exact (complete_ty_M_ω H)].
Qed.

Theorem ac_complete_tm {G i Γ t t' T l} : compt i -> [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> ac_tm G Γ t t' T.
Proof.
  intros [-> | ->] H; [exact (complete_tm_D H) |].
  destruct (lvlM_ty (eqtm_wf_ty (i := lM) eq_refl H)) as [Hl | ->];
    [exact (complete_tm_M_lwf H Hl) | exact (complete_tm_M_ω H)].
Qed.
