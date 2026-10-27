(** * Semantic validity (ch. 7a, specialised to the MLTT fragment)

    PER-style, following the paper's relational presentation:
    - [SubRel Γ Δ d d']: related local substitutions from [Δ] into [Γ],
      defined by recursion on the syntax of [Γ] (the head of [Γ, A] is
      related in the relation of [A] at the related tails);
    - [VTy Γ T T' l]: related substitutions give related types;
    - [VTm Γ t t' T l]: related substitutions give related terms.

    [LRrel] is the canonical term relation of a related pair of types: the
    union over derivations, which irrelevance makes equivalent to each of
    them and saturation makes usable as a relation.  It gives the Π case
    its domain/codomain functions without choice or extensionality. *)
From DeLaM.LogRel Require Export Reduction LevelInv.

Section Validity.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

(** ** The canonical term relation *)

Definition LRrel n G Γ T T' l : tm -> tm -> Prop :=
  fun t t' => exists R, LR n (LRbelow n) G Γ T T' l R /\ R t t'.

Lemma LRrel_canon n G Γ T T' l R :
  LR n (LRbelow n) G Γ T T' l R -> releq R (LRrel n G Γ T T' l).
Proof.
  intros H t t'; split.
  - intros Ht; now exists R.
  - intros (R' & H' & Ht). exact (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ H H' t t') Ht).
Qed.

Lemma LR_canon n G Γ T T' l R :
  LR n (LRbelow n) G Γ T T' l R -> LR n (LRbelow n) G Γ T T' l (LRrel n G Γ T T' l).
Proof. intros H; exact (LR_releq _ _ _ _ _ _ _ _ _ H (LRrel_canon _ _ _ _ _ _ _ H)). Qed.

(** Related types and related terms at level [l]. *)
Definition LRty l G Γ T T' := exists R, LogRel l G Γ T T' l R.
Definition LRtm l G Γ T T' t t' := LRrel (lmeasure l) G Γ T T' l t t'.

(** ** Related substitutions *)

Fixpoint SubRel (G : gctx) (Γ Δ : ctx) (d d' : lsub) {struct Γ} : Prop :=
  match Γ with
  | cnil | cvar _ =>
      [ G ; Δ ⊢g ] /\ LK dnftm d /\ LK dnftm d' /\ lsub_tail d Γ Δ /\ lsub_tail d' Γ Δ
  | cext Γ A l =>
      SubRel G Γ Δ (ldrop 1 d) (ldrop 1 d') /\
      LRtm l G Δ A[ldrop 1 d] A[ldrop 1 d'] (llk d 0) (llk d' 0)
  end.

Definition VTy G Γ T T' l := forall Δ d d', SubRel G Γ Δ d d' -> LRty l G Δ T[d] T'[d'].
Definition VTm G Γ t t' T l :=
  forall Δ d d', SubRel G Γ Δ d d' -> LRtm l G Δ T[d] T[d'] t[d] t'[d'].

(** ** Syntax *)

Lemma shift_subst_ty (A : ty) d : A⟨↑⟩[d] = A[ldrop 1 d].
Proof. apply ren_subst_ty; intros n; rewrite llk_ldrop, rlk_shift1; reflexivity. Qed.
Lemma subst_ren_lren_ty (T : ty) d (r : rsub) : T[d]⟨r⟩ = T[lren d r].
Proof. apply subst_ren_ty; intros n; now rewrite llk_lren. Qed.
Lemma subst_ren_lren (t : tm) d (r : rsub) : t[d]⟨r⟩ = t[lren d r].
Proof. apply subst_ren; intros n; now rewrite llk_lren. Qed.
Lemma ldrop_lren_ty (A : ty) d (r : rsub) : A[ldrop 1 d]⟨r⟩ = A[ldrop 1 (lren d r)].
Proof. apply subst_ren_ty; intros n; now rewrite !llk_ldrop, llk_lren. Qed.

(** ** Basic properties of related substitutions *)

Lemma lsub_tail_ext d d2 Γ Δ : (forall n, llk d n = llk d2 n) -> lsub_tail d Γ Δ -> lsub_tail d2 Γ Δ.
Proof. intros H [Ht Hl]; split; [exact Ht | intros n; rewrite <- H; apply Hl]. Qed.

Lemma SubRel_ext G Γ : forall Δ d1 d1' d2 d2',
  (forall n, llk d1 n = llk d2 n) -> (forall n, llk d1' n = llk d2' n) ->
  SubRel G Γ Δ d1 d1' -> SubRel G Γ Δ d2 d2'.
Proof.
  induction Γ as [| g | Γ IH A l]; intros Δ d1 d1' d2 d2' H H'; cbn [SubRel].
  1-2: intros (HΔ & N1 & N2 & T1 & T2); refine (conj HΔ (conj _ (conj _ (conj _ _))));
    eauto using lsub_tail_ext; intros n; [rewrite <- H | rewrite <- H']; auto.
  - intros (Ht & Hh). split.
    + refine (IH _ _ _ _ _ _ _ Ht); intros n; rewrite !llk_ldrop; auto.
    + rewrite <- H, <- H'.
      rewrite (subst_ext_ty A (ldrop 1 d2) (ldrop 1 d1)), (subst_ext_ty A (ldrop 1 d2') (ldrop 1 d1'));
        [exact Hh | |]; intros n; rewrite !llk_ldrop; auto.
Qed.

Lemma SubRel_ctx {G Γ Δ d d'} : SubRel G Γ Δ d d' -> [ G ; Δ ⊢g ].
Proof.
  revert d d'; induction Γ as [| g | Γ IH A l]; cbn [SubRel]; intros d d'.
  1-2: now intros (? & _).
  intros [Ht _]; exact (IH _ _ Ht).
Qed.

(** Symmetry and transitivity: from those of the logical relation. *)

Lemma LRtm_sym {l G Γ T T' t t'} : LRtm l G Γ T T' t t' -> LRtm l G Γ T' T t' t.
Proof. intros (R & H & Ht). exists (flipR R); split; [now apply LR_sym | exact Ht]. Qed.

Lemma LRtm_trans {l G Γ T1 T2 T3 t1 t2 t3} :
  LRtm l G Γ T1 T2 t1 t2 -> LRtm l G Γ T2 T3 t2 t3 -> LRtm l G Γ T1 T3 t1 t3.
Proof.
  intros (R1 & H1 & Ht1) (R2 & H2 & Ht2).
  destruct (LR_trans _ _ _ _ _ _ _ H1 _ _ H2) as [H3 Hc].
  exists R1; split; [exact H3 | exact (Hc _ _ _ Ht1 Ht2)].
Qed.

Lemma SubRel_sym G Γ : forall Δ d d', SubRel G Γ Δ d d' -> SubRel G Γ Δ d' d.
Proof.
  induction Γ as [| g | Γ IH A l]; cbn [SubRel]; intros Δ d d'.
  1-2: intros (HΔ & N1 & N2 & T1 & T2); auto.
  intros [Ht Hh]; split; [now apply IH | now apply LRtm_sym].
Qed.

Lemma SubRel_trans G Γ : forall Δ d1 d2 d3,
  SubRel G Γ Δ d1 d2 -> SubRel G Γ Δ d2 d3 -> SubRel G Γ Δ d1 d3.
Proof.
  induction Γ as [| g | Γ IH A l]; cbn [SubRel]; intros Δ d1 d2 d3.
  1-2: intros (HΔ & N1 & N2 & T1 & T2) (_ & _ & N3 & _ & T3); auto.
  intros [Ht1 Hh1] [Ht2 Hh2]; split; [eapply IH; eauto | eapply LRtm_trans; eauto].
Qed.

Lemma SubRel_refl_l {G Γ Δ d d'} : SubRel G Γ Δ d d' -> SubRel G Γ Δ d d.
Proof. intros H; eapply SubRel_trans; [exact H | now apply SubRel_sym]. Qed.
Lemma SubRel_refl_r {G Γ Δ d d'} : SubRel G Γ Δ d d' -> SubRel G Γ Δ d' d'.
Proof. intros H; eapply SubRel_trans; [apply SubRel_sym, H | exact H]. Qed.

(** Kripke: related substitutions stay related under weakenings. *)

Lemma LRtm_wk {l G Γ Δ} {ρ : wk} {T T' t t'} :
  ρ : Δ ≤ Γ -> [ G ; Δ ⊢g ] ->
  LRtm l G Γ T T' t t' -> LRtm l G Δ T⟨ρ⟩ T'⟨ρ⟩ t⟨ρ⟩ t'⟨ρ⟩.
Proof.
  intros Hρ HΔ (R & H & Ht).
  destruct (LR_wk _ _ _ _ _ _ _ H _ _ Hρ HΔ) as (R' & H' & HR').
  exists R'; split; [exact H' | now apply HR'].
Qed.

Lemma SubRel_wk G Γ : forall Δ Δ' (ρ : wk) d d', ρ : Δ' ≤ Δ -> [ G ; Δ' ⊢g ] ->
  SubRel G Γ Δ d d' -> SubRel G Γ Δ' (lren d ρ) (lren d' ρ).
Proof.
  induction Γ as [| g | Γ IH A l]; cbn [SubRel]; intros Δ Δ' ρ d d' Hρ HΔ'.
  1-2: intros (_ & N1 & N2 & T1 & T2); refine (conj HΔ' (conj _ (conj _ (conj _ _))));
    try (intros n; rewrite llk_lren; apply ren_dnf; auto);
    eapply lsub_tail_wkr; eauto using wk_wf_wkr.
  intros [Ht Hh]; split.
  - refine (SubRel_ext _ _ _ _ _ _ _ _ _ (IH _ _ _ _ _ Hρ HΔ' Ht));
      intros n; rewrite !llk_ldrop, !llk_lren, llk_ldrop; reflexivity.
  - rewrite !llk_lren, <- !ldrop_lren_ty. exact (LRtm_wk Hρ HΔ' Hh).
Qed.

(** Kripke weakenings (global, then local). *)

Lemma LRtm_kw {l G Γ} (ρ : kwk G Γ) {T T' t t'} :
  LRtm l G Γ T T' t t' ->
  LRtm l (kw_G ρ) (kw_Δ ρ) (kty ρ T) (kty ρ T') (ktm ρ t) (ktm ρ t').
Proof.
  intros (R & H & Ht).
  destruct (LR_kwk _ _ _ _ _ _ _ H ρ) as (R' & H' & HR').
  exists R'; split; [exact H' | now apply HR'].
Qed.

(** The substitution a Kripke weakening induces on a substitution into [Δ]. *)
Definition kwsub {G Δ} (ρ : kwk G Δ) (d : lsub) : lsub := lren d⟦kw_γ ρ⟧ (kw_r ρ).

Lemma llk_kwsub {G Δ} (ρ : kwk G Δ) d n : llk (kwsub ρ d) n = ktm ρ (llk d n).
Proof. unfold kwsub, ktm. now rewrite llk_lren, llk_gwa. Qed.

Lemma kty_subst {G Δ} (ρ : kwk G Δ) (T : ty) d : kty ρ T[d] = T⟦kw_γ ρ⟧[kwsub ρ d].
Proof. unfold kty, kwsub. now rewrite gwa_subst_ty, subst_ren_lren_ty. Qed.

Lemma SubRel_kw G Γ : forall Δ (ρ : kwk G Δ) d d', SubRel G Γ Δ d d' ->
  SubRel (kw_G ρ) Γ⟦kw_γ ρ⟧ (kw_Δ ρ) (kwsub ρ d) (kwsub ρ d').
Proof.
  induction Γ as [| g | Γ IH A l]; intros Δ ρ d d'.
  1-2: cbn [SubRel]; intros (_ & N1 & N2 & T1 & T2);
    pose proof (lsub_tail_gwa _ _ _ (kw_γ ρ) T1) as T1';
    pose proof (lsub_tail_gwa _ _ _ (kw_γ ρ) T2) as T2';
    rewrite ?gwa_cnil, ?gwa_cvar in *; cbn [SubRel];
    refine (conj (kw_ctx ρ) (conj _ (conj _ (conj _ _))));
    try (intros n; rewrite llk_kwsub; unfold ktm; apply ren_dnf, dnf_gwa; auto);
    unfold kwsub; eapply lsub_tail_wkr; first [exact (wk_wf_wkr _ _ _ (kw_wf ρ)) | eassumption].
  - rewrite gwa_cext. cbn [SubRel]. intros [Ht Hh]; split.
    + refine (SubRel_ext _ _ _ _ _ _ _ _ _ (IH _ ρ _ _ Ht));
        intros n; rewrite !llk_ldrop, !llk_kwsub, llk_ldrop; reflexivity.
    + pose proof (LRtm_kw ρ Hh) as X. rewrite !kty_subst, <- !llk_kwsub in X.
      rewrite (subst_ext_ty _ (ldrop 1 (kwsub ρ d)) (kwsub ρ (ldrop 1 d))),
              (subst_ext_ty _ (ldrop 1 (kwsub ρ d')) (kwsub ρ (ldrop 1 d'))).
      * exact X.
      * intros n; rewrite llk_ldrop, !llk_kwsub, llk_ldrop; reflexivity.
      * intros n; rewrite llk_ldrop, !llk_kwsub, llk_ldrop; reflexivity.
Qed.

(** ** Validity under global weakenings

    The Π case of the relation is Kripke over global weakenings, so the
    fundamental theorem's motive must be too. *)

Definition VTyG G Γ T T' l := forall G' γ, gwk_ok γ G' G -> VTy G' Γ⟦γ⟧ T⟦γ⟧ T'⟦γ⟧ l.
Definition VTmG G Γ t t' T l := forall G' γ, gwk_ok γ G' G -> VTm G' Γ⟦γ⟧ t⟦γ⟧ t'⟦γ⟧ T⟦γ⟧ l.

Lemma VTyG_loc {G Γ T T' l} : VTyG G Γ T T' l -> VTy G Γ T T' l.
Proof. intros H; exact (H G gwk_id (gwk_ok_id G)). Qed.
Lemma VTmG_loc {G Γ t t' T l} : VTmG G Γ t t' T l -> VTm G Γ t t' T l.
Proof. intros H; exact (H G gwk_id (gwk_ok_id G)). Qed.

Lemma VTyG_gwk {G Γ T T' l G' γ} : VTyG G Γ T T' l -> gwk_ok γ G' G ->
  VTyG G' Γ⟦γ⟧ T⟦γ⟧ T'⟦γ⟧ l.
Proof.
  intros H Hγ G'' γ' Hγ'. rewrite !gwa_comp_ty, gwa_comp_ctx. exact (H _ _ (gwk_ok_comp Hγ' Hγ)).
Qed.
Lemma VTmG_gwk {G Γ t t' T l G' γ} : VTmG G Γ t t' T l -> gwk_ok γ G' G ->
  VTmG G' Γ⟦γ⟧ t⟦γ⟧ t'⟦γ⟧ T⟦γ⟧ l.
Proof.
  intros H Hγ G'' γ' Hγ'. rewrite !gwa_comp_ty, !gwa_comp_tm, gwa_comp_ctx.
  exact (H _ _ (gwk_ok_comp Hγ' Hγ)).
Qed.

Lemma VTyG_intro {G Γ T T' l} :
  (forall G' γ, gwk_ok γ G' G -> [ ⊢ G' ] -> VTy G' Γ⟦γ⟧ T⟦γ⟧ T'⟦γ⟧ l) -> VTyG G Γ T T' l.
Proof. intros H G' γ Hγ Δ d d' Hd. exact (H G' γ Hγ (ctx_glob _ _ _ (SubRel_ctx Hd)) Δ d d' Hd). Qed.
Lemma VTmG_intro {G Γ t t' T l} :
  (forall G' γ, gwk_ok γ G' G -> [ ⊢ G' ] -> VTm G' Γ⟦γ⟧ t⟦γ⟧ t'⟦γ⟧ T⟦γ⟧ l) -> VTmG G Γ t t' T l.
Proof. intros H G' γ Hγ Δ d d' Hd. exact (H G' γ Hγ (ctx_glob _ _ _ (SubRel_ctx Hd)) Δ d d' Hd). Qed.

(** A valid type at a Kripke weakening of a related substitution. *)
Lemma VTyG_kw {G Γ A A' l Δ d d'} (ρ : kwk G Δ) : VTyG G Γ A A' l -> SubRel G Γ Δ d d' ->
  LRty l (kw_G ρ) (kw_Δ ρ) (kty ρ A[d]) (kty ρ A'[d']).
Proof.
  intros VA Hd. rewrite !kty_subst. exact (VA _ _ (kw_gok ρ) _ _ _ (SubRel_kw _ _ _ ρ _ _ Hd)).
Qed.

(** Related substitutions are typed substitutions. *)

Lemma LRtm_escape {l G Γ T T' t t'} :
  LRtm l G Γ T T' t t' -> [ G ; Γ ⊢g t : T @ l ] /\ [ G ; Γ ⊢g t' : T @ l ].
Proof. intros (R & H & Ht). destruct (escape_tm _ _ _ _ _ _ _ _ H _ _ Ht) as (? & ? & _). auto. Qed.

Lemma SubRel_dnf G Γ : forall Δ d d', SubRel G Γ Δ d d' -> LK dnftm d /\ LK dnftm d'.
Proof.
  induction Γ as [| g | Γ IH A l]; cbn [SubRel]; intros Δ d d'.
  1-2: intros (_ & N1 & N2 & _); auto.
  intros [Ht Hh]. destruct (IH _ _ _ Ht) as [N1 N2]. destruct (LRtm_escape Hh) as [H1 H2].
  split; intros [|n].
  - exact (wf_tm_dnf H1).
  - specialize (N1 n). now rewrite llk_ldrop in N1.
  - exact (wf_tm_dnf H2).
  - specialize (N2 n). now rewrite llk_ldrop in N2.
Qed.

Lemma SubRel_nf G Γ : forall Δ d d', SubRel G Γ Δ d d' -> LK nftm d /\ LK nftm d'.
Proof.
  intros Δ d d' H; destruct (SubRel_dnf _ _ _ _ _ H) as [N1 N2].
  split; intros n; apply dnftm_nftm; auto.
Qed.

Lemma SubRel_tail G Γ : forall Δ d d', SubRel G Γ Δ d d' -> lsub_tail d Γ Δ /\ lsub_tail d' Γ Δ.
Proof.
  induction Γ as [| g | Γ IH A l]; cbn [SubRel]; intros Δ d d'.
  1-2: intros (_ & _ & _ & T1 & T2); auto.
  intros [Ht _]. destruct (IH _ _ _ Ht) as [[T1 L1] [T2 L2]].
  split; split; auto; intros n; cbn [clen];
    replace (S (clen Γ) + n) with (1 + (clen Γ + n)) by lia; rewrite <- llk_ldrop; auto.
Qed.

Lemma SubRel_wf_l G Γ : forall Δ d d', SubRel G Γ Δ d d' -> lsub_wf G ge_layer Δ d Γ.
Proof.
  intros Δ d d' H. constructor;
    [rewrite ge_typeof; exact (SubRel_ctx H) | exact (proj1 (SubRel_dnf _ _ _ _ _ H))
    | exact (proj1 (SubRel_tail _ _ _ _ _ H)) |].
  intros n T l Hin; revert Δ d d' H; induction Hin as [Γ A l|Γ A l B l' n Hin IH]; 
    cbn [SubRel]; intros Δ d d' [Ht Hh].
  - rewrite shift_subst_ty. exact (proj1 (LRtm_escape Hh)).
  - rewrite shift_subst_ty. specialize (IH _ _ _ Ht). now rewrite llk_ldrop in IH.
Qed.

Lemma SubRel_wf_r {G Γ Δ d d'} : SubRel G Γ Δ d d' -> lsub_wf G ge_layer Δ d' Γ.
Proof. intros H; exact (SubRel_wf_l _ _ _ _ _ (SubRel_sym _ _ _ _ _ H)). Qed.

End Validity.
