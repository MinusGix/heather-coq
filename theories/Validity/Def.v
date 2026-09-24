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
From DeLaM.LogRel Require Export Reduction.

Section Validity.
Context `{E : GenericEq} `{EL : !GenericEqLaws}.

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
  | cnil | cvar _ => [ G ; Δ ⊢g ] /\ LK nftm d /\ LK nftm d'
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

Lemma SubRel_ext G Γ : forall Δ d1 d1' d2 d2',
  (forall n, llk d1 n = llk d2 n) -> (forall n, llk d1' n = llk d2' n) ->
  SubRel G Γ Δ d1 d1' -> SubRel G Γ Δ d2 d2'.
Proof.
  induction Γ as [| g | Γ IH A l]; intros Δ d1 d1' d2 d2' H H'; cbn [SubRel].
  - intros (HΔ & N1 & N2); refine (conj HΔ (conj _ _)); intros n; [rewrite <- H | rewrite <- H']; auto.
  - intros (HΔ & N1 & N2); refine (conj HΔ (conj _ _)); intros n; [rewrite <- H | rewrite <- H']; auto.
  - intros (Ht & Hh). split.
    + refine (IH _ _ _ _ _ _ _ Ht); intros n; rewrite !llk_ldrop; auto.
    + rewrite <- H, <- H'.
      rewrite (subst_ext_ty A (ldrop 1 d2) (ldrop 1 d1)), (subst_ext_ty A (ldrop 1 d2') (ldrop 1 d1'));
        [exact Hh | |]; intros n; rewrite !llk_ldrop; auto.
Qed.

Lemma SubRel_ctx {G Γ Δ d d'} : SubRel G Γ Δ d d' -> [ G ; Δ ⊢g ].
Proof.
  revert d d'; induction Γ as [| g | Γ IH A l]; cbn [SubRel]; intros d d'.
  1-2: now intros [].
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
  1-2: intros (HΔ & N1 & N2); auto.
  intros [Ht Hh]; split; [now apply IH | now apply LRtm_sym].
Qed.

Lemma SubRel_trans G Γ : forall Δ d1 d2 d3,
  SubRel G Γ Δ d1 d2 -> SubRel G Γ Δ d2 d3 -> SubRel G Γ Δ d1 d3.
Proof.
  induction Γ as [| g | Γ IH A l]; cbn [SubRel]; intros Δ d1 d2 d3.
  1-2: intros (HΔ & N1 & N2) (_ & _ & N3); auto.
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
  1-2: intros _; refine (conj HΔ' (conj _ _)); intros n; rewrite llk_lren; apply ren_nf.
  intros [Ht Hh]; split.
  - refine (SubRel_ext _ _ _ _ _ _ _ _ _ (IH _ _ _ _ _ Hρ HΔ' Ht));
      intros n; rewrite !llk_ldrop, !llk_lren, llk_ldrop; reflexivity.
  - rewrite !llk_lren, <- !ldrop_lren_ty. exact (LRtm_wk Hρ HΔ' Hh).
Qed.

(** Related substitutions are typed substitutions. *)

Lemma LRtm_escape {l G Γ T T' t t'} :
  LRtm l G Γ T T' t t' -> [ G ; Γ ⊢g t : T @ l ] /\ [ G ; Γ ⊢g t' : T @ l ].
Proof. intros (R & H & Ht). destruct (escape_tm _ _ _ _ _ _ _ _ H _ _ Ht) as (? & ? & _). auto. Qed.

Lemma SubRel_nf G Γ : forall Δ d d', SubRel G Γ Δ d d' -> LK nftm d /\ LK nftm d'.
Proof.
  induction Γ as [| g | Γ IH A l]; cbn [SubRel]; intros Δ d d'.
  1-2: intros (_ & N1 & N2); auto.
  intros [Ht Hh]. destruct (IH _ _ _ Ht) as [N1 N2]. destruct (LRtm_escape Hh) as [H1 H2].
  split; intros [|n].
  - exact (wf_tm_nf H1).
  - specialize (N1 n). now rewrite llk_ldrop in N1.
  - exact (wf_tm_nf H2).
  - specialize (N2 n). now rewrite llk_ldrop in N2.
Qed.

Lemma SubRel_wf_l G Γ : forall Δ d d', SubRel G Γ Δ d d' -> lsub_wf G ge_layer Δ d Γ.
Proof.
  intros Δ d d' H. refine (conj (SubRel_ctx H) (conj (proj1 (SubRel_nf _ _ _ _ _ H)) _)).
  intros n T l Hin; revert Δ d d' H; induction Hin as [Γ A l|Γ A l B l' n Hin IH]; 
    cbn [SubRel]; intros Δ d d' [Ht Hh].
  - rewrite shift_subst_ty. exact (proj1 (LRtm_escape Hh)).
  - rewrite shift_subst_ty. specialize (IH _ _ _ Ht). now rewrite llk_ldrop in IH.
Qed.

Lemma SubRel_wf_r {G Γ Δ d d'} : SubRel G Γ Δ d d' -> lsub_wf G ge_layer Δ d' Γ.
Proof. intros H; exact (SubRel_wf_l _ _ _ _ _ (SubRel_sym _ _ _ _ _ H)). Qed.

End Validity.
