(** * Properties of validity: stages, conversion, PER, lifting under binders *)
From DeLaM.Validity Require Export Def.

Section Props.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

(** ** Stages *)

Lemma LRty_stage {l n G Γ T T'} :
  lmeasure l <= n -> LRty l G Γ T T' <-> exists R, LR n (LRbelow n) G Γ T T' l R.
Proof.
  intros Hn; split; intros [R H]; exists R; now apply (LogRel_stage n) in H || apply (LogRel_stage n).
Qed.

Lemma LRtm_stage {l n G Γ T T' t t'} :
  lmeasure l <= n -> LRtm l G Γ T T' t t' <-> LRrel n G Γ T T' l t t'.
Proof.
  intros Hn; split; intros (R & H & Ht); exists R; split; auto.
  - now apply (LogRel_stage n).
  - now apply (LogRel_stage n).
Qed.

Lemma LRtm_ty {l G Γ T T' t t'} : LRtm l G Γ T T' t t' -> LRty l G Γ T T'.
Proof. intros (R & H & _); now exists R. Qed.

Lemma LRtm_of {l G Γ T T' R t t'} : LogRel l G Γ T T' l R -> R t t' -> LRtm l G Γ T T' t t'.
Proof. intros H Ht; now exists R. Qed.

(** Every term relation of a related pair is the canonical one. *)
Lemma LRtm_inv {l G Γ T T' R t t'} :
  LogRel l G Γ T T' l R -> LRtm l G Γ T T' t t' -> R t t'.
Proof. intros H Ht. exact (proj2 (LRrel_canon _ _ _ _ _ _ _ H t t') Ht). Qed.

(** ** Irrelevance and level conversion *)

Lemma LRtm_irrel_r {l G Γ T T' T'' t t'} :
  LRtm l G Γ T T' t t' -> LRty l G Γ T T'' -> LRtm l G Γ T T'' t t'.
Proof.
  intros (R & H & Ht) [R' H']. exists R'; split; [exact H'|].
  exact (proj1 (LR_irrel _ _ _ _ _ _ _ _ _ _ H H' t t') Ht).
Qed.

Lemma LRtm_irrel_l {l G Γ T T' T'' t t'} :
  LRtm l G Γ T' T t t' -> LRty l G Γ T'' T -> LRtm l G Γ T'' T t t'.
Proof.
  intros (R & H & Ht) [R' H']. exists R'; split; [exact H'|].
  exact (proj1 (LR_irrel_left _ _ _ _ _ _ _ _ _ H H' t t') Ht).
Qed.

Lemma lmeasure_lconv {G l l'} : lequiv (gL G) l l' -> lmeasure l = lmeasure l'.
Proof. apply lequiv_measure. Qed.

Lemma LRty_lconv {l l' G Γ T T'} :
  LRty l' G Γ T T' -> lequiv (gL G) l l' -> LRty l G Γ T T'.
Proof.
  intros [R H] Hl. exists R. unfold LogRel in *. rewrite (lmeasure_lconv Hl).
  eapply LR_lconv; [exact H | exact Hl].
Qed.

Lemma LRtm_lconv {l l' G Γ T T' t t'} :
  LRtm l' G Γ T T' t t' -> lequiv (gL G) l l' -> LRtm l G Γ T T' t t'.
Proof.
  intros (R & H & Ht) Hl. exists R; split; [|exact Ht]. rewrite (lmeasure_lconv Hl).
  eapply LR_lconv; [exact H | exact Hl].
Qed.

(** ** Types: symmetry, transitivity *)

Lemma LRty_sym {l G Γ T T'} : LRty l G Γ T T' -> LRty l G Γ T' T.
Proof. intros [R H]; exists (flipR R); now apply LR_sym. Qed.
Lemma LRty_trans {l G Γ T1 T2 T3} : LRty l G Γ T1 T2 -> LRty l G Γ T2 T3 -> LRty l G Γ T1 T3.
Proof.
  intros [R1 H1] [R2 H2]. exists R1. exact (proj1 (LR_trans _ _ _ _ _ _ _ H1 _ _ H2)).
Qed.

Lemma VTy_sym {G Γ T T' l} : VTy G Γ T T' l -> VTy G Γ T' T l.
Proof. intros H Δ d d' Hd. apply LRty_sym, H, SubRel_sym, Hd. Qed.

Lemma VTy_trans {G Γ T1 T2 T3 l} : VTy G Γ T1 T2 l -> VTy G Γ T2 T3 l -> VTy G Γ T1 T3 l.
Proof.
  intros H1 H2 Δ d d' Hd. eapply LRty_trans; [apply H1, Hd | apply H2, (SubRel_refl_r Hd)].
Qed.

Lemma VTy_refl_l {G Γ T T' l} : VTy G Γ T T' l -> VTy G Γ T T l.
Proof. intros H; eapply VTy_trans; [exact H | now apply VTy_sym]. Qed.

(** ** Terms: symmetry, transitivity, conversion *)

Lemma VTm_ty {G Γ t t' T l} : VTm G Γ t t' T l -> VTy G Γ T T l.
Proof. intros H Δ d d' Hd. exact (LRtm_ty (H _ _ _ Hd)). Qed.

Lemma VTm_sym {G Γ t t' T l} : VTm G Γ t t' T l -> VTm G Γ t' t T l.
Proof. intros H Δ d d' Hd. apply LRtm_sym, H, SubRel_sym, Hd. Qed.

Lemma VTm_trans {G Γ t1 t2 t3 T l} :
  VTm G Γ t1 t2 T l -> VTm G Γ t2 t3 T l -> VTm G Γ t1 t3 T l.
Proof.
  intros H1 H2 Δ d d' Hd. eapply LRtm_trans; [apply H1, (SubRel_refl_l Hd) | apply H2, Hd].
Qed.

Lemma VTm_conv {G Γ t t' T T' l} :
  VTm G Γ t t' T' l -> VTy G Γ T T' l -> VTm G Γ t t' T l.
Proof.
  intros Ht HT Δ d d' Hd.
  pose proof (Ht _ _ _ Hd) as H1.                 (* at T'[d], T'[d'] *)
  pose proof (HT _ _ _ (SubRel_refl_l Hd)) as H2. (* T[d] ~ T'[d] *)
  pose proof (VTy_refl_l HT _ _ _ Hd) as H3.      (* T[d] ~ T[d'] *)
  (* move the left type from T'[d] to T[d], then the right type to T[d'] *)
  assert (H4 : LRtm l G Δ T[d] T'[d'] t[d] t'[d']).
  { eapply LRtm_irrel_l; [exact H1 | eapply LRty_trans; [exact H2 | exact (LRtm_ty H1)]]. }
  exact (LRtm_irrel_r H4 H3).
Qed.

Lemma VTy_lconv {G Γ T T' l l'} : VTy G Γ T T' l' -> lequiv (gL G) l l' -> VTy G Γ T T' l.
Proof. intros H Hl Δ d d' Hd. exact (LRty_lconv (H _ _ _ Hd) Hl). Qed.
Lemma VTm_lconv {G Γ t t' T l l'} : VTm G Γ t t' T l' -> lequiv (gL G) l l' -> VTm G Γ t t' T l.
Proof. intros H Hl Δ d d' Hd. exact (LRtm_lconv (H _ _ _ Hd) Hl). Qed.

(** ** Under global weakenings *)

Lemma VTyG_sym {G Γ T T' l} : VTyG G Γ T T' l -> VTyG G Γ T' T l.
Proof. intros H G' γ Hγ. exact (VTy_sym (H _ _ Hγ)). Qed.
Lemma VTyG_trans {G Γ T1 T2 T3 l} : VTyG G Γ T1 T2 l -> VTyG G Γ T2 T3 l -> VTyG G Γ T1 T3 l.
Proof. intros H1 H2 G' γ Hγ. exact (VTy_trans (H1 _ _ Hγ) (H2 _ _ Hγ)). Qed.
Lemma VTyG_refl_l {G Γ T T' l} : VTyG G Γ T T' l -> VTyG G Γ T T l.
Proof. intros H G' γ Hγ. exact (VTy_refl_l (H _ _ Hγ)). Qed.
Lemma VTmG_ty {G Γ t t' T l} : VTmG G Γ t t' T l -> VTyG G Γ T T l.
Proof. intros H G' γ Hγ. exact (VTm_ty (H _ _ Hγ)). Qed.
Lemma VTmG_sym {G Γ t t' T l} : VTmG G Γ t t' T l -> VTmG G Γ t' t T l.
Proof. intros H G' γ Hγ. exact (VTm_sym (H _ _ Hγ)). Qed.
Lemma VTmG_trans {G Γ t1 t2 t3 T l} :
  VTmG G Γ t1 t2 T l -> VTmG G Γ t2 t3 T l -> VTmG G Γ t1 t3 T l.
Proof. intros H1 H2 G' γ Hγ. exact (VTm_trans (H1 _ _ Hγ) (H2 _ _ Hγ)). Qed.
Lemma VTmG_conv {G Γ t t' T T' l} : VTmG G Γ t t' T' l -> VTyG G Γ T T' l -> VTmG G Γ t t' T l.
Proof. intros H1 H2 G' γ Hγ. exact (VTm_conv (H1 _ _ Hγ) (H2 _ _ Hγ)). Qed.
Lemma VTyG_lconv {G Γ T T' l l'} : VTyG G Γ T T' l' -> lequiv (gL G) l l' -> VTyG G Γ T T' l.
Proof. intros H Hl G' γ Hγ. apply (VTy_lconv (H _ _ Hγ)). now rewrite (proj1 Hγ). Qed.
Lemma VTmG_lconv {G Γ t t' T l l'} : VTmG G Γ t t' T l' -> lequiv (gL G) l l' -> VTmG G Γ t t' T l.
Proof. intros H Hl G' γ Hγ. apply (VTm_lconv (H _ _ Hγ)). now rewrite (proj1 Hγ). Qed.

(** ** Extending related substitutions *)

Lemma SubRel_cons {G Γ Δ d d' A l a a'} :
  SubRel G Γ Δ d d' -> LRtm l G Δ A[d] A[d'] a a' ->
  SubRel G (Γ ,, A @ l) Δ (lcons d a) (lcons d' a').
Proof. intros Hd Ha; cbn [SubRel]; split; [exact Hd | exact Ha]. Qed.

(** Variables of the extended context are related (neutral reflection). *)
Lemma var0_LRtm {G Δ A A' l} :
  LRty l G (Δ ,, A @ l) A⟨↑⟩ A'⟨↑⟩ -> [ G ; Δ ,, A @ l ⊢g ] ->
  LRtm l G (Δ ,, A @ l) A⟨↑⟩ A'⟨↑⟩ (var 0) (var 0).
Proof.
  intros [R H] HΔ. exists R; split; [exact H|].
  destruct (escape_ty _ _ _ _ _ _ _ _ H) as (_ & _ & HAA).
  assert (Hv : [ G ; Δ ,, A @ l ⊢g var 0 : A⟨↑⟩ @ l ])
    by (apply wf_var; [now rewrite ge_typeof | constructor]).
  eapply LR_neutral; [exact H | apply gne_tm_var, Hv |].
  apply gne_tm_var. eapply wf_conv; [exact Hv | rewrite ge_typeof; apply eqty_sym, geq_ty_sound, HAA].
Qed.

Lemma llk_llift_lcons d n : llk (llift d) n = llk (lcons (lren d ↑) (var 0)) n.
Proof. rewrite llk_llift; destruct n; cbn; auto. now rewrite llk_lren. Qed.

Lemma SubRel_lift {G Γ Δ d d' A l} :
  SubRel G Γ Δ d d' -> VTy G Γ A A l -> [ G ; Δ ⊢g A[d] @ l ] -> lwf (gL G) l ->
  SubRel G (Γ ,, A @ l) (Δ ,, A[d] @ l) (llift d) (llift d').
Proof.
  intros Hd HA HAd Hl.
  assert (HΔ : [ G ; Δ ,, A[d] @ l ⊢g ]) by now apply ext_wf_g.
  assert (Hw : wk1 : (Δ ,, A[d] @ l) ≤ Δ) by (constructor; constructor).
  pose proof (SubRel_wk _ _ _ _ _ _ _ Hw HΔ Hd) as Hd1.
  eapply SubRel_ext; [symmetry; apply llk_llift_lcons | symmetry; apply llk_llift_lcons |].
  apply SubRel_cons; [exact Hd1|].
  rewrite <- !subst_ren_lren_ty.
  apply var0_LRtm; [| exact HΔ].
  pose proof (HA _ _ _ Hd1) as H. now rewrite <- !subst_ren_lren_ty in H.
Qed.

End Props.
