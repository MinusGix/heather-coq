(** * Consequences for the declarative system

    At layer P ([DeclEq lD]) and at layer M ([DeclEq lM], relation
    [LR_M]), for arbitrary well-formed global contexts: reducibility
    comes from the fundamental theorems with global substitutions
    ([Reducible]).  Closed canonicity needs a global context without type
    or term bindings ([ctx_only]), whose global variables would be closed
    neutrals. *)
From DeLaM.Typing Require Export DeclInstance.
From DeLaM.Validity Require Export Reducible DeclConsequencesP.

Section DeclConsequences.

Local Notation DEP := (DeclEq lD compt_D).
Local Notation DELP := (DeclEqLaws lD compt_D).
Local Notation DEM := (DeclEq lM compt_M).
Local Notation DELM := (DeclEqLaws lM compt_M).
Local Notation LRM := (LR_M DEP DEM).

Local Instance DeclEqM_inst : GenericEqM DEP DEM := DeclEqM.
Local Instance LRM_laws : VPLaws (@lr_vp LRM) := vpM_laws DEP DEM.

(** ** Reducibility *)

Lemma redM_eqty G Γ T T' l : [ G ; Γ ⊢[ lM ] T ≅ T' @ l ] -> @LRty DEM LRM l G Γ T T'.
Proof. intros H; exact (reducibleM_eqty DEP DEM H). Qed.
Lemma redM_eqtm G Γ t t' T l : [ G ; Γ ⊢[ lM ] t ≅ t' : T @ l ] -> @LRtm DEM LRM l G Γ T T t t'.
Proof. intros H; exact (reducibleM_eqtm DEP DEM H). Qed.

(** ** Layer M *)

Theorem declM_pi_inj {G Γ l l1 l2 l3 l4 A A' B B'} :
  [ G ; Γ ⊢[ lM ] tyPi l1 l2 A B ≅ tyPi l3 l4 A' B' @ l ] ->
  lequiv (gL G) l3 l1 /\ lequiv (gL G) l4 l2 /\
  [ G ; Γ ⊢[ lM ] A ≅ A' @ l1 ] /\ [ G ; Γ ,, A @ l1 ⊢[ lM ] B ≅ B' @ l2 ].
Proof. exact (pi_inj (E := DEM) (LP := LRM) redM_eqty). Qed.

Theorem declM_U_inj {G Γ l l' k} : [ G ; Γ ⊢[ lM ] tyU l ≅ tyU l' @ k ] -> lequiv (gL G) l' l.
Proof. exact (U_inj (E := DEM) (LP := LRM) redM_eqty). Qed.

Theorem declM_whnf_normalization_tm {G Γ t T l} : [ G ; Γ ⊢[ lM ] t : T @ l ] ->
  exists w, reds t w /\ whnf w.
Proof.
  intros H. destruct (whnf_normalization_tm (E := DEM) (LP := LRM) redM_eqtm H) as (w & Hw & Hwh).
  exists w; split; [exact (tmred_red _ _ _ _ _ _ _ Hw) | exact Hwh].
Qed.

Theorem declM_whnf_normalization_ty {G Γ T l} : [ G ; Γ ⊢[ lM ] T @ l ] ->
  exists W, reds_ty T W /\ whnf_ty W.
Proof.
  intros H. destruct (whnf_normalization_ty (E := DEM) (LP := LRM) redM_eqty H) as (W & HW & HWh).
  exists W; split; [exact (tyred_red _ _ _ _ _ _ HW) | exact HWh].
Qed.

Theorem declM_closed_nat_canonicity {G t} : ctx_only G -> [ G ; cnil ⊢[ lM ] t : tyNat @ lzero ] ->
  exists n, [ G ; cnil ⊢[ lM ] t ≅ numeral n : tyNat @ lzero ].
Proof. exact (closed_nat_canonicity (E := DEM) (LP := LRM) redM_eqtm). Qed.

Theorem declM_nat_not_pi {G Γ k l l' A B} : ~ [ G ; Γ ⊢[ lM ] tyNat ≅ tyPi l l' A B @ k ].
Proof. exact (nat_not_pi (E := DEM) (LP := LRM) redM_eqty). Qed.
Theorem declM_nat_not_U {G Γ k l} : ~ [ G ; Γ ⊢[ lM ] tyNat ≅ tyU l @ k ].
Proof. exact (nat_not_U (E := DEM) (LP := LRM) redM_eqty). Qed.
Theorem declM_U_not_pi {G Γ k l l1 l2 A B} : ~ [ G ; Γ ⊢[ lM ] tyU l ≅ tyPi l1 l2 A B @ k ].
Proof. exact (U_not_pi (E := DEM) (LP := LRM) redM_eqty). Qed.

(** ** Contextual types at M: injectivity and closed canonicity *)

Section ModInv.
Context `{E : GenericEq} `{LP : LRParams}.

Lemma CTyp_det {G Γ Δ k Δ1 k1 l l'} : [ G ; Γ ⊢g tyCTyp Δ k @ l ] ->
  [ G ; Γ ⊢g tyCTyp Δ k ⤳* tyCTyp Δ1 k1 @ l' ] -> Δ1 = Δ /\ k1 = k.
Proof.
  intros HT HR. pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HR (tyred_refl _ _ HT)
                             (whnf_tyCTyp _ _) (whnf_tyCTyp _ _)) as Eq. now injection Eq.
Qed.

Lemma CTrm_det {G Γ Δ A k Δ1 A1 k1 l l'} : [ G ; Γ ⊢g tyCTrm Δ A k @ l ] ->
  [ G ; Γ ⊢g tyCTrm Δ A k ⤳* tyCTrm Δ1 A1 k1 @ l' ] -> Δ1 = Δ /\ A1 = A /\ k1 = k.
Proof.
  intros HT HR. pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HR (tyred_refl _ _ HT)
                             (whnf_tyCTrm _ _ _) (whnf_tyCTrm _ _ _)) as Eq. now injection Eq.
Qed.

Lemma ModRel_CTyp_inv {G Γ Δ k Δ' k' l R} : ModRel G Γ (tyCTyp Δ k) (tyCTyp Δ' k') l R ->
  [ G ; Γ ⊢g tyCTyp Δ k @ l ] -> [ G ; Γ ⊢g tyCTyp Δ' k' @ l ] ->
  vp_ctx lr_vp G Δ Δ' /\ lequiv (gL G) k k' /\ releq R (CTypRel G Γ Δ Δ' k k').
Proof.
  intros HM HT HT'. inversion HM; subst.
  - match goal with
    | HTD : tyred _ _ _ (tyCTyp Δ k) _ _, HT'D : tyred _ _ _ (tyCTyp Δ' k') _ _ |- _ =>
        destruct (CTyp_det HT HTD) as [-> ->]; destruct (CTyp_det HT' HT'D) as [-> ->]
    end.
    refine (conj _ (conj _ _)); assumption.
  - exfalso. match goal with HTD : tyred _ _ _ (tyCTyp Δ k) (tyCTrm _ _ _) _ |- _ =>
      pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HTD (tyred_refl _ _ HT) (whnf_tyCTrm _ _ _) (whnf_tyCTyp _ _))
        as Eq; discriminate Eq end.
Qed.

Lemma ModRel_CTrm_inv {G Γ Δ A k Δ' A' k' l R} : ModRel G Γ (tyCTrm Δ A k) (tyCTrm Δ' A' k') l R ->
  [ G ; Γ ⊢g tyCTrm Δ A k @ l ] -> [ G ; Γ ⊢g tyCTrm Δ' A' k' @ l ] ->
  vp_ctx lr_vp G Δ Δ' /\ vp_ty lr_vp G Δ A A' k /\ lequiv (gL G) k k' /\
  releq R (CTrmRel G Γ Δ Δ' A A' k k').
Proof.
  intros HM HT HT'. inversion HM; subst.
  - exfalso. match goal with HTD : tyred _ _ _ (tyCTrm Δ A k) (tyCTyp _ _) _ |- _ =>
      pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HTD (tyred_refl _ _ HT) (whnf_tyCTyp _ _) (whnf_tyCTrm _ _ _))
        as Eq; discriminate Eq end.
  - match goal with
    | HTD : tyred _ _ _ (tyCTrm Δ A k) _ _, HT'D : tyred _ _ _ (tyCTrm Δ' A' k') _ _ |- _ =>
        destruct (CTrm_det HT HTD) as (-> & -> & ->); destruct (CTrm_det HT' HT'D) as (-> & -> & ->)
    end.
    refine (conj _ (conj _ (conj _ _))); assumption.
Qed.

End ModInv.

Theorem declM_CTyp_inj {G Γ Δ Δ' l l' k} : [ G ; Γ ⊢[ lM ] tyCTyp Δ l ≅ tyCTyp Δ' l' @ k ] ->
  [ G ⊢[ lD ] Δ ≅ Δ' ] /\ lequiv (gL G) l l'.
Proof.
  intros H. destruct (redM_eqty _ _ _ _ _ H) as [R HR].
  pose proof (eqty_wf_l (i := lM) eq_refl H) as HT. pose proof (eqty_wf_r (i := lM) eq_refl H) as HT'.
  destruct (LR_inv_CTyp HR (tyred_refl _ _ HT)) as [_ HM].
  destruct (ModRel_CTyp_inv HM HT HT') as ((HDD & _) & Hl & _). split; assumption.
Qed.

Theorem declM_CTrm_inj {G Γ Δ Δ' A A' l l' k} : [ G ; Γ ⊢[ lM ] tyCTrm Δ A l ≅ tyCTrm Δ' A' l' @ k ] ->
  [ G ⊢[ lD ] Δ ≅ Δ' ] /\ [ G ; Δ ⊢[ lD ] A ≅ A' @ l ] /\ lequiv (gL G) l l'.
Proof.
  intros H. destruct (redM_eqty _ _ _ _ _ H) as [R HR].
  pose proof (eqty_wf_l (i := lM) eq_refl H) as HT. pose proof (eqty_wf_r (i := lM) eq_refl H) as HT'.
  destruct (LR_inv_CTrm HR (tyred_refl _ _ HT)) as [_ HM].
  destruct (ModRel_CTrm_inv HM HT HT') as ((HDD & _) & (HAA & _) & Hl & _). exact (conj HDD (conj HAA Hl)).
Qed.

(** Closed terms of a contextual type are [box]es. *)
Theorem declM_closed_CTyp_canonicity {G t Δ l} : ctx_only G -> [ G ; cnil ⊢[ lM ] t : tyCTyp Δ l @ lzero ] ->
  exists T, [ G ; Δ ⊢[ lC ] T @ l ] /\ [ G ; cnil ⊢[ lM ] t ≅ boxT T : tyCTyp Δ l @ lzero ].
Proof.
  intros HG H. destruct (redM_eqtm _ _ _ _ _ _ (eqtm_refl _ _ _ _ _ _ H)) as (R & HR & Ht).
  pose proof (wf_tm_ty (i := lM) eq_refl H) as HT.
  destruct (LR_inv_CTyp HR (tyred_refl _ _ HT)) as [_ HM].
  destruct (ModRel_CTyp_inv HM HT HT) as (_ & _ & HRel).
  destruct (proj1 (HRel t t) Ht) as (w & w' & Hw & _ & _ & _ & Hn & _).
  destruct Hn as [T1 T1' (_ & HT1 & _) | ν ν' Hνν].
  - exists T1. split; [exact HT1 | exact (tmred_eq _ _ _ _ _ _ _ Hw)].
  - exfalso. exact (no_closed_neutral (gne_tm_typed_l Hνν) eq_refl HG (gne_tm_whne_l Hνν)).
Qed.

Theorem declM_closed_CTrm_canonicity {G t Δ A l} : ctx_only G ->
  [ G ; cnil ⊢[ lM ] t : tyCTrm Δ A l @ lzero ] ->
  exists c, [ G ; Δ ⊢[ lC ] c : A @ l ] /\ [ G ; cnil ⊢[ lM ] t ≅ boxt c : tyCTrm Δ A l @ lzero ].
Proof.
  intros HG H. destruct (redM_eqtm _ _ _ _ _ _ (eqtm_refl _ _ _ _ _ _ H)) as (R & HR & Ht).
  pose proof (wf_tm_ty (i := lM) eq_refl H) as HT.
  destruct (LR_inv_CTrm HR (tyred_refl _ _ HT)) as [_ HM].
  destruct (ModRel_CTrm_inv HM HT HT) as (_ & _ & _ & HRel).
  destruct (proj1 (HRel t t) Ht) as (w & w' & Hw & _ & _ & _ & Hn & _).
  destruct Hn as [c c' (_ & Hc & _) | ν ν' Hνν].
  - exists c. split; [exact Hc | exact (tmred_eq _ _ _ _ _ _ _ Hw)].
  - exfalso. exact (no_closed_neutral (gne_tm_typed_l Hνν) eq_refl HG (gne_tm_whne_l Hνν)).
Qed.

End DeclConsequences.
