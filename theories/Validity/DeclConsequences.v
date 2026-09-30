(** * Consequences for the declarative system

    At layer P ([DeclEq lD]) and at layer M ([DeclEq lM], relation
    [LR_M]), for arbitrary well-formed global contexts: reducibility
    comes from the fundamental theorems with global substitutions
    ([Reducible]).  Closed canonicity needs a global context without type
    or term bindings ([ctx_only]), whose global variables would be closed
    neutrals. *)
From DeLaM.Typing Require Export DeclInstance RecEq.
From DeLaM.Validity Require Export Reducible DeclConsequencesP.
From Coq Require Import Lia.

Section DeclConsequences.

Local Notation DEP := (DeclEq lD compt_D).
Local Notation DELP := (DeclEqLaws lD compt_D).
Local Notation DEM := (DeclEq lM compt_M).
Local Notation DELM := (DeclEqLaws lM compt_M).
Local Notation LRM := (LR_M DEP DEM).

Local Instance DeclEqM_inst : GenericEqM DEP DEM := DeclEqM.
Local Instance LRM_laws : VPLaws (@lr_vp LRM) := vpM_laws DEP DEM.

(** ** Reducibility *)

Lemma redM_eqty G Γ T T' l : [ G ; Γ ⊢[ lM ] T ≅ T' @ l ] -> lwf (gL G) l -> @LRty DEM LRM l G Γ T T'.
Proof. intros H Hl; exact (reducibleM_eqty DEP DEM H Hl). Qed.
Lemma redM_eqtm G Γ t t' T l : [ G ; Γ ⊢[ lM ] t ≅ t' : T @ l ] -> lwf (gL G) l ->
  @LRtm DEM LRM l G Γ T T t t'.
Proof. intros H Hl; exact (reducibleM_eqtm DEP DEM H Hl). Qed.

(** ** Levels at M: well formed, or ω (M4_DESIGN.md F6) *)

Lemma lvlM_ty {G Γ T l} : [ G ; Γ ⊢[ lM ] T @ l ] -> lwf (gL G) l \/ l = lomega.
Proof. intros H. destruct (proj1 (proj2 (proj2 judg_lvl)) _ _ _ _ _ H) as [? | [_ ?]]; auto. Qed.
Lemma lvlM_tm {G Γ t T l} : [ G ; Γ ⊢[ lM ] t : T @ l ] -> lwf (gL G) l \/ l = lomega.
Proof. intros H. destruct (proj1 (proj2 (proj2 (proj2 judg_lvl))) _ _ _ _ _ _ H) as [? | [_ ?]]; auto. Qed.
Lemma lvlM_eqty {G Γ T T' l} : [ G ; Γ ⊢[ lM ] T ≅ T' @ l ] -> lwf (gL G) l \/ l = lomega.
Proof. intros H. destruct (proj1 (proj2 (proj2 (proj2 (proj2 judg_lvl)))) _ _ _ _ _ _ H) as [? | [_ ?]]; auto. Qed.

(** [UΠ] types live at ω only. *)
Lemma upi_lvl {G i Γ n l A k} : [ G ; Γ ⊢[ i ] tyUPi n l A @ k ] -> k = lomega.
Proof.
  intros H; remember (tyUPi n l A) as X eqn:HX; revert HX.
  induction H; intros HX; try discriminate; auto.
  exfalso. match goal with IH : _ -> ?l' = lomega, E : lequiv _ _ ?l' |- _ =>
    rewrite (IH HX) in E; exact (lequiv_wf_r _ _ _ E) end.
Qed.

(** At ω, a type reduces to a [UΠ]. *)
Lemma omegaM_red_l {G Γ T T'} : [ G ; Γ ⊢[ lM ] T ≅ T' @ lomega ] ->
  exists n l A, [ G ; Γ ⊢[ lM ] T ⤳* tyUPi n l A @ lomega ].
Proof.
  intros H. destruct (reducibleM_eqty_ω DEP DEM H) as [R HR].
  destruct HR as [n l l' A A' iR _ _ HT _ _ _ _]. eauto.
Qed.
Lemma omegaM_red_r {G Γ T T'} : [ G ; Γ ⊢[ lM ] T ≅ T' @ lomega ] ->
  exists n l A, [ G ; Γ ⊢[ lM ] T' ⤳* tyUPi n l A @ lomega ].
Proof. intros H. exact (omegaM_red_l (eqty_sym _ _ _ _ _ _ H)). Qed.

Lemma omegaM_whnf_l {G Γ T T'} : [ G ; Γ ⊢[ lM ] T ≅ T' @ lomega ] -> whnf_ty T ->
  exists n l A, T = tyUPi n l A.
Proof.
  intros H Hw. destruct (omegaM_red_l H) as (n & l & A & HR).
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HR (tyred_refl _ _ (eqty_wf_l (i := lM) eq_refl H))
                (whnf_tyUPi _ _ _) Hw) as E. eauto.
Qed.
Lemma omegaM_whnf_r {G Γ T T'} : [ G ; Γ ⊢[ lM ] T ≅ T' @ lomega ] -> whnf_ty T' ->
  exists n l A, T' = tyUPi n l A.
Proof. intros H. exact (omegaM_whnf_l (eqty_sym _ _ _ _ _ _ H)). Qed.

(** A whnf type other than a [UΠ] is at a well-formed level. *)
Lemma lwfM_whnf_l {G Γ T T' l} : [ G ; Γ ⊢[ lM ] T ≅ T' @ l ] -> whnf_ty T ->
  (forall n l0 A, T <> tyUPi n l0 A) -> lwf (gL G) l.
Proof.
  intros H Hw Hn. destruct (lvlM_eqty H) as [? | ->]; [assumption|].
  destruct (omegaM_whnf_l H Hw) as (n & l0 & A & E). destruct (Hn _ _ _ E).
Qed.
Lemma lwfM_whnf_r {G Γ T T' l} : [ G ; Γ ⊢[ lM ] T ≅ T' @ l ] -> whnf_ty T' ->
  (forall n l0 A, T' <> tyUPi n l0 A) -> lwf (gL G) l.
Proof. intros H. exact (lwfM_whnf_l (eqty_sym _ _ _ _ _ _ H)). Qed.

Ltac not_upi := let n := fresh in let l := fresh in let A := fresh in let E := fresh in
  intros n l A E; discriminate E.

(** ** Layer M *)

Theorem declM_pi_inj {G Γ l l1 l2 l3 l4 A A' B B'} :
  [ G ; Γ ⊢[ lM ] tyPi l1 l2 A B ≅ tyPi l3 l4 A' B' @ l ] ->
  lequiv (gL G) l3 l1 /\ lequiv (gL G) l4 l2 /\
  [ G ; Γ ⊢[ lM ] A ≅ A' @ l1 ] /\ [ G ; Γ ,, A @ l1 ⊢[ lM ] B ≅ B' @ l2 ].
Proof.
  intros H. exact (pi_inj (E := DEM) (LP := LRM) redM_eqty H (lwfM_whnf_l H (whnf_tyPi _ _ _ _) ltac:(not_upi))).
Qed.

Theorem declM_sig_inj {G Γ l l1 l2 l3 l4 A A' B B'} :
  [ G ; Γ ⊢[ lM ] tySig l1 l2 A B ≅ tySig l3 l4 A' B' @ l ] ->
  lequiv (gL G) l3 l1 /\ lequiv (gL G) l4 l2 /\
  [ G ; Γ ⊢[ lM ] A ≅ A' @ l1 ] /\ [ G ; Γ ,, A @ l1 ⊢[ lM ] B ≅ B' @ l2 ].
Proof.
  intros H. exact (sig_inj (E := DEM) (LP := LRM) redM_eqty H (lwfM_whnf_l H (whnf_tySig _ _ _ _) ltac:(not_upi))).
Qed.

Theorem declM_id_inj {G Γ l l1 l2 A A' a a' b b'} :
  [ G ; Γ ⊢[ lM ] tyId l1 A a b ≅ tyId l2 A' a' b' @ l ] ->
  lequiv (gL G) l2 l1 /\ [ G ; Γ ⊢[ lM ] A ≅ A' @ l1 ] /\
  [ G ; Γ ⊢[ lM ] a ≅ a' : A @ l1 ] /\ [ G ; Γ ⊢[ lM ] b ≅ b' : A @ l1 ].
Proof.
  intros H. exact (id_inj (E := DEM) (LP := LRM) redM_eqty H (lwfM_whnf_l H (whnf_tyId _ _ _ _) ltac:(not_upi))).
Qed.

Theorem declM_seq_inj {G Γ l l1 l2 A A' a a' b b'} :
  [ G ; Γ ⊢[ lM ] tySEq l1 A a b ≅ tySEq l2 A' a' b' @ l ] ->
  lequiv (gL G) l2 l1 /\ [ G ; Γ ⊢[ lM ] A ≅ A' @ l1 ] /\
  [ G ; Γ ⊢[ lM ] a ≅ a' : A @ l1 ] /\ [ G ; Γ ⊢[ lM ] b ≅ b' : A @ l1 ].
Proof.
  intros H. exact (seq_inj (E := DEM) (LP := LRM) redM_eqty H (lwfM_whnf_l H (whnf_tySEq _ _ _ _) ltac:(not_upi))).
Qed.

Theorem declM_unit_inj {G Γ l l1 l2} :
  [ G ; Γ ⊢[ lM ] tyUnit l1 ≅ tyUnit l2 @ l ] -> lequiv (gL G) l2 l1.
Proof.
  intros H. exact (unit_inj (E := DEM) (LP := LRM) redM_eqty H (lwfM_whnf_l H (whnf_tyUnit _) ltac:(not_upi))).
Qed.

Theorem declM_U_inj {G Γ l l' k} : [ G ; Γ ⊢[ lM ] tyU l ≅ tyU l' @ k ] -> lequiv (gL G) l' l.
Proof. intros H. exact (U_inj (E := DEM) (LP := LRM) redM_eqty H (lwfM_whnf_l H (whnf_tyU _) ltac:(not_upi))). Qed.

(** Convertible whnf types have the same head (M6_DESIGN.md step 4); at ω
    both are [UΠ]s. *)
Theorem declM_head {G Γ W W' l} : [ G ; Γ ⊢[ lM ] W ≅ W' @ l ] -> whnf_ty W -> whnf_ty W' ->
  ty_head W = ty_head W'.
Proof.
  intros H Hw Hw'. destruct (lvlM_eqty H) as [Hl | ->].
  - exact (eqty_head (E := DEM) (LP := LRM) redM_eqty H Hl Hw Hw').
  - destruct (omegaM_whnf_l H Hw) as (? & ? & ? & ->). destruct (omegaM_whnf_r H Hw') as (? & ? & ? & ->).
    reflexivity.
Qed.

Theorem decl_head_c {G i Γ W W' l} : compt i -> [ G ; Γ ⊢[ i ] W ≅ W' @ l ] -> whnf_ty W -> whnf_ty W' ->
  ty_head W = ty_head W'.
Proof. intros [-> | ->]; [apply decl_head | apply declM_head]. Qed.

Theorem declM_whnf_normalization_tm {G Γ t T l} : [ G ; Γ ⊢[ lM ] t : T @ l ] ->
  exists w, reds t w /\ whnf w.
Proof.
  intros H. destruct (lvlM_tm H) as [Hl | ->].
  - destruct (whnf_normalization_tm (E := DEM) (LP := LRM) redM_eqtm H Hl) as (w & Hw & Hwh).
    exists w; split; [exact (tmred_red _ _ _ _ _ _ _ Hw) | exact Hwh].
  - (* at ω: the relation at ω reduces the term to a whnf *)
    destruct (reducibleM_eqtm_ω DEP DEM (eqtm_refl _ _ _ _ _ _ H)) as (R & HR & Ht).
    destruct HR as [n l l' A A' iR _ _ _ _ _ _ HRR].
    destruct (proj1 (HRR t t) Ht) as (w & w' & Hw & _ & Hwh & _).
    exists w; split; [exact (tmred_red _ _ _ _ _ _ _ Hw) | exact Hwh].
Qed.

Theorem declM_whnf_normalization_ty {G Γ T l} : [ G ; Γ ⊢[ lM ] T @ l ] ->
  exists W, reds_ty T W /\ whnf_ty W.
Proof.
  intros H. destruct (lvlM_ty H) as [Hl | ->].
  - destruct (whnf_normalization_ty (E := DEM) (LP := LRM) redM_eqty H Hl) as (W & HW & HWh).
    exists W; split; [exact (tyred_red _ _ _ _ _ _ HW) | exact HWh].
  - destruct (omegaM_red_l (eqty_refl _ _ _ _ _ H)) as (n & l & A & HW).
    exists (tyUPi n l A); split; [exact (tyred_red _ _ _ _ _ _ HW) | apply whnf_tyUPi].
Qed.

(** The typed forms (M6_DESIGN.md H6). *)
Theorem declM_whnf_tyred {G Γ T l} : [ G ; Γ ⊢[ lM ] T @ l ] ->
  exists W, [ G ; Γ ⊢[ lM ] T ⤳* W @ l ] /\ whnf_ty W.
Proof.
  intros H. destruct (lvlM_ty H) as [Hl | ->].
  - exact (whnf_normalization_ty (E := DEM) (LP := LRM) redM_eqty H Hl).
  - destruct (omegaM_red_l (eqty_refl _ _ _ _ _ H)) as (n & l & A & HW).
    exists (tyUPi n l A); split; [exact HW | apply whnf_tyUPi].
Qed.

Theorem declM_whnf_tmred {G Γ t T l} : [ G ; Γ ⊢[ lM ] t : T @ l ] ->
  exists w, [ G ; Γ ⊢[ lM ] t ⤳* w : T @ l ] /\ whnf w.
Proof.
  intros H. destruct (lvlM_tm H) as [Hl | ->].
  - exact (whnf_normalization_tm (E := DEM) (LP := LRM) redM_eqtm H Hl).
  - destruct (reducibleM_eqtm_ω DEP DEM (eqtm_refl _ _ _ _ _ _ H)) as (R & HR & Ht).
    destruct HR as [n l l' A A' iR _ _ HT _ _ _ HRR].
    destruct (proj1 (HRR t t) Ht) as (w & w' & Hw & _ & Hwh & _).
    exists w; split; [|exact Hwh].
    exact (tmred_conv (i := lM) _ _ _ _ _ eq_refl Hw (eqty_sym _ _ _ _ _ _ (tyred_eq _ _ _ _ _ _ HT))).
Qed.

Theorem declM_closed_nat_canonicity {G t} : ctx_only G -> [ G ; cnil ⊢[ lM ] t : tyNat @ lzero ] ->
  exists n, [ G ; cnil ⊢[ lM ] t ≅ numeral n : tyNat @ lzero ].
Proof. exact (closed_nat_canonicity (E := DEM) (LP := LRM) redM_eqtm). Qed.

Theorem declM_nat_not_pi {G Γ k l l' A B} : ~ [ G ; Γ ⊢[ lM ] tyNat ≅ tyPi l l' A B @ k ].
Proof. intros H. exact (nat_not_pi (E := DEM) (LP := LRM) redM_eqty (lwfM_whnf_l H whnf_tyNat ltac:(not_upi)) H). Qed.
Theorem declM_nat_not_U {G Γ k l} : ~ [ G ; Γ ⊢[ lM ] tyNat ≅ tyU l @ k ].
Proof. intros H. exact (nat_not_U (E := DEM) (LP := LRM) redM_eqty (lwfM_whnf_l H whnf_tyNat ltac:(not_upi)) H). Qed.
Theorem declM_U_not_pi {G Γ k l l1 l2 A B} : ~ [ G ; Γ ⊢[ lM ] tyU l ≅ tyPi l1 l2 A B @ k ].
Proof. intros H. exact (U_not_pi (E := DEM) (LP := LRM) redM_eqty (lwfM_whnf_l H (whnf_tyU _) ltac:(not_upi)) H). Qed.

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
  intros H. destruct (redM_eqty _ _ _ _ _ H (lwfM_whnf_l H (whnf_tyCTyp _ _) ltac:(not_upi))) as [R HR].
  pose proof (eqty_wf_l (i := lM) eq_refl H) as HT. pose proof (eqty_wf_r (i := lM) eq_refl H) as HT'.
  destruct (LR_inv_CTyp HR (tyred_refl _ _ HT)) as [_ HM].
  destruct (ModRel_CTyp_inv HM HT HT') as ((HDD & _) & Hl & _). split; assumption.
Qed.

Theorem declM_CTrm_inj {G Γ Δ Δ' A A' l l' k} : [ G ; Γ ⊢[ lM ] tyCTrm Δ A l ≅ tyCTrm Δ' A' l' @ k ] ->
  [ G ⊢[ lD ] Δ ≅ Δ' ] /\ [ G ; Δ ⊢[ lD ] A ≅ A' @ l ] /\ lequiv (gL G) l l'.
Proof.
  intros H. destruct (redM_eqty _ _ _ _ _ H (lwfM_whnf_l H (whnf_tyCTrm _ _ _) ltac:(not_upi))) as [R HR].
  pose proof (eqty_wf_l (i := lM) eq_refl H) as HT. pose proof (eqty_wf_r (i := lM) eq_refl H) as HT'.
  destruct (LR_inv_CTrm HR (tyred_refl _ _ HT)) as [_ HM].
  destruct (ModRel_CTrm_inv HM HT HT') as ((HDD & _) & (HAA & _) & Hl & _). exact (conj HDD (conj HAA Hl)).
Qed.

(** Closed terms of a contextual type are [box]es. *)
Theorem declM_closed_CTyp_canonicity {G t Δ l} : ctx_only G -> [ G ; cnil ⊢[ lM ] t : tyCTyp Δ l @ lzero ] ->
  exists T, [ G ; Δ ⊢[ lC ] T @ l ] /\ [ G ; cnil ⊢[ lM ] t ≅ boxT T : tyCTyp Δ l @ lzero ].
Proof.
  intros HG H. destruct (redM_eqtm _ _ _ _ _ _ (eqtm_refl _ _ _ _ _ _ H) I) as (R & HR & Ht).
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
  intros HG H. destruct (redM_eqtm _ _ _ _ _ _ (eqtm_refl _ _ _ _ _ _ H) I) as (R & HR & Ht).
  pose proof (wf_tm_ty (i := lM) eq_refl H) as HT.
  destruct (LR_inv_CTrm HR (tyred_refl _ _ HT)) as [_ HM].
  destruct (ModRel_CTrm_inv HM HT HT) as (_ & _ & _ & HRel).
  destruct (proj1 (HRel t t) Ht) as (w & w' & Hw & _ & _ & _ & Hn & _).
  destruct Hn as [c c' (_ & Hc & _) | ν ν' Hνν].
  - exists c. split; [exact Hc | exact (tmred_eq _ _ _ _ _ _ _ Hw)].
  - exfalso. exact (no_closed_neutral (gne_tm_typed_l Hνν) eq_refl HG (gne_tm_whne_l Hνν)).
Qed.

(** Equal boxes hold level-equivalent code (M6_DESIGN.md step 5): a box is
    its own whnf, and not a neutral. *)
Lemma reds_whnf_self {t w} : whnf t -> reds t w -> w = t.
Proof. intros Hw H; inversion H; subst; [reflexivity | exfalso; eapply whnf_no_red; eassumption]. Qed.

Theorem declM_boxT_leq {G Γ Δ l T T'} : [ G ; Γ ⊢[ lM ] boxT T ≅ boxT T' : tyCTyp Δ l @ lzero ] -> ty_leq T T'.
Proof.
  intros H. destruct (redM_eqtm _ _ _ _ _ _ H I) as (R & HR & Ht).
  pose proof (eqtm_wf_ty (i := lM) eq_refl H) as HT.
  destruct (LR_inv_CTyp HR (tyred_refl _ _ HT)) as [_ HM].
  destruct (ModRel_CTyp_inv HM HT HT) as (_ & _ & HRel).
  destruct (proj1 (HRel _ _) Ht) as (w & w' & Hw & Hw' & _ & _ & Hn & _).
  rewrite (reds_whnf_self (whnf_boxT _) (tmred_red _ _ _ _ _ _ _ Hw)) in Hn.
  rewrite (reds_whnf_self (whnf_boxT _) (tmred_red _ _ _ _ _ _ _ Hw')) in Hn.
  inversion Hn as [T1 T1' (E & _) | ν ν' Hνν]; subst; [exact E |].
  exfalso. pose proof (gne_tm_whne_l Hνν) as Hne. inversion Hne.
Qed.

Theorem declM_boxt_leq {G Γ Δ A l t t'} : [ G ; Γ ⊢[ lM ] boxt t ≅ boxt t' : tyCTrm Δ A l @ lzero ] -> tm_leq t t'.
Proof.
  intros H. destruct (redM_eqtm _ _ _ _ _ _ H I) as (R & HR & Ht).
  pose proof (eqtm_wf_ty (i := lM) eq_refl H) as HT.
  destruct (LR_inv_CTrm HR (tyred_refl _ _ HT)) as [_ HM].
  destruct (ModRel_CTrm_inv HM HT HT) as (_ & _ & _ & HRel).
  destruct (proj1 (HRel _ _) Ht) as (w & w' & Hw & Hw' & _ & _ & Hn & _).
  rewrite (reds_whnf_self (whnf_boxt _) (tmred_red _ _ _ _ _ _ _ Hw)) in Hn.
  rewrite (reds_whnf_self (whnf_boxt _) (tmred_red _ _ _ _ _ _ _ Hw')) in Hn.
  inversion Hn as [c c' (E & _) | ν ν' Hνν]; subst; [exact E |].
  exfalso. pose proof (gne_tm_whne_l Hνν) as Hne. inversion Hne.
Qed.

(** ** At ω: [UΠ] (M4_DESIGN.md F6) *)

(** The bodies of convertible [UΠ]s, at the level scope extended by the
    binder: the instance at the world that grows the scope by [n] levels,
    at those levels, escaped and moved back by the inverse rotation
    ([rotn], M3_DESIGN.md E14). *)
(** The top [n] levels of [n + L], in [uext] order. *)
Definition utop (n L : nat) : list lvl := map (fun k => lvar (L + k)) (rev (seq 0 n)).

Lemma utop_length n L : length (utop n L) = n.
Proof. unfold utop. now rewrite length_map, length_rev, length_seq. Qed.

Lemma utop_lwf n L : Forall (lwf (n + L)) (utop n L).
Proof.
  unfold utop. apply Forall_map, Forall_forall. intros k Hk.
  apply in_rev, in_seq in Hk. cbn [lwf]. lia.
Qed.

Lemma utop_rotn n L m : m < n + L -> lvsubst (uext (utop n L) lvar m) (pφ (rotn n L)) = lvar m.
Proof.
  intros Hm. unfold uext. rewrite utop_length. destruct (Nat.ltb_spec m n) as [Hlt | Hge].
  - unfold utop. rewrite (nth_indep _ _ (lvar (L + 0))) by (rewrite length_map, length_rev, length_seq; lia).
    rewrite (map_nth (fun k => lvar (L + k)) _ 0).
    rewrite rev_nth by (rewrite length_seq; lia). rewrite length_seq, seq_nth by lia.
    cbn [lvsubst]. unfold pφ, rotn. f_equal.
    destruct (Nat.ltb_spec (L + (0 + (n - S (n - S m)))) L); [lia|].
    destruct (Nat.ltb_spec (L + (0 + (n - S (n - S m)))) (n + L)); lia.
  - cbn [lvsubst]. unfold pφ, rotn. f_equal.
    destruct (Nat.ltb_spec (m - n) L); lia.
Qed.

Section Grow.
Context {L n : nat} {Ψ : list gdecl} {Γ : ctx} (HΓ : [ mkG L Ψ ; Γ ⊢[ lM ] ]).

Lemma grown_gok : gwk_ok gwk_id (mkG (n + L) Ψ) (mkG L Ψ).
Proof. split; [cbn; lia | constructor]. Qed.
Lemma grown_ctx : wf_ctx (mkG (n + L) Ψ) (@ge_layer DEM) Γ.
Proof.
  rewrite (@gm_layer_M DEP DEM _).
  exact (gwa_ctx (γ := gwk_id) grown_gok (wfg_grow L (n + L) Ψ ltac:(lia) (ctx_glob _ _ _ HΓ)) HΓ).
Qed.
Definition kw_grown : @kwk DEM (mkG L Ψ) Γ :=
  mkKwk (mkG (n + L) Ψ) Γ gwk_id wk_id grown_gok (wkwf_id _) grown_ctx.
End Grow.

Lemma declM_upi_body {G Γ n l A l' A'} : [ G ; Γ ⊢[ lM ] tyUPi n l A ≅ tyUPi n l' A' @ lomega ] ->
  [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] A ≅ A' @ l ].
Proof.
  intros H. destruct G as [L Ψ].
  pose proof (eqty_wf_l (i := lM) eq_refl H) as HU. pose proof (eqty_wf_r (i := lM) eq_refl H) as HU'.
  pose proof (proj1 (proj2 (proj2 ctx_extract)) _ _ _ _ _ HU) as HΓ.
  destruct (reducibleM_eqty_ω DEP DEM H) as [R HR].
  destruct HR as [m l0 l0' A0 A0' iR _ Hll HT HT' _ HI _].
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT (tyred_refl _ _ HU) (whnf_tyUPi _ _ _) (whnf_tyUPi _ _ _)) as E.
  injection E as -> -> ->.
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT' (tyred_refl _ _ HU') (whnf_tyUPi _ _ _) (whnf_tyUPi _ _ _)) as E.
  injection E as -> ->.
  pose proof (HI (kw_grown (n := n) HΓ) (utop n L) (utop n L) (utop_length n L)
                 (lequivs_refl _ _ (utop_lwf n L))) as X.
  destruct (escape_ty _ _ _ _ _ _ _ _ X) as (_ & _ & Y). apply geq_ty_sound in Y.
  unfold kty in Y; cbn [kw_grown kw_γ kw_r kw_G kw_Δ gwa wk_ren] in Y.
  pose proof (wf_ty_nf HU) as NA. pose proof (wf_ty_nf HU') as NA'.
  pose proof (wf_ty_dnf HU) as DA. pose proof (wf_ty_dnf HU') as DA'.
  pose proof (wf_ty_lwf HU) as WA. pose proof (wf_ty_lwf HU') as WA'.
  cbn in NA, NA', DA, DA', WA, WA'. destruct WA as [Wl WA]. destruct WA' as [_ WA'].
  rewrite !ren_id_ty in Y by assumption. rewrite (@gm_layer_M DEP DEM _) in Y.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 usubstitution)))) _ _ _ _ _ _ Y (n + L) (pφ (rotn n L))
                (uperm_usub_ok (uperm_rotn n L))) as Z.
  pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (EG : G_us (mkG (n + L) Ψ) (n + L) (pφ (rotn n L)) = gctx_uwk n (mkG L Ψ)).
  { unfold G_us, gctx_usubst, gctx_uwk; cbn. f_equal. exact (rotn_decls n L Ψ (wfg_lwf _ HG)). }
  assert (Eag : forall m, m < L -> pφ (rotn n L) m = pφ (ush n) m) by (intros; apply rotn_ush; assumption).
  assert (Eid : forall m, m < n + L -> lvsubst (uext (utop n L) lvar m) (pφ (rotn n L)) = lvar m)
    by exact (utop_rotn n L).
  assert (EΓ : ucsubst Γ (pφ (rotn n L)) = Γ⟨ush n⟩ᵤ)
    by (rewrite uren_us_ctx; exact (lwf_us_ext_ctx (wf_ctx_lwf HΓ) Eag)).
  assert (EA : forall B, dnfty B -> ty_lwf (n + L) B -> usubst_ty B[uext (utop n L) lvar]ᵤ (pφ (rotn n L)) = B).
  { intros B DB WB. change (B[uext (utop n L) lvar]ᵤ[pφ (rotn n L)]ᵤ = B).
    rewrite (usubst_usubst_ty _ _ _ _ (fun _ => eq_refl)), (lwf_us_ext_ty WB Eid).
    apply usubst_id_ty; [assumption | reflexivity]. }
  assert (El : lvsubst (lvsubst l (uext (utop n L) lvar)) (pφ (rotn n L)) = l).
  { rewrite (lvsubst_lvsubst _ _ _ _ (fun _ => eq_refl)), (lvsubst_ext_lwf _ _ _ _ Wl Eid).
    apply lvsubst_id; reflexivity. }
  rewrite EG, EΓ, (EA A DA WA), (EA A' DA' WA'), El in Z.
  exact Z.
Qed.

(** Injectivity of [UΠ] (08:38): the arities agree, the levels are
    equivalent, and the bodies are convertible in the extended scope. *)
Theorem declM_upi_inj {G Γ n l A n' l' A' k} : [ G ; Γ ⊢[ lM ] tyUPi n l A ≅ tyUPi n' l' A' @ k ] ->
  n' = n /\ lequiv (n + gL G) l l' /\ [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] A ≅ A' @ l ].
Proof.
  intros H. pose proof (upi_lvl (eqty_wf_l (i := lM) eq_refl H)) as ->.
  destruct (reducibleM_eqty_ω DEP DEM H) as [R HR].
  destruct HR as [m l0 l0' A0 A0' iR _ Hll HT HT' _ _ _].
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT (tyred_refl _ _ (eqty_wf_l (i := lM) eq_refl H))
                (whnf_tyUPi _ _ _) (whnf_tyUPi _ _ _)) as E. injection E as <- <- <-.
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT' (tyred_refl _ _ (eqty_wf_r (i := lM) eq_refl H))
                (whnf_tyUPi _ _ _) (whnf_tyUPi _ _ _)) as E. injection E as <- <- <-.
  refine (conj eq_refl (conj Hll _)). exact (declM_upi_body H).
Qed.

(** Discrimination of [UΠ] against the other type formers. *)
Lemma declM_upi_not {G Γ n l A X k} : whnf_ty X -> (forall n0 l0 A0, X <> tyUPi n0 l0 A0) ->
  ~ [ G ; Γ ⊢[ lM ] tyUPi n l A ≅ X @ k ].
Proof.
  intros Hw Hn H. pose proof (upi_lvl (eqty_wf_l (i := lM) eq_refl H)) as ->.
  destruct (omegaM_whnf_r H Hw) as (n0 & l0 & A0 & E). exact (Hn _ _ _ E).
Qed.

Theorem declM_upi_not_nat {G Γ n l A k} : ~ [ G ; Γ ⊢[ lM ] tyUPi n l A ≅ tyNat @ k ].
Proof. apply declM_upi_not; [exact whnf_tyNat | not_upi]. Qed.
Theorem declM_upi_not_U {G Γ n l A l' k} : ~ [ G ; Γ ⊢[ lM ] tyUPi n l A ≅ tyU l' @ k ].
Proof. apply declM_upi_not; [apply whnf_tyU | not_upi]. Qed.
Theorem declM_upi_not_pi {G Γ n l A l1 l2 B C k} : ~ [ G ; Γ ⊢[ lM ] tyUPi n l A ≅ tyPi l1 l2 B C @ k ].
Proof. apply declM_upi_not; [apply whnf_tyPi | not_upi]. Qed.
Theorem declM_upi_not_CTyp {G Γ n l A Δ l' k} : ~ [ G ; Γ ⊢[ lM ] tyUPi n l A ≅ tyCTyp Δ l' @ k ].
Proof. apply declM_upi_not; [apply whnf_tyCTyp | not_upi]. Qed.
Theorem declM_upi_not_CTrm {G Γ n l A Δ B l' k} : ~ [ G ; Γ ⊢[ lM ] tyUPi n l A ≅ tyCTrm Δ B l' @ k ].
Proof. apply declM_upi_not; [apply whnf_tyCTrm | not_upi]. Qed.

Theorem declM_upi_not_cpi {G Γ n l A l' B k} : ~ [ G ; Γ ⊢[ lM ] tyUPi n l A ≅ tyCPi l' B @ k ].
Proof. apply declM_upi_not; [apply whnf_tyCPi | not_upi]. Qed.
Theorem declM_upi_not_tpi {G Γ n l A Δ l1 l2 B k} : ~ [ G ; Γ ⊢[ lM ] tyUPi n l A ≅ tyTPi Δ l1 l2 B @ k ].
Proof. apply declM_upi_not; [apply whnf_tyTPi | not_upi]. Qed.

(** ** The meta-functions (M5_DESIGN.md G6)

    Injectivity: the bodies of convertible [CΠ]s (or [TΠ]s) are
    convertible under the binder, from the instance at the world one
    binding up, at the bound variable; the η identities take the
    instance's bodies back to the bodies themselves. *)

Theorem declM_cpi_inj {G Γ l l' T T' k} : [ G ; Γ ⊢[ lM ] tyCPi l T ≅ tyCPi l' T' @ k ] ->
  lequiv (gL G) l' l /\ [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T ≅ T' @ l ].
Proof.
  intros H. destruct (redM_eqty _ _ _ _ _ H (lwfM_whnf_l H (whnf_tyCPi _ _) ltac:(not_upi))) as [R HR].
  pose proof (eqty_wf_l (i := lM) eq_refl H) as HT. pose proof (eqty_wf_r (i := lM) eq_refl H) as HT'.
  destruct (LR_inv_cpi HR (tyred_refl _ _ HT)) as (m2 & U1' & instR & _ & _ & Hm2 & _ & HTr & HU & HU' & _ & HI & _).
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HTr (tyred_refl _ _ HT') (whnf_tyCPi _ _) (whnf_tyCPi _ _)) as E.
  injection E as -> ->.
  split; [exact Hm2 |].
  pose proof (proj1 (proj2 (proj2 ctx_extract)) _ _ _ _ _ HT) as HΓ.
  assert (HΓg : [ G ; Γ ⊢g ]) by (rewrite (@gm_layer_M DEP DEM _); exact HΓ).
  assert (HG1 : [ ⊢ gext G gdCtx ]) by (apply wfg_ctx, (ctx_glob _ _ _ HΓ)).
  set (ρS := kw_gstep gdCtx HG1 HΓg).
  assert (hS : vp_ctx (@lr_vp LRM) (kw_G ρS) (cvar 0) (cvar 0))
    by exact (conj (eqc_var _ _ 0 HG1 eq_refl) (conj CtxRelG_var CtxRelG_var)).
  destruct (escape_ty _ _ _ _ _ _ _ _ (HI ρS _ _ hS)) as (_ & _ & Y). apply geq_ty_sound in Y.
  rewrite (@gm_layer_M DEP DEM _) in HU, HU', Y.
  unfold ρS in Y. rewrite !kbody_gstep, (eta_c_ty HU), (eta_c_ty HU') in Y.
  cbn [kw_gstep kw_G kw_Δ gwa] in Y. change (Γ⟪gwk_step gwk_id⟫) with Γ⟪S⟫ in Y. exact Y.
Qed.

Theorem declM_tpi_inj {G Γ Δ Δ' l1 l2 l3 l4 T T' k} :
  [ G ; Γ ⊢[ lM ] tyTPi Δ l1 l2 T ≅ tyTPi Δ' l3 l4 T' @ k ] ->
  [ G ⊢[ lD ] Δ ≅ Δ' ] /\ lequiv (gL G) l3 l1 /\ lequiv (gL G) l4 l2 /\
  [ gext G (gdTy Δ lD l1) ; Γ⟪S⟫ ⊢[ lM ] T ≅ T' @ l2 ].
Proof.
  intros H. destruct (redM_eqty _ _ _ _ _ H (lwfM_whnf_l H (whnf_tyTPi _ _ _ _) ltac:(not_upi))) as [R HR].
  pose proof (eqty_wf_l (i := lM) eq_refl H) as HT. pose proof (eqty_wf_r (i := lM) eq_refl H) as HT'.
  destruct (LR_inv_tpi HR (tyred_refl _ _ HT))
    as (Θ' & m3 & m4 & U1' & instR & _ & _ & H31 & H42 & Wl1 & _ & HTr & hΘ & HU & HU' & _ & HI & _).
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HTr (tyred_refl _ _ HT') (whnf_tyTPi _ _ _ _) (whnf_tyTPi _ _ _ _))
    as E.
  injection E as -> -> -> ->.
  destruct hΘ as (HΔΔ & XP & XM).
  refine (conj HΔΔ (conj H31 (conj H42 _))).
  pose proof (proj1 (proj2 (proj2 ctx_extract)) _ _ _ _ _ HT) as HΓ.
  assert (HΓg : [ G ; Γ ⊢g ]) by (rewrite (@gm_layer_M DEP DEM _); exact HΓ).
  pose proof (eqctx_wf_l (i := lD) eq_refl HΔΔ) as HΔ.
  assert (HG1 : [ ⊢ gext G (gdTy Δ lD l1) ])
    by (apply wfg_ty; [exact (ctx_glob _ _ _ HΓ) | exact HΔ | right; reflexivity | exact Wl1]).
  set (ρS := kw_gstep (gdTy Δ lD l1) HG1 HΓg).
  pose proof (vp_ty_gvar0_at DEP DEM HΔ HG1 (CtxRelG_trans XP (CtxRelG_sym XP))
                (CtxRelG_trans XM (CtxRelG_sym XM))) as hS.
  destruct (escape_ty _ _ _ _ _ _ _ _ (HI ρS _ _ hS)) as (_ & _ & Y). apply geq_ty_sound in Y.
  rewrite (@gm_layer_M DEP DEM _) in HU, HU', Y.
  unfold ρS in Y. rewrite !kbody_gstep, (eta_t_ty HU), (eta_t_ty HU') in Y.
  cbn [kw_gstep kw_G kw_Δ gwa] in Y. change (Γ⟪gwk_step gwk_id⟫) with Γ⟪S⟫ in Y. exact Y.
Qed.

(** Discrimination: the other side of a convertible [CΠ] (or [TΠ])
    reduces to one. *)
Lemma declM_cpi_not {G Γ l T X k} : whnf_ty X -> (forall m U, X <> tyCPi m U) ->
  ~ [ G ; Γ ⊢[ lM ] tyCPi l T ≅ X @ k ].
Proof.
  intros Hw Hn H. destruct (redM_eqty _ _ _ _ _ H (lwfM_whnf_l H (whnf_tyCPi _ _) ltac:(not_upi))) as [R HR].
  destruct (LR_inv_cpi HR (tyred_refl _ _ (eqty_wf_l (i := lM) eq_refl H)))
    as (m2 & U1' & _ & _ & _ & _ & _ & HTr & _).
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HTr (tyred_refl _ _ (eqty_wf_r (i := lM) eq_refl H))
                (whnf_tyCPi _ _) Hw) as E.
  exact (Hn _ _ (eq_sym E)).
Qed.

Lemma declM_tpi_not {G Γ Δ l l' T X k} : whnf_ty X -> (forall Θ m m' U, X <> tyTPi Θ m m' U) ->
  ~ [ G ; Γ ⊢[ lM ] tyTPi Δ l l' T ≅ X @ k ].
Proof.
  intros Hw Hn H. destruct (redM_eqty _ _ _ _ _ H (lwfM_whnf_l H (whnf_tyTPi _ _ _ _) ltac:(not_upi))) as [R HR].
  destruct (LR_inv_tpi HR (tyred_refl _ _ (eqty_wf_l (i := lM) eq_refl H)))
    as (Θ' & m3 & m4 & U1' & _ & _ & _ & _ & _ & _ & _ & HTr & _).
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HTr (tyred_refl _ _ (eqty_wf_r (i := lM) eq_refl H))
                (whnf_tyTPi _ _ _ _) Hw) as E.
  exact (Hn _ _ _ _ (eq_sym E)).
Qed.

Ltac not_cpi := let m := fresh in let U := fresh in let E := fresh in intros m U E; discriminate E.
Ltac not_tpi := let a := fresh in let b := fresh in let c := fresh in let d := fresh in let E := fresh in
  intros a b c d E; discriminate E.

Theorem declM_cpi_not_nat {G Γ l T k} : ~ [ G ; Γ ⊢[ lM ] tyCPi l T ≅ tyNat @ k ].
Proof. apply declM_cpi_not; [exact whnf_tyNat | not_cpi]. Qed.
Theorem declM_cpi_not_U {G Γ l T l' k} : ~ [ G ; Γ ⊢[ lM ] tyCPi l T ≅ tyU l' @ k ].
Proof. apply declM_cpi_not; [apply whnf_tyU | not_cpi]. Qed.
Theorem declM_cpi_not_pi {G Γ l T l1 l2 A B k} : ~ [ G ; Γ ⊢[ lM ] tyCPi l T ≅ tyPi l1 l2 A B @ k ].
Proof. apply declM_cpi_not; [apply whnf_tyPi | not_cpi]. Qed.
Theorem declM_cpi_not_CTyp {G Γ l T Δ l' k} : ~ [ G ; Γ ⊢[ lM ] tyCPi l T ≅ tyCTyp Δ l' @ k ].
Proof. apply declM_cpi_not; [apply whnf_tyCTyp | not_cpi]. Qed.
Theorem declM_cpi_not_CTrm {G Γ l T Δ A l' k} : ~ [ G ; Γ ⊢[ lM ] tyCPi l T ≅ tyCTrm Δ A l' @ k ].
Proof. apply declM_cpi_not; [apply whnf_tyCTrm | not_cpi]. Qed.
Theorem declM_cpi_not_tpi {G Γ l T Δ l1 l2 B k} : ~ [ G ; Γ ⊢[ lM ] tyCPi l T ≅ tyTPi Δ l1 l2 B @ k ].
Proof. apply declM_cpi_not; [apply whnf_tyTPi | not_cpi]. Qed.

Theorem declM_tpi_not_nat {G Γ Δ l l' T k} : ~ [ G ; Γ ⊢[ lM ] tyTPi Δ l l' T ≅ tyNat @ k ].
Proof. apply declM_tpi_not; [exact whnf_tyNat | not_tpi]. Qed.
Theorem declM_tpi_not_U {G Γ Δ l l' T l0 k} : ~ [ G ; Γ ⊢[ lM ] tyTPi Δ l l' T ≅ tyU l0 @ k ].
Proof. apply declM_tpi_not; [apply whnf_tyU | not_tpi]. Qed.
Theorem declM_tpi_not_pi {G Γ Δ l l' T l1 l2 A B k} : ~ [ G ; Γ ⊢[ lM ] tyTPi Δ l l' T ≅ tyPi l1 l2 A B @ k ].
Proof. apply declM_tpi_not; [apply whnf_tyPi | not_tpi]. Qed.
Theorem declM_tpi_not_CTyp {G Γ Δ l l' T Θ l0 k} : ~ [ G ; Γ ⊢[ lM ] tyTPi Δ l l' T ≅ tyCTyp Θ l0 @ k ].
Proof. apply declM_tpi_not; [apply whnf_tyCTyp | not_tpi]. Qed.
Theorem declM_tpi_not_CTrm {G Γ Δ l l' T Θ A l0 k} : ~ [ G ; Γ ⊢[ lM ] tyTPi Δ l l' T ≅ tyCTrm Θ A l0 @ k ].
Proof. apply declM_tpi_not; [apply whnf_tyCTrm | not_tpi]. Qed.

(** ** Global functionality (M6_DESIGN.md H8)

    Instances at equal objects are equal. The typing rules of the
    applications take these equations as premises (M5_DESIGN.md G2); they
    are consequences of the fundamental theorem. *)

(** Escape at the identity substitutions, from validity at M. *)
Lemma escM_VTyS {G Γ T T' l} : [ G ; Γ ⊢[ lM ] ] -> lwf (gL G) l ->
  [ G ; Γ ⊢[ lM ] T @ l ] -> [ G ; Γ ⊢[ lM ] T' @ l ] ->
  @VTyS DEP DEM DEM LRM G Γ T T' l -> [ G ; Γ ⊢[ lM ] T ≅ T' @ l ].
Proof.
  intros HΓ Hl HT HT' VT.
  destruct (proj1 (proj2 (fundamentalM DEP DEM)) _ _ _ HΓ eq_refl) as (_ & VΓ).
  destruct (VTyS_red DEP DEM (E := DEM) (LP := LRM) HT HT' VΓ VT) as [R HR].
  exact (proj2 (proj2 (escape_ty _ _ _ _ _ _ _ _ HR))).
Qed.

Theorem declM_inst_c_eq {G Γ T l Δ Δ'} : [ G ; Γ ⊢[ lM ] ] -> lwf (gL G) l ->
  [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T @ l ] -> [ G ⊢[ lD ] Δ ≅ Δ' ] ->
  [ G ; Γ ⊢[ lM ] T⦃gsingle (GCtx Δ)⦄ ≅ T⦃gsingle (GCtx Δ')⦄ @ l ].
Proof.
  intros HΓ Hl HT HΔ.
  destruct (proj1 (proj1 (proj2 (proj2 (fundamentalM DEP DEM))) _ _ _ _ _ HT eq_refl) Hl) as (_ & VT).
  destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (fundamentalS DEP DEM)))))) _ _ _ _ HΔ eq_refl)
    as [VEP VEM].
  pose proof (eqctx_wf_l (i := lD) eq_refl HΔ) as HD. pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HD'.
  pose proof (VTyS_inst_c2 DEP DEM HD HD' VEP VEM VT) as VI.
  rewrite gcren_S_gsingle in VI by exact (wf_ctx_dnf HΓ).
  exact (escM_VTyS HΓ Hl (inst_c_ty HΓ HD HT) (inst_c_ty HΓ HD' HT) VI).
Qed.

Theorem declM_inst_t_eq {G Γ Δ l T l' A A'} : [ G ; Γ ⊢[ lM ] ] -> lwf (gL G) l' ->
  [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] T @ l' ] -> [ G ; Δ ⊢[ lD ] A ≅ A' @ l ] ->
  [ G ; Γ ⊢[ lM ] T⦃gsingle (GTy A)⦄ ≅ T⦃gsingle (GTy A')⦄ @ l' ].
Proof.
  intros HΓ Hl HT HA.
  destruct (proj1 (proj1 (proj2 (proj2 (fundamentalM DEP DEM))) _ _ _ _ _ HT eq_refl) Hl) as (_ & VT).
  destruct (proj1 (proj2 (proj2 (proj2 (proj2 (fundamentalS DEP DEM))))) _ _ _ _ _ _ HA eq_refl)
    as ((_ & VΔP & VΔM) & VAP & VAM).
  pose proof (eqty_wf_l (i := lD) eq_refl HA) as HAl. pose proof (eqty_wf_r (i := lD) eq_refl HA) as HAr.
  pose proof (proj1 (proj2 (proj2 ctx_extract)) _ _ _ _ _ HAl) as HD.
  pose proof (VTyS_inst_t2 DEP DEM HD HAl HAr VΔP VΔM VAP VAM VT) as VI.
  rewrite gcren_S_gsingle in VI by exact (wf_ctx_dnf HΓ).
  exact (escM_VTyS HΓ Hl (inst_t_ty HΓ HAl HT) (inst_t_ty HΓ HAr HT) VI).
Qed.

(** The motive instance of [elim_Typ]: the recursors' typing rules take its
    equation as a premise (M3_DESIGN.md E10). It follows from its
    ingredients: the motives' equation, the levels' equivalence (by [≡ₗ]),
    the contexts' equivalence (global functionality, in the motive's scope
    [Γ, x_T : CTyp g ℓ]) and the scrutinees' equation. *)
Theorem declM_motT_eq {G Γ MT MT' l1 l l' Δ Δ' t t'} :
  [ recGT G ; recΓT Γ ⊢[ lM ] MT ≅ MT' @ lvren l1 (ush 1) ] ->
  lwf (gL G) l1 -> lequiv (gL G) l l' -> [ G ⊢[ lD ] Δ ≅ Δ' ] ->
  [ G ; Γ ⊢[ lM ] t ≅ t' : tyCTyp Δ l @ lzero ] ->
  [ G ; Γ ⊢[ lM ] motT (wrapMT MT) l Δ t ≅ motT (wrapMT MT') l' Δ' t' @ l1 ].
Proof.
  destruct G as [L Ψ]. intros HMM Hl1 Hll HΔ Htt. cbn [gL] in *.
  pose proof (eqty_wf_r (i := lM) eq_refl HMM) as HMT'.
  pose proof (eqtm_wf_l (i := lM) eq_refl Htt) as Ht.
  pose proof (eqtm_wf_r (i := lM) eq_refl Htt) as Ht'.
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Ht) as HΓ.
  pose proof (ctx_glob _ _ _ HΓ) as Hg.
  pose proof (eqctx_wf_l (i := lD) eq_refl HΔ) as HD. pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HD'.
  pose proof (lequiv_wf_l _ _ _ Hll) as Hl. pose proof (lequiv_wf_r _ _ _ Hll) as Hl'.
  assert (EC : [ mkG L Ψ ; Γ ⊢[ lM ] tyCTyp Δ l ≅ tyCTyp Δ' l' @ lzero ]) by (apply eqty_CTyp; auto).
  assert (EC1 : [ mkG L Ψ ; Γ ⊢[ lM ] tyCTyp Δ l ≅ tyCTyp Δ l' @ lzero ])
    by (apply eqty_CTyp; auto using eqc_refl).
  assert (EC2 : [ mkG L Ψ ; Γ ⊢[ lM ] tyCTyp Δ' l' ≅ tyCTyp Δ l' @ lzero ])
    by (apply eqty_CTyp; auto using eqctx_sym_D, lequiv_refl).
  pose proof (wf_conv _ _ _ _ _ _ _ Ht (eqty_sym _ _ _ _ _ _ EC1)) as Ht1.
  pose proof (wf_conv _ _ _ _ _ _ _ Ht (eqty_sym _ _ _ _ _ _ EC)) as Ht2.
  pose proof (wf_conv _ _ _ _ _ _ _ Ht' (eqty_sym _ _ _ _ _ _ EC)) as Ht2'.
  pose proof (eqtm_conv _ _ _ _ _ _ _ _ Htt (eqty_sym _ _ _ _ _ _ EC)) as Htt2.
  (* the motive at the target's level, in the scope of the context variable *)
  pose proof (proj1 (proj2 (proj2 usubstitution)) _ _ _ _ _ HMT' L (usingle l') (usub_ok_single L l' Hl'))
    as X1.
  rewrite (G_us_recGT _ _ _ Hg), lvsubst_ush1_single in X1.
  set (Y := usubst_ty MT' (usingle l')) in X1.
  assert (HΓx : forall D, [ mkG L Ψ ; D ⊢[ lD ] ] ->
            [ mkG L Ψ ; Γ ,, tyCTyp D l' @ lzero ⊢[ lM ] Y⦃gsingle (GCtx D)⦄ @ l1 ]).
  { intros D HD0.
    assert (Hσ : [ mkG L Ψ ⊢ gsingle (GCtx D) : mkG L (gdCtx :: Ψ) ]).
    { apply (gsub_wf_single (mkG L Ψ) gdCtx); [exact Hg | exact (wf_ctx_dnf HD0) | exact HD0]. }
    pose proof (proj1 (proj2 (proj2 gsubstitution)) _ _ _ _ _ X1 Ψ _ Hσ) as X2.
    unfold gwk_to in X2; cbn [gL] in X2. change (gsubst ?x ?s) with (gcsubst x s) in X2 at 1.
    rewrite (recΓT_inst _ _ _ (wf_ctx_dnf HΓ)) in X2. exact X2. }
  (* 1. the motives *)
  pose proof (motT_eq_inst _ _ _ _ _ _ _ _ HMM Hl HD Ht) as E1.
  (* 2. the levels *)
  assert (E2 : [ mkG L Ψ ; Γ ⊢[ lM ] motT (wrapMT MT') l Δ t ≅ motT (wrapMT MT') l' Δ t @ l1 ]).
  { apply eqty_leq.
    - exact (motT_wf _ _ _ _ _ _ _ HMT' Hl HD Ht).
    - exact (motT_wf _ _ _ _ _ _ _ HMT' Hl' HD Ht1).
    - apply motT_leq; auto with leq. exact (lequiv_leqv _ _ _ Hll). }
  (* 3. the contexts: global functionality in the scope [Γ, x_T : CTyp g ℓ'] *)
  assert (E3 : [ mkG L Ψ ; Γ ⊢[ lM ] motT (wrapMT MT') l' Δ t ≅ motT (wrapMT MT') l' Δ' t @ l1 ]).
  { destruct (proj1 (proj1 (proj2 (proj2 (fundamentalM DEP DEM))) _ _ _ _ _ X1 eq_refl) Hl1) as (_ & VT).
    destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (fundamentalS DEP DEM)))))) _ _ _ _ HΔ eq_refl)
      as [VEP VEM].
    pose proof (VTyS_inst_c2 DEP DEM HD HD' VEP VEM VT) as VI.
    change (gsubst ?x ?s) with (gcsubst x s) in VI at 1.
    rewrite (recΓT_inst _ _ _ (wf_ctx_dnf HΓ)) in VI.
    assert (HΓ1 : [ mkG L Ψ ; Γ ,, tyCTyp Δ l' @ lzero ⊢[ lM ] ])
      by (apply wfc_ext; [exact HΓ | apply wft_CTyp; auto | exact I]).
    pose proof (escM_VTyS HΓ1 Hl1 (HΓx _ HD)
                  (stab_ty (i := lM) eq_refl EC2 (lequiv_refl L lzero I) HΓ1 (HΓx _ HD')) VI) as E.
    exact (eqty_single (i := lM) eq_refl E Ht1). }
  (* 4. the scrutinees *)
  assert (E4 : [ mkG L Ψ ; Γ ⊢[ lM ] motT (wrapMT MT') l' Δ' t ≅ motT (wrapMT MT') l' Δ' t' @ l1 ]).
  { exact (wf_ty_func (i := lM) eq_refl (HΓx _ HD') (lsub_eq_single (i := lM) eq_refl Ht2 Ht2' Htt2)). }
  eapply eqty_trans; [exact E1|]. eapply eqty_trans; [exact E2|]. eapply eqty_trans; [exact E3 | exact E4].
Qed.

(** The motive instance of [elim_Trm], likewise; its global step sends both
    the context and the type variable (two-object instance validity). *)
Theorem declM_mott_eq {G Γ Mt Mt' l2 l l' Δ Δ' T T' t t'} :
  [ recGt G ; recΓt Γ ⊢[ lM ] Mt ≅ Mt' @ lvren l2 (ush 1) ] ->
  lwf (gL G) l2 -> lequiv (gL G) l l' -> [ G ⊢[ lD ] Δ ≅ Δ' ] -> [ G ; Δ ⊢[ lD ] T ≅ T' @ l ] ->
  [ G ; Γ ⊢[ lM ] t ≅ t' : tyCTrm Δ T l @ lzero ] ->
  [ G ; Γ ⊢[ lM ] mott (wrapMt Mt) l Δ T t ≅ mott (wrapMt Mt') l' Δ' T' t' @ l2 ].
Proof.
  destruct G as [L Ψ]. intros HMM Hl2 Hll HΔ HTT Htt. cbn [gL] in *.
  pose proof (eqty_wf_r (i := lM) eq_refl HMM) as HMt'.
  pose proof (eqtm_wf_l (i := lM) eq_refl Htt) as Ht.
  pose proof (eqtm_wf_r (i := lM) eq_refl Htt) as Ht'.
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Ht) as HΓ.
  pose proof (ctx_glob _ _ _ HΓ) as Hg.
  pose proof (eqctx_wf_l (i := lD) eq_refl HΔ) as HD. pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HD'.
  pose proof (lequiv_wf_l _ _ _ Hll) as Hl. pose proof (lequiv_wf_r _ _ _ Hll) as Hl'.
  pose proof (eqty_wf_l (i := lD) eq_refl HTT) as HT. pose proof (eqty_wf_r (i := lD) eq_refl HTT) as HT'.
  pose proof (wft_lconv _ _ _ _ _ _ HT (lequiv_sym _ _ _ Hll)) as HT1.
  pose proof (wft_lconv _ _ _ _ _ _ HT' (lequiv_sym _ _ _ Hll)) as HT1'.
  pose proof (decl_ty_ctxconv_D HΔ HT' Hll) as HT2'.
  pose proof (eqty_lconv _ _ _ _ _ _ _ HTT (lequiv_sym _ _ _ Hll)) as HTT1.
  assert (EC : [ mkG L Ψ ; Γ ⊢[ lM ] tyCTrm Δ T l ≅ tyCTrm Δ' T' l' @ lzero ]) by (apply eqty_CTrm; auto).
  assert (EC1 : [ mkG L Ψ ; Γ ⊢[ lM ] tyCTrm Δ T l ≅ tyCTrm Δ T l' @ lzero ])
    by (apply eqty_CTrm; auto using eqc_refl, eqty_refl).
  pose proof (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EC) EC1) as EC2.
  pose proof (wf_conv _ _ _ _ _ _ _ Ht (eqty_sym _ _ _ _ _ _ EC1)) as Ht1.
  pose proof (wf_conv _ _ _ _ _ _ _ Ht (eqty_sym _ _ _ _ _ _ EC)) as Ht2.
  pose proof (wf_conv _ _ _ _ _ _ _ Ht' (eqty_sym _ _ _ _ _ _ EC)) as Ht2'.
  pose proof (eqtm_conv _ _ _ _ _ _ _ _ Htt (eqty_sym _ _ _ _ _ _ EC)) as Htt2.
  (* the motive at the target's level, in the scope of the context and type variables *)
  pose proof (proj1 (proj2 (proj2 usubstitution)) _ _ _ _ _ HMt' L (usingle l') (usub_ok_single L l' Hl'))
    as X1.
  rewrite (G_us_recGt _ _ _ Hg), lvsubst_ush1_single in X1.
  set (Y := usubst_ty Mt' (usingle l')) in X1.
  assert (Hdn : forall D, [ mkG L Ψ ; D ⊢[ lD ] ] -> gdnf (gsingle (GCtx D))).
  { intros D HD0 [|n]; cbn; [exact (wf_ctx_dnf HD0) | exact I]. }
  assert (HΓx : forall D A, [ mkG L Ψ ; D ⊢[ lD ] ] -> [ mkG L Ψ ; D ⊢[ lD ] A @ l' ] ->
            [ mkG L Ψ ; Γ ,, tyCTrm D A l' @ lzero ⊢[ lM ] Y⦃gup (gsingle (GCtx D))⦄⦃gsingle (GTy A)⦄ @ l2 ]).
  { intros D A HD0 HA0.
    assert (Hσ0 : [ mkG L Ψ ⊢ gsingle (GCtx D) : mkG L (gdCtx :: Ψ) ]).
    { apply (gsub_wf_single (mkG L Ψ) gdCtx); [exact Hg | exact (wf_ctx_dnf HD0) | exact HD0]. }
    assert (Hg1 : [ ⊢ mkG L (gdTy D lD l' :: Ψ) ]) by (apply wfg_ty; auto).
    assert (Hσ1 : [ mkG L (gdTy D lD l' :: Ψ) ⊢ gup (gsingle (GCtx D))
                    : mkG L (gdTy (cvar 0) lD l' :: gdCtx :: Ψ) ])
      by exact (gsub_wf_up _ _ _ (gdTy (cvar 0) lD l') Hσ0 Hg1).
    assert (Hσ2 : [ mkG L Ψ ⊢ gsingle (GTy A) : mkG L (gdTy D lD l' :: Ψ) ]).
    { apply (gsub_wf_single (mkG L Ψ) (gdTy D lD l')); [exact Hg | exact (wf_ty_dnf HA0) |].
      rewrite gdecl_gsubst_ren_single by exact (wf_ctx_dnf HD0). exact HA0. }
    pose proof (proj1 (proj2 (proj2 gsubstitution)) _ _ _ _ _ X1 _ _ Hσ1) as X2.
    unfold gwk_to in X2; cbn [gL] in X2.
    pose proof (proj1 (proj2 (proj2 gsubstitution)) _ _ _ _ _ X2 Ψ _ Hσ2) as X3.
    unfold gwk_to in X3; cbn [gL] in X3.
    change (gsubst (gsubst ?x ?s1) ?s2) with (gcsubst (gcsubst x s1) s2) in X3 at 1.
    rewrite (recΓt_inst _ _ _ _ (wf_ctx_dnf HΓ) (wf_ctx_dnf HD0) (wf_ty_nf HA0)) in X3. exact X3. }
  (* 1. the motives *)
  pose proof (mott_eq_inst _ _ _ _ _ _ _ _ _ HMM Hl HD HT Ht) as E1.
  (* 2. the levels *)
  assert (E2 : [ mkG L Ψ ; Γ ⊢[ lM ] mott (wrapMt Mt') l Δ T t ≅ mott (wrapMt Mt') l' Δ T t @ l2 ]).
  { apply eqty_leq.
    - exact (mott_wf _ _ _ _ _ _ _ _ HMt' Hl HD HT Ht).
    - exact (mott_wf _ _ _ _ _ _ _ _ HMt' Hl' HD HT1 Ht1).
    - apply mott_leq; auto with leq. exact (lequiv_leqv _ _ _ Hll). }
  (* 3. the context and type objects: two-object global functionality *)
  assert (E3 : [ mkG L Ψ ; Γ ⊢[ lM ] mott (wrapMt Mt') l' Δ T t ≅ mott (wrapMt Mt') l' Δ' T' t @ l2 ]).
  { destruct (proj1 (proj1 (proj2 (proj2 (fundamentalM DEP DEM))) _ _ _ _ _ X1 eq_refl) Hl2) as (_ & VT).
    destruct (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (fundamentalS DEP DEM)))))) _ _ _ _ HΔ eq_refl)
      as [VEP VEM].
    destruct (proj1 (proj2 (proj2 (proj2 (proj2 (fundamentalS DEP DEM))))) _ _ _ _ _ _ HTT1 eq_refl)
      as ((_ & VΔP & _) & VAP & VAM).
    pose proof (VTyS_inst_ct2 DEP DEM HD HD' VΔP VEP VEM HT1 HT1' VAP VAM VT) as VI.
    rewrite <- (gup_single_ctx _ _ _ (Hdn _ HD)), <- (gup_single_ty _ _ _ (Hdn _ HD)),
      <- (gup_single_ty _ _ _ (Hdn _ HD')) in VI.
    change (gsubst (gsubst ?x ?s1) ?s2) with (gcsubst (gcsubst x s1) s2) in VI at 1.
    rewrite (recΓt_inst _ _ _ _ (wf_ctx_dnf HΓ) (wf_ctx_dnf HD) (wf_ty_nf HT1)) in VI.
    assert (HΓ1 : [ mkG L Ψ ; Γ ,, tyCTrm Δ T l' @ lzero ⊢[ lM ] ])
      by (apply wfc_ext; [exact HΓ | apply wft_CTrm; auto | exact I]).
    pose proof (escM_VTyS HΓ1 Hl2 (HΓx _ _ HD HT1)
                  (stab_ty (i := lM) eq_refl EC2 (lequiv_refl L lzero I) HΓ1 (HΓx _ _ HD' HT2')) VI) as E.
    exact (eqty_single (i := lM) eq_refl E Ht1). }
  (* 4. the scrutinees *)
  assert (E4 : [ mkG L Ψ ; Γ ⊢[ lM ] mott (wrapMt Mt') l' Δ' T' t ≅ mott (wrapMt Mt') l' Δ' T' t' @ l2 ]).
  { exact (wf_ty_func (i := lM) eq_refl (HΓx _ _ HD' HT2') (lsub_eq_single (i := lM) eq_refl Ht2 Ht2' Htt2)). }
  eapply eqty_trans; [exact E1|]. eapply eqty_trans; [exact E2|]. eapply eqty_trans; [exact E3 | exact E4].
Qed.

End DeclConsequences.
