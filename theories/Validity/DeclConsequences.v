(** * Consequences for the declarative system

    At layer P ([DeclEq lD]) and at layer M ([DeclEq lM], relation
    [LR_M]), for arbitrary well-formed global contexts: reducibility
    comes from the fundamental theorems with global substitutions
    ([Reducible]).  Closed canonicity needs a global context without type
    or term bindings ([ctx_only]), whose global variables would be closed
    neutrals. *)
From DeLaM.Typing Require Export DeclInstance.
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

Theorem declM_U_inj {G Γ l l' k} : [ G ; Γ ⊢[ lM ] tyU l ≅ tyU l' @ k ] -> lequiv (gL G) l' l.
Proof. intros H. exact (U_inj (E := DEM) (LP := LRM) redM_eqty H (lwfM_whnf_l H (whnf_tyU _) ltac:(not_upi))). Qed.

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

End DeclConsequences.
