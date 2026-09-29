(** * The paper's rules are admissible in ours: P ⊆ O (M7_DESIGN.md C3 K4)

    Every judgment derivable by the paper's rules ([Typing/Paper.v]) is
    derivable by ours ([Typing/Declarative.v]). By induction on the P
    derivation; each P rule is an O rule whose extra premises are derived:
    - well-formedness of a congruence's left side, of domain contexts and
      of bodies: presupposition (at D and M, [Presupposition]; at V and C,
      [PresupC]) and inversion of the function types;
    - right-hand bodies under their own global binding ([TΠ], [ΛU],
      [letbox]): global-binding conversion ([gbind_*]);
    - instance premises: the recursor rules without their scope premises
      ([RecAdm]), the application results ([inst_*_ty]), the instance
      equations ([declM_inst_*_eq], [declM_mot*_eq]) and the β reducts'
      typing (subject reduction, [RecReduct]); the last three are
      consequences of the fundamental theorem;
    - levels: the paper's axiomatic equivalence is sound ([leqP_lequiv]).
    So consistency, canonicity, normalization and decidability of
    conversion hold for the paper's system on its typable syntax. *)
From DeLaM.Typing Require Import Paper PresupC RecAdm.
From DeLaM.Validity Require Import AlgSound RecReduct Consistency Canonicity.

(** ** Auxiliaries *)

Lemma Forall2_leqP_lequiv L ls ls' : Forall2 (leqP L) ls ls' -> Forall2 (lequiv L) ls ls'.
Proof. induction 1; constructor; auto using leqP_lequiv. Qed.

(** A type below M lives at a well-formed level (ω is M's). *)
Lemma ty_lwf_notM {G i Γ T l} : [ G ; Γ ⊢[ i ] T @ l ] -> i <> lM -> lwf (gL G) l.
Proof.
  induction 1; intros HM; try (exfalso; exact (HM eq_refl)); cbn [lwf];
    try solve [exact I | tauto | eapply lequiv_wf_l; eassumption].
  match goal with Hin : in_gctx _ _ (gdTy _ _ _), HΓ : wf_ctx _ _ _ |- _ =>
    exact (proj2 (gctx_decl_ok _ _ _ (ctx_glob _ _ _ HΓ) Hin)) end.
Qed.

Lemma glob_ext_ty {G Δ i l} : [ ⊢ gext G (gdTy Δ i l) ] -> [ G ; Δ ⊢[ lD ] ].
Proof. destruct G as [L Ψ]; intros H; inversion H; subst; assumption. Qed.

Lemma glob_of_M {G Γ T l} : [ G ; Γ ⊢[ lM ] T @ l ] -> [ ⊢ G ].
Proof. intros H; exact (ctx_glob _ _ _ (ctx_of_wf_ty (i := lM) eq_refl H)). Qed.

Lemma eqty_wf_any {G i Γ T T' l} : [ G ; Γ ⊢[ i ] T ≅ T' @ l ] ->
  [ G ; Γ ⊢[ i ] T @ l ] /\ [ G ; Γ ⊢[ i ] T' @ l ].
Proof.
  intros H; destruct i.
  - apply (eqty_wf_C (i := lV)); [unfold lle; cbn; lia | exact H].
  - apply (eqty_wf_C (i := lC)); [unfold lle; cbn; lia | exact H].
  - exact (conj (eqty_wf_l (i := lD) eq_refl H) (eqty_wf_r (i := lD) eq_refl H)).
  - exact (conj (eqty_wf_l (i := lM) eq_refl H) (eqty_wf_r (i := lM) eq_refl H)).
Qed.
Lemma eqtm_wf_any {G i Γ t t' T l} : [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] ->
  [ G ; Γ ⊢[ i ] t : T @ l ] /\ [ G ; Γ ⊢[ i ] t' : T @ l ].
Proof.
  intros H; destruct i.
  - apply (eqtm_wf_C (i := lV)); [unfold lle; cbn; lia | exact H].
  - apply (eqtm_wf_C (i := lC)); [unfold lle; cbn; lia | exact H].
  - exact (conj (eqtm_wf_l (i := lD) eq_refl H) (eqtm_wf_r (i := lD) eq_refl H)).
  - exact (conj (eqtm_wf_l (i := lM) eq_refl H) (eqtm_wf_r (i := lM) eq_refl H)).
Qed.

(** ** The P rules whose O form takes more premises *)

Section Rules.
Context {G : gctx}.

Lemma ps_tpi {Γ Δ l l' T} : [ G ; Γ ⊢[ lM ] ] -> [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] T @ l' ] ->
  lwf (gL G) l -> lwf (gL G) l' -> [ G ; Γ ⊢[ lM ] tyTPi Δ l l' T @ l' ].
Proof. intros HΓ HT W W'. apply wft_tpi; auto. exact (glob_ext_ty (glob_of_M HT)). Qed.

Lemma ps_CTrm {Γ Δ T l} : [ G ; Γ ⊢[ lM ] ] -> [ G ; Δ ⊢[ lD ] T @ l ] -> lwf (gL G) l ->
  [ G ; Γ ⊢[ lM ] tyCTrm Δ T l @ lzero ].
Proof. intros HΓ HT W. apply wft_CTrm; auto. exact (ctx_of_wf_ty (i := lD) eq_refl HT). Qed.

Lemma ps_ulam {Γ n l T t} : [ G ; Γ ⊢[ lM ] ] -> [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] t : T @ l ] ->
  0 < n -> lwf (n + gL G) l -> [ G ; Γ ⊢[ lM ] ulam n l T t : tyUPi n l T @ lomega ].
Proof. intros HΓ Ht Hn W. apply wf_ulam; auto. exact (wf_tm_ty (i := lM) eq_refl Ht). Qed.

Lemma ps_uapp {Γ n l T t ls} : [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] T @ l ] ->
  [ G ; Γ ⊢[ lM ] t : tyUPi n l T @ lomega ] -> length ls = n -> 0 < n -> Forall (lwf (gL G)) ls ->
  [ G ; Γ ⊢[ lM ] uapp t ls : T[uext ls lvar]ᵤ @ lvsubst l (uext ls lvar) ].
Proof.
  intros HT Ht Hlen Hn Hls. destruct (inv_ty_upi (wf_tm_ty (i := lM) eq_refl Ht)) as ((_ & _ & _ & W & _) & _).
  apply (wf_uapp G Γ n); auto.
Qed.

Lemma ps_clam {Γ l T t} : [ G ; Γ ⊢[ lM ] ] -> [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] t : T @ l ] -> lwf (gL G) l ->
  [ G ; Γ ⊢[ lM ] clam l T t : tyCPi l T @ l ].
Proof. intros HΓ Ht W. apply wf_clam; auto. exact (wf_tm_ty (i := lM) eq_refl Ht). Qed.

Lemma ps_capp {Γ l T t Δ} : [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T @ l ] ->
  [ G ; Γ ⊢[ lM ] t : tyCPi l T @ l ] -> [ G ; Δ ⊢[ lD ] ] ->
  [ G ; Γ ⊢[ lM ] capp t Δ : T⦃gsingle (GCtx Δ)⦄ @ l ].
Proof.
  intros HT Ht HΔ. destruct (inv_ty_cpi (wf_tm_ty (i := lM) eq_refl Ht)) as ((_ & HΓ & W & _) & _).
  apply wf_capp; auto. exact (inst_c_ty HΓ HΔ HT).
Qed.

Lemma ps_tlam {Γ Δ l l' T t} : [ G ; Γ ⊢[ lM ] ] -> [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] t : T @ l' ] ->
  lwf (gL G) l -> lwf (gL G) l' -> [ G ; Γ ⊢[ lM ] tlam Δ l l' T t : tyTPi Δ l l' T @ l' ].
Proof.
  intros HΓ Ht W W'. pose proof (wf_tm_ty (i := lM) eq_refl Ht) as HT.
  apply wf_tlam; auto. exact (glob_ext_ty (glob_of_M HT)).
Qed.

Lemma ps_tapp {Γ Δ l l' T t A} : [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] T @ l' ] ->
  [ G ; Γ ⊢[ lM ] t : tyTPi Δ l l' T @ l' ] -> [ G ; Δ ⊢[ lD ] A @ l ] ->
  [ G ; Γ ⊢[ lM ] tapp t A : T⦃gsingle (GTy A)⦄ @ l' ].
Proof.
  intros HT Ht HA. destruct (inv_ty_tpi (wf_tm_ty (i := lM) eq_refl Ht)) as ((_ & HΓ & HΔ & W & W' & _) & _).
  apply (wf_tapp G Γ Δ l); auto. exact (inst_t_ty HΓ HA HT).
Qed.

Lemma ps_boxT {Γ Δ T l} : [ G ; Γ ⊢[ lM ] ] -> [ G ; Δ ⊢[ lC ] T @ l ] ->
  [ G ; Γ ⊢[ lM ] boxT T : tyCTyp Δ l @ lzero ].
Proof.
  intros HΓ HT. apply wf_boxT; auto.
  - exact (ty_lwf_notM HT ltac:(discriminate)).
  - exact (ctx_of_ty_any HT).
Qed.

Lemma ps_boxt {Γ Δ t T l} : [ G ; Γ ⊢[ lM ] ] -> [ G ; Δ ⊢[ lC ] t : T @ l ] ->
  [ G ; Γ ⊢[ lM ] boxt t : tyCTrm Δ T l @ lzero ].
Proof.
  intros HΓ Ht. pose proof (wf_tm_ty_any Ht) as HT; cbn [typeof] in HT.
  apply wf_boxt; auto.
  - exact (ty_lwf_notM HT ltac:(discriminate)).
  - exact (ctx_of_tm_any Ht).
Qed.

(** Type equations *)

Lemma ps_eq_nat {i Γ} : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] -> [ G ; Γ ⊢[ i ] tyNat ≅ tyNat @ lzero ].
Proof. intros; apply eqty_refl, wft_nat; auto. Qed.

Lemma ps_eq_pi {i Γ l1 l2 l3 l4 A A' B B'} : i <> lV -> lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] -> [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] tyPi l1 l2 A B ≅ tyPi l3 l4 A' B' @ lmax l1 l2 ].
Proof. intros Hv H13 H24 HA HB; apply eqty_pi; auto. exact (proj1 (eqty_wf_any HA)). Qed.

Lemma ps_eq_cpi {Γ l l' T T'} : [ G ; Γ ⊢[ lM ] ] -> [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T ≅ T' @ l ] ->
  lequiv (gL G) l l' -> [ G ; Γ ⊢[ lM ] tyCPi l T ≅ tyCPi l' T' @ l ].
Proof. intros HΓ HT Hl; apply eqty_cpi; auto. exact (eqty_wf_l (i := lM) eq_refl HT). Qed.

(** Moving a judgment from the binding [U : Δ @ l] to an equal one
    [U : Δ' @ l'] (as [gbind_*], at the binding of a [TΠ]). *)
Lemma move_tybind {Δ Δ' i l l'} : lle i lD -> i <> lV -> [ ⊢ G ] -> [ G ; Δ' ⊢[ lD ] ] -> lwf (gL G) l' ->
  (i = lC \/ i = lD) -> [ G ⊢[ lD ] Δ ≅ Δ' ] -> lequiv (gL G) l l' ->
  (forall Γ T k, [ gext G (gdTy Δ i l) ; Γ ⊢[ lM ] T @ k ] -> [ gext G (gdTy Δ' i l') ; Γ ⊢[ lM ] T @ k ]) /\
  (forall Γ t T k, [ gext G (gdTy Δ i l) ; Γ ⊢[ lM ] t : T @ k ] ->
     [ gext G (gdTy Δ' i l') ; Γ ⊢[ lM ] t : T @ k ]).
Proof.
  intros Hle Hv HG HΔ' W' Hi HΔ Hl.
  assert (HGD : [ ⊢ gext G (gdTy Δ' i l') ]) by (apply wfg_ty; auto).
  pose proof (gbind_obj_ty Hle Hv HGD (eqctx_sym_D HΔ) (lequiv_sym _ _ _ Hl)) as Ho.
  split; intros; [exact (gbind_ty HG HGD Ho ltac:(eassumption)) | exact (gbind_tm HG HGD Ho eq_refl ltac:(eassumption))].
Qed.

Lemma ps_eq_tpi {Γ Δ Δ' l1 l2 l3 l4 T T'} : [ G ; Γ ⊢[ lM ] ] -> [ G ⊢[ lD ] Δ ≅ Δ' ] ->
  [ gext G (gdTy Δ lD l1) ; Γ⟪S⟫ ⊢[ lM ] T ≅ T' @ l2 ] ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ lM ] tyTPi Δ l1 l2 T ≅ tyTPi Δ' l3 l4 T' @ l2 ].
Proof.
  intros HΓ HΔ HTT H13 H24.
  pose proof (eqctx_wf_l (i := lD) eq_refl HΔ) as HD. pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HD'.
  destruct (move_tybind (i := lD) (lle_refl lD) ltac:(discriminate) (ctx_glob _ _ _ HΓ) HD'
              (lequiv_wf_r _ _ _ H13) (or_intror eq_refl) HΔ H13) as [Mv _].
  eapply eqty_tpi; eauto.
  - exact (eqty_wf_l (i := lM) eq_refl HTT).
  - eapply wft_lconv; [exact (Mv _ _ _ (eqty_wf_r (i := lM) eq_refl HTT)) | exact (lequiv_sym _ _ _ H24)].
Qed.

Lemma ps_eq_CTrm {Γ Δ Δ' T T' l l'} : [ G ; Γ ⊢[ lM ] ] -> [ G ⊢[ lD ] Δ ≅ Δ' ] ->
  [ G ; Δ ⊢[ lD ] T ≅ T' @ l ] -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ lM ] tyCTrm Δ T l ≅ tyCTrm Δ' T' l' @ lzero ].
Proof.
  intros HΓ HΔ HT Hl; apply eqty_CTrm; auto.
  - exact (eqctx_wf_l (i := lD) eq_refl HΔ).
  - exact (eqty_wf_l (i := lD) eq_refl HT).
Qed.

(** Term equations *)

Lemma ps_eq_code_pi {i Γ l1 l2 l3 l4 s s' t t'} : i <> lV -> lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] s ≅ s' : tyU l1 @ lsuc l1 ] ->
  [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t ≅ t' : tyU l2 @ lsuc l2 ] ->
  [ G ; Γ ⊢[ i ] tmPi l1 l2 s t ≅ tmPi l3 l4 s' t' : tyU (lmax l1 l2) @ lsuc (lmax l1 l2) ].
Proof. intros Hv H13 H24 Hs Ht; apply eqtm_code_pi; auto. exact (proj1 (eqtm_wf_any Hs)). Qed.

Lemma ps_eq_natrec {i Γ l l' M M' s s' z z' t t'} : i <> lV -> lequiv (gL G) l l' ->
  [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M ≅ M' @ l ] ->
  [ G ; Γ ⊢[ i ] s ≅ s' : M[lsingle zero] @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ i ] z ≅ z' : M[lsucc] @ l ] ->
  [ G ; Γ ⊢[ i ] t ≅ t' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] natrec l M s z t ≅ natrec l' M' s' z' t' : M[lsingle t] @ l ].
Proof. intros Hv Hl HM Hs Hz Ht; apply eqtm_natrec; auto. exact (proj1 (eqty_wf_any HM)). Qed.

Lemma ps_eq_ulam {Γ n l l' T T' t t'} : [ G ; Γ ⊢[ lM ] ] ->
  [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] T ≅ T' @ l ] ->
  [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] t ≅ t' : T @ l ] -> 0 < n -> lequiv (n + gL G) l l' ->
  [ G ; Γ ⊢[ lM ] ulam n l T t ≅ ulam n l' T' t' : tyUPi n l T @ lomega ].
Proof. intros HΓ HT Ht Hn Hl; apply eqtm_ulam; auto. exact (eqty_wf_l (i := lM) eq_refl HT). Qed.

Lemma ps_eq_uapp {Γ n l T t t' ls ls'} : [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] T @ l ] ->
  [ G ; Γ ⊢[ lM ] t ≅ t' : tyUPi n l T @ lomega ] -> length ls = n -> 0 < n ->
  Forall2 (lequiv (gL G)) ls ls' ->
  [ G ; Γ ⊢[ lM ] uapp t ls ≅ uapp t' ls' : T[uext ls lvar]ᵤ @ lvsubst l (uext ls lvar) ].
Proof.
  intros HT Htt Hlen Hn Hls.
  destruct (inv_ty_upi (eqtm_wf_ty (i := lM) eq_refl Htt)) as ((_ & _ & _ & W & _) & _).
  apply (eqtm_uapp G Γ n); auto.
Qed.

Lemma ps_eq_clam {Γ l l' T T' t t'} : [ G ; Γ ⊢[ lM ] ] ->
  [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T ≅ T' @ l ] -> [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] t ≅ t' : T @ l ] ->
  lequiv (gL G) l l' -> [ G ; Γ ⊢[ lM ] clam l T t ≅ clam l' T' t' : tyCPi l T @ l ].
Proof. intros HΓ HT Ht Hl; apply eqtm_clam; auto. exact (eqty_wf_l (i := lM) eq_refl HT). Qed.

Lemma ps_eq_capp {Γ l T t t' Δ Δ'} : [ G ; Γ ⊢[ lM ] t ≅ t' : tyCPi l T @ l ] -> [ G ⊢[ lD ] Δ ≅ Δ' ] ->
  [ G ; Γ ⊢[ lM ] capp t Δ ≅ capp t' Δ' : T⦃gsingle (GCtx Δ)⦄ @ l ].
Proof.
  intros Htt HΔ. destruct (inv_ty_cpi (eqtm_wf_ty (i := lM) eq_refl Htt)) as ((_ & HΓ & W & HT) & _).
  apply eqtm_capp; auto.
  - exact (eqctx_wf_l (i := lD) eq_refl HΔ).
  - exact (eqctx_wf_r (i := lD) eq_refl HΔ).
  - exact (declM_inst_c_eq HΓ W HT HΔ).
Qed.

Lemma ps_eq_tlam {Γ Δ Δ' l1 l2 l3 l4 T T' t t'} : [ G ; Γ ⊢[ lM ] ] -> [ G ⊢[ lD ] Δ ≅ Δ' ] ->
  [ gext G (gdTy Δ lD l1) ; Γ⟪S⟫ ⊢[ lM ] T ≅ T' @ l2 ] ->
  [ gext G (gdTy Δ lD l1) ; Γ⟪S⟫ ⊢[ lM ] t ≅ t' : T @ l2 ] ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ lM ] tlam Δ l1 l2 T t ≅ tlam Δ' l3 l4 T' t' : tyTPi Δ l1 l2 T @ l2 ].
Proof.
  intros HΓ HΔ HTT Htt H13 H24.
  pose proof (eqctx_wf_l (i := lD) eq_refl HΔ) as HD. pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HD'.
  destruct (move_tybind (i := lD) (lle_refl lD) ltac:(discriminate) (ctx_glob _ _ _ HΓ) HD'
              (lequiv_wf_r _ _ _ H13) (or_intror eq_refl) HΔ H13) as [MvT Mvt].
  pose proof (eqty_wf_r (i := lM) eq_refl HTT) as HT'.
  pose proof (wf_conv _ _ _ _ _ _ _ (eqtm_wf_r (i := lM) eq_refl Htt) (eqty_sym _ _ _ _ _ _ HTT)) as Ht'.
  apply eqtm_tlam; auto.
  - exact (eqty_wf_l (i := lM) eq_refl HTT).
  - eapply wft_lconv; [exact (MvT _ _ _ HT') | exact (lequiv_sym _ _ _ H24)].
  - eapply wf_lconv; [exact (Mvt _ _ _ _ Ht') | exact (lequiv_sym _ _ _ H24)].
Qed.

Lemma ps_eq_tapp {Γ Δ l l' T t t' A A'} : [ G ; Γ ⊢[ lM ] t ≅ t' : tyTPi Δ l l' T @ l' ] ->
  [ G ; Δ ⊢[ lD ] A ≅ A' @ l ] -> [ G ; Γ ⊢[ lM ] tapp t A ≅ tapp t' A' : T⦃gsingle (GTy A)⦄ @ l' ].
Proof.
  intros Htt HA. destruct (inv_ty_tpi (eqtm_wf_ty (i := lM) eq_refl Htt)) as ((_ & HΓ & HΔ & W & W' & HT) & _).
  apply (eqtm_tapp G Γ Δ l); auto.
  - exact (eqty_wf_l (i := lD) eq_refl HA).
  - exact (declM_inst_t_eq HΓ W' HT HA).
Qed.

Lemma ps_eq_boxT {Γ Δ T T' l} : [ G ; Γ ⊢[ lM ] ] -> [ G ; Δ ⊢[ lC ] T ≅ T' @ l ] ->
  [ G ; Γ ⊢[ lM ] boxT T ≅ boxT T' : tyCTyp Δ l @ lzero ].
Proof.
  intros HΓ HTT. destruct (eqty_wf_any HTT) as [HT HT'].
  apply eqtm_boxT; auto.
  - exact (ty_lwf_notM HT ltac:(discriminate)).
  - exact (ctx_of_ty_any HT).
Qed.

Lemma ps_eq_boxt {Γ Δ t t' T l} : [ G ; Γ ⊢[ lM ] ] -> [ G ; Δ ⊢[ lC ] t ≅ t' : T @ l ] ->
  [ G ; Γ ⊢[ lM ] boxt t ≅ boxt t' : tyCTrm Δ T l @ lzero ].
Proof.
  intros HΓ Htt. destruct (eqtm_wf_any Htt) as [Ht Ht'].
  pose proof (wf_tm_ty_any Ht) as HT; cbn [typeof] in HT.
  apply eqtm_boxt; auto.
  - exact (ty_lwf_notM HT ltac:(discriminate)).
  - exact (ctx_of_tm_any Ht).
Qed.

Lemma ps_eq_letboxT {Γ l1 l2 l3 l4 Δ Δ' M M' t1 t2 t t0} : [ G ; Γ ⊢[ lM ] ] ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 -> [ G ⊢[ lD ] Δ ≅ Δ' ] ->
  [ G ; Γ ⊢[ lM ] t ≅ t0 : tyCTyp Δ l2 @ lzero ] ->
  [ G ; Γ ,, tyCTyp Δ l2 @ lzero ⊢[ lM ] M ≅ M' @ l1 ] ->
  [ gext G (gdTy Δ lC l2) ; Γ⟪S⟫ ⊢[ lM ] t1 ≅ t2 : M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))] @ l1 ] ->
  [ G ; Γ ⊢[ lM ] letboxT l1 l2 Δ M t1 t ≅ letboxT l3 l4 Δ' M' t2 t0 : M[lsingle t] @ l1 ].
Proof.
  intros HΓ H13 H24 HΔ Ht HMM Ht12.
  pose proof (eqctx_wf_l (i := lD) eq_refl HΔ) as HD. pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HD'.
  pose proof (ctx_glob _ _ _ HΓ) as HG.
  pose proof (lequiv_wf_l _ _ _ H24) as W2. pose proof (lequiv_wf_r _ _ _ H24) as W4.
  assert (HGD : [ ⊢ gext G (gdTy Δ lC l2) ]) by (apply wfg_ty; auto).
  assert (HCC : [ G ; Γ ⊢[ lM ] tyCTyp Δ l2 ≅ tyCTyp Δ' l4 @ lzero ]) by (apply eqty_CTyp; auto).
  assert (HΓ1 : [ G ; Γ ,, tyCTyp Δ' l4 @ lzero ⊢[ lM ] ])
    by (apply wfc_ext; [exact HΓ | apply wft_CTyp; auto | exact I]).
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty (i := lM) eq_refl HCC (lequiv_refl (gL G) lzero I) HΓ1
                                        (eqty_wf_r (i := lM) eq_refl HMM)) (lequiv_sym _ _ _ H13)) as HM'.
  destruct (move_tybind (i := lC) ltac:(unfold lle; cbn; lia) ltac:(discriminate) HG HD' W4
              (or_introl eq_refl) HΔ H24) as [_ Mvt].
  pose proof (letboxT_body_eq HGD HD W2 HMM) as EMb.
  pose proof (wf_conv _ _ _ _ _ _ _ (eqtm_wf_r (i := lM) eq_refl Ht12) (eqty_sym _ _ _ _ _ _ EMb)) as Ht2.
  eapply eqtm_letboxT; eauto.
  - exact (eqty_wf_l (i := lM) eq_refl HMM).
  - eapply wf_lconv; [exact (Mvt _ _ _ _ Ht2) | exact (lequiv_sym _ _ _ H13)].
Qed.

Lemma ps_eq_letboxt {Γ l1 l2 l3 l4 Δ Δ' T T' M M' t1 t2 t t0} : [ G ; Γ ⊢[ lM ] ] ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 -> [ G ⊢[ lD ] Δ ≅ Δ' ] ->
  [ G ; Δ ⊢[ lD ] T ≅ T' @ l2 ] ->
  [ G ; Γ ⊢[ lM ] t ≅ t0 : tyCTrm Δ T l2 @ lzero ] ->
  [ G ; Γ ,, tyCTrm Δ T l2 @ lzero ⊢[ lM ] M ≅ M' @ l1 ] ->
  [ gext G (gdTm Δ lC T l2) ; Γ⟪S⟫ ⊢[ lM ] t1 ≅ t2 : M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))] @ l1 ] ->
  [ G ; Γ ⊢[ lM ] letboxt l1 l2 Δ T M t1 t ≅ letboxt l3 l4 Δ' T' M' t2 t0 : M[lsingle t] @ l1 ].
Proof.
  intros HΓ H13 H24 HΔ HTT Ht HMM Ht12.
  pose proof (eqctx_wf_l (i := lD) eq_refl HΔ) as HD. pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HD'.
  pose proof (ctx_glob _ _ _ HΓ) as HG.
  pose proof (lequiv_wf_l _ _ _ H24) as W2. pose proof (lequiv_wf_r _ _ _ H24) as W4.
  pose proof (eqty_wf_l (i := lD) eq_refl HTT) as HT.
  pose proof (ctxconv_eqty HΔ (i := lD) eq_refl HTT) as HTT'.
  pose proof (wft_lconv _ _ _ _ _ _ (eqty_wf_r (i := lD) eq_refl HTT') (lequiv_sym _ _ _ H24)) as HT'.
  assert (HGD : [ ⊢ gext G (gdTm Δ lC T l2) ]) by (apply wfg_tm; auto).
  assert (HGD' : [ ⊢ gext G (gdTm Δ' lC T' l4) ]) by (apply wfg_tm; auto).
  assert (HCC : [ G ; Γ ⊢[ lM ] tyCTrm Δ T l2 ≅ tyCTrm Δ' T' l4 @ lzero ]) by (apply eqty_CTrm; auto).
  assert (HΓ1 : [ G ; Γ ,, tyCTrm Δ' T' l4 @ lzero ⊢[ lM ] ])
    by (apply wfc_ext; [exact HΓ | apply wft_CTrm; auto | exact I]).
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty (i := lM) eq_refl HCC (lequiv_refl (gL G) lzero I) HΓ1
                                        (eqty_wf_r (i := lM) eq_refl HMM)) (lequiv_sym _ _ _ H13)) as HM'.
  assert (Ho : gobj_wf (gext G (gdTm Δ' lC T' l4)) (id_obj (gdTm Δ lC T l2) 0)
                 (gdecl_gsubst (gdTm Δ lC T l2) (gsub_wk gid (gwk_step gwk_id)))).
  { apply (gbind_obj_tm HGD' (eqctx_sym_D HΔ)); [| exact (lequiv_sym _ _ _ H24)].
    eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ HTT') | exact (lequiv_sym _ _ _ H24)]. }
  pose proof (letboxt_body_eq HGD HD HT W2 HMM) as EMb.
  pose proof (wf_conv _ _ _ _ _ _ _ (eqtm_wf_r (i := lM) eq_refl Ht12) (eqty_sym _ _ _ _ _ _ EMb)) as Ht2.
  eapply eqtm_letboxt; eauto.
  - exact (eqty_wf_l (i := lM) eq_refl HMM).
  - eapply wf_lconv; [exact (gbind_tm HG HGD' Ho eq_refl Ht2) | exact (lequiv_sym _ _ _ H13)].
Qed.

(** The recursors' congruences: the right side's scopes by [brΓ_wf], its
    branches moved there by [branch_conv], the instance equation by
    [declM_mot*_eq]. *)
Lemma ps_eq_elimT {Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' t t'} :
  lequiv (gL G) l1 l1' -> lequiv (gL G) l2 l2' ->
  [ recGT G ; recΓT Γ ⊢[ lM ] MT ≅ MT' @ lvren l1 (ush 1) ] ->
  [ recGt G ; recΓt Γ ⊢[ lM ] Mt ≅ Mt' @ lvren l2 (ush 1) ] ->
  (forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                         bs k ≅ bs' k : brRes k (wrapMT MT) (wrapMt Mt) @ brLv k l1 l2 ]) ->
  lequiv (gL G) l l' -> [ G ⊢[ lD ] Δ ≅ Δ' ] ->
  [ G ; Γ ⊢[ lM ] t ≅ t' : tyCTyp Δ l @ lzero ] ->
  [ G ; Γ ⊢[ lM ] elimT l1 l2 (mkrb MT Mt bs) l Δ t ≅ elimT l1' l2' (mkrb MT' Mt' bs') l' Δ' t'
                : motT (wrapMT MT) l Δ t @ l1 ].
Proof.
  intros E1 E2 EMT EMt Ebr El HΔ Htt.
  pose proof (ctx_of_eqtm (i := lM) eq_refl Htt) as HΓ.
  pose proof (lequiv_wf_l _ _ _ E1) as W1. pose proof (lequiv_wf_l _ _ _ E2) as W2.
  pose proof (lequiv_wf_r _ _ _ E1) as W1'. pose proof (lequiv_wf_r _ _ _ E2) as W2'.
  pose proof (eqty_wf_l (i := lM) eq_refl EMT) as HMT. pose proof (eqty_wf_l (i := lM) eq_refl EMt) as HMt.
  pose proof (wft_lconv _ _ _ _ _ _ (eqty_wf_r (i := lM) eq_refl EMT) (lequiv_ush 1 (lequiv_sym _ _ _ E1)))
    as HMT'.
  pose proof (wft_lconv _ _ _ _ _ _ (eqty_wf_r (i := lM) eq_refl EMt) (lequiv_ush 1 (lequiv_sym _ _ _ E2)))
    as HMt'.
  pose proof (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EMT) (lequiv_ush 1 (lequiv_sym _ _ _ E1))) as EMT'.
  pose proof (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EMt) (lequiv_ush 1 (lequiv_sym _ _ _ E2))) as EMt'.
  pose proof (fun k Hk => brΓ_wf HΓ W1 W2 HMT HMt k Hk) as Hbc.
  pose proof (fun k Hk => brΓ_wf HΓ W1' W2' HMT' HMt' k Hk) as Hbc'.
  assert (Hbs1 : forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ]
                                        bs' k : brRes k (wrapMT MT') (wrapMt Mt') @ brLv k l1' l2' ]).
  { intros k Hk. apply (branch_conv k Hk EMT' EMt' (lequiv_sym _ _ _ E1) (lequiv_sym _ _ _ E2) HΓ
                          (Hbc' k Hk) (Hbc k Hk)).
    exact (eqtm_wf_r (i := lM) eq_refl (Ebr k Hk)). }
  apply eqtm_elimT; auto.
  - exact (declM_motT_eq EMT W1 El HΔ Htt).
  - exact (eqctx_wf_l (i := lD) eq_refl HΔ).
  - exact (eqctx_wf_r (i := lD) eq_refl HΔ).
Qed.

Lemma ps_eq_elimt {Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' T T' t t'} :
  lequiv (gL G) l1 l1' -> lequiv (gL G) l2 l2' ->
  [ recGT G ; recΓT Γ ⊢[ lM ] MT ≅ MT' @ lvren l1 (ush 1) ] ->
  [ recGt G ; recΓt Γ ⊢[ lM ] Mt ≅ Mt' @ lvren l2 (ush 1) ] ->
  (forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                         bs k ≅ bs' k : brRes k (wrapMT MT) (wrapMt Mt) @ brLv k l1 l2 ]) ->
  lequiv (gL G) l l' -> [ G ⊢[ lD ] Δ ≅ Δ' ] -> [ G ; Δ ⊢[ lD ] T ≅ T' @ l ] ->
  [ G ; Γ ⊢[ lM ] t ≅ t' : tyCTrm Δ T l @ lzero ] ->
  [ G ; Γ ⊢[ lM ] elimt l1 l2 (mkrb MT Mt bs) l Δ T t ≅ elimt l1' l2' (mkrb MT' Mt' bs') l' Δ' T' t'
                : mott (wrapMt Mt) l Δ T t @ l2 ].
Proof.
  intros E1 E2 EMT EMt Ebr El HΔ HTT Htt.
  pose proof (ctx_of_eqtm (i := lM) eq_refl Htt) as HΓ.
  pose proof (lequiv_wf_l _ _ _ E1) as W1. pose proof (lequiv_wf_l _ _ _ E2) as W2.
  pose proof (lequiv_wf_r _ _ _ E1) as W1'. pose proof (lequiv_wf_r _ _ _ E2) as W2'.
  pose proof (eqty_wf_l (i := lM) eq_refl EMT) as HMT. pose proof (eqty_wf_l (i := lM) eq_refl EMt) as HMt.
  pose proof (wft_lconv _ _ _ _ _ _ (eqty_wf_r (i := lM) eq_refl EMT) (lequiv_ush 1 (lequiv_sym _ _ _ E1)))
    as HMT'.
  pose proof (wft_lconv _ _ _ _ _ _ (eqty_wf_r (i := lM) eq_refl EMt) (lequiv_ush 1 (lequiv_sym _ _ _ E2)))
    as HMt'.
  pose proof (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EMT) (lequiv_ush 1 (lequiv_sym _ _ _ E1))) as EMT'.
  pose proof (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EMt) (lequiv_ush 1 (lequiv_sym _ _ _ E2))) as EMt'.
  pose proof (fun k Hk => brΓ_wf HΓ W1 W2 HMT HMt k Hk) as Hbc.
  pose proof (fun k Hk => brΓ_wf HΓ W1' W2' HMT' HMt' k Hk) as Hbc'.
  assert (Hbs1 : forall k, k < nbr -> [ brG k G ; brΓ k Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ]
                                        bs' k : brRes k (wrapMT MT') (wrapMt Mt') @ brLv k l1' l2' ]).
  { intros k Hk. apply (branch_conv k Hk EMT' EMt' (lequiv_sym _ _ _ E1) (lequiv_sym _ _ _ E2) HΓ
                          (Hbc' k Hk) (Hbc k Hk)).
    exact (eqtm_wf_r (i := lM) eq_refl (Ebr k Hk)). }
  pose proof (ctxconv_eqty HΔ (i := lD) eq_refl HTT) as HTT'.
  apply eqtm_elimt; auto.
  - exact (declM_mott_eq EMt W2 El HΔ HTT Htt).
  - exact (eqctx_wf_l (i := lD) eq_refl HΔ).
  - exact (eqctx_wf_r (i := lD) eq_refl HΔ).
  - exact (eqty_wf_l (i := lD) eq_refl HTT).
  - eapply wft_lconv; [exact (eqty_wf_r (i := lD) eq_refl HTT') | exact (lequiv_sym _ _ _ El)].
Qed.

(** Computation rules with fewer premises in P *)

Lemma ps_ubeta {Γ n l T t ls} : [ G ; Γ ⊢[ lM ] ] ->
  [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] t : T @ l ] -> lwf (n + gL G) l ->
  length ls = n -> 0 < n -> Forall (lwf (gL G)) ls ->
  [ G ; Γ ⊢[ lM ] t[uext ls lvar]ᵤ ≅ uapp (ulam n l T t) ls : T[uext ls lvar]ᵤ @ lvsubst l (uext ls lvar) ].
Proof.
  intros; apply eqtm_sym, eqtm_ubeta; auto. exact (wf_tm_ty (i := lM) eq_refl ltac:(eassumption)).
Qed.

Lemma ps_ueta {Γ n l T t} : [ G ; Γ ⊢[ lM ] t : tyUPi n l T @ lomega ] ->
  [ G ; Γ ⊢[ lM ] ulam n l T (uapp t⟨ush n⟩ᵤ (ubvars n)) ≅ t : tyUPi n l T @ lomega ].
Proof.
  intros Ht. destruct (inv_ty_upi (wf_tm_ty (i := lM) eq_refl Ht)) as ((_ & _ & Hn & W & HT) & _).
  apply eqtm_ueta; auto.
Qed.

Lemma ps_cbeta {Γ l T t Δ} : [ G ; Γ ⊢[ lM ] ] -> [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] t : T @ l ] ->
  lwf (gL G) l -> [ G ; Δ ⊢[ lD ] ] ->
  [ G ; Γ ⊢[ lM ] t⦃gsingle (GCtx Δ)⦄ ≅ capp (clam l T t) Δ : T⦃gsingle (GCtx Δ)⦄ @ l ].
Proof.
  intros; apply eqtm_sym, eqtm_cbeta; auto. exact (wf_tm_ty (i := lM) eq_refl ltac:(eassumption)).
Qed.

Lemma ps_ceta {Γ l T t} : [ G ; Γ ⊢[ lM ] t : tyCPi l T @ l ] ->
  [ G ; Γ ⊢[ lM ] clam l T (capp t⟪S⟫ (cvar 0)) ≅ t : tyCPi l T @ l ].
Proof.
  intros Ht. destruct (inv_ty_cpi (wf_tm_ty (i := lM) eq_refl Ht)) as ((_ & _ & W & HT) & _).
  apply eqtm_ceta; auto.
Qed.

Lemma ps_tbeta {Γ Δ l l' T t A} : [ G ; Γ ⊢[ lM ] ] ->
  [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] t : T @ l' ] -> lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Δ ⊢[ lD ] A @ l ] ->
  [ G ; Γ ⊢[ lM ] t⦃gsingle (GTy A)⦄ ≅ tapp (tlam Δ l l' T t) A : T⦃gsingle (GTy A)⦄ @ l' ].
Proof.
  intros HΓ Ht W W' HA. apply eqtm_sym, eqtm_tbeta; auto.
  - exact (ctx_of_wf_ty (i := lD) eq_refl HA).
  - exact (wf_tm_ty (i := lM) eq_refl Ht).
Qed.

Lemma ps_teta {Γ Δ l l' T t} : [ G ; Γ ⊢[ lM ] t : tyTPi Δ l l' T @ l' ] ->
  [ G ; Γ ⊢[ lM ] tlam Δ l l' T (tapp t⟪S⟫ (tyGvar 0 (lshift 0))) ≅ t : tyTPi Δ l l' T @ l' ].
Proof.
  intros Ht. destruct (inv_ty_tpi (wf_tm_ty (i := lM) eq_refl Ht)) as ((_ & _ & HΔ & W & W' & HT) & _).
  apply eqtm_teta; auto.
Qed.

Lemma ps_elimT_beta {Γ l1 l2 rb l Δ c T k r} :
  [ G ; Γ ⊢[ lM ] elimT l1 l2 rb l Δ (boxT c) : T @ k ] -> redT l1 l2 rb l Δ c = Some r ->
  [ G ; Γ ⊢[ lM ] r ≅ elimT l1 l2 rb l Δ (boxT c) : T @ k ].
Proof.
  intros Hx E. apply eqtm_sym, (eqtm_elimT_beta _ _ _ _ _ _ _ _ _ _ _ Hx E).
  exact (subject_reduction_tm compt_M Hx (red_elimT_beta _ _ _ _ _ _ _ E)).
Qed.

Lemma ps_elimt_beta {Γ l1 l2 rb l Δ T0 c T k r} :
  [ G ; Γ ⊢[ lM ] elimt l1 l2 rb l Δ T0 (boxt c) : T @ k ] -> redt l1 l2 rb l Δ T0 c = Some r ->
  [ G ; Γ ⊢[ lM ] r ≅ elimt l1 l2 rb l Δ T0 (boxt c) : T @ k ].
Proof.
  intros Hx E. apply eqtm_sym, (eqtm_elimt_beta _ _ _ _ _ _ _ _ _ _ _ _ Hx E).
  exact (subject_reduction_tm compt_M Hx (red_elimt_beta _ _ _ _ _ _ _ _ E)).
Qed.

End Rules.

(** ** P ⊆ O *)

Theorem paper_sound :
  (forall G, [ ⊢ₚ G ] -> [ ⊢ G ]) /\
  (forall G i Γ, [ G ; Γ ⊢ₚ[ i ] ] -> [ G ; Γ ⊢[ i ] ]) /\
  (forall G i Γ T l, [ G ; Γ ⊢ₚ[ i ] T @ l ] -> [ G ; Γ ⊢[ i ] T @ l ]) /\
  (forall G i Γ t T l, [ G ; Γ ⊢ₚ[ i ] t : T @ l ] -> [ G ; Γ ⊢[ i ] t : T @ l ]) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢ₚ[ i ] T ≅ T' @ l ] -> [ G ; Γ ⊢[ i ] T ≅ T' @ l ]) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢ₚ[ i ] t ≅ t' : T @ l ] -> [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ]) /\
  (forall G i Γ Γ', [ G ⊢ₚ[ i ] Γ ≅ Γ' ] -> [ G ⊢[ i ] Γ ≅ Γ' ]).
Proof.
  apply ptyping_mut; intros;
    repeat match goal with H : leqP _ _ _ |- _ => apply leqP_lequiv in H end;
    repeat match goal with H : Forall2 (leqP _) _ _ |- _ => apply Forall2_leqP_lequiv in H end.
  (* O rules with the same premises *)
  all: try solve [econstructor; eassumption].
  (* reflexivity instances *)
  all: try solve [apply eqtm_refl; econstructor; eassumption].
  (* the elimination rules without their scope premises *)
  all: try solve [first [eapply wf_elimT_adm | eapply wf_elimt_adm]; eassumption].
  (* computation rules stated right to left *)
  all: try solve [apply eqtm_sym; econstructor; eassumption].
  all: first
    [ solve [eapply ps_tpi; eassumption] | solve [eapply ps_CTrm; eassumption]
    | solve [eapply ps_ulam; eassumption] | solve [eapply ps_uapp; eassumption]
    | solve [eapply ps_clam; eassumption] | solve [eapply ps_capp; eassumption]
    | solve [eapply ps_tlam; eassumption] | solve [eapply ps_tapp; eassumption]
    | solve [eapply ps_boxT; eassumption] | solve [eapply ps_boxt; eassumption]
    | solve [eapply ps_eq_nat; eassumption] | solve [eapply ps_eq_pi; eassumption]
    | solve [eapply ps_eq_cpi; eassumption] | solve [eapply ps_eq_tpi; eassumption]
    | solve [eapply ps_eq_CTrm; eassumption]
    | solve [eapply ps_eq_code_pi; eassumption] | solve [eapply ps_eq_natrec; eassumption]
    | solve [eapply ps_eq_ulam; eassumption] | solve [eapply ps_eq_uapp; eassumption]
    | solve [eapply ps_eq_clam; eassumption] | solve [eapply ps_eq_capp; eassumption]
    | solve [eapply ps_eq_tlam; eassumption] | solve [eapply ps_eq_tapp; eassumption]
    | solve [eapply ps_eq_boxT; eassumption] | solve [eapply ps_eq_boxt; eassumption]
    | solve [eapply ps_eq_letboxT; eassumption] | solve [eapply ps_eq_letboxt; eassumption]
    | solve [eapply ps_eq_elimT; eassumption] | solve [eapply ps_eq_elimt; eassumption]
    | solve [eapply ps_ubeta; eassumption] | solve [eapply ps_ueta; eassumption]
    | solve [eapply ps_cbeta; eassumption] | solve [eapply ps_ceta; eassumption]
    | solve [eapply ps_tbeta; eassumption] | solve [eapply ps_teta; eassumption]
    | solve [eapply ps_elimT_beta; eassumption] | solve [eapply ps_elimt_beta; eassumption] ].
Qed.

(** ** Consequences for the paper's system *)

Corollary paper_consistency {G i t l1 l2 l l' k} : compt i -> ctx_only G ->
  ~ [ G ; cnil ⊢ₚ[ i ] t : tyPi l1 l2 (tyU l) (tyEl l' (var 0)) @ k ].
Proof. intros Hc HG H. exact (consistency_closed Hc HG (proj1 (proj2 (proj2 (proj2 paper_sound))) _ _ _ _ _ _ H)). Qed.

(** A closed P-typed term reduces to a canonical value (its equation with
    the value is an O equation; the P one needs O ⊆ P). *)
Corollary paper_canonicity {G i t T k} : compt i -> ctx_only G -> [ G ; cnil ⊢ₚ[ i ] t : T @ k ] ->
  exists W w, reds_ty T W /\ whnf_ty W /\ ~ whne_ty W /\
    reds t w /\ whnf w /\ ~ whne w /\ canon_head (ty_head W) w.
Proof.
  intros Hc HG H.
  destruct (closed_canonicity Hc (or_introl HG) (proj1 (proj2 (proj2 (proj2 paper_sound))) _ _ _ _ _ _ H))
    as (W & w & ? & ? & ? & ? & ? & ? & _ & ?).
  exists W, w; repeat split; assumption.
Qed.
