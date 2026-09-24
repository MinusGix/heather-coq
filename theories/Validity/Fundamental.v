(** * The fundamental theorem: well-typed terms are valid

    By mutual induction over the declarative judgments at the layer of the
    generic equivalence ([ge_layer]). Each case is closed by the validity
    lemma of its rule; the wrappers below derive the extra typing premises
    of those lemmas (presupposition, stability) from the rule's own. *)
From DeLaM.Validity Require Export CodePi.

Section Fundamental.
Context `{E : GenericEq} `{EL : !GenericEqLaws}.

(** ** Rule-shaped wrappers *)

Section Wrappers.
Context {G : gctx} {Γ : ctx}.

Lemma ft_U {l} : lwf (gL G) l -> VTy G Γ (tyU l) (tyU l) (lsuc l).
Proof. intros Hwl; exact (V_U Hwl (lequiv_refl _ _ Hwl)). Qed.
Lemma ft_U_eq {l l'} : lequiv (gL G) l l' -> VTy G Γ (tyU l) (tyU l') (lsuc l).
Proof. intros Hl; exact (V_U (lequiv_wf_l _ _ _ Hl) Hl). Qed.

Lemma ft_El {l t} : lwf (gL G) l -> VTm G Γ t t (tyU l) (lsuc l) -> VTy G Γ (tyEl l t) (tyEl l t) l.
Proof. intros Hwl Vt; exact (V_El Hwl (lequiv_refl _ _ Hwl) Vt). Qed.
Lemma ft_El_eq {l l' t t'} :
  lequiv (gL G) l l' -> VTm G Γ t t' (tyU l) (lsuc l) -> VTy G Γ (tyEl l t) (tyEl l' t') l.
Proof. intros Hl Vt; exact (V_El (lequiv_wf_l _ _ _ Hl) Hl Vt). Qed.

Lemma ft_code_U {l} : lwf (gL G) l -> VTm G Γ (tmU l) (tmU l) (tyU (lsuc l)) (lsuc (lsuc l)).
Proof. intros Hwl; exact (V_code_U Hwl (lequiv_refl _ _ Hwl)). Qed.
Lemma ft_code_U_eq {l l'} :
  lequiv (gL G) l l' -> VTm G Γ (tmU l) (tmU l') (tyU (lsuc l)) (lsuc (lsuc l)).
Proof. intros Hl; exact (V_code_U (lequiv_wf_l _ _ _ Hl) Hl). Qed.

Lemma ft_pi {l l' A B} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ,, A @ l ⊢g B @ l' ] -> VTy G Γ A A l -> VTy G (Γ ,, A @ l) B B l' ->
  VTy G Γ (tyPi l l' A B) (tyPi l l' A B) (lmax l l').
Proof.
  intros Hw Hw' HB VA VB. exact (V_pi Hw Hw' (lequiv_refl _ _ Hw) (lequiv_refl _ _ Hw') HB HB VA VB).
Qed.

Lemma ft_pi_eq {l1 l2 l3 l4 A A' B B'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢g A ≅ A' @ l1 ] -> [ G ; Γ ,, A @ l1 ⊢g B ≅ B' @ l2 ] ->
  VTy G Γ A A' l1 -> VTy G (Γ ,, A @ l1) B B' l2 ->
  VTy G Γ (tyPi l1 l2 A B) (tyPi l3 l4 A' B') (lmax l1 l2).
Proof.
  intros H13 H24 HAA HBB VA VB.
  pose proof (lequiv_wf_l _ _ _ H13) as Hw1.
  assert (HΓ : [ G ; Γ ,, A' @ l1 ⊢g ]) by (apply ext_wf_g; [exact (eqty_wf_r ge_typeof HAA) | exact Hw1]).
  pose proof (stab_ty ge_typeof HAA (lequiv_refl _ _ Hw1) HΓ (eqty_wf_r ge_typeof HBB)) as HB'.
  exact (V_pi Hw1 (lequiv_wf_l _ _ _ H24) (lequiv_sym _ _ _ H13) (lequiv_sym _ _ _ H24)
           (eqty_wf_l ge_typeof HBB) HB' VA VB).
Qed.

Lemma ft_code_pi {l l' s t} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢g s : tyU l @ lsuc l ] -> [ G ; Γ ,, tyEl l s @ l ⊢g t : tyU l' @ lsuc l' ] ->
  VTm G Γ s s (tyU l) (lsuc l) -> VTm G (Γ ,, tyEl l s @ l) t t (tyU l') (lsuc l') ->
  VTm G Γ (tmPi l l' s t) (tmPi l l' s t) (tyU (lmax l l')) (lsuc (lmax l l')).
Proof.
  intros Hw Hw' Hs Ht Vs Vt.
  exact (V_code_pi Hw Hw' (lequiv_refl _ _ Hw) (lequiv_refl _ _ Hw') Hs Hs (eqtm_refl _ _ _ _ _ _ Hs)
           Ht Ht Vs Vt).
Qed.

Lemma ft_code_pi_eq {l1 l2 l3 l4 s s' t t'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢g s : tyU l1 @ lsuc l1 ] -> [ G ; Γ ⊢g s ≅ s' : tyU l1 @ lsuc l1 ] ->
  [ G ; Γ ,, tyEl l1 s @ l1 ⊢g t ≅ t' : tyU l2 @ lsuc l2 ] ->
  VTm G Γ s s' (tyU l1) (lsuc l1) -> VTm G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) (lsuc l2) ->
  VTm G Γ (tmPi l1 l2 s t) (tmPi l3 l4 s' t') (tyU (lmax l1 l2)) (lsuc (lmax l1 l2)).
Proof.
  intros H13 H24 Hs Hss Htt Vs Vt.
  exact (V_code_pi (lequiv_wf_l _ _ _ H13) (lequiv_wf_l _ _ _ H24) H13 H24 Hs (eqtm_wf_r ge_typeof Hss) Hss
           (eqtm_wf_l ge_typeof Htt) (eqtm_wf_r ge_typeof Htt) Vs Vt).
Qed.

Lemma ft_natrec {l M s z t} : lwf (gL G) l ->
  [ G ; Γ ,, tyNat @ lzero ⊢g M @ l ] -> [ G ; Γ ⊢g s : M[lsingle zero] @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢g z : M[lsucc] @ l ] ->
  VTy G (Γ ,, tyNat @ lzero) M M l -> VTm G Γ s s M[lsingle zero] l ->
  VTm G (Γ ,, tyNat @ lzero ,, M @ l) z z M[lsucc] l -> VTm G Γ t t tyNat lzero ->
  VTm G Γ (natrec l M s z t) (natrec l M s z t) M[lsingle t] l.
Proof.
  intros Hwl HM Hs Hz VM Vs Vz Vt.
  exact (V_natrec Hwl (lequiv_refl _ _ Hwl) HM HM Hs Hs Hz Hz VM Vs Vz Vt).
Qed.

Lemma ft_natrec_eq {l l' M M' s s' z z' t t'} : lequiv (gL G) l l' ->
  [ G ; Γ ,, tyNat @ lzero ⊢g M @ l ] -> [ G ; Γ ,, tyNat @ lzero ⊢g M ≅ M' @ l ] ->
  [ G ; Γ ⊢g s ≅ s' : M[lsingle zero] @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢g z ≅ z' : M[lsucc] @ l ] ->
  VTy G (Γ ,, tyNat @ lzero) M M' l -> VTm G Γ s s' M[lsingle zero] l ->
  VTm G (Γ ,, tyNat @ lzero ,, M @ l) z z' M[lsucc] l -> VTm G Γ t t' tyNat lzero ->
  VTm G Γ (natrec l M s z t) (natrec l' M' s' z' t') M[lsingle t] l.
Proof.
  intros Hll HM HMM Hss Hzz VM Vs Vz Vt.
  pose proof (lequiv_wf_l _ _ _ Hll) as Hwl.
  pose proof (lconv_ty (eqty_wf_r ge_typeof HMM) Hll) as HM'.
  (* [s' : M'[0] @ l'] *)
  pose proof (eqtm_wf_r ge_typeof Hss) as Hs'0.
  assert (H0 : [ G ; Γ ⊢g zero : tyNat @ lzero ])
    by (apply wf_zero; [exact ge_notV | rewrite ge_typeof; eapply ctx_of_tm, Hs'0]).
  pose proof (eqty_single ge_typeof HMM H0) as HM0.
  assert (Hs' : [ G ; Γ ⊢g s' : M'[lsingle zero] @ l' ]).
  { eapply wf_lconv; [|apply lequiv_sym, Hll].
    eapply wf_conv; [exact Hs'0 | rewrite ge_typeof; now apply eqty_sym]. }
  (* [z'] in [Γ, Nat, M' @ l'] at [M'[↑]] *)
  assert (HΓ' : [ G ; Γ ,, tyNat @ lzero ,, M' @ l' ⊢g ])
    by (apply ext_wf_g; [exact HM' | exact (lequiv_wf_r _ _ _ Hll)]).
  pose proof (stab_tm ge_typeof HMM Hll HΓ' (eqtm_wf_r ge_typeof Hzz)) as Hz'1.
  pose proof (eqty_subst ge_typeof HMM (lsub_wf_lsucc ge_typeof ge_notV HΓ')) as Hsucc.
  assert (Hz' : [ G ; Γ ,, tyNat @ lzero ,, M' @ l' ⊢g z' : M'[lsucc] @ l' ]).
  { eapply wf_lconv; [|apply lequiv_sym, Hll].
    eapply wf_conv; [exact Hz'1 | rewrite ge_typeof; now apply eqty_sym]. }
  exact (V_natrec Hwl Hll HM HM' (eqtm_wf_l ge_typeof Hss) Hs' (eqtm_wf_l ge_typeof Hzz) Hz'
           VM Vs Vz Vt).
Qed.

Lemma ft_lam {l l' A B t} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ,, A @ l ⊢g t : B @ l' ] -> VTy G Γ A A l -> VTm G (Γ ,, A @ l) t t B l' ->
  VTm G Γ (lam l l' A t) (lam l l' A t) (tyPi l l' A B) (lmax l l').
Proof.
  intros Hw Hw' Ht VA Vt.
  exact (V_lam Hw Hw' (lequiv_refl _ _ Hw) (lequiv_refl _ _ Hw') (wf_tm_ty ge_typeof Ht) Ht Ht VA
           (VTm_ty Vt) Vt).
Qed.

Lemma ft_lam_eq {l1 l2 l3 l4 A A' B t t'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ,, A @ l1 ⊢g t ≅ t' : B @ l2 ] -> VTy G Γ A A' l1 -> VTm G (Γ ,, A @ l1) t t' B l2 ->
  VTm G Γ (lam l1 l2 A t) (lam l3 l4 A' t') (tyPi l1 l2 A B) (lmax l1 l2).
Proof.
  intros H13 H24 Htt VA Vt.
  exact (V_lam (lequiv_wf_l _ _ _ H13) (lequiv_wf_l _ _ _ H24) (lequiv_sym _ _ _ H13) (lequiv_sym _ _ _ H24)
           (eqtm_wf_ty ge_typeof Htt) (eqtm_wf_l ge_typeof Htt) (eqtm_wf_r ge_typeof Htt) VA
           (VTm_ty Vt) Vt).
Qed.

Lemma ft_app {l l' A B t s} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ,, A @ l ⊢g B @ l' ] -> VTy G Γ A A l -> VTy G (Γ ,, A @ l) B B l' ->
  VTm G Γ t t (tyPi l l' A B) (lmax l l') -> VTm G Γ s s A l ->
  VTm G Γ (app t l l' A B s) (app t l l' A B s) B[lsingle s] l'.
Proof.
  intros Hw Hw' HB VA VB Vt Vs.
  exact (V_app Hw Hw' (lequiv_refl _ _ Hw) (lequiv_refl _ _ Hw') HB VA VB Vt Vs).
Qed.

Lemma ft_app_eq {l1 l2 l3 l4 A A' B B' t t' s s'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ,, A @ l1 ⊢g B ≅ B' @ l2 ] -> VTy G Γ A A' l1 -> VTy G (Γ ,, A @ l1) B B' l2 ->
  VTm G Γ t t' (tyPi l1 l2 A B) (lmax l1 l2) -> VTm G Γ s s' A l1 ->
  VTm G Γ (app t l1 l2 A B s) (app t' l3 l4 A' B' s') B[lsingle s] l2.
Proof.
  intros H13 H24 HBB VA VB Vt Vs.
  exact (V_app (lequiv_wf_l _ _ _ H13) (lequiv_wf_l _ _ _ H24) (lequiv_sym _ _ _ H13) (lequiv_sym _ _ _ H24)
           (eqty_wf_l ge_typeof HBB) VA VB Vt Vs).
Qed.

End Wrappers.

(** ** The theorem *)

Ltac ft_prep :=
  subst; rewrite ?ge_typeof in *;
  repeat match goal with H : ge_layer = ge_layer -> _ |- _ => specialize (H eq_refl) end.

Ltac ft_case :=
  first
  [ exact I | eassumption
  | solve [eapply V_var; eassumption] | solve [eapply V_nat] | solve [eapply V_zero]
  | solve [eapply V_code_nat] | solve [eapply V_succ; eassumption]
  | solve [eapply V_El_nat] | solve [eapply V_El_U; eassumption]
  | solve [eapply V_El_pi; eassumption]
  | solve [eapply VTy_sym; eassumption] | solve [eapply VTy_trans; eassumption]
  | solve [eapply VTm_sym; eassumption] | solve [eapply VTm_trans; eassumption]
  | solve [eapply VTy_lconv; eassumption] | solve [eapply VTm_lconv; eassumption]
  | solve [eapply VTm_conv; eassumption]
  | solve [eapply ft_U; eassumption] | solve [eapply ft_U_eq; eassumption]
  | solve [eapply ft_El; eassumption] | solve [eapply ft_El_eq; eassumption]
  | solve [eapply ft_code_U; eassumption] | solve [eapply ft_code_U_eq; eassumption]
  | solve [eapply ft_pi; eassumption] | solve [eapply ft_pi_eq; eassumption]
  | solve [eapply ft_code_pi; eassumption] | solve [eapply ft_code_pi_eq; eassumption]
  | solve [eapply ft_natrec; eassumption] | solve [eapply ft_natrec_eq; eassumption]
  | solve [eapply ft_lam; eassumption] | solve [eapply ft_lam_eq; eassumption]
  | solve [eapply ft_app; eassumption] | solve [eapply ft_app_eq; eassumption]
  | solve [eapply V_natrec_zero; eassumption] | solve [eapply V_natrec_succ; eassumption]
  | solve [eapply V_beta; eassumption] | solve [eapply V_eta; eassumption] ].

(** M2 transition (M2_DESIGN.md): until the layered relation is in place,
    the theorem is stated for the P layer and global contexts that bind
    context variables only.  The new rules then never apply: [□], [box]
    and [letbox] live at M, and [U^δ]/[u^δ] need a type/term binding. *)
Definition ctx_only (G : gctx) : Prop := forall n D, in_gctx (gΨ G) n D -> D = gdCtx.

Theorem fundamental : ge_layer = lD ->
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> True) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> i = ge_layer -> ctx_only G -> VTy G Γ T T l) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> i = ge_layer -> ctx_only G -> VTm G Γ t t T l) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> i = ge_layer -> ctx_only G -> VTy G Γ T T' l) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> i = ge_layer -> ctx_only G ->
     VTm G Γ t t' T l) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> True).
Proof.
  intros Hgl.
  apply typing_mut; intros; try exact I;
    try match goal with H : lM = ge_layer |- _ => rewrite Hgl in H; discriminate end;
    try match goal with
        | Hc : ctx_only _, Hin : in_gctx _ _ (gdTm _ _ _ _) |- _ => discriminate (Hc _ _ Hin)
        | Hc : ctx_only _, Hin : in_gctx _ _ (gdTy _ _ _) |- _ => discriminate (Hc _ _ Hin)
        end;
    ft_prep;
    repeat match goal with Hc : ctx_only ?G, IH : ctx_only ?G -> _ |- _ => specialize (IH Hc) end;
    ft_case.
Qed.

End Fundamental.
