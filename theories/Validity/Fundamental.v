(** * The cases of the fundamental theorem

    Each rule is closed by its validity lemma; the wrappers below derive
    the extra typing premises of those lemmas (presupposition, stability)
    from the rule's own, and the tactics lift a case to global weakenings.
    The theorem itself quantifies over related global substitutions:
    [FundamentalS] (layers C and P) and [FundamentalM] (layer M). *)
From DeLaM.Validity Require Export WElim.

Section Fundamental.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

(** ** Rule-shaped wrappers *)

Section Wrappers.
Context {G : gctx} {Γ : ctx}.

Lemma ft_U {l} : lwf (gL G) l -> VTy G Γ (tyU l) (tyU l) (lsuc l).
Proof. intros Hwl; exact (V_U Hwl (lequiv_refl _ _ Hwl)). Qed.
Lemma ft_U_eq {l l'} : lequiv (gL G) l l' -> VTy G Γ (tyU l) (tyU l') (lsuc l).
Proof. intros Hl; exact (V_U (lequiv_wf_l _ _ _ Hl) Hl). Qed.

Lemma ft_unit {l} : lwf (gL G) l -> VTy G Γ (tyUnit l) (tyUnit l) l.
Proof. intros Hwl; exact (V_unit Hwl (lequiv_refl _ _ Hwl)). Qed.
Lemma ft_unit_eq {l l'} : lequiv (gL G) l l' -> VTy G Γ (tyUnit l) (tyUnit l') l.
Proof. intros Hl; exact (V_unit (lequiv_wf_l _ _ _ Hl) Hl). Qed.
Lemma ft_code_unit {l} : lwf (gL G) l -> VTm G Γ (tmUnit l) (tmUnit l) (tyU l) (lsuc l).
Proof. intros Hwl; exact (V_code_unit Hwl (lequiv_refl _ _ Hwl)). Qed.
Lemma ft_code_unit_eq {l l'} : lequiv (gL G) l l' -> VTm G Γ (tmUnit l) (tmUnit l') (tyU l) (lsuc l).
Proof. intros Hl; exact (V_code_unit (lequiv_wf_l _ _ _ Hl) Hl). Qed.
Lemma ft_triv {l} : lwf (gL G) l -> VTm G Γ (tmTriv l) (tmTriv l) (tyUnit l) l.
Proof. intros Hwl; exact (V_triv Hwl (lequiv_refl _ _ Hwl)). Qed.

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
  [ G ; Γ ,, A @ l ⊢g B @ l' ] -> VTyG G Γ A A l -> VTyG G (Γ ,, A @ l) B B l' ->
  VTy G Γ (tyPi l l' A B) (tyPi l l' A B) (lmax l l').
Proof.
  intros Hw Hw' HB VA VB. exact (V_pi Hw Hw' (lequiv_refl _ _ Hw) (lequiv_refl _ _ Hw') HB VA VB).
Qed.

Lemma ft_pi_eq {l1 l2 l3 l4 A A' B B'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢g A ≅ A' @ l1 ] -> [ G ; Γ ,, A @ l1 ⊢g B ≅ B' @ l2 ] ->
  VTyG G Γ A A' l1 -> VTyG G (Γ ,, A @ l1) B B' l2 ->
  VTy G Γ (tyPi l1 l2 A B) (tyPi l3 l4 A' B') (lmax l1 l2).
Proof.
  intros H13 H24 HAA HBB VA VB.
  pose proof (lequiv_wf_l _ _ _ H13) as Hw1.
  exact (V_pi Hw1 (lequiv_wf_l _ _ _ H24) (lequiv_sym _ _ _ H13) (lequiv_sym _ _ _ H24)
           (eqty_wf_l ge_typeof HBB) VA VB).
Qed.

Lemma ft_code_pi {l l' s t} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢g s : tyU l @ lsuc l ] -> [ G ; Γ ,, tyEl l s @ l ⊢g t : tyU l' @ lsuc l' ] ->
  VTmG G Γ s s (tyU l) (lsuc l) -> VTmG G (Γ ,, tyEl l s @ l) t t (tyU l') (lsuc l') ->
  VTm G Γ (tmPi l l' s t) (tmPi l l' s t) (tyU (lmax l l')) (lsuc (lmax l l')).
Proof.
  intros Hw Hw' Hs Ht Vs Vt.
  exact (V_code_pi Hw Hw' (lequiv_refl _ _ Hw) (lequiv_refl _ _ Hw') Hs Ht Vs Vt).
Qed.

Lemma ft_code_pi_eq {l1 l2 l3 l4 s s' t t'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢g s : tyU l1 @ lsuc l1 ] -> [ G ; Γ ⊢g s ≅ s' : tyU l1 @ lsuc l1 ] ->
  [ G ; Γ ,, tyEl l1 s @ l1 ⊢g t ≅ t' : tyU l2 @ lsuc l2 ] ->
  VTmG G Γ s s' (tyU l1) (lsuc l1) -> VTmG G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) (lsuc l2) ->
  VTm G Γ (tmPi l1 l2 s t) (tmPi l3 l4 s' t') (tyU (lmax l1 l2)) (lsuc (lmax l1 l2)).
Proof.
  intros H13 H24 Hs Hss Htt Vs Vt.
  exact (V_code_pi (lequiv_wf_l _ _ _ H13) (lequiv_wf_l _ _ _ H24) H13 H24 Hs
           (eqtm_wf_l ge_typeof Htt) Vs Vt).
Qed.

Lemma ft_natrec {l M s z t} : lwf (gL G) l ->
  [ G ; Γ ,, tyNat @ lzero ⊢g M @ l ] -> [ G ; Γ ⊢g s : M[lsingle zero] @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢g z : M[lsucc] @ l ] ->
  VTy G (Γ ,, tyNat @ lzero) M M l -> VTm G Γ s s M[lsingle zero] l ->
  VTm G (Γ ,, tyNat @ lzero ,, M @ l) z z M[lsucc] l -> VTm G Γ t t tyNat lzero ->
  VTm G Γ (natrec l M s z t) (natrec l M s z t) M[lsingle t] l.
Proof.
  intros Hwl HM Hs Hz VM Vs Vz Vt.
  exact (V_natrec Hwl (lequiv_refl _ _ Hwl) HM Hs Hz VM Vs Vz Vt).
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
  exact (V_natrec (lequiv_wf_l _ _ _ Hll) Hll HM (eqtm_wf_l ge_typeof Hss) (eqtm_wf_l ge_typeof Hzz)
           VM Vs Vz Vt).
Qed.

Lemma ft_lam {l l' A B t} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ,, A @ l ⊢g t : B @ l' ] -> VTyG G Γ A A l -> VTmG G (Γ ,, A @ l) t t B l' ->
  VTm G Γ (lam l l' A t) (lam l l' A t) (tyPi l l' A B) (lmax l l').
Proof.
  intros Hw Hw' Ht VA Vt.
  exact (V_lam Hw Hw' (lequiv_refl _ _ Hw) (lequiv_refl _ _ Hw') (wf_tm_ty ge_typeof Ht) Ht VA
           (VTmG_ty Vt) Vt).
Qed.

Lemma ft_lam_eq {l1 l2 l3 l4 A A' B t t'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ,, A @ l1 ⊢g t ≅ t' : B @ l2 ] -> VTyG G Γ A A' l1 -> VTmG G (Γ ,, A @ l1) t t' B l2 ->
  VTm G Γ (lam l1 l2 A t) (lam l3 l4 A' t') (tyPi l1 l2 A B) (lmax l1 l2).
Proof.
  intros H13 H24 Htt VA Vt.
  exact (V_lam (lequiv_wf_l _ _ _ H13) (lequiv_wf_l _ _ _ H24) (lequiv_sym _ _ _ H13) (lequiv_sym _ _ _ H24)
           (eqtm_wf_ty ge_typeof Htt) (eqtm_wf_l ge_typeof Htt) VA
           (VTmG_ty Vt) Vt).
Qed.

Lemma ft_app {l l' A B t s} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ,, A @ l ⊢g B @ l' ] -> VTyG G Γ A A l -> VTyG G (Γ ,, A @ l) B B l' ->
  VTm G Γ t t (tyPi l l' A B) (lmax l l') -> VTm G Γ s s A l ->
  VTm G Γ (app t l l' A B s) (app t l l' A B s) B[lsingle s] l'.
Proof.
  intros Hw Hw' HB VA VB Vt Vs.
  exact (V_app Hw Hw' (lequiv_refl _ _ Hw) (lequiv_refl _ _ Hw') HB VA VB Vt Vs).
Qed.

Lemma ft_app_eq {l1 l2 l3 l4 A A' B B' t t' s s'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ,, A @ l1 ⊢g B ≅ B' @ l2 ] -> VTyG G Γ A A' l1 -> VTyG G (Γ ,, A @ l1) B B' l2 ->
  VTm G Γ t t' (tyPi l1 l2 A B) (lmax l1 l2) -> VTm G Γ s s' A l1 ->
  VTm G Γ (app t l1 l2 A B s) (app t' l3 l4 A' B' s') B[lsingle s] l2.
Proof.
  intros H13 H24 HBB VA VB Vt Vs.
  exact (V_app (lequiv_wf_l _ _ _ H13) (lequiv_wf_l _ _ _ H24) (lequiv_sym _ _ _ H13) (lequiv_sym _ _ _ H24)
           (eqty_wf_l ge_typeof HBB) VA VB Vt Vs).
Qed.

(** Dependent pairs (M8). *)
Lemma ft_sig {l l' A B} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ,, A @ l ⊢g B @ l' ] -> VTyG G Γ A A l -> VTyG G (Γ ,, A @ l) B B l' ->
  VTy G Γ (tySig l l' A B) (tySig l l' A B) (lmax l l').
Proof.
  intros Hw Hw' HB VA VB. exact (V_sig Hw Hw' (lequiv_refl _ _ Hw) (lequiv_refl _ _ Hw') HB VA VB).
Qed.

Lemma ft_sig_eq {l1 l2 l3 l4 A A' B B'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢g A ≅ A' @ l1 ] -> [ G ; Γ ,, A @ l1 ⊢g B ≅ B' @ l2 ] ->
  VTyG G Γ A A' l1 -> VTyG G (Γ ,, A @ l1) B B' l2 ->
  VTy G Γ (tySig l1 l2 A B) (tySig l3 l4 A' B') (lmax l1 l2).
Proof.
  intros H13 H24 HAA HBB VA VB.
  exact (V_sig (lequiv_wf_l _ _ _ H13) (lequiv_wf_l _ _ _ H24) (lequiv_sym _ _ _ H13) (lequiv_sym _ _ _ H24)
           (eqty_wf_l ge_typeof HBB) VA VB).
Qed.

Lemma ft_code_sig {l l' s t} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢g s : tyU l @ lsuc l ] -> [ G ; Γ ,, tyEl l s @ l ⊢g t : tyU l' @ lsuc l' ] ->
  VTmG G Γ s s (tyU l) (lsuc l) -> VTmG G (Γ ,, tyEl l s @ l) t t (tyU l') (lsuc l') ->
  VTm G Γ (tmSig l l' s t) (tmSig l l' s t) (tyU (lmax l l')) (lsuc (lmax l l')).
Proof.
  intros Hw Hw' Hs Ht Vs Vt.
  exact (V_code_sig Hw Hw' (lequiv_refl _ _ Hw) (lequiv_refl _ _ Hw') Hs Ht Vs Vt).
Qed.

Lemma ft_code_sig_eq {l1 l2 l3 l4 s s' t t'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢g s : tyU l1 @ lsuc l1 ] -> [ G ; Γ ⊢g s ≅ s' : tyU l1 @ lsuc l1 ] ->
  [ G ; Γ ,, tyEl l1 s @ l1 ⊢g t ≅ t' : tyU l2 @ lsuc l2 ] ->
  VTmG G Γ s s' (tyU l1) (lsuc l1) -> VTmG G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) (lsuc l2) ->
  VTm G Γ (tmSig l1 l2 s t) (tmSig l3 l4 s' t') (tyU (lmax l1 l2)) (lsuc (lmax l1 l2)).
Proof.
  intros H13 H24 Hs Hss Htt Vs Vt.
  exact (V_code_sig (lequiv_wf_l _ _ _ H13) (lequiv_wf_l _ _ _ H24) H13 H24 Hs
           (eqtm_wf_l ge_typeof Htt) Vs Vt).
Qed.

Lemma ft_pair {l l' A B a b} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ,, A @ l ⊢g B @ l' ] -> VTyG G Γ A A l -> VTyG G (Γ ,, A @ l) B B l' ->
  VTmG G Γ a a A l -> VTmG G Γ b b B[lsingle a] l' ->
  VTm G Γ (tmPair l l' A B a b) (tmPair l l' A B a b) (tySig l l' A B) (lmax l l').
Proof.
  intros Hw Hw' HB VA VB Va Vb.
  exact (V_pair Hw Hw' (lequiv_refl _ _ Hw) (lequiv_refl _ _ Hw') HB VA VB Va Vb).
Qed.

Lemma ft_pair_eq {l1 l2 l3 l4 A A' B B' a a' b b'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ,, A @ l1 ⊢g B ≅ B' @ l2 ] -> VTyG G Γ A A' l1 -> VTyG G (Γ ,, A @ l1) B B' l2 ->
  VTmG G Γ a a' A l1 -> VTmG G Γ b b' B[lsingle a] l2 ->
  VTm G Γ (tmPair l1 l2 A B a b) (tmPair l3 l4 A' B' a' b') (tySig l1 l2 A B) (lmax l1 l2).
Proof.
  intros H13 H24 HBB VA VB Va Vb.
  exact (V_pair (lequiv_wf_l _ _ _ H13) (lequiv_wf_l _ _ _ H24) (lequiv_sym _ _ _ H13) (lequiv_sym _ _ _ H24)
           (eqty_wf_l ge_typeof HBB) VA VB Va Vb).
Qed.

Lemma ft_fst {l l' A B p} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ,, A @ l ⊢g B @ l' ] -> VTyG G Γ A A l -> VTyG G (Γ ,, A @ l) B B l' ->
  VTm G Γ p p (tySig l l' A B) (lmax l l') ->
  VTm G Γ (tmFst l l' A B p) (tmFst l l' A B p) A l.
Proof.
  intros Hw Hw' HB VA VB Vp.
  exact (V_fst Hw Hw' (lequiv_refl _ _ Hw) (lequiv_refl _ _ Hw') HB VA VB Vp).
Qed.

Lemma ft_fst_eq {l1 l2 l3 l4 A A' B B' p p'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ,, A @ l1 ⊢g B ≅ B' @ l2 ] -> VTyG G Γ A A' l1 -> VTyG G (Γ ,, A @ l1) B B' l2 ->
  VTm G Γ p p' (tySig l1 l2 A B) (lmax l1 l2) ->
  VTm G Γ (tmFst l1 l2 A B p) (tmFst l3 l4 A' B' p') A l1.
Proof.
  intros H13 H24 HBB VA VB Vp.
  exact (V_fst (lequiv_wf_l _ _ _ H13) (lequiv_wf_l _ _ _ H24) (lequiv_sym _ _ _ H13) (lequiv_sym _ _ _ H24)
           (eqty_wf_l ge_typeof HBB) VA VB Vp).
Qed.

Lemma ft_snd {l l' A B p} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ,, A @ l ⊢g B @ l' ] -> VTyG G Γ A A l -> VTyG G (Γ ,, A @ l) B B l' ->
  VTm G Γ p p (tySig l l' A B) (lmax l l') ->
  VTm G Γ (tmSnd l l' A B p) (tmSnd l l' A B p) B[lsingle (tmFst l l' A B p)] l'.
Proof.
  intros Hw Hw' HB VA VB Vp.
  exact (V_snd Hw Hw' (lequiv_refl _ _ Hw) (lequiv_refl _ _ Hw') HB VA VB Vp).
Qed.

Lemma ft_snd_eq {l1 l2 l3 l4 A A' B B' p p'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ,, A @ l1 ⊢g B ≅ B' @ l2 ] -> VTyG G Γ A A' l1 -> VTyG G (Γ ,, A @ l1) B B' l2 ->
  VTm G Γ p p' (tySig l1 l2 A B) (lmax l1 l2) ->
  VTm G Γ (tmSnd l1 l2 A B p) (tmSnd l3 l4 A' B' p') B[lsingle (tmFst l1 l2 A B p)] l2.
Proof.
  intros H13 H24 HBB VA VB Vp.
  exact (V_snd (lequiv_wf_l _ _ _ H13) (lequiv_wf_l _ _ _ H24) (lequiv_sym _ _ _ H13) (lequiv_sym _ _ _ H24)
           (eqty_wf_l ge_typeof HBB) VA VB Vp).
Qed.

End Wrappers.

End Fundamental.

(** ** The theorem *)

Ltac ft_prep :=
  subst; cbn [typeof] in *;
  repeat match goal with H : ?x = ?x -> _ |- _ => specialize (H eq_refl) end.

Ltac ft_case :=
  first
  [ exact I | eassumption
  | solve [simple eapply V_var; eassumption] | solve [simple eapply V_nat] | solve [simple eapply V_zero]
  | solve [simple eapply V_code_nat] | solve [simple eapply V_succ; eassumption]
  | solve [simple eapply V_El_nat] | solve [simple eapply V_El_U; eassumption]
  | solve [simple eapply V_El_pi; eassumption]
  | solve [simple eapply VTy_sym; eassumption] | solve [simple eapply VTy_trans; eassumption]
  | solve [simple eapply VTm_sym; eassumption] | solve [simple eapply VTm_trans; eassumption]
  | solve [simple eapply VTy_lconv; eassumption] | solve [simple eapply VTm_lconv; eassumption]
  | solve [simple eapply VTm_conv; eassumption]
  | solve [simple eapply ft_U; eassumption] | solve [simple eapply ft_U_eq; eassumption]
  | solve [simple eapply ft_El; eassumption] | solve [simple eapply ft_El_eq; eassumption]
  | solve [simple eapply ft_code_U; eassumption] | solve [simple eapply ft_code_U_eq; eassumption]
  | solve [simple eapply ft_pi; eassumption] | solve [simple eapply ft_pi_eq; eassumption]
  | solve [simple eapply ft_code_pi; eassumption] | solve [simple eapply ft_code_pi_eq; eassumption]
  | solve [simple eapply ft_natrec; eassumption] | solve [simple eapply ft_natrec_eq; eassumption]
  | solve [simple eapply ft_lam; eassumption] | solve [simple eapply ft_lam_eq; eassumption]
  | solve [simple eapply ft_app; eassumption] | solve [simple eapply ft_app_eq; eassumption]
  | solve [simple eapply V_natrec_zero; eassumption] | solve [simple eapply V_natrec_succ; eassumption]
  | solve [simple eapply V_beta; eassumption] | solve [simple eapply V_eta; eassumption]
  (* dependent pairs (M8) *)
  | solve [simple eapply ft_sig; eassumption] | solve [simple eapply ft_sig_eq; eassumption]
  | solve [simple eapply ft_code_sig; eassumption] | solve [simple eapply ft_code_sig_eq; eassumption]
  | solve [simple eapply ft_pair; eassumption] | solve [simple eapply ft_pair_eq; eassumption]
  | solve [simple eapply ft_fst; eassumption] | solve [simple eapply ft_fst_eq; eassumption]
  | solve [simple eapply ft_snd; eassumption] | solve [simple eapply ft_snd_eq; eassumption]
  | solve [simple eapply V_fst_beta; eassumption] | solve [simple eapply V_snd_beta; eassumption]
  | solve [simple eapply V_sig_eta; eassumption] | solve [simple eapply V_El_sig; eassumption]
  (* the unit type (M8c) *)
  | solve [simple eapply ft_unit; eassumption] | solve [simple eapply ft_unit_eq; eassumption]
  | solve [simple eapply ft_code_unit; eassumption] | solve [simple eapply ft_code_unit_eq; eassumption]
  | solve [simple eapply ft_triv; eassumption] | solve [simple eapply V_El_unit; eassumption]
  | solve [simple eapply V_unit_eta; eassumption] ].

(** ** Lifting to global weakenings

    Each case is proved at an arbitrary global weakening [γ : G' ≤ G] of
    its rule's global context: the hypotheses at [G] are weakened, [⟦γ⟧]
    is pushed through the syntax, and the case's lemma applies at [G']. *)

Ltac gl_weaken :=
  match goal with Hγ : gwk_ok ?γ ?G' ?G, HG' : [ ⊢ ?G' ] |- _ =>
    repeat match goal with
    | H : VTyG G _ _ _ _ |- _ =>
        pose proof (VTyG_gwk H Hγ); pose proof (VTyG_loc (VTyG_gwk H Hγ)); clear H
    | H : VTmG G _ _ _ _ _ |- _ =>
        pose proof (VTmG_gwk H Hγ); pose proof (VTmG_loc (VTmG_gwk H Hγ)); clear H
    | H : wf_ctx G _ _ |- _ => pose proof (gwa_ctx Hγ HG' H); clear H
    | H : wf_ty G _ _ _ _ |- _ => pose proof (gwa_ty Hγ HG' H); clear H
    | H : wf_tm G _ _ _ _ _ |- _ => pose proof (gwa_tm Hγ HG' H); clear H
    | H : eq_ty G _ _ _ _ _ |- _ => pose proof (gwa_eqty Hγ HG' H); clear H
    | H : eq_tm G _ _ _ _ _ _ |- _ => pose proof (gwa_eqtm Hγ HG' H); clear H
    | H : in_ctx ?Γ0 _ _ _ |- _ =>
        lazymatch Γ0 with gwa _ _ => fail | _ => pose proof (in_ctx_gwa _ _ _ _ γ H); clear H end
    | H : lequiv (gL G) _ _ |- _ => apply (lequiv_weaken _ _ _ _ (proj1 Hγ)) in H
    | H : lwf (gL G) _ |- _ => apply (lwf_weaken _ _ _ (proj1 Hγ)) in H
    end
  end.

(** [gl_push]: generated by [tools/gen_push.py] from its lemma list. *)
Ltac gl_push_at h k := lazymatch h with
  | @subst => first [k gwa_subst_ty | k gwa_subst]
  | @lsingle => k gwa_lsingle
  | @lsingle2 => k gwa_lsingle2
  | @lsingle3 => k gwa_lsingle3
  | @lsucc => k gwa_lsucc
  | @ren => first [k gwa_ren | k gwa_ren_ty]
  | @tyNat => k gwa_tyNat
  | @tyPi => k gwa_tyPi
  | @tyU => k gwa_tyU
  | @tyEl => k gwa_tyEl
  | @var => k gwa_var
  | @zero => k gwa_zero
  | @succ => k gwa_succ
  | @tmNat => k gwa_tmNat
  | @tmU => k gwa_tmU
  | @tmPi => k gwa_tmPi
  | @lam => k gwa_lam
  | @app => k gwa_app
  | @natrec => k gwa_natrec
  | @cext => k gwa_cext
  | @tySig => k gwa_tySig
  | @tySum => k gwa_tySum
  | @tyW => k gwa_tyW
  | @tmSup => k gwa_sup
  | @tmElimW => k gwa_elimW
  | @wIH => k gwa_wIH
  | @tmInl => k gwa_inl
  | @tmInr => k gwa_inr
  | @tmCase => k gwa_case
  | @tmSig => k gwa_tmSig
  | @tmPair => k gwa_pair
  | @tmFst => k gwa_fst
  | @tmSnd => k gwa_snd
  | @tyUnit => k gwa_tyUnit
  | @tmUnit => k gwa_tmUnit
  | @tmSEmpty => k gwa_tmSEmpty
  | @tmEmpty => k gwa_tmEmpty
  | @tmSum => k gwa_tmSum
  | @tmW => k gwa_tmW
  | @tmTriv => k gwa_triv
  | @tySEq => k gwa_tySEq
  | @tySEmpty => k gwa_tySEmpty
  | @tyEmpty => k gwa_tyEmpty
  | @srefl => k gwa_srefl
  | @elimSEmpty => k gwa_elimSEmpty
  | @elimEmpty => k gwa_elimEmpty
  | @tyId => k gwa_tyId
  | @tmRefl => k gwa_refl
  | @tmId => k gwa_tmId
  | @tmSEq => k gwa_tmSEq
  | @tmJ => k gwa_J
  end.
Ltac gl_push := repeat match goal with
  | |- context [@gwa _ _ _ ?t] => let h := head_of t in gl_push_at h ltac:(fun L => rewrite L)
  | H : context [@gwa _ _ _ ?t] |- _ => let h := head_of t in gl_push_at h ltac:(fun L => rewrite L in H)
  end.

(** P-derivations are validated at an instance of any layer [≥ P]: their
    typing hypotheses are lifted to the instance's layer. *)
Ltac gl_liftD :=
  repeat match goal with
  | H : wf_ctx _ lD _ |- _ => pose proof (lift_ctx H ge_lle_D); clear H
  | H : wf_ty _ lD _ _ _ |- _ => pose proof (lift_ty H ge_lle_D); clear H
  | H : wf_tm _ lD _ _ _ _ |- _ => pose proof (lift_tm H ge_lle_D); clear H
  | H : eq_ty _ lD _ _ _ _ |- _ => pose proof (lift_eqty H ge_lle_D); clear H
  | H : eq_tm _ lD _ _ _ _ _ |- _ => pose proof (lift_eqtm H ge_lle_D); clear H
  end.

Ltac gl_lift :=
  first [apply VTyG_intro | apply VTmG_intro]; intros ? ? ? ?; gl_weaken; gl_push; gl_liftD.
