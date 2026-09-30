(** * Validity of binary sums (M12_DESIGN.md, M12b)

    Formation of [+], the injections, [case] and its two β rules. The
    term relation at [+] is [SumRel]: a term reduces to an injection whose
    payload is related at its summand, or to a neutral. [case] steps to a
    branch at an injection, whose motive instance is converted along the
    injection (related to the scrutinee); at a neutral, [case] is neutral. *)
From DeLaM.Validity Require Export Empty.

(** ** Syntax: the branch types *)

Lemma caseb_inl_llift (M : ty) l l' A B d : LK nftm d ->
  (M⟨rlift ↑⟩[lsingle (tmInl l l' A⟨↑⟩ B⟨↑⟩ (var 0))])[llift d]
  = M[llift d]⟨rlift ↑⟩[lsingle (tmInl l l' A[d]⟨↑⟩ B[d]⟨↑⟩ (var 0))].
Proof.
  intros Hd. rewrite (single_subst_ty _ (lk_llift _ Hd)), liftshift_llift_ty, subst_inl, !shift_llift_ty,
    subst_var, llk_llift. reflexivity.
Qed.
Lemma caseb_inr_llift (M : ty) l l' A B d : LK nftm d ->
  (M⟨rlift ↑⟩[lsingle (tmInr l l' A⟨↑⟩ B⟨↑⟩ (var 0))])[llift d]
  = M[llift d]⟨rlift ↑⟩[lsingle (tmInr l l' A[d]⟨↑⟩ B[d]⟨↑⟩ (var 0))].
Proof.
  intros Hd. rewrite (single_subst_ty _ (lk_llift _ Hd)), liftshift_llift_ty, subst_inr, !shift_llift_ty,
    subst_var, llk_llift. reflexivity.
Qed.

Lemma caseb_inl_cons (M : ty) l l' A B d a : LK nftm d -> nfty A[d] -> nfty B[d] ->
  (M⟨rlift ↑⟩[lsingle (tmInl l l' A⟨↑⟩ B⟨↑⟩ (var 0))])[lcons d a] = M[lcons d (tmInl l l' A[d] B[d] a)].
Proof.
  intros Hd NA NB. rewrite <- (lift_single_ty _ _ a Hd), (caseb_inl_llift _ _ _ _ _ _ Hd).
  rewrite case_inl_single by assumption. apply lift_single_ty, Hd.
Qed.
Lemma caseb_inr_cons (M : ty) l l' A B d b : LK nftm d -> nfty A[d] -> nfty B[d] ->
  (M⟨rlift ↑⟩[lsingle (tmInr l l' A⟨↑⟩ B⟨↑⟩ (var 0))])[lcons d b] = M[lcons d (tmInr l l' A[d] B[d] b)].
Proof.
  intros Hd NA NB. rewrite <- (lift_single_ty _ _ b Hd), (caseb_inr_llift _ _ _ _ _ _ Hd).
  rewrite case_inr_single by assumption. apply lift_single_ty, Hd.
Qed.

Section Sum.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

Local Lemma convg {G Δ t t' T T' l} :
  [ G ; Δ ⊢g t ≅ t' : T' @ l ] -> [ G ; Δ ⊢g T ≅ T' @ l ] -> [ G ; Δ ⊢g t ≅ t' : T @ l ].
Proof. intros H HT. apply eqtm_conv with (T' := T'); [exact H | now rewrite ge_typeof]. Qed.

(** ** [case]'s reductions, typed *)

Lemma case_motive_conv {G Δ l1 l2 l3 A B M e e'} :
  [ G ; Δ ,, tySum l1 l2 A B @ lmax l1 l2 ⊢g M @ l3 ] ->
  [ G ; Δ ⊢g e ≅ e' : tySum l1 l2 A B @ lmax l1 l2 ] -> [ G ; Δ ⊢g M[lsingle e] ≅ M[lsingle e'] @ l3 ].
Proof.
  intros HM Hee. apply (wf_ty_func ge_typeof HM).
  apply (lsub_eq_single ge_typeof); [exact (eqtm_wf_l ge_typeof Hee) | exact (eqtm_wf_r ge_typeof Hee) | exact Hee].
Qed.

Lemma case_cong {G Δ l1 l2 l3 A B M c1 c2 e e'} :
  lwf (gL G) l1 -> lwf (gL G) l2 -> lwf (gL G) l3 ->
  [ G ; Δ ⊢g A @ l1 ] -> [ G ; Δ ⊢g B @ l2 ] ->
  [ G ; Δ ,, tySum l1 l2 A B @ lmax l1 l2 ⊢g M @ l3 ] ->
  [ G ; Δ ,, A @ l1 ⊢g c1 : M⟨rlift ↑⟩[lsingle (tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] @ l3 ] ->
  [ G ; Δ ,, B @ l2 ⊢g c2 : M⟨rlift ↑⟩[lsingle (tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] @ l3 ] ->
  [ G ; Δ ⊢g e ≅ e' : tySum l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Δ ⊢g tmCase l1 l2 l3 A B M c1 c2 e ≅ tmCase l1 l2 l3 A B M c1 c2 e' : M[lsingle e] @ l3 ].
Proof.
  intros Hw1 Hw2 Hw3 HA HB HM Hc1 Hc2 Hee.
  apply eqtm_case; first [exact ge_compt | now apply lequiv_refl | assumption | now apply eqty_refl
                         | now apply eqtm_refl].
Qed.

(** A scrutinee equal to an injection whose annotations are equivalent to
    the [case]'s: [case] is the branch at the payload. *)
Lemma case_inl_eq {G Δ l1 l2 l3 A B M c1 c2 e k1 k2 C D a} :
  lwf (gL G) l1 -> lwf (gL G) l2 -> lwf (gL G) l3 ->
  [ G ; Δ ⊢g A @ l1 ] -> [ G ; Δ ⊢g B @ l2 ] ->
  [ G ; Δ ,, tySum l1 l2 A B @ lmax l1 l2 ⊢g M @ l3 ] ->
  [ G ; Δ ,, A @ l1 ⊢g c1 : M⟨rlift ↑⟩[lsingle (tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] @ l3 ] ->
  [ G ; Δ ,, B @ l2 ⊢g c2 : M⟨rlift ↑⟩[lsingle (tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] @ l3 ] ->
  [ G ; Δ ⊢g e ≅ tmInl k1 k2 C D a : tySum l1 l2 A B @ lmax l1 l2 ] ->
  lequiv (gL G) k1 l1 -> lequiv (gL G) k2 l2 -> [ G ; Δ ⊢g A ≅ C @ l1 ] -> [ G ; Δ ⊢g B ≅ D @ l2 ] ->
  [ G ; Δ ⊢g a : A @ l1 ] ->
  [ G ; Δ ⊢g tmCase l1 l2 l3 A B M c1 c2 e ≅ c1[lsingle a] : M[lsingle e] @ l3 ].
Proof.
  intros Hw1 Hw2 Hw3 HA HB HM Hc1 Hc2 Hee Hk1 Hk2 HAC HBD Ha.
  assert (Hinl : [ G ; Δ ⊢g tmInl l1 l2 A B a ≅ tmInl k1 k2 C D a : tySum l1 l2 A B @ lmax l1 l2 ])
    by (apply eqtm_inl; [exact ge_compt | now apply lequiv_sym | now apply lequiv_sym | exact HAC | exact HBD
                        | now apply eqtm_refl]).
  assert (Her : [ G ; Δ ⊢g e ≅ tmInl l1 l2 A B a : tySum l1 l2 A B @ lmax l1 l2 ])
    by (eapply eqtm_trans; [exact Hee | now apply eqtm_sym]).
  pose proof (eqtm_case_inl _ _ _ _ _ _ _ _ _ _ _ _ ge_compt Hw1 Hw2 Hw3 HA HB HM Hc1 Hc2 Ha) as Hb.
  eapply eqtm_trans; [exact (case_cong Hw1 Hw2 Hw3 HA HB HM Hc1 Hc2 Her)|].
  eapply convg; [exact Hb | exact (case_motive_conv HM Her)].
Qed.

Lemma case_inr_eq {G Δ l1 l2 l3 A B M c1 c2 e k1 k2 C D b} :
  lwf (gL G) l1 -> lwf (gL G) l2 -> lwf (gL G) l3 ->
  [ G ; Δ ⊢g A @ l1 ] -> [ G ; Δ ⊢g B @ l2 ] ->
  [ G ; Δ ,, tySum l1 l2 A B @ lmax l1 l2 ⊢g M @ l3 ] ->
  [ G ; Δ ,, A @ l1 ⊢g c1 : M⟨rlift ↑⟩[lsingle (tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] @ l3 ] ->
  [ G ; Δ ,, B @ l2 ⊢g c2 : M⟨rlift ↑⟩[lsingle (tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] @ l3 ] ->
  [ G ; Δ ⊢g e ≅ tmInr k1 k2 C D b : tySum l1 l2 A B @ lmax l1 l2 ] ->
  lequiv (gL G) k1 l1 -> lequiv (gL G) k2 l2 -> [ G ; Δ ⊢g A ≅ C @ l1 ] -> [ G ; Δ ⊢g B ≅ D @ l2 ] ->
  [ G ; Δ ⊢g b : B @ l2 ] ->
  [ G ; Δ ⊢g tmCase l1 l2 l3 A B M c1 c2 e ≅ c2[lsingle b] : M[lsingle e] @ l3 ].
Proof.
  intros Hw1 Hw2 Hw3 HA HB HM Hc1 Hc2 Hee Hk1 Hk2 HAC HBD Hb0.
  assert (Hinr : [ G ; Δ ⊢g tmInr l1 l2 A B b ≅ tmInr k1 k2 C D b : tySum l1 l2 A B @ lmax l1 l2 ])
    by (apply eqtm_inr; [exact ge_compt | now apply lequiv_sym | now apply lequiv_sym | exact HAC | exact HBD
                        | now apply eqtm_refl]).
  assert (Her : [ G ; Δ ⊢g e ≅ tmInr l1 l2 A B b : tySum l1 l2 A B @ lmax l1 l2 ])
    by (eapply eqtm_trans; [exact Hee | now apply eqtm_sym]).
  pose proof (eqtm_case_inr _ _ _ _ _ _ _ _ _ _ _ _ ge_compt Hw1 Hw2 Hw3 HA HB HM Hc1 Hc2 Hb0) as Hb.
  eapply eqtm_trans; [exact (case_cong Hw1 Hw2 Hw3 HA HB HM Hc1 Hc2 Her)|].
  eapply convg; [exact Hb | exact (case_motive_conv HM Her)].
Qed.

(** ** Formation and the injections *)

Lemma LR_sum_here {G Δ l1 l2 l3 l4 A A' B B' RA RB} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Δ ⊢g A @ l1 ] -> [ G ; Δ ⊢ A ≈ A' @ l1 ] -> [ G ; Δ ⊢g B @ l2 ] -> [ G ; Δ ⊢ B ≈ B' @ l2 ] ->
  LogRel l1 G Δ A A' l1 RA -> LogRel l2 G Δ B B' l2 RB ->
  LogRel (lmax l1 l2) G Δ (tySum l1 l2 A B) (tySum l3 l4 A' B') (lmax l1 l2) (SumRel G Δ l1 l2 A B RA RB).
Proof.
  intros Hw1 Hw2 H13 H24 HA HAA HB HBB HRA HRB.
  pose proof (geq_ty_sound (geq_ty_sum H13 H24 HAA HBB)) as EV.
  destruct (LR_tm_per _ _ _ _ _ _ _ HRA) as [SyA TrA].
  destruct (LR_tm_per _ _ _ _ _ _ _ HRB) as [SyB TrB].
  eapply (LRsum _ _ _ _ _ _ _ l1 l2 l3 l4 A A' B B' RA RB).
  - apply lequiv_refl, lwf_max; assumption.
  - now apply lequiv_sym.
  - now apply lequiv_sym.
  - exact Hw1.
  - exact Hw2.
  - apply tyred_refl, (eqty_wf_l ge_typeof EV).
  - apply tyred_refl, (eqty_wf_r ge_typeof EV).
  - exact HA.
  - exact HAA.
  - exact HB.
  - exact HBB.
  - eapply cumul_up; [|exact HRA]. rewrite lmeasure_max; lia.
  - eapply cumul_up; [|exact HRB]. rewrite lmeasure_max; lia.
  - exact SyA.
  - exact TrA.
  - exact SyB.
  - exact TrB.
  - apply releq_refl.
Qed.

Lemma V_sum {G Γ l1 l2 l3 l4 A A' B B'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  VTy G Γ A A' l1 -> VTy G Γ B B' l2 -> VTy G Γ (tySum l1 l2 A B) (tySum l3 l4 A' B') (lmax l1 l2).
Proof.
  intros Hw1 Hw2 H13 H24 VA VB Δ d d' Hd. push_subst.
  destruct (VA _ _ _ Hd) as [RA HRA]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HA & _ & EA).
  destruct (VB _ _ _ Hd) as [RB HRB]. destruct (escape_ty _ _ _ _ _ _ _ _ HRB) as (HB & _ & EB).
  eexists; exact (LR_sum_here Hw1 Hw2 H13 H24 HA EA HB EB HRA HRB).
Qed.

Lemma V_inl {G Γ l1 l2 l3 l4 A A' B B' a a'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  VTy G Γ A A' l1 -> VTy G Γ B B' l2 -> VTm G Γ a a' A l1 ->
  VTm G Γ (tmInl l1 l2 A B a) (tmInl l3 l4 A' B' a') (tySum l1 l2 A B) (lmax l1 l2).
Proof.
  intros Hw1 Hw2 H13 H24 VA VB Va Δ d d' Hd. push_subst.
  destruct (VTy_refl_l VA _ _ _ Hd) as [RA HRA]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HA & _ & EAA).
  destruct (VTy_refl_l VB _ _ _ Hd) as [RB HRB]. destruct (escape_ty _ _ _ _ _ _ _ _ HRB) as (HB & _ & EBB).
  destruct (VA _ _ _ Hd) as [RA' HRA']. destruct (escape_ty _ _ _ _ _ _ _ _ HRA') as (_ & _ & EA).
  destruct (VB _ _ _ Hd) as [RB' HRB']. destruct (escape_ty _ _ _ _ _ _ _ _ HRB') as (_ & _ & EB).
  pose proof (Va _ _ _ Hd) as Xa. pose proof (LRtm_geq Xa) as Ea.
  pose proof (geq_tm_sound (geq_tm_inl H13 H24 EA EB Ea)) as Dinl.
  eapply LRtm_of; [exact (LR_sum_here Hw1 Hw2 (lequiv_refl _ _ Hw1) (lequiv_refl _ _ Hw2) HA EAA HB EBB HRA HRB)|].
  exists (tmInl l1 l2 A[d] B[d] a[d]), (tmInl l3 l4 A'[d'] B'[d'] a'[d']).
  refine (conj (tmred_refl _ _ _ (eqtm_wf_l ge_typeof Dinl))
           (conj (tmred_refl _ _ _ (eqtm_wf_r ge_typeof Dinl)) (conj (geq_tm_inl H13 H24 EA EB Ea) _))).
  apply sumnf_inl;
    [ now apply lequiv_refl | now apply lequiv_refl | now apply lequiv_sym | now apply lequiv_sym
    | exact (geq_ty_trans EA (geq_ty_sym EA)) | exact EA
    | exact (geq_ty_trans EB (geq_ty_sym EB)) | exact EB
    | exact (LRtm_inv HRA Xa) ].
Qed.

Lemma V_inr {G Γ l1 l2 l3 l4 A A' B B' b b'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  VTy G Γ A A' l1 -> VTy G Γ B B' l2 -> VTm G Γ b b' B l2 ->
  VTm G Γ (tmInr l1 l2 A B b) (tmInr l3 l4 A' B' b') (tySum l1 l2 A B) (lmax l1 l2).
Proof.
  intros Hw1 Hw2 H13 H24 VA VB Vb Δ d d' Hd. push_subst.
  destruct (VTy_refl_l VA _ _ _ Hd) as [RA HRA]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HA & _ & EAA).
  destruct (VTy_refl_l VB _ _ _ Hd) as [RB HRB]. destruct (escape_ty _ _ _ _ _ _ _ _ HRB) as (HB & _ & EBB).
  destruct (VA _ _ _ Hd) as [RA' HRA']. destruct (escape_ty _ _ _ _ _ _ _ _ HRA') as (_ & _ & EA).
  destruct (VB _ _ _ Hd) as [RB' HRB']. destruct (escape_ty _ _ _ _ _ _ _ _ HRB') as (_ & _ & EB).
  pose proof (Vb _ _ _ Hd) as Xb. pose proof (LRtm_geq Xb) as Eb.
  pose proof (geq_tm_sound (geq_tm_inr H13 H24 EA EB Eb)) as Dinr.
  eapply LRtm_of; [exact (LR_sum_here Hw1 Hw2 (lequiv_refl _ _ Hw1) (lequiv_refl _ _ Hw2) HA EAA HB EBB HRA HRB)|].
  exists (tmInr l1 l2 A[d] B[d] b[d]), (tmInr l3 l4 A'[d'] B'[d'] b'[d']).
  refine (conj (tmred_refl _ _ _ (eqtm_wf_l ge_typeof Dinr))
           (conj (tmred_refl _ _ _ (eqtm_wf_r ge_typeof Dinr)) (conj (geq_tm_inr H13 H24 EA EB Eb) _))).
  apply sumnf_inr;
    [ now apply lequiv_refl | now apply lequiv_refl | now apply lequiv_sym | now apply lequiv_sym
    | exact (geq_ty_trans EA (geq_ty_sym EA)) | exact EA
    | exact (geq_ty_trans EB (geq_ty_sym EB)) | exact EB
    | exact (LRtm_inv HRB Xb) ].
Qed.

(** ** The code (M12c) and its decoding *)

(** Decoding a code whose annotations [k1], [k2] are equivalent to the
    levels at which its pieces are typed. *)
Lemma tyred_El_sum {G Δ la l1 l2 k1 k2 s t} : lequiv (gL G) la (lmax l1 l2) ->
  lequiv (gL G) k1 l1 -> lequiv (gL G) k2 l2 ->
  [ G ; Δ ⊢g s : tyU l1 @ lsuc l1 ] -> [ G ; Δ ⊢g t : tyU l2 @ lsuc l2 ] ->
  [ G ; Δ ⊢g tyEl la (tmSum k1 k2 s t) ⤳* tySum k1 k2 (tyEl k1 s) (tyEl k2 t) @ lmax l1 l2 ].
Proof.
  intros Hla Hk1 Hk2 Hs Ht.
  pose proof (lequiv_wf_l _ _ _ Hk1) as Wk1. pose proof (lequiv_wf_l _ _ _ Hk2) as Wk2.
  pose proof (conv_U' Hs (lequiv_sym _ _ _ Hk1)) as Hsk. pose proof (conv_U' Ht (lequiv_sym _ _ _ Hk2)) as Htk.
  assert (Hm : lequiv (gL G) (lmax k1 k2) (lmax l1 l2)) by now apply lequiv_max.
  assert (Hc0 : [ G ; Δ ⊢g tmSum k1 k2 s t : tyU (lmax k1 k2) @ lsuc (lmax k1 k2) ])
    by (apply wf_code_sum; [exact ge_compt | exact Wk1 | exact Wk2 | exact Hsk | exact Htk]).
  pose proof (conv_U' Hc0 Hm) as Hc.
  destruct (El_annot Hc Hla) as [HEl HEq].
  apply tyred_step; [exact HEl | constructor |].
  eapply eqty_trans; [exact HEq|].
  eapply (eqty_trans _ _ _ _ (tyEl (lmax k1 k2) (tmSum k1 k2 s t))).
  - apply eqty_El; [exact ge_notV | now apply lequiv_sym | apply eqtm_refl, Hc].
  - apply (eqty_lconv _ _ _ _ _ (lmax l1 l2) (lmax k1 k2)); [|now apply lequiv_sym].
    apply eqty_sym, eqty_El_sum; [exact ge_compt | exact Wk1 | exact Wk2 | exact Hsk | exact Htk].
Qed.

Lemma V_El_sum {G Γ l l' s t} : lwf (gL G) l -> lwf (gL G) l' ->
  VTm G Γ s s (tyU l) (lsuc l) -> VTm G Γ t t (tyU l') (lsuc l') ->
  VTy G Γ (tySum l l' (tyEl l s) (tyEl l' t)) (tyEl (lmax l l') (tmSum l l' s t)) (lmax l l').
Proof.
  intros Hw Hw' Vs Vt Δ d d' Hd.
  pose proof (V_El Hw (lequiv_refl _ _ Hw) Vs) as VA. pose proof (V_El Hw' (lequiv_refl _ _ Hw') Vt) as VB.
  destruct (V_sum Hw Hw' (lequiv_refl _ _ Hw) (lequiv_refl _ _ Hw') VA VB _ _ _ Hd) as [R HR].
  destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (HP & _ & _).
  pose proof (Vs _ _ _ (SubRel_refl_r Hd)) as Xs. pose proof (Vt _ _ _ (SubRel_refl_r Hd)) as Xt.
  rewrite !subst_tyU in Xs, Xt.
  exists R. eapply LR_red_ty; [exact HR | apply tyred_refl, HP |]. push_subst.
  apply tyred_El_sum; [apply lequiv_refl, lwf_max; assumption | now apply lequiv_refl | now apply lequiv_refl
                      | exact (proj1 (LRtm_escape Xs)) | exact (proj1 (LRtm_escape Xt))].
Qed.

Lemma V_code_sum {G Γ l1 l2 l3 l4 s s' t t'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  VTm G Γ s s' (tyU l1) (lsuc l1) -> VTm G Γ t t' (tyU l2) (lsuc l2) ->
  VTm G Γ (tmSum l1 l2 s t) (tmSum l3 l4 s' t') (tyU (lmax l1 l2)) (lsuc (lmax l1 l2)).
Proof.
  intros Hw1 Hw2 H13 H24 Vs Vt Δ d d' Hd.
  pose proof (V_El Hw1 H13 Vs) as VA. pose proof (V_El Hw2 H24 Vt) as VB.
  destruct (V_sum Hw1 Hw2 H13 H24 VA VB _ _ _ Hd) as [R HR].
  pose proof (Vs _ _ _ Hd) as Xs. pose proof (Vt _ _ _ Hd) as Xt. rewrite !subst_tyU in Xs, Xt.
  destruct (LRtm_escape Xs) as [Hsd Hs'd']. destruct (LRtm_escape Xt) as [Htd Ht'd'].
  pose proof (geq_tm_code_sum H13 H24 (LRtm_geq Xs) (LRtm_geq Xt)) as Hgeq.
  pose proof (geq_tm_sound Hgeq) as Hgeq'.
  push_subst. apply (LRtm_U (lwf_max Hw1 Hw2)).
  exists (tmSum l1 l2 s[d] t[d]), (tmSum l3 l4 s'[d'] t'[d']).
  refine (conj (tmred_refl _ _ _ (eqtm_wf_l ge_typeof Hgeq'))
           (conj (tmred_refl _ _ _ (eqtm_wf_r ge_typeof Hgeq'))
           (conj (whnf_tmSum _ _ _ _) (conj (whnf_tmSum _ _ _ _) (conj Hgeq _))))).
  intros la lb Hla Hlb. rewrite LRbelow_spec by (rewrite ?lmeasure_suc; lia).
  exists R. eapply LR_red_ty; [exact HR | |]; push_subst.
  - apply tyred_El_sum; [exact Hla | now apply lequiv_refl | now apply lequiv_refl | exact Hsd | exact Htd].
  - apply tyred_El_sum; [exact Hlb | now apply lequiv_sym | now apply lequiv_sym | exact Hs'd' | exact Ht'd'].
Qed.

(** ** [case] *)

Section CaseAt.
Context {G : gctx} {Γ : ctx} {l1 l2 l3 : lvl} {A A' B B' M M' : ty} {c1 c1' c2 c2' : tm}
  (Hw1 : lwf (gL G) l1) (Hw2 : lwf (gL G) l2) (Hw3 : lwf (gL G) l3)
  (VA : VTy G Γ A A' l1) (VB : VTy G Γ B B' l2)
  (VM : VTy G (Γ ,, tySum l1 l2 A B @ lmax l1 l2) M M' l3)
  (Vc1 : VTm G (Γ ,, A @ l1) c1 c1' M⟨rlift ↑⟩[lsingle (tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] l3)
  (Vc2 : VTm G (Γ ,, B @ l2) c2 c2' M⟨rlift ↑⟩[lsingle (tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] l3).

(** The premises of [case], at related substitutions. *)
Lemma case_at {Δ d d'} : SubRel G Γ Δ d d' ->
  [ G ; Δ ⊢g A[d] @ l1 ] /\ [ G ; Δ ⊢ A[d] ≈ A'[d'] @ l1 ] /\
  [ G ; Δ ⊢g B[d] @ l2 ] /\ [ G ; Δ ⊢ B[d] ≈ B'[d'] @ l2 ] /\
  [ G ; Δ ,, tySum l1 l2 A[d] B[d] @ lmax l1 l2 ⊢g M[llift d] @ l3 ] /\
  [ G ; Δ ,, tySum l1 l2 A[d] B[d] @ lmax l1 l2 ⊢ M[llift d] ≈ M'[llift d'] @ l3 ] /\
  [ G ; Δ ,, A[d] @ l1 ⊢ c1[llift d] ≈ c1'[llift d']
      : M[llift d]⟨rlift ↑⟩[lsingle (tmInl l1 l2 A[d]⟨↑⟩ B[d]⟨↑⟩ (var 0))] @ l3 ] /\
  [ G ; Δ ,, B[d] @ l2 ⊢ c2[llift d] ≈ c2'[llift d']
      : M[llift d]⟨rlift ↑⟩[lsingle (tmInr l1 l2 A[d]⟨↑⟩ B[d]⟨↑⟩ (var 0))] @ l3 ].
Proof.
  intros Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  destruct (VA _ _ _ Hd) as [RA HRA]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HA & _ & EA).
  destruct (VB _ _ _ Hd) as [RB HRB]. destruct (escape_ty _ _ _ _ _ _ _ _ HRB) as (HB & _ & EB).
  pose proof (V_sum Hw1 Hw2 (lequiv_refl _ _ Hw1) (lequiv_refl _ _ Hw2) (VTy_refl_l VA) (VTy_refl_l VB)) as VS.
  assert (HS : [ G ; Δ ⊢g (tySum l1 l2 A B)[d] @ lmax l1 l2 ]).
  { destruct (VS _ _ _ Hd) as [RS HRS]. exact (proj1 (escape_ty _ _ _ _ _ _ _ _ HRS)). }
  pose proof (SubRel_lift Hd VS HS (lwf_max Hw1 Hw2)) as HdS.
  destruct (VM _ _ _ HdS) as [RM HRM]. destruct (escape_ty _ _ _ _ _ _ _ _ HRM) as (HM & _ & EM).
  pose proof (LRtm_geq (Vc1 _ _ _ (SubRel_lift Hd (VTy_refl_l VA) HA Hw1))) as Ec1.
  pose proof (LRtm_geq (Vc2 _ _ _ (SubRel_lift Hd (VTy_refl_l VB) HB Hw2))) as Ec2.
  rewrite subst_tySum in HM, EM.
  rewrite (caseb_inl_llift _ _ _ _ _ _ Nd) in Ec1. rewrite (caseb_inr_llift _ _ _ _ _ _ Nd) in Ec2.
  repeat split; assumption.
Qed.

Lemma V_case {l4 l5 l6 t t'} : lequiv (gL G) l1 l4 -> lequiv (gL G) l2 l5 -> lequiv (gL G) l3 l6 ->
  VTm G Γ t t' (tySum l1 l2 A B) (lmax l1 l2) ->
  VTm G Γ (tmCase l1 l2 l3 A B M c1 c2 t) (tmCase l4 l5 l6 A' B' M' c1' c2' t') M[lsingle t] l3.
Proof.
  intros H14 H25 H36 Vt Δ d d' Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  rewrite !single_subst_ty by assumption. push_subst.
  pose proof (SubRel_refl_l Hd) as Hdd.
  destruct (case_at Hd) as (HA & EA & HB & EB & HM & EM & Ec1 & Ec2).
  pose proof (VTm_trans Vt (VTm_sym Vt)) as Vtt.
  (* the summands' relations at [d] *)
  destruct (VTy_refl_l VA _ _ _ Hdd) as [RA HRA]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (_ & _ & EAd).
  destruct (VTy_refl_l VB _ _ _ Hdd) as [RB HRB]. destruct (escape_ty _ _ _ _ _ _ _ _ HRB) as (_ & _ & EBd).
  destruct (LR_tm_per _ _ _ _ _ _ _ HRA) as [SyA TrA].
  destruct (LR_tm_per _ _ _ _ _ _ _ HRB) as [SyB TrB].
  pose proof (LR_sum_here Hw1 Hw2 (lequiv_refl _ _ Hw1) (lequiv_refl _ _ Hw2) HA EAd HB EBd HRA HRB) as HSdd.
  pose proof (wf_ty_nf HA) as NA. pose proof (wf_ty_nf HB) as NB.
  (* the scrutinee's relation is [SumRel] *)
  pose proof (Vt _ _ _ Hd) as Xt. rewrite !subst_tySum in Xt.
  assert (Rt : SumRel G Δ l1 l2 A[d] B[d] RA RB t[d] t'[d'])
    by exact (LRtm_inv HSdd (LRtm_irrel_r Xt (ex_intro _ _ HSdd))).
  (* the motive at the scrutinee, on both sides *)
  assert (Hs0 : SubRel G (Γ ,, tySum l1 l2 A B @ lmax l1 l2) Δ (lcons d t[d]) (lcons d t[d]))
    by exact (SubRel_cons Hdd (Vtt _ _ _ Hdd)).
  destruct (VTy_refl_l VM _ _ _ Hs0) as [RL HRL]. rewrite <- !lift_single_ty in HRL by exact Nd.
  assert (Hs1 : SubRel G (Γ ,, tySum l1 l2 A B @ lmax l1 l2) Δ (lcons d t[d]) (lcons d' t[d']))
    by exact (SubRel_cons Hd (Vtt _ _ _ Hd)).
  pose proof (VTy_refl_l VM _ _ _ Hs1) as XT. rewrite <- !lift_single_ty in XT by assumption.
  eapply LRtm_irrel_r; [|exact XT].
  (* declarative forms *)
  pose proof (geq_ty_sound EA) as DA. pose proof (geq_ty_sound EB) as DB.
  pose proof (geq_ty_sound EM) as DM.
  pose proof (geq_tm_sound Ec1) as Dc1. pose proof (geq_tm_sound Ec2) as Dc2.
  pose proof (eqtm_wf_l ge_typeof Dc1) as Hc1. pose proof (eqtm_wf_l ge_typeof Dc2) as Hc2.
  pose proof (geq_tm_sound (LRtm_geq Xt)) as Dt.
  assert (HCC : [ G ; Δ ⊢g tmCase l1 l2 l3 A[d] B[d] M[llift d] c1[llift d] c2[llift d] t[d]
                   ≅ tmCase l4 l5 l6 A'[d'] B'[d'] M'[llift d'] c1'[llift d'] c2'[llift d'] t'[d']
                   : M[llift d][lsingle t[d]] @ l3 ])
    by (apply eqtm_case; first [exact ge_compt | assumption]).
  (* the motive at an injection related to the scrutinee *)
  assert (Mat : forall x, LRtm (lmax l1 l2) G Δ (tySum l1 l2 A[d] B[d]) (tySum l1 l2 A[d] B[d]) t[d] x ->
            LRty l3 G Δ M[llift d][lsingle t[d]] M[llift d][lsingle x]).
  { intros x Hx. pose proof (VTy_refl_l VM _ _ _ (SubRel_cons Hdd (A := tySum l1 l2 A B) Hx)) as Y.
    rewrite <- !lift_single_ty in Y by exact Nd. exact Y. }
  destruct Rt as (w & w' & Hrw & Hrw' & Eww & Nww).
  destruct Nww as [k1 k2 k1' k2' C D C' D' a a' Hk1 Hk2 Hk1' Hk2' HC HC' HD HD' Ra
                  | k1 k2 k1' k2' C D C' D' a a' Hk1 Hk2 Hk1' Hk2' HC HC' HD HD' Ra | ν ν' Hν].
  - (* [inl]: both sides step to the left branch *)
    assert (Raa : RA a a) by exact (TrA _ _ _ Ra (SyA _ _ Ra)).
    destruct (escape_tm _ _ _ _ _ _ _ _ HRA _ _ Raa) as (Ha & _ & Eaa).
    pose proof (case_inl_eq Hw1 Hw2 Hw3 HA HB HM Hc1 Hc2 (tmred_eq _ _ _ _ _ _ _ Hrw) Hk1 Hk2
                  (geq_ty_sound HC) (geq_ty_sound HD) Ha) as HLc.
    (* the branches, at the motive instance of the scrutinee *)
    assert (Xa : LRtm l1 G Δ A[d] A[d'] a a')
      by exact (LRtm_irrel_r (LRtm_of HRA Ra) (VTy_refl_l VA _ _ _ Hd)).
    pose proof (Vc1 _ _ _ (SubRel_cons Hd Xa)) as Xc.
    destruct (VTy_refl_l VA _ _ _ Hd) as [RA2 HRA2]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA2) as (_ & HA' & _).
    destruct (VTy_refl_l VB _ _ _ Hd) as [RB2 HRB2]. destruct (escape_ty _ _ _ _ _ _ _ _ HRB2) as (_ & HB' & _).
    rewrite (caseb_inl_cons _ _ _ _ _ _ _ Nd NA NB), (caseb_inl_cons _ _ _ _ _ _ _ Nd' (wf_ty_nf HA') (wf_ty_nf HB'))
      in Xc.
    rewrite <- !lift_single_tm in Xc by assumption. rewrite <- !lift_single_ty in Xc by assumption.
    assert (XT2 : LRty l3 G Δ M[llift d][lsingle t[d]] M[llift d][lsingle (tmInl l1 l2 A[d] B[d] a)]).
    { apply Mat, (LRtm_of HSdd). eexists _, (tmInl l1 l2 A[d] B[d] a).
      pose proof (wf_inl _ _ _ _ _ _ _ _ ge_compt Hw1 Hw2 HA HB Ha) as Hinl.
      refine (conj Hrw (conj (tmred_refl _ _ _ Hinl) (conj _ _))).
      - apply geq_tm_sym, geq_tm_inl; [now apply lequiv_sym | now apply lequiv_sym | exact HC | exact HD | exact Eaa].
      - apply sumnf_inl; [exact Hk1 | exact Hk2 | now apply lequiv_refl | now apply lequiv_refl
                         | exact HC | exact EAd | exact HD | exact EBd | exact Raa]. }
    pose proof (LRtm_conv_l Xc XT2) as Xc2.
    assert (Lred : [ G ; Δ ⊢g tmCase l1 l2 l3 A[d] B[d] M[llift d] c1[llift d] c2[llift d] t[d]
                     ⤳* c1[llift d][lsingle a] : M[llift d][lsingle t[d]] @ l3 ]).
    { split; [exact (eqtm_wf_l ge_typeof HLc) | | exact HLc].
      eapply reds_trans; [apply reds_case, (tmred_red _ _ _ _ _ _ _ Hrw)|].
      econstructor; [apply red_case_inl | constructor]. }
    assert (Rred : [ G ; Δ ⊢g tmCase l4 l5 l6 A'[d'] B'[d'] M'[llift d'] c1'[llift d'] c2'[llift d'] t'[d']
                     ⤳* c1'[llift d'][lsingle a'] : M[llift d][lsingle t[d]] @ l3 ]).
    { split; [exact (eqtm_wf_r ge_typeof HCC) | |].
      - eapply reds_trans; [apply reds_case, (tmred_red _ _ _ _ _ _ _ Hrw')|].
        econstructor; [apply red_case_inl | constructor].
      - eapply eqtm_trans; [apply eqtm_sym, HCC|]. eapply eqtm_trans; [exact HLc|].
        exact (geq_tm_sound (LRtm_geq Xc2)). }
    eapply LRtm_red; [|exact Lred | exact Rred].
    eapply LRtm_irrel_r; [exact Xc2 | exact (ex_intro _ _ HRL)].
  - (* [inr]: both sides step to the right branch *)
    assert (Raa : RB a a) by exact (TrB _ _ _ Ra (SyB _ _ Ra)).
    destruct (escape_tm _ _ _ _ _ _ _ _ HRB _ _ Raa) as (Ha & _ & Eaa).
    pose proof (case_inr_eq Hw1 Hw2 Hw3 HA HB HM Hc1 Hc2 (tmred_eq _ _ _ _ _ _ _ Hrw) Hk1 Hk2
                  (geq_ty_sound HC) (geq_ty_sound HD) Ha) as HLc.
    assert (Xa : LRtm l2 G Δ B[d] B[d'] a a')
      by exact (LRtm_irrel_r (LRtm_of HRB Ra) (VTy_refl_l VB _ _ _ Hd)).
    pose proof (Vc2 _ _ _ (SubRel_cons Hd Xa)) as Xc.
    destruct (VTy_refl_l VA _ _ _ Hd) as [RA2 HRA2]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA2) as (_ & HA' & _).
    destruct (VTy_refl_l VB _ _ _ Hd) as [RB2 HRB2]. destruct (escape_ty _ _ _ _ _ _ _ _ HRB2) as (_ & HB' & _).
    rewrite (caseb_inr_cons _ _ _ _ _ _ _ Nd NA NB), (caseb_inr_cons _ _ _ _ _ _ _ Nd' (wf_ty_nf HA') (wf_ty_nf HB'))
      in Xc.
    rewrite <- !lift_single_tm in Xc by assumption. rewrite <- !lift_single_ty in Xc by assumption.
    assert (XT2 : LRty l3 G Δ M[llift d][lsingle t[d]] M[llift d][lsingle (tmInr l1 l2 A[d] B[d] a)]).
    { apply Mat, (LRtm_of HSdd). eexists _, (tmInr l1 l2 A[d] B[d] a).
      pose proof (wf_inr _ _ _ _ _ _ _ _ ge_compt Hw1 Hw2 HA HB Ha) as Hinr.
      refine (conj Hrw (conj (tmred_refl _ _ _ Hinr) (conj _ _))).
      - apply geq_tm_sym, geq_tm_inr; [now apply lequiv_sym | now apply lequiv_sym | exact HC | exact HD | exact Eaa].
      - apply sumnf_inr; [exact Hk1 | exact Hk2 | now apply lequiv_refl | now apply lequiv_refl
                         | exact HC | exact EAd | exact HD | exact EBd | exact Raa]. }
    pose proof (LRtm_conv_l Xc XT2) as Xc2.
    assert (Lred : [ G ; Δ ⊢g tmCase l1 l2 l3 A[d] B[d] M[llift d] c1[llift d] c2[llift d] t[d]
                     ⤳* c2[llift d][lsingle a] : M[llift d][lsingle t[d]] @ l3 ]).
    { split; [exact (eqtm_wf_l ge_typeof HLc) | | exact HLc].
      eapply reds_trans; [apply reds_case, (tmred_red _ _ _ _ _ _ _ Hrw)|].
      econstructor; [apply red_case_inr | constructor]. }
    assert (Rred : [ G ; Δ ⊢g tmCase l4 l5 l6 A'[d'] B'[d'] M'[llift d'] c1'[llift d'] c2'[llift d'] t'[d']
                     ⤳* c2'[llift d'][lsingle a'] : M[llift d][lsingle t[d]] @ l3 ]).
    { split; [exact (eqtm_wf_r ge_typeof HCC) | |].
      - eapply reds_trans; [apply reds_case, (tmred_red _ _ _ _ _ _ _ Hrw')|].
        econstructor; [apply red_case_inr | constructor].
      - eapply eqtm_trans; [apply eqtm_sym, HCC|]. eapply eqtm_trans; [exact HLc|].
        exact (geq_tm_sound (LRtm_geq Xc2)). }
    eapply LRtm_red; [|exact Lred | exact Rred].
    eapply LRtm_irrel_r; [exact Xc2 | exact (ex_intro _ _ HRL)].
  - (* a neutral: [case] is neutral *)
    pose proof (tmred_eq _ _ _ _ _ _ _ Hrw) as Deν.
    pose proof (case_cong Hw1 Hw2 Hw3 HA HB HM Hc1 Hc2 Deν) as HCν.
    pose proof (case_motive_conv HM Deν) as HMν.
    assert (HCνν : [ G ; Δ ⊢g tmCase l1 l2 l3 A[d] B[d] M[llift d] c1[llift d] c2[llift d] ν
                      ≅ tmCase l4 l5 l6 A'[d'] B'[d'] M'[llift d'] c1'[llift d'] c2'[llift d'] ν'
                      : M[llift d][lsingle t[d]] @ l3 ]).
    { eapply convg; [|exact HMν].
      apply eqtm_case; first [exact ge_compt | assumption | exact (geq_tm_sound (gne_tm_geq Hν))]. }
    assert (Lred : [ G ; Δ ⊢g tmCase l1 l2 l3 A[d] B[d] M[llift d] c1[llift d] c2[llift d] t[d]
                     ⤳* tmCase l1 l2 l3 A[d] B[d] M[llift d] c1[llift d] c2[llift d] ν
                     : M[llift d][lsingle t[d]] @ l3 ]).
    { split; [exact (eqtm_wf_l ge_typeof HCν) | apply reds_case, (tmred_red _ _ _ _ _ _ _ Hrw) | exact HCν]. }
    assert (Rred : [ G ; Δ ⊢g tmCase l4 l5 l6 A'[d'] B'[d'] M'[llift d'] c1'[llift d'] c2'[llift d'] t'[d']
                     ⤳* tmCase l4 l5 l6 A'[d'] B'[d'] M'[llift d'] c1'[llift d'] c2'[llift d'] ν'
                     : M[llift d][lsingle t[d]] @ l3 ]).
    { split; [exact (eqtm_wf_r ge_typeof HCC) | apply reds_case, (tmred_red _ _ _ _ _ _ _ Hrw') |].
      eapply eqtm_trans; [apply eqtm_sym, HCC|]. eapply eqtm_trans; [exact HCν | exact HCνν]. }
    pose proof (gne_tm_case H14 H25 H36 HA EA HB EB HM EM Ec1 Ec2 Hν) as Hne.
    apply (fun H => gne_tm_conv H (eqty_sym _ _ _ _ _ _ HMν)) in Hne.
    eapply LRtm_red; [|exact Lred | exact Rred].
    exact (LRtm_of HRL (LR_neutral _ _ _ _ _ _ _ HRL _ _ Hne Hne)).
Qed.

(** The β rules, the scrutinee an injection with the [case]'s annotations. *)
Lemma V_case_inl {a} :
  VTm G (Γ ,, A @ l1) c1 c1 M⟨rlift ↑⟩[lsingle (tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] l3 -> VTm G Γ a a A l1 ->
  VTm G Γ (tmCase l1 l2 l3 A B M c1 c2 (tmInl l1 l2 A B a)) c1[lsingle a] M[lsingle (tmInl l1 l2 A B a)] l3.
Proof.
  intros Vcc Va Δ d d' Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  destruct (case_at Hd) as (HA & _ & HB & _ & HM & _ & Ec1 & Ec2).
  destruct (VTy_refl_l VA _ _ _ Hd) as [RA2 HRA2]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA2) as (_ & HA' & _).
  destruct (VTy_refl_l VB _ _ _ Hd) as [RB2 HRB2]. destruct (escape_ty _ _ _ _ _ _ _ _ HRB2) as (_ & HB' & _).
  pose proof (Va _ _ _ Hd) as Xa. pose proof (proj1 (LRtm_escape Xa)) as Ha.
  pose proof (Vcc _ _ _ (SubRel_cons Hd Xa)) as X.
  rewrite (caseb_inl_cons _ _ _ _ _ _ _ Nd (wf_ty_nf HA) (wf_ty_nf HB)),
    (caseb_inl_cons _ _ _ _ _ _ _ Nd' (wf_ty_nf HA') (wf_ty_nf HB')) in X.
  rewrite <- !lift_single_tm in X by assumption.
  rewrite !single_subst_ty, !single_subst by assumption. push_subst. rewrite !lift_single_ty by assumption.
  eapply LRtm_red_l; [exact X|].
  pose proof (eqtm_wf_l ge_typeof (geq_tm_sound Ec1)) as Hc1.
  pose proof (eqtm_wf_l ge_typeof (geq_tm_sound Ec2)) as Hc2.
  pose proof (eqtm_case_inl _ _ _ _ _ _ _ _ _ _ _ _ ge_compt Hw1 Hw2 Hw3 HA HB HM Hc1 Hc2 Ha) as Hb.
  rewrite lift_single_ty in Hb by assumption.
  split; [exact (eqtm_wf_l ge_typeof Hb) | | exact Hb].
  econstructor; [apply red_case_inl | constructor].
Qed.

Lemma V_case_inr {b} :
  VTm G (Γ ,, B @ l2) c2 c2 M⟨rlift ↑⟩[lsingle (tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] l3 -> VTm G Γ b b B l2 ->
  VTm G Γ (tmCase l1 l2 l3 A B M c1 c2 (tmInr l1 l2 A B b)) c2[lsingle b] M[lsingle (tmInr l1 l2 A B b)] l3.
Proof.
  intros Vcc Vb Δ d d' Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  destruct (case_at Hd) as (HA & _ & HB & _ & HM & _ & Ec1 & Ec2).
  destruct (VTy_refl_l VA _ _ _ Hd) as [RA2 HRA2]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA2) as (_ & HA' & _).
  destruct (VTy_refl_l VB _ _ _ Hd) as [RB2 HRB2]. destruct (escape_ty _ _ _ _ _ _ _ _ HRB2) as (_ & HB' & _).
  pose proof (Vb _ _ _ Hd) as Xb. pose proof (proj1 (LRtm_escape Xb)) as Hb0.
  pose proof (Vcc _ _ _ (SubRel_cons Hd Xb)) as X.
  rewrite (caseb_inr_cons _ _ _ _ _ _ _ Nd (wf_ty_nf HA) (wf_ty_nf HB)),
    (caseb_inr_cons _ _ _ _ _ _ _ Nd' (wf_ty_nf HA') (wf_ty_nf HB')) in X.
  rewrite <- !lift_single_tm in X by assumption.
  rewrite !single_subst_ty, !single_subst by assumption. push_subst. rewrite !lift_single_ty by assumption.
  eapply LRtm_red_l; [exact X|].
  pose proof (eqtm_wf_l ge_typeof (geq_tm_sound Ec1)) as Hc1.
  pose proof (eqtm_wf_l ge_typeof (geq_tm_sound Ec2)) as Hc2.
  pose proof (eqtm_case_inr _ _ _ _ _ _ _ _ _ _ _ _ ge_compt Hw1 Hw2 Hw3 HA HB HM Hc1 Hc2 Hb0) as Hb.
  rewrite lift_single_ty in Hb by assumption.
  split; [exact (eqtm_wf_l ge_typeof Hb) | | exact Hb].
  econstructor; [apply red_case_inr | constructor].
Qed.

End CaseAt.

End Sum.
