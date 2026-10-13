(** * Validity of [nth] (M15_DESIGN.md, M15a: the index lemma)

    [nth^l(T; k; cs; i)] is a fixed [natrec] schema, so its validity is
    the validity lemmas of the formers it is built from ([natrec], [λ],
    application, [case], [elim_Empty], the projections), composed along
    its typing derivation ([nth_wf]). This is MX §13's index lemma: at
    related lengths, tuples and indices, the two [nth]s are related at
    [T]; [elim_Wf]'s motive instantiates it at the children of a [sup_f]
    ([V_nth_at]). Composing validity lemmas needs them closed under global
    weakenings ([VTyG], [VTmG]); the [VG_] lemmas lift the ones used. *)
From DeLaM.Validity Require Export Lam Sigma GLift WfNthReds.

Section WfNth.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

(** ** The composed lemmas, closed under global weakenings *)

Lemma VTy_shift1 {G Γ A A' B k l} : VTy G Γ A A' l -> VTy G (Γ ,, B @ k) A⟨↑⟩ A'⟨↑⟩ l.
Proof using . intros H Δ d d' [Hd _]. rewrite !shift_subst_ty. exact (H _ _ _ Hd). Qed.

Lemma shift_subst_tm (t : tm) d : t⟨↑⟩[d] = t[ldrop 1 d].
Proof using . apply ren_subst; intros n; rewrite llk_ldrop, rlk_shift1; reflexivity. Qed.

Lemma VTm_shift1 {G Γ t t' A B k l} : VTm G Γ t t' A l -> VTm G (Γ ,, B @ k) t⟨↑⟩ t'⟨↑⟩ A⟨↑⟩ l.
Proof using . intros H Δ d d' [Hd _]. rewrite !shift_subst_ty, !shift_subst_tm. exact (H _ _ _ Hd). Qed.

Lemma VG_shift_tm {G Γ t t' A B k l} : VTmG G Γ t t' A l -> VTmG G (Γ ,, B @ k) t⟨↑⟩ t'⟨↑⟩ A⟨↑⟩ l.
Proof using . intros. gl_lift. now apply VTm_shift1. Qed.

Lemma VG_shift {G Γ A A' B k l} : VTyG G Γ A A' l -> VTyG G (Γ ,, B @ k) A⟨↑⟩ A'⟨↑⟩ l.
Proof using . intros. gl_lift. now apply VTy_shift1. Qed.

Lemma VG_var {G Γ n T T0 l} : in_ctx Γ n T0 l -> T0 = T -> VTmG G Γ (var n) (var n) T l.
Proof using . intros H <-. gl_lift. now apply V_var. Qed.

Lemma VTmG_retype {G Γ t t' T0 T l} : VTmG G Γ t t' T0 l -> T0 = T -> VTmG G Γ t t' T l.
Proof using . now intros H <-. Qed.

Lemma VG_nat {G Γ} : VTyG G Γ tyNat tyNat lzero.
Proof using . gl_lift. exact V_nat. Qed.
Lemma VG_zero {G Γ} : VTmG G Γ zero zero tyNat lzero.
Proof using EL VL. gl_lift. exact V_zero. Qed.
Lemma VG_succ {G Γ t t'} : VTmG G Γ t t' tyNat lzero -> VTmG G Γ (succ t) (succ t') tyNat lzero.
Proof using EL VL. intros. gl_lift. now apply V_succ. Qed.

Lemma VG_unit {G Γ l l'} : lwf (gL G) l -> lequiv (gL G) l l' -> VTyG G Γ (tyUnit l) (tyUnit l') l.
Proof using . intros. gl_lift. eapply V_unit; eassumption. Qed.

Lemma VG_vec {G Γ l l' A A' n n'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTyG G Γ A A' l -> VTmG G Γ n n' tyNat lzero -> VTyG G Γ (tyVec l A n) (tyVec l' A' n') l.
Proof using EL VL. intros. gl_lift. eapply V_vec; eassumption. Qed.
Lemma VG_fin {G Γ n n'} : VTmG G Γ n n' tyNat lzero -> VTyG G Γ (tyFin n) (tyFin n') lzero.
Proof using EL VL. intros. gl_lift. eapply V_fin; eassumption. Qed.
Lemma VG_vec_zero {G Γ l l' A A'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTyG G Γ A A' l -> VTyG G Γ (tyVec l A zero) (tyUnit l') l.
Proof using EL. intros. gl_lift. eapply V_vec_zero; eassumption. Qed.
Lemma VG_vec_succ {G Γ l l' A A' n n'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTyG G Γ A A' l -> VTmG G Γ n n' tyNat lzero ->
  VTyG G Γ (tyVec l A (succ n)) (tySig l' l' A' (tyVec l' A'⟨↑⟩ n'⟨↑⟩)) l.
Proof using EL VL. intros. gl_lift. eapply V_vec_succ; eassumption. Qed.
Lemma VG_fin_zero {G Γ} : VTyG G Γ (tyFin zero) (tyEmpty lzero) lzero.
Proof using . gl_lift. exact V_fin_zero. Qed.
Lemma VG_fin_succ {G Γ n n'} : VTmG G Γ n n' tyNat lzero ->
  VTyG G Γ (tyFin (succ n)) (tySum lzero lzero (tyUnit lzero) (tyFin n')) lzero.
Proof using EL VL. intros. gl_lift. eapply V_fin_succ; eassumption. Qed.

Lemma VG_pi {G Γ l l' l3 l4 A A' B B'} : lwf (gL G) l -> lwf (gL G) l' ->
  lequiv (gL G) l3 l -> lequiv (gL G) l4 l' -> [ G ; Γ ,, A @ l ⊢g B @ l' ] ->
  VTyG G Γ A A' l -> VTyG G (Γ ,, A @ l) B B' l' ->
  VTyG G Γ (tyPi l l' A B) (tyPi l3 l4 A' B') (lmax l l').
Proof using EL VL VN. intros. gl_lift. eapply V_pi; eassumption. Qed.
Lemma VG_lam {G Γ l l' l3 l4 A A' B t t'} : lwf (gL G) l -> lwf (gL G) l' ->
  lequiv (gL G) l3 l -> lequiv (gL G) l4 l' -> [ G ; Γ ,, A @ l ⊢g B @ l' ] ->
  [ G ; Γ ,, A @ l ⊢g t : B @ l' ] -> VTyG G Γ A A' l -> VTyG G (Γ ,, A @ l) B B l' ->
  VTmG G (Γ ,, A @ l) t t' B l' ->
  VTmG G Γ (lam l l' A t) (lam l3 l4 A' t') (tyPi l l' A B) (lmax l l').
Proof using EL VL VN. intros. gl_lift. eapply V_lam; eassumption. Qed.
Lemma VG_app {G Γ l l' l3 l4 A A' B B' t t' s s'} : lwf (gL G) l -> lwf (gL G) l' ->
  lequiv (gL G) l3 l -> lequiv (gL G) l4 l' -> [ G ; Γ ,, A @ l ⊢g B @ l' ] ->
  VTyG G Γ A A' l -> VTyG G (Γ ,, A @ l) B B' l' ->
  VTmG G Γ t t' (tyPi l l' A B) (lmax l l') -> VTmG G Γ s s' A l ->
  VTmG G Γ (app t l l' A B s) (app t' l3 l4 A' B' s') B[lsingle s] l'.
Proof using EL VL VN. intros. gl_lift. eapply V_app; eassumption. Qed.
Lemma VG_fst {G Γ l l' l3 l4 A A' B B' p p'} : lwf (gL G) l -> lwf (gL G) l' ->
  lequiv (gL G) l3 l -> lequiv (gL G) l4 l' -> [ G ; Γ ,, A @ l ⊢g B @ l' ] ->
  VTyG G Γ A A' l -> VTyG G (Γ ,, A @ l) B B' l' ->
  VTmG G Γ p p' (tySig l l' A B) (lmax l l') ->
  VTmG G Γ (tmFst l l' A B p) (tmFst l3 l4 A' B' p') A l.
Proof using EL VL VN. intros. gl_lift. eapply V_fst; eassumption. Qed.
Lemma VG_snd {G Γ l l' l3 l4 A A' B B' p p'} : lwf (gL G) l -> lwf (gL G) l' ->
  lequiv (gL G) l3 l -> lequiv (gL G) l4 l' -> [ G ; Γ ,, A @ l ⊢g B @ l' ] ->
  VTyG G Γ A A' l -> VTyG G (Γ ,, A @ l) B B' l' ->
  VTmG G Γ p p' (tySig l l' A B) (lmax l l') ->
  VTmG G Γ (tmSnd l l' A B p) (tmSnd l3 l4 A' B' p') B[lsingle (tmFst l l' A B p)] l'.
Proof using EL VL VN. intros. gl_lift. eapply V_snd; eassumption. Qed.
Lemma VG_elimEmpty {G Γ l1 l2 l3 l4 M M' t t'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 -> [ G ; Γ ,, tyEmpty l2 @ l2 ⊢g M @ l1 ] ->
  VTyG G (Γ ,, tyEmpty l2 @ l2) M M' l1 -> VTmG G Γ t t' (tyEmpty l2) l2 ->
  VTmG G Γ (elimEmpty l1 l2 M t) (elimEmpty l3 l4 M' t') M[lsingle t] l1.
Proof using EL VL VN. intros. gl_lift. eapply V_elimEmpty; eassumption. Qed.
Lemma VG_case {G Γ l1 l2 l3 A A' B B' M M' c1 c1' c2 c2' l4 l5 l6 t t'} :
  lwf (gL G) l1 -> lwf (gL G) l2 -> lwf (gL G) l3 ->
  VTyG G Γ A A' l1 -> VTyG G Γ B B' l2 -> VTyG G (Γ ,, tySum l1 l2 A B @ lmax l1 l2) M M' l3 ->
  VTmG G (Γ ,, A @ l1) c1 c1' (M⟨rlift ↑⟩)[lsingle (tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] l3 ->
  VTmG G (Γ ,, B @ l2) c2 c2' (M⟨rlift ↑⟩)[lsingle (tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] l3 ->
  lequiv (gL G) l1 l4 -> lequiv (gL G) l2 l5 -> lequiv (gL G) l3 l6 ->
  VTmG G Γ t t' (tySum l1 l2 A B) (lmax l1 l2) ->
  VTmG G Γ (tmCase l1 l2 l3 A B M c1 c2 t) (tmCase l4 l5 l6 A' B' M' c1' c2' t') M[lsingle t] l3.
Proof using EL VL VN. intros. gl_lift. eapply V_case; eassumption. Qed.
Lemma VG_natrec {G Γ l l' M M' s s' z z' t t'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  [ G ; Γ ,, tyNat @ lzero ⊢g M @ l ] -> [ G ; Γ ⊢g s : M[lsingle zero] @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢g z : M[lsucc] @ l ] ->
  VTyG G (Γ ,, tyNat @ lzero) M M' l -> VTmG G Γ s s' M[lsingle zero] l ->
  VTmG G (Γ ,, tyNat @ lzero ,, M @ l) z z' M[lsucc] l -> VTmG G Γ t t' tyNat lzero ->
  VTmG G Γ (natrec l M s z t) (natrec l' M' s' z' t') M[lsingle t] l.
Proof using EL VL VN. intros. gl_lift. eapply V_natrec; eassumption. Qed.

(** ** The schema's pieces *)

Ltac gwkn H := first [ exact H | eapply (wk1_ty _ _ ge_typeof); [eassumption | gwkn H]
                     | eapply (wk1_tm _ _ ge_typeof); [eassumption | gwkn H] ].
Ltac gvar := eapply wf_tm_retype; [eapply wf_var; [rewrite ge_typeof; eassumption | repeat constructor] | cbn; try reflexivity].
Ltac vvar := eapply VG_var; [repeat constructor | cbn; try reflexivity].

Lemma lq_0l' {G l} : lwf (gL G) l -> lequiv (gL G) (lmax lzero l) l.
Proof using . intros Hl. eapply lequiv_trans; [apply lmax_comm; cbn; auto | apply lmax_zero; auto]. Qed.

Section NthV.
Context {G : gctx} {Γ : ctx} {l l' : lvl} {T T' : ty}
  (Hwl : lwf (gL G) l) (Hll : lequiv (gL G) l l')
  (HT : [ G ; Γ ⊢g T @ l ]) (VT : VTyG G Γ T T' l).

Lemma nth_mot_V : VTyG G (Γ ,, tyNat @ lzero) (nthMot l T) (nthMot l' T') l.
Proof using EL HT Hll Hwl VL VN VT.
  pose proof (ctx_of_wf_ty ge_typeof HT) as H0. pose proof ge_notV as Hv.
  assert (H1 : [ G ; Γ ,, tyNat @ lzero ⊢g ])
    by (apply ext_wf_g; [apply wft_nat; auto; now rewrite ge_typeof | cbn; auto]).
  assert (HV : [ G ; Γ ,, tyNat @ lzero ⊢g tyVec l T⟨↑⟩ (var 0) @ l ])
    by (apply wft_vec; auto using ge_compt; [gwkn HT | gvar]).
  assert (H2 : [ G ; Γ ,, tyNat @ lzero ,, tyVec l T⟨↑⟩ (var 0) @ l ⊢g ]) by (apply ext_wf_g; auto).
  assert (HF : [ G ; Γ ,, tyNat @ lzero ,, tyVec l T⟨↑⟩ (var 0) @ l ⊢g tyFin (var 1) @ lzero ])
    by (apply wft_fin; auto using ge_compt; gvar).
  assert (H3 : [ G ; Γ ,, tyNat @ lzero ,, tyVec l T⟨↑⟩ (var 0) @ l ,, tyFin (var 1) @ lzero ⊢g ])
    by (apply ext_wf_g; cbn; auto).
  assert (HT3 : [ G ; Γ ,, tyNat @ lzero ,, tyVec l T⟨↑⟩ (var 0) @ l ,, tyFin (var 1) @ lzero
                  ⊢g T⟨↑⟩⟨↑⟩⟨↑⟩ @ l ]) by gwkn HT.
  assert (HP : [ G ; Γ ,, tyNat @ lzero ,, tyVec l T⟨↑⟩ (var 0) @ l
                 ⊢g tyPi lzero l (tyFin (var 1)) T⟨↑⟩⟨↑⟩⟨↑⟩ @ l ])
    by (eapply wft_lconv; [apply wft_pi; cbn; auto using ge_compt | apply lequiv_sym, lq_0l', Hwl]).
  unfold nthMot. eapply VTyG_lconv; [| apply lequiv_sym, lmax_idem, Hwl].
  apply VG_pi; auto using lequiv_sym.
  - apply VG_vec; auto. apply VG_shift, VT. vvar.
  - eapply VTyG_lconv; [| apply lequiv_sym, lq_0l', Hwl].
    assert (Hw0 : lwf (gL G) lzero) by (cbn; auto).
    refine (VG_pi Hw0 Hwl (lequiv_refl _ _ Hw0) (lequiv_sym _ _ _ Hll) HT3 _ _).
    + apply VG_fin. vvar.
    + do 3 apply VG_shift. exact VT.
Qed.

Lemma nth_base_V : VTmG G Γ (nthBase l T) (nthBase l' T') (nthMot l T)[lsingle zero] l.
Proof using EL HT Hll Hwl VL VN VT.
  pose proof (ctx_of_wf_ty ge_typeof HT) as H0. pose proof ge_notV as Hv. pose proof (wf_ty_nf HT) as NT.
  assert (Hw0 : lwf (gL G) lzero) by (cbn; auto).
  rewrite nth_E0 by exact NT. unfold nthBase.
  assert (Hz : [ G ; Γ ⊢g zero : tyNat @ lzero ]) by (apply wf_zero; auto; now rewrite ge_typeof).
  assert (HV : [ G ; Γ ⊢g tyVec l T zero @ l ]) by (apply wft_vec; auto).
  assert (H1 : [ G ; Γ ,, tyVec l T zero @ l ⊢g ]) by (apply ext_wf_g; auto).
  assert (Hz1 : [ G ; Γ ,, tyVec l T zero @ l ⊢g zero : tyNat @ lzero ])
    by (apply wf_zero; auto; now rewrite ge_typeof).
  assert (HF : [ G ; Γ ,, tyVec l T zero @ l ⊢g tyFin zero @ lzero ]) by (apply wft_fin; auto).
  assert (H2 : [ G ; Γ ,, tyVec l T zero @ l ,, tyFin zero @ lzero ⊢g ]) by (apply ext_wf_g; cbn; auto).
  assert (HE : [ G ; Γ ,, tyVec l T zero @ l ,, tyFin zero @ lzero ⊢g tyEmpty lzero @ lzero ])
    by (apply wft_empty; cbn; auto; now rewrite ge_typeof).
  assert (H3 : [ G ; Γ ,, tyVec l T zero @ l ,, tyFin zero @ lzero ,, tyEmpty lzero @ lzero ⊢g ])
    by (apply ext_wf_g; cbn; auto).
  assert (HT2 : [ G ; Γ ,, tyVec l T zero @ l ,, tyFin zero @ lzero ⊢g T⟨↑⟩⟨↑⟩ @ l ]) by gwkn HT.
  assert (HT3 : [ G ; Γ ,, tyVec l T zero @ l ,, tyFin zero @ lzero ,, tyEmpty lzero @ lzero
                  ⊢g T⟨↑⟩⟨↑⟩⟨↑⟩ @ l ]) by gwkn HT.
  assert (Hv0 : [ G ; Γ ,, tyVec l T zero @ l ,, tyFin zero @ lzero ⊢g var 0 : tyEmpty lzero @ lzero ]).
  { eapply (conv_tm' ge_typeof); [gvar|]. apply eqty_sym, eqty_fin_zero; [exact ge_compt | now rewrite ge_typeof]. }
  assert (EE : T⟨↑⟩⟨↑⟩⟨↑⟩[lsingle (var 0)] = T⟨↑⟩⟨↑⟩) by teq.
  assert (He : [ G ; Γ ,, tyVec l T zero @ l ,, tyFin zero @ lzero
                 ⊢g elimEmpty l lzero T⟨↑⟩⟨↑⟩⟨↑⟩ (var 0) : T⟨↑⟩⟨↑⟩ @ l ])
    by (eapply wf_tm_retype; [apply wf_elimEmpty; cbn; auto | exact EE]).
  assert (HP : [ G ; Γ ,, tyVec l T zero @ l ⊢g tyPi lzero l (tyFin zero) T⟨↑⟩⟨↑⟩ @ l ])
    by (eapply wft_lconv; [apply wft_pi; cbn; auto | apply lequiv_sym, lq_0l', Hwl]).
  assert (Hl : [ G ; Γ ,, tyVec l T zero @ l
                 ⊢g lam lzero l (tyFin zero) (elimEmpty l lzero T⟨↑⟩⟨↑⟩⟨↑⟩ (var 0))
                 : tyPi lzero l (tyFin zero) T⟨↑⟩⟨↑⟩ @ l ])
    by (eapply wf_lconv; [apply wf_lam; cbn; auto | apply lequiv_sym, lq_0l', Hwl]).
  (* validity *)
  assert (VF : VTyG G (Γ ,, tyVec l T zero @ l) (tyFin zero) (tyFin zero) lzero) by exact (VG_fin VG_zero).
  assert (VT2 : VTyG G (Γ ,, tyVec l T zero @ l ,, tyFin zero @ lzero) T⟨↑⟩⟨↑⟩ T'⟨↑⟩⟨↑⟩ l)
    by (do 2 apply VG_shift; exact VT).
  assert (VE : VTmG G (Γ ,, tyVec l T zero @ l ,, tyFin zero @ lzero
                 ) (elimEmpty l lzero T⟨↑⟩⟨↑⟩⟨↑⟩ (var 0)) (elimEmpty l' lzero T'⟨↑⟩⟨↑⟩⟨↑⟩ (var 0)) T⟨↑⟩⟨↑⟩ l).
  { rewrite <- EE at 2. apply VG_elimEmpty; auto using lequiv_refl.
    - do 3 apply VG_shift; exact VT.
    - eapply VTmG_conv; [vvar | exact (VTyG_sym VG_fin_zero)]. }
  eapply VTmG_lconv; [| apply lequiv_sym, lmax_idem, Hwl].
  apply VG_lam; auto using lequiv_sym.
  - apply VG_vec; auto using VG_zero.
  - eapply VTyG_lconv; [| apply lequiv_sym, lq_0l', Hwl].
    exact (VTyG_refl_l (VG_pi Hw0 Hwl (lequiv_refl _ _ Hw0) (lequiv_sym _ _ _ Hll) HT2 VF VT2)).
  - eapply VTmG_lconv; [| apply lequiv_sym, lq_0l', Hwl].
    exact (VG_lam Hw0 Hwl (lequiv_refl _ _ Hw0) (lequiv_sym _ _ _ Hll) HT2 He VF (VTyG_refl_l VT2) VE).
Qed.

Lemma nth_step_V :
  VTmG G (Γ ,, tyNat @ lzero ,, nthMot l T @ l) (nthStep l T) (nthStep l' T') (nthMot l T)[lsucc] l.
Proof using EL HT Hll Hwl VL VN VT.
  pose proof (ctx_of_wf_ty ge_typeof HT) as H0. pose proof ge_notV as Hv. pose proof ge_compt as Hc.
  assert (Hw0 : lwf (gL G) lzero) by (cbn; auto).
  pose proof (nth_mot_wf ge_typeof ge_notV Hwl HT) as HM. pose proof (ctx_of_wf_ty ge_typeof HM) as H1.
  assert (H2 : [ G ; Γ ,, tyNat @ lzero ,, nthMot l T @ l ⊢g ]) by (apply ext_wf_g; auto).
  rewrite nth_ES. unfold nthStep.
  set (Δ0 := Γ ,, tyNat @ lzero ,, nthMot l T @ l) in *.
  assert (HV : [ G ; Δ0 ⊢g tyVec l T⟨↑⟩⟨↑⟩ (succ (var 1)) @ l ])
    by (apply wft_vec; auto; [gwkn HT | apply wf_succ; auto; gvar]).
  assert (H3 : [ G ; Δ0 ,, tyVec l T⟨↑⟩⟨↑⟩ (succ (var 1)) @ l ⊢g ]) by (apply ext_wf_g; auto).
  assert (HF : [ G ; Δ0 ,, tyVec l T⟨↑⟩⟨↑⟩ (succ (var 1)) @ l ⊢g tyFin (succ (var 2)) @ lzero ])
    by (apply wft_fin; auto; apply wf_succ; auto; gvar).
  set (Δ1 := Δ0 ,, tyVec l T⟨↑⟩⟨↑⟩ (succ (var 1)) @ l ,, tyFin (succ (var 2)) @ lzero).
  assert (H4 : [ G ; Δ1 ⊢g ]) by (apply ext_wf_g; cbn; auto).
  assert (Hk : [ G ; Δ1 ⊢g var 3 : tyNat @ lzero ]) by gvar.
  assert (HU : [ G ; Δ1 ⊢g tyUnit lzero @ lzero ]) by (apply wft_unit; cbn; auto; now rewrite ge_typeof).
  assert (HFk : [ G ; Δ1 ⊢g tyFin (var 3) @ lzero ]) by (apply wft_fin; auto).
  assert (HS : [ G ; Δ1 ⊢g tySum lzero lzero (tyUnit lzero) (tyFin (var 3)) @ lmax lzero lzero ])
    by (apply wft_sum; cbn; auto).
  assert (H5 : [ G ; Δ1 ,, tySum lzero lzero (tyUnit lzero) (tyFin (var 3)) @ lmax lzero lzero ⊢g ])
    by (apply ext_wf_g; cbn; auto).
  assert (H5u : [ G ; Δ1 ,, tyUnit lzero @ lzero ⊢g ]) by (apply ext_wf_g; cbn; auto).
  assert (H5f : [ G ; Δ1 ,, tyFin (var 3) @ lzero ⊢g ]) by (apply ext_wf_g; cbn; auto).
  assert (HT4 : [ G ; Δ1 ⊢g T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ @ l ]) by gwkn HT.
  assert (HT5 : [ G ; Δ1 ,, tySum lzero lzero (tyUnit lzero) (tyFin (var 3)) @ lmax lzero lzero
                  ⊢g T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ @ l ]) by gwkn HT.
  (* the tuple, as a pair, in either branch *)
  assert (Hcs : forall X, [ G ; Δ1 ,, X @ lzero ⊢g ] ->
            [ G ; Δ1 ,, X @ lzero ⊢g var 2 : tySig l l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 5)) @ lmax l l ]
            /\ [ G ; Δ1 ,, X @ lzero ⊢g T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ @ l ]
            /\ [ G ; Δ1 ,, X @ lzero ,, T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ @ l ⊢g tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 5) @ l ]).
  { intros X HX. assert (HTx : [ G ; Δ1 ,, X @ lzero ⊢g T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ @ l ]) by gwkn HT.
    assert (HX5 : [ G ; Δ1 ,, X @ lzero ,, T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ @ l ⊢g ]) by (apply ext_wf_g; auto).
    assert (Hk4 : [ G ; Δ1 ,, X @ lzero ⊢g var 4 : tyNat @ lzero ]) by gvar.
    split; [|split; [exact HTx|]].
    - eapply wf_lconv; [| apply lq_ll, Hwl]. eapply (conv_tm' ge_typeof); [gvar|].
      apply eqty_sym, eqty_vec_succ; auto.
    - apply wft_vec; auto; [gwkn HT | gvar]. }
  (* the tuple, as a pair, in either branch: validity *)
  assert (VCs : forall X, VTmG G (Δ1 ,, X @ lzero) (var 2) (var 2)
            (tySig l l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 5))) (lmax l l)).
  { intros X. eapply VTmG_conv; [eapply VTmG_lconv; [vvar | apply lq_ll, Hwl] |].
    eapply VTyG_lconv; [| apply lq_ll, Hwl]. apply VTyG_sym.
    refine (VG_vec_succ (n := var 4) (n' := var 4) Hwl (lequiv_refl _ _ Hwl) _ _).
    - do 5 apply VG_shift. exact (VTyG_refl_l VT).
    - vvar. }
  assert (VT5 : forall X k, VTyG G (Δ1 ,, X @ k) T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ T'⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ l)
    by (intros; do 5 apply VG_shift; exact VT).
  assert (VV5 : forall X k, VTyG G (Δ1 ,, X @ k ,, T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ @ l)
                  (tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 5)) (tyVec l' T'⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 5)) l)
    by (intros; apply VG_vec; auto; [do 6 apply VG_shift; exact VT | vvar]).
  (* the head *)
  destruct (Hcs _ H5u) as (Hpu & HTu & HVu).
  assert (Ec1 : (T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨rlift ↑⟩)[lsingle (tmInl lzero lzero (tyUnit lzero)⟨↑⟩ (tyFin (var 3))⟨↑⟩ (var 0))]
                = T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) by teq.
  assert (Vc1 : VTmG G (Δ1 ,, tyUnit lzero @ lzero)
            (tmFst l l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 5)) (var 2))
            (tmFst l' l' T'⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (tyVec l' T'⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 5)) (var 2))
            (T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨rlift ↑⟩)[lsingle (tmInl lzero lzero (tyUnit lzero)⟨↑⟩ (tyFin (var 3))⟨↑⟩ (var 0))] l).
  { rewrite Ec1. apply VG_fst; auto using lequiv_sym. }
  (* the tail, recursively *)
  destruct (Hcs _ H5f) as (Hpf & HTf & HVf).
  set (Δ2 := Δ1 ,, tyFin (var 3) @ lzero) in *.
  assert (Hk4 : [ G ; Δ2 ⊢g var 4 : tyNat @ lzero ]) by gvar.
  assert (HF4 : [ G ; Δ2 ⊢g tyFin (var 4) @ lzero ]) by (apply wft_fin; auto).
  assert (H6 : [ G ; Δ2 ,, tyFin (var 4) @ lzero ⊢g ]) by (apply ext_wf_g; cbn; auto).
  assert (HV4 : [ G ; Δ2 ⊢g tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4) @ l ]) by (apply wft_vec; auto).
  assert (H7 : [ G ; Δ2 ,, tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4) @ l ⊢g ]) by (apply ext_wf_g; auto).
  assert (HF5 : [ G ; Δ2 ,, tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4) @ l ⊢g tyFin (var 5) @ lzero ])
    by (apply wft_fin; auto; gvar).
  assert (H8 : [ G ; Δ2 ,, tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4) @ l ,, tyFin (var 5) @ lzero ⊢g ])
    by (apply ext_wf_g; cbn; auto).
  assert (HT6 : [ G ; Δ2 ,, tyFin (var 4) @ lzero ⊢g T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ @ l ]) by gwkn HT.
  assert (HT7 : [ G ; Δ2 ,, tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4) @ l ,, tyFin (var 5) @ lzero
                  ⊢g T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ @ l ]) by gwkn HT.
  assert (HP7 : [ G ; Δ2 ,, tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4) @ l
                  ⊢g tyPi lzero l (tyFin (var 5)) T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ @ l ])
    by (eapply wft_lconv; [apply wft_pi; cbn; auto | apply lequiv_sym, lq_0l', Hwl]).
  assert (Emot : (nthMot l T)⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩
                 = tyPi l l (tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4))
                     (tyPi lzero l (tyFin (var 5)) T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩))
    by (unfold nthMot; push_ren; f_equal; f_equal; teq).
  set (sd := tmSnd l l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 5)) (var 2)).
  assert (Esnd : (tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 5))[lsingle (tmFst l l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩
                   (tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 5)) (var 2))]
                 = tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4))
    by (push_subst; f_equal; try teq; pw).
  assert (Eapp1 : (tyPi lzero l (tyFin (var 5)) T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩)[lsingle sd]
                  = tyPi lzero l (tyFin (var 4)) T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩)
    by (push_subst; f_equal; try teq; pw).
  assert (Eapp2 : T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩[lsingle (var 0)] = T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) by teq.
  assert (Ec2 : (T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨rlift ↑⟩)[lsingle (tmInr lzero lzero (tyUnit lzero)⟨↑⟩ (tyFin (var 3))⟨↑⟩ (var 0))]
                = T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) by teq.
  assert (Hsd : [ G ; Δ2 ⊢g sd : tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4) @ l ])
    by (eapply wf_tm_retype; [apply wf_snd; eauto | exact Esnd]).
  assert (Hr : [ G ; Δ2 ⊢g var 3 : tyPi l l (tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4))
                     (tyPi lzero l (tyFin (var 5)) T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) @ lmax l l ])
    by (eapply wf_lconv; [| apply lq_ll, Hwl]; gvar; exact Emot).
  assert (Hrec : [ G ; Δ2 ⊢g app (var 3) l l (tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4))
                     (tyPi lzero l (tyFin (var 5)) T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) sd
                     : tyPi lzero l (tyFin (var 4)) T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ @ lmax lzero l ])
    by (eapply wf_lconv; [| apply lq_0l', Hwl]; eapply wf_tm_retype; [apply wf_app; auto | exact Eapp1]).
  assert (Hv0 : [ G ; Δ2 ⊢g var 0 : tyFin (var 4) @ lzero ]) by gvar.
  assert (Hc2 : [ G ; Δ2 ⊢g app (app (var 3) l l (tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4))
                     (tyPi lzero l (tyFin (var 5)) T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) sd)
                     lzero l (tyFin (var 4)) T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 0) : T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ @ l ])
    by (eapply wf_tm_retype; [apply wf_app; cbn; auto | exact Eapp2]).
  (* the tail's validity *)
  assert (VF4 : VTyG G Δ2 (tyFin (var 4)) (tyFin (var 4)) lzero) by (apply VG_fin; vvar).
  assert (VV4 : VTyG G Δ2 (tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4)) (tyVec l' T'⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4)) l)
    by (apply VG_vec; auto; [do 5 apply VG_shift; exact VT | vvar]).
  assert (VP7 : VTyG G (Δ2 ,, tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4) @ l)
                  (tyPi lzero l (tyFin (var 5)) T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩)
                  (tyPi lzero l' (tyFin (var 5)) T'⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) l).
  { eapply VTyG_lconv; [| apply lequiv_sym, lq_0l', Hwl].
    refine (VG_pi Hw0 Hwl (lequiv_refl _ _ Hw0) (lequiv_sym _ _ _ Hll) HT7 _ _).
    - apply VG_fin. vvar.
    - do 7 apply VG_shift. exact VT. }
  assert (VS : VTmG G Δ2 sd
                 (tmSnd l' l' T'⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (tyVec l' T'⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 5)) (var 2))
                 (tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4)) l).
  { rewrite <- Esnd.
    exact (VG_snd Hwl Hwl (lequiv_sym _ _ _ Hll) (lequiv_sym _ _ _ Hll) HVf (VT5 _ _) (VV5 _ _) (VCs _)). }
  assert (Vr : VTmG G Δ2 (var 3) (var 3) (tyPi l l (tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4))
                     (tyPi lzero l (tyFin (var 5)) T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩)) (lmax l l)).
  { eapply VTmG_lconv; [| apply lq_ll, Hwl]. eapply VG_var; [repeat constructor | exact Emot]. }
  assert (Vrec : VTmG G Δ2 (app (var 3) l l (tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4))
                     (tyPi lzero l (tyFin (var 5)) T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) sd)
                   (app (var 3) l' l' (tyVec l' T'⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4))
                     (tyPi lzero l' (tyFin (var 5)) T'⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩)
                     (tmSnd l' l' T'⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (tyVec l' T'⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 5)) (var 2)))
                   (tyPi lzero l (tyFin (var 4)) T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (lmax lzero l)).
  { eapply VTmG_lconv; [| apply lq_0l', Hwl]. rewrite <- Eapp1.
    apply VG_app; auto using lequiv_sym. }
  assert (Vc2 : VTmG G Δ2
            (app (app (var 3) l l (tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4))
                     (tyPi lzero l (tyFin (var 5)) T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) sd)
                     lzero l (tyFin (var 4)) T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 0))
            (app (app (var 3) l' l' (tyVec l' T'⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4))
                     (tyPi lzero l' (tyFin (var 5)) T'⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩)
                     (tmSnd l' l' T'⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (tyVec l' T'⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 5)) (var 2)))
                     lzero l' (tyFin (var 4)) T'⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 0))
            (T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨rlift ↑⟩)[lsingle (tmInr lzero lzero (tyUnit lzero)⟨↑⟩ (tyFin (var 3))⟨↑⟩ (var 0))] l).
  { rewrite Ec2. eapply VTmG_retype; [| exact Eapp2].
    refine (VG_app Hw0 Hwl (lequiv_refl _ _ Hw0) (lequiv_sym _ _ _ Hll) HT6 VF4 _ Vrec _).
    - do 6 apply VG_shift. exact VT.
    - vvar. }
  (* the [case] *)
  assert (Hc1 : [ G ; Δ1 ,, tyUnit lzero @ lzero ⊢g
                  tmFst l l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 5)) (var 2)
                  : (T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨rlift ↑⟩)[lsingle (tmInl lzero lzero (tyUnit lzero)⟨↑⟩ (tyFin (var 3))⟨↑⟩ (var 0))] @ l ])
    by (rewrite Ec1; apply wf_fst; eauto).
  assert (Hc2' : [ G ; Δ2 ⊢g
                  app (app (var 3) l l (tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4))
                     (tyPi lzero l (tyFin (var 5)) T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) sd)
                     lzero l (tyFin (var 4)) T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 0)
                  : (T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨rlift ↑⟩)[lsingle (tmInr lzero lzero (tyUnit lzero)⟨↑⟩ (tyFin (var 3))⟨↑⟩ (var 0))] @ l ])
    by (rewrite Ec2; exact Hc2).
  assert (Hscr : [ G ; Δ1 ⊢g var 0 : tySum lzero lzero (tyUnit lzero) (tyFin (var 3)) @ lmax lzero lzero ]).
  { eapply wf_lconv; [| apply lq_ll; cbn; auto]. eapply (conv_tm' ge_typeof); [gvar|].
    apply eqty_sym, eqty_fin_succ; auto. }
  assert (Ecase : T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩[lsingle (var 0)] = T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) by teq.
  set (body := tmCase lzero lzero l (tyUnit lzero) (tyFin (var 3)) T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩
                 (tmFst l l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 5)) (var 2))
                 (app (app (var 3) l l (tyVec l T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4))
                     (tyPi lzero l (tyFin (var 5)) T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) sd)
                     lzero l (tyFin (var 4)) T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 0))
                 (var 0)).
  assert (HB : [ G ; Δ1 ⊢g body : T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ @ l ])
    by (eapply wf_tm_retype; [apply wf_case; cbn; auto | exact Ecase]).
  assert (VB : VTmG G Δ1 body
                 (tmCase lzero lzero l' (tyUnit lzero) (tyFin (var 3)) T'⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩
                    (tmFst l' l' T'⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (tyVec l' T'⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 5)) (var 2))
                    (app (app (var 3) l' l' (tyVec l' T'⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 4))
                       (tyPi lzero l' (tyFin (var 5)) T'⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩)
                       (tmSnd l' l' T'⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (tyVec l' T'⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 5)) (var 2)))
                       lzero l' (tyFin (var 4)) T'⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ (var 0))
                    (var 0))
                 T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ l).
  { eapply VTmG_retype; [| exact Ecase]. unfold body.
    refine (VG_case Hw0 Hw0 Hwl (VG_unit Hw0 (lequiv_refl _ _ Hw0)) _ (VT5 _ _) Vc1 Vc2
              (lequiv_refl _ _ Hw0) (lequiv_refl _ _ Hw0) Hll _).
    - apply VG_fin. vvar.
    - eapply VTmG_conv; [eapply VTmG_lconv; [vvar | apply lmax_idem, Hw0] |].
      eapply VTyG_lconv; [| apply lmax_idem, Hw0]. apply VTyG_sym.
      refine (VG_fin_succ (n := var 3) _). vvar. }
  (* the two [λ]s *)
  assert (HV2 : VTyG G Δ0 (tyVec l T⟨↑⟩⟨↑⟩ (succ (var 1))) (tyVec l' T'⟨↑⟩⟨↑⟩ (succ (var 1))) l)
    by (apply VG_vec; auto; [do 2 apply VG_shift; exact VT | apply VG_succ; vvar]).
  assert (HF2 : VTyG G (Δ0 ,, tyVec l T⟨↑⟩⟨↑⟩ (succ (var 1)) @ l) (tyFin (succ (var 2))) (tyFin (succ (var 2))) lzero)
    by (apply VG_fin, VG_succ; vvar).
  assert (VT4 : VTyG G Δ1 T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ T'⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ l) by (do 4 apply VG_shift; exact VT).
  assert (HPi : [ G ; Δ0 ,, tyVec l T⟨↑⟩⟨↑⟩ (succ (var 1)) @ l
                  ⊢g tyPi lzero l (tyFin (succ (var 2))) T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ @ l ])
    by (eapply wft_lconv; [apply wft_pi; cbn; auto | apply lequiv_sym, lq_0l', Hwl]).
  assert (HL : [ G ; Δ0 ,, tyVec l T⟨↑⟩⟨↑⟩ (succ (var 1)) @ l
                 ⊢g lam lzero l (tyFin (succ (var 2))) body : tyPi lzero l (tyFin (succ (var 2))) T⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ @ l ])
    by (eapply wf_lconv; [apply wf_lam; cbn; auto | apply lequiv_sym, lq_0l', Hwl]).
  eapply VTmG_lconv; [| apply lequiv_sym, lmax_idem, Hwl].
  refine (VG_lam Hwl Hwl (lequiv_sym _ _ _ Hll) (lequiv_sym _ _ _ Hll) HPi HL HV2 _ _).
  - eapply VTyG_lconv; [| apply lequiv_sym, lq_0l', Hwl].
    exact (VTyG_refl_l (VG_pi Hw0 Hwl (lequiv_refl _ _ Hw0) (lequiv_sym _ _ _ Hll) HT4 HF2 VT4)).
  - eapply VTmG_lconv; [| apply lequiv_sym, lq_0l', Hwl].
    exact (VG_lam Hw0 Hwl (lequiv_refl _ _ Hw0) (lequiv_sym _ _ _ Hll) HT4 HB HF2 (VTyG_refl_l VT4) VB).
Qed.

(** MX §13's index lemma: [nth] at related lengths, tuples and indices. *)
Lemma V_nth {k k' cs cs' i i'} : [ G ; Γ ⊢g k : tyNat @ lzero ] ->
  VTmG G Γ k k' tyNat lzero -> VTmG G Γ cs cs' (tyVec l T k) l -> VTmG G Γ i i' (tyFin k) lzero ->
  VTmG G Γ (tmNth l T k cs i) (tmNth l' T' k' cs' i') T l.
Proof using EL HT Hll Hwl VL VN VT.
  intros Hk Vk Vcs Vi. pose proof (ctx_of_wf_ty ge_typeof HT) as H0. pose proof ge_notV as Hv.
  pose proof (wf_ty_nf HT) as NT. pose proof (wf_tm_nf Hk) as Nk.
  assert (Hw0 : lwf (gL G) lzero) by (cbn; auto).
  assert (HV : [ G ; Γ ⊢g tyVec l T k @ l ]) by (apply wft_vec; auto).
  assert (H1 : [ G ; Γ ,, tyVec l T k @ l ⊢g ]) by (apply ext_wf_g; auto).
  assert (HF : [ G ; Γ ⊢g tyFin k @ lzero ]) by (apply wft_fin; auto).
  assert (H2 : [ G ; Γ ,, tyFin k @ lzero ⊢g ]) by (apply ext_wf_g; cbn; auto).
  assert (Hk1 : [ G ; Γ ,, tyVec l T k @ l ⊢g k⟨↑⟩ : tyNat @ lzero ])
    by (eapply wf_tm_retype; [gwkn Hk | reflexivity]).
  assert (HF1 : [ G ; Γ ,, tyVec l T k @ l ⊢g tyFin k⟨↑⟩ @ lzero ]) by (apply wft_fin; auto).
  assert (H3 : [ G ; Γ ,, tyVec l T k @ l ,, tyFin k⟨↑⟩ @ lzero ⊢g ]) by (apply ext_wf_g; cbn; auto).
  assert (HT1 : [ G ; Γ ,, tyFin k @ lzero ⊢g T⟨↑⟩ @ l ]) by gwkn HT.
  assert (HT2 : [ G ; Γ ,, tyVec l T k @ l ,, tyFin k⟨↑⟩ @ lzero ⊢g T⟨↑⟩⟨↑⟩ @ l ]) by gwkn HT.
  assert (HP : [ G ; Γ ,, tyVec l T k @ l ⊢g tyPi lzero l (tyFin k⟨↑⟩) T⟨↑⟩⟨↑⟩ @ l ])
    by (eapply wft_lconv; [apply wft_pi; cbn; auto | apply lequiv_sym, lq_0l', Hwl]).
  pose proof (nth_mot_wf ge_typeof ge_notV Hwl HT) as HM.
  pose proof (nth_base_wf ge_typeof ge_notV Hwl HT) as Hs.
  pose proof (nth_step_wf ge_typeof ge_notV Hwl HT) as Hz.
  pose proof (VG_natrec Hwl Hll HM Hs Hz nth_mot_V nth_base_V nth_step_V Vk) as VNr.
  rewrite nth_Ek in VNr by assumption.
  assert (VP : VTyG G (Γ ,, tyVec l T k @ l) (tyPi lzero l (tyFin k⟨↑⟩) T⟨↑⟩⟨↑⟩)
                 (tyPi lzero l' (tyFin k'⟨↑⟩) T'⟨↑⟩⟨↑⟩) l).
  { eapply VTyG_lconv; [| apply lequiv_sym, lq_0l', Hwl].
    refine (VG_pi Hw0 Hwl (lequiv_refl _ _ Hw0) (lequiv_sym _ _ _ Hll) HT2 _ _).
    - apply VG_fin. exact (VG_shift_tm Vk).
    - do 2 apply VG_shift. exact VT. }
  pose proof (VG_app Hwl Hwl (lequiv_sym _ _ _ Hll) (lequiv_sym _ _ _ Hll) HP (VG_vec Hwl Hll VT Vk) VP
                (VTmG_lconv VNr (lq_ll Hwl)) Vcs) as VA1.
  rewrite nth_Ecs in VA1 by assumption.
  unfold tmNth. eapply VTmG_retype; [| exact (shift_single_ty T i NT)].
  exact (VG_app Hw0 Hwl (lequiv_refl _ _ Hw0) (lequiv_sym _ _ _ Hll) HT1 (VG_fin Vk) (VG_shift VT)
           (VTmG_lconv VA1 (lq_0l' Hwl)) Vi).
Qed.

End NthV.

End WfNth.
