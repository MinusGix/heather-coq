(** * Presupposition and inversion at every layer (M7_DESIGN.md C1, J3.1)

    [Presupposition] and [Inversion] are for layers with [typeof i = i].
    At V and C a judgment lifts to [typeof i] (D), which gives the
    presuppositions there. Inversion at any layer is the same induction,
    with the type equation at [typeof i], where [wf_conv]'s lives; the
    M-only heads are typed at M only ([i = lM]), where [Inversion]
    applies. *)
From DeLaM.Typing Require Export Inversion CtxConv.

(** ** Presupposition *)

Lemma wf_tm_ty_any {G i Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Γ ⊢[ typeof i ] T @ l ].
Proof. intros H. exact (wf_tm_ty (typeof_idem i) (lift_tm H (lle_self_typeof i))). Qed.

Lemma ctx_of_tm_any {G i Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Γ ⊢[ typeof i ] ].
Proof. intros H. exact (ctx_of_wf_tm (typeof_idem i) (lift_tm H (lle_self_typeof i))). Qed.

Lemma ctx_of_ty_any {G i Γ T l} : [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Γ ⊢[ typeof i ] ].
Proof. intros H. exact (ctx_of_wf_ty (typeof_idem i) (lift_ty H (lle_self_typeof i))). Qed.

(** ** Inversion *)

Ltac inv_tm_any :=
  let H := fresh "H" in let E := fresh "E" in let HW := fresh "HW" in
  intros H; pose proof (wf_tm_ty_any H) as HW; revert HW;
  match type of H with wf_tm _ _ _ ?t _ _ => let u := fresh "u" in remember t as u eqn:E end;
  induction H; intros HW; try discriminate E;
  [> first
    [ (* wf_conv *)
      match goal with
      | IH : ?a = ?b -> _ -> _, E' : ?a = ?b, Heq : eq_ty _ (typeof ?j) _ _ _ _ |- _ =>
          let IH' := fresh "IH'" in
          pose proof (IH E' (eqty_wf_r (typeof_idem j) Heq)) as IH'; clear IH;
          repeat match type of IH' with
                 | ex _ => let x := fresh "x" in destruct IH' as [x IH']; exists x
                 end;
          let HP := fresh "HP" in let Hk := fresh "Hk" in let HT := fresh "HT" in
          destruct IH' as [HP [Hk HT]]; split; [exact HP|]; split; [exact Hk|];
          eapply eqty_trans; eassumption
      end
    | (* wf_lconv *)
      match goal with
      | IH : ?a = ?b -> _ -> _, E' : ?a = ?b, Hl : lequiv _ _ _ |- _ =>
          let IH' := fresh "IH'" in
          pose proof (IH E' (wft_lconv _ _ _ _ _ _ HW (lequiv_sym _ _ _ Hl))) as IH'; clear IH;
          repeat match type of IH' with
                 | ex _ => let x := fresh "x" in destruct IH' as [x IH']; exists x
                 end;
          let HP := fresh "HP" in let Hk := fresh "Hk" in let HT := fresh "HT" in
          destruct IH' as [HP [Hk HT]]; split; [exact HP|]; split;
          [ exact (lvl_eq_lequiv Hl Hk) | eapply eqty_lconv; eassumption ]
      end
    | (* the head's rule *)
      (try injection E); intros; subst; repeat match goal with |- ex _ => eexists end;
      split; [| split; [left; reflexivity | apply eqty_refl; exact HW]];
      conj_assumption ] ..].

Lemma inva_var {G i Γ n T k} : [ G ; Γ ⊢[ i ] var n : T @ k ] ->
  exists T0 l0, ([ G ; Γ ⊢[ typeof i ] ] /\ in_ctx Γ n T0 l0) /\
    lvl_eq (gL G) k l0 /\ [ G ; Γ ⊢[ typeof i ] T ≅ T0 @ k ].
Proof. inv_tm_any. Qed.

Lemma inva_gvar {G i Γ u d T k} : [ G ; Γ ⊢[ i ] gvar u d : T @ k ] ->
  exists Δ i' T0 l0, ([ G ; Γ ⊢[ typeof i ] ] /\ in_gctx (gΨ G) u (gdTm Δ i' T0 l0) /\ lle i' i /\
    lsub_tail d Δ Γ /\ dnfl d /\
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n : A[d] @ k ])) /\
    lvl_eq (gL G) k l0 /\ [ G ; Γ ⊢[ typeof i ] T ≅ T0[d] @ k ].
Proof. inv_tm_any. Qed.

Lemma inva_gdef {G i Γ u t d T k} : [ G ; Γ ⊢[ i ] gdef u t d : T @ k ] ->
  exists Δ T0 l0 t0, ([ G ; Γ ⊢[ typeof i ] ] /\ in_gctx (gΨ G) u (gdDef Δ T0 l0 t0) /\ tm_leq t0 t /\
    lle lC i /\ lsub_tail d Δ Γ /\ dnfl d /\
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n : A[d] @ k ]) /\
    [ G ; Δ ⊢[ i ] t : T0 @ l0 ]) /\
    lvl_eq (gL G) k l0 /\ [ G ; Γ ⊢[ typeof i ] T ≅ T0[d] @ k ].
Proof. inv_tm_any. Qed.

Lemma inva_code_nat {G i Γ T k} : [ G ; Γ ⊢[ i ] tmNat : T @ k ] ->
  (i <> lV /\ [ G ; Γ ⊢[ typeof i ] ]) /\
    lvl_eq (gL G) k (lsuc lzero) /\ [ G ; Γ ⊢[ typeof i ] T ≅ tyU lzero @ k ].
Proof. inv_tm_any. Qed.

Lemma inva_code_U {G i Γ l T k} : [ G ; Γ ⊢[ i ] tmU l : T @ k ] ->
  (i <> lV /\ [ G ; Γ ⊢[ typeof i ] ] /\ lwf (gL G) l) /\
    lvl_eq (gL G) k (lsuc (lsuc l)) /\ [ G ; Γ ⊢[ typeof i ] T ≅ tyU (lsuc l) @ k ].
Proof. inv_tm_any. Qed.

Lemma inva_code_pi {G i Γ l l' s t T k} : [ G ; Γ ⊢[ i ] tmPi l l' s t : T @ k ] ->
  (i <> lV /\ lwf (gL G) l /\ lwf (gL G) l' /\ [ G ; Γ ⊢[ i ] s : tyU l @ lsuc l ] /\
    [ G ; Γ ,, tyEl l s @ l ⊢[ i ] t : tyU l' @ lsuc l' ]) /\
    lvl_eq (gL G) k (lsuc (lmax l l')) /\ [ G ; Γ ⊢[ typeof i ] T ≅ tyU (lmax l l') @ k ].
Proof. inv_tm_any. Qed.

Lemma inva_zero {G i Γ T k} : [ G ; Γ ⊢[ i ] zero : T @ k ] ->
  (i <> lV /\ [ G ; Γ ⊢[ typeof i ] ]) /\ lvl_eq (gL G) k lzero /\ [ G ; Γ ⊢[ typeof i ] T ≅ tyNat @ k ].
Proof. inv_tm_any. Qed.

Lemma inva_succ {G i Γ t T k} : [ G ; Γ ⊢[ i ] succ t : T @ k ] ->
  (i <> lV /\ [ G ; Γ ⊢[ i ] t : tyNat @ lzero ]) /\ lvl_eq (gL G) k lzero /\
    [ G ; Γ ⊢[ typeof i ] T ≅ tyNat @ k ].
Proof. inv_tm_any. Qed.

Lemma inva_natrec {G i Γ l M s z t T k} : [ G ; Γ ⊢[ i ] natrec l M s z t : T @ k ] ->
  (i <> lV /\ lwf (gL G) l /\ [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M @ l ] /\
    [ G ; Γ ⊢[ i ] s : M[lsingle zero] @ l ] /\
    [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ i ] z : M[lsucc] @ l ] /\
    [ G ; Γ ⊢[ i ] t : tyNat @ lzero ]) /\
    lvl_eq (gL G) k l /\ [ G ; Γ ⊢[ typeof i ] T ≅ M[lsingle t] @ k ].
Proof. inv_tm_any. Qed.

Lemma inva_lam {G i Γ l l' A t T k} : [ G ; Γ ⊢[ i ] lam l l' A t : T @ k ] ->
  exists B, (i <> lV /\ lwf (gL G) l /\ lwf (gL G) l' /\ [ G ; Γ ⊢[ i ] A @ l ] /\
    [ G ; Γ ,, A @ l ⊢[ i ] t : B @ l' ]) /\
    lvl_eq (gL G) k (lmax l l') /\ [ G ; Γ ⊢[ typeof i ] T ≅ tyPi l l' A B @ k ].
Proof. inv_tm_any. Qed.

Lemma inva_app {G i Γ l l' A B t s T k} : [ G ; Γ ⊢[ i ] app t l l' A B s : T @ k ] ->
  (i <> lV /\ lwf (gL G) l /\ lwf (gL G) l' /\ [ G ; Γ ⊢[ i ] A @ l ] /\
    [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] /\ [ G ; Γ ⊢[ i ] t : tyPi l l' A B @ lmax l l' ] /\
    [ G ; Γ ⊢[ i ] s : A @ l ]) /\
    lvl_eq (gL G) k l' /\ [ G ; Γ ⊢[ typeof i ] T ≅ B[lsingle s] @ k ].
Proof. inv_tm_any. Qed.

Lemma inva_code_sig {G i Γ l l' s t T k} : [ G ; Γ ⊢[ i ] tmSig l l' s t : T @ k ] ->
  (i <> lV /\ lwf (gL G) l /\ lwf (gL G) l' /\ [ G ; Γ ⊢[ i ] s : tyU l @ lsuc l ] /\
    [ G ; Γ ,, tyEl l s @ l ⊢[ i ] t : tyU l' @ lsuc l' ]) /\
    lvl_eq (gL G) k (lsuc (lmax l l')) /\ [ G ; Γ ⊢[ typeof i ] T ≅ tyU (lmax l l') @ k ].
Proof. inv_tm_any. Qed.

Lemma inva_pair {G i Γ l l' A B a b T k} : [ G ; Γ ⊢[ i ] tmPair l l' A B a b : T @ k ] ->
  (i <> lV /\ lwf (gL G) l /\ lwf (gL G) l' /\ [ G ; Γ ⊢[ i ] A @ l ] /\
    [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] /\ [ G ; Γ ⊢[ i ] a : A @ l ] /\
    [ G ; Γ ⊢[ i ] b : B[lsingle a] @ l' ]) /\
    lvl_eq (gL G) k (lmax l l') /\ [ G ; Γ ⊢[ typeof i ] T ≅ tySig l l' A B @ k ].
Proof. inv_tm_any. Qed.

Lemma inva_fst {G i Γ l l' A B p T k} : [ G ; Γ ⊢[ i ] tmFst l l' A B p : T @ k ] ->
  (i <> lV /\ lwf (gL G) l /\ lwf (gL G) l' /\ [ G ; Γ ⊢[ i ] A @ l ] /\
    [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] /\ [ G ; Γ ⊢[ i ] p : tySig l l' A B @ lmax l l' ]) /\
    lvl_eq (gL G) k l /\ [ G ; Γ ⊢[ typeof i ] T ≅ A @ k ].
Proof. inv_tm_any. Qed.

Lemma inva_snd {G i Γ l l' A B p T k} : [ G ; Γ ⊢[ i ] tmSnd l l' A B p : T @ k ] ->
  (i <> lV /\ lwf (gL G) l /\ lwf (gL G) l' /\ [ G ; Γ ⊢[ i ] A @ l ] /\
    [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] /\ [ G ; Γ ⊢[ i ] p : tySig l l' A B @ lmax l l' ]) /\
    lvl_eq (gL G) k l' /\ [ G ; Γ ⊢[ typeof i ] T ≅ B[lsingle (tmFst l l' A B p)] @ k ].
Proof. inv_tm_any. Qed.

Lemma inva_code_unit {G i Γ l T k} : [ G ; Γ ⊢[ i ] tmUnit l : T @ k ] ->
  (i <> lV /\ [ G ; Γ ⊢[ typeof i ] ] /\ lwf (gL G) l) /\
    lvl_eq (gL G) k (lsuc l) /\ [ G ; Γ ⊢[ typeof i ] T ≅ tyU l @ k ].
Proof. inv_tm_any. Qed.

Lemma inva_triv {G i Γ l T k} : [ G ; Γ ⊢[ i ] tmTriv l : T @ k ] ->
  (i <> lV /\ [ G ; Γ ⊢[ typeof i ] ] /\ lwf (gL G) l) /\
    lvl_eq (gL G) k l /\ [ G ; Γ ⊢[ typeof i ] T ≅ tyUnit l @ k ].
Proof. inv_tm_any. Qed.

(** Strict equality (M10a). *)
Lemma inva_srefl {G i Γ l A a T k} : [ G ; Γ ⊢[ i ] srefl l A a : T @ k ] ->
  (i <> lV /\ lwf (gL G) l /\ [ G ; Γ ⊢[ i ] A @ l ] /\ [ G ; Γ ⊢[ i ] a : A @ l ]) /\
    lvl_eq (gL G) k l /\ [ G ; Γ ⊢[ typeof i ] T ≅ tySEq l A a a @ k ].
Proof. inv_tm_any. Qed.

Lemma inva_elimSEmpty {G i Γ l l' M e T k} : [ G ; Γ ⊢[ i ] elimSEmpty l l' M e : T @ k ] ->
  (i <> lV /\ lwf (gL G) l /\ lwf (gL G) l' /\ [ G ; Γ ⊢[ i ] M @ l' ] /\
    [ G ; Γ ⊢[ i ] e : tySEmpty l @ l ]) /\ lvl_eq (gL G) k l' /\ [ G ; Γ ⊢[ typeof i ] T ≅ M @ k ].
Proof. inv_tm_any. Qed.

(** The identity type (M11a). *)
Lemma inva_idrefl {G i Γ l A a T k} : [ G ; Γ ⊢[ i ] tmRefl l A a : T @ k ] ->
  (i <> lV /\ lwf (gL G) l /\ [ G ; Γ ⊢[ i ] A @ l ] /\ [ G ; Γ ⊢[ i ] a : A @ l ]) /\
    lvl_eq (gL G) k l /\ [ G ; Γ ⊢[ typeof i ] T ≅ tyId l A a a @ k ].
Proof. inv_tm_any. Qed.

Lemma inva_J {G i Γ l l' A a M c u e T k} : [ G ; Γ ⊢[ i ] tmJ l l' A a M c u e : T @ k ] ->
  (i <> lV /\ lwf (gL G) l /\ lwf (gL G) l' /\ [ G ; Γ ⊢[ i ] A @ l ] /\ [ G ; Γ ⊢[ i ] a : A @ l ] /\
    [ G ; Γ ,, A @ l ⊢[ i ] tyId l A⟨↑⟩ a⟨↑⟩ (var 0) @ l ] /\
    [ G ; Γ ,, A @ l ,, tyId l A⟨↑⟩ a⟨↑⟩ (var 0) @ l ⊢[ i ] M @ l' ] /\
    [ G ; Γ ⊢[ i ] c : M[lsingle2 a (tmRefl l A a)] @ l' ] /\
    [ G ; Γ ⊢[ i ] u : A @ l ] /\ [ G ; Γ ⊢[ i ] e : tyId l A a u @ l ]) /\
    lvl_eq (gL G) k l' /\ [ G ; Γ ⊢[ typeof i ] T ≅ M[lsingle2 u e] @ k ].
Proof. inv_tm_any. Qed.

Lemma inva_code_id {G i Γ l s t u T k} : [ G ; Γ ⊢[ i ] tmId l s t u : T @ k ] ->
  (i <> lV /\ lwf (gL G) l /\ [ G ; Γ ⊢[ i ] s : tyU l @ lsuc l ] /\
    [ G ; Γ ⊢[ i ] t : tyEl l s @ l ] /\ [ G ; Γ ⊢[ i ] u : tyEl l s @ l ]) /\
    lvl_eq (gL G) k (lsuc l) /\ [ G ; Γ ⊢[ typeof i ] T ≅ tyU l @ k ].
Proof. inv_tm_any. Qed.

(** The empty type's eliminator (M12a). *)
Lemma inva_elimEmpty {G i Γ l l' M t T k} : [ G ; Γ ⊢[ i ] elimEmpty l l' M t : T @ k ] ->
  (compt i /\ lwf (gL G) l /\ lwf (gL G) l' /\ [ G ; Γ ,, tyEmpty l' @ l' ⊢[ i ] M @ l ] /\
    [ G ; Γ ⊢[ i ] t : tyEmpty l' @ l' ]) /\
    lvl_eq (gL G) k l /\ [ G ; Γ ⊢[ typeof i ] T ≅ M[lsingle t] @ k ].
Proof. inv_tm_any. Qed.

(** Binary sums (M12b). *)
Lemma inva_inl {G i Γ l l' A B a T k} : [ G ; Γ ⊢[ i ] tmInl l l' A B a : T @ k ] ->
  (compt i /\ lwf (gL G) l /\ lwf (gL G) l' /\ [ G ; Γ ⊢[ i ] A @ l ] /\ [ G ; Γ ⊢[ i ] B @ l' ] /\
    [ G ; Γ ⊢[ i ] a : A @ l ]) /\
    lvl_eq (gL G) k (lmax l l') /\ [ G ; Γ ⊢[ typeof i ] T ≅ tySum l l' A B @ k ].
Proof. inv_tm_any. Qed.

Lemma inva_inr {G i Γ l l' A B b T k} : [ G ; Γ ⊢[ i ] tmInr l l' A B b : T @ k ] ->
  (compt i /\ lwf (gL G) l /\ lwf (gL G) l' /\ [ G ; Γ ⊢[ i ] A @ l ] /\ [ G ; Γ ⊢[ i ] B @ l' ] /\
    [ G ; Γ ⊢[ i ] b : B @ l' ]) /\
    lvl_eq (gL G) k (lmax l l') /\ [ G ; Γ ⊢[ typeof i ] T ≅ tySum l l' A B @ k ].
Proof. inv_tm_any. Qed.

Lemma inva_case {G i Γ l l' l'' A B M c1 c2 t T k} : [ G ; Γ ⊢[ i ] tmCase l l' l'' A B M c1 c2 t : T @ k ] ->
  (compt i /\ lwf (gL G) l /\ lwf (gL G) l' /\ lwf (gL G) l'' /\
    [ G ; Γ ⊢[ i ] A @ l ] /\ [ G ; Γ ⊢[ i ] B @ l' ] /\
    [ G ; Γ ,, tySum l l' A B @ lmax l l' ⊢[ i ] M @ l'' ] /\
    [ G ; Γ ,, A @ l ⊢[ i ] c1 : M⟨rlift ↑⟩[lsingle (tmInl l l' A⟨↑⟩ B⟨↑⟩ (var 0))] @ l'' ] /\
    [ G ; Γ ,, B @ l' ⊢[ i ] c2 : M⟨rlift ↑⟩[lsingle (tmInr l l' A⟨↑⟩ B⟨↑⟩ (var 0))] @ l'' ] /\
    [ G ; Γ ⊢[ i ] t : tySum l l' A B @ lmax l l' ]) /\
    lvl_eq (gL G) k l'' /\ [ G ; Γ ⊢[ typeof i ] T ≅ M[lsingle t] @ k ].
Proof. inv_tm_any. Qed.

(** Strict equality's codes (M10c). *)
Lemma inva_code_seq {G i Γ l s t u T k} : [ G ; Γ ⊢[ i ] tmSEq l s t u : T @ k ] ->
  (i <> lV /\ lwf (gL G) l /\ [ G ; Γ ⊢[ i ] s : tyU l @ lsuc l ] /\
    [ G ; Γ ⊢[ i ] t : tyEl l s @ l ] /\ [ G ; Γ ⊢[ i ] u : tyEl l s @ l ]) /\
    lvl_eq (gL G) k (lsuc l) /\ [ G ; Γ ⊢[ typeof i ] T ≅ tyU l @ k ].
Proof. inv_tm_any. Qed.

Lemma inva_code_sempty {G i Γ l T k} : [ G ; Γ ⊢[ i ] tmSEmpty l : T @ k ] ->
  (i <> lV /\ [ G ; Γ ⊢[ typeof i ] ] /\ lwf (gL G) l) /\
    lvl_eq (gL G) k (lsuc l) /\ [ G ; Γ ⊢[ typeof i ] T ≅ tyU l @ k ].
Proof. inv_tm_any. Qed.

(** ** The M-only heads *)

(** Terms whose rules are at M only. *)
Definition m_only (t : tm) : Prop :=
  match t with
  | boxT _ | boxt _ | letboxT _ _ _ _ _ _ | letboxt _ _ _ _ _ _ _ | elimT _ _ _ _ _ _
  | elimt _ _ _ _ _ _ _ | ulam _ _ _ _ | uapp _ _ | clam _ _ _ | capp _ _ | tlam _ _ _ _ _ | tapp _ _ => True
  | _ => False
  end.

Lemma typed_m_only {G i Γ t T k} : [ G ; Γ ⊢[ i ] t : T @ k ] -> m_only t -> i = lM.
Proof. intros H Hm. induction H; cbn in Hm; first [contradiction | auto]. Qed.

(** The bundle's nodes and [tmErr] are never typed. *)
Definition junk (t : tm) : Prop :=
  match t with tmErr | tmTy _ | tmTup _ _ | bindU _ | bindG _ | bindL _ => True | _ => False end.

Lemma no_junk {G i Γ t T k} : [ G ; Γ ⊢[ i ] t : T @ k ] -> junk t -> False.
Proof. intros H Hj. induction H; cbn in Hj; first [contradiction | auto]. Qed.

(** Not typed at V (the variables are). *)
Definition v_typable (t : tm) : Prop := match t with var _ | gvar _ _ => True | _ => False end.

Lemma typed_V {G Γ t T k} : ~ v_typable t -> ~ [ G ; Γ ⊢[ lV ] t : T @ k ].
Proof.
  intros Hv H. remember lV as i eqn:Ei. induction H; subst; cbn in Hv; try congruence; auto;
    try match goal with Hm : lM = lV |- _ => discriminate Hm end;
    try match goal with c : compt lV |- _ => destruct c; discriminate end;
    try match goal with Hl : lle lC lV |- _ => unfold lle in Hl; cbn in Hl; lia end.
Qed.

(** No type is well formed at V. *)
Lemma no_ty_V {G Γ T k} : ~ [ G ; Γ ⊢[ lV ] T @ k ].
Proof.
  intros H. remember lV as i eqn:Ei. induction H; subst; try congruence; auto;
    try match goal with c : compt lV |- _ => destruct c; discriminate end.
Qed.
