(** * Typing inversion (M6_DESIGN.md H7)

    For every head, a typed term's premises hold and its type is equal to
    the rule's, at an equivalent level. The only generic typing rules are
    [wf_conv] and [wf_lconv], so each lemma is an induction on the typing
    derivation. The level part is [lvl_eq]: equal, or equivalent (no
    well-formedness needed for the head's case, ω included). For layers with
    [typeof i = i].

    Shape of each conclusion: [exists …, (premises) /\ lvl_eq L k l0 /\ T ≅ T0 @ k]. *)
From DeLaM.Typing Require Export Presupposition.

Definition lvl_eq (L : nat) (k l : lvl) : Prop := k = l \/ lequiv L k l.

Lemma lvl_eq_lequiv {L k l l'} : lequiv L l l' -> lvl_eq L l' k -> lvl_eq L l k.
Proof. intros Hl [<-|Hk]; right; [exact Hl | eapply lequiv_trans; eassumption]. Qed.

Lemma lvl_eq_wf {L k l} : lvl_eq L k l -> lwf L l -> lequiv L k l.
Proof. intros [->|Hk] Hl; [apply lequiv_refl, Hl | exact Hk]. Qed.

Ltac conj_assumption := first [ eassumption | split; conj_assumption ].

(** One induction for every inversion lemma. The motive carries the
    type's well-formedness (presupposition), so the head's case closes the
    equation by reflexivity. *)
Ltac inv_tm :=
  let Hi := fresh "Hi" in let H := fresh "H" in let E := fresh "E" in let HW := fresh "HW" in
  intros Hi H; pose proof (wf_tm_ty Hi H) as HW; revert Hi HW;
  match type of H with wf_tm _ _ _ ?t _ _ => let u := fresh "u" in remember t as u eqn:E end;
  induction H; intros Hi HW; try discriminate E;
  [> first
    [ (* wf_conv *)
      match goal with
      | IH : ?a = ?b -> typeof ?j = ?j -> _ -> _, E' : ?a = ?b,
        Heq : eq_ty _ (typeof ?j) _ _ _ _ |- _ =>
          rewrite Hi in Heq;
          let IH' := fresh "IH'" in pose proof (IH E' Hi (eqty_wf_r Hi Heq)) as IH'; clear IH;
          repeat match type of IH' with
                 | ex _ => let x := fresh "x" in destruct IH' as [x IH']; exists x
                 end;
          let HP := fresh "HP" in let Hk := fresh "Hk" in let HT := fresh "HT" in
          destruct IH' as [HP [Hk HT]]; split; [exact HP|]; split; [exact Hk|];
          eapply eqty_trans; eassumption
      end
    | (* wf_lconv *)
      match goal with
      | IH : ?a = ?b -> typeof ?j = ?j -> _ -> _, E' : ?a = ?b, Hl : lequiv _ _ _ |- _ =>
          let IH' := fresh "IH'" in
          pose proof (IH E' Hi (wft_lconv _ _ _ _ _ _ HW (lequiv_sym _ _ _ Hl))) as IH'; clear IH;
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

Lemma inv_var {G i Γ n T k} : typeof i = i -> [ G ; Γ ⊢[ i ] var n : T @ k ] ->
  exists T0 l0, ([ G ; Γ ⊢[ typeof i ] ] /\ in_ctx Γ n T0 l0) /\
    lvl_eq (gL G) k l0 /\ [ G ; Γ ⊢[ i ] T ≅ T0 @ k ].
Proof. inv_tm. Qed.

Lemma inv_gvar {G i Γ u d T k} : typeof i = i -> [ G ; Γ ⊢[ i ] gvar u d : T @ k ] ->
  exists Δ i' T0 l0, ([ G ; Γ ⊢[ typeof i ] ] /\ in_gctx (gΨ G) u (gdTm Δ i' T0 l0) /\ lle i' i /\
    lsub_tail d Δ Γ /\ dnfl d /\
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n : A[d] @ k ])) /\
    lvl_eq (gL G) k l0 /\ [ G ; Γ ⊢[ i ] T ≅ T0[d] @ k ].
Proof. inv_tm. Qed.

(** A defined global (M9): its carried body is level-equivalent to the
    declared one and typed at the use's layer. *)
Lemma inv_gdef {G i Γ u t d T k} : typeof i = i -> [ G ; Γ ⊢[ i ] gdef u t d : T @ k ] ->
  exists Δ T0 l0 t0, ([ G ; Γ ⊢[ typeof i ] ] /\ in_gctx (gΨ G) u (gdDef Δ T0 l0 t0) /\ tm_leq t0 t /\
    lle lC i /\ lsub_tail d Δ Γ /\ dnfl d /\
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n : A[d] @ k ]) /\
    [ G ; Δ ⊢[ i ] t : T0 @ l0 ]) /\
    lvl_eq (gL G) k l0 /\ [ G ; Γ ⊢[ i ] T ≅ T0[d] @ k ].
Proof. inv_tm. Qed.

Lemma inv_code_nat {G i Γ T k} : typeof i = i -> [ G ; Γ ⊢[ i ] tmNat : T @ k ] ->
  (i <> lV /\ [ G ; Γ ⊢[ typeof i ] ]) /\
    lvl_eq (gL G) k (lsuc lzero) /\ [ G ; Γ ⊢[ i ] T ≅ tyU lzero @ k ].
Proof. inv_tm. Qed.

Lemma inv_code_U {G i Γ l T k} : typeof i = i -> [ G ; Γ ⊢[ i ] tmU l : T @ k ] ->
  (i <> lV /\ [ G ; Γ ⊢[ typeof i ] ] /\ lwf (gL G) l) /\
    lvl_eq (gL G) k (lsuc (lsuc l)) /\ [ G ; Γ ⊢[ i ] T ≅ tyU (lsuc l) @ k ].
Proof. inv_tm. Qed.

Lemma inv_code_pi {G i Γ l l' s t T k} : typeof i = i -> [ G ; Γ ⊢[ i ] tmPi l l' s t : T @ k ] ->
  (i <> lV /\ lwf (gL G) l /\ lwf (gL G) l' /\ [ G ; Γ ⊢[ i ] s : tyU l @ lsuc l ] /\
    [ G ; Γ ,, tyEl l s @ l ⊢[ i ] t : tyU l' @ lsuc l' ]) /\
    lvl_eq (gL G) k (lsuc (lmax l l')) /\ [ G ; Γ ⊢[ i ] T ≅ tyU (lmax l l') @ k ].
Proof. inv_tm. Qed.

Lemma inv_zero {G i Γ T k} : typeof i = i -> [ G ; Γ ⊢[ i ] zero : T @ k ] ->
  (i <> lV /\ [ G ; Γ ⊢[ typeof i ] ]) /\ lvl_eq (gL G) k lzero /\ [ G ; Γ ⊢[ i ] T ≅ tyNat @ k ].
Proof. inv_tm. Qed.

Lemma inv_succ {G i Γ t T k} : typeof i = i -> [ G ; Γ ⊢[ i ] succ t : T @ k ] ->
  (i <> lV /\ [ G ; Γ ⊢[ i ] t : tyNat @ lzero ]) /\ lvl_eq (gL G) k lzero /\ [ G ; Γ ⊢[ i ] T ≅ tyNat @ k ].
Proof. inv_tm. Qed.

Lemma inv_natrec {G i Γ l M s z t T k} : typeof i = i -> [ G ; Γ ⊢[ i ] natrec l M s z t : T @ k ] ->
  (i <> lV /\ lwf (gL G) l /\ [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M @ l ] /\
    [ G ; Γ ⊢[ i ] s : M[lsingle zero] @ l ] /\
    [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ i ] z : M[lsucc] @ l ] /\
    [ G ; Γ ⊢[ i ] t : tyNat @ lzero ]) /\
    lvl_eq (gL G) k l /\ [ G ; Γ ⊢[ i ] T ≅ M[lsingle t] @ k ].
Proof. inv_tm. Qed.

Lemma inv_lam {G i Γ l l' A t T k} : typeof i = i -> [ G ; Γ ⊢[ i ] lam l l' A t : T @ k ] ->
  exists B, (i <> lV /\ lwf (gL G) l /\ lwf (gL G) l' /\ [ G ; Γ ⊢[ i ] A @ l ] /\
    [ G ; Γ ,, A @ l ⊢[ i ] t : B @ l' ]) /\
    lvl_eq (gL G) k (lmax l l') /\ [ G ; Γ ⊢[ i ] T ≅ tyPi l l' A B @ k ].
Proof. inv_tm. Qed.

Lemma inv_app {G i Γ l l' A B t s T k} : typeof i = i ->
  [ G ; Γ ⊢[ i ] app t l l' A B s : T @ k ] ->
  (i <> lV /\ lwf (gL G) l /\ lwf (gL G) l' /\ [ G ; Γ ⊢[ i ] A @ l ] /\
    [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] /\ [ G ; Γ ⊢[ i ] t : tyPi l l' A B @ lmax l l' ] /\
    [ G ; Γ ⊢[ i ] s : A @ l ]) /\
    lvl_eq (gL G) k l' /\ [ G ; Γ ⊢[ i ] T ≅ B[lsingle s] @ k ].
Proof. inv_tm. Qed.

Lemma inv_code_sig {G i Γ l l' s t T k} : typeof i = i -> [ G ; Γ ⊢[ i ] tmSig l l' s t : T @ k ] ->
  (i <> lV /\ lwf (gL G) l /\ lwf (gL G) l' /\ [ G ; Γ ⊢[ i ] s : tyU l @ lsuc l ] /\
    [ G ; Γ ,, tyEl l s @ l ⊢[ i ] t : tyU l' @ lsuc l' ]) /\
    lvl_eq (gL G) k (lsuc (lmax l l')) /\ [ G ; Γ ⊢[ i ] T ≅ tyU (lmax l l') @ k ].
Proof. inv_tm. Qed.

Lemma inv_pair {G i Γ l l' A B a b T k} : typeof i = i ->
  [ G ; Γ ⊢[ i ] tmPair l l' A B a b : T @ k ] ->
  (i <> lV /\ lwf (gL G) l /\ lwf (gL G) l' /\ [ G ; Γ ⊢[ i ] A @ l ] /\
    [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] /\ [ G ; Γ ⊢[ i ] a : A @ l ] /\
    [ G ; Γ ⊢[ i ] b : B[lsingle a] @ l' ]) /\
    lvl_eq (gL G) k (lmax l l') /\ [ G ; Γ ⊢[ i ] T ≅ tySig l l' A B @ k ].
Proof. inv_tm. Qed.

Lemma inv_fst {G i Γ l l' A B p T k} : typeof i = i ->
  [ G ; Γ ⊢[ i ] tmFst l l' A B p : T @ k ] ->
  (i <> lV /\ lwf (gL G) l /\ lwf (gL G) l' /\ [ G ; Γ ⊢[ i ] A @ l ] /\
    [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] /\ [ G ; Γ ⊢[ i ] p : tySig l l' A B @ lmax l l' ]) /\
    lvl_eq (gL G) k l /\ [ G ; Γ ⊢[ i ] T ≅ A @ k ].
Proof. inv_tm. Qed.

Lemma inv_snd {G i Γ l l' A B p T k} : typeof i = i ->
  [ G ; Γ ⊢[ i ] tmSnd l l' A B p : T @ k ] ->
  (i <> lV /\ lwf (gL G) l /\ lwf (gL G) l' /\ [ G ; Γ ⊢[ i ] A @ l ] /\
    [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] /\ [ G ; Γ ⊢[ i ] p : tySig l l' A B @ lmax l l' ]) /\
    lvl_eq (gL G) k l' /\ [ G ; Γ ⊢[ i ] T ≅ B[lsingle (tmFst l l' A B p)] @ k ].
Proof. inv_tm. Qed.

Lemma inv_code_unit {G i Γ l T k} : typeof i = i -> [ G ; Γ ⊢[ i ] tmUnit l : T @ k ] ->
  (i <> lV /\ [ G ; Γ ⊢[ typeof i ] ] /\ lwf (gL G) l) /\
    lvl_eq (gL G) k (lsuc l) /\ [ G ; Γ ⊢[ i ] T ≅ tyU l @ k ].
Proof. inv_tm. Qed.

Lemma inv_triv {G i Γ l T k} : typeof i = i -> [ G ; Γ ⊢[ i ] tmTriv l : T @ k ] ->
  (i <> lV /\ [ G ; Γ ⊢[ typeof i ] ] /\ lwf (gL G) l) /\
    lvl_eq (gL G) k l /\ [ G ; Γ ⊢[ i ] T ≅ tyUnit l @ k ].
Proof. inv_tm. Qed.

(** Strict equality (M10a). *)
Lemma inv_srefl {G i Γ l A a T k} : typeof i = i -> [ G ; Γ ⊢[ i ] srefl l A a : T @ k ] ->
  (compt i /\ lwf (gL G) l /\ [ G ; Γ ⊢[ i ] A @ l ] /\ [ G ; Γ ⊢[ i ] a : A @ l ]) /\
    lvl_eq (gL G) k l /\ [ G ; Γ ⊢[ i ] T ≅ tySEq l A a a @ k ].
Proof. inv_tm. Qed.

Lemma inv_elimSEmpty {G i Γ l l' M e T k} : typeof i = i -> [ G ; Γ ⊢[ i ] elimSEmpty l l' M e : T @ k ] ->
  (compt i /\ lwf (gL G) l /\ lwf (gL G) l' /\ [ G ; Γ ⊢[ i ] M @ l' ] /\
    [ G ; Γ ⊢[ i ] e : tySEmpty l @ l ]) /\ lvl_eq (gL G) k l' /\ [ G ; Γ ⊢[ i ] T ≅ M @ k ].
Proof. inv_tm. Qed.

Lemma inv_boxT {G i Γ C T k} : typeof i = i -> [ G ; Γ ⊢[ i ] boxT C : T @ k ] ->
  exists Δ l, (i = lM /\ [ G ; Γ ⊢[ lM ] ] /\ lwf (gL G) l /\ [ G ; Δ ⊢[ lD ] ] /\
    [ G ; Δ ⊢[ lC ] C @ l ]) /\
    lvl_eq (gL G) k lzero /\ [ G ; Γ ⊢[ i ] T ≅ tyCTyp Δ l @ k ].
Proof. inv_tm. Qed.

Lemma inv_boxt {G i Γ c T k} : typeof i = i -> [ G ; Γ ⊢[ i ] boxt c : T @ k ] ->
  exists Δ A l, (i = lM /\ [ G ; Γ ⊢[ lM ] ] /\ lwf (gL G) l /\ [ G ; Δ ⊢[ lD ] ] /\
    [ G ; Δ ⊢[ lD ] A @ l ] /\ [ G ; Δ ⊢[ lC ] c : A @ l ]) /\
    lvl_eq (gL G) k lzero /\ [ G ; Γ ⊢[ i ] T ≅ tyCTrm Δ A l @ k ].
Proof. inv_tm. Qed.

Lemma inv_letboxT {G i Γ l' l Δ M t' t T k} : typeof i = i ->
  [ G ; Γ ⊢[ i ] letboxT l' l Δ M t' t : T @ k ] ->
  (i = lM /\ lwf (gL G) l' /\ lwf (gL G) l /\ [ G ; Δ ⊢[ lD ] ] /\
    [ G ; Γ ,, tyCTyp Δ l @ lzero ⊢[ lM ] M @ l' ] /\
    [ gext G (gdTy Δ lC l) ; Γ⟪S⟫ ⊢[ lM ] t' : M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))] @ l' ] /\
    [ G ; Γ ⊢[ lM ] t : tyCTyp Δ l @ lzero ]) /\
    lvl_eq (gL G) k l' /\ [ G ; Γ ⊢[ i ] T ≅ M[lsingle t] @ k ].
Proof. inv_tm. Qed.

Lemma inv_letboxt {G i Γ l' l Δ A M t' t T k} : typeof i = i ->
  [ G ; Γ ⊢[ i ] letboxt l' l Δ A M t' t : T @ k ] ->
  (i = lM /\ lwf (gL G) l' /\ lwf (gL G) l /\ [ G ; Δ ⊢[ lD ] ] /\ [ G ; Δ ⊢[ lD ] A @ l ] /\
    [ G ; Γ ,, tyCTrm Δ A l @ lzero ⊢[ lM ] M @ l' ] /\
    [ gext G (gdTm Δ lC A l) ; Γ⟪S⟫ ⊢[ lM ] t' : M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))] @ l' ] /\
    [ G ; Γ ⊢[ lM ] t : tyCTrm Δ A l @ lzero ]) /\
    lvl_eq (gL G) k l' /\ [ G ; Γ ⊢[ i ] T ≅ M[lsingle t] @ k ].
Proof. inv_tm. Qed.

Lemma inv_elimT {G i Γ l1 l2 rb l Δ t T k} : typeof i = i ->
  [ G ; Γ ⊢[ i ] elimT l1 l2 rb l Δ t : T @ k ] ->
  exists MT Mt bs, (rb = mkrb MT Mt bs /\ i = lM /\
    [ G ; Γ ⊢[ lM ] motT (wrapMT MT) l Δ t @ l1 ] /\
    lwf (gL G) l1 /\ lwf (gL G) l2 /\ lwf (gL G) l /\ [ G ; Δ ⊢[ lD ] ] /\
    [ recGT G ; recΓT Γ ⊢[ lM ] MT @ lvren l1 (ush 1) ] /\
    [ recGt G ; recΓt Γ ⊢[ lM ] Mt @ lvren l2 (ush 1) ] /\
    (forall j, j < nbr -> [ brG j G ; brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ] ]) /\
    (forall j, j < nbr -> [ brG j G ; brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                           bs j : brRes j (wrapMT MT) (wrapMt Mt) @ brLv j l1 l2 ]) /\
    [ G ; Γ ⊢[ lM ] t : tyCTyp Δ l @ lzero ]) /\
    lvl_eq (gL G) k l1 /\ [ G ; Γ ⊢[ i ] T ≅ motT (wrapMT MT) l Δ t @ k ].
Proof. inv_tm. Qed.

Lemma inv_elimt {G i Γ l1 l2 rb l Δ A t T k} : typeof i = i ->
  [ G ; Γ ⊢[ i ] elimt l1 l2 rb l Δ A t : T @ k ] ->
  exists MT Mt bs, (rb = mkrb MT Mt bs /\ i = lM /\
    [ G ; Γ ⊢[ lM ] mott (wrapMt Mt) l Δ A t @ l2 ] /\
    lwf (gL G) l1 /\ lwf (gL G) l2 /\ lwf (gL G) l /\ [ G ; Δ ⊢[ lD ] ] /\
    [ recGT G ; recΓT Γ ⊢[ lM ] MT @ lvren l1 (ush 1) ] /\
    [ recGt G ; recΓt Γ ⊢[ lM ] Mt @ lvren l2 (ush 1) ] /\
    (forall j, j < nbr -> [ brG j G ; brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ] ]) /\
    (forall j, j < nbr -> [ brG j G ; brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                           bs j : brRes j (wrapMT MT) (wrapMt Mt) @ brLv j l1 l2 ]) /\
    [ G ; Δ ⊢[ lD ] A @ l ] /\
    [ G ; Γ ⊢[ lM ] t : tyCTrm Δ A l @ lzero ]) /\
    lvl_eq (gL G) k l2 /\ [ G ; Γ ⊢[ i ] T ≅ mott (wrapMt Mt) l Δ A t @ k ].
Proof. inv_tm. Qed.

Lemma inv_ulam {G i Γ n l T0 t T k} : typeof i = i -> [ G ; Γ ⊢[ i ] ulam n l T0 t : T @ k ] ->
  (i = lM /\ [ G ; Γ ⊢[ lM ] ] /\ 0 < n /\ lwf (n + gL G) l /\
    [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] T0 @ l ] /\
    [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] t : T0 @ l ]) /\
    lvl_eq (gL G) k lomega /\ [ G ; Γ ⊢[ i ] T ≅ tyUPi n l T0 @ k ].
Proof. inv_tm. Qed.

Lemma inv_uapp {G i Γ t ls T k} : typeof i = i -> [ G ; Γ ⊢[ i ] uapp t ls : T @ k ] ->
  exists n l T0, (i = lM /\ lwf (n + gL G) l /\ [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] T0 @ l ] /\
    length ls = n /\ Forall (lwf (gL G)) ls /\ [ G ; Γ ⊢[ lM ] t : tyUPi n l T0 @ lomega ]) /\
    lvl_eq (gL G) k (lvsubst l (uext ls lvar)) /\ [ G ; Γ ⊢[ i ] T ≅ T0[uext ls lvar]ᵤ @ k ].
Proof. inv_tm. Qed.

Lemma inv_clam {G i Γ l T0 t T k} : typeof i = i -> [ G ; Γ ⊢[ i ] clam l T0 t : T @ k ] ->
  (i = lM /\ [ G ; Γ ⊢[ lM ] ] /\ lwf (gL G) l /\
    [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T0 @ l ] /\ [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] t : T0 @ l ]) /\
    lvl_eq (gL G) k l /\ [ G ; Γ ⊢[ i ] T ≅ tyCPi l T0 @ k ].
Proof. inv_tm. Qed.

Lemma inv_capp {G i Γ t Δ T k} : typeof i = i -> [ G ; Γ ⊢[ i ] capp t Δ : T @ k ] ->
  exists l T0, (i = lM /\ lwf (gL G) l /\ [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T0 @ l ] /\
    [ G ; Δ ⊢[ lD ] ] /\ [ G ; Γ ⊢[ lM ] t : tyCPi l T0 @ l ] /\
    [ G ; Γ ⊢[ lM ] T0⦃gsingle (GCtx Δ)⦄ @ l ]) /\
    lvl_eq (gL G) k l /\ [ G ; Γ ⊢[ i ] T ≅ T0⦃gsingle (GCtx Δ)⦄ @ k ].
Proof. inv_tm. Qed.

Lemma inv_tlam {G i Γ Δ l l' T0 t T k} : typeof i = i -> [ G ; Γ ⊢[ i ] tlam Δ l l' T0 t : T @ k ] ->
  (i = lM /\ [ G ; Γ ⊢[ lM ] ] /\ [ G ; Δ ⊢[ lD ] ] /\ lwf (gL G) l /\ lwf (gL G) l' /\
    [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] T0 @ l' ] /\
    [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] t : T0 @ l' ]) /\
    lvl_eq (gL G) k l' /\ [ G ; Γ ⊢[ i ] T ≅ tyTPi Δ l l' T0 @ k ].
Proof. inv_tm. Qed.

Lemma inv_tapp {G i Γ t A T k} : typeof i = i -> [ G ; Γ ⊢[ i ] tapp t A : T @ k ] ->
  exists Δ l l' T0, (i = lM /\ [ G ; Γ ⊢[ lM ] t : tyTPi Δ l l' T0 @ l' ] /\
    [ G ; Δ ⊢[ lD ] ] /\ lwf (gL G) l /\ lwf (gL G) l' /\
    [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] T0 @ l' ] /\ [ G ; Δ ⊢[ lD ] A @ l ] /\
    [ G ; Γ ⊢[ lM ] T0⦃gsingle (GTy A)⦄ @ l' ]) /\
    lvl_eq (gL G) k l' /\ [ G ; Γ ⊢[ i ] T ≅ T0⦃gsingle (GTy A)⦄ @ k ].
Proof. inv_tm. Qed.

(** ** Types: the only generic rule is [wft_lconv] *)

Ltac inv_ty :=
  let H := fresh "H" in let E := fresh "E" in
  intros H;
  match type of H with wf_ty _ _ _ ?t _ => let u := fresh "u" in remember t as u eqn:E end;
  induction H; try discriminate E;
  [> first
    [ match goal with
      | IH : ?a = ?b -> _, E' : ?a = ?b, Hl : lequiv _ _ _ |- _ =>
          let IH' := fresh "IH'" in pose proof (IH E') as IH'; clear IH;
          repeat match type of IH' with
                 | ex _ => let x := fresh "x" in destruct IH' as [x IH']; exists x
                 end;
          let HP := fresh "HP" in let Hk := fresh "Hk" in
          destruct IH' as [HP Hk]; split; [exact HP | exact (lvl_eq_lequiv Hl Hk)]
      end
    | (try injection E); intros; subst; repeat match goal with |- ex _ => eexists end;
      split; [| left; reflexivity]; conj_assumption ] ..].

Lemma inv_ty_nat {G i Γ k} : [ G ; Γ ⊢[ i ] tyNat @ k ] ->
  (i <> lV /\ [ G ; Γ ⊢[ typeof i ] ]) /\ lvl_eq (gL G) k lzero.
Proof. inv_ty. Qed.

Lemma inv_ty_pi {G i Γ l l' A B k} : [ G ; Γ ⊢[ i ] tyPi l l' A B @ k ] ->
  (i <> lV /\ lwf (gL G) l /\ lwf (gL G) l' /\ [ G ; Γ ⊢[ i ] A @ l ] /\
    [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ]) /\ lvl_eq (gL G) k (lmax l l').
Proof. inv_ty. Qed.

Lemma inv_ty_U {G i Γ l k} : [ G ; Γ ⊢[ i ] tyU l @ k ] ->
  (i <> lV /\ [ G ; Γ ⊢[ typeof i ] ] /\ lwf (gL G) l) /\ lvl_eq (gL G) k (lsuc l).
Proof. inv_ty. Qed.

Lemma inv_ty_El {G i Γ l t k} : [ G ; Γ ⊢[ i ] tyEl l t @ k ] ->
  (i <> lV /\ lwf (gL G) l /\ [ G ; Γ ⊢[ i ] t : tyU l @ lsuc l ]) /\ lvl_eq (gL G) k l.
Proof. inv_ty. Qed.

Lemma inv_ty_gvar {G i Γ U d k} : [ G ; Γ ⊢[ i ] tyGvar U d @ k ] ->
  exists Δ i' l0, (i <> lV /\ [ G ; Γ ⊢[ typeof i ] ] /\ in_gctx (gΨ G) U (gdTy Δ i' l0) /\
    lle i' i /\ lsub_tail d Δ Γ /\ dnfl d /\
    (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n : A[d] @ k ])) /\ lvl_eq (gL G) k l0.
Proof. inv_ty. Qed.

Lemma inv_ty_CTyp {G i Γ Δ l k} : [ G ; Γ ⊢[ i ] tyCTyp Δ l @ k ] ->
  (i = lM /\ [ G ; Γ ⊢[ lM ] ] /\ [ G ; Δ ⊢[ lD ] ] /\ lwf (gL G) l) /\ lvl_eq (gL G) k lzero.
Proof. inv_ty. Qed.

Lemma inv_ty_CTrm {G i Γ Δ A l k} : [ G ; Γ ⊢[ i ] tyCTrm Δ A l @ k ] ->
  (i = lM /\ [ G ; Γ ⊢[ lM ] ] /\ [ G ; Δ ⊢[ lD ] ] /\ [ G ; Δ ⊢[ lD ] A @ l ] /\ lwf (gL G) l) /\
    lvl_eq (gL G) k lzero.
Proof. inv_ty. Qed.

Lemma inv_ty_upi {G i Γ n l T k} : [ G ; Γ ⊢[ i ] tyUPi n l T @ k ] ->
  (i = lM /\ [ G ; Γ ⊢[ lM ] ] /\ 0 < n /\ lwf (n + gL G) l /\
    [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] T @ l ]) /\ lvl_eq (gL G) k lomega.
Proof. inv_ty. Qed.

Lemma inv_ty_cpi {G i Γ l T k} : [ G ; Γ ⊢[ i ] tyCPi l T @ k ] ->
  (i = lM /\ [ G ; Γ ⊢[ lM ] ] /\ lwf (gL G) l /\ [ gext G gdCtx ; Γ⟪S⟫ ⊢[ lM ] T @ l ]) /\
    lvl_eq (gL G) k l.
Proof. inv_ty. Qed.

Lemma inv_ty_tpi {G i Γ Δ l l' T k} : [ G ; Γ ⊢[ i ] tyTPi Δ l l' T @ k ] ->
  (i = lM /\ [ G ; Γ ⊢[ lM ] ] /\ [ G ; Δ ⊢[ lD ] ] /\ lwf (gL G) l /\ lwf (gL G) l' /\
    [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢[ lM ] T @ l' ]) /\ lvl_eq (gL G) k l'.
Proof. inv_ty. Qed.

Lemma inv_ty_sig {G i Γ l l' A B k} : [ G ; Γ ⊢[ i ] tySig l l' A B @ k ] ->
  (i <> lV /\ lwf (gL G) l /\ lwf (gL G) l' /\ [ G ; Γ ⊢[ i ] A @ l ] /\
    [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ]) /\ lvl_eq (gL G) k (lmax l l').
Proof. inv_ty. Qed.

Lemma inv_ty_unit {G i Γ l k} : [ G ; Γ ⊢[ i ] tyUnit l @ k ] ->
  (i <> lV /\ [ G ; Γ ⊢[ typeof i ] ] /\ lwf (gL G) l) /\ lvl_eq (gL G) k l.
Proof. inv_ty. Qed.

Lemma inv_ty_seq {G i Γ l A a b k} : [ G ; Γ ⊢[ i ] tySEq l A a b @ k ] ->
  (compt i /\ lwf (gL G) l /\ [ G ; Γ ⊢[ i ] A @ l ] /\ [ G ; Γ ⊢[ i ] a : A @ l ] /\
    [ G ; Γ ⊢[ i ] b : A @ l ]) /\ lvl_eq (gL G) k l.
Proof. inv_ty. Qed.

Lemma inv_ty_sempty {G i Γ l k} : [ G ; Γ ⊢[ i ] tySEmpty l @ k ] ->
  (compt i /\ [ G ; Γ ⊢[ typeof i ] ] /\ lwf (gL G) l) /\ lvl_eq (gL G) k l.
Proof. inv_ty. Qed.

(** ** Lookups are deterministic *)

Lemma in_ctx_det {Γ n T l T' l'} : in_ctx Γ n T l -> in_ctx Γ n T' l' -> T = T' /\ l = l'.
Proof.
  intros H; revert T' l'; induction H as [Γ A l | Γ A l B l'' n H IH]; intros T' l' H';
    inversion H' as [? ? ? | ? ? ? ? ? ? H'']; subst; auto.
  destruct (IH _ _ H'') as [-> ->]; auto.
Qed.

Lemma in_gctx_det {Ψ n D D'} : in_gctx Ψ n D -> in_gctx Ψ n D' -> D = D'.
Proof.
  intros H; revert D'; induction H as [Ψ D | Ψ D D0 n H IH]; intros D' H';
    inversion H' as [? ? | ? ? ? ? H'']; subst; auto.
  now rewrite (IH _ H'').
Qed.

(** ** A type's level is unique (up to equivalence) *)

Lemma lvl_eq_uniq {L k k' h} : lvl_eq L k h -> lvl_eq L k' h -> k = k' \/ lequiv L k k'.
Proof.
  intros [->|H] [->|H']; [left; reflexivity | right; exact (lequiv_sym _ _ _ H') | right; exact H |].
  right; exact (lequiv_trans _ _ _ _ H (lequiv_sym _ _ _ H')).
Qed.

Lemma no_ty_err {G i Γ k} : ~ [ G ; Γ ⊢[ i ] tyErr @ k ].
Proof. intros H; remember tyErr as X eqn:E; induction H; try discriminate; auto. Qed.

Lemma ty_lvl_uniq {G i Γ T k k'} : [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T @ k' ] ->
  k = k' \/ lequiv (gL G) k k'.
Proof.
  intros H H'. destruct T.
  - exfalso; exact (no_ty_err H).
  - exact (lvl_eq_uniq (proj2 (inv_ty_nat H)) (proj2 (inv_ty_nat H'))).
  - exact (lvl_eq_uniq (proj2 (inv_ty_pi H)) (proj2 (inv_ty_pi H'))).
  - exact (lvl_eq_uniq (proj2 (inv_ty_U H)) (proj2 (inv_ty_U H'))).
  - exact (lvl_eq_uniq (proj2 (inv_ty_El H)) (proj2 (inv_ty_El H'))).
  - destruct (inv_ty_gvar H) as (Δ0 & i0 & l0 & (_ & _ & Hin & _) & Hk).
    destruct (inv_ty_gvar H') as (Δ1 & i1 & l1 & (_ & _ & Hin' & _) & Hk').
    pose proof (in_gctx_det Hin Hin') as E.
    injection E as <- <- <-. exact (lvl_eq_uniq Hk Hk').
  - exact (lvl_eq_uniq (proj2 (inv_ty_CTyp H)) (proj2 (inv_ty_CTyp H'))).
  - exact (lvl_eq_uniq (proj2 (inv_ty_CTrm H)) (proj2 (inv_ty_CTrm H'))).
  - exact (lvl_eq_uniq (proj2 (inv_ty_upi H)) (proj2 (inv_ty_upi H'))).
  - exact (lvl_eq_uniq (proj2 (inv_ty_cpi H)) (proj2 (inv_ty_cpi H'))).
  - exact (lvl_eq_uniq (proj2 (inv_ty_tpi H)) (proj2 (inv_ty_tpi H'))).
  - exact (lvl_eq_uniq (proj2 (inv_ty_sig H)) (proj2 (inv_ty_sig H'))).
  - exact (lvl_eq_uniq (proj2 (inv_ty_unit H)) (proj2 (inv_ty_unit H'))).
  - exact (lvl_eq_uniq (proj2 (inv_ty_seq H)) (proj2 (inv_ty_seq H'))).
  - exact (lvl_eq_uniq (proj2 (inv_ty_sempty H)) (proj2 (inv_ty_sempty H'))).
Qed.
