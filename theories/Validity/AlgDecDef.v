(** * Decidability of algorithmic conversion: the statements (M6_DESIGN.md step 6)

    The statements [Dc_*], the uniqueness of inferred types, the tactics
    the cases share, and the decidability of neutrality. The cases are
    split over [AlgDecNe], [AlgDecCode], [AlgDecId] and [AlgDecW], which
    build in parallel; [AlgDec] puts them together. *)
From DeLaM.Typing Require Export StaticCodeEq.
From DeLaM.Validity Require Export AlgComplete.

(** ** Uniqueness of the inferred type *)

Lemma elimT_inj {l1 l2 rb l Δ t l1' l2' rb' l' Δ' t'} :
  elimT l1 l2 rb l Δ t = elimT l1' l2' rb' l' Δ' t' ->
  l1 = l1' /\ l2 = l2' /\ rb = rb' /\ l = l' /\ Δ = Δ' /\ t = t'.
Proof. intros H; injection H; auto 7. Qed.
Lemma elimt_inj {l1 l2 rb l Δ T t l1' l2' rb' l' Δ' T' t'} :
  elimt l1 l2 rb l Δ T t = elimt l1' l2' rb' l' Δ' T' t' ->
  l1 = l1' /\ l2 = l2' /\ rb = rb' /\ l = l' /\ Δ = Δ' /\ T = T' /\ t = t'.
Proof. intros H; injection H; auto 8. Qed.

(** The components' equations, except the recursor block's (left to
    [mkrb_inj_MT]). *)
Ltac inj_small := repeat match goal with H : ?a = _ |- _ =>
  lazymatch a with mkrb _ _ _ => fail | _ => injection H; intros; clear H end end.
(** Inversion on the left term's head, cheaper than [inversion] (whose
    proof terms dominated this file): [destruct] with the left index
    remembered, mismatched heads closed by [discriminate]. The recursors go
    through [elimT_inj]: [injection] would unfold the [mkrb] block. *)
Ltac ne_inv D :=
  let x := fresh "x" in let E := fresh "E" in
  lazymatch type of D with ac_tmne _ _ ?v _ _ => remember v as x eqn:E in D end;
  destruct D; try discriminate E;
  lazymatch type of E with
  | elimT _ _ _ _ _ _ = _ => apply elimT_inj in E; decompose [and] E; clear E; inj_small
  | elimt _ _ _ _ _ _ _ = _ => apply elimt_inj in E; decompose [and] E; clear E; inj_small
  | _ => injection E; intros
  end; subst.

Lemma ac_infer_uniq_all :
  (forall G Γ T T', ac_ty G Γ T T' -> True) /\
  (forall G Γ W W', ac_tynf G Γ W W' -> True) /\
  (forall G Γ V V', ac_tyne G Γ V V' -> True) /\
  (forall G Δ Δ', ac_ctx G Δ Δ' -> True) /\
  (forall G Γ t t' T, ac_tm G Γ t t' T -> True) /\
  (forall G Γ w w' W, ac_tmnf G Γ w w' W -> True) /\
  (forall G Γ ν ν' T, ac_tmne G Γ ν ν' T -> forall ν2 T2, ac_tmne G Γ ν ν2 T2 -> T = T2) /\
  (forall G Γ ν ν' W, ac_tmnee G Γ ν ν' W -> forall ν2 W2, ac_tmnee G Γ ν ν2 W2 -> W = W2) /\
  (forall G Γ d d' Δ, ac_sub G Γ d d' Δ -> True).
Proof.
  apply ac_mut; intros; try exact I;
    lazymatch goal with D2 : ?J |- _ =>
      lazymatch J with ac_tmne _ _ _ _ _ => ne_inv D2; try kill_ne; try kill_box
                 | ac_tmnee _ _ _ _ _ => inversion D2; subst end end;
    repeat match goal with E : mkrb _ _ _ = mkrb _ _ _ |- _ => destruct (mkrb_inj_MT E) as [<- <-]; clear E end;
    try reflexivity;
    first
    [ match goal with H1 : in_ctx _ _ _ _, H2 : in_ctx _ _ _ _ |- _ =>
        destruct (in_ctx_det H1 H2) as [-> _]; reflexivity end
    | match goal with H1 : in_gctx _ _ _, H2 : in_gctx _ _ _ |- _ =>
        let E := fresh "E" in pose proof (in_gctx_det H1 H2) as E; injection E; intros; subst; reflexivity end
    | match goal with IH : forall _ _, ac_tmnee _ _ _ _ _ -> _ = _, D : ac_tmnee _ _ _ _ _ |- _ =>
        let E := fresh "E" in pose proof (IH _ _ D) as E; injection E; intros; subst; reflexivity end
    | match goal with IH : forall _ _, ac_tmne _ _ _ _ _ -> _ = _, D : ac_tmne _ _ _ _ _ |- _ =>
        let E := fresh "E" in pose proof (IH _ _ D) as E; subst; eapply reds_ty_whnf_det; eassumption end ].
Qed.

Lemma ac_ne_uniq {G Γ ν ν1 ν2 T1 T2} : ac_tmne G Γ ν ν1 T1 -> ac_tmne G Γ ν ν2 T2 -> T1 = T2.
Proof. intros D1 D2. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ac_infer_uniq_all)))))) _ _ _ _ _ D1 _ _ D2). Qed.
Lemma ac_nee_uniq {G Γ ν ν1 ν2 W1 W2} : ac_tmnee G Γ ν ν1 W1 -> ac_tmnee G Γ ν ν2 W2 -> W1 = W2.
Proof. intros D1 D2. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ac_infer_uniq_all))))))) _ _ _ _ _ D1 _ _ D2). Qed.

(** ** The statements

    The second index is the derivation's other side, unused: any
    derivation with the given left side will do. *)

Definition Dc_ty G Γ T (_ : ty) : Prop := forall T' i k k', compt i ->
  [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T' @ k' ] -> Dec (ac_ty G Γ T T').
Definition Dc_tynf G Γ T (_ : ty) : Prop := forall T' i k k', compt i ->
  [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T' @ k' ] -> Dec (ac_tynf G Γ T T').
Definition Dc_tyne G Γ T (_ : ty) : Prop := forall T' i k k', compt i ->
  [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T' @ k' ] -> Dec (ac_tyne G Γ T T').
Definition Dc_ctx G Δ (_ : ctx) : Prop := forall Δ',
  [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ' ⊢[ lD ] ] -> Dec (ac_ctx G Δ Δ').
Definition Dc_tm G Γ t (_ : tm) T : Prop := forall t' i k, compt i ->
  [ G ; Γ ⊢[ i ] t : T @ k ] -> [ G ; Γ ⊢[ i ] t' : T @ k ] -> Dec (ac_tm G Γ t t' T).
Definition Dc_tmnf G Γ t (_ : tm) T : Prop := forall t' i k, compt i ->
  [ G ; Γ ⊢[ i ] t : T @ k ] -> [ G ; Γ ⊢[ i ] t' : T @ k ] -> Dec (ac_tmnf G Γ t t' T).
Definition Dc_ne G Γ ν (_ : tm) T : Prop := forall ν' i k k' A A', compt i ->
  [ G ; Γ ⊢[ i ] ν : A @ k ] -> [ G ; Γ ⊢[ i ] ν' : A' @ k' ] -> Dec (ac_tmne G Γ ν ν' T).
Definition Dc_nee G Γ ν (_ : tm) W : Prop := forall ν' i k k' A A', compt i ->
  [ G ; Γ ⊢[ i ] ν : A @ k ] -> [ G ; Γ ⊢[ i ] ν' : A' @ k' ] -> Dec (ac_tmnee G Γ ν ν' W).
Definition Dc_sub G Γ d (_ : lsub) Θ : Prop := forall d' i, compt i -> [ G ; Θ ⊢[ i ] ] ->
  [ G ; Γ ⊢[ i ] d : Θ ] -> [ G ; Γ ⊢[ i ] d' : Θ ] -> Dec (ac_sub G Γ d d' Θ).

(** A negative answer, by inversion of the algorithm. *)
Ltac refute := right; let D := fresh "D" in intros D; inversion D; subst; try kill_ne; kill_box;
  try solve [contradiction | congruence].

(** The head constructor of a term. Related neutrals, and related normal
    forms at a positive type, share it: a mismatch is refuted without
    inverting the (large) judgments. *)
Definition tm_con (t : tm) : nat :=
  match t with
  | var _ => 0 | tmErr => 1 | tmNat => 2 | tmPi _ _ _ _ => 3 | tmU _ => 4 | zero => 5 | succ _ => 6
  | natrec _ _ _ _ _ => 7 | lam _ _ _ _ => 8 | app _ _ _ _ _ _ => 9 | gvar _ _ => 10 | boxT _ => 11
  | boxt _ => 12 | letboxT _ _ _ _ _ _ => 13 | letboxt _ _ _ _ _ _ _ => 14 | tmTy _ => 15 | tmTup _ _ => 16
  | bindU _ => 17 | bindG _ => 18 | bindL _ => 19 | elimT _ _ _ _ _ _ => 20 | elimt _ _ _ _ _ _ _ => 21
  | ulam _ _ _ _ => 22 | uapp _ _ => 23 | clam _ _ _ => 24 | capp _ _ => 25 | tlam _ _ _ _ _ => 26 | tapp _ _ => 27
  | tmSig _ _ _ _ => 28 | tmPair _ _ _ _ _ _ => 29 | tmFst _ _ _ _ _ => 30 | tmSnd _ _ _ _ _ => 31
  | tmUnit _ => 32 | tmTriv _ => 33 | gdef _ _ _ => 34 | srefl _ _ _ => 35 | elimSEmpty _ _ _ _ => 36
  | tmRefl _ _ _ => 37 | tmJ _ _ _ _ _ _ _ _ => 38 | tmId _ _ _ _ => 39
  | tmSEq _ _ _ _ => 40 | tmSEmpty _ => 41 | elimEmpty _ _ _ _ => 42
  | tmInl _ _ _ _ _ => 43 | tmInr _ _ _ _ _ => 44 | tmCase _ _ _ _ _ _ _ _ _ => 45
  | tmEmpty _ => 46 | tmSum _ _ _ _ => 47
  | tmSup _ _ _ _ _ _ => 48 | tmElimW _ _ _ _ _ _ _ _ => 49 | tmW _ _ _ _ => 50
  | tmVec _ _ _ => 51 | tmFin _ => 52 | tmSupf _ _ _ _ _ => 53 | tmElimWf _ _ _ _ _ _ _ => 54
  | tmWf _ _ _ => 55 | tmSq _ _ _ => 56 | tmElimSq _ _ _ _ _ _ => 57 | tmSqCode _ _ => 58
  | tmSupi _ _ _ _ _ _ _ _ _ => 59 | tmElimIWf _ _ _ _ _ _ _ _ _ _ _ _ => 60
  end.

Lemma ac_tmne_con {G Γ ν ν' T} : ac_tmne G Γ ν ν' T -> tm_con ν = tm_con ν'.
Proof. destruct 1; reflexivity. Qed.

Lemma ac_tmnf_con {G Γ w w' W} : ac_tmnf G Γ w w' W -> posty W -> ~ whne w -> tm_con w = tm_con w'.
Proof.
  destruct 1; intros Hp Hn; try reflexivity;
    try match goal with Hd : ac_tmnee _ _ _ _ _ |- _ => exfalso; exact (Hn (proj1 (ac_tmnee_whne Hd))) end;
    inversion Hp; subst; match goal with H : whne_ty _ |- _ => inversion H end.
Qed.

Lemma ac_tynf_head {G Γ W W'} : ac_tynf G Γ W W' -> ty_head W = ty_head W'.
Proof.
  destruct 1; try reflexivity.
  destruct (ac_tyne_whne H) as [Hn Hn']. rewrite (whne_ty_head _ Hn), (whne_ty_head _ Hn'). reflexivity.
Qed.

Ltac refute_con := right; let D := fresh "D" in intros D;
  let E := fresh "E" in
  first [ pose proof (ac_tmne_con D) as E
        | pose proof (ac_tmnf_con D ltac:(first [apply posty_nat | apply posty_U | apply posty_CTyp | apply posty_CTrm | apply posty_id | apply posty_sum | apply posty_W | apply posty_wf | apply posty_iwf]) ltac:(let Hn := fresh in intros Hn; discriminate (whne_ne_head Hn))) as E
        | pose proof (ac_tynf_head D) as E ];
  cbn in E; discriminate E.


(** Neutrality is decidable. *)
Fixpoint is_whne (t : tm) : bool :=
  match t with
  | var _ | gvar _ _ => true
  | natrec _ _ _ _ t | app t _ _ _ _ _ | letboxT _ _ _ _ _ t | letboxt _ _ _ _ _ _ t
  | uapp t _ | capp t _ | tapp t _ | tmFst _ _ _ _ t | tmSnd _ _ _ _ t | elimSEmpty _ _ _ t | elimEmpty _ _ _ t
  | tmJ _ _ _ _ _ _ _ t | tmCase _ _ _ _ _ _ _ _ t
  | tmElimW _ _ _ _ _ _ _ t | tmElimWf _ _ _ _ _ _ t | tmElimSq _ _ _ _ _ t
  | tmElimIWf _ _ _ _ _ _ _ _ _ _ _ t => is_whne t
  | elimT _ _ _ _ _ t => match t with boxT (tyGvar _ _) => true | _ => is_whne t end
  | elimt _ _ _ _ _ _ t => match t with boxt (gvar _ _) | boxt (gdef _ _ _) => true | _ => is_whne t end
  | _ => false
  end.

Lemma is_whne_sound t : is_whne t = true -> whne t.
Proof.
  induction t; cbn; intros H; try discriminate; try solve [constructor; auto].
  all: match goal with
       | |- whne (elimT _ _ _ _ _ ?s) =>
           destruct s; cbn in H; try solve [constructor; auto];
           match goal with |- whne (elimT _ _ _ _ _ (boxT ?T)) => destruct T; try discriminate;
                             apply whne_elimT_gvar end
       | |- whne (elimt _ _ _ _ _ _ ?s) =>
           destruct s; cbn in H; try solve [constructor; auto];
           match goal with |- whne (elimt _ _ _ _ _ _ (boxt ?c)) => destruct c; try discriminate;
                             first [apply whne_elimt_gvar | apply whne_elimt_gdef] end
       end.
Qed.

Lemma is_whne_complete t : whne t -> is_whne t = true.
Proof. induction 1; cbn; auto; destruct t; auto; inversion H. Qed.

Lemma whne_dec t : Dec (whne t).
Proof.
  destruct (is_whne t) eqn:E; [left; exact (is_whne_sound _ E) |].
  right; intros H; rewrite (is_whne_complete _ H) in E; discriminate.
Qed.

