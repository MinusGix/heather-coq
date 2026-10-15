(** * The recursors' scopes are well formed (M3)

    If [G] is well formed, so are the global contexts of the motives
    ([recGT], [recGt]) and of the branches ([brG k]): their declarations
    (04:1150–1300) are well formed in the universe-weakened [G]. *)
From DeLaM.Typing Require Export USubstitution.
From DeLaM.Syntax Require Import SubstCommute.
From DeLaM.Typing Require Import TypedDnf DNthCore.

Lemma in_gctx_nth Ψ n D : nth_error Ψ n = Some D -> in_gctx Ψ n (gdecl_ren D (Nat.add (S n))).
Proof.
  revert n D; induction Ψ as [|D0 Ψ IH]; intros [|n] D H; cbn in H; try discriminate.
  - injection H as <-. replace (gdecl_ren D0 (Nat.add 1)) with (gdecl_ren D0 S)
      by (destruct D0; reflexivity). constructor.
  - pose proof (IH _ _ H) as X. apply (ing_there _ _ D0) in X.
    replace (gdecl_ren (gdecl_ren D (Nat.add (S n))) S) with (gdecl_ren D (Nat.add (S (S n)))) in X;
      [exact X|].
    destruct D; cbn; f_equal; try reflexivity;
      first [ symmetry; apply (proj1 (proj2 (proj2 gren_gren_all))); reflexivity
            | symmetry; apply (proj1 gren_gren_all); reflexivity
            | symmetry; apply (proj1 (proj2 gren_gren_all)); reflexivity ].
Qed.

Lemma lsub_tail_id_var g : lsub_tail (lshift 0) (cvar g) (cvar g).
Proof. split; [reflexivity | intros n; cbn; f_equal; lia]. Qed.
Lemma no_in_ctx_var g n A k : ~ in_ctx (cvar g) n A k.
Proof. inversion 1. Qed.

(** [U^id] and [u^id] in the binding's own context. *)
Lemma lsub_tail_id Δ : lsub_tail (lshift 0) Δ Δ.
Proof. split; [reflexivity | intros n; cbn; f_equal; lia]. Qed.

Lemma in_ctx_nf Δ n A k : in_ctx Δ n A k -> nfty A.
Proof. destruct 1; apply ren_nf_ty. Qed.

Lemma id_entries G i Δ : [ G ; Δ ⊢[ typeof i ] ] ->
  forall n A k, in_ctx Δ n A k -> [ G ; Δ ⊢[ i ] llk (lshift 0) n : A[lshift 0] @ k ].
Proof.
  intros HΔ n A k Hin. cbn [llk]. rewrite Nat.add_0_r.
  rewrite (subst_id_ty A (lshift 0)) by (eauto using in_ctx_nf; intros; cbn; f_equal; lia).
  now apply wf_var.
Qed.

Lemma wf_gv G i Γ U Δ i' l : i <> lV -> [ G ; Γ ⊢[ typeof i ] ] ->
  in_gctx (gΨ G) U (gdTy Δ i' l) -> lle i' i -> Γ = Δ -> [ G ; Γ ⊢[ i ] tyGvar U (lshift 0) @ l ].
Proof.
  intros Hi HΓ Hin Hle ->. eapply wft_gvar; eauto using lsub_tail_id, id_entries. cbn; exact I.
Qed.

Lemma wf_gu G i u Δ i' T l : [ G ; Δ ⊢[ typeof i ] ] ->
  in_gctx (gΨ G) u (gdTm Δ i' T l) -> lle i' i -> nfty T ->
  [ G ; Δ ⊢[ i ] gvar u (lshift 0) : T @ l ].
Proof.
  intros HΔ Hin Hle HT. rewrite <- (subst_id_ty T (lshift 0)) by (auto; intros; cbn; f_equal; lia).
  eapply wf_gvar; eauto using lsub_tail_id, id_entries. cbn; exact I.
Qed.

(** One local more (M11b, [J]'s motive context): the identity instances
    shifted, as [⟨↑⟩] computes on them. *)
Lemma subst_lshift1_ty (T : ty) : T[lshift 1] = T⟨↑⟩.
Proof. symmetry; apply ren_as_subst_ty; intros n; cbn; f_equal; lia. Qed.
Lemma subst_lshift1 (t : tm) : t[lshift 1] = t⟨↑⟩.
Proof. symmetry; apply ren_as_subst; intros n; cbn; f_equal; lia. Qed.

Lemma lsub_tail_shift1_var g A la : lsub_tail (lshift 1) (cvar g) (cvar g ,, A @ la).
Proof. split; [reflexivity | intros n; cbn; f_equal; lia]. Qed.
Lemma wf_gv_up G i g A la U i' l : i <> lV -> [ G ; cvar g ,, A @ la ⊢[ typeof i ] ] ->
  in_gctx (gΨ G) U (gdTy (cvar g) i' l) -> lle i' i ->
  [ G ; cvar g ,, A @ la ⊢[ i ] tyGvar U (lshift 1) @ l ].
Proof.
  intros Hv HΓ Hin Hle. eapply wft_gvar; eauto using lsub_tail_shift1_var.
  all: try (intros ? ? ? HB; exfalso; exact (no_in_ctx_var _ _ _ _ HB)); cbn; exact I.
Qed.
Lemma wf_gu_up G i g A la u U i' l : [ G ; cvar g ,, A @ la ⊢[ typeof i ] ] ->
  in_gctx (gΨ G) u (gdTm (cvar g) i' (tyGvar U (lshift 0)) l) -> lle i' i ->
  [ G ; cvar g ,, A @ la ⊢[ i ] gvar u (lshift 1) : tyGvar U (lshift 1) @ l ].
Proof.
  intros HΓ Hin Hle. change (tyGvar U (lshift 1)) with ((tyGvar U (lshift 0))[lshift 1]).
  eapply wf_gvar; eauto using lsub_tail_shift1_var.
  all: try (intros ? ? ? HB; exfalso; exact (no_in_ctx_var _ _ _ _ HB)); cbn; exact I.
Qed.
Lemma wf_var0_gv G i Γ U la : [ G ; Γ ,, tyGvar U (lshift 0) @ la ⊢[ typeof i ] ] ->
  [ G ; Γ ,, tyGvar U (lshift 0) @ la ⊢[ i ] var 0 : tyGvar U (lshift 1) @ la ].
Proof. intros HΓ. exact (wf_var _ _ _ _ _ _ HΓ (in_here _ _ _)). Qed.

(** A global lookup at a concrete position of a concrete prefix. *)
Ltac glookup :=
  match goal with
  | H : in_gctx ?Ψ ?n _ |- in_gctx ?Ψ ?n _ => exact H
  | |- in_gctx ?Ψ ?n _ =>
      let H := fresh in pose proof (in_gctx_nth Ψ n _ eq_refl) as H; cbn in H; exact H
  end.

(** The lookups of a scope's own declarations, computed once and kept as
    hypotheses that [glookup] reuses (M13b: [elim_W]'s scope looks its six
    entries up about a hundred times, and each lookup normalises the
    renamed declaration). It stops at the first position it cannot
    compute, the scope's end. *)
Ltac glookups_from Ψ n :=
  let e := eval cbn in (nth_error Ψ n) in
  lazymatch e with
  | Some ?D =>
      let D' := eval cbn in (gdecl_ren D (Nat.add (S n))) in
      let H := fresh "Hlk" in assert (H : in_gctx Ψ n D') by exact (in_gctx_nth Ψ n D eq_refl);
      glookups_from Ψ (S n)
  | _ => idtac
  end.
Ltac glookups Ψ := glookups_from Ψ 0.
(* in a branch scope: W's (39-42), Wf's (47-50, M15b) and DVec's and IWf's
   (55-60, M17c) only, the scopes that use [RecWf]'s memoised automation *)
Ltac w_lookups k Ψ :=
  let b := eval cbv in (orb (orb (andb (Nat.leb 39 k) (Nat.ltb k 43)) (andb (Nat.leb 47 k) (Nat.ltb k 51)))
                            (andb (Nat.leb 55 k) (Nat.ltb k 61))) in
  lazymatch b with true => glookups Ψ | false => idtac end.

Ltac lvl_ok := cbn; repeat split; try lia.

(** Well-formedness of the concrete scope declarations. *)
Ltac wfd :=
  repeat match goal with
  (* each prefix of the global context is proved once, then reused by its
     entries' lookups (M12c: [case]'s seven entries made the rederivations
     the bulk of the cost) *)
  | H : [ ⊢ ?g ] |- [ ⊢ ?g ] => exact H
  | |- [ ⊢ mkG _ (gdCtx :: _) ] => apply wfg_ctx
  | |- [ ⊢ mkG ?L (gdTy _ _ _ :: ?Ψ) ] =>
      let HΨ := fresh "HΨ" in assert (HΨ : [ ⊢ mkG L Ψ ]);
      [ | apply wfg_ty; [ exact HΨ | | first [left; reflexivity | right; reflexivity] | lvl_ok ] ]
  | |- [ ⊢ mkG ?L (gdTm _ _ _ _ :: ?Ψ) ] =>
      let HΨ := fresh "HΨ" in assert (HΨ : [ ⊢ mkG L Ψ ]);
      [ | apply wfg_tm; [ exact HΨ | | first [left; reflexivity | right; reflexivity] | lvl_ok ] ]
  | |- [ _ ; cvar _ ⊢[ _ ] ] => apply wfc_var; [ | reflexivity ]
  | |- [ _ ; _ ,, _ @ _ ⊢[ _ ] ] => apply wfc_ext; [ | | lvl_ok ]
  | |- [ _ ; _ ⊢[ _ ] tyNat @ _ ] => apply wft_nat; [ discriminate | ]
  | |- [ _ ; _ ⊢[ _ ] tyU _ @ _ ] => apply wft_U; [ discriminate | | lvl_ok ]
  | |- [ _ ; _ ⊢[ _ ] tyPi _ _ _ _ @ _ ] => apply wft_pi; [ discriminate | lvl_ok | lvl_ok | | ]
  | |- [ _ ; _ ⊢[ _ ] tySig _ _ _ _ @ _ ] => apply wft_sig; [ discriminate | lvl_ok | lvl_ok | | ]
  | |- [ _ ; _ ⊢[ _ ] tyUnit _ @ _ ] => apply wft_unit; [ discriminate | | lvl_ok ]
  | |- [ _ ; _ ⊢[ _ ] tyId _ _ _ _ @ _ ] => apply wft_id; [ discriminate | lvl_ok | | | ]
  | |- [ _ ; _ ⊢[ _ ] tmRefl _ _ _ : tyId _ _ _ _ @ _ ] => apply wf_idrefl; [ discriminate | lvl_ok | | ]
  | |- [ _ ; _ ⊢[ _ ] tySEq _ _ _ _ @ _ ] => apply wft_seq; [ discriminate | lvl_ok | | | ]
  | |- [ _ ; _ ⊢[ _ ] tySEmpty _ @ _ ] => apply wft_sempty; [ discriminate | | lvl_ok ]
  | |- [ _ ; _ ⊢[ _ ] srefl _ _ _ : tySEq _ _ _ _ @ _ ] => apply wf_srefl; [ discriminate | lvl_ok | | ]
  (* the empty type and binary sums (M12c) *)
  | |- [ _ ; _ ⊢[ _ ] tyEmpty _ @ _ ] => apply wft_empty; [ discriminate | | lvl_ok ]
  | |- [ _ ; _ ⊢[ _ ] tySum _ _ _ _ @ _ ] => apply wft_sum; [ discriminate | lvl_ok | lvl_ok | | ]
  | |- [ _ ; _ ⊢[ _ ] tmInl _ _ _ _ _ : tySum _ _ _ _ @ _ ] => apply wf_inl; [ discriminate | lvl_ok | lvl_ok | | | ]
  | |- [ _ ; _ ⊢[ _ ] tmInr _ _ _ _ _ : tySum _ _ _ _ @ _ ] => apply wf_inr; [ discriminate | lvl_ok | lvl_ok | | | ]
  (* length-indexed tuples and finite indices (M14b) *)
  | |- [ _ ; _ ⊢[ _ ] tyVec _ _ _ @ _ ] => apply wft_vec; [ discriminate | lvl_ok | | ]
  | |- [ _ ; _ ⊢[ _ ] tyFin _ @ _ ] => apply wft_fin; [ discriminate | ]
  (* propositional truncation (M16b) *)
  | |- [ _ ; _ ⊢[ _ ] tySq _ _ @ _ ] => apply wft_sq; [ discriminate | lvl_ok | ]
  | |- [ _ ; _ ⊢[ _ ] tmSq _ _ _ : tySq _ _ @ _ ] => apply wf_sq; [ discriminate | lvl_ok | | ]
  | |- [ _ ; _ ,, tyGvar _ (lshift 0) @ _ ⊢[ _ ] var 0 : tyGvar _ (lshift 1) @ _ ] => apply wf_var0_gv
  | |- [ _ ; cvar _ ,, _ @ _ ⊢[ _ ] tyGvar _ (lshift 1) @ _ ] =>
      eapply wf_gv_up; [ discriminate | | glookup | unfold lle; cbn; lia ]
  | |- [ _ ; cvar _ ,, _ @ _ ⊢[ _ ] gvar _ (lshift 1) : tyGvar _ (lshift 1) @ _ ] =>
      eapply wf_gu_up; [ | glookup | unfold lle; cbn; lia ]
  | |- [ _ ; _ ⊢[ _ ] tyEl _ _ @ _ ] => apply wft_El; [ discriminate | lvl_ok | ]
  | |- [ _ ; _ ⊢[ _ ] tyGvar _ (lshift 0) @ _ ] =>
      eapply wf_gv; [ discriminate | | glookup | unfold lle; cbn; lia | reflexivity ]
  | |- [ _ ; _ ⊢[ _ ] gvar _ (lshift 0) : _ @ _ ] =>
      eapply wf_gu; [ | glookup | unfold lle; cbn; lia | cbn; tauto ]
  | |- lsub_tail (lshift 0) (cvar ?g) (cvar ?g) => apply lsub_tail_id_var
  | |- dnfl _ => cbn; tauto
  | |- forall n A k, in_ctx (cvar _) n A k -> _ => intros ? ? ? Hin; exfalso; exact (no_in_ctx_var _ _ _ _ Hin)
  end.

(** The two non-identity instances of [U_M] in the [elimN] branch. *)
Lemma wf_UM_succ G : [ G ; cvar 2 ,, tyNat @ lzero ,, tyGvar 1 (lshift 0) @ lvar 0 ⊢[ lD ] ] ->
  in_gctx (gΨ G) 1 (gdTy (cvar 2 ,, tyNat @ lzero) lC (lvar 0)) ->
  [ G ; cvar 2 ,, tyNat @ lzero ,, tyGvar 1 (lshift 0) @ lvar 0 ⊢[ lD ] tyGvar 1 lsucc @ lvar 0 ].
Proof.
  intros HΓ Hin. eapply wft_gvar; eauto.
  all: first [ discriminate | (unfold lle; cbn; lia) | (split; [reflexivity | intros; cbn; f_equal; lia])
             | (cbn; tauto) | idtac ].
  intros n A k HA. inversion HA as [? ? ? | ? ? ? ? ? ? HA']; subst; [|inversion HA'].
  cbn. apply wf_succ; [discriminate|].
  exact (wf_var _ lD _ 1 _ _ HΓ (in_there _ _ _ _ _ _ (in_here _ _ _))).
Qed.

Lemma wf_UM_zero G : [ G ; cvar 1 ⊢[ lD ] ] ->
  in_gctx (gΨ G) 0 (gdTy (cvar 1 ,, tyNat @ lzero) lC (lvar 0)) ->
  [ G ; cvar 1 ⊢[ lD ] tyGvar 0 (lsingle zero) @ lvar 0 ].
Proof.
  intros HΓ Hin. eapply wft_gvar; eauto.
  all: first [ discriminate | (unfold lle; cbn; lia) | (split; [reflexivity | intros; cbn; f_equal; lia])
             | (cbn; tauto) | idtac ].
  intros n A k HA. inversion HA as [? ? ? | ? ? ? ? ? ? HA']; subst; [|inversion HA'].
  cbn. apply wf_zero; [discriminate | exact HΓ].
Qed.

(** A type variable over one more local, at its single instance (the
    extension branches of M8d: [U_T^{id, u_a^id/x}], [U_T^{id, fst …/x}]). *)
Lemma wf_gv_single_var G i g U A la l a : i <> lV -> [ G ; cvar g ⊢[ typeof i ] ] ->
  in_gctx (gΨ G) U (gdTy (cvar g ,, A @ la) lC l) -> lle lC i -> nfty A -> dnfl (lsingle a) ->
  [ G ; cvar g ⊢[ i ] a : A @ la ] -> [ G ; cvar g ⊢[ i ] tyGvar U (lsingle a) @ l ].
Proof.
  intros Hv HΓ Hin Hle HA Hd Ha. eapply wft_gvar; eauto.
  - split; [reflexivity | intros; cbn; f_equal; lia].
  - intros n A' k HA'. inversion HA' as [? ? ? | ? ? ? ? ? ? HA'']; subst; [|inversion HA''].
    cbn [llk lsingle]. rewrite shift_single_ty by exact HA. exact Ha.
Qed.

(** A type variable over two more locals, at a double instance (M11b:
    [U_M^{id, u_a^id/y, refl(U_S^id; u_a^id)/p}] in [J]'s branch). *)
Lemma wf_gv_single2 G i g U A B la lb l a p : i <> lV -> [ G ; cvar g ⊢[ typeof i ] ] ->
  in_gctx (gΨ G) U (gdTy (cvar g ,, A @ la ,, B @ lb) lC l) -> lle lC i -> nfty A -> dnfl (lsingle2 a p) ->
  [ G ; cvar g ⊢[ i ] a : A @ la ] -> [ G ; cvar g ⊢[ i ] p : B[lsingle a] @ lb ] ->
  [ G ; cvar g ⊢[ i ] tyGvar U (lsingle2 a p) @ l ].
Proof.
  intros Hv HΓ Hin Hle HA Hd Ha Hp. eapply wft_gvar; eauto.
  - split; [reflexivity | intros; cbn; f_equal; lia].
  - intros n A' k HA'. inversion HA' as [? ? ? | ? ? ? ? ? ? HA'']; subst.
    + cbn [llk lsingle2]. rewrite (ren_subst_ty _ _ _ (lsingle a)); [exact Hp|].
      intros m; rewrite rlk_shift1; reflexivity.
    + inversion HA'' as [? ? ? | ? ? ? ? ? ? HA''']; subst; [|inversion HA'''].
      cbn [llk lsingle2]. rewrite shift2_single2_ty by exact HA. exact Ha.
Qed.

(** A type variable over one more local, at the injection of a new local
    (M12c: [U_M^{↑, inl x/z}] in [case]'s branch scopes). *)
Lemma wf_gv_up_inst G i g U A S la ls l X : i <> lV -> [ G ; cvar g ,, A @ la ⊢[ typeof i ] ] ->
  in_gctx (gΨ G) U (gdTy (cvar g ,, S @ ls) lC l) -> lle lC i -> dnfl (lcons (lshift 1) X) ->
  [ G ; cvar g ,, A @ la ⊢[ i ] X : S⟨↑⟩ @ ls ] -> [ G ; cvar g ,, A @ la ⊢[ i ] tyGvar U (lcons (lshift 1) X) @ l ].
Proof.
  intros Hv HΓ Hin Hle Hd HX. eapply wft_gvar; eauto.
  - split; [reflexivity | intros; cbn; f_equal; lia].
  - intros n A' k HA'. inversion HA' as [? ? ? | ? ? ? ? ? ? HA'']; subst; [|inversion HA''].
    cbn [llk]. rewrite shift_cons1_ty, subst_lshift1_ty. exact HX.
Qed.

Ltac wfd_all :=
  wfd;
  repeat match goal with
  | |- [ _ ; _ ⊢[ _ ] tyGvar 1 lsucc @ _ ] => apply wf_UM_succ; [ | glookup ]; wfd
  | |- [ _ ; _ ⊢[ _ ] tyGvar 0 (lsingle zero) @ _ ] => apply wf_UM_zero; [ | glookup ]; wfd
  | |- [ _ ; cvar _ ⊢[ _ ] tyGvar _ (lsingle _) @ _ ] =>
      eapply wf_gv_single_var; [ discriminate | | glookup | unfold lle; cbn; lia | cbn; tauto | cbn; tauto | ]; wfd
  | |- [ _ ; cvar _ ⊢[ _ ] tyGvar _ (lsingle2 _ _) @ _ ] =>
      eapply wf_gv_single2; [ discriminate | | glookup | unfold lle; cbn; lia | cbn; tauto | cbn; tauto | | cbn ]; wfd
  | |- [ _ ; cvar _ ,, _ @ _ ⊢[ _ ] tyGvar _ (lcons (lshift 1) _) @ _ ] =>
      eapply wf_gv_up_inst; [ discriminate | | glookup | unfold lle; cbn; lia | cbn; tauto
                            | cbn [ren Ren_ty Ren_tm ren_ty ren_tm lren r2l rdrop rshift1] ]; wfd
  end;
  try assumption.

(** W-types' scopes (M13b): the step telescope's instances, normalised by
    computation ([wfd_W]), are typed through these, which match the
    computed type up to a computed equation. *)
Lemma wf_var_eq G i Γ n T T' l : [ G ; Γ ⊢[ typeof i ] ] -> in_ctx Γ n T' l -> T' = T ->
  [ G ; Γ ⊢[ i ] var n : T @ l ].
Proof. intros HΓ Hin <-. exact (wf_var _ _ _ _ _ _ HΓ Hin). Qed.
Lemma wf_app_eq G i Γ l l' A B t s T : i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] ->
  [ G ; Γ ⊢[ i ] t : tyPi l l' A B @ lmax l l' ] -> [ G ; Γ ⊢[ i ] s : A @ l ] -> B[lsingle s] = T ->
  [ G ; Γ ⊢[ i ] app t l l' A B s : T @ l' ].
Proof. intros; subst; eapply wf_app; eauto. Qed.
Lemma wf_sup_eq G i Γ l l' A B a f T : i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] f : tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩ @ lmax l' (lmax l l') ] ->
  tyW l l' A B = T -> [ G ; Γ ⊢[ i ] tmSup l l' A B a f : T @ lmax l l' ].
Proof. intros; subst; eapply wf_sup; eauto. Qed.

Lemma wf_elimW' G i Γ l l' l'' A B M c t T : T = M[lsingle t] -> i <> lV ->
  lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) l'' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] ->
  [ G ; Γ ,, tyW l l' A B @ lmax l l' ⊢[ i ] M @ l'' ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] wfty l l' A B @ lmax l' (lmax l l') ] ->
  [ G ; Γ ,, A @ l ,, wfty l l' A B @ lmax l' (lmax l l') ⊢[ i ] wihty l l' l'' A B M @ lmax l' l'' ] ->
  [ G ; Γ ,, A @ l ,, wfty l l' A B @ lmax l' (lmax l l') ,, wihty l l' l'' A B M @ lmax l' l''
      ⊢[ i ] c : wstepty l l' A B M @ l'' ] ->
  [ G ; Γ ⊢[ i ] t : tyW l l' A B @ lmax l l' ] ->
  [ G ; Γ ⊢[ i ] tmElimW l l' l'' A B M c t : T @ l'' ].
Proof. intros ->; apply wf_elimW. Qed.
Lemma wf_elimWf' G i Γ l l' A N M c t T : T = M[lsingle t] -> i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] ->
  [ G ; Γ ,, tyWf l A N @ l ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] wfcsty l A N @ l ] ->
  [ G ; Γ ,, A @ l ,, wfcsty l A N @ l ⊢[ i ] wfihty l l' A N M @ lmax lzero l' ] ->
  [ G ; Γ ,, A @ l ,, wfcsty l A N @ l ,, wfihty l l' A N M @ lmax lzero l'
      ⊢[ i ] c : wfstepty l A N M @ l' ] ->
  [ G ; Γ ⊢[ i ] t : tyWf l A N @ l ] ->
  [ G ; Γ ⊢[ i ] tmElimWf l l' A N M c t : T @ l' ].
Proof. intros ->; apply wf_elimWf. Qed.

(** [elim_Wf]'s scope (M15b): its induction hypothesis's type carries
    [nth], typed here by its unfolding ([wty]), whose rules' types and the
    three conversions it crosses are matched up to a computed equation. *)
Lemma wf_natrec_eq G i Γ l M s z t T : i <> lV -> lwf (gL G) l ->
  [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M @ l ] ->
  [ G ; Γ ⊢[ i ] s : M[lsingle zero] @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ i ] z : M[lsucc] @ l ] ->
  [ G ; Γ ⊢[ i ] t : tyNat @ lzero ] -> M[lsingle t] = T ->
  [ G ; Γ ⊢[ i ] natrec l M s z t : T @ l ].
Proof. intros; subst; apply wf_natrec; auto. Qed.
Lemma wf_case_eq G i Γ l l' l'' A B M c1 c2 t T : i <> lV -> lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) l'' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] B @ l' ] ->
  [ G ; Γ ,, tySum l l' A B @ lmax l l' ⊢[ i ] M @ l'' ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] c1 : M⟨rlift ↑⟩[lsingle (tmInl l l' A⟨↑⟩ B⟨↑⟩ (var 0))] @ l'' ] ->
  [ G ; Γ ,, B @ l' ⊢[ i ] c2 : M⟨rlift ↑⟩[lsingle (tmInr l l' A⟨↑⟩ B⟨↑⟩ (var 0))] @ l'' ] ->
  [ G ; Γ ⊢[ i ] t : tySum l l' A B @ lmax l l' ] -> M[lsingle t] = T ->
  [ G ; Γ ⊢[ i ] tmCase l l' l'' A B M c1 c2 t : T @ l'' ].
Proof. intros; subst; eapply wf_case; eauto. Qed.
Lemma wf_snd_eq G i Γ l l' A B p T : i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] ->
  [ G ; Γ ⊢[ i ] p : tySig l l' A B @ lmax l l' ] -> B[lsingle (tmFst l l' A B p)] = T ->
  [ G ; Γ ⊢[ i ] tmSnd l l' A B p : T @ l' ].
Proof. intros; subst; eapply wf_snd; eauto. Qed.
Lemma wf_supi_eq G i Γ l li X A N Ot C a cs T : i <> lV -> lwf (gL G) l -> lwf (gL G) li ->
  [ G ; Γ ⊢[ i ] X @ li ] -> [ G ; Γ ⊢[ i ] A @ l ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] -> [ G ; Γ ,, A @ l ⊢[ i ] Ot : X⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] C : X⟨↑⟩⟨↑⟩ @ li ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] cs : tyDVec (lmax l li) N[lsingle a] (iwfFam l li X A N Ot C a) @ lmax l li ] ->
  tyIWf l li X A N Ot C Ot[lsingle a] = T -> [ G ; Γ ⊢[ i ] tmSupi l li X A N Ot C a cs : T @ lmax l li ].
Proof. intros; subst; apply wf_supi; auto. Qed.
Lemma wf_elimEmpty_eq G i Γ l l' M t T : i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ,, tyEmpty l' @ l' ⊢[ i ] M @ l ] -> [ G ; Γ ⊢[ i ] t : tyEmpty l' @ l' ] ->
  M[lsingle t] = T -> [ G ; Γ ⊢[ i ] elimEmpty l l' M t : T @ l ].
Proof. intros; subst; eapply wf_elimEmpty; eauto. Qed.
Lemma wf_gvar_eq G i Γ u Δ i' T T' l d : [ G ; Γ ⊢[ typeof i ] ] ->
  in_gctx (gΨ G) u (gdTm Δ i' T l) -> lle i' i -> lsub_tail d Δ Γ -> dnfl d ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n : A[d] @ k ]) -> T[d] = T' ->
  [ G ; Γ ⊢[ i ] gvar u d : T' @ l ].
Proof. intros; subst; eapply wf_gvar; eauto. Qed.
Lemma eqty_vec_succ_eq G i Γ l A A' n n' : compt i -> lwf (gL G) l -> [ G ; Γ ⊢[ i ] A @ l ] ->
  [ G ; Γ ⊢[ i ] n : tyNat @ lzero ] -> A⟨↑⟩ = A' -> n⟨↑⟩ = n' ->
  [ G ; Γ ⊢[ i ] tySig l l A (tyVec l A' n') ≅ tyVec l A (succ n) @ l ].
Proof. intros; subst; apply eqty_sym, eqty_vec_succ; auto. Qed.

(** [elim_IWf]'s scope (M17c): its induction hypothesis's type carries
    [dnth], typed here by its unfolding ([wty]) as [nth]'s is. Beyond
    [nth]'s conversions, [dnth]'s family moves along the recursion, so its
    applications' and first projection's types meet the expected ones only
    up to β (at the embeddings) and Unit-η (at the head): [weq] proves
    those, by congruence down to the redex. *)
Lemma wf_app_eq' G i Γ l l' A B t s T : B[lsingle s] = T -> i <> lV -> lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] ->
  [ G ; Γ ⊢[ i ] t : tyPi l l' A B @ lmax l l' ] -> [ G ; Γ ⊢[ i ] s : A @ l ] ->
  [ G ; Γ ⊢[ i ] app t l l' A B s : T @ l' ].
Proof. intros; subst; eapply wf_app; eauto. Qed.
Lemma eqty_dvec_succ_eq G i Γ l n F H Tl : compt i -> lwf (gL G) l ->
  [ G ; Γ ⊢[ i ] n : tyNat @ lzero ] -> [ G ; Γ ,, tyFin (succ n) @ lzero ⊢[ i ] F @ l ] ->
  dvecHd n F = H -> dvecTl l n F = Tl ->
  [ G ; Γ ⊢[ i ] tySig l l H Tl ≅ tyDVec l (succ n) F @ l ].
Proof. intros; subst; apply eqty_sym, eqty_dvec_succ; auto. Qed.
Lemma eqtm_beta_eq G i Γ l l' A B t s T : B[lsingle s] = T -> compt i -> lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ i ] B @ l' ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] t : B @ l' ] -> [ G ; Γ ⊢[ i ] s : A @ l ] ->
  [ G ; Γ ⊢[ i ] app (lam l l' A t) l l' A B s ≅ t[lsingle s] : T @ l' ].
Proof. intros; subst; apply eqtm_beta; auto. Qed.
Lemma eqtm_app_eq G i Γ l1 l2 l3 l4 A A' B B' t t' s s' T : B[lsingle s] = T -> i <> lV ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ i ] A @ l1 ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
  [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
  [ G ; Γ ⊢[ i ] t ≅ t' : tyPi l1 l2 A B @ lmax l1 l2 ] ->
  [ G ; Γ ⊢[ i ] s ≅ s' : A @ l1 ] ->
  [ G ; Γ ⊢[ i ] app t l1 l2 A B s ≅ app t' l3 l4 A' B' s' : T @ l2 ].
Proof. intros; subst; eapply eqtm_app; eauto. Qed.
Lemma eqtm_gvar_eq G i Γ u Δ i' T T' l d d' : [ G ; Γ ⊢[ typeof i ] ] ->
  in_gctx (gΨ G) u (gdTm Δ i' T l) -> lle i' i ->
  lsub_tail d Δ Γ -> dnfl d -> lsub_tail d' Δ Γ -> dnfl d' ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n : A[d] @ k ]) ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d' n : A[d'] @ k ]) ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n ≅ llk d' n : A[d] @ k ]) -> T[d] = T' ->
  [ G ; Γ ⊢[ i ] gvar u d ≅ gvar u d' : T' @ l ].
Proof. intros; subst; eapply eqtm_gvar; eauto. Qed.

(** [dnth]'s typing at the expected type ([DNthCore.dnth_wf_core]): the
    length's and the family's instances under [m] locals are premises,
    each typed under abstract locals by [dnth_ext] below. *)
Lemma wf_dnth_eq G i Γ l n F cs t T : compt i -> lwf (gL G) l -> [ G ; Γ ⊢[ i ] ] ->
  [ G ; Γ ⊢[ i ] n : tyNat @ lzero ] -> [ G ; Γ ,, tyFin n @ lzero ⊢[ i ] F @ l ] ->
  (forall m Δ, m <= 10 -> ctx_extn m Δ Γ -> [ G ; Δ ⊢[ i ] ] ->
     [ G ; Δ ⊢[ i ] n⟨rshift m⟩ : tyNat @ lzero ]) ->
  (forall m Δ e K x, m <= 9 -> ctx_extn m Δ Γ -> [ G ; Δ ⊢[ i ] ] ->
     [ G ; Δ ⊢[ i ] app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x : tyFin n⟨rshift m⟩ @ lzero ] ->
     [ G ; Δ ⊢[ i ] F⟨rlift (rshift m)⟩[lsingle (app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x)] @ l ]) ->
  (forall m Δ, m <= 2 -> ctx_extn m Δ Γ -> [ G ; Δ ⊢[ i ] ] ->
     [ G ; Δ ⊢[ i ] var 0 : tyFin n⟨rshift m⟩ @ lzero ] -> [ G ; Δ ⊢[ i ] F⟨rlift (rshift m)⟩[lsingle (var 0)] @ l ]) ->
  (forall m Δ e K x e' K' x', m <= 8 -> ctx_extn m Δ Γ -> [ G ; Δ ⊢[ i ] ] ->
     [ G ; Δ ⊢[ i ] app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x : tyFin n⟨rshift m⟩ @ lzero ] ->
     [ G ; Δ ⊢[ i ] app e' lzero lzero (tyFin K') (tyFin n⟨rshift (S m)⟩) x' : tyFin n⟨rshift m⟩ @ lzero ] ->
     [ G ; Δ ⊢[ i ] app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x
                  ≅ app e' lzero lzero (tyFin K') (tyFin n⟨rshift (S m)⟩) x' : tyFin n⟨rshift m⟩ @ lzero ] ->
     [ G ; Δ ⊢[ i ] F⟨rlift (rshift m)⟩[lsingle (app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x)]
                  ≅ F⟨rlift (rshift m)⟩[lsingle (app e' lzero lzero (tyFin K') (tyFin n⟨rshift (S m)⟩) x')] @ l ]) ->
  (forall m Δ e K x, m <= 2 -> ctx_extn m Δ Γ -> [ G ; Δ ⊢[ i ] ] ->
     [ G ; Δ ⊢[ i ] app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x : tyFin n⟨rshift m⟩ @ lzero ] ->
     [ G ; Δ ⊢[ i ] var 0 : tyFin n⟨rshift m⟩ @ lzero ] ->
     [ G ; Δ ⊢[ i ] app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x ≅ var 0 : tyFin n⟨rshift m⟩ @ lzero ] ->
     [ G ; Δ ⊢[ i ] F⟨rlift (rshift m)⟩[lsingle (app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x)]
                  ≅ F⟨rlift (rshift m)⟩[lsingle (var 0)] @ l ]) ->
  [ G ; Γ ⊢[ i ] cs : tyDVec l n F @ l ] -> [ G ; Γ ⊢[ i ] t : tyFin n @ lzero ] -> F[lsingle t] = T ->
  [ G ; Γ ⊢[ i ] tmDNth l n F cs t : T @ l ].
Proof.
  intros Hc Hl HΓ Hn HF NW FW FV FE FE0 Hcs Ht <-.
  exact (dnth_wf_core Hc Hl HΓ (wf_tm_nf Hn) (wf_ty_nf HF) Hn HF NW FW FV FE FE0 Hcs Ht).
Qed.
Lemma eqtm_retype_dnc G i Δ x y T T' l : [ G ; Δ ⊢[ i ] x ≅ y : T' @ l ] -> T' = T -> [ G ; Δ ⊢[ i ] x ≅ y : T @ l ].
Proof. now intros ? ->. Qed.

(** [Δ] extending [Γ] by a concrete number of locals, as [Γ] and as many
    abstract locals. *)
Lemma ctx_extn_S m Δ Γ : ctx_extn (S m) Δ Γ ->
  exists Δ' T l, Δ = (Δ' ,, T @ l) /\ ctx_extn m Δ' Γ.
Proof. destruct Δ; cbn; try contradiction; eauto. Qed.
Ltac ext_inv H :=
  lazymatch type of H with
  | ctx_extn 0 _ _ => cbn in H; subst
  | ctx_extn (S _) _ _ =>
      let D := fresh "D" in let T := fresh "T" in let l := fresh "l" in
      let E := fresh "E" in let H' := fresh "Hx" in
      destruct (ctx_extn_S _ _ _ H) as (D & T & l & E & H'); clear H; subst;
      ext_inv H'
  end.
(** A premise of [wf_dnth_eq]: one goal per number of locals up to the
    bound, under abstract locals. *)
Lemma dnf_of_wf G i Γ t T l : [ G ; Γ ⊢[ i ] t : T @ l ] -> dnftm t.
Proof. intros H. exact (proj1 (proj1 (proj2 (proj2 (proj2 typed_dnf))) _ _ _ _ _ _ H)). Qed.
(** The index's abstract parts are in deep normal form, by its typing
    ([wdnf] needs them, for the global instances it reaches). *)
Ltac dnf_hyps :=
  repeat match goal with
  | H : [ _ ; _ ⊢[ _ ] app ?e _ _ _ _ _ : _ @ _ ] |- _ =>
      is_var e; lazymatch goal with
      | _ : dnftm e |- _ => fail
      | _ => let Hd := fresh "Hd" in pose proof (dnf_of_wf _ _ _ _ _ _ H) as Hd; cbn [dnftm dnfty] in Hd;
             repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end
      end
  end.
(** A global instance's substitution is in deep normal form: by
    computation, but past [dnth] by its lemma ([cbn] unfolds it to a
    conjunction per node). *)
Ltac wdnf :=
  first
  [ solve [ cbn [dnfl dnftm dnfty];
            repeat first [ lazymatch goal with
                           | |- True => exact I | |- _ /\ _ => split
                           | |- dnftm (tmDNth _ _ _ _ _) => apply dnf_tmDNth
                           | |- dnftm ?t => is_var t; assumption
                           | |- ~ labsorb _ _ =>
                               let H := fresh in intro H;
                               first [ exact (False_ind _ H) | cbn [labsorb] in H; discriminate H ] end
                         | progress cbn [dnfl dnftm dnfty] ] ]
  | cbn; intuition congruence ].

Lemma in_ctx_ext_inv Γ A l n B k : in_ctx (Γ ,, A @ l) n B k ->
  (n = 0 /\ B = A⟨↑⟩ /\ k = l) \/ (exists n' B', n = S n' /\ B = B'⟨↑⟩ /\ in_ctx Γ n' B' k).
Proof. inversion 1; subst; [left | right; eexists _, _]; eauto. Qed.

(** A context's entries, one goal each ([inversion] and [subst] on the
    whole goal were a fifth of [elim_IWf]'s scope, M17c). *)
Ltac inv_in_ctx :=
  repeat match goal with
  | H : in_ctx (cvar _) _ _ _ |- _ => exact (False_ind _ (no_in_ctx_var _ _ _ _ H))
  | H : in_ctx (_ ,, _ @ _) _ _ _ |- _ =>
      apply in_ctx_ext_inv in H; destruct H as [(-> & -> & ->) | (? & ? & -> & -> & H)]
  end.

(** A term typed by a hypothesis, at its type up to computation: the
    index of [dnth]'s family under abstract locals ([wf_dnth_eq]). *)
Ltac wty_hyp :=
  lazymatch goal with
  | |- [ _ ; _ ⊢[ _ ] ?t : _ @ _ ] =>
      match goal with H : [ _ ; _ ⊢[ _ ] t : _ @ _ ] |- _ => eapply dnc_retype; [exact H | cbn; reflexivity] end
  | |- [ _ ; _ ⊢[ _ ] ?t ≅ ?t' : _ @ _ ] =>
      match goal with H : [ _ ; _ ⊢[ _ ] t ≅ t' : _ @ _ ] |- _ => eapply eqtm_retype_dnc; [exact H | cbn; reflexivity] end
  end.

Ltac wnorm :=
  cbn [typeof ren Ren_ty Ren_tm Ren_lsub subst Subst_ty Subst_tm Subst_lsub ren_ty ren_tm lren r2l rdrop
       rshift1 rlift rup lcons' rlk subst_ty subst_tm lcomp lnorm ldrop llift llk lsingle lsingle2 Nat.eqb Nat.add
       tmNth nthMot nthBase nthStep].
Ltac wnorm_in H :=
  cbn [typeof ren Ren_ty Ren_tm Ren_lsub subst Subst_ty Subst_tm Subst_lsub ren_ty ren_tm lren r2l rdrop
       rshift1 rlift rup lcons' rlk subst_ty subst_tm lcomp lnorm ldrop llift llk lsingle lsingle2 Nat.eqb Nat.add
       tmNth nthMot nthBase nthStep] in H.

(** The premises' hypotheses at their normal forms, as [wty] meets their
    terms. *)
Ltac wnorm_hyps :=
  repeat match goal with
  | H : [ _ ; _ ⊢[ _ ] app ?e _ _ _ _ _ : _ @ _ ] |- _ => is_var e; progress wnorm_in H
  | H : [ _ ; _ ⊢[ _ ] app ?e _ _ _ _ _ ≅ _ : _ @ _ ] |- _ => is_var e; progress wnorm_in H
  | H : [ _ ; _ ⊢[ _ ] var _ : _ @ _ ] |- _ => progress wnorm_in H
  end.
Ltac dnth_ext tac :=
  let m := fresh "m" in let D := fresh "D" in let Hm := fresh "Hm" in let Hx := fresh "Hx" in
  intros m D; repeat lazymatch goal with |- forall _ : tm, _ => intro | |- forall _ : ty, _ => intro end; intros Hm Hx; intros;
  dnf_hyps;
  repeat (destruct m as [|m]; [ext_inv Hx; wnorm_hyps; tac | try (exfalso; lia)]); fail "dnth_ext: an instance is left".

(** A former at its own level, or converted to the goal's (M15b: [nth]'s
    functions live at [l ⊔ l] and [0 ⊔ l], its motive's uses at [l]). *)
Ltac ty_lv Ln tac :=
  lazymatch goal with
  | |- [ _ ; _ ⊢[ _ ] _ @ ?L ] => tryif constr_eq L Ln then tac else (eapply wft_lconv; [ tac | lalg ])
  end.
Ltac tm_lv Ln tac :=
  lazymatch goal with
  | |- [ _ ; _ ⊢[ _ ] _ : _ @ ?L ] => tryif constr_eq L Ln then tac else (eapply wf_lconv; [ tac | lalg ])
  end.

Ltac ety_lv Ln tac :=
  lazymatch goal with
  | |- [ _ ; _ ⊢[ _ ] _ ≅ _ @ ?L ] => tryif constr_eq L Ln then tac else (eapply eqty_lconv; [ tac | lalg ])
  end.
Ltac etm_lv Ln tac :=
  lazymatch goal with
  | |- [ _ ; _ ⊢[ _ ] _ ≅ _ : _ @ ?L ] => tryif constr_eq L Ln then tac else (eapply eqtm_lconv; [ tac | lalg ])
  end.

(** The context's well-formedness is proved once per context and kept as
    a hypothesis: every variable and global instance below needs it, and
    rederiving it at each leaf is exponential in the telescope's depth. *)
Ltac wctx :=
  lazymatch goal with
  | |- [ _ ; _ ⊢[ _ ] ] =>
      first
      [ assumption
      | lazymatch goal with
        | |- [ _ ; cvar _ ⊢[ _ ] ] => apply wfc_var; [ assumption | reflexivity ]
        | |- [ ?G ; ?Γ ,, ?A @ ?l ⊢[ ?i ] ] =>
            let HΓ := fresh "HΓ" in assert (HΓ : [ G ; Γ ⊢[ i ] ]) by wctx;
            apply wfc_ext; [ exact HΓ | wty | lvl_ok ]
        end ]
  end
with wbind G Γ i A l k :=
  (* [A] at [Γ], then the extended context, then the continuation under it *)
  let HA := fresh "HA" in assert (HA : [ G ; Γ ⊢[ i ] A @ l ]) by wty;
  let HΓA := fresh "HΓA" in
  (* the context is at [typeof i]: [A] again there when [i] is [C] *)
  assert (HΓA : [ G ; Γ ,, A @ l ⊢[ typeof i ] ]) by (apply wfc_ext; [ wctx | first [exact HA | wty] | lvl_ok ]);
  k HA
with wty :=
  wnorm;
  lazymatch goal with
  | |- [ ?G ; ?Γ ⊢[ ?i ] tyPi ?l ?l' ?A ?B @ _ ] =>
      wbind G Γ i A l ltac:(fun HA =>
        ty_lv (lmax l l') ltac:(apply wft_pi; [ discriminate | lvl_ok | lvl_ok | exact HA | wty ]))
  | |- [ ?G ; ?Γ ⊢[ ?i ] tyW ?l ?l' ?A ?B @ _ ] =>
      wbind G Γ i A l ltac:(fun HA => apply wft_W; [ discriminate | lvl_ok | lvl_ok | exact HA | wty ])
  | |- [ _ ; _ ⊢[ _ ] tyGvar _ _ @ _ ] =>
      eapply wft_gvar; [ discriminate | wctx | glookup | unfold lle; cbn; lia
                       | split; [reflexivity | intros; cbn; f_equal; lia] | wdnf
                       | let H := fresh "Hin" in intros ? ? ? H; inv_in_ctx; wty ]
  | |- [ _ ; _ ⊢[ _ ] var _ : _ @ _ ] =>
      first [ eapply wf_var_eq; [ wctx | solve [repeat constructor] | reflexivity ]
            (* [nth]'s variables, at their functions' levels and at their
               unfolded types (M15b) *)
            | eapply wf_lconv; [ eapply wf_var_eq; [ wctx | solve [repeat constructor] | reflexivity ] | lalg ]
            | eapply wf_lconv;
              [ eapply wf_conv; [ eapply wf_var; [ wctx | solve [repeat constructor] ] | wnorm; wconv ]
              | lalg ]
            (* [dnth]'s family's index under abstract locals ([wf_dnth_eq]) *)
            | wty_hyp ]
  | |- [ _ ; _ ⊢[ _ ] gvar _ (lshift 0) : _ @ _ ] =>
      eapply wf_gu; [ wctx | glookup | unfold lle; cbn; lia | cbn; intuition congruence ]
  (* a term global at an instance ([sup_f]'s children's length, M15b) *)
  | |- [ _ ; _ ⊢[ _ ] gvar _ _ : _ @ _ ] =>
      eapply wf_gvar_eq; [ wctx | glookup | unfold lle; cbn; lia
                         | split; [reflexivity | intros; cbn; f_equal; lia] | wdnf
                         | let H := fresh "Hin" in intros ? ? ? H; inv_in_ctx; wty | wnorm; reflexivity ]
  | |- [ ?G ; ?Γ ⊢[ ?i ] app ?e ?l ?l' ?A ?B ?s : ?T @ _ ] =>
      (* [dnth]'s family's index under abstract locals ([wf_dnth_eq]) *)
      first [ is_var e; wty_hyp |
      wbind G Γ i A l ltac:(fun HA => tm_lv l' ltac:(
        let E := fresh "E" in
        tryif assert (E : B[lsingle s] = T) by (wnorm; reflexivity)
        then (clear E; eapply wf_app_eq'; [ wnorm; reflexivity | discriminate | lvl_ok | lvl_ok | exact HA | wty | wty | wty ])
        (* [dnth]'s applications, at their types up to β (M17c) *)
        else (apply wf_conv with (T' := B[lsingle s]);
          [ eapply wf_app; [ discriminate | lvl_ok | lvl_ok | exact HA | wty | wty | wty ] | wnorm; weq ]))) ]
  | |- [ ?G ; ?Γ ⊢[ ?i ] tmSup ?l _ ?A _ _ _ : _ @ _ ] =>
      wbind G Γ i A l ltac:(fun HA =>
        eapply wf_sup_eq; [ discriminate | lvl_ok | lvl_ok | exact HA | wty | wty | wty | reflexivity ])
  | |- [ _ ; _ ⊢[ _ ] tyU _ @ _ ] => apply wft_U; [ discriminate | wctx | lvl_ok ]
  | |- [ _ ; _ ⊢[ _ ] tyEl _ _ @ _ ] => apply wft_El; [ discriminate | lvl_ok | wty ]
  (* the code of W and [elimW], in the branches' heads and calls *)
  | |- [ ?G ; ?Γ ⊢[ ?i ] tmW ?l _ ?s _ : _ @ _ ] =>
      wbind G Γ i (tyEl l s) l ltac:(fun HA =>
        apply wf_code_W; [ discriminate | lvl_ok | lvl_ok | wty | wty ])
  | |- [ _ ; _ ⊢[ _ ] tmElimW _ _ _ _ _ _ _ _ : _ @ _ ] =>
      eapply wf_elimW'; [ reflexivity | discriminate | lvl_ok | lvl_ok | lvl_ok | wtop .. ]
  (* finitary well-founded trees' scopes (M15b), and the formers [nth]
     unfolds to *)
  | |- [ ?G ; ?Γ ⊢[ ?i ] tyWf ?l ?A _ @ _ ] =>
      wbind G Γ i A l ltac:(fun HA => apply wft_wf; [ discriminate | lvl_ok | exact HA | wty ])
  | |- [ _ ; _ ⊢[ _ ] tmNth _ _ _ _ _ : _ @ _ ] => unfold tmNth, nthMot, nthBase, nthStep; wty
  | |- [ ?G ; ?Γ ⊢[ ?i ] tmWf ?l ?s _ : _ @ _ ] =>
      wbind G Γ i (tyEl l s) l ltac:(fun HA => apply wf_code_wf; [ discriminate | lvl_ok | wty | wty ])
  | |- [ _ ; _ ⊢[ _ ] tmElimWf _ _ _ _ _ _ _ : _ @ _ ] =>
      eapply wf_elimWf'; [ reflexivity | discriminate | lvl_ok | lvl_ok | wtop .. ]
  | |- [ ?G ; ?Γ ⊢[ ?i ] tmSupf ?l ?A _ _ _ : _ @ _ ] =>
      wbind G Γ i A l ltac:(fun HA => apply wf_supf; [ discriminate | lvl_ok | exact HA | wty | wty | wty ])
  | |- [ _ ; _ ⊢[ _ ] tyNat @ _ ] => apply wft_nat; [ discriminate | wctx ]
  | |- [ _ ; _ ⊢[ _ ] tyUnit _ @ _ ] => apply wft_unit; [ discriminate | wctx | lvl_ok ]
  | |- [ _ ; _ ⊢[ _ ] tyEmpty _ @ _ ] => apply wft_empty; [ discriminate | wctx | lvl_ok ]
  | |- [ _ ; _ ⊢[ _ ] tySum ?l ?l' _ _ @ _ ] =>
      ty_lv (lmax l l') ltac:(apply wft_sum; [ discriminate | lvl_ok | lvl_ok | wty | wty ])
  | |- [ ?G ; ?Γ ⊢[ ?i ] tySig ?l ?l' ?A _ @ _ ] =>
      wbind G Γ i A l ltac:(fun HA =>
        ty_lv (lmax l l') ltac:(apply wft_sig; [ discriminate | lvl_ok | lvl_ok | exact HA | wty ]))
  | |- [ _ ; _ ⊢[ _ ] tyVec _ _ _ @ _ ] => apply wft_vec; [ discriminate | lvl_ok | wty | wty ]
  | |- [ _ ; _ ⊢[ _ ] tyFin _ @ _ ] => apply wft_fin; [ discriminate | wty ]
  | |- [ _ ; _ ⊢[ _ ] zero : _ @ _ ] => apply wf_zero; [ discriminate | wctx ]
  | |- [ _ ; _ ⊢[ _ ] succ _ : _ @ _ ] => apply wf_succ; [ discriminate | wty ]
  | |- [ _ ; _ ⊢[ _ ] natrec ?l _ _ _ _ : _ @ _ ] =>
      tm_lv l ltac:(eapply wf_natrec_eq;
        [ discriminate | lvl_ok | wtop | wty | unfold lsucc; wtop | wty | wnorm; reflexivity ])
  | |- [ ?G ; ?Γ ⊢[ ?i ] lam ?l ?l' ?A _ : _ @ _ ] =>
      wbind G Γ i A l ltac:(fun HA =>
        tm_lv (lmax l l') ltac:(apply wf_lam; [ discriminate | lvl_ok | lvl_ok | exact HA | wty ]))
  | |- [ _ ; _ ⊢[ _ ] tmCase _ _ ?l'' _ _ _ _ _ _ : _ @ _ ] =>
      tm_lv l'' ltac:(eapply wf_case_eq;
        [ discriminate | lvl_ok | lvl_ok | lvl_ok | wty | wty | wtop | wtop | wtop | wty | wnorm; reflexivity ])
  | |- [ ?G ; ?Γ ⊢[ ?i ] tmFst ?l _ ?A _ _ : ?T @ _ ] =>
      wbind G Γ i A l ltac:(fun HA =>
        tm_lv l ltac:(
          tryif unify T A
          then apply wf_fst; [ discriminate | lvl_ok | lvl_ok | exact HA | wty | wty ]
          (* [dnth]'s head, at its type up to Unit-η (M17c) *)
          else (apply wf_conv with (T' := A);
            [ apply wf_fst; [ discriminate | lvl_ok | lvl_ok | exact HA | wty | wty ] | wnorm; weq ])))
  | |- [ ?G ; ?Γ ⊢[ ?i ] tmSnd ?l ?l' ?A _ _ : _ @ _ ] =>
      wbind G Γ i A l ltac:(fun HA =>
        tm_lv l' ltac:(eapply wf_snd_eq; [ discriminate | lvl_ok | lvl_ok | exact HA | wty | wty | wnorm; reflexivity ]))
  | |- [ _ ; _ ⊢[ _ ] elimEmpty ?l _ _ _ : _ @ _ ] =>
      tm_lv l ltac:(eapply wf_elimEmpty_eq; [ discriminate | lvl_ok | lvl_ok | wtop | wty | wnorm; reflexivity ])
  (* propositional truncation (M16b) *)
  | |- [ _ ; _ ⊢[ _ ] tySq _ _ @ _ ] => apply wft_sq; [ discriminate | lvl_ok | wty ]
  | |- [ _ ; _ ⊢[ _ ] tmSq _ _ _ : _ @ _ ] => apply wf_sq; [ discriminate | lvl_ok | wty | wty ]
  | |- [ _ ; _ ⊢[ _ ] tmSqCode _ _ : _ @ _ ] => apply wf_code_sq; [ discriminate | lvl_ok | wty ]
  (* dependent tuples and indexed trees (M17c) *)
  | |- [ _ ; _ ⊢[ _ ] iwfFam _ _ _ _ _ _ _ _ @ _ ] => unfold iwfFam; wty
  (* [dnth]'s injections, at a sum or at the [Fin (S n)] it is *)
  | |- [ _ ; _ ⊢[ _ ] tmTriv _ : _ @ _ ] => apply wf_triv; [ discriminate | wctx | lvl_ok ]
  | |- [ _ ; _ ⊢[ _ ] tmInl ?l ?l' _ _ _ : tySum _ _ _ _ @ _ ] =>
      tm_lv (lmax l l') ltac:(apply wf_inl; [ discriminate | lvl_ok | lvl_ok | wty | wty | wty ])
  | |- [ _ ; _ ⊢[ _ ] tmInl _ _ _ _ _ : _ @ _ ] =>
      eapply wf_lconv; [ eapply wf_conv; [ apply wf_inl; [ discriminate | lvl_ok | lvl_ok | wty | wty | wty ]
                                        | wnorm; wconv ] | lalg ]
  | |- [ _ ; _ ⊢[ _ ] tmInr ?l ?l' _ _ _ : tySum _ _ _ _ @ _ ] =>
      tm_lv (lmax l l') ltac:(apply wf_inr; [ discriminate | lvl_ok | lvl_ok | wty | wty | wty ])
  | |- [ _ ; _ ⊢[ _ ] tmInr _ _ _ _ _ : _ @ _ ] =>
      eapply wf_lconv; [ eapply wf_conv; [ apply wf_inr; [ discriminate | lvl_ok | lvl_ok | wty | wty | wty ]
                                        | wnorm; wconv ] | lalg ]
  (* [dnth] by its lemma, the length and the family under abstract locals
     ([wf_dnth_eq]) *)
  | |- [ ?G ; ?Γ ⊢[ ?i ] tmDNth ?l ?n _ _ _ : _ @ _ ] =>
      wbind G Γ i (tyFin n) lzero ltac:(fun _ => tm_lv l ltac:(eapply wf_dnth_eq;
        [ first [exact compt_D | exact compt_M] | lvl_ok | wctx | wty | wty
        | dnth_ext ltac:(wty) | dnth_ext ltac:(wnorm; wty) | dnth_ext ltac:(wnorm; wty) | dnth_ext ltac:(wnorm; weq) | dnth_ext ltac:(wnorm; weq)
        | wty | wty | wnorm; reflexivity ]))
  | |- [ ?G ; ?Γ ⊢[ ?i ] tyDVec ?l ?n _ @ _ ] =>
      wbind G Γ i (tyFin n) lzero ltac:(fun _ => ty_lv l ltac:(apply wft_dvec; [ discriminate | lvl_ok | wty | wty ]))
  | |- [ ?G ; ?Γ ⊢[ ?i ] tyIWf ?l ?li _ ?A _ _ _ _ @ _ ] =>
      wbind G Γ i A l ltac:(fun HA =>
        ty_lv (lmax l li) ltac:(apply wft_iwf; [ discriminate | lvl_ok | lvl_ok | wty | exact HA | wty | wty | wtop | wty ]))
  | |- [ ?G ; ?Γ ⊢[ ?i ] tmDVec _ ?n _ : _ @ _ ] =>
      wbind G Γ i (tyFin n) lzero ltac:(fun _ => apply wf_code_dvec; [ discriminate | lvl_ok | wty | wty ])
  | |- [ ?G ; ?Γ ⊢[ ?i ] tmIWf ?l _ _ ?s _ _ _ _ : _ @ _ ] =>
      wbind G Γ i (tyEl l s) l ltac:(fun _ =>
        apply wf_code_iwf; [ discriminate | lvl_ok | lvl_ok | wty | wty | wty | wty | wtop | wty ])
  | |- [ ?G ; ?Γ ⊢[ ?i ] tmSupi ?l _ _ ?A _ _ _ _ _ : _ @ _ ] =>
      wbind G Γ i A l ltac:(fun HA =>
        eapply wf_supi_eq; [ discriminate | lvl_ok | lvl_ok | wty | exact HA | wty | wty | wtop | wty | wty
                           | wnorm; reflexivity ])
  end
(** The three conversions [nth]'s unfolding crosses (M15b): [Fin 0] is
    empty, [Fin (S n)] a sum and [Vec(A; S n)] a pair. *)
with wconv :=
  first [ wconv1 | eapply eqty_lconv; [ wconv1 | lalg ] ]
with wconv1 :=
  lazymatch goal with
  | |- [ _ ; _ ⊢[ _ ] tyEmpty _ ≅ tyFin zero @ _ ] =>
      apply eqty_sym, eqty_fin_zero; [ first [exact compt_D | exact compt_M] | wnorm; wctx ]
  | |- [ _ ; _ ⊢[ _ ] tySum _ _ _ _ ≅ tyFin (succ _) @ _ ] =>
      apply eqty_sym, eqty_fin_succ; [ first [exact compt_D | exact compt_M] | wty ]
  | |- [ _ ; _ ⊢[ _ ] tySig _ _ _ _ ≅ tyVec _ _ (succ _) @ _ ] =>
      eapply eqty_vec_succ_eq; [ first [exact compt_D | exact compt_M] | lvl_ok | wty | wty | wnorm; reflexivity .. ]
  (* [dnth]'s (M17c): [Fin (S n)] a sum the other way, [DVec (S n)] a pair *)
  | |- [ _ ; _ ⊢[ _ ] tyFin zero ≅ tyEmpty _ @ _ ] =>
      apply eqty_fin_zero; [ first [exact compt_D | exact compt_M] | wnorm; wctx ]
  | |- [ _ ; _ ⊢[ _ ] tyFin (succ _) ≅ tySum _ _ _ _ @ _ ] =>
      apply eqty_fin_succ; [ first [exact compt_D | exact compt_M] | wty ]
  | |- [ _ ; _ ⊢[ _ ] tySig _ _ _ _ ≅ tyDVec _ (succ _) _ @ _ ] =>
      eapply eqty_dvec_succ_eq; [ first [exact compt_D | exact compt_M] | lvl_ok | wty | wtop | wnorm; reflexivity .. ]
  end
(** Conversion up to β and Unit-η ([dnth]'s, M17c): syntactic equality,
    else congruence down to the redexes. *)
with weq :=
  wnorm;
  lazymatch goal with
  | |- [ _ ; _ ⊢[ _ ] ?T ≅ ?T @ _ ] => apply eqty_refl; wty
  | |- [ ?G ; ?Γ ⊢[ ?i ] tyPi ?l ?l' ?A _ ≅ tyPi _ _ _ _ @ _ ] =>
      wbind G Γ i A l ltac:(fun HA =>
        ety_lv (lmax l l') ltac:(eapply eqty_pi; [ discriminate | lalg | lalg | exact HA | weq | weq ]))
  | |- [ ?G ; ?Γ ⊢[ ?i ] tyDVec ?l ?n _ ≅ tyDVec _ _ _ @ _ ] =>
      wbind G Γ i (tyFin n) lzero ltac:(fun _ =>
        ety_lv l ltac:(eapply eqty_dvec; [ discriminate | lalg | wty | weqt | wty | weq ]))
  | |- [ ?G ; ?Γ ⊢[ ?i ] tyIWf ?l ?li _ ?A _ _ _ _ ≅ tyIWf _ _ _ _ _ _ _ _ @ _ ] =>
      wbind G Γ i A l ltac:(fun HA =>
        ety_lv (lmax l li) ltac:(eapply eqty_iwf;
          [ discriminate | lalg | lalg | wty | weq | exact HA | weq | wty | weqt | wty | weqt | wtop | wtopq | weqt ]))
  | |- [ _ ; _ ⊢[ _ ] tyFin _ ≅ tyFin _ @ _ ] => apply eqty_fin; [ discriminate | weqt ]
  end
with weqt :=
  wnorm;
  lazymatch goal with
  | |- [ _ ; _ ⊢[ _ ] ?t ≅ ?t : _ @ _ ] => apply eqtm_refl; wty
  | |- [ _ ; _ ⊢[ _ ] _ ≅ _ : tyUnit _ @ _ ] =>
      apply eqtm_unit_eta; [ first [exact compt_D | exact compt_M] | lvl_ok | wty | wty ]
  | |- [ ?G ; ?Γ ⊢[ ?i ] app (lam ?l ?l' ?A _) _ _ _ _ _ ≅ _ : _ @ _ ] =>
      wbind G Γ i A l ltac:(fun HA =>
        eapply eqtm_trans;
        [ etm_lv l' ltac:(eapply eqtm_beta_eq;
            [ wnorm; reflexivity | first [exact compt_D | exact compt_M] | lvl_ok | lvl_ok | exact HA | wty | wty | wty ])
        | weqt ])
  | |- [ _ ; _ ⊢[ _ ] _ ≅ app (lam _ _ _ _) _ _ _ _ _ : _ @ _ ] => apply eqtm_sym; weqt
  | |- [ ?G ; ?Γ ⊢[ ?i ] app ?e ?l ?l' ?A _ _ ≅ app _ _ _ _ _ _ : _ @ _ ] =>
      first [ is_var e; wty_hyp |
      wbind G Γ i A l ltac:(fun HA => etm_lv l' ltac:(
        eapply eqtm_app_eq; [ wnorm; reflexivity | discriminate | lalg | lalg | exact HA | weq | weq | weqt | weqt ])) ]
  | |- [ _ ; _ ⊢[ _ ] gvar _ _ ≅ gvar _ _ : _ @ _ ] =>
      eapply eqtm_gvar_eq; [ wctx | glookup | unfold lle; cbn; lia
                           | split; [reflexivity | intros; cbn; f_equal; lia] | wdnf
                           | split; [reflexivity | intros; cbn; f_equal; lia] | wdnf
                           | let H := fresh "Hin" in intros ? ? ? H; inv_in_ctx; wty
                           | let H := fresh "Hin" in intros ? ? ? H; inv_in_ctx; wty
                           | let H := fresh "Hin" in intros ? ? ? H; inv_in_ctx; weqt | wnorm; reflexivity ]
  (* an injection at [Fin (S n)], as the sum it is *)
  | |- [ _ ; _ ⊢[ _ ] tmInl _ _ _ _ _ ≅ tmInl _ _ _ _ _ : tyFin (succ _) @ _ ] =>
      eapply eqtm_conv; [ eapply eqtm_lconv; [ eapply eqtm_inl; [ discriminate | lalg | lalg | weq | weq | weqt ] | lalg ]
                        | wnorm; wconv ]
  | |- [ _ ; _ ⊢[ _ ] tmInr _ _ _ _ _ ≅ tmInr _ _ _ _ _ : tyFin (succ _) @ _ ] =>
      eapply eqtm_conv; [ eapply eqtm_lconv; [ eapply eqtm_inr; [ discriminate | lalg | lalg | weq | weq | weqt ] | lalg ]
                        | wnorm; wconv ]
  (* [dnth]'s family's index under abstract locals, at its premise's
     equation ([wf_dnth_eq]) *)
  | |- [ _ ; _ ⊢[ _ ] _ ≅ _ : _ @ _ ] => wty_hyp
  end
with wtopq :=
  lazymatch goal with
  | |- [ ?G ; ?Γ ⊢[ ?i ] _ ≅ _ : _ @ _ ] =>
      let HΓ := fresh "HΓ" in assert (HΓ : [ G ; Γ ⊢[ typeof i ] ]) by (wnorm; wctx); weqt
  end
(** A judgement in a context: the context first, then the judgement. *)
with wtop :=
  lazymatch goal with
  | |- [ _ ; _ ⊢[ _ ] ] => wctx
  | |- [ ?G ; ?Γ ⊢[ ?i ] _ @ _ ] =>
      let HΓ := fresh "HΓ" in assert (HΓ : [ G ; Γ ⊢[ typeof i ] ]) by (wnorm; wctx); wty
  | |- [ ?G ; ?Γ ⊢[ ?i ] _ : _ @ _ ] =>
      let HΓ := fresh "HΓ" in assert (HΓ : [ G ; Γ ⊢[ typeof i ] ]) by (wnorm; wctx); wty
  end.

(** The scopes' declarations, one by one, each prefix proved once. *)
Ltac wglob :=
  lazymatch goal with
  | |- [ ⊢ mkG _ (gdCtx :: _) ] => apply wfg_ctx; wglob
  | |- [ ⊢ mkG ?L (gdTy _ _ _ :: ?Ψ) ] =>
      let HΨ := fresh "HΨ" in assert (HΨ : [ ⊢ mkG L Ψ ]) by wglob;
      apply wfg_ty; [ exact HΨ | wtop | first [left; reflexivity | right; reflexivity] | lvl_ok ]
  | |- [ ⊢ mkG ?L (gdTm _ _ _ _ :: ?Ψ) ] =>
      let HΨ := fresh "HΨ" in assert (HΨ : [ ⊢ mkG L Ψ ]) by wglob;
      apply wfg_tm; [ exact HΨ | wtop | first [left; reflexivity | right; reflexivity] | lvl_ok ]
  | |- [ ⊢ _ ] => assumption
  end.

Section Scopes.
Context {G : gctx} (HG : [ ⊢ G ]).

Lemma wf_recGT : [ ⊢ recGT G ].
Proof using HG. unfold recGT; cbn. apply wfg_ctx. exact (uwk_glob 1 G HG). Qed.

Lemma wf_recGt : [ ⊢ recGt G ].
Proof using HG.
  pose proof (uwk_glob 1 G HG) as H1. unfold recGt, gctx_uwk in *; cbn [gL gΨ] in *.
  wfd_all.
Qed.

Lemma wf_brG_W k : 39 <= k < 43 -> [ ⊢ brG k G ].
Proof using HG.
  intros Hk. pose proof (uwk_glob (br_nu k) G HG) as Hu.
  unfold brG, gctx_uwk in *; cbn [gL gΨ] in *.
  assert (k = 39 \/ k = 40 \/ k = 41 \/ k = 42) as [E|[E|[E|E]]] by lia; subst k;
    cbn [brDecls List.app br_nu br_ar] in *; unfold gv, gu; wnorm; wglob.
Qed.

Lemma wf_brG_Wf k : 47 <= k < 51 -> [ ⊢ brG k G ].
Proof using HG.
  intros Hk. pose proof (uwk_glob (br_nu k) G HG) as Hu.
  unfold brG, gctx_uwk in *; cbn [gL gΨ] in *.
  assert (k = 47 \/ k = 48 \/ k = 49 \/ k = 50) as [E|[E|[E|E]]] by lia; subst k;
    cbn [brDecls List.app br_nu br_ar] in *; unfold gv, gu; wnorm; wglob.
Qed.

Lemma wf_brG_IWf k : 55 <= k < 60 -> [ ⊢ brG k G ].
Proof using HG.
  intros Hk. pose proof (uwk_glob (br_nu k) G HG) as Hu.
  unfold brG, gctx_uwk in *; cbn [gL gΨ] in *.
  assert (k = 55 \/ k = 56 \/ k = 57 \/ k = 58 \/ k = 59) as [E|[E|[E|[E|E]]]] by lia; subst k;
    cbn [brDecls List.app br_nu br_ar] in *; unfold gv, gu; wnorm; wglob.
Qed.

(** [elim_IWf]'s branch (M17c): its step's context carries [dnth] in the
    induction hypothesis's type, typed by its unfolding ([wty]). *)
Lemma wf_brG_60 : [ ⊢ brG 60 G ].
Proof using HG.
  pose proof (uwk_glob (br_nu 60) G HG) as Hu.
  unfold brG, gctx_uwk in *; cbn [gL gΨ] in *.
  cbn [brDecls List.app br_nu br_ar] in *; unfold gv, gu; wnorm; wglob.
Qed.

Lemma wf_brG k : k < nbr -> [ ⊢ brG k G ].
Proof using HG.
  intros Hk. assert (HW : 39 <= k < 43 \/ ~ 39 <= k < 43) by lia.
  destruct HW as [HW|HW]; [now apply wf_brG_W|].
  assert (HF : 47 <= k < 51 \/ ~ 47 <= k < 51) by lia.
  destruct HF as [HF|HF]; [now apply wf_brG_Wf|].
  assert (HI : 55 <= k < 60 \/ ~ 55 <= k < 60) by lia.
  destruct HI as [HI|HI]; [now apply wf_brG_IWf|].
  assert (H60 : k = 60 \/ k <> 60) by lia.
  destruct H60 as [->|H60]; [exact wf_brG_60|].
  pose proof (uwk_glob (br_nu k) G HG) as Hu.
  unfold brG, gctx_uwk in *; cbn [gL gΨ] in *.
  br_all ltac:(destruct k; [first [exfalso; lia | cbn [brDecls List.app br_nu br_ar] in *; unfold gv, gu;
    cbn [ren Ren_ty Ren_tm ren_ty ren_tm lren r2l rdrop rshift1]; wfd_all]|]). lia.
Qed.

End Scopes.
