(** * The recursors' scopes are well formed (M3)

    If [G] is well formed, so are the global contexts of the motives
    ([recGT], [recGt]) and of the branches ([brG k]): their declarations
    (04:1150–1300) are well formed in the universe-weakened [G]. *)
From DeLaM.Typing Require Export USubstitution.
From DeLaM.Syntax Require Import SubstCommute.

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
  | |- in_gctx ?Ψ ?n _ =>
      let H := fresh in pose proof (in_gctx_nth Ψ n _ eq_refl) as H; cbn in H; exact H
  end.

Ltac lvl_ok := cbn; repeat split; try lia.

(** Well-formedness of the concrete scope declarations. *)
Ltac wfd :=
  repeat match goal with
  | |- [ ⊢ mkG _ (gdCtx :: _) ] => apply wfg_ctx
  | |- [ ⊢ mkG _ (gdTy _ _ _ :: _) ] => apply wfg_ty; [ | | first [left; reflexivity | right; reflexivity] | lvl_ok ]
  | |- [ ⊢ mkG _ (gdTm _ _ _ _ :: _) ] => apply wfg_tm; [ | | first [left; reflexivity | right; reflexivity] | lvl_ok ]
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

Section Scopes.
Context {G : gctx} (HG : [ ⊢ G ]).

Lemma wf_recGT : [ ⊢ recGT G ].
Proof. unfold recGT; cbn. apply wfg_ctx. exact (uwk_glob 1 G HG). Qed.

Lemma wf_recGt : [ ⊢ recGt G ].
Proof.
  pose proof (uwk_glob 1 G HG) as H1. unfold recGt, gctx_uwk in *; cbn [gL gΨ] in *.
  wfd_all.
Qed.

Lemma wf_brG k : k < nbr -> [ ⊢ brG k G ].
Proof.
  intros Hk. pose proof (uwk_glob (br_nu k) G HG) as Hu.
  unfold brG, gctx_uwk in *; cbn [gL gΨ] in *.
  br_all ltac:(destruct k; [cbn [brDecls List.app br_nu br_ar] in *; unfold gv, gu;
    cbn [ren Ren_ty Ren_tm ren_ty ren_tm lren r2l rdrop rshift1]; wfd_all|]). lia.
Qed.

End Scopes.
