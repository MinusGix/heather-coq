(** * N1 is admissible, and Heather's [u^δ] translates (M9_DESIGN.md, open item 2)

    The occurrence rules of a defined global ([wf_gdef], [eqtm_gdef],
    [eqtm_delta]) carry the body's typing at the use layer (N1). That
    premise is derivable from [⊢ G]: the body is typed at C in its prefix
    ([wfg_def]) and weakened to [G] ([gctx_decl_ok]); the Static Code Lemma
    carries it to a level-equivalent variant (N2), and lifting to the use
    layer [i ≥ C]. So the three rules without it are admissible
    ([wf_gdef_adm], [eqtm_gdef_adm], [eqtm_delta_adm]). The variant's
    well-formed levels, the one premise they add, are necessary
    ([wf_gdef_lwf]).

    The translation of Heather's syntax (M9_DESIGN.md (b)) sends an
    occurrence [u^δ] to [occ Ψ u δ]: [gdef u t₀ δ] with the declared body
    when [Ψ] defines [u], [gvar u δ] otherwise. It is a function, so total,
    and the images of Heather's three rules for [u^δ] (use at [c ≤ j],
    congruence, δ at the computing layers) are derivable here
    ([occ_wf], [occ_eq], [occ_delta]). Every other rule is the same in
    both systems and the translation is the identity elsewhere, so every
    Heather derivation translates, rule by rule, to one of ours. *)
From DeLaM.Typing Require Import RecWf Inversion StaticCode.

(** ** The body, from [⊢ G] *)

Lemma def_body {G u Δ T l t0} : [ ⊢ G ] -> in_gctx (gΨ G) u (gdDef Δ T l t0) ->
  [ G ; Δ ⊢[ lD ] T @ l ] /\ [ G ; Δ ⊢[ lC ] t0 : T @ l ].
Proof. intros Hg Hin. destruct (gctx_decl_ok _ _ _ Hg Hin) as (_ & HT & _ & Ht). auto. Qed.

(** A level-equivalent variant of the body with well-formed levels is
    typed at C and equal to it there (the Static Code Lemma). *)
Lemma def_body_var {G u Δ T l t0 t} : [ ⊢ G ] -> in_gctx (gΨ G) u (gdDef Δ T l t0) ->
  tm_leq t0 t -> tm_lwf (gL G) t ->
  [ G ; Δ ⊢[ lC ] t : T @ l ] /\ [ G ; Δ ⊢[ lC ] t0 ≅ t : T @ l ].
Proof.
  intros Hg Hin E W. destruct (def_body Hg Hin) as (_ & Ht0).
  exact (proj1 (proj2 (proj2 (proj2 static_code))) _ _ _ _ _ _ Ht0 ltac:(unfold lle; cbn; lia) _ E W).
Qed.

(** N1: the premise [wf_gdef] adds, at every use layer. *)
Theorem n1_adm {G i u Δ T l t0 t} : [ ⊢ G ] -> in_gctx (gΨ G) u (gdDef Δ T l t0) ->
  tm_leq t0 t -> tm_lwf (gL G) t -> lle lC i -> [ G ; Δ ⊢[ i ] t : T @ l ].
Proof. intros Hg Hin E W Hi. exact (lift_tm (proj1 (def_body_var Hg Hin E W)) Hi). Qed.

(** The premise [eqtm_gdef] adds. *)
Lemma n1_adm_eq {G i u Δ T l t0 t t'} : [ ⊢ G ] -> in_gctx (gΨ G) u (gdDef Δ T l t0) ->
  tm_leq t0 t -> tm_lwf (gL G) t -> tm_leq t0 t' -> tm_lwf (gL G) t' -> lle lC i ->
  [ G ; Δ ⊢[ i ] t ≅ t' : T @ l ].
Proof.
  intros Hg Hin E W E' W' Hi.
  destruct (def_body_var Hg Hin E W) as (_ & H). destruct (def_body_var Hg Hin E' W') as (_ & H').
  exact (lift_eqtm (eqtm_trans _ _ _ _ _ _ _ _ (eqtm_sym _ _ _ _ _ _ _ H) H') Hi).
Qed.

(** ** The rules without N1's premise *)

Lemma wf_gdef_adm G i Γ u Δ T l t0 t d : [ G ; Γ ⊢[ typeof i ] ] ->
  in_gctx (gΨ G) u (gdDef Δ T l t0) -> tm_leq t0 t -> tm_lwf (gL G) t -> lle lC i ->
  lsub_tail d Δ Γ -> dnfl d ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n : A[d] @ k ]) ->
  [ G ; Γ ⊢[ i ] gdef u t d : T[d] @ l ].
Proof.
  intros HΓ Hin E W Hi Ht Nd Hd.
  eapply wf_gdef; try eassumption. exact (n1_adm (ctx_glob _ _ _ HΓ) Hin E W Hi).
Qed.

Lemma eqtm_gdef_adm G i Γ u Δ T l t0 t t' d d' : [ G ; Γ ⊢[ typeof i ] ] ->
  in_gctx (gΨ G) u (gdDef Δ T l t0) -> tm_leq t0 t -> tm_lwf (gL G) t ->
  tm_leq t0 t' -> tm_lwf (gL G) t' -> lle lC i ->
  lsub_tail d Δ Γ -> dnfl d -> lsub_tail d' Δ Γ -> dnfl d' ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n : A[d] @ k ]) ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d' n : A[d'] @ k ]) ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n ≅ llk d' n : A[d] @ k ]) ->
  [ G ; Γ ⊢[ i ] gdef u t d ≅ gdef u t' d' : T[d] @ l ].
Proof.
  intros HΓ Hin E W E' W' Hi. intros.
  eapply eqtm_gdef; try eassumption. exact (n1_adm_eq (ctx_glob _ _ _ HΓ) Hin E W E' W' Hi).
Qed.

Lemma eqtm_delta_adm G i Γ u Δ T l t0 t d : compt i -> [ G ; Γ ⊢[ typeof i ] ] ->
  in_gctx (gΨ G) u (gdDef Δ T l t0) -> tm_leq t0 t -> tm_lwf (gL G) t ->
  lsub_tail d Δ Γ -> dnfl d ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n : A[d] @ k ]) ->
  [ G ; Γ ⊢[ i ] gdef u t d ≅ t[d] : T[d] @ l ].
Proof.
  intros Hc HΓ Hin E W. intros.
  assert (Hi : lle lC i) by (destruct Hc as [-> | ->]; unfold lle; cbn; lia).
  eapply eqtm_delta; try eassumption. exact (n1_adm (ctx_glob _ _ _ HΓ) Hin E W Hi).
Qed.

(** The added premise is necessary: a typed occurrence's body has
    well-formed levels. *)
Lemma wf_gdef_lwf {G i Γ u t d T l} : [ G ; Γ ⊢[ i ] gdef u t d : T @ l ] -> tm_lwf (gL G) t.
Proof. intros H. exact (proj1 (wf_tm_lwf H)). Qed.

(** ** The translation of Heather's [u^δ] *)

(** Heather's term bindings: [u : Trm_i(Δ ⊢ T @ l)], opaque ([gdTm]), or
    defined at C ([gdDef]), its use layer then [c ≤ j] (M9_DESIGN.md). *)
Definition htrm (D : gdecl) (Δ : ctx) (i : layer) (T : ty) (l : lvl) : Prop :=
  D = gdTm Δ i T l \/ (exists t0, D = gdDef Δ T l t0 /\ i = lC).

(** The occurrence [u^δ]: [gdef] with the declared body (weakened to [Ψ],
    as [in_gctx] reads it) when [Ψ] defines [u], [gvar] otherwise. *)
Definition occ (Ψ : list gdecl) (u : nat) (d : lsub) : tm :=
  match nth_error Ψ u with
  | Some (gdDef _ _ _ t) => gdef u t⟪Nat.add (S u)⟫ d
  | _ => gvar u d
  end.

Lemma in_gctx_nth_inv {Ψ n D} : in_gctx Ψ n D ->
  exists D0, nth_error Ψ n = Some D0 /\ D = gdecl_ren D0 (Nat.add (S n)).
Proof.
  intros Hin.
  assert (H : exists D0, nth_error Ψ n = Some D0).
  { induction Hin as [Ψ D | Ψ D D' n _ IH]; cbn; eauto. }
  destruct H as (D0 & E). exists D0. split; [exact E|]. exact (in_gctx_det Hin (in_gctx_nth _ _ _ E)).
Qed.

Lemma occ_def {Ψ u Δ T l t0} d : in_gctx Ψ u (gdDef Δ T l t0) -> occ Ψ u d = gdef u t0 d.
Proof.
  intros Hin. destruct (in_gctx_nth_inv Hin) as ([] & E & H); cbn in H; try discriminate.
  injection H as _ _ _ ->. unfold occ. now rewrite E.
Qed.

Lemma occ_tm {Ψ u Δ i T l} d : in_gctx Ψ u (gdTm Δ i T l) -> occ Ψ u d = gvar u d.
Proof.
  intros Hin. destruct (in_gctx_nth_inv Hin) as ([] & E & H); cbn in H; try discriminate.
  unfold occ. now rewrite E.
Qed.

(** Heather's use rule, translated. *)
Theorem occ_wf G i Γ u D Δ i' T l d : [ G ; Γ ⊢[ typeof i ] ] ->
  in_gctx (gΨ G) u D -> htrm D Δ i' T l -> lle i' i -> lsub_tail d Δ Γ -> dnfl d ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n : A[d] @ k ]) ->
  [ G ; Γ ⊢[ i ] occ (gΨ G) u d : T[d] @ l ].
Proof.
  intros HΓ Hin [-> | (t0 & -> & ->)] Hi Ht Nd Hd.
  - rewrite (occ_tm _ Hin). eapply wf_gvar; eassumption.
  - rewrite (occ_def _ Hin).
    destruct (def_body (ctx_glob _ _ _ HΓ) Hin) as (_ & Ht0).
    eapply wf_gdef_adm; try eassumption; [apply tm_leq_refl | exact (wf_tm_lwf Ht0)].
Qed.

(** Heather's congruence for [u^δ], translated. *)
Theorem occ_eq G i Γ u D Δ i' T l d d' : [ G ; Γ ⊢[ typeof i ] ] ->
  in_gctx (gΨ G) u D -> htrm D Δ i' T l -> lle i' i ->
  lsub_tail d Δ Γ -> dnfl d -> lsub_tail d' Δ Γ -> dnfl d' ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n : A[d] @ k ]) ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d' n : A[d'] @ k ]) ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n ≅ llk d' n : A[d] @ k ]) ->
  [ G ; Γ ⊢[ i ] occ (gΨ G) u d ≅ occ (gΨ G) u d' : T[d] @ l ].
Proof.
  intros HΓ Hin [-> | (t0 & -> & ->)] Hi. all: intros.
  - rewrite (occ_tm d Hin), (occ_tm d' Hin). eapply eqtm_gvar; eassumption.
  - rewrite (occ_def d Hin), (occ_def d' Hin).
    destruct (def_body (ctx_glob _ _ _ HΓ) Hin) as (_ & Ht0).
    eapply eqtm_gdef_adm; try eassumption; first [apply tm_leq_refl | exact (wf_tm_lwf Ht0)].
Qed.

(** Heather's δ, translated: [u^δ ⇝ t₀[δ]] at the computing layers. *)
Theorem occ_delta G i Γ u Δ T l t0 d : compt i -> [ G ; Γ ⊢[ typeof i ] ] ->
  in_gctx (gΨ G) u (gdDef Δ T l t0) -> lsub_tail d Δ Γ -> dnfl d ->
  (forall n A k, in_ctx Δ n A k -> [ G ; Γ ⊢[ i ] llk d n : A[d] @ k ]) ->
  [ G ; Γ ⊢[ i ] occ (gΨ G) u d ≅ t0[d] : T[d] @ l ].
Proof.
  intros Hc HΓ Hin. intros. rewrite (occ_def d Hin).
  destruct (def_body (ctx_glob _ _ _ HΓ) Hin) as (_ & Ht0).
  eapply eqtm_delta_adm; try eassumption; [apply tm_leq_refl | exact (wf_tm_lwf Ht0)].
Qed.
