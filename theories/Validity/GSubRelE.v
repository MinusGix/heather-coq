(** * Extending related global substitutions by one binding

    For [letbox]: a [box]ed scrutinee extends [σ ≈ σ'] by its (literally
    equal) code ([gcons]); a neutral scrutinee needs [σ ≈ σ'] pushed under
    the new binding, sending it to [U₀^id] on both sides
    ([gsub_up_id]).  Both are an extension ([GSubRel_cons]), the latter of
    the weakened pair ([GSubRel_wk]). *)
From DeLaM.Validity Require Export GSubRelW.

#[local] Existing Instance LR_P.

Definition gcons (σ : gsub) (o : gobj) : gsub := fun n => match n with 0 => o | S n => σ n end.

(** [⇑σ] with the new binding sent to its identity instance. *)
Definition gsub_up_id (D : gdecl) (σ : gsub) : gsub := gcons (gsub_wk σ (gwk_step gwk_id)) (id_obj D 0).

(** ** Syntax *)

Lemma gcons_shift_ctx (Γ : ctx) σ o : Γ⟪S⟫⦃gcons σ o⦄ = Γ⦃σ⦄.
Proof. apply gsubst_gren_ctx; reflexivity. Qed.
Lemma gcons_shift_ty (T : ty) σ o : T⟪S⟫⦃gcons σ o⦄ = T⦃σ⦄.
Proof. apply gsubst_gren_ty; reflexivity. Qed.

Lemma gdecl_gsubst_cons D σ o : gdecl_gsubst (gdecl_ren D S) (gcons σ o) = gdecl_gsubst D σ.
Proof. destruct D; cbn [gdecl_gsubst gdecl_ren]; f_equal; auto using gcons_shift_ctx, gcons_shift_ty. Qed.

Lemma gosubst_shift_single o' o : dnfo o' -> gosubst (goren o' S) (gsingle o) = o'.
Proof.
  intros Ho. destruct o' as [j | Γ | T | t]; cbn in *; [reflexivity | f_equal ..].
  - rewrite (gsubst_gren_ctx _ _ _ (fun j => GId j)) by reflexivity. apply gsubst_id_ctx; auto.
  - rewrite (gsubst_gren_ty _ _ _ (fun j => GId j)) by reflexivity. apply gsubst_id_ty; auto.
  - rewrite (gsubst_gren_tm _ _ _ (fun j => GId j)) by reflexivity. apply gsubst_id; auto.
Qed.

(** Letbox β: the body under [⇑σ], then the code. *)
Lemma gup_single_tm (t : tm) σ o : (forall n, dnfo (σ n)) -> t⦃gup σ⦄⦃gsingle o⦄ = t⦃gcons σ o⦄.
Proof.
  intros Hσ. apply gsubst_gsubst. intros [|n]; cbn [gcons gup]; [reflexivity|].
  symmetry; apply gosubst_shift_single, Hσ.
Qed.

(** On well-typed syntax, [⇑σ] is [σ] pushed under the binding with
    [U₀^id]. *)
Lemma gsub_equiv_up_id G D σ : gsub_equiv (gext G D) (gup σ) (gsub_up_id D σ).
Proof.
  intros n D0 Hin. inversion Hin as [Ψ0 D1 | Ψ0 D1 D2 m Hm]; subst; cbn [gup gsub_up_id gcons].
  - right; left. exists 0; split; [reflexivity|]. now destruct D.
  - left. reflexivity.
Qed.

Lemma dnfo_gsub_up_id D σ : forall n, dnfo (gsub_up_id D σ n).
Proof. intros [|n]; cbn; [destruct D; cbn; auto | apply dnfo_goren]. Qed.

Lemma gsubst_up_id_tm {G Γ t T l} i D σ : [ gext G D ; Γ ⊢[ i ] t : T @ l ] ->
  t⦃gup σ⦄ = t⦃gsub_up_id D σ⦄.
Proof.
  intros H. exact (proj1 (proj2 (proj2 (proj2 equiv_gsubst))) _ _ _ _ _ _ H _ _
                     (gsub_equiv_up_id G D σ) (dnfo_gsub_up_id D σ)).
Qed.

Section GSubRelE.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM}.

Local Notation GSubRel := (GSubRel EP EM).
Local Notation GObjRel := (GObjRel EP EM).

Lemma gsub_wf_cons {G' G σ D o} : [ G' ⊢ σ : G ] -> dnfo o -> gobj_wf G' o (gdecl_gsubst D σ) ->
  [ G' ⊢ gcons σ o : gext G D ].
Proof.
  intros [Hg Hn Hv] Ho Hw. constructor; [exact Hg | intros [|n]; [exact Ho | apply Hn] |].
  intros n D0 Hin. inversion Hin as [Ψ0 D1 | Ψ0 D1 D2 m Hm]; subst; cbn [gcons]; rewrite gdecl_gsubst_cons;
    [exact Hw | exact (Hv _ _ Hm)].
Qed.

Lemma GRel0_cons {G' G σ σ' D o o'} : GRel0 EP EM G' G σ σ' -> GObjRel G' (gdecl_gsubst D σ) o o' ->
  GRel0 EP EM G' (gext G D) (gcons σ o) (gcons σ' o').
Proof.
  intros H Ho n D0 Hin. inversion Hin as [Ψ0 D1 | Ψ0 D1 D2 m Hm]; subst; cbn [gcons]; rewrite gdecl_gsubst_cons;
    [exact Ho | exact (H _ _ Hm)].
Qed.

(** Extension by an object related to itself on both sides. *)
Lemma GSubRel_cons {G' G σ σ' D o} : GSubRel G' G σ σ' -> dnfo o ->
  gobj_wf G' o (gdecl_gsubst D σ) -> gobj_wf G' o (gdecl_gsubst D σ') ->
  GObjRel G' (gdecl_gsubst D σ) o o -> GObjRel G' (gdecl_gsubst D σ') o o ->
  GSubRel G' (gext G D) (gcons σ o) (gcons σ' o).
Proof.
  intros [HL Hl Hr H1 H2 H3] Ho Hw Hw' R R'. constructor.
  - exact HL.
  - exact (gsub_wf_cons Hl Ho Hw).
  - exact (gsub_wf_cons Hr Ho Hw').
  - exact (GRel0_cons H1 R).
  - exact (GRel0_cons H2 R).
  - exact (GRel0_cons H3 R').
Qed.

(** Extension by related objects, one on each side. *)
Lemma GSubRel_cons2 {G' G σ σ' D o o'} : GSubRel G' G σ σ' -> dnfo o -> dnfo o' ->
  gobj_wf G' o (gdecl_gsubst D σ) -> gobj_wf G' o' (gdecl_gsubst D σ') ->
  GObjRel G' (gdecl_gsubst D σ) o o' -> GObjRel G' (gdecl_gsubst D σ) o o ->
  GObjRel G' (gdecl_gsubst D σ') o' o' ->
  GSubRel G' (gext G D) (gcons σ o) (gcons σ' o').
Proof.
  intros [HL Hl Hr H1 H2 H3] Ho Ho' Hw Hw' R Rl Rr. constructor.
  - exact HL.
  - exact (gsub_wf_cons Hl Ho Hw).
  - exact (gsub_wf_cons Hr Ho' Hw').
  - exact (GRel0_cons H1 R).
  - exact (GRel0_cons H2 Rl).
  - exact (GRel0_cons H3 Rr).
Qed.

(** Pushing under the binding. *)
Lemma GSubRel_up_id {G' G σ σ' D} : GSubRel G' G σ σ' ->
  [ ⊢ gext G' (gdecl_gsubst D σ) ] ->
  gobj_wf (gext G' (gdecl_gsubst D σ)) (id_obj D 0) (gdecl_ren (gdecl_gsubst D σ) S) ->
  gobj_wf (gext G' (gdecl_gsubst D σ)) (id_obj D 0) (gdecl_ren (gdecl_gsubst D σ') S) ->
  GObjRel (gext G' (gdecl_gsubst D σ)) (gdecl_ren (gdecl_gsubst D σ) S) (id_obj D 0) (id_obj D 0) ->
  GObjRel (gext G' (gdecl_gsubst D σ)) (gdecl_ren (gdecl_gsubst D σ') S) (id_obj D 0) (id_obj D 0) ->
  GSubRel (gext G' (gdecl_gsubst D σ)) (gext G D) (gsub_up_id D σ) (gsub_up_id D σ').
Proof.
  intros Hσ HG Hw Hw' R R'.
  assert (Hγ : gwk_ok (gwk_step gwk_id) (gext G' (gdecl_gsubst D σ)) G')
    by (split; [reflexivity | constructor; constructor]).
  pose proof (GSubRel_wk EP EM Hσ Hγ HG) as Hs.
  apply GSubRel_cons; [exact Hs | now destruct D | ..];
    rewrite <- gdecl_gsubst_wk by discriminate; assumption.
Qed.

End GSubRelE.
