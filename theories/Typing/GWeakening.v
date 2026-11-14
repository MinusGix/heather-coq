(** * Global weakening of every judgment

    [γ : Ψ' ≤ Ψ] (OPE data, [gwk_wf]) sends every judgment under [Ψ] to one
    under [Ψ'], at every layer.  The only binder of the global dimension so
    far is [letbox]'s body, typed under [Ψ, U] / [Ψ, u] with the local
    context globally shifted: it is handled by [gwk_up]. *)
(* [≡ₗ]'s laws first, as in [USubstitution] (which needs only [LevelEqURen]) *)
From DeLaM.Syntax Require Export LevelEq.
From DeLaM.Typing Require Export GRenRec RecWf TypedDnf.

(** ** The theorem *)

Definition gwk_to (G : gctx) (Ψ' : list gdecl) : gctx := mkG (gL G) Ψ'.


Lemma wf_tm_regty G i Δ x T T' l :
  [ G ; Δ ⊢[ i ] x : T' @ l ] -> T' = T -> [ G ; Δ ⊢[ i ] x : T @ l ].
Proof. now intros ? ->. Qed.
Lemma eq_tm_regty G i Δ x y T T' l :
  [ G ; Δ ⊢[ i ] x ≅ y : T' @ l ] -> T' = T -> [ G ; Δ ⊢[ i ] x ≅ y : T @ l ].
Proof. now intros ? ->. Qed.
Lemma wf_ty_regctx G i Δ Δ' T l : [ G ; Δ' ⊢[ i ] T @ l ] -> Δ' = Δ -> [ G ; Δ ⊢[ i ] T @ l ].
Proof. now intros ? ->. Qed.
Lemma eq_ty_regctx G i Δ Δ' T T' l :
  [ G ; Δ' ⊢[ i ] T ≅ T' @ l ] -> Δ' = Δ -> [ G ; Δ ⊢[ i ] T ≅ T' @ l ].
Proof. now intros ? ->. Qed.
(** [elim_W]'s step (M13a): its context and type both hold shifted types. *)
Lemma wf_tm_regctx G i Δ Δ' x T T' l :
  [ G ; Δ' ⊢[ i ] x : T' @ l ] -> Δ' = Δ -> T' = T -> [ G ; Δ ⊢[ i ] x : T @ l ].
Proof. now intros ? -> ->. Qed.
Lemma eq_tm_regctx G i Δ Δ' x y T T' l :
  [ G ; Δ' ⊢[ i ] x ≅ y : T' @ l ] -> Δ' = Δ -> T' = T -> [ G ; Δ ⊢[ i ] x ≅ y : T @ l ].
Proof. now intros ? -> ->. Qed.
Lemma wf_ty_regboth G i Δ Δ' T T' l :
  [ G ; Δ' ⊢[ i ] T' @ l ] -> Δ' = Δ -> T' = T -> [ G ; Δ ⊢[ i ] T @ l ].
Proof. now intros ? -> ->. Qed.
(** [elim_IWf]'s congruence and β (M17b): an equation of types in a shifted
    context, and a term that commutes with the weakening by an equation. *)
Lemma eq_ty_regall G i Δ Δ' T1 T2 T T' l :
  [ G ; Δ' ⊢[ i ] T1 ≅ T2 @ l ] -> Δ' = Δ -> T1 = T -> T2 = T' -> [ G ; Δ ⊢[ i ] T ≅ T' @ l ].
Proof. now intros ? -> -> ->. Qed.
Lemma wf_tm_regtm G i Δ x x' T T' l :
  [ G ; Δ ⊢[ i ] x' : T' @ l ] -> x' = x -> T' = T -> [ G ; Δ ⊢[ i ] x : T @ l ].
Proof. now intros ? -> ->. Qed.
Lemma wf_ty_regty G i Δ A A' l : [ G ; Δ ⊢[ i ] A @ l ] -> A = A' -> [ G ; Δ ⊢[ i ] A' @ l ].
Proof. now intros ? ->. Qed.
Lemma eq_ty_regty G i Δ A B A' B' l :
  [ G ; Δ ⊢[ i ] A ≅ B @ l ] -> A = A' -> B = B' -> [ G ; Δ ⊢[ i ] A' ≅ B' @ l ].
Proof. now intros ? -> ->. Qed.

(* twice: [case]'s branch types (M12b) shift summands inside an injection,
   which the first pass exposes *)
Ltac gw_eq := push_gren; gren_rewrite; push_gren; gren_rewrite; push_gren; first [reflexivity | f_equal; reflexivity].
(* [IWf]'s telescope (M17b) nests deeper: as many rounds as change the goal *)
Ltac gw_eq' := repeat progress (push_gren; gren_rewrite); first [reflexivity | f_equal; reflexivity].

#[export] Hint Resolve in_ctx_gren in_gctx_gwk gctx_var_gwk lsub_tail_gren nfl_gren : gwk.
#[export] Hint Constructors gwk_wf : gwk.
#[export] Hint Extern 1 (in_gctx _ _ _) =>
  match goal with
  | Hγ : gwk_wf ?γ _ _, Hin : in_gctx _ _ _ |- _ => exact (in_gctx_gwk _ _ _ _ _ Hγ Hin)
  end : gwk.
#[export] Hint Resolve wfc_nil wfc_var wfc_ext wfg_ctx wfg_ty wfg_tm lequiv_wf_l lequiv_wf_r : gwk.
#[export] Hint Extern 5 (wf_tm _ _ _ _ _ _) => eapply wf_tm_regty; [ | gw_eq ] : gwk.
#[export] Hint Extern 5 (eq_tm _ _ _ _ _ _ _) => eapply eq_tm_regty; [ | gw_eq ] : gwk.
#[export] Hint Extern 1 (lwf _ _) => (cbn; first [exact I | assumption]) : gwk.
#[export] Hint Extern 1 (lequiv _ _ _) => (cbn; assumption) : gwk.
#[export] Hint Extern 2 (lwf _ _) => (cbn; eapply lwf_weaken; [| eassumption]; cbn; lia) : gwk.
#[export] Hint Extern 2 (lequiv _ _ _) => (cbn; eapply lequiv_weaken; [| eassumption]; cbn; lia) : gwk.
#[export] Hint Extern 1 (_ <= _) => (cbn; lia) : gwk.
#[export] Hint Extern 2 (Forall (lwf _) _) => (cbn; eapply lwfs_weaken; [| eassumption]; cbn; lia) : gwk.
#[export] Hint Extern 2 (Forall2 (lequiv _) _ _) => (cbn; eapply lequivs_weaken; [| eassumption]; cbn; lia) : gwk.
#[export] Hint Extern 1 (lle _ _) => assumption : gwk.
#[export] Hint Extern 1 (_ <> _) => assumption : gwk.
#[export] Hint Extern 1 (compt _) => assumption : gwk.
#[export] Hint Extern 1 (ty_leq _ _) => apply (proj1 leq_gren_all); assumption : gwk.
#[export] Hint Extern 1 (tm_leq _ _) => apply (proj1 (proj2 leq_gren_all)); assumption : gwk.
#[export] Hint Extern 1 (_ = _ \/ _ = _) => first [left; reflexivity | right; reflexivity] : gwk.

Ltac gw_premises := eauto 6 with gwk.

Ltac gw_step := any_rule gw_premises.

(** One premise: directly, or through an induction hypothesis up to a type equation. *)
Ltac gw_premise :=
  first [ solve [eauto 6 with gwk]
        | solve [eapply wf_tm_regty;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 8 with gwk] end | gw_eq]]
        | solve [eapply eq_tm_regty;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 8 with gwk] end | gw_eq]]
        (* the recursors' motive instances (M3_DESIGN.md E10) *)
        | solve [eapply wf_ty_regty;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 8 with gwk] end | gw_eq]]
        | solve [eapply eq_ty_regty;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 8 with gwk] end | gw_eq | gw_eq]]
        (* [J]'s motive (M11a): its context holds shifted types, which commute
           with the weakening only by an equation *)
        | solve [eapply wf_ty_regctx;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 8 with gwk] end | gw_eq]]
        | solve [eapply eq_ty_regctx;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 8 with gwk] end | gw_eq]]
        | solve [eapply wf_tm_regctx;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 8 with gwk] end | gw_eq | gw_eq]]
        | solve [eapply wf_ty_regboth;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 8 with gwk] end | gw_eq | gw_eq]]
        | solve [eapply eq_tm_regctx;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 8 with gwk] end | gw_eq | gw_eq]]
        | solve [eapply eq_ty_regall;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 8 with gwk] end | gw_eq' | gw_eq' | gw_eq']]
        | solve [eapply wf_tm_regtm;
                 [match goal with IH : _ |- _ => eapply IH; solve [eauto 8 with gwk] end | gw_eq' | gw_eq']] ].

(** The lookup-typed local substitution of [u^δ]/[U^δ]. *)
Ltac gw_entries :=
  let n := fresh "n" in let A := fresh "A" in let k := fresh "k" in let Hin := fresh "Hin" in
  intros n A k Hin;
  let A0 := fresh "A0" in let HA0 := fresh "HA0" in
  destruct (in_ctx_gren_inv _ _ _ _ _ Hin) as (A0 & HA0 & ->);
  cbn [gren GRen_lsub]; rewrite !llk_glren; change (gren_tm ?x ?y) with x⟪y⟫;
  rewrite <- gren_subst_ty;
  match goal with IH : forall n A k (_ : in_ctx _ n A k), _ |- _ => eapply (IH n A0 k HA0) end;
  eauto with gwk.

(** The letbox body, typed under [Ψ, U] with the local context shifted. *)
Ltac gw_body :=
  match goal with
  | IH : forall L'' Ψ'' (γ' : gweak), _ <= L'' -> gwk_wf γ' Ψ'' (gΨ (gext ?G ?D)) -> _,
    Hγ : gwk_wf ?γ ?Ψ' (gΨ ?G), HL : gL ?G <= ?L' |- _ =>
      let X := fresh "X" in let Hw := fresh "Hw" in
      assert (Hw : [ ⊢ mkG L' (gdecl_ren D γ :: Ψ') ])
        by (cbn [gdecl_ren gΨ gL gext]; eauto 7 with gwk);
      pose proof (IH L' _ (gwk_up γ) HL (gwkwf_up _ _ _ D Hγ) Hw) as X;
      cbn [gwk_fn] in X; rewrite gcren_shift_up in X;
      rewrite ?gren_letbox_ty in X by reflexivity; exact X
  end.

(** The recursors' motives and branches, under [⇑γ] and [⇑ⁿγ]. *)
Ltac gw_motT :=
  match goal with
  | IH : forall L'' Ψ'' (γ' : gweak), _ <= L'' -> gwk_wf γ' Ψ'' (gΨ (recGT ?G)) -> _,
    Hγ : gwk_wf ?γ ?Ψ' (gΨ ?G), HL : gL ?G <= ?L', HG : [ ⊢ mkG ?L' ?Ψ' ] |- _ =>
      let X := fresh "X" in
      pose proof (IH _ _ (gwk_up γ) (le_n_S _ _ HL) (recGT_gwk γ (mkG L' Ψ') G (conj HL Hγ)) (wf_recGT HG)) as X;
      cbn [gwk_fn] in X; rewrite recΓT_gren in X; exact X
  end.
Ltac gw_mott :=
  match goal with
  | IH : forall L'' Ψ'' (γ' : gweak), _ <= L'' -> gwk_wf γ' Ψ'' (gΨ (recGt ?G)) -> _,
    Hγ : gwk_wf ?γ ?Ψ' (gΨ ?G), HL : gL ?G <= ?L', HG : [ ⊢ mkG ?L' ?Ψ' ] |- _ =>
      let X := fresh "X" in
      pose proof (IH _ _ (gwk_up (gwk_up γ)) (le_n_S _ _ HL) (recGt_gwk γ (mkG L' Ψ') G (conj HL Hγ))
                    (wf_recGt HG)) as X;
      cbn [gwk_fn] in X; rewrite recΓt_gren in X; exact X
  end.
Ltac gw_branches :=
  let k := fresh "k" in let Hk := fresh "Hk" in intros k Hk;
  match goal with
  | IH : forall k, k < nbr -> forall L'' Ψ'' (γ' : gweak), _ <= L'' -> gwk_wf γ' Ψ'' (gΨ (brG k ?G)) -> _,
    Hγ : gwk_wf ?γ ?Ψ' (gΨ ?G), HL : gL ?G <= ?L', HG : [ ⊢ mkG ?L' ?Ψ' ] |- _ =>
      let X := fresh "X" in
      pose proof (IH k Hk _ _ (gwk_upn (br_ng k) γ) (proj1 (Nat.add_le_mono_l _ _ (br_nu k)) HL)
                    (brG_gwk k γ (mkG L' Ψ') G Hk (conj HL Hγ)) (wf_brG HG k Hk)) as X;
      rewrite ?gren_gwk_upn_ctx, ?gren_gwk_upn_tm, ?gren_gwk_upn_ty in X;
      rewrite brΓ_gren in X by exact Hk; rewrite ?brRes_gren in X by exact Hk;
      exact X
  end.

(** [UΠ]'s body, under [n] fresh levels: the same weakening at the
    universe-weakened scope. *)
Ltac gw_upi_body :=
  match goal with
  | IH : forall L'' Ψ'' (γ' : gweak), gL (gctx_uwk ?n ?G) <= L'' -> _,
    Hγ : gwk_wf ?γ ?Ψ' (gΨ ?G), HL : gL ?G <= ?L', HG : [ ⊢ mkG ?L' ?Ψ' ] |- _ =>
      let X := fresh "X" in
      pose proof (IH (n + L') _ γ (proj1 (Nat.add_le_mono_l _ _ n) HL) (gwk_wf_uren _ _ _ (ush n) Hγ)
                    (uwk_glob n _ HG)) as X;
      rewrite gren_uren_ctx in X; exact X
  end.

Ltac gw_Δ tac :=
  match goal with
  | Hin : in_gctx _ _ (gdTy ?Δ _ _), Hγ : gwk_wf ?γ _ _ |- _ => tac (Δ⟪gwk_fn γ⟫)
  | Hin : in_gctx _ _ (gdTm ?Δ _ _ _), Hγ : gwk_wf ?γ _ _ |- _ => tac (Δ⟪gwk_fn γ⟫)
  | Hin : in_gctx _ _ (gdDef ?Δ _ _ _), Hγ : gwk_wf ?γ _ _ |- _ => tac (Δ⟪gwk_fn γ⟫)
  end.

Ltac gw_manual :=
  match goal with
  (* [ind_∥∥] (M16a): its step's type, through the induction hypotheses *)
  | |- wf_tm _ _ _ (tmElimSq _ _ _ _ _ _) _ _ => eapply wf_elimSq; gw_premise
  | |- eq_tm _ _ _ (tmElimSq _ _ _ _ _ (tmSq _ _ _)) _ _ _ => eapply eqtm_elimSq_sq; gw_premise
  | |- eq_tm _ _ _ (tmElimSq _ _ _ _ _ _) _ _ _ => eapply eqtm_elimSq; gw_premise
  (* [case] (M12b): its branches' types, through the induction hypotheses *)
  | |- wf_tm _ _ _ (tmCase _ _ _ _ _ _ _ _ _) _ _ => eapply wf_case; gw_premise
  | |- eq_tm _ _ _ (tmCase _ _ _ _ _ _ _ _ (tmInl _ _ _ _ _)) _ _ _ => eapply eqtm_case_inl; gw_premise
  | |- eq_tm _ _ _ (tmCase _ _ _ _ _ _ _ _ (tmInr _ _ _ _ _)) _ _ _ => eapply eqtm_case_inr; gw_premise
  | |- eq_tm _ _ _ (tmCase _ _ _ _ _ _ _ _ _) _ _ _ => eapply eqtm_case; gw_premise
  (* [W] (M13a): the step telescope, through the induction hypotheses *)
  | |- wf_tm _ _ _ (tmSup _ _ _ _ _ _) _ _ => eapply wf_sup; gw_premise
  | |- wf_tm _ _ _ (tmElimW _ _ _ _ _ _ _ _) _ _ => eapply wf_elimW; gw_premise
  | |- eq_tm _ _ _ (tmElimW _ _ _ _ _ _ _ (tmSup _ _ _ _ _ _)) _ _ _ => eapply eqtm_elimW_sup; gw_premise
  | |- eq_tm _ _ _ (tmElimW _ _ _ _ _ _ _ _) _ _ _ => eapply eqtm_elimW; gw_premise
  | |- eq_tm _ _ _ (tmSup _ _ _ _ _ _) _ _ _ => eapply eqtm_sup; gw_premise
  | |- wf_ty _ _ _ (tyGvar _ _) _ =>
      gw_Δ ltac:(fun D => eapply wft_gvar with (Δ := D)); [ .. | gw_entries]; eauto with gwk
  | |- eq_ty _ _ _ (tyGvar _ _) _ _ =>
      gw_Δ ltac:(fun D => eapply eqty_gvar with (Δ := D));
      [ .. | gw_entries | gw_entries | gw_entries]; eauto with gwk
  | |- wf_tm _ _ _ (gvar _ _) _ _ =>
      rewrite gren_subst_ty;
      gw_Δ ltac:(fun D => eapply wf_gvar with (Δ := D)); [ .. | gw_entries]; eauto with gwk
  | |- eq_tm _ _ _ (gvar _ _) _ _ _ =>
      rewrite gren_subst_ty;
      gw_Δ ltac:(fun D => eapply eqtm_gvar with (Δ := D));
      [ .. | gw_entries | gw_entries | gw_entries]; eauto with gwk
  (* defined globals (M9) *)
  | |- wf_tm _ _ _ (gdef _ _ _) _ _ =>
      rewrite gren_subst_ty;
      gw_Δ ltac:(fun D => eapply wf_gdef with (Δ := D)); [ .. | gw_entries | ]; eauto with gwk
  | |- eq_tm _ _ _ (gdef _ _ _) (gdef _ _ _) _ _ =>
      rewrite gren_subst_ty;
      gw_Δ ltac:(fun D => eapply eqtm_gdef with (Δ := D));
      [ .. | gw_entries | gw_entries | gw_entries | ]; eauto with gwk
  | |- eq_tm _ _ _ (gdef _ _ _) _ _ _ =>
      rewrite gren_subst_ty, gren_subst;
      gw_Δ ltac:(fun D => eapply eqtm_delta with (Δ := D)); [ .. | gw_entries | ]; eauto with gwk
  | |- wf_tm _ _ _ (letboxT _ _ _ _ _ _) _ _ =>
      eapply wf_letboxT; try gw_body; gw_premise
  | |- wf_tm _ _ _ (letboxt _ _ _ _ _ _ _) _ _ =>
      eapply wf_letboxt; try gw_body; gw_premise
  | |- eq_tm _ _ _ (letboxT _ _ _ _ _ (boxT _)) _ _ _ =>
      cbn [goren]; eapply eqtm_letboxT_beta; try gw_body; gw_premise
  | |- eq_tm _ _ _ (letboxt _ _ _ _ _ _ (boxt _)) _ _ _ =>
      cbn [goren]; eapply eqtm_letboxt_beta; try gw_body; gw_premise
  | |- eq_tm _ _ _ (letboxT _ _ _ _ _ _) _ _ _ =>
      eapply eqtm_letboxT; try gw_body; gw_premise
  | |- eq_tm _ _ _ (letboxt _ _ _ _ _ _ _) _ _ _ =>
      eapply eqtm_letboxt; try gw_body; gw_premise
  | |- wf_tm _ _ _ (elimT _ _ _ _ _ _) _ _ =>
      eapply wf_elimT; [ .. | gw_motT | gw_mott | gw_branches | gw_branches | ]; gw_premise
  | |- wf_tm _ _ _ (elimt _ _ _ _ _ _ _) _ _ =>
      eapply wf_elimt; [ .. | gw_motT | gw_mott | gw_branches | gw_branches | | ]; gw_premise
  | |- eq_tm _ _ _ (elimT _ _ _ _ _ (boxT _)) _ _ _ =>
      eapply eqtm_elimT_beta; [gw_premise | now apply redT_gren | gw_premise]
  | |- eq_tm _ _ _ (elimt _ _ _ _ _ _ (boxt _)) _ _ _ =>
      eapply eqtm_elimt_beta; [gw_premise | now apply redt_gren | gw_premise]
  | |- eq_tm _ _ _ (elimT _ _ _ _ _ _) _ _ _ =>
      eapply eqtm_elimT;
      [ .. | gw_motT | gw_motT | gw_motT | gw_mott | gw_mott | gw_mott
           | gw_branches | gw_branches | gw_branches | gw_branches | ];
      gw_premise
  | |- eq_tm _ _ _ (elimt _ _ _ _ _ _ _) _ _ _ =>
      eapply eqtm_elimt;
      [ .. | gw_motT | gw_motT | gw_motT | gw_mott | gw_mott | gw_mott
           | gw_branches | gw_branches | gw_branches | gw_branches | ];
      gw_premise
  (* meta-functions (M5): bodies under the global binder, as letbox's *)
  (* the identity type (M11a): [J]'s motive context commutes by an equation *)
  (* finitary well-founded trees (M15a): the arity's instance commutes by an equation *)
  (* dependent tuples (M17a): the tail's index annotation shifts the length *)
  | |- eq_ty _ _ _ (tyDVec _ (succ _) _) (tySig _ _ _ _) _ => gren_rewrite; eapply eqty_dvec_succ; gw_premise
  (* the codes of DVec and IWf (M17c): the shifted index code commutes by an
     equation, and the decodings come before [IWf]'s and [DVec]'s congruences *)
  | |- eq_ty _ _ _ (tyIWf _ _ _ _ _ _ _ _) (tyEl _ _) _ => eapply eqty_El_iwf; gw_premise
  | |- eq_ty _ _ _ (tyDVec _ _ _) (tyEl _ _) _ => eapply eqty_El_dvec; gw_premise
  | |- wf_tm _ _ _ (tmIWf _ _ _ _ _ _ _ _) _ _ => eapply wf_code_iwf; gw_premise
  | |- eq_tm _ _ _ (tmIWf _ _ _ _ _ _ _ _) _ _ _ => eapply eqtm_code_iwf; gw_premise
  | |- eq_ty _ _ _ (tyIWi _ _ _ _ _ _ _ _ _ _) (tyEl _ _) _ => eapply eqty_El_iwi; gw_premise
  | |- wf_tm _ _ _ (tmIWi _ _ _ _ _ _ _ _ _ _) _ _ => eapply wf_code_iwi; gw_premise
  | |- eq_tm _ _ _ (tmIWi _ _ _ _ _ _ _ _ _ _) _ _ _ => eapply eqtm_code_iwi; gw_premise
  | |- wf_tm _ _ _ (tmDVec _ _ _) _ _ => eapply wf_code_dvec; gw_premise
  | |- eq_tm _ _ _ (tmDVec _ _ _) _ _ _ => eapply eqtm_code_dvec; gw_premise
  (* indexed coinductive types (M18b): the step and out types commute by equations *)
  | |- wf_ty _ _ _ (tyM _ _ _ _ _ _ _ _) _ => eapply wft_M; gw_premise
  | |- eq_ty _ _ _ (tyM _ _ _ _ _ _ _ _) _ _ => eapply eqty_M; gw_premise
  | |- wf_tm _ _ _ (tmCorec _ _ _ _ _ _ _ _ _ _ _ _) _ _ => eapply wf_corec; gw_premise
  | |- eq_tm _ _ _ (tmCorec _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ => eapply eqtm_corec; gw_premise
  | |- wf_tm _ _ _ (tmOut _ _ _ _ _ _ _ _ _) _ _ => eapply wf_out; gw_premise
  | |- eq_tm _ _ _ (tmOut _ _ _ _ _ _ _ _ (tmCorec _ _ _ _ _ _ _ _ _ _ _ _)) _ _ _ =>
      gren_rewrite; push_gren; eapply eqtm_out_corec; gw_premise
  | |- eq_tm _ _ _ (tmOut _ _ _ _ _ _ _ _ _) _ _ _ => eapply eqtm_out; gw_premise
  (* indexed finitary trees (M17b): the shifted index type commutes by an equation *)
  | |- wf_ty _ _ _ (tyIWf _ _ _ _ _ _ _ _) _ => eapply wft_iwf; gw_premise
  | |- eq_ty _ _ _ (tyIWf _ _ _ _ _ _ _ _) _ _ => eapply eqty_iwf; gw_premise
  | |- wf_tm _ _ _ (tmSupi _ _ _ _ _ _ _ _ _) _ _ => eapply wf_supi; gw_premise
  | |- eq_tm _ _ _ (tmSupi _ _ _ _ _ _ _ _ _) _ _ _ => eapply eqtm_supi; gw_premise
  | |- wf_tm _ _ _ (tmElimIWf _ _ _ _ _ _ _ _ _ _ _ _) _ _ => eapply wf_elimIWf; gw_premise
  | |- eq_tm _ _ _ (tmElimIWf _ _ _ _ _ _ _ _ _ _ _ (tmSupi _ _ _ _ _ _ _ _ _)) _ _ _ =>
      gren_rewrite; push_gren; eapply eqtm_elimIWf_supi; gw_premise
  | |- eq_tm _ _ _ (tmElimIWf _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ => eapply eqtm_elimIWf; gw_premise
  (* [IWi] (M19), as [IWf] *)
  | |- wf_ty _ _ _ (tyIWi _ _ _ _ _ _ _ _ _ _) _ => eapply wft_iwi; gw_premise
  | |- eq_ty _ _ _ (tyIWi _ _ _ _ _ _ _ _ _ _) _ _ => eapply eqty_iwi; gw_premise
  | |- wf_tm _ _ _ (tmSupii _ _ _ _ _ _ _ _ _ _ _) _ _ => eapply wf_supii; gw_premise
  | |- eq_tm _ _ _ (tmSupii _ _ _ _ _ _ _ _ _ _ _) _ _ _ => eapply eqtm_supii; gw_premise
  | |- wf_tm _ _ _ (tmElimIWi _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ => eapply wf_elimIWi; gw_premise
  | |- eq_tm _ _ _ (tmElimIWi _ _ _ _ _ _ _ _ _ _ _ _ _ (tmSupii _ _ _ _ _ _ _ _ _ _ _)) _ _ _ =>
      gren_rewrite; push_gren; eapply eqtm_elimIWi_supii; gw_premise
  | |- eq_tm _ _ _ (tmElimIWi _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ => eapply eqtm_elimIWi; gw_premise
  | |- wf_tm _ _ _ (tmSupf _ _ _ _ _) _ _ => eapply wf_supf; gw_premise
  | |- eq_tm _ _ _ (tmSupf _ _ _ _ _) _ _ _ => eapply eqtm_supf; gw_premise
  | |- wf_tm _ _ _ (tmElimWf _ _ _ _ _ _ _) _ _ => eapply wf_elimWf; gw_premise
  | |- eq_tm _ _ _ (tmElimWf _ _ _ _ _ _ (tmSupf _ _ _ _ _)) _ _ _ => eapply eqtm_elimWf_supf; gw_premise
  | |- eq_tm _ _ _ (tmElimWf _ _ _ _ _ _ _) _ _ _ => eapply eqtm_elimWf; gw_premise
  | |- wf_tm _ _ _ (tmJ _ _ _ _ _ _ _ _) _ _ => eapply wf_J; gw_premise
  | |- eq_tm _ _ _ (tmJ _ _ _ _ _ _ _ (tmRefl _ _ _)) _ _ _ => eapply eqtm_J_beta; gw_premise
  | |- eq_tm _ _ _ (tmJ _ _ _ _ _ _ _ _) _ _ _ => eapply eqtm_J; gw_premise
  | |- wf_ty _ _ _ (tyCPi _ _) _ => eapply wft_cpi; try gw_body; gw_premise
  | |- wf_ty _ _ _ (tyTPi _ _ _ _) _ => eapply wft_tpi; try gw_body; gw_premise
  | |- eq_ty _ _ _ (tyCPi _ _) _ _ => eapply eqty_cpi; try gw_body; gw_premise
  | |- eq_ty _ _ _ (tyTPi _ _ _ _) _ _ => eapply eqty_tpi; try gw_body; gw_premise
  | |- wf_tm _ _ _ (clam _ _ _) _ _ => eapply wf_clam; try gw_body; gw_premise
  | |- wf_tm _ _ _ (tlam _ _ _ _ _) _ _ => eapply wf_tlam; try gw_body; gw_premise
  | |- wf_tm _ _ _ (capp _ _) _ _ => eapply wf_capp; try gw_body; gw_premise
  | Hb : wf_ty (gext _ (gdTy _ lD ?k)) _ _ _ _ |- wf_tm _ _ _ (tapp _ _) _ _ =>
      eapply wf_tapp with (l := k); try gw_body; gw_premise
  | |- eq_tm _ _ _ (clam _ _ (capp _ _)) _ _ _ => eapply eqtm_ceta; try gw_body; gw_premise
  | |- eq_tm _ _ _ (tlam _ _ _ _ (tapp _ _)) _ _ _ => eapply eqtm_teta; try gw_body; gw_premise
  | |- eq_tm _ _ _ (clam _ _ _) _ _ _ => eapply eqtm_clam; try gw_body; gw_premise
  | |- eq_tm _ _ _ (tlam _ _ _ _ _) _ _ _ => eapply eqtm_tlam; try gw_body; gw_premise
  | |- eq_tm _ _ _ (capp (clam _ _ _) _) _ _ _ => eapply eqtm_cbeta; try gw_body; gw_premise
  | |- eq_tm _ _ _ (tapp (tlam _ _ _ _ _) _) _ _ _ => eapply eqtm_tbeta; try gw_body; gw_premise
  | |- eq_tm _ _ _ (capp _ _) _ _ _ => eapply eqtm_capp; try gw_body; gw_premise
  | Hb : wf_ty (gext _ (gdTy _ lD ?k)) _ _ _ _ |- eq_tm _ _ _ (tapp _ _) _ _ _ =>
      eapply eqtm_tapp with (l := k); try gw_body; gw_premise
  | |- wf_ty _ _ _ (tyUPi _ _ _) _ => eapply wft_upi; try gw_upi_body; gw_premise
  | |- eq_ty _ _ _ (tyUPi _ _ _) _ _ => eapply eqty_upi; try gw_upi_body; gw_premise
  | |- wf_tm _ _ _ (ulam _ _ _ _) _ _ => eapply wf_ulam; try gw_upi_body; gw_premise
  | |- eq_tm _ _ _ (ulam _ _ _ (uapp _ (ubvars _))) _ _ _ => eapply eqtm_ueta; try gw_upi_body; gw_premise
  | |- eq_tm _ _ _ (ulam _ _ _ _) _ _ _ => eapply eqtm_ulam; try gw_upi_body; gw_premise
  | |- wf_tm _ _ _ (uapp _ _) _ _ => eapply wf_uapp; try gw_upi_body; gw_premise
  | |- eq_tm _ _ _ (uapp (ulam _ _ _ _) _) _ _ _ => eapply eqtm_ubeta; try gw_upi_body; gw_premise
  | |- eq_tm _ _ _ (uapp _ _) _ _ _ => eapply eqtm_uapp; try gw_upi_body; gw_premise
  | |- eq_tm _ _ _ (boxT _) _ _ _ => eapply eqtm_boxT; gw_premise
  | |- eq_tm _ _ _ (boxt _) _ _ _ => eapply eqtm_boxt; gw_premise
  | |- wf_tm _ _ _ (natrec _ _ _ _ _) _ _ => eapply wf_natrec; gw_premise
  | |- eq_tm _ _ _ (natrec _ _ _ _ zero) _ _ _ => eapply eqtm_natrec_zero; gw_premise
  | |- eq_tm _ _ _ (natrec _ _ _ _ (succ _)) _ _ _ => eapply eqtm_natrec_succ; gw_premise
  | |- eq_tm _ _ _ (natrec _ _ _ _ _) (natrec _ _ _ _ _) _ _ => eapply eqtm_natrec; gw_premise
  | |- eq_tm _ _ _ (lam _ _ _ _) _ _ _ => eapply eqtm_eta; gw_premise
  | |- wf_tm _ _ _ (tmPair _ _ _ _ _ _) _ _ => eapply wf_pair; gw_premise
  | |- eq_tm _ _ _ (tmFst _ _ _ _ (tmPair _ _ _ _ _ _)) _ _ _ => eapply eqtm_fst_beta; gw_premise
  | |- eq_tm _ _ _ (tmSnd _ _ _ _ (tmPair _ _ _ _ _ _)) _ _ _ => eapply eqtm_snd_beta; gw_premise
  | |- eq_tm _ _ _ (tmPair _ _ _ _ _ _) (tmPair _ _ _ _ _ _) _ _ => eapply eqtm_pair; gw_premise
  | |- eq_tm _ _ _ _ _ (tyUnit _) _ => eapply eqtm_unit_eta; gw_premise
  | |- eq_ty _ lM _ _ _ _ => eapply eqty_leq; gw_premise
  | |- eq_tm _ lM _ _ _ _ _ => eapply eqtm_leq; gw_premise
  end.

Theorem gweakening :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> forall L' Ψ' (γ : gweak), gL G <= L' -> gwk_wf γ Ψ' (gΨ G) ->
     [ ⊢ mkG L' Ψ' ] -> [ mkG L' Ψ' ; Γ⟪γ⟫ ⊢[ i ] ]) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> forall L' Ψ' (γ : gweak), gL G <= L' -> gwk_wf γ Ψ' (gΨ G) ->
     [ ⊢ mkG L' Ψ' ] -> [ mkG L' Ψ' ; Γ⟪γ⟫ ⊢[ i ] T⟪γ⟫ @ l ]) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> forall L' Ψ' (γ : gweak), gL G <= L' -> gwk_wf γ Ψ' (gΨ G) ->
     [ ⊢ mkG L' Ψ' ] -> [ mkG L' Ψ' ; Γ⟪γ⟫ ⊢[ i ] t⟪γ⟫ : T⟪γ⟫ @ l ]) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> forall L' Ψ' (γ : gweak), gL G <= L' -> gwk_wf γ Ψ' (gΨ G) ->
     [ ⊢ mkG L' Ψ' ] -> [ mkG L' Ψ' ; Γ⟪γ⟫ ⊢[ i ] T⟪γ⟫ ≅ T'⟪γ⟫ @ l ]) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> forall L' Ψ' (γ : gweak), gL G <= L' -> gwk_wf γ Ψ' (gΨ G) ->
     [ ⊢ mkG L' Ψ' ] -> [ mkG L' Ψ' ; Γ⟪γ⟫ ⊢[ i ] t⟪γ⟫ ≅ t'⟪γ⟫ : T⟪γ⟫ @ l ]) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> forall L' Ψ' (γ : gweak), gL G <= L' -> gwk_wf γ Ψ' (gΨ G) ->
     [ ⊢ mkG L' Ψ' ] -> [ mkG L' Ψ' ⊢[ i ] Γ⟪γ⟫ ≅ Γ'⟪γ⟫ ]).
Proof.
  apply typing_mut; intros.
  par: (
    (try exact I; push_gren; gren_rewrite; push_gren);
    (* manual cases first: a failing [gw_step] backtracks through every rule *)
    (first [solve [gw_manual] | gw_step])).
Qed.

(** ** Named corollaries, for a weakening [γ : G' ≤ G] *)

Section Named.
Context {γ : gweak} {G' G : gctx} (Hγ : gwk_ok γ G' G) (HG' : [ ⊢ G' ]).

Ltac gwk_named k :=
  destruct G' as [L' Ψ']; destruct Hγ as [Hl Hw]; cbn in Hl, Hw;
  intros H; exact (k _ _ _ _ _ _ H _ _ _ Hl Hw HG') || exact (k _ _ _ _ _ H _ _ _ Hl Hw HG')
  || exact (k _ _ _ _ _ _ _ H _ _ _ Hl Hw HG') || exact (k _ _ _ H _ _ _ Hl Hw HG')
  || exact (k _ _ _ _ H _ _ _ Hl Hw HG').

Lemma gwk_ctx {i Γ} : [ G ; Γ ⊢[ i ] ] -> [ G' ; Γ⟪γ⟫ ⊢[ i ] ].
Proof. gwk_named (proj1 (proj2 gweakening)). Qed.
Lemma gwk_ty {i Γ T l} : [ G ; Γ ⊢[ i ] T @ l ] -> [ G' ; Γ⟪γ⟫ ⊢[ i ] T⟪γ⟫ @ l ].
Proof. gwk_named (proj1 (proj2 (proj2 gweakening))). Qed.
Lemma gwk_tm {i Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G' ; Γ⟪γ⟫ ⊢[ i ] t⟪γ⟫ : T⟪γ⟫ @ l ].
Proof. gwk_named (proj1 (proj2 (proj2 (proj2 gweakening)))). Qed.
Lemma gwk_eqty {i Γ T T' l} : [ G ; Γ ⊢[ i ] T ≅ T' @ l ] ->
  [ G' ; Γ⟪γ⟫ ⊢[ i ] T⟪γ⟫ ≅ T'⟪γ⟫ @ l ].
Proof. gwk_named (proj1 (proj2 (proj2 (proj2 (proj2 gweakening))))). Qed.
Lemma gwk_eqtm {i Γ t t' T l} : [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] ->
  [ G' ; Γ⟪γ⟫ ⊢[ i ] t⟪γ⟫ ≅ t'⟪γ⟫ : T⟪γ⟫ @ l ].
Proof. gwk_named (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 gweakening)))))). Qed.
Lemma gwk_eqctx {i Γ Γ'} : [ G ⊢[ i ] Γ ≅ Γ' ] -> [ G' ⊢[ i ] Γ⟪γ⟫ ≅ Γ'⟪γ⟫ ].
Proof. gwk_named (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 gweakening)))))). Qed.

End Named.


(** ** Local weakenings under global renaming *)

Lemma wk_wf_gren (ρ : wk) Δ Γ ξ : ρ : Δ ≤ Γ -> ρ : Δ⟪ξ⟫ ≤ Γ⟪ξ⟫.
Proof.
  induction 1; cbn [gren GRen_ctx gcren]; change (gren_ty ?A ?ξ) with A⟪ξ⟫;
    change (gcren ?A ?ξ) with A⟪ξ⟫; try rewrite gren_ren_ty'; now constructor.
Qed.

(** ** Composition of global weakenings *)

Fixpoint gwk_comp (γ' γ : gweak) : gweak :=          (* first γ, then γ' *)
  match γ', γ with
  | gwk_id, γ => γ
  | gwk_step γ', γ => gwk_step (gwk_comp γ' γ)
  | gwk_up γ', gwk_id => gwk_up γ'
  | gwk_up γ', gwk_step γ => gwk_step (gwk_comp γ' γ)
  | gwk_up γ', gwk_up γ => gwk_up (gwk_comp γ' γ)
  end.

Lemma gwk_fn_comp γ' γ n : gwk_comp γ' γ n = γ' (γ n).
Proof.
  revert γ n; induction γ' as [|γ' IH|γ' IH]; intros γ n.
  - destruct γ; reflexivity.
  - cbn. now rewrite IH.
  - destruct γ as [|γ|γ]; cbn; [reflexivity | now rewrite IH |].
    destruct n; cbn; [reflexivity | now rewrite IH].
Qed.

Lemma gwk_comp_id_r γ : gwk_comp γ gwk_id = γ.
Proof. induction γ; cbn; congruence. Qed.

Lemma gwk_comp_wf γ' γ Ψ'' Ψ' Ψ : gwk_wf γ' Ψ'' Ψ' -> gwk_wf γ Ψ' Ψ -> gwk_wf (gwk_comp γ' γ) Ψ'' Ψ.
Proof.
  intros H'; revert γ Ψ; induction H' as [Θ|γ' Ξ Θ D H' IH|γ' Ξ Θ D H' IH]; intros γ Ψ0 H.
  - destruct γ; exact H.
  - constructor; auto.
  - inversion H as [Θ0|γ0 Θ0 Ψ1 D0 H0|γ0 Θ0 Ψ1 D0 H0]; subst; cbn.
    + constructor; auto.
    + constructor; auto.
    + rewrite (gdecl_ren_comp _ _ _ (gwk_comp γ' γ0)) by (intros; apply gwk_fn_comp).
      constructor; auto.
Qed.

Lemma gwk_ok_id G : gwk_ok gwk_id G G.
Proof. split; [apply le_n | constructor]. Qed.
Lemma gwk_ok_id_inv {G' G} : gwk_ok gwk_id G' G -> G' = mkG (gL G') (gΨ G).
Proof.
  destruct G' as [L' Ψ'], G as [L Ψ]; intros [Hl Hw]; cbn in *.
  inversion Hw; subst; reflexivity.
Qed.
Lemma gwk_ok_comp {γ' γ G'' G' G} : gwk_ok γ' G'' G' -> gwk_ok γ G' G ->
  gwk_ok (gwk_comp γ' γ) G'' G.
Proof. intros [H1 H2] [H3 H4]; split; [lia | eapply gwk_comp_wf; eauto]. Qed.

(** ** The action of a global weakening

    [x⟦γ⟧] is [x⟪γ⟫], except that the identity weakening acts as the
    identity *by definition* (renaming by the identity function is the
    identity only on deep-normal syntax).  The Kripke quantification of the
    logical relation uses it, so that its purely local instances are
    literally M1's. *)

Definition gwa {X} `{GRen X} (γ : gweak) (x : X) : X :=
  match γ with gwk_id => x | _ => x⟪γ⟫ end.
Notation "x ⟦ γ ⟧" := (gwa γ x) (at level 5, format "x ⟦ γ ⟧").

Lemma gwa_gren {X} `{GRen X} (γ : gweak) (x : X) : γ <> gwk_id -> x⟦γ⟧ = x⟪γ⟫.
Proof. destruct γ; cbn; congruence. Qed.

(** Composition, for each syntactic class. *)
Lemma gwk_comp_not_id γ' γ : γ <> gwk_id -> gwk_comp γ' γ <> gwk_id.
Proof. destruct γ', γ; cbn; congruence. Qed.

Lemma gwa_comp_gen {X} `{GRen X}
  (gg : forall (x : X) ξ ζ θ, (forall i, θ i = ζ (ξ i)) -> x⟪ξ⟫⟪ζ⟫ = x⟪θ⟫)
  (x : X) γ' γ : x⟦γ⟧⟦γ'⟧ = x⟦gwk_comp γ' γ⟧.
Proof.
  destruct γ' as [|γ1|γ1]; [reflexivity|..];
    (destruct γ as [|γ2|γ2]; [now rewrite gwk_comp_id_r|..]);
    rewrite !gwa_gren by (discriminate || (apply gwk_comp_not_id; discriminate));
    apply gg; intros; apply gwk_fn_comp.
Qed.

Lemma gwa_comp_ty (T : ty) γ' γ : T⟦γ⟧⟦γ'⟧ = T⟦gwk_comp γ' γ⟧.
Proof. apply gwa_comp_gen, gren_gren_ty. Qed.
Lemma gwa_comp_tm (t : tm) γ' γ : t⟦γ⟧⟦γ'⟧ = t⟦gwk_comp γ' γ⟧.
Proof. apply gwa_comp_gen, gren_gren_tm'. Qed.
Lemma gwa_comp_ctx (Γ : ctx) γ' γ : Γ⟦γ⟧⟦γ'⟧ = Γ⟦gwk_comp γ' γ⟧.
Proof. apply gwa_comp_gen, gcren_gcren. Qed.

(** Commutation with the local operations. *)
Lemma gwa_ren_ty (T : ty) (r : rsub) γ : T⟨r⟩⟦γ⟧ = T⟦γ⟧⟨r⟩.
Proof. destruct γ; cbn [gwa]; auto using gren_ren_ty. Qed.
Lemma gwa_ren (t : tm) (r : rsub) γ : t⟨r⟩⟦γ⟧ = t⟦γ⟧⟨r⟩.
Proof. destruct γ; cbn [gwa]; auto using gren_ren. Qed.
Lemma gwa_subst_ty (T : ty) d γ : T[d]⟦γ⟧ = T⟦γ⟧[d⟦γ⟧].
Proof. destruct γ; cbn [gwa]; auto using gren_subst_ty. Qed.
Lemma gwa_subst (t : tm) d γ : t[d]⟦γ⟧ = t⟦γ⟧[d⟦γ⟧].
Proof. destruct γ; cbn [gwa]; auto using gren_subst. Qed.
Lemma gwa_lsingle (a : tm) γ : (lsingle a)⟦γ⟧ = lsingle a⟦γ⟧.
Proof. destruct γ; reflexivity. Qed.

(** Constructor equations. *)
Section PushGwa.
Variable (γ : gweak).
Lemma gwa_tyNat : tyNat⟦γ⟧ = tyNat. Proof. now destruct γ. Qed.
Lemma gwa_tyPi l l' A B : (tyPi l l' A B)⟦γ⟧ = tyPi l l' A⟦γ⟧ B⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_tyU l : (tyU l)⟦γ⟧ = tyU l. Proof. now destruct γ. Qed.
Lemma gwa_tyEl l t : (tyEl l t)⟦γ⟧ = tyEl l t⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_tyCTyp Δ l : (tyCTyp Δ l)⟦γ⟧ = tyCTyp Δ⟦γ⟧ l. Proof. now destruct γ. Qed.
Lemma gwa_tyCTrm Δ T l : (tyCTrm Δ T l)⟦γ⟧ = tyCTrm Δ⟦γ⟧ T⟦γ⟧ l. Proof. now destruct γ. Qed.
Lemma gwa_var n : (var n)⟦γ⟧ = var n. Proof. now destruct γ. Qed.
Lemma gwa_zero : zero⟦γ⟧ = zero. Proof. now destruct γ. Qed.
Lemma gwa_succ t : (succ t)⟦γ⟧ = succ t⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_tmNat : tmNat⟦γ⟧ = tmNat. Proof. now destruct γ. Qed.
Lemma gwa_tmU l : (tmU l)⟦γ⟧ = tmU l. Proof. now destruct γ. Qed.
Lemma gwa_tmPi l l' s t : (tmPi l l' s t)⟦γ⟧ = tmPi l l' s⟦γ⟧ t⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_lam l l' A t : (lam l l' A t)⟦γ⟧ = lam l l' A⟦γ⟧ t⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_app t l l' A B s : (app t l l' A B s)⟦γ⟧ = app t⟦γ⟧ l l' A⟦γ⟧ B⟦γ⟧ s⟦γ⟧.
Proof. now destruct γ. Qed.
Lemma gwa_natrec l M s z t : (natrec l M s z t)⟦γ⟧ = natrec l M⟦γ⟧ s⟦γ⟧ z⟦γ⟧ t⟦γ⟧.
Proof. now destruct γ. Qed.
Lemma gwa_cext Γ A l : (Γ ,, A @ l)⟦γ⟧ = Γ⟦γ⟧ ,, A⟦γ⟧ @ l. Proof. now destruct γ. Qed.
Lemma gwa_cnil : cnil⟦γ⟧ = cnil. Proof. now destruct γ. Qed.
Lemma gwa_cvar g : (cvar g)⟦γ⟧ = cvar (γ g). Proof. now destruct γ. Qed.
Lemma gwa_tySig l l' A B : (tySig l l' A B)⟦γ⟧ = tySig l l' A⟦γ⟧ B⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_tySum l l' A B : (tySum l l' A B)⟦γ⟧ = tySum l l' A⟦γ⟧ B⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_tyW l l' A B : (tyW l l' A B)⟦γ⟧ = tyW l l' A⟦γ⟧ B⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_tyVec l A n : (tyVec l A n)⟦γ⟧ = tyVec l A⟦γ⟧ n⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_tyFin n : (tyFin n)⟦γ⟧ = tyFin n⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_tyWf l A N : (tyWf l A N)⟦γ⟧ = tyWf l A⟦γ⟧ N⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_supf l A N a cs : (tmSupf l A N a cs)⟦γ⟧ = tmSupf l A⟦γ⟧ N⟦γ⟧ a⟦γ⟧ cs⟦γ⟧.
Proof. now destruct γ. Qed.
Lemma gwa_elimWf l l' A N M c t :
  (tmElimWf l l' A N M c t)⟦γ⟧ = tmElimWf l l' A⟦γ⟧ N⟦γ⟧ M⟦γ⟧ c⟦γ⟧ t⟦γ⟧.
Proof. now destruct γ. Qed.
Lemma gwa_sup l l' A B a f : (tmSup l l' A B a f)⟦γ⟧ = tmSup l l' A⟦γ⟧ B⟦γ⟧ a⟦γ⟧ f⟦γ⟧.
Proof. now destruct γ. Qed.
Lemma gwa_elimW l l' l'' A B M c t :
  (tmElimW l l' l'' A B M c t)⟦γ⟧ = tmElimW l l' l'' A⟦γ⟧ B⟦γ⟧ M⟦γ⟧ c⟦γ⟧ t⟦γ⟧.
Proof. now destruct γ. Qed.
Lemma gwa_tySq l A : (tySq l A)⟦γ⟧ = tySq l A⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_tyDVec l n F : (tyDVec l n F)⟦γ⟧ = tyDVec l n⟦γ⟧ F⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_sq l A a : (tmSq l A a)⟦γ⟧ = tmSq l A⟦γ⟧ a⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_elimSq l l' A M c t :
  (tmElimSq l l' A M c t)⟦γ⟧ = tmElimSq l l' A⟦γ⟧ M⟦γ⟧ c⟦γ⟧ t⟦γ⟧.
Proof. now destruct γ. Qed.
Lemma gwa_tmSqCode l s : (tmSqCode l s)⟦γ⟧ = tmSqCode l s⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_tmDVec l n f : (tmDVec l n f)⟦γ⟧ = tmDVec l n⟦γ⟧ f⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_tmIWf l li x s n o c m :
  (tmIWf l li x s n o c m)⟦γ⟧ = tmIWf l li x⟦γ⟧ s⟦γ⟧ n⟦γ⟧ o⟦γ⟧ c⟦γ⟧ m⟦γ⟧.
Proof. now destruct γ. Qed.
Lemma gwa_tmIWi l lp li x s n d o c m :
  (tmIWi l lp li x s n d o c m)⟦γ⟧ = tmIWi l lp li x⟦γ⟧ s⟦γ⟧ n⟦γ⟧ d⟦γ⟧ o⟦γ⟧ c⟦γ⟧ m⟦γ⟧.
Proof. now destruct γ. Qed.
Lemma gwa_inl l l' A B a : (tmInl l l' A B a)⟦γ⟧ = tmInl l l' A⟦γ⟧ B⟦γ⟧ a⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_inr l l' A B a : (tmInr l l' A B a)⟦γ⟧ = tmInr l l' A⟦γ⟧ B⟦γ⟧ a⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_case l l' l'' A B M c1 c2 t :
  (tmCase l l' l'' A B M c1 c2 t)⟦γ⟧ = tmCase l l' l'' A⟦γ⟧ B⟦γ⟧ M⟦γ⟧ c1⟦γ⟧ c2⟦γ⟧ t⟦γ⟧.
Proof. now destruct γ. Qed.
Lemma gwa_tmSig l l' s t : (tmSig l l' s t)⟦γ⟧ = tmSig l l' s⟦γ⟧ t⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_pair l l' A B a b : (tmPair l l' A B a b)⟦γ⟧ = tmPair l l' A⟦γ⟧ B⟦γ⟧ a⟦γ⟧ b⟦γ⟧.
Proof. now destruct γ. Qed.
Lemma gwa_fst l l' A B p : (tmFst l l' A B p)⟦γ⟧ = tmFst l l' A⟦γ⟧ B⟦γ⟧ p⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_snd l l' A B p : (tmSnd l l' A B p)⟦γ⟧ = tmSnd l l' A⟦γ⟧ B⟦γ⟧ p⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_tyUnit l : (tyUnit l)⟦γ⟧ = tyUnit l. Proof. now destruct γ. Qed.
Lemma gwa_tmUnit l : (tmUnit l)⟦γ⟧ = tmUnit l. Proof. now destruct γ. Qed.
Lemma gwa_tmSEmpty l : (tmSEmpty l)⟦γ⟧ = tmSEmpty l. Proof. now destruct γ. Qed.
Lemma gwa_tmEmpty l : (tmEmpty l)⟦γ⟧ = tmEmpty l. Proof. now destruct γ. Qed.
Lemma gwa_tmSum l l' s t : (tmSum l l' s t)⟦γ⟧ = tmSum l l' s⟦γ⟧ t⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_tmW l l' s t : (tmW l l' s t)⟦γ⟧ = tmW l l' s⟦γ⟧ t⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_tmVec l s n : (tmVec l s n)⟦γ⟧ = tmVec l s⟦γ⟧ n⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_tmWf l s n : (tmWf l s n)⟦γ⟧ = tmWf l s⟦γ⟧ n⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_tmFin n : (tmFin n)⟦γ⟧ = tmFin n⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_triv l : (tmTriv l)⟦γ⟧ = tmTriv l. Proof. now destruct γ. Qed.
Lemma gwa_tySEq l A a b : (tySEq l A a b)⟦γ⟧ = tySEq l A⟦γ⟧ a⟦γ⟧ b⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_tySEmpty l : (tySEmpty l)⟦γ⟧ = tySEmpty l. Proof. now destruct γ. Qed.
Lemma gwa_tyEmpty l : (tyEmpty l)⟦γ⟧ = tyEmpty l. Proof. now destruct γ. Qed.
Lemma gwa_srefl l A a : (srefl l A a)⟦γ⟧ = srefl l A⟦γ⟧ a⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_elimSEmpty l l' M e : (elimSEmpty l l' M e)⟦γ⟧ = elimSEmpty l l' M⟦γ⟧ e⟦γ⟧.
Proof. now destruct γ. Qed.
Lemma gwa_elimEmpty l l' M e : (elimEmpty l l' M e)⟦γ⟧ = elimEmpty l l' M⟦γ⟧ e⟦γ⟧.
Proof. now destruct γ. Qed.
Lemma gwa_tyId l A a b : (tyId l A a b)⟦γ⟧ = tyId l A⟦γ⟧ a⟦γ⟧ b⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_refl l A a : (tmRefl l A a)⟦γ⟧ = tmRefl l A⟦γ⟧ a⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_tmId l s t u : (tmId l s t u)⟦γ⟧ = tmId l s⟦γ⟧ t⟦γ⟧ u⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_tmSEq l s t u : (tmSEq l s t u)⟦γ⟧ = tmSEq l s⟦γ⟧ t⟦γ⟧ u⟦γ⟧. Proof. now destruct γ. Qed.
Lemma gwa_J l l' A a M c u e :
  (tmJ l l' A a M c u e)⟦γ⟧ = tmJ l l' A⟦γ⟧ a⟦γ⟧ M⟦γ⟧ c⟦γ⟧ u⟦γ⟧ e⟦γ⟧.
Proof. now destruct γ. Qed.
End PushGwa.

(** [push_gwa]: generated by [tools/gen_push.py] from its lemma list. *)
Ltac push_gwa_at h k := lazymatch h with
  | @tyNat => k gwa_tyNat
  | @tyPi => k gwa_tyPi
  | @tyU => k gwa_tyU
  | @tyEl => k gwa_tyEl
  | @tyCTyp => k gwa_tyCTyp
  | @tyCTrm => k gwa_tyCTrm
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
  | @tyVec => k gwa_tyVec
  | @tyFin => k gwa_tyFin
  | @tyWf => k gwa_tyWf
  | @tmSupf => k gwa_supf
  | @tmElimWf => k gwa_elimWf
  | @tmSup => k gwa_sup
  | @tmElimW => k gwa_elimW
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
  | @tmVec => k gwa_tmVec
  | @tmWf => k gwa_tmWf
  | @tmFin => k gwa_tmFin
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
  | @tySq => k gwa_tySq
  | @tyDVec => k gwa_tyDVec
  | @tmSq => k gwa_sq
  | @tmElimSq => k gwa_elimSq
  | @tmSqCode => k gwa_tmSqCode
  | @tmDVec => k gwa_tmDVec
  | @tmIWf => k gwa_tmIWf
  | @tmIWi => k gwa_tmIWi
  end.
Ltac push_gwa := repeat match goal with
  | |- context [@gwa _ _ _ ?t] => let h := head_of t in push_gwa_at h ltac:(fun L => rewrite L)
  end.

(** Normal forms, reduction, local weakenings. *)
Lemma whne_gwa t γ : whne t -> whne t⟦γ⟧.
Proof. destruct γ; cbn [gwa]; auto using whne_gren. Qed.
Lemma whnf_gwa t γ : whnf t -> whnf t⟦γ⟧.
Proof. destruct γ; cbn [gwa]; auto using whnf_gren. Qed.
Lemma whne_ty_gwa T γ : whne_ty T -> whne_ty T⟦γ⟧.
Proof. destruct γ; cbn [gwa]; auto using whne_ty_gren. Qed.
Lemma whnf_ty_gwa T γ : whnf_ty T -> whnf_ty T⟦γ⟧.
Proof. destruct γ; cbn [gwa]; auto using whnf_ty_gren. Qed.
Lemma reds_gwa t u γ : reds t u -> reds t⟦γ⟧ u⟦γ⟧.
Proof. destruct γ; cbn [gwa]; auto using reds_gren. Qed.
Lemma reds_ty_gwa T U γ : reds_ty T U -> reds_ty T⟦γ⟧ U⟦γ⟧.
Proof. destruct γ; cbn [gwa]; auto using reds_ty_gren. Qed.
Lemma wk_wf_gwa (ρ : wk) Δ Γ γ : ρ : Δ ≤ Γ -> ρ : Δ⟦γ⟧ ≤ Γ⟦γ⟧.
Proof. destruct γ; cbn [gwa]; auto using wk_wf_gren. Qed.

(** Judgments. *)
(** The identity global renaming is the identity on deep-normal syntax. *)
Lemma gren_id_ty' (T : ty) : dnfty T -> T⟪gwk_fn gwk_id⟫ = T.
Proof. intros H; apply (proj1 gren_id_all); auto. Qed.
Lemma gren_id_tm' (t : tm) : dnftm t -> t⟪gwk_fn gwk_id⟫ = t.
Proof. intros H; apply (proj1 (proj2 gren_id_all)); auto. Qed.
Lemma gren_id_ctx' (Γ : ctx) : dnfctx Γ -> Γ⟪gwk_fn gwk_id⟫ = Γ.
Proof. intros H; apply (proj1 (proj2 (proj2 gren_id_all))); auto. Qed.

(** Level growth of a global context (M3_DESIGN.md E14). *)
Lemma wfg_grow L L' Ψ : L <= L' -> [ ⊢ mkG L Ψ ] -> [ ⊢ mkG L' Ψ ].
Proof.
  intros HL; induction Ψ as [|D Ψ IH]; intros H; [constructor|].
  inversion H; subst; pose proof (IH ltac:(assumption)) as Hg.
  - now constructor.
  - econstructor; [exact Hg | | eassumption | eapply lwf_weaken; eassumption].
    pose proof (proj1 (proj2 gweakening) _ _ _ ltac:(eassumption) L' Ψ gwk_id HL (gwkwf_id _) Hg) as X.
    rewrite gren_id_ctx' in X by (eapply wf_ctx_dnf; eassumption). exact X.
  - econstructor; [exact Hg | | eassumption | eapply lwf_weaken; eassumption].
    pose proof (proj1 (proj2 (proj2 gweakening)) _ _ _ _ _ ltac:(eassumption) L' Ψ gwk_id HL (gwkwf_id _) Hg) as X.
    rewrite gren_id_ctx', gren_id_ty' in X by first [eapply wf_ty_dnf_ctx; eassumption | eapply wf_ty_dnf; eassumption].
    exact X.
  - (* a definition (M9): its type and its body *)
    econstructor; [exact Hg | | eapply lwf_weaken; eassumption | ].
    + pose proof (proj1 (proj2 (proj2 gweakening)) _ _ _ _ _ ltac:(eassumption) L' Ψ gwk_id HL (gwkwf_id _) Hg) as X.
      rewrite gren_id_ctx', gren_id_ty' in X by first [eapply wf_ty_dnf_ctx; eassumption | eapply wf_ty_dnf; eassumption].
      exact X.
    + match goal with Ht : wf_tm _ _ _ _ _ _ |- _ =>
        pose proof (proj1 (proj2 (proj2 (proj2 gweakening))) _ _ _ _ _ _ Ht L' Ψ gwk_id HL (gwkwf_id _) Hg) as X end.
      rewrite gren_id_ctx', gren_id_ty', gren_id_tm' in X
        by first [eapply wf_ty_dnf_ctx; eassumption | eapply wf_ty_dnf; eassumption | eapply wf_tm_dnf; eassumption].
      exact X.
Qed.

Ltac dnf_of H :=
  first [ exact (wf_ctx_dnf H) | exact (wf_ty_dnf H) | exact (wf_ty_dnf_ctx H) | exact (wf_tm_dnf H)
        | exact (wf_tm_dnf_ty H) | exact (wf_tm_dnf_ctx H) | exact (proj1 (eqty_dnf H))
        | exact (proj2 (eqty_dnf H)) | exact (eqty_dnf_ctx H) | exact (proj1 (eqtm_dnf H))
        | exact (proj1 (proj2 (eqtm_dnf H))) | exact (proj2 (proj2 (eqtm_dnf H))) | exact (eqtm_dnf_ctx H)
        | exact (proj1 (eqctx_dnf H)) | exact (proj2 (eqctx_dnf H)) ].

Section NamedGwa.
Context {γ : gweak} {G' G : gctx} (Hγ : gwk_ok γ G' G) (HG' : [ ⊢ G' ]).

Ltac gwa_named k :=
  destruct γ as [|γ0|γ0] eqn:Eγ; cbn [gwa];
  [ let H := fresh "H" in let H0 := fresh "H0" in
    intros H; pose proof H as H0; apply (k _ _ _ Hγ HG') in H;
    rewrite ?gren_id_ctx', ?gren_id_ty', ?gren_id_tm' in H by dnf_of H0; exact H
  | rewrite <- Eγ in *; apply (k _ _ _ Hγ HG') .. ].

Lemma gwa_ctx {i Γ} : [ G ; Γ ⊢[ i ] ] -> [ G' ; Γ⟦γ⟧ ⊢[ i ] ].
Proof. gwa_named @gwk_ctx. Qed.
Lemma gwa_ty {i Γ T l} : [ G ; Γ ⊢[ i ] T @ l ] -> [ G' ; Γ⟦γ⟧ ⊢[ i ] T⟦γ⟧ @ l ].
Proof. gwa_named @gwk_ty. Qed.
Lemma gwa_tm {i Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G' ; Γ⟦γ⟧ ⊢[ i ] t⟦γ⟧ : T⟦γ⟧ @ l ].
Proof. gwa_named @gwk_tm. Qed.
Lemma gwa_eqty {i Γ T T' l} : [ G ; Γ ⊢[ i ] T ≅ T' @ l ] ->
  [ G' ; Γ⟦γ⟧ ⊢[ i ] T⟦γ⟧ ≅ T'⟦γ⟧ @ l ].
Proof. gwa_named @gwk_eqty. Qed.
Lemma gwa_eqtm {i Γ t t' T l} : [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] ->
  [ G' ; Γ⟦γ⟧ ⊢[ i ] t⟦γ⟧ ≅ t'⟦γ⟧ : T⟦γ⟧ @ l ].
Proof. gwa_named @gwk_eqtm. Qed.

End NamedGwa.

(** Local substitutions under [⟦γ⟧]. *)
Lemma llk_gwa (d : lsub) γ n : llk d⟦γ⟧ n = (llk d n)⟦γ⟧.
Proof. destruct γ; cbn [gwa]; auto using llk_glren. Qed.
Lemma dnf_gwa (t : tm) γ : dnftm t -> dnftm t⟦γ⟧.
Proof. destruct γ; cbn [gwa]; auto; intros; apply gren_dnf_all. Qed.
Lemma lsub_tail_gwa d Δ Γ γ : lsub_tail d Δ Γ -> lsub_tail d⟦γ⟧ Δ⟦γ⟧ Γ⟦γ⟧.
Proof. destruct γ; cbn [gwa]; auto using lsub_tail_gren. Qed.
Lemma llk_llift_gwa (d : lsub) γ n : llk (llift d)⟦γ⟧ n = llk (llift d⟦γ⟧) n.
Proof.
  rewrite llk_gwa, !llk_llift. destruct n; [now rewrite gwa_var|].
  change (ren_tm ?x ?r) with x⟨r⟩. now rewrite gwa_ren, llk_gwa.
Qed.
Lemma in_ctx_gwa Γ n T l γ : in_ctx Γ n T l -> in_ctx Γ⟦γ⟧ n T⟦γ⟧ l.
Proof. destruct γ; cbn [gwa]; auto using in_ctx_gren. Qed.
Lemma gwa_lsucc γ : lsucc⟦γ⟧ = lsucc.
Proof. now destruct γ. Qed.
Lemma gwa_lsingle2 (t q : tm) γ : (lsingle2 t q)⟦γ⟧ = lsingle2 t⟦γ⟧ q⟦γ⟧.
Proof. now destruct γ. Qed.
Lemma gwa_eqctx {γ G' G i Γ Γ'} : gwk_ok γ G' G -> [ ⊢ G' ] ->
  [ G ⊢[ i ] Γ ≅ Γ' ] -> [ G' ⊢[ i ] Γ⟦γ⟧ ≅ Γ'⟦γ⟧ ].
Proof.
  intros Hγ HG' H. destruct γ as [|γ0|γ0] eqn:Eγ; cbn [gwa];
    [ pose proof H as H0; apply (gwk_eqctx Hγ HG') in H;
      rewrite ?gren_id_ctx' in H by dnf_of H0; exact H
    | exact (gwk_eqctx Hγ HG' H) ..].
Qed.

(** Global variables and lookups under [⟦γ⟧]. *)
Lemma gwa_tyGvar γ U d : (tyGvar U d)⟦γ⟧ = tyGvar (γ U) d⟦γ⟧.
Proof. now destruct γ. Qed.
Lemma gwa_gvar γ u d : (gvar u d)⟦γ⟧ = gvar (γ u) d⟦γ⟧.
Proof. now destruct γ. Qed.
Lemma gwa_gdef γ u b d : (gdef u b d)⟦γ⟧ = gdef (γ u) b⟦γ⟧ d⟦γ⟧.
Proof. now destruct γ. Qed.
Lemma dnfl_gwa (d : lsub) γ : dnfl d -> dnfl d⟦γ⟧.
Proof. destruct γ; cbn [gwa]; auto; intros; apply gren_dnf_all. Qed.
Lemma in_ctx_gwa_inv Γ n T l γ : in_ctx Γ⟦γ⟧ n T l -> exists T0, in_ctx Γ n T0 l /\ T = T0⟦γ⟧.
Proof. destruct γ; cbn [gwa]; [eauto | apply in_ctx_gren_inv ..]. Qed.

Definition gdecl_gwa (D : gdecl) (γ : gweak) : gdecl :=
  match D with
  | gdCtx => gdCtx
  | gdTy Δ i l => gdTy Δ⟦γ⟧ i l
  | gdTm Δ i T l => gdTm Δ⟦γ⟧ i T⟦γ⟧ l
  | gdDef Δ T l t => gdDef Δ⟦γ⟧ T⟦γ⟧ l t⟦γ⟧
  end.

Lemma gwk_wf_id_eq {Ψ' Ψ} : gwk_wf gwk_id Ψ' Ψ -> Ψ' = Ψ.
Proof. intros H; inversion H; reflexivity. Qed.

Lemma in_gctx_gwa {γ G' G n D} : gwk_ok γ G' G -> in_gctx (gΨ G) n D ->
  in_gctx (gΨ G') (γ n) (gdecl_gwa D γ).
Proof.
  intros [_ Hw] Hin. destruct γ as [|γ0|γ0] eqn:Eγ.
  - rewrite (gwk_wf_id_eq Hw). destruct D; exact Hin.
  - rewrite <- Eγ in *. pose proof (in_gctx_gwk _ _ _ _ _ Hw Hin) as X. subst γ. destruct D; exact X.
  - rewrite <- Eγ in *. pose proof (in_gctx_gwk _ _ _ _ _ Hw Hin) as X. subst γ. destruct D; exact X.
Qed.
