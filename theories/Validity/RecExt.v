(** * The identity extension for the code recursors (M3_DESIGN.md E13, E14)

    The neutral recursion laws need the motives and branches generically
    related under their binders ([ElimPrem]). They come from the motives'
    and branches' validity at the identity extension of the substitutions:
    the level binders by universe weakening ([LR_uwk] and friends), the
    fresh global variables as identity images, the fresh local variables
    as neutrals at their (valid) types. *)
From DeLaM.Validity Require Export LetboxS UPermV.

Lemma gdecl_gsubst_ext D σ τ : (forall i, σ i = τ i) -> gdecl_gsubst D σ = gdecl_gsubst D τ.
Proof.
  intros H; destruct D; cbn [gdecl_gsubst]; f_equal.
  all: first [ reflexivity | exact (proj1 (proj2 (proj2 gsubst_ext_all)) _ _ _ H)
             | exact (proj1 gsubst_ext_all _ _ _ H) ].
Qed.

Lemma gsub_wf_ext {G' G σ τ} : (forall i, σ i = τ i) -> [ G' ⊢ σ : G ] -> [ G' ⊢ τ : G ].
Proof.
  intros H [Hg Hn Hv]. constructor; [exact Hg | intros i; rewrite <- H; apply Hn |].
  intros n D Hin. rewrite <- H, <- (gdecl_gsubst_ext D σ τ H). exact (Hv _ _ Hin).
Qed.


Section RecNe.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VPP : VPPerm lr_vp}.

Lemma SubRel_uwk {L Ψ Γ Δ d d'} : [ ⊢ mkG L Ψ ] -> ctx_lwf L Γ ->
  SubRel (mkG L Ψ) Γ Δ d d' -> SubRel (gctx_uwk 1 (mkG L Ψ)) Γ⟨ush 1⟩ᵤ Δ⟨ush 1⟩ᵤ (uwk d) (uwk d').
Proof.
  intros HG WΓ Hd.
  assert (Hgrow : gwk_ok gwk_id (mkG (S L) Ψ) (mkG L Ψ)) by exact (conj (le_S _ _ (le_n _)) (gwkwf_id _)).
  pose proof (wfg_grow L (S L) Ψ (le_S _ _ (le_n _)) HG) as HG'.
  assert (EG : Gp (rot L) (mkG (S L) Ψ) = gctx_uwk 1 (mkG L Ψ)).
  { unfold Gp, G_us, gctx_usubst, gctx_uwk; cbn. f_equal. exact (rot_decls L Ψ (wfg_lwf _ HG)). }
  assert (Eag : forall m, m < L -> pφ (rot L) m = pφ (ush 1) m) by exact (fun m Hm => rot_ush L m Hm).
  pose proof (SubRel_wf_l _ _ _ _ _ Hd) as Wd. pose proof (SubRel_wf_l _ _ _ _ _ (SubRel_refl_r Hd)) as Wd'.
  pose proof (lsub_wf_lwf Wd) as Ld. pose proof (lsub_wf_lwf Wd') as Ld'.
  pose proof (wf_ctx_lwf (SubRel_ctx Hd)) as WΔ.
  pose proof (SubRel_gwa Hd Hgrow HG') as X; cbn [gwa] in X.
  pose proof (SubRel_perm (G := mkG (S L) Ψ) (uperm_rot L) _ _ _ _ X) as Y.
  rewrite EG, (lwf_us_ext_ctx WΓ Eag), (lwf_us_ext_ctx WΔ Eag), <- !uren_us_ctx in Y.
  refine (SubRel_ext _ _ _ _ _ _ _ _ _ Y); intros n; cbn [usubst USubst_lsub];
    rewrite llk_ulsubst; unfold uwk; rewrite llk_ulren;
    first [ rewrite ((proj1 (proj2 lwf_us_ext_all)) _ _ _ _ (Ld n) Eag)
          | rewrite ((proj1 (proj2 lwf_us_ext_all)) _ _ _ _ (Ld' n) Eag) ];
    symmetry; apply (proj1 (proj2 uren_as_usubst_all)); reflexivity.
Qed.

Lemma SubRel_uwkn {n L Ψ Γ Δ d d'} : [ ⊢ mkG L Ψ ] -> ctx_lwf L Γ ->
  SubRel (mkG L Ψ) Γ Δ d d' -> SubRel (gctx_uwk n (mkG L Ψ)) Γ⟨ush n⟩ᵤ Δ⟨ush n⟩ᵤ (uwkn n d) (uwkn n d').
Proof.
  intros HG WΓ Hd.
  assert (Hgrow : gwk_ok gwk_id (mkG (n + L) Ψ) (mkG L Ψ)) by exact (conj (Nat.le_add_l _ _) (gwkwf_id _)).
  pose proof (wfg_grow L (n + L) Ψ (Nat.le_add_l _ _) HG) as HG'.
  assert (EG : Gp (rotn n L) (mkG (n + L) Ψ) = gctx_uwk n (mkG L Ψ)).
  { unfold Gp, G_us, gctx_usubst, gctx_uwk; cbn. f_equal. exact (rotn_decls n L Ψ (wfg_lwf _ HG)). }
  assert (Eag : forall m, m < L -> pφ (rotn n L) m = pφ (ush n) m) by exact (fun m Hm => rotn_ush n L m Hm).
  pose proof (SubRel_wf_l _ _ _ _ _ Hd) as Wd. pose proof (SubRel_wf_l _ _ _ _ _ (SubRel_refl_r Hd)) as Wd'.
  pose proof (lsub_wf_lwf Wd) as Ld. pose proof (lsub_wf_lwf Wd') as Ld'.
  pose proof (wf_ctx_lwf (SubRel_ctx Hd)) as WΔ.
  pose proof (SubRel_gwa Hd Hgrow HG') as X; cbn [gwa] in X.
  pose proof (SubRel_perm (G := mkG (n + L) Ψ) (uperm_rotn n L) _ _ _ _ X) as Y.
  rewrite EG, (lwf_us_ext_ctx WΓ Eag), (lwf_us_ext_ctx WΔ Eag), <- !uren_us_ctx in Y.
  refine (SubRel_ext _ _ _ _ _ _ _ _ _ Y); intros m; cbn [usubst USubst_lsub];
    rewrite llk_ulsubst, llk_uwkn by first [exact (proj1 (SubRel_dnf _ _ _ _ _ Hd)) | exact (proj2 (SubRel_dnf _ _ _ _ _ Hd))];
    first [ rewrite ((proj1 (proj2 lwf_us_ext_all)) _ _ _ _ (Ld m) Eag)
          | rewrite ((proj1 (proj2 lwf_us_ext_all)) _ _ _ _ (Ld' m) Eag) ];
    symmetry; apply (proj1 (proj2 uren_as_usubst_all)); reflexivity.
Qed.

End RecNe.

Section ExtRel.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM}.
Local Notation GSubRel := (GSubRel EP EM).

Lemma GRel0_ext {G' G σ σ' τ τ'} : (forall i, σ i = τ i) -> (forall i, σ' i = τ' i) ->
  GRel0 EP EM G' G σ σ' -> GRel0 EP EM G' G τ τ'.
Proof.
  intros H H' R n D Hin. rewrite <- H, <- H', <- (gdecl_gsubst_ext D σ τ H). exact (R _ _ Hin).
Qed.

Lemma GSubRel_ext {G' G σ σ' τ τ'} : (forall i, σ i = τ i) -> (forall i, σ' i = τ' i) ->
  GSubRel G' G σ σ' -> GSubRel G' G τ τ'.
Proof.
  intros H H' [HL Hl Hr R Rl Rr]. constructor; [exact HL | exact (gsub_wf_ext H Hl) | exact (gsub_wf_ext H' Hr)
    | exact (GRel0_ext H H' R) | exact (GRel0_ext H H Rl) | exact (GRel0_ext H' H' Rr)].
Qed.

End ExtRel.

(** ** Global substitutions: universe weakening, and a fresh binding *)

Definition decl_lvl (D : gdecl) : lvl := match D with gdCtx => lzero | gdTy _ _ l | gdTm _ _ _ l => l end.
Definition decl_layer_ok (D : gdecl) : Prop :=
  match D with gdCtx => True | gdTy _ i _ | gdTm _ i _ _ => lle i lD end.

Section GS.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM}.

Lemma GObjRel_uwk {L Ψ D D' o o'} : [ ⊢ mkG L Ψ ] -> lwf L (decl_lvl D) -> decl_layer_ok D ->
  gobj_wf (mkG L Ψ) o D -> gobj_wf (mkG L Ψ) o' D' -> GObjRel EP EM (mkG L Ψ) D o o' ->
  GObjRel EP EM (gctx_uwk 1 (mkG L Ψ)) (gdecl_uren D S) (gouren o S) (gouren o' S).
Proof.
  intros HG Hl Hi Ho Ho'. destruct D as [|Δ i k|Δ i A k]; destruct o, o'; cbn [GObjRel gouren gdecl_uren] in *;
    try tauto; try (intros; assumption).
  - (* contexts *)
    destruct D' as [|Δ' i' k'|Δ' i' A' k']; cbn in Ho'; try contradiction.
    intros (HP & HM). pose proof (wf_ctx_dnf Ho) as N. pose proof (wf_ctx_dnf Ho') as N'.
    pose proof (wf_ctx_lwf Ho) as W. pose proof (wf_ctx_lwf Ho') as W'.
    exact (conj (CtxRelG_uwk (E := EP) HG N N' W W' HP) (CtxRelG_uwk (E := EM) HG N N' W W' HM)).
  - (* types *)
    destruct D' as [|Δ' i' k'|Δ' i' A' k']; cbn in Ho'; try contradiction.
    intros (HE & HP & HM). cbn in Hl.
    pose proof (proj1 (proj2 (proj2 ctx_extract)) _ _ _ _ _ Ho) as HΔ.
    pose proof (wf_ctx_dnf HΔ) as N. pose proof (wf_ctx_lwf HΔ) as W.
    pose proof (wf_ty_lwf Ho) as WT. pose proof (wf_ty_lwf Ho') as WT'.
    refine (conj _ (conj (VTyG_uwk (E := EP) HG N W WT WT' Hl HP) (VTyG_uwk (E := EM) HG N W WT WT' Hl HM))).
    intros Hic. apply (proj1 leq_uren_all), HE, Hic.
  - (* terms *)
    destruct D' as [|Δ' i' k'|Δ' i' A' k']; cbn in Ho'; try contradiction.
    intros (HE & HP & HM). cbn in Hl.
    pose proof (lift_tm Ho Hi) as HoD.
    pose proof (wf_tm_ty (i := lD) eq_refl HoD) as HA.
    pose proof (proj1 (proj2 (proj2 ctx_extract)) _ _ _ _ _ HA) as HΔ.
    pose proof (wf_ctx_dnf HΔ) as N. pose proof (wf_ctx_lwf HΔ) as W. pose proof (wf_ty_lwf HA) as WA.
    pose proof (wf_tm_lwf Ho) as Wt. pose proof (wf_tm_lwf Ho') as Wt'.
    refine (conj _ (conj (VTmG_uwk (E := EP) HG N W Wt Wt' WA Hl HP) (VTmG_uwk (E := EM) HG N W Wt Wt' WA Hl HM))).
    apply (proj1 (proj2 leq_uren_all)), HE.
Qed.

Lemma GObjRel_uwkn {n L Ψ D D' o o'} : [ ⊢ mkG L Ψ ] -> lwf L (decl_lvl D) -> decl_layer_ok D ->
  gobj_wf (mkG L Ψ) o D -> gobj_wf (mkG L Ψ) o' D' -> GObjRel EP EM (mkG L Ψ) D o o' ->
  GObjRel EP EM (gctx_uwk n (mkG L Ψ)) (gdecl_uren D (ush n)) (gouren o (ush n)) (gouren o' (ush n)).
Proof.
  intros HG Hl Hi Ho Ho'. destruct D as [|Δ i k|Δ i A k]; destruct o, o'; cbn [GObjRel gouren gdecl_uren] in *;
    try tauto; try (intros; assumption).
  - (* contexts *)
    destruct D' as [|Δ' i' k'|Δ' i' A' k']; cbn in Ho'; try contradiction.
    intros (HP & HM). pose proof (wf_ctx_dnf Ho) as N. pose proof (wf_ctx_dnf Ho') as N'.
    pose proof (wf_ctx_lwf Ho) as W. pose proof (wf_ctx_lwf Ho') as W'.
    exact (conj (CtxRelG_uwkn (E := EP) HG N N' W W' HP) (CtxRelG_uwkn (E := EM) HG N N' W W' HM)).
  - (* types *)
    destruct D' as [|Δ' i' k'|Δ' i' A' k']; cbn in Ho'; try contradiction.
    intros (HE & HP & HM). cbn in Hl.
    pose proof (proj1 (proj2 (proj2 ctx_extract)) _ _ _ _ _ Ho) as HΔ.
    pose proof (wf_ctx_dnf HΔ) as N. pose proof (wf_ctx_lwf HΔ) as W.
    pose proof (wf_ty_lwf Ho) as WT. pose proof (wf_ty_lwf Ho') as WT'.
    refine (conj _ (conj (VTyG_uwkn (E := EP) HG N W WT WT' Hl HP) (VTyG_uwkn (E := EM) HG N W WT WT' Hl HM))).
    intros Hic. apply (proj1 leq_uren_all), HE, Hic.
  - (* terms *)
    destruct D' as [|Δ' i' k'|Δ' i' A' k']; cbn in Ho'; try contradiction.
    intros (HE & HP & HM). cbn in Hl.
    pose proof (lift_tm Ho Hi) as HoD.
    pose proof (wf_tm_ty (i := lD) eq_refl HoD) as HA.
    pose proof (proj1 (proj2 (proj2 ctx_extract)) _ _ _ _ _ HA) as HΔ.
    pose proof (wf_ctx_dnf HΔ) as N. pose proof (wf_ctx_lwf HΔ) as W. pose proof (wf_ty_lwf HA) as WA.
    pose proof (wf_tm_lwf Ho) as Wt. pose proof (wf_tm_lwf Ho') as Wt'.
    refine (conj _ (conj (VTmG_uwkn (E := EP) HG N W Wt Wt' WA Hl HP) (VTmG_uwkn (E := EM) HG N W Wt Wt' WA Hl HM))).
    apply (proj1 (proj2 leq_uren_all)), HE.
Qed.

End GS.

Lemma decl_lvl_ren D ξ : decl_lvl (gdecl_ren D ξ) = decl_lvl D.
Proof. now destruct D. Qed.
Lemma decl_layer_ren D ξ : decl_layer_ok (gdecl_ren D ξ) <-> decl_layer_ok D.
Proof. now destruct D. Qed.
Lemma decl_lvl_gsubst D σ : decl_lvl (gdecl_gsubst D σ) = decl_lvl D.
Proof. now destruct D. Qed.
Lemma decl_layer_gsubst D σ : decl_layer_ok (gdecl_gsubst D σ) <-> decl_layer_ok D.
Proof. now destruct D. Qed.

Lemma wfg_in {L Ψ n D} : [ ⊢ mkG L Ψ ] -> in_gctx Ψ n D -> lwf L (decl_lvl D) /\ decl_layer_ok D.
Proof.
  intros HG Hin; revert HG. induction Hin as [Ψ D | Ψ D D' n Hin IH]; intros HG;
    rewrite decl_lvl_ren, decl_layer_ren.
  - inversion HG; subst; cbn; split; auto; unfold lle; cbn;
      match goal with H : _ = _ \/ _ = _ |- _ => destruct H as [-> | ->]; cbn; lia end.
  - apply IH. inversion HG; subst; assumption.
Qed.

Section GS2.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM}.

Lemma GSubRel_uwk {G' G σ σ'} : [ ⊢ G ] -> GSubRel EP EM G' G σ σ' ->
  GSubRel EP EM (gctx_uwk 1 G') (gctx_uwk 1 G) (guwk σ) (guwk σ').
Proof.
  intros HG [HL Hl Hr H1 H2 H3]. destruct G' as [L' Ψ']. destruct G as [L Ψ].
  pose proof (gsw_glob _ _ _ Hl) as HG'. pose proof (gsw_dnf _ _ _ Hl) as Nσ. pose proof (gsw_dnf _ _ _ Hr) as Nσ'.
  assert (Fact : forall n D0, in_gctx Ψ n D0 -> forall τ, lwf L' (decl_lvl (gdecl_gsubst D0 τ)) /\
                    decl_layer_ok (gdecl_gsubst D0 τ)).
  { intros n D0 Hin τ. destruct (wfg_in HG Hin) as [Hlv Hly].
    rewrite decl_lvl_gsubst, decl_layer_gsubst. split; [exact (lwf_weaken _ _ _ HL Hlv) | exact Hly]. }
  assert (R : forall τ τ', [ mkG L' Ψ' ⊢ τ : mkG L Ψ ] -> [ mkG L' Ψ' ⊢ τ' : mkG L Ψ ] -> gdnf τ ->
            GRel0 EP EM (mkG L' Ψ') (mkG L Ψ) τ τ' ->
            GRel0 EP EM (gctx_uwk 1 (mkG L' Ψ')) (gctx_uwk 1 (mkG L Ψ)) (guwk τ) (guwk τ')).
  { intros τ τ' Hτ Hτ' Nτ Hrel n D Hin. unfold gctx_uwk in Hin; cbn [gΨ] in Hin.
    destruct (in_gctx_uren_inv _ _ _ _ Hin) as (D0 & HD0 & ->).
    change (guwk τ) with (guwkn 1 τ). rewrite (gdecl_gsubst_uren D0 1 τ Nτ).
    destruct (Fact _ _ HD0 τ) as [Hlv Hly].
    exact (GObjRel_uwk EP EM HG' Hlv Hly (gsw_var _ _ _ Hτ _ _ HD0) (gsw_var _ _ _ Hτ' _ _ HD0) (Hrel _ _ HD0)). }
  constructor.
  - cbn in HL |- *; lia.
  - exact (gsub_wf_uwkn 1 _ _ _ Hl).
  - exact (gsub_wf_uwkn 1 _ _ _ Hr).
  - exact (R _ _ Hl Hr Nσ H1).
  - exact (R _ _ Hl Hl Nσ H2).
  - exact (R _ _ Hr Hr Nσ' H3).
Qed.

Lemma GSubRel_uwkn {n G' G σ σ'} : [ ⊢ G ] -> GSubRel EP EM G' G σ σ' ->
  GSubRel EP EM (gctx_uwk n G') (gctx_uwk n G) (guwkn n σ) (guwkn n σ').
Proof.
  intros HG [HL Hl Hr H1 H2 H3]. destruct G' as [L' Ψ']. destruct G as [L Ψ].
  pose proof (gsw_glob _ _ _ Hl) as HG'. pose proof (gsw_dnf _ _ _ Hl) as Nσ. pose proof (gsw_dnf _ _ _ Hr) as Nσ'.
  assert (Fact : forall m D0, in_gctx Ψ m D0 -> forall τ, lwf L' (decl_lvl (gdecl_gsubst D0 τ)) /\
                    decl_layer_ok (gdecl_gsubst D0 τ)).
  { intros m D0 Hin τ. destruct (wfg_in HG Hin) as [Hlv Hly].
    rewrite decl_lvl_gsubst, decl_layer_gsubst. split; [exact (lwf_weaken _ _ _ HL Hlv) | exact Hly]. }
  assert (R : forall τ τ', [ mkG L' Ψ' ⊢ τ : mkG L Ψ ] -> [ mkG L' Ψ' ⊢ τ' : mkG L Ψ ] -> gdnf τ ->
            GRel0 EP EM (mkG L' Ψ') (mkG L Ψ) τ τ' ->
            GRel0 EP EM (gctx_uwk n (mkG L' Ψ')) (gctx_uwk n (mkG L Ψ)) (guwkn n τ) (guwkn n τ')).
  { intros τ τ' Hτ Hτ' Nτ Hrel m D Hin. unfold gctx_uwk in Hin; cbn [gΨ] in Hin.
    destruct (in_gctx_uren_inv _ _ _ _ Hin) as (D0 & HD0 & ->).
    rewrite (gdecl_gsubst_uren D0 n τ Nτ), !guwkn_lk by first [apply Nτ | apply (gsw_dnf _ _ _ Hτ')].
    destruct (Fact _ _ HD0 τ) as [Hlv Hly].
    exact (GObjRel_uwkn EP EM HG' Hlv Hly (gsw_var _ _ _ Hτ _ _ HD0) (gsw_var _ _ _ Hτ' _ _ HD0) (Hrel _ _ HD0)). }
  constructor.
  - cbn in HL |- *; lia.
  - exact (gsub_wf_uwkn n _ _ _ Hl).
  - exact (gsub_wf_uwkn n _ _ _ Hr).
  - exact (R _ _ Hl Hr Nσ H1).
  - exact (R _ _ Hl Hl Nσ H2).
  - exact (R _ _ Hr Hr Nσ' H3).
Qed.

(** A fresh binding, sent to itself. *)
Lemma GSubRel_gup {G' G σ σ' D} : GSubRel EP EM G' G σ σ' ->
  [ ⊢ gext G' (gdecl_gsubst D σ) ] -> gdecl_gsubst D σ' = gdecl_gsubst D σ ->
  GSubRel EP EM (gext G' (gdecl_gsubst D σ)) (gext G D) (gup σ) (gup σ').
Proof.
  intros Hσ HG ED.
  assert (Hγ : gwk_ok (gwk_step gwk_id) (gext G' (gdecl_gsubst D σ)) G')
    by (split; [reflexivity | constructor; constructor]).
  pose proof (GSubRel_wk EP EM Hσ Hγ HG) as Hs.
  assert (Hw : forall τ, gdecl_gsubst D τ = gdecl_gsubst D σ ->
             gobj_wf (gext G' (gdecl_gsubst D σ)) (GId 0) (gdecl_gsubst D (gsub_wk τ (gwk_step gwk_id)))).
  { intros τ Eτ. rewrite <- gdecl_gsubst_wk by discriminate. rewrite Eτ.
    destruct D; cbn [gdecl_gsubst gdecl_ren gobj_wf].
    - unfold gctx_var; cbn. reflexivity.
    - exists i; split; [apply lle_refl | exact (ing_here _ (gdTy _ _ _))].
    - exists i; split; [apply lle_refl | exact (ing_here _ (gdTm _ _ _ _))]. }
  refine (GSubRel_ext EP EM _ _ (GSubRel_cons EP EM (o := GId 0) Hs I (Hw _ eq_refl) (Hw _ ED) _ _)).
  - intros [|n]; reflexivity.
  - intros [|n]; reflexivity.
  - destruct D; cbn; reflexivity.
  - destruct D; cbn; reflexivity.
Qed.

End GS2.

(** ** The identity extension: fresh globals and fresh locals *)

Section Ext.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

Lemma SubRel_gwkn {G Γ Δ d d' D Ds} : SubRel G Γ Δ d d' ->
  [ ⊢ mkG (gL G) ((D :: Ds) ++ gΨ G) ] ->
  SubRel (mkG (gL G) ((D :: Ds) ++ gΨ G)) (gcren Γ (ush (length (D :: Ds))))
    (gcren Δ (ush (length (D :: Ds)))) (gwkn (length (D :: Ds)) d) (gwkn (length (D :: Ds)) d').
Proof.
  intros Hd HG. destruct (SubRel_dnf _ _ _ _ _ Hd) as [N N'].
  assert (Hγ : gwk_ok (gwk_stepn (length (D :: Ds))) (mkG (gL G) ((D :: Ds) ++ gΨ G)) G)
    by (split; [reflexivity | apply gwk_stepn_wf]).
  pose proof (SubRel_gwa Hd Hγ HG) as X.
  assert (Ec : forall C : ctx, C⟦gwk_stepn (length (D :: Ds))⟧ = gcren C (ush (length (D :: Ds)))).
  { intros C. unfold gwa, gwk_stepn; cbn [length]. rewrite Nat.iter_succ; cbn beta iota.
    apply (proj1 (proj2 (proj2 gren_ext_all))); intros; exact (gwk_stepn_fn (S (length Ds)) _). }
  rewrite !Ec in X.
  refine (SubRel_ext _ _ _ _ _ _ _ _ _ X); intros m; unfold gwa, gwk_stepn; cbn [length];
    rewrite Nat.iter_succ; cbn beta iota; cbn [gren GRen_lsub];
    rewrite llk_glren, llk_gwkn by assumption;
    apply (proj1 (proj2 gren_ext_all)); intros; exact (gwk_stepn_fn (S (length Ds)) _).
Qed.

Lemma CtxRel_cexts_pre {G} As : forall Γ Γ', CtxRel G (cexts Γ As) (cexts Γ' As) -> CtxRel G Γ Γ'.
Proof.
  induction As as [|[A l] As IH]; intros Γ Γ' H; cbn [cexts] in H; [exact H|].
  exact (CtxRel_tl (IH _ _ H)).
Qed.

Lemma SubRel_cexts {G} As : forall Γ Δ d d', SubRel G Γ Δ d d' ->
  CtxRel G (cexts Γ As) (cexts Γ As) -> Forall (fun '(_, l) => lwf (gL G) l) As ->
  SubRel G (cexts Γ As) (cexts Δ (cexts_sub As d)) (lliftn (length As) d) (lliftn (length As) d').
Proof.
  induction As as [|[A l] As IH]; intros Γ Δ d d' Hd HC HL; cbn [cexts cexts_sub length]; [exact Hd|].
  inversion HL as [|x y Hl HL']; subst.
  pose proof (CtxRel_cexts_pre As (Γ ,, A @ l) (Γ ,, A @ l) HC) as HC0. cbn [CtxRel] in HC0. destruct HC0 as (_ & _ & HA & _).
  pose proof (HA _ _ _ Hd) as [R HR]. destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (HAd & _ & _).
  pose proof (SubRel_lift Hd HA HAd Hl) as Hd1.
  unfold lliftn in *. rewrite !Nat.iter_succ_r. exact (IH _ _ _ _ Hd1 HC HL').
Qed.

End Ext.

Section ExtG.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM}.

Fixpoint closed_decls (Ds : list gdecl) : Prop :=
  match Ds with
  | nil => True
  | D :: Ds => (forall τ, gdecl_gsubst D (gupn (length Ds) τ) = D) /\ closed_decls Ds
  end.

Lemma GSubRel_gupn {G' G σ σ'} Ds : GSubRel EP EM G' G σ σ' -> closed_decls Ds ->
  [ ⊢ mkG (gL G') (Ds ++ gΨ G') ] ->
  GSubRel EP EM (mkG (gL G') (Ds ++ gΨ G')) (mkG (gL G) (Ds ++ gΨ G)) (gupn (length Ds) σ) (gupn (length Ds) σ').
Proof.
  intros Hσ. induction Ds as [|D Ds IH]; intros HC HG; cbn [length List.app].
  - destruct G' as [L' Ψ'], G as [L Ψ]; exact Hσ.
  - destruct HC as [HD HC].
    pose proof (wf_glob_cons _ _ _ HG) as HG0.
    pose proof (IH HC HG0) as X.
    pose proof (GSubRel_gup EP EM (D := D) X) as Y. unfold gext in Y; cbn [gL gΨ] in Y.
    rewrite HD in Y. specialize (Y HG). rewrite !HD in Y. exact (Y eq_refl).
Qed.

End ExtG.
