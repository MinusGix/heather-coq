(** * The relation along level permutations (M3_DESIGN.md E14)

    A permutation [π] of the level variables (with inverse [πi], fixing
    everything from [gL G] up) preserves the relation: [LR_perm]. The
    term relation is transported exactly, on deep-normal terms.

    Π's Kripke worlds of the permuted context are pulled back along [πi]
    ([kw_pull]) and worlds of the original context pushed forward along
    [π] ([kw_push]); the families of the permuted Π are "related by some
    relation of these types", which irrelevance makes exact without
    choice. The backward directions are the forward ones along [πi],
    followed by the round trips. *)
From DeLaM.Typing Require Export UPerm StaticCode.
From DeLaM.LogRel Require Export LevelInv.
From DeLaM.LogRel Require Import MAux.

Definition Gp (π : nat -> nat) (G : gctx) : gctx := G_us G (gL G) (pφ π).


Lemma lmeasure_perm π l : lmeasure (lvsubst l (pφ π)) = lmeasure l.
Proof. unfold lmeasure; induction l; cbn; auto. Qed.

(** The parameters of the [□] cases along permutations. *)
Class VPPerm (vp : VParam) := {
  vpp_ctx {π πi G Δ Δ'} : uperm π πi (gL G) -> [ ⊢ G ] ->
    vp_ctx vp G Δ Δ' -> vp_ctx vp (Gp π G) Δ[pφ π]ᵤ Δ'[pφ π]ᵤ ;
  vpp_ty {π πi G Δ T T' l} : uperm π πi (gL G) -> [ ⊢ G ] ->
    vp_ty vp G Δ T T' l -> vp_ty vp (Gp π G) Δ[pφ π]ᵤ T[pφ π]ᵤ T'[pφ π]ᵤ (lvsubst l (pφ π)) ;
  vpp_tyc {π πi G Δ T T' l} : uperm π πi (gL G) -> [ ⊢ G ] ->
    vp_tyc vp G Δ T T' l -> vp_tyc vp (Gp π G) Δ[pφ π]ᵤ T[pφ π]ᵤ T'[pφ π]ᵤ (lvsubst l (pφ π)) ;
  vpp_tmc {π πi G Δ A t t' l} : uperm π πi (gL G) -> [ ⊢ G ] ->
    vp_tmc vp G Δ A t t' l -> vp_tmc vp (Gp π G) Δ[pφ π]ᵤ A[pφ π]ᵤ t[pφ π]ᵤ t'[pφ π]ᵤ (lvsubst l (pφ π)) ;
  (* the meta-functions' arguments come back along the inverse (M5) *)
  vpp_ctx_dnf {G Δ Δ'} : vp_ctx vp G Δ Δ' -> dnfctx Δ /\ dnfctx Δ' ;
  vpp_ty_dnf {G Δ A A' l} : vp_ty vp G Δ A A' l -> dnfty A /\ dnfty A'
}.

#[export] Instance vp_empty_perm : VPPerm vp_empty.
Proof. constructor; cbn; tauto. Qed.
#[export] Instance LR_P_perm : VPPerm (@lr_vp LR_P) := vp_empty_perm.

Lemma Gp_rt {π πi G} : uperm π πi (gL G) -> [ ⊢ G ] -> Gp πi (Gp π G) = G.
Proof. intros Hp HG. unfold Gp. exact (rt_gctx (proj1 Hp) G HG). Qed.

Section UPermLR.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VPP : VPPerm lr_vp}.

(** ** Generic judgments along a permutation *)

Section Along.
Context {π πi : nat -> nat} {G : gctx} (Hp : uperm π πi (gL G)).
Let Hφ := uperm_usub_ok Hp.

Lemma pg_gne_ty {Γ V V' l} : [ G ; Γ ⊢ V ~ V' @ l ] ->
  [ Gp π G ; Γ[pφ π]ᵤ ⊢ V[pφ π]ᵤ ~ V'[pφ π]ᵤ @ lvsubst l (pφ π) ].
Proof using EL Hφ. exact (gne_ty_us Hφ). Qed.
Lemma pg_geq_ty {Γ T T' l} : [ G ; Γ ⊢ T ≈ T' @ l ] ->
  [ Gp π G ; Γ[pφ π]ᵤ ⊢ T[pφ π]ᵤ ≈ T'[pφ π]ᵤ @ lvsubst l (pφ π) ].
Proof using EL Hφ. exact (geq_ty_us Hφ). Qed.
Lemma pg_gne_tm {Γ t t' T l} : [ G ; Γ ⊢ t ~ t' : T @ l ] ->
  [ Gp π G ; Γ[pφ π]ᵤ ⊢ t[pφ π]ᵤ ~ t'[pφ π]ᵤ : T[pφ π]ᵤ @ lvsubst l (pφ π) ].
Proof using EL Hφ. exact (gne_tm_us Hφ). Qed.
Lemma pg_geq_tm {Γ t t' T l} : [ G ; Γ ⊢ t ≈ t' : T @ l ] ->
  [ Gp π G ; Γ[pφ π]ᵤ ⊢ t[pφ π]ᵤ ≈ t'[pφ π]ᵤ : T[pφ π]ᵤ @ lvsubst l (pφ π) ].
Proof using EL Hφ. exact (geq_tm_us Hφ). Qed.
Lemma pg_ty {Γ T l} : [ G ; Γ ⊢g T @ l ] -> [ Gp π G ; Γ[pφ π]ᵤ ⊢g T[pφ π]ᵤ @ lvsubst l (pφ π) ].
Proof using Hp. exact (p_ty Hp). Qed.
Lemma pg_tm {Γ t T l} : [ G ; Γ ⊢g t : T @ l ] ->
  [ Gp π G ; Γ[pφ π]ᵤ ⊢g t[pφ π]ᵤ : T[pφ π]ᵤ @ lvsubst l (pφ π) ].
Proof using Hp. exact (p_tm Hp). Qed.
Lemma pg_eqty {Γ T T' l} : [ G ; Γ ⊢g T ≅ T' @ l ] ->
  [ Gp π G ; Γ[pφ π]ᵤ ⊢g T[pφ π]ᵤ ≅ T'[pφ π]ᵤ @ lvsubst l (pφ π) ].
Proof using Hp. exact (p_eqty Hp). Qed.
Lemma pg_ctx {Γ} : [ G ; Γ ⊢g ] -> [ Gp π G ; Γ[pφ π]ᵤ ⊢g ].
Proof using Hp. exact (p_ctx Hp). Qed.
Lemma pg_tyred {Γ T W l} : [ G ; Γ ⊢g T ⤳* W @ l ] ->
  [ Gp π G ; Γ[pφ π]ᵤ ⊢g T[pφ π]ᵤ ⤳* W[pφ π]ᵤ @ lvsubst l (pφ π) ].
Proof using Hp. intros []; split; [exact (p_ty Hp ltac:(eassumption)) | now apply reds_ty_usubst | exact (p_eqty Hp ltac:(eassumption))]. Qed.
Lemma pg_tmred {Γ t w T l} : [ G ; Γ ⊢g t ⤳* w : T @ l ] ->
  [ Gp π G ; Γ[pφ π]ᵤ ⊢g t[pφ π]ᵤ ⤳* w[pφ π]ᵤ : T[pφ π]ᵤ @ lvsubst l (pφ π) ].
Proof using Hp. intros []; split; [exact (p_tm Hp ltac:(eassumption)) | now apply reds_usubst | exact (p_eqtm Hp ltac:(eassumption))]. Qed.
Lemma pg_lequiv {l l'} : lequiv (gL G) l l' -> lequiv (gL (Gp π G)) (lvsubst l (pφ π)) (lvsubst l' (pφ π)).
Proof using Hp. exact (p_lequiv Hp). Qed.
Lemma pg_lwf {l} : lwf (gL G) l -> lwf (gL (Gp π G)) (lvsubst l (pφ π)).
Proof using Hp. exact (p_lwf Hp). Qed.

(** The shared type-level data of a binder former, permuted; [F]
    commutes with universe substitution as [Π] and [Σ] do. *)
Lemma poly_pg {F Γ T T' l l1 l2 l3 l4 A B A' B'} :
  (forall k k' C D φ, (F k k' C D)[φ]ᵤ = F (lvsubst k φ) (lvsubst k' φ) C[φ]ᵤ D[φ]ᵤ) ->
  PolyFacts G Γ F T T' l l1 l2 l3 l4 A B A' B' ->
  PolyFacts (Gp π G) Γ[pφ π]ᵤ F T[pφ π]ᵤ T'[pφ π]ᵤ (lvsubst l (pφ π))
    (lvsubst l1 (pφ π)) (lvsubst l2 (pφ π)) (lvsubst l3 (pφ π)) (lvsubst l4 (pφ π))
    A[pφ π]ᵤ B[pφ π]ᵤ A'[pφ π]ᵤ B'[pφ π]ᵤ.
Proof using EL Hφ.
  intros HF [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB].
  pose proof (pg_tyred HT) as X. pose proof (pg_tyred HT') as X'. rewrite HF in X, X'.
  split.
  - exact (pg_lequiv Hl).
  - exact (pg_lequiv Hl3).
  - exact (pg_lequiv Hl4).
  - exact (pg_lwf Hw1).
  - exact (pg_lwf Hw2).
  - exact X.
  - exact X'.
  - exact (pg_ty HA).
  - exact (pg_ty HA').
  - exact (pg_ty HB).
  - exact (pg_ty HB').
  - exact (pg_geq_ty HAA).
  - exact (pg_geq_ty HBB).
Qed.

End Along.

Lemma kty_us {G0 Γ0} (ρ : kwk G0 Γ0) T φ : (kty ρ T)[φ]ᵤ = T[φ]ᵤ⟦kw_γ ρ⟧⟨kw_r ρ⟩.
Proof using . unfold kty. now rewrite usubst_ren_ty, usubst_gwa_ty. Qed.
Lemma ktyl_us {G0 Γ0} (ρ : kwk G0 Γ0) T φ : (ktyl ρ T)[φ]ᵤ = T[φ]ᵤ⟦kw_γ ρ⟧⟨rlift (kw_r ρ)⟩.
Proof using . unfold ktyl. now rewrite usubst_ren_ty, usubst_gwa_ty. Qed.
Lemma ktm_us {G0 Γ0} (ρ : kwk G0 Γ0) t φ : (ktm ρ t)[φ]ᵤ = t[φ]ᵤ⟦kw_γ ρ⟧⟨kw_r ρ⟩.
Proof using . unfold ktm. now rewrite usubst_ren, usubst_gwa_tm. Qed.
Lemma ktml_us {G0 Γ0} (ρ : kwk G0 Γ0) t φ : (ktml ρ t)[φ]ᵤ = t[φ]ᵤ⟦kw_γ ρ⟧⟨rlift (kw_r ρ)⟩.
Proof using . unfold ktml. now rewrite usubst_ren, usubst_gwa_tm. Qed.

(** ** Kripke worlds *)

Section Push.
Context {π πi : nat -> nat} {G : gctx} {Γ : ctx} (Hp : uperm π πi (gL G)) (ρ : kwk G Γ).

Lemma kw_push_gok : gwk_ok (kw_γ ρ) (Gp π (kw_G ρ)) (Gp π G).
Proof using . split; [exact (kw_gL ρ) | exact (gwk_wf_usubst _ _ _ _ (proj2 (kw_gok ρ)))]. Qed.
Lemma kw_push_wf : kw_r ρ : (kw_Δ ρ)[pφ π]ᵤ ≤ (Γ[pφ π]ᵤ)⟦kw_γ ρ⟧.
Proof using . rewrite <- usubst_gwa_ctx. apply wk_wf_usubst, kw_wf. Qed.
Lemma kw_push_ctx : [ Gp π (kw_G ρ) ; (kw_Δ ρ)[pφ π]ᵤ ⊢g ].
Proof using Hp. exact (pg_ctx (uperm_grow _ _ _ _ (kw_gL ρ) Hp) (kw_ctx ρ)). Qed.

Definition kw_push : kwk (Gp π G) (Γ[pφ π]ᵤ) :=
  mkKwk (Gp π (kw_G ρ)) ((kw_Δ ρ)[pφ π]ᵤ) (kw_γ ρ) (kw_r ρ) kw_push_gok kw_push_wf kw_push_ctx.

Lemma kty_push T : kty kw_push T[pφ π]ᵤ = (kty ρ T)[pφ π]ᵤ.
Proof using . unfold kty; cbn. now rewrite usubst_ren_ty, usubst_gwa_ty. Qed.
Lemma ktm_push t : ktm kw_push t[pφ π]ᵤ = (ktm ρ t)[pφ π]ᵤ.
Proof using . unfold ktm; cbn. now rewrite usubst_ren, usubst_gwa_tm. Qed.
Lemma ktyl_push T : ktyl kw_push T[pφ π]ᵤ = (ktyl ρ T)[pφ π]ᵤ.
Proof using . unfold ktyl; cbn. now rewrite usubst_ren_ty, usubst_gwa_ty. Qed.
Lemma kbody_push T : kbody kw_push T[pφ π]ᵤ = (kbody ρ T)[pφ π]ᵤ.
Proof using . unfold kbody; cbn. now rewrite usubst_ren_ty, usubst_gwa_ty. Qed.

Let Hpρ : uperm π πi (gL (kw_G ρ)) := uperm_grow _ _ _ _ (kw_gL ρ) Hp.

Lemma push_geq_kty {X Y l} : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ X ≈ Y @ l ] ->
  [ kw_G kw_push ; kw_Δ kw_push ⊢ kty kw_push X[pφ π]ᵤ ≈ Y[pφ π]ᵤ @ lvsubst l (pφ π) ].
Proof using EL. intros H. pose proof (pg_geq_ty Hpρ H) as Z. rewrite <- kty_push in Z. exact Z. Qed.
Lemma push_geq_ktyl {C X Y lc l} : [ kw_G ρ ; kw_Δ ρ ,, kty ρ C @ lc ⊢ ktyl ρ X ≈ Y @ l ] ->
  [ kw_G kw_push ; kw_Δ kw_push ,, kty kw_push C[pφ π]ᵤ @ lvsubst lc (pφ π)
      ⊢ ktyl kw_push X[pφ π]ᵤ ≈ Y[pφ π]ᵤ @ lvsubst l (pφ π) ].
Proof using EL.
  intros H. pose proof (pg_geq_ty Hpρ H) as Z.
  change ((kw_Δ ρ ,, kty ρ C @ lc)[pφ π]ᵤ) with ((kw_Δ ρ)[pφ π]ᵤ ,, (kty ρ C)[pφ π]ᵤ @ lvsubst lc (pφ π)) in Z.
  rewrite <- kty_push, <- ktyl_push in Z. exact Z.
Qed.

End Push.

Section Pull.
Context {π πi : nat -> nat} {G : gctx} {Γ : ctx} (Hp : uperm π πi (gL G)) (HG : [ ⊢ G ]) (HΓ : dnfctx Γ)
  (ρ' : kwk (Gp π G) (Γ[pφ π]ᵤ)).
Let Hi := proj1 Hp.
Let Hpi : uperm πi π (gL (kw_G ρ')) := uperm_grow _ _ _ _ (kw_gL ρ') (uperm_inv _ _ _ Hp).

Lemma kw_pull_gok : gwk_ok (kw_γ ρ') (Gp πi (kw_G ρ')) G.
Proof using HG Hi.
  split; [exact (kw_gL ρ') |].
  pose proof (gwk_wf_usubst _ _ _ (pφ πi) (proj2 (kw_gok ρ'))) as X.
  unfold Gp, G_us, gctx_usubst in X |- *; cbn [gΨ] in X |- *.
  now rewrite (rt_gdecls Hi _ (wfg_dnf _ HG)) in X.
Qed.
Lemma kw_pull_wf : kw_r ρ' : (kw_Δ ρ')[pφ πi]ᵤ ≤ Γ⟦kw_γ ρ'⟧.
Proof using Hi HΓ.
  pose proof (wk_wf_usubst _ _ _ (pφ πi) (kw_wf ρ')) as X.
  rewrite usubst_gwa_ctx, (rt_ctx Hi _ HΓ) in X. exact X.
Qed.
Lemma kw_pull_ctx : [ Gp πi (kw_G ρ') ; (kw_Δ ρ')[pφ πi]ᵤ ⊢g ].
Proof using Hpi. exact (pg_ctx Hpi (kw_ctx ρ')). Qed.

Definition kw_pull : kwk G Γ :=
  mkKwk (Gp πi (kw_G ρ')) ((kw_Δ ρ')[pφ πi]ᵤ) (kw_γ ρ') (kw_r ρ') kw_pull_gok kw_pull_wf kw_pull_ctx.

Lemma pull_G : Gp π (kw_G kw_pull) = kw_G ρ'.
Proof using . unfold Gp; cbn. exact (rt_gctx (proj1 (proj2 Hp)) _ (kw_glob ρ')). Qed.
Lemma pull_Δ : (kw_Δ kw_pull)[pφ π]ᵤ = kw_Δ ρ'.
Proof using . cbn. exact (rt_ctx (proj1 (proj2 Hp)) _ (wf_ctx_dnf (kw_ctx ρ'))). Qed.
Lemma kty_pull T : (kty kw_pull T)[pφ π]ᵤ = kty ρ' T[pφ π]ᵤ.
Proof using . unfold kty; cbn. now rewrite usubst_ren_ty, usubst_gwa_ty. Qed.
Lemma ktyl_pull T : (ktyl kw_pull T)[pφ π]ᵤ = ktyl ρ' T[pφ π]ᵤ.
Proof using . unfold ktyl; cbn. now rewrite usubst_ren_ty, usubst_gwa_ty. Qed.
Lemma ktm_pull t : (ktm kw_pull t)[pφ π]ᵤ = ktm ρ' t[pφ π]ᵤ.
Proof using . unfold ktm; cbn. now rewrite usubst_ren, usubst_gwa_tm. Qed.
Lemma ktml_pull t : (ktml kw_pull t)[pφ π]ᵤ = ktml ρ' t[pφ π]ᵤ.
Proof using . unfold ktml; cbn. now rewrite usubst_ren, usubst_gwa_tm. Qed.
Lemma kbody_pull T : (kbody kw_pull T)[pφ π]ᵤ = kbody ρ' T[pφ π]ᵤ.
Proof using . unfold kbody; cbn. now rewrite usubst_ren_ty, usubst_gwa_ty. Qed.
Lemma pull_gL : gL (kw_G kw_pull) = gL (kw_G ρ').
Proof using . reflexivity. Qed.

Lemma pull_geq_kty {X Y l} : dnfty X -> [ kw_G ρ' ; kw_Δ ρ' ⊢ kty ρ' X[pφ π]ᵤ ≈ Y @ l ] ->
  [ kw_G kw_pull ; kw_Δ kw_pull ⊢ kty kw_pull X ≈ Y[pφ πi]ᵤ @ lvsubst l (pφ πi) ].
Proof using EL.
  intros NX H. pose proof (pg_geq_ty Hpi H) as Z. rewrite kty_us, (rt_ty Hi _ NX) in Z. exact Z.
Qed.
Lemma pull_geq_ktyl {C X Y lc l} : dnfty C -> dnfty X ->
  [ kw_G ρ' ; kw_Δ ρ' ,, kty ρ' C[pφ π]ᵤ @ lc ⊢ ktyl ρ' X[pφ π]ᵤ ≈ Y @ l ] ->
  [ kw_G kw_pull ; kw_Δ kw_pull ,, kty kw_pull C @ lvsubst lc (pφ πi) ⊢ ktyl kw_pull X ≈ Y[pφ πi]ᵤ @ lvsubst l (pφ πi) ].
Proof using EL.
  intros NC NX H. pose proof (pg_geq_ty Hpi H) as Z.
  change ((kw_Δ ρ' ,, kty ρ' C[pφ π]ᵤ @ lc)[pφ πi]ᵤ)
    with ((kw_Δ ρ')[pφ πi]ᵤ ,, (kty ρ' C[pφ π]ᵤ)[pφ πi]ᵤ @ lvsubst lc (pφ πi)) in Z.
  rewrite kty_us, ktyl_us, (rt_ty Hi _ NC), (rt_ty Hi _ NX) in Z. exact Z.
Qed.

End Pull.

(** ** Term relations along a permutation *)

Section Rel.
Context {π πi : nat -> nat} {G : gctx} {Γ : ctx} (Hp : uperm π πi (gL G)) (HG : [ ⊢ G ]).

Lemma NatRel_perm : forall t t', NatRel G Γ t t' -> NatRel (Gp π G) Γ[pφ π]ᵤ t[pφ π]ᵤ t'[pφ π]ᵤ.
Proof using EL Hp.
  apply (NatRel_mut G Γ (fun t t' _ => NatRel (Gp π G) Γ[pφ π]ᵤ t[pφ π]ᵤ t'[pφ π]ᵤ)
                        (fun t t' _ => NatNf (Gp π G) Γ[pφ π]ᵤ t[pφ π]ᵤ t'[pφ π]ᵤ)).
  - intros t t' w w' Hw Hw' Heq _ IH.
    econstructor; [exact (pg_tmred Hp Hw) | exact (pg_tmred Hp Hw') | exact (pg_geq_tm Hp Heq) | exact IH].
  - cbn; constructor.
  - intros; cbn; now constructor.
  - intros ν ν' H; constructor. exact (pg_gne_tm Hp H).
Qed.

Lemma NeRel_perm V V' l t t' : NeRel G Γ V V' l t t' ->
  NeRel (Gp π G) Γ[pφ π]ᵤ V[pφ π]ᵤ V'[pφ π]ᵤ (lvsubst l (pφ π)) t[pφ π]ᵤ t'[pφ π]ᵤ.
Proof using EL Hp.
  intros (ν & ν' & H1 & H2 & H3 & H4). exists ν[pφ π]ᵤ, ν'[pφ π]ᵤ.
  exact (conj (pg_tmred Hp H1) (conj (pg_tmred Hp H2) (conj (pg_gne_tm Hp H3) (pg_gne_tm Hp H4)))).
Qed.

(** The identity type (M11a): along a permutation of its carrier's relation. *)
Lemma IdRel_perm {l1 A a b RA RA'} :
  (forall x y, RA x y -> RA' x[pφ π]ᵤ y[pφ π]ᵤ) -> forall t t', IdRel G Γ l1 A a b RA t t' ->
  IdRel (Gp π G) Γ[pφ π]ᵤ (lvsubst l1 (pφ π)) A[pφ π]ᵤ a[pφ π]ᵤ b[pφ π]ᵤ RA' t[pφ π]ᵤ t'[pφ π]ᵤ.
Proof using EL Hp.
  intros Ep t t' (w & w' & H1 & H2 & H3 & Hn). exists w[pφ π]ᵤ, w'[pφ π]ᵤ.
  refine (conj (pg_tmred Hp H1) (conj (pg_tmred Hp H2) (conj (pg_geq_tm Hp H3) _))).
  destruct Hn as [k k' C C' c c' Hk Hk' HC HC' R1 R2 R3 R4 | ν ν' Hν]; cbn.
  - apply idnf_refl; auto.
    + exact (pg_lequiv Hp Hk).
    + exact (pg_lequiv Hp Hk').
    + exact (pg_geq_ty Hp HC).
    + exact (pg_geq_ty Hp HC').
  - apply idnf_ne. exact (pg_gne_tm Hp Hν).
Qed.

(** Binary sums (M12b): along permutations of both summands' relations. *)
Lemma SumRel_perm {l1 l2 A B RA RB RA' RB'} :
  (forall x y, RA x y -> RA' x[pφ π]ᵤ y[pφ π]ᵤ) -> (forall x y, RB x y -> RB' x[pφ π]ᵤ y[pφ π]ᵤ) ->
  forall t t', SumRel G Γ l1 l2 A B RA RB t t' ->
  SumRel (Gp π G) Γ[pφ π]ᵤ (lvsubst l1 (pφ π)) (lvsubst l2 (pφ π)) A[pφ π]ᵤ B[pφ π]ᵤ RA' RB'
    t[pφ π]ᵤ t'[pφ π]ᵤ.
Proof using EL Hp.
  intros EpA EpB t t' (w & w' & H1 & H2 & H3 & Hn). exists w[pφ π]ᵤ, w'[pφ π]ᵤ.
  refine (conj (pg_tmred Hp H1) (conj (pg_tmred Hp H2) (conj (pg_geq_tm Hp H3) _))).
  destruct Hn as [k1 k2 k1' k2' C D C' D' a a' Hk1 Hk2 Hk1' Hk2' HC HC' HD HD' Ha
                 | k1 k2 k1' k2' C D C' D' a a' Hk1 Hk2 Hk1' Hk2' HC HC' HD HD' Ha | ν ν' Hν]; cbn.
  - apply sumnf_inl;
      [ exact (pg_lequiv Hp Hk1) | exact (pg_lequiv Hp Hk2) | exact (pg_lequiv Hp Hk1') | exact (pg_lequiv Hp Hk2')
      | exact (pg_geq_ty Hp HC) | exact (pg_geq_ty Hp HC') | exact (pg_geq_ty Hp HD) | exact (pg_geq_ty Hp HD')
      | exact (EpA _ _ Ha) ].
  - apply sumnf_inr;
      [ exact (pg_lequiv Hp Hk1) | exact (pg_lequiv Hp Hk2) | exact (pg_lequiv Hp Hk1') | exact (pg_lequiv Hp Hk2')
      | exact (pg_geq_ty Hp HC) | exact (pg_geq_ty Hp HC') | exact (pg_geq_ty Hp HD) | exact (pg_geq_ty Hp HD')
      | exact (EpB _ _ Ha) ].
  - apply sumnf_ne. exact (pg_gne_tm Hp Hν).
Qed.

(** Propositional truncation (M16a): along a permutation of its carrier's
    relation, each side alone. *)
Lemma SqRel_perm {l1 A RA RA'} :
  (forall x y, RA x y -> RA' x[pφ π]ᵤ y[pφ π]ᵤ) -> forall t t', SqRel G Γ l1 A RA t t' ->
  SqRel (Gp π G) Γ[pφ π]ᵤ (lvsubst l1 (pφ π)) A[pφ π]ᵤ RA' t[pφ π]ᵤ t'[pφ π]ᵤ.
Proof using EL Hp.
  intros Ep.
  assert (U : forall t, SqU G Γ l1 A RA t ->
                SqU (Gp π G) Γ[pφ π]ᵤ (lvsubst l1 (pφ π)) A[pφ π]ᵤ RA' t[pφ π]ᵤ).
  { intros t (w & H1 & Hn). exists w[pφ π]ᵤ. split; [exact (pg_tmred Hp H1) |].
    destruct Hn as [k C a Hk HC Ha | ν Hν]; cbn.
    - apply sqnf_sq; [exact (pg_lequiv Hp Hk) | exact (pg_geq_ty Hp HC) | exact (Ep _ _ Ha)].
    - apply sqnf_ne. exact (pg_gne_tm Hp Hν). }
  intros t t' [H H']. exact (conj (U _ H) (U _ H')).
Qed.

Lemma CTypNf_perm {Δ k w w'} : CTypNf G Γ Δ k w w' ->
  CTypNf (Gp π G) Γ[pφ π]ᵤ Δ[pφ π]ᵤ (lvsubst k (pφ π)) w[pφ π]ᵤ w'[pφ π]ᵤ.
Proof using EL HG Hp VPP.
  destruct 1 as [T1 T1' H | ν ν' H]; cbn.
  - constructor. exact (vpp_tyc Hp HG H).
  - apply ctyn_ne. exact (pg_gne_tm Hp H).
Qed.
Lemma CTrmNf_perm {Δ A k w w'} : CTrmNf G Γ Δ A k w w' ->
  CTrmNf (Gp π G) Γ[pφ π]ᵤ Δ[pφ π]ᵤ A[pφ π]ᵤ (lvsubst k (pφ π)) w[pφ π]ᵤ w'[pφ π]ᵤ.
Proof using EL HG Hp VPP.
  destruct 1 as [t1 t1' H | ν ν' H]; cbn.
  - constructor. exact (vpp_tmc Hp HG H).
  - apply ctrn_ne. exact (pg_gne_tm Hp H).
Qed.
Lemma CTypRel_perm {Δ Δ' k k' t t'} : CTypRel G Γ Δ Δ' k k' t t' ->
  CTypRel (Gp π G) Γ[pφ π]ᵤ Δ[pφ π]ᵤ Δ'[pφ π]ᵤ (lvsubst k (pφ π)) (lvsubst k' (pφ π)) t[pφ π]ᵤ t'[pφ π]ᵤ.
Proof using EL HG Hp VPP.
  intros (w & w' & H1 & H2 & H3 & H4 & H5 & H6). exists w[pφ π]ᵤ, w'[pφ π]ᵤ.
  refine (conj (pg_tmred Hp H1) (conj (pg_tmred Hp H2) (conj (pg_geq_tm Hp H3) (conj (pg_geq_tm Hp H4) _)))).
  exact (conj (CTypNf_perm H5) (CTypNf_perm H6)).
Qed.
Lemma CTrmRel_perm {Δ Δ' A A' k k' t t'} : CTrmRel G Γ Δ Δ' A A' k k' t t' ->
  CTrmRel (Gp π G) Γ[pφ π]ᵤ Δ[pφ π]ᵤ Δ'[pφ π]ᵤ A[pφ π]ᵤ A'[pφ π]ᵤ (lvsubst k (pφ π)) (lvsubst k' (pφ π))
    t[pφ π]ᵤ t'[pφ π]ᵤ.
Proof using EL HG Hp VPP.
  intros (w & w' & H1 & H2 & H3 & H4 & H5 & H6). exists w[pφ π]ᵤ, w'[pφ π]ᵤ.
  refine (conj (pg_tmred Hp H1) (conj (pg_tmred Hp H2) (conj (pg_geq_tm Hp H3) (conj (pg_geq_tm Hp H4) _)))).
  exact (conj (CTrmNf_perm H5) (CTrmNf_perm H6)).
Qed.

End Rel.

(** ** The statement *)

Definition Pperm n := forall G Γ T T' l R,
  LR n (LRbelow n) G Γ T T' l R -> forall π πi, uperm π πi (gL G) ->
  exists R', LR n (LRbelow n) (Gp π G) Γ[pφ π]ᵤ T[pφ π]ᵤ T'[pφ π]ᵤ (lvsubst l (pφ π)) R' /\
    forall t t', dnftm t -> dnftm t' -> (R t t' <-> R' t[pφ π]ᵤ t'[pφ π]ᵤ).

Lemma LR_glob {n rec G Γ T T' l R} : LR n rec G Γ T T' l R -> [ ⊢ G ] /\ dnfctx Γ /\ dnfty T /\ dnfty T'.
Proof using EL.
  intros H. destruct (escape_ty _ _ _ _ _ _ _ _ H) as (HT & HT' & _).
  pose proof (ctx_of_ty HT) as HΓ.
  exact (conj (ctx_glob _ _ _ HΓ) (conj (wf_ctx_dnf HΓ) (conj (wf_ty_dnf HT) (wf_ty_dnf HT')))).
Qed.

Lemma LR_rel_dnf {n rec G Γ T T' l R} : LR n rec G Γ T T' l R -> forall t t', R t t' -> dnftm t /\ dnftm t'.
Proof using EL.
  intros H t t' Ht. destruct (escape_tm _ _ _ _ _ _ _ _ H _ _ Ht) as (H1 & H2 & _).
  exact (conj (wf_tm_dnf H1) (wf_tm_dnf H2)).
Qed.

(** ** The universe *)

Lemma URel_perm n {π πi G Γ l1 t t'} : (forall m, m < n -> Pperm m) -> lmeasure l1 < n ->
  uperm π πi (gL G) ->
  URel (LRbelow n) G Γ l1 t t' -> URel (LRbelow n) (Gp π G) Γ[pφ π]ᵤ (lvsubst l1 (pφ π)) t[pφ π]ᵤ t'[pφ π]ᵤ.
Proof using EL.
  intros IHn Hn Hp (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & HK).
  exists w[pφ π]ᵤ, w'[pφ π]ᵤ.
  refine (conj (pg_tmred Hp Hw) (conj (pg_tmred Hp Hw') (conj (whnf_usubst _ _ Hnf)
            (conj (whnf_usubst _ _ Hnf') (conj (pg_geq_tm Hp Heq) _))))).
  intros la lb Hla Hlb.
  pose proof (uperm_inv _ _ _ Hp) as Hpi.
  assert (Hpull : forall lx, lequiv (gL (Gp π G)) lx (lvsubst l1 (pφ π)) ->
                    lequiv (gL G) (lvsubst lx (pφ πi)) l1 /\ lvsubst (lvsubst lx (pφ πi)) (pφ π) = lx).
  { intros lx Hx. split.
    - pose proof (pg_lequiv (G := Gp π G) Hpi Hx) as X. rewrite (rt_lvl (proj1 Hp)) in X. exact X.
    - exact (rt_lvl (proj1 (proj2 Hp)) lx). }
  destruct (Hpull la Hla) as [Hla0 Ea]. destruct (Hpull lb Hlb) as [Hlb0 Eb].
  destruct (HK _ _ Hla0 Hlb0) as [R0 H0].
  rewrite LRbelow_spec in H0 by exact Hn. unfold LogRel in H0.
  destruct (IHn _ Hn _ _ _ _ _ _ H0 _ _ Hp) as (R1 & H1 & _).
  cbn [usubst USubst_ty usubst_ty] in H1. change (usubst_tm ?x ?φ) with x[φ]ᵤ in H1.
  rewrite Ea, Eb in H1.
  exists R1. rewrite LRbelow_spec by (rewrite lmeasure_perm; exact Hn).
  unfold LogRel. rewrite lmeasure_perm. exact H1.
Qed.

(** ** Contextual types *)

Lemma ModRel_perm {π πi G Γ T T' l R} : uperm π πi (gL G) -> [ ⊢ G ] -> dnfctx Γ ->
  ModRel G Γ T T' l R ->
  exists R', ModRel (Gp π G) Γ[pφ π]ᵤ T[pφ π]ᵤ T'[pφ π]ᵤ (lvsubst l (pφ π)) R' /\
    forall t t', dnftm t -> dnftm t' -> (R t t' <-> R' t[pφ π]ᵤ t'[pφ π]ᵤ).
Proof using EL VPP.
  intros Hp HG HΓ. pose proof (uperm_inv _ _ _ Hp) as Hpi. pose proof (p_glob Hp HG) as HG'.
  destruct 1 as [T T' l Δ Δ' k k' R Hl Hk HT HT' HΔ Hgeq HR
                | T T' l Δ Δ' A A' k k' R Hl Hk HT HT' HΔ HA HA' Hgeq HR].
  - pose proof (wf_ty_dnf (eqty_wf_r ge_typeof (tyred_eq _ _ _ _ _ _ HT))) as ND.
    pose proof (wf_ty_dnf (eqty_wf_r ge_typeof (tyred_eq _ _ _ _ _ _ HT'))) as ND'. cbn in ND, ND'.
    exists (CTypRel (Gp π G) Γ[pφ π]ᵤ Δ[pφ π]ᵤ Δ'[pφ π]ᵤ (lvsubst k (pφ π)) (lvsubst k' (pφ π))). split.
    + eapply MRctyp; [exact (pg_lequiv Hp Hl) | exact (pg_lequiv Hp Hk) | exact (pg_tyred Hp HT)
                     | exact (pg_tyred Hp HT') | exact (vpp_ctx Hp HG HΔ) | exact (pg_geq_ty Hp Hgeq)
                     | apply releq_refl].
    + intros t t' Nt Nt'. rewrite (HR t t'). split; [apply (CTypRel_perm Hp HG)|].
      intros X. apply (CTypRel_perm (G := Gp π G) Hpi HG') in X.
      rewrite (Gp_rt Hp HG), !(rt_ctx (proj1 Hp)), !(rt_lvl (proj1 Hp)), !(rt_tm (proj1 Hp)) in X by assumption.
      exact X.
  - pose proof (wf_ty_dnf (eqty_wf_r ge_typeof (tyred_eq _ _ _ _ _ _ HT))) as ND.
    pose proof (wf_ty_dnf (eqty_wf_r ge_typeof (tyred_eq _ _ _ _ _ _ HT'))) as ND'. cbn in ND, ND'.
    exists (CTrmRel (Gp π G) Γ[pφ π]ᵤ Δ[pφ π]ᵤ Δ'[pφ π]ᵤ A[pφ π]ᵤ A'[pφ π]ᵤ (lvsubst k (pφ π)) (lvsubst k' (pφ π))).
    split.
    + eapply MRctrm; [exact (pg_lequiv Hp Hl) | exact (pg_lequiv Hp Hk) | exact (pg_tyred Hp HT)
                     | exact (pg_tyred Hp HT') | exact (vpp_ctx Hp HG HΔ) | exact (vpp_ty Hp HG HA)
                     | exact (vpp_ty Hp HG HA') | exact (pg_geq_ty Hp Hgeq) | apply releq_refl].
    + intros t t' Nt Nt'. rewrite (HR t t'). split; [apply (CTrmRel_perm Hp HG)|].
      intros X. apply (CTrmRel_perm (G := Gp π G) Hpi HG') in X.
      rewrite (Gp_rt Hp HG), !(rt_ctx (proj1 Hp)), !(rt_ty (proj1 Hp)), !(rt_lvl (proj1 Hp)),
        !(rt_tm (proj1 Hp)) in X by (first [assumption | tauto]).
      exact X.
Qed.

(** ** Syntax helpers *)

Lemma usubst_lsingle_ty' (M : ty) a φ : M[lsingle a][φ]ᵤ = M[φ]ᵤ[lsingle a[φ]ᵤ].
Proof using . exact (usubst_lsingle_ty M a φ). Qed.
Lemma usubst_gsingle_ty' (T : ty) o φ : T⦃gsingle o⦄[φ]ᵤ = T[φ]ᵤ⦃gsingle (gousubst o φ)⦄.
Proof using . exact (usubst_gsingle_ty T o φ). Qed.
Lemma dnf_capp t Δ : dnftm t -> dnfctx Δ -> dnftm (capp t Δ).
Proof using . cbn; auto. Qed.
Lemma dnf_tapp t A : dnftm t -> dnfty A -> dnftm (tapp t A).
Proof using . cbn; auto. Qed.
Lemma dnf_us_ctx (Δ : ctx) φ : dnfctx Δ[φ]ᵤ.
Proof using . apply (proj1 (proj2 (proj2 usubst_dnf_all))). Qed.

Lemma dnf_ktm {G0 Γ0} (ρ : kwk G0 Γ0) t : dnftm t -> dnftm (ktm ρ t).
Proof using . intros H; unfold ktm; apply ren_dnf, dnf_gwa, H. Qed.
Lemma dnf_us_tm (t : tm) φ : dnftm t[φ]ᵤ.
Proof using . apply (proj1 (proj2 usubst_dnf_all)). Qed.
Lemma dnf_us_ty (T : ty) φ : dnfty T[φ]ᵤ.
Proof using . apply (proj1 usubst_dnf_all). Qed.

Lemma tyred_glob {G Γ T W l} : [ G ; Γ ⊢g T ⤳* W @ l ] -> [ ⊢ G ] /\ dnfctx Γ /\ dnfty T /\ dnfty W.
Proof using .
  intros H. pose proof (tyred_wf _ _ _ _ _ _ H) as HT. pose proof (ctx_of_ty HT) as HΓ.
  pose proof (eqty_wf_r ge_typeof (tyred_eq _ _ _ _ _ _ H)) as HW.
  exact (conj (ctx_glob _ _ _ HΓ) (conj (wf_ctx_dnf HΓ) (conj (wf_ty_dnf HT) (wf_ty_dnf HW)))).
Qed.

Lemma geq_ty_dnf {G Γ T T' l} : [ G ; Γ ⊢ T ≈ T' @ l ] -> dnfty T /\ dnfty T'.
Proof using EL. intros H; exact (eqty_dnf (geq_ty_sound H)). Qed.
Lemma geq_tm_dnf {G Γ t t' T l} : [ G ; Γ ⊢ t ≈ t' : T @ l ] -> dnftm t /\ dnftm t'.
Proof using EL. intros H; destruct (eqtm_dnf (geq_tm_sound H)) as (? & ? & _); auto. Qed.

Lemma usubst_fst' la lb (A B : ty) p φ :
  (tmFst la lb A B p)[φ]ᵤ = tmFst (lvsubst la φ) (lvsubst lb φ) A[φ]ᵤ B[φ]ᵤ p[φ]ᵤ.
Proof using . reflexivity. Qed.
Lemma usubst_snd' la lb (A B : ty) p φ :
  (tmSnd la lb A B p)[φ]ᵤ = tmSnd (lvsubst la φ) (lvsubst lb φ) A[φ]ᵤ B[φ]ᵤ p[φ]ᵤ.
Proof using . reflexivity. Qed.
Lemma usubst_app' f la lb (A B : ty) a φ :
  (app f la lb A B a)[φ]ᵤ = app f[φ]ᵤ (lvsubst la φ) (lvsubst lb φ) A[φ]ᵤ B[φ]ᵤ a[φ]ᵤ.
Proof using . reflexivity. Qed.

Lemma pull_tmred {π πi G Γ t w T l} : uperm π πi (gL G) -> [ ⊢ G ] -> dnfctx Γ -> dnftm t -> dnfty T ->
  [ Gp π G ; Γ[pφ π]ᵤ ⊢g t[pφ π]ᵤ ⤳* w : T[pφ π]ᵤ @ lvsubst l (pφ π) ] ->
  [ G ; Γ ⊢g t ⤳* w[pφ πi]ᵤ : T @ l ].
Proof using .
  intros Hp HG HΓ Nt NT H. pose proof (pg_tmred (G := Gp π G) (uperm_inv _ _ _ Hp) H) as X.
  rewrite (Gp_rt Hp HG), (rt_ctx (proj1 Hp) _ HΓ), (rt_tm (proj1 Hp) _ Nt), (rt_ty (proj1 Hp) _ NT),
    (rt_lvl (proj1 Hp)) in X.
  exact X.
Qed.
Lemma pull_geq_tm {π πi G Γ w w' T l} : uperm π πi (gL G) -> [ ⊢ G ] -> dnfctx Γ -> dnfty T ->
  [ Gp π G ; Γ[pφ π]ᵤ ⊢ w ≈ w' : T[pφ π]ᵤ @ lvsubst l (pφ π) ] ->
  [ G ; Γ ⊢ w[pφ πi]ᵤ ≈ w'[pφ πi]ᵤ : T @ l ].
Proof using EL.
  intros Hp HG HΓ NT H. pose proof (pg_geq_tm (G := Gp π G) (uperm_inv _ _ _ Hp) H) as X.
  rewrite (Gp_rt Hp HG), (rt_ctx (proj1 Hp) _ HΓ), (rt_ty (proj1 Hp) _ NT), (rt_lvl (proj1 Hp)) in X.
  exact X.
Qed.

(** ** The relation along a permutation *)

(** ** Well-founded trees along a permutation (M13a)

    [WRel]'s children live at weakened worlds with the data composed, so
    the transport is by induction, with the data abstract: a world of the
    permuted context corresponds to one of the original ([kcorr]: the
    same weakenings, the contexts permuted), and the hypotheses ask the
    data to be carried along corresponding worlds. The target context is
    abstract up to an equation, as the children's is [kw_G ρ'] rather
    than a permuted one. The backward direction is the forward one along
    [πi]. *)
Definition kcorr (π : nat -> nat) {G Γ G' Γ'} (ρ : kwk G Γ) (ρ' : kwk G' Γ') : Prop :=
  Gp π (kw_G ρ) = kw_G ρ' /\ (kw_Δ ρ)[pφ π]ᵤ = kw_Δ ρ' /\ kw_γ ρ = kw_γ ρ' /\ kw_r ρ = kw_r ρ'.

Section Corr.
Context {π : nat -> nat} {G Γ G' Γ'} {ρ : kwk G Γ} {ρ' : kwk G' Γ'} (Hk : kcorr π ρ ρ').

Lemma kcorr_kty T : (kty ρ T)[pφ π]ᵤ = kty ρ' T[pφ π]ᵤ.
Proof using Hk. destruct Hk as (_ & _ & Eg & Er). rewrite kty_us. unfold kty. now rewrite Eg, Er. Qed.
Lemma kcorr_ktyl T : (ktyl ρ T)[pφ π]ᵤ = ktyl ρ' T[pφ π]ᵤ.
Proof using Hk. destruct Hk as (_ & _ & Eg & Er). rewrite ktyl_us. unfold ktyl. now rewrite Eg, Er. Qed.
Lemma kcorr_ktm t : (ktm ρ t)[pφ π]ᵤ = ktm ρ' t[pφ π]ᵤ.
Proof using Hk. destruct Hk as (_ & _ & Eg & Er). rewrite ktm_us. unfold ktm. now rewrite Eg, Er. Qed.
Lemma kcorr_ktml t : (ktml ρ t)[pφ π]ᵤ = ktml ρ' t[pφ π]ᵤ.
Proof using Hk. destruct Hk as (_ & _ & Eg & Er). rewrite ktml_us. unfold ktml. now rewrite Eg, Er. Qed.

Lemma kcorr_comp (ρ0 : kwk (kw_G ρ) (kw_Δ ρ)) (ρ0' : kwk (kw_G ρ') (kw_Δ ρ')) :
  kcorr π ρ0 ρ0' -> kcorr π (kw_comp ρ ρ0) (kw_comp ρ' ρ0').
Proof using Hk.
  destruct Hk as (_ & _ & Eg & Er). intros (E1 & E2 & Eg0 & Er0). unfold kcorr; cbn [kw_comp kw_G kw_Δ kw_γ kw_r].
  split; [exact E1 | split; [exact E2 | split; congruence]].
Qed.

End Corr.

Lemma kcorr_pull {π πi G Γ} (Hp : uperm π πi (gL G)) (HG : [ ⊢ G ]) (HΓ : dnfctx Γ)
  (ρ' : kwk (Gp π G) Γ[pφ π]ᵤ) : kcorr π (kw_pull Hp HG HΓ ρ') ρ'.
Proof using . split; [exact (pull_G Hp HG HΓ ρ') | split; [exact (pull_Δ Hp HG HΓ ρ') | split; reflexivity]]. Qed.

(** Correspondence along [πi], turned around. *)
Lemma kcorr_flip {π πi G Γ G0 Γ0} (ρ0 : kwk G0 Γ0) (ρ : kwk G Γ) :
  uperm π πi (gL (kw_G ρ0)) -> kcorr πi ρ0 ρ -> kcorr π ρ ρ0.
Proof using .
  intros Hp (E1 & E2 & Eg & Er).
  split; [| split; [| split; [now rewrite Eg | now rewrite Er]]].
  - rewrite <- E1. exact (Gp_rt (uperm_inv _ _ _ Hp) (kw_glob ρ0)).
  - rewrite <- E2. exact (rt_ctx (proj1 (proj2 Hp)) _ (wf_ctx_dnf (kw_ctx ρ0))).
Qed.

Lemma dnf_kty {G0 Γ0} (ρ : kwk G0 Γ0) T : dnfty T -> dnfty (kty ρ T).
Proof using . intros H; unfold kty; apply ren_dnf_ty; destruct (kw_γ ρ); cbn [gwa]; auto; intros; apply gren_dnf_all. Qed.
Lemma dnf_ktyl {G0 Γ0} (ρ : kwk G0 Γ0) T : dnfty T -> dnfty (ktyl ρ T).
Proof using . intros H; unfold ktyl; apply ren_dnf_ty; destruct (kw_γ ρ); cbn [gwa]; auto; intros; apply gren_dnf_all. Qed.
Lemma dnf_ktml {G0 Γ0} (ρ : kwk G0 Γ0) t : dnftm t -> dnftm (ktml ρ t).
Proof using . intros H; unfold ktml; apply ren_dnf, dnf_gwa, H. Qed.

Lemma usubst_sup' l l' (A B : ty) a f φ :
  (tmSup l l' A B a f)[φ]ᵤ = tmSup (lvsubst l φ) (lvsubst l' φ) A[φ]ᵤ B[φ]ᵤ a[φ]ᵤ f[φ]ᵤ.
Proof using . reflexivity. Qed.
Lemma usubst_tyW' l l' (A B : ty) φ : (tyW l l' A B)[φ]ᵤ = tyW (lvsubst l φ) (lvsubst l' φ) A[φ]ᵤ B[φ]ᵤ.
Proof using . reflexivity. Qed.

Lemma usubst_tyPi' l l' (A B : ty) φ : (tyPi l l' A B)[φ]ᵤ = tyPi (lvsubst l φ) (lvsubst l' φ) A[φ]ᵤ B[φ]ᵤ.
Proof using . reflexivity. Qed.

Lemma WhRel_pg {π πi G Γ T l t t'} : uperm π πi (gL G) -> WhRel G Γ T l t t' ->
  WhRel (Gp π G) Γ[pφ π]ᵤ T[pφ π]ᵤ (lvsubst l (pφ π)) t[pφ π]ᵤ t'[pφ π]ᵤ.
Proof using EL.
  intros Hp (w & w' & H & H' & N & N' & Ew). exists w[pφ π]ᵤ, w'[pφ π]ᵤ.
  exact (conj (pg_tmred Hp H) (conj (pg_tmred Hp H') (conj (whnf_usubst _ _ N)
           (conj (whnf_usubst _ _ N') (pg_geq_tm Hp Ew))))).
Qed.

Lemma WRel_perm π πi :
  forall G Γ l1 l2 A B (d : DomRel G Γ) (c : CodRel G Γ d) t t',
  WRel G Γ l1 l2 A B d c t t' ->
  forall (Hp : uperm π πi (gL G)) (HG : [ ⊢ G ]) (HΓ : dnfctx Γ) G' Γ' (d' : DomRel G' Γ') (c' : CodRel G' Γ' d'),
  Gp π G = G' -> Γ[pφ π]ᵤ = Γ' -> dnfty A -> dnfty B ->
  (forall (ρ : kwk G Γ) (ρ' : kwk G' Γ'), kcorr π ρ ρ' ->
     forall x y, dnftm x -> dnftm y -> d ρ x y -> d' ρ' x[pφ π]ᵤ y[pφ π]ᵤ) ->
  (forall (ρ : kwk G Γ) (ρ' : kwk G' Γ'), kcorr π ρ ρ' ->
     forall x y (h : d ρ x y) x' y' (h' : d' ρ' x' y'), x' = x[pφ π]ᵤ -> y' = y[pφ π]ᵤ ->
     forall u v, c' ρ' x' y' h' u v -> c ρ x y h u[pφ πi]ᵤ v[pφ πi]ᵤ) ->
  (forall ρ' x y (h' : d' ρ' x y) u v, c' ρ' x y h' u v -> dnftm u /\ dnftm v) ->
  WRel G' Γ' (lvsubst l1 (pφ π)) (lvsubst l2 (pφ π)) A[pφ π]ᵤ B[pφ π]ᵤ d' c' t[pφ π]ᵤ t'[pφ π]ᵤ.
Proof using EL.
  apply (WRel_mut
    (fun G Γ l1 l2 A B d c t t' _ =>
      forall (Hp : uperm π πi (gL G)) (HG : [ ⊢ G ]) (HΓ : dnfctx Γ) G' Γ' (d' : DomRel G' Γ')
        (c' : CodRel G' Γ' d'),
      Gp π G = G' -> Γ[pφ π]ᵤ = Γ' -> dnfty A -> dnfty B ->
      (forall (ρ : kwk G Γ) (ρ' : kwk G' Γ'), kcorr π ρ ρ' ->
         forall x y, dnftm x -> dnftm y -> d ρ x y -> d' ρ' x[pφ π]ᵤ y[pφ π]ᵤ) ->
      (forall (ρ : kwk G Γ) (ρ' : kwk G' Γ'), kcorr π ρ ρ' ->
         forall x y (h : d ρ x y) x' y' (h' : d' ρ' x' y'), x' = x[pφ π]ᵤ -> y' = y[pφ π]ᵤ ->
         forall u v, c' ρ' x' y' h' u v -> c ρ x y h u[pφ πi]ᵤ v[pφ πi]ᵤ) ->
      (forall ρ' x y (h' : d' ρ' x y) u v, c' ρ' x y h' u v -> dnftm u /\ dnftm v) ->
      WRel G' Γ' (lvsubst l1 (pφ π)) (lvsubst l2 (pφ π)) A[pφ π]ᵤ B[pφ π]ᵤ d' c' t[pφ π]ᵤ t'[pφ π]ᵤ)
    (fun G Γ l1 l2 A B d c w w' _ =>
      forall (Hp : uperm π πi (gL G)) (HG : [ ⊢ G ]) (HΓ : dnfctx Γ) G' Γ' (d' : DomRel G' Γ')
        (c' : CodRel G' Γ' d'),
      Gp π G = G' -> Γ[pφ π]ᵤ = Γ' -> dnfty A -> dnfty B -> dnftm w -> dnftm w' ->
      (forall (ρ : kwk G Γ) (ρ' : kwk G' Γ'), kcorr π ρ ρ' ->
         forall x y, dnftm x -> dnftm y -> d ρ x y -> d' ρ' x[pφ π]ᵤ y[pφ π]ᵤ) ->
      (forall (ρ : kwk G Γ) (ρ' : kwk G' Γ'), kcorr π ρ ρ' ->
         forall x y (h : d ρ x y) x' y' (h' : d' ρ' x' y'), x' = x[pφ π]ᵤ -> y' = y[pφ π]ᵤ ->
         forall u v, c' ρ' x' y' h' u v -> c ρ x y h u[pφ πi]ᵤ v[pφ πi]ᵤ) ->
      (forall ρ' x y (h' : d' ρ' x y) u v, c' ρ' x y h' u v -> dnftm u /\ dnftm v) ->
      WNf G' Γ' (lvsubst l1 (pφ π)) (lvsubst l2 (pφ π)) A[pφ π]ᵤ B[pφ π]ᵤ d' c' w[pφ π]ᵤ w'[pφ π]ᵤ)).
  - intros G Γ l1 l2 A B d c t t' w w' Hw Hw' Heq Hn IH Hp HG HΓ G' Γ' d' c' EG EΓ NA NB Hd Hc Hcd.
    destruct (geq_tm_dnf Heq) as [Nw Nw']. subst G' Γ'.
    apply (wrel _ _ _ _ _ _ _ _ _ _ w[pφ π]ᵤ w'[pφ π]ᵤ).
    + exact (pg_tmred Hp Hw).
    + exact (pg_tmred Hp Hw').
    + exact (pg_geq_tm Hp Heq).
    + exact (IH Hp HG HΓ _ _ d' c' eq_refl eq_refl NA NB Nw Nw' Hd Hc Hcd).
  - intros G Γ l1 l2 A B d c k1 k2 k1' k2' C D C' D' a a' f f' Hk1 Hk2 Hk1' Hk2' HC HC' HD HD' Ha Hwf Hf IH
      Hp HG HΓ G' Γ' d' c' EG EΓ NA NB Nw Nw' Hd Hc Hcd.
    subst G' Γ'.
    destruct Nw as (_ & _ & Na & _). destruct Nw' as (_ & _ & Na' & _).
    pose proof (proj1 Hp) as Hinv. pose proof (proj1 (proj2 Hp)) as Hinv'.
    rewrite !usubst_sup'.
    apply wnf_sup.
    1-4: apply (pg_lequiv Hp); assumption.
    + exact (pg_geq_ty Hp HC).
    + exact (pg_geq_ty Hp HC').
    + exact (pg_geq_ty Hp HD).
    + exact (pg_geq_ty Hp HD').
    + intros ρ'. pose proof (kcorr_pull Hp HG HΓ ρ') as Hk.
      pose proof (Hd _ _ Hk _ _ (dnf_ktm _ _ Na) (dnf_ktm _ _ Na') (Ha (kw_pull Hp HG HΓ ρ'))) as X.
      rewrite !(kcorr_ktm Hk) in X. exact X.
    + intros ρ'. pose proof (kcorr_pull Hp HG HΓ ρ') as Hk.
      pose proof (WhRel_pg (uperm_grow _ _ _ _ (kw_gL (kw_pull Hp HG HΓ ρ')) Hp) (Hwf (kw_pull Hp HG HΓ ρ'))) as X.
      rewrite (proj1 Hk), (proj1 (proj2 Hk)), usubst_tyPi', usubst_lsingle_ty', usubst_ren_ty, usubst_tyW',
        !(kcorr_ktyl Hk), (kcorr_kty Hk), !(kcorr_ktm Hk) in X.
      exact X.
    + intros ρ' ha' b b' Hbb' la lb A1 B1 la' lb' A1' B1' H1 H2 H3 H4 HA1 HB1 HA1' HB1'.
      pose proof (kcorr_pull Hp HG HΓ ρ') as Hk.
      set (ρ := kw_pull Hp HG HΓ ρ') in Hk.
      pose proof (Ha ρ) as ha.
      pose proof (Hc _ _ Hk _ _ ha _ _ ha' (eq_sym (kcorr_ktm Hk a)) (eq_sym (kcorr_ktm Hk a')) b b' Hbb') as Hbb.
      destruct (Hcd _ _ _ _ _ _ Hbb') as [Nb Nb'].
      pose proof (uperm_grow _ _ _ _ (kw_gL ρ') (uperm_inv _ _ _ Hp)) as Hpρ'.
      assert (PullL : forall lx lk, lequiv (gL (Gp π G)) lx (lvsubst lk (pφ π)) ->
                        lequiv (gL G) (lvsubst lx (pφ πi)) lk).
      { intros lx lk Hx. pose proof (pg_lequiv (G := Gp π G) (uperm_inv _ _ _ Hp) Hx) as X.
        rewrite (rt_lvl Hinv) in X. exact X. }
      (* the annotations, pulled back *)
      assert (PA : forall X lx, [ kw_G ρ' ; kw_Δ ρ' ⊢ (ktyl ρ' B[pφ π]ᵤ)[lsingle (ktm ρ' a[pφ π]ᵤ)] ≈ X @ lx ] ->
                     [ kw_G ρ ; kw_Δ ρ ⊢ (ktyl ρ B)[lsingle (ktm ρ a)] ≈ X[pφ πi]ᵤ @ lvsubst lx (pφ πi) ]).
      { intros X lx HX. pose proof (pg_geq_ty Hpρ' HX) as Z.
        rewrite usubst_lsingle_ty', ktyl_us, ktm_us, (rt_ty Hinv _ NB), (rt_tm Hinv _ Na) in Z. exact Z. }
      assert (PB : forall X lx ly, [ kw_G ρ' ; kw_Δ ρ' ,, (ktyl ρ' B[pφ π]ᵤ)[lsingle (ktm ρ' a[pφ π]ᵤ)] @ lx
                       ⊢ (tyW (lvsubst l1 (pφ π)) (lvsubst l2 (pφ π)) (kty ρ' A[pφ π]ᵤ) (ktyl ρ' B[pφ π]ᵤ))⟨↑⟩
                         ≈ X @ ly ] ->
                     [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ B)[lsingle (ktm ρ a)] @ lvsubst lx (pφ πi)
                       ⊢ (tyW l1 l2 (kty ρ A) (ktyl ρ B))⟨↑⟩ ≈ X[pφ πi]ᵤ @ lvsubst ly (pφ πi) ]).
      { intros X lx ly HX. pose proof (pg_geq_ty Hpρ' HX) as Z.
        change ((kw_Δ ρ' ,, (ktyl ρ' B[pφ π]ᵤ)[lsingle (ktm ρ' a[pφ π]ᵤ)] @ lx)[pφ πi]ᵤ)
          with ((kw_Δ ρ')[pφ πi]ᵤ ,, ((ktyl ρ' B[pφ π]ᵤ)[lsingle (ktm ρ' a[pφ π]ᵤ)])[pφ πi]ᵤ
                  @ lvsubst lx (pφ πi)) in Z.
        rewrite usubst_ren_ty, usubst_tyW', usubst_lsingle_ty', kty_us, !ktyl_us, ktm_us, !(rt_lvl Hinv),
          (rt_ty Hinv _ NA), (rt_ty Hinv _ NB), (rt_tm Hinv _ Na) in Z. exact Z. }
      destruct (geq_ty_dnf HA1) as [_ NA1]. destruct (geq_ty_dnf HB1) as [_ NB1].
      destruct (geq_ty_dnf HA1') as [_ NA1']. destruct (geq_ty_dnf HB1') as [_ NB1'].
      pose proof (PA _ _ HA1) as HA1b. pose proof (PB _ _ _ HB1) as HB1b.
      pose proof (PA _ _ HA1') as HA1'b. pose proof (PB _ _ _ HB1') as HB1'b.
      change (lvsubst (lmax (lvsubst l1 (pφ π)) (lvsubst l2 (pφ π))) (pφ πi))
        with (lvsubst (lvsubst (lmax l1 l2) (pφ π)) (pφ πi)) in HB1b, HB1'b.
      rewrite !(rt_lvl Hinv) in HA1b. rewrite !(rt_lvl Hinv) in HB1b.
      rewrite !(rt_lvl Hinv) in HA1'b. rewrite !(rt_lvl Hinv) in HB1'b.
      pose proof (IH ρ ha _ _ Hbb _ _ _ _ _ _ _ _ (PullL _ _ H1) (PullL _ (lmax l1 l2) H2) (PullL _ _ H3) (PullL _ (lmax l1 l2) H4)
                    HA1b HB1b HA1'b HB1'b (uperm_grow _ _ _ _ (kw_gL ρ) Hp) (kw_glob ρ) (wf_ctx_dnf (kw_ctx ρ))
                    (kw_G ρ') (kw_Δ ρ') (fun ρ0' => d' (kw_comp ρ' ρ0')) (fun ρ0' x x' h => c' (kw_comp ρ' ρ0') x x' h)
                    (proj1 Hk) (proj1 (proj2 Hk)) (dnf_kty _ _ NA) (dnf_ktyl _ _ NB)) as X.
      rewrite (kcorr_kty Hk), (kcorr_ktyl Hk), !usubst_app', !(kcorr_ktm Hk), !(rt_lvl Hinv'),
        (rt_ty Hinv' _ NA1), (rt_ty Hinv' _ NB1), (rt_ty Hinv' _ NA1'), (rt_ty Hinv' _ NB1'),
        (rt_tm Hinv' _ Nb), (rt_tm Hinv' _ Nb') in X.
      apply X.
      * intros ρ0 ρ0' Hk0 x y Nx Ny h. exact (Hd _ _ (kcorr_comp Hk _ _ Hk0) x y Nx Ny h).
      * intros ρ0 ρ0' Hk0 x y h x' y' h' Ex Ey u v Huv.
        exact (Hc _ _ (kcorr_comp Hk _ _ Hk0) x y h x' y' h' Ex Ey u v Huv).
      * intros ρ0' x y h' u v Huv. exact (Hcd _ _ _ _ _ _ Huv).
  - intros G Γ l1 l2 A B d c ν ν' Hν Hp HG HΓ G' Γ' d' c' EG EΓ NA NB Nw Nw' Hd Hc Hcd.
    subst G' Γ'. apply wnf_ne. exact (pg_gne_tm Hp Hν).
Qed.

(** ** Finitary trees along a permutation (M15a)

    As [WRel_perm], with the data abstract: a [sup]'s spine premise is at
    the worlds of the permuted context, pulled back; the spine itself is
    at the context, its children's annotations pulled back along [πi]. *)
Lemma usubst_tyWf_ren l (A : ty) (N : tm) φ :
  (tyWf l A N)⟨↑⟩[φ]ᵤ = (tyWf l A N)[φ]ᵤ⟨↑⟩.
Proof using . apply usubst_ren_ty. Qed.

Lemma usubst_vecwf l (A : ty) (N m : tm) φ :
  (tyVec l (tyWf l A N)⟨↑⟩ m⟨↑⟩)[φ]ᵤ = tyVec (lvsubst l φ) (tyWf l A N)[φ]ᵤ⟨↑⟩ m[φ]ᵤ⟨↑⟩.
Proof using . rewrite <- usubst_ren_ty, <- usubst_ren. reflexivity. Qed.

Lemma usubst_sigvec l (A : ty) (N m : tm) φ :
  (tySig l l (tyWf l A N) (tyVec l (tyWf l A N)⟨↑⟩ m⟨↑⟩))[φ]ᵤ =
  tySig (lvsubst l φ) (lvsubst l φ) (tyWf l A N)[φ]ᵤ (tyVec (lvsubst l φ) (tyWf l A N)[φ]ᵤ⟨↑⟩ m[φ]ᵤ⟨↑⟩).
Proof using . rewrite <- usubst_vecwf. reflexivity. Qed.

Lemma WfRel_perm π πi :
  (forall G Γ l A N (d : DomRel G Γ) t t', WfRel G Γ l A N d t t' ->
     forall (Hp : uperm π πi (gL G)) (HG : [ ⊢ G ]) (HΓ : dnfctx Γ) G' Γ' (d' : DomRel G' Γ'),
     Gp π G = G' -> Γ[pφ π]ᵤ = Γ' -> dnfty A -> dnftm N ->
     (forall (ρ : kwk G Γ) (ρ' : kwk G' Γ'), kcorr π ρ ρ' ->
        forall x y, dnftm x -> dnftm y -> d ρ x y -> d' ρ' x[pφ π]ᵤ y[pφ π]ᵤ) ->
     WfRel G' Γ' (lvsubst l (pφ π)) A[pφ π]ᵤ N[pφ π]ᵤ d' t[pφ π]ᵤ t'[pφ π]ᵤ) /\
  (forall G Γ l A N (d : DomRel G Γ) w w', WfNf G Γ l A N d w w' ->
     forall (Hp : uperm π πi (gL G)) (HG : [ ⊢ G ]) (HΓ : dnfctx Γ) G' Γ' (d' : DomRel G' Γ'),
     Gp π G = G' -> Γ[pφ π]ᵤ = Γ' -> dnfty A -> dnftm N -> dnftm w -> dnftm w' ->
     (forall (ρ : kwk G Γ) (ρ' : kwk G' Γ'), kcorr π ρ ρ' ->
        forall x y, dnftm x -> dnftm y -> d ρ x y -> d' ρ' x[pφ π]ᵤ y[pφ π]ᵤ) ->
     WfNf G' Γ' (lvsubst l (pφ π)) A[pφ π]ᵤ N[pφ π]ᵤ d' w[pφ π]ᵤ w'[pφ π]ᵤ) /\
  (forall G Γ l A N (d : DomRel G Γ) k cs cs', VecSp G Γ l A N d k cs cs' ->
     forall (Hp : uperm π πi (gL G)) (HG : [ ⊢ G ]) (HΓ : dnfctx Γ) G' Γ' (d' : DomRel G' Γ'),
     Gp π G = G' -> Γ[pφ π]ᵤ = Γ' -> dnfty A -> dnftm N ->
     (forall (ρ : kwk G Γ) (ρ' : kwk G' Γ'), kcorr π ρ ρ' ->
        forall x y, dnftm x -> dnftm y -> d ρ x y -> d' ρ' x[pφ π]ᵤ y[pφ π]ᵤ) ->
     VecSp G' Γ' (lvsubst l (pφ π)) A[pφ π]ᵤ N[pφ π]ᵤ d' k[pφ π]ᵤ cs[pφ π]ᵤ cs'[pφ π]ᵤ).
Proof using EL.
  apply WfRel_comb.
  - intros G Γ l A N d t t' w w' Hw Hw' Heq Hn IH Hp HG HΓ G' Γ' d' EG EΓ NA NN Hd.
    destruct (geq_tm_dnf Heq) as [Nw Nw']. subst G' Γ'.
    apply (wfrel _ _ _ _ _ _ _ _ w[pφ π]ᵤ w'[pφ π]ᵤ).
    + exact (pg_tmred Hp Hw).
    + exact (pg_tmred Hp Hw').
    + exact (pg_geq_tm Hp Heq).
    + exact (IH Hp HG HΓ _ _ d' eq_refl eq_refl NA NN Nw Nw' Hd).
  - intros G Γ l A N d k k' C C' M M' a a' cs cs' Hk Hk' HC HC' HM HM' Ha Hcs IH
      Hp HG HΓ G' Γ' d' EG EΓ NA NN Nw Nw' Hd.
    subst G' Γ'.
    destruct Nw as (_ & _ & Na & Ncs). destruct Nw' as (_ & _ & Na' & Ncs').
    apply wfnf_sup.
    1-2: apply (pg_lequiv Hp); assumption.
    + exact (pg_geq_ty Hp HC).
    + exact (pg_geq_ty Hp HC').
    + exact (pg_geq_tm Hp HM).
    + exact (pg_geq_tm Hp HM').
    + intros ρ'. pose proof (kcorr_pull Hp HG HΓ ρ') as Hk0.
      pose proof (Hd _ _ Hk0 _ _ (dnf_ktm _ _ Na) (dnf_ktm _ _ Na') (Ha (kw_pull Hp HG HΓ ρ'))) as X.
      rewrite !(kcorr_ktm Hk0) in X. exact X.
    + intros ρ'. pose proof (kcorr_pull Hp HG HΓ ρ') as Hk0.
      set (ρ := kw_pull Hp HG HΓ ρ') in Hk0.
      pose proof (IH ρ (uperm_grow _ _ _ _ (kw_gL ρ) Hp) (kw_glob ρ) (wf_ctx_dnf (kw_ctx ρ))
                    (kw_G ρ') (kw_Δ ρ') (fun ρ0' => d' (kw_comp ρ' ρ0'))
                    (proj1 Hk0) (proj1 (proj2 Hk0)) (dnf_kty _ _ NA) (dnf_ktml _ _ NN)) as X.
      rewrite (kcorr_kty Hk0), (kcorr_ktml Hk0), usubst_lsingle, (kcorr_ktml Hk0), !(kcorr_ktm Hk0) in X.
      apply X.
      intros ρ0 ρ0' Hk1 x y Nx Ny h. exact (Hd _ _ (kcorr_comp Hk0 _ _ Hk1) x y Nx Ny h).
  - intros G Γ l A N d ν ν' Hν Hp HG HΓ G' Γ' d' EG EΓ NA NN Nw Nw' Hd.
    subst G' Γ'. apply wfnf_ne. exact (pg_gne_tm Hp Hν).
  - intros G Γ l A N d k cs cs' Hk Hu Hp HG HΓ G' Γ' d' EG EΓ NA NN Hd.
    subst G' Γ'. apply vsp_zero; [exact (pg_tmred Hp Hk)|].
    destruct Hu as (w & w' & Hr & Hr' & Hf & Hf').
    exists w[pφ π]ᵤ, w'[pφ π]ᵤ.
    exact (conj (pg_tmred Hp Hr) (conj (pg_tmred Hp Hr') (conj (whnf_usubst _ _ Hf) (whnf_usubst _ _ Hf')))).
  - intros G Γ l A N d k m cs cs' w w' Hk Hcs Hcs' Hwh Hwh' Heq Hfst IHfst Hsnd IHsnd
      Hp HG HΓ G' Γ' d' EG EΓ NA NN Hd.
    subst G' Γ'.
    pose proof (proj1 Hp) as Hinv. pose proof (proj1 (proj2 Hp)) as Hinv'.
    pose proof (uperm_inv _ _ _ Hp) as Hpi.
    assert (NW : dnfty (tyWf l A N)) by (cbn; auto).
    assert (NΓW : dnfctx (Γ ,, tyWf l A N @ l)) by (cbn; auto).
    assert (NV : dnfty (tyVec l (tyWf l A N)⟨↑⟩ m⟨↑⟩)) by (split; [apply ren_dnf_ty; exact NW | apply ren_dnf];
          exact (wf_tm_dnf (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hk)))).
    assert (PullL : forall lx lk, lequiv (gL (Gp π G)) lx (lvsubst lk (pφ π)) ->
                      lequiv (gL G) (lvsubst lx (pφ πi)) lk).
    { intros lx lk Hx. pose proof (pg_lequiv (G := Gp π G) Hpi Hx) as X. rewrite (rt_lvl Hinv) in X. exact X. }
    assert (PA : forall X, [ Gp π G ; Γ[pφ π]ᵤ ⊢ (tyWf l A N)[pφ π]ᵤ ≈ X @ lvsubst l (pφ π) ] ->
                   [ G ; Γ ⊢ tyWf l A N ≈ X[pφ πi]ᵤ @ l ]).
    { intros X HX. pose proof (pg_geq_ty (G := Gp π G) Hpi HX) as Z.
      rewrite (Gp_rt Hp HG), (rt_ctx Hinv _ HΓ), (rt_ty Hinv _ NW), (rt_lvl Hinv) in Z. exact Z. }
    assert (PB : forall X, [ Gp π G ; Γ[pφ π]ᵤ ,, (tyWf l A N)[pφ π]ᵤ @ lvsubst l (pφ π)
                             ⊢ tyVec (lvsubst l (pφ π)) (tyWf l A N)[pφ π]ᵤ⟨↑⟩ m[pφ π]ᵤ⟨↑⟩ ≈ X @ lvsubst l (pφ π) ] ->
                   [ G ; Γ ,, tyWf l A N @ l ⊢ tyVec l (tyWf l A N)⟨↑⟩ m⟨↑⟩ ≈ X[pφ πi]ᵤ @ l ]).
    { intros X HX. rewrite <- usubst_vecwf in HX.
      pose proof (pg_geq_ty (G := Gp π G) (Γ := (Γ ,, tyWf l A N @ l)[pφ π]ᵤ) Hpi HX) as Z.
      rewrite (Gp_rt Hp HG), (rt_ctx Hinv _ NΓW), (rt_ty Hinv _ NV), (rt_lvl Hinv) in Z. exact Z. }
    pose proof (pg_tmred Hp Hcs) as Rcs. pose proof (pg_tmred Hp Hcs') as Rcs'. pose proof (pg_geq_tm Hp Heq) as Eq.
    rewrite usubst_sigvec in Rcs, Rcs', Eq.
    apply (vsp_succ (Gp π G) Γ[pφ π]ᵤ (lvsubst l (pφ π)) A[pφ π]ᵤ N[pφ π]ᵤ d' k[pφ π]ᵤ m[pφ π]ᵤ
             cs[pφ π]ᵤ cs'[pφ π]ᵤ w[pφ π]ᵤ w'[pφ π]ᵤ).
    + exact (pg_tmred Hp Hk).
    + exact Rcs.
    + exact Rcs'.
    + exact (whnf_usubst _ _ Hwh).
    + exact (whnf_usubst _ _ Hwh').
    + exact Eq.
    + intros la lb A1 B1 la' lb' A1' B1' H1 H2 H3 H4 HA1 HB1 HA1' HB1'.
      destruct (geq_ty_dnf HA1) as [_ NA1]. destruct (geq_ty_dnf HB1) as [_ NB1].
      destruct (geq_ty_dnf HA1') as [_ NA1']. destruct (geq_ty_dnf HB1') as [_ NB1'].
      pose proof (IHfst _ _ _ _ _ _ _ _ (PullL _ _ H1) (PullL _ _ H2) (PullL _ _ H3) (PullL _ _ H4)
                    (PA _ HA1) (PB _ HB1) (PA _ HA1') (PB _ HB1') Hp HG HΓ _ _ d' eq_refl eq_refl NA NN Hd) as X.
      rewrite !usubst_fst', !(rt_lvl Hinv'), (rt_ty Hinv' _ NA1), (rt_ty Hinv' _ NB1),
        (rt_ty Hinv' _ NA1'), (rt_ty Hinv' _ NB1') in X.
      exact X.
    + intros la lb A1 B1 la' lb' A1' B1' H1 H2 H3 H4 HA1 HB1 HA1' HB1'.
      destruct (geq_ty_dnf HA1) as [_ NA1]. destruct (geq_ty_dnf HB1) as [_ NB1].
      destruct (geq_ty_dnf HA1') as [_ NA1']. destruct (geq_ty_dnf HB1') as [_ NB1'].
      pose proof (IHsnd _ _ _ _ _ _ _ _ (PullL _ _ H1) (PullL _ _ H2) (PullL _ _ H3) (PullL _ _ H4)
                    (PA _ HA1) (PB _ HB1) (PA _ HA1') (PB _ HB1') Hp HG HΓ _ _ d' eq_refl eq_refl NA NN Hd) as X.
      rewrite !usubst_snd', !(rt_lvl Hinv'), (rt_ty Hinv' _ NA1), (rt_ty Hinv' _ NB1),
        (rt_ty Hinv' _ NA1'), (rt_ty Hinv' _ NB1') in X.
      exact X.
  - intros G Γ l A N d k ν cs cs' Hk Hν Hne Hp HG HΓ G' Γ' d' EG EΓ NA NN Hd.
    subst G' Γ'.
    apply (vsp_ne _ _ _ _ _ _ _ ν[pφ π]ᵤ); [exact (pg_tmred Hp Hk) | exact (pg_gne_tm Hp Hν) |].
    exact (NeRel_perm Hp _ _ _ _ _ Hne).
Qed.

(** ** Indexed finitary trees along a permutation (M17b)

    As [WfRel_perm], with both the index and the shape data abstract and
    carried along corresponding worlds ([DTr]); the annotations' agreement
    is declarative and permutes as the judgments do. *)
Lemma ktmll_us {G0 Γ0} (ρ : kwk G0 Γ0) t φ : (ktmll ρ t)[φ]ᵤ = t[φ]ᵤ⟦kw_γ ρ⟧⟨rlift (rlift (kw_r ρ))⟩.
Proof using . unfold ktmll. now rewrite usubst_ren, usubst_gwa_tm. Qed.
Lemma kcorr_ktmll {π G Γ G' Γ'} {ρ : kwk G Γ} {ρ' : kwk G' Γ'} (Hk : kcorr π ρ ρ') t :
  (ktmll ρ t)[pφ π]ᵤ = ktmll ρ' t[pφ π]ᵤ.
Proof using . destruct Hk as (_ & _ & Eg & Er). rewrite ktmll_us. unfold ktmll. now rewrite Eg, Er. Qed.
Lemma ktmll_pull {π πi G Γ} (Hp : uperm π πi (gL G)) (HG : [ ⊢ G ]) (HΓ : dnfctx Γ)
  (ρ' : kwk (Gp π G) (Γ[pφ π]ᵤ)) t : (ktmll (kw_pull Hp HG HΓ ρ') t)[pφ π]ᵤ = ktmll ρ' t[pφ π]ᵤ.
Proof using . unfold ktmll; cbn. now rewrite usubst_ren, usubst_gwa_tm. Qed.
Lemma dnf_ktmll {G0 Γ0} (ρ : kwk G0 Γ0) t : dnftm t -> dnftm (ktmll ρ t).
Proof using . intros H; unfold ktmll; apply ren_dnf, dnf_gwa, H. Qed.

Definition DTr (π : nat -> nat) {G Γ G' Γ'} (d : DomRel G Γ) (d' : DomRel G' Γ') : Prop :=
  forall (ρ : kwk G Γ) (ρ' : kwk G' Γ'), kcorr π ρ ρ' ->
    forall x y, dnftm x -> dnftm y -> d ρ x y -> d' ρ' x[pφ π]ᵤ y[pφ π]ᵤ.

Lemma DTr_comp {π G Γ G' Γ'} {ρ : kwk G Γ} {ρ' : kwk G' Γ'} (Hk : kcorr π ρ ρ') {d d'} :
  DTr π d d' -> DTr π (fun ρ0 => d (kw_comp ρ ρ0)) (fun ρ0' => d' (kw_comp ρ' ρ0')).
Proof using . intros H ρ0 ρ0' Hk1 x y Nx Ny h. exact (H _ _ (kcorr_comp Hk _ _ Hk1) x y Nx Ny h). Qed.

Lemma PosRel_perm {π πi G Γ} (Hp : uperm π πi (gL G)) {k k' p p'} : PosRel G Γ k k' p p' ->
  PosRel (Gp π G) Γ[pφ π]ᵤ k[pφ π]ᵤ k'[pφ π]ᵤ p[pφ π]ᵤ p'[pφ π]ᵤ.
Proof using EL.
  induction 1 as [k k' m m' Hk Hk' Hm | k k' m m' p p' Hk Hk' Hp' IH | k k' p p' Ek Hp'].
  - exact (pos_hd _ _ _ _ m[pφ π]ᵤ m'[pφ π]ᵤ (pg_tmred Hp Hk) (pg_tmred Hp Hk') (NatRel_perm Hp _ _ Hm)).
  - exact (pos_tl _ _ _ _ m[pφ π]ᵤ m'[pφ π]ᵤ _ _ (pg_tmred Hp Hk) (pg_tmred Hp Hk') IH).
  - exact (pos_ne _ _ _ _ _ _ (p_eqtm Hp Ek) (pg_gne_tm Hp Hp')).
Qed.

Lemma PosRel_dnf {G Γ k k' p p'} : PosRel G Γ k k' p p' -> dnftm p /\ dnftm p'.
Proof using EL.
  induction 1 as [k k' m m' Hk Hk' Hm | k k' m m' p p' Hk Hk' Hp' [IH IH'] | k k' p p' Ek Hp'].
  3: { pose proof (geq_tm_sound (gne_tm_geq Hp')) as Ep.
       exact (conj (wf_tm_dnf (eqtm_wf_l ge_typeof Ep)) (wf_tm_dnf (eqtm_wf_r ge_typeof Ep))). }
  all: pose proof (wf_tm_dnf (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hk))) as N1;
    pose proof (wf_tm_dnf (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hk'))) as N2;
    cbn in N1, N2; unfold posHd, posTl; cbn; repeat split; auto.
Qed.

Lemma IWfEq_pg {π πi G} (Hp : uperm π πi (gL G)) {Γ l li k ki X X' A A' N N' Ot Ot' C C'} :
  IWfEq (G := G) (i := ge_layer) Γ l li k ki X X' A A' N N' Ot Ot' C C' ->
  IWfEq (G := Gp π G) (i := ge_layer) Γ[pφ π]ᵤ (lvsubst l (pφ π)) (lvsubst li (pφ π))
    (lvsubst k (pφ π)) (lvsubst ki (pφ π)) X[pφ π]ᵤ X'[pφ π]ᵤ A[pφ π]ᵤ A'[pφ π]ᵤ N[pφ π]ᵤ N'[pφ π]ᵤ
    Ot[pφ π]ᵤ Ot'[pφ π]ᵤ C[pφ π]ᵤ C'[pφ π]ᵤ.
Proof using EL.
  intros (Hl & Hli & (Wl & Wli & HX & HA & HN & HO & HC) & EX & EA & EN & EO & EC & HX' & HA' & HN' & HO' & HC').
  pose proof (pg_tm Hp HO) as HOp. pose proof (pg_tm Hp HC) as HCp.
  pose proof (pg_tm Hp HO') as HOp'. pose proof (pg_tm Hp HC') as HCp'.
  pose proof (p_eqtm Hp EO) as EOp. pose proof (p_eqtm Hp EC) as ECp.
  rewrite usubst_ren_ty in HOp, HOp', EOp. rewrite !usubst_ren_ty in HCp. rewrite !usubst_ren_ty in HCp'.
  rewrite !usubst_ren_ty in ECp.
  exact (conj (pg_lequiv Hp Hl) (conj (pg_lequiv Hp Hli)
          (conj (conj (pg_lwf Hp Wl) (conj (pg_lwf Hp Wli) (conj (pg_ty Hp HX) (conj (pg_ty Hp HA)
                  (conj (pg_tm Hp HN) (conj HOp HCp))))))
          (conj (pg_eqty Hp EX) (conj (pg_eqty Hp EA) (conj (p_eqtm Hp EN) (conj EOp (conj ECp
          (conj (pg_ty Hp HX') (conj (pg_ty Hp HA') (conj (pg_tm Hp HN') (conj HOp' HCp')))))))))))).
Qed.

Lemma usubst_iwfFamT l li (X A : ty) (N Ot C c : tm) φ :
  (iwfFamT l li X A N Ot C c)[φ]ᵤ = iwfFamT (lvsubst l φ) (lvsubst li φ) X[φ]ᵤ A[φ]ᵤ N[φ]ᵤ Ot[φ]ᵤ C[φ]ᵤ c[φ]ᵤ.
Proof using . unfold iwfFamT. cbn. rewrite ?usubst_ren_ty', ?usubst_ren'. reflexivity. Qed.
Lemma usubst_dvecHd n (F : ty) φ : (dvecHd n F)[φ]ᵤ = dvecHd n[φ]ᵤ F[φ]ᵤ.
Proof using . rewrite usubst_lsingle_ty. reflexivity. Qed.
Lemma usubst_dvecTl L n (F : ty) φ : (dvecTl L n F)[φ]ᵤ = dvecTl (lvsubst L φ) n[φ]ᵤ F[φ]ᵤ.
Proof using . cbn. rewrite usubst_lsingle_ty. cbn. rewrite ?usubst_ren_ty', ?usubst_ren'. reflexivity. Qed.
Lemma usubst_tySig' la lb (A B : ty) φ : (tySig la lb A B)[φ]ᵤ = tySig (lvsubst la φ) (lvsubst lb φ) A[φ]ᵤ B[φ]ᵤ.
Proof using . reflexivity. Qed.
Lemma usubst_tyDVec' L n (F : ty) φ : (tyDVec L n F)[φ]ᵤ = tyDVec (lvsubst L φ) n[φ]ᵤ F[φ]ᵤ.
Proof using . reflexivity. Qed.
Lemma usubst_posMv k c φ : (posMv k c)[φ]ᵤ = posMv k[φ]ᵤ c[φ]ᵤ.
Proof using . unfold posMv, posTl. rewrite usubst_lsingle. cbn. rewrite ?usubst_ren'. reflexivity. Qed.

Lemma IWfRel_perm π πi :
  (forall G Γ l li X A N Ot C (ix d : DomRel G Γ) m t t', IWfRel G Γ l li X A N Ot C ix d m t t' ->
     forall (Hp : uperm π πi (gL G)) (HG : [ ⊢ G ]) (HΓ : dnfctx Γ) G' Γ' (ix' d' : DomRel G' Γ'),
     Gp π G = G' -> Γ[pφ π]ᵤ = Γ' -> dnfty X -> dnfty A -> dnftm N -> dnftm Ot -> dnftm C -> dnftm m ->
     DTr π ix ix' -> DTr π d d' ->
     IWfRel G' Γ' (lvsubst l (pφ π)) (lvsubst li (pφ π)) X[pφ π]ᵤ A[pφ π]ᵤ N[pφ π]ᵤ Ot[pφ π]ᵤ C[pφ π]ᵤ
       ix' d' m[pφ π]ᵤ t[pφ π]ᵤ t'[pφ π]ᵤ) /\
  (forall G Γ l li X A N Ot C (ix d : DomRel G Γ) m w w', IWfNf G Γ l li X A N Ot C ix d m w w' ->
     forall (Hp : uperm π πi (gL G)) (HG : [ ⊢ G ]) (HΓ : dnfctx Γ) G' Γ' (ix' d' : DomRel G' Γ'),
     Gp π G = G' -> Γ[pφ π]ᵤ = Γ' -> dnfty X -> dnfty A -> dnftm N -> dnftm Ot -> dnftm C -> dnftm m ->
     dnftm w -> dnftm w' -> DTr π ix ix' -> DTr π d d' ->
     IWfNf G' Γ' (lvsubst l (pφ π)) (lvsubst li (pφ π)) X[pφ π]ᵤ A[pφ π]ᵤ N[pφ π]ᵤ Ot[pφ π]ᵤ C[pφ π]ᵤ
       ix' d' m[pφ π]ᵤ w[pφ π]ᵤ w'[pφ π]ᵤ) /\
  (forall G Γ l li X A N Ot C (ix d : DomRel G Γ) c k cs cs', DVecISp G Γ l li X A N Ot C ix d c k cs cs' ->
     forall (Hp : uperm π πi (gL G)) (HG : [ ⊢ G ]) (HΓ : dnfctx Γ) G' Γ' (ix' d' : DomRel G' Γ'),
     Gp π G = G' -> Γ[pφ π]ᵤ = Γ' -> dnfty X -> dnfty A -> dnftm N -> dnftm Ot -> dnftm C -> dnftm c ->
     DTr π ix ix' -> DTr π d d' ->
     DVecISp G' Γ' (lvsubst l (pφ π)) (lvsubst li (pφ π)) X[pφ π]ᵤ A[pφ π]ᵤ N[pφ π]ᵤ Ot[pφ π]ᵤ C[pφ π]ᵤ
       ix' d' c[pφ π]ᵤ k[pφ π]ᵤ cs[pφ π]ᵤ cs'[pφ π]ᵤ).
Proof using EL.
  apply IWfRel_comb.
  - intros G Γ l li X A N Ot C ix d m t t' w w' Hw Hw' Heq Hn IH
      Hp HG HΓ G' Γ' ix' d' EG EΓ NX NA NN NO NC Nm Hix Hd.
    destruct (geq_tm_dnf Heq) as [Nw Nw']. subst G' Γ'.
    apply (iwfrel _ _ _ _ _ _ _ _ _ _ _ _ _ _ w[pφ π]ᵤ w'[pφ π]ᵤ).
    + exact (pg_tmred Hp Hw).
    + exact (pg_tmred Hp Hw').
    + exact (pg_geq_tm Hp Heq).
    + exact (IH Hp HG HΓ _ _ ix' d' eq_refl eq_refl NX NA NN NO NC Nm Nw Nw' Hix Hd).
  - intros G Γ l li X A N Ot C ix d m k ki k' ki' X1 A1 N1 O1 C1 X1' A1' N1' O1' C1' a a' cs cs'
      E1 E2 Hd0 Ho Hcs IH Hp HG HΓ G' Γ' ix' d' EG EΓ NX NA NN NO NC Nm Nw Nw' Hix Hd.
    subst G' Γ'.
    destruct Nw as (_ & _ & _ & _ & _ & Na & Ncs). destruct Nw' as (_ & _ & _ & _ & _ & Na' & Ncs').
    apply iwfnf_sup.
    + exact (IWfEq_pg Hp E1).
    + exact (IWfEq_pg Hp E2).
    + intros ρ'. pose proof (kcorr_pull Hp HG HΓ ρ') as Hk0.
      pose proof (Hd _ _ Hk0 _ _ (dnf_ktm _ _ Na) (dnf_ktm _ _ Na') (Hd0 (kw_pull Hp HG HΓ ρ'))) as Y.
      rewrite !(kcorr_ktm Hk0) in Y. exact Y.
    + intros ρ'. pose proof (kcorr_pull Hp HG HΓ ρ') as Hk0.
      pose proof (Hix _ _ Hk0 _ _ (subst_dnf _ _ (dnf_ktml _ _ NO) (lk_dnf_lsingle _ (dnf_ktm _ _ Na)))
                    (dnf_ktm _ _ Nm) (Ho (kw_pull Hp HG HΓ ρ'))) as Y.
      rewrite usubst_lsingle, (kcorr_ktml Hk0), !(kcorr_ktm Hk0) in Y. exact Y.
    + intros ρ'. pose proof (kcorr_pull Hp HG HΓ ρ') as Hk0.
      set (ρ := kw_pull Hp HG HΓ ρ') in Hk0.
      pose proof (IH ρ (uperm_grow _ _ _ _ (kw_gL ρ) Hp) (kw_glob ρ) (wf_ctx_dnf (kw_ctx ρ))
                    (kw_G ρ') (kw_Δ ρ') (fun ρ0' => ix' (kw_comp ρ' ρ0')) (fun ρ0' => d' (kw_comp ρ' ρ0'))
                    (proj1 Hk0) (proj1 (proj2 Hk0)) (dnf_kty _ _ NX) (dnf_kty _ _ NA) (dnf_ktml _ _ NN)
                    (dnf_ktml _ _ NO) (dnf_ktmll _ _ NC)
                    (subst_dnf _ _ (dnf_ktmll _ _ NC) (lk_dnf_llift _ (lk_dnf_lsingle _ (dnf_ktm _ _ Na))))
                    (DTr_comp Hk0 Hix) (DTr_comp Hk0 Hd)) as Y.
      rewrite !(kcorr_kty Hk0), usubst_llift_single, usubst_lsingle, !(kcorr_ktml Hk0), !(kcorr_ktmll Hk0),
        !(kcorr_ktm Hk0) in Y.
      exact Y.
  - intros G Γ l li X A N Ot C ix d m ν ν' Hν Hp HG HΓ G' Γ' ix' d' EG EΓ NX NA NN NO NC Nm Nw Nw' Hix Hd.
    subst G' Γ'. apply iwfnf_ne. exact (pg_gne_tm Hp Hν).
  - intros G Γ l li X A N Ot C ix d c k cs cs' Hk Hu Hp HG HΓ G' Γ' ix' d' EG EΓ NX NA NN NO NC Nc Hix Hd.
    subst G' Γ'. apply visp_zero; [exact (pg_tmred Hp Hk)|].
    destruct Hu as (w & w' & Hr & Hr' & Hf & Hf').
    exists w[pφ π]ᵤ, w'[pφ π]ᵤ.
    exact (conj (pg_tmred Hp Hr) (conj (pg_tmred Hp Hr') (conj (whnf_usubst _ _ Hf) (whnf_usubst _ _ Hf')))).
  - intros G Γ l li X A N Ot C ix d c k m cs cs' w w' Hk Hcs Hcs' Hwh Hwh' Heq Hfst IHfst Hsnd IHsnd
      Hp HG HΓ G' Γ' ix' d' EG EΓ NX NA NN NO NC Nc Hix Hd.
    subst G' Γ'.
    pose proof (proj1 Hp) as Hinv. pose proof (proj1 (proj2 Hp)) as Hinv'.
    pose proof (uperm_inv _ _ _ Hp) as Hpi.
    assert (Nm : dnftm m) by exact (wf_tm_dnf (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hk))).
    assert (NF : dnfty (iwfFamT l li X A N Ot C c))
      by (unfold iwfFamT; cbn; repeat split; auto using ren_dnf, ren_dnf_ty).
    assert (Nhd : dnftm (posHd m)) by (unfold posHd; cbn; repeat split; auto).
    assert (NH : dnfty (dvecHd m (iwfFamT l li X A N Ot C c)))
      by exact (subst_dnf_ty _ _ NF (lk_dnf_lsingle _ Nhd)).
    assert (NT : dnfty (dvecTl (lmax l li) m (iwfFamT l li X A N Ot C c))).
    { cbn [dnfty]. split; [apply ren_dnf, Nm|].
      apply subst_dnf_ty; [apply ren_dnf_ty, ren_dnf_ty, NF | apply lk_dnf_lsingle].
      cbn; repeat split; auto using ren_dnf. }
    assert (NΓH : dnfctx (Γ ,, dvecHd m (iwfFamT l li X A N Ot C c) @ lmax l li)) by (cbn; auto).
    assert (PullL : forall lx lk, lequiv (gL (Gp π G)) lx (lvsubst lk (pφ π)) ->
                      lequiv (gL G) (lvsubst lx (pφ πi)) lk).
    { intros lx lk Hx. pose proof (pg_lequiv (G := Gp π G) Hpi Hx) as Z. rewrite (rt_lvl Hinv) in Z. exact Z. }
    assert (PA : forall Y,
               [ Gp π G ; Γ[pφ π]ᵤ ⊢ dvecHd m[pφ π]ᵤ (iwfFamT (lvsubst l (pφ π)) (lvsubst li (pφ π))
                    X[pφ π]ᵤ A[pφ π]ᵤ N[pφ π]ᵤ Ot[pφ π]ᵤ C[pφ π]ᵤ c[pφ π]ᵤ) ≈ Y @ lvsubst (lmax l li) (pφ π) ] ->
               [ G ; Γ ⊢ dvecHd m (iwfFamT l li X A N Ot C c) ≈ Y[pφ πi]ᵤ @ lmax l li ]).
    { intros Y HY.
      assert (HY' : [ Gp π G ; Γ[pφ π]ᵤ ⊢ (dvecHd m (iwfFamT l li X A N Ot C c))[pφ π]ᵤ ≈ Y
                        @ lvsubst (lmax l li) (pφ π) ])
        by (rewrite usubst_dvecHd, usubst_iwfFamT; exact HY).
      pose proof (pg_geq_ty (G := Gp π G) Hpi HY') as Z.
      rewrite (Gp_rt Hp HG), (rt_ctx Hinv _ HΓ), (rt_ty Hinv _ NH), (rt_lvl Hinv) in Z. exact Z. }
    assert (PB : forall Y,
               [ Gp π G ; Γ[pφ π]ᵤ ,, dvecHd m[pφ π]ᵤ (iwfFamT (lvsubst l (pφ π)) (lvsubst li (pφ π))
                    X[pφ π]ᵤ A[pφ π]ᵤ N[pφ π]ᵤ Ot[pφ π]ᵤ C[pφ π]ᵤ c[pφ π]ᵤ) @ lvsubst (lmax l li) (pφ π)
                 ⊢ dvecTl (lvsubst (lmax l li) (pφ π)) m[pφ π]ᵤ (iwfFamT (lvsubst l (pφ π)) (lvsubst li (pφ π))
                    X[pφ π]ᵤ A[pφ π]ᵤ N[pφ π]ᵤ Ot[pφ π]ᵤ C[pφ π]ᵤ c[pφ π]ᵤ) ≈ Y @ lvsubst (lmax l li) (pφ π) ] ->
               [ G ; Γ ,, dvecHd m (iwfFamT l li X A N Ot C c) @ lmax l li
                   ⊢ dvecTl (lmax l li) m (iwfFamT l li X A N Ot C c) ≈ Y[pφ πi]ᵤ @ lmax l li ]).
    { intros Y HY.
      assert (HY' : [ Gp π G ; (Γ ,, dvecHd m (iwfFamT l li X A N Ot C c) @ lmax l li)[pφ π]ᵤ
                        ⊢ (dvecTl (lmax l li) m (iwfFamT l li X A N Ot C c))[pφ π]ᵤ ≈ Y
                        @ lvsubst (lmax l li) (pφ π) ]).
      { change ((Γ ,, dvecHd m (iwfFamT l li X A N Ot C c) @ lmax l li)[pφ π]ᵤ)
          with (Γ[pφ π]ᵤ ,, (dvecHd m (iwfFamT l li X A N Ot C c))[pφ π]ᵤ @ lvsubst (lmax l li) (pφ π)).
        rewrite usubst_dvecHd, usubst_dvecTl, usubst_iwfFamT. exact HY. }
      pose proof (pg_geq_ty (G := Gp π G) Hpi HY') as Z.
      rewrite (Gp_rt Hp HG), (rt_ctx Hinv _ NΓH), (rt_ty Hinv _ NT), (rt_lvl Hinv) in Z. exact Z. }
    pose proof (pg_tmred Hp Hcs) as Rcs. pose proof (pg_tmred Hp Hcs') as Rcs'. pose proof (pg_geq_tm Hp Heq) as Eq.
    rewrite usubst_tySig', usubst_dvecHd, usubst_dvecTl, usubst_iwfFamT in Rcs, Rcs', Eq.
    apply (visp_succ (Gp π G) Γ[pφ π]ᵤ (lvsubst l (pφ π)) (lvsubst li (pφ π)) X[pφ π]ᵤ A[pφ π]ᵤ N[pφ π]ᵤ
             Ot[pφ π]ᵤ C[pφ π]ᵤ ix' d' c[pφ π]ᵤ k[pφ π]ᵤ m[pφ π]ᵤ cs[pφ π]ᵤ cs'[pφ π]ᵤ w[pφ π]ᵤ w'[pφ π]ᵤ).
    + exact (pg_tmred Hp Hk).
    + exact Rcs.
    + exact Rcs'.
    + exact (whnf_usubst _ _ Hwh).
    + exact (whnf_usubst _ _ Hwh').
    + exact Eq.
    + intros la lb A1 B1 la' lb' A1' B1' H1 H2 H3 H4 HA1 HB1 HA1' HB1'.
      destruct (geq_ty_dnf HA1) as [_ NA1]. destruct (geq_ty_dnf HB1) as [_ NB1].
      destruct (geq_ty_dnf HA1') as [_ NA1']. destruct (geq_ty_dnf HB1') as [_ NB1'].
      pose proof (IHfst _ _ _ _ _ _ _ _ (PullL _ (lmax l li) H1) (PullL _ (lmax l li) H2)
                    (PullL _ (lmax l li) H3) (PullL _ (lmax l li) H4)
                    (PA _ HA1) (PB _ HB1) (PA _ HA1') (PB _ HB1') Hp HG HΓ _ _ ix' d' eq_refl eq_refl
                    NX NA NN NO NC (subst_dnf _ _ Nc (lk_dnf_lsingle _ Nhd)) Hix Hd) as Y.
      rewrite !usubst_fst', !(rt_lvl Hinv'), (rt_ty Hinv' _ NA1), (rt_ty Hinv' _ NB1),
        (rt_ty Hinv' _ NA1'), (rt_ty Hinv' _ NB1'), usubst_lsingle in Y.
      exact Y.
    + intros la lb A1 B1 la' lb' A1' B1' H1 H2 H3 H4 HA1 HB1 HA1' HB1'.
      destruct (geq_ty_dnf HA1) as [_ NA1]. destruct (geq_ty_dnf HB1) as [_ NB1].
      destruct (geq_ty_dnf HA1') as [_ NA1']. destruct (geq_ty_dnf HB1') as [_ NB1'].
      assert (Nmv : dnftm (posMv m c)).
      { unfold posMv. apply subst_dnf; [apply ren_dnf, Nc | apply lk_dnf_lsingle].
        unfold posTl; cbn; repeat split; auto using ren_dnf. }
      pose proof (IHsnd _ _ _ _ _ _ _ _ (PullL _ (lmax l li) H1) (PullL _ (lmax l li) H2)
                    (PullL _ (lmax l li) H3) (PullL _ (lmax l li) H4)
                    (PA _ HA1) (PB _ HB1) (PA _ HA1') (PB _ HB1') Hp HG HΓ _ _ ix' d' eq_refl eq_refl
                    NX NA NN NO NC Nmv Hix Hd) as Y.
      rewrite !usubst_snd', !(rt_lvl Hinv'), (rt_ty Hinv' _ NA1), (rt_ty Hinv' _ NB1),
        (rt_ty Hinv' _ NA1'), (rt_ty Hinv' _ NB1'), usubst_posMv in Y.
      exact Y.
  - intros G Γ l li X A N Ot C ix d c k ν cs cs' Hk Hν Hne Hp HG HΓ G' Γ' ix' d' EG EΓ NX NA NN NO NC Nc Hix Hd.
    subst G' Γ'.
    apply (visp_ne _ _ _ _ _ _ _ _ _ _ _ _ _ ν[pφ π]ᵤ); [exact (pg_tmred Hp Hk) | exact (pg_gne_tm Hp Hν) |].
    pose proof (NeRel_perm Hp _ _ _ _ _ Hne) as Y. rewrite usubst_tyDVec', usubst_iwfFamT in Y. exact Y.
Qed.

(** ** Indexed [M] along a permutation (M18b)

    As [IWfRel_perm], by induction on the depth, with the relations
    abstract: the shapes' relation carried forward along corresponding
    worlds ([STr]), the positions' relation, a [Π] domain of the
    observations, backward ([PTr]). The observations' [Σ] and [Π]
    relations are carried by [SigRel_pt] and [PiRel_pt], whose target
    data are abstract up to equations: the observations' are the
    permuted data seen from a world, not syntactically permuted. *)

Lemma usubst_mKidTy l l' li (X A B : ty) (C j : tm) φ :
  (mKidTy l l' li X A B C j)[φ]ᵤ =
  mKidTy (lvsubst l φ) (lvsubst l' φ) (lvsubst li φ) X[φ]ᵤ A[φ]ᵤ B[φ]ᵤ C[φ]ᵤ j[φ]ᵤ.
Proof using . cbn. rewrite ?usubst_ren_ty', ?usubst_ren', usubst_llift2_single. reflexivity. Qed.
Lemma usubst_out' k k' ki (X A B : ty) (C j t : tm) φ :
  (tmOut k k' ki X A B C j t)[φ]ᵤ =
  tmOut (lvsubst k φ) (lvsubst k' φ) (lvsubst ki φ) X[φ]ᵤ A[φ]ᵤ B[φ]ᵤ C[φ]ᵤ j[φ]ᵤ t[φ]ᵤ.
Proof using . reflexivity. Qed.

Lemma ktyll_us {G0 Γ0} (ρ : kwk G0 Γ0) T φ : (ktyll ρ T)[φ]ᵤ = T[φ]ᵤ⟦kw_γ ρ⟧⟨rlift (rlift (kw_r ρ))⟩.
Proof using . unfold ktyll. now rewrite usubst_ren_ty, usubst_gwa_ty. Qed.
Lemma ktmlll_us {G0 Γ0} (ρ : kwk G0 Γ0) t φ :
  (ktmlll ρ t)[φ]ᵤ = t[φ]ᵤ⟦kw_γ ρ⟧⟨rlift (rlift (rlift (kw_r ρ)))⟩.
Proof using . unfold ktmlll. now rewrite usubst_ren, usubst_gwa_tm. Qed.
Lemma kcorr_ktyll {π G Γ G' Γ'} {ρ : kwk G Γ} {ρ' : kwk G' Γ'} (Hk : kcorr π ρ ρ') T :
  (ktyll ρ T)[pφ π]ᵤ = ktyll ρ' T[pφ π]ᵤ.
Proof using . destruct Hk as (_ & _ & Eg & Er). rewrite ktyll_us. unfold ktyll. now rewrite Eg, Er. Qed.
Lemma kcorr_ktmlll {π G Γ G' Γ'} {ρ : kwk G Γ} {ρ' : kwk G' Γ'} (Hk : kcorr π ρ ρ') t :
  (ktmlll ρ t)[pφ π]ᵤ = ktmlll ρ' t[pφ π]ᵤ.
Proof using . destruct Hk as (_ & _ & Eg & Er). rewrite ktmlll_us. unfold ktmlll. now rewrite Eg, Er. Qed.
Lemma dnf_ktyll {G0 Γ0} (ρ : kwk G0 Γ0) T : dnfty T -> dnfty (ktyll ρ T).
Proof using . intros H; unfold ktyll; apply ren_dnf_ty; destruct (kw_γ ρ); cbn [gwa]; auto; intros; apply gren_dnf_all. Qed.
Lemma dnf_ktmlll {G0 Γ0} (ρ : kwk G0 Γ0) t : dnftm t -> dnftm (ktmlll ρ t).
Proof using . intros H; unfold ktmlll; apply ren_dnf, dnf_gwa, H. Qed.

(** A world of a corresponding world's context corresponds to one of the
    original's. *)
Lemma kcorr_lift {π πi G Γ G0 Γ0} (ρ : kwk G Γ) (ρ0 : kwk G0 Γ0) :
  uperm π πi (gL (kw_G ρ)) -> kcorr π ρ ρ0 ->
  forall ρ1 : kwk (kw_G ρ0) (kw_Δ ρ0), exists ρ1b : kwk (kw_G ρ) (kw_Δ ρ), kcorr π ρ1b ρ1.
Proof using EL.
  intros Hp (E1 & E2 & _). rewrite <- E1, <- E2. intros ρ1.
  exists (kw_pull Hp (kw_glob ρ) (wf_ctx_dnf (kw_ctx ρ)) ρ1). apply kcorr_pull.
Qed.

Lemma PullL {π πi G} (Hp : uperm π πi (gL G)) lx lk :
  lequiv (gL (Gp π G)) lx (lvsubst lk (pφ π)) -> lequiv (gL G) (lvsubst lx (pφ πi)) lk.
Proof using .
  intros Hx. pose proof (pg_lequiv (G := Gp π G) (uperm_inv _ _ _ Hp) Hx) as X.
  rewrite (rt_lvl (proj1 Hp)) in X. exact X.
Qed.

Lemma MGeq_dnf {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C'} :
  MGeq G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' ->
  dnfty X /\ dnfty A /\ dnfty B /\ dnftm C /\ dnfty X' /\ dnfty A' /\ dnfty B' /\ dnftm C'.
Proof using EL.
  intros HG.
  pose proof (MEq_of_MGeq HG) as (_ & _ & _ & (_ & _ & _ & HX & HA & HB & HC) & _ & _ & _ & _ & HX' & HA' & HB' & HC').
  repeat split; first [exact (wf_ty_dnf HX) | exact (wf_ty_dnf HA) | exact (wf_ty_dnf HB) | exact (wf_tm_dnf HC)
                      | exact (wf_ty_dnf HX') | exact (wf_ty_dnf HA') | exact (wf_ty_dnf HB') | exact (wf_tm_dnf HC')].
Qed.

Lemma MAnn_dnf {G Γ l l' li X A B C j k k' ki X1 A1 B1 C1 j1} :
  MAnn G Γ l l' li X A B C j k k' ki X1 A1 B1 C1 j1 ->
  dnfty X1 /\ dnfty A1 /\ dnfty B1 /\ dnftm C1 /\ dnftm j1.
Proof using EL.
  intros (_ & _ & _ & HX & HA & HB & HC & Hj).
  exact (conj (wf_ty_dnf (eqty_wf_r ge_typeof HX)) (conj (wf_ty_dnf (eqty_wf_r ge_typeof HA))
          (conj (wf_ty_dnf (eqty_wf_r ge_typeof HB)) (conj (wf_tm_dnf (eqtm_wf_r ge_typeof HC))
            (wf_tm_dnf (eqtm_wf_r ge_typeof Hj)))))).
Qed.

Lemma MAnn_pg {π πi G} (Hp : uperm π πi (gL G)) {Γ l l' li X A B C j k k' ki X1 A1 B1 C1 j1} :
  MAnn G Γ l l' li X A B C j k k' ki X1 A1 B1 C1 j1 ->
  MAnn (Gp π G) Γ[pφ π]ᵤ (lvsubst l (pφ π)) (lvsubst l' (pφ π)) (lvsubst li (pφ π))
    X[pφ π]ᵤ A[pφ π]ᵤ B[pφ π]ᵤ C[pφ π]ᵤ j[pφ π]ᵤ (lvsubst k (pφ π)) (lvsubst k' (pφ π)) (lvsubst ki (pφ π))
    X1[pφ π]ᵤ A1[pφ π]ᵤ B1[pφ π]ᵤ C1[pφ π]ᵤ j1[pφ π]ᵤ.
Proof using EL.
  intros (H1 & H2 & H3 & EX & EA & EB & EC & Ej).
  pose proof (p_eqtm Hp EC) as EC'. rewrite !usubst_ren_ty in EC'.
  exact (conj (pg_lequiv Hp H1) (conj (pg_lequiv Hp H2) (conj (pg_lequiv Hp H3) (conj (pg_eqty Hp EX)
          (conj (pg_eqty Hp EA) (conj (pg_eqty Hp EB) (conj EC' (p_eqtm Hp Ej)))))))).
Qed.

(** [Π]'s relation along a permutation: the domain comes back, the
    codomain goes forward. *)
Lemma PiRel_pt {π πi G Γ l1 l2 l3 l4 A B A' B'} {domR : DomRel G Γ} {codR : CodRel G Γ domR}
    {G' Γ' k1 k2 k3 k4 A2 B2 A2' B2'} {domR' : DomRel G' Γ'} {codR' : CodRel G' Γ' domR'}
    (Hp : uperm π πi (gL G)) (HG : [ ⊢ G ]) (HΓ : dnfctx Γ) :
  Gp π G = G' -> Γ[pφ π]ᵤ = Γ' ->
  lvsubst l1 (pφ π) = k1 -> lvsubst l2 (pφ π) = k2 -> lvsubst l3 (pφ π) = k3 -> lvsubst l4 (pφ π) = k4 ->
  A[pφ π]ᵤ = A2 -> B[pφ π]ᵤ = B2 -> A'[pφ π]ᵤ = A2' -> B'[pφ π]ᵤ = B2' ->
  dnfty A -> dnfty B -> dnfty A' -> dnfty B' ->
  (forall (ρ : kwk G Γ) (ρ' : kwk G' Γ'), kcorr π ρ ρ' -> forall a a', domR' ρ' a a' ->
     dnftm a /\ dnftm a' /\ domR ρ a[pφ πi]ᵤ a'[pφ πi]ᵤ) ->
  (forall (ρ : kwk G Γ) (ρ' : kwk G' Γ'), kcorr π ρ ρ' ->
     forall a a' (h : domR ρ a a') b b' x x' (h' : domR' ρ' x x') y y',
     dnftm a -> dnftm a' -> x = a[pφ π]ᵤ -> x' = a'[pφ π]ᵤ -> y = b[pφ π]ᵤ -> y' = b'[pφ π]ᵤ ->
     codR ρ a a' h b b' -> codR' ρ' x x' h' y y') ->
  forall t t' u u', t[pφ π]ᵤ = u -> t'[pφ π]ᵤ = u' ->
  PiRel G Γ l1 l2 l3 l4 A B A' B' domR codR t t' -> PiRel G' Γ' k1 k2 k3 k4 A2 B2 A2' B2' domR' codR' u u'.
Proof using EL.
  intros EG EΓ E1 E2 E3 E4 EA EB EA' EB' NA NB NA' NB' Hb Hc t t' u u' Et Et'.
  subst G' Γ' k1 k2 k3 k4 A2 B2 A2' B2' u u'.
  pose proof (proj1 Hp) as Hinv. pose proof (proj1 (proj2 Hp)) as Hinv'.
  intros (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
  destruct (geq_tm_dnf Heq) as [Nw Nw'].
  exists w[pφ π]ᵤ, w'[pφ π]ᵤ.
  refine (conj (pg_tmred Hp Hw) (conj (pg_tmred Hp Hw') (conj (whnf_usubst _ _ Hnf)
            (conj (whnf_usubst _ _ Hnf') (conj (pg_geq_tm Hp Heq) (conj (pg_geq_tm Hp Heq') _)))))).
  intros ρ' a a' ha la lb la' lb' A1 B1 A1' B1' Hla Hlb Hla' Hlb' HA1 HB1 HA1' HB1'.
  pose proof (kcorr_pull Hp HG HΓ ρ') as Hk.
  destruct (Hb _ _ Hk a a' ha) as (Na & Na' & hx).
  destruct (geq_ty_dnf HA1) as [_ NA1]. destruct (geq_ty_dnf HB1) as [_ NB1].
  destruct (geq_ty_dnf HA1') as [_ NA1']. destruct (geq_ty_dnf HB1') as [_ NB1'].
  pose proof (pull_geq_kty Hp HG HΓ ρ' NA HA1) as HA1b. rewrite (rt_lvl Hinv) in HA1b.
  pose proof (pull_geq_ktyl Hp HG HΓ ρ' NA NB HB1) as HB1b. rewrite !(rt_lvl Hinv) in HB1b.
  pose proof (pull_geq_kty Hp HG HΓ ρ' NA' HA1') as HA1'b. rewrite (rt_lvl Hinv) in HA1'b.
  pose proof (pull_geq_ktyl Hp HG HΓ ρ' NA' NB' HB1') as HB1'b. rewrite !(rt_lvl Hinv) in HB1'b.
  pose proof (HK (kw_pull Hp HG HΓ ρ') _ _ hx _ _ _ _ _ _ _ _ (PullL Hp _ _ Hla) (PullL Hp _ _ Hlb)
                (PullL Hp _ _ Hla') (PullL Hp _ _ Hlb') HA1b HB1b HA1'b HB1'b) as X1.
  refine (Hc _ _ Hk _ _ hx _ _ _ _ ha _ _ (dnf_us_tm _ _) (dnf_us_tm _ _) _ _ _ _ X1).
  - now rewrite (rt_tm Hinv' _ Na).
  - now rewrite (rt_tm Hinv' _ Na').
  - rewrite usubst_app', (ktm_pull Hp HG HΓ ρ'), !(rt_lvl Hinv'), (rt_ty Hinv' _ NA1), (rt_ty Hinv' _ NB1),
      (rt_tm Hinv' _ Na). reflexivity.
  - rewrite usubst_app', (ktm_pull Hp HG HΓ ρ'), !(rt_lvl Hinv'), (rt_ty Hinv' _ NA1'), (rt_ty Hinv' _ NB1'),
      (rt_tm Hinv' _ Na'). reflexivity.
Qed.

(** [Σ]'s relation along a permutation: both components go forward. *)
Lemma SigRel_pt {π πi G Γ l1 l2 l3 l4 A B A' B'} {domR : DomRel G Γ} {codR : CodRel G Γ domR}
    {G' Γ' k1 k2 k3 k4 A2 B2 A2' B2'} {domR' : DomRel G' Γ'} {codR' : CodRel G' Γ' domR'}
    (Hp : uperm π πi (gL G)) (HG : [ ⊢ G ]) (HΓ : dnfctx Γ) :
  Gp π G = G' -> Γ[pφ π]ᵤ = Γ' ->
  lvsubst l1 (pφ π) = k1 -> lvsubst l2 (pφ π) = k2 -> lvsubst l3 (pφ π) = k3 -> lvsubst l4 (pφ π) = k4 ->
  A[pφ π]ᵤ = A2 -> B[pφ π]ᵤ = B2 -> A'[pφ π]ᵤ = A2' -> B'[pφ π]ᵤ = B2' ->
  dnfty A -> dnfty B -> dnfty A' -> dnfty B' ->
  (forall (ρ : kwk G Γ) (ρ' : kwk G' Γ'), kcorr π ρ ρ' -> forall a a' x x',
     dnftm a -> dnftm a' -> x = a[pφ π]ᵤ -> x' = a'[pφ π]ᵤ -> domR ρ a a' -> domR' ρ' x x') ->
  (forall (ρ : kwk G Γ) (ρ' : kwk G' Γ'), kcorr π ρ ρ' ->
     forall a a' (h : domR ρ a a') b b' x x' (h' : domR' ρ' x x') y y',
     dnftm a -> dnftm a' -> x = a[pφ π]ᵤ -> x' = a'[pφ π]ᵤ -> y = b[pφ π]ᵤ -> y' = b'[pφ π]ᵤ ->
     codR ρ a a' h b b' -> codR' ρ' x x' h' y y') ->
  forall t t' u u', t[pφ π]ᵤ = u -> t'[pφ π]ᵤ = u' ->
  SigRel G Γ l1 l2 l3 l4 A B A' B' domR codR t t' -> SigRel G' Γ' k1 k2 k3 k4 A2 B2 A2' B2' domR' codR' u u'.
Proof using EL.
  intros EG EΓ E1 E2 E3 E4 EA EB EA' EB' NA NB NA' NB' Hd Hc t t' u u' Et Et'.
  subst G' Γ' k1 k2 k3 k4 A2 B2 A2' B2' u u'.
  pose proof (proj1 Hp) as Hinv. pose proof (proj1 (proj2 Hp)) as Hinv'.
  intros (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
  destruct (geq_tm_dnf Heq) as [Nw Nw'].
  exists w[pφ π]ᵤ, w'[pφ π]ᵤ.
  refine (conj (pg_tmred Hp Hw) (conj (pg_tmred Hp Hw') (conj (whnf_usubst _ _ Hnf)
            (conj (whnf_usubst _ _ Hnf') (conj (pg_geq_tm Hp Heq) (conj (pg_geq_tm Hp Heq') _)))))).
  intros ρ' la lb la' lb' A1 B1 A1' B1' Hla Hlb Hla' Hlb' HA1 HB1 HA1' HB1'.
  pose proof (kcorr_pull Hp HG HΓ ρ') as Hk.
  destruct (geq_ty_dnf HA1) as [_ NA1]. destruct (geq_ty_dnf HB1) as [_ NB1].
  destruct (geq_ty_dnf HA1') as [_ NA1']. destruct (geq_ty_dnf HB1') as [_ NB1'].
  pose proof (pull_geq_kty Hp HG HΓ ρ' NA HA1) as HA1b. rewrite (rt_lvl Hinv) in HA1b.
  pose proof (pull_geq_ktyl Hp HG HΓ ρ' NA NB HB1) as HB1b. rewrite !(rt_lvl Hinv) in HB1b.
  pose proof (pull_geq_kty Hp HG HΓ ρ' NA' HA1') as HA1'b. rewrite (rt_lvl Hinv) in HA1'b.
  pose proof (pull_geq_ktyl Hp HG HΓ ρ' NA' NB' HB1') as HB1'b. rewrite !(rt_lvl Hinv) in HB1'b.
  destruct (HK (kw_pull Hp HG HΓ ρ') _ _ _ _ _ _ _ _ (PullL Hp _ _ Hla) (PullL Hp _ _ Hlb)
              (PullL Hp _ _ Hla') (PullL Hp _ _ Hlb') HA1b HB1b HA1'b HB1'b) as (h & X1).
  assert (Na : dnftm (tmFst (lvsubst la (pφ πi)) (lvsubst lb (pφ πi)) A1[pφ πi]ᵤ B1[pφ πi]ᵤ
                        (ktm (kw_pull Hp HG HΓ ρ') w)))
    by (cbn; repeat split; auto using dnf_ktm, dnf_us_tm, dnf_us_ty).
  assert (Na' : dnftm (tmFst (lvsubst la' (pφ πi)) (lvsubst lb' (pφ πi)) A1'[pφ πi]ᵤ B1'[pφ πi]ᵤ
                         (ktm (kw_pull Hp HG HΓ ρ') w')))
    by (cbn; repeat split; auto using dnf_ktm, dnf_us_tm, dnf_us_ty).
  assert (Ex : tmFst la lb A1 B1 (ktm ρ' w[pφ π]ᵤ) =
               (tmFst (lvsubst la (pφ πi)) (lvsubst lb (pφ πi)) A1[pφ πi]ᵤ B1[pφ πi]ᵤ
                  (ktm (kw_pull Hp HG HΓ ρ') w))[pφ π]ᵤ)
    by (rewrite usubst_fst', (ktm_pull Hp HG HΓ ρ'), !(rt_lvl Hinv'), (rt_ty Hinv' _ NA1), (rt_ty Hinv' _ NB1);
        reflexivity).
  assert (Ex' : tmFst la' lb' A1' B1' (ktm ρ' w'[pφ π]ᵤ) =
                (tmFst (lvsubst la' (pφ πi)) (lvsubst lb' (pφ πi)) A1'[pφ πi]ᵤ B1'[pφ πi]ᵤ
                   (ktm (kw_pull Hp HG HΓ ρ') w'))[pφ π]ᵤ)
    by (rewrite usubst_fst', (ktm_pull Hp HG HΓ ρ'), !(rt_lvl Hinv'), (rt_ty Hinv' _ NA1'), (rt_ty Hinv' _ NB1');
        reflexivity).
  pose proof (Hd _ _ Hk _ _ _ _ Na Na' Ex Ex' h) as h'.
  exists h'. refine (Hc _ _ Hk _ _ h _ _ _ _ h' _ _ Na Na' Ex Ex' _ _ X1).
  - rewrite usubst_snd', (ktm_pull Hp HG HΓ ρ'), !(rt_lvl Hinv'), (rt_ty Hinv' _ NA1), (rt_ty Hinv' _ NB1).
    reflexivity.
  - rewrite usubst_snd', (ktm_pull Hp HG HΓ ρ'), !(rt_lvl Hinv'), (rt_ty Hinv' _ NA1'), (rt_ty Hinv' _ NB1').
    reflexivity.
Qed.

Lemma dnf_mKidTy l l' li (X A B : ty) (C j : tm) :
  dnfty X -> dnfty A -> dnfty B -> dnftm C -> dnftm j -> dnfty (mKidTy l l' li X A B C j).
Proof using .
  intros NX NA NB NC Nj. cbn [dnfty].
  repeat split; auto using ren_dnf, ren_dnf_ty.
  apply subst_dnf; [exact NC | exact (lk_dnf_llift _ (lk_dnf_llift _ (lk_dnf_lsingle _ Nj)))].
Qed.

(** The shapes' relation forward, the positions' backward, along
    corresponding worlds, at related indices and shapes. *)
Definition STr (π : nat -> nat) {G Γ G' Γ'} (I : DomRel G Γ) (S : MShRel G Γ) (S' : MShRel G' Γ') : Prop :=
  forall (ρ : kwk G Γ) (ρ' : kwk G' Γ'), kcorr π ρ ρ' -> forall x y a b,
    dnftm x -> dnftm y -> dnftm a -> dnftm b -> I ρ x y -> S ρ x y a b ->
    S' ρ' x[pφ π]ᵤ y[pφ π]ᵤ a[pφ π]ᵤ b[pφ π]ᵤ.
Definition PTr (π πi : nat -> nat) {G Γ G' Γ'} (I : DomRel G Γ) (S : MShRel G Γ) (P : MPosRel G Γ)
    (P' : MPosRel G' Γ') : Prop :=
  forall (ρ : kwk G Γ) (ρ' : kwk G' Γ'), kcorr π ρ ρ' -> forall x y a b,
    dnftm x -> dnftm y -> dnftm a -> dnftm b -> I ρ x y -> S ρ x y a b ->
    forall p q, P' ρ' x[pφ π]ᵤ y[pφ π]ᵤ a[pφ π]ᵤ b[pφ π]ᵤ p q ->
    dnftm p /\ dnftm q /\ P ρ x y a b p[pφ πi]ᵤ q[pφ πi]ᵤ.

Lemma STr_comp {π G Γ G' Γ'} {ρ : kwk G Γ} {ρ' : kwk G' Γ'} (Hk : kcorr π ρ ρ')
    {I : DomRel G Γ} {S : MShRel G Γ} {S' : MShRel G' Γ'} :
  STr π I S S' -> STr π (fun ρ0 => I (kw_comp ρ ρ0)) (fun ρ0 => S (kw_comp ρ ρ0)) (fun ρ0' => S' (kw_comp ρ' ρ0')).
Proof using . intros H ρ0 ρ0' Hk1. exact (H _ _ (kcorr_comp Hk _ _ Hk1)). Qed.
Lemma PTr_comp {π πi G Γ G' Γ'} {ρ : kwk G Γ} {ρ' : kwk G' Γ'} (Hk : kcorr π ρ ρ')
    {I : DomRel G Γ} {S : MShRel G Γ} {P : MPosRel G Γ} {P' : MPosRel G' Γ'} :
  PTr π πi I S P P' -> PTr π πi (fun ρ0 => I (kw_comp ρ ρ0)) (fun ρ0 => S (kw_comp ρ ρ0))
    (fun ρ0 => P (kw_comp ρ ρ0)) (fun ρ0' => P' (kw_comp ρ' ρ0')).
Proof using . intros H ρ0 ρ0' Hk1. exact (H _ _ (kcorr_comp Hk _ _ Hk1)). Qed.

Definition MPermAt (π πi : nat -> nat) n := forall G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' I S P m m',
  MSide G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' I S P -> dnftm m -> dnftm m' ->
  (forall ρ, I ρ (ktm ρ m) (ktm ρ m')) -> uperm π πi (gL G) ->
  forall G' Γ' X2 A2 B2 C2 X2' A2' B2' C2' m2 m2' (S' : MShRel G' Γ') (P' : MPosRel G' Γ'),
  Gp π G = G' -> Γ[pφ π]ᵤ = Γ' -> X[pφ π]ᵤ = X2 -> A[pφ π]ᵤ = A2 -> B[pφ π]ᵤ = B2 -> C[pφ π]ᵤ = C2 ->
  X'[pφ π]ᵤ = X2' -> A'[pφ π]ᵤ = A2' -> B'[pφ π]ᵤ = B2' -> C'[pφ π]ᵤ = C2' ->
  m[pφ π]ᵤ = m2 -> m'[pφ π]ᵤ = m2' -> STr π I S S' -> PTr π πi I S P P' ->
  forall t t', MRn n G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' S P m m' t t' ->
    MRn n G' Γ' (lvsubst l1 (pφ π)) (lvsubst l2 (pφ π)) (lvsubst li (pφ π)) X2 A2 B2 C2
      (lvsubst r1 (pφ π)) (lvsubst r2 (pφ π)) (lvsubst ri (pφ π)) X2' A2' B2' C2' S' P' m2 m2'
      t[pφ π]ᵤ t'[pφ π]ᵤ.

(** The observations, given the children's: the target's annotations
    come back along the inverse. *)
Lemma MObs_pt {π πi} n (IH : MPermAt π πi n) {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' I S P m m'} :
  MSide G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' I S P -> dnftm m -> dnftm m' ->
  (forall ρ, I ρ (ktm ρ m) (ktm ρ m')) -> uperm π πi (gL G) ->
  forall G' Γ' X2 A2 B2 C2 X2' A2' B2' C2' m2 m2' (S' : MShRel G' Γ') (P' : MPosRel G' Γ'),
  Gp π G = G' -> Γ[pφ π]ᵤ = Γ' -> X[pφ π]ᵤ = X2 -> A[pφ π]ᵤ = A2 -> B[pφ π]ᵤ = B2 -> C[pφ π]ᵤ = C2 ->
  X'[pφ π]ᵤ = X2' -> A'[pφ π]ᵤ = A2' -> B'[pφ π]ᵤ = B2' -> C'[pφ π]ᵤ = C2' ->
  m[pφ π]ᵤ = m2 -> m'[pφ π]ᵤ = m2' -> STr π I S S' -> PTr π πi I S P P' ->
  forall t t', MObs (MRn n) G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' S P m m' t t' ->
    MObs (MRn n) G' Γ' (lvsubst l1 (pφ π)) (lvsubst l2 (pφ π)) (lvsubst li (pφ π)) X2 A2 B2 C2
      (lvsubst r1 (pφ π)) (lvsubst r2 (pφ π)) (lvsubst ri (pφ π)) X2' A2' B2' C2' S' P' m2 m2'
      t[pφ π]ᵤ t'[pφ π]ᵤ.
Proof using EL.
  intros HM Nm Nm' Im Hp G' Γ' X2 A2 B2 C2 X2' A2' B2' C2' m2 m2' S' P' EG EΓ EX EA EB EC EX' EA' EB' EC'
    Em Em' HS HP t t' H.
  subst G' Γ' X2 A2 B2 C2 X2' A2' B2' C2' m2 m2'.
  pose proof (proj1 Hp) as Hinv. pose proof (proj1 (proj2 Hp)) as Hinv'.
  pose proof (uperm_inv _ _ _ Hp) as Hpi.
  pose proof (MGeq_ctx (ms_geq HM)) as HΓw. pose proof (ctx_glob _ _ _ HΓw) as HG.
  pose proof (wf_ctx_dnf HΓw) as HΓ.
  pose proof (dnftm_nftm _ Nm) as Fm. pose proof (dnftm_nftm _ Nm') as Fm'.
  destruct (MGeq_dnf (ms_geq HM)) as (NX & NA & NB & NC & NX' & NA' & NB' & NC').
  intros k1 k2 ki X1 A1 B1 C1 j1 k1' k2' ki' X1' A1' B1' C1' j1' Ann Ann'.
  destruct (MAnn_dnf Ann) as (NX1 & NA1 & NB1 & NC1 & Nj1).
  destruct (MAnn_dnf Ann') as (NX1' & NA1' & NB1' & NC1' & Nj1').
  pose proof (MAnn_pg (G := Gp π G) Hpi Ann) as Annb. pose proof (MAnn_pg (G := Gp π G) Hpi Ann') as Annb'.
  rewrite (Gp_rt Hp HG), (rt_ctx Hinv _ HΓ), !(rt_lvl Hinv), (rt_ty Hinv _ NX), (rt_ty Hinv _ NA),
    (rt_ty Hinv _ NB), (rt_tm Hinv _ NC), (rt_tm Hinv _ Nm) in Annb.
  rewrite (Gp_rt Hp HG), (rt_ctx Hinv _ HΓ), !(rt_lvl Hinv), (rt_ty Hinv _ NX'), (rt_ty Hinv _ NA'),
    (rt_ty Hinv _ NB'), (rt_tm Hinv _ NC'), (rt_tm Hinv _ Nm') in Annb'.
  specialize (H _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Annb Annb').
  assert (Hupρ : forall ρ : kwk G Γ, uperm π πi (gL (kw_G ρ))) by (intros ρ; exact (uperm_grow _ _ _ _ (kw_gL ρ) Hp)).
  refine (SigRel_pt Hp HG HΓ eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl (usubst_lsingle_ty' _ _ _) _
            (usubst_lsingle_ty' _ _ _) _ (subst_dnf_ty _ _ NA (lk_dnf_lsingle _ Nm)) _
            (subst_dnf_ty _ _ NA' (lk_dnf_lsingle _ Nm')) _ _ _ _ _ _ _ _ _ H).
  - rewrite usubst_tyPi', usubst_llift_single_ty, usubst_mKidTy. reflexivity.
  - rewrite usubst_tyPi', usubst_llift_single_ty, usubst_mKidTy. reflexivity.
  - cbn [dnfty]. split; [apply subst_dnf_ty; [exact NB | exact (lk_dnf_llift _ (lk_dnf_lsingle _ Nm))] |].
    apply dnf_mKidTy; assumption.
  - cbn [dnfty]. split; [apply subst_dnf_ty; [exact NB' | exact (lk_dnf_llift _ (lk_dnf_lsingle _ Nm'))] |].
    apply dnf_mKidTy; assumption.
  - (* the shapes *)
    intros ρ ρ' Hk x y x' y' Nx Ny Ex Ey h. subst x' y'. cbn beta in h |- *.
    pose proof (HS ρ ρ' Hk _ _ x y (dnf_ktm _ _ Nm) (dnf_ktm _ _ Nm') Nx Ny (Im ρ) h) as Y.
    rewrite !(kcorr_ktm Hk) in Y. exact Y.
  - (* the children's functions *)
    intros ρ ρ' Hk a a' h b b' x x' h' y y' Na Na' Ex Ex' Ey Ey' Hcod. subst x x'. cbn beta in h, Hcod |- *.
    refine (PiRel_pt (Hupρ ρ) (kw_glob ρ) (wf_ctx_dnf (kw_ctx ρ)) (proj1 Hk) (proj1 (proj2 Hk))
              eq_refl eq_refl eq_refl eq_refl _ _ _ _ _ _ _ _ _ _ b b' y y' (eq_sym Ey) (eq_sym Ey') Hcod).
    + rewrite usubst_lsingle_ty', (kcorr_ktyl Hk), usubst_llift_single_ty. reflexivity.
    + rewrite usubst_llift_single_ty, (kcorr_ktyll Hk), usubst_mKidTy. reflexivity.
    + rewrite usubst_lsingle_ty', (kcorr_ktyl Hk), usubst_llift_single_ty. reflexivity.
    + rewrite usubst_llift_single_ty, (kcorr_ktyll Hk), usubst_mKidTy. reflexivity.
    + apply subst_dnf_ty; [| exact (lk_dnf_lsingle _ Na)].
      apply dnf_ktyl, subst_dnf_ty; [exact NB | exact (lk_dnf_llift _ (lk_dnf_lsingle _ Nm))].
    + apply subst_dnf_ty; [| exact (lk_dnf_llift _ (lk_dnf_lsingle _ Na))]. apply dnf_ktyll, dnf_mKidTy; assumption.
    + apply subst_dnf_ty; [| exact (lk_dnf_lsingle _ Na')].
      apply dnf_ktyl, subst_dnf_ty; [exact NB' | exact (lk_dnf_llift _ (lk_dnf_lsingle _ Nm'))].
    + apply subst_dnf_ty; [| exact (lk_dnf_llift _ (lk_dnf_lsingle _ Na'))]. apply dnf_ktyll, dnf_mKidTy; assumption.
    + (* the positions come back *)
      intros ρ1 ρ1' Hk1 p q hp. cbn beta in hp |- *.
      pose proof (kcorr_comp Hk _ _ Hk1) as Hkc.
      assert (Sh : S (kw_comp ρ ρ1) (ktm (kw_comp ρ ρ1) m) (ktm (kw_comp ρ ρ1) m') (ktm ρ1 a) (ktm ρ1 a'))
        by (rewrite !(ktm_comp ρ ρ1); exact (ms_shmon HM ρ ρ1 _ _ _ _ (Im ρ) h)).
      apply (HP _ _ Hkc _ _ _ _ (dnf_ktm _ _ Nm) (dnf_ktm _ _ Nm') (dnf_ktm _ _ Na) (dnf_ktm _ _ Na') (Im _) Sh).
      rewrite !(kcorr_ktm Hkc), !(kcorr_ktm Hk1). exact hp.
    + (* the children: the induction hypothesis *)
      intros ρ1 ρ1' Hk1 p q hp z z' p' q' hp' w w' Np Nq Ep Eq Ew Ew' Hz. subst p' q' w w'. cbn beta in hp, Hz |- *.
      pose proof (kcorr_comp Hk _ _ Hk1) as Hkc.
      destruct (MSide_child ρ ρ1 a a' p q HM Fm Fm' Im h hp) as (_ & _ & J).
      assert (Ec : ((ktmlll (kw_comp ρ ρ1) C)[lsingle3 (ktm (kw_comp ρ ρ1) m) (ktm ρ1 a) p])[pφ π]ᵤ =
                   (ktmlll (kw_comp ρ' ρ1') C[pφ π]ᵤ)[lsingle3 (ktm (kw_comp ρ' ρ1') m[pφ π]ᵤ) (ktm ρ1' a[pφ π]ᵤ) p[pφ π]ᵤ])
        by (rewrite usubst_lsingle3, (kcorr_ktmlll Hkc), (kcorr_ktm Hkc), (kcorr_ktm Hk1); reflexivity).
      assert (Ec' : ((ktmlll (kw_comp ρ ρ1) C')[lsingle3 (ktm (kw_comp ρ ρ1) m') (ktm ρ1 a') q])[pφ π]ᵤ =
                    (ktmlll (kw_comp ρ' ρ1') C'[pφ π]ᵤ)[lsingle3 (ktm (kw_comp ρ' ρ1') m'[pφ π]ᵤ) (ktm ρ1' a'[pφ π]ᵤ) q[pφ π]ᵤ])
        by (rewrite usubst_lsingle3, (kcorr_ktmlll Hkc), (kcorr_ktm Hkc), (kcorr_ktm Hk1); reflexivity).
      exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MSide_kw (kw_comp ρ ρ1) HM)
               (subst_dnf _ _ (dnf_ktmlll _ _ NC) (lk_dnf_lsingle3 _ _ _ (dnf_ktm _ _ Nm) (dnf_ktm _ _ Na) Np))
               (subst_dnf _ _ (dnf_ktmlll _ _ NC') (lk_dnf_lsingle3 _ _ _ (dnf_ktm _ _ Nm') (dnf_ktm _ _ Na') Nq))
               J (uperm_grow _ _ _ _ (kw_gL ρ1) (Hupρ ρ)) (kw_G ρ1') (kw_Δ ρ1') _ _ _ _ _ _ _ _ _ _ _ _
               (proj1 Hk1) (proj1 (proj2 Hk1)) (kcorr_kty Hkc X) (kcorr_ktyl Hkc A) (kcorr_ktyll Hkc B)
               (kcorr_ktmlll Hkc C) (kcorr_kty Hkc X') (kcorr_ktyl Hkc A') (kcorr_ktyll Hkc B')
               (kcorr_ktmlll Hkc C') Ec Ec' (STr_comp Hkc HS) (PTr_comp Hkc HP) z z' Hz).
  - rewrite usubst_out', !(rt_lvl Hinv'), (rt_ty Hinv' _ NX1), (rt_ty Hinv' _ NA1), (rt_ty Hinv' _ NB1),
      (rt_tm Hinv' _ NC1), (rt_tm Hinv' _ Nj1). reflexivity.
  - rewrite usubst_out', !(rt_lvl Hinv'), (rt_ty Hinv' _ NX1'), (rt_ty Hinv' _ NA1'), (rt_ty Hinv' _ NB1'),
      (rt_tm Hinv' _ NC1'), (rt_tm Hinv' _ Nj1'). reflexivity.
Qed.

Lemma MRn_perm π πi n : MPermAt π πi n.
Proof using EL.
  induction n as [|n IH]; intros G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' I S P m m' HM Nm Nm' Im Hp
    G' Γ' X2 A2 B2 C2 X2' A2' B2' C2' m2 m2' S' P' EG EΓ EX EA EB EC EX' EA' EB' EC' Em Em' HS HP t t'
    [Hgen Hobs].
  all: split; [subst; destruct Hgen as (w & w' & R1 & R2 & W1 & W2 & E1 & E2); exists w[pφ π]ᵤ, w'[pφ π]ᵤ;
               exact (conj (pg_tmred Hp R1) (conj (pg_tmred Hp R2) (conj (whnf_usubst _ _ W1)
                 (conj (whnf_usubst _ _ W2) (conj (pg_geq_tm Hp E1) (pg_geq_tm Hp E2)))))) |].
  - exact Logic.I.
  - subst G' Γ' X2 A2 B2 C2 X2' A2' B2' C2' m2 m2'.
    pose proof (MGeq_ctx (ms_geq HM)) as HΓw. pose proof (ctx_glob _ _ _ HΓw) as HG.
    pose proof (wf_ctx_dnf HΓw) as HΓ.
    intros ρ'. pose proof (kcorr_pull Hp HG HΓ ρ') as Hk. set (ρ := kw_pull Hp HG HΓ ρ') in Hk.
    pose proof (MObs_pt n IH (MSide_kw ρ HM) (dnf_ktm _ _ Nm) (dnf_ktm _ _ Nm') (MIdx_kw ρ Im)
                  (uperm_grow _ _ _ _ (kw_gL ρ) Hp) (kw_G ρ') (kw_Δ ρ') _ _ _ _ _ _ _ _ _ _ _ _
                  (proj1 Hk) (proj1 (proj2 Hk)) (kcorr_kty Hk X) (kcorr_ktyl Hk A) (kcorr_ktyll Hk B)
                  (kcorr_ktmlll Hk C) (kcorr_kty Hk X') (kcorr_ktyl Hk A') (kcorr_ktyll Hk B')
                  (kcorr_ktmlll Hk C') (kcorr_ktm Hk m) (kcorr_ktm Hk m') (STr_comp Hk HS) (PTr_comp Hk HP)
                  _ _ (Hobs ρ)) as Y.
    rewrite !(kcorr_ktm Hk) in Y. exact Y.
Qed.


Lemma LR_perm_step n : (forall m, m < n -> Pperm m) -> Pperm n.
Proof using EL VL VPP.
  intros IHn G Γ T T' l R H.
  induction H as [G Γ T T' l R Hl HT HT' HR
                 | G Γ T T' l l1 l2 R Hl Hl2 Hn HT HT' HR
                 | G Γ T T' l V V' R HT HT' HV HR
                 | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R P domAd IHdom codAd IHcod HR
                 | G Γ T T' l R Hj HM
                 | G Γ T T' l l1 l2 T1 T1' instR R Hj Hl Hl2 Hw1 HT HT' HT1 HT1' Hgeq instAd IHinst HR
                 | G Γ T T' l Δ1 Δ1' l1 l2 l3 l4 T1 T1' instR R Hj Hl Hl3 Hl4 Hw1 Hw2 HT HT' HΔ HT1 HT1'
                     Hgeq instAd IHinst HR
                 | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R P domAd IHdom codAd IHcod HR
                 | G Γ T T' l l1 l2 R Hl Hl2 Hw HT HT' HR
                 | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                 | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA IHRA Hra Hrb Hps Hpt HR
                 | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                 | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                     HRA IHRA HRB IHRB Hpa Hta Hpb Htb HR
                 | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R P domAd IHdom codAd IHcod HR
                 | G Γ T T' l l1 l2 A A' N N' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN
                     domAd IHdom arAd HR
                 | G Γ T T' l l1 l2 A A' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ IHRQ Hqs Hqt HR
                 | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                     HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                     widxAd IHwidx Hwisym Hwistr wdomAd IHwdom warAd wotAd wchAd wixAd HR
                 | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                     Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                     HmXX HmAA HmBB HmCC Hmmm midxAd IHmidx mshAd IHmsh mposAd IHmpos mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR];
    intros π πi Hp;
    pose proof (uperm_inv _ _ _ Hp) as Hpi;
    pose proof (proj1 Hp) as Hinv; pose proof (proj1 (proj2 Hp)) as Hinv';
    try (destruct (tyred_glob HT) as (HG & HΓ & NT & NW);
         destruct (tyred_glob HT') as (_ & _ & NT' & NW');
         pose proof (p_glob Hp HG) as HG').
  - (* Nat *)
    exists (NatRel (Gp π G) Γ[pφ π]ᵤ). split.
    + eapply LRnat; [exact (pg_lequiv Hp Hl) | exact (pg_tyred Hp HT) | exact (pg_tyred Hp HT') | apply releq_refl].
    + intros t t' Nt Nt'. rewrite (HR t t'). split; [apply (NatRel_perm Hp) |].
      intros X. apply (NatRel_perm (G := Gp π G) Hpi) in X.
      rewrite (Gp_rt Hp HG), (rt_ctx Hinv _ HΓ), !(rt_tm Hinv) in X by assumption. exact X.
  - (* U *)
    assert (Hn' : lmeasure (lvsubst l1 (pφ π)) < n) by (rewrite lmeasure_perm; exact Hn).
    exists (URel (LRbelow n) (Gp π G) Γ[pφ π]ᵤ (lvsubst l1 (pφ π))). split.
    + eapply LRU; [exact (pg_lequiv Hp Hl) | exact (pg_lequiv Hp Hl2) | exact Hn' | exact (pg_tyred Hp HT)
                  | exact (pg_tyred Hp HT') | apply releq_refl].
    + intros t t' Nt Nt'. rewrite (HR t t'). split; [apply (URel_perm n IHn Hn Hp) |].
      intros X. apply (URel_perm (G := Gp π G) n IHn Hn' Hpi) in X.
      rewrite (Gp_rt Hp HG), (rt_ctx Hinv _ HΓ), (rt_lvl Hinv), !(rt_tm Hinv) in X by assumption. exact X.
  - (* neutral *)
    exists (NeRel (Gp π G) Γ[pφ π]ᵤ V[pφ π]ᵤ V'[pφ π]ᵤ (lvsubst l (pφ π))). split.
    + eapply LRne; [exact (pg_tyred Hp HT) | exact (pg_tyred Hp HT') | exact (pg_gne_ty Hp HV) | apply releq_refl].
    + intros t t' Nt Nt'. rewrite (HR t t'). split; [apply (NeRel_perm Hp) |].
      intros X. apply (NeRel_perm (G := Gp π G) Hpi) in X.
      rewrite (Gp_rt Hp HG), (rt_ctx Hinv _ HΓ), (rt_lvl Hinv), !(rt_ty Hinv), !(rt_tm Hinv) in X by assumption.
      exact X.
  - (* Π *)
    pose proof (poly_pg Hp (fun _ _ _ _ _ => eq_refl) P) as P'.
    destruct P as [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB].
    destruct (tyred_glob HT) as (HG & HΓ & NT & NW); destruct (tyred_glob HT') as (_ & _ & NT' & NW');
    pose proof (p_glob Hp HG) as HG'.
    set (Aπ := A[pφ π]ᵤ). set (A'π := A'[pφ π]ᵤ). set (Bπ := B[pφ π]ᵤ). set (B'π := B'[pφ π]ᵤ).
    set (k1 := lvsubst l1 (pφ π)). set (k2 := lvsubst l2 (pφ π)).
    pose proof (wf_ty_dnf HA) as NA. pose proof (wf_ty_dnf HA') as NA'.
    pose proof (wf_ty_dnf HB) as NB. pose proof (wf_ty_dnf HB') as NB'.
    set (domR' := fun (ρ' : kwk (Gp π G) Γ[pφ π]ᵤ) a a' =>
           exists Rd, LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (kty ρ' Aπ) (kty ρ' A'π) k1 Rd /\ Rd a a').
    set (codR' := fun (ρ' : kwk (Gp π G) Γ[pφ π]ᵤ) a a' (_ : domR' ρ' a a') b b' =>
           exists Rc, LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (ktyl ρ' Bπ)[lsingle a] (ktyl ρ' B'π)[lsingle a'] k2 Rc
             /\ Rc b b').
    (* the domains at a world of the permuted context, through its pull-back *)
    assert (Dom : forall ρ', exists Rd,
               LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (kty ρ' Aπ) (kty ρ' A'π) k1 Rd /\
               forall x y, dnftm x -> dnftm y -> (domR (kw_pull Hp HG HΓ ρ') x y <-> Rd x[pφ π]ᵤ y[pφ π]ᵤ)).
    { intros ρ'.
      assert (Hpρ : uperm π πi (gL (kw_G (kw_pull Hp HG HΓ ρ')))) by exact (uperm_grow _ _ _ _ (kw_gL ρ') Hp).
      destruct (IHdom (kw_pull Hp HG HΓ ρ') π πi Hpρ) as (Rd & HRd & ERd).
      rewrite (pull_G Hp HG HΓ ρ'), (pull_Δ Hp HG HΓ ρ'), !(kty_pull Hp HG HΓ ρ') in HRd.
      exists Rd. exact (conj HRd ERd). }
    assert (Cod : forall ρ' x x' (hx : domR (kw_pull Hp HG HΓ ρ') x x'), exists Rc,
               LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (ktyl ρ' Bπ)[lsingle x[pφ π]ᵤ] (ktyl ρ' B'π)[lsingle x'[pφ π]ᵤ]
                 k2 Rc /\
               forall y y', dnftm y -> dnftm y' ->
                 (codR (kw_pull Hp HG HΓ ρ') x x' hx y y' <-> Rc y[pφ π]ᵤ y'[pφ π]ᵤ)).
    { intros ρ' x x' hx.
      assert (Hpρ : uperm π πi (gL (kw_G (kw_pull Hp HG HΓ ρ')))) by exact (uperm_grow _ _ _ _ (kw_gL ρ') Hp).
      destruct (IHcod (kw_pull Hp HG HΓ ρ') x x' hx π πi Hpρ) as (Rc & HRc & ERc).
      rewrite (pull_G Hp HG HΓ ρ'), (pull_Δ Hp HG HΓ ρ'), !usubst_lsingle_ty', !(ktyl_pull Hp HG HΓ ρ') in HRc.
      exists Rc. exact (conj HRc ERc). }
    (* a related pair of the permuted domain comes from one of the original *)
    assert (Back : forall ρ' a a', domR' ρ' a a' ->
               dnftm a /\ dnftm a' /\ domR (kw_pull Hp HG HΓ ρ') a[pφ πi]ᵤ a'[pφ πi]ᵤ).
    { intros ρ' a a' (Rd2 & H2 & h2). destruct (Dom ρ') as (Rd & HRd & ERd).
      destruct (LR_rel_dnf H2 _ _ h2) as [Na Na'].
      pose proof (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRd H2 a a') h2) as h.
      refine (conj Na (conj Na' _)). apply (ERd _ _ (dnf_us_tm _ _) (dnf_us_tm _ _)).
      rewrite !(rt_tm Hinv') by assumption. exact h. }
    assert (Hdom' : forall ρ', LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (kty ρ' Aπ) (kty ρ' A'π) k1 (domR' ρ')).
    { intros ρ'. destruct (Dom ρ') as (Rd & HRd & _). refine (LR_releq _ _ _ _ _ _ _ _ _ HRd _).
      intros a a'; split; [intros h; exists Rd; exact (conj HRd h) |].
      intros (Rd2 & H2 & h2). exact (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRd H2 a a') h2). }
    assert (Hcod' : forall ρ' a a' (ha : domR' ρ' a a'),
               LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (ktyl ρ' Bπ)[lsingle a] (ktyl ρ' B'π)[lsingle a'] k2
                 (codR' ρ' a a' ha)).
    { intros ρ' a a' ha. destruct (Back ρ' a a' ha) as (Na & Na' & hx).
      destruct (Cod ρ' _ _ hx) as (Rc & HRc & _). rewrite !(rt_tm Hinv') in HRc by assumption.
      refine (LR_releq _ _ _ _ _ _ _ _ _ HRc _).
      intros b b'; split; [intros h; exists Rc; exact (conj HRc h) |].
      intros (Rc2 & H2 & h2). exact (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRc H2 b b') h2). }
    exists (PiRel (Gp π G) Γ[pφ π]ᵤ k1 k2 (lvsubst l3 (pφ π)) (lvsubst l4 (pφ π)) Aπ Bπ A'π B'π domR' codR').
    split.
    + apply (LRpi n (LRbelow n) (Gp π G) Γ[pφ π]ᵤ T[pφ π]ᵤ T'[pφ π]ᵤ (lvsubst l (pφ π)) k1 k2
               (lvsubst l3 (pφ π)) (lvsubst l4 (pφ π)) Aπ Bπ A'π B'π domR' codR').
      * exact P'.
      * exact Hdom'.
      * exact Hcod'.
      * apply releq_refl.
    + subst codR' domR' Aπ A'π Bπ B'π k1 k2.
      intros t t' Nt Nt'. rewrite (HR t t'). split.
      * intros (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
        destruct (geq_tm_dnf Heq) as [Nw Nw'].
        exists w[pφ π]ᵤ, w'[pφ π]ᵤ.
        refine (conj (pg_tmred Hp Hw) (conj (pg_tmred Hp Hw') (conj (whnf_usubst _ _ Hnf)
                  (conj (whnf_usubst _ _ Hnf') (conj (pg_geq_tm Hp Heq) (conj (pg_geq_tm Hp Heq') _)))))).
        intros ρ' a a' ha la lb la' lb' A1 B1 A1' B1' Hla Hlb Hla' Hlb' HA1 HB1 HA1' HB1'.
        destruct (Back ρ' a a' ha) as (Na & Na' & hx).
        assert (PullL : forall lx lk, lequiv (gL (Gp π G)) lx (lvsubst lk (pφ π)) ->
                          lequiv (gL G) (lvsubst lx (pφ πi)) lk).
        { intros lx lk Hx. pose proof (pg_lequiv (G := Gp π G) Hpi Hx) as X. rewrite (rt_lvl Hinv) in X. exact X. }
        destruct (geq_ty_dnf HA1) as [_ NA1]. destruct (geq_ty_dnf HB1) as [_ NB1].
        destruct (geq_ty_dnf HA1') as [_ NA1']. destruct (geq_ty_dnf HB1') as [_ NB1'].
        pose proof (pull_geq_kty Hp HG HΓ ρ' NA HA1) as HA1b. rewrite (rt_lvl Hinv) in HA1b.
        pose proof (pull_geq_ktyl Hp HG HΓ ρ' NA NB HB1) as HB1b. rewrite !(rt_lvl Hinv) in HB1b.
        pose proof (pull_geq_kty Hp HG HΓ ρ' NA' HA1') as HA1'b. rewrite (rt_lvl Hinv) in HA1'b.
        pose proof (pull_geq_ktyl Hp HG HΓ ρ' NA' NB' HB1') as HB1'b. rewrite !(rt_lvl Hinv) in HB1'b.
        pose proof (HK (kw_pull Hp HG HΓ ρ') _ _ hx _ _ _ _ _ _ _ _ (PullL _ _ Hla) (PullL _ _ Hlb)
                      (PullL _ _ Hla') (PullL _ _ Hlb') HA1b HB1b HA1'b HB1'b) as X1.
        destruct (Cod ρ' _ _ hx) as (Rc & HRc & ERc).
        apply ERc in X1;
          [| cbn; repeat split; auto using dnf_ktm, dnf_us_tm, dnf_us_ty ..].
        rewrite !usubst_app', !(ktm_pull Hp HG HΓ ρ'), !(rt_lvl Hinv'), !(rt_ty Hinv'), !(rt_tm Hinv') in X1
          by assumption.
        rewrite !(rt_tm Hinv') in HRc by assumption.
        exists Rc. exact (conj HRc X1).
      * intros (w0 & w0' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
        destruct (geq_tm_dnf Heq) as [Nw0 Nw0'].
        assert (NP : dnfty (tyPi l1 l2 A B)) by (cbn; auto).
        assert (NP' : dnfty (tyPi l3 l4 A' B')) by (cbn; auto).
        exists w0[pφ πi]ᵤ, w0'[pφ πi]ᵤ.
        refine (conj (pull_tmred (T := tyPi l1 l2 A B) (l := lmax l1 l2) Hp HG HΓ Nt NP Hw)
                 (conj (pull_tmred (T := tyPi l3 l4 A' B') (l := lmax l1 l2) Hp HG HΓ Nt' NP' Hw')
                 (conj (whnf_usubst _ _ Hnf) (conj (whnf_usubst _ _ Hnf')
                 (conj (pull_geq_tm (T := tyPi l1 l2 A B) (l := lmax l1 l2) Hp HG HΓ NP Heq)
                 (conj (pull_geq_tm (T := tyPi l3 l4 A' B') (l := lmax l1 l2) Hp HG HΓ NP' Heq') _)))))).
        intros ρ a a' ha la lb la' lb' A1 B1 A1' B1' Hla Hlb Hla' Hlb' HA1 HB1 HA1' HB1'.
        pose proof (uperm_grow _ _ _ _ (kw_gL ρ) Hp) as Hpρ.
        destruct (IHdom ρ π πi Hpρ) as (Rd & HRd & ERd). rewrite <- !(kty_push Hp ρ) in HRd.
        destruct (LR_rel_dnf (domAd ρ) _ _ ha) as [Na Na'].
        assert (ha' : exists Rd0, LR n (LRbelow n) (kw_G (kw_push Hp ρ)) (kw_Δ (kw_push Hp ρ))
                        (kty (kw_push Hp ρ) A[pφ π]ᵤ) (kty (kw_push Hp ρ) A'[pφ π]ᵤ) (lvsubst l1 (pφ π)) Rd0
                        /\ Rd0 a[pφ π]ᵤ a'[pφ π]ᵤ)
          by (exists Rd; exact (conj HRd (proj1 (ERd a a' Na Na') ha))).
        destruct (geq_ty_dnf HA1) as [_ NA1]. destruct (geq_ty_dnf HB1) as [_ NB1].
        destruct (geq_ty_dnf HA1') as [_ NA1']. destruct (geq_ty_dnf HB1') as [_ NB1'].
        destruct (HK (kw_push Hp ρ) _ _ ha' _ _ _ _ _ _ _ _ (pg_lequiv Hp Hla) (pg_lequiv Hp Hlb)
                    (pg_lequiv Hp Hla') (pg_lequiv Hp Hlb') (push_geq_kty Hp ρ HA1) (push_geq_ktyl Hp ρ HB1)
                    (push_geq_kty Hp ρ HA1') (push_geq_ktyl Hp ρ HB1')) as (Rc0 & HRc0 & h0).
        destruct (IHcod ρ a a' ha π πi Hpρ) as (Rc & HRc & ERc).
        rewrite !usubst_lsingle_ty', <- !(ktyl_push Hp ρ) in HRc.
        pose proof (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRc HRc0 _ _) h0) as h1.
        refine (proj2 (ERc (app (ktm ρ w0[pφ πi]ᵤ) la lb A1 B1 a) (app (ktm ρ w0'[pφ πi]ᵤ) la' lb' A1' B1' a')
                         _ _) _);
          [cbn; repeat split; auto using dnf_ktm, dnf_us_tm .. |].
        rewrite !usubst_app', <- !(ktm_push Hp ρ), !(rt_tm Hinv') by assumption. exact h1.
  - (* contextual types *)
    destruct (LR_glob (LRmod n (LRbelow n) _ _ _ _ _ _ Hj HM)) as (HG & HΓ & _).
    destruct (ModRel_perm Hp HG HΓ HM) as (R' & HM' & HR'). exists R'.
    split; [apply LRmod; [exact Hj | exact HM'] | exact HR'].
  - (* CΠ: as for Π, worlds of the permuted context are pulled back, the
       contexts along the inverse *)
    set (T1π := T1[pφ π]ᵤ). set (T1'π := T1'[pφ π]ᵤ). set (k1 := lvsubst l1 (pφ π)).
    pose proof (wf_ty_dnf HT1) as N1. pose proof (wf_ty_dnf HT1') as N1'.
    set (instR' := fun (ρ' : kwk (Gp π G) Γ[pφ π]ᵤ) Δ Δ' (_ : vp_ctx lr_vp (kw_G ρ') Δ Δ') b b' =>
           exists Rc, LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (kbody ρ' T1π)⦃gsingle (GCtx Δ)⦄
                        (kbody ρ' T1'π)⦃gsingle (GCtx Δ')⦄ k1 Rc /\ Rc b b').
    assert (PullC : forall ρ' Δ Δ' (h : vp_ctx lr_vp (kw_G ρ') Δ Δ'),
              vp_ctx lr_vp (kw_G (kw_pull Hp HG HΓ ρ')) Δ[pφ πi]ᵤ Δ'[pφ πi]ᵤ)
      by (intros ρ' Δ Δ' h; exact (vpp_ctx (uperm_grow _ _ _ _ (kw_gL ρ') Hpi) (kw_glob ρ') h)).
    assert (Inst : forall ρ' Δ Δ' (h : vp_ctx lr_vp (kw_G ρ') Δ Δ'), exists Rc,
              LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (kbody ρ' T1π)⦃gsingle (GCtx Δ)⦄
                (kbody ρ' T1'π)⦃gsingle (GCtx Δ')⦄ k1 Rc /\
              forall y y', dnftm y -> dnftm y' ->
                (instR (kw_pull Hp HG HΓ ρ') _ _ (PullC ρ' Δ Δ' h) y y' <-> Rc y[pφ π]ᵤ y'[pφ π]ᵤ)).
    { intros ρ' Δ Δ' h. destruct (vpp_ctx_dnf h) as [N N'].
      assert (Hpρ : uperm π πi (gL (kw_G (kw_pull Hp HG HΓ ρ')))) by exact (uperm_grow _ _ _ _ (kw_gL ρ') Hp).
      destruct (IHinst (kw_pull Hp HG HΓ ρ') _ _ (PullC ρ' Δ Δ' h) π πi Hpρ) as (Rc & HRc & ERc).
      rewrite (pull_G Hp HG HΓ ρ'), (pull_Δ Hp HG HΓ ρ'), !usubst_gsingle_ty', !(kbody_pull Hp HG HΓ ρ') in HRc.
      cbn [gousubst] in HRc. change (ucsubst ?x ?φ) with x[φ]ᵤ in HRc.
      rewrite !(rt_ctx Hinv') in HRc by assumption.
      exists Rc. exact (conj HRc ERc). }
    assert (Hinst' : forall ρ' Δ Δ' (h : vp_ctx lr_vp (kw_G ρ') Δ Δ'),
              LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (kbody ρ' T1π)⦃gsingle (GCtx Δ)⦄
                (kbody ρ' T1'π)⦃gsingle (GCtx Δ')⦄ k1 (instR' ρ' Δ Δ' h)).
    { intros ρ' Δ Δ' h. destruct (Inst ρ' Δ Δ' h) as (Rc & HRc & _).
      refine (LR_releq _ _ _ _ _ _ _ _ _ HRc _).
      intros b b'; split; [intros hb; exists Rc; exact (conj HRc hb) |].
      intros (Rc2 & H2 & h2). exact (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRc H2 b b') h2). }
    exists (CPiRel (Gp π G) Γ[pφ π]ᵤ k1 (lvsubst l2 (pφ π)) T1π T1'π instR'). split.
    + apply (LRcpi n (LRbelow n) (Gp π G) Γ[pφ π]ᵤ T[pφ π]ᵤ T'[pφ π]ᵤ (lvsubst l (pφ π)) k1
               (lvsubst l2 (pφ π)) T1π T1'π instR').
      * exact Hj.
      * exact (pg_lequiv Hp Hl).
      * exact (pg_lequiv Hp Hl2).
      * exact (pg_lwf Hp Hw1).
      * exact (pg_tyred Hp HT).
      * exact (pg_tyred Hp HT').
      * pose proof (pg_ty (G := gext G gdCtx) Hp HT1) as X. rewrite usubst_gren_ctx in X. exact X.
      * pose proof (pg_ty (G := gext G gdCtx) Hp HT1') as X. rewrite usubst_gren_ctx in X. exact X.
      * exact (pg_geq_ty Hp Hgeq).
      * exact Hinst'.
      * apply releq_refl.
    + subst instR' T1π T1'π k1.
      intros t t' Nt Nt'. rewrite (HR t t'). split.
      * intros (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
        destruct (geq_tm_dnf Heq) as [Nw Nw'].
        exists w[pφ π]ᵤ, w'[pφ π]ᵤ.
        refine (conj (pg_tmred Hp Hw) (conj (pg_tmred Hp Hw') (conj (whnf_usubst _ _ Hnf)
                  (conj (whnf_usubst _ _ Hnf') (conj (pg_geq_tm Hp Heq) (conj (pg_geq_tm Hp Heq') _)))))).
        intros ρ' Δ Δ' h. destruct (vpp_ctx_dnf h) as [N N'].
        pose proof (HK (kw_pull Hp HG HΓ ρ') _ _ (PullC ρ' Δ Δ' h)) as X1.
        destruct (Inst ρ' Δ Δ' h) as (Rc & HRc & ERc).
        apply ERc in X1; [| apply dnf_capp; [apply dnf_ktm; assumption | apply dnf_us_ctx] ..].
        cbn [usubst USubst_tm usubst_tm] in X1. change (usubst_tm ?x ?φ) with x[φ]ᵤ in X1.
        change (ucsubst ?x ?φ) with x[φ]ᵤ in X1.
        rewrite !(ktm_pull Hp HG HΓ ρ'), !(rt_ctx Hinv') in X1 by assumption.
        exists Rc. exact (conj HRc X1).
      * intros (w0 & w0' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
        destruct (geq_tm_dnf Heq) as [Nw0 Nw0'].
        assert (NP : dnfty (tyCPi l1 T1)) by exact N1.
        assert (NP' : dnfty (tyCPi l2 T1')) by exact N1'.
        exists w0[pφ πi]ᵤ, w0'[pφ πi]ᵤ.
        refine (conj (pull_tmred (T := tyCPi l1 T1) (l := l1) Hp HG HΓ Nt NP Hw)
                 (conj (pull_tmred (T := tyCPi l2 T1') (l := l1) Hp HG HΓ Nt' NP' Hw')
                 (conj (whnf_usubst _ _ Hnf) (conj (whnf_usubst _ _ Hnf')
                 (conj (pull_geq_tm (T := tyCPi l1 T1) (l := l1) Hp HG HΓ NP Heq)
                 (conj (pull_geq_tm (T := tyCPi l2 T1') (l := l1) Hp HG HΓ NP' Heq') _)))))).
        intros ρ Δ Δ' h. destruct (vpp_ctx_dnf h) as [N N'].
        pose proof (uperm_grow _ _ _ _ (kw_gL ρ) Hp) as Hpρ.
        pose proof (vpp_ctx Hpρ (kw_glob ρ) h) as hπ.
        destruct (HK (kw_push Hp ρ) _ _ hπ) as (Rc0 & HRc0 & h0).
        destruct (IHinst ρ Δ Δ' h π πi Hpρ) as (Rc & HRc & ERc).
        rewrite !usubst_gsingle_ty', <- !(kbody_push Hp ρ) in HRc. cbn [gousubst] in HRc.
        pose proof (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRc HRc0 _ _) h0) as h1.
        refine (proj2 (ERc (capp (ktm ρ w0[pφ πi]ᵤ) Δ) (capp (ktm ρ w0'[pφ πi]ᵤ) Δ') _ _) _);
          [apply dnf_capp; [apply dnf_ktm, dnf_us_tm | assumption] .. |].
        cbn [usubst USubst_tm usubst_tm]. change (usubst_tm ?x ?φ) with x[φ]ᵤ.
        rewrite <- !(ktm_push Hp ρ), !(rt_tm Hinv') by assumption. exact h1.
  - (* TΠ: likewise, the types along the inverse, in the domain moved along the world *)
    set (T1π := T1[pφ π]ᵤ). set (T1'π := T1'[pφ π]ᵤ). set (k1 := lvsubst l1 (pφ π)).
    set (k2 := lvsubst l2 (pφ π)). set (Δ1π := Δ1[pφ π]ᵤ).
    pose proof (wf_ty_dnf HT1) as N1. pose proof (wf_ty_dnf HT1') as N1'.
    pose proof (wf_ctx_dnf (proj1 (wf_gext_ty_inv (ctx_glob _ _ _ (ctx_of_ty HT1))))) as NΔ1.
    set (instR' := fun (ρ' : kwk (Gp π G) Γ[pφ π]ᵤ) A A' (_ : vp_ty lr_vp (kw_G ρ') Δ1π⟦kw_γ ρ'⟧ A A' k1) b b' =>
           exists Rc, LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (kbody ρ' T1π)⦃gsingle (GTy A)⦄
                        (kbody ρ' T1'π)⦃gsingle (GTy A')⦄ k2 Rc /\ Rc b b').
    assert (PullT : forall ρ' A A' (h : vp_ty lr_vp (kw_G ρ') Δ1π⟦kw_γ ρ'⟧ A A' k1),
              vp_ty lr_vp (kw_G (kw_pull Hp HG HΓ ρ')) Δ1⟦kw_γ (kw_pull Hp HG HΓ ρ')⟧ A[pφ πi]ᵤ A'[pφ πi]ᵤ l1).
    { intros ρ' A A' h. pose proof (vpp_ty (uperm_grow _ _ _ _ (kw_gL ρ') Hpi) (kw_glob ρ') h) as X.
      rewrite usubst_gwa_ctx in X. subst Δ1π k1. rewrite (rt_ctx Hinv _ NΔ1), (rt_lvl Hinv) in X. exact X. }
    assert (Inst : forall ρ' A A' (h : vp_ty lr_vp (kw_G ρ') Δ1π⟦kw_γ ρ'⟧ A A' k1), exists Rc,
              LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (kbody ρ' T1π)⦃gsingle (GTy A)⦄
                (kbody ρ' T1'π)⦃gsingle (GTy A')⦄ k2 Rc /\
              forall y y', dnftm y -> dnftm y' ->
                (instR (kw_pull Hp HG HΓ ρ') _ _ (PullT ρ' A A' h) y y' <-> Rc y[pφ π]ᵤ y'[pφ π]ᵤ)).
    { intros ρ' A A' h. destruct (vpp_ty_dnf h) as [N N'].
      assert (Hpρ : uperm π πi (gL (kw_G (kw_pull Hp HG HΓ ρ')))) by exact (uperm_grow _ _ _ _ (kw_gL ρ') Hp).
      destruct (IHinst (kw_pull Hp HG HΓ ρ') _ _ (PullT ρ' A A' h) π πi Hpρ) as (Rc & HRc & ERc).
      rewrite (pull_G Hp HG HΓ ρ'), (pull_Δ Hp HG HΓ ρ'), !usubst_gsingle_ty', !(kbody_pull Hp HG HΓ ρ') in HRc.
      cbn [gousubst] in HRc. change (usubst_ty ?x ?φ) with x[φ]ᵤ in HRc.
      rewrite !(rt_ty Hinv') in HRc by assumption.
      exists Rc. exact (conj HRc ERc). }
    assert (Hinst' : forall ρ' A A' (h : vp_ty lr_vp (kw_G ρ') Δ1π⟦kw_γ ρ'⟧ A A' k1),
              LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (kbody ρ' T1π)⦃gsingle (GTy A)⦄
                (kbody ρ' T1'π)⦃gsingle (GTy A')⦄ k2 (instR' ρ' A A' h)).
    { intros ρ' A A' h. destruct (Inst ρ' A A' h) as (Rc & HRc & _).
      refine (LR_releq _ _ _ _ _ _ _ _ _ HRc _).
      intros b b'; split; [intros hb; exists Rc; exact (conj HRc hb) |].
      intros (Rc2 & H2 & h2). exact (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRc H2 b b') h2). }
    exists (TPiRel (Gp π G) Γ[pφ π]ᵤ Δ1π Δ1'[pφ π]ᵤ k1 k2 (lvsubst l3 (pφ π)) (lvsubst l4 (pφ π)) T1π T1'π instR').
    split.
    + apply (LRtpi n (LRbelow n) (Gp π G) Γ[pφ π]ᵤ T[pφ π]ᵤ T'[pφ π]ᵤ (lvsubst l (pφ π)) Δ1π Δ1'[pφ π]ᵤ
               k1 k2 (lvsubst l3 (pφ π)) (lvsubst l4 (pφ π)) T1π T1'π instR').
      * exact Hj.
      * exact (pg_lequiv Hp Hl).
      * exact (pg_lequiv Hp Hl3).
      * exact (pg_lequiv Hp Hl4).
      * exact (pg_lwf Hp Hw1).
      * exact (pg_lwf Hp Hw2).
      * exact (pg_tyred Hp HT).
      * exact (pg_tyred Hp HT').
      * exact (vpp_ctx Hp HG HΔ).
      * pose proof (pg_ty (G := gext G (gdTy Δ1 lD l1)) Hp HT1) as X. rewrite usubst_gren_ctx in X. exact X.
      * pose proof (pg_ty (G := gext G (gdTy Δ1' lD l3)) Hp HT1') as X. rewrite usubst_gren_ctx in X. exact X.
      * exact (pg_geq_ty Hp Hgeq).
      * exact Hinst'.
      * apply releq_refl.
    + subst instR' T1π T1'π k1 k2.
      intros t t' Nt Nt'. rewrite (HR t t'). split.
      * intros (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
        destruct (geq_tm_dnf Heq) as [Nw Nw'].
        exists w[pφ π]ᵤ, w'[pφ π]ᵤ.
        refine (conj (pg_tmred Hp Hw) (conj (pg_tmred Hp Hw') (conj (whnf_usubst _ _ Hnf)
                  (conj (whnf_usubst _ _ Hnf') (conj (pg_geq_tm Hp Heq) (conj (pg_geq_tm Hp Heq') _)))))).
        intros ρ' A A' h. destruct (vpp_ty_dnf h) as [N N'].
        pose proof (HK (kw_pull Hp HG HΓ ρ') _ _ (PullT ρ' A A' h)) as X1.
        destruct (Inst ρ' A A' h) as (Rc & HRc & ERc).
        apply ERc in X1; [| apply dnf_tapp; [apply dnf_ktm; assumption | apply dnf_us_ty] ..].
        cbn [usubst USubst_tm usubst_tm] in X1. change (usubst_tm ?x ?φ) with x[φ]ᵤ in X1.
        change (usubst_ty ?x ?φ) with x[φ]ᵤ in X1.
        rewrite !(ktm_pull Hp HG HΓ ρ'), !(rt_ty Hinv') in X1 by assumption.
        exists Rc. exact (conj HRc X1).
      * intros (w0 & w0' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
        destruct (geq_tm_dnf Heq) as [Nw0 Nw0'].
        assert (NP : dnfty (tyTPi Δ1 l1 l2 T1)) by (cbn; auto).
        assert (NP' : dnfty (tyTPi Δ1' l3 l4 T1'))
          by (cbn; split; [exact (wf_ctx_dnf (proj1 (wf_gext_ty_inv (ctx_glob _ _ _ (ctx_of_ty HT1'))))) | exact N1']).
        exists w0[pφ πi]ᵤ, w0'[pφ πi]ᵤ.
        refine (conj (pull_tmred (T := tyTPi Δ1 l1 l2 T1) (l := l2) Hp HG HΓ Nt NP Hw)
                 (conj (pull_tmred (T := tyTPi Δ1' l3 l4 T1') (l := l2) Hp HG HΓ Nt' NP' Hw')
                 (conj (whnf_usubst _ _ Hnf) (conj (whnf_usubst _ _ Hnf')
                 (conj (pull_geq_tm (T := tyTPi Δ1 l1 l2 T1) (l := l2) Hp HG HΓ NP Heq)
                 (conj (pull_geq_tm (T := tyTPi Δ1' l3 l4 T1') (l := l2) Hp HG HΓ NP' Heq') _)))))).
        intros ρ A A' h. destruct (vpp_ty_dnf h) as [N N'].
        pose proof (uperm_grow _ _ _ _ (kw_gL ρ) Hp) as Hpρ.
        pose proof (vpp_ty Hpρ (kw_glob ρ) h) as hπ. rewrite usubst_gwa_ctx in hπ.
        destruct (HK (kw_push Hp ρ) _ _ hπ) as (Rc0 & HRc0 & h0).
        destruct (IHinst ρ A A' h π πi Hpρ) as (Rc & HRc & ERc).
        rewrite !usubst_gsingle_ty', <- !(kbody_push Hp ρ) in HRc. cbn [gousubst] in HRc.
        pose proof (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRc HRc0 _ _) h0) as h1.
        refine (proj2 (ERc (tapp (ktm ρ w0[pφ πi]ᵤ) A) (tapp (ktm ρ w0'[pφ πi]ᵤ) A') _ _) _);
          [apply dnf_tapp; [apply dnf_ktm, dnf_us_tm | assumption] .. |].
        cbn [usubst USubst_tm usubst_tm]. change (usubst_tm ?x ?φ) with x[φ]ᵤ.
        rewrite <- !(ktm_push Hp ρ), !(rt_tm Hinv') by assumption. exact h1.
  - (* Σ *)
    pose proof (poly_pg Hp (fun _ _ _ _ _ => eq_refl) P) as P'.
    destruct P as [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB].
    destruct (tyred_glob HT) as (HG & HΓ & NT & NW); destruct (tyred_glob HT') as (_ & _ & NT' & NW');
    pose proof (p_glob Hp HG) as HG'.
    set (Aπ := A[pφ π]ᵤ). set (A'π := A'[pφ π]ᵤ). set (Bπ := B[pφ π]ᵤ). set (B'π := B'[pφ π]ᵤ).
    set (k1 := lvsubst l1 (pφ π)). set (k2 := lvsubst l2 (pφ π)).
    pose proof (wf_ty_dnf HA) as NA. pose proof (wf_ty_dnf HA') as NA'.
    pose proof (wf_ty_dnf HB) as NB. pose proof (wf_ty_dnf HB') as NB'.
    set (domR' := fun (ρ' : kwk (Gp π G) Γ[pφ π]ᵤ) a a' =>
           exists Rd, LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (kty ρ' Aπ) (kty ρ' A'π) k1 Rd /\ Rd a a').
    set (codR' := fun (ρ' : kwk (Gp π G) Γ[pφ π]ᵤ) a a' (_ : domR' ρ' a a') b b' =>
           exists Rc, LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (ktyl ρ' Bπ)[lsingle a] (ktyl ρ' B'π)[lsingle a'] k2 Rc
             /\ Rc b b').
    (* the domains at a world of the permuted context, through its pull-back *)
    assert (Dom : forall ρ', exists Rd,
               LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (kty ρ' Aπ) (kty ρ' A'π) k1 Rd /\
               forall x y, dnftm x -> dnftm y -> (domR (kw_pull Hp HG HΓ ρ') x y <-> Rd x[pφ π]ᵤ y[pφ π]ᵤ)).
    { intros ρ'.
      assert (Hpρ : uperm π πi (gL (kw_G (kw_pull Hp HG HΓ ρ')))) by exact (uperm_grow _ _ _ _ (kw_gL ρ') Hp).
      destruct (IHdom (kw_pull Hp HG HΓ ρ') π πi Hpρ) as (Rd & HRd & ERd).
      rewrite (pull_G Hp HG HΓ ρ'), (pull_Δ Hp HG HΓ ρ'), !(kty_pull Hp HG HΓ ρ') in HRd.
      exists Rd. exact (conj HRd ERd). }
    assert (Cod : forall ρ' x x' (hx : domR (kw_pull Hp HG HΓ ρ') x x'), exists Rc,
               LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (ktyl ρ' Bπ)[lsingle x[pφ π]ᵤ] (ktyl ρ' B'π)[lsingle x'[pφ π]ᵤ]
                 k2 Rc /\
               forall y y', dnftm y -> dnftm y' ->
                 (codR (kw_pull Hp HG HΓ ρ') x x' hx y y' <-> Rc y[pφ π]ᵤ y'[pφ π]ᵤ)).
    { intros ρ' x x' hx.
      assert (Hpρ : uperm π πi (gL (kw_G (kw_pull Hp HG HΓ ρ')))) by exact (uperm_grow _ _ _ _ (kw_gL ρ') Hp).
      destruct (IHcod (kw_pull Hp HG HΓ ρ') x x' hx π πi Hpρ) as (Rc & HRc & ERc).
      rewrite (pull_G Hp HG HΓ ρ'), (pull_Δ Hp HG HΓ ρ'), !usubst_lsingle_ty', !(ktyl_pull Hp HG HΓ ρ') in HRc.
      exists Rc. exact (conj HRc ERc). }
    (* a related pair of the permuted domain comes from one of the original *)
    assert (Back : forall ρ' a a', domR' ρ' a a' ->
               dnftm a /\ dnftm a' /\ domR (kw_pull Hp HG HΓ ρ') a[pφ πi]ᵤ a'[pφ πi]ᵤ).
    { intros ρ' a a' (Rd2 & H2 & h2). destruct (Dom ρ') as (Rd & HRd & ERd).
      destruct (LR_rel_dnf H2 _ _ h2) as [Na Na'].
      pose proof (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRd H2 a a') h2) as h.
      refine (conj Na (conj Na' _)). apply (ERd _ _ (dnf_us_tm _ _) (dnf_us_tm _ _)).
      rewrite !(rt_tm Hinv') by assumption. exact h. }
    assert (Hdom' : forall ρ', LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (kty ρ' Aπ) (kty ρ' A'π) k1 (domR' ρ')).
    { intros ρ'. destruct (Dom ρ') as (Rd & HRd & _). refine (LR_releq _ _ _ _ _ _ _ _ _ HRd _).
      intros a a'; split; [intros h; exists Rd; exact (conj HRd h) |].
      intros (Rd2 & H2 & h2). exact (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRd H2 a a') h2). }
    assert (Hcod' : forall ρ' a a' (ha : domR' ρ' a a'),
               LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (ktyl ρ' Bπ)[lsingle a] (ktyl ρ' B'π)[lsingle a'] k2
                 (codR' ρ' a a' ha)).
    { intros ρ' a a' ha. destruct (Back ρ' a a' ha) as (Na & Na' & hx).
      destruct (Cod ρ' _ _ hx) as (Rc & HRc & _). rewrite !(rt_tm Hinv') in HRc by assumption.
      refine (LR_releq _ _ _ _ _ _ _ _ _ HRc _).
      intros b b'; split; [intros h; exists Rc; exact (conj HRc h) |].
      intros (Rc2 & H2 & h2). exact (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRc H2 b b') h2). }
    exists (SigRel (Gp π G) Γ[pφ π]ᵤ k1 k2 (lvsubst l3 (pφ π)) (lvsubst l4 (pφ π)) Aπ Bπ A'π B'π domR' codR').
    split.
    + apply (LRsig n (LRbelow n) (Gp π G) Γ[pφ π]ᵤ T[pφ π]ᵤ T'[pφ π]ᵤ (lvsubst l (pφ π)) k1 k2
               (lvsubst l3 (pφ π)) (lvsubst l4 (pφ π)) Aπ Bπ A'π B'π domR' codR').
      * exact P'.
      * exact Hdom'.
      * exact Hcod'.
      * apply releq_refl.
    + subst codR' domR' Aπ A'π Bπ B'π k1 k2.
      intros t t' Nt Nt'. rewrite (HR t t'). split.
      * intros (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
        destruct (geq_tm_dnf Heq) as [Nw Nw'].
        exists w[pφ π]ᵤ, w'[pφ π]ᵤ.
        refine (conj (pg_tmred Hp Hw) (conj (pg_tmred Hp Hw') (conj (whnf_usubst _ _ Hnf)
                  (conj (whnf_usubst _ _ Hnf') (conj (pg_geq_tm Hp Heq) (conj (pg_geq_tm Hp Heq') _)))))).
        intros ρ' la lb la' lb' A1 B1 A1' B1' Hla Hlb Hla' Hlb' HA1 HB1 HA1' HB1'.
        assert (PullL : forall lx lk, lequiv (gL (Gp π G)) lx (lvsubst lk (pφ π)) ->
                          lequiv (gL G) (lvsubst lx (pφ πi)) lk).
        { intros lx lk Hx. pose proof (pg_lequiv (G := Gp π G) Hpi Hx) as X. rewrite (rt_lvl Hinv) in X. exact X. }
        destruct (geq_ty_dnf HA1) as [_ NA1]. destruct (geq_ty_dnf HB1) as [_ NB1].
        destruct (geq_ty_dnf HA1') as [_ NA1']. destruct (geq_ty_dnf HB1') as [_ NB1'].
        pose proof (pull_geq_kty Hp HG HΓ ρ' NA HA1) as HA1b. rewrite (rt_lvl Hinv) in HA1b.
        pose proof (pull_geq_ktyl Hp HG HΓ ρ' NA NB HB1) as HB1b. rewrite !(rt_lvl Hinv) in HB1b.
        pose proof (pull_geq_kty Hp HG HΓ ρ' NA' HA1') as HA1'b. rewrite (rt_lvl Hinv) in HA1'b.
        pose proof (pull_geq_ktyl Hp HG HΓ ρ' NA' NB' HB1') as HB1'b. rewrite !(rt_lvl Hinv) in HB1'b.
        destruct (HK (kw_pull Hp HG HΓ ρ') _ _ _ _ _ _ _ _ (PullL _ _ Hla) (PullL _ _ Hlb)
                    (PullL _ _ Hla') (PullL _ _ Hlb') HA1b HB1b HA1'b HB1'b) as [hx X1].
        destruct (Dom ρ') as (Rd & HRd & ERd).
        pose proof hx as hd. apply ERd in hd; [| cbn; repeat split; auto using dnf_ktm, dnf_us_ty ..].
        rewrite !usubst_fst', !(ktm_pull Hp HG HΓ ρ'), !(rt_lvl Hinv'), !(rt_ty Hinv') in hd by assumption.
        exists (ex_intro _ Rd (conj HRd hd)).
        destruct (Cod ρ' _ _ hx) as (Rc & HRc & ERc).
        apply ERc in X1;
          [| cbn; repeat split; auto using dnf_ktm, dnf_us_tm, dnf_us_ty ..].
        rewrite !usubst_snd', !(ktm_pull Hp HG HΓ ρ'), !(rt_lvl Hinv'), !(rt_ty Hinv') in X1
          by assumption.
        rewrite !usubst_fst', !(ktm_pull Hp HG HΓ ρ'), !(rt_lvl Hinv'), !(rt_ty Hinv') in HRc by assumption.
        exists Rc. exact (conj HRc X1).
      * intros (w0 & w0' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
        destruct (geq_tm_dnf Heq) as [Nw0 Nw0'].
        assert (NP : dnfty (tySig l1 l2 A B)) by (cbn; auto).
        assert (NP' : dnfty (tySig l3 l4 A' B')) by (cbn; auto).
        exists w0[pφ πi]ᵤ, w0'[pφ πi]ᵤ.
        refine (conj (pull_tmred (T := tySig l1 l2 A B) (l := lmax l1 l2) Hp HG HΓ Nt NP Hw)
                 (conj (pull_tmred (T := tySig l3 l4 A' B') (l := lmax l1 l2) Hp HG HΓ Nt' NP' Hw')
                 (conj (whnf_usubst _ _ Hnf) (conj (whnf_usubst _ _ Hnf')
                 (conj (pull_geq_tm (T := tySig l1 l2 A B) (l := lmax l1 l2) Hp HG HΓ NP Heq)
                 (conj (pull_geq_tm (T := tySig l3 l4 A' B') (l := lmax l1 l2) Hp HG HΓ NP' Heq') _)))))).
        intros ρ la lb la' lb' A1 B1 A1' B1' Hla Hlb Hla' Hlb' HA1 HB1 HA1' HB1'.
        pose proof (uperm_grow _ _ _ _ (kw_gL ρ) Hp) as Hpρ.
        destruct (geq_ty_dnf HA1) as [_ NA1]. destruct (geq_ty_dnf HB1) as [_ NB1].
        destruct (geq_ty_dnf HA1') as [_ NA1']. destruct (geq_ty_dnf HB1') as [_ NB1'].
        destruct (HK (kw_push Hp ρ) _ _ _ _ _ _ _ _ (pg_lequiv Hp Hla) (pg_lequiv Hp Hlb)
                    (pg_lequiv Hp Hla') (pg_lequiv Hp Hlb') (push_geq_kty Hp ρ HA1) (push_geq_ktyl Hp ρ HB1)
                    (push_geq_kty Hp ρ HA1') (push_geq_ktyl Hp ρ HB1')) as [h0 C0].
        destruct C0 as (Rc0 & HRc0 & c0). destruct h0 as (Rd0 & HRd0 & hd0).
        destruct (IHdom ρ π πi Hpρ) as (Rd & HRd & ERd). rewrite <- !(kty_push Hp ρ) in HRd.
        pose proof (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRd HRd0 _ _) hd0) as hd.
        assert (Nf : forall la0 lb0 A0 B0 u, dnfty A0 -> dnfty B0 -> dnftm u ->
                  dnftm (tmFst la0 lb0 A0 B0 (ktm ρ u)) /\ dnftm (tmSnd la0 lb0 A0 B0 (ktm ρ u)))
          by (intros; cbn; split; repeat split; auto using dnf_ktm).
        assert (h : domR ρ (tmFst la lb A1 B1 (ktm ρ w0[pφ πi]ᵤ)) (tmFst la' lb' A1' B1' (ktm ρ w0'[pφ πi]ᵤ))).
        { apply (ERd _ _ (proj1 (Nf _ _ _ _ _ NA1 NB1 (dnf_us_tm _ _)))
                         (proj1 (Nf _ _ _ _ _ NA1' NB1' (dnf_us_tm _ _)))).
          rewrite !usubst_fst', <- !(ktm_push Hp ρ), !(rt_tm Hinv') by assumption. exact hd. }
        exists h.
        destruct (IHcod ρ _ _ h π πi Hpρ) as (Rc & HRc & ERc).
        rewrite !usubst_lsingle_ty', <- !(ktyl_push Hp ρ) in HRc.
        rewrite !usubst_fst', <- !(ktm_push Hp ρ), !(rt_tm Hinv') in HRc by assumption.
        pose proof (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRc HRc0 _ _) c0) as c1.
        apply (ERc _ _ (proj2 (Nf _ _ _ _ _ NA1 NB1 (dnf_us_tm _ _)))
                       (proj2 (Nf _ _ _ _ _ NA1' NB1' (dnf_us_tm _ _)))).
        rewrite !usubst_snd', <- !(ktm_push Hp ρ), !(rt_tm Hinv') by assumption. exact c1.
  - (* Unit *)
    exists (UnitRel (Gp π G) Γ[pφ π]ᵤ (lvsubst l1 (pφ π))). split.
    + eapply LRunit; [exact (pg_lequiv Hp Hl) | exact (pg_lequiv Hp Hl2) | exact (pg_lwf Hp Hw)
                     | exact (pg_tyred Hp HT) | exact (pg_tyred Hp HT') | apply releq_refl].
    + intros t t' Nt Nt'. rewrite (HR t t'). split.
      * intros (w & w' & Hr & Hr' & Hf & Hf'). exists w[pφ π]ᵤ, w'[pφ π]ᵤ.
        exact (conj (pg_tmred Hp Hr) (conj (pg_tmred Hp Hr') (conj (whnf_usubst _ _ Hf) (whnf_usubst _ _ Hf')))).
      * intros (w & w' & Hr & Hr' & Hf & Hf'). apply (pg_tmred (G := Gp π G) Hpi) in Hr, Hr'.
        change ((tyUnit ?x)[?φ]ᵤ) with (tyUnit (lvsubst x φ)) in Hr, Hr'.
        rewrite (Gp_rt Hp HG), (rt_ctx Hinv _ HΓ), (rt_lvl Hinv), !(rt_tm Hinv) in Hr, Hr' by assumption.
        exists w[pφ πi]ᵤ, w'[pφ πi]ᵤ.
        exact (conj Hr (conj Hr' (conj (whnf_usubst _ _ Hf) (whnf_usubst _ _ Hf')))).
  - (* sEq *)
    cbn in NW. destruct NW as (NA & Na & Nb).
    exists (SEqRel (Gp π G) Γ[pφ π]ᵤ (tySEq (lvsubst s1 (pφ π)) SA[pφ π]ᵤ sa[pφ π]ᵤ sb[pφ π]ᵤ)
              (lvsubst s1 (pφ π))). split.
    + eapply LRseq; [exact (pg_lequiv Hp Hl) | exact (pg_lequiv Hp Hl2) | exact (pg_lwf Hp Hw)
                    | exact (pg_tyred Hp HT) | exact (pg_tyred Hp HT') | exact (pg_ty Hp HSA)
                    | exact (pg_geq_ty Hp HSAA) | exact (pg_geq_tm Hp Hsaa) | exact (pg_geq_tm Hp Hsbb)
                    | apply releq_refl].
    + intros t t' Nt Nt'. rewrite (HR t t'). split.
      * intros (w & w' & Hr & Hr' & Hf & Hf'). exists w[pφ π]ᵤ, w'[pφ π]ᵤ.
        exact (conj (pg_tmred Hp Hr) (conj (pg_tmred Hp Hr') (conj (whnf_usubst _ _ Hf) (whnf_usubst _ _ Hf')))).
      * intros (w & w' & Hr & Hr' & Hf & Hf'). apply (pg_tmred (G := Gp π G) Hpi) in Hr, Hr'.
        change ((tySEq ?x ?A0 ?a0 ?b0)[?φ]ᵤ) with (tySEq (lvsubst x φ) A0[φ]ᵤ a0[φ]ᵤ b0[φ]ᵤ) in Hr, Hr'.
        rewrite (Gp_rt Hp HG), (rt_ctx Hinv _ HΓ), (rt_lvl Hinv), (rt_ty Hinv _ NA), !(rt_tm Hinv) in Hr, Hr'
          by assumption.
        exists w[pφ πi]ᵤ, w'[pφ πi]ᵤ.
        exact (conj Hr (conj Hr' (conj (whnf_usubst _ _ Hf) (whnf_usubst _ _ Hf')))).
  - (* sEmpty *)
    exists (SEmptyRel (Gp π G) Γ[pφ π]ᵤ (lvsubst s1 (pφ π))). split.
    + eapply LRsempty; [exact (pg_lequiv Hp Hl) | exact (pg_lequiv Hp Hl2) | exact (pg_lwf Hp Hw)
                       | exact (pg_tyred Hp HT) | exact (pg_tyred Hp HT') | apply releq_refl].
    + intros t t' Nt Nt'. rewrite (HR t t'). split.
      * intros (w & w' & Hr & Hr' & Hf & Hf'). exists w[pφ π]ᵤ, w'[pφ π]ᵤ.
        exact (conj (pg_tmred Hp Hr) (conj (pg_tmred Hp Hr') (conj (pg_gne_tm Hp Hf) (pg_gne_tm Hp Hf')))).
      * intros (w & w' & Hr & Hr' & Hf & Hf'). apply (pg_tmred (G := Gp π G) Hpi) in Hr, Hr'.
        apply (pg_gne_tm (G := Gp π G) Hpi) in Hf, Hf'.
        change ((tySEmpty ?x)[?φ]ᵤ) with (tySEmpty (lvsubst x φ)) in Hr, Hr', Hf, Hf'.
        rewrite (Gp_rt Hp HG), (rt_ctx Hinv _ HΓ), (rt_lvl Hinv) in Hr, Hr', Hf, Hf'.
        rewrite !(rt_tm Hinv) in Hr, Hr' by assumption.
        exists w[pφ πi]ᵤ, w'[pφ πi]ᵤ.
        exact (conj Hr (conj Hr' (conj Hf Hf'))).
  - (* Id: along the carrier's permuted relation *)
    cbn in NW. destruct NW as (NA & Na & Nb).
    destruct (IHRA π πi Hp) as (RA' & HRA' & ERA).
    destruct (LR_tm_per _ _ _ _ _ _ _ HRA') as [Hs' Ht'].
    assert (F : forall x y, RA x y -> RA' x[pφ π]ᵤ y[pφ π]ᵤ).
    { intros x y H0. destruct (LR_rel_dnf HRA _ _ H0) as [Nx Ny]. exact (proj1 (ERA x y Nx Ny) H0). }
    assert (B : forall x y, RA' x y -> RA x[pφ πi]ᵤ y[pφ πi]ᵤ).
    { intros x y H0. destruct (LR_rel_dnf HRA' _ _ H0) as [Nx Ny].
      apply (ERA _ _ (dnf_us_tm _ _) (dnf_us_tm _ _)). rewrite !(rt_tm Hinv') by assumption. exact H0. }
    exists (IdRel (Gp π G) Γ[pφ π]ᵤ (lvsubst s1 (pφ π)) IA[pφ π]ᵤ ia[pφ π]ᵤ ib[pφ π]ᵤ RA'). split.
    + eapply LRid; [exact (pg_lequiv Hp Hl) | exact (pg_lequiv Hp Hl2) | exact (pg_lwf Hp Hw)
                   | exact (pg_tyred Hp HT) | exact (pg_tyred Hp HT') | exact (pg_ty Hp HIA)
                   | exact (pg_geq_ty Hp HIAA) | exact (pg_geq_tm Hp Hiaa) | exact (pg_geq_tm Hp Hibb)
                   | exact HRA' | exact (F _ _ Hra) | exact (F _ _ Hrb) | exact Hs' | exact Ht'
                   | apply releq_refl].
    + intros t t' Nt Nt'. rewrite (HR t t'). split; [apply (IdRel_perm Hp F) |].
      intros X. apply (IdRel_perm (G := Gp π G) Hpi B) in X.
      rewrite (Gp_rt Hp HG), (rt_ctx Hinv _ HΓ), (rt_lvl Hinv), (rt_ty Hinv _ NA), !(rt_tm Hinv) in X
        by assumption.
      exact X.
  - (* Empty *)
    exists (EmptyRel (Gp π G) Γ[pφ π]ᵤ (lvsubst s1 (pφ π))). split.
    + eapply LRempty; [exact (pg_lequiv Hp Hl) | exact (pg_lequiv Hp Hl2) | exact (pg_lwf Hp Hw)
                      | exact (pg_tyred Hp HT) | exact (pg_tyred Hp HT') | apply releq_refl].
    + intros t t' Nt Nt'. rewrite (HR t t'). split.
      * intros (w & w' & Hr & Hr' & Hf & Hf'). exists w[pφ π]ᵤ, w'[pφ π]ᵤ.
        exact (conj (pg_tmred Hp Hr) (conj (pg_tmred Hp Hr') (conj (pg_gne_tm Hp Hf) (pg_gne_tm Hp Hf')))).
      * intros (w & w' & Hr & Hr' & Hf & Hf'). apply (pg_tmred (G := Gp π G) Hpi) in Hr, Hr'.
        apply (pg_gne_tm (G := Gp π G) Hpi) in Hf, Hf'.
        change ((tyEmpty ?x)[?φ]ᵤ) with (tyEmpty (lvsubst x φ)) in Hr, Hr', Hf, Hf'.
        rewrite (Gp_rt Hp HG), (rt_ctx Hinv _ HΓ), (rt_lvl Hinv) in Hr, Hr', Hf, Hf'.
        rewrite !(rt_tm Hinv) in Hr, Hr' by assumption.
        exists w[pφ πi]ᵤ, w'[pφ πi]ᵤ.
        exact (conj Hr (conj Hr' (conj Hf Hf'))).
  - (* +: along both summands' permuted relations *)
    cbn in NW. destruct NW as (NA & NB).
    destruct (IHRA π πi Hp) as (RA' & HRA' & ERA).
    destruct (IHRB π πi Hp) as (RB' & HRB' & ERB).
    destruct (LR_tm_per _ _ _ _ _ _ _ HRA') as [HsA' HtA'].
    destruct (LR_tm_per _ _ _ _ _ _ _ HRB') as [HsB' HtB'].
    assert (FA : forall x y, RA x y -> RA' x[pφ π]ᵤ y[pφ π]ᵤ).
    { intros x y H0. destruct (LR_rel_dnf HRA _ _ H0) as [Nx Ny]. exact (proj1 (ERA x y Nx Ny) H0). }
    assert (FB : forall x y, RB x y -> RB' x[pφ π]ᵤ y[pφ π]ᵤ).
    { intros x y H0. destruct (LR_rel_dnf HRB _ _ H0) as [Nx Ny]. exact (proj1 (ERB x y Nx Ny) H0). }
    assert (BA : forall x y, RA' x y -> RA x[pφ πi]ᵤ y[pφ πi]ᵤ).
    { intros x y H0. destruct (LR_rel_dnf HRA' _ _ H0) as [Nx Ny].
      apply (ERA _ _ (dnf_us_tm _ _) (dnf_us_tm _ _)). rewrite !(rt_tm Hinv') by assumption. exact H0. }
    assert (BB : forall x y, RB' x y -> RB x[pφ πi]ᵤ y[pφ πi]ᵤ).
    { intros x y H0. destruct (LR_rel_dnf HRB' _ _ H0) as [Nx Ny].
      apply (ERB _ _ (dnf_us_tm _ _) (dnf_us_tm _ _)). rewrite !(rt_tm Hinv') by assumption. exact H0. }
    exists (SumRel (Gp π G) Γ[pφ π]ᵤ (lvsubst u1 (pφ π)) (lvsubst u2 (pφ π)) UA[pφ π]ᵤ UB[pφ π]ᵤ RA' RB').
    split.
    + eapply LRsum; [exact (pg_lequiv Hp Hl) | exact (pg_lequiv Hp Hl3) | exact (pg_lequiv Hp Hl4)
                    | exact (pg_lwf Hp Hw1) | exact (pg_lwf Hp Hw2)
                    | exact (pg_tyred Hp HT) | exact (pg_tyred Hp HT') | exact (pg_ty Hp HUA)
                    | exact (pg_geq_ty Hp HUAA) | exact (pg_ty Hp HUB) | exact (pg_geq_ty Hp HUBB)
                    | exact HRA' | exact HRB' | exact HsA' | exact HtA' | exact HsB' | exact HtB'
                    | apply releq_refl].
    + intros t t' Nt Nt'. rewrite (HR t t'). split; [apply (SumRel_perm Hp FA FB) |].
      intros X. apply (SumRel_perm (G := Gp π G) Hpi BA BB) in X.
      rewrite (Gp_rt Hp HG), (rt_ctx Hinv _ HΓ), !(rt_lvl Hinv), (rt_ty Hinv _ NA), (rt_ty Hinv _ NB),
        !(rt_tm Hinv) in X by assumption.
      exact X.
  - (* W: the type-level data as Σ's; the terms by [WRel_perm], backwards along [πi] *)
    pose proof (poly_pg Hp (fun _ _ _ _ _ => eq_refl) P) as P'.
    destruct P as [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB].
    destruct (tyred_glob HT) as (HG & HΓ & NT & NW); destruct (tyred_glob HT') as (_ & _ & NT' & NW');
    pose proof (p_glob Hp HG) as HG'.
    set (Aπ := A[pφ π]ᵤ). set (A'π := A'[pφ π]ᵤ). set (Bπ := B[pφ π]ᵤ). set (B'π := B'[pφ π]ᵤ).
    set (k1 := lvsubst l1 (pφ π)). set (k2 := lvsubst l2 (pφ π)).
    pose proof (wf_ty_dnf HA) as NA. pose proof (wf_ty_dnf HA') as NA'.
    pose proof (wf_ty_dnf HB) as NB. pose proof (wf_ty_dnf HB') as NB'.
    set (domR' := fun (ρ' : kwk (Gp π G) Γ[pφ π]ᵤ) a a' =>
           exists Rd, LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (kty ρ' Aπ) (kty ρ' A'π) k1 Rd /\ Rd a a').
    set (codR' := fun (ρ' : kwk (Gp π G) Γ[pφ π]ᵤ) a a' (_ : domR' ρ' a a') b b' =>
           exists Rc, LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (ktyl ρ' Bπ)[lsingle a] (ktyl ρ' B'π)[lsingle a'] k2 Rc
             /\ Rc b b').
    (* the domains at a world of the permuted context, through its pull-back *)
    assert (Dom : forall ρ', exists Rd,
               LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (kty ρ' Aπ) (kty ρ' A'π) k1 Rd /\
               forall x y, dnftm x -> dnftm y -> (domR (kw_pull Hp HG HΓ ρ') x y <-> Rd x[pφ π]ᵤ y[pφ π]ᵤ)).
    { intros ρ'.
      assert (Hpρ : uperm π πi (gL (kw_G (kw_pull Hp HG HΓ ρ')))) by exact (uperm_grow _ _ _ _ (kw_gL ρ') Hp).
      destruct (IHdom (kw_pull Hp HG HΓ ρ') π πi Hpρ) as (Rd & HRd & ERd).
      rewrite (pull_G Hp HG HΓ ρ'), (pull_Δ Hp HG HΓ ρ'), !(kty_pull Hp HG HΓ ρ') in HRd.
      exists Rd. exact (conj HRd ERd). }
    assert (Cod : forall ρ' x x' (hx : domR (kw_pull Hp HG HΓ ρ') x x'), exists Rc,
               LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (ktyl ρ' Bπ)[lsingle x[pφ π]ᵤ] (ktyl ρ' B'π)[lsingle x'[pφ π]ᵤ]
                 k2 Rc /\
               forall y y', dnftm y -> dnftm y' ->
                 (codR (kw_pull Hp HG HΓ ρ') x x' hx y y' <-> Rc y[pφ π]ᵤ y'[pφ π]ᵤ)).
    { intros ρ' x x' hx.
      assert (Hpρ : uperm π πi (gL (kw_G (kw_pull Hp HG HΓ ρ')))) by exact (uperm_grow _ _ _ _ (kw_gL ρ') Hp).
      destruct (IHcod (kw_pull Hp HG HΓ ρ') x x' hx π πi Hpρ) as (Rc & HRc & ERc).
      rewrite (pull_G Hp HG HΓ ρ'), (pull_Δ Hp HG HΓ ρ'), !usubst_lsingle_ty', !(ktyl_pull Hp HG HΓ ρ') in HRc.
      exists Rc. exact (conj HRc ERc). }
    (* a related pair of the permuted domain comes from one of the original *)
    assert (Back : forall ρ' a a', domR' ρ' a a' ->
               dnftm a /\ dnftm a' /\ domR (kw_pull Hp HG HΓ ρ') a[pφ πi]ᵤ a'[pφ πi]ᵤ).
    { intros ρ' a a' (Rd2 & H2 & h2). destruct (Dom ρ') as (Rd & HRd & ERd).
      destruct (LR_rel_dnf H2 _ _ h2) as [Na Na'].
      pose proof (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRd H2 a a') h2) as h.
      refine (conj Na (conj Na' _)). apply (ERd _ _ (dnf_us_tm _ _) (dnf_us_tm _ _)).
      rewrite !(rt_tm Hinv') by assumption. exact h. }
    assert (Hdom' : forall ρ', LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (kty ρ' Aπ) (kty ρ' A'π) k1 (domR' ρ')).
    { intros ρ'. destruct (Dom ρ') as (Rd & HRd & _). refine (LR_releq _ _ _ _ _ _ _ _ _ HRd _).
      intros a a'; split; [intros h; exists Rd; exact (conj HRd h) |].
      intros (Rd2 & H2 & h2). exact (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRd H2 a a') h2). }
    assert (Hcod' : forall ρ' a a' (ha : domR' ρ' a a'),
               LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (ktyl ρ' Bπ)[lsingle a] (ktyl ρ' B'π)[lsingle a'] k2
                 (codR' ρ' a a' ha)).
    { intros ρ' a a' ha. destruct (Back ρ' a a' ha) as (Na & Na' & hx).
      destruct (Cod ρ' _ _ hx) as (Rc & HRc & _). rewrite !(rt_tm Hinv') in HRc by assumption.
      refine (LR_releq _ _ _ _ _ _ _ _ _ HRc _).
      intros b b'; split; [intros h; exists Rc; exact (conj HRc h) |].
      intros (Rc2 & H2 & h2). exact (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRc H2 b b') h2). }
    exists (WRel (Gp π G) Γ[pφ π]ᵤ k1 k2 Aπ Bπ domR' codR').
    split.
    + apply (LRw n (LRbelow n) (Gp π G) Γ[pφ π]ᵤ T[pφ π]ᵤ T'[pφ π]ᵤ (lvsubst l (pφ π)) k1 k2
               (lvsubst l3 (pφ π)) (lvsubst l4 (pφ π)) Aπ Bπ A'π B'π domR' codR').
      * exact P'.
      * exact Hdom'.
      * exact Hcod'.
      * apply releq_refl.
    + subst codR' domR' Aπ A'π Bπ B'π k1 k2.
      intros t t' Nt Nt'. rewrite (HR t t'). split.
      * intros H. refine (WRel_perm π πi _ _ _ _ _ _ _ _ _ _ H Hp HG HΓ _ _ _ _ eq_refl eq_refl NA NB _ _ _).
        -- intros ρ ρ' Hk x y Nx Ny h.
           destruct (IHdom ρ π πi (uperm_grow _ _ _ _ (kw_gL ρ) Hp)) as (Rd & HRd & ERd).
           rewrite (proj1 Hk), (proj1 (proj2 Hk)), !(kcorr_kty Hk) in HRd.
           exists Rd. exact (conj HRd (proj1 (ERd x y Nx Ny) h)).
        -- intros ρ ρ' Hk x y h x' y' h' -> -> u v (Rc & HRc & Huv).
           destruct (IHcod ρ x y h π πi (uperm_grow _ _ _ _ (kw_gL ρ) Hp)) as (Rc0 & HRc0 & ERc0).
           rewrite (proj1 Hk), (proj1 (proj2 Hk)), !usubst_lsingle_ty', !(kcorr_ktyl Hk) in HRc0.
           pose proof (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRc0 HRc u v) Huv) as X.
           destruct (LR_rel_dnf HRc _ _ Huv) as [Nu Nv].
           apply (ERc0 _ _ (dnf_us_tm _ _) (dnf_us_tm _ _)). rewrite !(rt_tm Hinv') by assumption. exact X.
        -- intros ρ' x y h' u v (Rc & HRc & Huv). exact (LR_rel_dnf HRc _ _ Huv).
      * intros H.
        assert (Hk' : forall (ρ0 : kwk (Gp π G) Γ[pφ π]ᵤ) (ρ : kwk G Γ), kcorr πi ρ0 ρ -> kcorr π ρ ρ0)
          by (intros ρ0 ρ Hk0; exact (kcorr_flip ρ0 ρ (uperm_grow _ _ _ _ (kw_gL ρ0) Hp) Hk0)).
        pose proof (WRel_perm πi π _ _ _ _ _ _ _ _ _ _ H Hpi HG' (dnf_us_ctx _ _) G Γ domR codR
                      (Gp_rt Hp HG) (rt_ctx Hinv _ HΓ) (dnf_us_ty _ _) (dnf_us_ty _ _)) as X.
        rewrite !(rt_lvl Hinv), (rt_ty Hinv _ NA), (rt_ty Hinv _ NB), (rt_tm Hinv _ Nt), (rt_tm Hinv _ Nt') in X.
        apply X.
        -- intros ρ0 ρ Hk0 x y Nx Ny (Rd2 & H2 & h2). pose proof (Hk' _ _ Hk0) as Hk.
           destruct (IHdom ρ π πi (uperm_grow _ _ _ _ (kw_gL ρ) Hp)) as (Rd & HRd & ERd).
           rewrite (proj1 Hk), (proj1 (proj2 Hk)), !(kcorr_kty Hk) in HRd.
           pose proof (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRd H2 x y) h2) as h.
           apply (ERd _ _ (dnf_us_tm _ _) (dnf_us_tm _ _)). rewrite !(rt_tm Hinv') by assumption. exact h.
        -- intros ρ0 ρ Hk0 x y h x' y' h' -> -> u v Huv. pose proof (Hk' _ _ Hk0) as Hk.
           destruct h as (Rd2 & H2 & h2). destruct (LR_rel_dnf H2 _ _ h2) as [Nx Ny].
           destruct (IHcod ρ _ _ h' π πi (uperm_grow _ _ _ _ (kw_gL ρ) Hp)) as (Rc & HRc & ERc).
           rewrite (proj1 Hk), (proj1 (proj2 Hk)), !usubst_lsingle_ty', !(kcorr_ktyl Hk), !(rt_tm Hinv')
             in HRc by assumption.
           destruct (LR_rel_dnf (codAd ρ _ _ h') _ _ Huv) as [Nu Nv].
           exists Rc. exact (conj HRc (proj1 (ERc u v Nu Nv) Huv)).
        -- intros ρ x y h u v Huv. exact (LR_rel_dnf (codAd ρ x y h) _ _ Huv).
  - (* Wf: the domain as W's; the arity through the pull-back; the terms by
       [WfRel_perm], backwards along [πi] *)
    set (Aπ := A[pφ π]ᵤ). set (A'π := A'[pφ π]ᵤ). set (Nπ := N[pφ π]ᵤ). set (N'π := N'[pφ π]ᵤ).
    set (k1 := lvsubst l1 (pφ π)).
    pose proof (wf_ty_dnf HA) as NA. pose proof (wf_ty_dnf HA') as NA'.
    pose proof (wf_tm_dnf HNt) as NN. pose proof (wf_tm_dnf HNt') as NN'.
    set (domR' := fun (ρ' : kwk (Gp π G) Γ[pφ π]ᵤ) a a' =>
           exists Rd, LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (kty ρ' Aπ) (kty ρ' A'π) k1 Rd /\ Rd a a').
    assert (Dom : forall ρ', exists Rd,
               LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (kty ρ' Aπ) (kty ρ' A'π) k1 Rd /\
               forall x y, dnftm x -> dnftm y -> (domR (kw_pull Hp HG HΓ ρ') x y <-> Rd x[pφ π]ᵤ y[pφ π]ᵤ)).
    { intros ρ'.
      assert (Hpρ : uperm π πi (gL (kw_G (kw_pull Hp HG HΓ ρ')))) by exact (uperm_grow _ _ _ _ (kw_gL ρ') Hp).
      destruct (IHdom (kw_pull Hp HG HΓ ρ') π πi Hpρ) as (Rd & HRd & ERd).
      rewrite (pull_G Hp HG HΓ ρ'), (pull_Δ Hp HG HΓ ρ'), !(kty_pull Hp HG HΓ ρ') in HRd.
      exists Rd. exact (conj HRd ERd). }
    assert (Back : forall ρ' a a', domR' ρ' a a' ->
               dnftm a /\ dnftm a' /\ domR (kw_pull Hp HG HΓ ρ') a[pφ πi]ᵤ a'[pφ πi]ᵤ).
    { intros ρ' a a' (Rd2 & H2 & h2). destruct (Dom ρ') as (Rd & HRd & ERd).
      destruct (LR_rel_dnf H2 _ _ h2) as [Na Na'].
      pose proof (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRd H2 a a') h2) as h.
      refine (conj Na (conj Na' _)). apply (ERd _ _ (dnf_us_tm _ _) (dnf_us_tm _ _)).
      rewrite !(rt_tm Hinv') by assumption. exact h. }
    assert (Hdom' : forall ρ', LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (kty ρ' Aπ) (kty ρ' A'π) k1 (domR' ρ')).
    { intros ρ'. destruct (Dom ρ') as (Rd & HRd & _). refine (LR_releq _ _ _ _ _ _ _ _ _ HRd _).
      intros a a'; split; [intros h; exists Rd; exact (conj HRd h) |].
      intros (Rd2 & H2 & h2). exact (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRd H2 a a') h2). }
    assert (Har : forall ρ' a a', domR' ρ' a a' ->
               NatRel (kw_G ρ') (kw_Δ ρ') (ktml ρ' Nπ)[lsingle a] (ktml ρ' N'π)[lsingle a']).
    { intros ρ' a a' ha. destruct (Back ρ' a a' ha) as (Na & Na' & hx).
      pose proof (NatRel_perm (G := kw_G (kw_pull Hp HG HΓ ρ')) (uperm_grow _ _ _ _ (kw_gL ρ') Hp) _ _ (arAd _ _ _ hx)) as X.
      rewrite (pull_G Hp HG HΓ ρ'), (pull_Δ Hp HG HΓ ρ'), !usubst_lsingle, !(ktml_pull Hp HG HΓ ρ'),
        !(rt_tm Hinv') in X by assumption.
      exact X. }
    exists (WfRel (Gp π G) Γ[pφ π]ᵤ k1 Aπ Nπ domR'). split.
    + apply (LRwf n (LRbelow n) (Gp π G) Γ[pφ π]ᵤ T[pφ π]ᵤ T'[pφ π]ᵤ (lvsubst l (pφ π)) k1 (lvsubst l2 (pφ π))
               Aπ A'π Nπ N'π domR').
      * exact (pg_lequiv Hp Hl).
      * exact (pg_lequiv Hp Hl2).
      * exact (pg_lwf Hp Hw).
      * exact (pg_tyred Hp HT).
      * exact (pg_tyred Hp HT').
      * exact (pg_ty Hp HA).
      * exact (pg_ty Hp HA').
      * exact (pg_tm Hp HNt).
      * exact (pg_tm Hp HNt').
      * exact (pg_geq_ty Hp HAA).
      * exact (pg_geq_tm Hp HNN).
      * exact Hdom'.
      * exact Har.
      * apply releq_refl.
    + subst domR' Aπ A'π Nπ N'π k1.
      intros t t' Nt Nt'. rewrite (HR t t'). split.
      * intros H. refine (proj1 (WfRel_perm π πi) _ _ _ _ _ _ _ _ H Hp HG HΓ _ _ _ eq_refl eq_refl NA NN _).
        intros ρ ρ' Hk x y Nx Ny h.
        destruct (IHdom ρ π πi (uperm_grow _ _ _ _ (kw_gL ρ) Hp)) as (Rd & HRd & ERd).
        rewrite (proj1 Hk), (proj1 (proj2 Hk)), !(kcorr_kty Hk) in HRd.
        exists Rd. exact (conj HRd (proj1 (ERd x y Nx Ny) h)).
      * intros H.
        assert (Hk' : forall (ρ0 : kwk (Gp π G) Γ[pφ π]ᵤ) (ρ : kwk G Γ), kcorr πi ρ0 ρ -> kcorr π ρ ρ0)
          by (intros ρ0 ρ Hk0; exact (kcorr_flip ρ0 ρ (uperm_grow _ _ _ _ (kw_gL ρ0) Hp) Hk0)).
        pose proof (proj1 (WfRel_perm πi π) _ _ _ _ _ _ _ _ H Hpi HG' (dnf_us_ctx _ _) G Γ domR
                      (Gp_rt Hp HG) (rt_ctx Hinv _ HΓ) (dnf_us_ty _ _) (dnf_us_tm _ _)) as X.
        rewrite !(rt_lvl Hinv), (rt_ty Hinv _ NA), (rt_tm Hinv _ NN), (rt_tm Hinv _ Nt), (rt_tm Hinv _ Nt') in X.
        apply X.
        intros ρ0 ρ Hk0 x y Nx Ny (Rd2 & H2 & h2). pose proof (Hk' _ _ Hk0) as Hk.
        destruct (IHdom ρ π πi (uperm_grow _ _ _ _ (kw_gL ρ) Hp)) as (Rd & HRd & ERd).
        rewrite (proj1 Hk), (proj1 (proj2 Hk)), !(kcorr_kty Hk) in HRd.
        pose proof (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRd H2 x y) h2) as h.
        apply (ERd _ _ (dnf_us_tm _ _) (dnf_us_tm _ _)). rewrite !(rt_tm Hinv') by assumption. exact h.
  - (* ∥·∥: along the carrier's permuted relation *)
    cbn in NW. rename NW into NA.
    destruct (IHRQ π πi Hp) as (RA' & HRA' & ERA).
    destruct (LR_tm_per _ _ _ _ _ _ _ HRA') as [Hs' Ht'].
    assert (F : forall x y, RQ x y -> RA' x[pφ π]ᵤ y[pφ π]ᵤ).
    { intros x y H0. destruct (LR_rel_dnf HRQ _ _ H0) as [Nx Ny]. exact (proj1 (ERA x y Nx Ny) H0). }
    assert (B : forall x y, RA' x y -> RQ x[pφ πi]ᵤ y[pφ πi]ᵤ).
    { intros x y H0. destruct (LR_rel_dnf HRA' _ _ H0) as [Nx Ny].
      apply (ERA _ _ (dnf_us_tm _ _) (dnf_us_tm _ _)). rewrite !(rt_tm Hinv') by assumption. exact H0. }
    exists (SqRel (Gp π G) Γ[pφ π]ᵤ (lvsubst l1 (pφ π)) A[pφ π]ᵤ RA'). split.
    + eapply LRsq; [exact (pg_lequiv Hp Hl) | exact (pg_lequiv Hp Hl2) | exact (pg_lwf Hp Hw)
                   | exact (pg_tyred Hp HT) | exact (pg_tyred Hp HT') | exact (pg_ty Hp HA)
                   | exact (pg_geq_ty Hp HAA) | exact HRA' | exact Hs' | exact Ht' | apply releq_refl].
    + intros t t' Nt Nt'. rewrite (HR t t'). split; [apply (SqRel_perm Hp F) |].
      intros X. apply (SqRel_perm (G := Gp π G) Hpi B) in X.
      rewrite (Gp_rt Hp HG), (rt_ctx Hinv _ HΓ), (rt_lvl Hinv), (rt_ty Hinv _ NA), !(rt_tm Hinv) in X
        by assumption.
      exact X.
  - (* IWf: the index and shape domains as Wf's; the output and child indices
       through the pull-back; the terms by [IWfRel_perm], backwards along [πi] *)
    pose proof (wf_ty_dnf HwX) as NX. pose proof (wf_ty_dnf HwX') as NX'.
    pose proof (wf_ty_dnf HwA) as NA. pose proof (wf_ty_dnf HwA') as NA'.
    pose proof (wf_tm_dnf HwN) as NN. pose proof (wf_tm_dnf HwN') as NN'.
    pose proof (wf_tm_dnf HwO) as NO. pose proof (wf_tm_dnf HwO') as NO'.
    pose proof (wf_tm_dnf HwC) as NC. pose proof (wf_tm_dnf HwC') as NC'.
    pose proof (wf_tm_dnf Hwm) as Nm. pose proof (wf_tm_dnf Hwm') as Nm'.
    set (idxR' := fun (ρ' : kwk (Gp π G) Γ[pφ π]ᵤ) x y =>
           exists Ri, LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (kty ρ' wX[pφ π]ᵤ) (kty ρ' wX'[pφ π]ᵤ)
                        (lvsubst wli1 (pφ π)) Ri /\ Ri x y).
    set (domR' := fun (ρ' : kwk (Gp π G) Γ[pφ π]ᵤ) a a' =>
           exists Rd, LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (kty ρ' wA[pφ π]ᵤ) (kty ρ' wA'[pφ π]ᵤ)
                        (lvsubst wl1 (pφ π)) Rd /\ Rd a a').
    (* the indices and the domains at a world of the permuted context, through its pull-back *)
    assert (Idx : forall ρ', exists Ri,
               LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (kty ρ' wX[pφ π]ᵤ) (kty ρ' wX'[pφ π]ᵤ) (lvsubst wli1 (pφ π)) Ri /\
               forall x y, dnftm x -> dnftm y -> (widxR (kw_pull Hp HG HΓ ρ') x y <-> Ri x[pφ π]ᵤ y[pφ π]ᵤ)).
    { intros ρ'.
      assert (Hpρ : uperm π πi (gL (kw_G (kw_pull Hp HG HΓ ρ')))) by exact (uperm_grow _ _ _ _ (kw_gL ρ') Hp).
      destruct (IHwidx (kw_pull Hp HG HΓ ρ') π πi Hpρ) as (Ri & HRi & ERi).
      rewrite (pull_G Hp HG HΓ ρ'), (pull_Δ Hp HG HΓ ρ'), !(kty_pull Hp HG HΓ ρ') in HRi.
      exists Ri. exact (conj HRi ERi). }
    assert (Dom : forall ρ', exists Rd,
               LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (kty ρ' wA[pφ π]ᵤ) (kty ρ' wA'[pφ π]ᵤ) (lvsubst wl1 (pφ π)) Rd /\
               forall x y, dnftm x -> dnftm y -> (wdomR (kw_pull Hp HG HΓ ρ') x y <-> Rd x[pφ π]ᵤ y[pφ π]ᵤ)).
    { intros ρ'.
      assert (Hpρ : uperm π πi (gL (kw_G (kw_pull Hp HG HΓ ρ')))) by exact (uperm_grow _ _ _ _ (kw_gL ρ') Hp).
      destruct (IHwdom (kw_pull Hp HG HΓ ρ') π πi Hpρ) as (Rd & HRd & ERd).
      rewrite (pull_G Hp HG HΓ ρ'), (pull_Δ Hp HG HΓ ρ'), !(kty_pull Hp HG HΓ ρ') in HRd.
      exists Rd. exact (conj HRd ERd). }
    (* a related pair of the permuted relations comes from one of the original *)
    assert (BackI : forall ρ' x y, idxR' ρ' x y ->
               dnftm x /\ dnftm y /\ widxR (kw_pull Hp HG HΓ ρ') x[pφ πi]ᵤ y[pφ πi]ᵤ).
    { intros ρ' x y (Ri2 & H2 & h2). destruct (Idx ρ') as (Ri & HRi & ERi).
      destruct (LR_rel_dnf H2 _ _ h2) as [Nx Ny].
      pose proof (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRi H2 x y) h2) as h.
      refine (conj Nx (conj Ny _)). apply (ERi _ _ (dnf_us_tm _ _) (dnf_us_tm _ _)).
      rewrite !(rt_tm Hinv') by assumption. exact h. }
    assert (Back : forall ρ' a a', domR' ρ' a a' ->
               dnftm a /\ dnftm a' /\ wdomR (kw_pull Hp HG HΓ ρ') a[pφ πi]ᵤ a'[pφ πi]ᵤ).
    { intros ρ' a a' (Rd2 & H2 & h2). destruct (Dom ρ') as (Rd & HRd & ERd).
      destruct (LR_rel_dnf H2 _ _ h2) as [Na Na'].
      pose proof (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRd H2 a a') h2) as h.
      refine (conj Na (conj Na' _)). apply (ERd _ _ (dnf_us_tm _ _) (dnf_us_tm _ _)).
      rewrite !(rt_tm Hinv') by assumption. exact h. }
    assert (ForwI : forall ρ' x y, dnftm x -> dnftm y -> widxR (kw_pull Hp HG HΓ ρ') x y ->
               idxR' ρ' x[pφ π]ᵤ y[pφ π]ᵤ).
    { intros ρ' x y Nx Ny h. destruct (Idx ρ') as (Ri & HRi & ERi).
      exists Ri. exact (conj HRi (proj1 (ERi x y Nx Ny) h)). }
    assert (Hidx' : forall ρ', LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (kty ρ' wX[pφ π]ᵤ) (kty ρ' wX'[pφ π]ᵤ)
                                 (lvsubst wli1 (pφ π)) (idxR' ρ')).
    { intros ρ'. destruct (Idx ρ') as (Ri & HRi & _). refine (LR_releq _ _ _ _ _ _ _ _ _ HRi _).
      intros x y; split; [intros h; exists Ri; exact (conj HRi h) |].
      intros (Ri2 & H2 & h2). exact (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRi H2 x y) h2). }
    assert (Hdom' : forall ρ', LR n (LRbelow n) (kw_G ρ') (kw_Δ ρ') (kty ρ' wA[pφ π]ᵤ) (kty ρ' wA'[pφ π]ᵤ)
                                 (lvsubst wl1 (pφ π)) (domR' ρ')).
    { intros ρ'. destruct (Dom ρ') as (Rd & HRd & _). refine (LR_releq _ _ _ _ _ _ _ _ _ HRd _).
      intros a a'; split; [intros h; exists Rd; exact (conj HRd h) |].
      intros (Rd2 & H2 & h2). exact (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRd H2 a a') h2). }
    assert (Hisym' : forall ρ' x y, idxR' ρ' x y -> idxR' ρ' y x).
    { intros ρ' x y h. destruct (BackI ρ' x y h) as (Nx & Ny & h').
      pose proof (ForwI ρ' _ _ (dnf_us_tm _ _) (dnf_us_tm _ _) (Hwisym _ _ _ h')) as Y.
      rewrite !(rt_tm Hinv') in Y by assumption. exact Y. }
    assert (Histr' : forall ρ' x y z, idxR' ρ' x y -> idxR' ρ' y z -> idxR' ρ' x z).
    { intros ρ' x y z h1 h2. destruct (BackI ρ' x y h1) as (Nx & Ny & h1').
      destruct (BackI ρ' y z h2) as (_ & Nz & h2').
      pose proof (ForwI ρ' _ _ (dnf_us_tm _ _) (dnf_us_tm _ _) (Hwistr _ _ _ _ h1' h2')) as Y.
      rewrite !(rt_tm Hinv') in Y by assumption. exact Y. }
    assert (Har' : forall ρ' a a', domR' ρ' a a' ->
               NatRel (kw_G ρ') (kw_Δ ρ') (ktml ρ' wN[pφ π]ᵤ)[lsingle a] (ktml ρ' wN'[pφ π]ᵤ)[lsingle a']).
    { intros ρ' a a' ha. destruct (Back ρ' a a' ha) as (Na & Na' & hx).
      pose proof (NatRel_perm (G := kw_G (kw_pull Hp HG HΓ ρ')) (uperm_grow _ _ _ _ (kw_gL ρ') Hp) _ _
                    (warAd _ _ _ hx)) as Y.
      rewrite (pull_G Hp HG HΓ ρ'), (pull_Δ Hp HG HΓ ρ'), !usubst_lsingle, !(ktml_pull Hp HG HΓ ρ'),
        !(rt_tm Hinv') in Y by assumption.
      exact Y. }
    assert (Hot' : forall ρ' a a', domR' ρ' a a' ->
               idxR' ρ' (ktml ρ' wO[pφ π]ᵤ)[lsingle a] (ktml ρ' wO'[pφ π]ᵤ)[lsingle a']).
    { intros ρ' a a' ha. destruct (Back ρ' a a' ha) as (Na & Na' & hx).
      pose proof (ForwI ρ' _ _ (subst_dnf _ _ (dnf_ktml _ _ NO) (lk_dnf_lsingle _ (dnf_us_tm _ _)))
                    (subst_dnf _ _ (dnf_ktml _ _ NO') (lk_dnf_lsingle _ (dnf_us_tm _ _))) (wotAd _ _ _ hx)) as Y.
      rewrite !usubst_lsingle, !(ktml_pull Hp HG HΓ ρ'), !(rt_tm Hinv') in Y by assumption. exact Y. }
    assert (Hch' : forall ρ' a a', domR' ρ' a a' -> forall p p',
               PosRel (kw_G ρ') (kw_Δ ρ') (ktml ρ' wN[pφ π]ᵤ)[lsingle a] (ktml ρ' wN'[pφ π]ᵤ)[lsingle a'] p p' ->
               idxR' ρ' (ktmll ρ' wC[pφ π]ᵤ)[lsingle2 a p] (ktmll ρ' wC'[pφ π]ᵤ)[lsingle2 a' p']).
    { intros ρ' a a' ha p p' HP. destruct (Back ρ' a a' ha) as (Na & Na' & hx).
      destruct (PosRel_dnf HP) as [Np Np'].
      pose proof (PosRel_perm (uperm_grow _ _ _ _ (kw_gL ρ') Hpi) HP) as HP'.
      rewrite !usubst_lsingle, !ktml_us, (rt_tm Hinv _ NN), (rt_tm Hinv _ NN') in HP'.
      pose proof (ForwI ρ' _ _ (subst_dnf _ _ (dnf_ktmll _ _ NC) (lk_dnf_lsingle2 _ _ (dnf_us_tm _ _) (dnf_us_tm _ _)))
                    (subst_dnf _ _ (dnf_ktmll _ _ NC') (lk_dnf_lsingle2 _ _ (dnf_us_tm _ _) (dnf_us_tm _ _)))
                    (wchAd (kw_pull Hp HG HΓ ρ') _ _ hx _ _ HP')) as Y.
      rewrite !usubst_lsingle2, !(ktmll_pull Hp HG HΓ ρ'), !(rt_tm Hinv') in Y by assumption. exact Y. }
    assert (Hix' : forall ρ', idxR' ρ' (ktm ρ' wm[pφ π]ᵤ) (ktm ρ' wm'[pφ π]ᵤ)).
    { intros ρ'. pose proof (ForwI ρ' _ _ (dnf_ktm _ _ Nm) (dnf_ktm _ _ Nm') (wixAd (kw_pull Hp HG HΓ ρ'))) as Y.
      rewrite !(ktm_pull Hp HG HΓ ρ') in Y. exact Y. }
    exists (IWfRel (Gp π G) Γ[pφ π]ᵤ (lvsubst wl1 (pφ π)) (lvsubst wli1 (pφ π)) wX[pφ π]ᵤ wA[pφ π]ᵤ wN[pφ π]ᵤ
              wO[pφ π]ᵤ wC[pφ π]ᵤ idxR' domR' wm[pφ π]ᵤ).
    split.
    + apply (LRiwf n (LRbelow n) (Gp π G) Γ[pφ π]ᵤ T[pφ π]ᵤ T'[pφ π]ᵤ (lvsubst l (pφ π)) (lvsubst wl1 (pφ π))
               (lvsubst wli1 (pφ π)) (lvsubst wl2 (pφ π)) (lvsubst wli2 (pφ π)) wX[pφ π]ᵤ wX'[pφ π]ᵤ
               wA[pφ π]ᵤ wA'[pφ π]ᵤ wN[pφ π]ᵤ wN'[pφ π]ᵤ wO[pφ π]ᵤ wO'[pφ π]ᵤ wC[pφ π]ᵤ wC'[pφ π]ᵤ
               wm[pφ π]ᵤ wm'[pφ π]ᵤ idxR' domR').
      * exact (pg_lequiv Hp Hl).
      * exact (pg_lequiv Hp Hl2).
      * exact (pg_lequiv Hp Hwli2).
      * exact (pg_lwf Hp Hw).
      * exact (pg_lwf Hp Hwwi).
      * exact (pg_tyred Hp HT).
      * exact (pg_tyred Hp HT').
      * exact (pg_ty Hp HwX).
      * exact (pg_ty Hp HwX').
      * exact (pg_ty Hp HwA).
      * exact (pg_ty Hp HwA').
      * exact (pg_tm Hp HwN).
      * exact (pg_tm Hp HwN').
      * pose proof (pg_tm Hp HwO) as Y. rewrite usubst_ren_ty in Y. exact Y.
      * pose proof (pg_tm Hp HwO') as Y. rewrite usubst_ren_ty in Y. exact Y.
      * pose proof (pg_tm Hp HwC) as Y. rewrite !usubst_ren_ty in Y. exact Y.
      * pose proof (pg_tm Hp HwC') as Y. rewrite !usubst_ren_ty in Y. exact Y.
      * exact (pg_tm Hp Hwm).
      * exact (pg_tm Hp Hwm').
      * exact (pg_geq_ty Hp HwXX).
      * exact (pg_geq_ty Hp HwAA).
      * exact (pg_geq_tm Hp HwNN).
      * pose proof (pg_geq_tm Hp HwOO) as Y. rewrite usubst_ren_ty in Y. exact Y.
      * pose proof (pg_geq_tm Hp HwCC) as Y. rewrite !usubst_ren_ty in Y. exact Y.
      * exact (pg_geq_tm Hp Hwmm).
      * exact Hidx'.
      * exact Hisym'.
      * exact Histr'.
      * exact Hdom'.
      * exact Har'.
      * exact Hot'.
      * exact Hch'.
      * exact Hix'.
      * apply releq_refl.
    + subst idxR' domR'.
      intros t t' Nt Nt'. rewrite (HR t t'). split.
      * intros H. refine (proj1 (IWfRel_perm π πi) _ _ _ _ _ _ _ _ _ _ _ _ _ _ H Hp HG HΓ _ _ _ _ eq_refl eq_refl
                            NX NA NN NO NC Nm _ _).
        -- intros ρ ρ' Hk x y Nx Ny h.
           destruct (IHwidx ρ π πi (uperm_grow _ _ _ _ (kw_gL ρ) Hp)) as (Ri & HRi & ERi).
           rewrite (proj1 Hk), (proj1 (proj2 Hk)), !(kcorr_kty Hk) in HRi.
           exists Ri. exact (conj HRi (proj1 (ERi x y Nx Ny) h)).
        -- intros ρ ρ' Hk x y Nx Ny h.
           destruct (IHwdom ρ π πi (uperm_grow _ _ _ _ (kw_gL ρ) Hp)) as (Rd & HRd & ERd).
           rewrite (proj1 Hk), (proj1 (proj2 Hk)), !(kcorr_kty Hk) in HRd.
           exists Rd. exact (conj HRd (proj1 (ERd x y Nx Ny) h)).
      * intros H.
        assert (Hk' : forall (ρ0 : kwk (Gp π G) Γ[pφ π]ᵤ) (ρ : kwk G Γ), kcorr πi ρ0 ρ -> kcorr π ρ ρ0)
          by (intros ρ0 ρ Hk0; exact (kcorr_flip ρ0 ρ (uperm_grow _ _ _ _ (kw_gL ρ0) Hp) Hk0)).
        pose proof (proj1 (IWfRel_perm πi π) _ _ _ _ _ _ _ _ _ _ _ _ _ _ H Hpi HG' (dnf_us_ctx _ _) G Γ widxR wdomR
                      (Gp_rt Hp HG) (rt_ctx Hinv _ HΓ) (dnf_us_ty _ _) (dnf_us_ty _ _) (dnf_us_tm _ _)
                      (dnf_us_tm _ _) (dnf_us_tm _ _) (dnf_us_tm _ _)) as X.
        rewrite !(rt_lvl Hinv), (rt_ty Hinv _ NX), (rt_ty Hinv _ NA), (rt_tm Hinv _ NN), (rt_tm Hinv _ NO),
          (rt_tm Hinv _ NC), (rt_tm Hinv _ Nm), (rt_tm Hinv _ Nt), (rt_tm Hinv _ Nt') in X.
        apply X.
        -- intros ρ0 ρ Hk0 x y Nx Ny (Ri2 & H2 & h2). pose proof (Hk' _ _ Hk0) as Hk.
           destruct (IHwidx ρ π πi (uperm_grow _ _ _ _ (kw_gL ρ) Hp)) as (Ri & HRi & ERi).
           rewrite (proj1 Hk), (proj1 (proj2 Hk)), !(kcorr_kty Hk) in HRi.
           pose proof (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRi H2 x y) h2) as h.
           apply (ERi _ _ (dnf_us_tm _ _) (dnf_us_tm _ _)). rewrite !(rt_tm Hinv') by assumption. exact h.
        -- intros ρ0 ρ Hk0 x y Nx Ny (Rd2 & H2 & h2). pose proof (Hk' _ _ Hk0) as Hk.
           destruct (IHwdom ρ π πi (uperm_grow _ _ _ _ (kw_gL ρ) Hp)) as (Rd & HRd & ERd).
           rewrite (proj1 Hk), (proj1 (proj2 Hk)), !(kcorr_kty Hk) in HRd.
           pose proof (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRd H2 x y) h2) as h.
           apply (ERd _ _ (dnf_us_tm _ _) (dnf_us_tm _ _)). rewrite !(rt_tm Hinv') by assumption. exact h.
  - (* M: the index, shapes and positions as IWf's, each through a world of
       the original context corresponding to one of the permuted; the
       terms by [MRn_perm], backwards along [πi] *)
    pose proof (wf_ty_dnf HmX) as NX. pose proof (wf_ty_dnf HmX') as NX'.
    pose proof (wf_ty_dnf HmA) as NA. pose proof (wf_ty_dnf HmA') as NA'.
    pose proof (wf_ty_dnf HmB) as NB. pose proof (wf_ty_dnf HmB') as NB'.
    pose proof (wf_tm_dnf HmC) as NC. pose proof (wf_tm_dnf HmC') as NC'.
    pose proof (wf_tm_dnf Hmm) as Nm. pose proof (wf_tm_dnf Hmm') as Nm'.
    set (idxR' := fun (ρ0 : kwk (Gp π G) Γ[pφ π]ᵤ) x y =>
           exists Ri, LR n (LRbelow n) (kw_G ρ0) (kw_Δ ρ0) (kty ρ0 mX[pφ π]ᵤ) (kty ρ0 mX'[pφ π]ᵤ)
                        (lvsubst mli (pφ π)) Ri /\ Ri x y).
    set (shR' := fun (ρ0 : kwk (Gp π G) Γ[pφ π]ᵤ) x y a b =>
           exists Rs, LR n (LRbelow n) (kw_G ρ0) (kw_Δ ρ0) (ktyl ρ0 mA[pφ π]ᵤ)[lsingle x]
                        (ktyl ρ0 mA'[pφ π]ᵤ)[lsingle y] (lvsubst ml1 (pφ π)) Rs /\ Rs a b).
    set (posR' := fun (ρ0 : kwk (Gp π G) Γ[pφ π]ᵤ) x y a b p q =>
           exists Rp, LR n (LRbelow n) (kw_G ρ0) (kw_Δ ρ0) (ktyll ρ0 mB[pφ π]ᵤ)[lsingle2 x a]
                        (ktyll ρ0 mB'[pφ π]ᵤ)[lsingle2 y b] (lvsubst ml2 (pφ π)) Rp /\ Rp p q).
    assert (Hup : forall ρ : kwk G Γ, uperm π πi (gL (kw_G ρ)))
      by (intros ρ; exact (uperm_grow _ _ _ _ (kw_gL ρ) Hp)).
    (* the three relations at a world of the permuted context, through a
       corresponding world of the original *)
    assert (LIdx : forall (ρ : kwk G Γ) (ρ0 : kwk (Gp π G) Γ[pφ π]ᵤ), kcorr π ρ ρ0 -> exists Ri,
               LR n (LRbelow n) (kw_G ρ0) (kw_Δ ρ0) (kty ρ0 mX[pφ π]ᵤ) (kty ρ0 mX'[pφ π]ᵤ) (lvsubst mli (pφ π)) Ri /\
               forall x y, dnftm x -> dnftm y -> (midxR ρ x y <-> Ri x[pφ π]ᵤ y[pφ π]ᵤ)).
    { intros ρ ρ0 Hk. destruct (IHmidx ρ π πi (Hup ρ)) as (Ri & HRi & ERi).
      rewrite (proj1 Hk), (proj1 (proj2 Hk)), !(kcorr_kty Hk) in HRi. exists Ri. exact (conj HRi ERi). }
    assert (LSh : forall (ρ : kwk G Γ) (ρ0 : kwk (Gp π G) Γ[pφ π]ᵤ), kcorr π ρ ρ0 -> forall x y, midxR ρ x y ->
               exists Rs, LR n (LRbelow n) (kw_G ρ0) (kw_Δ ρ0) (ktyl ρ0 mA[pφ π]ᵤ)[lsingle x[pφ π]ᵤ]
                 (ktyl ρ0 mA'[pφ π]ᵤ)[lsingle y[pφ π]ᵤ] (lvsubst ml1 (pφ π)) Rs /\
               forall a b, dnftm a -> dnftm b -> (mshR ρ x y a b <-> Rs a[pφ π]ᵤ b[pφ π]ᵤ)).
    { intros ρ ρ0 Hk x y h. destruct (IHmsh ρ x y h π πi (Hup ρ)) as (Rs & HRs & ERs).
      rewrite (proj1 Hk), (proj1 (proj2 Hk)), !usubst_lsingle_ty', !(kcorr_ktyl Hk) in HRs.
      exists Rs. exact (conj HRs ERs). }
    assert (LPos : forall (ρ : kwk G Γ) (ρ0 : kwk (Gp π G) Γ[pφ π]ᵤ), kcorr π ρ ρ0 -> forall x y a b,
               midxR ρ x y -> mshR ρ x y a b ->
               exists Rp, LR n (LRbelow n) (kw_G ρ0) (kw_Δ ρ0) (ktyll ρ0 mB[pφ π]ᵤ)[lsingle2 x[pφ π]ᵤ a[pφ π]ᵤ]
                 (ktyll ρ0 mB'[pφ π]ᵤ)[lsingle2 y[pφ π]ᵤ b[pφ π]ᵤ] (lvsubst ml2 (pφ π)) Rp /\
               forall p q, dnftm p -> dnftm q -> (mposR ρ x y a b p q <-> Rp p[pφ π]ᵤ q[pφ π]ᵤ)).
    { intros ρ ρ0 Hk x y a b h hs. destruct (IHmpos ρ x y a b h hs π πi (Hup ρ)) as (Rp & HRp & ERp).
      rewrite (proj1 Hk), (proj1 (proj2 Hk)), !usubst_lsingle2_ty, !(kcorr_ktyll Hk) in HRp.
      exists Rp. exact (conj HRp ERp). }
    (* forward and back along corresponding worlds *)
    assert (IdxF : forall ρ ρ0, kcorr π ρ ρ0 -> forall x y, dnftm x -> dnftm y -> midxR ρ x y ->
               idxR' ρ0 x[pφ π]ᵤ y[pφ π]ᵤ).
    { intros ρ ρ0 Hk x y Nx Ny h. destruct (LIdx ρ ρ0 Hk) as (Ri & HRi & ERi).
      exists Ri. exact (conj HRi (proj1 (ERi x y Nx Ny) h)). }
    assert (IdxB : forall ρ ρ0, kcorr π ρ ρ0 -> forall x y, idxR' ρ0 x y ->
               dnftm x /\ dnftm y /\ midxR ρ x[pφ πi]ᵤ y[pφ πi]ᵤ).
    { intros ρ ρ0 Hk x y (Ri2 & H2 & h2). destruct (LIdx ρ ρ0 Hk) as (Ri & HRi & ERi).
      destruct (LR_rel_dnf H2 _ _ h2) as [Nx Ny].
      pose proof (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRi H2 x y) h2) as h.
      refine (conj Nx (conj Ny _)). apply (ERi _ _ (dnf_us_tm _ _) (dnf_us_tm _ _)).
      rewrite !(rt_tm Hinv') by assumption. exact h. }
    assert (ShF : STr π midxR mshR shR').
    { intros ρ ρ0 Hk x y a b Nx Ny Na Nb h hs. destruct (LSh ρ ρ0 Hk x y h) as (Rs & HRs & ERs).
      exists Rs. exact (conj HRs (proj1 (ERs a b Na Nb) hs)). }
    assert (ShB : forall ρ ρ0, kcorr π ρ ρ0 -> forall x y, midxR ρ x y -> forall a b,
               shR' ρ0 x[pφ π]ᵤ y[pφ π]ᵤ a b -> dnftm a /\ dnftm b /\ mshR ρ x y a[pφ πi]ᵤ b[pφ πi]ᵤ).
    { intros ρ ρ0 Hk x y h a b (Rs2 & H2 & h2). destruct (LSh ρ ρ0 Hk x y h) as (Rs & HRs & ERs).
      destruct (LR_rel_dnf H2 _ _ h2) as [Na Nb].
      pose proof (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRs H2 a b) h2) as h'.
      refine (conj Na (conj Nb _)). apply (ERs _ _ (dnf_us_tm _ _) (dnf_us_tm _ _)).
      rewrite !(rt_tm Hinv') by assumption. exact h'. }
    assert (PosF : forall ρ ρ0, kcorr π ρ ρ0 -> forall x y a b, midxR ρ x y -> mshR ρ x y a b ->
               forall p q, dnftm p -> dnftm q -> mposR ρ x y a b p q ->
               posR' ρ0 x[pφ π]ᵤ y[pφ π]ᵤ a[pφ π]ᵤ b[pφ π]ᵤ p[pφ π]ᵤ q[pφ π]ᵤ).
    { intros ρ ρ0 Hk x y a b h hs p q Np Nq hp. destruct (LPos ρ ρ0 Hk x y a b h hs) as (Rp & HRp & ERp).
      exists Rp. exact (conj HRp (proj1 (ERp p q Np Nq) hp)). }
    assert (PosB : PTr π πi midxR mshR mposR posR').
    { intros ρ ρ0 Hk x y a b _ _ _ _ h hs p q (Rp2 & H2 & h2).
      destruct (LPos ρ ρ0 Hk x y a b h hs) as (Rp & HRp & ERp).
      destruct (LR_rel_dnf H2 _ _ h2) as [Np Nq].
      pose proof (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRp H2 p q) h2) as h'.
      refine (conj Np (conj Nq _)). apply (ERp _ _ (dnf_us_tm _ _) (dnf_us_tm _ _)).
      rewrite !(rt_tm Hinv') by assumption. exact h'. }
    (* a related index and shape of the permuted relations come from the original's *)
    assert (Back2 : forall ρ ρ0, kcorr π ρ ρ0 -> forall x y a b, idxR' ρ0 x y -> shR' ρ0 x y a b ->
               dnftm x /\ dnftm y /\ dnftm a /\ dnftm b /\ midxR ρ x[pφ πi]ᵤ y[pφ πi]ᵤ /\
               mshR ρ x[pφ πi]ᵤ y[pφ πi]ᵤ a[pφ πi]ᵤ b[pφ πi]ᵤ).
    { intros ρ ρ0 Hk x y a b h hs. destruct (IdxB ρ ρ0 Hk x y h) as (Nx & Ny & h').
      rewrite <- (rt_tm Hinv' _ Nx), <- (rt_tm Hinv' _ Ny) in hs.
      destruct (ShB ρ ρ0 Hk _ _ h' a b hs) as (Na & Nb & hs').
      exact (conj Nx (conj Ny (conj Na (conj Nb (conj h' hs'))))). }
    (* the premises of the permuted type, at the pulled-back worlds *)
    assert (KP : forall ρ0, kcorr π (kw_pull Hp HG HΓ ρ0) ρ0) by (intros ρ0; apply kcorr_pull).
    assert (Hidx' : forall ρ0, LR n (LRbelow n) (kw_G ρ0) (kw_Δ ρ0) (kty ρ0 mX[pφ π]ᵤ) (kty ρ0 mX'[pφ π]ᵤ)
                                 (lvsubst mli (pφ π)) (idxR' ρ0)).
    { intros ρ0. destruct (LIdx _ ρ0 (KP ρ0)) as (Ri & HRi & _). refine (LR_releq _ _ _ _ _ _ _ _ _ HRi _).
      intros x y; split; [intros h; exists Ri; exact (conj HRi h) |].
      intros (Ri2 & H2 & h2). exact (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRi H2 x y) h2). }
    assert (Hsh' : forall ρ0 x y, idxR' ρ0 x y ->
               LR n (LRbelow n) (kw_G ρ0) (kw_Δ ρ0) (ktyl ρ0 mA[pφ π]ᵤ)[lsingle x] (ktyl ρ0 mA'[pφ π]ᵤ)[lsingle y]
                 (lvsubst ml1 (pφ π)) (shR' ρ0 x y)).
    { intros ρ0 x y h. destruct (IdxB _ ρ0 (KP ρ0) x y h) as (Nx & Ny & h').
      destruct (LSh _ ρ0 (KP ρ0) _ _ h') as (Rs & HRs & _). rewrite !(rt_tm Hinv') in HRs by assumption.
      refine (LR_releq _ _ _ _ _ _ _ _ _ HRs _).
      intros a b; split; [intros hs; exists Rs; exact (conj HRs hs) |].
      intros (Rs2 & H2 & h2). exact (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRs H2 a b) h2). }
    assert (Hpos' : forall ρ0 x y a b, idxR' ρ0 x y -> shR' ρ0 x y a b ->
               LR n (LRbelow n) (kw_G ρ0) (kw_Δ ρ0) (ktyll ρ0 mB[pφ π]ᵤ)[lsingle2 x a]
                 (ktyll ρ0 mB'[pφ π]ᵤ)[lsingle2 y b] (lvsubst ml2 (pφ π)) (posR' ρ0 x y a b)).
    { intros ρ0 x y a b h hs. destruct (Back2 _ ρ0 (KP ρ0) x y a b h hs) as (Nx & Ny & Na & Nb & h' & hs').
      destruct (LPos _ ρ0 (KP ρ0) _ _ _ _ h' hs') as (Rp & HRp & _). rewrite !(rt_tm Hinv') in HRp by assumption.
      refine (LR_releq _ _ _ _ _ _ _ _ _ HRp _).
      intros p q; split; [intros hp; exists Rp; exact (conj HRp hp) |].
      intros (Rp2 & H2 & h2). exact (proj2 (LR_irrel _ _ _ _ _ _ _ _ _ _ HRp H2 p q) h2). }
    (* related positions come from the original's *)
    assert (BackP : forall ρ0 x y a b p q, idxR' ρ0 x y -> shR' ρ0 x y a b -> posR' ρ0 x y a b p q ->
               dnftm x /\ dnftm y /\ dnftm a /\ dnftm b /\ dnftm p /\ dnftm q /\
               midxR (kw_pull Hp HG HΓ ρ0) x[pφ πi]ᵤ y[pφ πi]ᵤ /\
               mshR (kw_pull Hp HG HΓ ρ0) x[pφ πi]ᵤ y[pφ πi]ᵤ a[pφ πi]ᵤ b[pφ πi]ᵤ /\
               mposR (kw_pull Hp HG HΓ ρ0) x[pφ πi]ᵤ y[pφ πi]ᵤ a[pφ πi]ᵤ b[pφ πi]ᵤ p[pφ πi]ᵤ q[pφ πi]ᵤ).
    { intros ρ0 x y a b p q h hs hp. destruct (Back2 _ ρ0 (KP ρ0) x y a b h hs) as (Nx & Ny & Na & Nb & h' & hs').
      rewrite <- (rt_tm Hinv' _ Nx), <- (rt_tm Hinv' _ Ny), <- (rt_tm Hinv' _ Na), <- (rt_tm Hinv' _ Nb) in hp.
      destruct (PosB _ ρ0 (KP ρ0) _ _ _ _ (dnf_us_tm _ _) (dnf_us_tm _ _) (dnf_us_tm _ _) (dnf_us_tm _ _) h' hs' p q hp)
        as (Np & Nq & hp').
      repeat split; assumption. }
    assert (Hch' : forall ρ0 x y a b p q, idxR' ρ0 x y -> shR' ρ0 x y a b -> posR' ρ0 x y a b p q ->
               idxR' ρ0 (ktmlll ρ0 mC[pφ π]ᵤ)[lsingle3 x a p] (ktmlll ρ0 mC'[pφ π]ᵤ)[lsingle3 y b q]).
    { intros ρ0 x y a b p q h hs hp.
      destruct (BackP ρ0 x y a b p q h hs hp) as (Nx & Ny & Na & Nb & Np & Nq & h' & hs' & hp').
      pose proof (IdxF _ ρ0 (KP ρ0) _ _
                    (subst_dnf _ _ (dnf_ktmlll _ _ NC) (lk_dnf_lsingle3 _ _ _ (dnf_us_tm _ _) (dnf_us_tm _ _) (dnf_us_tm _ _)))
                    (subst_dnf _ _ (dnf_ktmlll _ _ NC') (lk_dnf_lsingle3 _ _ _ (dnf_us_tm _ _) (dnf_us_tm _ _) (dnf_us_tm _ _)))
                    (mchAd _ _ _ _ _ _ _ h' hs' hp')) as Y.
      rewrite !usubst_lsingle3, !(kcorr_ktmlll (KP ρ0)), !(rt_tm Hinv') in Y by assumption. exact Y. }
    assert (Ext : forall (Δ : ctx) T l', (Δ ,, T @ l')[pφ π]ᵤ = Δ[pφ π]ᵤ ,, T[pφ π]ᵤ @ lvsubst l' (pφ π))
      by (intros; reflexivity).
    assert (HgB' : forall ρ0 x y, idxR' ρ0 x y ->
               [ kw_G ρ0 ; kw_Δ ρ0 ,, (ktyl ρ0 mA[pφ π]ᵤ)[lsingle x] @ lvsubst ml1 (pφ π)
                   ⊢ (ktyll ρ0 mB[pφ π]ᵤ)[llift (lsingle x)] ≈ (ktyll ρ0 mB'[pφ π]ᵤ)[llift (lsingle y)]
                   @ lvsubst ml2 (pφ π) ]).
    { intros ρ0 x y h. destruct (IdxB _ ρ0 (KP ρ0) x y h) as (Nx & Ny & h').
      pose proof (pg_geq_ty (Hup _) (mgB _ _ _ h')) as Y.
      rewrite Ext, (proj1 (KP ρ0)), (proj1 (proj2 (KP ρ0))), usubst_lsingle_ty', !usubst_llift_single_ty,
        (kcorr_ktyl (KP ρ0)), !(kcorr_ktyll (KP ρ0)), !(rt_tm Hinv') in Y by assumption.
      exact Y. }
    assert (HgC' : forall ρ0 x y, idxR' ρ0 x y ->
               [ kw_G ρ0 ; kw_Δ ρ0 ,, (ktyl ρ0 mA[pφ π]ᵤ)[lsingle x] @ lvsubst ml1 (pφ π)
                   ,, (ktyll ρ0 mB[pφ π]ᵤ)[llift (lsingle x)] @ lvsubst ml2 (pφ π)
                   ⊢ (ktmlll ρ0 mC[pφ π]ᵤ)[llift (llift (lsingle x))] ≈ (ktmlll ρ0 mC'[pφ π]ᵤ)[llift (llift (lsingle y))]
                   : (kty ρ0 mX[pφ π]ᵤ)⟨↑⟩⟨↑⟩ @ lvsubst mli (pφ π) ]).
    { intros ρ0 x y h. destruct (IdxB _ ρ0 (KP ρ0) x y h) as (Nx & Ny & h').
      pose proof (pg_geq_tm (Hup _) (mgC _ _ _ h')) as Y.
      rewrite !Ext, (proj1 (KP ρ0)), (proj1 (proj2 (KP ρ0))), usubst_lsingle_ty', usubst_llift_single_ty,
        !usubst_llift2_single, !usubst_ren_ty, (kcorr_ktyl (KP ρ0)), (kcorr_ktyll (KP ρ0)),
        !(kcorr_ktmlll (KP ρ0)), (kcorr_kty (KP ρ0)), !(rt_tm Hinv') in Y by assumption.
      exact Y. }
    assert (HgCa' : forall ρ0 x y a b, idxR' ρ0 x y -> shR' ρ0 x y a b ->
               [ kw_G ρ0 ; kw_Δ ρ0 ,, (ktyll ρ0 mB[pφ π]ᵤ)[lsingle2 x a] @ lvsubst ml2 (pφ π)
                   ⊢ (ktmlll ρ0 mC[pφ π]ᵤ)[llift (lsingle2 x a)] ≈ (ktmlll ρ0 mC'[pφ π]ᵤ)[llift (lsingle2 y b)]
                   : (kty ρ0 mX[pφ π]ᵤ)⟨↑⟩ @ lvsubst mli (pφ π) ]).
    { intros ρ0 x y a b h hs. destruct (Back2 _ ρ0 (KP ρ0) x y a b h hs) as (Nx & Ny & Na & Nb & h' & hs').
      pose proof (pg_geq_tm (Hup _) (mgCa _ _ _ _ _ h' hs')) as Y.
      rewrite Ext, (proj1 (KP ρ0)), (proj1 (proj2 (KP ρ0))), usubst_lsingle2_ty, !usubst_llift_single2,
        usubst_ren_ty, (kcorr_ktyll (KP ρ0)), !(kcorr_ktmlll (KP ρ0)), (kcorr_kty (KP ρ0)),
        !(rt_tm Hinv') in Y by assumption.
      exact Y. }
    assert (Lift : forall ρ0 (ρ1 : kwk (kw_G ρ0) (kw_Δ ρ0)),
               exists ρ1b : kwk (kw_G (kw_pull Hp HG HΓ ρ0)) (kw_Δ (kw_pull Hp HG HΓ ρ0)), kcorr π ρ1b ρ1)
      by (intros ρ0; exact (kcorr_lift _ ρ0 (Hup _) (KP ρ0))).
    assert (Himon' : forall ρ0 (ρ1 : kwk (kw_G ρ0) (kw_Δ ρ0)) x y, idxR' ρ0 x y ->
               idxR' (kw_comp ρ0 ρ1) (ktm ρ1 x) (ktm ρ1 y)).
    { intros ρ0 ρ1 x y h. destruct (Lift ρ0 ρ1) as (ρ1b & Hk1).
      destruct (IdxB _ ρ0 (KP ρ0) x y h) as (Nx & Ny & h').
      pose proof (IdxF _ _ (kcorr_comp (KP ρ0) _ _ Hk1) _ _ (dnf_ktm _ _ (dnf_us_tm _ _)) (dnf_ktm _ _ (dnf_us_tm _ _))
                    (mimon _ ρ1b _ _ h')) as Y.
      rewrite !(kcorr_ktm Hk1), !(rt_tm Hinv') in Y by assumption. exact Y. }
    assert (Hshmon' : forall ρ0 (ρ1 : kwk (kw_G ρ0) (kw_Δ ρ0)) x y a b, idxR' ρ0 x y -> shR' ρ0 x y a b ->
               shR' (kw_comp ρ0 ρ1) (ktm ρ1 x) (ktm ρ1 y) (ktm ρ1 a) (ktm ρ1 b)).
    { intros ρ0 ρ1 x y a b h hs. destruct (Lift ρ0 ρ1) as (ρ1b & Hk1).
      destruct (Back2 _ ρ0 (KP ρ0) x y a b h hs) as (Nx & Ny & Na & Nb & h' & hs').
      pose proof (ShF _ _ (kcorr_comp (KP ρ0) _ _ Hk1) _ _ _ _ (dnf_ktm _ _ (dnf_us_tm _ _))
                    (dnf_ktm _ _ (dnf_us_tm _ _)) (dnf_ktm _ _ (dnf_us_tm _ _)) (dnf_ktm _ _ (dnf_us_tm _ _))
                    (mimon _ ρ1b _ _ h') (mshmon _ ρ1b _ _ _ _ h' hs')) as Y.
      rewrite !(kcorr_ktm Hk1), !(rt_tm Hinv') in Y by assumption. exact Y. }
    assert (Hposmon' : forall ρ0 (ρ1 : kwk (kw_G ρ0) (kw_Δ ρ0)) x y a b p q, idxR' ρ0 x y -> shR' ρ0 x y a b ->
               posR' ρ0 x y a b p q ->
               posR' (kw_comp ρ0 ρ1) (ktm ρ1 x) (ktm ρ1 y) (ktm ρ1 a) (ktm ρ1 b) (ktm ρ1 p) (ktm ρ1 q)).
    { intros ρ0 ρ1 x y a b p q h hs hp. destruct (Lift ρ0 ρ1) as (ρ1b & Hk1).
      destruct (BackP ρ0 x y a b p q h hs hp) as (Nx & Ny & Na & Nb & Np & Nq & h' & hs' & hp').
      pose proof (PosF _ _ (kcorr_comp (KP ρ0) _ _ Hk1) _ _ _ _ (mimon _ ρ1b _ _ h') (mshmon _ ρ1b _ _ _ _ h' hs')
                    _ _ (dnf_ktm _ _ (dnf_us_tm _ _)) (dnf_ktm _ _ (dnf_us_tm _ _))
                    (mposmon _ ρ1b _ _ _ _ _ _ h' hs' hp')) as Y.
      rewrite !(kcorr_ktm Hk1), !(rt_tm Hinv') in Y by assumption. exact Y. }
    assert (Hix' : forall ρ0, idxR' ρ0 (ktm ρ0 mm[pφ π]ᵤ) (ktm ρ0 mm'[pφ π]ᵤ)).
    { intros ρ0. pose proof (IdxF _ ρ0 (KP ρ0) _ _ (dnf_ktm _ _ Nm) (dnf_ktm _ _ Nm') (mixAd _)) as Y.
      rewrite !(kcorr_ktm (KP ρ0)) in Y. exact Y. }
    assert (HmCp : [ Gp π G ; Γ[pφ π]ᵤ ,, mX[pφ π]ᵤ @ lvsubst mli (pφ π) ,, mA[pφ π]ᵤ @ lvsubst ml1 (pφ π)
                       ,, mB[pφ π]ᵤ @ lvsubst ml2 (pφ π) ⊢g mC[pφ π]ᵤ : mX[pφ π]ᵤ⟨↑⟩⟨↑⟩⟨↑⟩ @ lvsubst mli (pφ π) ])
      by (pose proof (pg_tm Hp HmC) as Y; rewrite !usubst_ren_ty in Y; exact Y).
    assert (HmCp' : [ Gp π G ; Γ[pφ π]ᵤ ,, mX'[pφ π]ᵤ @ lvsubst mli (pφ π) ,, mA'[pφ π]ᵤ @ lvsubst ml1 (pφ π)
                        ,, mB'[pφ π]ᵤ @ lvsubst ml2 (pφ π) ⊢g mC'[pφ π]ᵤ : mX'[pφ π]ᵤ⟨↑⟩⟨↑⟩⟨↑⟩ @ lvsubst mli (pφ π) ])
      by (pose proof (pg_tm Hp HmC') as Y; rewrite !usubst_ren_ty in Y; exact Y).
    assert (HmCCp : [ Gp π G ; Γ[pφ π]ᵤ ,, mX[pφ π]ᵤ @ lvsubst mli (pφ π) ,, mA[pφ π]ᵤ @ lvsubst ml1 (pφ π)
                        ,, mB[pφ π]ᵤ @ lvsubst ml2 (pφ π) ⊢ mC[pφ π]ᵤ ≈ mC'[pφ π]ᵤ
                        : mX[pφ π]ᵤ⟨↑⟩⟨↑⟩⟨↑⟩ @ lvsubst mli (pφ π) ])
      by (pose proof (pg_geq_tm Hp HmCC) as Y; rewrite !usubst_ren_ty in Y; exact Y).
    (* the two sides *)
    pose proof (MSide_of_LR Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HmX HmA HmB HmC HmXX HmAA HmBB HmCC
                  midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon) as HM1.
    pose proof (MSide_of_LR (pg_lequiv Hp Hmr1) (pg_lequiv Hp Hmr2) (pg_lequiv Hp Hmri) (pg_lwf Hp Hmw1)
                  (pg_lwf Hp Hmw2) (pg_lwf Hp Hmwi) (pg_ty Hp HmX) (pg_ty Hp HmA) (pg_ty Hp HmB) HmCp
                  (pg_geq_ty Hp HmXX) (pg_geq_ty Hp HmAA) (pg_geq_ty Hp HmBB) HmCCp
                  Hidx' Hsh' Hpos' Hch' HgB' HgC' HgCa' Himon' Hshmon' Hposmon') as HM'.
    assert (Flip : forall (ρ0 : kwk (Gp π G) Γ[pφ π]ᵤ) (ρ : kwk G Γ), kcorr πi ρ0 ρ -> kcorr π ρ ρ0)
      by (intros ρ0 ρ Hk0; exact (kcorr_flip ρ0 ρ (uperm_grow _ _ _ _ (kw_gL ρ0) Hp) Hk0)).
    assert (ShB' : STr πi idxR' shR' mshR).
    { intros ρ0 ρ Hk0 x y a b _ _ _ _ h hs.
      destruct (Back2 ρ ρ0 (Flip _ _ Hk0) x y a b h hs) as (_ & _ & _ & _ & _ & hs'). exact hs'. }
    assert (PosB' : PTr πi π idxR' shR' posR' mposR).
    { intros ρ0 ρ Hk0 x y a b Nx Ny Na Nb h hs p q hp.
      destruct (Back2 ρ ρ0 (Flip _ _ Hk0) x y a b h hs) as (_ & _ & _ & _ & h' & hs').
      destruct (LR_rel_dnf (mposAd _ _ _ _ _ h' hs') _ _ hp) as [Np Nq].
      pose proof (PosF ρ ρ0 (Flip _ _ Hk0) _ _ _ _ h' hs' p q Np Nq hp) as Y.
      rewrite !(rt_tm Hinv') in Y by assumption. exact (conj Np (conj Nq Y)). }
    exists (MR (Gp π G) Γ[pφ π]ᵤ (lvsubst ml1 (pφ π)) (lvsubst ml2 (pφ π)) (lvsubst mli (pφ π)) mX[pφ π]ᵤ
              mA[pφ π]ᵤ mB[pφ π]ᵤ mC[pφ π]ᵤ (lvsubst mr1 (pφ π)) (lvsubst mr2 (pφ π)) (lvsubst mri (pφ π))
              mX'[pφ π]ᵤ mA'[pφ π]ᵤ mB'[pφ π]ᵤ mC'[pφ π]ᵤ shR' posR' mm[pφ π]ᵤ mm'[pφ π]ᵤ).
    split.
    + apply (LRm n (LRbelow n) (Gp π G) Γ[pφ π]ᵤ T[pφ π]ᵤ T'[pφ π]ᵤ (lvsubst l (pφ π)) (lvsubst ml1 (pφ π))
               (lvsubst ml2 (pφ π)) (lvsubst mli (pφ π)) (lvsubst mr1 (pφ π)) (lvsubst mr2 (pφ π))
               (lvsubst mri (pφ π)) mX[pφ π]ᵤ mX'[pφ π]ᵤ mA[pφ π]ᵤ mA'[pφ π]ᵤ mB[pφ π]ᵤ mB'[pφ π]ᵤ mC[pφ π]ᵤ
               mC'[pφ π]ᵤ mm[pφ π]ᵤ mm'[pφ π]ᵤ idxR' shR' posR').
      * exact (pg_lequiv Hp Hl).
      * exact (pg_lequiv Hp Hmr1).
      * exact (pg_lequiv Hp Hmr2).
      * exact (pg_lequiv Hp Hmri).
      * exact (pg_lwf Hp Hmw1).
      * exact (pg_lwf Hp Hmw2).
      * exact (pg_lwf Hp Hmwi).
      * exact (pg_tyred Hp HT).
      * exact (pg_tyred Hp HT').
      * exact (pg_ty Hp HmX).
      * exact (pg_ty Hp HmX').
      * exact (pg_ty Hp HmA).
      * exact (pg_ty Hp HmA').
      * exact (pg_ty Hp HmB).
      * exact (pg_ty Hp HmB').
      * exact HmCp.
      * exact HmCp'.
      * exact (pg_tm Hp Hmm).
      * exact (pg_tm Hp Hmm').
      * exact (pg_geq_ty Hp HmXX).
      * exact (pg_geq_ty Hp HmAA).
      * exact (pg_geq_ty Hp HmBB).
      * exact HmCCp.
      * exact (pg_geq_tm Hp Hmmm).
      * exact Hidx'.
      * exact Hsh'.
      * exact Hpos'.
      * exact Hch'.
      * exact HgB'.
      * exact HgC'.
      * exact HgCa'.
      * exact Himon'.
      * exact Hshmon'.
      * exact Hposmon'.
      * exact Hix'.
      * apply releq_refl.
    + intros t t' Nt Nt'. rewrite (HR t t'). split.
      * intros H n'.
        exact (MRn_perm π πi n' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM1 Nm Nm' mixAd Hp
                 _ _ _ _ _ _ _ _ _ _ _ _ _ _ eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl
                 eq_refl eq_refl eq_refl eq_refl ShF PosB t t' (H n')).
      * intros H n'.
        pose proof (MRn_perm πi π n' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM' (dnf_us_tm _ _) (dnf_us_tm _ _)
                      Hix' Hpi G Γ _ _ _ _ _ _ _ _ _ _ mshR mposR (Gp_rt Hp HG) (rt_ctx Hinv _ HΓ)
                      (rt_ty Hinv _ NX) (rt_ty Hinv _ NA) (rt_ty Hinv _ NB) (rt_tm Hinv _ NC) (rt_ty Hinv _ NX')
                      (rt_ty Hinv _ NA') (rt_ty Hinv _ NB') (rt_tm Hinv _ NC') (rt_tm Hinv _ Nm) (rt_tm Hinv _ Nm')
                      ShB' PosB' _ _ (H n')) as Y.
        rewrite !(rt_lvl Hinv), (rt_tm Hinv _ Nt), (rt_tm Hinv _ Nt') in Y. exact Y.
Qed.

Theorem LR_perm n : Pperm n.
Proof using EL VL VPP.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  apply LR_perm_step, IHn.
Qed.

(** ** Universe weakening: growth by one level, then the rotation
    (M3_DESIGN.md E14) *)

Definition rot (L : nat) : nat -> nat := fun n => if n <? L then S n else if n =? L then 0 else n.
Definition roti (L : nat) : nat -> nat := fun n => match n with 0 => L | S m => if m <? L then m else n end.

Lemma uperm_rot L : uperm (rot L) (roti L) (S L).
Proof using .
  unfold rot, roti; repeat split.
  - intros n. destruct (Nat.ltb_spec n L).
    + destruct (Nat.ltb_spec n L); lia.
    + destruct (Nat.eqb_spec n L); [lia |].
      destruct n as [|m]; [lia |]. destruct (Nat.ltb_spec m L); lia.
  - intros [|m].
    + destruct (Nat.ltb_spec L L); [lia|]. rewrite Nat.eqb_refl; reflexivity.
    + destruct (Nat.ltb_spec m L).
      * destruct (Nat.ltb_spec m L); lia.
      * destruct (Nat.ltb_spec (S m) L); [lia|]. destruct (Nat.eqb_spec (S m) L); lia.
  - intros n Hn. destruct (Nat.ltb_spec n L); [lia|]. destruct (Nat.eqb_spec n L); lia.
  - intros n Hn. destruct (Nat.ltb_spec n L); [lia|]. destruct (Nat.eqb_spec n L); lia.
Qed.

Lemma rot_ush L n : n < L -> pφ (rot L) n = lvar (ush 1 n).
Proof using . intros Hn. unfold pφ, rot, ush. destruct (Nat.ltb_spec n L); [reflexivity | lia]. Qed.

Lemma uren_us_ty (T : ty) ρ : T⟨ρ⟩ᵤ = T[pφ ρ]ᵤ.
Proof using . apply (proj1 uren_as_usubst_all); reflexivity. Qed.
Lemma uren_us_tm (t : tm) ρ : t⟨ρ⟩ᵤ = t[pφ ρ]ᵤ.
Proof using . apply (proj1 (proj2 uren_as_usubst_all)); reflexivity. Qed.
Lemma uren_us_ctx (Γ : ctx) ρ : Γ⟨ρ⟩ᵤ = Γ[pφ ρ]ᵤ.
Proof using . apply (proj1 (proj2 (proj2 uren_as_usubst_all))); reflexivity. Qed.

Definition decl_lwf (L : nat) (D : gdecl) : Prop :=
  match D with
  | gdCtx => True | gdTy Δ _ l => ctx_lwf L Δ /\ lwf L l | gdTm Δ _ T l => ctx_lwf L Δ /\ ty_lwf L T /\ lwf L l
  | gdDef Δ T l t => ctx_lwf L Δ /\ ty_lwf L T /\ lwf L l /\ tm_lwf L t
  end.

Lemma wfg_lwf G : [ ⊢ G ] -> Forall (decl_lwf (gL G)) (gΨ G).
Proof using .
  induction 1 as [L | L Ψ HG IH | L Ψ Δ i l HG IH HΔ Hi Hl | L Ψ Δ i T l HG IH HT Hi Hl | L Ψ Δ T l t HG IH HT Hl Ht];
    cbn in *.
  - constructor.
  - constructor; [exact I | exact IH].
  - constructor; [split; [exact (wf_ctx_lwf HΔ) | exact Hl] | exact IH].
  - constructor; [| exact IH].
    refine (conj _ (conj (wf_ty_lwf HT) Hl)).
    exact (wf_ctx_lwf (proj1 (proj2 (proj2 ctx_extract)) _ _ _ _ _ HT)).
  - constructor; [| exact IH].
    refine (conj _ (conj (wf_ty_lwf HT) (conj Hl (wf_tm_lwf Ht)))).
    exact (wf_ctx_lwf (proj1 (proj2 (proj2 ctx_extract)) _ _ _ _ _ HT)).
Qed.

Lemma rot_decls L Ψ : Forall (decl_lwf L) Ψ ->
  map (fun D => gdecl_usubst D (pφ (rot L))) Ψ = map (fun D => gdecl_uren D (ush 1)) Ψ.
Proof using .
  induction 1 as [|D Ψ HD _ IH]; cbn; f_equal; auto.
  assert (Eag : forall m, m < L -> pφ (rot L) m = pφ (ush 1) m) by (intros; apply rot_ush; assumption).
  destruct D; cbn in HD |- *; [reflexivity | ..];
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
  - f_equal; [rewrite uren_us_ctx; exact (lwf_us_ext_ctx ltac:(eassumption) Eag)
             | rewrite (lvren_as_lvsubst _ _ (pφ (ush 1))) by reflexivity;
               exact (lvsubst_ext_lwf _ _ _ _ ltac:(eassumption) Eag)].
  - f_equal; [rewrite uren_us_ctx; exact (lwf_us_ext_ctx ltac:(eassumption) Eag)
             | rewrite uren_us_ty; exact (lwf_us_ext_ty ltac:(eassumption) Eag)
             | rewrite (lvren_as_lvsubst _ _ (pφ (ush 1))) by reflexivity;
               exact (lvsubst_ext_lwf _ _ _ _ ltac:(eassumption) Eag)].
  - f_equal; [rewrite uren_us_ctx; exact (lwf_us_ext_ctx ltac:(eassumption) Eag)
             | rewrite uren_us_ty; exact (lwf_us_ext_ty ltac:(eassumption) Eag)
             | rewrite (lvren_as_lvsubst _ _ (pφ (ush 1))) by reflexivity;
               exact (lvsubst_ext_lwf _ _ _ _ ltac:(eassumption) Eag)
             | rewrite uren_us_tm; exact (lwf_us_ext_tm ltac:(eassumption) Eag)].
Qed.

Section Grow.
Context {L : nat} {Ψ : list gdecl} {Γ : ctx} (HΓ : [ mkG L Ψ ; Γ ⊢g ]).

Lemma grow_gok : gwk_ok gwk_id (mkG (S L) Ψ) (mkG L Ψ).
Proof using . split; [cbn; lia | constructor]. Qed.
Lemma grow_ctx : [ mkG (S L) Ψ ; Γ ⊢g ].
Proof using HΓ.
  exact (gwa_ctx (γ := gwk_id) grow_gok (wfg_grow L (S L) Ψ ltac:(lia) (ctx_glob _ _ _ HΓ)) HΓ).
Qed.
Definition kw_grow : kwk (mkG L Ψ) Γ :=
  mkKwk (mkG (S L) Ψ) Γ gwk_id wk_id grow_gok (wkwf_id _) grow_ctx.

End Grow.

Lemma ren_id_tm' (t : tm) : nftm t -> t⟨rshift 0⟩ = t.
Proof using .
  intros H. rewrite (ren_as_subst _ _ (lshift 0)); [apply subst_id; auto|]; intros; cbn; f_equal; lia.
Qed.

Theorem LR_uwk {n G Γ T T' l R} : LR n (LRbelow n) G Γ T T' l R -> lwf (gL G) l ->
  exists R', LR n (LRbelow n) (gctx_uwk 1 G) Γ⟨ush 1⟩ᵤ T⟨ush 1⟩ᵤ T'⟨ush 1⟩ᵤ (lvren l (ush 1)) R' /\
    forall t t', R t t' -> R' t⟨ush 1⟩ᵤ t'⟨ush 1⟩ᵤ.
Proof using EL VL VPP.
  intros H Hl. destruct G as [L Ψ].
  destruct (escape_ty _ _ _ _ _ _ _ _ H) as (HT & HT' & _). pose proof (ctx_of_ty HT) as HΓ.
  pose proof (ctx_glob _ _ _ HΓ) as HG.
  destruct (LR_kwk n _ _ _ _ _ _ H (kw_grow HΓ)) as (R1 & H1 & E1).
  unfold kty in H1; cbn [kw_grow kw_γ kw_r kw_G kw_Δ gwa] in H1.
  cbn [wk_ren] in H1.
  rewrite !ren_id_ty in H1 by first [exact (wf_ty_nf HT) | exact (wf_ty_nf HT')].
  destruct (LR_perm n _ _ _ _ _ _ H1 (rot L) (roti L) (uperm_rot L)) as (R2 & H2 & E2).
  assert (EG : Gp (rot L) (mkG (S L) Ψ) = gctx_uwk 1 (mkG L Ψ)).
  { unfold Gp, G_us, gctx_usubst, gctx_uwk; cbn. f_equal. exact (rot_decls L Ψ (wfg_lwf _ HG)). }
  assert (Eag : forall m, m < L -> pφ (rot L) m = pφ (ush 1) m) by (intros; apply rot_ush; assumption).
  rewrite EG, (lwf_us_ext_ctx (wf_ctx_lwf HΓ) Eag), (lwf_us_ext_ty (wf_ty_lwf HT) Eag),
    (lwf_us_ext_ty (wf_ty_lwf HT') Eag), (lvsubst_ext_lwf _ _ _ _ Hl Eag), <- !uren_us_ty, <- uren_us_ctx,
    <- (lvren_as_lvsubst _ _ (pφ (ush 1))) in H2 by reflexivity.
  exists R2. split; [exact H2 |].
  intros t t' Ht. destruct (escape_tm _ _ _ _ _ _ _ _ H _ _ Ht) as (Ht1 & Ht2 & _).
  pose proof (E1 t t' Ht) as X. unfold ktm in X; cbn [kw_grow kw_γ kw_r gwa] in X.
  cbn [wk_ren] in X.
  rewrite !ren_id_tm' in X by first [exact (wf_tm_nf Ht1) | exact (wf_tm_nf Ht2)].
  apply (E2 _ _ (wf_tm_dnf Ht1) (wf_tm_dnf Ht2)) in X.
  rewrite (lwf_us_ext_tm (wf_tm_lwf Ht1) Eag), (lwf_us_ext_tm (wf_tm_lwf Ht2) Eag), <- !uren_us_tm in X.
  exact X.
Qed.

(** ** [n] fresh levels at once *)

Definition rotn (n L : nat) : nat -> nat :=
  fun m => if m <? L then n + m else if m <? n + L then m - L else m.
Definition rotni (n L : nat) : nat -> nat :=
  fun m => if m <? n then L + m else if m <? n + L then m - n else m.

Lemma uperm_rotn n L : uperm (rotn n L) (rotni n L) (n + L).
Proof using .
  unfold rotn, rotni; repeat split.
  - intros m. destruct (Nat.ltb_spec m L).
    + destruct (Nat.ltb_spec (n + m) n); [lia|]. destruct (Nat.ltb_spec (n + m) (n + L)); lia.
    + destruct (Nat.ltb_spec m (n + L)).
      * destruct (Nat.ltb_spec (m - L) n); lia.
      * destruct (Nat.ltb_spec m n); [lia|]. destruct (Nat.ltb_spec m (n + L)); lia.
  - intros m. destruct (Nat.ltb_spec m n).
    + destruct (Nat.ltb_spec (L + m) L); [lia|]. destruct (Nat.ltb_spec (L + m) (n + L)); lia.
    + destruct (Nat.ltb_spec m (n + L)).
      * destruct (Nat.ltb_spec (m - n) L); lia.
      * destruct (Nat.ltb_spec m L); [lia|]. destruct (Nat.ltb_spec m (n + L)); lia.
  - intros m Hm. destruct (Nat.ltb_spec m L); [lia|]. destruct (Nat.ltb_spec m (n + L)); lia.
  - intros m Hm. destruct (Nat.ltb_spec m L); [lia|]. destruct (Nat.ltb_spec m (n + L)); lia.
Qed.

Lemma rotn_ush n L m : m < L -> pφ (rotn n L) m = lvar (ush n m).
Proof using . intros Hm. unfold pφ, rotn, ush. destruct (Nat.ltb_spec m L); [reflexivity | lia]. Qed.

Lemma rotn_decls n L Ψ : Forall (decl_lwf L) Ψ ->
  map (fun D => gdecl_usubst D (pφ (rotn n L))) Ψ = map (fun D => gdecl_uren D (ush n)) Ψ.
Proof using .
  induction 1 as [|D Ψ HD _ IH]; cbn; f_equal; auto.
  assert (Eag : forall m, m < L -> pφ (rotn n L) m = pφ (ush n) m) by (intros; apply rotn_ush; assumption).
  destruct D; cbn in HD |- *; [reflexivity | ..];
    repeat match goal with H : _ /\ _ |- _ => destruct H end.
  - f_equal; [rewrite uren_us_ctx; exact (lwf_us_ext_ctx ltac:(eassumption) Eag)
             | rewrite (lvren_as_lvsubst _ _ (pφ (ush n))) by reflexivity;
               exact (lvsubst_ext_lwf _ _ _ _ ltac:(eassumption) Eag)].
  - f_equal; [rewrite uren_us_ctx; exact (lwf_us_ext_ctx ltac:(eassumption) Eag)
             | rewrite uren_us_ty; exact (lwf_us_ext_ty ltac:(eassumption) Eag)
             | rewrite (lvren_as_lvsubst _ _ (pφ (ush n))) by reflexivity;
               exact (lvsubst_ext_lwf _ _ _ _ ltac:(eassumption) Eag)].
  - f_equal; [rewrite uren_us_ctx; exact (lwf_us_ext_ctx ltac:(eassumption) Eag)
             | rewrite uren_us_ty; exact (lwf_us_ext_ty ltac:(eassumption) Eag)
             | rewrite (lvren_as_lvsubst _ _ (pφ (ush n))) by reflexivity;
               exact (lvsubst_ext_lwf _ _ _ _ ltac:(eassumption) Eag)
             | rewrite uren_us_tm; exact (lwf_us_ext_tm ltac:(eassumption) Eag)].
Qed.

End UPermLR.
