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
From DeLaM.Typing Require Export UPerm.
From DeLaM.LogRel Require Export LevelInv.

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
Proof. exact (gne_ty_us Hφ). Qed.
Lemma pg_geq_ty {Γ T T' l} : [ G ; Γ ⊢ T ≈ T' @ l ] ->
  [ Gp π G ; Γ[pφ π]ᵤ ⊢ T[pφ π]ᵤ ≈ T'[pφ π]ᵤ @ lvsubst l (pφ π) ].
Proof. exact (geq_ty_us Hφ). Qed.
Lemma pg_gne_tm {Γ t t' T l} : [ G ; Γ ⊢ t ~ t' : T @ l ] ->
  [ Gp π G ; Γ[pφ π]ᵤ ⊢ t[pφ π]ᵤ ~ t'[pφ π]ᵤ : T[pφ π]ᵤ @ lvsubst l (pφ π) ].
Proof. exact (gne_tm_us Hφ). Qed.
Lemma pg_geq_tm {Γ t t' T l} : [ G ; Γ ⊢ t ≈ t' : T @ l ] ->
  [ Gp π G ; Γ[pφ π]ᵤ ⊢ t[pφ π]ᵤ ≈ t'[pφ π]ᵤ : T[pφ π]ᵤ @ lvsubst l (pφ π) ].
Proof. exact (geq_tm_us Hφ). Qed.
Lemma pg_ty {Γ T l} : [ G ; Γ ⊢g T @ l ] -> [ Gp π G ; Γ[pφ π]ᵤ ⊢g T[pφ π]ᵤ @ lvsubst l (pφ π) ].
Proof. exact (p_ty Hp). Qed.
Lemma pg_tm {Γ t T l} : [ G ; Γ ⊢g t : T @ l ] ->
  [ Gp π G ; Γ[pφ π]ᵤ ⊢g t[pφ π]ᵤ : T[pφ π]ᵤ @ lvsubst l (pφ π) ].
Proof. exact (p_tm Hp). Qed.
Lemma pg_eqty {Γ T T' l} : [ G ; Γ ⊢g T ≅ T' @ l ] ->
  [ Gp π G ; Γ[pφ π]ᵤ ⊢g T[pφ π]ᵤ ≅ T'[pφ π]ᵤ @ lvsubst l (pφ π) ].
Proof. exact (p_eqty Hp). Qed.
Lemma pg_ctx {Γ} : [ G ; Γ ⊢g ] -> [ Gp π G ; Γ[pφ π]ᵤ ⊢g ].
Proof. exact (p_ctx Hp). Qed.
Lemma pg_tyred {Γ T W l} : [ G ; Γ ⊢g T ⤳* W @ l ] ->
  [ Gp π G ; Γ[pφ π]ᵤ ⊢g T[pφ π]ᵤ ⤳* W[pφ π]ᵤ @ lvsubst l (pφ π) ].
Proof. intros []; split; [exact (p_ty Hp ltac:(eassumption)) | now apply reds_ty_usubst | exact (p_eqty Hp ltac:(eassumption))]. Qed.
Lemma pg_tmred {Γ t w T l} : [ G ; Γ ⊢g t ⤳* w : T @ l ] ->
  [ Gp π G ; Γ[pφ π]ᵤ ⊢g t[pφ π]ᵤ ⤳* w[pφ π]ᵤ : T[pφ π]ᵤ @ lvsubst l (pφ π) ].
Proof. intros []; split; [exact (p_tm Hp ltac:(eassumption)) | now apply reds_usubst | exact (p_eqtm Hp ltac:(eassumption))]. Qed.
Lemma pg_lequiv {l l'} : lequiv (gL G) l l' -> lequiv (gL (Gp π G)) (lvsubst l (pφ π)) (lvsubst l' (pφ π)).
Proof. exact (p_lequiv Hp). Qed.
Lemma pg_lwf {l} : lwf (gL G) l -> lwf (gL (Gp π G)) (lvsubst l (pφ π)).
Proof. exact (p_lwf Hp). Qed.

(** The shared type-level data of a binder former, permuted; [F]
    commutes with universe substitution as [Π] and [Σ] do. *)
Lemma poly_pg {F Γ T T' l l1 l2 l3 l4 A B A' B'} :
  (forall k k' C D φ, (F k k' C D)[φ]ᵤ = F (lvsubst k φ) (lvsubst k' φ) C[φ]ᵤ D[φ]ᵤ) ->
  PolyFacts G Γ F T T' l l1 l2 l3 l4 A B A' B' ->
  PolyFacts (Gp π G) Γ[pφ π]ᵤ F T[pφ π]ᵤ T'[pφ π]ᵤ (lvsubst l (pφ π))
    (lvsubst l1 (pφ π)) (lvsubst l2 (pφ π)) (lvsubst l3 (pφ π)) (lvsubst l4 (pφ π))
    A[pφ π]ᵤ B[pφ π]ᵤ A'[pφ π]ᵤ B'[pφ π]ᵤ.
Proof.
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
Proof. unfold kty. now rewrite usubst_ren_ty, usubst_gwa_ty. Qed.
Lemma ktyl_us {G0 Γ0} (ρ : kwk G0 Γ0) T φ : (ktyl ρ T)[φ]ᵤ = T[φ]ᵤ⟦kw_γ ρ⟧⟨rlift (kw_r ρ)⟩.
Proof. unfold ktyl. now rewrite usubst_ren_ty, usubst_gwa_ty. Qed.
Lemma ktm_us {G0 Γ0} (ρ : kwk G0 Γ0) t φ : (ktm ρ t)[φ]ᵤ = t[φ]ᵤ⟦kw_γ ρ⟧⟨kw_r ρ⟩.
Proof. unfold ktm. now rewrite usubst_ren, usubst_gwa_tm. Qed.
Lemma ktml_us {G0 Γ0} (ρ : kwk G0 Γ0) t φ : (ktml ρ t)[φ]ᵤ = t[φ]ᵤ⟦kw_γ ρ⟧⟨rlift (kw_r ρ)⟩.
Proof. unfold ktml. now rewrite usubst_ren, usubst_gwa_tm. Qed.

(** ** Kripke worlds *)

Section Push.
Context {π πi : nat -> nat} {G : gctx} {Γ : ctx} (Hp : uperm π πi (gL G)) (ρ : kwk G Γ).

Lemma kw_push_gok : gwk_ok (kw_γ ρ) (Gp π (kw_G ρ)) (Gp π G).
Proof. split; [exact (kw_gL ρ) | exact (gwk_wf_usubst _ _ _ _ (proj2 (kw_gok ρ)))]. Qed.
Lemma kw_push_wf : kw_r ρ : (kw_Δ ρ)[pφ π]ᵤ ≤ (Γ[pφ π]ᵤ)⟦kw_γ ρ⟧.
Proof. rewrite <- usubst_gwa_ctx. apply wk_wf_usubst, kw_wf. Qed.
Lemma kw_push_ctx : [ Gp π (kw_G ρ) ; (kw_Δ ρ)[pφ π]ᵤ ⊢g ].
Proof. exact (pg_ctx (uperm_grow _ _ _ _ (kw_gL ρ) Hp) (kw_ctx ρ)). Qed.

Definition kw_push : kwk (Gp π G) (Γ[pφ π]ᵤ) :=
  mkKwk (Gp π (kw_G ρ)) ((kw_Δ ρ)[pφ π]ᵤ) (kw_γ ρ) (kw_r ρ) kw_push_gok kw_push_wf kw_push_ctx.

Lemma kty_push T : kty kw_push T[pφ π]ᵤ = (kty ρ T)[pφ π]ᵤ.
Proof. unfold kty; cbn. now rewrite usubst_ren_ty, usubst_gwa_ty. Qed.
Lemma ktm_push t : ktm kw_push t[pφ π]ᵤ = (ktm ρ t)[pφ π]ᵤ.
Proof. unfold ktm; cbn. now rewrite usubst_ren, usubst_gwa_tm. Qed.
Lemma ktyl_push T : ktyl kw_push T[pφ π]ᵤ = (ktyl ρ T)[pφ π]ᵤ.
Proof. unfold ktyl; cbn. now rewrite usubst_ren_ty, usubst_gwa_ty. Qed.
Lemma kbody_push T : kbody kw_push T[pφ π]ᵤ = (kbody ρ T)[pφ π]ᵤ.
Proof. unfold kbody; cbn. now rewrite usubst_ren_ty, usubst_gwa_ty. Qed.

Let Hpρ : uperm π πi (gL (kw_G ρ)) := uperm_grow _ _ _ _ (kw_gL ρ) Hp.

Lemma push_geq_kty {X Y l} : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ X ≈ Y @ l ] ->
  [ kw_G kw_push ; kw_Δ kw_push ⊢ kty kw_push X[pφ π]ᵤ ≈ Y[pφ π]ᵤ @ lvsubst l (pφ π) ].
Proof. intros H. pose proof (pg_geq_ty Hpρ H) as Z. rewrite <- kty_push in Z. exact Z. Qed.
Lemma push_geq_ktyl {C X Y lc l} : [ kw_G ρ ; kw_Δ ρ ,, kty ρ C @ lc ⊢ ktyl ρ X ≈ Y @ l ] ->
  [ kw_G kw_push ; kw_Δ kw_push ,, kty kw_push C[pφ π]ᵤ @ lvsubst lc (pφ π)
      ⊢ ktyl kw_push X[pφ π]ᵤ ≈ Y[pφ π]ᵤ @ lvsubst l (pφ π) ].
Proof.
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
Proof.
  split; [exact (kw_gL ρ') |].
  pose proof (gwk_wf_usubst _ _ _ (pφ πi) (proj2 (kw_gok ρ'))) as X.
  unfold Gp, G_us, gctx_usubst in X |- *; cbn [gΨ] in X |- *.
  now rewrite (rt_gdecls Hi _ (wfg_dnf _ HG)) in X.
Qed.
Lemma kw_pull_wf : kw_r ρ' : (kw_Δ ρ')[pφ πi]ᵤ ≤ Γ⟦kw_γ ρ'⟧.
Proof.
  pose proof (wk_wf_usubst _ _ _ (pφ πi) (kw_wf ρ')) as X.
  rewrite usubst_gwa_ctx, (rt_ctx Hi _ HΓ) in X. exact X.
Qed.
Lemma kw_pull_ctx : [ Gp πi (kw_G ρ') ; (kw_Δ ρ')[pφ πi]ᵤ ⊢g ].
Proof. exact (pg_ctx Hpi (kw_ctx ρ')). Qed.

Definition kw_pull : kwk G Γ :=
  mkKwk (Gp πi (kw_G ρ')) ((kw_Δ ρ')[pφ πi]ᵤ) (kw_γ ρ') (kw_r ρ') kw_pull_gok kw_pull_wf kw_pull_ctx.

Lemma pull_G : Gp π (kw_G kw_pull) = kw_G ρ'.
Proof. unfold Gp; cbn. exact (rt_gctx (proj1 (proj2 Hp)) _ (kw_glob ρ')). Qed.
Lemma pull_Δ : (kw_Δ kw_pull)[pφ π]ᵤ = kw_Δ ρ'.
Proof. cbn. exact (rt_ctx (proj1 (proj2 Hp)) _ (wf_ctx_dnf (kw_ctx ρ'))). Qed.
Lemma kty_pull T : (kty kw_pull T)[pφ π]ᵤ = kty ρ' T[pφ π]ᵤ.
Proof. unfold kty; cbn. now rewrite usubst_ren_ty, usubst_gwa_ty. Qed.
Lemma ktyl_pull T : (ktyl kw_pull T)[pφ π]ᵤ = ktyl ρ' T[pφ π]ᵤ.
Proof. unfold ktyl; cbn. now rewrite usubst_ren_ty, usubst_gwa_ty. Qed.
Lemma ktm_pull t : (ktm kw_pull t)[pφ π]ᵤ = ktm ρ' t[pφ π]ᵤ.
Proof. unfold ktm; cbn. now rewrite usubst_ren, usubst_gwa_tm. Qed.
Lemma ktml_pull t : (ktml kw_pull t)[pφ π]ᵤ = ktml ρ' t[pφ π]ᵤ.
Proof. unfold ktml; cbn. now rewrite usubst_ren, usubst_gwa_tm. Qed.
Lemma kbody_pull T : (kbody kw_pull T)[pφ π]ᵤ = kbody ρ' T[pφ π]ᵤ.
Proof. unfold kbody; cbn. now rewrite usubst_ren_ty, usubst_gwa_ty. Qed.
Lemma pull_gL : gL (kw_G kw_pull) = gL (kw_G ρ').
Proof. reflexivity. Qed.

Lemma pull_geq_kty {X Y l} : dnfty X -> [ kw_G ρ' ; kw_Δ ρ' ⊢ kty ρ' X[pφ π]ᵤ ≈ Y @ l ] ->
  [ kw_G kw_pull ; kw_Δ kw_pull ⊢ kty kw_pull X ≈ Y[pφ πi]ᵤ @ lvsubst l (pφ πi) ].
Proof.
  intros NX H. pose proof (pg_geq_ty Hpi H) as Z. rewrite kty_us, (rt_ty Hi _ NX) in Z. exact Z.
Qed.
Lemma pull_geq_ktyl {C X Y lc l} : dnfty C -> dnfty X ->
  [ kw_G ρ' ; kw_Δ ρ' ,, kty ρ' C[pφ π]ᵤ @ lc ⊢ ktyl ρ' X[pφ π]ᵤ ≈ Y @ l ] ->
  [ kw_G kw_pull ; kw_Δ kw_pull ,, kty kw_pull C @ lvsubst lc (pφ πi) ⊢ ktyl kw_pull X ≈ Y[pφ πi]ᵤ @ lvsubst l (pφ πi) ].
Proof.
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
Proof.
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
Proof.
  intros (ν & ν' & H1 & H2 & H3 & H4). exists ν[pφ π]ᵤ, ν'[pφ π]ᵤ.
  exact (conj (pg_tmred Hp H1) (conj (pg_tmred Hp H2) (conj (pg_gne_tm Hp H3) (pg_gne_tm Hp H4)))).
Qed.

(** The identity type (M11a): along a permutation of its carrier's relation. *)
Lemma IdRel_perm {l1 A a b RA RA'} :
  (forall x y, RA x y -> RA' x[pφ π]ᵤ y[pφ π]ᵤ) -> forall t t', IdRel G Γ l1 A a b RA t t' ->
  IdRel (Gp π G) Γ[pφ π]ᵤ (lvsubst l1 (pφ π)) A[pφ π]ᵤ a[pφ π]ᵤ b[pφ π]ᵤ RA' t[pφ π]ᵤ t'[pφ π]ᵤ.
Proof.
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
Proof.
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
Proof.
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
Proof.
  destruct 1 as [T1 T1' H | ν ν' H]; cbn.
  - constructor. exact (vpp_tyc Hp HG H).
  - apply ctyn_ne. exact (pg_gne_tm Hp H).
Qed.
Lemma CTrmNf_perm {Δ A k w w'} : CTrmNf G Γ Δ A k w w' ->
  CTrmNf (Gp π G) Γ[pφ π]ᵤ Δ[pφ π]ᵤ A[pφ π]ᵤ (lvsubst k (pφ π)) w[pφ π]ᵤ w'[pφ π]ᵤ.
Proof.
  destruct 1 as [t1 t1' H | ν ν' H]; cbn.
  - constructor. exact (vpp_tmc Hp HG H).
  - apply ctrn_ne. exact (pg_gne_tm Hp H).
Qed.
Lemma CTypRel_perm {Δ Δ' k k' t t'} : CTypRel G Γ Δ Δ' k k' t t' ->
  CTypRel (Gp π G) Γ[pφ π]ᵤ Δ[pφ π]ᵤ Δ'[pφ π]ᵤ (lvsubst k (pφ π)) (lvsubst k' (pφ π)) t[pφ π]ᵤ t'[pφ π]ᵤ.
Proof.
  intros (w & w' & H1 & H2 & H3 & H4 & H5 & H6). exists w[pφ π]ᵤ, w'[pφ π]ᵤ.
  refine (conj (pg_tmred Hp H1) (conj (pg_tmred Hp H2) (conj (pg_geq_tm Hp H3) (conj (pg_geq_tm Hp H4) _)))).
  exact (conj (CTypNf_perm H5) (CTypNf_perm H6)).
Qed.
Lemma CTrmRel_perm {Δ Δ' A A' k k' t t'} : CTrmRel G Γ Δ Δ' A A' k k' t t' ->
  CTrmRel (Gp π G) Γ[pφ π]ᵤ Δ[pφ π]ᵤ Δ'[pφ π]ᵤ A[pφ π]ᵤ A'[pφ π]ᵤ (lvsubst k (pφ π)) (lvsubst k' (pφ π))
    t[pφ π]ᵤ t'[pφ π]ᵤ.
Proof.
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
Proof.
  intros H. destruct (escape_ty _ _ _ _ _ _ _ _ H) as (HT & HT' & _).
  pose proof (ctx_of_ty HT) as HΓ.
  exact (conj (ctx_glob _ _ _ HΓ) (conj (wf_ctx_dnf HΓ) (conj (wf_ty_dnf HT) (wf_ty_dnf HT')))).
Qed.

Lemma LR_rel_dnf {n rec G Γ T T' l R} : LR n rec G Γ T T' l R -> forall t t', R t t' -> dnftm t /\ dnftm t'.
Proof.
  intros H t t' Ht. destruct (escape_tm _ _ _ _ _ _ _ _ H _ _ Ht) as (H1 & H2 & _).
  exact (conj (wf_tm_dnf H1) (wf_tm_dnf H2)).
Qed.

(** ** The universe *)

Lemma URel_perm n {π πi G Γ l1 t t'} : (forall m, m < n -> Pperm m) -> lmeasure l1 < n ->
  uperm π πi (gL G) ->
  URel (LRbelow n) G Γ l1 t t' -> URel (LRbelow n) (Gp π G) Γ[pφ π]ᵤ (lvsubst l1 (pφ π)) t[pφ π]ᵤ t'[pφ π]ᵤ.
Proof.
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
Proof.
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
Proof. exact (usubst_lsingle_ty M a φ). Qed.
Lemma usubst_gsingle_ty' (T : ty) o φ : T⦃gsingle o⦄[φ]ᵤ = T[φ]ᵤ⦃gsingle (gousubst o φ)⦄.
Proof. exact (usubst_gsingle_ty T o φ). Qed.
Lemma dnf_capp t Δ : dnftm t -> dnfctx Δ -> dnftm (capp t Δ).
Proof. cbn; auto. Qed.
Lemma dnf_tapp t A : dnftm t -> dnfty A -> dnftm (tapp t A).
Proof. cbn; auto. Qed.
Lemma dnf_us_ctx (Δ : ctx) φ : dnfctx Δ[φ]ᵤ.
Proof. apply (proj1 (proj2 (proj2 usubst_dnf_all))). Qed.

Lemma dnf_ktm {G0 Γ0} (ρ : kwk G0 Γ0) t : dnftm t -> dnftm (ktm ρ t).
Proof. intros H; unfold ktm; apply ren_dnf, dnf_gwa, H. Qed.
Lemma dnf_us_tm (t : tm) φ : dnftm t[φ]ᵤ.
Proof. apply (proj1 (proj2 usubst_dnf_all)). Qed.
Lemma dnf_us_ty (T : ty) φ : dnfty T[φ]ᵤ.
Proof. apply (proj1 usubst_dnf_all). Qed.

Lemma tyred_glob {G Γ T W l} : [ G ; Γ ⊢g T ⤳* W @ l ] -> [ ⊢ G ] /\ dnfctx Γ /\ dnfty T /\ dnfty W.
Proof.
  intros H. pose proof (tyred_wf _ _ _ _ _ _ H) as HT. pose proof (ctx_of_ty HT) as HΓ.
  pose proof (eqty_wf_r ge_typeof (tyred_eq _ _ _ _ _ _ H)) as HW.
  exact (conj (ctx_glob _ _ _ HΓ) (conj (wf_ctx_dnf HΓ) (conj (wf_ty_dnf HT) (wf_ty_dnf HW)))).
Qed.

Lemma geq_ty_dnf {G Γ T T' l} : [ G ; Γ ⊢ T ≈ T' @ l ] -> dnfty T /\ dnfty T'.
Proof. intros H; exact (eqty_dnf (geq_ty_sound H)). Qed.
Lemma geq_tm_dnf {G Γ t t' T l} : [ G ; Γ ⊢ t ≈ t' : T @ l ] -> dnftm t /\ dnftm t'.
Proof. intros H; destruct (eqtm_dnf (geq_tm_sound H)) as (? & ? & _); auto. Qed.

Lemma usubst_fst' la lb (A B : ty) p φ :
  (tmFst la lb A B p)[φ]ᵤ = tmFst (lvsubst la φ) (lvsubst lb φ) A[φ]ᵤ B[φ]ᵤ p[φ]ᵤ.
Proof. reflexivity. Qed.
Lemma usubst_snd' la lb (A B : ty) p φ :
  (tmSnd la lb A B p)[φ]ᵤ = tmSnd (lvsubst la φ) (lvsubst lb φ) A[φ]ᵤ B[φ]ᵤ p[φ]ᵤ.
Proof. reflexivity. Qed.
Lemma usubst_app' f la lb (A B : ty) a φ :
  (app f la lb A B a)[φ]ᵤ = app f[φ]ᵤ (lvsubst la φ) (lvsubst lb φ) A[φ]ᵤ B[φ]ᵤ a[φ]ᵤ.
Proof. reflexivity. Qed.

Lemma pull_tmred {π πi G Γ t w T l} : uperm π πi (gL G) -> [ ⊢ G ] -> dnfctx Γ -> dnftm t -> dnfty T ->
  [ Gp π G ; Γ[pφ π]ᵤ ⊢g t[pφ π]ᵤ ⤳* w : T[pφ π]ᵤ @ lvsubst l (pφ π) ] ->
  [ G ; Γ ⊢g t ⤳* w[pφ πi]ᵤ : T @ l ].
Proof.
  intros Hp HG HΓ Nt NT H. pose proof (pg_tmred (G := Gp π G) (uperm_inv _ _ _ Hp) H) as X.
  rewrite (Gp_rt Hp HG), (rt_ctx (proj1 Hp) _ HΓ), (rt_tm (proj1 Hp) _ Nt), (rt_ty (proj1 Hp) _ NT),
    (rt_lvl (proj1 Hp)) in X.
  exact X.
Qed.
Lemma pull_geq_tm {π πi G Γ w w' T l} : uperm π πi (gL G) -> [ ⊢ G ] -> dnfctx Γ -> dnfty T ->
  [ Gp π G ; Γ[pφ π]ᵤ ⊢ w ≈ w' : T[pφ π]ᵤ @ lvsubst l (pφ π) ] ->
  [ G ; Γ ⊢ w[pφ πi]ᵤ ≈ w'[pφ πi]ᵤ : T @ l ].
Proof.
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
Proof. destruct Hk as (_ & _ & Eg & Er). rewrite kty_us. unfold kty. now rewrite Eg, Er. Qed.
Lemma kcorr_ktyl T : (ktyl ρ T)[pφ π]ᵤ = ktyl ρ' T[pφ π]ᵤ.
Proof. destruct Hk as (_ & _ & Eg & Er). rewrite ktyl_us. unfold ktyl. now rewrite Eg, Er. Qed.
Lemma kcorr_ktm t : (ktm ρ t)[pφ π]ᵤ = ktm ρ' t[pφ π]ᵤ.
Proof. destruct Hk as (_ & _ & Eg & Er). rewrite ktm_us. unfold ktm. now rewrite Eg, Er. Qed.
Lemma kcorr_ktml t : (ktml ρ t)[pφ π]ᵤ = ktml ρ' t[pφ π]ᵤ.
Proof. destruct Hk as (_ & _ & Eg & Er). rewrite ktml_us. unfold ktml. now rewrite Eg, Er. Qed.

Lemma kcorr_comp (ρ0 : kwk (kw_G ρ) (kw_Δ ρ)) (ρ0' : kwk (kw_G ρ') (kw_Δ ρ')) :
  kcorr π ρ0 ρ0' -> kcorr π (kw_comp ρ ρ0) (kw_comp ρ' ρ0').
Proof.
  destruct Hk as (_ & _ & Eg & Er). intros (E1 & E2 & Eg0 & Er0). unfold kcorr; cbn [kw_comp kw_G kw_Δ kw_γ kw_r].
  split; [exact E1 | split; [exact E2 | split; congruence]].
Qed.

End Corr.

Lemma kcorr_pull {π πi G Γ} (Hp : uperm π πi (gL G)) (HG : [ ⊢ G ]) (HΓ : dnfctx Γ)
  (ρ' : kwk (Gp π G) Γ[pφ π]ᵤ) : kcorr π (kw_pull Hp HG HΓ ρ') ρ'.
Proof. split; [exact (pull_G Hp HG HΓ ρ') | split; [exact (pull_Δ Hp HG HΓ ρ') | split; reflexivity]]. Qed.

(** Correspondence along [πi], turned around. *)
Lemma kcorr_flip {π πi G Γ G0 Γ0} (ρ0 : kwk G0 Γ0) (ρ : kwk G Γ) :
  uperm π πi (gL (kw_G ρ0)) -> kcorr πi ρ0 ρ -> kcorr π ρ ρ0.
Proof.
  intros Hp (E1 & E2 & Eg & Er).
  split; [| split; [| split; [now rewrite Eg | now rewrite Er]]].
  - rewrite <- E1. exact (Gp_rt (uperm_inv _ _ _ Hp) (kw_glob ρ0)).
  - rewrite <- E2. exact (rt_ctx (proj1 (proj2 Hp)) _ (wf_ctx_dnf (kw_ctx ρ0))).
Qed.

Lemma dnf_kty {G0 Γ0} (ρ : kwk G0 Γ0) T : dnfty T -> dnfty (kty ρ T).
Proof. intros H; unfold kty; apply ren_dnf_ty; destruct (kw_γ ρ); cbn [gwa]; auto; intros; apply gren_dnf_all. Qed.
Lemma dnf_ktyl {G0 Γ0} (ρ : kwk G0 Γ0) T : dnfty T -> dnfty (ktyl ρ T).
Proof. intros H; unfold ktyl; apply ren_dnf_ty; destruct (kw_γ ρ); cbn [gwa]; auto; intros; apply gren_dnf_all. Qed.
Lemma dnf_ktml {G0 Γ0} (ρ : kwk G0 Γ0) t : dnftm t -> dnftm (ktml ρ t).
Proof. intros H; unfold ktml; apply ren_dnf, dnf_gwa, H. Qed.

Lemma usubst_sup' l l' (A B : ty) a f φ :
  (tmSup l l' A B a f)[φ]ᵤ = tmSup (lvsubst l φ) (lvsubst l' φ) A[φ]ᵤ B[φ]ᵤ a[φ]ᵤ f[φ]ᵤ.
Proof. reflexivity. Qed.
Lemma usubst_tyW' l l' (A B : ty) φ : (tyW l l' A B)[φ]ᵤ = tyW (lvsubst l φ) (lvsubst l' φ) A[φ]ᵤ B[φ]ᵤ.
Proof. reflexivity. Qed.

Lemma usubst_tyPi' l l' (A B : ty) φ : (tyPi l l' A B)[φ]ᵤ = tyPi (lvsubst l φ) (lvsubst l' φ) A[φ]ᵤ B[φ]ᵤ.
Proof. reflexivity. Qed.

Lemma WhRel_pg {π πi G Γ T l t t'} : uperm π πi (gL G) -> WhRel G Γ T l t t' ->
  WhRel (Gp π G) Γ[pφ π]ᵤ T[pφ π]ᵤ (lvsubst l (pφ π)) t[pφ π]ᵤ t'[pφ π]ᵤ.
Proof.
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
Proof.
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
Proof. apply usubst_ren_ty. Qed.

Lemma usubst_vecwf l (A : ty) (N m : tm) φ :
  (tyVec l (tyWf l A N)⟨↑⟩ m⟨↑⟩)[φ]ᵤ = tyVec (lvsubst l φ) (tyWf l A N)[φ]ᵤ⟨↑⟩ m[φ]ᵤ⟨↑⟩.
Proof. rewrite <- usubst_ren_ty, <- usubst_ren. reflexivity. Qed.

Lemma usubst_sigvec l (A : ty) (N m : tm) φ :
  (tySig l l (tyWf l A N) (tyVec l (tyWf l A N)⟨↑⟩ m⟨↑⟩))[φ]ᵤ =
  tySig (lvsubst l φ) (lvsubst l φ) (tyWf l A N)[φ]ᵤ (tyVec (lvsubst l φ) (tyWf l A N)[φ]ᵤ⟨↑⟩ m[φ]ᵤ⟨↑⟩).
Proof. rewrite <- usubst_vecwf. reflexivity. Qed.

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
Proof.
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

Lemma LR_perm_step n : (forall m, m < n -> Pperm m) -> Pperm n.
Proof.
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
                 | G Γ T T' l l1 l2 A A' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ IHRQ Hqs Hqt HR];
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
Qed.

Theorem LR_perm n : Pperm n.
Proof.
  induction n as [n IHn] using (well_founded_induction lt_wf).
  apply LR_perm_step, IHn.
Qed.

(** ** Universe weakening: growth by one level, then the rotation
    (M3_DESIGN.md E14) *)

Definition rot (L : nat) : nat -> nat := fun n => if n <? L then S n else if n =? L then 0 else n.
Definition roti (L : nat) : nat -> nat := fun n => match n with 0 => L | S m => if m <? L then m else n end.

Lemma uperm_rot L : uperm (rot L) (roti L) (S L).
Proof.
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
Proof. intros Hn. unfold pφ, rot, ush. destruct (Nat.ltb_spec n L); [reflexivity | lia]. Qed.

Lemma uren_us_ty (T : ty) ρ : T⟨ρ⟩ᵤ = T[pφ ρ]ᵤ.
Proof. apply (proj1 uren_as_usubst_all); reflexivity. Qed.
Lemma uren_us_tm (t : tm) ρ : t⟨ρ⟩ᵤ = t[pφ ρ]ᵤ.
Proof. apply (proj1 (proj2 uren_as_usubst_all)); reflexivity. Qed.
Lemma uren_us_ctx (Γ : ctx) ρ : Γ⟨ρ⟩ᵤ = Γ[pφ ρ]ᵤ.
Proof. apply (proj1 (proj2 (proj2 uren_as_usubst_all))); reflexivity. Qed.

Definition decl_lwf (L : nat) (D : gdecl) : Prop :=
  match D with
  | gdCtx => True | gdTy Δ _ l => ctx_lwf L Δ /\ lwf L l | gdTm Δ _ T l => ctx_lwf L Δ /\ ty_lwf L T /\ lwf L l
  | gdDef Δ T l t => ctx_lwf L Δ /\ ty_lwf L T /\ lwf L l /\ tm_lwf L t
  end.

Lemma wfg_lwf G : [ ⊢ G ] -> Forall (decl_lwf (gL G)) (gΨ G).
Proof.
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
Proof.
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
Proof. split; [cbn; lia | constructor]. Qed.
Lemma grow_ctx : [ mkG (S L) Ψ ; Γ ⊢g ].
Proof.
  exact (gwa_ctx (γ := gwk_id) grow_gok (wfg_grow L (S L) Ψ ltac:(lia) (ctx_glob _ _ _ HΓ)) HΓ).
Qed.
Definition kw_grow : kwk (mkG L Ψ) Γ :=
  mkKwk (mkG (S L) Ψ) Γ gwk_id wk_id grow_gok (wkwf_id _) grow_ctx.

End Grow.

Lemma ren_id_tm' (t : tm) : nftm t -> t⟨rshift 0⟩ = t.
Proof.
  intros H. rewrite (ren_as_subst _ _ (lshift 0)); [apply subst_id; auto|]; intros; cbn; f_equal; lia.
Qed.

Theorem LR_uwk {n G Γ T T' l R} : LR n (LRbelow n) G Γ T T' l R -> lwf (gL G) l ->
  exists R', LR n (LRbelow n) (gctx_uwk 1 G) Γ⟨ush 1⟩ᵤ T⟨ush 1⟩ᵤ T'⟨ush 1⟩ᵤ (lvren l (ush 1)) R' /\
    forall t t', R t t' -> R' t⟨ush 1⟩ᵤ t'⟨ush 1⟩ᵤ.
Proof.
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
Proof.
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
Proof. intros Hm. unfold pφ, rotn, ush. destruct (Nat.ltb_spec m L); [reflexivity | lia]. Qed.

Lemma rotn_decls n L Ψ : Forall (decl_lwf L) Ψ ->
  map (fun D => gdecl_usubst D (pφ (rotn n L))) Ψ = map (fun D => gdecl_uren D (ush n)) Ψ.
Proof.
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
