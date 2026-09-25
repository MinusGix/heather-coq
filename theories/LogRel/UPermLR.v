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
    vp_tmc vp G Δ A t t' l -> vp_tmc vp (Gp π G) Δ[pφ π]ᵤ A[pφ π]ᵤ t[pφ π]ᵤ t'[pφ π]ᵤ (lvsubst l (pφ π))
}.

#[export] Instance vp_empty_perm : VPPerm vp_empty.
Proof. constructor; cbn; tauto. Qed.

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

End Along.

Lemma kty_us {G0 Γ0} (ρ : kwk G0 Γ0) T φ : (kty ρ T)[φ]ᵤ = T[φ]ᵤ⟦kw_γ ρ⟧⟨kw_r ρ⟩.
Proof. unfold kty. now rewrite usubst_ren_ty, usubst_gwa_ty. Qed.
Lemma ktyl_us {G0 Γ0} (ρ : kwk G0 Γ0) T φ : (ktyl ρ T)[φ]ᵤ = T[φ]ᵤ⟦kw_γ ρ⟧⟨rlift (kw_r ρ)⟩.
Proof. unfold ktyl. now rewrite usubst_ren_ty, usubst_gwa_ty. Qed.
Lemma ktm_us {G0 Γ0} (ρ : kwk G0 Γ0) t φ : (ktm ρ t)[φ]ᵤ = t[φ]ᵤ⟦kw_γ ρ⟧⟨kw_r ρ⟩.
Proof. unfold ktm. now rewrite usubst_ren, usubst_gwa_tm. Qed.

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

Lemma LR_perm_step n : (forall m, m < n -> Pperm m) -> Pperm n.
Proof.
  intros IHn G Γ T T' l R H.
  induction H as [G Γ T T' l R Hl HT HT' HR
                 | G Γ T T' l l1 l2 R Hl Hl2 Hn HT HT' HR
                 | G Γ T T' l V V' R HT HT' HV HR
                 | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R Hl Hl3 Hl4 Hw1 Hw2 HT HT'
                     HA HA' HB HB' HAA HBB domAd IHdom codAd IHcod HR
                 | G Γ T T' l R Hj HM];
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
      * exact (pg_lequiv Hp Hl).
      * exact (pg_lequiv Hp Hl3).
      * exact (pg_lequiv Hp Hl4).
      * exact (pg_lwf Hp Hw1).
      * exact (pg_lwf Hp Hw2).
      * exact (pg_tyred Hp HT).
      * exact (pg_tyred Hp HT').
      * exact (pg_ty Hp HA).
      * exact (pg_ty Hp HA').
      * exact (pg_ty Hp HB).
      * exact (pg_ty Hp HB').
      * exact (pg_geq_ty Hp HAA).
      * exact (pg_geq_ty Hp HBB).
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
  match D with gdCtx => True | gdTy Δ _ l => ctx_lwf L Δ /\ lwf L l | gdTm Δ _ T l => ctx_lwf L Δ /\ ty_lwf L T /\ lwf L l end.

Lemma wfg_lwf G : [ ⊢ G ] -> Forall (decl_lwf (gL G)) (gΨ G).
Proof.
  induction 1 as [L | L Ψ HG IH | L Ψ Δ i l HG IH HΔ Hi Hl | L Ψ Δ i T l HG IH HT Hi Hl]; cbn in *.
  - constructor.
  - constructor; [exact I | exact IH].
  - constructor; [split; [exact (wf_ctx_lwf HΔ) | exact Hl] | exact IH].
  - constructor; [| exact IH].
    refine (conj _ (conj (wf_ty_lwf HT) Hl)).
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

End UPermLR.
