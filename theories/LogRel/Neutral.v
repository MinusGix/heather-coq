(** * Reflection of neutrals (ch. 7, Reflexivity of Neutral)

    Neutral terms that are generically equal at both related types are
    related.  By induction on the derivation; the universe case builds a
    neutral derivation one stage down, the Π case applies the neutral
    congruence law for application. *)
From DeLaM.LogRel Require Export Weakening.
From DeLaM.LogRel Require Import MAux.

(** ** The meta-functions' neutral applications at related arguments
    (M5_DESIGN.md G3)

    The laws ([gne_tm_capp], [gne_tm_tapp]) compare the arguments by the
    generic equivalence at P, which the relation only sees through its
    parameters. The class states the applications at parameter-related
    arguments; it holds vacuously at [j = P], and at [j = M] by escape of
    the payload (Payload.v). *)
Class VPNe `{E : GenericEq} `{LP : LRParams} := {
  vpn_capp {G Γ l T ν ν' Δ Δ'} : lr_j = jM -> lwf (gL G) l ->
    [ gext G gdCtx ; Γ⟪S⟫ ⊢g T @ l ] -> vp_ctx lr_vp G Δ Δ' ->
    [ G ; Γ ⊢g T⦃gsingle (GCtx Δ)⦄ ≅ T⦃gsingle (GCtx Δ')⦄ @ l ] ->
    [ G ; Γ ⊢ ν ~ ν' : tyCPi l T @ l ] ->
    [ G ; Γ ⊢ capp ν Δ ~ capp ν' Δ' : T⦃gsingle (GCtx Δ)⦄ @ l ] ;
  vpn_tapp {G Γ Δ l l' T ν ν' A A'} : lr_j = jM -> lwf (gL G) l -> lwf (gL G) l' ->
    [ gext G (gdTy Δ lD l) ; Γ⟪S⟫ ⊢g T @ l' ] -> vp_ctx lr_vp G Δ Δ -> vp_ty lr_vp G Δ A A' l ->
    [ G ; Γ ⊢g T⦃gsingle (GTy A)⦄ ≅ T⦃gsingle (GTy A')⦄ @ l' ] ->
    [ G ; Γ ⊢ ν ~ ν' : tyTPi Δ l l' T @ l' ] ->
    [ G ; Γ ⊢ tapp ν A ~ tapp ν' A' : T⦃gsingle (GTy A)⦄ @ l' ]
}.

#[export] Instance VPNe_P `{E : GenericEq} : @VPNe E LR_P.
Proof. constructor; intros; discriminate. Qed.

Section Neutral.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

(** ** Helpers *)

Lemma gne_tm_typed_l {G Γ ν ν' T l} : [ G ; Γ ⊢ ν ~ ν' : T @ l ] -> [ G ; Γ ⊢g ν : T @ l ].
Proof. intros H; exact (eqtm_wf_l ge_typeof (geq_tm_sound (gne_tm_geq H))). Qed.
Lemma gne_tm_typed_r {G Γ ν ν' T l} : [ G ; Γ ⊢ ν ~ ν' : T @ l ] -> [ G ; Γ ⊢g ν' : T @ l ].
Proof. intros H; exact (eqtm_wf_r ge_typeof (geq_tm_sound (gne_tm_geq H))). Qed.

(** Convert a neutral equality along [T ⤳* W] (and a level equivalence). *)
Lemma gne_tm_red {G Γ ν ν' T W l l'} :
  [ G ; Γ ⊢ ν ~ ν' : T @ l ] -> [ G ; Γ ⊢g T ⤳* W @ l ] -> lequiv (gL G) l' l ->
  [ G ; Γ ⊢ ν ~ ν' : W @ l' ].
Proof.
  intros Hν HT Hl. eapply gne_tm_lconv; [|exact Hl]. eapply gne_tm_conv; [exact Hν | apply HT].
Qed.

Lemma gne_tmred_refl {G Γ ν ν' T l} : [ G ; Γ ⊢ ν ~ ν' : T @ l ] ->
  [ G ; Γ ⊢g ν ⤳* ν : T @ l ] /\ [ G ; Γ ⊢g ν' ⤳* ν' : T @ l ].
Proof. intros H; split; apply tmred_refl; eauto using gne_tm_typed_l, gne_tm_typed_r. Qed.

(** ** Contextual types *)

Lemma ModRel_neutral {G Γ T T' l R} : ModRel G Γ T T' l R -> forall ν ν',
  [ G ; Γ ⊢ ν ~ ν' : T @ l ] -> [ G ; Γ ⊢ ν ~ ν' : T' @ l ] -> R ν ν'.
Proof.
  destruct 1 as [T T' l Δ Δ' k k' R Hl Hk HT HT' HΔ Hgeq HR
                | T T' l Δ Δ' A A' k k' R Hl Hk HT HT' HΔ HA HA' Hgeq HR];
    intros ν ν' Hν Hν'; apply HR;
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as H1;
    pose proof (gne_tm_red Hν' HT' (lequiv_sym _ _ _ Hl)) as H2;
    destruct (gne_tmred_refl H1) as [R1 _]; destruct (gne_tmred_refl H2) as [_ R2];
    exists ν, ν'; refine (conj R1 (conj R2 (conj (gne_tm_geq H1) (conj (gne_tm_geq H2) (conj _ _)))));
    constructor; assumption.
Qed.

(** ** Reflection *)

(** ** [Π]'s and [Σ]'s relations at neutrals, given their components'
    (M18b: [M]'s observations; the [Π] and [Σ] cases below are these
    with the induction hypotheses) *)

Section BinNe.
Context {G : gctx} {Γ : ctx} {l1 l2 l3 l4 : lvl} {A B A' B' : ty}
  {domR : DomRel G Γ} {codR : CodRel G Γ domR}
  (Hl3 : lequiv (gL G) l3 l1) (Hl4 : lequiv (gL G) l4 l2) (Hw1 : lwf (gL G) l1) (Hw2 : lwf (gL G) l2)
  (HA : [ G ; Γ ⊢g A @ l1 ]) (HA' : [ G ; Γ ⊢g A' @ l1 ])
  (HAA : [ G ; Γ ⊢ A ≈ A' @ l1 ]) (HBB : [ G ; Γ ,, A @ l1 ⊢ B ≈ B' @ l2 ])
  (Edom : forall (ρ : kwk G Γ) a a', domR ρ a a' -> [ kw_G ρ ; kw_Δ ρ ⊢ a ≈ a' : kty ρ A @ l1 ])
  (Ecod : forall (ρ : kwk G Γ) a a' (h : domR ρ a a'),
     [ kw_G ρ ; kw_Δ ρ ⊢ (ktyl ρ B)[lsingle a] ≈ (ktyl ρ B')[lsingle a'] @ l2 ])
  (Ndom : forall (ρ : kwk G Γ) ν ν', [ kw_G ρ ; kw_Δ ρ ⊢ ν ~ ν' : kty ρ A @ l1 ] ->
     [ kw_G ρ ; kw_Δ ρ ⊢ ν ~ ν' : kty ρ A' @ l1 ] -> domR ρ ν ν')
  (Ncod : forall (ρ : kwk G Γ) a a' (h : domR ρ a a') ν ν',
     [ kw_G ρ ; kw_Δ ρ ⊢ ν ~ ν' : (ktyl ρ B)[lsingle a] @ l2 ] ->
     [ kw_G ρ ; kw_Δ ρ ⊢ ν ~ ν' : (ktyl ρ B')[lsingle a'] @ l2 ] -> codR ρ a a' h ν ν').

Lemma PiRel_neutral ν ν' :
  [ G ; Γ ⊢ ν ~ ν' : tyPi l1 l2 A B @ lmax l1 l2 ] -> [ G ; Γ ⊢ ν ~ ν' : tyPi l3 l4 A' B' @ lmax l1 l2 ] ->
  PiRel G Γ l1 l2 l3 l4 A B A' B' domR codR ν ν'.
Proof.
  intros HP HP'.
  destruct (gne_tmred_refl HP) as [H1 _]. destruct (gne_tmred_refl HP') as [_ H2].
  exists ν, ν'.
  refine (conj H1 (conj H2 (conj _ (conj _ (conj (gne_tm_geq HP) (conj (gne_tm_geq HP') _)))))).
  1-2: constructor; eauto using gne_tm_whne_l, gne_tm_whne_r.
  intros ρ a a' ha la lb la' lb' A1 B1 A1' B1' Hla Hlb Hla' Hlb' HA1 HB1 HA1' HB1'.
  apply (kw_lequiv ρ) in Hla, Hlb, Hla', Hlb'.
  pose proof (kw_lwf ρ Hw1) as Hw1'.
  (* facts in the weakened context *)
  assert (HAr : [ kw_G ρ ; kw_Δ ρ ⊢g kty ρ A @ l1 ]) by exact (kw_ty ρ HA).
  assert (HA'r : [ kw_G ρ ; kw_Δ ρ ⊢g kty ρ A' @ l1 ]) by exact (kw_ty ρ HA').
  assert (HΔA : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l1 ⊢g ]) by exact (kw_ext ρ HA Hw1).
  assert (EA : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A ≈ kty ρ A' @ l1 ]) by exact (kw_geq_ty ρ HAA).
  assert (EB : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l1 ⊢ ktyl ρ B ≈ ktyl ρ B' @ l2 ])
    by exact (kw_geq_ty_l ρ HA Hw1 HBB).
  assert (HA1w : [ kw_G ρ ; kw_Δ ρ ⊢g A1 @ la ]).
  { eapply lconv_ty; [exact (eqty_wf_r ge_typeof (geq_ty_sound HA1)) | now apply lequiv_sym]. }
  assert (HΔA1 : [ kw_G ρ ; kw_Δ ρ ,, A1 @ la ⊢g ]) by (apply ext_wf_g; eauto using lequiv_wf_l).
  pose proof (Edom ρ a a' ha) as Haa.
  pose proof (eqtm_wf_l ge_typeof (geq_tm_sound Haa)) as Ha.
  (* the two annotations agree *)
  assert (EA1 : [ kw_G ρ ; kw_Δ ρ ⊢ A1 ≈ A1' @ la ]).
  { eapply geq_ty_lconv; [|exact Hla].
    eapply geq_ty_trans; [apply geq_ty_sym, HA1 | eapply geq_ty_trans; [exact EA | exact HA1']]. }
  assert (EB1 : [ kw_G ρ ; kw_Δ ρ ,, A1 @ la ⊢ B1 ≈ B1' @ lb ]).
  { eapply geq_ty_lconv; [|exact Hlb].
    eapply geq_ty_ctxconv; [apply geq_ty_sound, HA1 | now apply lequiv_sym | exact HΔA1 |].
    eapply geq_ty_trans; [apply geq_ty_sym, HB1 | eapply geq_ty_trans; [exact EB |]].
    eapply geq_ty_ctxconv; [apply geq_ty_sound, geq_ty_sym, EA | apply lequiv_refl, Hw1'
                           | exact HΔA | exact HB1']. }
  assert (Hνr : [ kw_G ρ ; kw_Δ ρ ⊢ ktm ρ ν ~ ktm ρ ν' : tyPi la lb A1 B1 @ lmax la lb ]).
  { eapply (gne_tm_lconv (l' := lmax l1 l2)); [|now apply lequiv_max].
    pose proof (kw_gne_tm ρ HP) as Y. rewrite kty_tyPi in Y.
    eapply gne_tm_conv; [exact Y|].
    apply geq_ty_sound, geq_ty_pi; auto using lequiv_sym. }
  assert (Haa1 : [ kw_G ρ ; kw_Δ ρ ⊢ a ≈ a' : A1 @ la ]).
  { eapply geq_tm_conv_l; [exact Haa | | exact Hla].
    eapply eqty_lconv; [apply geq_ty_sound, HA1 | exact Hla]. }
  pose proof (gne_tm_app (lequiv_trans _ _ _ _ Hla (lequiv_sym _ _ _ Hla'))
                (lequiv_trans _ _ _ _ Hlb (lequiv_sym _ _ _ Hlb')) HA1w EA1 EB1 Hνr Haa1) as X.
  assert (X1 : [ kw_G ρ ; kw_Δ ρ ⊢ app (ktm ρ ν) la lb A1 B1 a ~ app (ktm ρ ν') la' lb' A1' B1' a'
                   : (ktyl ρ B)[lsingle a] @ l2 ]).
  { eapply gne_tm_conv; [eapply gne_tm_lconv; [exact X | now apply lequiv_sym]|].
    apply (eqty_single ge_typeof (geq_ty_sound (geq_ty_sym HB1)) Ha). }
  apply (Ncod ρ a a' ha); [exact X1|].
  eapply gne_tm_conv; [exact X1|].
  exact (geq_ty_sound (Ecod ρ a a' ha)).
Qed.

Lemma SigRel_neutral ν ν' :
  [ G ; Γ ⊢ ν ~ ν' : tySig l1 l2 A B @ lmax l1 l2 ] -> [ G ; Γ ⊢ ν ~ ν' : tySig l3 l4 A' B' @ lmax l1 l2 ] ->
  SigRel G Γ l1 l2 l3 l4 A B A' B' domR codR ν ν'.
Proof.
  intros HP HP'.
  destruct (gne_tmred_refl HP) as [H1 _]. destruct (gne_tmred_refl HP') as [_ H2].
  exists ν, ν'.
  refine (conj H1 (conj H2 (conj _ (conj _ (conj (gne_tm_geq HP) (conj (gne_tm_geq HP') _)))))).
  1-2: constructor; eauto using gne_tm_whne_l, gne_tm_whne_r.
  intros ρ la lb la' lb' A1 B1 A1' B1' Hla Hlb Hla' Hlb' HA1 HB1 HA1' HB1'.
  apply (kw_lequiv ρ) in Hla, Hlb, Hla', Hlb'.
  pose proof (kw_lwf ρ Hw1) as Hw1'.
  assert (HAr : [ kw_G ρ ; kw_Δ ρ ⊢g kty ρ A @ l1 ]) by exact (kw_ty ρ HA).
  assert (HΔA : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l1 ⊢g ]) by exact (kw_ext ρ HA Hw1).
  assert (EA : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A ≈ kty ρ A' @ l1 ]) by exact (kw_geq_ty ρ HAA).
  assert (EB : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l1 ⊢ ktyl ρ B ≈ ktyl ρ B' @ l2 ])
    by exact (kw_geq_ty_l ρ HA Hw1 HBB).
  assert (HA1w : [ kw_G ρ ; kw_Δ ρ ⊢g A1 @ la ]).
  { eapply lconv_ty; [exact (eqty_wf_r ge_typeof (geq_ty_sound HA1)) | now apply lequiv_sym]. }
  assert (HΔA1 : [ kw_G ρ ; kw_Δ ρ ,, A1 @ la ⊢g ]) by (apply ext_wf_g; eauto using lequiv_wf_l).
  assert (EA1 : [ kw_G ρ ; kw_Δ ρ ⊢ A1 ≈ A1' @ la ]).
  { eapply geq_ty_lconv; [|exact Hla].
    eapply geq_ty_trans; [apply geq_ty_sym, HA1 | eapply geq_ty_trans; [exact EA | exact HA1']]. }
  assert (EB1 : [ kw_G ρ ; kw_Δ ρ ,, A1 @ la ⊢ B1 ≈ B1' @ lb ]).
  { eapply geq_ty_lconv; [|exact Hlb].
    eapply geq_ty_ctxconv; [apply geq_ty_sound, HA1 | now apply lequiv_sym | exact HΔA1 |].
    eapply geq_ty_trans; [apply geq_ty_sym, HB1 | eapply geq_ty_trans; [exact EB |]].
    eapply geq_ty_ctxconv; [apply geq_ty_sound, geq_ty_sym, EA | apply lequiv_refl, Hw1'
                           | exact HΔA | exact HB1']. }
  assert (Hνr : [ kw_G ρ ; kw_Δ ρ ⊢ ktm ρ ν ~ ktm ρ ν' : tySig la lb A1 B1 @ lmax la lb ]).
  { eapply (gne_tm_lconv (l' := lmax l1 l2)); [|now apply lequiv_max].
    pose proof (kw_gne_tm ρ HP) as Y. rewrite kty_tySig in Y.
    eapply gne_tm_conv; [exact Y|].
    apply geq_ty_sound, geq_ty_sig; auto using lequiv_sym. }
  pose proof (lequiv_trans _ _ _ _ Hla (lequiv_sym _ _ _ Hla')) as Qa.
  pose proof (lequiv_trans _ _ _ _ Hlb (lequiv_sym _ _ _ Hlb')) as Qb.
  (* the first projections, at both domains *)
  assert (F1 : [ kw_G ρ ; kw_Δ ρ ⊢ tmFst la lb A1 B1 (ktm ρ ν) ~ tmFst la' lb' A1' B1' (ktm ρ ν')
                   : kty ρ A @ l1 ]).
  { eapply gne_tm_conv; [eapply gne_tm_lconv; [exact (gne_tm_fst Qa Qb HA1w EA1 EB1 Hνr)
                                              | now apply lequiv_sym]|].
    apply geq_ty_sound, geq_ty_sym, HA1. }
  assert (F2 : [ kw_G ρ ; kw_Δ ρ ⊢ tmFst la lb A1 B1 (ktm ρ ν) ~ tmFst la' lb' A1' B1' (ktm ρ ν')
                   : kty ρ A' @ l1 ]) by (eapply gne_tm_conv; [exact F1 | apply geq_ty_sound, EA]).
  pose proof (Ndom ρ _ _ F1 F2) as h. exists h.
  pose proof (eqtm_wf_l ge_typeof (geq_tm_sound (Edom ρ _ _ h))) as Ha.
  (* the second projections, at the codomain instances *)
  assert (X1 : [ kw_G ρ ; kw_Δ ρ ⊢ tmSnd la lb A1 B1 (ktm ρ ν) ~ tmSnd la' lb' A1' B1' (ktm ρ ν')
                   : (ktyl ρ B)[lsingle (tmFst la lb A1 B1 (ktm ρ ν))] @ l2 ]).
  { eapply gne_tm_conv; [eapply gne_tm_lconv; [exact (gne_tm_snd Qa Qb HA1w EA1 EB1 Hνr)
                                              | now apply lequiv_sym]|].
    apply (eqty_single ge_typeof (geq_ty_sound (geq_ty_sym HB1)) Ha). }
  apply (Ncod ρ _ _ h); [exact X1|].
  eapply gne_tm_conv; [exact X1|].
  exact (geq_ty_sound (Ecod ρ _ _ h)).
Qed.

End BinNe.

(** ** Indexed [M] (M18b)

    By induction on the depth: the generic clauses are the neutrals
    themselves; in every world and at every choice of annotations, [out]
    of the two neutrals is a neutral ([gne_tm_out]) at [out]'s type, so
    [SigRel_neutral] relates them, its codomain by [PiRel_neutral] whose
    codomain is the induction hypothesis at the children. The shapes' and
    positions' reflection are hypotheses ([LR_neutral]'s induction
    hypotheses at the former). *)
Section MNe.

Definition MShNe {G Γ} (idxR : DomRel G Γ) (shR : MShRel G Γ) (A A' : ty) (l : lvl) : Prop :=
  forall (ρ : kwk G Γ) x x' ν ν', idxR ρ x x' ->
  [ kw_G ρ ; kw_Δ ρ ⊢ ν ~ ν' : (ktyl ρ A)[lsingle x] @ l ] ->
  [ kw_G ρ ; kw_Δ ρ ⊢ ν ~ ν' : (ktyl ρ A')[lsingle x'] @ l ] -> shR ρ x x' ν ν'.

Definition MPosNe {G Γ} (idxR : DomRel G Γ) (shR : MShRel G Γ) (posR : MPosRel G Γ) (B B' : ty) (l : lvl) : Prop :=
  forall (ρ : kwk G Γ) x x' a a' ν ν', idxR ρ x x' -> shR ρ x x' a a' ->
  [ kw_G ρ ; kw_Δ ρ ⊢ ν ~ ν' : (ktyll ρ B)[lsingle2 x a] @ l ] ->
  [ kw_G ρ ; kw_Δ ρ ⊢ ν ~ ν' : (ktyll ρ B')[lsingle2 x' a'] @ l ] -> posR ρ x x' a a' ν ν'.

Lemma MShNe_kw {G Γ idxR shR A A' l} (ρ : kwk G Γ) : MShNe idxR shR A A' l ->
  MShNe (fun ρ' => idxR (kw_comp ρ ρ')) (fun ρ' => shR (kw_comp ρ ρ')) (ktyl ρ A) (ktyl ρ A') l.
Proof.
  intros H ρ' x x' ν ν' h H1 H2. rewrite <- !(ktyl_comp ρ ρ') in H1, H2. exact (H _ x x' ν ν' h H1 H2).
Qed.

Lemma MPosNe_kw {G Γ idxR shR posR B B' l} (ρ : kwk G Γ) : MPosNe idxR shR posR B B' l ->
  MPosNe (fun ρ' => idxR (kw_comp ρ ρ')) (fun ρ' => shR (kw_comp ρ ρ')) (fun ρ' => posR (kw_comp ρ ρ'))
    (ktyll ρ B) (ktyll ρ B') l.
Proof.
  intros H ρ' x x' a a' ν ν' h ha H1 H2. rewrite <- !(ktyll_comp ρ ρ') in H1, H2.
  exact (H _ x x' a a' ν ν' h ha H1 H2).
Qed.

(** The codomain of [out]'s type, and its child type at a position, in
    a world. *)
Lemma ktyl_Pi_single {G Γ} (ρ : kwk G Γ) l l' A B a :
  (ktyl ρ (tyPi l l' A B))[lsingle a] = tyPi l l' (ktyl ρ A)[lsingle a] (ktyll ρ B)[llift (lsingle a)].
Proof. unfold ktyl, ktyll. now rewrite gwa_tyPi. Qed.

Lemma kw_kid_single {G Γ} (ρ : kwk G Γ) l l' li (X A B : ty) (C j a p : tm) :
  nfty X -> nfty A -> nfty B -> nftm C -> nftm j -> nftm a ->
  (ktyl ρ (tyM l l' li X⟨↑⟩ A⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩ C⟨rlift (rlift (rlift ↑))⟩
     C[llift (lsingle2 j a)]))[lsingle p] =
  tyM l l' li (kty ρ X) (ktyl ρ A) (ktyll ρ B) (ktmlll ρ C) (ktmlll ρ C)[lsingle3 (ktm ρ j) (ktm ρ a) p].
Proof.
  intros. unfold ktyl, ktyll, kty, ktmlll, ktm. rewrite gwa_tyM, !gwa_ren_ty, !gwa_ren, gwa_subst.
  rewrite (subst_ext _ (llift (lsingle2 j a))⟦kw_γ ρ⟧ (llift (lsingle2 j⟦kw_γ ρ⟧ a⟦kw_γ ρ⟧)))
    by (intros n; rewrite llk_llift_gwa, gwa_lsingle2; reflexivity).
  meq. all: now rewrite ?Nat.add_0_r.
Qed.

Definition MNeAt k := forall G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR m m',
  MSide G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR -> nftm m -> nftm m' ->
  (forall ρ, idxR ρ (ktm ρ m) (ktm ρ m')) ->
  MShNe idxR shR A A' l1 -> MPosNe idxR shR posR B B' l2 ->
  forall ν ν', [ G ; Γ ⊢ ν ~ ν' : tyM l1 l2 li X A B C m @ mlvl l1 l2 li ] ->
  [ G ; Γ ⊢ ν ~ ν' : tyM r1 r2 ri X' A' B' C' m' @ mlvl l1 l2 li ] ->
  MRn k G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' shR posR m m' ν ν'.

Lemma MObs_ne k (IH : MNeAt k) {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR m m'}
    (HM : MSide G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR) (Nm : nftm m) (Nm' : nftm m')
    (I : forall ρ, idxR ρ (ktm ρ m) (ktm ρ m'))
    (Hsh : MShNe idxR shR A A' l1) (Hpos : MPosNe idxR shR posR B B' l2) ν ν' :
  [ G ; Γ ⊢ ν ~ ν' : tyM l1 l2 li X A B C m @ mlvl l1 l2 li ] ->
  [ G ; Γ ⊢ ν ~ ν' : tyM r1 r2 ri X' A' B' C' m' @ mlvl l1 l2 li ] ->
  MObs (MRn k) G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' shR posR m m' ν ν'.
Proof.
  intros Hν Hν'. pose proof (ms_geq HM) as HG. pose proof (MEq_of_MGeq HG) as HE.
  pose proof HG as (H1 & H2 & H3 & HS & HXX & _).
  pose proof HS as (W1 & W2 & Wi & HX & _).
  pose proof (MEq_sig_r ge_typeof ge_notV HE) as HS'.
  destruct (MGeq_nf HG) as (NX & NA & NB & NC & NX' & NA' & NB' & NC').
  assert (Hm : lequiv (gL G) (mlvl l1 l2 li) (mlvl r1 r2 ri)) by (apply lequiv_mlvl; assumption).
  assert (Wm : lwf (gL G) (mlvl l1 l2 li)) by (split; [split|]; assumption).
  destruct (MSide_root HM Nm Nm' I) as (Em & EA & EB & EC).
  pose proof (geq_tm_sound Em) as DM.
  pose proof (eqtm_wf_l ge_typeof DM) as Hmw. pose proof (eqtm_wf_r ge_typeof DM) as Hmw'.
  intros k1 k2 ki X1 A1 B1 C1 j1 k1' k2' ki' X1' A1' B1' C1' j1' Ann Ann'.
  pose proof (MEq_of_MAnn HS Ann) as HE1.
  pose proof (MEq_of_MAnn HS' Ann') as HE2.
  pose proof (MEq_trans ge_typeof ge_notV (MEq_sym ge_typeof ge_notV HE1) (MEq_trans ge_typeof ge_notV HE HE2))
    as HE12.
  pose proof Ann as (K1 & K2 & Ki & _ & _ & _ & _ & Ej1).
  pose proof Ann' as (_ & _ & _ & _ & _ & _ & _ & Ej1').
  pose proof HE1 as (_ & _ & _ & _ & EX1 & _).
  pose proof (eqtm_wf_r ge_typeof Ej1) as Hj1.
  (* the two annotations' indices, at the first's type *)
  assert (Hjj : [ G ; Γ ⊢g j1 ≅ j1' : X1 @ ki ]).
  { eapply eqtm_lconv; [| exact Ki].
    eapply eqtm_conv; [| rewrite ge_typeof; exact (eqty_sym _ _ _ _ _ _ EX1)].
    eapply eqtm_trans; [exact (eqtm_sym _ _ _ _ _ _ _ Ej1) |].
    eapply eqtm_trans; [exact DM |].
    eapply eqtm_conv; [eapply eqtm_lconv; [exact Ej1' | exact H3] | rewrite ge_typeof; exact (geq_ty_sound HXX)]. }
  (* [out] of the neutrals, at its first annotations' type *)
  assert (Hν1 : [ G ; Γ ⊢ ν ~ ν' : tyM k1 k2 ki X1 A1 B1 C1 j1 @ mlvl k1 k2 ki ]).
  { eapply gne_tm_lconv; [| exact (lequiv_mlvl K1 K2 Ki)].
    eapply gne_tm_conv; [exact Hν | exact (M_ty_eq ge_typeof ge_notV HE1 Ej1)]. }
  destruct HE12 as (Q1 & Q2 & Q3 & (_ & _ & _ & HX1 & HA1 & HB1 & HC1) & QX & QA & QB & QC & _).
  pose proof (gne_tm_out Q1 Q2 Q3 HX1 QX HA1 QA HB1 QB HC1 QC Hjj Hν1) as Ho.
  (* at [out]'s types at the signatures *)
  assert (Y1 : [ G ; Γ ⊢ tmOut k1 k2 ki X1 A1 B1 C1 j1 ν ~ tmOut k1' k2' ki' X1' A1' B1' C1' j1' ν'
                  : mOutTy l1 l2 li X A B C m @ lmax l1 (mlvl l1 l2 li) ]).
  { eapply gne_tm_conv; [eapply gne_tm_lconv; [exact Ho | exact (lequiv_sym _ _ _ (lequiv_max _ _ _ _ _ K1 (lequiv_mlvl K1 K2 Ki)))]|].
    exact (eqty_sym _ _ _ _ _ _ (M_out_eq ge_typeof ge_notV HE1 Hmw Hj1 Ej1)). }
  assert (Y2 : [ G ; Γ ⊢ tmOut k1 k2 ki X1 A1 B1 C1 j1 ν ~ tmOut k1' k2' ki' X1' A1' B1' C1' j1' ν'
                  : mOutTy r1 r2 ri X' A' B' C' m' @ lmax l1 (mlvl l1 l2 li) ])
    by exact (gne_tm_conv Y1 (M_out_eq ge_typeof ge_notV HE Hmw Hmw' DM)).
  pose proof (geq_ty_sound EA) as DA.
  refine (SigRel_neutral W1 (eqty_wf_l ge_typeof DA) EA (M_outB_geq HG EB EC) _ _ _ _ _ _ Y1 Y2).
  - intros ρ a a' h. rewrite kty_lsingle. exact (ms_eS HM ρ _ _ a a' (I ρ) h).
  - intros ρ a a' h. rewrite !ktyl_Pi_single, !kw_B_single, !kw_mKid. rewrite !mKid_single by kw_nf.
    pose proof (ms_gBa HM ρ _ _ a a' (I ρ) h) as GB.
    pose proof (eqty_wf_l ge_typeof (geq_ty_sound GB)) as HB.
    pose proof (MGeq_M (MGeq_wk1 (MGeq_kw ρ HG) (ext_wf_g HB (kw_lwf ρ W2))) (ms_gCa HM ρ _ _ a a' (I ρ) h)) as K.
    eapply geq_ty_lconv; [| apply lequiv_sym, M_lv_f; apply (kw_lwf ρ); assumption].
    exact (geq_ty_pi (kw_lequiv ρ H2) (kw_lequiv ρ Hm) HB GB K).
  - intros ρ v v' Hv Hv'. rewrite !kty_lsingle in Hv, Hv'. exact (Hsh ρ _ _ v v' (I ρ) Hv Hv').
  - intros ρ a a' h v v' Hv Hv'. cbv beta.
    rewrite !ktyl_Pi_single in Hv, Hv'.
    pose proof (ms_gBa HM ρ _ _ a a' (I ρ) h) as GB.
    pose proof (geq_ty_sound GB) as DB.
    pose proof (eqty_wf_l ge_typeof DB) as HB. pose proof (eqty_wf_r ge_typeof DB) as HB'.
    pose proof (MGeq_M (MGeq_wk1 (MGeq_kw ρ HG) (ext_wf_g HB (kw_lwf ρ W2))) (ms_gCa HM ρ _ _ a a' (I ρ) h)) as K.
    pose proof (wf_tm_nf (eqtm_wf_l ge_typeof (geq_tm_sound (ms_eS HM ρ _ _ a a' (I ρ) h)))) as Na.
    pose proof (wf_tm_nf (eqtm_wf_r ge_typeof (geq_tm_sound (ms_eS HM ρ _ _ a a' (I ρ) h)))) as Na'.
    assert (Lf : lequiv (gL (kw_G ρ)) (lmax l2 (mlvl l1 l2 li)) (mlvl l1 l2 li))
      by (apply M_lv_f; apply (kw_lwf ρ); assumption).
    apply (gne_tm_lconv (l := lmax l2 (mlvl l1 l2 li))) in Hv, Hv'; [| exact Lf ..].
    rewrite !kw_B_single, !kw_mKid in Hv. rewrite !mKid_single in Hv by kw_nf.
    rewrite !kw_B_single, !kw_mKid in Hv'. rewrite !mKid_single in Hv' by kw_nf.
    rewrite !kw_B_single, !kw_mKid. rewrite !mKid_single by kw_nf.
    refine (PiRel_neutral (kw_lwf ρ W2) HB HB' GB K _ _ _ _ _ Hv Hv').
    + intros ρ' p p' hp. rewrite kty_lsingle2, <- (ktyll_comp ρ ρ'), <- (ktm_comp ρ ρ' m).
      assert (Sa : shR (kw_comp ρ ρ') (ktm (kw_comp ρ ρ') m) (ktm (kw_comp ρ ρ') m') (ktm ρ' a) (ktm ρ' a'))
        by (rewrite !(ktm_comp ρ ρ'); exact (ms_shmon HM ρ ρ' _ _ _ _ (I ρ) h)).
      exact (ms_eP HM (kw_comp ρ ρ') _ _ _ _ p p' (I _) Sa hp).
    + intros ρ' p p' hp. rewrite !kw_kid_single by first [kw_nf | assumption].
      rewrite <- (kty_comp ρ ρ' X), <- (ktyl_comp ρ ρ' A), <- (ktyll_comp ρ ρ' B), <- !(ktmlll_comp ρ ρ'),
        <- (ktm_comp ρ ρ' m), <- (kty_comp ρ ρ' X'), <- (ktyl_comp ρ ρ' A'), <- (ktyll_comp ρ ρ' B'),
        <- (ktm_comp ρ ρ' m').
      assert (Sa : shR (kw_comp ρ ρ') (ktm (kw_comp ρ ρ') m) (ktm (kw_comp ρ ρ') m') (ktm ρ' a) (ktm ρ' a'))
        by (rewrite !(ktm_comp ρ ρ'); exact (ms_shmon HM ρ ρ' _ _ _ _ (I ρ) h)).
      exact (MGeq_M (MGeq_kw (kw_comp ρ ρ') HG)
               (ms_eI HM _ _ _ (ms_ch HM (kw_comp ρ ρ') _ _ _ _ p p' (I _) Sa hp))).
    + intros ρ' p p' hp u u' Hu Hu'. rewrite !kw_kid_single in Hu, Hu' by first [kw_nf | assumption].
      rewrite <- (kty_comp ρ ρ' X), <- (ktyl_comp ρ ρ' A), <- (ktyll_comp ρ ρ' B), <- !(ktmlll_comp ρ ρ'),
        <- (ktm_comp ρ ρ' m) in Hu.
      rewrite <- (kty_comp ρ ρ' X'), <- (ktyl_comp ρ ρ' A'), <- (ktyll_comp ρ ρ' B'), <- !(ktmlll_comp ρ ρ'),
        <- (ktm_comp ρ ρ' m') in Hu'.
      destruct (MSide_child ρ ρ' a a' p p' HM Nm Nm' I h hp) as (N1 & N2 & Ic).
      exact (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MSide_kw (kw_comp ρ ρ') HM) N1 N2 Ic
               (MShNe_kw (kw_comp ρ ρ') Hsh) (MPosNe_kw (kw_comp ρ ρ') Hpos) _ _ Hu Hu').
Qed.

Lemma MRn_ne k : MNeAt k.
Proof.
  induction k as [|k IH]; intros G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR m m'
    HM Nm Nm' I Hsh Hpos ν ν' Hν Hν'.
  all: split; [ destruct (gne_tmred_refl Hν) as [R1 _]; destruct (gne_tmred_refl Hν') as [_ R2];
                exists ν, ν'; refine (conj R1 (conj R2 (conj _ (conj _ (conj (gne_tm_geq Hν) (gne_tm_geq Hν'))))));
                constructor; eauto using gne_tm_whne_l, gne_tm_whne_r |].
  1: exact Logic.I.
  intros ρ. pose proof (kw_gne_tm ρ Hν) as Y. pose proof (kw_gne_tm ρ Hν') as Y'.
  rewrite kty_tyM in Y, Y'.
  exact (MObs_ne k IH (MSide_kw ρ HM) ltac:(kw_nf) ltac:(kw_nf) (MIdx_kw ρ I)
           (MShNe_kw ρ Hsh) (MPosNe_kw ρ Hpos) _ _ Y Y').
Qed.

End MNe.

Theorem LR_neutral n G Γ T T' l R :
  LR n (LRbelow n) G Γ T T' l R -> forall ν ν',
  [ G ; Γ ⊢ ν ~ ν' : T @ l ] -> [ G ; Γ ⊢ ν ~ ν' : T' @ l ] -> R ν ν'.
Proof.
  induction 1 as [G Γ T T' l R Hl HT HT' HR
                 | G Γ T T' l l1 l2 R Hl Hl2 Hn HT HT' HR
                 | G Γ T T' l V V' R HT HT' HV HR
                 | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                     [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd IHdom codAd IHcod HR
                 | G Γ T T' l R Hj HM
                 | G Γ T T' l l1 l2 T1 T1' instR R Hj Hl Hl2 Hw1 HT HT' HT1 HT1' Hgeq instAd IHinst HR
                 | G Γ T T' l Δ1 Δ1' l1 l2 l3 l4 T1 T1' instR R Hj Hl Hl3 Hl4 Hw1 Hw2 HT HT' HΔ HT1 HT1'
                     Hgeq instAd IHinst HR
                 | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                     [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd IHdom codAd IHcod HR
                 | G Γ T T' l l1 l2 R Hl Hl2 Hw HT HT' HR
                 | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                 | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA IHRA Hra Hrb Hps Hpt HR
                 | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                 | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                     HRA IHRA HRB IHRB Hpa Hta Hpb Htb HR
                 | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                     [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd IHdom codAd IHcod HR
                 | G Γ T T' l l1 l2 A A' N N' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd IHdom arAd HR
                 | G Γ T T' l l1 l2 A A' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ IHRQ Hqs Hqt HR
                 | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                     HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                     widxAd IHwidx Hwisym Hwistr wdomAd IHwdom warAd wotAd wchAd wixAd HR
                 | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                     Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                     HmXX HmAA HmBB HmCC Hmmm midxAd IHmidx mshAd IHmsh mposAd IHmpos mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR];
    intros ν ν' Hν Hν'; first [exact (ModRel_neutral HM _ _ Hν Hν') | apply HR].
  - (* Nat *)
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as HN.
    destruct (gne_tmred_refl HN) as [H1 H2].
    econstructor; [exact H1 | exact H2 | now apply gne_tm_geq | now constructor].
  - (* U *)
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as HU.
    destruct (gne_tmred_refl HU) as [H1 H2].
    exists ν, ν'. refine (conj H1 (conj H2 (conj _ (conj _ (conj (gne_tm_geq HU) _))))).
    1-2: constructor; eauto using gne_tm_whne_l, gne_tm_whne_r.
    intros la lb Hla Hlb. rewrite LRbelow_spec by exact Hn.
    assert (HUa : [ G ; Γ ⊢ ν ~ ν' : tyU la @ lsuc la ]).
    { eapply gne_tm_lconv; [|apply lequiv_suc, Hla].
      eapply gne_tm_conv; [exact HU|].
      apply eqty_U; [exact ge_notV | rewrite ge_typeof; eapply ctx_of_tm, gne_tm_typed_l, HU
                    | now apply lequiv_sym]. }
    assert (HEl : [ G ; Γ ⊢ tyEl la ν ~ tyEl lb ν' @ l1 ]).
    { eapply gne_ty_lconv; [|apply lequiv_sym, Hla].
      apply gne_ty_El; [eapply lequiv_trans; [exact Hla | now apply lequiv_sym] | exact HUa]. }
    pose proof (eqty_wf_l ge_typeof (geq_ty_sound (gne_ty_geq HEl))) as Hw.
    pose proof (eqty_wf_r ge_typeof (geq_ty_sound (gne_ty_geq HEl))) as Hw'.
    eexists. eapply LRne; [apply tyred_refl, Hw | apply tyred_refl, Hw' | exact HEl | apply releq_refl].
  - (* neutral *)
    destruct (gne_tmred_refl Hν) as [H1 _]. destruct (gne_tmred_refl Hν') as [_ H2].
    exists ν, ν'. refine (conj _ (conj _ (conj _ _))).
    + eapply tmred_conv; [apply ge_typeof | exact H1 | apply HT].
    + eapply tmred_conv; [apply ge_typeof | exact H2 | apply HT'].
    + eapply gne_tm_conv; [exact Hν | apply HT].
    + eapply gne_tm_conv; [exact Hν' | apply HT'].
  - (* Π *)
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as HP.
    pose proof (gne_tm_red Hν' HT' (lequiv_sym _ _ _ Hl)) as HP'.
    refine (PiRel_neutral Hw1 HA HA' HAA HBB _ _ IHcod _ _ HP HP').
    + intros ρ a a' ha. exact (proj2 (proj2 (escape_tm _ _ _ _ _ _ _ _ (domAd ρ) a a' ha))).
    + intros ρ a a' ha. exact (proj2 (proj2 (escape_ty _ _ _ _ _ _ _ _ (codAd ρ a a' ha)))).
  - (* CΠ: the neutral application at every world and related contexts *)
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as HP.
    pose proof (gne_tm_red Hν' HT' (lequiv_sym _ _ _ Hl)) as HP'.
    destruct (gne_tmred_refl HP) as [H1 _]. destruct (gne_tmred_refl HP') as [_ H2].
    exists ν, ν'.
    refine (conj H1 (conj H2 (conj _ (conj _ (conj (gne_tm_geq HP) (conj (gne_tm_geq HP') _)))))).
    1-2: constructor; eauto using gne_tm_whne_l, gne_tm_whne_r.
    intros ρ Δ Δ' h.
    pose proof (vpl_ctx_trans (vpl_ctx_sym h) h) as h'.
    destruct (escape_ty _ _ _ _ _ _ _ _ (instAd ρ Δ Δ' h)) as (_ & _ & E1).
    destruct (escape_ty _ _ _ _ _ _ _ _ (instAd ρ Δ' Δ' h')) as (_ & _ & E2).
    assert (Einst : [ kw_G ρ ; kw_Δ ρ ⊢g (kbody ρ T1)⦃gsingle (GCtx Δ)⦄ ≅ (kbody ρ T1)⦃gsingle (GCtx Δ')⦄ @ l1 ])
      by (apply geq_ty_sound; eapply geq_ty_trans; [exact E1 | apply geq_ty_sym, E2]).
    assert (Hνr : [ kw_G ρ ; kw_Δ ρ ⊢ ktm ρ ν ~ ktm ρ ν' : tyCPi l1 (kbody ρ T1) @ l1 ])
      by (pose proof (kw_gne_tm ρ HP) as Y; rewrite kty_tyCPi in Y; exact Y).
    pose proof (vpn_capp Hj (kw_lwf ρ Hw1) (kw_body_ty_c ρ HT1) h Einst Hνr) as X.
    apply (IHinst ρ Δ Δ' h); [exact X|].
    eapply gne_tm_conv; [exact X | apply geq_ty_sound, E1].
  - (* TΠ *)
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as HP.
    pose proof (gne_tm_red Hν' HT' (lequiv_sym _ _ _ Hl)) as HP'.
    destruct (gne_tmred_refl HP) as [H1 _]. destruct (gne_tmred_refl HP') as [_ H2].
    exists ν, ν'.
    refine (conj H1 (conj H2 (conj _ (conj _ (conj (gne_tm_geq HP) (conj (gne_tm_geq HP') _)))))).
    1-2: constructor; eauto using gne_tm_whne_l, gne_tm_whne_r.
    intros ρ A A' h.
    pose proof (vpl_ty_trans (vpl_ty_sym h) h) as h'.
    pose proof (vpl_ctx_gwk (kw_gok ρ) (kw_glob ρ) HΔ) as HΔr.
    destruct (escape_ty _ _ _ _ _ _ _ _ (instAd ρ A A' h)) as (_ & _ & E1).
    destruct (escape_ty _ _ _ _ _ _ _ _ (instAd ρ A' A' h')) as (_ & _ & E2).
    assert (Einst : [ kw_G ρ ; kw_Δ ρ ⊢g (kbody ρ T1)⦃gsingle (GTy A)⦄ ≅ (kbody ρ T1)⦃gsingle (GTy A')⦄ @ l2 ])
      by (apply geq_ty_sound; eapply geq_ty_trans; [exact E1 | apply geq_ty_sym, E2]).
    assert (Hνr : [ kw_G ρ ; kw_Δ ρ ⊢ ktm ρ ν ~ ktm ρ ν' : tyTPi Δ1⟦kw_γ ρ⟧ l1 l2 (kbody ρ T1) @ l2 ])
      by (pose proof (kw_gne_tm ρ HP) as Y; rewrite kty_tyTPi in Y; exact Y).
    pose proof (vpn_tapp Hj (kw_lwf ρ Hw1) (kw_lwf ρ Hw2) (kw_body_ty_t ρ HT1)
                  (vpl_ctx_trans HΔr (vpl_ctx_sym HΔr)) h Einst Hνr) as X.
    apply (IHinst ρ A A' h); [exact X|].
    eapply gne_tm_conv; [exact X | apply geq_ty_sound, E1].
  - (* Σ: the neutral projections *)
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as HP.
    pose proof (gne_tm_red Hν' HT' (lequiv_sym _ _ _ Hl)) as HP'.
    refine (SigRel_neutral Hw1 HA HAA HBB _ _ IHdom IHcod _ _ HP HP').
    + intros ρ a a' ha. exact (proj2 (proj2 (escape_tm _ _ _ _ _ _ _ _ (domAd ρ) a a' ha))).
    + intros ρ a a' ha. exact (proj2 (proj2 (escape_ty _ _ _ _ _ _ _ _ (codAd ρ a a' ha)))).
  - (* Unit: typed neutrals are related *)
    assert (EU : [ G ; Γ ⊢g T ≅ tyUnit l1 @ l ]) by apply HT.
    assert (EU' : [ G ; Γ ⊢g T' ≅ tyUnit l2 @ l ]) by apply HT'.
    pose proof (lequiv_sym _ _ _ Hl) as Hl'.
    pose proof (lequiv_trans _ _ _ _ Hl2 Hl') as Hl2'.
    assert (X1 : [ G ; Γ ⊢g ν : tyUnit l1 @ l1 ]).
    { eapply conv_tm; [exact (gne_tm_typed_l Hν) | eapply eqty_lconv; [apply eqty_sym, EU | exact Hl'] | exact Hl']. }
    assert (X2 : [ G ; Γ ⊢g ν' : tyUnit l1 @ l1 ]).
    { apply (unit_conv Hl2).
      eapply conv_tm; [exact (gne_tm_typed_r Hν') | eapply eqty_lconv; [apply eqty_sym, EU' | exact Hl2'] | exact Hl2']. }
    exists ν, ν'. refine (conj (tmred_refl _ _ _ X1) (conj (tmred_refl _ _ _ X2) (conj _ _))).
    + constructor; exact (gne_tm_whne_l Hν).
    + constructor; exact (gne_tm_whne_r Hν').
  - (* sEq: typed neutrals are related *)
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as HP.
    destruct (gne_tmred_refl HP) as [H1 H2].
    exists ν, ν'. refine (conj H1 (conj H2 (conj _ _))).
    + constructor; exact (gne_tm_whne_l Hν).
    + constructor; exact (gne_tm_whne_r Hν').
  - (* sEmpty: each side a neutral related to itself *)
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as HP.
    destruct (gne_tmred_refl HP) as [H1 H2].
    exists ν, ν'. refine (conj H1 (conj H2 (conj _ _))).
    + exact (gne_tm_trans HP (gne_tm_sym HP)).
    + exact (gne_tm_trans (gne_tm_sym HP) HP).
  - (* Id: typed neutrals are related, as neutrals *)
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as HP.
    destruct (gne_tmred_refl HP) as [H1 H2].
    exists ν, ν'. refine (conj H1 (conj H2 (conj (gne_tm_geq HP) _))).
    now apply idnf_ne.
  - (* Empty: each side a neutral related to itself, as at sEmpty *)
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as HP.
    destruct (gne_tmred_refl HP) as [H1 H2].
    exists ν, ν'. refine (conj H1 (conj H2 (conj _ _))).
    + exact (gne_tm_trans HP (gne_tm_sym HP)).
    + exact (gne_tm_trans (gne_tm_sym HP) HP).
  - (* +: typed neutrals are related, as neutrals *)
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as HP.
    destruct (gne_tmred_refl HP) as [H1 H2].
    exists ν, ν'. refine (conj H1 (conj H2 (conj (gne_tm_geq HP) _))).
    now apply sumnf_ne.
  - (* W: typed neutrals are related, as neutrals *)
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as HP.
    destruct (gne_tmred_refl HP) as [H1 H2].
    econstructor; [exact H1 | exact H2 | exact (gne_tm_geq HP) | now apply wnf_ne].
  - (* Wf: typed neutrals are related, as neutrals *)
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as HP.
    destruct (gne_tmred_refl HP) as [H1 H2].
    econstructor; [exact H1 | exact H2 | exact (gne_tm_geq HP) | now apply wfnf_ne].
  - (* ∥·∥: each side a neutral related to itself, as at Empty *)
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as HP.
    destruct (gne_tmred_refl HP) as [H1 H2].
    split; [exists ν | exists ν']; split; [exact H1 | | exact H2 |]; apply sqnf_ne.
    + exact (gne_tm_trans HP (gne_tm_sym HP)).
    + exact (gne_tm_trans (gne_tm_sym HP) HP).
  - (* IWf: typed neutrals are related, as neutrals *)
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as HP.
    destruct (gne_tmred_refl HP) as [H1 H2].
    econstructor; [exact H1 | exact H2 | exact (gne_tm_geq HP) | now apply iwfnf_ne].
  - (* M: by depth, the shapes and positions by their induction hypotheses *)
    pose proof (MSide_of_LR Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HmX HmA HmB HmC HmXX HmAA HmBB HmCC
                  midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon) as HM.
    pose proof (gne_tm_red Hν HT (lequiv_sym _ _ _ Hl)) as HP.
    pose proof (gne_tm_red Hν' HT' (lequiv_sym _ _ _ Hl)) as HP'.
    intros k. exact (MRn_ne k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM (wf_tm_nf Hmm) (wf_tm_nf Hmm') mixAd
                       (fun ρ x x' v v' h => IHmsh ρ x x' h v v')
                       (fun ρ x x' a a' v v' h ha => IHmpos ρ x x' a a' h ha v v') _ _ HP HP').
Qed.

End Neutral.
