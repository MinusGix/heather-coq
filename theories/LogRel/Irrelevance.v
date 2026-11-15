(** * Irrelevance (ch. 7, Right Irrelevance)

    Two derivations relating the same left type [T] to [T'] and to [T'']
    give equivalent term relations.  The left type fixes the shape (weak
    head normal forms are unique), the universe level and the Π components;
    the right-hand types only enter through conversion. *)
From DeLaM.LogRel Require Export Modal.
From DeLaM.LogRel Require Import MAux.

Section Irrelevance.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

(** ** Declarative helpers at the instance's layer *)

Lemma tyred_eq' {G Γ T W l} : [ G ; Γ ⊢g T ⤳* W @ l ] -> [ G ; Γ ⊢g T ≅ W @ l ].
Proof using . now intros []. Qed.

(** Right-hand types related to the same left type are convertible. *)
Lemma right_conv {n rec G Γ T T' T'' l R R'} :
  LR n rec G Γ T T' l R -> LR n rec G Γ T T'' l R' -> [ G ; Γ ⊢g T' ≅ T'' @ l ].
Proof using EL.
  intros H1 H2. apply escape_ty in H1 as (_ & _ & H1), H2 as (_ & _ & H2).
  apply geq_ty_sound in H1, H2. eapply eqty_trans; [apply eqty_sym, H1 | exact H2].
Qed.

(** ** Shapes: typed reductions of one type to two whnfs agree *)

Lemma red_whnf_agree {G Γ T W W' l l'} :
  [ G ; Γ ⊢g T ⤳* W @ l ] -> [ G ; Γ ⊢g T ⤳* W' @ l' ] -> whnf_ty W -> whnf_ty W' -> W = W'.
Proof using . apply tyred_whnf_det. Qed.

Ltac whnf_of V :=
  match goal with
  | H : [ _ ; _ ⊢ V ~ _ @ _ ] |- _ => exact (whnf_ty_ne _ (gne_ty_whne_l H))
  | _ => solve [eauto with whnf]
  end.

(** Two reductions of the same type: identify the targets, or refute. *)
Ltac agree :=
  match goal with
  | H1 : tyred ?G ?i ?Γ ?T ?W1 ?l, H2 : tyred ?G ?i ?Γ ?T ?W2 ?l' |- _ =>
      let Heq := fresh "Heq" in
      assert (Heq : W1 = W2) by (eapply red_whnf_agree; [exact H1 | exact H2 | whnf_of W1 | whnf_of W2]);
      clear H2;
      first [ discriminate Heq
            | injection Heq; intros; subst
            | subst W1
            | subst W2
            | clear Heq ]
  end.

(** Expose the reduction of the left type of a contextual-type case. *)
Ltac open_mod :=
  match goal with HM : ModRel _ _ _ _ _ _ |- _ => destruct HM end.

Ltac ne_absurd :=
  match goal with
  | H : [ _ ; _ ⊢ ?V ~ _ @ _ ] |- _ =>
      let Hw := fresh in pose proof (gne_ty_whne_l H) as Hw; solve [inversion Hw]
  end.

(** ** The neutral case *)

Lemma NeRel_conv {G Γ V V' V'' l t t'} :
  [ G ; Γ ⊢g V' ≅ V'' @ l ] -> NeRel G Γ V V' l t t' -> NeRel G Γ V V'' l t t'.
Proof using EL.
  intros HV (ν & ν' & H1 & H2 & H3 & H4). exists ν, ν'.
  refine (conj H1 (conj _ (conj H3 _))).
  - eapply tmred_conv; eauto using ge_typeof.
  - eapply gne_tm_conv; eauto.
Qed.

(** ** The Π case, one direction *)

Section PiDir.
Context {G Γ l1 l2 l3 l4 m3 m4 A B A' B' A'' B''}
  {domR : DomRel G Γ} {codR : CodRel G Γ domR}
  {domR' : DomRel G Γ} {codR' : CodRel G Γ domR'}
  (Hl1 : lwf (gL G) l1)
  (HA : [ G ; Γ ⊢g A @ l1 ]) (HA' : [ G ; Γ ⊢g A' @ l1 ]) (HA'' : [ G ; Γ ⊢g A'' @ l1 ])
  (HAA' : [ G ; Γ ⊢ A ≈ A' @ l1 ]) (HAA'' : [ G ; Γ ⊢ A ≈ A'' @ l1 ])
  (HBB' : [ G ; Γ ,, A @ l1 ⊢ B ≈ B' @ l2 ]) (HBB'' : [ G ; Γ ,, A @ l1 ⊢ B ≈ B'' @ l2 ])
  (HP : [ G ; Γ ⊢g tyPi l3 l4 A' B' ≅ tyPi m3 m4 A'' B'' @ lmax l1 l2 ])
  (Hdom : forall ρ, releq (domR ρ) (domR' ρ))
  (Hcod : forall ρ a a' ha ha', releq (codR ρ a a' ha) (codR' ρ a a' ha')).

Lemma PiRel_dir t t' :
  PiRel G Γ l1 l2 l3 l4 A B A' B' domR codR t t' ->
  PiRel G Γ l1 l2 m3 m4 A B A'' B'' domR' codR' t t'.
Proof using EL HA HA' HA'' HAA' HAA'' HBB' HBB'' HP Hcod Hdom Hl1.
  intros (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
  exists w, w'. refine (conj Hw (conj _ (conj Hnf (conj Hnf' (conj Heq (conj _ _)))))).
  - eapply tmred_conv; eauto using ge_typeof.
  - eapply geq_tm_conv; eauto.
  - intros ρ a a' ha' la lb la' lb' A1 B1 A1' B1' H1 H2 H3 H4 HA1 HB1 HA1' HB1'.
    pose proof ((proj2 (Hdom ρ a a')) ha') as ha.
    apply (Hcod ρ a a' ha ha').
    (* the annotations of the right application, in terms of [A'], [B'] *)
    pose proof (kw_lwf ρ Hl1) as Hl1'.
    pose proof (kw_ext ρ HA'' Hl1) as HΔA''.
    pose proof (kw_ext ρ HA' Hl1) as HΔA'.
    assert (E1 : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A ≈ kty ρ A' @ l1 ]) by exact (kw_geq_ty ρ HAA').
    assert (E2 : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A ≈ kty ρ A'' @ l1 ]) by exact (kw_geq_ty ρ HAA'').
    assert (E3 : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l1 ⊢ ktyl ρ B' ≈ ktyl ρ B'' @ l2 ]).
    { eapply geq_ty_trans; [apply geq_ty_sym, (kw_geq_ty_l ρ HA Hl1 HBB')
                            | exact (kw_geq_ty_l ρ HA Hl1 HBB'')]. }
    refine (HK ρ a a' ha la lb la' lb' A1 B1 A1' B1' H1 H2 H3 H4 HA1 HB1 _ _).
    + eapply geq_ty_trans; [|exact HA1'].
      eapply geq_ty_trans; [apply geq_ty_sym, E1 | exact E2].
    + (* move [B'⟨r⟩ ≈ B''⟨r⟩] to [Δ, A''⟨r⟩], compose, move to [Δ, A'⟨r⟩] *)
      assert (E4 : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A'' @ l1 ⊢ ktyl ρ B' ≈ B1' @ l2 ]).
      { eapply geq_ty_trans; [|exact HB1'].
        eapply geq_ty_ctxconv; [apply geq_ty_sound, E2 | now apply lequiv_refl | exact HΔA'' | exact E3]. }
      eapply geq_ty_ctxconv; [| now apply lequiv_refl | exact HΔA' | exact E4].
      apply geq_ty_sound. eapply geq_ty_trans; [apply geq_ty_sym, E2 | exact E1].
Qed.

End PiDir.

(** ** The Σ case, one direction *)

Section SigDir.
Context {G Γ l1 l2 l3 l4 m3 m4 A B A' B' A'' B''}
  {domR : DomRel G Γ} {codR : CodRel G Γ domR}
  {domR' : DomRel G Γ} {codR' : CodRel G Γ domR'}
  (Hl1 : lwf (gL G) l1)
  (HA : [ G ; Γ ⊢g A @ l1 ]) (HA' : [ G ; Γ ⊢g A' @ l1 ]) (HA'' : [ G ; Γ ⊢g A'' @ l1 ])
  (HAA' : [ G ; Γ ⊢ A ≈ A' @ l1 ]) (HAA'' : [ G ; Γ ⊢ A ≈ A'' @ l1 ])
  (HBB' : [ G ; Γ ,, A @ l1 ⊢ B ≈ B' @ l2 ]) (HBB'' : [ G ; Γ ,, A @ l1 ⊢ B ≈ B'' @ l2 ])
  (HP : [ G ; Γ ⊢g tySig l3 l4 A' B' ≅ tySig m3 m4 A'' B'' @ lmax l1 l2 ])
  (Hdom : forall ρ, releq (domR ρ) (domR' ρ))
  (Hcod : forall ρ a a' ha ha', releq (codR ρ a a' ha) (codR' ρ a a' ha')).

Lemma SigRel_dir t t' :
  SigRel G Γ l1 l2 l3 l4 A B A' B' domR codR t t' ->
  SigRel G Γ l1 l2 m3 m4 A B A'' B'' domR' codR' t t'.
Proof using EL HA HA' HA'' HAA' HAA'' HBB' HBB'' HP Hcod Hdom Hl1.
  intros (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
  exists w, w'. refine (conj Hw (conj _ (conj Hnf (conj Hnf' (conj Heq (conj _ _)))))).
  - eapply tmred_conv; eauto using ge_typeof.
  - eapply geq_tm_conv; eauto.
  - intros ρ la lb la' lb' A1 B1 A1' B1' H1 H2 H3 H4 HA1 HB1 HA1' HB1'.
    (* the annotations of the right application, in terms of [A'], [B'] *)
    pose proof (kw_lwf ρ Hl1) as Hl1'.
    pose proof (kw_ext ρ HA'' Hl1) as HΔA''.
    pose proof (kw_ext ρ HA' Hl1) as HΔA'.
    assert (E1 : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A ≈ kty ρ A' @ l1 ]) by exact (kw_geq_ty ρ HAA').
    assert (E2 : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A ≈ kty ρ A'' @ l1 ]) by exact (kw_geq_ty ρ HAA'').
    assert (E3 : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l1 ⊢ ktyl ρ B' ≈ ktyl ρ B'' @ l2 ]).
    { eapply geq_ty_trans; [apply geq_ty_sym, (kw_geq_ty_l ρ HA Hl1 HBB')
                            | exact (kw_geq_ty_l ρ HA Hl1 HBB'')]. }
    assert (X1 : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A' ≈ A1' @ l1 ]).
    { eapply geq_ty_trans; [|exact HA1']. eapply geq_ty_trans; [apply geq_ty_sym, E1 | exact E2]. }
    assert (X2 : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A' @ l1 ⊢ ktyl ρ B' ≈ B1' @ l2 ]).
    { (* move [B'⟨r⟩ ≈ B''⟨r⟩] to [Δ, A''⟨r⟩], compose, move to [Δ, A'⟨r⟩] *)
      assert (E4 : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A'' @ l1 ⊢ ktyl ρ B' ≈ B1' @ l2 ]).
      { eapply geq_ty_trans; [|exact HB1'].
        eapply geq_ty_ctxconv; [apply geq_ty_sound, E2 | now apply lequiv_refl | exact HΔA'' | exact E3]. }
      eapply geq_ty_ctxconv; [| now apply lequiv_refl | exact HΔA' | exact E4].
      apply geq_ty_sound. eapply geq_ty_trans; [apply geq_ty_sym, E2 | exact E1]. }
    destruct (HK ρ la lb la' lb' A1 B1 A1' B1' H1 H2 H3 H4 HA1 HB1 X1 X2) as [h Hc].
    exists (proj1 (Hdom ρ _ _) h). exact (proj1 (Hcod ρ _ _ h _ _ _) Hc).
Qed.

End SigDir.

(** ** Indexed [M], one direction (M18b)

    [MRn] at two right signatures and relations agreeing with each other
    where both are defined, by induction on the depth: the generic
    clauses move along the right types' conversion, the observations by
    [SigRel_dir] at [out]'s type and, in its codomain, [PiRel_dir] at the
    children's, whose codomain is the induction hypothesis in a world. *)
Section MIrrel.

Lemma MGen_dir {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C'' m m' m'' t t'} :
  [ G ; Γ ⊢g tyM r1 r2 ri X' A' B' C' m' ≅ tyM s1 s2 si X'' A'' B'' C'' m'' @ mlvl l1 l2 li ] ->
  MGen G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' m m' t t' ->
  MGen G Γ l1 l2 li X A B C s1 s2 si X'' A'' B'' C'' m m'' t t'.
Proof using EL.
  intros ET (w & w' & H1 & H2 & H3 & H4 & H5 & H6). exists w, w'.
  refine (conj H1 (conj _ (conj H3 (conj H4 (conj H5 _))))).
  - eapply tmred_conv; [apply ge_typeof | exact H2 | exact ET].
  - eapply geq_tm_conv; [exact H6 | exact ET].
Qed.

(** The hypotheses of one direction: the two sides, the relations'
    agreement, and the indices. *)
Definition MIrrHyps G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C''
    (idxR idxR' : DomRel G Γ) (shR shR' : MShRel G Γ) (posR posR' : MPosRel G Γ) (m m' m'' : tm) : Prop :=
  MSide G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR /\
  MSide G Γ l1 l2 li X A B C s1 s2 si X'' A'' B'' C'' idxR' shR' posR' /\
  (forall ρ x x' x'', idxR ρ x x' -> idxR' ρ x x'' -> releq (shR ρ x x') (shR' ρ x x'')) /\
  (forall ρ x x' x'' a a', idxR ρ x x' -> idxR' ρ x x'' -> shR ρ x x' a a' ->
     releq (posR ρ x x' a a') (posR' ρ x x'' a a')) /\
  nftm m /\ nftm m' /\ nftm m'' /\
  (forall ρ, idxR ρ (ktm ρ m) (ktm ρ m')) /\ (forall ρ, idxR' ρ (ktm ρ m) (ktm ρ m'')).

Lemma MIrrHyps_swap {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C''
    idxR idxR' shR shR' posR posR' m m' m''} :
  MIrrHyps G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C'' idxR idxR' shR shR' posR posR' m m' m'' ->
  MIrrHyps G Γ l1 l2 li X A B C s1 s2 si X'' A'' B'' C'' r1 r2 ri X' A' B' C' idxR' idxR shR' shR posR' posR m m'' m'.
Proof using.
  intros (H1 & H2 & HS & HP & N & N' & N'' & I1 & I2).
  refine (conj H2 (conj H1 (conj _ (conj _ (conj N (conj N'' (conj N' (conj I2 I1)))))))).
  - intros ρ x x'' x' h2 h1. apply releq_sym', (HS ρ x x' x'' h1 h2).
  - intros ρ x x'' x' a a' h2 h1 ha. apply releq_sym', (HP ρ x x' x'' a a' h1 h2).
    exact (proj2 (HS ρ x x' x'' h1 h2 a a') ha).
Qed.

(** The hypotheses at a child. *)
Lemma MIrrHyps_child {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C''
    idxR idxR' shR shR' posR posR' m m' m''} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) a a' p p' :
  MIrrHyps G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C'' idxR idxR' shR shR' posR posR' m m' m'' ->
  shR ρ (ktm ρ m) (ktm ρ m') a a' ->
  posR (kw_comp ρ ρ') (ktm (kw_comp ρ ρ') m) (ktm (kw_comp ρ ρ') m') (ktm ρ' a) (ktm ρ' a') p p' ->
  MIrrHyps (kw_G ρ') (kw_Δ ρ')
    l1 l2 li (kty (kw_comp ρ ρ') X) (ktyl (kw_comp ρ ρ') A) (ktyll (kw_comp ρ ρ') B) (ktmlll (kw_comp ρ ρ') C)
    r1 r2 ri (kty (kw_comp ρ ρ') X') (ktyl (kw_comp ρ ρ') A') (ktyll (kw_comp ρ ρ') B') (ktmlll (kw_comp ρ ρ') C')
    s1 s2 si (kty (kw_comp ρ ρ') X'') (ktyl (kw_comp ρ ρ') A'') (ktyll (kw_comp ρ ρ') B'')
      (ktmlll (kw_comp ρ ρ') C'')
    (fun ρ'' => idxR (kw_comp (kw_comp ρ ρ') ρ'')) (fun ρ'' => idxR' (kw_comp (kw_comp ρ ρ') ρ''))
    (fun ρ'' => shR (kw_comp (kw_comp ρ ρ') ρ'')) (fun ρ'' => shR' (kw_comp (kw_comp ρ ρ') ρ''))
    (fun ρ'' => posR (kw_comp (kw_comp ρ ρ') ρ'')) (fun ρ'' => posR' (kw_comp (kw_comp ρ ρ') ρ''))
    (ktmlll (kw_comp ρ ρ') C)[lsingle3 (ktm (kw_comp ρ ρ') m) (ktm ρ' a) p]
    (ktmlll (kw_comp ρ ρ') C')[lsingle3 (ktm (kw_comp ρ ρ') m') (ktm ρ' a') p']
    (ktmlll (kw_comp ρ ρ') C'')[lsingle3 (ktm (kw_comp ρ ρ') m'') (ktm ρ' a') p'].
Proof using EL.
  intros (HM1 & HM2 & HS & HP & Nm & Nm' & Nm'' & I1 & I2) ha hp.
  set (ρ1 := kw_comp ρ ρ').
  pose proof (proj1 (HS ρ _ _ _ (I1 ρ) (I2 ρ) a a') ha) as ha2.
  (* the shapes, moved to [ρ1] *)
  assert (Sa1 : shR ρ1 (ktm ρ1 m) (ktm ρ1 m') (ktm ρ' a) (ktm ρ' a')).
  { subst ρ1. rewrite !ktm_comp. exact (ms_shmon HM1 ρ ρ' _ _ _ _ (I1 ρ) ha). }
  assert (Sa2 : shR' ρ1 (ktm ρ1 m) (ktm ρ1 m'') (ktm ρ' a) (ktm ρ' a')).
  { subst ρ1. rewrite !ktm_comp. exact (ms_shmon HM2 ρ ρ' _ _ _ _ (I2 ρ) ha2). }
  pose proof (proj1 (HP ρ1 _ _ _ _ _ (I1 ρ1) (I2 ρ1) Sa1 p p') hp) as hp2.
  (* the positions are normal *)
  assert (Np : nftm p /\ nftm p').
  { pose proof (geq_tm_sound (ms_eP HM1 ρ1 _ _ _ _ _ _ (I1 ρ1) Sa1 hp)) as Ep.
    exact (conj (wf_tm_nf (eqtm_wf_l ge_typeof Ep)) (wf_tm_nf (eqtm_wf_r ge_typeof Ep))). }
  destruct Np as [Np Np'].
  assert (Nr : forall t : tm, nftm (ktm ρ1 t)) by (intros; unfold ktm; apply ren_nf).
  assert (Nr' : forall t : tm, nftm (ktm ρ' t)) by (intros; unfold ktm; apply ren_nf).
  assert (Nl : forall t : tm, nftm (ktmlll ρ1 t)) by (intros; unfold ktmlll; apply ren_nf).
  (* the child indices in a world *)
  assert (Hch : forall (R : DomRel G Γ) (S : MShRel G Γ) (P : MPosRel G Γ) X0 A0 B0 C0 k1 k2 ki X1 A1 B1 C1 n n' b b' q q',
             MSide G Γ l1 l2 li X0 A0 B0 C0 k1 k2 ki X1 A1 B1 C1 R S P ->
             (forall ρ, R ρ (ktm ρ n) (ktm ρ n')) ->
             S ρ1 (ktm ρ1 n) (ktm ρ1 n') b b' -> P ρ1 (ktm ρ1 n) (ktm ρ1 n') b b' q q' ->
             forall ρ'' : kwk (kw_G ρ') (kw_Δ ρ'),
             R (kw_comp ρ1 ρ'') (ktm ρ'' (ktmlll ρ1 C0)[lsingle3 (ktm ρ1 n) b q])
               (ktm ρ'' (ktmlll ρ1 C1)[lsingle3 (ktm ρ1 n') b' q'])).
  { intros R S P X0 A0 B0 C0 k1 k2 ki X1 A1 B1 C1 n n' b b' q q' HM In Sb Pq ρ''.
    pose proof (ms_shmon HM ρ1 ρ'' _ _ _ _ (In ρ1) Sb) as Sb'.
    pose proof (ms_posmon HM ρ1 ρ'' _ _ _ _ _ _ (In ρ1) Sb Pq) as Pq'.
    rewrite <- !ktm_comp in Sb', Pq'.
    pose proof (ms_ch HM _ _ _ _ _ _ _ (In (kw_comp ρ1 ρ'')) Sb' Pq') as Y.
    rewrite !ktm_lsingle3, <- !(ktmlll_comp ρ1 ρ''), <- !(ktm_comp ρ1 ρ''). exact Y. }
  refine (conj (MSide_kw ρ1 HM1) (conj (MSide_kw ρ1 HM2) (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
  - intros ρ''. exact (HS (kw_comp ρ1 ρ'')).
  - intros ρ''. exact (HP (kw_comp ρ1 ρ'')).
  - apply subst_nf; [apply Nl | apply LK_lsingle3; auto].
  - apply subst_nf; [apply Nl | apply LK_lsingle3; auto].
  - apply subst_nf; [apply Nl | apply LK_lsingle3; auto].
  - intros ρ''. exact (Hch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM1 I1 Sa1 hp ρ'').
  - intros ρ''. exact (Hch _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM2 I2 Sa2 hp2 ρ'').
Qed.

Lemma lequiv_mlvl {L l1 l2 li r1 r2 ri} :
  lequiv L l1 r1 -> lequiv L l2 r2 -> lequiv L li ri -> lequiv L (mlvl l1 l2 li) (mlvl r1 r2 ri).
Proof using. intros. now apply lequiv_max; [apply lequiv_max|]. Qed.

(** One direction at a depth. *)
Definition MDirAt n := forall G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C''
    idxR idxR' shR shR' posR posR' m m' m'',
  MIrrHyps G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C'' idxR idxR' shR shR' posR posR' m m' m'' ->
  forall t t', MRn n G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' shR posR m m' t t' ->
    MRn n G Γ l1 l2 li X A B C s1 s2 si X'' A'' B'' C'' shR' posR' m m'' t t'.

(** The hypotheses in a world. *)
Lemma MIrrHyps_kw {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C''
    idxR idxR' shR shR' posR posR' m m' m''} (ρ : kwk G Γ) :
  MIrrHyps G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C'' idxR idxR' shR shR' posR posR' m m' m'' ->
  MIrrHyps (kw_G ρ) (kw_Δ ρ) l1 l2 li (kty ρ X) (ktyl ρ A) (ktyll ρ B) (ktmlll ρ C)
    r1 r2 ri (kty ρ X') (ktyl ρ A') (ktyll ρ B') (ktmlll ρ C') s1 s2 si (kty ρ X'') (ktyl ρ A'') (ktyll ρ B'') (ktmlll ρ C'')
    (fun ρ' => idxR (kw_comp ρ ρ')) (fun ρ' => idxR' (kw_comp ρ ρ')) (fun ρ' => shR (kw_comp ρ ρ'))
    (fun ρ' => shR' (kw_comp ρ ρ')) (fun ρ' => posR (kw_comp ρ ρ')) (fun ρ' => posR' (kw_comp ρ ρ'))
    (ktm ρ m) (ktm ρ m') (ktm ρ m'').
Proof using EL.
  intros (HM1 & HM2 & HS & HP & _ & _ & _ & I1 & I2).
  refine (conj (MSide_kw ρ HM1) (conj (MSide_kw ρ HM2) (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))).
  3-5: kw_nf.
  - intros ρ'. exact (HS (kw_comp ρ ρ')).
  - intros ρ'. exact (HP (kw_comp ρ ρ')).
  - intros ρ'. cbn beta. rewrite <- !ktm_comp. exact (I1 (kw_comp ρ ρ')).
  - intros ρ'. cbn beta. rewrite <- !ktm_comp. exact (I2 (kw_comp ρ ρ')).
Qed.

(** The observations, given the children's. *)
Lemma MObs_dir n (IH : MDirAt n) {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C''
    idxR idxR' shR shR' posR posR' m m' m''} :
  MIrrHyps G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C'' idxR idxR' shR shR' posR posR' m m' m'' ->
  forall t t', MObs (MRn n) G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' shR posR m m' t t' ->
    MObs (MRn n) G Γ l1 l2 li X A B C s1 s2 si X'' A'' B'' C'' shR' posR' m m'' t t'.
Proof using EL.
  intros H t t' Ht.
  pose proof H as (HM1 & HM2 & HSr & HPr & Nm & Nm' & Nm'' & I1 & I2).
  pose proof (ms_geq HM1) as HG1; pose proof (ms_geq HM2) as HG2.
  destruct (MSide_root HM1 Nm Nm' I1) as (Em1 & EA1 & EB1 & EC1).
  destruct (MSide_root HM2 Nm Nm'' I2) as (Em2 & EA2 & EB2 & EC2).
  intros k1 k2 ki X1 A1 B1 C1 j1 k1' k2' ki' X1' A1' B1' C1' j1' Ann Ann''.
  pose proof HG1 as (Hr1 & Hr2 & Hri & (W1 & W2 & Wi & _) & HXX' & _).
  pose proof HG2 as (Hs1 & Hs2 & Hsi & _).
  (* the second right annotations, at the first right signature *)
  assert (Ann' : MAnn G Γ r1 r2 ri X' A' B' C' m' k1' k2' ki' X1' A1' B1' C1' j1').
  { refine (MAnn_conv (MEq_trans ge_typeof ge_notV (MEq_sym ge_typeof ge_notV (MEq_of_MGeq HG1))
                         (MEq_of_MGeq HG2)) _ Ann'').
    eapply eqtm_lconv; [| exact (lequiv_sym _ _ _ Hri)].
    eapply eqtm_conv; [| rewrite ge_typeof; exact (eqty_sym _ _ _ _ _ _ (geq_ty_sound HXX'))].
    eapply eqtm_trans; [apply eqtm_sym, (geq_tm_sound Em1) | exact (geq_tm_sound Em2)]. }
  specialize (Ht k1 k2 ki X1 A1 B1 C1 j1 k1' k2' ki' X1' A1' B1' C1' j1' Ann Ann').
  pose proof (geq_ty_sound EA1) as DA1. pose proof (geq_ty_sound EA2) as DA2.
  refine (SigRel_dir W1 (eqty_wf_l ge_typeof DA1) (eqty_wf_r ge_typeof DA1) (eqty_wf_r ge_typeof DA2)
            EA1 EA2 (M_outB_geq HG1 EB1 EC1) (M_outB_geq HG2 EB2 EC2) _ _ _ _ _ Ht).
  - pose proof (eqty_wf_l ge_typeof DA1) as HA.
    eapply (eqty_trans _ _ _ _ (tySig l1 (mlvl l1 l2 li) A[lsingle m]
              (tyPi l2 (mlvl l1 l2 li) B[llift (lsingle m)] (mKidTy l1 l2 li X A B C m)))); [apply eqty_sym|]; apply geq_ty_sound, geq_ty_sig;
      first [ eassumption | apply lequiv_mlvl; assumption | exact (M_outB_geq HG1 EB1 EC1)
            | exact (M_outB_geq HG2 EB2 EC2) ].
  - intros ρ. exact (HSr ρ _ _ _ (I1 ρ) (I2 ρ)).
  - intros ρ a a' ha ha'. cbv beta.
    pose proof (ms_gBa HM1 ρ _ _ a a' (I1 ρ) ha) as GB1.
    pose proof (ms_gBa HM2 ρ _ _ a a' (I2 ρ) ha') as GB2.
    pose proof (ms_gCa HM1 ρ _ _ a a' (I1 ρ) ha) as GC1.
    pose proof (ms_gCa HM2 ρ _ _ a a' (I2 ρ) ha') as GC2.
    pose proof (geq_ty_sound GB1) as DB1. pose proof (geq_ty_sound GB2) as DB2.
    pose proof (eqty_wf_l ge_typeof DB1) as HB.
    pose proof (kw_lwf ρ W2) as W2'.
    pose proof (ext_wf_g HB W2') as HΔB.
    pose proof (MGeq_M (MGeq_wk1 (MGeq_kw ρ HG1) HΔB) GC1) as K1.
    pose proof (MGeq_M (MGeq_wk1 (MGeq_kw ρ HG2) HΔB) GC2) as K2.
    rewrite !kw_B_single, !kw_mKid. rewrite !mKid_single by kw_nf.
    assert (Hdom : forall ρ' : kwk (kw_G ρ) (kw_Δ ρ),
      releq (posR (kw_comp ρ ρ') (ktm (kw_comp ρ ρ') m) (ktm (kw_comp ρ ρ') m') (ktm ρ' a) (ktm ρ' a'))
            (posR' (kw_comp ρ ρ') (ktm (kw_comp ρ ρ') m) (ktm (kw_comp ρ ρ') m'') (ktm ρ' a) (ktm ρ' a'))).
    { intros ρ'.
      assert (Sa1 : shR (kw_comp ρ ρ') (ktm (kw_comp ρ ρ') m) (ktm (kw_comp ρ ρ') m') (ktm ρ' a) (ktm ρ' a')).
      { rewrite !(ktm_comp ρ ρ'). exact (ms_shmon HM1 ρ ρ' _ _ _ _ (I1 ρ) ha). }
      exact (HPr (kw_comp ρ ρ') _ _ _ _ _ (I1 _) (I2 _) Sa1). }
    assert (HP : [ kw_G ρ ; kw_Δ ρ ⊢g
        tyPi r2 (mlvl r1 r2 ri) (ktyll ρ B')[lsingle2 (ktm ρ m') a']
          (tyM r1 r2 ri (kty ρ X')⟨↑⟩ (ktyl ρ A')⟨rlift ↑⟩ (ktyll ρ B')⟨rlift (rlift ↑)⟩
             (ktmlll ρ C')⟨rlift (rlift (rlift ↑))⟩ (ktmlll ρ C')[llift (lsingle2 (ktm ρ m') a')])
        ≅ tyPi s2 (mlvl s1 s2 si) (ktyll ρ B'')[lsingle2 (ktm ρ m'') a']
          (tyM s1 s2 si (kty ρ X'')⟨↑⟩ (ktyl ρ A'')⟨rlift ↑⟩ (ktyll ρ B'')⟨rlift (rlift ↑)⟩
             (ktmlll ρ C'')⟨rlift (rlift (rlift ↑))⟩ (ktmlll ρ C'')[llift (lsingle2 (ktm ρ m'') a')])
        @ lmax l2 (mlvl l1 l2 li) ]).
    { eapply (eqty_trans _ _ _ _ (tyPi l2 (mlvl l1 l2 li) (ktyll ρ B)[lsingle2 (ktm ρ m) a]
          (tyM l1 l2 li (kty ρ X)⟨↑⟩ (ktyl ρ A)⟨rlift ↑⟩ (ktyll ρ B)⟨rlift (rlift ↑)⟩
             (ktmlll ρ C)⟨rlift (rlift (rlift ↑))⟩ (ktmlll ρ C)[llift (lsingle2 (ktm ρ m) a)])));
        [apply eqty_sym|]; apply geq_ty_sound, geq_ty_pi;
        first [ exact HB | exact GB1 | exact GB2 | exact K1 | exact K2
              | apply kw_lequiv; assumption | apply lequiv_mlvl; apply kw_lequiv; assumption ]. }
    intros t1 t1'; split; intros Ht1.
    + refine (PiRel_dir W2' HB (eqty_wf_r ge_typeof DB1) (eqty_wf_r ge_typeof DB2) GB1 GB2 K1 K2 HP
                Hdom _ _ _ Ht1).
      intros ρ' p p' hp hp'. intros t2 t2'; split; intros Ht2.
      * eapply IH; [exact (MIrrHyps_child ρ ρ' a a' p p' H ha hp) | exact Ht2].
      * eapply IH; [exact (MIrrHyps_swap (MIrrHyps_child ρ ρ' a a' p p' H ha hp)) | exact Ht2].
    + refine (PiRel_dir W2' HB (eqty_wf_r ge_typeof DB2) (eqty_wf_r ge_typeof DB1) GB2 GB1 K2 K1
                (eqty_sym _ _ _ _ _ _ HP) (fun ρ' => releq_sym' (Hdom ρ')) _ _ _ Ht1).
      intros ρ' p p' hp hp'. intros t2 t2'; split; intros Ht2.
      * eapply IH; [exact (MIrrHyps_swap (MIrrHyps_child ρ ρ' a a' p p' H ha hp')) | exact Ht2].
      * eapply IH; [exact (MIrrHyps_child ρ ρ' a a' p p' H ha hp') | exact Ht2].
Qed.

(** One direction, by induction on the depth. *)
Lemma MRn_dir n : MDirAt n.
Proof using EL.
  induction n as [|n IH]; intros G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C''
    idxR idxR' shR shR' posR posR' m m' m'' H t t' Ht.
  all: pose proof H as (HM1 & HM2 & HSr & HPr & Nm & Nm' & Nm'' & I1 & I2).
  all: pose proof (ms_geq HM1) as HG1; pose proof (ms_geq HM2) as HG2.
  all: destruct (MSide_root HM1 Nm Nm' I1) as (Em1 & EA1 & EB1 & EC1).
  all: destruct (MSide_root HM2 Nm Nm'' I2) as (Em2 & EA2 & EB2 & EC2).
  all: assert (ET : [ G ; Γ ⊢g tyM r1 r2 ri X' A' B' C' m' ≅ tyM s1 s2 si X'' A'' B'' C'' m'' @ mlvl l1 l2 li ])
    by (eapply eqty_trans; [apply eqty_sym, geq_ty_sound, (MGeq_M HG1 Em1) | exact (geq_ty_sound (MGeq_M HG2 Em2))]).
  all: destruct Ht as [Hg Ht]; split; [exact (MGen_dir ET Hg) |].
  1: exact I.
  intros ρ. exact (MObs_dir n IH (MIrrHyps_kw ρ H) _ _ (Ht ρ)).
Qed.

Lemma MR_irrel {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C''
    idxR idxR' shR shR' posR posR' m m' m''} :
  MIrrHyps G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' s1 s2 si X'' A'' B'' C'' idxR idxR' shR shR' posR posR' m m' m'' ->
  releq (MR G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' shR posR m m')
        (MR G Γ l1 l2 li X A B C s1 s2 si X'' A'' B'' C'' shR' posR' m m'').
Proof using EL.
  intros H t t'; split; intros Ht n.
  - eapply MRn_dir; [exact H | apply Ht].
  - eapply MRn_dir; [exact (MIrrHyps_swap H) | apply Ht].
Qed.

(** A side from [LRm]'s premises. *)
Lemma MSide_of_LR {n rec G Γ l1 l2 li r1 r2 ri X X' A A' B B' C C' idxR shR posR} :
  lequiv (gL G) r1 l1 -> lequiv (gL G) r2 l2 -> lequiv (gL G) ri li ->
  lwf (gL G) l1 -> lwf (gL G) l2 -> lwf (gL G) li ->
  [ G ; Γ ⊢g X @ li ] -> [ G ; Γ ,, X @ li ⊢g A @ l1 ] -> [ G ; Γ ,, X @ li ,, A @ l1 ⊢g B @ l2 ] ->
  [ G ; Γ ,, X @ li ,, A @ l1 ,, B @ l2 ⊢g C : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] ->
  [ G ; Γ ⊢ X ≈ X' @ li ] -> [ G ; Γ ,, X @ li ⊢ A ≈ A' @ l1 ] ->
  [ G ; Γ ,, X @ li ,, A @ l1 ⊢ B ≈ B' @ l2 ] ->
  [ G ; Γ ,, X @ li ,, A @ l1 ,, B @ l2 ⊢ C ≈ C' : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] ->
  (forall ρ : kwk G Γ, LR n rec (kw_G ρ) (kw_Δ ρ) (kty ρ X) (kty ρ X') li (idxR ρ)) ->
  (forall (ρ : kwk G Γ) x x', idxR ρ x x' ->
      LR n rec (kw_G ρ) (kw_Δ ρ) (ktyl ρ A)[lsingle x] (ktyl ρ A')[lsingle x'] l1 (shR ρ x x')) ->
  (forall (ρ : kwk G Γ) x x' a a', idxR ρ x x' -> shR ρ x x' a a' ->
      LR n rec (kw_G ρ) (kw_Δ ρ) (ktyll ρ B)[lsingle2 x a] (ktyll ρ B')[lsingle2 x' a'] l2
        (posR ρ x x' a a')) ->
  (forall (ρ : kwk G Γ) x x' a a' p p', idxR ρ x x' -> shR ρ x x' a a' -> posR ρ x x' a a' p p' ->
      idxR ρ (ktmlll ρ C)[lsingle3 x a p] (ktmlll ρ C')[lsingle3 x' a' p']) ->
  (forall (ρ : kwk G Γ) x x', idxR ρ x x' ->
      [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ A)[lsingle x] @ l1
          ⊢ (ktyll ρ B)[llift (lsingle x)] ≈ (ktyll ρ B')[llift (lsingle x')] @ l2 ]) ->
  (forall (ρ : kwk G Γ) x x', idxR ρ x x' ->
      [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ A)[lsingle x] @ l1 ,, (ktyll ρ B)[llift (lsingle x)] @ l2
          ⊢ (ktmlll ρ C)[llift (llift (lsingle x))] ≈ (ktmlll ρ C')[llift (llift (lsingle x'))]
          : (kty ρ X)⟨↑⟩⟨↑⟩ @ li ]) ->
  (forall (ρ : kwk G Γ) x x' a a', idxR ρ x x' -> shR ρ x x' a a' ->
      [ kw_G ρ ; kw_Δ ρ ,, (ktyll ρ B)[lsingle2 x a] @ l2
          ⊢ (ktmlll ρ C)[llift (lsingle2 x a)] ≈ (ktmlll ρ C')[llift (lsingle2 x' a')] : (kty ρ X)⟨↑⟩ @ li ]) ->
  (forall (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) x x', idxR ρ x x' ->
      idxR (kw_comp ρ ρ') (ktm ρ' x) (ktm ρ' x')) ->
  (forall (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) x x' a a', idxR ρ x x' -> shR ρ x x' a a' ->
      shR (kw_comp ρ ρ') (ktm ρ' x) (ktm ρ' x') (ktm ρ' a) (ktm ρ' a')) ->
  (forall (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) x x' a a' p p', idxR ρ x x' -> shR ρ x x' a a' ->
      posR ρ x x' a a' p p' ->
      posR (kw_comp ρ ρ') (ktm ρ' x) (ktm ρ' x') (ktm ρ' a) (ktm ρ' a') (ktm ρ' p) (ktm ρ' p')) ->
  MSide G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR.
Proof using EL.
  intros Hr1 Hr2 Hri W1 W2 Wi HX HA HB HC HXX HAA HBB HCC Hidx Hsh Hpos ch gB gC gCa imon shmon posmon.
  split; try assumption.
  - refine (conj (lequiv_sym _ _ _ Hr1) (conj (lequiv_sym _ _ _ Hr2) (conj (lequiv_sym _ _ _ Hri) _))).
    exact (conj (conj W1 (conj W2 (conj Wi (conj HX (conj HA (conj HB HC)))))) (conj HXX (conj HAA (conj HBB HCC)))).
  - intros ρ x x' h. exact (proj2 (proj2 (escape_tm _ _ _ _ _ _ _ _ (Hidx ρ) x x' h))).
  - intros ρ x x' h. exact (proj2 (proj2 (escape_ty _ _ _ _ _ _ _ _ (Hsh ρ x x' h)))).
  - intros ρ x x' a a' h ha. exact (proj2 (proj2 (escape_tm _ _ _ _ _ _ _ _ (Hsh ρ x x' h) a a' ha))).
  - intros ρ x x' a a' h ha. exact (proj2 (proj2 (escape_ty _ _ _ _ _ _ _ _ (Hpos ρ x x' a a' h ha)))).
  - intros ρ x x' a a' p p' h ha hp.
    exact (proj2 (proj2 (escape_tm _ _ _ _ _ _ _ _ (Hpos ρ x x' a a' h ha) p p' hp))).
Qed.

End MIrrel.

(** The binder cases ([Π], [Σ]): the right types are convertible, the
    domain and codomain relations irrelevant, and the term relations move
    along them by [dir]. *)
Ltac poly_irrel F geqF dir :=
  let HP := fresh "HP" in let Hdom := fresh "Hdom" in let Hcod := fresh "Hcod" in
  match goal with
  | |- releq (_ ?G ?Γ ?l1 ?l2 ?l3 ?l4 ?A ?B ?A' ?B' ?dR ?cR)
             (_ _ _ _ _ ?k3 ?k4 _ _ ?C' ?D' ?dR' ?cR') =>
      assert (HP : [ G ; Γ ⊢g F l3 l4 A' B' ≅ F k3 k4 C' D' @ lmax l1 l2 ])
        by (eapply (eqty_trans _ _ _ _ (F l1 l2 A B)); [apply eqty_sym|];
            apply geq_ty_sound, geqF; eauto using lequiv_sym);
      assert (Hdom : forall ρ, releq (dR ρ) (dR' ρ))
        by (intros; match goal with IH : forall (ρ : kwk _ _) T'' R', _ -> releq (dR _) _ |- _ =>
                                        eapply IH end; eauto);
      assert (Hcod : forall ρ a a' ha ha', releq (cR ρ a a' ha) (cR' ρ a a' ha'))
        by (intros; match goal with IH : forall (ρ : kwk _ _) a a' ha T'' R', _ -> releq (cR _ _ _ _) _ |- _ =>
                                        eapply IH end; eauto)
  end;
  intros t t'; split;
  [ eapply dir; eassumption
  | eapply dir; try eassumption;
    [ now apply eqty_sym | intros; apply releq_sym, Hdom | intros; apply releq_sym, Hcod ] ].

(** ** The meta-function cases, one direction *)

Lemma CPiRel_dir {G Γ l1 l2 m2 T1 T1' T1''} {instR instR' : CInstRel G Γ} :
  [ G ; Γ ⊢g tyCPi l2 T1' ≅ tyCPi m2 T1'' @ l1 ] ->
  (forall ρ Δ Δ' h, releq (instR ρ Δ Δ' h) (instR' ρ Δ Δ' h)) ->
  forall t t', CPiRel G Γ l1 l2 T1 T1' instR t t' -> CPiRel G Γ l1 m2 T1 T1'' instR' t t'.
Proof using EL.
  intros HP Hinst t t' (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
  exists w, w'. refine (conj Hw (conj _ (conj Hnf (conj Hnf' (conj Heq (conj _ _)))))).
  - eapply tmred_conv; eauto using ge_typeof.
  - eapply geq_tm_conv; eauto.
  - intros ρ Δ Δ' h. apply (Hinst ρ Δ Δ' h), HK.
Qed.

Lemma TPiRel_dir {G Γ Δ1 Δ1' Δ1'' l1 l2 l3 l4 m3 m4 T1 T1' T1''} {instR instR' : TInstRel G Γ Δ1 l1} :
  [ G ; Γ ⊢g tyTPi Δ1' l3 l4 T1' ≅ tyTPi Δ1'' m3 m4 T1'' @ l2 ] ->
  (forall ρ A A' h, releq (instR ρ A A' h) (instR' ρ A A' h)) ->
  forall t t', TPiRel G Γ Δ1 Δ1' l1 l2 l3 l4 T1 T1' instR t t' ->
    TPiRel G Γ Δ1 Δ1'' l1 l2 m3 m4 T1 T1'' instR' t t'.
Proof using EL.
  intros HP Hinst t t' (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
  exists w, w'. refine (conj Hw (conj _ (conj Hnf (conj Hnf' (conj Heq (conj _ _)))))).
  - eapply tmred_conv; eauto using ge_typeof.
  - eapply geq_tm_conv; eauto.
  - intros ρ A A' h. apply (Hinst ρ A A' h), HK.
Qed.

(** ** Irrelevance *)

Theorem LR_irrel n rec G Γ T T' T'' l R R' :
  LR n rec G Γ T T' l R -> LR n rec G Γ T T'' l R' -> releq R R'.
Proof using EL VL.
  intros H1; revert T'' R'.
  induction H1 as [G Γ T T' l R Hl HT HT' HR
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
                  | G Γ T T' l l1 li1 l2 li2 X X' A A' N N' Ot Ot' Ch Ch' m m' idxR domR R Hl Hl2 Hli2 Hw Hwi
                      HT HT' HX HX' HA HA' HN HN' HO HO' HCh HCh' Hmt Hmt' HXX HAA HNN HOO HChh Hmm
                      idxAd IHidx Hisym Histr domAd IHdom arAd otAd chAd ixAd HR
                  | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                      Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                      HmXX HmAA HmBB HmCC Hmmm midxAd IHmidx mshAd IHmsh mposAd IHmpos mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR
                | G Γ T T' l vl1 vlp1 vli1 vl2 vlp2 vli2 vX vX' vA vA' vN vN' vD vD' vO vO' vC vC' vm vm' vidxR vdomR vpdR R
                    Hl Hvl2 Hvlp2 Hvli2 Hvw Hvwp Hvwi HT HT' HvX HvX' HvA HvA' HvN HvN' HvD HvD' HvO HvO' HvC HvC' Hvm Hvm'
                    HvXX HvAA HvNN HvDD HvOO HvCC Hvmm vidxAd IHvidx Hvisym Hvistr vdomAd IHvdom varAd votAd vpdAd IHvpd vpdE vpdMon vchAd vgC vixAd HR];
    intros T'' R' H2;
    inversion H2 as [? ? ? ? ? ? Hk HTk HTk' HkR
                    | ? ? ? ? ? k1 k2 ? Hk Hk2 Hkn HTk HTk' HkR
                    | ? ? ? ? ? W W' ? HTk HTk' HW HkR
                    | ? ? ? ? ? k1 k2 k3 k4 C D C' D' domR' codR' ?
                        [Hk Hk3 Hk4 Hkw1 Hkw2 HTk HTk' HC HC' HD HD' HCC HDD] domAd' codAd' HkR
                    | ? ? ? ? ? ? Hkj HkM
                    | ? ? ? ? ? k1 k2 U1 U1' instR' ? Hkj Hk Hk2 Hkw1 HTk HTk' HU1 HU1' Hkgeq instAd' HkR
                    | ? ? ? ? ? Θ1 Θ1' k1 k2 k3 k4 U1 U1' instR' ? Hkj Hk Hk3 Hk4 Hkw1 Hkw2 HTk HTk' HΘ
                        HU1 HU1' Hkgeq instAd' HkR
                    | ? ? ? ? ? k1 k2 k3 k4 C D C' D' domR' codR' ?
                        [Hk Hk3 Hk4 Hkw1 Hkw2 HTk HTk' HC HC' HD HD' HCC HDD] domAd' codAd' HkR
                    | ? ? ? ? ? k1 k2 ? Hk Hk2 Hkn HTk HTk' HkR
                    | ? ? ? ? ? t1 t2 C C' c c' d d' ? Hk Hk2 Hkn HTk HTk' HC HCC Hcc Hdd HkR
                    | ? ? ? ? ? t1 t2 ? Hk Hk2 Hkn HTk HTk' HkR
                    | ? ? ? ? ? t1 t2 C C' c c' d d' RA' ? Hk Hk2 Hkn HTk HTk' HC HCC Hcc Hdd
                        HRA' Hra' Hrb' Hps' Hpt' HkR
                    | ? ? ? ? ? t1 t2 ? Hk Hk2 Hkn HTk HTk' HkR
                    | ? ? ? ? ? t1 t2 t3 t4 C C' D D' RA' RB' ? Hk Hk3 Hk4 Hkw1 Hkw2 HTk HTk' HC HCC HD HDD
                        HRA' HRB' Hpa' Hta' Hpb' Htb' HkR
                    | ? ? ? ? ? k1 k2 k3 k4 C D C' D' domR' codR' ?
                        [Hk Hk3 Hk4 Hkw1 Hkw2 HTk HTk' HC HC' HD HD' HCC HDD] domAd' codAd' HkR
                    | ? ? ? ? ? k1 k2 C C' M M' domR' ? Hk Hk2 Hkw HTk HTk' HC HC' HkN HkN' HCC HkNN domAd' arAd' HkR
                    | ? ? ? ? ? k1 k2 C C' RQ' ? Hk Hk2 Hkw HTk HTk' HC HCC HRQ' Hqs' Hqt' HkR
                    | ? ? ? ? ? k1 ki1 k2 ki2 jX jX' jA jA' jN jN' jO jO' jC jC' q q' idxR' domR' ? Hk Hk2 Hki2 Hkw Hkwi
                        HTk HTk' HjX HjX' HjA HjA' HjN HjN' HjO HjO' HjC HjC' Hq Hq' HjXX HjAA HjNN HjOO HjCC Hqq
                        idxAd' Hisym' Histr' domAd' arAd' otAd' chAd' ixAd' HkR
                    | ? ? ? ? ? nl1 nl2 nli nr1 nr2 nri nX nX' nA nA' nB nB' nC nC' nm nm' nidxR nshR nposR ?
                        Hk Hnr1 Hnr2 Hnri Hnw1 Hnw2 Hnwi HTk HTk' HnX HnX' HnA HnA' HnB HnB' HnC HnC' Hnm Hnm'
                        HnXX HnAA HnBB HnCC Hnmm nidxAd nshAd nposAd nchAd ngB ngC ngCa nimon nshmon nposmon
                        nixAd HkR
                    | ? ? ? ? ? j1 jp1 ji1 j2 jp2 ji2 kX kX' kA kA' kN kN' kD kD' kO kO' kC kC' q q' kidxR kdomR kpdR ?
                        Hk Hj2 Hjp2 Hji2 Hjw Hjwp Hjwi HTk HTk' HkX HkX' HkA HkA' HkN HkN' HkD HkD' HkO HkO' HkC HkC'
                        Hq Hq' HkXX HkAA HkNN HkDD HkOO HkCC Hqq kidxAd Hkisym Hkistr kdomAd karAd kotAd kpdAd kpdE kpdMon
                        kchAd kgC kixAd HkR];
    subst; try (agree; try ne_absurd).
  (* contextual types, and mismatches with them *)
  all: try solve [eapply ModRel_irrel; eassumption].
  all: try solve [open_mod; agree; try ne_absurd].
  all: eapply releq_trans; [exact HR | eapply releq_trans; [| apply releq_sym, HkR]].
  (* same shape *)
  - apply releq_refl.
  - apply releq_refl.
  - assert (HVV : [ G ; Γ ⊢g V' ≅ W' @ l ]).
    { eapply eqty_trans; [apply eqty_sym|]; apply geq_ty_sound, gne_ty_geq; eassumption. }
    intros t t'; split; apply NeRel_conv; [exact HVV | now apply eqty_sym].
  - poly_irrel tyPi @geq_ty_pi @PiRel_dir.
  - (* CΠ: the right types are convertible, the instances irrelevant *)
    match goal with
    | |- releq (CPiRel _ _ ?a1 ?a2 ?A1 ?A1' ?iR) (CPiRel _ _ _ ?b2 _ ?B1' ?iR') =>
        assert (HP : [ G ; Γ ⊢g tyCPi a2 A1' ≅ tyCPi b2 B1' @ a1 ])
          by (eapply eqty_trans; [apply eqty_sym, geq_ty_sound; eassumption | apply geq_ty_sound; eassumption]);
        assert (Hinst : forall ρ Δ Δ' h, releq (iR ρ Δ Δ' h) (iR' ρ Δ Δ' h))
          by (intros; eapply IHinst; eauto)
    end.
    intros t t'; split.
    + eapply CPiRel_dir; eassumption.
    + eapply CPiRel_dir; [now apply eqty_sym | intros; apply releq_sym, Hinst].
  - (* TΠ *)
    match goal with
    | |- releq (TPiRel _ _ _ ?D1' ?a1 ?a2 ?a3 ?a4 _ ?A1' ?iR) (TPiRel _ _ _ ?E1' _ _ ?b3 ?b4 _ ?B1' ?iR') =>
        assert (HP : [ G ; Γ ⊢g tyTPi D1' a3 a4 A1' ≅ tyTPi E1' b3 b4 B1' @ a2 ])
          by (eapply eqty_trans; [apply eqty_sym, geq_ty_sound; eassumption | apply geq_ty_sound; eassumption]);
        assert (Hinst : forall ρ A A' h, releq (iR ρ A A' h) (iR' ρ A A' h))
          by (intros; eapply IHinst; eauto)
    end.
    intros t t'; split.
    + eapply TPiRel_dir; eassumption.
    + eapply TPiRel_dir; [now apply eqty_sym | intros; apply releq_sym, Hinst].
  - poly_irrel tySig @geq_ty_sig @SigRel_dir.
  - apply releq_refl.
  - apply releq_refl.
  - apply releq_refl.
  - (* Id: the carriers' relations agree *)
    apply IdRel_releq. eapply IHRA; eassumption.
  - apply releq_refl.
  - (* +: the summands' relations agree *)
    apply SumRel_releq; [eapply IHRA | eapply IHRB]; eassumption.
  - (* W: the shapes' and positions' relations agree *)
    apply WRel_releq.
    + intros; match goal with IH : forall (ρ : kwk _ _) T'' R', _ -> releq (domR _) _ |- _ =>
                                eapply IH end; eauto.
    + intros; match goal with IH : forall (ρ : kwk _ _) a a' ha T'' R', _ -> releq (codR _ _ _ _) _ |- _ =>
                                eapply IH end; eauto.
  - (* Wf: the shapes' relations agree *)
    apply WfRel_releq.
    intros; match goal with IH : forall (ρ : kwk _ _) T'' R', _ -> releq (domR _) _ |- _ =>
                              eapply IH end; eauto.
  - (* ∥·∥: the carriers' relations agree *)
    apply SqRel_releq. eapply IHRQ; eassumption.
  - (* IWf: the index's and the shapes' relations agree *)
    apply IWfRel_releq.
    + intros; match goal with IH : forall (ρ : kwk _ _) T'' R', _ -> releq (idxR _) _ |- _ =>
                                eapply IH end; eauto.
    + intros; match goal with IH : forall (ρ : kwk _ _) T'' R', _ -> releq (domR _) _ |- _ =>
                                eapply IH end; eauto.
  - (* M: the two sides, and the index's, shapes' and positions' relations agree *)
    assert (Rs : forall ρ x x' x'', midxR ρ x x' -> nidxR ρ x x'' -> releq (mshR ρ x x') (nshR ρ x x'')).
    { intros ρ x x' x'' h h'. eapply IHmsh; [exact h | apply nshAd, h']. }
    assert (Rp : forall ρ x x' x'' a a', midxR ρ x x' -> nidxR ρ x x'' -> mshR ρ x x' a a' ->
                   releq (mposR ρ x x' a a') (nposR ρ x x'' a a')).
    { intros ρ x x' x'' a a' h h' ha. eapply IHmpos; [exact h | exact ha |].
      apply nposAd; [exact h' | apply (Rs ρ x x' x'' h h'), ha]. }
    apply (MR_irrel (idxR := midxR) (idxR' := nidxR)).
    refine (conj _ (conj _ (conj Rs (conj Rp (conj _ (conj _ (conj _ (conj mixAd nixAd)))))))).
    + eapply MSide_of_LR; eassumption.
    + eapply MSide_of_LR; eassumption.
    + exact (wf_tm_nf Hmm).
    + exact (wf_tm_nf Hmm').
    + exact (wf_tm_nf Hnm').
  - (* IWi: the index's and the shapes' relations agree, and the domains'
       relations where the relation reads them: against a right position
       related along either right length ([PosRel_retarget]) *)
    assert (Hd : forall ρ, releq (vdomR ρ) (kdomR ρ))
      by (intros; match goal with IH : forall (ρ : kwk _ _) T'' R', _ -> releq (vdomR _) _ |- _ =>
                                    eapply IH end; eauto).
    apply IWiRel_releq.
    + intros; match goal with IH : forall (ρ : kwk _ _) T'' R', _ -> releq (vidxR _) _ |- _ =>
                                eapply IH end; eauto.
    + exact Hd.
    + intros ρ a a' p y y' ha (p' & Hy).
      pose proof (vpdE _ _ _ _ _ _ _ Hy) as Hp.
      destruct (PosRel_retarget Hp _ (karAd ρ a a' (proj1 (Hd ρ a a') ha))) as (p2 & Hp2).
      exists p2. eapply IHvpd; [exact ha | exact Hp | exact (kpdAd ρ a a' (proj1 (Hd ρ a a') ha) p p2 Hp2) | exact Hy].
    + intros ρ a a' p y y' ha (p' & Hy).
      pose proof (kpdE _ _ _ _ _ _ _ Hy) as Hp.
      destruct (PosRel_retarget Hp _ (varAd ρ a a' ha)) as (p2 & Hp2).
      exists p2. apply (proj2 (IHvpd ρ a a' ha p p2 Hp2 _ _ (kpdAd ρ a a' (proj1 (Hd ρ a a') ha) p p' Hp) y y')), Hy.
Qed.

(** ** Inversion by the left type's normal form *)

Section Inversion.
Context {n : nat} {rec : lvl -> RedRel} {G : gctx} {Γ : ctx} {T T' : ty} {l : lvl}
  {R : tm -> tm -> Prop} (H : LR n rec G Γ T T' l R).

Lemma LR_inv_nat {l'} : [ G ; Γ ⊢g T ⤳* tyNat @ l' ] ->
  lequiv (gL G) l lzero /\ [ G ; Γ ⊢g T' ⤳* tyNat @ l ] /\ releq R (NatRel G Γ).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l l1 l2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l l1 l2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR
                | G Γ T T' l vl1 vlp1 vli1 vl2 vlp2 vli2 vX vX' vA vA' vN vN' vD vD' vO vO' vC vC' vm vm' vidxR vdomR vpdR R
                    Hl Hvl2 Hvlp2 Hvli2 Hvw Hvwp Hvwi HT HT' HvX HvX' HvA HvA' HvN HvN' HvD HvD' HvO HvO' HvC HvC' Hvm Hvm'
                    HvXX HvAA HvNN HvDD HvOO HvCC Hvmm vidxAd Hvisym Hvistr vdomAd varAd votAd vpdAd vpdE vpdMon vchAd vgC vixAd HR];
    intros HN; try open_mod; agree; try ne_absurd; auto.
Qed.

Lemma LR_inv_U {l1 l'} : [ G ; Γ ⊢g T ⤳* tyU l1 @ l' ] ->
  exists l2, lequiv (gL G) l (lsuc l1) /\ lequiv (gL G) l2 l1 /\ lmeasure l1 < n /\
    [ G ; Γ ⊢g T' ⤳* tyU l2 @ l ] /\ releq R (URel rec G Γ l1).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR
                | G Γ T T' l vl1 vlp1 vli1 vl2 vlp2 vli2 vX vX' vA vA' vN vN' vD vD' vO vO' vC vC' vm vm' vidxR vdomR vpdR R
                    Hl Hvl2 Hvlp2 Hvli2 Hvw Hvwp Hvwi HT HT' HvX HvX' HvA HvA' HvN HvN' HvD HvD' HvO HvO' HvC HvC' Hvm Hvm'
                    HvXX HvAA HvNN HvDD HvOO HvCC Hvmm vidxAd Hvisym Hvistr vdomAd varAd votAd vpdAd vpdE vpdMon vchAd vgC vixAd HR];
    intros HN; try open_mod; agree; try ne_absurd; eauto 7.
Qed.

Lemma LR_inv_unit {l1 l'} : [ G ; Γ ⊢g T ⤳* tyUnit l1 @ l' ] ->
  exists l2, lequiv (gL G) l l1 /\ lequiv (gL G) l2 l1 /\ lwf (gL G) l1 /\
    [ G ; Γ ⊢g T' ⤳* tyUnit l2 @ l ] /\ releq R (UnitRel G Γ l1).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR
                | G Γ T T' l vl1 vlp1 vli1 vl2 vlp2 vli2 vX vX' vA vA' vN vN' vD vD' vO vO' vC vC' vm vm' vidxR vdomR vpdR R
                    Hl Hvl2 Hvlp2 Hvli2 Hvw Hvwp Hvwi HT HT' HvX HvX' HvA HvA' HvN HvN' HvD HvD' HvO HvO' HvC HvC' Hvm Hvm'
                    HvXX HvAA HvNN HvDD HvOO HvCC Hvmm vidxAd Hvisym Hvistr vdomAd varAd votAd vpdAd vpdE vpdMon vchAd vgC vixAd HR];
    intros HN; try open_mod; agree; try ne_absurd; eauto 7.
Qed.

Lemma LR_inv_seq {l1 X x y l'} : [ G ; Γ ⊢g T ⤳* tySEq l1 X x y @ l' ] ->
  exists l2 X' x' y', lequiv (gL G) l l1 /\ lequiv (gL G) l2 l1 /\ lwf (gL G) l1 /\
    [ G ; Γ ⊢g T' ⤳* tySEq l2 X' x' y' @ l ] /\ [ G ; Γ ⊢g X @ l1 ] /\ [ G ; Γ ⊢ X ≈ X' @ l1 ] /\
    [ G ; Γ ⊢ x ≈ x' : X @ l1 ] /\ [ G ; Γ ⊢ y ≈ y' : X @ l1 ] /\
    releq R (SEqRel G Γ (tySEq l1 X x y) l1).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR
                | G Γ T T' l vl1 vlp1 vli1 vl2 vlp2 vli2 vX vX' vA vA' vN vN' vD vD' vO vO' vC vC' vm vm' vidxR vdomR vpdR R
                    Hl Hvl2 Hvlp2 Hvli2 Hvw Hvwp Hvwi HT HT' HvX HvX' HvA HvA' HvN HvN' HvD HvD' HvO HvO' HvC HvC' Hvm Hvm'
                    HvXX HvAA HvNN HvDD HvOO HvCC Hvmm vidxAd Hvisym Hvistr vdomAd varAd votAd vpdAd vpdE vpdMon vchAd vgC vixAd HR];
    intros HN; try open_mod; agree; try ne_absurd; eauto 15.
Qed.

Lemma LR_inv_id {l1 X x y l'} : [ G ; Γ ⊢g T ⤳* tyId l1 X x y @ l' ] ->
  exists l2 X' x' y' RA, lequiv (gL G) l l1 /\ lequiv (gL G) l2 l1 /\ lwf (gL G) l1 /\
    [ G ; Γ ⊢g T' ⤳* tyId l2 X' x' y' @ l ] /\ [ G ; Γ ⊢g X @ l1 ] /\ [ G ; Γ ⊢ X ≈ X' @ l1 ] /\
    [ G ; Γ ⊢ x ≈ x' : X @ l1 ] /\ [ G ; Γ ⊢ y ≈ y' : X @ l1 ] /\
    LR n rec G Γ X X' l1 RA /\ RA x x' /\ RA y y' /\
    (forall u v, RA u v -> RA v u) /\ (forall u v w, RA u v -> RA v w -> RA u w) /\
    releq R (IdRel G Γ l1 X x y RA).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR
                | G Γ T T' l vl1 vlp1 vli1 vl2 vlp2 vli2 vX vX' vA vA' vN vN' vD vD' vO vO' vC vC' vm vm' vidxR vdomR vpdR R
                    Hl Hvl2 Hvlp2 Hvli2 Hvw Hvwp Hvwi HT HT' HvX HvX' HvA HvA' HvN HvN' HvD HvD' HvO HvO' HvC HvC' Hvm Hvm'
                    HvXX HvAA HvNN HvDD HvOO HvCC Hvmm vidxAd Hvisym Hvistr vdomAd varAd votAd vpdAd vpdE vpdMon vchAd vgC vixAd HR];
    intros HN; try open_mod; agree; try ne_absurd; eauto 20.
Qed.

(** Binary sums (M12b). *)
Lemma LR_inv_sum {l1 l2 X Y l'} : [ G ; Γ ⊢g T ⤳* tySum l1 l2 X Y @ l' ] ->
  exists l3 l4 X' Y' RA RB, lequiv (gL G) l (lmax l1 l2) /\ lequiv (gL G) l3 l1 /\ lequiv (gL G) l4 l2 /\
    lwf (gL G) l1 /\ lwf (gL G) l2 /\
    [ G ; Γ ⊢g T' ⤳* tySum l3 l4 X' Y' @ l ] /\ [ G ; Γ ⊢g X @ l1 ] /\ [ G ; Γ ⊢ X ≈ X' @ l1 ] /\
    [ G ; Γ ⊢g Y @ l2 ] /\ [ G ; Γ ⊢ Y ≈ Y' @ l2 ] /\
    LR n rec G Γ X X' l1 RA /\ LR n rec G Γ Y Y' l2 RB /\
    (forall u v, RA u v -> RA v u) /\ (forall u v w, RA u v -> RA v w -> RA u w) /\
    (forall u v, RB u v -> RB v u) /\ (forall u v w, RB u v -> RB v w -> RB u w) /\
    releq R (SumRel G Γ l1 l2 X Y RA RB).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR
                | G Γ T T' l vl1 vlp1 vli1 vl2 vlp2 vli2 vX vX' vA vA' vN vN' vD vD' vO vO' vC vC' vm vm' vidxR vdomR vpdR R
                    Hl Hvl2 Hvlp2 Hvli2 Hvw Hvwp Hvwi HT HT' HvX HvX' HvA HvA' HvN HvN' HvD HvD' HvO HvO' HvC HvC' Hvm Hvm'
                    HvXX HvAA HvNN HvDD HvOO HvCC Hvmm vidxAd Hvisym Hvistr vdomAd varAd votAd vpdAd vpdE vpdMon vchAd vgC vixAd HR];
    intros HN; try open_mod; agree; try ne_absurd; do 6 eexists; eauto 25.
Qed.

Lemma LR_inv_sempty {l1 l'} : [ G ; Γ ⊢g T ⤳* tySEmpty l1 @ l' ] ->
  exists l2, lequiv (gL G) l l1 /\ lequiv (gL G) l2 l1 /\ lwf (gL G) l1 /\
    [ G ; Γ ⊢g T' ⤳* tySEmpty l2 @ l ] /\ releq R (SEmptyRel G Γ l1).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR
                | G Γ T T' l vl1 vlp1 vli1 vl2 vlp2 vli2 vX vX' vA vA' vN vN' vD vD' vO vO' vC vC' vm vm' vidxR vdomR vpdR R
                    Hl Hvl2 Hvlp2 Hvli2 Hvw Hvwp Hvwi HT HT' HvX HvX' HvA HvA' HvN HvN' HvD HvD' HvO HvO' HvC HvC' Hvm Hvm'
                    HvXX HvAA HvNN HvDD HvOO HvCC Hvmm vidxAd Hvisym Hvistr vdomAd varAd votAd vpdAd vpdE vpdMon vchAd vgC vixAd HR];
    intros HN; try open_mod; agree; try ne_absurd; eauto 7.
Qed.

(** The empty type (M12a). *)
Lemma LR_inv_empty {l1 l'} : [ G ; Γ ⊢g T ⤳* tyEmpty l1 @ l' ] ->
  exists l2, lequiv (gL G) l l1 /\ lequiv (gL G) l2 l1 /\ lwf (gL G) l1 /\
    [ G ; Γ ⊢g T' ⤳* tyEmpty l2 @ l ] /\ releq R (EmptyRel G Γ l1).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR
                | G Γ T T' l vl1 vlp1 vli1 vl2 vlp2 vli2 vX vX' vA vA' vN vN' vD vD' vO vO' vC vC' vm vm' vidxR vdomR vpdR R
                    Hl Hvl2 Hvlp2 Hvli2 Hvw Hvwp Hvwi HT HT' HvX HvX' HvA HvA' HvN HvN' HvD HvD' HvO HvO' HvC HvC' Hvm Hvm'
                    HvXX HvAA HvNN HvDD HvOO HvCC Hvmm vidxAd Hvisym Hvistr vdomAd varAd votAd vpdAd vpdE vpdMon vchAd vgC vixAd HR];
    intros HN; try open_mod; agree; try ne_absurd; eauto 7.
Qed.


Lemma LR_inv_ne {V l'} : [ G ; Γ ⊢g T ⤳* V @ l' ] -> whne_ty V ->
  exists V', [ G ; Γ ⊢g T' ⤳* V' @ l ] /\ [ G ; Γ ⊢ V ~ V' @ l ] /\ releq R (NeRel G Γ V V' l).
Proof using EL H.
  intros HN HV0; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l W W' R HT HT' HW HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR
                | G Γ T T' l vl1 vlp1 vli1 vl2 vlp2 vli2 vX vX' vA vA' vN vN' vD vD' vO vO' vC vC' vm vm' vidxR vdomR vpdR R
                    Hl Hvl2 Hvlp2 Hvli2 Hvw Hvwp Hvwi HT HT' HvX HvX' HvA HvA' HvN HvN' HvD HvD' HvO HvO' HvC HvC' Hvm Hvm'
                    HvXX HvAA HvNN HvDD HvOO HvCC Hvmm vidxAd Hvisym Hvistr vdomAd varAd votAd vpdAd vpdE vpdMon vchAd vgC vixAd HR];
    intros HN; try open_mod; agree; try solve [inversion HV0]; eauto.
Qed.

Lemma LR_inv_pi {m1 m2 C D l'} : [ G ; Γ ⊢g T ⤳* tyPi m1 m2 C D @ l' ] ->
  exists m3 m4 C' D' (domR : DomRel G Γ) (codR : CodRel G Γ domR),
    PolyFacts G Γ tyPi T T' l m1 m2 m3 m4 C D C' D' /\
    (forall ρ : kwk G Γ, LR n rec (kw_G ρ) (kw_Δ ρ) (kty ρ C) (kty ρ C') m1 (domR ρ)) /\
    (forall (ρ : kwk G Γ) a a' (ha : domR ρ a a'),
        LR n rec (kw_G ρ) (kw_Δ ρ) (ktyl ρ D)[lsingle a] (ktyl ρ D')[lsingle a'] m2
           (codR ρ a a' ha)) /\
    releq R (PiRel G Γ m1 m2 m3 m4 C D C' D' domR codR).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR
                | G Γ T T' l vl1 vlp1 vli1 vl2 vlp2 vli2 vX vX' vA vA' vN vN' vD vD' vO vO' vC vC' vm vm' vidxR vdomR vpdR R
                    Hl Hvl2 Hvlp2 Hvli2 Hvw Hvwp Hvwi HT HT' HvX HvX' HvA HvA' HvN HvN' HvD HvD' HvO HvO' HvC HvC' Hvm Hvm'
                    HvXX HvAA HvNN HvDD HvOO HvCC Hvmm vidxAd Hvisym Hvistr vdomAd varAd votAd vpdAd vpdE vpdMon vchAd vgC vixAd HR];
    intros HN; try open_mod; agree; try ne_absurd.
  do 6 eexists; refine (conj _ _); [split|]; eauto 20.
Qed.

Lemma LR_inv_sig {m1 m2 C D l'} : [ G ; Γ ⊢g T ⤳* tySig m1 m2 C D @ l' ] ->
  exists m3 m4 C' D' (domR : DomRel G Γ) (codR : CodRel G Γ domR),
    PolyFacts G Γ tySig T T' l m1 m2 m3 m4 C D C' D' /\
    (forall ρ : kwk G Γ, LR n rec (kw_G ρ) (kw_Δ ρ) (kty ρ C) (kty ρ C') m1 (domR ρ)) /\
    (forall (ρ : kwk G Γ) a a' (ha : domR ρ a a'),
        LR n rec (kw_G ρ) (kw_Δ ρ) (ktyl ρ D)[lsingle a] (ktyl ρ D')[lsingle a'] m2
           (codR ρ a a' ha)) /\
    releq R (SigRel G Γ m1 m2 m3 m4 C D C' D' domR codR).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR
                | G Γ T T' l vl1 vlp1 vli1 vl2 vlp2 vli2 vX vX' vA vA' vN vN' vD vD' vO vO' vC vC' vm vm' vidxR vdomR vpdR R
                    Hl Hvl2 Hvlp2 Hvli2 Hvw Hvwp Hvwi HT HT' HvX HvX' HvA HvA' HvN HvN' HvD HvD' HvO HvO' HvC HvC' Hvm Hvm'
                    HvXX HvAA HvNN HvDD HvOO HvCC Hvmm vidxAd Hvisym Hvistr vdomAd varAd votAd vpdAd vpdE vpdMon vchAd vgC vixAd HR];
    intros HN; try open_mod; agree; try ne_absurd.
  do 6 eexists; refine (conj _ _); [split|]; eauto 20.
Qed.

Lemma LR_inv_W {m1 m2 C D l'} : [ G ; Γ ⊢g T ⤳* tyW m1 m2 C D @ l' ] ->
  exists m3 m4 C' D' (domR : DomRel G Γ) (codR : CodRel G Γ domR),
    PolyFacts G Γ tyW T T' l m1 m2 m3 m4 C D C' D' /\
    (forall ρ : kwk G Γ, LR n rec (kw_G ρ) (kw_Δ ρ) (kty ρ C) (kty ρ C') m1 (domR ρ)) /\
    (forall (ρ : kwk G Γ) a a' (ha : domR ρ a a'),
        LR n rec (kw_G ρ) (kw_Δ ρ) (ktyl ρ D)[lsingle a] (ktyl ρ D')[lsingle a'] m2
           (codR ρ a a' ha)) /\
    releq R (WRel G Γ m1 m2 C D domR codR).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR
                | G Γ T T' l vl1 vlp1 vli1 vl2 vlp2 vli2 vX vX' vA vA' vN vN' vD vD' vO vO' vC vC' vm vm' vidxR vdomR vpdR R
                    Hl Hvl2 Hvlp2 Hvli2 Hvw Hvwp Hvwi HT HT' HvX HvX' HvA HvA' HvN HvN' HvD HvD' HvO HvO' HvC HvC' Hvm Hvm'
                    HvXX HvAA HvNN HvDD HvOO HvCC Hvmm vidxAd Hvisym Hvistr vdomAd varAd votAd vpdAd vpdE vpdMon vchAd vgC vixAd HR];
    intros HN; try open_mod; agree; try ne_absurd.
  do 6 eexists; refine (conj _ _); [split|]; eauto 20.
Qed.

Lemma LR_inv_wf {m1 C M l'} : [ G ; Γ ⊢g T ⤳* tyWf m1 C M @ l' ] ->
  exists m2 C' M' (domR : DomRel G Γ),
    lequiv (gL G) l m1 /\ lequiv (gL G) m2 m1 /\ lwf (gL G) m1 /\
    [ G ; Γ ⊢g T ⤳* tyWf m1 C M @ l ] /\ [ G ; Γ ⊢g T' ⤳* tyWf m2 C' M' @ l ] /\
    [ G ; Γ ⊢g C @ m1 ] /\ [ G ; Γ ⊢g C' @ m1 ] /\
    [ G ; Γ ,, C @ m1 ⊢g M : tyNat @ lzero ] /\ [ G ; Γ ,, C' @ m1 ⊢g M' : tyNat @ lzero ] /\
    [ G ; Γ ⊢ C ≈ C' @ m1 ] /\ [ G ; Γ ,, C @ m1 ⊢ M ≈ M' : tyNat @ lzero ] /\
    (forall ρ : kwk G Γ, LR n rec (kw_G ρ) (kw_Δ ρ) (kty ρ C) (kty ρ C') m1 (domR ρ)) /\
    (forall (ρ : kwk G Γ) a a', domR ρ a a' ->
        NatRel (kw_G ρ) (kw_Δ ρ) (ktml ρ M)[lsingle a] (ktml ρ M')[lsingle a']) /\
    releq R (WfRel G Γ m1 C M domR).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR
                | G Γ T T' l vl1 vlp1 vli1 vl2 vlp2 vli2 vX vX' vA vA' vN vN' vD vD' vO vO' vC vC' vm vm' vidxR vdomR vpdR R
                    Hl Hvl2 Hvlp2 Hvli2 Hvw Hvwp Hvwi HT HT' HvX HvX' HvA HvA' HvN HvN' HvD HvD' HvO HvO' HvC HvC' Hvm Hvm'
                    HvXX HvAA HvNN HvDD HvOO HvCC Hvmm vidxAd Hvisym Hvistr vdomAd varAd votAd vpdAd vpdE vpdMon vchAd vgC vixAd HR];
    intros HN; try open_mod; agree; try ne_absurd.
  do 4 eexists; eauto 20.
Qed.

(** Indexed W-types (M17b). *)
Lemma LR_inv_iwf {iL iLi iX iA iN iO iC im l'} : [ G ; Γ ⊢g T ⤳* tyIWf iL iLi iX iA iN iO iC im @ l' ] ->
  exists k2 ki2 X' A' N' Ot' C' m' (idxR domR : DomRel G Γ),
    lequiv (gL G) l (lmax iL iLi) /\ lequiv (gL G) k2 iL /\ lequiv (gL G) ki2 iLi /\
    lwf (gL G) iL /\ lwf (gL G) iLi /\
    [ G ; Γ ⊢g T ⤳* tyIWf iL iLi iX iA iN iO iC im @ l ] /\
    [ G ; Γ ⊢g T' ⤳* tyIWf k2 ki2 X' A' N' Ot' C' m' @ l ] /\
    [ G ; Γ ⊢g iX @ iLi ] /\ [ G ; Γ ⊢g X' @ iLi ] /\ [ G ; Γ ⊢g iA @ iL ] /\ [ G ; Γ ⊢g A' @ iL ] /\
    [ G ; Γ ,, iA @ iL ⊢g iN : tyNat @ lzero ] /\ [ G ; Γ ,, A' @ iL ⊢g N' : tyNat @ lzero ] /\
    [ G ; Γ ,, iA @ iL ⊢g iO : iX⟨↑⟩ @ iLi ] /\ [ G ; Γ ,, A' @ iL ⊢g Ot' : X'⟨↑⟩ @ iLi ] /\
    [ G ; Γ ,, iA @ iL ,, tyFin iN @ lzero ⊢g iC : iX⟨↑⟩⟨↑⟩ @ iLi ] /\
    [ G ; Γ ,, A' @ iL ,, tyFin N' @ lzero ⊢g C' : X'⟨↑⟩⟨↑⟩ @ iLi ] /\
    [ G ; Γ ⊢g im : iX @ iLi ] /\ [ G ; Γ ⊢g m' : X' @ iLi ] /\
    [ G ; Γ ⊢ iX ≈ X' @ iLi ] /\ [ G ; Γ ⊢ iA ≈ A' @ iL ] /\ [ G ; Γ ,, iA @ iL ⊢ iN ≈ N' : tyNat @ lzero ] /\
    [ G ; Γ ,, iA @ iL ⊢ iO ≈ Ot' : iX⟨↑⟩ @ iLi ] /\
    [ G ; Γ ,, iA @ iL ,, tyFin iN @ lzero ⊢ iC ≈ C' : iX⟨↑⟩⟨↑⟩ @ iLi ] /\
    [ G ; Γ ⊢ im ≈ m' : iX @ iLi ] /\
    (forall ρ : kwk G Γ, LR n rec (kw_G ρ) (kw_Δ ρ) (kty ρ iX) (kty ρ X') iLi (idxR ρ)) /\
    (forall (ρ : kwk G Γ) x y, idxR ρ x y -> idxR ρ y x) /\
    (forall (ρ : kwk G Γ) x y z, idxR ρ x y -> idxR ρ y z -> idxR ρ x z) /\
    (forall ρ : kwk G Γ, LR n rec (kw_G ρ) (kw_Δ ρ) (kty ρ iA) (kty ρ A') iL (domR ρ)) /\
    (forall (ρ : kwk G Γ) a a', domR ρ a a' ->
        NatRel (kw_G ρ) (kw_Δ ρ) (ktml ρ iN)[lsingle a] (ktml ρ N')[lsingle a']) /\
    (forall (ρ : kwk G Γ) a a', domR ρ a a' ->
        idxR ρ (ktml ρ iO)[lsingle a] (ktml ρ Ot')[lsingle a']) /\
    (forall (ρ : kwk G Γ) a a', domR ρ a a' -> forall p p',
        PosRel (kw_G ρ) (kw_Δ ρ) (ktml ρ iN)[lsingle a] (ktml ρ N')[lsingle a'] p p' ->
        idxR ρ (ktmll ρ iC)[lsingle2 a p] (ktmll ρ C')[lsingle2 a' p']) /\
    (forall ρ : kwk G Γ, idxR ρ (ktm ρ im) (ktm ρ m')) /\
    releq R (IWfRel G Γ iL iLi iX iA iN iO iC idxR domR im).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR
                | G Γ T T' l vl1 vlp1 vli1 vl2 vlp2 vli2 vX vX' vA vA' vN vN' vD vD' vO vO' vC vC' vm vm' vidxR vdomR vpdR R
                    Hl Hvl2 Hvlp2 Hvli2 Hvw Hvwp Hvwi HT HT' HvX HvX' HvA HvA' HvN HvN' HvD HvD' HvO HvO' HvC HvC' Hvm Hvm'
                    HvXX HvAA HvNN HvDD HvOO HvCC Hvmm vidxAd Hvisym Hvistr vdomAd varAd votAd vpdAd vpdE vpdMon vchAd vgC vixAd HR];
    intros HN; try open_mod; agree; try ne_absurd.
  do 10 eexists; eauto 40.
Qed.

Lemma LR_inv_iwi {iL iLp iLi iX iA iN iD iO iC im l'} : [ G ; Γ ⊢g T ⤳* tyIWi iL iLp iLi iX iA iN iD iO iC im @ l' ] ->
  exists k2 kp2 ki2 X' A' N' D' Ot' C' m' (idxR domR : DomRel G Γ) (pdR : IPosDomRel G Γ),
    lequiv (gL G) l (iwiL iL iLp iLi) /\ lequiv (gL G) k2 iL /\ lequiv (gL G) kp2 iLp /\ lequiv (gL G) ki2 iLi /\
    lwf (gL G) iL /\ lwf (gL G) iLp /\ lwf (gL G) iLi /\
    [ G ; Γ ⊢g T ⤳* tyIWi iL iLp iLi iX iA iN iD iO iC im @ l ] /\
    [ G ; Γ ⊢g T' ⤳* tyIWi k2 kp2 ki2 X' A' N' D' Ot' C' m' @ l ] /\
    [ G ; Γ ⊢g iX @ iLi ] /\ [ G ; Γ ⊢g X' @ iLi ] /\ [ G ; Γ ⊢g iA @ iL ] /\ [ G ; Γ ⊢g A' @ iL ] /\
    [ G ; Γ ,, iA @ iL ⊢g iN : tyNat @ lzero ] /\ [ G ; Γ ,, A' @ iL ⊢g N' : tyNat @ lzero ] /\
    [ G ; Γ ,, iA @ iL ,, tyFin iN @ lzero ⊢g iD @ iLp ] /\ [ G ; Γ ,, A' @ iL ,, tyFin N' @ lzero ⊢g D' @ iLp ] /\
    [ G ; Γ ,, iA @ iL ⊢g iO : iX⟨↑⟩ @ iLi ] /\ [ G ; Γ ,, A' @ iL ⊢g Ot' : X'⟨↑⟩ @ iLi ] /\
    [ G ; Γ ,, iA @ iL ,, tyFin iN @ lzero ,, iD @ iLp ⊢g iC : iX⟨↑⟩⟨↑⟩⟨↑⟩ @ iLi ] /\
    [ G ; Γ ,, A' @ iL ,, tyFin N' @ lzero ,, D' @ iLp ⊢g C' : X'⟨↑⟩⟨↑⟩⟨↑⟩ @ iLi ] /\
    [ G ; Γ ⊢g im : iX @ iLi ] /\ [ G ; Γ ⊢g m' : X' @ iLi ] /\
    [ G ; Γ ⊢ iX ≈ X' @ iLi ] /\ [ G ; Γ ⊢ iA ≈ A' @ iL ] /\ [ G ; Γ ,, iA @ iL ⊢ iN ≈ N' : tyNat @ lzero ] /\
    [ G ; Γ ,, iA @ iL ,, tyFin iN @ lzero ⊢ iD ≈ D' @ iLp ] /\
    [ G ; Γ ,, iA @ iL ⊢ iO ≈ Ot' : iX⟨↑⟩ @ iLi ] /\
    [ G ; Γ ,, iA @ iL ,, tyFin iN @ lzero ,, iD @ iLp ⊢ iC ≈ C' : iX⟨↑⟩⟨↑⟩⟨↑⟩ @ iLi ] /\
    [ G ; Γ ⊢ im ≈ m' : iX @ iLi ] /\
    (forall ρ : kwk G Γ, LR n rec (kw_G ρ) (kw_Δ ρ) (kty ρ iX) (kty ρ X') iLi (idxR ρ)) /\
    (forall (ρ : kwk G Γ) x y, idxR ρ x y -> idxR ρ y x) /\
    (forall (ρ : kwk G Γ) x y z, idxR ρ x y -> idxR ρ y z -> idxR ρ x z) /\
    (forall ρ : kwk G Γ, LR n rec (kw_G ρ) (kw_Δ ρ) (kty ρ iA) (kty ρ A') iL (domR ρ)) /\
    (forall (ρ : kwk G Γ) a a', domR ρ a a' ->
        NatRel (kw_G ρ) (kw_Δ ρ) (ktml ρ iN)[lsingle a] (ktml ρ N')[lsingle a']) /\
    (forall (ρ : kwk G Γ) a a', domR ρ a a' ->
        idxR ρ (ktml ρ iO)[lsingle a] (ktml ρ Ot')[lsingle a']) /\
    (forall (ρ : kwk G Γ) a a', domR ρ a a' -> forall p p',
        PosRel (kw_G ρ) (kw_Δ ρ) (ktml ρ iN)[lsingle a] (ktml ρ N')[lsingle a'] p p' ->
        LR n rec (kw_G ρ) (kw_Δ ρ) (ktyll ρ iD)[lsingle2 a p] (ktyll ρ D')[lsingle2 a' p'] iLp (pdR ρ a a' p p')) /\
    (forall (ρ : kwk G Γ) a a' p p' y y', pdR ρ a a' p p' y y' ->
        PosRel (kw_G ρ) (kw_Δ ρ) (ktml ρ iN)[lsingle a] (ktml ρ N')[lsingle a'] p p') /\
    (forall (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) a a' p p' y y', pdR ρ a a' p p' y y' ->
        pdR (kw_comp ρ ρ') (ktm ρ' a) (ktm ρ' a') (ktm ρ' p) (ktm ρ' p') (ktm ρ' y) (ktm ρ' y')) /\
    (forall (ρ : kwk G Γ) a a', domR ρ a a' -> forall p p' y y', pdR ρ a a' p p' y y' ->
        idxR ρ (ktmlll ρ iC)[lsingle3 a p y] (ktmlll ρ C')[lsingle3 a' p' y']) /\
    (forall (ρ : kwk G Γ) a a', domR ρ a a' -> forall p p',
        PosRel (kw_G ρ) (kw_Δ ρ) (ktml ρ iN)[lsingle a] (ktml ρ N')[lsingle a'] p p' ->
        [ kw_G ρ ; kw_Δ ρ ,, (ktyll ρ iD)[lsingle2 a p] @ iLp
            ⊢ (ktmlll ρ iC)[llift (lsingle2 a p)] ≈ (ktmlll ρ C')[llift (lsingle2 a' p')] : (kty ρ iX)⟨↑⟩ @ iLi ]) /\
    (forall ρ : kwk G Γ, idxR ρ (ktm ρ im) (ktm ρ m')) /\
    releq R (IWiRel G Γ iL iLp iLi iX iA iN iD iO iC idxR domR pdR im).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR
                | G Γ T T' l vl1 vlp1 vli1 vl2 vlp2 vli2 vX vX' vA vA' vN vN' vD vD' vO vO' vC vC' vm vm' vidxR vdomR vpdR R
                    Hl Hvl2 Hvlp2 Hvli2 Hvw Hvwp Hvwi HT HT' HvX HvX' HvA HvA' HvN HvN' HvD HvD' HvO HvO' HvC HvC' Hvm Hvm'
                    HvXX HvAA HvNN HvDD HvOO HvCC Hvmm vidxAd Hvisym Hvistr vdomAd varAd votAd vpdAd vpdE vpdMon vchAd vgC vixAd HR];
    intros HN; try open_mod; agree; try ne_absurd.
  do 13 eexists; eauto 50.
Qed.


(** Indexed [M] (M18b). *)
Lemma LR_inv_M {ul1 ul2 uli uX uA uB uC um l'} : [ G ; Γ ⊢g T ⤳* tyM ul1 ul2 uli uX uA uB uC um @ l' ] ->
  exists r1 r2 ri X' A' B' C' m' (idxR : DomRel G Γ) (shR : MShRel G Γ) (posR : MPosRel G Γ),
    lequiv (gL G) l (mlvl ul1 ul2 uli) /\
    lequiv (gL G) r1 ul1 /\ lequiv (gL G) r2 ul2 /\ lequiv (gL G) ri uli /\
    lwf (gL G) ul1 /\ lwf (gL G) ul2 /\ lwf (gL G) uli /\
    [ G ; Γ ⊢g T ⤳* tyM ul1 ul2 uli uX uA uB uC um @ l ] /\ [ G ; Γ ⊢g T' ⤳* tyM r1 r2 ri X' A' B' C' m' @ l ] /\
    [ G ; Γ ⊢g uX @ uli ] /\ [ G ; Γ ⊢g X' @ uli ] /\
    [ G ; Γ ,, uX @ uli ⊢g uA @ ul1 ] /\ [ G ; Γ ,, X' @ uli ⊢g A' @ ul1 ] /\
    [ G ; Γ ,, uX @ uli ,, uA @ ul1 ⊢g uB @ ul2 ] /\ [ G ; Γ ,, X' @ uli ,, A' @ ul1 ⊢g B' @ ul2 ] /\
    [ G ; Γ ,, uX @ uli ,, uA @ ul1 ,, uB @ ul2 ⊢g uC : uX⟨↑⟩⟨↑⟩⟨↑⟩ @ uli ] /\
    [ G ; Γ ,, X' @ uli ,, A' @ ul1 ,, B' @ ul2 ⊢g C' : X'⟨↑⟩⟨↑⟩⟨↑⟩ @ uli ] /\
    [ G ; Γ ⊢g um : uX @ uli ] /\ [ G ; Γ ⊢g m' : X' @ uli ] /\
    [ G ; Γ ⊢ uX ≈ X' @ uli ] /\ [ G ; Γ ,, uX @ uli ⊢ uA ≈ A' @ ul1 ] /\
    [ G ; Γ ,, uX @ uli ,, uA @ ul1 ⊢ uB ≈ B' @ ul2 ] /\
    [ G ; Γ ,, uX @ uli ,, uA @ ul1 ,, uB @ ul2 ⊢ uC ≈ C' : uX⟨↑⟩⟨↑⟩⟨↑⟩ @ uli ] /\
    [ G ; Γ ⊢ um ≈ m' : uX @ uli ] /\
    (forall ρ : kwk G Γ, LR n rec (kw_G ρ) (kw_Δ ρ) (kty ρ uX) (kty ρ X') uli (idxR ρ)) /\
    (forall (ρ : kwk G Γ) x x', idxR ρ x x' ->
        LR n rec (kw_G ρ) (kw_Δ ρ) (ktyl ρ uA)[lsingle x] (ktyl ρ A')[lsingle x'] ul1 (shR ρ x x')) /\
    (forall (ρ : kwk G Γ) x x' a a', idxR ρ x x' -> shR ρ x x' a a' ->
        LR n rec (kw_G ρ) (kw_Δ ρ) (ktyll ρ uB)[lsingle2 x a] (ktyll ρ B')[lsingle2 x' a'] ul2
          (posR ρ x x' a a')) /\
    (forall (ρ : kwk G Γ) x x' a a' p p', idxR ρ x x' -> shR ρ x x' a a' -> posR ρ x x' a a' p p' ->
        idxR ρ (ktmlll ρ uC)[lsingle3 x a p] (ktmlll ρ C')[lsingle3 x' a' p']) /\
    (forall (ρ : kwk G Γ) x x', idxR ρ x x' ->
        [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ uA)[lsingle x] @ ul1
            ⊢ (ktyll ρ uB)[llift (lsingle x)] ≈ (ktyll ρ B')[llift (lsingle x')] @ ul2 ]) /\
    (forall (ρ : kwk G Γ) x x', idxR ρ x x' ->
        [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ uA)[lsingle x] @ ul1 ,, (ktyll ρ uB)[llift (lsingle x)] @ ul2
            ⊢ (ktmlll ρ uC)[llift (llift (lsingle x))] ≈ (ktmlll ρ C')[llift (llift (lsingle x'))]
            : (kty ρ uX)⟨↑⟩⟨↑⟩ @ uli ]) /\
    (forall (ρ : kwk G Γ) x x' a a', idxR ρ x x' -> shR ρ x x' a a' ->
        [ kw_G ρ ; kw_Δ ρ ,, (ktyll ρ uB)[lsingle2 x a] @ ul2
            ⊢ (ktmlll ρ uC)[llift (lsingle2 x a)] ≈ (ktmlll ρ C')[llift (lsingle2 x' a')] : (kty ρ uX)⟨↑⟩ @ uli ]) /\
    (forall (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) x x', idxR ρ x x' ->
        idxR (kw_comp ρ ρ') (ktm ρ' x) (ktm ρ' x')) /\
    (forall (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) x x' a a', idxR ρ x x' -> shR ρ x x' a a' ->
        shR (kw_comp ρ ρ') (ktm ρ' x) (ktm ρ' x') (ktm ρ' a) (ktm ρ' a')) /\
    (forall (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) x x' a a' p p', idxR ρ x x' -> shR ρ x x' a a' ->
        posR ρ x x' a a' p p' ->
        posR (kw_comp ρ ρ') (ktm ρ' x) (ktm ρ' x') (ktm ρ' a) (ktm ρ' a') (ktm ρ' p) (ktm ρ' p')) /\
    (forall ρ : kwk G Γ, idxR ρ (ktm ρ um) (ktm ρ m')) /\
    releq R (MR G Γ ul1 ul2 uli uX uA uB uC r1 r2 ri X' A' B' C' shR posR um m').
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR
                | G Γ T T' l vl1 vlp1 vli1 vl2 vlp2 vli2 vX vX' vA vA' vN vN' vD vD' vO vO' vC vC' vm vm' vidxR vdomR vpdR R
                    Hl Hvl2 Hvlp2 Hvli2 Hvw Hvwp Hvwi HT HT' HvX HvX' HvA HvA' HvN HvN' HvD HvD' HvO HvO' HvC HvC' Hvm Hvm'
                    HvXX HvAA HvNN HvDD HvOO HvCC Hvmm vidxAd Hvisym Hvistr vdomAd varAd votAd vpdAd vpdE vpdMon vchAd vgC vixAd HR];
    intros HN; try open_mod; agree; try ne_absurd.
  do 11 eexists; eauto 50.
Qed.

(** Propositional truncation (M16a). *)
Lemma LR_inv_sq {m1 C l'} : [ G ; Γ ⊢g T ⤳* tySq m1 C @ l' ] ->
  exists m2 C' RC, lequiv (gL G) l m1 /\ lequiv (gL G) m2 m1 /\ lwf (gL G) m1 /\
    [ G ; Γ ⊢g T ⤳* tySq m1 C @ l ] /\ [ G ; Γ ⊢g T' ⤳* tySq m2 C' @ l ] /\
    [ G ; Γ ⊢g C @ m1 ] /\ [ G ; Γ ⊢ C ≈ C' @ m1 ] /\ LR n rec G Γ C C' m1 RC /\
    (forall u v, RC u v -> RC v u) /\ (forall u v w, RC u v -> RC v w -> RC u w) /\
    releq R (SqRel G Γ m1 C RC).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR
                | G Γ T T' l vl1 vlp1 vli1 vl2 vlp2 vli2 vX vX' vA vA' vN vN' vD vD' vO vO' vC vC' vm vm' vidxR vdomR vpdR R
                    Hl Hvl2 Hvlp2 Hvli2 Hvw Hvwp Hvwi HT HT' HvX HvX' HvA HvA' HvN HvN' HvD HvD' HvO HvO' HvC HvC' Hvm Hvm'
                    HvXX HvAA HvNN HvDD HvOO HvCC Hvmm vidxAd Hvisym Hvistr vdomAd varAd votAd vpdAd vpdE vpdMon vchAd vgC vixAd HR];
    intros HN; try open_mod; agree; try ne_absurd.
  do 3 eexists; eauto 20.
Qed.

Lemma LR_inv_CTyp {Δ k l'} : [ G ; Γ ⊢g T ⤳* tyCTyp Δ k @ l' ] -> lr_j = jM /\ ModRel G Γ T T' l R.
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR
                | G Γ T T' l vl1 vlp1 vli1 vl2 vlp2 vli2 vX vX' vA vA' vN vN' vD vD' vO vO' vC vC' vm vm' vidxR vdomR vpdR R
                    Hl Hvl2 Hvlp2 Hvli2 Hvw Hvwp Hvwi HT HT' HvX HvX' HvA HvA' HvN HvN' HvD HvD' HvO HvO' HvC HvC' Hvm Hvm'
                    HvXX HvAA HvNN HvDD HvOO HvCC Hvmm vidxAd Hvisym Hvistr vdomAd varAd votAd vpdAd vpdE vpdMon vchAd vgC vixAd HR];
    intros HN; first [exact (conj Hj HM) | agree; try ne_absurd].
Qed.

Lemma LR_inv_CTrm {Δ A k l'} : [ G ; Γ ⊢g T ⤳* tyCTrm Δ A k @ l' ] -> lr_j = jM /\ ModRel G Γ T T' l R.
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l k1 k2 l3 l4 A0 B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l k1 k2 l3 l4 A0 B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l k1 k2 l3 l4 A0 B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR
                | G Γ T T' l vl1 vlp1 vli1 vl2 vlp2 vli2 vX vX' vA vA' vN vN' vD vD' vO vO' vC vC' vm vm' vidxR vdomR vpdR R
                    Hl Hvl2 Hvlp2 Hvli2 Hvw Hvwp Hvwi HT HT' HvX HvX' HvA HvA' HvN HvN' HvD HvD' HvO HvO' HvC HvC' Hvm Hvm'
                    HvXX HvAA HvNN HvDD HvOO HvCC Hvmm vidxAd Hvisym Hvistr vdomAd varAd votAd vpdAd vpdE vpdMon vchAd vgC vixAd HR];
    intros HN; first [exact (conj Hj HM) | agree; try ne_absurd].
Qed.

Lemma LR_inv_cpi {m1 U1 l'} : [ G ; Γ ⊢g T ⤳* tyCPi m1 U1 @ l' ] ->
  exists m2 U1' (instR : CInstRel G Γ),
    lr_j = jM /\ lequiv (gL G) l m1 /\ lequiv (gL G) m2 m1 /\ lwf (gL G) m1 /\
    [ G ; Γ ⊢g T' ⤳* tyCPi m2 U1' @ l ] /\
    [ gext G gdCtx ; Γ⟪S⟫ ⊢g U1 @ m1 ] /\ [ gext G gdCtx ; Γ⟪S⟫ ⊢g U1' @ m1 ] /\
    [ G ; Γ ⊢ tyCPi m1 U1 ≈ tyCPi m2 U1' @ m1 ] /\
    (forall (ρ : kwk G Γ) Δ Δ' (h : vp_ctx lr_vp (kw_G ρ) Δ Δ'),
        LR n rec (kw_G ρ) (kw_Δ ρ) (kbody ρ U1)⦃gsingle (GCtx Δ)⦄ (kbody ρ U1')⦃gsingle (GCtx Δ')⦄
           m1 (instR ρ Δ Δ' h)) /\
    releq R (CPiRel G Γ m1 m2 U1 U1' instR).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR
                | G Γ T T' l vl1 vlp1 vli1 vl2 vlp2 vli2 vX vX' vA vA' vN vN' vD vD' vO vO' vC vC' vm vm' vidxR vdomR vpdR R
                    Hl Hvl2 Hvlp2 Hvli2 Hvw Hvwp Hvwi HT HT' HvX HvX' HvA HvA' HvN HvN' HvD HvD' HvO HvO' HvC HvC' Hvm Hvm'
                    HvXX HvAA HvNN HvDD HvOO HvCC Hvmm vidxAd Hvisym Hvistr vdomAd varAd votAd vpdAd vpdE vpdMon vchAd vgC vixAd HR];
    intros HN; try open_mod; agree; try ne_absurd.
  do 3 eexists; eauto 20.
Qed.

Lemma LR_inv_tpi {Θ m1 m2 U1 l'} : [ G ; Γ ⊢g T ⤳* tyTPi Θ m1 m2 U1 @ l' ] ->
  exists Θ' m3 m4 U1' (instR : TInstRel G Γ Θ m1),
    lr_j = jM /\ lequiv (gL G) l m2 /\ lequiv (gL G) m3 m1 /\ lequiv (gL G) m4 m2 /\
    lwf (gL G) m1 /\ lwf (gL G) m2 /\
    [ G ; Γ ⊢g T' ⤳* tyTPi Θ' m3 m4 U1' @ l ] /\ vp_ctx lr_vp G Θ Θ' /\
    [ gext G (gdTy Θ lD m1) ; Γ⟪S⟫ ⊢g U1 @ m2 ] /\ [ gext G (gdTy Θ' lD m3) ; Γ⟪S⟫ ⊢g U1' @ m4 ] /\
    [ G ; Γ ⊢ tyTPi Θ m1 m2 U1 ≈ tyTPi Θ' m3 m4 U1' @ m2 ] /\
    (forall (ρ : kwk G Γ) A A' (h : vp_ty lr_vp (kw_G ρ) Θ⟦kw_γ ρ⟧ A A' m1),
        LR n rec (kw_G ρ) (kw_Δ ρ) (kbody ρ U1)⦃gsingle (GTy A)⦄ (kbody ρ U1')⦃gsingle (GTy A')⦄
           m2 (instR ρ A A' h)) /\
    releq R (TPiRel G Γ Θ Θ' m1 m2 m3 m4 U1 U1' instR).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR
                | G Γ T T' l vl1 vlp1 vli1 vl2 vlp2 vli2 vX vX' vA vA' vN vN' vD vD' vO vO' vC vC' vm vm' vidxR vdomR vpdR R
                    Hl Hvl2 Hvlp2 Hvli2 Hvw Hvwp Hvwi HT HT' HvX HvX' HvA HvA' HvN HvN' HvD HvD' HvO HvO' HvC HvC' Hvm Hvm'
                    HvXX HvAA HvNN HvDD HvOO HvCC Hvmm vidxAd Hvisym Hvistr vdomAd varAd votAd vpdAd vpdE vpdMon vchAd vgC vixAd HR];
    intros HN; try open_mod; agree; try ne_absurd.
  do 5 eexists; eauto 20.
Qed.

End Inversion.

End Irrelevance.
