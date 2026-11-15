(** * The children's spine to the relation at their [DVec] (M19_DESIGN.md, M19b)

    The converse of [DVecWSp_of_LR], for [elim_IWi]'s validity: a
    [sup_ii]'s spine, in every world, is related at the children's [DVec]
    type, so that the step's [cs] entry of the substitution is related.
    As [IWfSp]'s, by induction on the length's [NatRel] in every world at
    once, generalized over the domain family [d] and the family of child
    indices [c]. Two differences:
    - The head is a function: its relation at the field's [Π] is [PiRel],
      whose applications to arguments related at the domain are the
      spine's at the argument relation [yR] ([IWiSp_head]). So the spine
      in each world comes with an argument relation that holds of any
      arguments related at the domain, at a position related to some
      position of the right length ([YOk]).
    - The codomain relation is [IWiRel] by [LR_iwi_rel], at index, shape
      and domain relations canonical where the relation reads them
      ([IWiCan], as [elimIWi_kd]). *)
From DeLaM.Validity Require Export IWi IWfSp.
From DeLaM.LogRel Require Import IWfAux IWiAux.
From DeLaM.Validity Require Import W.

Section S.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

(** ** Syntax *)

Section KwSyntax.
Context {G : gctx} {Γ : ctx} (ρ : kwk G Γ).

Lemma ktyll_iwiFamCodT l lp li X A N D Ot C c :
  ktyll ρ (iwiFamCodT l lp li X A N D Ot C c) =
  iwiFamCodT l lp li (kty ρ X) (kty ρ A) (ktml ρ N) (ktyll ρ D) (ktml ρ Ot) (ktmlll ρ C) (ktmll ρ c).
Proof using .
  unfold iwiFamCodT, kty, ktml, ktyll, ktmll, ktmlll.
  rewrite gwa_tyIWi, !gwa_ren_ty, !gwa_ren. cbn. f_equal. all: teq_core.
Qed.

(** A field's codomain at a position, in a world, at an argument. *)
Lemma kcod_single l lp li X A N D Ot C c p b :
  nfty X -> nfty A -> nftm N -> nfty D -> nftm Ot -> nftm C ->
  (ktyl ρ (iwiFamCodT l lp li X A N D Ot C c)[llift (lsingle p)])[lsingle b] =
  tyIWi l lp li (kty ρ X) (kty ρ A) (ktml ρ N) (ktyll ρ D) (ktml ρ Ot) (ktmlll ρ C)
    (ktmll ρ c)[lsingle2 (ktm ρ p) b].
Proof using .
  intros NX NA NN ND NO NC.
  assert (Nρ : nfty (kty ρ X) /\ nfty (kty ρ A) /\ nftm (ktml ρ N) /\ nfty (ktyll ρ D) /\ nftm (ktml ρ Ot)
               /\ nftm (ktmlll ρ C) /\ nftm (ktm ρ p))
    by (unfold kty, ktml, ktyll, ktmlll, ktm; repeat split; first [apply ren_nf_ty | apply ren_nf]).
  destruct Nρ as (NX' & NA' & NN' & ND' & NO' & NC' & Np).
  rewrite ktyl_llift_single, ktyll_iwiFamCodT, iwiFamCodT_single, iwiCod_single, llift_single_single_tm
    by assumption.
  reflexivity.
Qed.

End KwSyntax.

(** [IWiRel] is closed under reduction. *)
Lemma IWiRel_red_fwd {G Δ l lp li X A N D Ot C ix dm pd m t t' u u'} :
  IWiRel G Δ l lp li X A N D Ot C ix dm pd m t t' ->
  [ G ; Δ ⊢g t ⤳* u : tyIWi l lp li X A N D Ot C m @ iwiL l lp li ] ->
  [ G ; Δ ⊢g t' ⤳* u' : tyIWi l lp li X A N D Ot C m @ iwiL l lp li ] ->
  IWiRel G Δ l lp li X A N D Ot C ix dm pd m u u'.
Proof using EL.
  intros H Hu Hu'. destruct (IWiRel_inv H) as (w & w' & Hw & Hw' & Ew & Nw).
  econstructor; [exact (tmred_to_whnf Hu Hw (IWiNf_whnf_l Nw)) | exact (tmred_to_whnf Hu' Hw' (IWiNf_whnf_r Nw))
                | exact Ew | exact Nw].
Qed.

(** ** Canonical relations, and the spine in every world *)

(** The index, shape and domain relations, canonical where the relation
    reads them, against a right arity [N0] ([LR_iwi_rel]'s premises). *)
Definition IWiCan G Δ l lp li X A N N0 D (ix dm : DomRel G Δ) (pd : IPosDomRel G Δ) : Prop :=
  KDom G Δ (lmeasure (iwiL l lp li)) li X ix /\ KDom G Δ (lmeasure (iwiL l lp li)) l A dm /\
  (forall (ρ : kwk G Δ) a a', dm ρ a a' ->
     NatRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N)[lsingle a] (ktml ρ N0)[lsingle a']) /\
  (forall (ρ : kwk G Δ) a a', dm ρ a a' -> forall p p',
     PosRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N)[lsingle a] (ktml ρ N0)[lsingle a'] p p' ->
     exists D1, LR (lmeasure (iwiL l lp li)) (LRbelow (lmeasure (iwiL l lp li))) (kw_G ρ) (kw_Δ ρ)
       (ktyll ρ D)[lsingle2 a p] D1 lp (pd ρ a a' p p')) /\
  (forall (ρ : kwk G Δ) a a' p p' y y', pd ρ a a' p p' y y' ->
     PosRel (kw_G ρ) (kw_Δ ρ) (ktml ρ N)[lsingle a] (ktml ρ N0)[lsingle a'] p p').

Lemma IWiCan_comp {G Δ l lp li X A N N0 D} {ix dm : DomRel G Δ} {pd : IPosDomRel G Δ} (ρ : kwk G Δ) :
  IWiCan G Δ l lp li X A N N0 D ix dm pd ->
  IWiCan (kw_G ρ) (kw_Δ ρ) l lp li (kty ρ X) (kty ρ A) (ktml ρ N) (ktml ρ N0) (ktyll ρ D)
    (fun ρ' => ix (kw_comp ρ ρ')) (fun ρ' => dm (kw_comp ρ ρ')) (fun ρ' => pd (kw_comp ρ ρ')).
Proof using .
  intros (HX & HA & Har & Hpd & HpdE).
  refine (conj (KDom_comp ρ HX) (conj (KDom_comp ρ HA) (conj _ (conj _ _)))).
  - intros ρ' a a' h. pose proof (Har (kw_comp ρ ρ') a a' h) as Y. now rewrite !ktml_comp in Y.
  - intros ρ' a a' h p p' Hp. rewrite <- !ktml_comp in Hp.
    destruct (Hpd (kw_comp ρ ρ') a a' h p p' Hp) as [D1 Y]. rewrite ktyll_comp in Y. eauto.
  - intros ρ' a a' p p' y y' Hy. pose proof (HpdE _ _ _ _ _ _ _ Hy) as Z. now rewrite !ktml_comp in Z.
Qed.

(** An argument relation holding of arguments related at the domain
    family, at a position related to one of the right length. *)
Definition YOk G Δ lp (d : ty) (k k' : tm) (yR : tm -> tm -> tm -> Prop) : Prop :=
  forall p p' b b' T1, PosRel G Δ k k' p p' -> LRtm lp G Δ d[lsingle p] T1 b b' -> yR p b b'.

(** The spine at its own world, and in every world at an argument
    relation as above, as [sup_ii]'s premise provides it. *)
Definition IKSpW G Δ l lp li X A N D Ot C (ix dm : DomRel G Δ) (pd : IPosDomRel G Δ) d c k k' cs cs' : Prop :=
  (exists yR0, DVecWSp G Δ l lp li X A N D Ot C ix dm pd yR0 d c k cs cs') /\
  forall ρ : kwk G Δ, exists yR, YOk (kw_G ρ) (kw_Δ ρ) lp (ktyl ρ d) (ktm ρ k) (ktm ρ k') yR /\
    DVecWSp (kw_G ρ) (kw_Δ ρ) l lp li (kty ρ X) (kty ρ A) (ktml ρ N) (ktyll ρ D) (ktml ρ Ot) (ktmlll ρ C)
      (fun ρ' => ix (kw_comp ρ ρ')) (fun ρ' => dm (kw_comp ρ ρ')) (fun ρ' => pd (kw_comp ρ ρ')) yR
      (ktyl ρ d) (ktmll ρ c) (ktm ρ k) (ktm ρ cs) (ktm ρ cs').

Lemma IKSpW_kw {G Δ l lp li X A N D Ot C} {ix dm : DomRel G Δ} {pd : IPosDomRel G Δ} {d c k k' cs cs'}
    (ρ : kwk G Δ) :
  IKSpW G Δ l lp li X A N D Ot C ix dm pd d c k k' cs cs' ->
  IKSpW (kw_G ρ) (kw_Δ ρ) l lp li (kty ρ X) (kty ρ A) (ktml ρ N) (ktyll ρ D) (ktml ρ Ot) (ktmlll ρ C)
    (fun ρ' => ix (kw_comp ρ ρ')) (fun ρ' => dm (kw_comp ρ ρ')) (fun ρ' => pd (kw_comp ρ ρ'))
    (ktyl ρ d) (ktmll ρ c) (ktm ρ k) (ktm ρ k') (ktm ρ cs) (ktm ρ cs').
Proof using .
  intros [_ HK]. split.
  - destruct (HK ρ) as (yR & _ & Y). eauto.
  - intros ρ'. destruct (HK (kw_comp ρ ρ')) as (yR & Hy & Y). exists yR.
    rewrite ktyl_comp, !ktm_comp in Hy.
    rewrite kty_comp, kty_comp, ktml_comp, ktyll_comp, ktml_comp, ktmlll_comp, ktyl_comp, ktmll_comp, !ktm_comp in Y.
    exact (conj Hy Y).
Qed.

(** ** The head, a function

    The head of a spine at a successor, at any annotations equivalent to
    the field's: related at the field's [Π] by [PiRel], its applications
    in each world being the spine's there, at arguments [yR] relates by
    [YOk], reduced to the applications of the head's whnf. *)
Lemma IWiSp_head {G Δ l lp li X A N N0 D Ot C} {ix dm : DomRel G Δ} {pd : IPosDomRel G Δ}
    {d c k k' m m' cs cs' w w' T0 T0' l0 l0' la lb A1 B1 la' lb' A1' B1' T R} :
  nfty X -> nfty A -> nftm N -> nfty D -> nftm Ot -> nftm C ->
  IWiCan G Δ l lp li X A N N0 D ix dm pd ->
  IKSpW G Δ l lp li X A N D Ot C ix dm pd d c k k' cs cs' ->
  [ G ; Δ ⊢g k ⤳* succ m : tyNat @ lzero ] -> [ G ; Δ ⊢g k' ⤳* succ m' : tyNat @ lzero ] -> NatRel G Δ m m' ->
  [ G ; Δ ⊢g cs ⤳* w : T0 @ l0 ] -> whnf w -> [ G ; Δ ⊢g cs' ⤳* w' : T0' @ l0' ] -> whnf w' ->
  lequiv (gL G) la (iwiL l lp li) -> lequiv (gL G) lb (iwiL l lp li) ->
  lequiv (gL G) la' (iwiL l lp li) -> lequiv (gL G) lb' (iwiL l lp li) ->
  [ G ; Δ ⊢ dvecHd m (iwiFamT l lp li X A N D Ot C d c) ≈ A1 @ iwiL l lp li ] ->
  [ G ; Δ ,, dvecHd m (iwiFamT l lp li X A N D Ot C d c) @ iwiL l lp li
      ⊢ dvecTl (iwiL l lp li) m (iwiFamT l lp li X A N D Ot C d c) ≈ B1 @ iwiL l lp li ] ->
  [ G ; Δ ⊢ dvecHd m (iwiFamT l lp li X A N D Ot C d c) ≈ A1' @ iwiL l lp li ] ->
  [ G ; Δ ,, dvecHd m (iwiFamT l lp li X A N D Ot C d c) @ iwiL l lp li
      ⊢ dvecTl (iwiL l lp li) m (iwiFamT l lp li X A N D Ot C d c) ≈ B1' @ iwiL l lp li ] ->
  LogRel (iwiL l lp li) G Δ (dvecHd m (iwiFamT l lp li X A N D Ot C d c)) T (iwiL l lp li) R ->
  R (tmFst la lb A1 B1 w) (tmFst la' lb' A1' B1' w').
Proof using EL VL VN.
  intros NX NA NN ND NO NC HCan [[yR0 Hown] HK] Hk Hk' Hmm Hr Nw Hr' Nw' H1 H2 H1' H2' HA1 HB1 HA1' HB1' H.
  destruct HCan as (HX & HA & Har & Hpd & HpdE).
  set (F := iwiFamT l lp li X A N D Ot C d c) in *.
  set (Cod := (iwiFamCodT l lp li X A N D Ot C c)[llift (lsingle (posHd m))]).
  (* the head's whnfs, by the own spine *)
  destruct (DVecWSp_succ_inv Hown Hk) as (w0 & w0' & Hr0 & Hr0' & Nw0 & Nw0' & _ & Hwh & _ & _).
  assert (w0 = w) by (eapply tmred_whnf_det; [exact Hr0 | exact Hr | exact Nw0 | exact Nw]). subst w0.
  assert (w0' = w') by (eapply tmred_whnf_det; [exact Hr0' | exact Hr' | exact Nw0' | exact Nw']). subst w0'.
  destruct (Hwh _ _ _ _ _ _ _ _ H1 H2 H1' H2' HA1 HB1 HA1' HB1') as (v & v' & Hv & Hv' & Nv & Nv' & Ev).
  pose proof (eqty_wf_l ge_typeof (geq_ty_sound HA1)) as Hhd.
  assert (EF : dvecHd m F = tyPi lp (iwiL l lp li) d[lsingle (posHd m)] Cod)
    by (unfold F, Cod; rewrite iwiFamT_single, iwiFamCodT_single by assumption; reflexivity).
  rewrite EF in H. fold F in Hv, Hv', Ev. rewrite EF in Hv, Hv', Ev.
  destruct (escape_ty _ _ _ _ _ _ _ _ H) as (HT & _ & _).
  destruct (LR_inv_pi H (tyred_refl _ _ HT)) as (m3 & m4 & C' & D' & domR & codR & PF & domAd & codAd & Heq).
  destruct PF as [Hlv Hm3 Hm4 Hw1 Hw2 _ _ HC0 HC' HB0 HD' HCC HDD].
  apply (proj2 (Heq _ _)).
  assert (EΠ : [ G ; Δ ⊢g tyPi lp (iwiL l lp li) d[lsingle (posHd m)] Cod ≅ tyPi m3 m4 C' D'
                 @ lmax lp (iwiL l lp li) ])
    by (apply geq_ty_sound, geq_ty_pi; auto using lequiv_sym).
  assert (Hle : lmeasure lp <= lmeasure (iwiL l lp li)) by (rewrite !lmeasure_max; lia).
  pose proof (lequiv_sym _ _ _ Hlv) as Hlv'.
  exists v, v'. refine (conj _ (conj _ (conj Nv (conj Nv' (conj _ (conj _ _)))))).
  - eapply tmred_lconv; [exact Hv | exact Hlv'].
  - eapply tmred_conv; [apply ge_typeof | eapply tmred_lconv; [exact Hv' | exact Hlv'] | exact EΠ].
  - eapply geq_tm_lconv; [exact Ev | exact Hlv'].
  - eapply geq_tm_conv; [eapply geq_tm_lconv; [exact Ev | exact Hlv'] | exact EΠ].
  - intros ρ b b' hb la2 lb2 la2' lb2' A3 B3 A3' B3' J1 J2 J1' J2' HA3 HB3 HA3' HB3'.
    pose proof (kw_lwf ρ Hw1) as Hw1ρ. pose proof (kw_lwf ρ Hw2) as Hw2ρ.
    (* the argument, related at the domain *)
    pose proof (domAd ρ) as DOM.
    assert (Xb : LRtm lp (kw_G ρ) (kw_Δ ρ) (kty ρ d[lsingle (posHd m)]) (kty ρ C') b b')
      by (apply (LRtm_stage Hle); exists (domR ρ); split; [exact DOM | exact hb]).
    destruct (LRtm_escape Xb) as [Hbt Hb't]. pose proof (LRtm_geq Xb) as Ebb.
    (* the spine in the world *)
    destruct (HK ρ) as (yR & HyR & Hsp).
    pose proof (kw_tmred_succ Hk ρ) as Hkρ. pose proof (kw_tmred_succ Hk' ρ) as Hk'ρ.
    destruct (DVecWSp_succ_inv Hsp Hkρ) as (w1 & w1' & Hr1 & Hr1' & Nw1 & Nw1' & _ & _ & Happ & _).
    assert (w1 = ktm ρ w)
      by (eapply tmred_whnf_det; [exact Hr1 | exact (kw_tmred ρ Hr) | exact Nw1 | exact (whnf_kw ρ _ Nw)]).
    subst w1.
    assert (w1' = ktm ρ w')
      by (eapply tmred_whnf_det; [exact Hr1' | exact (kw_tmred ρ Hr') | exact Nw1' | exact (whnf_kw ρ _ Nw')]).
    subst w1'.
    assert (Hy : yR (posHd (ktm ρ m)) b b').
    { apply (HyR _ (posHd (ktm ρ m')) b b' (kty ρ C')).
      - exact (pos_hd _ _ _ _ _ _ Hkρ Hk'ρ (NatRel_kw ρ _ _ Hmm)).
      - rewrite kty_single, ktm_posHd in Xb. exact Xb. }
    (* the annotations in the world *)
    pose proof (kw_geq_ty ρ HA1) as KA1. pose proof (kw_geq_ty_l ρ Hhd Hw2 HB1) as KB1.
    pose proof (kw_geq_ty ρ HA1') as KA1'. pose proof (kw_geq_ty_l ρ Hhd Hw2 HB1') as KB1'.
    rewrite (ktyl_dvecTl ρ) in KB1, KB1'. rewrite (kty_dvecHd ρ) in KA1, KB1, KA1', KB1'.
    unfold F in KA1, KB1, KA1', KB1'. rewrite (ktyl_iwiFamT ρ) in KA1, KB1, KA1', KB1'.
    pose proof (kw_geq_ty ρ HCC) as KC. pose proof (kw_geq_ty_l ρ HC0 Hw1 HDD) as KD.
    assert (HA3'x : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ d[lsingle (posHd m)] ≈ A3' @ lp ]) by exact (geq_ty_trans KC HA3').
    assert (HB3'x : [ kw_G ρ ; kw_Δ ρ ,, kty ρ d[lsingle (posHd m)] @ lp ⊢ ktyl ρ Cod ≈ B3' @ iwiL l lp li ]).
    { eapply geq_ty_trans; [exact KD|].
      eapply geq_ty_ctxconv; [apply eqty_sym, geq_ty_sound, KC | now apply lequiv_refl
                             | apply ext_wf_g; [exact (kw_ty ρ HC0) | exact Hw1ρ] | exact HB3']. }
    (* the applications at the head, by the spine *)
    pose proof HA3 as HA3r. pose proof HB3 as HB3r. pose proof HA3'x as HA3'r. pose proof HB3'x as HB3'r.
    unfold Cod in HB3r, HB3'r.
    rewrite kty_single, ktm_posHd in HA3r, HB3r, HA3'r, HB3'r.
    rewrite ktyl_llift_single, ktyll_iwiFamCodT, ktm_posHd in HB3r, HB3'r.
    pose proof (Happ la lb (kty ρ A1) (ktyl ρ B1) la' lb' (kty ρ A1') (ktyl ρ B1')
                  (kw_lequiv ρ H1) (kw_lequiv ρ H2) (kw_lequiv ρ H1') (kw_lequiv ρ H2') KA1 KB1 KA1' KB1'
                  b b' Hy la2 lb2 A3 B3 la2' lb2' A3' B3' (kw_lequiv ρ J1) (kw_lequiv ρ J2) (kw_lequiv ρ J1') (kw_lequiv ρ J2') HA3r HB3r HA3'r HB3'r) as Y.
    (* ... reduced to the applications of the head's whnfs *)
    pose proof (kw_tmred ρ Hv) as Kv. pose proof (kw_tmred ρ Hv') as Kv'.
    rewrite ktm_fst, kty_tyPi in Kv, Kv'.
    pose proof (tmred_lconv _ _ _ _ _ Kv (kw_lequiv ρ Hlv')) as Kv1.
    pose proof (tmred_lconv _ _ _ _ _ Kv' (kw_lequiv ρ Hlv')) as Kv1'.
    pose proof (kw_ty ρ HC0) as HC0ρ. pose proof (kw_ty_l ρ HC0 Hw1 HB0) as HB0ρ.
    pose proof (tmred_app_annot Hw1ρ Hw2ρ (kw_lequiv ρ J1) (kw_lequiv ρ J2) HC0ρ HB0ρ Hbt (geq_ty_sound HA3) (geq_ty_sound HB3) Kv1) as Ra.
    pose proof (tmred_app_annot Hw1ρ Hw2ρ (kw_lequiv ρ J1') (kw_lequiv ρ J2') HC0ρ HB0ρ Hb't (geq_ty_sound HA3'x) (geq_ty_sound HB3'x) Kv1')
      as Ra'.
    pose proof (wf_ty_func ge_typeof HB0ρ (lsub_eq_single ge_typeof Hb't Hbt (eqtm_sym _ _ _ _ _ _ _ (geq_tm_sound Ebb))))
      as EB.
    pose proof (tmred_conv _ _ _ _ _ ge_typeof Ra' EB) as Ra''.
    unfold Cod in Ra, Ra''. rewrite kcod_single, ktm_posHd in Ra, Ra'' by assumption.
    pose proof (IWiRel_red_fwd Y Ra Ra'') as Y'.
    (* the codomain relation is [IWiRel] *)
    pose proof (codAd ρ b b' hb) as COD. unfold Cod in COD. rewrite kcod_single, ktm_posHd in COD by assumption.
    destruct (IWiCan_comp ρ (conj HX (conj HA (conj Har (conj Hpd HpdE))))) as (HXρ & HAρ & Harρ & Hpdρ & HpdEρ).
    exact (proj2 (LR_iwi_rel COD HXρ HAρ Harρ Hpdρ HpdEρ _ _) Y').
Qed.

(** The tail of a spine at a successor, at any annotations equivalent to
    the field's, is a spine at the moved families. *)
Lemma IKSpW_tl {G Δ l lp li X A N D Ot C} {ix dm : DomRel G Δ} {pd : IPosDomRel G Δ}
    {d c k k' m m' cs cs' w w' T0 T0' l0 l0' la lb A1 B1 la' lb' A1' B1'} :
  IKSpW G Δ l lp li X A N D Ot C ix dm pd d c k k' cs cs' ->
  [ G ; Δ ⊢g k ⤳* succ m : tyNat @ lzero ] -> [ G ; Δ ⊢g k' ⤳* succ m' : tyNat @ lzero ] ->
  [ G ; Δ ⊢g cs ⤳* w : T0 @ l0 ] -> whnf w -> [ G ; Δ ⊢g cs' ⤳* w' : T0' @ l0' ] -> whnf w' ->
  lequiv (gL G) la (iwiL l lp li) -> lequiv (gL G) lb (iwiL l lp li) ->
  lequiv (gL G) la' (iwiL l lp li) -> lequiv (gL G) lb' (iwiL l lp li) ->
  [ G ; Δ ⊢ dvecHd m (iwiFamT l lp li X A N D Ot C d c) ≈ A1 @ iwiL l lp li ] ->
  [ G ; Δ ,, dvecHd m (iwiFamT l lp li X A N D Ot C d c) @ iwiL l lp li
      ⊢ dvecTl (iwiL l lp li) m (iwiFamT l lp li X A N D Ot C d c) ≈ B1 @ iwiL l lp li ] ->
  [ G ; Δ ⊢ dvecHd m (iwiFamT l lp li X A N D Ot C d c) ≈ A1' @ iwiL l lp li ] ->
  [ G ; Δ ,, dvecHd m (iwiFamT l lp li X A N D Ot C d c) @ iwiL l lp li
      ⊢ dvecTl (iwiL l lp li) m (iwiFamT l lp li X A N D Ot C d c) ≈ B1' @ iwiL l lp li ] ->
  IKSpW G Δ l lp li X A N D Ot C ix dm pd (posMvT m d) (posMv2 m c) m m'
    (tmSnd la lb A1 B1 w) (tmSnd la' lb' A1' B1' w').
Proof using EL.
  intros [[yR0 Hown] HK] Hk Hk' Hr Nw Hr' Nw' H1 H2 H1' H2' HA1 HB1 HA1' HB1'.
  pose proof (eqty_wf_l ge_typeof (geq_ty_sound HA1)) as Hhd. pose proof (lequiv_wf_r _ _ _ H1) as HwL.
  split.
  - destruct (DVecWSp_succ_inv Hown Hk) as (w0 & w0' & Hr0 & Hr0' & Nw0 & Nw0' & _ & _ & _ & Htl).
    assert (w0 = w) by (eapply tmred_whnf_det; [exact Hr0 | exact Hr | exact Nw0 | exact Nw]). subst w0.
    assert (w0' = w') by (eapply tmred_whnf_det; [exact Hr0' | exact Hr' | exact Nw0' | exact Nw']). subst w0'.
    eexists. exact (Htl _ _ _ _ _ _ _ _ H1 H2 H1' H2' HA1 HB1 HA1' HB1').
  - intros ρ. destruct (HK ρ) as (yR & HyR & Hsp).
    pose proof (kw_tmred_succ Hk ρ) as Hkρ. pose proof (kw_tmred_succ Hk' ρ) as Hk'ρ.
    destruct (DVecWSp_succ_inv Hsp Hkρ) as (w1 & w1' & Hr1 & Hr1' & Nw1 & Nw1' & _ & _ & _ & Htl).
    assert (w1 = ktm ρ w)
      by (eapply tmred_whnf_det; [exact Hr1 | exact (kw_tmred ρ Hr) | exact Nw1 | exact (whnf_kw ρ _ Nw)]).
    subst w1.
    assert (w1' = ktm ρ w')
      by (eapply tmred_whnf_det; [exact Hr1' | exact (kw_tmred ρ Hr') | exact Nw1' | exact (whnf_kw ρ _ Nw')]).
    subst w1'.
    assert (Nm : nftm (ktm ρ m)) by (unfold ktm; apply ren_nf).
    exists (fun p => yR (posTl (ktm ρ m) p)). split.
    + intros p p' b b' T1 Hp Hb. rewrite ktyl_posMvT, posMvT_single in Hb by exact Nm.
      apply (HyR _ (posTl (ktm ρ m') p') b b' T1); [|exact Hb].
      apply pos_tl; assumption.
    + pose proof (kw_geq_ty ρ HA1) as KA1. pose proof (kw_geq_ty_l ρ Hhd HwL HB1) as KB1.
      pose proof (kw_geq_ty ρ HA1') as KA1'. pose proof (kw_geq_ty_l ρ Hhd HwL HB1') as KB1'.
      rewrite (ktyl_dvecTl ρ) in KB1, KB1'. rewrite (kty_dvecHd ρ) in KA1, KB1, KA1', KB1'.
      rewrite (ktyl_iwiFamT ρ) in KA1, KB1, KA1', KB1'.
      rewrite ktyl_posMvT, ktmll_posMv2, !ktm_snd.
      exact (Htl la lb (kty ρ A1) (ktyl ρ B1) la' lb' (kty ρ A1') (ktyl ρ B1')
               (kw_lequiv ρ H1) (kw_lequiv ρ H2) (kw_lequiv ρ H1') (kw_lequiv ρ H2') KA1 KB1 KA1' KB1').
Qed.

(** ** Spine to relation *)

(** At a domain family, a family of child indices and the lengths, in a
    world. *)
Definition IWVecQ G Δ l lp li X A N D Ot C (ix dm : DomRel G Δ) (pd : IPosDomRel G Δ) d c k k' :=
  forall T' R, LogRel (iwiL l lp li) G Δ (tyDVec (iwiL l lp li) k (iwiFamT l lp li X A N D Ot C d c)) T'
                 (iwiL l lp li) R ->
  forall cs cs', IKSpW G Δ l lp li X A N D Ot C ix dm pd d c k k' cs cs' -> R cs cs'.

Lemma IWVecQ_zero {G Δ l lp li X A N D Ot C} {ix dm : DomRel G Δ} {pd : IPosDomRel G Δ} {d c k k'} :
  lwf (gL G) (iwiL l lp li) ->
  [ G ; Δ ,, tyFin k @ lzero ⊢g iwiFamT l lp li X A N D Ot C d c @ iwiL l lp li ] ->
  [ G ; Δ ⊢g k ⤳* zero : tyNat @ lzero ] -> IWVecQ G Δ l lp li X A N D Ot C ix dm pd d c k k'.
Proof using EL.
  intros HwL HF Hk T' R H cs cs' [[yR0 Hown] _].
  pose proof (fin_stab_ty' (tmred_eq _ _ _ _ _ _ _ Hk) HF) as HF0.
  assert (Hred : [ G ; Δ ⊢g tyDVec (iwiL l lp li) k (iwiFamT l lp li X A N D Ot C d c)
                   ⤳* tyUnit (iwiL l lp li) @ iwiL l lp li ])
    by (eapply tyred_trans; [exact (tyred_dvec HwL HF Hk) | exact (tyred_dvec_zero HwL HF0)]).
  destruct (LR_inv_unit H Hred) as (l2 & _ & _ & _ & _ & HR).
  exact (proj2 (HR _ _) (DVecWSp_zero_inv Hown Hk)).
Qed.

Lemma IWVecQ_ne {G Δ l lp li X A N D Ot C} {ix dm : DomRel G Δ} {pd : IPosDomRel G Δ} {d c k k' ν} :
  lwf (gL G) (iwiL l lp li) ->
  [ G ; Δ ,, tyFin k @ lzero ⊢g iwiFamT l lp li X A N D Ot C d c @ iwiL l lp li ] ->
  [ G ; Δ ⊢g k ⤳* ν : tyNat @ lzero ] -> whne ν -> IWVecQ G Δ l lp li X A N D Ot C ix dm pd d c k k'.
Proof using EL.
  intros HwL HF Hk Nν T' R H cs cs' [[yR0 Hown] _].
  destruct (LR_inv_ne H (tyred_dvec HwL HF Hk) (whne_tyDVec _ _ _ Nν)) as (V' & _ & HVV & HR).
  apply (proj2 (HR _ _)).
  eapply NeRel_conv2; [| | exact (DVecWSp_ne_inv Hown Hk Nν)].
  - apply eqty_refl. exact (eqty_wf_l ge_typeof (geq_ty_sound (gne_ty_geq HVV))).
  - apply geq_ty_sound, gne_ty_geq, HVV.
Qed.

Lemma IWVecQ_succ {G Δ l lp li X A N N0 D Ot C} {ix dm : DomRel G Δ} {pd : IPosDomRel G Δ} {d c k k' m m'} :
  lwf (gL G) (iwiL l lp li) ->
  nfty X -> nfty A -> nftm N -> nfty D -> nftm Ot -> nftm C ->
  [ G ; Δ ,, tyFin k @ lzero ⊢g iwiFamT l lp li X A N D Ot C d c @ iwiL l lp li ] ->
  IWiCan G Δ l lp li X A N N0 D ix dm pd ->
  [ G ; Δ ⊢g m : tyNat @ lzero ] -> [ G ; Δ ⊢g k ⤳* succ m : tyNat @ lzero ] ->
  [ G ; Δ ⊢g k' ⤳* succ m' : tyNat @ lzero ] -> NatRel G Δ m m' ->
  (forall ρ : kwk G Δ,
     IWVecQ (kw_G ρ) (kw_Δ ρ) l lp li (kty ρ X) (kty ρ A) (ktml ρ N) (ktyll ρ D) (ktml ρ Ot) (ktmlll ρ C)
       (fun ρ' => ix (kw_comp ρ ρ')) (fun ρ' => dm (kw_comp ρ ρ')) (fun ρ' => pd (kw_comp ρ ρ'))
       (ktyl ρ (posMvT m d)) (ktmll ρ (posMv2 m c)) (ktm ρ m) (ktm ρ m')) ->
  IWVecQ G Δ l lp li X A N D Ot C ix dm pd d c k k'.
Proof using EL VL VN.
  intros HwL NX NA NN ND NO NC HF HCan Hm Hk Hk' Hmm IH T' R H cs cs' HKs.
  pose proof HKs as [[yR0 Hown] _].
  pose proof (fin_stab_ty' (tmred_eq _ _ _ _ _ _ _ Hk) HF) as HF1.
  set (F := iwiFamT l lp li X A N D Ot C d c) in *.
  assert (Hred : [ G ; Δ ⊢g tyDVec (iwiL l lp li) k F
                   ⤳* tySig (iwiL l lp li) (iwiL l lp li) (dvecHd m F) (dvecTl (iwiL l lp li) m F) @ iwiL l lp li ])
    by (eapply tyred_trans; [exact (tyred_dvec HwL HF Hk) | exact (tyred_dvec_succ HwL HF1 Hm)]).
  destruct (LR_inv_sig H Hred) as (m3 & m4 & C' & D' & dS & cS & P & domAd & codAd & HR).
  destruct P as [_ Hm3 Hm4 _ _ _ _ HC0 HC' HV HD' HWC HVD].
  apply HR.
  destruct (DVecWSp_succ_inv Hown Hk) as (w & w' & Hr & Hr' & Nw & Nw' & Ew & _ & _ & _).
  assert (EΣ : [ G ; Δ ⊢g tySig (iwiL l lp li) (iwiL l lp li) (dvecHd m F) (dvecTl (iwiL l lp li) m F)
                 ≅ tySig m3 m4 C' D' @ lmax (iwiL l lp li) (iwiL l lp li) ])
    by (apply geq_ty_sound, geq_ty_sig; auto using lequiv_sym).
  exists w, w'. refine (conj Hr (conj _ (conj Nw (conj Nw' (conj Ew (conj _ _)))))).
  - eapply tmred_conv; [apply ge_typeof | exact Hr' | exact EΣ].
  - exact (geq_tm_conv Ew EΣ).
  - intros ρ la lb la' lb' A1 B1 A1' B1' H1 H2 H1' H2' HA1 HB1 HA1' HB1'.
    pose proof (kw_lwf ρ HwL) as HwLρ.
    (* the annotations, at the spine's types in the world *)
    pose proof (kw_geq_ty ρ HWC) as KC. pose proof (kw_geq_ty_l ρ HC0 HwL HVD) as KD.
    pose proof (kw_ty ρ HC0) as HC0ρ.
    assert (HA1'x : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ (dvecHd m F) ≈ A1' @ iwiL l lp li ]) by exact (geq_ty_trans KC HA1').
    assert (HB1'x : [ kw_G ρ ; kw_Δ ρ ,, kty ρ (dvecHd m F) @ iwiL l lp li
                      ⊢ ktyl ρ (dvecTl (iwiL l lp li) m F) ≈ B1' @ iwiL l lp li ]).
    { eapply geq_ty_trans; [exact KD|].
      eapply geq_ty_ctxconv; [apply eqty_sym, geq_ty_sound, KC | now apply lequiv_refl
                             | apply ext_wf_g; [exact HC0ρ | exact HwLρ] | exact HB1']. }
    rewrite (ktyl_dvecTl ρ) in HB1, HB1'x. rewrite (kty_dvecHd ρ) in HA1, HB1, HA1'x, HB1'x.
    unfold F in HA1, HB1, HA1'x, HB1'x. rewrite (ktyl_iwiFamT ρ) in HA1, HB1, HA1'x, HB1'x.
    pose proof (kw_tmred_succ Hk ρ) as Hkρ. pose proof (kw_tmred_succ Hk' ρ) as Hk'ρ.
    pose proof (kw_tmred ρ Hr) as Hrρ. pose proof (kw_tmred ρ Hr') as Hrρ'.
    pose proof (kw_lequiv ρ H1) as J1. pose proof (kw_lequiv ρ H2) as J2.
    pose proof (kw_lequiv ρ H1') as J1'. pose proof (kw_lequiv ρ H2') as J2'.
    assert (Nρ : nfty (kty ρ X) /\ nfty (kty ρ A) /\ nftm (ktml ρ N) /\ nfty (ktyll ρ D) /\ nftm (ktml ρ Ot)
                 /\ nftm (ktmlll ρ C))
      by (unfold kty, ktml, ktyll, ktmlll; repeat split; first [apply ren_nf_ty | apply ren_nf]).
    destruct Nρ as (NXρ & NAρ & NNρ & NDρ & NOρ & NCρ).
    (* the first projections, in [Σ]'s domain relation: functions *)
    pose proof (domAd ρ) as DOM. rewrite (kty_dvecHd ρ) in DOM. unfold F in DOM. rewrite (ktyl_iwiFamT ρ) in DOM.
    pose proof (IWiSp_head NXρ NAρ NNρ NDρ NOρ NCρ (IWiCan_comp ρ HCan) (IKSpW_kw ρ HKs) Hkρ Hk'ρ
                  (NatRel_kw ρ _ _ Hmm) Hrρ (whnf_kw ρ _ Nw) Hrρ' (whnf_kw ρ _ Nw') J1 J2 J1' J2'
                  HA1 HB1 HA1'x HB1'x DOM) as Fst.
    exists Fst.
    (* the second projections, in [Σ]'s codomain relation, by the induction hypothesis *)
    pose proof (codAd ρ _ _ Fst) as COD.
    rewrite (dvec_cod_single ρ), (kty_tyDVec ρ), (ktyl_dvecMv_eq ρ) in COD. unfold F in COD.
    rewrite (ktyl_iwiFamT ρ), iwiFamT_mv in COD.
    pose proof (IH ρ) as IHρ. unfold IWVecQ in IHρ. rewrite ktyl_posMvT, ktmll_posMv2 in IHρ.
    apply (IHρ _ _ COD).
    exact (IKSpW_tl (IKSpW_kw ρ HKs) Hkρ Hk'ρ Hrρ (whnf_kw ρ _ Nw) Hrρ' (whnf_kw ρ _ Nw') J1 J2 J1' J2'
             HA1 HB1 HA1'x HB1'x).
Qed.

Lemma ktyll_kid {G Δ} (HΔ : [ G ; Δ ⊢g ]) (T : ty) : nfty T -> ktyll (kid HΔ) T = T.
Proof using .
  intros H. unfold ktyll, kid, kw_loc; cbn [kw_γ kw_gk kw_r kw_rk gwa wk_ren kw_mk].
  rewrite <- (ren_id_ty T H) at 2. apply ren_ext_ty. intros [|[|n]]; rlk_simpl; cbn; lia.
Qed.
Lemma ktmlll_kid {G Δ} (HΔ : [ G ; Δ ⊢g ]) (t : tm) : nftm t -> ktmlll (kid HΔ) t = t.
Proof using .
  intros H. unfold ktmlll, kid, kw_loc; cbn [kw_γ kw_gk kw_r kw_rk gwa wk_ren kw_mk].
  rewrite <- (ren_id_tm t H) at 2. apply ren_ext_tm. intros [|[|[|n]]]; rlk_simpl; cbn; lia.
Qed.

Section SpineK.
Context {G : gctx} {Δ : ctx} {l lp li : lvl} {X A D : ty} {N N0 Ot C : tm}
  {ix dm : DomRel G Δ} {pd : IPosDomRel G Δ}
  (HwL : lwf (gL G) (iwiL l lp li))
  (NX : nfty X) (NA : nfty A) (NN : nftm N) (ND : nfty D) (NO : nftm Ot) (NC : nftm C)
  (HCan : IWiCan G Δ l lp li X A N N0 D ix dm pd).

(** Spine to relation: by induction on the lengths' [NatRel], in every
    world at once, over every domain family and family of child indices. *)
Lemma LR_of_DVecWSp_all : forall k k', NatRel G Δ k k' -> forall d c,
  [ G ; Δ ,, tyFin k @ lzero ⊢g iwiFamT l lp li X A N D Ot C d c @ iwiL l lp li ] ->
  forall ρ : kwk G Δ,
    IWVecQ (kw_G ρ) (kw_Δ ρ) l lp li (kty ρ X) (kty ρ A) (ktml ρ N) (ktyll ρ D) (ktml ρ Ot) (ktmlll ρ C)
      (fun ρ' => ix (kw_comp ρ ρ')) (fun ρ' => dm (kw_comp ρ ρ')) (fun ρ' => pd (kw_comp ρ ρ'))
      (ktyl ρ d) (ktmll ρ c) (ktm ρ k) (ktm ρ k').
Proof using EL HCan HwL NA NC ND NN NO NX VL VN.
  assert (Nρ : forall ρ : kwk G Δ, nfty (kty ρ X) /\ nfty (kty ρ A) /\ nftm (ktml ρ N) /\ nfty (ktyll ρ D)
                                    /\ nftm (ktml ρ Ot) /\ nftm (ktmlll ρ C))
    by (intros ρ; unfold kty, ktml, ktyll, ktmlll; repeat split; first [apply ren_nf_ty | apply ren_nf]).
  assert (HFρ : forall k d c (ρ : kwk G Δ), [ G ; Δ ⊢g k : tyNat @ lzero ] ->
            [ G ; Δ ,, tyFin k @ lzero ⊢g iwiFamT l lp li X A N D Ot C d c @ iwiL l lp li ] ->
            [ kw_G ρ ; kw_Δ ρ ,, tyFin (ktm ρ k) @ lzero
              ⊢g iwiFamT l lp li (kty ρ X) (kty ρ A) (ktml ρ N) (ktyll ρ D) (ktml ρ Ot) (ktmlll ρ C)
                   (ktyl ρ d) (ktmll ρ c) @ iwiL l lp li ]).
  { intros k d c ρ Hk HF. assert (HFin : [ G ; Δ ⊢g tyFin k @ lzero ]) by (apply wft_fin; [exact ge_notV | exact Hk]).
    pose proof (kw_ty_l ρ HFin I HF) as Y.
    rewrite kty_tyFin, ktyl_iwiFamT in Y. exact Y. }
  apply (NatRel_mut G Δ
    (fun k k' _ => forall d c,
       [ G ; Δ ,, tyFin k @ lzero ⊢g iwiFamT l lp li X A N D Ot C d c @ iwiL l lp li ] ->
       forall ρ : kwk G Δ,
       IWVecQ (kw_G ρ) (kw_Δ ρ) l lp li (kty ρ X) (kty ρ A) (ktml ρ N) (ktyll ρ D) (ktml ρ Ot) (ktmlll ρ C)
         (fun ρ' => ix (kw_comp ρ ρ')) (fun ρ' => dm (kw_comp ρ ρ')) (fun ρ' => pd (kw_comp ρ ρ'))
         (ktyl ρ d) (ktmll ρ c) (ktm ρ k) (ktm ρ k'))
    (fun w w' _ => forall k k', [ G ; Δ ⊢g k ⤳* w : tyNat @ lzero ] -> [ G ; Δ ⊢g k' ⤳* w' : tyNat @ lzero ] ->
       forall d c,
       [ G ; Δ ,, tyFin k @ lzero ⊢g iwiFamT l lp li X A N D Ot C d c @ iwiL l lp li ] ->
       forall ρ : kwk G Δ,
       IWVecQ (kw_G ρ) (kw_Δ ρ) l lp li (kty ρ X) (kty ρ A) (ktml ρ N) (ktyll ρ D) (ktml ρ Ot) (ktmlll ρ C)
         (fun ρ' => ix (kw_comp ρ ρ')) (fun ρ' => dm (kw_comp ρ ρ')) (fun ρ' => pd (kw_comp ρ ρ'))
         (ktyl ρ d) (ktmll ρ c) (ktm ρ k) (ktm ρ k'))).
  - intros t t' w w' Ht Ht' _ _ IH. exact (IH t t' Ht Ht').
  - intros k k' Hk _ d c HF ρ. pose proof (kw_tmred ρ Hk) as Hkρ. rewrite ktm_zero, kty_tyNat in Hkρ.
    exact (IWVecQ_zero (kw_lwf ρ HwL) (HFρ _ _ _ ρ (tmred_wf _ _ _ _ _ _ _ Hk) HF) Hkρ).
  - intros m m' Hmm IH k k' Hk Hk' d c HF ρ.
    destruct (NatRel_escape Hmm) as (Hm & _ & _). pose proof (kw_tm ρ Hm) as Hmρ. rewrite kty_tyNat in Hmρ.
    pose proof (fin_stab_ty' (tmred_eq _ _ _ _ _ _ _ Hk) HF) as HF1.
    pose proof (dvecMv_wf ge_typeof ge_notV ge_compt Hm HF1) as HFmv. rewrite iwiFamT_mv in HFmv.
    destruct (Nρ ρ) as (NXρ & NAρ & NNρ & NDρ & NOρ & NCρ).
    apply (IWVecQ_succ (kw_lwf ρ HwL) NXρ NAρ NNρ NDρ NOρ NCρ (HFρ _ _ _ ρ (tmred_wf _ _ _ _ _ _ _ Hk) HF)
             (IWiCan_comp ρ HCan) Hmρ (kw_tmred_succ Hk ρ) (kw_tmred_succ Hk' ρ) (NatRel_kw ρ _ _ Hmm)).
    intros ρ'. rewrite <- (ktyl_posMvT ρ), <- (ktmll_posMv2 ρ).
    pose proof (IH (posMvT m d) (posMv2 m c) HFmv (kw_comp ρ ρ')) as Y.
    rewrite kty_comp, kty_comp, ktml_comp, ktyll_comp, ktml_comp, ktmlll_comp, ktyl_comp, ktmll_comp, !ktm_comp in Y.
    exact Y.
  - intros ν ν' Hνν k k' Hk _ d c HF ρ. pose proof (kw_tmred ρ Hk) as Hkρ. rewrite kty_tyNat in Hkρ.
    exact (IWVecQ_ne (kw_lwf ρ HwL) (HFρ _ _ _ ρ (tmred_wf _ _ _ _ _ _ _ Hk) HF) Hkρ
             (gne_tm_whne_l (kw_gne_tm ρ Hνν))).
Qed.

(** Spine to relation at the spine's own world, from the spine in every
    world at an argument relation as above. *)
Lemma LR_of_DVecWSp_own {d c k k' cs cs'} (HΔ : [ G ; Δ ⊢g ]) : NatRel G Δ k k' -> nfty d -> nftm c ->
  [ G ; Δ ,, tyFin k @ lzero ⊢g iwiFamT l lp li X A N D Ot C d c @ iwiL l lp li ] ->
  nftm cs -> nftm cs' ->
  (forall ρ : kwk G Δ, exists yR, YOk (kw_G ρ) (kw_Δ ρ) lp (ktyl ρ d) (ktm ρ k) (ktm ρ k') yR /\
     DVecWSp (kw_G ρ) (kw_Δ ρ) l lp li (kty ρ X) (kty ρ A) (ktml ρ N) (ktyll ρ D) (ktml ρ Ot) (ktmlll ρ C)
       (fun ρ' => ix (kw_comp ρ ρ')) (fun ρ' => dm (kw_comp ρ ρ')) (fun ρ' => pd (kw_comp ρ ρ')) yR
       (ktyl ρ d) (ktmll ρ c) (ktm ρ k) (ktm ρ cs) (ktm ρ cs')) ->
  forall T' R, LogRel (iwiL l lp li) G Δ (tyDVec (iwiL l lp li) k (iwiFamT l lp li X A N D Ot C d c)) T'
                 (iwiL l lp li) R ->
  R cs cs'.
Proof using EL HCan HwL NA NC ND NN NO NX VL VN.
  intros Hkk Nd Nc HF Ncs Ncs' Hsp T' R H.
  destruct (NatRel_escape Hkk) as (Hk & Hk' & _). pose proof (wf_tm_nf Hk) as Nk. pose proof (wf_tm_nf Hk') as Nk'.
  pose proof (LR_of_DVecWSp_all _ _ Hkk d c HF (kid HΔ)) as Y. unfold IWVecQ in Y.
  rewrite (kty_kid HΔ _ NX), (kty_kid HΔ _ NA), (ktml_kid' HΔ _ NN), (ktyll_kid HΔ _ ND), (ktml_kid' HΔ _ NO),
    (ktmlll_kid HΔ _ NC), (ktyl_kid HΔ _ Nd), (ktmll_kid HΔ _ Nc), (ktm_kid HΔ _ Nk), (ktm_kid HΔ _ Nk') in Y.
  apply (Y T' R H cs cs'). split.
  - destruct (Hsp (kid HΔ)) as (yR & _ & Z). exists yR.
    rewrite (kty_kid HΔ _ NX), (kty_kid HΔ _ NA), (ktml_kid' HΔ _ NN), (ktyll_kid HΔ _ ND), (ktml_kid' HΔ _ NO),
      (ktmlll_kid HΔ _ NC), (ktyl_kid HΔ _ Nd), (ktmll_kid HΔ _ Nc), (ktm_kid HΔ _ Nk), (ktm_kid HΔ _ Ncs),
      (ktm_kid HΔ _ Ncs') in Z.
    exact Z.
  - intros ρ. destruct (Hsp (kw_comp (kid HΔ) ρ)) as (yR & Hy & Z). exists yR.
    rewrite ktyl_comp, !ktm_comp in Hy.
    rewrite kty_comp, kty_comp, ktml_comp, ktyll_comp, ktml_comp, ktmlll_comp, ktyl_comp, ktmll_comp, !ktm_comp in Z.
    rewrite (ktyl_kid HΔ _ Nd), (ktm_kid HΔ _ Nk), (ktm_kid HΔ _ Nk') in Hy.
    rewrite (kty_kid HΔ _ NX), (kty_kid HΔ _ NA), (ktml_kid' HΔ _ NN), (ktyll_kid HΔ _ ND), (ktml_kid' HΔ _ NO),
      (ktmlll_kid HΔ _ NC), (ktyl_kid HΔ _ Nd), (ktmll_kid HΔ _ Nc), (ktm_kid HΔ _ Nk), (ktm_kid HΔ _ Ncs),
      (ktm_kid HΔ _ Ncs') in Z.
    exact (conj Hy Z).
Qed.

End SpineK.

End S.
