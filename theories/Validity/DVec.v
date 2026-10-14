(** * Validity of [DVec] (M17_DESIGN.md, M17a)

    As [Vec] (M14a), [DVec] has no case of its own in the relation: at a
    length that reduces to [0] or [S k] a [DVec] type is related by its
    reduct's case ([Unit] or [Σ]), through the relation's closure under
    typed weak-head expansion; at a neutral length it is a neutral type.
    The relation is built by induction on the length's [NatRel]. Unlike
    [Vec]'s element type, the family moves along the recursion ([F] at the
    successor, [F[inr j]] at the predecessor), so the induction is
    generalized over a semantic family ([DFam]): in every Kripke world,
    indices related at [Fin] give related instances of the family. *)
From DeLaM.Validity Require Export Vec.
From DeLaM.Typing Require Import Inversion.
From DeLaM.Typing Require Export DVecEq.

Section DVec.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

Section KwSyntax.
Context {G : gctx} {Γ : ctx} (ρ : kwk G Γ).

Lemma kty_dvecHd n F :
  kty ρ (dvecHd n F) = (ktyl ρ F)[lsingle (tmInl lzero lzero (tyUnit lzero) (tyFin (ktm ρ n)) (tmTriv lzero))].
Proof. rewrite kty_single, ktm_inl, kty_tyUnit, kty_tyFin. unfold ktm. now rewrite gwa_triv. Qed.

Lemma ktyl_dvecMv n F i : nftm n ->
  (ktyl ρ (dvecMv n F))[lsingle i] = (ktyl ρ F)[lsingle (tmInr lzero lzero (tyUnit lzero) (tyFin (ktm ρ n)) i)].
Proof.
  intros Hn. rewrite <- dvecMv_single by apply ren_nf. f_equal.
  unfold dvecMv, ktyl, ktm. rewrite gwa_subst_ty, gwa_lsingle, lsingle_ren_ty, gwa_ren_ty.
  rewrite liftshift_lift_ty. f_equal. f_equal.
  unfold gwa; destruct (kw_γ ρ); cbn; f_equal; f_equal;
    change (ren_tm ?x ?r) with x⟨r⟩; rewrite ?shift_lift; try reflexivity.
  all: change (gren_tm ?x ?y) with x⟪y⟫; rewrite gren_ren, shift_lift; reflexivity.
Qed.

(** [Σ]'s codomain at the successor does not depend on the first component. *)
Lemma dvec_cod_single l n F a :
  (ktyl ρ (dvecTl l n F))[lsingle a] = kty ρ (tyDVec l n (dvecMv n F)).
Proof. rewrite dvecTl_eq, ktyl_shift, shift_single_ty; [reflexivity | unfold kty; apply ren_nf_ty]. Qed.

End KwSyntax.

(** ** Indices *)

Lemma LRtm_red_ty {l G Δ T T' W W' t t'} : LRtm l G Δ W W' t t' ->
  [ G ; Δ ⊢g T ⤳* W @ l ] -> [ G ; Δ ⊢g T' ⤳* W' @ l ] -> LRtm l G Δ T T' t t'.
Proof.
  intros (R & H & Ht) HT HT'. exists R; split; [|exact Ht].
  eapply LR_red_ty; [exact H | exact HT | exact HT'].
Qed.

Lemma LRtm_triv {G Δ} : [ G ; Δ ⊢g ] ->
  LRtm lzero G Δ (tyUnit lzero) (tyUnit lzero) (tmTriv lzero) (tmTriv lzero).
Proof.
  intros HΔ. apply (LRtm_unit (l := lzero) I).
  assert (Ht : [ G ; Δ ⊢g tmTriv lzero : tyUnit lzero @ lzero ])
    by (apply wf_triv; [exact ge_notV | now rewrite ge_typeof | exact I]).
  exists (tmTriv lzero), (tmTriv lzero).
  exact (conj (tmred_refl _ _ _ Ht) (conj (tmred_refl _ _ _ Ht) (conj (whnf_triv _) (whnf_triv _)))).
Qed.

(** The injections into a sum of related summands. *)
Lemma LRtm_inl_here {G Δ l1 l2 A A' B B' a a'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  LRty l1 G Δ A A' -> LRty l2 G Δ B B' -> LRtm l1 G Δ A A' a a' ->
  LRtm (lmax l1 l2) G Δ (tySum l1 l2 A B) (tySum l1 l2 A' B') (tmInl l1 l2 A B a) (tmInl l1 l2 A' B' a').
Proof.
  intros Hw1 Hw2 [RA HRA] [RB HRB] Xa.
  destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HA & _ & EA).
  destruct (escape_ty _ _ _ _ _ _ _ _ HRB) as (HB & _ & EB).
  pose proof (lequiv_refl _ _ Hw1) as Q1. pose proof (lequiv_refl _ _ Hw2) as Q2.
  pose proof (LRtm_geq Xa) as Ea.
  pose proof (geq_tm_sound (geq_tm_inl Q1 Q2 EA EB Ea)) as Dinl.
  eapply LRtm_of; [exact (LR_sum_here Hw1 Hw2 Q1 Q2 HA EA HB EB HRA HRB)|].
  exists (tmInl l1 l2 A B a), (tmInl l1 l2 A' B' a').
  refine (conj (tmred_refl _ _ _ (eqtm_wf_l ge_typeof Dinl))
           (conj (tmred_refl _ _ _ (eqtm_wf_r ge_typeof Dinl)) (conj (geq_tm_inl Q1 Q2 EA EB Ea) _))).
  apply sumnf_inl; [exact Q1 | exact Q2 | exact Q1 | exact Q2
                   | exact (geq_ty_trans EA (geq_ty_sym EA)) | exact EA
                   | exact (geq_ty_trans EB (geq_ty_sym EB)) | exact EB
                   | exact (LRtm_inv HRA Xa) ].
Qed.

Lemma LRtm_inr_here {G Δ l1 l2 A A' B B' b b'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  LRty l1 G Δ A A' -> LRty l2 G Δ B B' -> LRtm l2 G Δ B B' b b' ->
  LRtm (lmax l1 l2) G Δ (tySum l1 l2 A B) (tySum l1 l2 A' B') (tmInr l1 l2 A B b) (tmInr l1 l2 A' B' b').
Proof.
  intros Hw1 Hw2 [RA HRA] [RB HRB] Xb.
  destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HA & _ & EA).
  destruct (escape_ty _ _ _ _ _ _ _ _ HRB) as (HB & _ & EB).
  pose proof (lequiv_refl _ _ Hw1) as Q1. pose proof (lequiv_refl _ _ Hw2) as Q2.
  pose proof (LRtm_geq Xb) as Eb.
  pose proof (geq_tm_sound (geq_tm_inr Q1 Q2 EA EB Eb)) as Dinr.
  eapply LRtm_of; [exact (LR_sum_here Hw1 Hw2 Q1 Q2 HA EA HB EB HRA HRB)|].
  exists (tmInr l1 l2 A B b), (tmInr l1 l2 A' B' b').
  refine (conj (tmred_refl _ _ _ (eqtm_wf_l ge_typeof Dinr))
           (conj (tmred_refl _ _ _ (eqtm_wf_r ge_typeof Dinr)) (conj (geq_tm_inr Q1 Q2 EA EB Eb) _))).
  apply sumnf_inr; [exact Q1 | exact Q2 | exact Q1 | exact Q2
                   | exact (geq_ty_trans EA (geq_ty_sym EA)) | exact EA
                   | exact (geq_ty_trans EB (geq_ty_sym EB)) | exact EB
                   | exact (LRtm_inv HRB Xb) ].
Qed.

(** The lengths of related [Fin] types are typed. *)
Lemma LRty_fin_len {G Δ k k'} : LRty lzero G Δ (tyFin k) (tyFin k') ->
  [ G ; Δ ⊢g ] /\ [ G ; Δ ⊢g k : tyNat @ lzero ] /\ [ G ; Δ ⊢g k' : tyNat @ lzero ].
Proof.
  intros [R HR]. destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (HF & HF' & _).
  refine (conj (ctx_of_ty HF) (conj _ _)).
  - exact (proj2 (proj1 (inv_ty_fin HF))).
  - exact (proj2 (proj1 (inv_ty_fin HF'))).
Qed.

Lemma LRtm_fin_inl {G Δ k k'} : LRty lzero G Δ (tyFin k) (tyFin k') ->
  LRtm lzero G Δ (tyFin (succ k)) (tyFin (succ k'))
    (tmInl lzero lzero (tyUnit lzero) (tyFin k) (tmTriv lzero))
    (tmInl lzero lzero (tyUnit lzero) (tyFin k') (tmTriv lzero)).
Proof.
  intros HRB. destruct (LRty_fin_len HRB) as (HΔ & Hk & Hk').
  pose proof (LRtm_triv HΔ) as Xa.
  pose proof (LRtm_inl_here (l1 := lzero) (l2 := lzero) I I (LRtm_ty Xa) HRB Xa) as X.
  apply (fun H => LRtm_lconv H (lequiv_sym _ _ _ (lmax_idem (gL G) lzero I))) in X.
  exact (LRtm_red_ty X (tyred_fin_succ Hk) (tyred_fin_succ Hk')).
Qed.

Lemma LRtm_fin_inr {G Δ k k' i i'} : LRtm lzero G Δ (tyFin k) (tyFin k') i i' ->
  LRtm lzero G Δ (tyFin (succ k)) (tyFin (succ k'))
    (tmInr lzero lzero (tyUnit lzero) (tyFin k) i) (tmInr lzero lzero (tyUnit lzero) (tyFin k') i').
Proof.
  intros Xb. pose proof (LRtm_ty Xb) as HRB. destruct (LRty_fin_len HRB) as (HΔ & Hk & Hk').
  pose proof (LRtm_ty (LRtm_triv HΔ)) as HRA.
  pose proof (LRtm_inr_here (l1 := lzero) (l2 := lzero) I I HRA HRB Xb) as X.
  apply (fun H => LRtm_lconv H (lequiv_sym _ _ _ (lmax_idem (gL G) lzero I))) in X.
  exact (LRtm_red_ty X (tyred_fin_succ Hk) (tyred_fin_succ Hk')).
Qed.

(** ** The family

    Related families: in every world, indices related at [Fin] give
    related instances. *)

Definition DFam G Δ l m m' F F' : Prop := nfty F /\ nfty F' /\
  forall (ρ : kwk G Δ) i i',
    LRtm lzero (kw_G ρ) (kw_Δ ρ) (tyFin (ktm ρ m)) (tyFin (ktm ρ m')) i i' ->
    LRty l (kw_G ρ) (kw_Δ ρ) (ktyl ρ F)[lsingle i] (ktyl ρ F')[lsingle i'].

Lemma LRty_kw {l G Γ} (ρ : kwk G Γ) {T T'} :
  LRty l G Γ T T' -> LRty l (kw_G ρ) (kw_Δ ρ) (kty ρ T) (kty ρ T').
Proof. intros [R H]. destruct (LR_kwk _ _ _ _ _ _ _ H ρ) as (R' & HR' & _). now exists R'. Qed.

(** The family under the index's binder, at the bound variable. *)
Lemma DFam_escape {G Δ l m m' F F'} : DFam G Δ l m m' F F' ->
  LRty lzero G Δ (tyFin m) (tyFin m') ->
  [ G ; Δ ,, tyFin m @ lzero ⊢g F @ l ] /\ [ G ; Δ ,, tyFin m @ lzero ⊢g F' @ l ] /\
  [ G ; Δ ,, tyFin m @ lzero ⊢ F ≈ F' @ l ].
Proof.
  intros (NF & NF' & HF) HRm.
  pose proof HRm as [Rm HRm0].
  destruct (escape_ty _ _ _ _ _ _ _ _ HRm0) as (Hm & _ & _).
  assert (HΔm : [ G ; Δ ,, tyFin m @ lzero ⊢g ]) by (apply ext_wf_g; [exact Hm | exact I]).
  assert (Hw1 : wk1 : (Δ ,, tyFin m @ lzero) ≤ Δ) by (constructor; constructor).
  pose proof (LRty_kw (kw_loc wk1 Hw1 HΔm) HRm) as HR1.
  assert (h0 : LRtm lzero G (Δ ,, tyFin m @ lzero) (tyFin m)⟨↑⟩ (tyFin m')⟨↑⟩ (var 0) (var 0)).
  { unfold kty, kw_loc in HR1; cbn [kw_G kw_Δ kw_γ kw_r gwa] in HR1.
    change (wk_ren wk1) with ↑ in HR1. apply var0_LRtm; [exact HR1 | exact HΔm]. }
  pose proof (HF (kw_loc wk1 Hw1 HΔm) (var 0) (var 0)) as K.
  unfold ktyl, ktm, kw_loc in K; cbn [kw_G kw_Δ kw_γ kw_r gwa] in K.
  change (wk_ren wk1) with ↑ in K.
  destruct (K h0) as [R HR].
  rewrite !liftshift_single_var_ty in HR by assumption.
  exact (escape_ty _ _ _ _ _ _ _ _ HR).
Qed.

Lemma DFam_red {G Δ l m m' w w' F F'} : DFam G Δ l m m' F F' ->
  [ G ; Δ ⊢g m ⤳* w : tyNat @ lzero ] -> [ G ; Δ ⊢g m' ⤳* w' : tyNat @ lzero ] ->
  DFam G Δ l w w' F F'.
Proof.
  intros (NF & NF' & HF) Hm Hm'. refine (conj NF (conj NF' _)).
  intros ρ i i' Hi. apply HF.
  pose proof (kw_tmred ρ Hm) as Hρm. pose proof (kw_tmred ρ Hm') as Hρm'.
  rewrite kty_tyNat in Hρm, Hρm'.
  exact (LRtm_red_ty Hi (tyred_fin Hρm) (tyred_fin Hρm')).
Qed.

(** The tail's family is related at the predecessor. *)
Lemma DFam_succ {G Δ l k k' F F'} : nftm k -> nftm k' ->
  DFam G Δ l (succ k) (succ k') F F' -> DFam G Δ l k k' (dvecMv k F) (dvecMv k' F').
Proof.
  intros Nk Nk' (NF & NF' & HF).
  assert (Nv : forall n, nftm (tmInr lzero lzero (tyUnit lzero) (tyFin n⟨↑⟩) (var 0))).
  { intros n. cbn [nftm nfty]. repeat split; apply ren_nf. }
  refine (conj _ (conj _ _)).
  - unfold dvecMv. apply subst_nf_ty; [apply ren_nf_ty | apply lk_lsingle, Nv].
  - unfold dvecMv. apply subst_nf_ty; [apply ren_nf_ty | apply lk_lsingle, Nv].
  - intros ρ i i' Hi. rewrite !ktyl_dvecMv by assumption.
    apply HF. rewrite !ktm_succ. exact (LRtm_fin_inr Hi).
Qed.

(** Canonical lengths are related. *)
Lemma NatRel_zero {G Δ} : [ G ; Δ ⊢g ] -> NatRel G Δ zero zero.
Proof.
  intros HΔ. assert (Hz : [ G ; Δ ⊢g zero : tyNat @ lzero ])
    by (apply wf_zero; [exact ge_notV | now rewrite ge_typeof]).
  econstructor; [apply tmred_refl, Hz | apply tmred_refl, Hz | now apply geq_tm_zero | constructor].
Qed.

Lemma NatRel_succ {G Δ t t'} : NatRel G Δ t t' -> NatRel G Δ (succ t) (succ t').
Proof.
  intros Ht. destruct (NatRel_escape Ht) as (H1 & H2 & H12). econstructor.
  - apply tmred_refl, wf_succ; [exact ge_notV | exact H1].
  - apply tmred_refl, wf_succ; [exact ge_notV | exact H2].
  - now apply geq_tm_succ.
  - now constructor.
Qed.

Lemma NatRel_ne {G Δ ν ν'} : [ G ; Δ ⊢ ν ~ ν' : tyNat @ lzero ] -> NatRel G Δ ν ν'.
Proof.
  intros Hνν. pose proof (geq_tm_sound (gne_tm_geq Hνν)) as Hν. econstructor.
  - apply tmred_refl, (eqtm_wf_l ge_typeof Hν).
  - apply tmred_refl, (eqtm_wf_r ge_typeof Hν).
  - exact (gne_tm_geq Hνν).
  - now constructor.
Qed.

Section DVecLR.
Context {G : gctx} {Δ : ctx} {l l' : lvl} (HΔ : [ G ; Δ ⊢g ])
  (Hw : lwf (gL G) l) (Hl : lequiv (gL G) l l').

(** The family's typings, the right one moved to its own length. *)
Lemma DFam_typed {m m' F F'} : DFam G Δ l m m' F F' -> NatRel G Δ m m' ->
  [ G ; Δ ,, tyFin m @ lzero ⊢g F @ l ] /\ [ G ; Δ ,, tyFin m' @ lzero ⊢g F' @ l' ] /\
  [ G ; Δ ,, tyFin m @ lzero ⊢ F ≈ F' @ l ].
Proof.
  intros HF Hm. destruct (NatRel_escape Hm) as (_ & Hm' & Hmm).
  destruct (DFam_escape HF (LR_fin_nat HΔ Hm)) as (HF0 & HF0' & HFF).
  refine (conj HF0 (conj _ HFF)).
  apply (wft_lconv _ _ _ _ l' l); [|now apply lequiv_sym].
  eapply (stab_ty ge_typeof); [| apply (lequiv_refl _ lzero I) | |exact HF0'].
  - apply eqty_fin; [exact ge_notV | exact (geq_tm_sound Hmm)].
  - apply ext_wf_g; [apply wft_fin; [exact ge_notV | exact Hm'] | exact I].
Qed.

(** At a successor: [Σ] over the head's instance, with [DVec] at the
    predecessor (related at [Δ]) in every world. *)
Lemma LR_dvec_sig {k k' F F' T T'} : NatRel G Δ k k' -> DFam G Δ l (succ k) (succ k') F F' ->
  LRty l G Δ (tyDVec l k (dvecMv k F)) (tyDVec l' k' (dvecMv k' F')) ->
  [ G ; Δ ⊢g T ⤳* tySig l l (dvecHd k F) (dvecTl l k F) @ l ] ->
  [ G ; Δ ⊢g T' ⤳* tySig l' l' (dvecHd k' F') (dvecTl l' k' F') @ l ] -> LRty l G Δ T T'.
Proof.
  intros Hk HF [RV HRV] HT HT'. pose proof HF as (NF & NF' & HF0).
  destruct (NatRel_escape Hk) as (Hk0 & Hk0' & _).
  pose proof (dnftm_nftm _ (wf_tm_dnf Hk0)) as Nk. pose proof (dnftm_nftm _ (wf_tm_dnf Hk0')) as Nk'.
  destruct (escape_ty _ _ _ _ _ _ _ _ HRV) as (HV & HV' & HVV).
  (* the head, in every world *)
  assert (HD : forall ρ : kwk G Δ,
             LRty l (kw_G ρ) (kw_Δ ρ) (kty ρ (dvecHd k F)) (kty ρ (dvecHd k' F'))).
  { intros ρ. rewrite !kty_dvecHd. apply HF0. rewrite !ktm_succ. apply LRtm_fin_inl.
    exact (LR_fin_nat (kw_ctx ρ) (NatRel_kw ρ _ _ Hk)). }
  (* the head at [Δ] *)
  pose proof (eqty_wf_r ge_typeof (tyred_eq _ _ _ _ _ _ HT)) as HS.
  destruct (inv_ty_sig HS) as ((_ & _ & _ & HA0 & _) & _).
  pose proof (eqty_wf_r ge_typeof (tyred_eq _ _ _ _ _ _ HT')) as HS'.
  destruct (inv_ty_sig HS') as ((_ & _ & _ & HA0' & _) & _).
  pose proof (HD (kw_loc wk_id (wkwf_id Δ) HΔ)) as [RA HRA].
  unfold kty, kw_loc in HRA; cbn [kw_G kw_Δ kw_γ kw_r gwa wk_ren] in HRA.
  rewrite !ren_id_ty in HRA by (eapply wf_ty_nf; eassumption).
  destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HA & HA' & HAA).
  assert (HΔA : [ G ; Δ ,, dvecHd k F @ l ⊢g ]) by now apply ext_wf_g.
  assert (HΔA' : [ G ; Δ ,, dvecHd k' F' @ l ⊢g ]) by now apply ext_wf_g.
  set (domR := fun ρ : kwk G Δ =>
         LRrel (lmeasure l) (kw_G ρ) (kw_Δ ρ) (kty ρ (dvecHd k F)) (kty ρ (dvecHd k' F')) l).
  set (codR := fun (ρ : kwk G Δ) a a' (_ : domR ρ a a') =>
         LRrel (lmeasure l) (kw_G ρ) (kw_Δ ρ) (ktyl ρ (dvecTl l k F))[lsingle a]
           (ktyl ρ (dvecTl l' k' F'))[lsingle a'] l).
  eexists. eapply (LRsig _ _ _ _ _ _ _ l l l' l' (dvecHd k F) (dvecTl l k F) (dvecHd k' F') (dvecTl l' k' F')
                     domR codR); [split | | | apply releq_refl].
  - apply lequiv_sym, lmax_idem, Hw.
  - now apply lequiv_sym.
  - now apply lequiv_sym.
  - exact Hw.
  - exact Hw.
  - exact HT.
  - exact HT'.
  - exact HA.
  - exact HA'.
  - rewrite dvecTl_eq. eapply wk1_ty_g; [rewrite ge_typeof; exact HΔA | exact HV].
  - rewrite dvecTl_eq. eapply wk1_ty_g; [rewrite ge_typeof; exact HΔA' | exact HV'].
  - exact HAA.
  - rewrite !dvecTl_eq. exact (geq_ty_wk (wkr_shift1 _ _ _) HΔA HVV).
  - intros ρ. destruct (HD ρ) as [R' HR']. exact (LR_canon _ _ _ _ _ _ _ HR').
  - intros ρ a a' ha. unfold codR. rewrite !dvec_cod_single.
    destruct (LR_kwk _ _ _ _ _ _ _ HRV ρ) as (R' & HR' & _).
    exact (LR_canon _ _ _ _ _ _ _ HR').
Qed.

Lemma LR_dvec_nat {m m'} : NatRel G Δ m m' -> forall F F', DFam G Δ l m m' F F' ->
  LRty l G Δ (tyDVec l m F) (tyDVec l' m' F').
Proof.
  pose proof (lequiv_wf_r _ _ _ Hl) as Hw'.
  revert m m'.
  apply (NatRel_mut G Δ
           (fun m m' _ => forall F F', DFam G Δ l m m' F F' -> LRty l G Δ (tyDVec l m F) (tyDVec l' m' F'))
           (fun w w' _ => forall F F', DFam G Δ l w w' F F' -> LRty l G Δ (tyDVec l w F) (tyDVec l' w' F'))).
  - intros t t' w w' Ht Ht' Heq Hnf IH F F' HF.
    destruct (DFam_typed HF (natrel _ _ _ _ _ _ Ht Ht' Heq Hnf)) as (HF1 & HF1' & _).
    destruct (IH F F' (DFam_red HF Ht Ht')) as [R HR]. exists R.
    eapply LR_red_ty; [exact HR | exact (tyred_dvec Hw HF1 Ht) |].
    exact (tyred_lconv _ _ _ _ (tyred_dvec Hw' HF1' Ht') Hl).
  - intros F F' HF.
    destruct (DFam_typed HF (NatRel_zero HΔ)) as (HF1 & HF1' & _).
    apply (LR_unit_red (l' := l')); [exact Hw | exact Hl | exact (tyred_dvec_zero Hw HF1) |].
    exact (tyred_lconv _ _ _ _ (tyred_dvec_zero Hw' HF1') Hl).
  - intros t t' Ht IH F F' HF. destruct (NatRel_escape Ht) as (Hk & Hk' & _).
    pose proof (dnftm_nftm _ (wf_tm_dnf Hk)) as Nk. pose proof (dnftm_nftm _ (wf_tm_dnf Hk')) as Nk'.
    destruct (DFam_typed HF (NatRel_succ Ht)) as (HF1 & HF1' & _).
    apply (LR_dvec_sig Ht HF (IH _ _ (DFam_succ Nk Nk' HF))); [exact (tyred_dvec_succ Hw HF1 Hk) |].
    exact (tyred_lconv _ _ _ _ (tyred_dvec_succ Hw' HF1' Hk') Hl).
  - intros ν ν' Hνν F F' HF.
    pose proof (geq_tm_sound (gne_tm_geq Hνν)) as Hν.
    destruct (DFam_typed HF (NatRel_ne Hνν)) as (HF1 & HF1' & HFF).
    exists (NeRel G Δ (tyDVec l ν F) (tyDVec l' ν' F') l).
    eapply LRne.
    + apply tyred_refl, wft_dvec; [exact (compt_notV _ ge_compt) | exact Hw | exact (eqtm_wf_l ge_typeof Hν) | exact HF1].
    + eapply tyred_lconv; [|exact Hl].
      apply tyred_refl, wft_dvec; [exact (compt_notV _ ge_compt) | exact Hw' | exact (eqtm_wf_r ge_typeof Hν) | exact HF1'].
    + exact (gne_ty_dvec Hl Hνν HF1 HFF).
    + apply releq_refl.
Qed.

End DVecLR.

(** ** The rules *)

Section DVecV.
Context {G : gctx} {Γ : ctx} {l : lvl} {n : tm} {F F' : ty}
  (Vn : VTm G Γ n n tyNat lzero) (VF : VTyG G (Γ ,, tyFin n @ lzero) F F' l).

(** The family under a related substitution: typed, and related as a
    family whatever the right length is. *)
Lemma V_fam_typed {Δ d d'} : SubRel G Γ Δ d d' ->
  [ G ; Δ ,, tyFin n[d] @ lzero ⊢g F[llift d] @ l ] /\ nfty F[llift d] /\ nfty F'[llift d'].
Proof using EL VL VN Vn VF.
  intros Hd. pose proof (V_fin Vn) as VFin.
  destruct (VFin _ _ _ Hd) as [R HR].
  destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (HFd & _ & _).
  assert (Hlift : SubRel G (Γ ,, tyFin n @ lzero) (Δ ,, (tyFin n)[d] @ lzero) (llift d) (llift d'))
    by (apply SubRel_lift; [exact Hd | exact (VTy_refl_l VFin) | exact HFd | exact I]).
  destruct (VTyG_loc VF _ _ _ Hlift) as [R' HR'].
  destruct (escape_ty _ _ _ _ _ _ _ _ HR') as (H1 & H2 & _).
  refine (conj H1 (conj _ _)); eapply wf_ty_nf; eassumption.
Qed.

Lemma V_dfam {Δ d d' m'} : SubRel G Γ Δ d d' ->
  DFam G Δ l n[d] m' F[llift d] F'[llift d'].
Proof using EL VL VN Vn VF.
  intros Hd. destruct (V_fam_typed Hd) as (_ & NF & NF').
  refine (conj NF (conj NF' _)). intros ρ i i' Hi.
  pose proof (SubRel_kw _ _ _ ρ _ _ Hd) as Hdρ.
  pose proof (Vn _ _ _ Hd) as Hn. rewrite subst_tyNat in Hn. apply LRtm_nat in Hn.
  pose proof (LR_fin_nat (kw_ctx ρ) (NatRel_kw ρ _ _ Hn)) as HRF.
  assert (Ha : LRtm lzero (kw_G ρ) (kw_Δ ρ) (tyFin n)⟦kw_γ ρ⟧[kwsub ρ d] (tyFin n)⟦kw_γ ρ⟧[kwsub ρ d'] i i').
  { rewrite <- !kty_subst, !subst_tyFin, !kty_tyFin. exact (LRtm_irrel_r Hi HRF). }
  pose proof (VF _ _ (kw_gok ρ)) as VFρ. rewrite gwa_cext in VFρ.
  pose proof (VFρ _ _ _ (SubRel_cons Hdρ Ha)) as HR.
  now rewrite <- !ktyl_subst_single in HR.
Qed.

End DVecV.

Lemma V_dvec {G Γ l l' n n' F F'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTm G Γ n n' tyNat lzero -> VTyG G (Γ ,, tyFin n @ lzero) F F' l ->
  VTy G Γ (tyDVec l n F) (tyDVec l' n' F') l.
Proof.
  intros Hw Hl Vn VF Δ d d' Hd. rewrite !subst_tyDVec.
  pose proof (Vn _ _ _ Hd) as Hn. rewrite subst_tyNat in Hn. apply LRtm_nat in Hn.
  exact (LR_dvec_nat (SubRel_ctx Hd) Hw Hl Hn _ _ (V_dfam (VTm_trans Vn (VTm_sym Vn)) VF Hd)).
Qed.

Lemma V_dvec_zero {G Γ l l' F F'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTyG G (Γ ,, tyFin zero @ lzero) F F' l -> VTy G Γ (tyDVec l zero F) (tyUnit l') l.
Proof.
  intros Hw Hl VF Δ d d' Hd. rewrite subst_tyDVec, subst_zero, subst_tyUnit.
  destruct (V_fam_typed V_zero VF Hd) as (HF & _ & _). rewrite subst_zero in HF.
  apply (LR_unit_red (l' := l')); [exact Hw | exact Hl | exact (tyred_dvec_zero Hw HF) |].
  apply tyred_refl, wft_unit_g; [exact (SubRel_ctx Hd) | exact Hl].
Qed.

Lemma V_dvec_succ {G Γ l l' n n' F F'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTm G Γ n n' tyNat lzero -> VTyG G (Γ ,, tyFin (succ n) @ lzero) F F' l ->
  VTy G Γ (tyDVec l (succ n) F) (tySig l' l' (dvecHd n' F') (dvecTl l' n' F')) l.
Proof.
  intros Hw Hl Vn VF Δ d d' Hd. pose proof (SubRel_ctx Hd) as HΔ.
  destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  rewrite subst_tyDVec, subst_succ, subst_tySig, dvecHd_subst, dvecTl_subst by assumption.
  pose proof (Vn _ _ _ Hd) as Hn. rewrite subst_tyNat in Hn. apply LRtm_nat in Hn.
  destruct (NatRel_escape Hn) as (Hk & Hk' & _).
  pose proof (dnftm_nftm _ (wf_tm_dnf Hk)) as Nk. pose proof (dnftm_nftm _ (wf_tm_dnf Hk')) as Nk'.
  pose proof (V_succ (VTm_trans Vn (VTm_sym Vn))) as Vsn.
  destruct (V_fam_typed Vsn VF Hd) as (HF & _ & _). rewrite subst_succ in HF.
  pose proof (V_dfam (m' := succ n'[d']) Vsn VF Hd) as DF. rewrite subst_succ in DF.
  destruct (DFam_typed HΔ Hl DF (NatRel_succ Hn)) as (_ & HF1' & _).
  pose proof (lequiv_wf_r _ _ _ Hl) as Hw'.
  apply (LR_dvec_sig HΔ Hw Hl Hn DF (LR_dvec_nat HΔ Hw Hl Hn _ _ (DFam_succ Nk Nk' DF)));
    [exact (tyred_dvec_succ Hw HF Hk) |].
  eapply tyred_lconv; [|exact Hl].
  apply tyred_refl. exact (eqty_wf_r ge_typeof (tyred_eq _ _ _ _ _ _ (tyred_dvec_succ Hw' HF1' Hk'))).
Qed.

End DVec.
