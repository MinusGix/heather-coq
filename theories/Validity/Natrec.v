(** * Validity of the natural-number eliminator *)
From DeLaM.Validity Require Export PiComp.

Section Natrec.
Context `{E : GenericEq} `{EL : !GenericEqLaws}.

(** ** Syntax *)

Lemma lsucc_cons2_ty (M : ty) d n r :
  LK nftm d -> M[lsucc][lcons (lcons d n) r] = M[llift d][lsingle (succ n)].
Proof.
  intros Hd. rewrite lift_single_ty by exact Hd.
  apply subst_subst_ty. intros [|m]; cbn; auto. replace (m + 2) with (S (S m)) by lia. reflexivity.
Qed.

Lemma lift2_single2 (z : tm) d n r :
  LK nftm d -> z[llift (llift d)][lsingle2 n r] = z[lcons (lcons d n) r].
Proof.
  intros Hd. apply subst_subst. intros [|[|m]].
  - rewrite !llk_llift. reflexivity.
  - rewrite !llk_llift. change (ren_tm ?x ?r) with x⟨r⟩. reflexivity.
  - rewrite !llk_llift. change (ren_tm (ren_tm ?x ?r) ?r') with x⟨r⟩⟨r'⟩.
    cbn [llk]. rewrite shift2_single2 by apply Hd. reflexivity.
Qed.

(** ** Changing either type of a term relation to a related one *)

Lemma LRtm_conv_l {l G Γ T T' T2 t t'} :
  LRtm l G Γ T T' t t' -> LRty l G Γ T2 T -> LRtm l G Γ T2 T' t t'.
Proof.
  intros (R & H & Ht) [R2 H2].
  destruct (LR_trans _ _ _ _ _ _ _ H2 _ _ H) as [H3 Hc].
  pose proof (LR_refl_l _ _ _ _ _ _ _ H) as HTT.
  pose proof (LR_irrel_left _ _ _ _ _ _ _ _ _ H2 HTT) as E2.
  exists R2; split; [exact H3|].
  apply (Hc t t t'); [apply E2, (LR_tm_refl_l _ _ _ _ _ _ _ _ _ H Ht) | exact Ht].
Qed.

Lemma LRtm_conv_r {l G Γ T T' T2 t t'} :
  LRtm l G Γ T T' t t' -> LRty l G Γ T' T2 -> LRtm l G Γ T T2 t t'.
Proof.
  intros (R & H & Ht) [R2 H2].
  exists R; split; [exact (proj1 (LR_trans _ _ _ _ _ _ _ H _ _ H2)) | exact Ht].
Qed.

(** ** Natural numbers: reflexivity *)

Lemma NatRel_refl_l G Γ : forall t t', NatRel G Γ t t' -> NatRel G Γ t t.
Proof.
  apply (NatRel_mut G Γ (fun t t' _ => NatRel G Γ t t) (fun w w' _ => NatNf G Γ w w)).
  - intros t t' w w' Hw Hw' Heq _ IH.
    econstructor; [exact Hw | exact Hw | eapply geq_tm_trans; [exact Heq | now apply geq_tm_sym] | exact IH].
  - constructor.
  - intros; now constructor.
  - intros ν ν' H; constructor. eapply gne_tm_trans; [exact H | now apply gne_tm_sym].
Qed.

Lemma NatRel_refl_r {G Γ t t'} : NatRel G Γ t t' -> NatRel G Γ t' t'.
Proof. intros H; exact (NatRel_refl_l _ _ _ _ (NatRel_sym _ _ _ _ H)). Qed.

(** A natural number is related to its normal form. *)
Lemma NatRel_to_nf {G Γ t w w'} :
  [ G ; Γ ⊢g t ⤳* w : tyNat @ lzero ] -> [ G ; Γ ⊢ w ≈ w' : tyNat @ lzero ] -> NatNf G Γ w w' ->
  NatRel G Γ t w.
Proof.
  intros Hw Heq Hnf.
  assert (Hww : NatRel G Γ w w).
  { assert (Hnf0 : NatRel G Γ w w').
    { econstructor; [| |exact Heq|exact Hnf].
      - apply tmred_refl. exact (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hw)).
      - apply tmred_refl. exact (eqtm_wf_r ge_typeof (geq_tm_sound Heq)). }
    exact (NatRel_refl_l _ _ _ _ Hnf0). }
  inversion Hww as [? ? w1 w2 Hw1 Hw2 Heq12 Hnf12]; subst.
  econstructor; [exact (tmred_trans _ _ _ _ _ Hw Hw1) | exact Hw2 | exact Heq12 | exact Hnf12].
Qed.

(** ** Typed reductions of the eliminator *)

Section NatrecRed.
Context {G : gctx} {Δ : ctx} {l : lvl} {M : ty} {s z : tm}
  (Hwl : lwf (gL G) l) (HM : [ G ; Δ ,, tyNat @ lzero ⊢g M @ l ])
  (Hs : [ G ; Δ ⊢g s : M[lsingle zero] @ l ])
  (Hz : [ G ; Δ ,, tyNat @ lzero ,, M @ l ⊢g z : M[lsucc] @ l ]).

Lemma wf_natrec_g {n} : [ G ; Δ ⊢g n : tyNat @ lzero ] ->
  [ G ; Δ ⊢g natrec l M s z n : M[lsingle n] @ l ].
Proof. intros; apply wf_natrec; auto using ge_notV. Qed.

Lemma tmred_natrec_cong {n w} : [ G ; Δ ⊢g n ⤳* w : tyNat @ lzero ] ->
  [ G ; Δ ⊢g natrec l M s z n ⤳* natrec l M s z w : M[lsingle n] @ l ].
Proof.
  intros [Hn Hr Heq]. split.
  - now apply wf_natrec_g.
  - now apply reds_natrec.
  - apply eqtm_natrec; auto using ge_notV, lequiv_refl, eqty_refl, eqtm_refl.
Qed.

Lemma tmred_natrec_zero : [ G ; Δ ⊢g natrec l M s z zero ⤳* s : M[lsingle zero] @ l ].
Proof.
  split.
  - apply wf_natrec_g, wf_zero; [exact ge_notV | rewrite ge_typeof; eapply ctx_of_tm, Hs].
  - econstructor; [constructor | constructor].
  - apply eqtm_natrec_zero; auto using ge_compt.
Qed.

Lemma tmred_natrec_succ {n} : [ G ; Δ ⊢g n : tyNat @ lzero ] ->
  [ G ; Δ ⊢g natrec l M s z (succ n) ⤳* z[lsingle2 n (natrec l M s z n)] : M[lsingle (succ n)] @ l ].
Proof.
  intros Hn. split.
  - apply wf_natrec_g, wf_succ; auto using ge_notV.
  - econstructor; [constructor | constructor].
  - apply eqtm_natrec_succ; auto using ge_compt.
Qed.

End NatrecRed.

(** ** Generic helpers *)

Lemma NatNf_sym G Γ : forall w w', NatNf G Γ w w' -> NatNf G Γ w' w.
Proof.
  apply (NatNf_mut G Γ (fun t t' _ => NatRel G Γ t' t) (fun t t' _ => NatNf G Γ t' t)).
  - intros t t' w w' Hw Hw' Heq _ IH. econstructor; eauto using geq_tm_sym.
  - constructor.
  - intros; now constructor.
  - intros; constructor; now apply gne_tm_sym.
Qed.

Lemma LRtm_geq {l G Γ T T' t t'} : LRtm l G Γ T T' t t' -> [ G ; Γ ⊢ t ≈ t' : T @ l ].
Proof. intros (R & H & Ht). exact (proj2 (proj2 (escape_tm _ _ _ _ _ _ _ _ H _ _ Ht))). Qed.

(** Anti-reduction on both sides, and on the left only. *)
Lemma LRtm_red {l G Γ T T' t t' u u'} :
  LRtm l G Γ T T' u u' -> [ G ; Γ ⊢g t ⤳* u : T @ l ] -> [ G ; Γ ⊢g t' ⤳* u' : T' @ l ] ->
  LRtm l G Γ T T' t t'.
Proof.
  intros (R & H & Hu) Ht Ht'. exists R; split; [exact H|].
  exact (LR_red_tm _ _ _ _ _ _ _ _ H _ _ _ _ Hu Ht Ht').
Qed.

Lemma LRtm_red_l {l G Γ T T' t u u'} :
  LRtm l G Γ T T' u u' -> [ G ; Γ ⊢g t ⤳* u : T @ l ] -> LRtm l G Γ T T' t u'.
Proof.
  intros Hu Ht. eapply LRtm_red; [exact Hu | exact Ht|]. apply tmred_refl.
  destruct Hu as (R & H & Hu). destruct (escape_ty _ _ _ _ _ _ _ _ H) as (_ & _ & HTT).
  destruct (escape_tm _ _ _ _ _ _ _ _ H _ _ Hu) as (_ & Hu' & _).
  eapply wf_conv; [exact Hu' | rewrite ge_typeof; apply geq_ty_sound, geq_ty_sym, HTT].
Qed.

Lemma VTy_nat_at {G Γ Δ A B l e e' n n'} :
  VTy G (Γ ,, tyNat @ lzero) A B l -> SubRel G Γ Δ e e' -> NatRel G Δ n n' ->
  LRty l G Δ A[llift e][lsingle n] B[llift e'][lsingle n'].
Proof.
  intros V He Hn. destruct (SubRel_nf _ _ _ _ _ He) as [Ne Ne'].
  rewrite !lift_single_ty by assumption.
  apply V, SubRel_cons; [exact He | exact (proj2 LRtm_nat Hn)].
Qed.

Lemma single_zero_subst_ty (M : ty) d : LK nftm d -> M[lsingle zero][d] = M[llift d][lsingle zero].
Proof. intros Hd. rewrite single_subst_ty by exact Hd. now push_subst. Qed.

Lemma natrec_prems_subst {G Γ Δ d l M s z} :
  lsub_wf G ge_layer Δ d Γ -> lwf (gL G) l ->
  [ G ; Γ ,, tyNat @ lzero ⊢g M @ l ] -> [ G ; Γ ⊢g s : M[lsingle zero] @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢g z : M[lsucc] @ l ] ->
  [ G ; Δ ,, tyNat @ lzero ⊢g M[llift d] @ l ] /\
  [ G ; Δ ⊢g s[d] : M[llift d][lsingle zero] @ l ] /\
  [ G ; Δ ,, tyNat @ lzero ,, M[llift d] @ l ⊢g z[llift (llift d)] : M[llift d][lsucc] @ l ].
Proof.
  intros Hd Hwl HM Hs Hz. pose proof (lsub_wf_nf Hd) as Nd.
  assert (HN : [ G ; Δ ⊢g tyNat @ lzero ])
    by (apply wft_nat; [exact ge_notV | exact (lsub_wf_ctx Hd)]).
  assert (Hd1 : lsub_wf G ge_layer (Δ ,, tyNat @ lzero) (llift d) (Γ ,, tyNat @ lzero))
    by (eapply (lsub_wf_lift' _ _ ge_typeof); [exact Hd | exact HN | exact I | reflexivity]).
  pose proof (wf_ty_subst ge_typeof HM Hd1) as HMd.
  assert (Hd2 : lsub_wf G ge_layer (Δ ,, tyNat @ lzero ,, M[llift d] @ l) (llift (llift d))
                  (Γ ,, tyNat @ lzero ,, M @ l))
    by (apply (lsub_wf_lift _ _ ge_typeof); assumption).
  refine (conj HMd (conj _ _)).
  - rewrite <- single_zero_subst_ty by exact Nd. exact (wf_tm_subst ge_typeof Hs Hd).
  - rewrite <- lsucc_subst_ty. exact (wf_tm_subst ge_typeof Hz Hd2).
Qed.

(** ** The core lemma: related eliminations at related naturals *)

Section NatrecCore.
Context {G : gctx} {Γ : ctx} {l l' : lvl} {M M' : ty} {s s' z z' : tm}
  (Hwl : lwf (gL G) l) (Hll : lequiv (gL G) l l')
  (HM : [ G ; Γ ,, tyNat @ lzero ⊢g M @ l ]) (HM' : [ G ; Γ ,, tyNat @ lzero ⊢g M' @ l' ])
  (Hs : [ G ; Γ ⊢g s : M[lsingle zero] @ l ]) (Hs' : [ G ; Γ ⊢g s' : M'[lsingle zero] @ l' ])
  (Hz : [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢g z : M[lsucc] @ l ])
  (Hz' : [ G ; Γ ,, tyNat @ lzero ,, M' @ l' ⊢g z' : M'[lsucc] @ l' ])
  (VM : VTy G (Γ ,, tyNat @ lzero) M M' l)
  (Vs : VTm G Γ s s' M[lsingle zero] l)
  (Vz : VTm G (Γ ,, tyNat @ lzero ,, M @ l) z z' M[lsucc] l).

Let NR d n := natrec l M[llift d] s[d] z[llift (llift d)] n.
Let NR' d n := natrec l' M'[llift d] s'[d] z'[llift (llift d)] n.

(** The step case, before converting the types. *)
Lemma natrec_step {Δ d d' t t'} : SubRel G Γ Δ d d' -> NatRel G Δ t t' ->
  LRtm l G Δ M[llift d][lsingle t] M'[llift d'][lsingle t'] (NR d t) (NR' d' t') ->
  LRtm l G Δ M[llift d][lsingle (succ t)] M[llift d'][lsingle (succ t')]
    z[llift (llift d)][lsingle2 t (NR d t)] z'[llift (llift d')][lsingle2 t' (NR' d' t')].
Proof.
  intros Hd Htt IH. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  pose proof (LRtm_irrel_r IH (VTy_nat_at (VTy_refl_l VM) Hd Htt)) as Y.
  rewrite !lift_single_ty in Y by assumption.
  pose proof (Vz _ _ _ (SubRel_cons (SubRel_cons (A := tyNat) Hd (proj2 LRtm_nat Htt)) Y)) as Z.
  rewrite !lsucc_cons2_ty, <- !lift2_single2 in Z by assumption. exact Z.
Qed.

Lemma natrec_core {Δ d d'} : SubRel G Γ Δ d d' -> forall n n', NatRel G Δ n n' ->
  LRtm l G Δ M[llift d][lsingle n] M'[llift d'][lsingle n'] (NR d n) (NR' d' n').
Proof.
  intros Hd. pose proof (SubRel_ctx Hd) as HΔ. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  pose proof (VTy_refl_l VM) as VMM. pose proof (VTy_refl_l (VTy_sym VM)) as VM'M'.
  destruct (natrec_prems_subst (SubRel_wf_l _ _ _ _ _ Hd) Hwl HM Hs Hz) as (HMd & Hsd & Hzd).
  destruct (natrec_prems_subst (SubRel_wf_r Hd) (lequiv_wf_r _ _ _ Hll) HM' Hs' Hz')
    as (HMd' & Hsd' & Hzd').
  (* the right-hand reductions, at level [l] *)
  assert (Rcong : forall n w, [ G ; Δ ⊢g n ⤳* w : tyNat @ lzero ] ->
            [ G ; Δ ⊢g NR' d' n ⤳* NR' d' w : M'[llift d'][lsingle n] @ l ])
    by (intros; eapply tmred_lconv; [apply tmred_natrec_cong; eauto using lequiv_wf_r | exact Hll]).
  apply (NatRel_mut G Δ
    (fun n n' _ => LRtm l G Δ M[llift d][lsingle n] M'[llift d'][lsingle n'] (NR d n) (NR' d' n'))
    (fun w w' _ => NatRel G Δ w w' ->
       LRtm l G Δ M[llift d][lsingle w] M'[llift d'][lsingle w'] (NR d w) (NR' d' w'))).
  - (* reduction to normal forms *)
    intros t t' w w' Hw Hw' Heq Hnf IH.
    assert (Hww : NatRel G Δ w w').
    { econstructor; [| |exact Heq|exact Hnf]; apply tmred_refl.
      - exact (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hw)).
      - exact (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hw')). }
    pose proof (NatRel_to_nf Hw Heq Hnf) as Htw.
    pose proof (NatRel_to_nf Hw' (geq_tm_sym Heq) (NatNf_sym _ _ _ _ Hnf)) as Ht'w'.
    pose proof (LRtm_conv_l (IH Hww) (VTy_nat_at VMM (SubRel_refl_l Hd) Htw)) as X.
    pose proof (LRtm_conv_r X (VTy_nat_at VM'M' (SubRel_refl_r Hd) (NatRel_sym _ _ _ _ Ht'w'))) as X'.
    eapply LRtm_red; [exact X' | now apply tmred_natrec_cong | now apply Rcong].
  - (* zero *)
    intros H0. pose proof (Vs _ _ _ Hd) as X.
    rewrite !single_zero_subst_ty in X by assumption.
    pose proof (LRtm_irrel_r X (VTy_nat_at VM Hd H0)) as X'.
    eapply LRtm_red; [exact X' | now apply tmred_natrec_zero|].
    eapply tmred_lconv; [apply tmred_natrec_zero; eauto using lequiv_wf_r | exact Hll].
  - (* successor *)
    intros t t' Htt IH HS.
    pose proof (LRtm_irrel_r (natrec_step Hd Htt IH) (VTy_nat_at VM Hd HS)) as X.
    destruct (NatRel_escape Htt) as (Ht & Ht' & _).
    eapply LRtm_red; [exact X | now apply tmred_natrec_succ|].
    eapply tmred_lconv; [apply tmred_natrec_succ; eauto using lequiv_wf_r | exact Hll].
  - (* neutrals *)
    intros ν ν' Hνν Hne. destruct (VTy_nat_at VM Hd Hne) as [R HR].
    exists R; split; [exact HR|].
    destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (_ & _ & HMM).
    assert (HN : [ G ; Δ ⊢g tyNat @ lzero ])
      by (apply wft_nat; [exact ge_notV | now rewrite ge_typeof]).
    assert (Hlift : SubRel G (Γ ,, tyNat @ lzero) (Δ ,, tyNat @ lzero) (llift d) (llift d'))
      by exact (SubRel_lift (A := tyNat) Hd V_nat HN I).
    destruct (VM _ _ _ Hlift) as [RM HRM]. destruct (escape_ty _ _ _ _ _ _ _ _ HRM) as (_ & _ & EqM).
    pose proof (Vs _ _ _ Hd) as Xs. rewrite !single_zero_subst_ty in Xs by assumption.
    pose proof (Vz _ _ _ (SubRel_lift Hlift VMM HMd Hwl)) as Xz. rewrite !lsucc_subst_ty in Xz.
    pose proof (gne_tm_natrec Hll HMd EqM (LRtm_geq Xs) (LRtm_geq Xz) Hνν) as Hν.
    apply (LR_neutral _ _ _ _ _ _ _ HR); [exact Hν|].
    eapply gne_tm_conv; [exact Hν | now apply geq_ty_sound].
Qed.

Lemma V_natrec {t t'} : VTm G Γ t t' tyNat lzero ->
  VTm G Γ (natrec l M s z t) (natrec l' M' s' z' t') M[lsingle t] l.
Proof.
  intros Vt Δ d d' Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  pose proof (VTm_trans Vt (VTm_sym Vt)) as Vtt.
  push_subst. rewrite !single_subst_ty by assumption.
  eapply LRtm_irrel_r; [exact (natrec_core Hd _ _ (proj1 LRtm_nat (Vt _ _ _ Hd)))|].
  exact (VTy_nat_at (VTy_refl_l VM) Hd (proj1 LRtm_nat (Vtt _ _ _ Hd))).
Qed.

End NatrecCore.

(** ** Computation rules *)

Section NatrecComp.
Context {G : gctx} {Γ : ctx} {l : lvl} {M : ty} {s z : tm}
  (Hwl : lwf (gL G) l)
  (HM : [ G ; Γ ,, tyNat @ lzero ⊢g M @ l ])
  (Hs : [ G ; Γ ⊢g s : M[lsingle zero] @ l ])
  (Hz : [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢g z : M[lsucc] @ l ])
  (VM : VTy G (Γ ,, tyNat @ lzero) M M l)
  (Vs : VTm G Γ s s M[lsingle zero] l)
  (Vz : VTm G (Γ ,, tyNat @ lzero ,, M @ l) z z M[lsucc] l).

Lemma V_natrec_zero : VTm G Γ (natrec l M s z zero) s M[lsingle zero] l.
Proof.
  intros Δ d d' Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  pose proof (Vs _ _ _ Hd) as X. rewrite !single_zero_subst_ty in X |- * by assumption.
  destruct (natrec_prems_subst (SubRel_wf_l _ _ _ _ _ Hd) Hwl HM Hs Hz) as (HMd & Hsd & Hzd).
  push_subst. eapply LRtm_red_l; [exact X|]. now apply tmred_natrec_zero.
Qed.

Lemma V_natrec_succ {t} : VTm G Γ t t tyNat lzero ->
  VTm G Γ (natrec l M s z (succ t)) z[lsingle2 t (natrec l M s z t)] M[lsingle (succ t)] l.
Proof.
  intros Vt Δ d d' Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  destruct (natrec_prems_subst (SubRel_wf_l _ _ _ _ _ Hd) Hwl HM Hs Hz) as (HMd & Hsd & Hzd).
  pose proof (proj1 LRtm_nat (Vt _ _ _ Hd)) as Htt.
  pose proof (natrec_core Hwl (lequiv_refl _ _ Hwl) HM HM Hs Hs Hz Hz VM Vs Vz Hd _ _ Htt) as IH.
  pose proof (natrec_step VM Vz Hd Htt IH) as X.
  rewrite single_subst_ty, single_subst_ty, single2_subst by assumption. push_subst.
  destruct (NatRel_escape Htt) as (Ht & _ & _).
  eapply LRtm_red_l; [exact X|]. now apply tmred_natrec_succ.
Qed.

End NatrecComp.

End Natrec.
