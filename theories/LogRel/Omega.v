(** * The relation at ω (M4_DESIGN.md F3)

    The types at ω are the [UΠ] types. Their relation is one definition on
    top of the finite relation, not a case of [LR]: an instance of a [UΠ]
    at levels [ls] lives at the finite level [l[ls]], related by [LogRel]
    at that level (07a:848–890, 07:435). The instances are Kripke over
    [kwk] worlds, whose level growth replaces the paper's universe
    weakenings (M3_DESIGN.md E14). Every property is proved from the finite
    relation's. *)
From DeLaM.LogRel Require Export Reduction LevelInv.

Section Omega.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

(** ** Definitions *)

(** The instances' relations, indexed by the world and both level lists. *)
Definition UInstRel (G : gctx) (Γ : ctx) := kwk G Γ -> list lvl -> list lvl -> tm -> tm -> Prop.

(** Related universe-polymorphic functions: they reduce to related weak-head
    normal forms whose instances at equivalent levels are related, in
    every world. *)
Definition UPiRel (G : gctx) (Γ : ctx) (n : nat) (l l' : lvl) (A A' : ty) (instR : UInstRel G Γ)
    : tm -> tm -> Prop :=
  fun t t' => exists w w',
    [ G ; Γ ⊢g t ⤳* w : tyUPi n l A @ lomega ] /\ [ G ; Γ ⊢g t' ⤳* w' : tyUPi n l' A' @ lomega ] /\
    whnf w /\ whnf w' /\
    [ G ; Γ ⊢ w ≈ w' : tyUPi n l A @ lomega ] /\ [ G ; Γ ⊢ w ≈ w' : tyUPi n l' A' @ lomega ] /\
    forall (ρ : kwk G Γ) ls ls', length ls = n -> Forall2 (lequiv (gL (kw_G ρ))) ls ls' ->
      instR ρ ls ls' (uapp (ktm ρ w) ls) (uapp (ktm ρ w') ls').

Inductive LRω (G : gctx) (Γ : ctx) (T T' : ty) (R : tm -> tm -> Prop) : Prop :=
| LRupi n l l' A A' (instR : UInstRel G Γ) :
    0 < n -> lequiv (n + gL G) l l' ->
    [ G ; Γ ⊢g T ⤳* tyUPi n l A @ lomega ] -> [ G ; Γ ⊢g T' ⤳* tyUPi n l' A' @ lomega ] ->
    [ G ; Γ ⊢ tyUPi n l A ≈ tyUPi n l' A' @ lomega ] ->
    (forall (ρ : kwk G Γ) ls ls', length ls = n -> Forall2 (lequiv (gL (kw_G ρ))) ls ls' ->
       LogRel (lvsubst l (uext ls lvar)) (kw_G ρ) (kw_Δ ρ)
         (kty ρ A)[uext ls lvar]ᵤ (kty ρ A')[uext ls' lvar]ᵤ (lvsubst l (uext ls lvar))
         (instR ρ ls ls')) ->
    releq R (UPiRel G Γ n l l' A A' instR) ->
    LRω G Γ T T' R.

(** ** Helpers *)

Lemma kty_tyUPi {G Γ} (ρ : kwk G Γ) n l A : kty ρ (tyUPi n l A) = tyUPi n l (kty ρ A).
Proof using . unfold kty; destruct (kw_γ ρ); reflexivity. Qed.
Lemma ktm_uapp {G Γ} (ρ : kwk G Γ) t ls : ktm ρ (uapp t ls) = uapp (ktm ρ t) ls.
Proof using . unfold ktm; destruct (kw_γ ρ); reflexivity. Qed.

Lemma upi_agree {G Γ T n l A n' l' A' k k'} :
  [ G ; Γ ⊢g T ⤳* tyUPi n l A @ k ] -> [ G ; Γ ⊢g T ⤳* tyUPi n' l' A' @ k' ] ->
  n' = n /\ l' = l /\ A' = A.
Proof using .
  intros H1 H2. assert (Eq : tyUPi n l A = tyUPi n' l' A')
    by (eapply tyred_whnf_det; [exact H1 | exact H2 | constructor | constructor]).
  injection Eq; auto.
Qed.

Lemma lequivs_sym L ls ls' : Forall2 (lequiv L) ls ls' -> Forall2 (lequiv L) ls' ls.
Proof using . induction 1; constructor; auto using lequiv_sym. Qed.

(** The instance levels of equivalent levels at equivalent level lists. *)
Lemma lequiv_ilv {L L' n l l' ls ls'} : L <= L' -> lequiv (n + L) l l' -> length ls = n ->
  Forall2 (lequiv L') ls ls' -> lequiv L' (lvsubst l (uext ls lvar)) (lvsubst l' (uext ls' lvar)).
Proof using .
  intros HL Hl Hn Hls. subst n.
  eapply lequiv_trans.
  - eapply lequiv_lvsubst; [exact (usub_ok_uext _ _ _ _ (lequivs_lwf_l _ _ _ Hls) (usub_ok_id _)) |].
    eapply lequiv_weaken; [| exact Hl]. lia.
  - apply lequiv_uinst; [| exact Hls]. eapply lwf_weaken; [| exact (lequiv_wf_r _ _ _ Hl)]. lia.
Qed.

(** A relation at one stage, moved to an equivalent level. *)
Lemma LogRel_move {l0 l1 G Γ T T' R} : lequiv (gL G) l1 l0 ->
  LogRel l0 G Γ T T' l0 R -> LogRel l1 G Γ T T' l1 R.
Proof using EL.
  intros El H. unfold LogRel in *. rewrite (lequiv_measure _ _ _ El).
  exact (LR_lconv _ _ _ _ _ _ _ _ _ H El).
Qed.

Lemma tyred_eqω {G Γ T W} : [ G ; Γ ⊢g T ⤳* W @ lomega ] -> [ G ; Γ ⊢g T ≅ W @ lomega ].
Proof using . now intros []. Qed.

Lemma tmred_convω {G Γ t w T T'} : [ G ; Γ ⊢g t ⤳* w : T @ lomega ] -> [ G ; Γ ⊢g T ≅ T' @ lomega ] ->
  [ G ; Γ ⊢g t ⤳* w : T' @ lomega ].
Proof using . intros H Heq. eapply tmred_conv; [apply ge_typeof | exact H | exact Heq]. Qed.

Lemma wf_convω {G Γ t T T'} : [ G ; Γ ⊢g t : T @ lomega ] -> [ G ; Γ ⊢g T' ≅ T @ lomega ] ->
  [ G ; Γ ⊢g t : T' @ lomega ].
Proof using . intros H Heq. eapply wf_conv; [exact H | now rewrite ge_typeof]. Qed.

(** ** Irrelevance *)

Lemma UPiRel_dir {G Γ n l l' k' A A' B'} {iR iR' : UInstRel G Γ}
  (HP : [ G ; Γ ⊢g tyUPi n l' A' ≅ tyUPi n k' B' @ lomega ])
  (Hi : forall ρ ls ls', length ls = n -> Forall2 (lequiv (gL (kw_G ρ))) ls ls' ->
          releq (iR ρ ls ls') (iR' ρ ls ls')) t t' :
  UPiRel G Γ n l l' A A' iR t t' -> UPiRel G Γ n l k' A B' iR' t t'.
Proof using EL.
  intros (w & w' & Hw & Hw' & Hnf & Hnf' & E1 & E2 & HK).
  exists w, w'. refine (conj Hw (conj (tmred_convω Hw' HP) (conj Hnf (conj Hnf' (conj E1 (conj _ _)))))).
  - eapply geq_tm_conv; [exact E2 | exact HP].
  - intros ρ ls ls' Hn Hls. apply (Hi ρ ls ls' Hn Hls), HK; assumption.
Qed.

Lemma LRω_releq {G Γ T T' R R'} : LRω G Γ T T' R -> releq R R' -> LRω G Γ T T' R'.
Proof using .
  intros [n l l' A A' iR Hn Hl HT HT' HTT HI HR] Hrq.
  apply (LRupi _ _ _ _ _ n l l' A A' iR); auto. eapply releq_trans; [apply releq_sym, Hrq | exact HR].
Qed.

Theorem LRω_irrel {G Γ T T' T'' R R'} : LRω G Γ T T' R -> LRω G Γ T T'' R' -> releq R R'.
Proof using EL VL.
  intros [n l l' A A' iR Hn Hl HT HT' HTT HI HR] [n2 k k' B B' iR' Hn2 Hk HT2 HT2' HTT2 HI2 HR2].
  destruct (upi_agree HT HT2) as (-> & -> & ->).
  assert (Hi : forall ρ ls ls', length ls = n -> Forall2 (lequiv (gL (kw_G ρ))) ls ls' ->
                 releq (iR ρ ls ls') (iR' ρ ls ls'))
    by (intros ρ ls ls' Hn' Hls; exact (LR_irrel _ _ _ _ _ _ _ _ _ _ (HI ρ ls ls' Hn' Hls) (HI2 ρ ls ls' Hn' Hls))).
  assert (HP : [ G ; Γ ⊢g tyUPi n l' A' ≅ tyUPi n k' B' @ lomega ])
    by (eapply eqty_trans; [apply eqty_sym, geq_ty_sound, HTT | apply geq_ty_sound, HTT2]).
  eapply releq_trans; [exact HR | eapply releq_trans; [| apply releq_sym, HR2]].
  intros t t'; split.
  - exact (UPiRel_dir HP Hi t t').
  - apply (UPiRel_dir (eqty_sym _ _ _ _ _ _ HP)). intros ρ ls ls' Hn' Hls; apply releq_sym, Hi; assumption.
Qed.

(** ** Symmetry *)

Lemma UPiRel_flip {G Γ n l l' A A'} {iR : UInstRel G Γ} t t' :
  UPiRel G Γ n l l' A A' iR t t' ->
  UPiRel G Γ n l' l A' A (fun ρ ls ls' => flipR (iR ρ ls' ls)) t' t.
Proof using EL.
  intros (w & w' & Hw & Hw' & Hnf & Hnf' & E1 & E2 & HK).
  exists w', w. refine (conj Hw' (conj Hw (conj Hnf' (conj Hnf (conj _ (conj _ _)))))).
  - apply geq_tm_sym, E2.
  - apply geq_tm_sym, E1.
  - intros ρ ls ls' Hn Hls. unfold flipR.
    apply HK; [rewrite <- (Forall2_length Hls); exact Hn | apply lequivs_sym, Hls].
Qed.

Theorem LRω_sym {G Γ T T' R} : LRω G Γ T T' R -> LRω G Γ T' T (flipR R).
Proof using EL VL.
  intros [n l l' A A' iR Hn Hl HT HT' HTT HI HR].
  apply (LRupi _ _ _ _ _ n l' l A' A (fun ρ ls ls' => flipR (iR ρ ls' ls))).
  - exact Hn.
  - apply lequiv_sym, Hl.
  - exact HT'.
  - exact HT.
  - apply geq_ty_sym, HTT.
  - intros ρ ls ls' Hn' Hls.
    assert (Hn2 : length ls' = n) by (rewrite <- (Forall2_length Hls); exact Hn').
    pose proof (LogRel_sym _ _ _ _ _ _ _ (HI ρ ls' ls Hn2 (lequivs_sym _ _ _ Hls))) as X.
    eapply LogRel_move; [| exact X].
    exact (lequiv_ilv (kw_gL ρ) (lequiv_sym _ _ _ Hl) Hn' Hls).
  - intros t t'; split; intros H.
    + exact (UPiRel_flip t' t (proj1 (HR t' t) H)).
    + apply HR. exact (UPiRel_flip t t' H).
Qed.

(** ** Transitivity *)

Theorem LRω_trans {G Γ T1 T2 T3 R12 R23} : LRω G Γ T1 T2 R12 -> LRω G Γ T2 T3 R23 ->
  LRω G Γ T1 T3 R12 /\ (forall t1 t2 t3, R12 t1 t2 -> R23 t2 t3 -> R12 t1 t3).
Proof using EL VL.
  intros [n l l' A A' iR Hn Hl HT HT' HTT HI HR] [n2 k k' B B' iR2 Hn2 Hk HT2 HT2' HTT2 HI2 HR2].
  destruct (upi_agree HT' HT2) as (-> & -> & ->).
  (* the instances compose *)
  assert (Hi : forall (ρ : kwk G Γ) ls ls' (Hn' : length ls = n) (Hls : Forall2 (lequiv (gL (kw_G ρ))) ls ls'),
    LogRel (lvsubst l (uext ls lvar)) (kw_G ρ) (kw_Δ ρ) (kty ρ A)[uext ls lvar]ᵤ (kty ρ B')[uext ls' lvar]ᵤ
      (lvsubst l (uext ls lvar)) (iR ρ ls ls') /\
    (forall t1 t2 t3, iR ρ ls ls' t1 t2 -> iR2 ρ ls' ls' t2 t3 -> iR ρ ls ls' t1 t3)).
  { intros ρ ls ls' Hn' Hls.
    assert (Hn3 : length ls' = n) by (rewrite <- (Forall2_length Hls); exact Hn').
    pose proof (HI2 ρ ls' ls' Hn3 (lequivs_refl _ _ (lequivs_lwf_r _ _ _ Hls))) as X23.
    assert (Elv : lequiv (gL (kw_G ρ)) (lvsubst l (uext ls lvar)) (lvsubst l' (uext ls' lvar)))
      by exact (lequiv_ilv (kw_gL ρ) Hl Hn' Hls).
    pose proof (LogRel_move Elv X23) as Y.
    exact (LR_trans _ _ _ _ _ _ _ (HI ρ ls ls' Hn' Hls) _ _ Y). }
  assert (HP : [ G ; Γ ⊢g tyUPi n l' A' ≅ tyUPi n k' B' @ lomega ]) by exact (geq_ty_sound HTT2).
  split.
  - apply (LRupi _ _ _ _ _ n l k' A B' iR).
    + exact Hn.
    + eapply lequiv_trans; [exact Hl | exact Hk].
    + exact HT.
    + exact HT2'.
    + eapply geq_ty_trans; [exact HTT | exact HTT2].
    + intros ρ ls ls' Hn' Hls; exact (proj1 (Hi ρ ls ls' Hn' Hls)).
    + eapply releq_trans; [exact HR|]. intros t t'; split.
      * apply UPiRel_dir; [exact HP | intros; apply releq_refl].
      * apply UPiRel_dir; [exact (eqty_sym _ _ _ _ _ _ HP) | intros; apply releq_refl].
  - intros t1 t2 t3 H12 H23. apply HR in H12. apply HR2 in H23. apply HR.
    destruct H12 as (w1 & w2 & Hw1 & Hw2 & Hnf1 & Hnf2 & E1 & E1' & K1).
    destruct H23 as (w2' & w3 & Hw2' & Hw3 & Hnf2' & Hnf3 & E2 & E2' & K2).
    assert (w2' = w2) as -> by (eapply tmred_whnf_det; [exact Hw2' | exact Hw2 | assumption ..]).
    exists w1, w3. refine (conj Hw1 (conj _ (conj Hnf1 (conj Hnf3 (conj _ (conj _ _)))))).
    + exact (tmred_convω Hw3 (eqty_sym _ _ _ _ _ _ HP)).
    + eapply geq_tm_trans; [exact E1 |].
      eapply geq_tm_conv; [exact E2 | apply eqty_sym, geq_ty_sound, HTT].
    + eapply geq_tm_trans; [exact E1' | exact E2].
    + intros ρ ls ls' Hn' Hls.
      assert (Hn3 : length ls' = n) by (rewrite <- (Forall2_length Hls); exact Hn').
      apply (proj2 (Hi ρ ls ls' Hn' Hls)) with (uapp (ktm ρ w2) ls').
      * apply K1; assumption.
      * apply K2; [exact Hn3 | exact (lequivs_refl _ _ (lequivs_lwf_r _ _ _ Hls))].
Qed.

Corollary LRω_refl_l {G Γ T T' R} : LRω G Γ T T' R -> LRω G Γ T T R.
Proof using EL VL. intros H. exact (proj1 (LRω_trans H (LRω_sym H))). Qed.
Corollary LRω_refl_r {G Γ T T' R} : LRω G Γ T T' R -> LRω G Γ T' T' (flipR R).
Proof using EL VL. intros H. exact (LRω_refl_l (LRω_sym H)). Qed.
Corollary LRω_tm_refl_l {G Γ T T' R t t'} : LRω G Γ T T' R -> R t t' -> R t t.
Proof using EL VL. intros H Ht. exact (proj2 (LRω_trans H (LRω_sym H)) t t' t Ht Ht). Qed.

(** ** Kripke weakening *)

Theorem LRω_kwk {G Γ T T' R} : LRω G Γ T T' R -> forall ρ : kwk G Γ,
  exists R', LRω (kw_G ρ) (kw_Δ ρ) (kty ρ T) (kty ρ T') R' /\
    forall t t', R t t' -> R' (ktm ρ t) (ktm ρ t').
Proof using EL.
  intros [n l l' A A' iR Hn Hl HT HT' HTT HI HR] ρ.
  set (iR' := fun (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) ls ls' => iR (kw_comp ρ ρ') ls ls').
  exists (UPiRel (kw_G ρ) (kw_Δ ρ) n l l' (kty ρ A) (kty ρ A') iR'). split.
  - apply (LRupi _ _ _ _ _ n l l' (kty ρ A) (kty ρ A') iR').
    + exact Hn.
    + eapply lequiv_weaken; [| exact Hl]. pose proof (kw_gL ρ); lia.
    + rewrite <- kty_tyUPi. apply kw_tyred, HT.
    + rewrite <- kty_tyUPi. apply kw_tyred, HT'.
    + rewrite <- !kty_tyUPi. apply kw_geq_ty, HTT.
    + intros ρ' ls ls' Hn' Hls. unfold iR'. rewrite <- !kty_comp. exact (HI (kw_comp ρ ρ') ls ls' Hn' Hls).
    + apply releq_refl.
  - intros t t' H. apply HR in H. destruct H as (w & w' & Hw & Hw' & Hnf & Hnf' & E1 & E2 & HK).
    exists (ktm ρ w), (ktm ρ w').
    rewrite <- !kty_tyUPi.
    refine (conj (kw_tmred ρ Hw) (conj (kw_tmred ρ Hw') (conj _ (conj _ (conj (kw_geq_tm ρ E1)
              (conj (kw_geq_tm ρ E2) _)))))).
    + apply whnf_kw, Hnf.
    + apply whnf_kw, Hnf'.
    + intros ρ' ls ls' Hn' Hls. unfold iR'. rewrite <- !ktm_comp. apply HK; assumption.
Qed.

(** ** Anti-reduction *)

Theorem LRω_red_ty {G Γ T T' R T1 T1'} : LRω G Γ T T' R ->
  [ G ; Γ ⊢g T1 ⤳* T @ lomega ] -> [ G ; Γ ⊢g T1' ⤳* T' @ lomega ] -> LRω G Γ T1 T1' R.
Proof using .
  intros [n l l' A A' iR Hn Hl HT HT' HTT HI HR] H1 H1'.
  apply (LRupi _ _ _ _ _ n l l' A A' iR); eauto using tyred_trans.
Qed.

Theorem LRω_red_tm {G Γ T T' R} : LRω G Γ T T' R -> forall t t' t1 t1', R t t' ->
  [ G ; Γ ⊢g t1 ⤳* t : T @ lomega ] -> [ G ; Γ ⊢g t1' ⤳* t' : T' @ lomega ] -> R t1 t1'.
Proof using .
  intros [n l l' A A' iR Hn Hl HT HT' HTT HI HR] t t' t1 t1' Htt H1 H1'.
  apply HR in Htt. apply HR. destruct Htt as (w & w' & Hw & Hw' & Hrest).
  exists w, w'. refine (conj _ (conj _ Hrest)).
  - eapply tmred_trans; [exact (tmred_convω H1 (tyred_eqω HT)) | exact Hw].
  - eapply tmred_trans; [exact (tmred_convω H1' (tyred_eqω HT')) | exact Hw'].
Qed.

(** ** Escape *)

Theorem LRω_escape_ty {G Γ T T' R} : LRω G Γ T T' R ->
  [ G ; Γ ⊢g T @ lomega ] /\ [ G ; Γ ⊢g T' @ lomega ] /\ [ G ; Γ ⊢ T ≈ T' @ lomega ].
Proof using EL.
  intros [n l l' A A' iR Hn Hl HT HT' HTT HI HR].
  refine (conj (tyred_wf _ _ _ _ _ _ HT) (conj (tyred_wf _ _ _ _ _ _ HT') _)).
  eapply geq_ty_exp; [exact HT | exact HT' | exact HTT].
Qed.

Theorem LRω_escape_tm {G Γ T T' R} : LRω G Γ T T' R -> forall t t', R t t' ->
  [ G ; Γ ⊢g t : T @ lomega ] /\ [ G ; Γ ⊢g t' : T @ lomega ] /\ [ G ; Γ ⊢ t ≈ t' : T @ lomega ].
Proof using EL.
  intros [n l l' A A' iR Hn Hl HT HT' HTT HI HR] t t' Htt.
  apply HR in Htt. destruct Htt as (w & w' & Hw & Hw' & Hnf & Hnf' & E1 & E2 & HK).
  pose proof (tyred_eqω HT) as ET.
  assert (EP : [ G ; Γ ⊢g tyUPi n l' A' ≅ tyUPi n l A @ lomega ])
    by (apply eqty_sym, geq_ty_sound, HTT).
  assert (Hw'' : [ G ; Γ ⊢g t' ⤳* w' : tyUPi n l A @ lomega ]) by exact (tmred_convω Hw' EP).
  refine (conj _ (conj _ _)).
  - exact (wf_convω (tmred_wf _ _ _ _ _ _ _ Hw) ET).
  - exact (wf_convω (tmred_wf _ _ _ _ _ _ _ Hw'') ET).
  - eapply geq_tm_conv; [eapply geq_tm_exp; [exact Hw | exact Hw'' | exact E1] | apply eqty_sym, ET].
Qed.

(** ** Level invariance (M3_DESIGN.md E6') *)

Lemma ty_leq_upi_inv {n l A W} : ty_leq (tyUPi n l A) W ->
  exists k C, W = tyUPi n k C /\ leqv l k /\ ty_leq A C.
Proof using . destruct W; cbn; try contradiction. intros (-> & ? & ?). do 2 eexists; eauto. Qed.

Theorem LRω_leq {G Γ T1 T2 T3 R R3} : LRω G Γ T1 T2 R -> LRω G Γ T3 T3 R3 -> ty_leq T2 T3 ->
  LRω G Γ T1 T3 R /\ (forall t1 t2 t3, R t1 t2 -> R3 t3 t3 -> tm_leq t2 t3 -> R t1 t3).
Proof using EL VL.
  intros [n l l' A A' iR Hn Hl HT HT' HTT HI HR] [n3 k k' C C' iR3 Hn3 Hk HT3 HT3' HTT3 HI3 HR3] ET.
  destruct (upi_agree HT3 HT3') as (_ & -> & ->).
  pose proof (reds_ty_whnf_leq _ _ _ _ ET (tyred_red _ _ _ _ _ _ HT') (tyred_red _ _ _ _ _ _ HT3)
                (whnf_tyUPi _ _ _) (whnf_tyUPi _ _ _)) as EW.
  destruct (ty_leq_upi_inv EW) as (k2 & C2 & EC & Elk & EAC). injection EC as -> <- <-.
  assert (Hlk : lequiv (n + gL G) l k).
  { eapply lequiv_trans; [exact Hl |]. apply leqv_lequiv; [exact (lequiv_wf_r _ _ _ Hl) | exact (lequiv_wf_l _ _ _ Hk) | exact Elk]. }
  assert (HTT' : [ G ; Γ ⊢ tyUPi n l A ≈ tyUPi n k C @ lomega ])
    by (eapply geq_ty_leq_r; [exact HTT | exact HTT3 | exact EW]).
  assert (HP : [ G ; Γ ⊢g tyUPi n l' A' ≅ tyUPi n k C @ lomega ])
    by (eapply eqty_trans; [apply eqty_sym, geq_ty_sound, HTT | apply geq_ty_sound, HTT']).
  (* the instances *)
  assert (Hi : forall (ρ : kwk G Γ) ls ls' (Hn' : length ls = n) (Hls : Forall2 (lequiv (gL (kw_G ρ))) ls ls'),
    LogRel (lvsubst l (uext ls lvar)) (kw_G ρ) (kw_Δ ρ) (kty ρ A)[uext ls lvar]ᵤ (kty ρ C)[uext ls' lvar]ᵤ
      (lvsubst l (uext ls lvar)) (iR ρ ls ls') /\
    (forall t1 t2 t3, iR ρ ls ls' t1 t2 -> iR3 ρ ls' ls' t3 t3 -> tm_leq t2 t3 -> iR ρ ls ls' t1 t3)).
  { intros ρ ls ls' Hn' Hls.
    assert (Hn4 : length ls' = n) by (rewrite <- (Forall2_length Hls); exact Hn').
    pose proof (HI3 ρ ls' ls' Hn4 (lequivs_refl _ _ (lequivs_lwf_r _ _ _ Hls))) as X3.
    assert (Elv : lequiv (gL (kw_G ρ)) (lvsubst l (uext ls lvar)) (lvsubst k (uext ls' lvar)))
      by exact (lequiv_ilv (kw_gL ρ) Hlk Hn' Hls).
    pose proof (LogRel_move Elv X3) as Y.
    assert (EA : ty_leq (kty ρ A')[uext ls' lvar]ᵤ (kty ρ C)[uext ls' lvar]ᵤ)
      by (apply (proj1 leq_usubst_all); [intros; apply leqv_refl | apply kty_leq, EAC]).
    exact (conj (LogRel_leq_ty (HI ρ ls ls' Hn' Hls) Y EA)
                (fun t1 t2 t3 => LogRel_leq_tm (HI ρ ls ls' Hn' Hls) Y EA)). }
  split.
  - apply (LRupi _ _ _ _ _ n l k A C iR).
    + exact Hn.
    + exact Hlk.
    + exact HT.
    + exact HT3.
    + exact HTT'.
    + intros ρ ls ls' Hn' Hls; exact (proj1 (Hi ρ ls ls' Hn' Hls)).
    + eapply releq_trans; [exact HR|]. intros t t'; split.
      * apply UPiRel_dir; [exact HP | intros; apply releq_refl].
      * apply UPiRel_dir; [exact (eqty_sym _ _ _ _ _ _ HP) | intros; apply releq_refl].
  - intros t1 t2 t3 H H3 Et. apply HR in H. apply HR3 in H3. apply HR.
    destruct H as (w1 & w2 & Hw1 & Hw2 & Hnf1 & Hnf2 & E1 & E1' & K1).
    destruct H3 as (w3 & w3' & Hw3 & Hw3' & Hnf3 & Hnf3' & E3 & E3' & K3).
    assert (w3' = w3) as -> by (eapply tmred_whnf_det; [exact Hw3' | exact Hw3 | assumption ..]).
    pose proof (reds_whnf_leq _ _ _ _ Et (tmred_red _ _ _ _ _ _ _ Hw2) (tmred_red _ _ _ _ _ _ _ Hw3)
                  Hnf2 Hnf3) as Ew.
    assert (E3l : [ G ; Γ ⊢ w3 ≈ w3 : tyUPi n l A @ lomega ])
      by (eapply geq_tm_conv; [exact E3 | apply eqty_sym, geq_ty_sound, HTT']).
    assert (E13 : [ G ; Γ ⊢ w1 ≈ w3 : tyUPi n l A @ lomega ]) by exact (geq_tm_leq_r E1 E3l Ew).
    exists w1, w3.
    refine (conj Hw1 (conj (tmred_convω Hw3 (eqty_sym _ _ _ _ _ _ HP)) (conj Hnf1 (conj Hnf3 (conj E13 (conj _ _)))))).
    + eapply geq_tm_conv; [exact E13 | apply geq_ty_sound, HTT].
    + intros ρ ls ls' Hn' Hls.
      assert (Hn4 : length ls' = n) by (rewrite <- (Forall2_length Hls); exact Hn').
      apply (proj2 (Hi ρ ls ls' Hn' Hls)) with (uapp (ktm ρ w2) ls').
      * apply K1; assumption.
      * apply K3; [exact Hn4 | exact (lequivs_refl _ _ (lequivs_lwf_r _ _ _ Hls))].
      * cbn. split; [apply ktm_leq, Ew | apply leqvs_refl].
Qed.

End Omega.
