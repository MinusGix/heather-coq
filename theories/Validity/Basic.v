(** * Validity of variables, natural numbers, universes, codes and [El] *)
From DeLaM.Validity Require Export SubstV.

Section Basic.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

(** ** Declarative helpers at the instance's layer *)

Lemma conv_U' {G Γ t l l'} :
  [ G ; Γ ⊢g t : tyU l @ lsuc l ] -> lequiv (gL G) l l' -> [ G ; Γ ⊢g t : tyU l' @ lsuc l' ].
Proof. apply (conv_U ge_typeof ge_notV). Qed.

(** Changing the annotation of [El]. *)
Lemma El_annot {G Γ la l c} :
  [ G ; Γ ⊢g c : tyU l @ lsuc l ] -> lequiv (gL G) la l ->
  [ G ; Γ ⊢g tyEl la c @ l ] /\ [ G ; Γ ⊢g tyEl la c ≅ tyEl l c @ l ].
Proof.
  intros Hc Hl. pose proof (conv_U' Hc (lequiv_sym _ _ _ Hl)) as Hca.
  split.
  - eapply (wft_lconv _ _ _ _ _ la); [apply wft_El; eauto using lequiv_wf_l, ge_notV | now apply lequiv_sym].
  - eapply (eqty_lconv _ _ _ _ _ _ la); [|now apply lequiv_sym].
    apply eqty_El; [exact ge_notV | exact Hl | now apply eqtm_refl].
Qed.

Lemma tyred_step {G Γ T W l} :
  [ G ; Γ ⊢g T @ l ] -> red_ty T W -> [ G ; Γ ⊢g T ≅ W @ l ] -> [ G ; Γ ⊢g T ⤳* W @ l ].
Proof. intros HT Hr HE; split; auto. econstructor; [exact Hr | constructor]. Qed.

Lemma tyred_El {G Γ t w la l} :
  [ G ; Γ ⊢g t ⤳* w : tyU l @ lsuc l ] -> lequiv (gL G) la l ->
  [ G ; Γ ⊢g tyEl la t ⤳* tyEl la w @ l ].
Proof.
  intros [Ht Hr Hte] Hl.
  destruct (El_annot Ht Hl) as [HEl _]. split; [exact HEl | now apply reds_El |].
  eapply (eqty_lconv _ _ _ _ _ _ la); [|now apply lequiv_sym].
  apply eqty_El; [exact ge_notV | apply lequiv_refl; eauto using lequiv_wf_l |].
  eapply eqtm_lconv; [|apply lequiv_suc, Hl].
  eapply eqtm_conv; [exact Hte | rewrite ge_typeof].
  eapply (eqty_lconv _ _ _ _ _ _ (lsuc la)); [|apply lequiv_suc, lequiv_sym, Hl].
  apply eqty_U; [exact ge_notV | rewrite ge_typeof; eapply ctx_of_tm, Ht | exact Hl].
Qed.

(** ** Variables *)

Lemma V_var {G Γ n T l} : in_ctx Γ n T l -> VTm G Γ (var n) (var n) T l.
Proof.
  intros Hin Δ d d'; revert Δ d d'.
  induction Hin as [Γ A l|Γ A l B l' n Hin IH]; cbn [SubRel]; intros Δ d d' [Ht Hh].
  - push_subst. rewrite !shift_subst_ty. exact Hh.
  - push_subst. rewrite !shift_subst_ty. specialize (IH _ _ _ Ht).
    rewrite !subst_var in IH. now rewrite !llk_ldrop in IH.
Qed.

(** ** Natural numbers *)

Lemma LR_nat_here {G Δ} n : [ G ; Δ ⊢g ] -> LR n (LRbelow n) G Δ tyNat tyNat lzero (NatRel G Δ).
Proof.
  intros HΔ.
  assert (HN : [ G ; Δ ⊢g tyNat @ lzero ]) by (apply wft_nat; [exact ge_notV | now rewrite ge_typeof]).
  eapply LRnat; [apply lequiv_refl; exact I | apply tyred_refl, HN | apply tyred_refl, HN
                | apply releq_refl].
Qed.

Lemma V_nat {G Γ} : VTy G Γ tyNat tyNat lzero.
Proof. intros Δ d d' Hd. exists (NatRel G Δ). apply LR_nat_here, (SubRel_ctx Hd). Qed.

Lemma LRtm_nat {G Δ t t'} : LRtm lzero G Δ tyNat tyNat t t' <-> NatRel G Δ t t'.
Proof.
  split.
  - intros H. assert (HΔ : [ G ; Δ ⊢g ]) by (destruct H as (R & HR & _); exact (ctx_of_ty (proj1 (escape_ty _ _ _ _ _ _ _ _ HR)))).
    exact (LRtm_inv (LR_nat_here _ HΔ) H).
  - intros H. assert (HΔ : [ G ; Δ ⊢g ]).
    { destruct H as [t t' w w' Hw]. eapply ctx_of_tm, Hw. }
    exact (LRtm_of (LR_nat_here _ HΔ) H).
Qed.

Lemma NatRel_escape {G Δ t t'} : NatRel G Δ t t' ->
  [ G ; Δ ⊢g t : tyNat @ lzero ] /\ [ G ; Δ ⊢g t' : tyNat @ lzero ] /\
  [ G ; Δ ⊢ t ≈ t' : tyNat @ lzero ].
Proof.
  intros H. assert (HΔ : [ G ; Δ ⊢g ]) by (destruct H as [t t' w w' Hw]; eapply ctx_of_tm, Hw).
  exact (escape_tm _ _ _ _ _ _ _ _ (LR_nat_here 0 HΔ) _ _ H).
Qed.

Lemma V_zero {G Γ} : VTm G Γ zero zero tyNat lzero.
Proof.
  intros Δ d d' Hd. apply LRtm_nat. pose proof (SubRel_ctx Hd) as HΔ.
  assert (Hz : [ G ; Δ ⊢g zero : tyNat @ lzero ])
    by (apply wf_zero; [exact ge_notV | now rewrite ge_typeof]).
  econstructor; [apply tmred_refl, Hz | apply tmred_refl, Hz | now apply geq_tm_zero | constructor].
Qed.

Lemma V_succ {G Γ t t'} : VTm G Γ t t' tyNat lzero -> VTm G Γ (succ t) (succ t') tyNat lzero.
Proof.
  intros Ht Δ d d' Hd. apply LRtm_nat. specialize (Ht _ _ _ Hd). apply LRtm_nat in Ht.
  destruct (NatRel_escape Ht) as (H1 & H2 & H12).
  econstructor.
  - apply tmred_refl, wf_succ; [exact ge_notV | exact H1].
  - apply tmred_refl, wf_succ; [exact ge_notV | exact H2].
  - now apply geq_tm_succ.
  - now constructor.
Qed.

(** ** Universes *)

Lemma LR_U_here {G Δ l l'} :
  [ G ; Δ ⊢g ] -> lwf (gL G) l -> lequiv (gL G) l l' ->
  LogRel (lsuc l) G Δ (tyU l) (tyU l') (lsuc l) (URel (LRbelow (lmeasure (lsuc l))) G Δ l).
Proof.
  intros HΔ Hwl Hl.
  assert (HU : forall k, lequiv (gL G) l k -> [ G ; Δ ⊢g tyU k @ lsuc l ]).
  { intros k Hk. eapply wft_lconv; [apply wft_U; [exact ge_notV | now rewrite ge_typeof
                                                 | eauto using lequiv_wf_r] | now apply lequiv_suc]. }
  eapply LRU with (l1 := l) (l2 := l').
  - now apply lequiv_refl.
  - now apply lequiv_sym.
  - rewrite ?lmeasure_suc; lia.
  - apply tyred_refl, HU, lequiv_refl, Hwl.
  - apply tyred_refl, HU, Hl.
  - apply releq_refl.
Qed.

Lemma V_U {G Γ l l'} : lwf (gL G) l -> lequiv (gL G) l l' -> VTy G Γ (tyU l) (tyU l') (lsuc l).
Proof. intros Hwl Hl Δ d d' Hd. eexists; apply LR_U_here; auto. exact (SubRel_ctx Hd). Qed.

(** Terms of a universe: the universe relation. *)
Lemma LRtm_U {G Δ l t t'} :
  lwf (gL G) l ->
  LRtm (lsuc l) G Δ (tyU l) (tyU l) t t' <-> URel (LRbelow (lmeasure (lsuc l))) G Δ l t t'.
Proof.
  intros Hwl; split.
  - intros H. assert (HΔ : [ G ; Δ ⊢g ]) by (destruct H as (R & HR & _); exact (ctx_of_ty (proj1 (escape_ty _ _ _ _ _ _ _ _ HR)))).
    exact (LRtm_inv (LR_U_here HΔ Hwl (lequiv_refl _ _ Hwl)) H).
  - intros H. assert (HΔ : [ G ; Δ ⊢g ]).
    { destruct H as (w & _ & Hw & _). eapply ctx_of_tm, Hw. }
    exact (LRtm_of (LR_U_here HΔ Hwl (lequiv_refl _ _ Hwl)) H).
Qed.

(** Decoding related codes gives related types. *)
Lemma V_El {G Γ l l' t t'} :
  lwf (gL G) l -> lequiv (gL G) l l' ->
  VTm G Γ t t' (tyU l) (lsuc l) -> VTy G Γ (tyEl l t) (tyEl l' t') l.
Proof.
  intros Hwl Hl Ht Δ d d' Hd. specialize (Ht _ _ _ Hd). rewrite !subst_tyU in Ht.
  apply (LRtm_U Hwl) in Ht. destruct Ht as (w & w' & Hw & Hw' & _ & _ & _ & HK).
  destruct (HK l l') as [R HR]; [now apply lequiv_refl | now apply lequiv_sym |].
  rewrite LRbelow_spec in HR by (rewrite ?lmeasure_suc; lia).
  exists R. push_subst. eapply LR_red_ty; [exact HR | |].
  - apply tyred_El; [exact Hw | now apply lequiv_refl].
  - apply tyred_El; [exact Hw' | now apply lequiv_sym].
Qed.

(** ** Codes of [Nat] and of universes *)

Lemma tyred_El_nat {G Δ la} :
  [ G ; Δ ⊢g ] -> lequiv (gL G) la lzero -> [ G ; Δ ⊢g tyEl la tmNat ⤳* tyNat @ lzero ].
Proof.
  intros HΔ Hl.
  assert (Hc : [ G ; Δ ⊢g tmNat : tyU lzero @ lsuc lzero ])
    by (apply wf_code_nat; [exact ge_notV | now rewrite ge_typeof]).
  destruct (El_annot Hc Hl) as [HEl HEq].
  apply tyred_step; [exact HEl | constructor |].
  eapply eqty_trans; [exact HEq|]. apply eqty_sym, eqty_El_nat; [exact ge_compt | now rewrite ge_typeof].
Qed.

Lemma V_code_nat {G Γ} : VTm G Γ tmNat tmNat (tyU lzero) (lsuc lzero).
Proof.
  intros Δ d d' Hd. pose proof (SubRel_ctx Hd) as HΔ. push_subst.
  apply (LRtm_U (l := lzero) I).
  assert (Hc : [ G ; Δ ⊢g tmNat : tyU lzero @ lsuc lzero ])
    by (apply wf_code_nat; [exact ge_notV | now rewrite ge_typeof]).
  exists tmNat, tmNat.
  refine (conj (tmred_refl _ _ _ Hc) (conj (tmred_refl _ _ _ Hc) (conj whnf_tmNat (conj whnf_tmNat
            (conj (geq_tm_code_nat HΔ) _))))).
  intros la lb Hla Hlb. rewrite LRbelow_spec by (rewrite ?lmeasure_suc; lia).
  exists (NatRel G Δ). eapply LRnat.
  - now apply lequiv_refl.
  - now apply tyred_El_nat.
  - now apply tyred_El_nat.
  - apply releq_refl.
Qed.

Lemma tyred_El_U {G Δ la l0} :
  [ G ; Δ ⊢g ] -> lwf (gL G) l0 -> lequiv (gL G) la (lsuc l0) ->
  [ G ; Δ ⊢g tyEl la (tmU l0) ⤳* tyU l0 @ lsuc l0 ].
Proof.
  intros HΔ Hw0 Hl.
  assert (Hc : [ G ; Δ ⊢g tmU l0 : tyU (lsuc l0) @ lsuc (lsuc l0) ])
    by (apply wf_code_U; [exact ge_notV | now rewrite ge_typeof | exact Hw0]).
  destruct (El_annot Hc Hl) as [HEl HEq].
  apply tyred_step; [exact HEl | constructor |].
  eapply eqty_trans; [exact HEq|].
  apply eqty_sym, eqty_El_U; [exact ge_compt | now rewrite ge_typeof | exact Hw0].
Qed.

Lemma V_code_U {G Γ l l'} :
  lwf (gL G) l -> lequiv (gL G) l l' ->
  VTm G Γ (tmU l) (tmU l') (tyU (lsuc l)) (lsuc (lsuc l)).
Proof.
  intros Hwl Hl Δ d d' Hd. pose proof (SubRel_ctx Hd) as HΔ. push_subst.
  apply (LRtm_U (l := lsuc l) Hwl).
  assert (Hc : forall k, lequiv (gL G) l k -> [ G ; Δ ⊢g tmU k : tyU (lsuc l) @ lsuc (lsuc l) ]).
  { intros k Hk. eapply wf_lconv; [|apply lequiv_suc, lequiv_suc, Hk].
    eapply wf_conv; [apply wf_code_U; [exact ge_notV | now rewrite ge_typeof | eauto using lequiv_wf_r]|].
    rewrite ge_typeof. eapply eqty_lconv; [|apply lequiv_suc, lequiv_suc, lequiv_sym, Hk].
    apply eqty_U; [exact ge_notV | now rewrite ge_typeof | now apply lequiv_suc]. }
  exists (tmU l), (tmU l').
  refine (conj (tmred_refl _ _ _ (Hc _ (lequiv_refl _ _ Hwl)))
            (conj (tmred_refl _ _ _ (Hc _ Hl)) (conj (whnf_tmU _) (conj (whnf_tmU _)
            (conj (geq_tm_code_U HΔ Hl) _))))).
  intros la lb Hla Hlb. rewrite LRbelow_spec by (rewrite ?lmeasure_suc; lia).
  exists (URel (LRbelow (lmeasure (lsuc l))) G Δ l).
  eapply LRU with (l1 := l) (l2 := l').
  - now apply lequiv_refl.
  - now apply lequiv_sym.
  - rewrite ?lmeasure_suc; lia.
  - now apply tyred_El_U.
  - eapply (tyred_lconv _ _ (lsuc l) (lsuc l')); [|now apply lequiv_suc].
    apply tyred_El_U; [exact HΔ | eauto using lequiv_wf_r |].
    eapply lequiv_trans; [exact Hlb | now apply lequiv_suc].
  - apply releq_refl.
Qed.

(** [Nat ≅ El 0 ⌜Nat⌝] and [U l ≅ El (1+l) ⌜U l⌝]. *)
Lemma V_El_nat {G Γ} : VTy G Γ tyNat (tyEl lzero tmNat) lzero.
Proof.
  intros Δ d d' Hd. pose proof (SubRel_ctx Hd) as HΔ. push_subst.
  exists (NatRel G Δ). eapply LRnat.
  - now apply lequiv_refl.
  - apply tyred_refl, wft_nat; [exact ge_notV | now rewrite ge_typeof].
  - now apply tyred_El_nat, lequiv_refl.
  - apply releq_refl.
Qed.

Lemma V_El_U {G Γ l} : lwf (gL G) l -> VTy G Γ (tyU l) (tyEl (lsuc l) (tmU l)) (lsuc l).
Proof.
  intros Hwl Δ d d' Hd. pose proof (SubRel_ctx Hd) as HΔ. push_subst.
  exists (URel (LRbelow (lmeasure (lsuc l))) G Δ l).
  eapply LRU with (l1 := l) (l2 := l).
  - now apply lequiv_refl.
  - now apply lequiv_refl.
  - rewrite ?lmeasure_suc; lia.
  - apply tyred_refl, wft_U; [exact ge_notV | now rewrite ge_typeof | exact Hwl].
  - apply tyred_El_U; [exact HΔ | exact Hwl | now apply lequiv_refl].
  - apply releq_refl.
Qed.

End Basic.
