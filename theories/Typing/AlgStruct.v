(** * Structural properties of algorithmic conversion (M6_DESIGN.md step 3)

    Local and global weakening, universe substitution, closure under [≡ₗ].
    Each rule is a lemma over the induction hypotheses; the mutual
    induction dispatches them. Local contexts of layer D (the [Δ]s of
    contextual types) do not depend on the ambient context, so local
    weakening leaves [ac_ctx] untouched. *)
From DeLaM.Syntax Require Export LevelRed.
From DeLaM.Typing Require Export Algorithmic Properties GWeakening.

Ltac push_ren_in H := revert H; push_ren; intros H.

Lemma posty_ren W r : posty W -> posty W⟨r⟩.
Proof.
  destruct 1; cbn; first [apply posty_nat | apply posty_U | apply posty_CTyp | apply posty_CTrm | idtac].
  apply posty_ne, whne_ty_ren; assumption.
Qed.

(** ** Retyping *)

Lemma ac_tm_eq {G Γ t t' T T'} : ac_tm G Γ t t' T -> T = T' -> ac_tm G Γ t t' T'.
Proof. now intros ? <-. Qed.
Lemma ac_tmne_eq {G Γ t t' T T'} : ac_tmne G Γ t t' T -> T = T' -> ac_tmne G Γ t t' T'.
Proof. now intros ? <-. Qed.
Lemma ac_tm_eq3 {G Γ t1 t2 u1 u2 T T'} : ac_tm G Γ t1 t2 T -> t1 = u1 -> t2 = u2 -> T = T' ->
  ac_tm G Γ u1 u2 T'.
Proof. now intros ? <- <- <-. Qed.
Lemma ac_ty_eq3 {G Γ T1 T2 U1 U2} : ac_ty G Γ T1 T2 -> T1 = U1 -> T2 = U2 -> ac_ty G Γ U1 U2.
Proof. now intros ? <- <-. Qed.

(** ** Local weakening *)

Definition AW_ty G Γ T T' : Prop := forall Δ r, wkr r Δ Γ -> ac_ty G Δ T⟨r⟩ T'⟨r⟩.
Definition AW_tynf G Γ T T' : Prop := forall Δ r, wkr r Δ Γ -> ac_tynf G Δ T⟨r⟩ T'⟨r⟩.
Definition AW_tyne G Γ T T' : Prop := forall Δ r, wkr r Δ Γ -> ac_tyne G Δ T⟨r⟩ T'⟨r⟩.
Definition AW_tm G Γ t t' T : Prop := forall Δ r, wkr r Δ Γ -> ac_tm G Δ t⟨r⟩ t'⟨r⟩ T⟨r⟩.
Definition AW_tmnf G Γ t t' T : Prop := forall Δ r, wkr r Δ Γ -> ac_tmnf G Δ t⟨r⟩ t'⟨r⟩ T⟨r⟩.
Definition AW_tmne G Γ t t' T : Prop := forall Δ r, wkr r Δ Γ -> ac_tmne G Δ t⟨r⟩ t'⟨r⟩ T⟨r⟩.
Definition AW_tmnee G Γ t t' T : Prop := forall Δ r, wkr r Δ Γ -> ac_tmnee G Δ t⟨r⟩ t'⟨r⟩ T⟨r⟩.
Definition AW_sub G Γ d d' Θ : Prop := forall Δ r, wkr r Δ Γ -> ac_sub G Δ (lren d r) (lren d' r) Θ.

Lemma W_act_red {G Γ T T' W W'} : reds_ty T W -> reds_ty T' W' -> whnf_ty W -> whnf_ty W' ->
  AW_tynf G Γ W W' -> AW_ty G Γ T T'.
Proof. intros ? ? ? ? IH Δ r Hr. eapply act_red; eauto using reds_ty_ren, whnf_ty_ren. Qed.

Lemma W_actnf_nat {G Γ} : AW_tynf G Γ tyNat tyNat.
Proof. intros Δ r _. apply actnf_nat. Qed.
Lemma W_actnf_U {G Γ l l'} : leqv l l' -> AW_tynf G Γ (tyU l) (tyU l').
Proof. intros H Δ r _. now apply actnf_U. Qed.
Lemma W_actnf_pi {G Γ l1 l2 l3 l4 A A' B B'} : leqv l1 l3 -> leqv l2 l4 ->
  AW_ty G Γ A A' -> AW_ty G (Γ ,, A @ l1) B B' -> AW_tynf G Γ (tyPi l1 l2 A B) (tyPi l3 l4 A' B').
Proof. intros H1 H2 IHA IHB Δ r Hr. push_ren. apply actnf_pi; auto. apply IHB. now constructor. Qed.
Lemma W_actnf_ne {G Γ V V'} : AW_tyne G Γ V V' -> AW_tynf G Γ V V'.
Proof. intros IH Δ r Hr. exact (actnf_ne _ _ _ _ (IH _ _ Hr)). Qed.
Lemma W_actnf_CTyp {G Γ Δ0 Δ0' l l'} : ac_ctx G Δ0 Δ0' -> leqv l l' ->
  AW_tynf G Γ (tyCTyp Δ0 l) (tyCTyp Δ0' l').
Proof. intros Hc Hl Δ r _. push_ren. now apply actnf_CTyp. Qed.
Lemma W_actnf_CTrm {G Γ Δ0 Δ0' T T' l l'} : ac_ctx G Δ0 Δ0' -> ac_ty G Δ0 T T' -> leqv l l' ->
  AW_tynf G Γ (tyCTrm Δ0 T l) (tyCTrm Δ0' T' l').
Proof. intros Hc HT Hl Δ r _. push_ren. now apply actnf_CTrm. Qed.
Lemma W_actnf_upi {G Γ n l l' T T'} : leqv l l' -> AW_ty (gctx_uwk n G) Γ⟨ush n⟩ᵤ T T' ->
  AW_tynf G Γ (tyUPi n l T) (tyUPi n l' T').
Proof. intros Hl IH Δ r Hr. push_ren. apply actnf_upi; auto. apply IH, wkr_uren, Hr. Qed.
Lemma W_actnf_cpi {G Γ l l' T T'} : leqv l l' -> AW_ty (gext G gdCtx) Γ⟪S⟫ T T' ->
  AW_tynf G Γ (tyCPi l T) (tyCPi l' T').
Proof. intros Hl IH Δ r Hr. push_ren. apply actnf_cpi; auto. apply IH, wkr_gren, Hr. Qed.
Lemma W_actnf_tpi {G Γ Δ0 Δ0' l1 l2 l3 l4 T T'} : ac_ctx G Δ0 Δ0' -> leqv l1 l3 -> leqv l2 l4 ->
  AW_ty (gext G (gdTy Δ0 lD l1)) Γ⟪S⟫ T T' -> AW_tynf G Γ (tyTPi Δ0 l1 l2 T) (tyTPi Δ0' l3 l4 T').
Proof. intros Hc H1 H2 IH Δ r Hr. push_ren. apply actnf_tpi; auto. apply IH, wkr_gren, Hr. Qed.

Lemma W_actne_gvar {G Γ U Δ0 i' l d d'} : in_gctx (gΨ G) U (gdTy Δ0 i' l) -> AW_sub G Γ d d' Δ0 ->
  AW_tyne G Γ (tyGvar U d) (tyGvar U d').
Proof. intros Hin IH Δ r Hr. push_ren. eapply actne_gvar; [exact Hin | exact (IH _ _ Hr)]. Qed.
Lemma W_actne_El {G Γ l l' ν ν' W} : leqv l l' -> AW_tmnee G Γ ν ν' W ->
  AW_tyne G Γ (tyEl l ν) (tyEl l' ν').
Proof. intros Hl IH Δ r Hr. push_ren. eapply actne_El; [exact Hl | exact (IH _ _ Hr)]. Qed.

Lemma W_actm_red {G Γ t t' T w w' W} : reds_ty T W -> whnf_ty W -> reds t w -> reds t' w' ->
  whnf w -> whnf w' -> AW_tmnf G Γ w w' W -> AW_tm G Γ t t' T.
Proof. intros ? ? ? ? ? ? IH Δ r Hr. eapply actm_red; eauto using reds_ty_ren, whnf_ty_ren, reds_ren, whnf_ren. Qed.

Lemma W_actmnf_code_nat {G Γ l} : AW_tmnf G Γ tmNat tmNat (tyU l).
Proof. intros Δ r _. push_ren. apply actmnf_code_nat. Qed.
Lemma W_actmnf_code_U {G Γ l k k'} : leqv k k' -> AW_tmnf G Γ (tmU k) (tmU k') (tyU l).
Proof. intros H Δ r _. push_ren. now apply actmnf_code_U. Qed.
Lemma W_actmnf_code_pi {G Γ l l1 l2 l3 l4 s s' t t'} : leqv l1 l3 -> leqv l2 l4 ->
  AW_tm G Γ s s' (tyU l1) -> AW_tm G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) ->
  AW_tmnf G Γ (tmPi l1 l2 s t) (tmPi l3 l4 s' t') (tyU l).
Proof.
  intros H1 H2 IHs IHt Δ r Hr. push_ren.
  pose proof (wkr_up _ _ _ (tyEl l1 s) l1 Hr) as X. push_ren_in X.
  apply actmnf_code_pi; [exact H1 | exact H2 | exact (IHs _ _ Hr) | exact (IHt _ _ X)].
Qed.
Lemma W_actmnf_zero {G Γ} : AW_tmnf G Γ zero zero tyNat.
Proof. intros Δ r _. push_ren. apply actmnf_zero. Qed.
Lemma W_actmnf_succ {G Γ t t'} : AW_tm G Γ t t' tyNat -> AW_tmnf G Γ (succ t) (succ t') tyNat.
Proof. intros IH Δ r Hr. push_ren. apply actmnf_succ. exact (IH _ _ Hr). Qed.
Lemma W_actmnf_ne {G Γ ν ν' W W'} : posty W -> AW_tmnee G Γ ν ν' W' -> AW_tmnf G Γ ν ν' W.
Proof. intros Hp IH Δ r Hr. eapply actmnf_ne; [exact (posty_ren _ _ Hp) | exact (IH _ _ Hr)]. Qed.
Lemma W_actmnf_eta {G Γ l l' A B w w'} :
  AW_tm G (Γ ,, A @ l) (app w⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0)) (app w'⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0)) B ->
  AW_tmnf G Γ w w' (tyPi l l' A B).
Proof.
  intros IH Δ r Hr. push_ren. apply actmnf_eta.
  pose proof (IH _ (rlift r) (wkr_up _ _ _ A l Hr)) as X. push_ren_in X.
  rewrite ?shift_lift, ?shift_lift_ty, ?liftshift_lift_ty in X. exact X.
Qed.
Lemma W_actmnf_ueta {G Γ n l T w w'} :
  AW_tm (gctx_uwk n G) Γ⟨ush n⟩ᵤ (uapp w⟨ush n⟩ᵤ (ubvars n)) (uapp w'⟨ush n⟩ᵤ (ubvars n)) T ->
  AW_tmnf G Γ w w' (tyUPi n l T).
Proof.
  intros IH Δ r Hr. push_ren. apply actmnf_ueta.
  pose proof (IH _ r (wkr_uren _ _ _ _ Hr)) as X. push_ren_in X. exact X.
Qed.
Lemma W_actmnf_ceta {G Γ l T w w'} :
  AW_tm (gext G gdCtx) Γ⟪S⟫ (capp w⟪S⟫ (cvar 0)) (capp w'⟪S⟫ (cvar 0)) T -> AW_tmnf G Γ w w' (tyCPi l T).
Proof.
  intros IH Δ r Hr. push_ren. apply actmnf_ceta.
  pose proof (IH _ r (wkr_gren _ _ _ _ Hr)) as X. push_ren_in X. rewrite <- !gren_ren in X. exact X.
Qed.
Lemma W_actmnf_teta {G Γ Δ0 l l' T w w'} :
  AW_tm (gext G (gdTy Δ0 lD l)) Γ⟪S⟫ (tapp w⟪S⟫ (tyGvar 0 (lshift 0))) (tapp w'⟪S⟫ (tyGvar 0 (lshift 0))) T ->
  AW_tmnf G Γ w w' (tyTPi Δ0 l l' T).
Proof.
  intros IH Δ r Hr. push_ren. apply actmnf_teta.
  pose proof (IH _ r (wkr_gren _ _ _ _ Hr)) as X. push_ren_in X. rewrite <- !gren_ren in X. exact X.
Qed.
Lemma W_actmnf_boxT {G Γ Δ0 l T T'} : ty_leq T T' -> AW_tmnf G Γ (boxT T) (boxT T') (tyCTyp Δ0 l).
Proof. intros H Δ r _. push_ren. now apply actmnf_boxT. Qed.
Lemma W_actmnf_boxt {G Γ Δ0 A l t t'} : tm_leq t t' -> AW_tmnf G Γ (boxt t) (boxt t') (tyCTrm Δ0 A l).
Proof. intros H Δ r _. push_ren. now apply actmnf_boxt. Qed.

Lemma W_actmne_var {G Γ n T l} : in_ctx Γ n T l -> AW_tmne G Γ (var n) (var n) T.
Proof. intros Hin Δ r Hr. push_ren. eapply actmne_var. eapply in_ctx_wkr; eassumption. Qed.

Lemma W_actmne_gvar {G Γ u Δ0 i' T l d d'} : in_gctx (gΨ G) u (gdTm Δ0 i' T l) -> AW_sub G Γ d d' Δ0 ->
  AW_tmne G Γ (gvar u d) (gvar u d') T[d].
Proof.
  intros Hin IH Δ r Hr. push_ren.
  rewrite (subst_ren_ty _ _ _ _ (fun m => llk_lren _ _ m)).
  eapply actmne_gvar; [exact Hin | exact (IH _ _ Hr)].
Qed.

Lemma W_actmne_natrec {G Γ l l' M M' s s' z z' ν ν' W} : leqv l l' ->
  AW_ty G (Γ ,, tyNat @ lzero) M M' -> AW_tm G Γ s s' M[lsingle zero] ->
  AW_tm G (Γ ,, tyNat @ lzero ,, M @ l) z z' M[lsucc] -> AW_tmnee G Γ ν ν' W ->
  AW_tmne G Γ (natrec l M s z ν) (natrec l' M' s' z' ν') M[lsingle ν].
Proof.
  intros Hl IHM IHs IHz IHν Δ r Hr. push_ren. rewrite single_ren_ty.
  pose proof (wkr_up _ _ _ tyNat lzero Hr) as HrN. push_ren_in HrN.
  pose proof (wkr_up _ _ _ M l HrN) as HrM.
  eapply actmne_natrec; [exact Hl | exact (IHM _ _ HrN) | | | exact (IHν _ _ Hr)].
  - eapply ac_tm_eq; [exact (IHs _ _ Hr) | rewrite single_ren_ty; reflexivity].
  - eapply ac_tm_eq; [exact (IHz _ _ HrM) | apply lsucc_ren_ty].
Qed.

Lemma W_actmne_app {G Γ l1 l2 l3 l4 A A' B B' ν ν' s s' m m' A0 B0} :
  AW_tmnee G Γ ν ν' (tyPi m m' A0 B0) -> AW_tm G Γ s s' A0 ->
  AW_tmne G Γ (app ν l1 l2 A B s) (app ν' l3 l4 A' B' s') B0[lsingle s].
Proof.
  intros IHν IHs Δ r Hr. push_ren. rewrite single_ren_ty.
  pose proof (IHν _ _ Hr) as X. push_ren_in X.
  eapply actmne_app; [exact X | exact (IHs _ _ Hr)].
Qed.

(** The [letbox] bodies: the renaming commutes with the global shift. *)
Lemma letbox_body_ren (M : ty) (b : tm) r : (M⟪S⟫[lsingle b])⟨r⟩ = (M⟨rlift r⟩)⟪S⟫[lsingle b⟨r⟩].
Proof. rewrite single_ren_ty, <- gren_ren_ty'. reflexivity. Qed.

Lemma W_actmne_letboxT {G Γ l1 l2 l3 l4 Δ0 Δ0' M M' t1 t2 ν ν' W} : leqv l1 l3 -> leqv l2 l4 ->
  ac_ctx G Δ0 Δ0' -> AW_ty G (Γ ,, tyCTyp Δ0 l2 @ lzero) M M' ->
  AW_tm (gext G (gdTy Δ0 lC l2)) Γ⟪S⟫ t1 t2 (M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))]) ->
  AW_tmnee G Γ ν ν' W ->
  AW_tmne G Γ (letboxT l1 l2 Δ0 M t1 ν) (letboxT l3 l4 Δ0' M' t2 ν') M[lsingle ν].
Proof.
  intros H13 H24 Hc IHM IHt IHν Δ r Hr. push_ren. rewrite single_ren_ty.
  pose proof (wkr_up _ _ _ (tyCTyp Δ0 l2) lzero Hr) as HrC. push_ren_in HrC.
  eapply actmne_letboxT; [exact H13 | exact H24 | exact Hc | exact (IHM _ _ HrC) | | exact (IHν _ _ Hr)].
  eapply ac_tm_eq; [exact (IHt _ _ (wkr_gren _ _ _ S Hr)) | apply letbox_body_ren].
Qed.

Lemma W_actmne_letboxt {G Γ l1 l2 l3 l4 Δ0 Δ0' T T' M M' t1 t2 ν ν' W} : leqv l1 l3 -> leqv l2 l4 ->
  ac_ctx G Δ0 Δ0' -> ac_ty G Δ0 T T' -> AW_ty G (Γ ,, tyCTrm Δ0 T l2 @ lzero) M M' ->
  AW_tm (gext G (gdTm Δ0 lC T l2)) Γ⟪S⟫ t1 t2 (M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))]) ->
  AW_tmnee G Γ ν ν' W ->
  AW_tmne G Γ (letboxt l1 l2 Δ0 T M t1 ν) (letboxt l3 l4 Δ0' T' M' t2 ν') M[lsingle ν].
Proof.
  intros H13 H24 Hc HT IHM IHt IHν Δ r Hr. push_ren. rewrite single_ren_ty.
  pose proof (wkr_up _ _ _ (tyCTrm Δ0 T l2) lzero Hr) as HrC. push_ren_in HrC.
  eapply actmne_letboxt; [exact H13 | exact H24 | exact Hc | exact HT | exact (IHM _ _ HrC) | | exact (IHν _ _ Hr)].
  eapply ac_tm_eq; [exact (IHt _ _ (wkr_gren _ _ _ S Hr)) | apply letbox_body_ren].
Qed.

(** The recursors: motives under [⇑r], branches under [⇑ⁿr]. *)
Lemma W_branches {G Γ MT Mt l1 l2 bs bs' Δ r} : wkr r Δ Γ ->
  (forall j, j < 13 -> AW_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  forall j, j < 13 -> ac_tm (brG j G) (brΓ j Δ (wrapMT MT⟨rlift r⟩) (wrapMt Mt⟨rlift r⟩) l1 l2)
                       ((bs j)⟨rliftn (br_nl j) r⟩) ((bs' j)⟨rliftn (br_nl j) r⟩)
                       (brRes j (wrapMT MT⟨rlift r⟩) (wrapMt Mt⟨rlift r⟩)).
Proof.
  intros Hr IH j Hj. pose proof (IH j Hj _ _ (wkr_brΓ j r Δ Γ (wrapMT MT) (wrapMt Mt) l1 l2 Hj Hr)) as X.
  rewrite brRes_ren, wrapMT_ren, wrapMt_ren in X by exact Hj. exact X.
Qed.

Lemma W_actmne_elimT {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ0 Δ0' ν ν' W} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> ac_ctx G Δ0 Δ0' ->
  AW_ty (recGT G) (recΓT Γ) MT MT' -> AW_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < 13 -> AW_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  AW_tmnee G Γ ν ν' W ->
  AW_tmne G Γ (elimT l1 l2 (mkrb MT Mt bs) l Δ0 ν) (elimT l1' l2' (mkrb MT' Mt' bs') l' Δ0' ν')
    (motT (wrapMT MT) l Δ0 ν).
Proof.
  intros H1 H2 Hl Hc IHT IHt IHb IHν Δ r Hr. push_ren. rewrite !mkrb_ren, motT_ren, wrapMT_ren.
  eapply actmne_elimT; [exact H1 | exact H2 | exact Hl | exact Hc
                        | exact (IHT _ _ (wkr_recΓT _ _ _ Hr)) | exact (IHt _ _ (wkr_recΓt _ _ _ Hr))
                        | exact (W_branches Hr IHb) | exact (IHν _ _ Hr)].
Qed.

Lemma W_actmne_elimT_gvar {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ0 Δ0' U d d'} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> ac_ctx G Δ0 Δ0' ->
  AW_ty (recGT G) (recΓT Γ) MT MT' -> AW_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < 13 -> AW_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  lsub_leq d d' ->
  AW_tmne G Γ (elimT l1 l2 (mkrb MT Mt bs) l Δ0 (boxT (tyGvar U d)))
    (elimT l1' l2' (mkrb MT' Mt' bs') l' Δ0' (boxT (tyGvar U d')))
    (motT (wrapMT MT) l Δ0 (boxT (tyGvar U d))).
Proof.
  intros H1 H2 Hl Hc IHT IHt IHb Hd Δ r Hr. push_ren. rewrite !mkrb_ren, motT_ren, wrapMT_ren. push_ren.
  eapply actmne_elimT_gvar; [exact H1 | exact H2 | exact Hl | exact Hc
                             | exact (IHT _ _ (wkr_recΓT _ _ _ Hr)) | exact (IHt _ _ (wkr_recΓt _ _ _ Hr))
                             | exact (W_branches Hr IHb) | exact Hd].
Qed.

Lemma W_actmne_elimt {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ0 Δ0' T T' ν ν' W} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> ac_ctx G Δ0 Δ0' -> ac_ty G Δ0 T T' ->
  AW_ty (recGT G) (recΓT Γ) MT MT' -> AW_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < 13 -> AW_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  AW_tmnee G Γ ν ν' W ->
  AW_tmne G Γ (elimt l1 l2 (mkrb MT Mt bs) l Δ0 T ν) (elimt l1' l2' (mkrb MT' Mt' bs') l' Δ0' T' ν')
    (mott (wrapMt Mt) l Δ0 T ν).
Proof.
  intros H1 H2 Hl Hc HT IHT IHt IHb IHν Δ r Hr. push_ren. rewrite !mkrb_ren, mott_ren, wrapMt_ren.
  eapply actmne_elimt; [exact H1 | exact H2 | exact Hl | exact Hc | exact HT
                        | exact (IHT _ _ (wkr_recΓT _ _ _ Hr)) | exact (IHt _ _ (wkr_recΓt _ _ _ Hr))
                        | exact (W_branches Hr IHb) | exact (IHν _ _ Hr)].
Qed.

Lemma W_actmne_elimt_gvar {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ0 Δ0' T T' u d d'} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> ac_ctx G Δ0 Δ0' -> ac_ty G Δ0 T T' ->
  AW_ty (recGT G) (recΓT Γ) MT MT' -> AW_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < 13 -> AW_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  lsub_leq d d' ->
  AW_tmne G Γ (elimt l1 l2 (mkrb MT Mt bs) l Δ0 T (boxt (gvar u d)))
    (elimt l1' l2' (mkrb MT' Mt' bs') l' Δ0' T' (boxt (gvar u d')))
    (mott (wrapMt Mt) l Δ0 T (boxt (gvar u d))).
Proof.
  intros H1 H2 Hl Hc HT IHT IHt IHb Hd Δ r Hr. push_ren. rewrite !mkrb_ren, mott_ren, wrapMt_ren. push_ren.
  eapply actmne_elimt_gvar; [exact H1 | exact H2 | exact Hl | exact Hc | exact HT
                             | exact (IHT _ _ (wkr_recΓT _ _ _ Hr)) | exact (IHt _ _ (wkr_recΓt _ _ _ Hr))
                             | exact (W_branches Hr IHb) | exact Hd].
Qed.

Lemma W_actmne_uapp {G Γ n l T ν ν' ls ls'} : AW_tmnee G Γ ν ν' (tyUPi n l T) -> length ls = n ->
  Forall2 leqv ls ls' ->
  AW_tmne G Γ (uapp ν ls) (uapp ν' ls') T[uext ls lvar]ᵤ.
Proof.
  intros IH Hn Hls Δ r Hr. push_ren. pose proof (IH _ _ Hr) as X. push_ren_in X.
  eapply actmne_uapp; [exact X | exact Hn | exact Hls].
Qed.

Lemma W_actmne_capp {G Γ l T ν ν' Δ0 Δ0'} : AW_tmnee G Γ ν ν' (tyCPi l T) -> ac_ctx G Δ0 Δ0' ->
  AW_tmne G Γ (capp ν Δ0) (capp ν' Δ0') T⦃gsingle (GCtx Δ0)⦄.
Proof.
  intros IH Hc Δ r Hr. push_ren. rewrite gsingle_ren_ty. pose proof (IH _ _ Hr) as X. push_ren_in X.
  eapply actmne_capp; [exact X | exact Hc].
Qed.

Lemma W_actmne_tapp {G Γ Δ0 l l' T ν ν' A A'} : AW_tmnee G Γ ν ν' (tyTPi Δ0 l l' T) -> ac_ty G Δ0 A A' ->
  AW_tmne G Γ (tapp ν A) (tapp ν' A') T⦃gsingle (GTy A)⦄.
Proof.
  intros IH HA Δ r Hr. push_ren. rewrite gsingle_ren_ty. pose proof (IH _ _ Hr) as X. push_ren_in X.
  eapply actmne_tapp; [exact X | exact HA].
Qed.

Lemma W_actmnee_red {G Γ ν ν' T W} : AW_tmne G Γ ν ν' T -> reds_ty T W -> whnf_ty W ->
  AW_tmnee G Γ ν ν' W.
Proof. intros IH Hr Hw Δ r H. eapply actmnee_red; [exact (IH _ _ H) | apply reds_ty_ren, Hr | apply whnf_ty_ren, Hw]. Qed.

Lemma W_acs_pt {G Γ d d' Θ} :
  (forall n A k, in_ctx Θ n A k -> AW_tm G Γ (llk d n) (llk d' n) A[d]) -> AW_sub G Γ d d' Θ.
Proof.
  intros IH Δ r Hr. apply acs_pt. intros n A k Hin. rewrite !llk_lren.
  rewrite <- (subst_ren_ty A _ _ _ (fun m => llk_lren _ _ m)). exact (IH n A k Hin _ _ Hr).
Qed.

Theorem ac_wk_all :
  (forall G Γ T T', ac_ty G Γ T T' -> AW_ty G Γ T T') /\
  (forall G Γ W W', ac_tynf G Γ W W' -> AW_tynf G Γ W W') /\
  (forall G Γ V V', ac_tyne G Γ V V' -> AW_tyne G Γ V V') /\
  (forall G Δ Δ', ac_ctx G Δ Δ' -> True) /\
  (forall G Γ t t' T, ac_tm G Γ t t' T -> AW_tm G Γ t t' T) /\
  (forall G Γ w w' W, ac_tmnf G Γ w w' W -> AW_tmnf G Γ w w' W) /\
  (forall G Γ ν ν' T, ac_tmne G Γ ν ν' T -> AW_tmne G Γ ν ν' T) /\
  (forall G Γ ν ν' W, ac_tmnee G Γ ν ν' W -> AW_tmnee G Γ ν ν' W) /\
  (forall G Γ d d' Δ, ac_sub G Γ d d' Δ -> AW_sub G Γ d d' Δ).
Proof.
  apply ac_mut; intros; try exact I;
    first
    [ solve [eapply W_act_red; eassumption] | solve [eapply W_actnf_nat] | solve [eapply W_actnf_U; eassumption]
    | solve [eapply W_actnf_pi; eassumption] | solve [eapply W_actnf_ne; eassumption]
    | solve [eapply W_actnf_CTyp; eassumption] | solve [eapply W_actnf_CTrm; eassumption]
    | solve [eapply W_actnf_upi; eassumption] | solve [eapply W_actnf_cpi; eassumption]
    | solve [eapply W_actnf_tpi; eassumption]
    | solve [eapply W_actne_gvar; eassumption] | solve [eapply W_actne_El; eassumption]
    | solve [eapply W_actm_red; eassumption]
    | solve [eapply W_actmnf_code_nat] | solve [eapply W_actmnf_code_U; eassumption]
    | solve [eapply W_actmnf_code_pi; eassumption] | solve [eapply W_actmnf_zero]
    | solve [eapply W_actmnf_succ; eassumption] | solve [eapply W_actmnf_ne; eassumption]
    | solve [eapply W_actmnf_eta; eassumption] | solve [eapply W_actmnf_ueta; eassumption]
    | solve [eapply W_actmnf_ceta; eassumption] | solve [eapply W_actmnf_teta; eassumption]
    | solve [eapply W_actmnf_boxT; eassumption] | solve [eapply W_actmnf_boxt; eassumption]
    | solve [eapply W_actmne_var; eassumption] | solve [eapply W_actmne_gvar; eassumption]
    | solve [eapply W_actmne_natrec; eassumption] | solve [eapply W_actmne_app; eassumption]
    | solve [eapply W_actmne_letboxT; eassumption] | solve [eapply W_actmne_letboxt; eassumption]
    | solve [eapply W_actmne_elimT; eassumption] | solve [eapply W_actmne_elimT_gvar; eassumption]
    | solve [eapply W_actmne_elimt; eassumption] | solve [eapply W_actmne_elimt_gvar; eassumption]
    | solve [eapply W_actmne_uapp; eassumption] | solve [eapply W_actmne_capp; eassumption]
    | solve [eapply W_actmne_tapp; eassumption] | solve [eapply W_actmnee_red; eassumption]
    | solve [eapply W_acs_pt; eassumption] ].
Qed.

(** ** Global weakening

    The algorithm checks no level against the universe context, but the
    scopes it builds ([gctx_uwk], [recGT], [brG]) mention it, so the
    statement is at a [gwk_ok] weakening. *)

Ltac push_gren_in H := revert H; push_gren; intros H.

Lemma posty_gren W ξ : posty W -> posty W⟪ξ⟫.
Proof.
  destruct 1; cbn; first [apply posty_nat | apply posty_U | apply posty_CTyp | apply posty_CTrm | idtac].
  apply posty_ne, whne_ty_gren; assumption.
Qed.

Lemma gwk_ok_ext {γ G' G} D : gwk_ok γ G' G -> gwk_ok (gwk_up γ) (gext G' (gdecl_ren D γ)) (gext G D).
Proof. intros [HL Hw]; split; [exact HL | exact (gwkwf_up _ _ _ D Hw)]. Qed.
Lemma gwk_ok_uwk {γ G' G} n : gwk_ok γ G' G -> gwk_ok γ (gctx_uwk n G') (gctx_uwk n G).
Proof. intros [HL Hw]; split; [cbn; lia | exact (gwk_wf_uren _ _ _ (ush n) Hw)]. Qed.
Lemma gwk_ok_recGT {γ G' G} : gwk_ok γ G' G -> gwk_ok (gwk_up γ) (recGT G') (recGT G).
Proof. intros H; split; [cbn; destruct H; lia | exact (recGT_gwk _ _ _ H)]. Qed.
Lemma gwk_ok_recGt {γ G' G} : gwk_ok γ G' G -> gwk_ok (gwk_up (gwk_up γ)) (recGt G') (recGt G).
Proof. intros H; split; [cbn; destruct H; lia | exact (recGt_gwk _ _ _ H)]. Qed.
Lemma gwk_ok_brG {γ G' G} k : k < 13 -> gwk_ok γ G' G -> gwk_ok (gwk_upn (br_ng k) γ) (brG k G') (brG k G).
Proof. intros Hk H; split; [cbn; destruct H; lia | exact (brG_gwk _ _ _ _ Hk H)]. Qed.

Definition AG_ty G Γ T T' : Prop := forall G' (γ : gweak), gwk_ok γ G' G -> ac_ty G' Γ⟪γ⟫ T⟪γ⟫ T'⟪γ⟫.
Definition AG_tynf G Γ T T' : Prop := forall G' (γ : gweak), gwk_ok γ G' G -> ac_tynf G' Γ⟪γ⟫ T⟪γ⟫ T'⟪γ⟫.
Definition AG_tyne G Γ T T' : Prop := forall G' (γ : gweak), gwk_ok γ G' G -> ac_tyne G' Γ⟪γ⟫ T⟪γ⟫ T'⟪γ⟫.
Definition AG_ctx G Δ Δ' : Prop := forall G' (γ : gweak), gwk_ok γ G' G -> ac_ctx G' Δ⟪γ⟫ Δ'⟪γ⟫.
Definition AG_tm G Γ t t' T : Prop := forall G' (γ : gweak), gwk_ok γ G' G -> ac_tm G' Γ⟪γ⟫ t⟪γ⟫ t'⟪γ⟫ T⟪γ⟫.
Definition AG_tmnf G Γ t t' T : Prop := forall G' (γ : gweak), gwk_ok γ G' G -> ac_tmnf G' Γ⟪γ⟫ t⟪γ⟫ t'⟪γ⟫ T⟪γ⟫.
Definition AG_tmne G Γ t t' T : Prop := forall G' (γ : gweak), gwk_ok γ G' G -> ac_tmne G' Γ⟪γ⟫ t⟪γ⟫ t'⟪γ⟫ T⟪γ⟫.
Definition AG_tmnee G Γ t t' T : Prop := forall G' (γ : gweak), gwk_ok γ G' G -> ac_tmnee G' Γ⟪γ⟫ t⟪γ⟫ t'⟪γ⟫ T⟪γ⟫.
Definition AG_sub G Γ d d' Θ : Prop := forall G' (γ : gweak), gwk_ok γ G' G ->
  ac_sub G' Γ⟪γ⟫ d⟪γ⟫ d'⟪γ⟫ Θ⟪γ⟫.

Lemma G_act_red {G Γ T T' W W'} : reds_ty T W -> reds_ty T' W' -> whnf_ty W -> whnf_ty W' ->
  AG_tynf G Γ W W' -> AG_ty G Γ T T'.
Proof. intros ? ? ? ? IH G' γ Hγ. eapply act_red; eauto using reds_ty_gren, whnf_ty_gren. Qed.
Lemma G_actnf_nat {G Γ} : AG_tynf G Γ tyNat tyNat.
Proof. intros G' γ _. apply actnf_nat. Qed.
Lemma G_actnf_U {G Γ l l'} : leqv l l' -> AG_tynf G Γ (tyU l) (tyU l').
Proof. intros H G' γ _. now apply actnf_U. Qed.
Lemma G_actnf_pi {G Γ l1 l2 l3 l4 A A' B B'} : leqv l1 l3 -> leqv l2 l4 ->
  AG_ty G Γ A A' -> AG_ty G (Γ ,, A @ l1) B B' -> AG_tynf G Γ (tyPi l1 l2 A B) (tyPi l3 l4 A' B').
Proof.
  intros H1 H2 IHA IHB G' γ Hγ. push_gren.
  pose proof (IHB _ _ Hγ) as X. push_gren_in X.
  apply actnf_pi; [exact H1 | exact H2 | exact (IHA _ _ Hγ) | exact X].
Qed.
Lemma G_actnf_ne {G Γ V V'} : AG_tyne G Γ V V' -> AG_tynf G Γ V V'.
Proof. intros IH G' γ Hγ. exact (actnf_ne _ _ _ _ (IH _ _ Hγ)). Qed.
Lemma G_actnf_CTyp {G Γ Δ0 Δ0' l l'} : AG_ctx G Δ0 Δ0' -> leqv l l' ->
  AG_tynf G Γ (tyCTyp Δ0 l) (tyCTyp Δ0' l').
Proof. intros IH Hl G' γ Hγ. push_gren. exact (actnf_CTyp _ _ _ _ _ _ (IH _ _ Hγ) Hl). Qed.
Lemma G_actnf_CTrm {G Γ Δ0 Δ0' T T' l l'} : AG_ctx G Δ0 Δ0' -> AG_ty G Δ0 T T' -> leqv l l' ->
  AG_tynf G Γ (tyCTrm Δ0 T l) (tyCTrm Δ0' T' l').
Proof. intros IHc IHT Hl G' γ Hγ. push_gren. exact (actnf_CTrm _ _ _ _ _ _ _ _ (IHc _ _ Hγ) (IHT _ _ Hγ) Hl). Qed.
Lemma G_actnf_upi {G Γ n l l' T T'} : leqv l l' -> AG_ty (gctx_uwk n G) Γ⟨ush n⟩ᵤ T T' ->
  AG_tynf G Γ (tyUPi n l T) (tyUPi n l' T').
Proof.
  intros Hl IH G' γ Hγ. push_gren. apply actnf_upi; [exact Hl |].
  pose proof (IH _ _ (gwk_ok_uwk n Hγ)) as X. rewrite gren_uren_ctx in X. exact X.
Qed.
Lemma G_actnf_cpi {G Γ l l' T T'} : leqv l l' -> AG_ty (gext G gdCtx) Γ⟪S⟫ T T' ->
  AG_tynf G Γ (tyCPi l T) (tyCPi l' T').
Proof.
  intros Hl IH G' γ Hγ. push_gren. apply actnf_cpi; [exact Hl |].
  pose proof (IH _ _ (gwk_ok_ext gdCtx Hγ)) as X. cbn [gwk_fn] in X. rewrite gcren_shift_up in X. exact X.
Qed.
Lemma G_actnf_tpi {G Γ Δ0 Δ0' l1 l2 l3 l4 T T'} : AG_ctx G Δ0 Δ0' -> leqv l1 l3 -> leqv l2 l4 ->
  AG_ty (gext G (gdTy Δ0 lD l1)) Γ⟪S⟫ T T' -> AG_tynf G Γ (tyTPi Δ0 l1 l2 T) (tyTPi Δ0' l3 l4 T').
Proof.
  intros IHc H1 H2 IH G' γ Hγ. push_gren. apply actnf_tpi; [exact (IHc _ _ Hγ) | exact H1 | exact H2 |].
  pose proof (IH _ _ (gwk_ok_ext (gdTy Δ0 lD l1) Hγ)) as X. cbn [gwk_fn] in X. rewrite gcren_shift_up in X.
  exact X.
Qed.
Lemma G_actne_gvar {G Γ U Δ0 i' l d d'} : in_gctx (gΨ G) U (gdTy Δ0 i' l) -> AG_sub G Γ d d' Δ0 ->
  AG_tyne G Γ (tyGvar U d) (tyGvar U d').
Proof.
  intros Hin IH G' γ Hγ. push_gren.
  eapply actne_gvar; [exact (in_gctx_gwk _ _ _ _ _ (proj2 Hγ) Hin) | exact (IH _ _ Hγ)].
Qed.
Lemma G_actne_El {G Γ l l' ν ν' W} : leqv l l' -> AG_tmnee G Γ ν ν' W -> AG_tyne G Γ (tyEl l ν) (tyEl l' ν').
Proof. intros Hl IH G' γ Hγ. push_gren. eapply actne_El; [exact Hl | exact (IH _ _ Hγ)]. Qed.
Lemma G_acc_nil {G} : AG_ctx G cnil cnil.
Proof. intros G' γ _. apply acc_nil. Qed.
Lemma G_acc_var {G g} : AG_ctx G (cvar g) (cvar g).
Proof. intros G' γ _. push_gren. apply acc_var. Qed.
Lemma G_acc_ext {G Γ Γ' A A' l l'} : AG_ctx G Γ Γ' -> AG_ty G Γ A A' -> leqv l l' ->
  AG_ctx G (Γ ,, A @ l) (Γ' ,, A' @ l').
Proof. intros IHc IHA Hl G' γ Hγ. push_gren. exact (acc_ext _ _ _ _ _ _ _ (IHc _ _ Hγ) (IHA _ _ Hγ) Hl). Qed.

Lemma G_actm_red {G Γ t t' T w w' W} : reds_ty T W -> whnf_ty W -> reds t w -> reds t' w' ->
  whnf w -> whnf w' -> AG_tmnf G Γ w w' W -> AG_tm G Γ t t' T.
Proof. intros ? ? ? ? ? ? IH G' γ Hγ. eapply actm_red; eauto using reds_ty_gren, whnf_ty_gren, reds_gren, whnf_gren. Qed.
Lemma G_actmnf_code_nat {G Γ l} : AG_tmnf G Γ tmNat tmNat (tyU l).
Proof. intros G' γ _. push_gren. apply actmnf_code_nat. Qed.
Lemma G_actmnf_code_U {G Γ l k k'} : leqv k k' -> AG_tmnf G Γ (tmU k) (tmU k') (tyU l).
Proof. intros H G' γ _. push_gren. now apply actmnf_code_U. Qed.
Lemma G_actmnf_code_pi {G Γ l l1 l2 l3 l4 s s' t t'} : leqv l1 l3 -> leqv l2 l4 ->
  AG_tm G Γ s s' (tyU l1) -> AG_tm G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) ->
  AG_tmnf G Γ (tmPi l1 l2 s t) (tmPi l3 l4 s' t') (tyU l).
Proof.
  intros H1 H2 IHs IHt G' γ Hγ. push_gren. pose proof (IHt _ _ Hγ) as X. push_gren_in X.
  apply actmnf_code_pi; [exact H1 | exact H2 | exact (IHs _ _ Hγ) | exact X].
Qed.
Lemma G_actmnf_zero {G Γ} : AG_tmnf G Γ zero zero tyNat.
Proof. intros G' γ _. push_gren. apply actmnf_zero. Qed.
Lemma G_actmnf_succ {G Γ t t'} : AG_tm G Γ t t' tyNat -> AG_tmnf G Γ (succ t) (succ t') tyNat.
Proof. intros IH G' γ Hγ. push_gren. apply actmnf_succ. exact (IH _ _ Hγ). Qed.
Lemma G_actmnf_ne {G Γ ν ν' W W'} : posty W -> AG_tmnee G Γ ν ν' W' -> AG_tmnf G Γ ν ν' W.
Proof. intros Hp IH G' γ Hγ. eapply actmnf_ne; [exact (posty_gren _ _ Hp) | exact (IH _ _ Hγ)]. Qed.
Lemma G_actmnf_eta {G Γ l l' A B w w'} :
  AG_tm G (Γ ,, A @ l) (app w⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0)) (app w'⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0)) B ->
  AG_tmnf G Γ w w' (tyPi l l' A B).
Proof.
  intros IH G' γ Hγ. push_gren. apply actmnf_eta.
  pose proof (IH _ _ Hγ) as X. push_gren_in X. rewrite ?gren_ren, ?gren_ren_ty' in X. exact X.
Qed.
Lemma G_actmnf_ueta {G Γ n l T w w'} :
  AG_tm (gctx_uwk n G) Γ⟨ush n⟩ᵤ (uapp w⟨ush n⟩ᵤ (ubvars n)) (uapp w'⟨ush n⟩ᵤ (ubvars n)) T ->
  AG_tmnf G Γ w w' (tyUPi n l T).
Proof.
  intros IH G' γ Hγ. push_gren. apply actmnf_ueta.
  pose proof (IH _ _ (gwk_ok_uwk n Hγ)) as X. push_gren_in X. rewrite ?gren_uren_ctx in X. exact X.
Qed.
Lemma G_actmnf_ceta {G Γ l T w w'} :
  AG_tm (gext G gdCtx) Γ⟪S⟫ (capp w⟪S⟫ (cvar 0)) (capp w'⟪S⟫ (cvar 0)) T -> AG_tmnf G Γ w w' (tyCPi l T).
Proof.
  intros IH G' γ Hγ. push_gren. apply actmnf_ceta.
  pose proof (IH _ _ (gwk_ok_ext gdCtx Hγ)) as X. cbn [gwk_fn] in X. push_gren_in X.
  rewrite gcren_shift_up, !gren_shift_up_tm in X. exact X.
Qed.
Lemma G_actmnf_teta {G Γ Δ0 l l' T w w'} :
  AG_tm (gext G (gdTy Δ0 lD l)) Γ⟪S⟫ (tapp w⟪S⟫ (tyGvar 0 (lshift 0))) (tapp w'⟪S⟫ (tyGvar 0 (lshift 0))) T ->
  AG_tmnf G Γ w w' (tyTPi Δ0 l l' T).
Proof.
  intros IH G' γ Hγ. push_gren. apply actmnf_teta.
  pose proof (IH _ _ (gwk_ok_ext (gdTy Δ0 lD l) Hγ)) as X. cbn [gwk_fn] in X. push_gren_in X.
  rewrite gcren_shift_up, !gren_shift_up_tm in X. exact X.
Qed.
Lemma G_actmnf_boxT {G Γ Δ0 l T T'} : ty_leq T T' -> AG_tmnf G Γ (boxT T) (boxT T') (tyCTyp Δ0 l).
Proof. intros H G' γ _. push_gren. apply actmnf_boxT. apply (proj1 leq_gren_all); assumption. Qed.
Lemma G_actmnf_boxt {G Γ Δ0 A l t t'} : tm_leq t t' -> AG_tmnf G Γ (boxt t) (boxt t') (tyCTrm Δ0 A l).
Proof. intros H G' γ _. push_gren. apply actmnf_boxt. apply (proj1 (proj2 leq_gren_all)); assumption. Qed.

Lemma G_actmne_var {G Γ n T l} : in_ctx Γ n T l -> AG_tmne G Γ (var n) (var n) T.
Proof. intros Hin G' γ _. push_gren. eapply actmne_var. exact (in_ctx_gren _ _ _ _ _ Hin). Qed.

Lemma G_actmne_gvar {G Γ u Δ0 i' T l d d'} : in_gctx (gΨ G) u (gdTm Δ0 i' T l) -> AG_sub G Γ d d' Δ0 ->
  AG_tmne G Γ (gvar u d) (gvar u d') T[d].
Proof.
  intros Hin IH G' γ Hγ. push_gren. rewrite gren_subst_ty.
  eapply actmne_gvar; [exact (in_gctx_gwk _ _ _ _ _ (proj2 Hγ) Hin) | exact (IH _ _ Hγ)].
Qed.

Lemma G_actmne_natrec {G Γ l l' M M' s s' z z' ν ν' W} : leqv l l' ->
  AG_ty G (Γ ,, tyNat @ lzero) M M' -> AG_tm G Γ s s' M[lsingle zero] ->
  AG_tm G (Γ ,, tyNat @ lzero ,, M @ l) z z' M[lsucc] -> AG_tmnee G Γ ν ν' W ->
  AG_tmne G Γ (natrec l M s z ν) (natrec l' M' s' z' ν') M[lsingle ν].
Proof.
  intros Hl IHM IHs IHz IHν G' γ Hγ. push_gren. rewrite gren_single_ty.
  pose proof (IHM _ _ Hγ) as XM. push_gren_in XM.
  pose proof (IHs _ _ Hγ) as Xs. rewrite gren_single_ty in Xs. push_gren_in Xs.
  pose proof (IHz _ _ Hγ) as Xz. rewrite gren_lsucc_ty in Xz. push_gren_in Xz.
  eapply actmne_natrec; [exact Hl | exact XM | exact Xs | exact Xz | exact (IHν _ _ Hγ)].
Qed.

Lemma G_actmne_app {G Γ l1 l2 l3 l4 A A' B B' ν ν' s s' m m' A0 B0} :
  AG_tmnee G Γ ν ν' (tyPi m m' A0 B0) -> AG_tm G Γ s s' A0 ->
  AG_tmne G Γ (app ν l1 l2 A B s) (app ν' l3 l4 A' B' s') B0[lsingle s].
Proof.
  intros IHν IHs G' γ Hγ. push_gren. rewrite gren_single_ty.
  pose proof (IHν _ _ Hγ) as X. push_gren_in X.
  eapply actmne_app; [exact X | exact (IHs _ _ Hγ)].
Qed.

Lemma G_actmne_letboxT {G Γ l1 l2 l3 l4 Δ0 Δ0' M M' t1 t2 ν ν' W} : leqv l1 l3 -> leqv l2 l4 ->
  AG_ctx G Δ0 Δ0' -> AG_ty G (Γ ,, tyCTyp Δ0 l2 @ lzero) M M' ->
  AG_tm (gext G (gdTy Δ0 lC l2)) Γ⟪S⟫ t1 t2 (M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))]) ->
  AG_tmnee G Γ ν ν' W ->
  AG_tmne G Γ (letboxT l1 l2 Δ0 M t1 ν) (letboxT l3 l4 Δ0' M' t2 ν') M[lsingle ν].
Proof.
  intros H13 H24 IHc IHM IHt IHν G' γ Hγ. push_gren. rewrite gren_single_ty.
  pose proof (IHM _ _ Hγ) as XM. push_gren_in XM.
  pose proof (IHt _ _ (gwk_ok_ext (gdTy Δ0 lC l2) Hγ)) as Xt. cbn [gwk_fn gdecl_ren] in Xt.
  rewrite gcren_shift_up, gren_letbox_ty in Xt by reflexivity.
  eapply actmne_letboxT; [exact H13 | exact H24 | exact (IHc _ _ Hγ) | exact XM | exact Xt | exact (IHν _ _ Hγ)].
Qed.

Lemma G_actmne_letboxt {G Γ l1 l2 l3 l4 Δ0 Δ0' T T' M M' t1 t2 ν ν' W} : leqv l1 l3 -> leqv l2 l4 ->
  AG_ctx G Δ0 Δ0' -> AG_ty G Δ0 T T' -> AG_ty G (Γ ,, tyCTrm Δ0 T l2 @ lzero) M M' ->
  AG_tm (gext G (gdTm Δ0 lC T l2)) Γ⟪S⟫ t1 t2 (M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))]) ->
  AG_tmnee G Γ ν ν' W ->
  AG_tmne G Γ (letboxt l1 l2 Δ0 T M t1 ν) (letboxt l3 l4 Δ0' T' M' t2 ν') M[lsingle ν].
Proof.
  intros H13 H24 IHc IHT IHM IHt IHν G' γ Hγ. push_gren. rewrite gren_single_ty.
  pose proof (IHM _ _ Hγ) as XM. push_gren_in XM.
  pose proof (IHt _ _ (gwk_ok_ext (gdTm Δ0 lC T l2) Hγ)) as Xt. cbn [gwk_fn gdecl_ren] in Xt.
  rewrite gcren_shift_up, gren_letbox_ty in Xt by reflexivity.
  eapply actmne_letboxt; [exact H13 | exact H24 | exact (IHc _ _ Hγ) | exact (IHT _ _ Hγ) | exact XM | exact Xt
                         | exact (IHν _ _ Hγ)].
Qed.

Lemma G_branches {G Γ MT Mt l1 l2 bs bs' G' γ} : gwk_ok γ G' G ->
  (forall j, j < 13 -> AG_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  forall j, j < 13 -> ac_tm (brG j G') (brΓ j Γ⟪γ⟫ (wrapMT MT⟪gupr γ⟫) (wrapMt Mt⟪gupr (gupr γ)⟫) l1 l2)
                       ((bs j)⟪guprn (br_ng j) γ⟫) ((bs' j)⟪guprn (br_ng j) γ⟫)
                       (brRes j (wrapMT MT⟪gupr γ⟫) (wrapMt Mt⟪gupr (gupr γ)⟫)).
Proof.
  intros Hγ IH j Hj. pose proof (IH j Hj _ _ (gwk_ok_brG j Hj Hγ)) as X.
  rewrite ?gren_gwk_upn_ctx, ?gren_gwk_upn_tm, ?gren_gwk_upn_ty in X.
  rewrite brΓ_gren, brRes_gren, ?wrapMT_gren, ?wrapMt_gren in X by exact Hj. exact X.
Qed.

Lemma G_actmne_elimT {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ0 Δ0' ν ν' W} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> AG_ctx G Δ0 Δ0' ->
  AG_ty (recGT G) (recΓT Γ) MT MT' -> AG_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < 13 -> AG_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  AG_tmnee G Γ ν ν' W ->
  AG_tmne G Γ (elimT l1 l2 (mkrb MT Mt bs) l Δ0 ν) (elimT l1' l2' (mkrb MT' Mt' bs') l' Δ0' ν')
    (motT (wrapMT MT) l Δ0 ν).
Proof.
  intros H1 H2 Hl IHc IHT IHt IHb IHν G' γ Hγ. push_gren. rewrite !mkrb_gren, motT_gren, wrapMT_gren.
  pose proof (IHT _ _ (gwk_ok_recGT Hγ)) as XT. cbn [gwk_fn] in XT. rewrite recΓT_gren in XT.
  pose proof (IHt _ _ (gwk_ok_recGt Hγ)) as Xt. cbn [gwk_fn] in Xt. rewrite recΓt_gren in Xt.
  eapply actmne_elimT; [exact H1 | exact H2 | exact Hl | exact (IHc _ _ Hγ) | exact XT | exact Xt
                        | exact (G_branches Hγ IHb) | exact (IHν _ _ Hγ)].
Qed.

Lemma G_actmne_elimT_gvar {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ0 Δ0' U d d'} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> AG_ctx G Δ0 Δ0' ->
  AG_ty (recGT G) (recΓT Γ) MT MT' -> AG_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < 13 -> AG_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  lsub_leq d d' ->
  AG_tmne G Γ (elimT l1 l2 (mkrb MT Mt bs) l Δ0 (boxT (tyGvar U d)))
    (elimT l1' l2' (mkrb MT' Mt' bs') l' Δ0' (boxT (tyGvar U d')))
    (motT (wrapMT MT) l Δ0 (boxT (tyGvar U d))).
Proof.
  intros H1 H2 Hl IHc IHT IHt IHb Hd G' γ Hγ. push_gren. rewrite !mkrb_gren, motT_gren, wrapMT_gren. push_gren.
  pose proof (IHT _ _ (gwk_ok_recGT Hγ)) as XT. cbn [gwk_fn] in XT. rewrite recΓT_gren in XT.
  pose proof (IHt _ _ (gwk_ok_recGt Hγ)) as Xt. cbn [gwk_fn] in Xt. rewrite recΓt_gren in Xt.
  eapply actmne_elimT_gvar; [exact H1 | exact H2 | exact Hl | exact (IHc _ _ Hγ) | exact XT | exact Xt
                             | exact (G_branches Hγ IHb) | exact (proj2 (proj2 (proj2 leq_gren_all)) _ _ _ Hd)].
Qed.

Lemma G_actmne_elimt {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ0 Δ0' T T' ν ν' W} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> AG_ctx G Δ0 Δ0' -> AG_ty G Δ0 T T' ->
  AG_ty (recGT G) (recΓT Γ) MT MT' -> AG_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < 13 -> AG_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  AG_tmnee G Γ ν ν' W ->
  AG_tmne G Γ (elimt l1 l2 (mkrb MT Mt bs) l Δ0 T ν) (elimt l1' l2' (mkrb MT' Mt' bs') l' Δ0' T' ν')
    (mott (wrapMt Mt) l Δ0 T ν).
Proof.
  intros H1 H2 Hl IHc IHi IHT IHt IHb IHν G' γ Hγ. push_gren. rewrite !mkrb_gren, mott_gren, wrapMt_gren.
  pose proof (IHT _ _ (gwk_ok_recGT Hγ)) as XT. cbn [gwk_fn] in XT. rewrite recΓT_gren in XT.
  pose proof (IHt _ _ (gwk_ok_recGt Hγ)) as Xt. cbn [gwk_fn] in Xt. rewrite recΓt_gren in Xt.
  eapply actmne_elimt; [exact H1 | exact H2 | exact Hl | exact (IHc _ _ Hγ) | exact (IHi _ _ Hγ) | exact XT | exact Xt
                        | exact (G_branches Hγ IHb) | exact (IHν _ _ Hγ)].
Qed.

Lemma G_actmne_elimt_gvar {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ0 Δ0' T T' u d d'} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> AG_ctx G Δ0 Δ0' -> AG_ty G Δ0 T T' ->
  AG_ty (recGT G) (recΓT Γ) MT MT' -> AG_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < 13 -> AG_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  lsub_leq d d' ->
  AG_tmne G Γ (elimt l1 l2 (mkrb MT Mt bs) l Δ0 T (boxt (gvar u d)))
    (elimt l1' l2' (mkrb MT' Mt' bs') l' Δ0' T' (boxt (gvar u d')))
    (mott (wrapMt Mt) l Δ0 T (boxt (gvar u d))).
Proof.
  intros H1 H2 Hl IHc IHi IHT IHt IHb Hd G' γ Hγ. push_gren. rewrite !mkrb_gren, mott_gren, wrapMt_gren. push_gren.
  pose proof (IHT _ _ (gwk_ok_recGT Hγ)) as XT. cbn [gwk_fn] in XT. rewrite recΓT_gren in XT.
  pose proof (IHt _ _ (gwk_ok_recGt Hγ)) as Xt. cbn [gwk_fn] in Xt. rewrite recΓt_gren in Xt.
  eapply actmne_elimt_gvar; [exact H1 | exact H2 | exact Hl | exact (IHc _ _ Hγ) | exact (IHi _ _ Hγ) | exact XT
                             | exact Xt | exact (G_branches Hγ IHb)
                             | exact (proj2 (proj2 (proj2 leq_gren_all)) _ _ _ Hd)].
Qed.

Lemma G_actmne_uapp {G Γ n l T ν ν' ls ls'} : AG_tmnee G Γ ν ν' (tyUPi n l T) -> length ls = n ->
  Forall2 leqv ls ls' ->
  AG_tmne G Γ (uapp ν ls) (uapp ν' ls') T[uext ls lvar]ᵤ.
Proof.
  intros IH Hn Hls G' γ Hγ. push_gren. pose proof (IH _ _ Hγ) as X. push_gren_in X.
  eapply actmne_uapp; [exact X | exact Hn | exact Hls].
Qed.

Lemma G_actmne_capp {G Γ l T ν ν' Δ0 Δ0'} : AG_tmnee G Γ ν ν' (tyCPi l T) -> AG_ctx G Δ0 Δ0' ->
  AG_tmne G Γ (capp ν Δ0) (capp ν' Δ0') T⦃gsingle (GCtx Δ0)⦄.
Proof.
  intros IH IHc G' γ Hγ. push_gren. rewrite gren_gsingle_ty. cbn [goren].
  pose proof (IH _ _ Hγ) as X. push_gren_in X.
  eapply actmne_capp; [exact X | exact (IHc _ _ Hγ)].
Qed.

Lemma G_actmne_tapp {G Γ Δ0 l l' T ν ν' A A'} : AG_tmnee G Γ ν ν' (tyTPi Δ0 l l' T) -> AG_ty G Δ0 A A' ->
  AG_tmne G Γ (tapp ν A) (tapp ν' A') T⦃gsingle (GTy A)⦄.
Proof.
  intros IH IHA G' γ Hγ. push_gren. rewrite gren_gsingle_ty. cbn [goren].
  pose proof (IH _ _ Hγ) as X. push_gren_in X.
  eapply actmne_tapp; [exact X | exact (IHA _ _ Hγ)].
Qed.

Lemma G_actmnee_red {G Γ ν ν' T W} : AG_tmne G Γ ν ν' T -> reds_ty T W -> whnf_ty W ->
  AG_tmnee G Γ ν ν' W.
Proof. intros IH Hr Hw G' γ Hγ. eapply actmnee_red; [exact (IH _ _ Hγ) | apply reds_ty_gren, Hr | apply whnf_ty_gren, Hw]. Qed.

Lemma G_acs_pt {G Γ d d' Θ} :
  (forall n A k, in_ctx Θ n A k -> AG_tm G Γ (llk d n) (llk d' n) A[d]) -> AG_sub G Γ d d' Θ.
Proof.
  intros IH G' γ Hγ. apply acs_pt. intros n A k Hin.
  destruct (in_ctx_gren_inv _ _ _ _ _ Hin) as (A0 & Hin0 & ->).
  change (llk (glren d γ) n) with (llk d⟪γ⟫ n). change (llk (glren d' γ) n) with (llk d'⟪γ⟫ n).
  rewrite !llk_glren, <- gren_subst_ty. exact (IH n A0 k Hin0 _ _ Hγ).
Qed.

Theorem ac_gwk_all :
  (forall G Γ T T', ac_ty G Γ T T' -> AG_ty G Γ T T') /\
  (forall G Γ W W', ac_tynf G Γ W W' -> AG_tynf G Γ W W') /\
  (forall G Γ V V', ac_tyne G Γ V V' -> AG_tyne G Γ V V') /\
  (forall G Δ Δ', ac_ctx G Δ Δ' -> AG_ctx G Δ Δ') /\
  (forall G Γ t t' T, ac_tm G Γ t t' T -> AG_tm G Γ t t' T) /\
  (forall G Γ w w' W, ac_tmnf G Γ w w' W -> AG_tmnf G Γ w w' W) /\
  (forall G Γ ν ν' T, ac_tmne G Γ ν ν' T -> AG_tmne G Γ ν ν' T) /\
  (forall G Γ ν ν' W, ac_tmnee G Γ ν ν' W -> AG_tmnee G Γ ν ν' W) /\
  (forall G Γ d d' Δ, ac_sub G Γ d d' Δ -> AG_sub G Γ d d' Δ).
Proof.
  apply ac_mut; intros;
    first
    [ solve [eapply G_act_red; eassumption] | solve [eapply G_actnf_nat] | solve [eapply G_actnf_U; eassumption]
    | solve [eapply G_actnf_pi; eassumption] | solve [eapply G_actnf_ne; eassumption]
    | solve [eapply G_actnf_CTyp; eassumption] | solve [eapply G_actnf_CTrm; eassumption]
    | solve [eapply G_actnf_upi; eassumption] | solve [eapply G_actnf_cpi; eassumption]
    | solve [eapply G_actnf_tpi; eassumption]
    | solve [eapply G_actne_gvar; eassumption] | solve [eapply G_actne_El; eassumption]
    | solve [eapply G_acc_nil] | solve [eapply G_acc_var] | solve [eapply G_acc_ext; eassumption]
    | solve [eapply G_actm_red; eassumption]
    | solve [eapply G_actmnf_code_nat] | solve [eapply G_actmnf_code_U; eassumption]
    | solve [eapply G_actmnf_code_pi; eassumption] | solve [eapply G_actmnf_zero]
    | solve [eapply G_actmnf_succ; eassumption] | solve [eapply G_actmnf_ne; eassumption]
    | solve [eapply G_actmnf_eta; eassumption] | solve [eapply G_actmnf_ueta; eassumption]
    | solve [eapply G_actmnf_ceta; eassumption] | solve [eapply G_actmnf_teta; eassumption]
    | solve [eapply G_actmnf_boxT; eassumption] | solve [eapply G_actmnf_boxt; eassumption]
    | solve [eapply G_actmne_var; eassumption] | solve [eapply G_actmne_gvar; eassumption]
    | solve [eapply G_actmne_natrec; eassumption] | solve [eapply G_actmne_app; eassumption]
    | solve [eapply G_actmne_letboxT; eassumption] | solve [eapply G_actmne_letboxt; eassumption]
    | solve [eapply G_actmne_elimT; eassumption] | solve [eapply G_actmne_elimT_gvar; eassumption]
    | solve [eapply G_actmne_elimt; eassumption] | solve [eapply G_actmne_elimt_gvar; eassumption]
    | solve [eapply G_actmne_uapp; eassumption] | solve [eapply G_actmne_capp; eassumption]
    | solve [eapply G_actmne_tapp; eassumption] | solve [eapply G_actmnee_red; eassumption]
    | solve [eapply G_acs_pt; eassumption] ].
Qed.

(** ** Universe substitution

    [φ] need not be well formed: the judgments do not look at the level
    context. *)

Ltac upush := cbn [usubst_ty usubst_tm ucsubst ulsubst lvsubst gousubst gdecl_usubst].
Ltac upush_in H := cbn [usubst_ty usubst_tm ucsubst ulsubst lvsubst gousubst gdecl_usubst] in H.

Lemma leqv_us {l l'} φ : leqv l l' -> leqv (lvsubst l φ) (lvsubst l' φ).
Proof. intros H; apply leqv_lvsubst; [exact H | intros; apply leqv_refl]. Qed.

Lemma posty_us W φ : posty W -> posty (usubst_ty W φ).
Proof. destruct 1; upush; constructor; now apply whne_ty_usubst. Qed.

Definition AU_ty G Γ T T' : Prop := forall L' φ,
  ac_ty (gctx_usubst G L' φ) (ucsubst Γ φ) (usubst_ty T φ) (usubst_ty T' φ).
Definition AU_tynf G Γ T T' : Prop := forall L' φ,
  ac_tynf (gctx_usubst G L' φ) (ucsubst Γ φ) (usubst_ty T φ) (usubst_ty T' φ).
Definition AU_tyne G Γ T T' : Prop := forall L' φ,
  ac_tyne (gctx_usubst G L' φ) (ucsubst Γ φ) (usubst_ty T φ) (usubst_ty T' φ).
Definition AU_ctx G Δ Δ' : Prop := forall L' φ,
  ac_ctx (gctx_usubst G L' φ) (ucsubst Δ φ) (ucsubst Δ' φ).
Definition AU_tm G Γ t t' T : Prop := forall L' φ,
  ac_tm (gctx_usubst G L' φ) (ucsubst Γ φ) (usubst_tm t φ) (usubst_tm t' φ) (usubst_ty T φ).
Definition AU_tmnf G Γ t t' T : Prop := forall L' φ,
  ac_tmnf (gctx_usubst G L' φ) (ucsubst Γ φ) (usubst_tm t φ) (usubst_tm t' φ) (usubst_ty T φ).
Definition AU_tmne G Γ t t' T : Prop := forall L' φ,
  ac_tmne (gctx_usubst G L' φ) (ucsubst Γ φ) (usubst_tm t φ) (usubst_tm t' φ) (usubst_ty T φ).
Definition AU_tmnee G Γ t t' T : Prop := forall L' φ,
  ac_tmnee (gctx_usubst G L' φ) (ucsubst Γ φ) (usubst_tm t φ) (usubst_tm t' φ) (usubst_ty T φ).
Definition AU_sub G Γ d d' Θ : Prop := forall L' φ,
  ac_sub (gctx_usubst G L' φ) (ucsubst Γ φ) (ulsubst d φ) (ulsubst d' φ) (ucsubst Θ φ).

Lemma U_act_red {G Γ T T' W W'} : reds_ty T W -> reds_ty T' W' -> whnf_ty W -> whnf_ty W' ->
  AU_tynf G Γ W W' -> AU_ty G Γ T T'.
Proof.
  intros H1 H2 H3 H4 IH L' φ.
  eapply act_red; [apply reds_ty_usubst, H1 | apply reds_ty_usubst, H2 | apply whnf_ty_usubst, H3
                  | apply whnf_ty_usubst, H4 | exact (IH L' φ)].
Qed.

Lemma U_actnf_nat {G Γ} : AU_tynf G Γ tyNat tyNat.
Proof. intros L' φ; upush; constructor. Qed.
Lemma U_actnf_U {G Γ l l'} : leqv l l' -> AU_tynf G Γ (tyU l) (tyU l').
Proof. intros Hl L' φ; upush; constructor; exact (leqv_us φ Hl). Qed.
Lemma U_actnf_pi {G Γ l1 l2 l3 l4 A A' B B'} : leqv l1 l3 -> leqv l2 l4 ->
  AU_ty G Γ A A' -> AU_ty G (Γ ,, A @ l1) B B' -> AU_tynf G Γ (tyPi l1 l2 A B) (tyPi l3 l4 A' B').
Proof.
  intros H13 H24 IHA IHB L' φ; upush.
  pose proof (IHB L' φ) as XB; upush_in XB.
  constructor; [exact (leqv_us φ H13) | exact (leqv_us φ H24) | exact (IHA L' φ) | exact XB].
Qed.
Lemma U_actnf_ne {G Γ V V'} : AU_tyne G Γ V V' -> AU_tynf G Γ V V'.
Proof. intros IH L' φ; constructor; exact (IH L' φ). Qed.
Lemma U_actnf_CTyp {G Γ Δ0 Δ0' l l'} : AU_ctx G Δ0 Δ0' -> leqv l l' ->
  AU_tynf G Γ (tyCTyp Δ0 l) (tyCTyp Δ0' l').
Proof. intros IH Hl L' φ; upush; constructor; [exact (IH L' φ) | exact (leqv_us φ Hl)]. Qed.
Lemma U_actnf_CTrm {G Γ Δ0 Δ0' T T' l l'} : AU_ctx G Δ0 Δ0' -> AU_ty G Δ0 T T' -> leqv l l' ->
  AU_tynf G Γ (tyCTrm Δ0 T l) (tyCTrm Δ0' T' l').
Proof. intros IH IHT Hl L' φ; upush; constructor; [exact (IH L' φ) | exact (IHT L' φ) | exact (leqv_us φ Hl)]. Qed.
Lemma U_actnf_upi {G Γ n l l' T T'} : leqv l l' -> AU_ty (gctx_uwk n G) Γ⟨ush n⟩ᵤ T T' ->
  AU_tynf G Γ (tyUPi n l T) (tyUPi n l' T').
Proof.
  intros Hl IH L' φ; upush. pose proof (IH (n + L') (uupn n φ)) as X.
  rewrite gctx_uwk_usubst, ucren_ush_usubst in X.
  constructor; [exact (leqv_us _ Hl) | exact X].
Qed.
Lemma U_actnf_cpi {G Γ l l' T T'} : leqv l l' -> AU_ty (gext G gdCtx) Γ⟪S⟫ T T' ->
  AU_tynf G Γ (tyCPi l T) (tyCPi l' T').
Proof.
  intros Hl IH L' φ; upush. pose proof (IH L' φ) as X. rewrite usubst_gren_ctx' in X.
  constructor; [exact (leqv_us φ Hl) | exact X].
Qed.
Lemma U_actnf_tpi {G Γ Δ0 Δ0' l1 l2 l3 l4 T T'} : AU_ctx G Δ0 Δ0' -> leqv l1 l3 -> leqv l2 l4 ->
  AU_ty (gext G (gdTy Δ0 lD l1)) Γ⟪S⟫ T T' -> AU_tynf G Γ (tyTPi Δ0 l1 l2 T) (tyTPi Δ0' l3 l4 T').
Proof.
  intros IHc H13 H24 IH L' φ; upush. pose proof (IH L' φ) as X. rewrite usubst_gren_ctx' in X.
  constructor; [exact (IHc L' φ) | exact (leqv_us φ H13) | exact (leqv_us φ H24) | exact X].
Qed.

Lemma U_actne_gvar {G Γ U Δ0 i' l d d'} : in_gctx (gΨ G) U (gdTy Δ0 i' l) -> AU_sub G Γ d d' Δ0 ->
  AU_tyne G Γ (tyGvar U d) (tyGvar U d').
Proof.
  intros Hin IH L' φ; upush. pose proof (in_gctx_usubst _ _ _ φ Hin) as X. upush_in X.
  eapply actne_gvar; [exact X | exact (IH L' φ)].
Qed.
Lemma U_actne_El {G Γ l l' ν ν' W} : leqv l l' -> AU_tmnee G Γ ν ν' W -> AU_tyne G Γ (tyEl l ν) (tyEl l' ν').
Proof. intros Hl IH L' φ; upush; eapply actne_El; [exact (leqv_us φ Hl) | exact (IH L' φ)]. Qed.

Lemma U_acc_nil {G} : AU_ctx G cnil cnil.
Proof. intros L' φ; constructor. Qed.
Lemma U_acc_var {G g} : AU_ctx G (cvar g) (cvar g).
Proof. intros L' φ; constructor. Qed.
Lemma U_acc_ext {G Γ Γ' A A' l l'} : AU_ctx G Γ Γ' -> AU_ty G Γ A A' -> leqv l l' ->
  AU_ctx G (Γ ,, A @ l) (Γ' ,, A' @ l').
Proof. intros IH IHA Hl L' φ; upush; constructor; [exact (IH L' φ) | exact (IHA L' φ) | exact (leqv_us φ Hl)]. Qed.

Lemma U_actm_red {G Γ t t' T w w' W} : reds_ty T W -> whnf_ty W -> reds t w -> reds t' w' ->
  whnf w -> whnf w' -> AU_tmnf G Γ w w' W -> AU_tm G Γ t t' T.
Proof.
  intros H1 H2 H3 H4 H5 H6 IH L' φ.
  eapply actm_red; [apply reds_ty_usubst, H1 | apply whnf_ty_usubst, H2 | apply reds_usubst, H3
                   | apply reds_usubst, H4 | apply whnf_usubst, H5 | apply whnf_usubst, H6 | exact (IH L' φ)].
Qed.

Lemma U_actmnf_code_nat {G Γ l} : AU_tmnf G Γ tmNat tmNat (tyU l).
Proof. intros L' φ; upush; constructor. Qed.
Lemma U_actmnf_code_U {G Γ l k k'} : leqv k k' -> AU_tmnf G Γ (tmU k) (tmU k') (tyU l).
Proof. intros Hk L' φ; upush; constructor; exact (leqv_us φ Hk). Qed.
Lemma U_actmnf_code_pi {G Γ l l1 l2 l3 l4 s s' t t'} : leqv l1 l3 -> leqv l2 l4 ->
  AU_tm G Γ s s' (tyU l1) -> AU_tm G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) ->
  AU_tmnf G Γ (tmPi l1 l2 s t) (tmPi l3 l4 s' t') (tyU l).
Proof.
  intros H13 H24 IHs IHt L' φ; upush.
  pose proof (IHs L' φ) as Xs; upush_in Xs. pose proof (IHt L' φ) as Xt; upush_in Xt.
  constructor; [exact (leqv_us φ H13) | exact (leqv_us φ H24) | exact Xs | exact Xt].
Qed.
Lemma U_actmnf_zero {G Γ} : AU_tmnf G Γ zero zero tyNat.
Proof. intros L' φ; constructor. Qed.
Lemma U_actmnf_succ {G Γ t t'} : AU_tm G Γ t t' tyNat -> AU_tmnf G Γ (succ t) (succ t') tyNat.
Proof. intros IH L' φ; upush; constructor; exact (IH L' φ). Qed.
Lemma U_actmnf_ne {G Γ ν ν' W W'} : posty W -> AU_tmnee G Γ ν ν' W' -> AU_tmnf G Γ ν ν' W.
Proof. intros Hp IH L' φ; eapply actmnf_ne; [exact (posty_us _ φ Hp) | exact (IH L' φ)]. Qed.
Lemma U_actmnf_eta {G Γ l l' A B w w'} :
  AU_tm G (Γ ,, A @ l) (app w⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0))
                       (app w'⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0)) B ->
  AU_tmnf G Γ w w' (tyPi l l' A B).
Proof.
  intros IH L' φ; upush. pose proof (IH L' φ) as X; upush_in X.
  rewrite !usubst_ren', !usubst_ren_ty' in X. constructor; exact X.
Qed.
Lemma U_actmnf_ueta {G Γ n l T w w'} :
  AU_tm (gctx_uwk n G) Γ⟨ush n⟩ᵤ (uapp w⟨ush n⟩ᵤ (ubvars n)) (uapp w'⟨ush n⟩ᵤ (ubvars n)) T ->
  AU_tmnf G Γ w w' (tyUPi n l T).
Proof.
  intros IH L' φ; upush. pose proof (IH (n + L') (uupn n φ)) as X; upush_in X.
  rewrite gctx_uwk_usubst, ucren_ush_usubst, !uren_ush_usubst_tm, ubvars_uupn in X.
  constructor; exact X.
Qed.
Lemma U_actmnf_ceta {G Γ l T w w'} :
  AU_tm (gext G gdCtx) Γ⟪S⟫ (capp w⟪S⟫ (cvar 0)) (capp w'⟪S⟫ (cvar 0)) T ->
  AU_tmnf G Γ w w' (tyCPi l T).
Proof.
  intros IH L' φ; upush. pose proof (IH L' φ) as X; upush_in X.
  rewrite usubst_gren_ctx', !usubst_gren_tm' in X. constructor; exact X.
Qed.
Lemma U_actmnf_teta {G Γ Δ0 l l' T w w'} :
  AU_tm (gext G (gdTy Δ0 lD l)) Γ⟪S⟫ (tapp w⟪S⟫ (tyGvar 0 (lshift 0))) (tapp w'⟪S⟫ (tyGvar 0 (lshift 0))) T ->
  AU_tmnf G Γ w w' (tyTPi Δ0 l l' T).
Proof.
  intros IH L' φ; upush. pose proof (IH L' φ) as X; upush_in X.
  rewrite usubst_gren_ctx', !usubst_gren_tm' in X. constructor; exact X.
Qed.
Lemma U_actmnf_boxT {G Γ Δ0 l T T'} : ty_leq T T' -> AU_tmnf G Γ (boxT T) (boxT T') (tyCTyp Δ0 l).
Proof.
  intros H L' φ; upush. constructor.
  apply (proj1 leq_usubst_all); [intros; apply leqv_refl | exact H].
Qed.
Lemma U_actmnf_boxt {G Γ Δ0 A l t t'} : tm_leq t t' -> AU_tmnf G Γ (boxt t) (boxt t') (tyCTrm Δ0 A l).
Proof.
  intros H L' φ; upush. constructor.
  apply (proj1 (proj2 leq_usubst_all)); [intros; apply leqv_refl | exact H].
Qed.

Lemma U_actmne_var {G Γ n T l} : in_ctx Γ n T l -> AU_tmne G Γ (var n) (var n) T.
Proof. intros Hin L' φ; upush. eapply actmne_var. exact (in_ctx_usubst _ _ _ _ φ Hin). Qed.

Lemma U_actmne_gvar {G Γ u Δ0 i' T l d d'} : in_gctx (gΨ G) u (gdTm Δ0 i' T l) -> AU_sub G Γ d d' Δ0 ->
  AU_tmne G Γ (gvar u d) (gvar u d') T[d].
Proof.
  intros Hin IH L' φ; upush. rewrite usubst_subst_ty'.
  pose proof (in_gctx_usubst _ _ _ φ Hin) as X. upush_in X.
  eapply actmne_gvar; [exact X | exact (IH L' φ)].
Qed.

Lemma U_actmne_natrec {G Γ l l' M M' s s' z z' ν ν' W} : leqv l l' ->
  AU_ty G (Γ ,, tyNat @ lzero) M M' -> AU_tm G Γ s s' M[lsingle zero] ->
  AU_tm G (Γ ,, tyNat @ lzero ,, M @ l) z z' M[lsucc] -> AU_tmnee G Γ ν ν' W ->
  AU_tmne G Γ (natrec l M s z ν) (natrec l' M' s' z' ν') M[lsingle ν].
Proof.
  intros Hl IHM IHs IHz IHν L' φ; upush. rewrite usubst_lsingle_ty.
  pose proof (IHM L' φ) as XM; upush_in XM.
  pose proof (IHs L' φ) as Xs; rewrite usubst_lsingle_ty in Xs; upush_in Xs.
  pose proof (IHz L' φ) as Xz; rewrite usubst_lsucc_ty in Xz; upush_in Xz.
  eapply actmne_natrec; [exact (leqv_us φ Hl) | exact XM | exact Xs | exact Xz | exact (IHν L' φ)].
Qed.

Lemma U_actmne_app {G Γ l1 l2 l3 l4 A A' B B' ν ν' s s' m m' A0 B0} :
  AU_tmnee G Γ ν ν' (tyPi m m' A0 B0) -> AU_tm G Γ s s' A0 ->
  AU_tmne G Γ (app ν l1 l2 A B s) (app ν' l3 l4 A' B' s') B0[lsingle s].
Proof.
  intros IHν IHs L' φ; upush. rewrite usubst_lsingle_ty.
  pose proof (IHν L' φ) as X; upush_in X.
  eapply actmne_app; [exact X | exact (IHs L' φ)].
Qed.

Lemma U_actmne_letboxT {G Γ l1 l2 l3 l4 Δ0 Δ0' M M' t1 t2 ν ν' W} : leqv l1 l3 -> leqv l2 l4 ->
  AU_ctx G Δ0 Δ0' -> AU_ty G (Γ ,, tyCTyp Δ0 l2 @ lzero) M M' ->
  AU_tm (gext G (gdTy Δ0 lC l2)) Γ⟪S⟫ t1 t2 (M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))]) ->
  AU_tmnee G Γ ν ν' W ->
  AU_tmne G Γ (letboxT l1 l2 Δ0 M t1 ν) (letboxT l3 l4 Δ0' M' t2 ν') M[lsingle ν].
Proof.
  intros H13 H24 IHc IHM IHt IHν L' φ; upush. rewrite usubst_lsingle_ty.
  pose proof (IHM L' φ) as XM; upush_in XM.
  pose proof (IHt L' φ) as Xt. rewrite usubst_gren_ctx', usubst_lsingle_ty, usubst_gren_ty' in Xt. upush_in Xt.
  eapply actmne_letboxT; [exact (leqv_us φ H13) | exact (leqv_us φ H24) | exact (IHc L' φ) | exact XM
                         | exact Xt | exact (IHν L' φ)].
Qed.

Lemma U_actmne_letboxt {G Γ l1 l2 l3 l4 Δ0 Δ0' T T' M M' t1 t2 ν ν' W} : leqv l1 l3 -> leqv l2 l4 ->
  AU_ctx G Δ0 Δ0' -> AU_ty G Δ0 T T' -> AU_ty G (Γ ,, tyCTrm Δ0 T l2 @ lzero) M M' ->
  AU_tm (gext G (gdTm Δ0 lC T l2)) Γ⟪S⟫ t1 t2 (M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))]) ->
  AU_tmnee G Γ ν ν' W ->
  AU_tmne G Γ (letboxt l1 l2 Δ0 T M t1 ν) (letboxt l3 l4 Δ0' T' M' t2 ν') M[lsingle ν].
Proof.
  intros H13 H24 IHc IHT IHM IHt IHν L' φ; upush. rewrite usubst_lsingle_ty.
  pose proof (IHM L' φ) as XM; upush_in XM.
  pose proof (IHt L' φ) as Xt. rewrite usubst_gren_ctx', usubst_lsingle_ty, usubst_gren_ty' in Xt. upush_in Xt.
  eapply actmne_letboxt; [exact (leqv_us φ H13) | exact (leqv_us φ H24) | exact (IHc L' φ) | exact (IHT L' φ)
                         | exact XM | exact Xt | exact (IHν L' φ)].
Qed.

Lemma U_branches {G Γ MT Mt l1 l2 bs bs' L' φ} :
  (forall j, j < 13 -> AU_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  forall j, j < 13 -> ac_tm (brG j (gctx_usubst G L' φ))
                       (brΓ j (ucsubst Γ φ) (wrapMT (usubst_ty MT (uup φ))) (wrapMt (usubst_ty Mt (uup φ)))
                          (lvsubst l1 φ) (lvsubst l2 φ))
                       (usubst_tm (bs j) (uupn (br_nu j) φ)) (usubst_tm (bs' j) (uupn (br_nu j) φ))
                       (brRes j (wrapMT (usubst_ty MT (uup φ))) (wrapMt (usubst_ty Mt (uup φ)))).
Proof.
  intros IH j Hj. pose proof (IH j Hj (br_nu j + L') (uupn (br_nu j) φ)) as X.
  rewrite brG_usubst, brΓ_usubst, brRes_usubst in X by exact Hj. exact X.
Qed.

Ltac U_motives IHT IHt L' φ :=
  let XT := fresh "XT" in let Xt := fresh "Xt" in
  pose proof (IHT (S L') (uup φ)) as XT; rewrite recGT_usubst, recΓT_usubst in XT;
  pose proof (IHt (S L') (uup φ)) as Xt; rewrite recGt_usubst, recΓt_usubst in Xt.

Lemma U_actmne_elimT {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ0 Δ0' ν ν' W} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> AU_ctx G Δ0 Δ0' ->
  AU_ty (recGT G) (recΓT Γ) MT MT' -> AU_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < 13 -> AU_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  AU_tmnee G Γ ν ν' W ->
  AU_tmne G Γ (elimT l1 l2 (mkrb MT Mt bs) l Δ0 ν) (elimT l1' l2' (mkrb MT' Mt' bs') l' Δ0' ν')
    (motT (wrapMT MT) l Δ0 ν).
Proof.
  intros H1 H2 Hl IHc IHT IHt IHb IHν L' φ; upush. rewrite !mkrb_usubst, motT_usubst, wrapMT_usubst.
  U_motives IHT IHt L' φ.
  eapply actmne_elimT; [exact (leqv_us φ H1) | exact (leqv_us φ H2) | exact (leqv_us φ Hl) | exact (IHc L' φ)
                        | exact XT | exact Xt | exact (U_branches IHb) | exact (IHν L' φ)].
Qed.

Lemma U_actmne_elimT_gvar {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ0 Δ0' U d d'} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> AU_ctx G Δ0 Δ0' ->
  AU_ty (recGT G) (recΓT Γ) MT MT' -> AU_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < 13 -> AU_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  lsub_leq d d' ->
  AU_tmne G Γ (elimT l1 l2 (mkrb MT Mt bs) l Δ0 (boxT (tyGvar U d)))
    (elimT l1' l2' (mkrb MT' Mt' bs') l' Δ0' (boxT (tyGvar U d')))
    (motT (wrapMT MT) l Δ0 (boxT (tyGvar U d))).
Proof.
  intros H1 H2 Hl IHc IHT IHt IHb Hd L' φ; upush. rewrite !mkrb_usubst, motT_usubst, wrapMT_usubst. upush.
  U_motives IHT IHt L' φ.
  eapply actmne_elimT_gvar; [exact (leqv_us φ H1) | exact (leqv_us φ H2) | exact (leqv_us φ Hl)
                             | exact (IHc L' φ) | exact XT | exact Xt | exact (U_branches IHb)
                             | apply (proj2 (proj2 (proj2 leq_usubst_all))); [intros; apply leqv_refl | exact Hd]].
Qed.

Lemma U_actmne_elimt {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ0 Δ0' T T' ν ν' W} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> AU_ctx G Δ0 Δ0' -> AU_ty G Δ0 T T' ->
  AU_ty (recGT G) (recΓT Γ) MT MT' -> AU_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < 13 -> AU_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  AU_tmnee G Γ ν ν' W ->
  AU_tmne G Γ (elimt l1 l2 (mkrb MT Mt bs) l Δ0 T ν) (elimt l1' l2' (mkrb MT' Mt' bs') l' Δ0' T' ν')
    (mott (wrapMt Mt) l Δ0 T ν).
Proof.
  intros H1 H2 Hl IHc IHi IHT IHt IHb IHν L' φ; upush. rewrite !mkrb_usubst, mott_usubst, wrapMt_usubst.
  U_motives IHT IHt L' φ.
  eapply actmne_elimt; [exact (leqv_us φ H1) | exact (leqv_us φ H2) | exact (leqv_us φ Hl) | exact (IHc L' φ)
                        | exact (IHi L' φ) | exact XT | exact Xt | exact (U_branches IHb) | exact (IHν L' φ)].
Qed.

Lemma U_actmne_elimt_gvar {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ0 Δ0' T T' u d d'} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> AU_ctx G Δ0 Δ0' -> AU_ty G Δ0 T T' ->
  AU_ty (recGT G) (recΓT Γ) MT MT' -> AU_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < 13 -> AU_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  lsub_leq d d' ->
  AU_tmne G Γ (elimt l1 l2 (mkrb MT Mt bs) l Δ0 T (boxt (gvar u d)))
    (elimt l1' l2' (mkrb MT' Mt' bs') l' Δ0' T' (boxt (gvar u d')))
    (mott (wrapMt Mt) l Δ0 T (boxt (gvar u d))).
Proof.
  intros H1 H2 Hl IHc IHi IHT IHt IHb Hd L' φ; upush. rewrite !mkrb_usubst, mott_usubst, wrapMt_usubst. upush.
  U_motives IHT IHt L' φ.
  eapply actmne_elimt_gvar; [exact (leqv_us φ H1) | exact (leqv_us φ H2) | exact (leqv_us φ Hl)
                             | exact (IHc L' φ) | exact (IHi L' φ) | exact XT | exact Xt | exact (U_branches IHb)
                             | apply (proj2 (proj2 (proj2 leq_usubst_all))); [intros; apply leqv_refl | exact Hd]].
Qed.

Lemma U_actmne_uapp {G Γ n l T ν ν' ls ls'} : AU_tmnee G Γ ν ν' (tyUPi n l T) -> length ls = n ->
  Forall2 leqv ls ls' -> AU_tmne G Γ (uapp ν ls) (uapp ν' ls') T[uext ls lvar]ᵤ.
Proof.
  intros IH Hn Hls L' φ; upush. change (usubst_ty T[uext ls lvar]ᵤ φ) with (T[uext ls lvar]ᵤ[φ]ᵤ).
  rewrite (usubst_ubeta_ty n ls φ T Hn).
  pose proof (IH L' φ) as X; upush_in X.
  eapply actmne_uapp; [exact X | now rewrite length_map | apply leqvs_lvsubst; [exact Hls | intros; apply leqv_refl]].
Qed.

Lemma U_actmne_capp {G Γ l T ν ν' Δ0 Δ0'} : AU_tmnee G Γ ν ν' (tyCPi l T) -> AU_ctx G Δ0 Δ0' ->
  AU_tmne G Γ (capp ν Δ0) (capp ν' Δ0') T⦃gsingle (GCtx Δ0)⦄.
Proof.
  intros IH IHc L' φ; upush. rewrite usubst_gsingle_ty. cbn [gousubst].
  pose proof (IH L' φ) as X; upush_in X.
  eapply actmne_capp; [exact X | exact (IHc L' φ)].
Qed.

Lemma U_actmne_tapp {G Γ Δ0 l l' T ν ν' A A'} : AU_tmnee G Γ ν ν' (tyTPi Δ0 l l' T) -> AU_ty G Δ0 A A' ->
  AU_tmne G Γ (tapp ν A) (tapp ν' A') T⦃gsingle (GTy A)⦄.
Proof.
  intros IH IHA L' φ; upush. rewrite usubst_gsingle_ty. cbn [gousubst].
  pose proof (IH L' φ) as X; upush_in X.
  eapply actmne_tapp; [exact X | exact (IHA L' φ)].
Qed.

Lemma U_actmnee_red {G Γ ν ν' T W} : AU_tmne G Γ ν ν' T -> reds_ty T W -> whnf_ty W ->
  AU_tmnee G Γ ν ν' W.
Proof.
  intros IH Hr Hw L' φ.
  eapply actmnee_red; [exact (IH L' φ) | apply reds_ty_usubst, Hr | apply whnf_ty_usubst, Hw].
Qed.

Lemma U_acs_pt {G Γ d d' Θ} :
  (forall n A k, in_ctx Θ n A k -> AU_tm G Γ (llk d n) (llk d' n) A[d]) -> AU_sub G Γ d d' Θ.
Proof.
  intros IH L' φ. apply acs_pt. intros n A k Hin.
  destruct (in_ctx_usubst_inv _ _ _ _ _ Hin) as (A0 & k0 & Hin0 & -> & ->).
  rewrite !llk_ulsubst, <- usubst_subst_ty'. exact (IH n A0 k0 Hin0 L' φ).
Qed.

Theorem ac_us_all :
  (forall G Γ T T', ac_ty G Γ T T' -> AU_ty G Γ T T') /\
  (forall G Γ W W', ac_tynf G Γ W W' -> AU_tynf G Γ W W') /\
  (forall G Γ V V', ac_tyne G Γ V V' -> AU_tyne G Γ V V') /\
  (forall G Δ Δ', ac_ctx G Δ Δ' -> AU_ctx G Δ Δ') /\
  (forall G Γ t t' T, ac_tm G Γ t t' T -> AU_tm G Γ t t' T) /\
  (forall G Γ w w' W, ac_tmnf G Γ w w' W -> AU_tmnf G Γ w w' W) /\
  (forall G Γ ν ν' T, ac_tmne G Γ ν ν' T -> AU_tmne G Γ ν ν' T) /\
  (forall G Γ ν ν' W, ac_tmnee G Γ ν ν' W -> AU_tmnee G Γ ν ν' W) /\
  (forall G Γ d d' Δ, ac_sub G Γ d d' Δ -> AU_sub G Γ d d' Δ).
Proof.
  apply ac_mut; intros;
    first
    [ solve [eapply U_act_red; eassumption] | solve [eapply U_actnf_nat] | solve [eapply U_actnf_U; eassumption]
    | solve [eapply U_actnf_pi; eassumption] | solve [eapply U_actnf_ne; eassumption]
    | solve [eapply U_actnf_CTyp; eassumption] | solve [eapply U_actnf_CTrm; eassumption]
    | solve [eapply U_actnf_upi; eassumption] | solve [eapply U_actnf_cpi; eassumption]
    | solve [eapply U_actnf_tpi; eassumption]
    | solve [eapply U_actne_gvar; eassumption] | solve [eapply U_actne_El; eassumption]
    | solve [eapply U_acc_nil] | solve [eapply U_acc_var] | solve [eapply U_acc_ext; eassumption]
    | solve [eapply U_actm_red; eassumption]
    | solve [eapply U_actmnf_code_nat] | solve [eapply U_actmnf_code_U; eassumption]
    | solve [eapply U_actmnf_code_pi; eassumption] | solve [eapply U_actmnf_zero]
    | solve [eapply U_actmnf_succ; eassumption] | solve [eapply U_actmnf_ne; eassumption]
    | solve [eapply U_actmnf_eta; eassumption] | solve [eapply U_actmnf_ueta; eassumption]
    | solve [eapply U_actmnf_ceta; eassumption] | solve [eapply U_actmnf_teta; eassumption]
    | solve [eapply U_actmnf_boxT; eassumption] | solve [eapply U_actmnf_boxt; eassumption]
    | solve [eapply U_actmne_var; eassumption] | solve [eapply U_actmne_gvar; eassumption]
    | solve [eapply U_actmne_natrec; eassumption] | solve [eapply U_actmne_app; eassumption]
    | solve [eapply U_actmne_letboxT; eassumption] | solve [eapply U_actmne_letboxt; eassumption]
    | solve [eapply U_actmne_elimT; eassumption] | solve [eapply U_actmne_elimT_gvar; eassumption]
    | solve [eapply U_actmne_elimt; eassumption] | solve [eapply U_actmne_elimt_gvar; eassumption]
    | solve [eapply U_actmne_uapp; eassumption] | solve [eapply U_actmne_capp; eassumption]
    | solve [eapply U_actmne_tapp; eassumption] | solve [eapply U_actmnee_red; eassumption]
    | solve [eapply U_acs_pt; eassumption] ].
Qed.

(** ** Closure under [≡ₗ] on the right

    With reflexivity, this gives the instances' [≡ₗ] laws. The right
    side of a recursor is [≡ₗ]-related to a bundle, so it is a bundle. *)

Lemma ctx_leq_trans Γ1 Γ2 Γ3 : ctx_leq Γ1 Γ2 -> ctx_leq Γ2 Γ3 -> ctx_leq Γ1 Γ3.
Proof. apply leq_trans_all. Qed.
Lemma lsub_leq_trans d1 d2 d3 : lsub_leq d1 d2 -> lsub_leq d2 d3 -> lsub_leq d1 d3.
Proof. apply leq_trans_all. Qed.

(** Destruct the variable a [≡ₗ] hypothesis is stuck on. *)
Ltac lstep E :=
  match type of E with
  | ty_leq _ ?x => is_var x; destruct x
  | tm_leq _ ?x => is_var x; destruct x
  | ctx_leq _ ?x => is_var x; destruct x
  | lsub_leq _ ?x => is_var x; destruct x
  | context [match ?x with _ => _ end] => is_var x; destruct x
  end; cbn [ty_leq tm_leq ctx_leq lsub_leq] in E; try contradiction.

Fixpoint unwrap (n : nat) (t : tm) : tm :=
  match n, t with
  | S n, (bindU b | bindG b | bindL b) => unwrap n b
  | _, _ => t
  end.

Lemma unwrap_wrap nu ng nl b : unwrap (nu + ng + nl) (wrap nu ng nl b) = b.
Proof.
  unfold wrap. induction nu as [|nu IH]; cbn [wrapU plus unwrap]; [|exact IH].
  induction ng as [|ng IH']; cbn [wrapG plus unwrap]; [|exact IH'].
  induction nl as [|nl IH'']; cbn [wrapL unwrap]; [reflexivity | exact IH''].
Qed.

Lemma leq_wrap_inv nu ng nl b x : tm_leq (wrap nu ng nl b) x -> exists b', x = wrap nu ng nl b' /\ tm_leq b b'.
Proof.
  unfold wrap. revert x; induction nu as [|nu IH]; intros x E; cbn [wrapU] in *.
  - revert x E; induction ng as [|ng IH']; intros x E; cbn [wrapG] in *.
    + revert x E; induction nl as [|nl IH'']; intros x E; cbn [wrapL] in *; [now exists x|].
      destruct x; cbn [tm_leq] in E; try contradiction.
      destruct (IH'' _ E) as (b' & -> & Eb). now exists b'.
    + destruct x; cbn [tm_leq] in E; try contradiction.
      destruct (IH' _ E) as (b' & -> & Eb). now exists b'.
  - destruct x; cbn [tm_leq] in E; try contradiction.
    destruct (IH _ E) as (b' & -> & Eb). now exists b'.
Qed.

Lemma tup_from_ext f g k n : (forall j, k <= j -> j < k + n -> f j = g j) -> tup_from f k n = tup_from g k n.
Proof.
  revert k; induction n as [|n IH]; intros k H; cbn [tup_from]; [reflexivity|].
  f_equal; [apply H; lia | apply IH; intros j H1 H2; apply H; lia].
Qed.

Lemma leq_tup_from_inv f k n x : tm_leq (tup_from f k n) x ->
  exists g, x = tup_from g k n /\ forall j, k <= j -> j < k + n -> tm_leq (f j) (g j).
Proof.
  revert k x; induction n as [|n IH]; intros k x E; cbn [tup_from] in *.
  - lstep E. exists f; split; [reflexivity | intros; lia].
  - lstep E. destruct E as [Ea Erest].
    destruct (IH _ _ Erest) as (g & -> & Eg).
    match type of Ea with tm_leq _ ?a => exists (fun j => if Nat.eqb j k then a else g j) end. split.
    + rewrite Nat.eqb_refl. f_equal. apply tup_from_ext. intros j H1 _.
      destruct (Nat.eqb_spec j k); [lia | reflexivity].
    + intros j H1 H2. destruct (Nat.eqb_spec j k) as [->|Hne]; [exact Ea | apply Eg; lia].
Qed.

Lemma mkrb_leq_inv MT Mt bs rb : tm_leq (mkrb MT Mt bs) rb ->
  exists MT2 Mt2 bs2, rb = mkrb MT2 Mt2 bs2 /\ ty_leq MT MT2 /\ ty_leq Mt Mt2 /\
    forall k, k < 13 -> tm_leq (bs k) (bs2 k).
Proof.
  unfold mkrb, wrapMT, wrapMt. intros E.
  lstep E. destruct E as [E1 E].
  do 4 lstep E1.
  match goal with |- context [tmTup (bindU (bindG (bindL (tmTy ?T)))) _] => exists T end.
  lstep E. destruct E as [E2 E].
  do 5 lstep E2.
  match goal with |- context [tmTup (bindU (bindG (bindG (bindL (tmTy ?T))))) _] => exists T end.
  destruct (leq_tup_from_inv _ _ _ _ E) as (g & -> & Eg).
  exists (fun k => let '(nu, ng, nl) := br_ar k in unwrap (nu + ng + nl) (g k)).
  split; [| split; [exact E1 | split; [exact E2 |]]].
  - do 2 f_equal. apply tup_from_ext. intros j _ Hj. cbn in Hj.
    specialize (Eg j (Nat.le_0_l j) Hj). destruct (br_ar j) as [[nu ng] nl].
    destruct (leq_wrap_inv _ _ _ _ _ Eg) as (b' & -> & _). now rewrite unwrap_wrap.
  - intros k Hk. specialize (Eg k (Nat.le_0_l k) Hk). destruct (br_ar k) as [[nu ng] nl].
    destruct (leq_wrap_inv _ _ _ _ _ Eg) as (b' & -> & Eb). now rewrite unwrap_wrap.
Qed.

Ltac linv E := lstep E; repeat match type of E with _ /\ _ => let E' := fresh "E" in destruct E as [E' E] end.

#[local] Hint Resolve leqv_trans leqvs_trans ty_leq_trans tm_leq_trans ctx_leq_trans lsub_leq_trans : lq.

Definition AL_ty G Γ T T' : Prop := forall T2, ty_leq T' T2 -> ac_ty G Γ T T2.
Definition AL_tynf G Γ T T' : Prop := forall T2, ty_leq T' T2 -> ac_tynf G Γ T T2.
Definition AL_tyne G Γ T T' : Prop := forall T2, ty_leq T' T2 -> ac_tyne G Γ T T2.
Definition AL_ctx G Δ Δ' : Prop := forall Δ2, ctx_leq Δ' Δ2 -> ac_ctx G Δ Δ2.
Definition AL_tm G Γ t t' T : Prop := forall t2, tm_leq t' t2 -> ac_tm G Γ t t2 T.
Definition AL_tmnf G Γ t t' T : Prop := forall t2, tm_leq t' t2 -> ac_tmnf G Γ t t2 T.
Definition AL_tmne G Γ t t' T : Prop := forall t2, tm_leq t' t2 -> ac_tmne G Γ t t2 T.
Definition AL_tmnee G Γ t t' T : Prop := forall t2, tm_leq t' t2 -> ac_tmnee G Γ t t2 T.
Definition AL_sub G Γ d d' Θ : Prop := forall d2, lsub_leq d' d2 -> ac_sub G Γ d d2 Θ.

Lemma L_act_red {G Γ T T' W W'} : reds_ty T W -> reds_ty T' W' -> whnf_ty W -> whnf_ty W' ->
  AL_tynf G Γ W W' -> AL_ty G Γ T T'.
Proof.
  intros H1 H2 H3 H4 IH T2 E. destruct (reds_ty_leq _ _ _ H2 E) as (W2 & HW2 & EW).
  eapply act_red; [exact H1 | exact HW2 | exact H3 | exact (whnf_ty_leq _ _ EW H4) | exact (IH _ EW)].
Qed.

Lemma L_actnf_nat {G Γ} : AL_tynf G Γ tyNat tyNat.
Proof. intros T2 E; linv E. apply actnf_nat. Qed.
Lemma L_actnf_U {G Γ l l'} : leqv l l' -> AL_tynf G Γ (tyU l) (tyU l').
Proof. intros Hl T2 E; linv E. apply actnf_U; eauto with lq. Qed.
Lemma L_actnf_pi {G Γ l1 l2 l3 l4 A A' B B'} : leqv l1 l3 -> leqv l2 l4 ->
  AL_ty G Γ A A' -> AL_ty G (Γ ,, A @ l1) B B' -> AL_tynf G Γ (tyPi l1 l2 A B) (tyPi l3 l4 A' B').
Proof. intros H13 H24 IHA IHB T2 E; linv E. apply actnf_pi; eauto with lq. Qed.
Lemma L_actnf_ne {G Γ V V'} : AL_tyne G Γ V V' -> AL_tynf G Γ V V'.
Proof. intros IH T2 E. apply actnf_ne, IH, E. Qed.
Lemma L_actnf_CTyp {G Γ Δ0 Δ0' l l'} : AL_ctx G Δ0 Δ0' -> leqv l l' ->
  AL_tynf G Γ (tyCTyp Δ0 l) (tyCTyp Δ0' l').
Proof. intros IH Hl T2 E; linv E. apply actnf_CTyp; eauto with lq. Qed.
Lemma L_actnf_CTrm {G Γ Δ0 Δ0' T T' l l'} : AL_ctx G Δ0 Δ0' -> AL_ty G Δ0 T T' -> leqv l l' ->
  AL_tynf G Γ (tyCTrm Δ0 T l) (tyCTrm Δ0' T' l').
Proof. intros IH IHT Hl T2 E; linv E. apply actnf_CTrm; eauto with lq. Qed.
Lemma L_actnf_upi {G Γ n l l' T T'} : leqv l l' -> AL_ty (gctx_uwk n G) Γ⟨ush n⟩ᵤ T T' ->
  AL_tynf G Γ (tyUPi n l T) (tyUPi n l' T').
Proof. intros Hl IH T2 E; linv E. subst. apply actnf_upi; eauto with lq. Qed.
Lemma L_actnf_cpi {G Γ l l' T T'} : leqv l l' -> AL_ty (gext G gdCtx) Γ⟪S⟫ T T' ->
  AL_tynf G Γ (tyCPi l T) (tyCPi l' T').
Proof. intros Hl IH T2 E; linv E. apply actnf_cpi; eauto with lq. Qed.
Lemma L_actnf_tpi {G Γ Δ0 Δ0' l1 l2 l3 l4 T T'} : AL_ctx G Δ0 Δ0' -> leqv l1 l3 -> leqv l2 l4 ->
  AL_ty (gext G (gdTy Δ0 lD l1)) Γ⟪S⟫ T T' -> AL_tynf G Γ (tyTPi Δ0 l1 l2 T) (tyTPi Δ0' l3 l4 T').
Proof. intros IHc H13 H24 IH T2 E; linv E. apply actnf_tpi; eauto with lq. Qed.

Lemma L_actne_gvar {G Γ U Δ0 i' l d d'} : in_gctx (gΨ G) U (gdTy Δ0 i' l) -> AL_sub G Γ d d' Δ0 ->
  AL_tyne G Γ (tyGvar U d) (tyGvar U d').
Proof. intros Hin IH T2 E; linv E. subst. eapply actne_gvar; [exact Hin | eauto]. Qed.
Lemma L_actne_El {G Γ l l' ν ν' W} : leqv l l' -> AL_tmnee G Γ ν ν' W -> AL_tyne G Γ (tyEl l ν) (tyEl l' ν').
Proof. intros Hl IH T2 E; linv E. eapply actne_El; eauto with lq. Qed.

Lemma L_acc_nil {G} : AL_ctx G cnil cnil.
Proof. intros Δ2 E; linv E. apply acc_nil. Qed.
Lemma L_acc_var {G g} : AL_ctx G (cvar g) (cvar g).
Proof. intros Δ2 E; linv E. subst. apply acc_var. Qed.
Lemma L_acc_ext {G Γ Γ' A A' l l'} : AL_ctx G Γ Γ' -> AL_ty G Γ A A' -> leqv l l' ->
  AL_ctx G (Γ ,, A @ l) (Γ' ,, A' @ l').
Proof. intros IH IHA Hl Δ2 E; linv E. apply acc_ext; eauto with lq. Qed.

Lemma L_actm_red {G Γ t t' T w w' W} : reds_ty T W -> whnf_ty W -> reds t w -> reds t' w' ->
  whnf w -> whnf w' -> AL_tmnf G Γ w w' W -> AL_tm G Γ t t' T.
Proof.
  intros H1 H2 H3 H4 H5 H6 IH t2 E. destruct (reds_leq _ _ _ H4 E) as (w2 & Hw2 & Ew).
  eapply actm_red; [exact H1 | exact H2 | exact H3 | exact Hw2 | exact H5 | exact (whnf_leq _ _ Ew H6)
                   | exact (IH _ Ew)].
Qed.

Lemma L_actmnf_code_nat {G Γ l} : AL_tmnf G Γ tmNat tmNat (tyU l).
Proof. intros t2 E; linv E. apply actmnf_code_nat. Qed.
Lemma L_actmnf_code_U {G Γ l k k'} : leqv k k' -> AL_tmnf G Γ (tmU k) (tmU k') (tyU l).
Proof. intros Hk t2 E; linv E. apply actmnf_code_U; eauto with lq. Qed.
Lemma L_actmnf_code_pi {G Γ l l1 l2 l3 l4 s s' t t'} : leqv l1 l3 -> leqv l2 l4 ->
  AL_tm G Γ s s' (tyU l1) -> AL_tm G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) ->
  AL_tmnf G Γ (tmPi l1 l2 s t) (tmPi l3 l4 s' t') (tyU l).
Proof. intros H13 H24 IHs IHt t2 E; linv E. apply actmnf_code_pi; eauto with lq. Qed.
Lemma L_actmnf_zero {G Γ} : AL_tmnf G Γ zero zero tyNat.
Proof. intros t2 E; linv E. apply actmnf_zero. Qed.
Lemma L_actmnf_succ {G Γ t t'} : AL_tm G Γ t t' tyNat -> AL_tmnf G Γ (succ t) (succ t') tyNat.
Proof. intros IH t2 E; linv E. apply actmnf_succ; eauto. Qed.
Lemma L_actmnf_ne {G Γ ν ν' W W'} : posty W -> AL_tmnee G Γ ν ν' W' -> AL_tmnf G Γ ν ν' W.
Proof. intros Hp IH t2 E. eapply actmnf_ne; [exact Hp | exact (IH _ E)]. Qed.
Lemma L_actmnf_eta {G Γ l l' A B w w'} :
  AL_tm G (Γ ,, A @ l) (app w⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0))
                       (app w'⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0)) B ->
  AL_tmnf G Γ w w' (tyPi l l' A B).
Proof.
  intros IH t2 E. apply actmnf_eta, IH. cbn [tm_leq].
  repeat split; first [apply leq_ren_tm, E | apply leqv_refl | apply ty_leq_refl].
Qed.
Lemma L_actmnf_ueta {G Γ n l T w w'} :
  AL_tm (gctx_uwk n G) Γ⟨ush n⟩ᵤ (uapp w⟨ush n⟩ᵤ (ubvars n)) (uapp w'⟨ush n⟩ᵤ (ubvars n)) T ->
  AL_tmnf G Γ w w' (tyUPi n l T).
Proof. intros IH t2 E. apply actmnf_ueta, IH. split; [apply leq_uren_tm, E | apply leqvs_refl]. Qed.
Lemma L_actmnf_ceta {G Γ l T w w'} :
  AL_tm (gext G gdCtx) Γ⟪S⟫ (capp w⟪S⟫ (cvar 0)) (capp w'⟪S⟫ (cvar 0)) T ->
  AL_tmnf G Γ w w' (tyCPi l T).
Proof. intros IH t2 E. apply actmnf_ceta, IH. split; [apply leq_gren_tm, E | reflexivity]. Qed.
Lemma L_actmnf_teta {G Γ Δ0 l l' T w w'} :
  AL_tm (gext G (gdTy Δ0 lD l)) Γ⟪S⟫ (tapp w⟪S⟫ (tyGvar 0 (lshift 0))) (tapp w'⟪S⟫ (tyGvar 0 (lshift 0))) T ->
  AL_tmnf G Γ w w' (tyTPi Δ0 l l' T).
Proof. intros IH t2 E. apply actmnf_teta, IH. split; [apply leq_gren_tm, E | apply ty_leq_refl]. Qed.
Lemma L_actmnf_boxT {G Γ Δ0 l T T'} : ty_leq T T' -> AL_tmnf G Γ (boxT T) (boxT T') (tyCTyp Δ0 l).
Proof. intros H t2 E; linv E. apply actmnf_boxT; eauto with lq. Qed.
Lemma L_actmnf_boxt {G Γ Δ0 A l t t'} : tm_leq t t' -> AL_tmnf G Γ (boxt t) (boxt t') (tyCTrm Δ0 A l).
Proof. intros H t2 E; linv E. apply actmnf_boxt; eauto with lq. Qed.

Lemma L_actmne_var {G Γ n T l} : in_ctx Γ n T l -> AL_tmne G Γ (var n) (var n) T.
Proof. intros Hin t2 E; linv E. subst. eapply actmne_var; exact Hin. Qed.
Lemma L_actmne_gvar {G Γ u Δ0 i' T l d d'} : in_gctx (gΨ G) u (gdTm Δ0 i' T l) -> AL_sub G Γ d d' Δ0 ->
  AL_tmne G Γ (gvar u d) (gvar u d') T[d].
Proof. intros Hin IH t2 E; linv E. subst. eapply actmne_gvar; [exact Hin | eauto]. Qed.
Lemma L_actmne_natrec {G Γ l l' M M' s s' z z' ν ν' W} : leqv l l' ->
  AL_ty G (Γ ,, tyNat @ lzero) M M' -> AL_tm G Γ s s' M[lsingle zero] ->
  AL_tm G (Γ ,, tyNat @ lzero ,, M @ l) z z' M[lsucc] -> AL_tmnee G Γ ν ν' W ->
  AL_tmne G Γ (natrec l M s z ν) (natrec l' M' s' z' ν') M[lsingle ν].
Proof. intros Hl IHM IHs IHz IHν t2 E; linv E. eapply actmne_natrec; eauto with lq. Qed.
Lemma L_actmne_app {G Γ l1 l2 l3 l4 A A' B B' ν ν' s s' m m' A0 B0} :
  AL_tmnee G Γ ν ν' (tyPi m m' A0 B0) -> AL_tm G Γ s s' A0 ->
  AL_tmne G Γ (app ν l1 l2 A B s) (app ν' l3 l4 A' B' s') B0[lsingle s].
Proof. intros IHν IHs t2 E; linv E. eapply actmne_app; eauto. Qed.
Lemma L_actmne_letboxT {G Γ l1 l2 l3 l4 Δ0 Δ0' M M' t1 t2 ν ν' W} : leqv l1 l3 -> leqv l2 l4 ->
  AL_ctx G Δ0 Δ0' -> AL_ty G (Γ ,, tyCTyp Δ0 l2 @ lzero) M M' ->
  AL_tm (gext G (gdTy Δ0 lC l2)) Γ⟪S⟫ t1 t2 (M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))]) ->
  AL_tmnee G Γ ν ν' W ->
  AL_tmne G Γ (letboxT l1 l2 Δ0 M t1 ν) (letboxT l3 l4 Δ0' M' t2 ν') M[lsingle ν].
Proof. intros H13 H24 IHc IHM IHt IHν x E; linv E. eapply actmne_letboxT; eauto with lq. Qed.
Lemma L_actmne_letboxt {G Γ l1 l2 l3 l4 Δ0 Δ0' T T' M M' t1 t2 ν ν' W} : leqv l1 l3 -> leqv l2 l4 ->
  AL_ctx G Δ0 Δ0' -> AL_ty G Δ0 T T' -> AL_ty G (Γ ,, tyCTrm Δ0 T l2 @ lzero) M M' ->
  AL_tm (gext G (gdTm Δ0 lC T l2)) Γ⟪S⟫ t1 t2 (M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))]) ->
  AL_tmnee G Γ ν ν' W ->
  AL_tmne G Γ (letboxt l1 l2 Δ0 T M t1 ν) (letboxt l3 l4 Δ0' T' M' t2 ν') M[lsingle ν].
Proof. intros H13 H24 IHc IHT IHM IHt IHν x E; linv E. eapply actmne_letboxt; eauto with lq. Qed.

(** The right bundle, [≡ₗ]-related to [mkrb MT' Mt' bs'], is a bundle. *)
Ltac L_bundle :=
  match goal with Erb : tm_leq (mkrb _ _ _) _ |- _ =>
    let MT2 := fresh "MT2" in let Mt2 := fresh "Mt2" in let bs2 := fresh "bs2" in
    let EMT := fresh "EMT" in let EMt := fresh "EMt" in let Ebs := fresh "Ebs" in
    destruct (mkrb_leq_inv _ _ _ _ Erb) as (MT2 & Mt2 & bs2 & -> & EMT & EMt & Ebs)
  end.

Lemma L_actmne_elimT {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ0 Δ0' ν ν' W} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> AL_ctx G Δ0 Δ0' ->
  AL_ty (recGT G) (recΓT Γ) MT MT' -> AL_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < 13 -> AL_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  AL_tmnee G Γ ν ν' W ->
  AL_tmne G Γ (elimT l1 l2 (mkrb MT Mt bs) l Δ0 ν) (elimT l1' l2' (mkrb MT' Mt' bs') l' Δ0' ν')
    (motT (wrapMT MT) l Δ0 ν).
Proof.
  intros H1 H2 Hl IHc IHT IHt IHb IHν x E; linv E. L_bundle.
  eapply actmne_elimT; eauto with lq. intros k Hk. exact (IHb k Hk _ (Ebs k Hk)).
Qed.

Lemma L_actmne_elimT_gvar {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ0 Δ0' U d d'} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> AL_ctx G Δ0 Δ0' ->
  AL_ty (recGT G) (recΓT Γ) MT MT' -> AL_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < 13 -> AL_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  lsub_leq d d' ->
  AL_tmne G Γ (elimT l1 l2 (mkrb MT Mt bs) l Δ0 (boxT (tyGvar U d)))
    (elimT l1' l2' (mkrb MT' Mt' bs') l' Δ0' (boxT (tyGvar U d')))
    (motT (wrapMT MT) l Δ0 (boxT (tyGvar U d))).
Proof.
  intros H1 H2 Hl IHc IHT IHt IHb Hd x E; linv E. L_bundle.
  match goal with Es : context [match ?x with _ => _ end] |- _ => is_var x; linv Es; linv Es end. subst.
  eapply actmne_elimT_gvar; eauto with lq. intros k Hk. exact (IHb k Hk _ (Ebs k Hk)).
Qed.

Lemma L_actmne_elimt {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ0 Δ0' T T' ν ν' W} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> AL_ctx G Δ0 Δ0' -> AL_ty G Δ0 T T' ->
  AL_ty (recGT G) (recΓT Γ) MT MT' -> AL_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < 13 -> AL_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  AL_tmnee G Γ ν ν' W ->
  AL_tmne G Γ (elimt l1 l2 (mkrb MT Mt bs) l Δ0 T ν) (elimt l1' l2' (mkrb MT' Mt' bs') l' Δ0' T' ν')
    (mott (wrapMt Mt) l Δ0 T ν).
Proof.
  intros H1 H2 Hl IHc IHi IHT IHt IHb IHν x E; linv E. L_bundle.
  eapply actmne_elimt; eauto with lq. intros k Hk. exact (IHb k Hk _ (Ebs k Hk)).
Qed.

Lemma L_actmne_elimt_gvar {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ0 Δ0' T T' u d d'} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> AL_ctx G Δ0 Δ0' -> AL_ty G Δ0 T T' ->
  AL_ty (recGT G) (recΓT Γ) MT MT' -> AL_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < 13 -> AL_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  lsub_leq d d' ->
  AL_tmne G Γ (elimt l1 l2 (mkrb MT Mt bs) l Δ0 T (boxt (gvar u d)))
    (elimt l1' l2' (mkrb MT' Mt' bs') l' Δ0' T' (boxt (gvar u d')))
    (mott (wrapMt Mt) l Δ0 T (boxt (gvar u d))).
Proof.
  intros H1 H2 Hl IHc IHi IHT IHt IHb Hd x E; linv E. L_bundle.
  match goal with Es : context [match ?x with _ => _ end] |- _ => is_var x; linv Es; linv Es end. subst.
  eapply actmne_elimt_gvar; eauto with lq. intros k Hk. exact (IHb k Hk _ (Ebs k Hk)).
Qed.

Lemma L_actmne_uapp {G Γ n l T ν ν' ls ls'} : AL_tmnee G Γ ν ν' (tyUPi n l T) -> length ls = n ->
  Forall2 leqv ls ls' -> AL_tmne G Γ (uapp ν ls) (uapp ν' ls') T[uext ls lvar]ᵤ.
Proof. intros IH Hn Hls t2 E; linv E. eapply actmne_uapp; eauto with lq. Qed.
Lemma L_actmne_capp {G Γ l T ν ν' Δ0 Δ0'} : AL_tmnee G Γ ν ν' (tyCPi l T) -> AL_ctx G Δ0 Δ0' ->
  AL_tmne G Γ (capp ν Δ0) (capp ν' Δ0') T⦃gsingle (GCtx Δ0)⦄.
Proof. intros IH IHc t2 E; linv E. eapply actmne_capp; eauto. Qed.
Lemma L_actmne_tapp {G Γ Δ0 l l' T ν ν' A A'} : AL_tmnee G Γ ν ν' (tyTPi Δ0 l l' T) -> AL_ty G Δ0 A A' ->
  AL_tmne G Γ (tapp ν A) (tapp ν' A') T⦃gsingle (GTy A)⦄.
Proof. intros IH IHA t2 E; linv E. eapply actmne_tapp; eauto. Qed.

Lemma L_actmnee_red {G Γ ν ν' T W} : AL_tmne G Γ ν ν' T -> reds_ty T W -> whnf_ty W ->
  AL_tmnee G Γ ν ν' W.
Proof. intros IH Hr Hw t2 E. eapply actmnee_red; [exact (IH _ E) | exact Hr | exact Hw]. Qed.

Lemma L_acs_pt {G Γ d d' Θ} :
  (forall n A k, in_ctx Θ n A k -> AL_tm G Γ (llk d n) (llk d' n) A[d]) -> AL_sub G Γ d d' Θ.
Proof. intros IH d2 E. apply acs_pt. intros n A k Hin. exact (IH n A k Hin _ (llk_leq _ _ n E)). Qed.

Theorem ac_leq_all :
  (forall G Γ T T', ac_ty G Γ T T' -> AL_ty G Γ T T') /\
  (forall G Γ W W', ac_tynf G Γ W W' -> AL_tynf G Γ W W') /\
  (forall G Γ V V', ac_tyne G Γ V V' -> AL_tyne G Γ V V') /\
  (forall G Δ Δ', ac_ctx G Δ Δ' -> AL_ctx G Δ Δ') /\
  (forall G Γ t t' T, ac_tm G Γ t t' T -> AL_tm G Γ t t' T) /\
  (forall G Γ w w' W, ac_tmnf G Γ w w' W -> AL_tmnf G Γ w w' W) /\
  (forall G Γ ν ν' T, ac_tmne G Γ ν ν' T -> AL_tmne G Γ ν ν' T) /\
  (forall G Γ ν ν' W, ac_tmnee G Γ ν ν' W -> AL_tmnee G Γ ν ν' W) /\
  (forall G Γ d d' Δ, ac_sub G Γ d d' Δ -> AL_sub G Γ d d' Δ).
Proof.
  apply ac_mut; intros;
    first
    [ solve [eapply L_act_red; eassumption] | solve [eapply L_actnf_nat] | solve [eapply L_actnf_U; eassumption]
    | solve [eapply L_actnf_pi; eassumption] | solve [eapply L_actnf_ne; eassumption]
    | solve [eapply L_actnf_CTyp; eassumption] | solve [eapply L_actnf_CTrm; eassumption]
    | solve [eapply L_actnf_upi; eassumption] | solve [eapply L_actnf_cpi; eassumption]
    | solve [eapply L_actnf_tpi; eassumption]
    | solve [eapply L_actne_gvar; eassumption] | solve [eapply L_actne_El; eassumption]
    | solve [eapply L_acc_nil] | solve [eapply L_acc_var] | solve [eapply L_acc_ext; eassumption]
    | solve [eapply L_actm_red; eassumption]
    | solve [eapply L_actmnf_code_nat] | solve [eapply L_actmnf_code_U; eassumption]
    | solve [eapply L_actmnf_code_pi; eassumption] | solve [eapply L_actmnf_zero]
    | solve [eapply L_actmnf_succ; eassumption] | solve [eapply L_actmnf_ne; eassumption]
    | solve [eapply L_actmnf_eta; eassumption] | solve [eapply L_actmnf_ueta; eassumption]
    | solve [eapply L_actmnf_ceta; eassumption] | solve [eapply L_actmnf_teta; eassumption]
    | solve [eapply L_actmnf_boxT; eassumption] | solve [eapply L_actmnf_boxt; eassumption]
    | solve [eapply L_actmne_var; eassumption] | solve [eapply L_actmne_gvar; eassumption]
    | solve [eapply L_actmne_natrec; eassumption] | solve [eapply L_actmne_app; eassumption]
    | solve [eapply L_actmne_letboxT; eassumption] | solve [eapply L_actmne_letboxt; eassumption]
    | solve [eapply L_actmne_elimT; eassumption] | solve [eapply L_actmne_elimT_gvar; eassumption]
    | solve [eapply L_actmne_elimt; eassumption] | solve [eapply L_actmne_elimt_gvar; eassumption]
    | solve [eapply L_actmne_uapp; eassumption] | solve [eapply L_actmne_capp; eassumption]
    | solve [eapply L_actmne_tapp; eassumption] | solve [eapply L_actmnee_red; eassumption]
    | solve [eapply L_acs_pt; eassumption] ].
Qed.

(** ** Annotations along the head spine (M6_DESIGN.md H10)

    [spa t t']: [t'] is [t] with the annotations of [app] nodes on its
    head spine (through [app], [uapp], [capp], [tapp]) changed. Reduction
    never reads them, and neither do the neutral rules, so the term
    judgments are closed under [spa] on both sides. *)

Inductive spa : tm -> tm -> Prop :=
| spa_refl t : spa t t
| spa_app f f' l1 l2 A B l1' l2' A' B' s : spa f f' -> spa (app f l1 l2 A B s) (app f' l1' l2' A' B' s)
| spa_uapp f f' ls : spa f f' -> spa (uapp f ls) (uapp f' ls)
| spa_capp f f' Δ0 : spa f f' -> spa (capp f Δ0) (capp f' Δ0)
| spa_tapp f f' T : spa f f' -> spa (tapp f T) (tapp f' T).

#[local] Hint Constructors spa : spa.

Lemma spa_ren t t' r : spa t t' -> spa t⟨r⟩ t'⟨r⟩.
Proof. induction 1; cbn; eauto with spa. Qed.
Lemma spa_uren t t' ρ : spa t t' -> spa t⟨ρ⟩ᵤ t'⟨ρ⟩ᵤ.
Proof. induction 1; cbn; eauto with spa. Qed.
Lemma spa_gren t t' ξ : spa t t' -> spa t⟪ξ⟫ t'⟪ξ⟫.
Proof. induction 1; cbn; eauto with spa. Qed.

Lemma spa_whne t t' : spa t t' -> whne t -> whne t'.
Proof. induction 1; intros Hw; [exact Hw | ..]; inversion Hw; subst; constructor; auto. Qed.

Lemma spa_whnf t t' : spa t t' -> whnf t -> whnf t'.
Proof.
  intros H Hw. destruct H; [exact Hw | ..];
    inversion Hw; subst; apply whnf_ne; (eapply spa_whne; [econstructor; eassumption | eassumption]).
Qed.

Lemma spa_red t t' : spa t t' -> forall u, red t u -> exists u', red t' u' /\ spa u u'.
Proof.
  induction 1; intros u Hr;
    first [ solve [exists u; split; [exact Hr | apply spa_refl]] | inversion Hr; subst ].
  all: first
    [ match goal with Hs : spa (_ _ _ _ _) _ |- _ => inversion Hs; subst end;
      eexists; split; [econstructor; try first [eassumption | reflexivity] | apply spa_refl]
    | match goal with Hs : spa (_ _ _ _) _ |- _ => inversion Hs; subst end;
      eexists; split; [econstructor; try first [eassumption | reflexivity] | apply spa_refl]
    | match goal with Hs : spa (_ _ _) _ |- _ => inversion Hs; subst end;
      eexists; split; [econstructor; try first [eassumption | reflexivity] | apply spa_refl]
    | match goal with IH : forall u, red ?f u -> _, Hr' : red ?f ?f1 |- _ =>
        destruct (IH _ Hr') as (f3 & Hr3 & Hs3) end;
      eexists; split; [econstructor; exact Hr3 | constructor; exact Hs3] ].
Qed.

Lemma spa_reds t t' u : reds t u -> spa t t' -> exists u', reds t' u' /\ spa u u'.
Proof.
  intros H; revert t'; induction H as [t | t v u Htv Hvu IH]; intros t' Hs.
  - exists t'; split; [constructor | exact Hs].
  - destruct (spa_red _ _ Hs _ Htv) as (v' & Hv' & Hsv).
    destruct (IH _ Hsv) as (u' & Hu' & Hsu). exists u'; split; [econstructor; eassumption | exact Hsu].
Qed.

Lemma spa_app_inv f l1 l2 A B s x : spa (app f l1 l2 A B s) x ->
  exists f' l1' l2' A' B', x = app f' l1' l2' A' B' s /\ spa f f'.
Proof. intros H; inversion H; subst; do 5 eexists; split; eauto with spa. Qed.
Lemma spa_uapp_inv f ls x : spa (uapp f ls) x -> exists f', x = uapp f' ls /\ spa f f'.
Proof. intros H; inversion H; subst; eexists; split; eauto with spa. Qed.
Lemma spa_capp_inv f Δ0 x : spa (capp f Δ0) x -> exists f', x = capp f' Δ0 /\ spa f f'.
Proof. intros H; inversion H; subst; eexists; split; eauto with spa. Qed.
Lemma spa_tapp_inv f T x : spa (tapp f T) x -> exists f', x = tapp f' T /\ spa f f'.
Proof. intros H; inversion H; subst; eexists; split; eauto with spa. Qed.

Definition AP_tm G Γ t t' T : Prop := forall t2 t2', spa t t2 -> spa t' t2' -> ac_tm G Γ t2 t2' T.
Definition AP_tmnf G Γ t t' T : Prop := forall t2 t2', spa t t2 -> spa t' t2' -> ac_tmnf G Γ t2 t2' T.
Definition AP_tmne G Γ t t' T : Prop := forall t2 t2', spa t t2 -> spa t' t2' -> ac_tmne G Γ t2 t2' T.
Definition AP_tmnee G Γ t t' T : Prop := forall t2 t2', spa t t2 -> spa t' t2' -> ac_tmnee G Γ t2 t2' T.

(** A non-spine head is only related to itself. *)
Ltac spa_triv :=
  repeat match goal with Hs : spa ?t ?x |- _ =>
    is_var x; tryif is_var t then fail else (inversion Hs; subst; clear Hs) end.

Theorem ac_spa_all :
  (forall G Γ T T', ac_ty G Γ T T' -> True) /\
  (forall G Γ W W', ac_tynf G Γ W W' -> True) /\
  (forall G Γ V V', ac_tyne G Γ V V' -> True) /\
  (forall G Δ Δ', ac_ctx G Δ Δ' -> True) /\
  (forall G Γ t t' T, ac_tm G Γ t t' T -> AP_tm G Γ t t' T) /\
  (forall G Γ w w' W, ac_tmnf G Γ w w' W -> AP_tmnf G Γ w w' W) /\
  (forall G Γ ν ν' T, ac_tmne G Γ ν ν' T -> AP_tmne G Γ ν ν' T) /\
  (forall G Γ ν ν' W, ac_tmnee G Γ ν ν' W -> AP_tmnee G Γ ν ν' W) /\
  (forall G Γ d d' Δ, ac_sub G Γ d d' Δ -> True).
Proof.
  apply ac_mut; intros; try exact I; intros x x' Hx Hx'.
  (* only reflexive, or a positive type *)
  all: try solve [spa_triv; econstructor; eauto].
  (* reduction *)
  all: try solve
    [ match type of Hx with spa ?a _ => match goal with Hr : reds a _ |- _ =>
        destruct (spa_reds _ _ _ Hr Hx) as (u2 & Hu2 & Hs2) end end;
      match type of Hx' with spa ?a _ => match goal with Hr : reds a _ |- _ =>
        destruct (spa_reds _ _ _ Hr Hx') as (u2' & Hu2' & Hs2') end end;
      eapply actm_red; [eassumption | eassumption | exact Hu2 | exact Hu2' | eapply spa_whnf; eassumption
                       | eapply spa_whnf; eassumption | auto] ].
  (* η *)
  all: try solve
    [ first [apply actmnf_eta | apply actmnf_ueta | apply actmnf_ceta | apply actmnf_teta];
      match goal with IH : AP_tm _ _ _ _ _ |- _ => apply IH end;
      first [ apply spa_app, spa_ren | apply spa_uapp, spa_uren | apply spa_capp, spa_gren
            | apply spa_tapp, spa_gren ]; assumption ].
  (* spine heads *)
  all: first
    [ destruct (spa_app_inv _ _ _ _ _ _ _ Hx) as (hd & ? & ? & ? & ? & -> & Hf);
      destruct (spa_app_inv _ _ _ _ _ _ _ Hx') as (hd' & ? & ? & ? & ? & -> & Hf')
    | destruct (spa_uapp_inv _ _ _ Hx) as (hd & -> & Hf); destruct (spa_uapp_inv _ _ _ Hx') as (hd' & -> & Hf')
    | destruct (spa_capp_inv _ _ _ Hx) as (hd & -> & Hf); destruct (spa_capp_inv _ _ _ Hx') as (hd' & -> & Hf')
    | destruct (spa_tapp_inv _ _ _ Hx) as (hd & -> & Hf); destruct (spa_tapp_inv _ _ _ Hx') as (hd' & -> & Hf') ];
    econstructor;
    first [ match goal with IH : AP_tmnee _ _ _ _ _ |- _ => exact (IH _ _ Hf Hf') end
          | match goal with IH : AP_tm _ _ _ _ _ |- _ => apply IH; apply spa_refl end
          | eassumption ].
Qed.
