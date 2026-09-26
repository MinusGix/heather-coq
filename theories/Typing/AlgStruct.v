(** * Structural properties of algorithmic conversion (M6_DESIGN.md step 3)

    Local weakening. Each rule is a lemma over the induction hypotheses;
    the mutual induction dispatches them. Local contexts of layer D (the
    [Δ]s of contextual types) do not depend on the ambient context, so
    [ac_ctx] is untouched. *)
From DeLaM.Typing Require Export Algorithmic Properties.

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

Lemma W_actmne_uapp {G Γ n l T ν ν' ls ls'} : AW_tmnee G Γ ν ν' (tyUPi n l T) -> Forall2 leqv ls ls' ->
  AW_tmne G Γ (uapp ν ls) (uapp ν' ls') T[uext ls lvar]ᵤ.
Proof.
  intros IH Hls Δ r Hr. push_ren. pose proof (IH _ _ Hr) as X. push_ren_in X.
  eapply actmne_uapp; [exact X | exact Hls].
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
