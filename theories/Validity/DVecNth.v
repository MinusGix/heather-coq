(** * Validity of [dnth] (M17_DESIGN.md, M17a: the index lemma)

    [dnth^l(n; i. F; cs; i)] is a fixed [natrec] schema, so its validity
    is the validity lemmas of the formers it is built from, composed along
    its typing derivation ([Typing/DNth.v]), as [V_nth] (M15a) composes
    [nth]'s. Beyond [nth], the family moves along the recursion: its
    instances are [F] under a weakening, at an index ([VG_fam]), and the
    derivation's three conversions (Fin's computation, Unit-η at the head,
    β at the embeddings) are validity of type equalities: [F]'s validity
    at indices related by Unit-η's or β's validity. *)
From DeLaM.Validity Require Export WfNth DVec.
From DeLaM.Typing Require Import DNth.

Section DVecNth.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

(** ** Weakening under the family's binder *)

Lemma VTy_lift1 {G Γ A B B' C kc k l} : VTy G (Γ ,, A @ k) B B' l ->
  VTy G (Γ ,, C @ kc ,, A⟨↑⟩ @ k) B⟨rlift ↑⟩ B'⟨rlift ↑⟩ l.
Proof using .
  intros H Δ d d' [[Hd _] Ha]. rewrite !shift_subst_ty in Ha.
  assert (E1 : forall (T : ty) e, T⟨rlift ↑⟩[e] = T[lcons (ldrop 1 (ldrop 1 e)) (llk e 0)]).
  { intros T e. apply ren_subst_ty. intros [|m]; rewrite rlk_rlift; [reflexivity|].
    change (llk (ldrop 1 (ldrop 1 e)) m = llk e (S (rlk ↑ m))). rewrite !llk_ldrop, rlk_shift1. f_equal. }
  rewrite !E1. exact (H _ _ _ (SubRel_cons Hd Ha)).
Qed.

Lemma VG_lift1 {G Γ A B B' C kc k l} : VTyG G (Γ ,, A @ k) B B' l ->
  VTyG G (Γ ,, C @ kc ,, A⟨↑⟩ @ k) B⟨rlift ↑⟩ B'⟨rlift ↑⟩ l.
Proof using . intros. gl_lift. now apply VTy_lift1. Qed.

Lemma VTy_ren_id {G Γ T T' r l} : (forall k, rlk r k = k) -> VTy G Γ T T' l -> VTy G Γ T⟨r⟩ T'⟨r⟩ l.
Proof using .
  intros Hr H Δ d d' Hd.
  rewrite (ren_subst_ty T r d d), (ren_subst_ty T' r d' d') by (intros k; now rewrite Hr).
  exact (H _ _ _ Hd).
Qed.

Lemma VG_ren_id {G Γ T T' r l} : (forall k, rlk r k = k) -> VTyG G Γ T T' l -> VTyG G Γ T⟨r⟩ T'⟨r⟩ l.
Proof using . intros. gl_lift. now apply VTy_ren_id. Qed.

Lemma VTm_ren_id {G Γ t t' T r l} : (forall k, rlk r k = k) -> VTm G Γ t t' T l -> VTm G Γ t⟨r⟩ t'⟨r⟩ T l.
Proof using .
  intros Hr H Δ d d' Hd.
  rewrite (ren_subst t r d d), (ren_subst t' r d' d') by (intros k; now rewrite Hr).
  exact (H _ _ _ Hd).
Qed.

Lemma VG_ren_id_tm {G Γ t t' T r l} : (forall k, rlk r k = k) -> VTmG G Γ t t' T l -> VTmG G Γ t⟨r⟩ t'⟨r⟩ T l.
Proof using . intros. gl_lift. now apply VTm_ren_id. Qed.

(** The weakenings [dnth]'s schema meets: [m] binders over [Γ]. *)
Lemma wkr_zero_inv {Δ Γ} : wkr (rshift 0) Δ Γ -> Δ = Γ.
Proof using .
  intros H. remember (rshift 0) as r0 eqn:Er. destruct H as [| r Δ Γ A k H | r Δ Γ A k H].
  - reflexivity.
  - destruct r; discriminate.
  - discriminate.
Qed.

Lemma wkr_succ_inv {Δ Γ m} : wkr (rshift (S m)) Δ Γ -> exists Δ0 A k, Δ = Δ0 ,, A @ k /\ wkr (rshift m) Δ0 Γ.
Proof using .
  intros H. remember (rshift (S m)) as r0 eqn:Er. destruct H as [| r Δ Γ A k H | r Δ Γ A k H].
  - discriminate.
  - destruct r as [j|]; [| discriminate]. cbn in Er. injection Er as ->. eauto.
  - discriminate.
Qed.

Ltac vvar := eapply VG_var; [repeat constructor |
  try (unfold dnthMot, dnthEmb, dnthFam, dnthRes, dnthFamS; push_ren; rlk_simpl; nshift; reflexivity)].
(** A context's well-formedness: an assumption, or one extended by [Fin]s
    of its variables. *)
Ltac gctx := first [ eassumption
  | apply (ext_wf ge_typeof); [apply wft_fin; [exact ge_notV |
      eapply wf_tm_retype; [eapply wf_var; [rewrite ge_typeof; gctx | repeat constructor] | reflexivity]] | exact I] ].
Ltac gvar := eapply wf_tm_retype; [eapply wf_var; [rewrite ge_typeof; gctx | repeat constructor] |
  try (unfold dnthMot, dnthEmb, dnthFam, dnthRes, dnthFamS; push_ren; rlk_simpl; nshift; reflexivity)].

Lemma lq_00' {G} : lequiv (gL G) lzero (lmax lzero lzero).
Proof using . apply lequiv_sym, lmax_idem; exact I. Qed.

(** ** The formers' validity, closed under global weakenings *)

Lemma VG_dvec {G Γ l l' n n' F F'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTmG G Γ n n' tyNat lzero -> VTyG G (Γ ,, tyFin n @ lzero) F F' l ->
  VTyG G Γ (tyDVec l n F) (tyDVec l' n' F') l.
Proof using EL VL VN. intros. gl_lift. eapply V_dvec; eassumption. Qed.
Lemma VG_dvec_zero {G Γ l l' F F'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTyG G (Γ ,, tyFin zero @ lzero) F F' l -> VTyG G Γ (tyDVec l zero F) (tyUnit l') l.
Proof using EL VL VN. intros. gl_lift. eapply V_dvec_zero; eassumption. Qed.
Lemma VG_dvec_succ {G Γ l l' n n' F F'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTmG G Γ n n' tyNat lzero -> VTyG G (Γ ,, tyFin (succ n) @ lzero) F F' l ->
  VTyG G Γ (tyDVec l (succ n) F) (tySig l' l' (dvecHd n' F') (dvecTl l' n' F')) l.
Proof using EL VL VN. intros. gl_lift. eapply V_dvec_succ; eassumption. Qed.

Lemma VG_beta {G Γ l l' A B t s} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ,, A @ l ⊢g B @ l' ] -> [ G ; Γ ,, A @ l ⊢g t : B @ l' ] ->
  VTyG G Γ A A l -> VTmG G (Γ ,, A @ l) t t B l' -> VTmG G Γ s s A l ->
  VTmG G Γ (app (lam l l' A t) l l' A B s) t[lsingle s] B[lsingle s] l'.
Proof using EL VL VN. intros. gl_lift. eapply V_beta; eassumption. Qed.
Lemma VG_inl {G Γ l1 l2 l3 l4 A A' B B' a a'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  VTyG G Γ A A' l1 -> VTyG G Γ B B' l2 -> VTmG G Γ a a' A l1 ->
  VTmG G Γ (tmInl l1 l2 A B a) (tmInl l3 l4 A' B' a') (tySum l1 l2 A B) (lmax l1 l2).
Proof using EL VL VN. intros. gl_lift. eapply V_inl; eassumption. Qed.
Lemma VG_inr {G Γ l1 l2 l3 l4 A A' B B' b b'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  VTyG G Γ A A' l1 -> VTyG G Γ B B' l2 -> VTmG G Γ b b' B l2 ->
  VTmG G Γ (tmInr l1 l2 A B b) (tmInr l3 l4 A' B' b') (tySum l1 l2 A B) (lmax l1 l2).
Proof using EL VL VN. intros. gl_lift. eapply V_inr; eassumption. Qed.
Lemma VG_triv {G Γ l l'} : lwf (gL G) l -> lequiv (gL G) l l' -> VTmG G Γ (tmTriv l) (tmTriv l') (tyUnit l) l.
Proof using EL VL VN. intros. gl_lift. eapply V_triv; eassumption. Qed.
Lemma VG_unit_eta {G Γ l t t1 t' t1'} : lwf (gL G) l ->
  VTmG G Γ t t1 (tyUnit l) l -> VTmG G Γ t' t1' (tyUnit l) l -> VTmG G Γ t t1' (tyUnit l) l.
Proof using EL VL VN. intros. gl_lift. eapply V_unit_eta; eassumption. Qed.

(** The step's abbreviations, unfolded. *)
Ltac unset_step := repeat match goal with
  | H := _ |- _ => lazymatch type of H with ty => subst H | tm => subst H end
  end.

(** Normalizing a validity's weakenings, the context left alone. *)
Ltac vshift := lazymatch goal with
  | |- VTyG _ ?D _ _ _ => let DD := fresh "DD" in set (DD := D); nshift_go; subst DD
  | |- VTmG _ ?D _ _ _ _ => let DD := fresh "DD" in set (DD := D); nshift_go; subst DD
  | |- _ => nshift
  end.

Lemma VTyG_rw {G Γ T1 T2 T1' T2' l} : T1 = T1' -> T2 = T2' -> VTyG G Γ T1' T2' l -> VTyG G Γ T1 T2 l.
Proof using . now intros -> ->. Qed.
Lemma VTmG_rw {G Γ t1 t2 T t1' t2' T' l} : t1 = t1' -> t2 = t2' -> T = T' ->
  VTmG G Γ t1' t2' T' l -> VTmG G Γ t1 t2 T l.
Proof using . now intros -> -> ->. Qed.

(** [Fin (succ K)]'s two injections. *)
Lemma VG_fin_inl {G Γ K t t'} : VTmG G Γ K K tyNat lzero -> VTmG G Γ t t' (tyUnit lzero) lzero ->
  VTmG G Γ (tmInl lzero lzero (tyUnit lzero) (tyFin K) t) (tmInl lzero lzero (tyUnit lzero) (tyFin K) t')
    (tyFin (succ K)) lzero.
Proof using EL VL VN.
  intros VK Vt. eapply VTmG_conv; [| exact (VG_fin_succ VK)]. eapply VTmG_lconv; [| exact lq_00'].
  apply VG_inl; [exact I | exact I | exact (lequiv_refl (gL G) lzero I) | exact (lequiv_refl (gL G) lzero I)
    | apply VG_unit; [exact I | exact (lequiv_refl (gL G) lzero I)] | exact (VG_fin VK) | exact Vt].
Qed.
Lemma VG_fin_inr {G Γ K t t'} : VTmG G Γ K K tyNat lzero -> VTmG G Γ t t' (tyFin K) lzero ->
  VTmG G Γ (tmInr lzero lzero (tyUnit lzero) (tyFin K) t) (tmInr lzero lzero (tyUnit lzero) (tyFin K) t')
    (tyFin (succ K)) lzero.
Proof using EL VL VN.
  intros VK Vt. eapply VTmG_conv; [| exact (VG_fin_succ VK)]. eapply VTmG_lconv; [| exact lq_00'].
  apply VG_inr; [exact I | exact I | exact (lequiv_refl (gL G) lzero I) | exact (lequiv_refl (gL G) lzero I)
    | apply VG_unit; [exact I | exact (lequiv_refl (gL G) lzero I)] | exact (VG_fin VK) | exact Vt].
Qed.

(** ** The length and the family, along the schema *)

Section DNthV.
Context {G : gctx} {Γ : ctx} {l l' : lvl} {n n' : tm} {F F' : ty}
  (Hwl : lwf (gL G) l) (Hll : lequiv (gL G) l l')
  (Hn : [ G ; Γ ⊢g n : tyNat @ lzero ]) (Vn : VTmG G Γ n n' tyNat lzero)
  (HF : [ G ; Γ ,, tyFin n @ lzero ⊢g F @ l ]) (VF : VTyG G (Γ ,, tyFin n @ lzero) F F' l).

Let Nn : nftm n := wf_tm_nf Hn.
Let Hw0 : lwf (gL G) lzero := I.

Lemma Vn_wk : forall m Δ, wkr (rshift m) Δ Γ -> VTmG G Δ n⟨rshift m⟩ n'⟨rshift m⟩ tyNat lzero.
Proof using Vn.
  induction m as [|m IH]; intros Δ Hr.
  - rewrite (wkr_zero_inv Hr). apply VG_ren_id_tm; [intros; cbn; lia | exact Vn].
  - destruct (wkr_succ_inv Hr) as (Δ0 & A & k & -> & Hr0).
    rewrite <- !shiftS_tm. exact (VG_shift_tm (IH _ Hr0)).
Qed.

Lemma VG_famw : forall m Δ, wkr (rshift m) Δ Γ ->
  VTyG G (Δ ,, tyFin n⟨rshift m⟩ @ lzero) F⟨rlift (rshift m)⟩ F'⟨rlift (rshift m)⟩ l.
Proof using Hn VF.
  induction m as [|m IH]; intros Δ Hr.
  - rewrite (wkr_zero_inv Hr), (ren_id_tm _ Nn).
    apply VG_ren_id; [intros [|k]; rewrite rlk_rlift; cbn; lia | exact VF].
  - destruct (wkr_succ_inv Hr) as (Δ0 & A & k & -> & Hr0).
    pose proof (VG_lift1 (C := A) (kc := k) (IH _ Hr0)) as X.
    rewrite !liftS_ty in X. change ((tyFin n⟨rshift m⟩)⟨↑⟩) with (tyFin n⟨rshift m⟩⟨↑⟩) in X.
    rewrite shiftS_tm in X. exact X.
Qed.

Lemma VG_fam {Δ m t t'} : wkr (rshift m) Δ Γ -> VTmG G Δ t t' (tyFin n⟨rshift m⟩) lzero ->
  VTyG G Δ F⟨rlift (rshift m)⟩[lsingle t] F'⟨rlift (rshift m)⟩[lsingle t'] l.
Proof using EL Hn VF. intros Hr Ht. exact (VTyG_single (VG_famw _ _ Hr) Ht). Qed.

(** An embedding at an index of [Fin K], the right-hand annotation of its
    codomain any length related to [n]'s weakening. *)
Lemma VG_emb_app_g {Δ m K K' ev ev' t t' n2} : wkr (rshift m) Δ Γ -> [ G ; Δ ⊢g ] ->
  [ G ; Δ ⊢g K : tyNat @ lzero ] -> VTmG G Δ K K' tyNat lzero ->
  VTmG G (Δ ,, tyFin K @ lzero) n⟨rshift (S m)⟩ n2 tyNat lzero ->
  VTmG G Δ ev ev' (tyPi lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩)) (lmax lzero lzero) ->
  VTmG G Δ t t' (tyFin K) lzero ->
  VTmG G Δ (app ev lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) t)
    (app ev' lzero lzero (tyFin K') (tyFin n2) t') (tyFin n⟨rshift m⟩) lzero.
Proof using EL VL VN Hn.
  intros Hr HΔ HK VK Vn2 Vev Vt.
  assert (HFK : [ G ; Δ ⊢g tyFin K @ lzero ]) by (apply wft_fin; [exact ge_notV | exact HK]).
  assert (HΔK : [ G ; Δ ,, tyFin K @ lzero ⊢g ]) by (apply (ext_wf ge_typeof); [exact HFK | exact I]).
  assert (HC : [ G ; Δ ,, tyFin K @ lzero ⊢g tyFin n⟨rshift (S m)⟩ @ lzero ])
    by (apply wft_fin; [exact ge_notV|]; exact (n_wk ge_compt Hn (wkr_shiftS m Hr) HΔK)).
  eapply VTmG_retype; [refine (VG_app Hw0 Hw0 (lequiv_refl _ _ Hw0) (lequiv_refl _ _ Hw0) HC (VG_fin VK) (VG_fin Vn2) Vev Vt) |].
  change ((tyFin n⟨rshift (S m)⟩)[lsingle t]) with (tyFin (n⟨rshift (S m)⟩[lsingle t])). now rewrite shiftS_single.
Qed.

Lemma VG_emb_app {Δ m K K' ev ev' t t'} : wkr (rshift m) Δ Γ -> [ G ; Δ ⊢g ] ->
  [ G ; Δ ⊢g K : tyNat @ lzero ] -> VTmG G Δ K K' tyNat lzero ->
  VTmG G Δ ev ev' (tyPi lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩)) (lmax lzero lzero) ->
  VTmG G Δ t t' (tyFin K) lzero ->
  VTmG G Δ (app ev lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) t)
    (app ev' lzero lzero (tyFin K') (tyFin n'⟨rshift (S m)⟩) t') (tyFin n⟨rshift m⟩) lzero.
Proof using EL VL VN Hn Vn.
  intros Hr HΔ HK VK. apply (VG_emb_app_g Hr HΔ HK VK). exact (Vn_wk _ _ (wkr_shiftS m Hr)).
Qed.

(** The same with [n] on both sides. *)
Lemma Vnn_wk {m Δ} : wkr (rshift m) Δ Γ -> VTmG G Δ n⟨rshift m⟩ n⟨rshift m⟩ tyNat lzero.
Proof using EL VL Vn. intros Hr. pose proof (Vn_wk _ _ Hr) as X. exact (VTmG_trans X (VTmG_sym X)). Qed.

Lemma VG_emb_app_l {Δ m K ev t t'} : wkr (rshift m) Δ Γ -> [ G ; Δ ⊢g ] ->
  [ G ; Δ ⊢g K : tyNat @ lzero ] -> VTmG G Δ K K tyNat lzero ->
  VTmG G Δ ev ev (tyPi lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩)) (lmax lzero lzero) ->
  VTmG G Δ t t' (tyFin K) lzero ->
  VTmG G Δ (app ev lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) t)
    (app ev lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) t') (tyFin n⟨rshift m⟩) lzero.
Proof using EL VL VN Hn Vn.
  intros Hr HΔ HK VK. apply (VG_emb_app_g Hr HΔ HK VK). exact (Vnn_wk (wkr_shiftS m Hr)).
Qed.

(** [F]'s instances at related indices, [F] on both sides: the validity of
    the type equalities the derivation converts along. *)
Lemma VG_fam_rel {Δ m a a'} : wkr (rshift m) Δ Γ -> VTmG G Δ a a' (tyFin n⟨rshift m⟩) lzero ->
  VTyG G Δ F⟨rlift (rshift m)⟩[lsingle a] F⟨rlift (rshift m)⟩[lsingle a'] l.
Proof using EL VL Hn VF.
  intros Hr Ha. exact (VTyG_trans (VG_fam Hr Ha) (VTyG_sym (VG_fam Hr (VTmG_trans (VTmG_sym Ha) Ha)))).
Qed.

(** β at an embedding's instance, in [F] on both sides. *)
Lemma VG_fam_beta {Δ m K b s} : wkr (rshift m) Δ Γ -> [ G ; Δ ,, tyFin K @ lzero ⊢g ] ->
  VTmG G Δ K K tyNat lzero ->
  [ G ; Δ ,, tyFin K @ lzero ⊢g b : tyFin n⟨rshift (S m)⟩ @ lzero ] ->
  VTmG G (Δ ,, tyFin K @ lzero) b b (tyFin n⟨rshift (S m)⟩) lzero -> VTmG G Δ s s (tyFin K) lzero ->
  VTyG G Δ F⟨rlift (rshift m)⟩[lsingle (app (lam lzero lzero (tyFin K) b) lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) s)]
    F⟨rlift (rshift m)⟩[lsingle b[lsingle s]] l.
Proof using EL VL VN Hn VF.
  intros Hr HΔK VK Hb Vb Vs. apply (VG_fam_rel Hr).
  assert (HC : [ G ; Δ ,, tyFin K @ lzero ⊢g tyFin n⟨rshift (S m)⟩ @ lzero ])
    by (apply wft_fin; [exact ge_notV|]; exact (n_wk ge_compt Hn (wkr_shiftS m Hr) HΔK)).
  refine (VTmG_retype (VG_beta Hw0 Hw0 HC Hb (VG_fin VK) Vb Vs) _).
  change ((tyFin n⟨rshift (S m)⟩)[lsingle s]) with (tyFin (n⟨rshift (S m)⟩[lsingle s])). now rewrite shiftS_single.
Qed.

Lemma dnth_emb_V : VTyG G (Γ ,, tyNat @ lzero) (dnthEmb n) (dnthEmb n') lzero.
Proof using EL VL VN Hn Vn.
  pose proof (ctx_of_wf_tm ge_typeof Hn) as HΓ.
  assert (H1 : [ G ; Γ ,, tyNat @ lzero ⊢g ])
    by (apply (ext_wf ge_typeof); [apply wft_nat; [exact ge_notV | rewrite ge_typeof; exact HΓ] | exact I]).
  assert (HF1 : [ G ; Γ ,, tyNat @ lzero ⊢g tyFin (var 0) @ lzero ]) by (apply wft_fin; [exact ge_notV | gvar]).
  assert (H2 : [ G ; Γ ,, tyNat @ lzero ,, tyFin (var 0) @ lzero ⊢g ]) by (apply (ext_wf ge_typeof); [exact HF1 | exact I]).
  unfold dnthEmb. eapply VTyG_lconv; [| exact lq_00'].
  apply VG_pi; [exact Hw0 | exact Hw0 | exact (lequiv_refl _ _ Hw0) | exact (lequiv_refl _ _ Hw0) | | apply VG_fin; vvar |].
  - apply wft_fin; [exact ge_notV |]. nshift. exact (n_wk ge_compt Hn (wkr_shiftS 1 (wkr_shift1 _ _ _)) H2).
  - apply VG_fin. vshift. apply Vn_wk. wkr_n.
Qed.

Lemma dnth_rest_V : VTyG G (Γ ,, tyNat @ lzero ,, dnthEmb n @ lzero)
  (tyPi l l (tyDVec l (var 1) (dnthFam n F)) (tyPi lzero l (tyFin (var 2)) (dnthRes n F)))
  (tyPi l' l' (tyDVec l' (var 1) (dnthFam n' F')) (tyPi lzero l' (tyFin (var 2)) (dnthRes n' F'))) l.
Proof using EL VL VN Hwl Hll Hn Vn HF VF.
  pose proof (dnth_mot_wf ge_compt Hwl Hn HF) as HM.
  destruct (inv_ty_pi HM) as ((_ & _ & _ & HE & HR) & _).
  destruct (inv_ty_pi HR) as ((_ & _ & _ & HD & HP) & _).
  destruct (inv_ty_pi HP) as ((_ & _ & _ & HF2 & HRes) & _).
  destruct (inv_ty_dvec HD) as ((_ & _ & _ & HFam) & _).
  pose proof (ctx_of_wf_ty ge_typeof HFam) as C3. pose proof (ctx_of_wf_ty ge_typeof HRes) as C4.
  eapply VTyG_lconv; [| apply lequiv_sym, lq_ll, Hwl].
  apply VG_pi; [exact Hwl | exact Hwl | exact (lequiv_sym _ _ _ Hll) | exact (lequiv_sym _ _ _ Hll) | exact HP | |].
  - apply VG_dvec; [exact Hwl | exact Hll | vvar |].
    unfold dnthFam. vshift. apply (VG_fam (m := 3)); [wkr_n |].
    apply (VG_emb_app (m := 3)); [wkr_n | exact C3 | gvar | vvar | | vvar].
    eapply VTmG_lconv; [vvar | exact (lequiv_sym _ _ _ lq_00')].
  - eapply VTyG_lconv; [| apply lequiv_sym, lq_0l, Hwl].
    apply VG_pi; [exact Hw0 | exact Hwl | exact (lequiv_refl _ _ Hw0) | exact (lequiv_sym _ _ _ Hll) | exact HRes | apply VG_fin; vvar |].
    unfold dnthRes. vshift. apply (VG_fam (m := 4)); [wkr_n |].
    apply (VG_emb_app (m := 4)); [wkr_n | exact C4 | gvar | vvar | | vvar].
    eapply VTmG_lconv; [vvar | exact (lequiv_sym _ _ _ lq_00')].
Qed.

Lemma dnth_mot_V : VTyG G (Γ ,, tyNat @ lzero) (dnthMot l n F) (dnthMot l' n' F') l.
Proof using EL VL VN Hwl Hll Hn Vn HF VF.
  pose proof (dnth_mot_wf ge_compt Hwl Hn HF) as HM.
  destruct (inv_ty_pi HM) as ((_ & _ & _ & HE & HR) & _).
  unfold dnthMot. eapply VTyG_lconv; [| apply lequiv_sym, lq_0l, Hwl].
  exact (VG_pi Hw0 Hwl (lequiv_refl _ _ Hw0) (lequiv_sym _ _ _ Hll) HR dnth_emb_V dnth_rest_V).
Qed.

(** The base: [λ e cs i. elimEmpty i], at [Fin 0]. The annotations'
    typings come from inverting [dnth_base_wf]. *)
Lemma dnth_base_V : VTmG G Γ (dnthBase l n F) (dnthBase l' n' F') (dnthMot l n F)[lsingle zero] l.
Proof using EL VL VN Hwl Hll Hn Vn HF VF.
  pose proof (dnth_base_wf ge_compt Hwl Hn HF) as HB. pose proof (wf_ty_nf HF) as NF.
  rewrite (dnth_E0 l n F Nn NF) in HB |- *. unfold dnthBase in HB |- *.
  destruct (inv_lam ge_typeof HB) as (B1 & (_ & _ & _ & HE0 & Hb1) & _).
  destruct (inv_lam ge_typeof Hb1) as (B2 & (_ & _ & _ & HD0 & Hb2) & _).
  destruct (inv_lam ge_typeof Hb2) as (B3 & (_ & _ & _ & HF0 & Hb3) & _).
  destruct (inv_elimEmpty ge_typeof Hb3) as ((_ & _ & _ & HM0 & Hv0) & _).
  clear B1 B2 B3 Hb1 Hb2 Hb3 HB.
  destruct (inv_ty_pi HE0) as ((_ & _ & _ & _ & HFn1) & _).
  destruct (inv_ty_dvec HD0) as ((_ & _ & _ & HFam) & _).
  pose proof (ctx_of_wf_ty ge_typeof HFam) as C2. pose proof (ctx_of_wf_tm ge_typeof Hv0) as C3.
  pose proof (ctx_of_wf_ty ge_typeof HM0) as C4.
  assert (Hz : forall Δ, [ G ; Δ ⊢g ] -> [ G ; Δ ⊢g zero : tyNat @ lzero ])
    by (intros Δ HΔ; apply wf_zero; [exact ge_notV | rewrite ge_typeof; exact HΔ]).
  (* the body and the [λ]s' typings *)
  assert (Hbody : [ G ; Γ ,, tyPi lzero lzero (tyFin zero) (tyFin n⟨↑⟩) @ lzero
      ,, tyDVec l zero F⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin zero) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))] @ l
      ,, tyFin zero @ lzero
      ⊢g elimEmpty l lzero F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 3) lzero lzero (tyFin zero) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))] (var 0)
      : F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 2) lzero lzero (tyFin zero) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))] @ l ])
    by (eapply wf_tm_retype; [apply wf_elimEmpty; [exact ge_notV | exact Hwl | exact Hw0 | exact HM0 | exact Hv0] | meq]).
  pose proof (wf_tm_ty ge_typeof Hbody) as HR0.
  assert (Hlam3 : [ G ; Γ ,, tyPi lzero lzero (tyFin zero) (tyFin n⟨↑⟩) @ lzero
      ,, tyDVec l zero F⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin zero) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))] @ l
      ⊢g lam lzero l (tyFin zero) (elimEmpty l lzero F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 3) lzero lzero (tyFin zero) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))] (var 0))
      : tyPi lzero l (tyFin zero) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 2) lzero lzero (tyFin zero) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))] @ l ])
    by (eapply wf_lconv; [apply wf_lam; [exact ge_notV | exact Hw0 | exact Hwl | exact HF0 | exact Hbody] | apply lequiv_sym, lq_0l, Hwl]).
  pose proof (wf_tm_ty ge_typeof Hlam3) as HP3.
  assert (Hlam2 : [ G ; Γ ,, tyPi lzero lzero (tyFin zero) (tyFin n⟨↑⟩) @ lzero
      ⊢g lam l l (tyDVec l zero F⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin zero) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))])
           (lam lzero l (tyFin zero) (elimEmpty l lzero F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 3) lzero lzero (tyFin zero) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))] (var 0)))
      : tyPi l l (tyDVec l zero F⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin zero) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))])
           (tyPi lzero l (tyFin zero) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 2) lzero lzero (tyFin zero) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))]) @ l ])
    by (eapply wf_lconv; [apply wf_lam; [exact ge_notV | exact Hwl | exact Hwl | exact HD0 | exact Hlam3] | apply lequiv_sym, lq_ll, Hwl]).
  pose proof (wf_tm_ty ge_typeof Hlam2) as HP2.
  (* validity, from the inside out *)
  assert (VM0 : VTyG G (Γ ,, tyPi lzero lzero (tyFin zero) (tyFin n⟨↑⟩) @ lzero
      ,, tyDVec l zero F⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin zero) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))] @ l
      ,, tyFin zero @ lzero ,, tyEmpty lzero @ lzero)
      F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 3) lzero lzero (tyFin zero) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))]
      F'⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 3) lzero lzero (tyFin zero) (tyFin n'⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))] l).
  { vshift. apply (VG_fam (m := 4)); [wkr_n |].
    apply (VG_emb_app (m := 4)); [wkr_n | exact C4 | exact (Hz _ C4) | exact VG_zero | |].
    - eapply VTmG_lconv; [vvar | exact (lequiv_sym _ _ _ lq_00')].
    - eapply VTmG_conv; [vvar | exact VG_fin_zero]. }
  assert (VR0 : VTyG G (Γ ,, tyPi lzero lzero (tyFin zero) (tyFin n⟨↑⟩) @ lzero
      ,, tyDVec l zero F⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin zero) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))] @ l
      ,, tyFin zero @ lzero)
      F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 2) lzero lzero (tyFin zero) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))]
      F'⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 2) lzero lzero (tyFin zero) (tyFin n'⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))] l).
  { vshift. apply (VG_fam (m := 3)); [wkr_n |].
    apply (VG_emb_app (m := 3)); [wkr_n | exact C3 | exact (Hz _ C3) | exact VG_zero | | vvar].
    eapply VTmG_lconv; [vvar | exact (lequiv_sym _ _ _ lq_00')]. }
  assert (VD0 : VTyG G (Γ ,, tyPi lzero lzero (tyFin zero) (tyFin n⟨↑⟩) @ lzero)
      (tyDVec l zero F⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin zero) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))])
      (tyDVec l' zero F'⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin zero) (tyFin n'⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))]) l).
  { apply VG_dvec; [exact Hwl | exact Hll | exact VG_zero |].
    vshift. apply (VG_fam (m := 2)); [wkr_n |].
    apply (VG_emb_app (m := 2)); [wkr_n | exact C2 | exact (Hz _ C2) | exact VG_zero | | vvar].
    eapply VTmG_lconv; [vvar | exact (lequiv_sym _ _ _ lq_00')]. }
  assert (VE0 : VTyG G Γ (tyPi lzero lzero (tyFin zero) (tyFin n⟨↑⟩)) (tyPi lzero lzero (tyFin zero) (tyFin n'⟨↑⟩)) lzero).
  { eapply VTyG_lconv; [| exact lq_00'].
    apply VG_pi; [exact Hw0 | exact Hw0 | exact (lequiv_refl _ _ Hw0) | exact (lequiv_refl _ _ Hw0) | exact HFn1 | exact (VG_fin VG_zero) |].
    apply VG_fin. vshift. apply Vn_wk. wkr_n. }
  assert (VP3 : VTyG G (Γ ,, tyPi lzero lzero (tyFin zero) (tyFin n⟨↑⟩) @ lzero
      ,, tyDVec l zero F⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin zero) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))] @ l)
      (tyPi lzero l (tyFin zero) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 2) lzero lzero (tyFin zero) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))])
      (tyPi lzero l' (tyFin zero) F'⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 2) lzero lzero (tyFin zero) (tyFin n'⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))]) l).
  { eapply VTyG_lconv; [| apply lequiv_sym, lq_0l, Hwl].
    exact (VG_pi Hw0 Hwl (lequiv_refl _ _ Hw0) (lequiv_sym _ _ _ Hll) HR0 (VG_fin VG_zero) VR0). }
  assert (VB1 := VG_pi Hwl Hwl (lequiv_sym _ _ _ Hll) (lequiv_sym _ _ _ Hll) HP3 VD0 VP3).
  eapply VTmG_lconv; [| apply lequiv_sym, lq_0l, Hwl].
  refine (VG_lam Hw0 Hwl (lequiv_refl _ _ Hw0) (lequiv_sym _ _ _ Hll) HP2 Hlam2 VE0
            (VTyG_refl_l (VTyG_lconv VB1 (lequiv_sym _ _ _ (lq_ll Hwl)))) _).
  eapply VTmG_lconv; [| apply lequiv_sym, lq_ll, Hwl].
  refine (VG_lam Hwl Hwl (lequiv_sym _ _ _ Hll) (lequiv_sym _ _ _ Hll) HP3 Hlam3 VD0 (VTyG_refl_l VP3) _).
  eapply VTmG_lconv; [| apply lequiv_sym, lq_0l, Hwl].
  refine (VG_lam Hw0 Hwl (lequiv_refl _ _ Hw0) (lequiv_sym _ _ _ Hll) HR0 Hbody (VG_fin VG_zero) (VTyG_refl_l VR0) _).
  refine (VTmG_retype (VG_elimEmpty Hwl Hw0 Hll (lequiv_refl _ _ Hw0) HM0 VM0 _) _); [| meq].
  eapply VTmG_conv; [vvar | exact (VTyG_sym VG_fin_zero)].
Qed.

Lemma dnth_step_V :
  VTmG G (Γ ,, tyNat @ lzero ,, dnthMot l n F @ l) (dnthStep l n F) (dnthStep l' n' F') (dnthMot l n F)[lsucc] l.
Proof using EL VL VN Hwl Hll Hn Vn HF VF.
  pose proof (dnth_step_wf ge_compt Hwl Hn HF) as HS. pose proof (wf_ty_nf HF) as NF.
  rewrite (dnth_ES l n F Nn NF) in HS |- *. unfold dnthStep in HS |- *.
  destruct (inv_lam ge_typeof HS) as (B1 & (_ & _ & _ & HE1 & Hb1) & _).
  destruct (inv_lam ge_typeof Hb1) as (B2 & (_ & _ & _ & HD1 & Hb2) & _).
  destruct (inv_lam ge_typeof Hb2) as (B3 & (_ & _ & _ & HFc & Hb3) & _).
  destruct (inv_case ge_typeof Hb3) as ((_ & _ & _ & _ & HU & HFk & HMc & Hc1 & Hc2 & Hscr) & _).
  clear B1 B2 B3 Hb1 Hb2 Hb3 HS.
  destruct (inv_ty_pi HE1) as ((_ & _ & _ & _ & HFn3) & _).
  destruct (inv_ty_dvec HD1) as ((_ & _ & HK2 & HFam4) & _).
  pose proof (ctx_of_wf_ty ge_typeof HFam4) as C4. pose proof (ctx_of_wf_ty ge_typeof HFk) as C5.
  pose proof (ctx_of_wf_ty ge_typeof HMc) as C6.
  assert (HSc : forall Δ t, [ G ; Δ ⊢g t : tyNat @ lzero ] -> [ G ; Δ ⊢g succ t : tyNat @ lzero ])
    by (intros; apply wf_succ; [exact ge_notV | assumption]).
  pose proof (wf_case _ _ _ _ _ _ _ _ _ _ _ _ ge_notV Hw0 Hw0 Hwl HU HFk HMc Hc1 Hc2 Hscr) as Hbody0.
  lazymatch goal with
  | |- VTmG _ _ (lam _ _ ?e1 (lam _ _ ?d1 (lam _ _ _ (tmCase _ _ _ _ _ ?mc ?c1 ?c2 _))))
                (lam _ _ ?e1' (lam _ _ ?d1' (lam _ _ _ (tmCase _ _ _ _ _ ?mc' ?c1' ?c2' _))))
                (tyPi _ _ _ (tyPi _ _ _ (tyPi _ _ _ ?r))) _ =>
    set (E1 := e1) in *; set (E1' := e1') in *; set (D1 := d1) in *; set (D1' := d1') in *;
    set (Mc := mc) in *; set (Mc' := mc') in *; set (C1 := c1) in *; set (C1' := c1') in *;
    set (C2 := c2) in *; set (C2' := c2') in *; set (R := r) in *
  end.
  assert (ER : Mc[lsingle (var 0)] = R) by (unset_step; meq).
  rewrite ER in Hbody0.
  pose proof (wf_lconv _ _ _ _ _ l _ (wf_lam _ _ _ _ _ _ _ _ ge_notV Hw0 Hwl HFc Hbody0) (lequiv_sym _ _ _ (lq_0l Hwl))) as Hlam3.
  pose proof (wf_tm_ty ge_typeof Hlam3) as HP3.
  pose proof (wf_lconv _ _ _ _ _ l _ (wf_lam _ _ _ _ _ _ _ _ ge_notV Hwl Hwl HD1 Hlam3) (lequiv_sym _ _ _ (lq_ll Hwl))) as Hlam2.
  pose proof (wf_tm_ty ge_typeof Hlam2) as HP2. pose proof (wf_tm_ty ge_typeof Hbody0) as HR.
  (* the binders' types *)
  assert (VE1 : VTyG G (Γ ,, tyNat @ lzero ,, dnthMot l n F @ l) E1 E1' lzero).
  { unset_step. eapply VTyG_lconv; [| exact lq_00'].
    apply VG_pi; [exact Hw0 | exact Hw0 | exact (lequiv_refl _ _ Hw0) | exact (lequiv_refl _ _ Hw0) | exact HFn3 | apply VG_fin, VG_succ; vvar |].
    apply VG_fin. vshift. apply Vn_wk. wkr_n. }
  assert (VD1 : VTyG G (Γ ,, tyNat @ lzero ,, dnthMot l n F @ l ,, E1 @ lzero) D1 D1' l).
  { unset_step. apply VG_dvec; [exact Hwl | exact Hll | apply VG_succ; vvar |].
    vshift. apply (VG_fam (m := 4)); [wkr_n |].
    apply (VG_emb_app (m := 4)); [wkr_n | exact C4 | apply HSc; gvar | apply VG_succ; vvar | | vvar].
    eapply VTmG_lconv; [vvar | exact (lequiv_sym _ _ _ lq_00')]. }
  assert (VR : VTyG G (Γ ,, tyNat @ lzero ,, dnthMot l n F @ l ,, E1 @ lzero ,, D1 @ l ,, tyFin (succ (var 3)) @ lzero) R R l).
  { unset_step. vshift. apply (VG_fam_rel (m := 5)); [wkr_n |].
    apply (VG_emb_app_l (m := 5)); [wkr_n | exact C5 | apply HSc; gvar | apply VG_succ; vvar | | vvar].
    eapply VTmG_lconv; [vvar | exact (lequiv_sym _ _ _ lq_00')]. }
  assert (VFc : VTyG G (Γ ,, tyNat @ lzero ,, dnthMot l n F @ l ,, E1 @ lzero ,, D1 @ l) (tyFin (succ (var 3))) (tyFin (succ (var 3))) lzero)
    by (apply VG_fin, VG_succ; vvar).
  assert (VP3 := VTyG_lconv (VG_pi Hw0 Hwl (lequiv_refl _ _ Hw0) (lequiv_refl _ _ Hwl) HR VFc VR) (lequiv_sym _ _ _ (lq_0l Hwl))).
  assert (VB1 := VTyG_lconv (VG_pi Hwl Hwl (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwl) HP3 (VTyG_refl_l VD1) VP3) (lequiv_sym _ _ _ (lq_ll Hwl))).
  (* the tuple, as a pair, under one more binder *)
  assert (VTup : forall X k, [ G ; Γ ,, tyNat @ lzero ,, dnthMot l n F @ l ,, E1 @ lzero ,, D1 @ l ,, tyFin (succ (var 3)) @ lzero ,, X @ k ⊢g ] ->
    VTyG G (Γ ,, tyNat @ lzero ,, dnthMot l n F @ l ,, E1 @ lzero ,, D1 @ l ,, tyFin (succ (var 3)) @ lzero ,, X @ k)
      (dvecHd (var 5) (dnthFamS n F)) (dvecHd (var 5) (dnthFamS n' F')) l /\
    VTyG G (Γ ,, tyNat @ lzero ,, dnthMot l n F @ l ,, E1 @ lzero ,, D1 @ l ,, tyFin (succ (var 3)) @ lzero ,, X @ k
        ,, dvecHd (var 5) (dnthFamS n F) @ l)
      (dvecTl l (var 5) (dnthFamS n F)) (dvecTl l' (var 5) (dnthFamS n' F')) l /\
    VTmG G (Γ ,, tyNat @ lzero ,, dnthMot l n F @ l ,, E1 @ lzero ,, D1 @ l ,, tyFin (succ (var 3)) @ lzero ,, X @ k)
      (var 2) (var 2) (tySig l l (dvecHd (var 5) (dnthFamS n F)) (dvecTl l (var 5) (dnthFamS n F))) (lmax l l)).
  { intros X k HX. unset_step.
    match type of HX with [ _ ; ?D ⊢g ] => set (Dx := D) in * end.
    assert (Hk5 : [ G ; Dx ⊢g var 5 : tyNat @ lzero ]) by gvar.
    assert (VK5 : VTmG G Dx (var 5) (var 5) tyNat lzero) by vvar.
    assert (H7 : [ G ; Dx ,, tyFin (succ (var 5)) @ lzero ⊢g ])
      by (apply (ext_wf ge_typeof); [apply wft_fin; [exact ge_notV | apply HSc, Hk5] | exact I]).
    assert (VFS : VTyG G (Dx ,, tyFin (succ (var 5)) @ lzero) (dnthFamS n F) (dnthFamS n' F') l).
    { unfold dnthFamS. vshift. apply (VG_fam (m := 7)); [unfold Dx; wkr_n |].
      apply (VG_emb_app (m := 7)); [unfold Dx; wkr_n | exact H7 | apply HSc; gvar | apply VG_succ; vvar | | vvar].
      eapply VTmG_lconv; [vvar | exact (lequiv_sym _ _ _ lq_00')]. }
    split; [| split].
    - eapply VTyG_single; [exact VFS |]. apply VG_fin_inl; [exact VK5 | apply VG_triv; [exact I | exact (lequiv_refl (gL G) lzero I)]].
    - rewrite !dvecTl_eq. apply VG_shift. apply VG_dvec; [exact Hwl | exact Hll | exact VK5 |].
      unfold dvecMv. eapply VTyG_single; [exact (VG_lift1 (C := tyFin (var 5)) (kc := lzero) VFS) |].
      change ((tyFin (succ (var 5)))⟨↑⟩) with (tyFin (succ (var 5)⟨↑⟩)).
      apply VG_fin_inr; [exact (VG_shift_tm VK5) | vvar].
    - pose proof (VG_dvec_succ (l' := l) Hwl (lequiv_refl _ _ Hwl) VK5 (VTyG_refl_l VFS)) as VS.
      eapply VTmG_conv; [| exact (VTyG_lconv (VTyG_sym VS) (lq_ll Hwl))].
      eapply VTmG_lconv; [vvar | exact (lq_ll Hwl)]; push_ren; unfold dnthFamS; meq. }
  (* the three [λ]s *)
  eapply VTmG_lconv; [| apply lequiv_sym, lq_0l, Hwl].
  refine (VG_lam Hw0 Hwl (lequiv_refl _ _ Hw0) (lequiv_sym _ _ _ Hll) HP2 Hlam2 VE1 VB1 _).
  eapply VTmG_lconv; [| apply lequiv_sym, lq_ll, Hwl].
  refine (VG_lam Hwl Hwl (lequiv_sym _ _ _ Hll) (lequiv_sym _ _ _ Hll) HP3 Hlam3 VD1 VP3 _).
  eapply VTmG_lconv; [| apply lequiv_sym, lq_0l, Hwl].
  refine (VG_lam Hw0 Hwl (lequiv_refl _ _ Hw0) (lequiv_sym _ _ _ Hll) HR Hbody0 VFc VR _).
  (* the [case] *)
  rewrite <- ER.
  refine (VG_case Hw0 Hw0 Hwl (VG_unit Hw0 (lequiv_refl _ _ Hw0)) _ _ _ _ (lequiv_refl _ _ Hw0) (lequiv_refl _ _ Hw0) Hll _).
  - apply VG_fin. vvar.
  - unset_step. vshift. apply (VG_fam (m := 6)); [wkr_n |].
    apply (VG_emb_app (m := 6)); [wkr_n | exact C6 | apply HSc; gvar | apply VG_succ; vvar | |].
    + eapply VTmG_lconv; [vvar | exact (lequiv_sym _ _ _ lq_00')].
    + eapply VTmG_conv; [| apply (VG_fin_succ (n := var 5) (n' := var 5)); vvar].
      eapply VTmG_lconv; [vvar | exact lq_00'].
  - (* inl: the head, at the family's [inl ⟨⟩] instance (Unit-η) *)
    unset_step. pose proof (ctx_of_wf_tm ge_typeof Hc1) as Cu.
    destruct (inv_fst ge_typeof Hc1) as ((_ & _ & _ & _ & HTl & _) & _).
    destruct (VTup _ _ Cu) as (VHd & VTl & Vp).
    eapply VTmG_conv; [exact (VG_fst Hwl Hwl (lequiv_sym _ _ _ Hll) (lequiv_sym _ _ _ Hll) HTl VHd VTl Vp) |].
    refine (VTyG_rw _ _ (VG_fam_rel (m := 6)
      (a := app (var 3) lzero lzero (tyFin (succ (var 5))) (tyFin n⟨rshift 7⟩) (tmInl lzero lzero (tyUnit lzero) (tyFin (var 5)) (var 0)))
      (a' := app (var 3) lzero lzero (tyFin (succ (var 5))) (tyFin n⟨rshift 7⟩) (tmInl lzero lzero (tyUnit lzero) (tyFin (var 5)) (tmTriv lzero)))
      _ _)).
    + meq.
    + unfold dnthFamS. meq.
    + wkr_n.
    + apply (VG_emb_app_l (m := 6)); [wkr_n | exact Cu | apply HSc; gvar | apply VG_succ; vvar | |].
      * eapply VTmG_lconv; [vvar | exact (lequiv_sym _ _ _ lq_00')].
      * apply VG_fin_inl; [vvar |]. eapply VG_unit_eta; [exact I | vvar | apply VG_triv; [exact I | exact (lequiv_refl (gL G) lzero I)]].
  - (* inr: the recursive call at [λy. e (inr y)], the tail and the index (β) *)
    unset_step. pose proof (ctx_of_wf_tm ge_typeof Hc2) as Cj.
    destruct (inv_app ge_typeof Hc2) as ((_ & _ & _ & _ & HFr & Hf & _) & _).
    destruct (inv_app ge_typeof Hf) as ((_ & _ & _ & _ & HPi & Hg & Hsnd) & _).
    destruct (inv_app ge_typeof Hg) as ((_ & _ & _ & _ & HRest & _ & HlamE) & _).
    destruct (inv_snd ge_typeof Hsnd) as ((_ & _ & _ & _ & HTl & _) & _).
    destruct (inv_lam ge_typeof HlamE) as (BE & (_ & _ & _ & _ & HbE) & _).
    destruct (inv_app ge_typeof HbE) as ((_ & _ & _ & HAE & HBE & HevE & HinrE) & _).
    destruct (inv_ty_pi HPi) as ((_ & _ & _ & _ & HFr8) & _).
    destruct (VTup _ _ Cj) as (VHd & VTl & Vp).
    pose proof (ctx_of_wf_ty ge_typeof HFr) as Cj5. pose proof (ctx_of_wf_ty ge_typeof HFr8) as Cj6.
    lazymatch goal with
    | |- VTmG _ ?Dj (app (app _ _ _ _ _ _) _ _ _ ?fr _) (app (app _ _ _ _ _ _) _ _ _ ?fr' _) _ _ =>
      assert (VFr : VTyG G (Dj ,, tyFin (var 5) @ lzero) fr fr' l)
    end.
    { vshift. apply (VG_fam (m := 7)); [wkr_n |].
      apply (VG_emb_app (m := 7)); [wkr_n | exact Cj5 | apply HSc; gvar | apply VG_succ; vvar | |].
      - eapply VTmG_lconv; [vvar | exact (lequiv_sym _ _ _ lq_00')].
      - apply VG_fin_inr; vvar. }
    lazymatch goal with
    | |- VTmG _ ?Dj (app (app _ _ _ ?dv (tyPi _ _ _ ?fr8) _) _ _ _ _ _) (app (app _ _ _ _ (tyPi _ _ _ ?fr8') _) _ _ _ _ _) _ _ =>
      assert (VFr8 : VTyG G (Dj ,, dv @ l ,, tyFin (var 6) @ lzero) fr8 fr8' l)
    end.
    { vshift. apply (VG_fam (m := 8)); [wkr_n |].
      apply (VG_emb_app (m := 8)); [wkr_n | exact Cj6 | apply HSc; gvar | apply VG_succ; vvar | |].
      - eapply VTmG_lconv; [vvar | exact (lequiv_sym _ _ _ lq_00')].
      - apply VG_fin_inr; vvar. }
    refine (VTmG_retype (VG_app Hw0 Hwl (lequiv_refl _ _ Hw0) (lequiv_sym _ _ _ Hll) HFr _ VFr _ _) _).
    + apply VG_fin. vvar.
    + (* the recursive call, applied to the tail *)
      eapply VTmG_lconv; [| apply lq_0l, Hwl].
      refine (VTmG_retype (VG_app Hwl Hwl (lequiv_sym _ _ _ Hll) (lequiv_sym _ _ _ Hll) HPi _ _ _ _) _).
      * apply VG_dvec; [exact Hwl | exact Hll | vvar | exact VFr].
      * eapply VTyG_lconv; [| apply lequiv_sym, lq_0l, Hwl].
        refine (VG_pi Hw0 Hwl (lequiv_refl _ _ Hw0) (lequiv_sym _ _ _ Hll) HFr8 _ VFr8). apply VG_fin. vvar.
      * (* the recursive call at the shifted embedding *)
        eapply VTmG_lconv; [| apply lq_ll, Hwl].
        eapply VTmG_conv; [refine (VG_app Hw0 Hwl (lequiv_refl _ _ Hw0) (lequiv_sym _ _ _ Hll) HRest _ _ _ _) |].
        -- do 5 apply VG_shift. exact dnth_emb_V.
        -- do 5 apply VG_lift1. exact dnth_rest_V.
        -- eapply VTmG_lconv; [| exact (lq_0l Hwl)]. eapply VG_var; [repeat constructor | reflexivity].
        -- refine (VTmG_retype (VTmG_lconv (VG_lam (B := tyFin n⟨rshift 7⟩) Hw0 Hw0 (lequiv_refl _ _ Hw0) (lequiv_refl _ _ Hw0) _ _ _ _ _) lq_00') _).
           ++ apply wft_fin; [exact ge_notV |]. apply (n_wk ge_compt Hn); [wkr_n | exact Cj5].
           ++ eapply wf_tm_retype; [exact (wf_app _ _ _ _ _ _ _ _ _ ge_notV Hw0 Hw0 HAE HBE HevE HinrE) | meq].
           ++ apply VG_fin. vvar.
           ++ apply VG_fin, Vnn_wk. wkr_n.
           ++ vshift. apply (VG_emb_app (m := 7)); [wkr_n | exact Cj5 | apply HSc; gvar | apply VG_succ; vvar | |].
              ** eapply VTmG_lconv; [vvar | exact (lequiv_sym _ _ _ lq_00')].
              ** apply VG_fin_inr; vvar.
           ++ unfold dnthEmb. push_ren. rlk_simpl. nshift. reflexivity.
        -- (* its type, β in the family *)
           refine (VTyG_rw eq_refl _ (VTyG_lconv (VG_pi
             (A' := tyDVec l (var 5) F⟨rlift (rshift 7)⟩[lsingle (app (lam lzero lzero (tyFin (var 6)) (app (var 5) lzero lzero (tyFin (succ (var 7))) (tyFin n⟨rshift 9⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 7)) (var 0)))) lzero lzero (tyFin (var 6)) (tyFin n⟨rshift 8⟩) (var 0))])
             (B' := tyPi lzero l (tyFin (var 6)) F⟨rlift (rshift 8)⟩[lsingle (app (lam lzero lzero (tyFin (var 7)) (app (var 6) lzero lzero (tyFin (succ (var 8))) (tyFin n⟨rshift 10⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 8)) (var 0)))) lzero lzero (tyFin (var 7)) (tyFin n⟨rshift 9⟩) (var 0))])
             Hwl Hwl (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwl) HPi _ _) (lequiv_sym _ _ _ (lq_ll Hwl)))).
           ++ unfold dnthFam, dnthRes. push_ren. push_subst. meq.
           ++ apply VG_dvec; [exact Hwl | exact (lequiv_refl _ _ Hwl) | vvar |].
              apply VTyG_sym. refine (VTyG_rw eq_refl _ (VG_fam_beta (m := 7) _ _ _ _ _ _)).
              ** meq.
              ** wkr_n.
              ** gctx.
              ** vvar.
              ** apply (emb_app_wf ge_compt Hn (m := 8)); [wkr_n | gctx | apply HSc; gvar | |].
                 { eapply wf_lconv; [gvar | exact (lequiv_sym _ _ _ lq_00')]. }
                 { apply (fin_of_sum ge_compt); [gvar |]. apply wf_inr; [exact ge_notV | exact I | exact I | | apply wft_fin; [exact ge_notV | gvar] | gvar].
                   apply wft_unit; [exact ge_notV | rewrite ge_typeof | exact I]. gctx. }
              ** apply (VG_emb_app_l (m := 8)); [wkr_n | gctx | apply HSc; gvar | apply VG_succ; vvar | |].
                 { eapply VTmG_lconv; [vvar | exact (lequiv_sym _ _ _ lq_00')]. }
                 { apply VG_fin_inr; vvar. }
              ** vvar.
           ++ eapply VTyG_lconv; [| apply lequiv_sym, lq_0l, Hwl].
              refine (VG_pi Hw0 Hwl (lequiv_refl _ _ Hw0) (lequiv_refl _ _ Hwl) HFr8 _ _); [apply VG_fin; vvar |].
              apply VTyG_sym. refine (VTyG_rw eq_refl _ (VG_fam_beta (m := 8) _ _ _ _ _ _)).
              ** meq.
              ** wkr_n.
              ** gctx.
              ** vvar.
              ** apply (emb_app_wf ge_compt Hn (m := 9)); [wkr_n | gctx | apply HSc; gvar | |].
                 { eapply wf_lconv; [gvar | exact (lequiv_sym _ _ _ lq_00')]. }
                 { apply (fin_of_sum ge_compt); [gvar |]. apply wf_inr; [exact ge_notV | exact I | exact I | | apply wft_fin; [exact ge_notV | gvar] | gvar].
                   apply wft_unit; [exact ge_notV | rewrite ge_typeof | exact I]. gctx. }
              ** apply (VG_emb_app_l (m := 9)); [wkr_n | gctx | apply HSc; gvar | apply VG_succ; vvar | |].
                 { eapply VTmG_lconv; [vvar | exact (lequiv_sym _ _ _ lq_00')]. }
                 { apply VG_fin_inr; vvar. }
              ** vvar.
      * (* the tail *)
        refine (VTmG_retype (VG_snd Hwl Hwl (lequiv_sym _ _ _ Hll) (lequiv_sym _ _ _ Hll) HTl VHd VTl Vp) _).
        unfold dnthFamS. push_subst. meq.
      * meq.
    + vvar.
    + meq.
  - eapply VTmG_lconv; [| exact (lequiv_sym _ _ _ lq_00')].
    eapply VTmG_conv; [| apply VTyG_sym, (VG_fin_succ (n := var 4) (n' := var 4)); vvar]. vvar.
Qed.

(** M17_DESIGN.md's index lemma: [dnth] at related lengths, families,
    tuples and indices, as [V_nth]. *)
Lemma V_dnth {cs cs' t t'} : VTmG G Γ cs cs' (tyDVec l n F) l -> VTmG G Γ t t' (tyFin n) lzero ->
  VTmG G Γ (tmDNth l n F cs t) (tmDNth l' n' F' cs' t') F[lsingle t] l.
Proof using EL VL VN Hwl Hll Hn Vn HF VF.
  intros Vcs Vt. pose proof (wf_ty_nf HF) as NF.
  pose proof (dnth_mot_wf ge_compt Hwl Hn HF) as HM.
  pose proof (VG_natrec Hwl Hll HM (dnth_base_wf ge_compt Hwl Hn HF) (dnth_step_wf ge_compt Hwl Hn HF)
                dnth_mot_V dnth_base_V dnth_step_V Vn) as VNr.
  pose proof (wf_ty_single ge_typeof HM Hn) as HMn.
  assert (EM : (dnthMot l n F)[lsingle n] = tyPi lzero l (tyPi lzero lzero (tyFin n) (tyFin n⟨↑⟩))
      (tyPi l l (tyDVec l n⟨↑⟩ F⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin n⟨↑⟩⟨↑⟩) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))])
         (tyPi lzero l (tyFin n⟨↑⟩⟨↑⟩) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 2) lzero lzero (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))])))
    by (unfold dnthMot, dnthEmb, dnthFam, dnthRes; meq).
  rewrite EM in VNr, HMn.
  destruct (inv_ty_pi HMn) as ((_ & _ & _ & HEm & HRest) & _).
  destruct (inv_ty_pi HEm) as ((_ & _ & _ & _ & HFn1') & _).
  destruct (inv_ty_pi HRest) as ((_ & _ & _ & HD2 & HP2) & _).
  destruct (inv_ty_pi HP2) as ((_ & _ & _ & _ & HRes3) & _).
  destruct (inv_ty_dvec HD2) as ((_ & _ & _ & HFam2) & _).
  pose proof (ctx_of_wf_ty ge_typeof HFn1') as C1. pose proof (ctx_of_wf_ty ge_typeof HFam2) as C2.
  pose proof (ctx_of_wf_ty ge_typeof HRes3) as C3.
  assert (HΓD : [ G ; Γ ,, tyDVec l n F @ l ⊢g ])
    by (apply (ext_wf ge_typeof); [apply wft_dvec; [exact ge_compt | exact Hwl | exact Hn | exact HF] | exact Hwl]).
  assert (HFn1 : [ G ; Γ ,, tyDVec l n F @ l ⊢g tyFin n⟨↑⟩ @ lzero ])
    by (apply wft_fin; [exact ge_notV | exact (n_wk ge_compt Hn (wkr_shift1 _ _ _) HΓD)]).
  assert (HΓD1 : [ G ; Γ ,, tyDVec l n F @ l ,, tyFin n⟨↑⟩ @ lzero ⊢g ]) by (apply (ext_wf ge_typeof); [exact HFn1 | exact I]).
  assert (HFl : [ G ; Γ ,, tyDVec l n F @ l ,, tyFin n⟨↑⟩ @ lzero ⊢g F⟨rlift ↑⟩ @ l ])
    by exact (fam_wk ge_compt Hn HF (wkr_shift1 _ _ _) HΓD).
  assert (HP : [ G ; Γ ,, tyDVec l n F @ l ⊢g tyPi lzero l (tyFin n⟨↑⟩) F⟨rlift ↑⟩ @ l ])
    by (eapply wft_lconv; [apply wft_pi; [exact ge_notV | exact I | exact Hwl | exact HFn1 | exact HFl] | apply lequiv_sym, lq_0l, Hwl]).
  assert (C11 : [ G ; Γ ,, tyFin n @ lzero ,, tyFin n⟨rshift 1⟩ @ lzero ⊢g ])
    by (apply (ext_wf ge_typeof); [apply wft_fin; [exact ge_notV | apply (n_wk ge_compt Hn); [wkr_n | exact C1]] | exact I]).
  assert (C22 : [ G ; Γ ,, tyDVec l n F @ l ,, tyFin n⟨↑⟩ @ lzero ,, tyFin n⟨rshift 2⟩ @ lzero ⊢g ])
    by (apply (ext_wf ge_typeof); [apply wft_fin; [exact ge_notV | apply (n_wk ge_compt Hn); [wkr_n | exact HΓD1]] | exact I]).
  pose proof (VTmG_trans Vn (VTmG_sym Vn)) as Vnn.
  unfold tmDNth.
  refine (VG_app Hw0 Hwl (lequiv_refl _ _ Hw0) (lequiv_sym _ _ _ Hll) HF (VG_fin Vn) VF _ Vt).
  eapply VTmG_lconv; [| apply lq_0l, Hwl].
  refine (VTmG_retype (VG_app Hwl Hwl (lequiv_sym _ _ _ Hll) (lequiv_sym _ _ _ Hll) HP (VG_dvec Hwl Hll Vn VF) _ _ Vcs) _).
  - eapply VTyG_lconv; [| apply lequiv_sym, lq_0l, Hwl].
    exact (VG_pi Hw0 Hwl (lequiv_refl _ _ Hw0) (lequiv_sym _ _ _ Hll) HFl (VG_fin (VG_shift_tm Vn)) (VG_famw 1 _ (wkr_shift1 _ _ _))).
  - (* the [natrec] at the identity embedding *)
    eapply VTmG_lconv; [| apply lq_ll, Hwl].
    eapply VTmG_conv; [refine (VG_app Hw0 Hwl (lequiv_refl _ _ Hw0) (lequiv_sym _ _ _ Hll) HRest _ _ (VTmG_lconv VNr (lq_0l Hwl)) _) |].
    + eapply VTyG_lconv; [| exact lq_00'].
      exact (VG_pi Hw0 Hw0 (lequiv_refl _ _ Hw0) (lequiv_refl _ _ Hw0) HFn1' (VG_fin Vn) (VG_fin (VG_shift_tm Vn))).
    + eapply VTyG_lconv; [| apply lequiv_sym, lq_ll, Hwl].
      apply VG_pi; [exact Hwl | exact Hwl | exact (lequiv_sym _ _ _ Hll) | exact (lequiv_sym _ _ _ Hll) | exact HP2 | |].
      * apply VG_dvec; [exact Hwl | exact Hll | exact (VG_shift_tm Vn) |].
        vshift. apply (VG_fam (m := 2)); [wkr_n |].
        apply (VG_emb_app (m := 2)); [wkr_n | exact C2 | apply (n_wk ge_compt Hn); [wkr_n | exact C2] | apply Vn_wk; wkr_n | | vvar].
        eapply VTmG_lconv; [vvar | exact (lequiv_sym _ _ _ lq_00')].
      * eapply VTyG_lconv; [| apply lequiv_sym, lq_0l, Hwl].
        apply VG_pi; [exact Hw0 | exact Hwl | exact (lequiv_refl _ _ Hw0) | exact (lequiv_sym _ _ _ Hll) | exact HRes3 | |].
        { apply VG_fin. vshift. apply Vn_wk. wkr_n. }
        vshift. apply (VG_fam (m := 3)); [wkr_n |].
        apply (VG_emb_app (m := 3)); [wkr_n | exact C3 | apply (n_wk ge_compt Hn); [wkr_n | exact C3] | apply Vn_wk; wkr_n | | vvar].
        eapply VTmG_lconv; [vvar | exact (lequiv_sym _ _ _ lq_00')].
    + refine (VTmG_lconv (VG_lam Hw0 Hw0 (lequiv_refl _ _ Hw0) (lequiv_refl _ _ Hw0) HFn1' _ (VG_fin Vn) _ _) lq_00').
      * gvar.
      * apply VG_fin. exact (VTmG_trans (VG_shift_tm Vn) (VTmG_sym (VG_shift_tm Vn))).
      * vvar.
    + (* its type: β in the family, of the tuple and of the result *)
      refine (VTyG_rw eq_refl _ (VTyG_lconv (VG_pi
        (A' := tyDVec l n F⟨rlift (rshift 1)⟩[lsingle (app (lam lzero lzero (tyFin n⟨rshift 1⟩) (var 0)) lzero lzero (tyFin n⟨rshift 1⟩) (tyFin n⟨rshift 2⟩) (var 0))])
        (B' := tyPi lzero l (tyFin n⟨↑⟩) F⟨rlift (rshift 2)⟩[lsingle (app (lam lzero lzero (tyFin n⟨rshift 2⟩) (var 0)) lzero lzero (tyFin n⟨rshift 2⟩) (tyFin n⟨rshift 3⟩) (var 0))])
        Hwl Hwl (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwl) HP _ _) (lequiv_sym _ _ _ (lq_ll Hwl)))).
      * meq.
      * apply VG_dvec; [exact Hwl | exact (lequiv_refl _ _ Hwl) | exact Vnn |].
        apply VTyG_sym. refine (VTyG_rw eq_refl _ (VG_fam_beta (m := 1) _ C11 _ _ _ _)).
        -- meq.
        -- wkr_n.
        -- apply Vnn_wk. wkr_n.
        -- gvar.
        -- vvar.
        -- vvar.
      * eapply VTyG_lconv; [| apply lequiv_sym, lq_0l, Hwl].
        refine (VG_pi Hw0 Hwl (lequiv_refl _ _ Hw0) (lequiv_refl _ _ Hwl) HFl _ _).
        { apply VG_fin. exact (VTmG_trans (VG_shift_tm Vn) (VTmG_sym (VG_shift_tm Vn))). }
        apply VTyG_sym. refine (VTyG_rw eq_refl _ (VG_fam_beta (m := 2) _ C22 _ _ _ _)).
        -- meq.
        -- wkr_n.
        -- apply Vnn_wk. wkr_n.
        -- gvar.
        -- vvar.
        -- vvar.
  - meq.
Qed.

End DNthV.

End DVecNth.
