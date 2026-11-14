(** * Typing of [dnth] (M17_DESIGN.md, M17a)

    [dnth^l(n; i. F; cs; i)] is a fixed [natrec] schema ([Syntax/Term.v]),
    typed at layers D and M ([compt i]): beyond [nth]'s derivation
    ([PresupAux], M15a), its family moves along the recursion, so the
    derivation crosses two more conversions, Unit-η at the head ([fst cs]
    is at the family's [inl ⟨⟩] instance, the [case] branch at [inl x]) and
    β at the embeddings ([(λy. e (inr y)) j] against [e (inr j)], and the
    identity embedding at the top). The family's instances are handled
    uniformly: [F] under a renaming [r] and at an index [t]
    ([F⟨⇑r⟩[t/i]], [fam_wf] and [fam_eq]). The derivation itself is
    [DNthCore]'s, which takes those instances as premises, so that
    [RecWf] can use it before weakening exists; here they are
    discharged by weakening and substitution. *)
From DeLaM.Typing Require Export Inversion.
From DeLaM.Syntax Require Import TemplateEq.
From DeLaM.Typing Require DNthCore.

(** ** Iterated weakenings *)

Lemma shift2_tm (t : tm) : t⟨↑⟩⟨↑⟩ = t⟨rshift 2⟩.
Proof using . rewrite ren_ren_comp. apply ren_ext_tm; intros m; rlk_simpl; cbn; lia. Qed.
Lemma shiftS_tm (t : tm) k : t⟨rshift k⟩⟨↑⟩ = t⟨rshift (S k)⟩.
Proof using . rewrite ren_ren_comp. apply ren_ext_tm; intros m; rlk_simpl; cbn; lia. Qed.
Lemma lift2_ty (T : ty) : T⟨rlift ↑⟩⟨rlift ↑⟩ = T⟨rlift (rshift 2)⟩.
Proof using . rewrite ren_ren_comp_ty. apply ren_ext_ty; intros [|m]; rlk_simpl; cbn; lia. Qed.
Lemma liftS_ty (T : ty) k : T⟨rlift (rshift k)⟩⟨rlift ↑⟩ = T⟨rlift (rshift (S k))⟩.
Proof using . rewrite ren_ren_comp_ty. apply ren_ext_ty; intros [|m]; rlk_simpl; cbn; lia. Qed.

Lemma shift_add_tm (t : tm) a b : t⟨rshift a⟩⟨rshift b⟩ = t⟨rshift (a + b)⟩.
Proof using . rewrite ren_ren_comp. apply ren_ext_tm; intros m; rlk_simpl; cbn; lia. Qed.
Lemma lift_add_ty (T : ty) a b : T⟨rlift (rshift a)⟩⟨rlift (rshift b)⟩ = T⟨rlift (rshift (a + b))⟩.
Proof using . rewrite ren_ren_comp_ty. apply ren_ext_ty; intros [|m]; rlk_simpl; cbn; lia. Qed.

Lemma shift_lift_tm (t : tm) k a : t⟨rshift (S k)⟩⟨rlift (rshift a)⟩ = t⟨rshift (S k + a)⟩.
Proof using . rewrite ren_ren_comp. apply ren_ext_tm; intros m; rlk_simpl; cbn; rewrite ?Nat.add_succ_r; cbn; rlk_simpl; cbn; lia. Qed.

(** Iterated weakenings to one [rshift k] (and [rlift (rshift k)]). *)
Ltac nshift_go := unfold rshift1; repeat first [ rewrite shift_add_tm | rewrite shift_lift_tm | rewrite lift_add_ty
  | match goal with |- context [rshift (?a + ?b)] =>
      let c := eval compute in (a + b) in change (a + b) with c end ].
(** In a judgement, the context is left alone. *)
Ltac nshift := lazymatch goal with
  | |- [ _ ; ?D ⊢[ _ ] _ @ _ ] => let DD := fresh "DD" in set (DD := D); nshift_go; subst DD
  | |- [ _ ; ?D ⊢[ _ ] _ : _ @ _ ] => let DD := fresh "DD" in set (DD := D); nshift_go; subst DD
  | |- _ => nshift_go
  end.

Lemma wkr_shiftS {Δ Γ A l} k : wkr (rshift k) Δ Γ -> wkr (rshift (S k)) (Δ ,, A @ l) Γ.
Proof using . intros H. exact (wkr_step _ _ _ A l H). Qed.

Ltac wkr_n := repeat first [ apply wkr_shiftS | apply wkr_id | apply wkr_shift1 ].

(** ** Syntactic equations of the motive's instances *)

(** [PresupAux]'s [teq_core] (local to its section): two substitution
    instances agree pointwise. *)
Ltac tcong := repeat match goal with
  | |- tyPi _ _ _ _ = tyPi _ _ _ _ => f_equal
  | |- tySig _ _ _ _ = tySig _ _ _ _ => f_equal
  | |- tyDVec _ _ _ = tyDVec _ _ _ => f_equal
  | |- tyFin _ = tyFin _ => f_equal
  end.
Ltac fin_sub := repeat match goal with
  | |- context [subst_ty (tyFin ?a) ?d] => change (subst_ty (tyFin a) d) with (tyFin (a[d]))
  | |- context [(tyFin ?a)[?d]] => change ((tyFin a)[d]) with (tyFin (a[d]))
  end;
  f_equal; repeat rewrite subst_comp; apply subst_ext; intros ?m; pw;
  rewrite Nat.add_comm; cbn [Nat.add llk]; push_ren; rlk_simpl; cbn; f_equal; lia.
Ltac teq_core := repeat first [ rewrite ren_as_r2l_ty | rewrite ren_as_r2l ];
  repeat first [ rewrite subst_comp_ty | rewrite subst_comp ];
  first [ apply subst_ext_ty | apply subst_ext
        | apply subst_id_ty; [assumption|] | apply subst_id; [assumption|]
        | symmetry; apply subst_id_ty; [assumption|] | symmetry; apply subst_id; [assumption|] ];
  intros [|[|[|[|[|[|[|[|?n]]]]]]]]; unfold lsucc; pw;
  try solve [apply ren_as_r2l | symmetry; apply ren_as_r2l].
(** Raw [ren_ty] (and the like) left by [cbn], back to the classes'
    notation, which [push_ren] and [push_subst] read. *)
Ltac refold := try change ren_ty with (@ren ty Ren_ty); try change ren_tm with (@ren tm Ren_tm);
  try change subst_ty with (@subst ty Subst_ty); try change subst_tm with (@subst tm Subst_tm).
(** A pointwise term equation: congruence down to [n]'s instances, which
    are compared as substitutions. *)
Ltac n_eq := repeat first [ rewrite ren_as_r2l | rewrite ren_as_r2l_ty ];
  repeat first [ rewrite subst_comp | rewrite subst_comp_ty ];
  first [ apply subst_ext | apply subst_ext_ty ]; intros ?m; pw;
  rewrite Nat.add_comm; cbn [Nat.add llk]; push_ren; rlk_simpl; cbn; f_equal; lia.
Ltac tq := refold; push_ren; push_subst; pw;
  repeat match goal with
  | |- ?x = ?x => reflexivity
  | |- app _ _ _ _ _ _ = app _ _ _ _ _ _ => f_equal
  | |- lam _ _ _ _ = lam _ _ _ _ => f_equal
  | |- tmInr _ _ _ _ _ = tmInr _ _ _ _ _ => f_equal
  | |- tmInl _ _ _ _ _ = tmInl _ _ _ _ _ => f_equal
  | |- succ _ = succ _ => f_equal
  | |- tyFin _ = tyFin _ => f_equal
  | |- var _ = var _ => f_equal; lia
  | |- _ = _ => progress (refold; push_ren; push_subst; pw)
  end; n_eq.
(** The motive's equations: by computation on a template ([geq],
    [TemplateEq]), else congruence, then pointwise. *)
Ltac meq_pw := push_subst; tcong; try solve [pw]; try teq_core; try solve [f_equal; try reflexivity; fin_sub]; try solve [tq].
Ltac meq := first [ geq | meq_pw ].

Section DNth.
Context {G : gctx} {i : layer} (Hc : compt i).

Let Hi : typeof i = i := compt_typeof_self _ Hc.
Let Hv : i <> lV := compt_notV _ Hc.

(** ** The family's instances *)

Section Fam.
Context {Γ : ctx} {n : tm} {F : ty} {l : lvl}
  (Hn : [ G ; Γ ⊢[ i ] n : tyNat @ lzero ]) (HF : [ G ; Γ ,, tyFin n @ lzero ⊢[ i ] F @ l ]).

Lemma fam_ctx {Δ r} : wkr r Δ Γ -> [ G ; Δ ⊢[ i ] ] -> [ G ; Δ ,, tyFin n⟨r⟩ @ lzero ⊢[ i ] ].
Proof using Hc Hn.
  intros Hr HΔ. apply (ext_wf Hi); [| exact I]. apply wft_fin; [exact Hv |].
  exact (proj1 (proj2 weakening_r) _ _ _ _ _ _ Hn Hi _ _ Hr HΔ).
Qed.

Lemma fam_wk {Δ r} : wkr r Δ Γ -> [ G ; Δ ⊢[ i ] ] -> [ G ; Δ ,, tyFin n⟨r⟩ @ lzero ⊢[ i ] F⟨rlift r⟩ @ l ].
Proof using Hc Hn HF.
  intros Hr HΔ. eapply (proj1 weakening_r); [exact HF | exact Hi | | exact (fam_ctx Hr HΔ)].
  exact (wkr_up _ _ _ (tyFin n) lzero Hr).
Qed.

Lemma fam_wf {Δ r t} : wkr r Δ Γ -> [ G ; Δ ⊢[ i ] ] -> [ G ; Δ ⊢[ i ] t : tyFin n⟨r⟩ @ lzero ] ->
  [ G ; Δ ⊢[ i ] F⟨rlift r⟩[lsingle t] @ l ].
Proof using Hc Hn HF. intros Hr HΔ Ht. exact (wf_ty_single Hi (fam_wk Hr HΔ) Ht). Qed.

Lemma fam_eq {Δ r t t'} : wkr r Δ Γ -> [ G ; Δ ⊢[ i ] ] ->
  [ G ; Δ ⊢[ i ] t : tyFin n⟨r⟩ @ lzero ] -> [ G ; Δ ⊢[ i ] t' : tyFin n⟨r⟩ @ lzero ] ->
  [ G ; Δ ⊢[ i ] t ≅ t' : tyFin n⟨r⟩ @ lzero ] ->
  [ G ; Δ ⊢[ i ] F⟨rlift r⟩[lsingle t] ≅ F⟨rlift r⟩[lsingle t'] @ l ].
Proof using Hc Hn HF.
  intros Hr HΔ Ht Ht' Htt. exact (wf_ty_func Hi (fam_wk Hr HΔ) (lsub_eq_single Hi Ht Ht' Htt)).
Qed.

End Fam.

Lemma shiftS_single (t : tm) k s : nftm t -> t⟨rshift (S k)⟩[lsingle s] = t⟨rshift k⟩.
Proof using .
  intros _. rewrite (ren_subst _ _ _ (lshift k)).
  - symmetry; apply ren_as_subst. intros m; cbn; rlk_simpl; cbn; f_equal; lia.
  - intros m; rlk_simpl; cbn. rewrite Nat.add_succ_r; cbn. f_equal; lia.
Qed.

Ltac wvar := eapply wf_tm_retype; [eapply wf_var; [rewrite Hi; eassumption | repeat constructor] |
  try (unfold dnthMot, dnthEmb, dnthFam, dnthRes, dnthFamS; push_ren; rlk_simpl; nshift; reflexivity)].

Lemma lq_00 : lequiv (gL G) lzero (lmax lzero lzero).
Proof using . apply lequiv_sym, lmax_idem; exact I. Qed.

(** ** The motive's instances *)

Lemma dnth_E0 l (n : tm) (F : ty) : nftm n -> nfty F ->
  (dnthMot l n F)[lsingle zero] =
  tyPi lzero l (tyPi lzero lzero (tyFin zero) (tyFin n⟨↑⟩))
    (tyPi l l (tyDVec l zero F⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin zero) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))])
       (tyPi lzero l (tyFin zero) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 2) lzero lzero (tyFin zero) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))])).
Proof using .
  intros Nn NF. unfold dnthMot, dnthEmb, dnthFam, dnthRes. push_subst.
  meq.
Qed.

Lemma dnth_ES l (n : tm) (F : ty) : nftm n -> nfty F ->
  (dnthMot l n F)[lsucc] =
  tyPi lzero l (tyPi lzero lzero (tyFin (succ (var 1))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩))
    (tyPi l l (tyDVec l (succ (var 2)) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin (succ (var 3))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))])
       (tyPi lzero l (tyFin (succ (var 3))) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 2) lzero lzero (tyFin (succ (var 4))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))])).
Proof using .
  intros Nn NF. unfold dnthMot, dnthEmb, dnthFam, dnthRes. push_subst. meq.
Qed.

(** [Fin (succ k)] against [Unit + Fin k], both ways. *)
Lemma fin_of_sum {Δ t K} : [ G ; Δ ⊢[ i ] K : tyNat @ lzero ] ->
  [ G ; Δ ⊢[ i ] t : tySum lzero lzero (tyUnit lzero) (tyFin K) @ lmax lzero lzero ] ->
  [ G ; Δ ⊢[ i ] t : tyFin (succ K) @ lzero ].
Proof using Hc.
  intros HK Ht. eapply wf_conv; [eapply wf_lconv; [exact Ht | exact lq_00] |].
  rewrite Hi. exact (eqty_fin_succ _ _ _ _ Hc HK).
Qed.

Lemma fin_of_sum_eq {Δ t t' K} : [ G ; Δ ⊢[ i ] K : tyNat @ lzero ] ->
  [ G ; Δ ⊢[ i ] t ≅ t' : tySum lzero lzero (tyUnit lzero) (tyFin K) @ lmax lzero lzero ] ->
  [ G ; Δ ⊢[ i ] t ≅ t' : tyFin (succ K) @ lzero ].
Proof using Hc.
  intros HK Ht. eapply eqtm_conv; [eapply eqtm_lconv; [exact Ht | exact lq_00] |].
  rewrite Hi. exact (eqty_fin_succ _ _ _ _ Hc HK).
Qed.

Lemma eqty_rw {Δ T1 T2 T1' T2' k} : T1 = T1' -> T2 = T2' ->
  [ G ; Δ ⊢[ i ] T1' ≅ T2' @ k ] -> [ G ; Δ ⊢[ i ] T1 ≅ T2 @ k ].
Proof using . now intros -> ->. Qed.

Section Schema.
Context {Γ : ctx} {n : tm} {F : ty} {l : lvl} (Hl : lwf (gL G) l)
  (Hn : [ G ; Γ ⊢[ i ] n : tyNat @ lzero ]) (HF : [ G ; Γ ,, tyFin n @ lzero ⊢[ i ] F @ l ]).

Let HΓ : [ G ; Γ ⊢[ i ] ] := ctx_of_wf_tm Hi Hn.
Let Nn : nftm n := wf_tm_nf Hn.
Let NF : nfty F := wf_ty_nf HF.

(** [n] in any context weakening [Γ]. *)
Lemma n_wk {Δ r} : wkr r Δ Γ -> [ G ; Δ ⊢[ i ] ] -> [ G ; Δ ⊢[ i ] n⟨r⟩ : tyNat @ lzero ].
Proof using Hc Hn. intros Hr HΔ. exact (proj1 (proj2 weakening_r) _ _ _ _ _ _ Hn Hi _ _ Hr HΔ). Qed.

(** An embedding applied at an index of [Fin k], in a context [Δ] where
    the embedding is [var e], [k] is [var ke] (or any [Nat]), and [Δ]
    weakens [Γ] by [m] binders. *)
Lemma emb_app_wf {Δ m ev K t} : wkr (rshift m) Δ Γ -> [ G ; Δ ⊢[ i ] ] ->
  [ G ; Δ ⊢[ i ] K : tyNat @ lzero ] ->
  [ G ; Δ ⊢[ i ] ev : tyPi lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) @ lmax lzero lzero ] ->
  [ G ; Δ ⊢[ i ] t : tyFin K @ lzero ] ->
  [ G ; Δ ⊢[ i ] app ev lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) t : tyFin n⟨rshift m⟩ @ lzero ].
Proof using Hc Hn.
  intros Hr HΔ HK He Ht.
  assert (HFK : [ G ; Δ ⊢[ i ] tyFin K @ lzero ]) by (apply wft_fin; [exact Hv | exact HK]).
  assert (HΔK : [ G ; Δ ,, tyFin K @ lzero ⊢[ i ] ]) by (apply (ext_wf Hi); [exact HFK | exact I]).
  eapply wf_tm_retype; [apply wf_app; [exact Hv | exact I | exact I | exact HFK | | exact He | exact Ht] |].
  - apply wft_fin; [exact Hv|]. apply (n_wk (wkr_shiftS m Hr) HΔK).
  - change ((tyFin n⟨rshift (S m)⟩)[lsingle t]) with (tyFin (n⟨rshift (S m)⟩[lsingle t])).
    now rewrite shiftS_single.
Qed.

Lemma emb_app_eq {Δ m ev K t t'} : wkr (rshift m) Δ Γ -> [ G ; Δ ⊢[ i ] ] ->
  [ G ; Δ ⊢[ i ] K : tyNat @ lzero ] ->
  [ G ; Δ ⊢[ i ] ev : tyPi lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) @ lmax lzero lzero ] ->
  [ G ; Δ ⊢[ i ] t ≅ t' : tyFin K @ lzero ] ->
  [ G ; Δ ⊢[ i ] app ev lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) t
      ≅ app ev lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) t' : tyFin n⟨rshift m⟩ @ lzero ].
Proof using Hc Hn.
  intros Hr HΔ HK He Ht.
  assert (HFK : [ G ; Δ ⊢[ i ] tyFin K @ lzero ]) by (apply wft_fin; [exact Hv | exact HK]).
  assert (HΔK : [ G ; Δ ,, tyFin K @ lzero ⊢[ i ] ]) by (apply (ext_wf Hi); [exact HFK | exact I]).
  assert (HC : [ G ; Δ ,, tyFin K @ lzero ⊢[ i ] tyFin n⟨rshift (S m)⟩ @ lzero ])
    by (apply wft_fin; [exact Hv|]; apply (n_wk (wkr_shiftS m Hr) HΔK)).
  assert (E : (tyFin n⟨rshift (S m)⟩)[lsingle t] = tyFin n⟨rshift m⟩)
    by (change ((tyFin n⟨rshift (S m)⟩)[lsingle t]) with (tyFin (n⟨rshift (S m)⟩[lsingle t])); now rewrite shiftS_single).
  rewrite <- E. eapply eqtm_app; [exact Hv | exact (lequiv_refl (gL G) lzero I) | exact (lequiv_refl (gL G) lzero I) | exact HFK
    | exact (eqty_refl _ _ _ _ _ HFK) | exact (eqty_refl _ _ _ _ _ HC) | exact (eqtm_refl _ _ _ _ _ _ He) | exact Ht].
Qed.

(** β at an embedding's instance: the family at [(λy. b) s] against [b[s/y]]. *)
Lemma fam_beta {Δ m K b s} : wkr (rshift m) Δ Γ -> [ G ; Δ ⊢[ i ] ] -> [ G ; Δ ⊢[ i ] K : tyNat @ lzero ] ->
  [ G ; Δ ,, tyFin K @ lzero ⊢[ i ] b : tyFin n⟨rshift (S m)⟩ @ lzero ] -> [ G ; Δ ⊢[ i ] s : tyFin K @ lzero ] ->
  [ G ; Δ ⊢[ i ] F⟨rlift (rshift m)⟩[lsingle (app (lam lzero lzero (tyFin K) b) lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) s)]
      ≅ F⟨rlift (rshift m)⟩[lsingle b[lsingle s]] @ l ].
Proof using Hc Hn HF.
  intros Hr HΔ HK Hb Hs.
  assert (HFK : [ G ; Δ ⊢[ i ] tyFin K @ lzero ]) by (apply wft_fin; [exact Hv | exact HK]).
  assert (HΔK : [ G ; Δ ,, tyFin K @ lzero ⊢[ i ] ]) by (apply (ext_wf Hi); [exact HFK | exact I]).
  assert (HC : [ G ; Δ ,, tyFin K @ lzero ⊢[ i ] tyFin n⟨rshift (S m)⟩ @ lzero ])
    by (apply wft_fin; [exact Hv|]; apply (n_wk (wkr_shiftS m Hr) HΔK)).
  assert (E : (tyFin n⟨rshift (S m)⟩)[lsingle s] = tyFin n⟨rshift m⟩)
    by (change ((tyFin n⟨rshift (S m)⟩)[lsingle s]) with (tyFin (n⟨rshift (S m)⟩[lsingle s])); now rewrite shiftS_single).
  assert (Hlam : [ G ; Δ ⊢[ i ] lam lzero lzero (tyFin K) b : tyPi lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) @ lmax lzero lzero ])
    by (apply wf_lam; [exact Hv | exact I | exact I | exact HFK | exact Hb]).
  assert (Hbs : [ G ; Δ ⊢[ i ] b[lsingle s] : tyFin n⟨rshift m⟩ @ lzero ]) by (rewrite <- E; exact (wf_tm_single Hi Hb Hs)).
  assert (Hβ : [ G ; Δ ⊢[ i ] app (lam lzero lzero (tyFin K) b) lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) s ≅ b[lsingle s] : tyFin n⟨rshift m⟩ @ lzero ])
    by (rewrite <- E; exact (eqtm_beta _ _ _ lzero lzero _ _ _ _ Hc I I HFK HC Hb Hs)).
  exact (fam_eq Hn HF Hr HΔ (emb_app_wf Hr HΔ HK Hlam Hs) Hbs Hβ).
Qed.

(** The derivation itself is [DNthCore]'s, at the family's instances
    under weakenings ([fam_wf], [fam_eq]); [RecWf] takes it at abstract
    instances, before weakening exists. *)
Lemma extn_wkr {m Δ} : DNthCore.ctx_extn m Δ Γ -> wkr (rshift m) Δ Γ.
Proof using .
  revert Δ; induction m as [|m IH]; intros Δ Hx; cbn in Hx.
  - subst. exact (wkr_id _).
  - destruct Δ; try contradiction. exact (wkr_shiftS _ (IH _ Hx)).
Qed.

Let NW m Δ (_ : m <= 11) (Hx : DNthCore.ctx_extn m Δ Γ) (HΔ : [ G ; Δ ⊢[ i ] ]) :=
  n_wk (extn_wkr Hx) HΔ.
Let FW m Δ (e : tm) (K : tm) (x : tm) (_ : 2 <= m <= 9) (Hx : DNthCore.ctx_extn m Δ Γ) (HΔ : [ G ; Δ ⊢[ i ] ])
    Ht (_ : DNthCore.wk_tm G i Δ (app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x) (tyFin n⟨rshift m⟩)) :=
  @fam_wf _ n F l Hn HF Δ (rshift m) (app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x) (extn_wkr Hx) HΔ Ht.
Let FV m Δ (_ : 2 <= m <= 2) (Hx : DNthCore.ctx_extn m Δ Γ) (HΔ : [ G ; Δ ⊢[ i ] ]) Ht
    (_ : DNthCore.wk_tm G i Δ (var 0) (tyFin n⟨rshift m⟩)) :=
  @fam_wf _ n F l Hn HF Δ (rshift m) (var 0) (extn_wkr Hx) HΔ Ht.
Let FE m Δ (e : tm) (K : tm) (x : tm) (e' : tm) (K' : tm) (x' : tm) (_ : 6 <= m <= 8)
    (Hx : DNthCore.ctx_extn m Δ Γ) (HΔ : [ G ; Δ ⊢[ i ] ]) Ht Ht' Htt
    (_ : DNthCore.wk_tm G i Δ (app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x) (tyFin n⟨rshift m⟩))
    (_ : DNthCore.wk_tm G i Δ (app e' lzero lzero (tyFin K') (tyFin n⟨rshift (S m)⟩) x') (tyFin n⟨rshift m⟩))
    (_ : DNthCore.wk_eq G i Δ (app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x)
           (app e' lzero lzero (tyFin K') (tyFin n⟨rshift (S m)⟩) x') (tyFin n⟨rshift m⟩)) :=
  @fam_eq _ n F l Hn HF Δ (rshift m) (app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x)
    (app e' lzero lzero (tyFin K') (tyFin n⟨rshift (S m)⟩) x') (extn_wkr Hx) HΔ Ht Ht' Htt.
Let FE0 m Δ (e : tm) (K : tm) (x : tm) (_ : m <= 2) (Hx : DNthCore.ctx_extn m Δ Γ) (HΔ : [ G ; Δ ⊢[ i ] ]) Ht Ht' Htt
    (_ : DNthCore.wk_tm G i Δ (app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x) (tyFin n⟨rshift m⟩))
    (_ : DNthCore.wk_tm G i Δ (var 0) (tyFin n⟨rshift m⟩))
    (_ : DNthCore.wk_eq G i Δ (app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x) (var 0) (tyFin n⟨rshift m⟩)) :=
  @fam_eq _ n F l Hn HF Δ (rshift m) (app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x) (var 0) (extn_wkr Hx) HΔ Ht Ht' Htt.

Lemma dnth_mot_wf : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] dnthMot l n F @ l ].
Proof using Hc Hl Hn HF. exact (DNthCore.dnth_mot_wf Hc Hl HΓ Nn NF Hn HF NW FW FV FE FE0). Qed.

Lemma dnth_base_wf : [ G ; Γ ⊢[ i ] dnthBase l n F : (dnthMot l n F)[lsingle zero] @ l ].
Proof using Hc Hl Hn HF. exact (DNthCore.dnth_base_wf Hc Hl HΓ Nn NF Hn HF NW FW FV FE FE0). Qed.

Lemma dnth_step_wf :
  [ G ; Γ ,, tyNat @ lzero ,, dnthMot l n F @ l ⊢[ i ] dnthStep l n F : (dnthMot l n F)[lsucc] @ l ].
Proof using Hc Hl Hn HF. exact (DNthCore.dnth_step_wf Hc Hl HΓ Nn NF Hn HF NW FW FV FE FE0). Qed.

(** [dnth]'s typing: the [natrec] at the length, applied to the identity
    embedding (β in the family, both of the tuple and of the result), the
    tuple and the index. *)
Lemma dnth_wf {cs t} : [ G ; Γ ⊢[ i ] cs : tyDVec l n F @ l ] -> [ G ; Γ ⊢[ i ] t : tyFin n @ lzero ] ->
  [ G ; Γ ⊢[ i ] tmDNth l n F cs t : F[lsingle t] @ l ].
Proof using Hc Hl Hn HF. exact (DNthCore.dnth_wf_core Hc Hl HΓ Nn NF Hn HF NW FW FV FE FE0). Qed.

End Schema.

End DNth.
