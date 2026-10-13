(** * Typing of [dnth] (M17_DESIGN.md, M17a)

    [dnth^l(n; i. F; cs; i)] is a fixed [natrec] schema ([Syntax/Term.v]),
    typed at layers D and M ([compt i]): beyond [nth]'s derivation
    ([PresupAux], M15a), its family moves along the recursion, so the
    derivation crosses two more conversions, Unit-η at the head ([fst cs]
    is at the family's [inl ⟨⟩] instance, the [case] branch at [inl x]) and
    β at the embeddings ([(λy. e (inr y)) j] against [e (inr j)], and the
    identity embedding at the top). The family's instances are handled
    uniformly: [F] under a renaming [r] and at an index [t]
    ([F⟨⇑r⟩[t/i]], [fam_wf] and [fam_eq]). *)
From DeLaM.Typing Require Export Inversion.

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
Ltac wkn H := first [ exact H | eapply (wk1_ty G i Hi); [eassumption | wkn H] | eapply (wk1_tm G i Hi); [eassumption | wkn H] ].

Lemma lq_00 : lequiv (gL G) lzero (lmax lzero lzero).
Proof using . apply lequiv_sym, lmax_idem; exact I. Qed.

(** ** The motive's instances *)

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
(** The motive's equations: congruence, then pointwise. *)
Ltac meq := push_subst; tcong; try solve [pw]; try teq_core; try solve [f_equal; try reflexivity; fin_sub]; try solve [tq].

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

Lemma sum_of_fin {Δ t K} : [ G ; Δ ⊢[ i ] K : tyNat @ lzero ] -> [ G ; Δ ⊢[ i ] t : tyFin (succ K) @ lzero ] ->
  [ G ; Δ ⊢[ i ] t : tySum lzero lzero (tyUnit lzero) (tyFin K) @ lmax lzero lzero ].
Proof using Hc.
  intros HK Ht. eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]. eapply wf_conv; [exact Ht |].
  rewrite Hi. apply eqty_sym. exact (eqty_fin_succ _ _ _ _ Hc HK).
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

Lemma dnth_emb_wf {Δ m K} : wkr (rshift m) Δ Γ -> [ G ; Δ ⊢[ i ] ] -> [ G ; Δ ⊢[ i ] K : tyNat @ lzero ] ->
  [ G ; Δ ⊢[ i ] tyPi lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) @ lzero ].
Proof using Hc Hn.
  intros Hr HΔ HK.
  assert (HFK : [ G ; Δ ⊢[ i ] tyFin K @ lzero ]) by (apply wft_fin; [exact Hv | exact HK]).
  assert (HΔK : [ G ; Δ ,, tyFin K @ lzero ⊢[ i ] ]) by (apply (ext_wf Hi); [exact HFK | exact I]).
  eapply wft_lconv; [| exact lq_00]. apply wft_pi; [exact Hv | exact I | exact I | exact HFK |].
  apply wft_fin; [exact Hv|]. apply (n_wk (wkr_shiftS m Hr) HΔK).
Qed.

Lemma dnth_mot_wf : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] dnthMot l n F @ l ].
Proof using Hc Hl Hn HF.
  assert (H1 : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] ]) by (apply (ext_wf Hi); [apply wft_nat; [exact Hv | rewrite Hi; exact HΓ] | exact I]).
  assert (Hk1 : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] var 0 : tyNat @ lzero ]) by wvar.
  assert (HE : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] dnthEmb n @ lzero ]).
  { unfold dnthEmb. nshift. exact (dnth_emb_wf (wkr_shift1 _ _ _) H1 Hk1). }
  set (Δ2 := Γ ,, tyNat @ lzero ,, dnthEmb n @ lzero).
  assert (H2 : [ G ; Δ2 ⊢[ i ] ]) by (apply (ext_wf Hi); [exact HE | exact I]).
  assert (Hk2 : [ G ; Δ2 ⊢[ i ] var 1 : tyNat @ lzero ]) by wvar.
  assert (HF2 : [ G ; Δ2 ⊢[ i ] tyFin (var 1) @ lzero ]) by (apply wft_fin; [exact Hv | exact Hk2]).
  assert (H3 : [ G ; Δ2 ,, tyFin (var 1) @ lzero ⊢[ i ] ]) by (apply (ext_wf Hi); [exact HF2 | exact I]).
  assert (HFam : [ G ; Δ2 ,, tyFin (var 1) @ lzero ⊢[ i ] dnthFam n F @ l ]).
  { unfold dnthFam. nshift. apply (fam_wf Hn HF (r := rshift 3)); [wkr_n | exact H3 |].
    apply (emb_app_wf (m := 3)); [wkr_n | exact H3 | wvar | | wvar].
    eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]. wvar. }
  assert (HD : [ G ; Δ2 ⊢[ i ] tyDVec l (var 1) (dnthFam n F) @ l ])
    by (apply wft_dvec; [exact Hc | exact Hl | exact Hk2 | exact HFam]).
  assert (H3' : [ G ; Δ2 ,, tyDVec l (var 1) (dnthFam n F) @ l ⊢[ i ] ]) by (apply (ext_wf Hi); [exact HD | exact Hl]).
  assert (HF3 : [ G ; Δ2 ,, tyDVec l (var 1) (dnthFam n F) @ l ⊢[ i ] tyFin (var 2) @ lzero ])
    by (apply wft_fin; [exact Hv | wvar]).
  assert (H4 : [ G ; Δ2 ,, tyDVec l (var 1) (dnthFam n F) @ l ,, tyFin (var 2) @ lzero ⊢[ i ] ])
    by (apply (ext_wf Hi); [exact HF3 | exact I]).
  unfold dnthMot. eapply wft_lconv; [| apply lequiv_sym, lq_0l, Hl].
  apply wft_pi; [exact Hv | exact I | exact Hl | exact HE |].
  eapply wft_lconv; [| apply lequiv_sym, lq_ll, Hl].
  apply wft_pi; [exact Hv | exact Hl | exact Hl | exact HD |].
  eapply wft_lconv; [| apply lequiv_sym, lq_0l, Hl].
  apply wft_pi; [exact Hv | exact I | exact Hl | exact HF3 |].
  unfold dnthRes. nshift. apply (fam_wf Hn HF (r := rshift 4)); [wkr_n | exact H4 |].
  apply (emb_app_wf (m := 4)); [wkr_n | exact H4 | wvar | | wvar].
  eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]. wvar.
Qed.

Lemma dnth_base_wf : [ G ; Γ ⊢[ i ] dnthBase l n F : (dnthMot l n F)[lsingle zero] @ l ].
Proof using Hc Hl Hn HF.
  rewrite (dnth_E0 l n F Nn NF). unfold dnthBase.
  assert (Hz : forall Δ, [ G ; Δ ⊢[ i ] ] -> [ G ; Δ ⊢[ i ] zero : tyNat @ lzero ])
    by (intros Δ HΔ; apply wf_zero; [exact Hv | rewrite Hi; exact HΔ]).
  assert (HE0 : [ G ; Γ ⊢[ i ] tyPi lzero lzero (tyFin zero) (tyFin n⟨↑⟩) @ lzero ])
    by exact (dnth_emb_wf (m := 0) (wkr_id _) HΓ (Hz _ HΓ)).
  set (Γ1 := Γ ,, tyPi lzero lzero (tyFin zero) (tyFin n⟨↑⟩) @ lzero).
  assert (H1 : [ G ; Γ1 ⊢[ i ] ]) by (apply (ext_wf Hi); [exact HE0 | exact I]).
  assert (HF1 : [ G ; Γ1 ⊢[ i ] tyFin zero @ lzero ]) by (apply wft_fin; [exact Hv | exact (Hz _ H1)]).
  assert (H1' : [ G ; Γ1 ,, tyFin zero @ lzero ⊢[ i ] ]) by (apply (ext_wf Hi); [exact HF1 | exact I]).
  assert (HD0 : [ G ; Γ1 ⊢[ i ] tyDVec l zero F⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin zero) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))] @ l ]).
  { apply wft_dvec; [exact Hc | exact Hl | exact (Hz _ H1) |]. nshift.
    apply (fam_wf Hn HF (r := rshift 2)); [wkr_n | exact H1' |].
    apply (emb_app_wf (m := 2)); [wkr_n | exact H1' | exact (Hz _ H1') | | wvar].
    eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]. wvar. }
  set (Γ2 := Γ1 ,, tyDVec l zero F⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin zero) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))] @ l).
  assert (H2 : [ G ; Γ2 ⊢[ i ] ]) by (apply (ext_wf Hi); [exact HD0 | exact Hl]).
  assert (HF2 : [ G ; Γ2 ⊢[ i ] tyFin zero @ lzero ]) by (apply wft_fin; [exact Hv | exact (Hz _ H2)]).
  assert (H3 : [ G ; Γ2 ,, tyFin zero @ lzero ⊢[ i ] ]) by (apply (ext_wf Hi); [exact HF2 | exact I]).
  assert (EZ : forall Δ, [ G ; Δ ⊢[ i ] ] -> [ G ; Δ ⊢[ typeof i ] tyFin zero ≅ tyEmpty lzero @ lzero ])
    by (intros Δ HΔ; rewrite Hi; apply eqty_fin_zero; [exact Hc | rewrite Hi; exact HΔ]).
  assert (HEm : [ G ; Γ2 ,, tyFin zero @ lzero ⊢[ i ] tyEmpty lzero @ lzero ])
    by (apply wft_empty; [exact Hv | rewrite Hi; exact H3 | exact I]).
  assert (H4 : [ G ; Γ2 ,, tyFin zero @ lzero ,, tyEmpty lzero @ lzero ⊢[ i ] ]) by (apply (ext_wf Hi); [exact HEm | exact I]).
  eapply wf_lconv; [| apply lequiv_sym, lq_0l, Hl].
  apply wf_lam; [exact Hv | exact I | exact Hl | exact HE0 |].
  eapply wf_lconv; [| apply lequiv_sym, lq_ll, Hl].
  apply wf_lam; [exact Hv | exact Hl | exact Hl | exact HD0 |].
  eapply wf_lconv; [| apply lequiv_sym, lq_0l, Hl].
  apply wf_lam; [exact Hv | exact I | exact Hl | exact HF2 |].
  eapply wf_tm_retype; [apply wf_elimEmpty; [exact Hv | exact Hl | exact I | |] |].
  - nshift. apply (fam_wf Hn HF (r := rshift 4)); [wkr_n | exact H4 |].
    apply (emb_app_wf (m := 4)); [wkr_n | exact H4 | exact (Hz _ H4) | |].
    + eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]. wvar.
    + eapply wf_conv; [wvar | exact (EZ _ H4)].
  - eapply wf_conv; [wvar | apply eqty_sym, (EZ _ H3)].
  - meq.
Qed.

Lemma dnth_step_wf :
  [ G ; Γ ,, tyNat @ lzero ,, dnthMot l n F @ l ⊢[ i ] dnthStep l n F : (dnthMot l n F)[lsucc] @ l ].
Proof using Hc Hl Hn HF.
  rewrite (dnth_ES l n F Nn NF). unfold dnthStep.
  assert (Hsucc : forall Δ t, [ G ; Δ ⊢[ i ] t : tyNat @ lzero ] -> [ G ; Δ ⊢[ i ] succ t : tyNat @ lzero ])
    by (intros; apply wf_succ; [exact Hv | assumption]).
  assert (H0 : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] ]) by (apply (ext_wf Hi); [apply wft_nat; [exact Hv | rewrite Hi; exact HΓ] | exact I]).
  set (Δr := Γ ,, tyNat @ lzero ,, dnthMot l n F @ l).
  assert (Hr : [ G ; Δr ⊢[ i ] ]) by (apply (ext_wf Hi); [exact dnth_mot_wf | exact Hl]).
  assert (HE1 : [ G ; Δr ⊢[ i ] tyPi lzero lzero (tyFin (succ (var 1))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) @ lzero ])
    by (nshift; apply (dnth_emb_wf (m := 2)); [unfold Δr; wkr_n | exact Hr | apply Hsucc; wvar]).
  set (Δe := Δr ,, tyPi lzero lzero (tyFin (succ (var 1))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) @ lzero).
  assert (He : [ G ; Δe ⊢[ i ] ]) by (apply (ext_wf Hi); [exact HE1 | exact I]).
  assert (HFe : [ G ; Δe ⊢[ i ] tyFin (succ (var 2)) @ lzero ]) by (apply wft_fin; [exact Hv | apply Hsucc; wvar]).
  assert (He' : [ G ; Δe ,, tyFin (succ (var 2)) @ lzero ⊢[ i ] ]) by (apply (ext_wf Hi); [exact HFe | exact I]).
  assert (HD1 : [ G ; Δe ⊢[ i ] tyDVec l (succ (var 2)) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin (succ (var 3))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))] @ l ]).
  { apply wft_dvec; [exact Hc | exact Hl | apply Hsucc; wvar |]. nshift.
    apply (fam_wf Hn HF (r := rshift 4)); [wkr_n | exact He' |].
    apply (emb_app_wf (m := 4)); [wkr_n | exact He' | apply Hsucc; wvar | | wvar].
    eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]. wvar. }
  set (Δc := Δe ,, tyDVec l (succ (var 2)) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin (succ (var 3))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))] @ l).
  assert (Hcs : [ G ; Δc ⊢[ i ] ]) by (apply (ext_wf Hi); [exact HD1 | exact Hl]).
  assert (HFc : [ G ; Δc ⊢[ i ] tyFin (succ (var 3)) @ lzero ]) by (apply wft_fin; [exact Hv | apply Hsucc; wvar]).
  set (Δi := Δc ,, tyFin (succ (var 3)) @ lzero).
  assert (Hii : [ G ; Δi ⊢[ i ] ]) by (apply (ext_wf Hi); [exact HFc | exact I]).
  eapply wf_lconv; [| apply lequiv_sym, lq_0l, Hl].
  apply wf_lam; [exact Hv | exact I | exact Hl | exact HE1 |].
  eapply wf_lconv; [| apply lequiv_sym, lq_ll, Hl].
  apply wf_lam; [exact Hv | exact Hl | exact Hl | exact HD1 |].
  eapply wf_lconv; [| apply lequiv_sym, lq_0l, Hl].
  apply wf_lam; [exact Hv | exact I | exact Hl | exact HFc |].
  assert (HU : forall Δ, [ G ; Δ ⊢[ i ] ] -> [ G ; Δ ⊢[ i ] tyUnit lzero @ lzero ])
    by (intros Δ HΔ; apply wft_unit; [exact Hv | rewrite Hi; exact HΔ | exact I]).
  assert (HB : [ G ; Δi ⊢[ i ] tyFin (var 4) @ lzero ]) by (apply wft_fin; [exact Hv | wvar]).
  assert (HS : [ G ; Δi ⊢[ i ] tySum lzero lzero (tyUnit lzero) (tyFin (var 4)) @ lmax lzero lzero ])
    by (apply wft_sum; [exact Hv | exact I | exact I | exact (HU _ Hii) | exact HB]).
  assert (HiS : [ G ; Δi ,, tySum lzero lzero (tyUnit lzero) (tyFin (var 4)) @ lmax lzero lzero ⊢[ i ] ])
    by (apply (ext_wf Hi); [exact HS | apply lwf_max; exact I]).
  eapply wf_tm_retype; [apply wf_case; [exact Hv | exact I | exact I | exact Hl | exact (HU _ Hii) | exact HB | | | | ] | meq].
  - (* the motive *) nshift. apply (fam_wf Hn HF (r := rshift 6)); [unfold Δi, Δc, Δe, Δr; wkr_n | exact HiS |].
    apply (emb_app_wf (m := 6)); [unfold Δi, Δc, Δe, Δr; wkr_n | exact HiS | apply Hsucc; wvar | |].
    + eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]. wvar.
    + apply fin_of_sum; [wvar | wvar].
  - (* inl: the head, at the family's [inl ⟨⟩] instance (Unit-η) *)
    set (Δu := Δi ,, tyUnit lzero @ lzero).
    assert (Hu : [ G ; Δu ⊢[ i ] ]) by (apply (ext_wf Hi); [exact (HU _ Hii) | exact I]).
    assert (Hk5 : [ G ; Δu ⊢[ i ] var 5 : tyNat @ lzero ]) by wvar.
    assert (HF5 : [ G ; Δu ⊢[ i ] tyFin (var 5) @ lzero ]) by (apply wft_fin; [exact Hv | exact Hk5]).
    assert (HFS1 : [ G ; Δu ⊢[ i ] tyFin (succ (var 5)) @ lzero ]) by (apply wft_fin; [exact Hv | apply Hsucc, Hk5]).
    assert (Hu' : [ G ; Δu ,, tyFin (succ (var 5)) @ lzero ⊢[ i ] ]) by (apply (ext_wf Hi); [exact HFS1 | exact I]).
    assert (HFS : [ G ; Δu ,, tyFin (succ (var 5)) @ lzero ⊢[ i ] dnthFamS n F @ l ]).
    { unfold dnthFamS. nshift. apply (fam_wf Hn HF (r := rshift 7)); [unfold Δu, Δi, Δc, Δe, Δr; wkr_n | exact Hu' |].
      apply (emb_app_wf (m := 7)); [unfold Δu, Δi, Δc, Δe, Δr; wkr_n | exact Hu' | apply Hsucc; wvar | | wvar].
      eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]. wvar. }
    pose proof (eqty_dvec_succ _ _ _ _ _ _ Hc Hl Hk5 HFS) as EQ.
    destruct (inv_ty_sig (eqty_wf_r Hi EQ)) as ((_ & _ & _ & HA & HB2) & _).
    eapply wf_conv; [apply wf_fst; [exact Hv | exact Hl | exact Hl | exact HA | exact HB2 |] |].
    + eapply wf_lconv; [| apply lq_ll, Hl]. eapply wf_conv; [| rewrite Hi; exact (eqty_sym _ _ _ _ _ _ EQ)].
      wvar. push_ren. unfold dnthFamS. meq.
    + rewrite Hi.
      assert (He3 : [ G ; Δu ⊢[ i ] var 3 : tyPi lzero lzero (tyFin (succ (var 5))) (tyFin n⟨rshift 7⟩) @ lmax lzero lzero ])
        by (eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]; wvar).
      assert (Hx : [ G ; Δu ⊢[ i ] tmInl lzero lzero (tyUnit lzero) (tyFin (var 5)) (var 0) : tyFin (succ (var 5)) @ lzero ])
        by (apply fin_of_sum; [exact Hk5 | apply wf_inl; [exact Hv | exact I | exact I | exact (HU _ Hu) | exact HF5 | wvar]]).
      assert (Ht : [ G ; Δu ⊢[ i ] tmTriv lzero : tyUnit lzero @ lzero ]) by (apply wf_triv; [exact Hv | rewrite Hi; exact Hu | exact I]).
      assert (Hx' : [ G ; Δu ⊢[ i ] tmInl lzero lzero (tyUnit lzero) (tyFin (var 5)) (tmTriv lzero) : tyFin (succ (var 5)) @ lzero ])
        by (apply fin_of_sum; [exact Hk5 | apply wf_inl; [exact Hv | exact I | exact I | exact (HU _ Hu) | exact HF5 | exact Ht]]).
      assert (Exx : [ G ; Δu ⊢[ i ] tmInl lzero lzero (tyUnit lzero) (tyFin (var 5)) (var 0) ≅ tmInl lzero lzero (tyUnit lzero) (tyFin (var 5)) (tmTriv lzero) : tyFin (succ (var 5)) @ lzero ]).
      { apply fin_of_sum_eq; [exact Hk5 |]. apply eqtm_inl; [exact Hv | exact (lequiv_refl (gL G) lzero I) | exact (lequiv_refl (gL G) lzero I)
          | exact (eqty_refl _ _ _ _ _ (HU _ Hu)) | exact (eqty_refl _ _ _ _ _ HF5) |].
        apply eqtm_unit_eta; [exact Hc | exact I | wvar | exact Ht]. }
      assert (Hr6 : wkr (rshift 6) Δu Γ) by (unfold Δu, Δi, Δc, Δe, Δr; wkr_n).
      refine (eqty_rw _ _ (fam_eq Hn HF Hr6 Hu (emb_app_wf (m := 6) Hr6 Hu (Hsucc _ _ Hk5) He3 Hx)
        (emb_app_wf (m := 6) Hr6 Hu (Hsucc _ _ Hk5) He3 Hx') (emb_app_eq (m := 6) Hr6 Hu (Hsucc _ _ Hk5) He3 Exx)));
        unfold dnthFamS; meq.
  - (* inr: the recursive call at [λy. e (inr y)], the tail and the index (β) *)
    set (Δj := Δi ,, tyFin (var 4) @ lzero).
    assert (Hj : [ G ; Δj ⊢[ i ] ]) by (apply (ext_wf Hi); [exact HB | exact I]).
    assert (Hk5 : [ G ; Δj ⊢[ i ] var 5 : tyNat @ lzero ]) by wvar.
    assert (HF5 : [ G ; Δj ⊢[ i ] tyFin (var 5) @ lzero ]) by (apply wft_fin; [exact Hv | exact Hk5]).
    assert (Hj5 : [ G ; Δj ,, tyFin (var 5) @ lzero ⊢[ i ] ]) by (apply (ext_wf Hi); [exact HF5 | exact I]).
    assert (Hk6 : [ G ; Δj ,, tyFin (var 5) @ lzero ⊢[ i ] var 6 : tyNat @ lzero ]) by wvar.
    assert (HF6 : [ G ; Δj ,, tyFin (var 5) @ lzero ⊢[ i ] tyFin (var 6) @ lzero ]) by (apply wft_fin; [exact Hv | exact Hk6]).
    assert (Hj56 : [ G ; Δj ,, tyFin (var 5) @ lzero ,, tyFin (var 6) @ lzero ⊢[ i ] ]) by (apply (ext_wf Hi); [exact HF6 | exact I]).
    assert (Hr6 : wkr (rshift 6) Δj Γ) by (unfold Δj, Δi, Δc, Δe, Δr; wkr_n).
    assert (Hr7 : wkr (rshift 7) (Δj ,, tyFin (var 5) @ lzero) Γ) by (unfold Δj, Δi, Δc, Δe, Δr; wkr_n).
    assert (Hr8 : wkr (rshift 8) (Δj ,, tyFin (var 5) @ lzero ,, tyFin (var 6) @ lzero) Γ) by (unfold Δj, Δi, Δc, Δe, Δr; wkr_n).
    assert (HbE : [ G ; Δj ,, tyFin (var 5) @ lzero ⊢[ i ] app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨rshift 8⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)) : tyFin n⟨rshift 7⟩ @ lzero ]).
    { apply (emb_app_wf Hr7 Hj5 (Hsucc _ _ Hk6)); [eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]; wvar |].
      apply fin_of_sum; [exact Hk6 | apply wf_inr; [exact Hv | exact I | exact I | exact (HU _ Hj5) | exact HF6 | wvar]]. }
    assert (HFres : [ G ; Δj ,, tyFin (var 5) @ lzero ⊢[ i ] F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))] @ l ])
      by (nshift; exact (fam_wf Hn HF Hr7 Hj5 HbE)).
    assert (HDV : [ G ; Δj ⊢[ i ] tyDVec l (var 5) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))] @ l ]) by (apply wft_dvec; [exact Hc | exact Hl | exact Hk5 | exact HFres]).
    assert (HjD : [ G ; Δj ,, tyDVec l (var 5) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))] @ l ⊢[ i ] ]) by (apply (ext_wf Hi); [exact HDV | exact Hl]).
    assert (Hk6' : [ G ; Δj ,, tyDVec l (var 5) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))] @ l ⊢[ i ] var 6 : tyNat @ lzero ]) by wvar.
    assert (HF6' : [ G ; Δj ,, tyDVec l (var 5) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))] @ l ⊢[ i ] tyFin (var 6) @ lzero ]) by (apply wft_fin; [exact Hv | exact Hk6']).
    assert (HjD6 : [ G ; Δj ,, tyDVec l (var 5) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))] @ l ,, tyFin (var 6) @ lzero ⊢[ i ] ]) by (apply (ext_wf Hi); [exact HF6' | exact I]).
    assert (Hk7 : [ G ; Δj ,, tyDVec l (var 5) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))] @ l ,, tyFin (var 6) @ lzero ⊢[ i ] var 7 : tyNat @ lzero ]) by wvar.
    assert (Hr8' : wkr (rshift 8) (Δj ,, tyDVec l (var 5) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))] @ l ,, tyFin (var 6) @ lzero) Γ) by (unfold Δj, Δi, Δc, Δe, Δr; wkr_n).
    assert (HbE' : [ G ; Δj ,, tyDVec l (var 5) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))] @ l ,, tyFin (var 6) @ lzero ⊢[ i ] app (var 5) lzero lzero (tyFin (succ (var 7))) (tyFin n⟨rshift 9⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 7)) (var 0)) : tyFin n⟨rshift 8⟩ @ lzero ]).
    { apply (emb_app_wf Hr8' HjD6 (Hsucc _ _ Hk7)); [eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]; wvar |].
      apply fin_of_sum; [exact Hk7 | apply wf_inr; [exact Hv | exact I | exact I | exact (HU _ HjD6) | apply wft_fin; [exact Hv | exact Hk7] | wvar]]. }
    assert (HPi : [ G ; Δj ,, tyDVec l (var 5) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))] @ l ⊢[ i ] tyPi lzero l (tyFin (var 6)) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 5) lzero lzero (tyFin (succ (var 7))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 7)) (var 0)))] @ l ]).
    { eapply wft_lconv; [| apply lequiv_sym, lq_0l, Hl]. apply wft_pi; [exact Hv | exact I | exact Hl | exact HF6' |].
      nshift. exact (fam_wf Hn HF Hr8' HjD6 HbE'). }
    eapply wf_tm_retype; [eapply wf_app; [exact Hv | exact I | exact Hl | exact HF5 | exact HFres | | wvar] | meq].
    eapply wf_lconv; [| apply lq_0l, Hl].
    eapply wf_tm_retype; [eapply wf_app; [exact Hv | exact Hl | exact Hl | exact HDV | exact HPi | | ] | meq].
    + (* the recursive call at the shifted embedding *)
      assert (Hr4 : [ G ; Δj ⊢[ i ] var 4 : tyPi lzero l (dnthEmb n)⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩
          (tyPi l l (tyDVec l (var 1) (dnthFam n F)) (tyPi lzero l (tyFin (var 2)) (dnthRes n F)))⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ @ l ])
        by wvar.
      destruct (inv_ty_pi (wf_tm_ty Hi Hr4)) as ((_ & _ & _ & HEm & HRest) & _).
      eapply wf_lconv; [| apply lq_ll, Hl].
      eapply wf_conv; [eapply wf_app; [exact Hv | exact I | exact Hl | exact HEm | exact HRest | eapply wf_lconv; [exact Hr4 | apply lq_0l, Hl] |] |].
      * eapply wf_tm_retype; [eapply wf_lconv; [apply wf_lam; [exact Hv | exact I | exact I | exact HF5 | nshift; exact HbE] | exact lq_00] |].
        unfold dnthEmb; push_ren; rlk_simpl; nshift; reflexivity.
      * rewrite Hi.
        assert (EF : [ G ; Δj ,, tyFin (var 5) @ lzero ⊢[ i ] F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))] ≅ F⟨rlift (rshift 7)⟩[lsingle (app (lam lzero lzero (tyFin (var 6)) (app (var 5) lzero lzero (tyFin (succ (var 7))) (tyFin n⟨rshift 9⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 7)) (var 0)))) lzero lzero (tyFin (var 6)) (tyFin n⟨rshift 8⟩) (var 0))] @ l ]).
        { apply eqty_sym. refine (eqty_rw eq_refl _ (fam_beta Hr7 Hj5 Hk6 _ _)); [meq | |].
          - assert (Hk7a : [ G ; Δj ,, tyFin (var 5) @ lzero ,, tyFin (var 6) @ lzero ⊢[ i ] var 7 : tyNat @ lzero ]) by wvar.
            apply (emb_app_wf Hr8 Hj56 (Hsucc _ _ Hk7a)); [eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]; wvar |].
            apply fin_of_sum; [wvar | apply wf_inr; [exact Hv | exact I | exact I | exact (HU _ Hj56) | apply wft_fin; [exact Hv | wvar] | wvar]].
          - wvar. }
        assert (HF7 : [ G ; Δj ,, tyDVec l (var 5) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))] @ l ,, tyFin (var 6) @ lzero ⊢[ i ] tyFin (var 7) @ lzero ]) by (apply wft_fin; [exact Hv | exact Hk7]).
        assert (Hj7 : [ G ; Δj ,, tyDVec l (var 5) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))] @ l ,, tyFin (var 6) @ lzero ,, tyFin (var 7) @ lzero ⊢[ i ] ]) by (apply (ext_wf Hi); [exact HF7 | exact I]).
        assert (Hk8 : [ G ; Δj ,, tyDVec l (var 5) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))] @ l ,, tyFin (var 6) @ lzero ,, tyFin (var 7) @ lzero ⊢[ i ] var 8 : tyNat @ lzero ]) by wvar.
        assert (Hr9 : wkr (rshift 9) (Δj ,, tyDVec l (var 5) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))] @ l ,, tyFin (var 6) @ lzero ,, tyFin (var 7) @ lzero) Γ) by (unfold Δj, Δi, Δc, Δe, Δr; wkr_n).
        assert (EF8 : [ G ; Δj ,, tyDVec l (var 5) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))] @ l ,, tyFin (var 6) @ lzero ⊢[ i ] F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 5) lzero lzero (tyFin (succ (var 7))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 7)) (var 0)))] ≅ F⟨rlift (rshift 8)⟩[lsingle (app (lam lzero lzero (tyFin (var 7)) (app (var 6) lzero lzero (tyFin (succ (var 8))) (tyFin n⟨rshift 10⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 8)) (var 0)))) lzero lzero (tyFin (var 7)) (tyFin n⟨rshift 9⟩) (var 0))] @ l ]).
        { apply eqty_sym. refine (eqty_rw eq_refl _ (fam_beta Hr8' HjD6 Hk7 _ _)); [meq | |].
          - apply (emb_app_wf Hr9 Hj7 (Hsucc _ _ Hk8)); [eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]; wvar |].
            apply fin_of_sum; [exact Hk8 | apply wf_inr; [exact Hv | exact I | exact I | exact (HU _ Hj7) | apply wft_fin; [exact Hv | exact Hk8] | wvar]].
          - wvar. }
        assert (EPi : [ G ; Δj ⊢[ i ] tyPi l l (tyDVec l (var 5) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))]) (tyPi lzero l (tyFin (var 6)) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 5) lzero lzero (tyFin (succ (var 7))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 7)) (var 0)))]) ≅ tyPi l l (tyDVec l (var 5) F⟨rlift (rshift 7)⟩[lsingle (app (lam lzero lzero (tyFin (var 6)) (app (var 5) lzero lzero (tyFin (succ (var 7))) (tyFin n⟨rshift 9⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 7)) (var 0)))) lzero lzero (tyFin (var 6)) (tyFin n⟨rshift 8⟩) (var 0))]) (tyPi lzero l (tyFin (var 6)) F⟨rlift (rshift 8)⟩[lsingle (app (lam lzero lzero (tyFin (var 7)) (app (var 6) lzero lzero (tyFin (succ (var 8))) (tyFin n⟨rshift 10⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 8)) (var 0)))) lzero lzero (tyFin (var 7)) (tyFin n⟨rshift 9⟩) (var 0))]) @ lmax l l ]).
        { apply eqty_pi; [exact Hv | exact (lequiv_refl _ _ Hl) | exact (lequiv_refl _ _ Hl) | exact HDV | |].
          - apply eqty_dvec; [exact Hc | exact (lequiv_refl _ _ Hl) | exact Hk5 | exact (eqtm_refl _ _ _ _ _ _ Hk5) | exact HFres | exact EF].
          - eapply eqty_lconv; [| apply lequiv_sym, lq_0l, Hl].
            apply eqty_pi; [exact Hv | exact (lequiv_refl (gL G) lzero I) | exact (lequiv_refl _ _ Hl) | exact HF6' | exact (eqty_refl _ _ _ _ _ HF6') | exact EF8]. }
        refine (eqty_rw eq_refl _ (eqty_lconv _ _ _ _ _ _ _ EPi (lequiv_sym _ _ _ (lq_ll Hl)))).
        unfold dnthFam, dnthRes. push_ren. push_subst. meq.
    + (* the tail *)
      assert (HFS1 : [ G ; Δj ⊢[ i ] tyFin (succ (var 5)) @ lzero ]) by (apply wft_fin; [exact Hv | apply Hsucc, Hk5]).
      assert (Hj' : [ G ; Δj ,, tyFin (succ (var 5)) @ lzero ⊢[ i ] ]) by (apply (ext_wf Hi); [exact HFS1 | exact I]).
      assert (HFS : [ G ; Δj ,, tyFin (succ (var 5)) @ lzero ⊢[ i ] dnthFamS n F @ l ]).
      { unfold dnthFamS. nshift. apply (fam_wf Hn HF (r := rshift 7)); [unfold Δj, Δi, Δc, Δe, Δr; wkr_n | exact Hj' |].
        apply (emb_app_wf (m := 7)); [unfold Δj, Δi, Δc, Δe, Δr; wkr_n | exact Hj' | apply Hsucc; wvar | | wvar].
        eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]. wvar. }
      pose proof (eqty_dvec_succ _ _ _ _ _ _ Hc Hl Hk5 HFS) as EQ.
      destruct (inv_ty_sig (eqty_wf_r Hi EQ)) as ((_ & _ & _ & HA & HB2) & _).
      eapply wf_tm_retype; [apply wf_snd; [exact Hv | exact Hl | exact Hl | exact HA | exact HB2 |] | unfold dnthFamS; push_subst; meq].
      eapply wf_lconv; [| apply lq_ll, Hl]. eapply wf_conv; [| rewrite Hi; exact (eqty_sym _ _ _ _ _ _ EQ)].
      wvar. push_ren. unfold dnthFamS. meq.
  - (* the scrutinee *) apply sum_of_fin; [wvar | wvar].
Qed.

(** [dnth]'s typing: the [natrec] at the length, applied to the identity
    embedding (β in the family, both of the tuple and of the result), the
    tuple and the index. *)
Lemma dnth_wf {cs t} : [ G ; Γ ⊢[ i ] cs : tyDVec l n F @ l ] -> [ G ; Γ ⊢[ i ] t : tyFin n @ lzero ] ->
  [ G ; Γ ⊢[ i ] tmDNth l n F cs t : F[lsingle t] @ l ].
Proof using Hc Hl Hn HF.
  intros Hcs Ht. unfold tmDNth.
  assert (HFn : [ G ; Γ ⊢[ i ] tyFin n @ lzero ]) by (apply wft_fin; [exact Hv | exact Hn]).
  assert (HΓn : [ G ; Γ ,, tyFin n @ lzero ⊢[ i ] ]) by (apply (ext_wf Hi); [exact HFn | exact I]).
  assert (HDV : [ G ; Γ ⊢[ i ] tyDVec l n F @ l ]) by (apply wft_dvec; [exact Hc | exact Hl | exact Hn | exact HF]).
  assert (HΓD : [ G ; Γ ,, tyDVec l n F @ l ⊢[ i ] ]) by (apply (ext_wf Hi); [exact HDV | exact Hl]).
  assert (HFn1 : [ G ; Γ ,, tyDVec l n F @ l ⊢[ i ] tyFin n⟨↑⟩ @ lzero ])
    by (apply wft_fin; [exact Hv | exact (n_wk (wkr_shift1 _ _ _) HΓD)]).
  assert (HΓD1 : [ G ; Γ ,, tyDVec l n F @ l ,, tyFin n⟨↑⟩ @ lzero ⊢[ i ] ]) by (apply (ext_wf Hi); [exact HFn1 | exact I]).
  apply wf_app; [exact Hv | exact I | exact Hl | exact HFn | exact HF | | exact Ht].
  eapply wf_lconv; [| apply lq_0l, Hl].
  eapply wf_tm_retype; [eapply wf_app; [exact Hv | exact Hl | exact Hl | exact HDV | | | exact Hcs] |].
  - eapply wft_lconv; [| apply lequiv_sym, lq_0l, Hl]. apply wft_pi; [exact Hv | exact I | exact Hl | exact HFn1 |].
    exact (fam_wk Hn HF (wkr_shift1 _ _ _) HΓD).
  - assert (HN : [ G ; Γ ⊢[ i ] natrec l (dnthMot l n F) (dnthBase l n F) (dnthStep l n F) n : tyPi lzero l (tyPi lzero lzero (tyFin n) (tyFin n⟨↑⟩)) (tyPi l l (tyDVec l n⟨↑⟩ F⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin n⟨↑⟩⟨↑⟩) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))]) (tyPi lzero l (tyFin n⟨↑⟩⟨↑⟩) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 2) lzero lzero (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))])) @ l ]).
    { eapply wf_tm_retype; [apply wf_natrec; [exact Hv | exact Hl | exact dnth_mot_wf | exact dnth_base_wf | exact dnth_step_wf | exact Hn] |].
      unfold dnthMot, dnthEmb, dnthFam, dnthRes. meq. }
    destruct (inv_ty_pi (wf_tm_ty Hi HN)) as ((_ & _ & _ & HEm & HRest) & _).
    eapply wf_lconv; [| apply lq_ll, Hl].
    eapply wf_conv; [eapply wf_app; [exact Hv | exact I | exact Hl | exact HEm | exact HRest | eapply wf_lconv; [exact HN | apply lq_0l, Hl] |] |].
    + eapply wf_lconv; [| exact lq_00]. apply wf_lam; [exact Hv | exact I | exact I | exact HFn | wvar].
    + rewrite Hi.
      assert (Hr1 : wkr (rshift 1) (Γ ,, tyFin n @ lzero) Γ) by wkr_n.
      assert (Hr2 : wkr (rshift 2) (Γ ,, tyDVec l n F @ l ,, tyFin n⟨↑⟩ @ lzero) Γ) by wkr_n.
      assert (Hn1 : [ G ; Γ ,, tyFin n @ lzero ⊢[ i ] n⟨rshift 1⟩ : tyNat @ lzero ]) by exact (n_wk Hr1 HΓn).
      assert (Hn2 : [ G ; Γ ,, tyDVec l n F @ l ,, tyFin n⟨↑⟩ @ lzero ⊢[ i ] n⟨rshift 2⟩ : tyNat @ lzero ]) by exact (n_wk Hr2 HΓD1).
      assert (E1 : [ G ; Γ ,, tyFin n @ lzero ⊢[ i ] F ≅ F⟨rlift (rshift 1)⟩[lsingle (app (lam lzero lzero (tyFin n⟨rshift 1⟩) (var 0)) lzero lzero (tyFin n⟨rshift 1⟩) (tyFin n⟨rshift 2⟩) (var 0))] @ l ]).
      { apply eqty_sym. refine (eqty_rw eq_refl _ (fam_beta Hr1 HΓn Hn1 _ _)); [meq | | wvar].
        assert (HX : [ G ; Γ ,, tyFin n @ lzero ,, tyFin n⟨rshift 1⟩ @ lzero ⊢[ i ] ]) by (apply (ext_wf Hi); [apply wft_fin; [exact Hv | exact Hn1] | exact I]).
        wvar. }
      assert (E2 : [ G ; Γ ,, tyDVec l n F @ l ,, tyFin n⟨↑⟩ @ lzero ⊢[ i ] F⟨rlift ↑⟩ ≅ F⟨rlift (rshift 2)⟩[lsingle (app (lam lzero lzero (tyFin n⟨rshift 2⟩) (var 0)) lzero lzero (tyFin n⟨rshift 2⟩) (tyFin n⟨rshift 3⟩) (var 0))] @ l ]).
      { apply eqty_sym. refine (eqty_rw eq_refl _ (fam_beta Hr2 HΓD1 Hn2 _ _)); [meq | | wvar].
        assert (HX : [ G ; Γ ,, tyDVec l n F @ l ,, tyFin n⟨↑⟩ @ lzero ,, tyFin n⟨rshift 2⟩ @ lzero ⊢[ i ] ]) by (apply (ext_wf Hi); [apply wft_fin; [exact Hv | exact Hn2] | exact I]).
        wvar. }
      assert (EPi : [ G ; Γ ⊢[ i ] tyPi l l (tyDVec l n F) (tyPi lzero l (tyFin n⟨↑⟩) F⟨rlift ↑⟩)
          ≅ tyPi l l (tyDVec l n F⟨rlift (rshift 1)⟩[lsingle (app (lam lzero lzero (tyFin n⟨rshift 1⟩) (var 0)) lzero lzero (tyFin n⟨rshift 1⟩) (tyFin n⟨rshift 2⟩) (var 0))]) (tyPi lzero l (tyFin n⟨↑⟩) F⟨rlift (rshift 2)⟩[lsingle (app (lam lzero lzero (tyFin n⟨rshift 2⟩) (var 0)) lzero lzero (tyFin n⟨rshift 2⟩) (tyFin n⟨rshift 3⟩) (var 0))]) @ lmax l l ]).
      { apply eqty_pi; [exact Hv | exact (lequiv_refl _ _ Hl) | exact (lequiv_refl _ _ Hl) | exact HDV | |].
        - apply eqty_dvec; [exact Hc | exact (lequiv_refl _ _ Hl) | exact Hn | exact (eqtm_refl _ _ _ _ _ _ Hn) | exact HF | exact E1].
        - eapply eqty_lconv; [| apply lequiv_sym, lq_0l, Hl].
          apply eqty_pi; [exact Hv | exact (lequiv_refl (gL G) lzero I) | exact (lequiv_refl _ _ Hl) | exact HFn1 | exact (eqty_refl _ _ _ _ _ HFn1) | exact E2]. }
      refine (eqty_rw eq_refl _ (eqty_lconv _ _ _ _ _ _ _ EPi (lequiv_sym _ _ _ (lq_ll Hl)))). meq.
  - meq.
Qed.

End Schema.

End DNth.
