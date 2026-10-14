(** * Typing of [dnth] at every layer but V (M17_DESIGN.md, M17c)

    [DNth]'s [dnth_wf] holds at D and M; this is its port to every layer
    but V, as [StaticCode]'s [nth_wf_g] ports [nth_wf] (M15b): contexts at
    [typeof i], and every conversion the derivation crosses ([Fin]'s and
    [DVec]'s computation at a successor, Unit-η and β at the embeddings)
    an equation at [typeof i], taken from [DNth]'s lemmas there. The type
    checker's [elim_IWf] at layer C and the recursor's [elim_IWf] branch
    build their step telescopes from it. *)
From DeLaM.Typing Require Export DNth.

Section DNthG.
Context {G : gctx} {i : layer} (Hv : i <> lV).

Let Ct : compt (typeof i) := compt_typeof i.
Let Hty : typeof (typeof i) = typeof i := typeof_idem i.
Let Hv' : typeof i <> lV := compt_notV _ Ct.
Let up {Γ T l} (H : [ G ; Γ ⊢[ i ] T @ l ]) : [ G ; Γ ⊢[ typeof i ] T @ l ] :=
  lift_ty H (lle_self_typeof i).
Let upt {Γ t T l} (H : [ G ; Γ ⊢[ i ] t : T @ l ]) : [ G ; Γ ⊢[ typeof i ] t : T @ l ] :=
  lift_tm H (lle_self_typeof i).

Lemma dg_ext {Δ A l} : [ G ; Δ ⊢[ typeof i ] ] -> [ G ; Δ ⊢[ i ] A @ l ] -> lwf (gL G) l ->
  [ G ; Δ ,, A @ l ⊢[ typeof i ] ].
Proof using . intros H HA Hl. exact (wfc_ext _ _ _ _ _ H (up HA) Hl). Qed.

Lemma dg_wk_ty {Δ Γ r T k} : wkr r Δ Γ -> [ G ; Δ ⊢[ typeof i ] ] -> [ G ; Γ ⊢[ i ] T @ k ] ->
  [ G ; Δ ⊢[ i ] T⟨r⟩ @ k ].
Proof using . intros Hr HΔ HT. exact (proj1 (proj2 (proj2 weakening_all)) _ _ _ _ _ HT _ _ Hr HΔ). Qed.
Lemma dg_wk_tm {Δ Γ r t T k} : wkr r Δ Γ -> [ G ; Δ ⊢[ typeof i ] ] -> [ G ; Γ ⊢[ i ] t : T @ k ] ->
  [ G ; Δ ⊢[ i ] t⟨r⟩ : T⟨r⟩ @ k ].
Proof using . intros Hr HΔ Ht. exact (proj1 (proj2 (proj2 (proj2 weakening_all))) _ _ _ _ _ _ Ht _ _ Hr HΔ). Qed.

Ltac gvar := eapply wf_tm_retype; [eapply wf_var; [eassumption | repeat constructor] |
  first [reflexivity | (unfold dnthMot, dnthEmb, dnthFam, dnthRes, dnthFamS; push_ren; rlk_simpl; nshift; reflexivity) | idtac]].
Ltac gwk H := first [ exact H | eapply wk1_ty_g; [eassumption | gwk H] | eapply wk1_tm_g; [eassumption | gwk H] ].

(** [Fin (succ k)] against [Unit + Fin k], along [Fin]'s computation at [typeof i]. *)
Lemma fin_of_sum_g {Δ t K} : [ G ; Δ ⊢[ i ] K : tyNat @ lzero ] ->
  [ G ; Δ ⊢[ i ] t : tySum lzero lzero (tyUnit lzero) (tyFin K) @ lmax lzero lzero ] ->
  [ G ; Δ ⊢[ i ] t : tyFin (succ K) @ lzero ].
Proof using .
  intros HK Ht. eapply wf_conv; [eapply wf_lconv; [exact Ht | exact lq_00] |].
  exact (eqty_fin_succ _ _ _ _ Ct (upt HK)).
Qed.

Lemma sum_of_fin_g {Δ t K} : [ G ; Δ ⊢[ i ] K : tyNat @ lzero ] -> [ G ; Δ ⊢[ i ] t : tyFin (succ K) @ lzero ] ->
  [ G ; Δ ⊢[ i ] t : tySum lzero lzero (tyUnit lzero) (tyFin K) @ lmax lzero lzero ].
Proof using .
  intros HK Ht. eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]. eapply wf_conv; [exact Ht |].
  apply eqty_sym. exact (eqty_fin_succ _ _ _ _ Ct (upt HK)).
Qed.

(** The two injections into [Fin (succ K)]. *)
Lemma fin_inl_g {Δ K} : [ G ; Δ ⊢[ typeof i ] ] -> [ G ; Δ ⊢[ i ] K : tyNat @ lzero ] ->
  [ G ; Δ ⊢[ i ] tmInl lzero lzero (tyUnit lzero) (tyFin K) (tmTriv lzero) : tyFin (succ K) @ lzero ].
Proof using Hv.
  intros HΔ HK. apply fin_of_sum_g; [exact HK|].
  apply wf_inl; [exact Hv | exact I | exact I | apply wft_unit; [exact Hv | exact HΔ | exact I]
    | apply wft_fin; [exact Hv | exact HK] | apply wf_triv; [exact Hv | exact HΔ | exact I]].
Qed.

(** [DVec]'s successor reduct's components, typed at [i]. *)
Lemma dvec_succ_g {Δ K F' l} : lwf (gL G) l -> [ G ; Δ ⊢[ typeof i ] ] -> [ G ; Δ ⊢[ i ] K : tyNat @ lzero ] ->
  [ G ; Δ ,, tyFin (succ K) @ lzero ⊢[ i ] F' @ l ] ->
  [ G ; Δ ⊢[ i ] dvecHd K F' @ l ] /\ [ G ; Δ ,, dvecHd K F' @ l ⊢[ i ] dvecTl l K F' @ l ].
Proof using Hv.
  intros Hl HΔ HK HF.
  assert (HA : [ G ; Δ ⊢[ i ] dvecHd K F' @ l ])
    by exact (wf_ty_subst_g HF (lsub_wf_single_g G i _ _ _ _ HΔ (fin_inl_g HΔ HK))).
  split; [exact HA |].
  pose proof (dg_ext HΔ HA Hl) as H1.
  assert (HK1 : [ G ; Δ ,, dvecHd K F' @ l ⊢[ i ] K⟨↑⟩ : tyNat @ lzero ])
    by (eapply wf_tm_retype; [exact (wk1_tm_g G i _ _ _ _ _ _ H1 HK) | reflexivity]).
  assert (HF1 : [ G ; Δ ,, dvecHd K F' @ l ⊢[ i ] tyFin K⟨↑⟩ @ lzero ]) by (apply wft_fin; [exact Hv | exact HK1]).
  pose proof (dg_ext H1 HF1 I) as H2.
  assert (HK2 : [ G ; Δ ,, dvecHd K F' @ l ,, tyFin K⟨↑⟩ @ lzero ⊢[ i ] K⟨↑⟩⟨↑⟩ : tyNat @ lzero ])
    by (eapply wf_tm_retype; [exact (wk1_tm_g G i _ _ _ _ _ _ H2 HK1) | reflexivity]).
  assert (HSK : [ G ; Δ ⊢[ i ] tyFin (succ K) @ lzero ]) by (apply wft_fin; [exact Hv | apply wf_succ; [exact Hv | exact HK]]).
  assert (HSK1 : [ G ; Δ ,, dvecHd K F' @ l ⊢[ i ] (tyFin (succ K))⟨↑⟩ @ lzero ]) by gwk HSK.
  assert (HSK2 : [ G ; Δ ,, dvecHd K F' @ l ,, tyFin K⟨↑⟩ @ lzero ⊢[ i ] (tyFin (succ K))⟨↑⟩⟨↑⟩ @ lzero ]) by gwk HSK.
  pose proof (dg_ext H1 HSK1 I) as H1'.
  pose proof (dg_ext H2 HSK2 I) as H2'.
  assert (HF1' : [ G ; Δ ,, dvecHd K F' @ l ,, (tyFin (succ K))⟨↑⟩ @ lzero ⊢[ i ] F'⟨rlift ↑⟩ @ l ])
    by exact (dg_wk_ty (wkr_up _ _ _ _ _ (wkr_shift1 _ _ _)) H1' HF).
  assert (HF2' : [ G ; Δ ,, dvecHd K F' @ l ,, tyFin K⟨↑⟩ @ lzero ,, (tyFin (succ K))⟨↑⟩⟨↑⟩ @ lzero ⊢[ i ]
                   F'⟨rlift ↑⟩⟨rlift ↑⟩ @ l ])
    by exact (dg_wk_ty (wkr_up _ _ _ _ _ (wkr_shift1 _ _ _)) H2' HF1').
  assert (Hinr : [ G ; Δ ,, dvecHd K F' @ l ,, tyFin K⟨↑⟩ @ lzero ⊢[ i ]
                   tmInr lzero lzero (tyUnit lzero) (tyFin K⟨↑⟩⟨↑⟩) (var 0) : tyFin (succ K⟨↑⟩⟨↑⟩) @ lzero ]).
  { apply fin_of_sum_g; [exact HK2 |].
    apply wf_inr; [exact Hv | exact I | exact I | apply wft_unit; [exact Hv | exact H2 | exact I]
      | apply wft_fin; [exact Hv | exact HK2] | gvar]. }
  apply wft_dvec; [exact Hv | exact Hl | exact HK1 |].
  exact (wf_ty_subst_g HF2' (lsub_wf_single_g G i _ _ _ _ H2 Hinr)).
Qed.

Section Schema.
Context {Γ : ctx} {n : tm} {F : ty} {l : lvl} (Hl : lwf (gL G) l)
  (Hn : [ G ; Γ ⊢[ i ] n : tyNat @ lzero ]) (HF : [ G ; Γ ,, tyFin n @ lzero ⊢[ i ] F @ l ]).

Let HΓ : [ G ; Γ ⊢[ typeof i ] ] := proj1 (proj2 (proj2 (proj2 ctx_extract))) _ _ _ _ _ _ Hn.
Let Nn : nftm n := wf_tm_nf Hn.
Let NF : nfty F := wf_ty_nf HF.

Lemma n_wk_g {Δ r} : wkr r Δ Γ -> [ G ; Δ ⊢[ typeof i ] ] -> [ G ; Δ ⊢[ i ] n⟨r⟩ : tyNat @ lzero ].
Proof using Hn. intros Hr HΔ. exact (dg_wk_tm Hr HΔ Hn). Qed.

Lemma fam_wf_g {Δ r t} : wkr r Δ Γ -> [ G ; Δ ⊢[ typeof i ] ] -> [ G ; Δ ⊢[ i ] t : tyFin n⟨r⟩ @ lzero ] ->
  [ G ; Δ ⊢[ i ] F⟨rlift r⟩[lsingle t] @ l ].
Proof using Hv Hn HF.
  intros Hr HΔ Ht.
  assert (HFn : [ G ; Δ ⊢[ i ] tyFin n⟨r⟩ @ lzero ]) by (apply wft_fin; [exact Hv | exact (n_wk_g Hr HΔ)]).
  pose proof (dg_wk_ty (wkr_up _ _ _ (tyFin n) lzero Hr) (dg_ext HΔ HFn I) HF) as HF1.
  exact (wf_ty_subst_g HF1 (lsub_wf_single_g G i _ _ _ _ HΔ Ht)).
Qed.

Lemma emb_app_wf_g {Δ m ev K t} : wkr (rshift m) Δ Γ -> [ G ; Δ ⊢[ typeof i ] ] ->
  [ G ; Δ ⊢[ i ] K : tyNat @ lzero ] ->
  [ G ; Δ ⊢[ i ] ev : tyPi lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) @ lmax lzero lzero ] ->
  [ G ; Δ ⊢[ i ] t : tyFin K @ lzero ] ->
  [ G ; Δ ⊢[ i ] app ev lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) t : tyFin n⟨rshift m⟩ @ lzero ].
Proof using Hv Hn.
  intros Hr HΔ HK He Ht.
  assert (HFK : [ G ; Δ ⊢[ i ] tyFin K @ lzero ]) by (apply wft_fin; [exact Hv | exact HK]).
  pose proof (dg_ext HΔ HFK I) as HΔK.
  eapply wf_tm_retype; [apply wf_app; [exact Hv | exact I | exact I | exact HFK | | exact He | exact Ht] |].
  - apply wft_fin; [exact Hv|]. apply (n_wk_g (wkr_shiftS m Hr) HΔK).
  - change ((tyFin n⟨rshift (S m)⟩)[lsingle t]) with (tyFin (n⟨rshift (S m)⟩[lsingle t])).
    now rewrite shiftS_single.
Qed.

Lemma dnth_emb_wf_g {Δ m K} : wkr (rshift m) Δ Γ -> [ G ; Δ ⊢[ typeof i ] ] -> [ G ; Δ ⊢[ i ] K : tyNat @ lzero ] ->
  [ G ; Δ ⊢[ i ] tyPi lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) @ lzero ].
Proof using Hv Hn.
  intros Hr HΔ HK.
  assert (HFK : [ G ; Δ ⊢[ i ] tyFin K @ lzero ]) by (apply wft_fin; [exact Hv | exact HK]).
  pose proof (dg_ext HΔ HFK I) as HΔK.
  eapply wft_lconv; [| exact lq_00]. apply wft_pi; [exact Hv | exact I | exact I | exact HFK |].
  apply wft_fin; [exact Hv|]. apply (n_wk_g (wkr_shiftS m Hr) HΔK).
Qed.

(** The family at an embedding's instance, typed through [fam_wf_g]. *)
Ltac fam_at m wk := nshift; apply (fam_wf_g (r := rshift m)); [wk | eassumption |];
  apply (emb_app_wf_g (m := m)); [wk | eassumption | | | ].

Lemma dnth_mot_wf_g : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] dnthMot l n F @ l ].
Proof using Hv Hl Hn HF.
  assert (H1 : [ G ; Γ ,, tyNat @ lzero ⊢[ typeof i ] ]) by (apply dg_ext; [exact HΓ | apply wft_nat; [exact Hv | exact HΓ] | exact I]).
  assert (Hk1 : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] var 0 : tyNat @ lzero ]) by gvar.
  assert (HE : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] dnthEmb n @ lzero ]).
  { unfold dnthEmb. nshift. exact (dnth_emb_wf_g (wkr_shift1 _ _ _) H1 Hk1). }
  set (Δ2 := Γ ,, tyNat @ lzero ,, dnthEmb n @ lzero).
  assert (H2 : [ G ; Δ2 ⊢[ typeof i ] ]) by (apply dg_ext; [exact H1 | exact HE | exact I]).
  assert (Hk2 : [ G ; Δ2 ⊢[ i ] var 1 : tyNat @ lzero ]) by gvar.
  assert (HF2 : [ G ; Δ2 ⊢[ i ] tyFin (var 1) @ lzero ]) by (apply wft_fin; [exact Hv | exact Hk2]).
  assert (H3 : [ G ; Δ2 ,, tyFin (var 1) @ lzero ⊢[ typeof i ] ]) by (apply dg_ext; [exact H2 | exact HF2 | exact I]).
  assert (HFam : [ G ; Δ2 ,, tyFin (var 1) @ lzero ⊢[ i ] dnthFam n F @ l ]).
  { unfold dnthFam. fam_at 3 ltac:(wkr_n); [gvar | | gvar]. eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]. gvar. }
  assert (HD : [ G ; Δ2 ⊢[ i ] tyDVec l (var 1) (dnthFam n F) @ l ])
    by (apply wft_dvec; [exact Hv | exact Hl | exact Hk2 | exact HFam]).
  assert (H3' : [ G ; Δ2 ,, tyDVec l (var 1) (dnthFam n F) @ l ⊢[ typeof i ] ]) by (apply dg_ext; [exact H2 | exact HD | exact Hl]).
  assert (HF3 : [ G ; Δ2 ,, tyDVec l (var 1) (dnthFam n F) @ l ⊢[ i ] tyFin (var 2) @ lzero ])
    by (apply wft_fin; [exact Hv | gvar]).
  assert (H4 : [ G ; Δ2 ,, tyDVec l (var 1) (dnthFam n F) @ l ,, tyFin (var 2) @ lzero ⊢[ typeof i ] ])
    by (apply dg_ext; [exact H3' | exact HF3 | exact I]).
  unfold dnthMot. eapply wft_lconv; [| apply lequiv_sym, lq_0l, Hl].
  apply wft_pi; [exact Hv | exact I | exact Hl | exact HE |].
  eapply wft_lconv; [| apply lequiv_sym, lq_ll, Hl].
  apply wft_pi; [exact Hv | exact Hl | exact Hl | exact HD |].
  eapply wft_lconv; [| apply lequiv_sym, lq_0l, Hl].
  apply wft_pi; [exact Hv | exact I | exact Hl | exact HF3 |].
  unfold dnthRes. fam_at 4 ltac:(wkr_n); [gvar | | gvar]. eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]. gvar.
Qed.

Lemma dnth_base_wf_g : [ G ; Γ ⊢[ i ] dnthBase l n F : (dnthMot l n F)[lsingle zero] @ l ].
Proof using Hv Hl Hn HF.
  rewrite (dnth_E0 l n F Nn NF). unfold dnthBase.
  assert (Hz : forall Δ, [ G ; Δ ⊢[ typeof i ] ] -> [ G ; Δ ⊢[ i ] zero : tyNat @ lzero ])
    by (intros Δ HΔ; apply wf_zero; [exact Hv | exact HΔ]).
  assert (HE0 : [ G ; Γ ⊢[ i ] tyPi lzero lzero (tyFin zero) (tyFin n⟨↑⟩) @ lzero ])
    by exact (dnth_emb_wf_g (m := 0) (wkr_id _) HΓ (Hz _ HΓ)).
  set (Γ1 := Γ ,, tyPi lzero lzero (tyFin zero) (tyFin n⟨↑⟩) @ lzero).
  assert (H1 : [ G ; Γ1 ⊢[ typeof i ] ]) by (apply dg_ext; [exact HΓ | exact HE0 | exact I]).
  assert (HF1 : [ G ; Γ1 ⊢[ i ] tyFin zero @ lzero ]) by (apply wft_fin; [exact Hv | exact (Hz _ H1)]).
  assert (H1' : [ G ; Γ1 ,, tyFin zero @ lzero ⊢[ typeof i ] ]) by (apply dg_ext; [exact H1 | exact HF1 | exact I]).
  assert (HD0 : [ G ; Γ1 ⊢[ i ] tyDVec l zero F⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin zero) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))] @ l ]).
  { apply wft_dvec; [exact Hv | exact Hl | exact (Hz _ H1) |].
    fam_at 2 ltac:(wkr_n); [exact (Hz _ H1') | | gvar]. eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]. gvar. }
  set (Γ2 := Γ1 ,, tyDVec l zero F⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin zero) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))] @ l).
  assert (H2 : [ G ; Γ2 ⊢[ typeof i ] ]) by (apply dg_ext; [exact H1 | exact HD0 | exact Hl]).
  assert (HF2 : [ G ; Γ2 ⊢[ i ] tyFin zero @ lzero ]) by (apply wft_fin; [exact Hv | exact (Hz _ H2)]).
  assert (H3 : [ G ; Γ2 ,, tyFin zero @ lzero ⊢[ typeof i ] ]) by (apply dg_ext; [exact H2 | exact HF2 | exact I]).
  assert (EZ : forall Δ, [ G ; Δ ⊢[ typeof i ] ] -> [ G ; Δ ⊢[ typeof i ] tyFin zero ≅ tyEmpty lzero @ lzero ])
    by (intros Δ HΔ; apply eqty_fin_zero; [exact Ct | rewrite Hty; exact HΔ]).
  assert (HEm : [ G ; Γ2 ,, tyFin zero @ lzero ⊢[ i ] tyEmpty lzero @ lzero ])
    by (apply wft_empty; [exact Hv | exact H3 | exact I]).
  assert (H4 : [ G ; Γ2 ,, tyFin zero @ lzero ,, tyEmpty lzero @ lzero ⊢[ typeof i ] ]) by (apply dg_ext; [exact H3 | exact HEm | exact I]).
  eapply wf_lconv; [| apply lequiv_sym, lq_0l, Hl].
  apply wf_lam; [exact Hv | exact I | exact Hl | exact HE0 |].
  eapply wf_lconv; [| apply lequiv_sym, lq_ll, Hl].
  apply wf_lam; [exact Hv | exact Hl | exact Hl | exact HD0 |].
  eapply wf_lconv; [| apply lequiv_sym, lq_0l, Hl].
  apply wf_lam; [exact Hv | exact I | exact Hl | exact HF2 |].
  eapply wf_tm_retype; [apply wf_elimEmpty; [exact Hv | exact Hl | exact I | |] |].
  - fam_at 4 ltac:(wkr_n); [exact (Hz _ H4) | |].
    + eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]. gvar.
    + eapply wf_conv; [gvar | exact (EZ _ H4)].
  - eapply wf_conv; [gvar | apply eqty_sym, (EZ _ H3)].
  - meq.
Qed.

Lemma dnth_step_wf_g :
  [ G ; Γ ,, tyNat @ lzero ,, dnthMot l n F @ l ⊢[ i ] dnthStep l n F : (dnthMot l n F)[lsucc] @ l ].
Proof using Hv Hl Hn HF.
  rewrite (dnth_ES l n F Nn NF). unfold dnthStep.
  assert (Hsucc : forall Δ t, [ G ; Δ ⊢[ i ] t : tyNat @ lzero ] -> [ G ; Δ ⊢[ i ] succ t : tyNat @ lzero ])
    by (intros; apply wf_succ; [exact Hv | assumption]).
  assert (HN0 : [ G ; Γ ⊢[ i ] tyNat @ lzero ]) by (apply wft_nat; [exact Hv | exact HΓ]).
  assert (H0 : [ G ; Γ ,, tyNat @ lzero ⊢[ typeof i ] ]) by (apply dg_ext; [exact HΓ | exact HN0 | exact I]).
  set (Δr := Γ ,, tyNat @ lzero ,, dnthMot l n F @ l).
  assert (Hr : [ G ; Δr ⊢[ typeof i ] ]) by (apply dg_ext; [exact H0 | exact dnth_mot_wf_g | exact Hl]).
  assert (HE1 : [ G ; Δr ⊢[ i ] tyPi lzero lzero (tyFin (succ (var 1))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) @ lzero ])
    by (nshift; apply (dnth_emb_wf_g (m := 2)); [unfold Δr; wkr_n | exact Hr | apply Hsucc; gvar]).
  set (Δe := Δr ,, tyPi lzero lzero (tyFin (succ (var 1))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) @ lzero).
  assert (He : [ G ; Δe ⊢[ typeof i ] ]) by (apply dg_ext; [exact Hr | exact HE1 | exact I]).
  assert (HFe : [ G ; Δe ⊢[ i ] tyFin (succ (var 2)) @ lzero ]) by (apply wft_fin; [exact Hv | apply Hsucc; gvar]).
  assert (He' : [ G ; Δe ,, tyFin (succ (var 2)) @ lzero ⊢[ typeof i ] ]) by (apply dg_ext; [exact He | exact HFe | exact I]).
  assert (HD1 : [ G ; Δe ⊢[ i ] tyDVec l (succ (var 2)) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin (succ (var 3))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))] @ l ]).
  { apply wft_dvec; [exact Hv | exact Hl | apply Hsucc; gvar |].
    fam_at 4 ltac:(wkr_n); [apply Hsucc; gvar | | gvar]. eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]. gvar. }
  set (Δc := Δe ,, tyDVec l (succ (var 2)) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin (succ (var 3))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))] @ l).
  assert (Hcs : [ G ; Δc ⊢[ typeof i ] ]) by (apply dg_ext; [exact He | exact HD1 | exact Hl]).
  assert (HFc : [ G ; Δc ⊢[ i ] tyFin (succ (var 3)) @ lzero ]) by (apply wft_fin; [exact Hv | apply Hsucc; gvar]).
  set (Δi := Δc ,, tyFin (succ (var 3)) @ lzero).
  assert (Hii : [ G ; Δi ⊢[ typeof i ] ]) by (apply dg_ext; [exact Hcs | exact HFc | exact I]).
  eapply wf_lconv; [| apply lequiv_sym, lq_0l, Hl].
  apply wf_lam; [exact Hv | exact I | exact Hl | exact HE1 |].
  eapply wf_lconv; [| apply lequiv_sym, lq_ll, Hl].
  apply wf_lam; [exact Hv | exact Hl | exact Hl | exact HD1 |].
  eapply wf_lconv; [| apply lequiv_sym, lq_0l, Hl].
  apply wf_lam; [exact Hv | exact I | exact Hl | exact HFc |].
  assert (HU : forall Δ, [ G ; Δ ⊢[ typeof i ] ] -> [ G ; Δ ⊢[ i ] tyUnit lzero @ lzero ])
    by (intros Δ HΔ; apply wft_unit; [exact Hv | exact HΔ | exact I]).
  assert (HB : [ G ; Δi ⊢[ i ] tyFin (var 4) @ lzero ]) by (apply wft_fin; [exact Hv | gvar]).
  assert (HS : [ G ; Δi ⊢[ i ] tySum lzero lzero (tyUnit lzero) (tyFin (var 4)) @ lmax lzero lzero ])
    by (apply wft_sum; [exact Hv | exact I | exact I | exact (HU _ Hii) | exact HB]).
  assert (HiS : [ G ; Δi ,, tySum lzero lzero (tyUnit lzero) (tyFin (var 4)) @ lmax lzero lzero ⊢[ typeof i ] ])
    by (apply dg_ext; [exact Hii | exact HS | apply lwf_max; exact I]).
  eapply wf_tm_retype; [apply wf_case; [exact Hv | exact I | exact I | exact Hl | exact (HU _ Hii) | exact HB | | | | ] | meq].
  - (* the motive *) fam_at 6 ltac:(unfold Δi, Δc, Δe, Δr; wkr_n); [apply Hsucc; gvar | |].
    + eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]. gvar.
    + apply fin_of_sum_g; [gvar | gvar].
  - (* inl: the head, at the family's [inl ⟨⟩] instance (Unit-η at [typeof i]) *)
    set (Δu := Δi ,, tyUnit lzero @ lzero).
    assert (Hu : [ G ; Δu ⊢[ typeof i ] ]) by (apply dg_ext; [exact Hii | exact (HU _ Hii) | exact I]).
    assert (Hk5 : [ G ; Δu ⊢[ i ] var 5 : tyNat @ lzero ]) by gvar.
    assert (HF5 : [ G ; Δu ⊢[ i ] tyFin (var 5) @ lzero ]) by (apply wft_fin; [exact Hv | exact Hk5]).
    assert (HFS1 : [ G ; Δu ⊢[ i ] tyFin (succ (var 5)) @ lzero ]) by (apply wft_fin; [exact Hv | apply Hsucc, Hk5]).
    assert (Hu' : [ G ; Δu ,, tyFin (succ (var 5)) @ lzero ⊢[ typeof i ] ]) by (apply dg_ext; [exact Hu | exact HFS1 | exact I]).
    assert (HFS : [ G ; Δu ,, tyFin (succ (var 5)) @ lzero ⊢[ i ] dnthFamS n F @ l ]).
    { unfold dnthFamS. fam_at 7 ltac:(unfold Δu, Δi, Δc, Δe, Δr; wkr_n); [apply Hsucc; gvar | | gvar]. eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]. gvar. }
    pose proof (eqty_dvec_succ _ _ _ _ _ _ Ct Hl (upt Hk5) (up HFS)) as EQ.
    destruct (dvec_succ_g Hl Hu Hk5 HFS) as [HA HB2].
    eapply wf_conv; [apply wf_fst; [exact Hv | exact Hl | exact Hl | exact HA | exact HB2 |] |].
    + eapply wf_lconv; [| apply lq_ll, Hl]. eapply wf_conv; [| exact (eqty_sym _ _ _ _ _ _ EQ)].
      gvar. push_ren. unfold dnthFamS. meq.
    + assert (He3 : [ G ; Δu ⊢[ i ] var 3 : tyPi lzero lzero (tyFin (succ (var 5))) (tyFin n⟨rshift 7⟩) @ lmax lzero lzero ])
        by (eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]; gvar).
      assert (Hx : [ G ; Δu ⊢[ i ] tmInl lzero lzero (tyUnit lzero) (tyFin (var 5)) (var 0) : tyFin (succ (var 5)) @ lzero ])
        by (apply fin_of_sum_g; [exact Hk5 | apply wf_inl; [exact Hv | exact I | exact I | exact (HU _ Hu) | exact HF5 | gvar]]).
      pose proof (fin_inl_g Hu Hk5) as Hx'.
      assert (Ht : [ G ; Δu ⊢[ i ] tmTriv lzero : tyUnit lzero @ lzero ]) by (apply wf_triv; [exact Hv | exact Hu | exact I]).
      assert (Exx : [ G ; Δu ⊢[ typeof i ] tmInl lzero lzero (tyUnit lzero) (tyFin (var 5)) (var 0) ≅ tmInl lzero lzero (tyUnit lzero) (tyFin (var 5)) (tmTriv lzero) : tyFin (succ (var 5)) @ lzero ]).
      { apply (fin_of_sum_eq Ct (upt Hk5)). apply eqtm_inl; [exact Hv' | exact (lequiv_refl (gL G) lzero I) | exact (lequiv_refl (gL G) lzero I)
          | exact (eqty_refl _ _ _ _ _ (up (HU _ Hu))) | exact (eqty_refl _ _ _ _ _ (up HF5)) |].
        apply eqtm_unit_eta; [exact Ct | exact I | | exact (upt Ht)].
        eapply wf_tm_retype; [eapply wf_var; [rewrite Hty; exact Hu | repeat constructor] | reflexivity]. }
      assert (Hr6 : wkr (rshift 6) Δu Γ) by (unfold Δu, Δi, Δc, Δe, Δr; wkr_n).
      refine (eqty_rw _ _ (fam_eq Ct (upt Hn) (up HF) Hr6 Hu
        (emb_app_wf Ct (upt Hn) Hr6 Hu (upt (Hsucc _ _ Hk5)) (upt He3) (upt Hx))
        (emb_app_wf Ct (upt Hn) Hr6 Hu (upt (Hsucc _ _ Hk5)) (upt He3) (upt Hx'))
        (emb_app_eq Ct (upt Hn) Hr6 Hu (upt (Hsucc _ _ Hk5)) (upt He3) Exx)));
        unfold dnthFamS; meq.
  - (* inr: the recursive call at [λy. e (inr y)], the tail and the index (β at [typeof i]) *)
    set (Δj := Δi ,, tyFin (var 4) @ lzero).
    assert (Hj : [ G ; Δj ⊢[ typeof i ] ]) by (apply dg_ext; [exact Hii | exact HB | exact I]).
    assert (Hk5 : [ G ; Δj ⊢[ i ] var 5 : tyNat @ lzero ]) by gvar.
    assert (HF5 : [ G ; Δj ⊢[ i ] tyFin (var 5) @ lzero ]) by (apply wft_fin; [exact Hv | exact Hk5]).
    assert (Hj5 : [ G ; Δj ,, tyFin (var 5) @ lzero ⊢[ typeof i ] ]) by (apply dg_ext; [exact Hj | exact HF5 | exact I]).
    assert (Hk6 : [ G ; Δj ,, tyFin (var 5) @ lzero ⊢[ i ] var 6 : tyNat @ lzero ]) by gvar.
    assert (HF6 : [ G ; Δj ,, tyFin (var 5) @ lzero ⊢[ i ] tyFin (var 6) @ lzero ]) by (apply wft_fin; [exact Hv | exact Hk6]).
    assert (Hj56 : [ G ; Δj ,, tyFin (var 5) @ lzero ,, tyFin (var 6) @ lzero ⊢[ typeof i ] ]) by (apply dg_ext; [exact Hj5 | exact HF6 | exact I]).
    assert (Hr6 : wkr (rshift 6) Δj Γ) by (unfold Δj, Δi, Δc, Δe, Δr; wkr_n).
    assert (Hr7 : wkr (rshift 7) (Δj ,, tyFin (var 5) @ lzero) Γ) by (unfold Δj, Δi, Δc, Δe, Δr; wkr_n).
    assert (Hr8 : wkr (rshift 8) (Δj ,, tyFin (var 5) @ lzero ,, tyFin (var 6) @ lzero) Γ) by (unfold Δj, Δi, Δc, Δe, Δr; wkr_n).
    assert (HbE : [ G ; Δj ,, tyFin (var 5) @ lzero ⊢[ i ] app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨rshift 8⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)) : tyFin n⟨rshift 7⟩ @ lzero ]).
    { apply (emb_app_wf_g Hr7 Hj5 (Hsucc _ _ Hk6)); [eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]; gvar |].
      apply fin_of_sum_g; [exact Hk6 | apply wf_inr; [exact Hv | exact I | exact I | exact (HU _ Hj5) | exact HF6 | gvar]]. }
    set (Fr := F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))]).
    assert (HFres : [ G ; Δj ,, tyFin (var 5) @ lzero ⊢[ i ] Fr @ l ])
      by (unfold Fr; nshift; exact (fam_wf_g Hr7 Hj5 HbE)).
    assert (HDV : [ G ; Δj ⊢[ i ] tyDVec l (var 5) Fr @ l ]) by (apply wft_dvec; [exact Hv | exact Hl | exact Hk5 | exact HFres]).
    set (ΔD := Δj ,, tyDVec l (var 5) Fr @ l).
    assert (HjD : [ G ; ΔD ⊢[ typeof i ] ]) by (apply dg_ext; [exact Hj | exact HDV | exact Hl]).
    assert (Hk6' : [ G ; ΔD ⊢[ i ] var 6 : tyNat @ lzero ]) by gvar.
    assert (HF6' : [ G ; ΔD ⊢[ i ] tyFin (var 6) @ lzero ]) by (apply wft_fin; [exact Hv | exact Hk6']).
    assert (HjD6 : [ G ; ΔD ,, tyFin (var 6) @ lzero ⊢[ typeof i ] ]) by (apply dg_ext; [exact HjD | exact HF6' | exact I]).
    assert (Hk7 : [ G ; ΔD ,, tyFin (var 6) @ lzero ⊢[ i ] var 7 : tyNat @ lzero ]) by gvar.
    assert (Hr8' : wkr (rshift 8) (ΔD ,, tyFin (var 6) @ lzero) Γ) by (unfold ΔD, Δj, Δi, Δc, Δe, Δr; wkr_n).
    assert (HbE' : [ G ; ΔD ,, tyFin (var 6) @ lzero ⊢[ i ] app (var 5) lzero lzero (tyFin (succ (var 7))) (tyFin n⟨rshift 9⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 7)) (var 0)) : tyFin n⟨rshift 8⟩ @ lzero ]).
    { apply (emb_app_wf_g Hr8' HjD6 (Hsucc _ _ Hk7)); [eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]; gvar |].
      apply fin_of_sum_g; [exact Hk7 | apply wf_inr; [exact Hv | exact I | exact I | exact (HU _ HjD6) | apply wft_fin; [exact Hv | exact Hk7] | gvar]]. }
    assert (HPi : [ G ; ΔD ⊢[ i ] tyPi lzero l (tyFin (var 6)) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 5) lzero lzero (tyFin (succ (var 7))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 7)) (var 0)))] @ l ]).
    { eapply wft_lconv; [| apply lequiv_sym, lq_0l, Hl]. apply wft_pi; [exact Hv | exact I | exact Hl | exact HF6' |].
      nshift. exact (fam_wf_g Hr8' HjD6 HbE'). }
    eapply wf_tm_retype; [eapply wf_app; [exact Hv | exact I | exact Hl | exact HF5 | exact HFres | | gvar] | unfold Fr; meq].
    eapply wf_lconv; [| apply lq_0l, Hl].
    eapply wf_tm_retype; [eapply wf_app; [exact Hv | exact Hl | exact Hl | exact HDV | exact HPi | | ] | unfold Fr; meq].
    + (* the recursive call at the shifted embedding *)
      assert (HM5 : [ G ; Δj ⊢[ i ] tyPi lzero l (dnthEmb n)⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩
          (tyPi l l (tyDVec l (var 1) (dnthFam n F)) (tyPi lzero l (tyFin (var 2)) (dnthRes n F)))⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ @ l ]).
      { assert (HM5' : [ G ; Δj ⊢[ i ] (dnthMot l n F)⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ @ l ])
          by (pose proof dnth_mot_wf_g as HM; gwk HM).
        exact HM5'. }
      assert (Hr4 : [ G ; Δj ⊢[ i ] var 4 : tyPi lzero l (dnthEmb n)⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩
          (tyPi l l (tyDVec l (var 1) (dnthFam n F)) (tyPi lzero l (tyFin (var 2)) (dnthRes n F)))⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ @ l ])
        by gvar.
      destruct (inv_ty_pi HM5) as ((_ & _ & _ & HEm & HRest) & _).
      eapply wf_lconv; [| apply lq_ll, Hl].
      eapply wf_conv; [eapply wf_app; [exact Hv | exact I | exact Hl | exact HEm | exact HRest | eapply wf_lconv; [exact Hr4 | apply lq_0l, Hl] |] |].
      * eapply wf_tm_retype; [eapply wf_lconv; [apply wf_lam; [exact Hv | exact I | exact I | exact HF5 | nshift; exact HbE] | exact lq_00] |].
        unfold dnthEmb; push_ren; rlk_simpl; nshift; reflexivity.
      * assert (EF : [ G ; Δj ,, tyFin (var 5) @ lzero ⊢[ typeof i ] Fr ≅ F⟨rlift (rshift 7)⟩[lsingle (app (lam lzero lzero (tyFin (var 6)) (app (var 5) lzero lzero (tyFin (succ (var 7))) (tyFin n⟨rshift 9⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 7)) (var 0)))) lzero lzero (tyFin (var 6)) (tyFin n⟨rshift 8⟩) (var 0))] @ l ]).
        { assert (Hk7a : [ G ; Δj ,, tyFin (var 5) @ lzero ,, tyFin (var 6) @ lzero ⊢[ i ] var 7 : tyNat @ lzero ]) by gvar.
          assert (Hb : [ G ; Δj ,, tyFin (var 5) @ lzero ,, tyFin (var 6) @ lzero ⊢[ i ] app (var 5) lzero lzero (tyFin (succ (var 7))) (tyFin n⟨rshift 9⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 7)) (var 0)) : tyFin n⟨rshift 8⟩ @ lzero ]).
          { apply (emb_app_wf_g Hr8 Hj56 (Hsucc _ _ Hk7a)); [eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]; gvar |].
            apply fin_of_sum_g; [gvar | apply wf_inr; [exact Hv | exact I | exact I | exact (HU _ Hj56) | apply wft_fin; [exact Hv | gvar] | gvar]]. }
          assert (H0' : [ G ; Δj ,, tyFin (var 5) @ lzero ⊢[ i ] var 0 : tyFin (var 6) @ lzero ]) by gvar.
          apply eqty_sym. refine (eqty_rw eq_refl _ (fam_beta Ct (upt Hn) (up HF) Hr7 Hj5 (upt Hk6) (upt Hb) (upt H0'))).
          unfold Fr; meq. }
        assert (HF7 : [ G ; ΔD ,, tyFin (var 6) @ lzero ⊢[ i ] tyFin (var 7) @ lzero ]) by (apply wft_fin; [exact Hv | exact Hk7]).
        assert (Hj7 : [ G ; ΔD ,, tyFin (var 6) @ lzero ,, tyFin (var 7) @ lzero ⊢[ typeof i ] ]) by (apply dg_ext; [exact HjD6 | exact HF7 | exact I]).
        assert (Hk8 : [ G ; ΔD ,, tyFin (var 6) @ lzero ,, tyFin (var 7) @ lzero ⊢[ i ] var 8 : tyNat @ lzero ]) by gvar.
        assert (Hr9 : wkr (rshift 9) (ΔD ,, tyFin (var 6) @ lzero ,, tyFin (var 7) @ lzero) Γ) by (unfold ΔD, Δj, Δi, Δc, Δe, Δr; wkr_n).
        assert (EF8 : [ G ; ΔD ,, tyFin (var 6) @ lzero ⊢[ typeof i ] F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 5) lzero lzero (tyFin (succ (var 7))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 7)) (var 0)))] ≅ F⟨rlift (rshift 8)⟩[lsingle (app (lam lzero lzero (tyFin (var 7)) (app (var 6) lzero lzero (tyFin (succ (var 8))) (tyFin n⟨rshift 10⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 8)) (var 0)))) lzero lzero (tyFin (var 7)) (tyFin n⟨rshift 9⟩) (var 0))] @ l ]).
        { assert (Hb : [ G ; ΔD ,, tyFin (var 6) @ lzero ,, tyFin (var 7) @ lzero ⊢[ i ] app (var 6) lzero lzero (tyFin (succ (var 8))) (tyFin n⟨rshift 10⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 8)) (var 0)) : tyFin n⟨rshift 9⟩ @ lzero ]).
          { apply (emb_app_wf_g Hr9 Hj7 (Hsucc _ _ Hk8)); [eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]; gvar |].
            apply fin_of_sum_g; [exact Hk8 | apply wf_inr; [exact Hv | exact I | exact I | exact (HU _ Hj7) | apply wft_fin; [exact Hv | exact Hk8] | gvar]]. }
          assert (H0' : [ G ; ΔD ,, tyFin (var 6) @ lzero ⊢[ i ] var 0 : tyFin (var 7) @ lzero ]) by gvar.
          apply eqty_sym. refine (eqty_rw eq_refl _ (fam_beta Ct (upt Hn) (up HF) Hr8' HjD6 (upt Hk7) (upt Hb) (upt H0'))).
          meq. }
        assert (EPi : [ G ; Δj ⊢[ typeof i ] tyPi l l (tyDVec l (var 5) Fr) (tyPi lzero l (tyFin (var 6)) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 5) lzero lzero (tyFin (succ (var 7))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 7)) (var 0)))]) ≅ tyPi l l (tyDVec l (var 5) F⟨rlift (rshift 7)⟩[lsingle (app (lam lzero lzero (tyFin (var 6)) (app (var 5) lzero lzero (tyFin (succ (var 7))) (tyFin n⟨rshift 9⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 7)) (var 0)))) lzero lzero (tyFin (var 6)) (tyFin n⟨rshift 8⟩) (var 0))]) (tyPi lzero l (tyFin (var 6)) F⟨rlift (rshift 8)⟩[lsingle (app (lam lzero lzero (tyFin (var 7)) (app (var 6) lzero lzero (tyFin (succ (var 8))) (tyFin n⟨rshift 10⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 8)) (var 0)))) lzero lzero (tyFin (var 7)) (tyFin n⟨rshift 9⟩) (var 0))]) @ lmax l l ]).
        { apply eqty_pi; [exact Hv' | exact (lequiv_refl _ _ Hl) | exact (lequiv_refl _ _ Hl) | exact (up HDV) | |].
          - apply eqty_dvec; [exact Hv' | exact (lequiv_refl _ _ Hl) | exact (upt Hk5) | exact (eqtm_refl _ _ _ _ _ _ (upt Hk5)) | exact (up HFres) | exact EF].
          - eapply eqty_lconv; [| apply lequiv_sym, lq_0l, Hl].
            apply eqty_pi; [exact Hv' | exact (lequiv_refl (gL G) lzero I) | exact (lequiv_refl _ _ Hl) | exact (up HF6') | exact (eqty_refl _ _ _ _ _ (up HF6')) | exact EF8]. }
        refine (eqty_rw eq_refl _ (eqty_lconv _ _ _ _ _ _ _ EPi (lequiv_sym _ _ _ (lq_ll Hl)))).
        unfold dnthFam, dnthRes. push_ren. push_subst. meq.
    + (* the tail *)
      assert (HFS1 : [ G ; Δj ⊢[ i ] tyFin (succ (var 5)) @ lzero ]) by (apply wft_fin; [exact Hv | apply Hsucc, Hk5]).
      assert (Hj' : [ G ; Δj ,, tyFin (succ (var 5)) @ lzero ⊢[ typeof i ] ]) by (apply dg_ext; [exact Hj | exact HFS1 | exact I]).
      assert (HFS : [ G ; Δj ,, tyFin (succ (var 5)) @ lzero ⊢[ i ] dnthFamS n F @ l ]).
      { unfold dnthFamS. fam_at 7 ltac:(unfold Δj, Δi, Δc, Δe, Δr; wkr_n); [apply Hsucc; gvar | | gvar]. eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]. gvar. }
      pose proof (eqty_dvec_succ _ _ _ _ _ _ Ct Hl (upt Hk5) (up HFS)) as EQ.
      destruct (dvec_succ_g Hl Hj Hk5 HFS) as [HA HB2].
      eapply wf_tm_retype; [apply wf_snd; [exact Hv | exact Hl | exact Hl | exact HA | exact HB2 |] | unfold Fr, dnthFamS; push_subst; meq].
      eapply wf_lconv; [| apply lq_ll, Hl]. eapply wf_conv; [| exact (eqty_sym _ _ _ _ _ _ EQ)].
      gvar. push_ren. unfold dnthFamS. meq.
  - (* the scrutinee *) apply sum_of_fin_g; [gvar | gvar].
Qed.

(** [dnth]'s typing at every layer but V. *)
Lemma dnth_wf_g {cs t} : [ G ; Γ ⊢[ i ] cs : tyDVec l n F @ l ] -> [ G ; Γ ⊢[ i ] t : tyFin n @ lzero ] ->
  [ G ; Γ ⊢[ i ] tmDNth l n F cs t : F[lsingle t] @ l ].
Proof using Hv Hl Hn HF.
  intros Hcs Ht. unfold tmDNth.
  assert (HFn : [ G ; Γ ⊢[ i ] tyFin n @ lzero ]) by (apply wft_fin; [exact Hv | exact Hn]).
  assert (HΓn : [ G ; Γ ,, tyFin n @ lzero ⊢[ typeof i ] ]) by (apply dg_ext; [exact HΓ | exact HFn | exact I]).
  assert (HDV : [ G ; Γ ⊢[ i ] tyDVec l n F @ l ]) by (apply wft_dvec; [exact Hv | exact Hl | exact Hn | exact HF]).
  assert (HΓD : [ G ; Γ ,, tyDVec l n F @ l ⊢[ typeof i ] ]) by (apply dg_ext; [exact HΓ | exact HDV | exact Hl]).
  assert (HFn1 : [ G ; Γ ,, tyDVec l n F @ l ⊢[ i ] tyFin n⟨↑⟩ @ lzero ])
    by (apply wft_fin; [exact Hv | exact (n_wk_g (wkr_shift1 _ _ _) HΓD)]).
  assert (HΓD1 : [ G ; Γ ,, tyDVec l n F @ l ,, tyFin n⟨↑⟩ @ lzero ⊢[ typeof i ] ]) by (apply dg_ext; [exact HΓD | exact HFn1 | exact I]).
  apply wf_app; [exact Hv | exact I | exact Hl | exact HFn | exact HF | | exact Ht].
  eapply wf_lconv; [| apply lq_0l, Hl].
  eapply wf_tm_retype; [eapply wf_app; [exact Hv | exact Hl | exact Hl | exact HDV | | | exact Hcs] |].
  - eapply wft_lconv; [| apply lequiv_sym, lq_0l, Hl]. apply wft_pi; [exact Hv | exact I | exact Hl | exact HFn1 |].
    exact (dg_wk_ty (wkr_up _ _ _ (tyFin n) lzero (wkr_shift1 _ _ _)) HΓD1 HF).
  - assert (HN : [ G ; Γ ⊢[ i ] natrec l (dnthMot l n F) (dnthBase l n F) (dnthStep l n F) n : tyPi lzero l (tyPi lzero lzero (tyFin n) (tyFin n⟨↑⟩)) (tyPi l l (tyDVec l n⟨↑⟩ F⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin n⟨↑⟩⟨↑⟩) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))]) (tyPi lzero l (tyFin n⟨↑⟩⟨↑⟩) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 2) lzero lzero (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))])) @ l ]).
    { eapply wf_tm_retype; [apply wf_natrec; [exact Hv | exact Hl | exact dnth_mot_wf_g | exact dnth_base_wf_g | exact dnth_step_wf_g | exact Hn] |].
      unfold dnthMot, dnthEmb, dnthFam, dnthRes. meq. }
    assert (HNT : [ G ; Γ ⊢[ i ] tyPi lzero l (tyPi lzero lzero (tyFin n) (tyFin n⟨↑⟩)) (tyPi l l (tyDVec l n⟨↑⟩ F⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin n⟨↑⟩⟨↑⟩) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))]) (tyPi lzero l (tyFin n⟨↑⟩⟨↑⟩) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 2) lzero lzero (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))])) @ l ]).
    { pose proof (wf_ty_subst_g dnth_mot_wf_g (lsub_wf_single_g G i _ _ _ _ HΓ Hn)) as X.
      revert X. unfold dnthMot, dnthEmb, dnthFam, dnthRes. intros X. refine (eq_rect _ (fun T => [ G ; Γ ⊢[ i ] T @ l ]) X _ _). meq. }
    destruct (inv_ty_pi HNT) as ((_ & _ & _ & HEm & HRest) & _).
    eapply wf_lconv; [| apply lq_ll, Hl].
    eapply wf_conv; [eapply wf_app; [exact Hv | exact I | exact Hl | exact HEm | exact HRest | eapply wf_lconv; [exact HN | apply lq_0l, Hl] |] |].
    + eapply wf_lconv; [| exact lq_00]. apply wf_lam; [exact Hv | exact I | exact I | exact HFn | gvar].
    + assert (Hr1 : wkr (rshift 1) (Γ ,, tyFin n @ lzero) Γ) by wkr_n.
      assert (Hr2 : wkr (rshift 2) (Γ ,, tyDVec l n F @ l ,, tyFin n⟨↑⟩ @ lzero) Γ) by wkr_n.
      assert (Hn1 : [ G ; Γ ,, tyFin n @ lzero ⊢[ i ] n⟨rshift 1⟩ : tyNat @ lzero ]) by exact (n_wk_g Hr1 HΓn).
      assert (Hn2 : [ G ; Γ ,, tyDVec l n F @ l ,, tyFin n⟨↑⟩ @ lzero ⊢[ i ] n⟨rshift 2⟩ : tyNat @ lzero ]) by exact (n_wk_g Hr2 HΓD1).
      assert (E1 : [ G ; Γ ,, tyFin n @ lzero ⊢[ typeof i ] F ≅ F⟨rlift (rshift 1)⟩[lsingle (app (lam lzero lzero (tyFin n⟨rshift 1⟩) (var 0)) lzero lzero (tyFin n⟨rshift 1⟩) (tyFin n⟨rshift 2⟩) (var 0))] @ l ]).
      { assert (HX : [ G ; Γ ,, tyFin n @ lzero ,, tyFin n⟨rshift 1⟩ @ lzero ⊢[ typeof i ] ])
          by (apply dg_ext; [exact HΓn | apply wft_fin; [exact Hv | exact Hn1] | exact I]).
        assert (Hb : [ G ; Γ ,, tyFin n @ lzero ,, tyFin n⟨rshift 1⟩ @ lzero ⊢[ i ] var 0 : tyFin n⟨rshift 2⟩ @ lzero ]) by gvar.
        assert (Hs : [ G ; Γ ,, tyFin n @ lzero ⊢[ i ] var 0 : tyFin n⟨rshift 1⟩ @ lzero ]) by gvar.
        apply eqty_sym. refine (eqty_rw eq_refl _ (fam_beta Ct (upt Hn) (up HF) Hr1 HΓn (upt Hn1) (upt Hb) (upt Hs))).
        meq. }
      assert (E2 : [ G ; Γ ,, tyDVec l n F @ l ,, tyFin n⟨↑⟩ @ lzero ⊢[ typeof i ] F⟨rlift ↑⟩ ≅ F⟨rlift (rshift 2)⟩[lsingle (app (lam lzero lzero (tyFin n⟨rshift 2⟩) (var 0)) lzero lzero (tyFin n⟨rshift 2⟩) (tyFin n⟨rshift 3⟩) (var 0))] @ l ]).
      { assert (HX : [ G ; Γ ,, tyDVec l n F @ l ,, tyFin n⟨↑⟩ @ lzero ,, tyFin n⟨rshift 2⟩ @ lzero ⊢[ typeof i ] ])
          by (apply dg_ext; [exact HΓD1 | apply wft_fin; [exact Hv | exact Hn2] | exact I]).
        assert (Hb : [ G ; Γ ,, tyDVec l n F @ l ,, tyFin n⟨↑⟩ @ lzero ,, tyFin n⟨rshift 2⟩ @ lzero ⊢[ i ] var 0 : tyFin n⟨rshift 3⟩ @ lzero ]) by gvar.
        assert (Hs : [ G ; Γ ,, tyDVec l n F @ l ,, tyFin n⟨↑⟩ @ lzero ⊢[ i ] var 0 : tyFin n⟨rshift 2⟩ @ lzero ]) by gvar.
        apply eqty_sym. refine (eqty_rw eq_refl _ (fam_beta Ct (upt Hn) (up HF) Hr2 HΓD1 (upt Hn2) (upt Hb) (upt Hs))).
        meq. }
      assert (EPi : [ G ; Γ ⊢[ typeof i ] tyPi l l (tyDVec l n F) (tyPi lzero l (tyFin n⟨↑⟩) F⟨rlift ↑⟩)
          ≅ tyPi l l (tyDVec l n F⟨rlift (rshift 1)⟩[lsingle (app (lam lzero lzero (tyFin n⟨rshift 1⟩) (var 0)) lzero lzero (tyFin n⟨rshift 1⟩) (tyFin n⟨rshift 2⟩) (var 0))]) (tyPi lzero l (tyFin n⟨↑⟩) F⟨rlift (rshift 2)⟩[lsingle (app (lam lzero lzero (tyFin n⟨rshift 2⟩) (var 0)) lzero lzero (tyFin n⟨rshift 2⟩) (tyFin n⟨rshift 3⟩) (var 0))]) @ lmax l l ]).
      { apply eqty_pi; [exact Hv' | exact (lequiv_refl _ _ Hl) | exact (lequiv_refl _ _ Hl) | exact (up HDV) | |].
        - apply eqty_dvec; [exact Hv' | exact (lequiv_refl _ _ Hl) | exact (upt Hn) | exact (eqtm_refl _ _ _ _ _ _ (upt Hn)) | exact (up HF) | exact E1].
        - eapply eqty_lconv; [| apply lequiv_sym, lq_0l, Hl].
          apply eqty_pi; [exact Hv' | exact (lequiv_refl (gL G) lzero I) | exact (lequiv_refl _ _ Hl) | exact (up HFn1) | exact (eqty_refl _ _ _ _ _ (up HFn1)) | exact E2]. }
      refine (eqty_rw eq_refl _ (eqty_lconv _ _ _ _ _ _ _ EPi (lequiv_sym _ _ _ (lq_ll Hl)))). meq.
  - meq.
Qed.

End Schema.

End DNthG.
