(** * [DVec]'s successor reduct along equal lengths and families (M17b)

    [DVec^l(S m; F)]'s head [F[inl ⟨⟩]] and tail [DVec^l(m; j. F[inr j])]
    are equal at equal lengths and families. [IWf]'s relation (M17b)
    spells out the children's spine at these reducts, and its symmetry
    and transitivity move a spine to the other side's family. The tail's
    family [dvecMv] and its syntax come first (they were [Validity/DVec]'s,
    M17a). *)
From DeLaM.Typing Require Export PresupAux.

(** ** Syntax *)

(** The tail's family, at the predecessor's index [j : Fin n]. *)
Definition dvecMv (n : tm) (F : ty) : ty :=
  F⟨rlift ↑⟩[lsingle (tmInr lzero lzero (tyUnit lzero) (tyFin n⟨↑⟩) (var 0))].

Lemma dvecTl_eq l n F : dvecTl l n F = (tyDVec l n (dvecMv n F))⟨↑⟩.
Proof.
  unfold dvecMv. change ((tyDVec l ?m ?G)⟨?r⟩) with (tyDVec l m⟨r⟩ G⟨rlift r⟩).
  rewrite lsingle_ren_ty. cbn [ren Ren_tm Ren_ty ren_tm ren_ty rlk]. fold ren_ty ren_tm.
  repeat (f_equal; try ren_comm). all: rlk_simpl; reflexivity.
Qed.

Lemma dvecMv_single m (K : ty) i : nftm m ->
  (dvecMv m K)[lsingle i] = K[lsingle (tmInr lzero lzero (tyUnit lzero) (tyFin m) i)].
Proof.
  intros Hm. unfold dvecMv.
  rewrite (subst_subst_ty _ _ _
             (lcons (lsingle i) (tmInr lzero lzero (tyUnit lzero) (tyFin m) i))).
  - apply ren_subst_ty. intros [|k]; rlk_simpl; cbn; reflexivity.
  - intros [|k]; cbn; [| now rewrite Nat.add_0_r].
    change (subst_tm ?x ?d) with x[d]. now rewrite shift_single.
Qed.

(** The head's and the tail's instances commute with substitution. *)
Lemma dvecHd_subst m (F : ty) d : LK nftm d ->
  (dvecHd m F)[d] = dvecHd m[d] F[llift d].
Proof. intros Hd. now rewrite single_subst_ty by exact Hd. Qed.

Lemma dvecMv_subst m (F : ty) d : LK nftm d -> (dvecMv m F)[llift d] = dvecMv m[d] F[llift d].
Proof.
  intros Hd. unfold dvecMv. rewrite single_subst_ty by now apply lk_llift.
  rewrite liftshift_llift_ty. f_equal. f_equal.
  change ((tmInr ?a ?b ?A ?B ?t)[?e]) with (tmInr a b A[e] B[e] t[e]).
  rewrite subst_tyUnit, subst_tyFin, shift_llift. f_equal.
  change ((var 0)[?e]) with (llk e 0). now rewrite llk_llift.
Qed.

Lemma dvecTl_subst l m (F : ty) d : LK nftm d ->
  (dvecTl l m F)[llift d] = dvecTl l m[d] F[llift d].
Proof.
  intros Hd. rewrite !dvecTl_eq, shift_llift_ty, subst_tyDVec, dvecMv_subst by exact Hd.
  reflexivity.
Qed.

(** ** Equal heads and tails *)

Section DVecEq.
Context {G : gctx} {i : layer} (Hi : typeof i = i) (Hv : i <> lV) (Hc : compt i).

(** The canonical indices of [Fin (succ m)] along equal lengths. *)
Lemma fin_inl_eq {Γ m m'} : [ G ; Γ ⊢[ i ] m : tyNat @ lzero ] -> [ G ; Γ ⊢[ i ] m ≅ m' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] tmInl lzero lzero (tyUnit lzero) (tyFin m) (tmTriv lzero)
      ≅ tmInl lzero lzero (tyUnit lzero) (tyFin m') (tmTriv lzero) : tyFin (succ m) @ lzero ].
Proof using Hi Hv Hc.
  intros Hm Hmm. pose proof (ctx_of_wf_tm Hi Hm) as HΓ.
  eapply eqtm_conv; [| rewrite Hi; apply eqty_fin_succ; assumption].
  eapply eqtm_lconv; [| apply lequiv_sym, lmax_idem; exact I].
  apply eqtm_inl; try exact Hv; try (apply lequiv_refl; exact I).
  - apply eqty_refl, wft_unit; [exact Hv | now rewrite Hi | exact I].
  - apply eqty_fin; assumption.
  - apply eqtm_refl, wf_triv; [exact Hv | now rewrite Hi | exact I].
Qed.

Lemma fin_inr_eq {Γ m m' b b'} : [ G ; Γ ⊢[ i ] m : tyNat @ lzero ] -> [ G ; Γ ⊢[ i ] m ≅ m' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] b ≅ b' : tyFin m @ lzero ] ->
  [ G ; Γ ⊢[ i ] tmInr lzero lzero (tyUnit lzero) (tyFin m) b
      ≅ tmInr lzero lzero (tyUnit lzero) (tyFin m') b' : tyFin (succ m) @ lzero ].
Proof using Hi Hv Hc.
  intros Hm Hmm Hbb. pose proof (ctx_of_wf_tm Hi Hm) as HΓ.
  eapply eqtm_conv; [| rewrite Hi; apply eqty_fin_succ; assumption].
  eapply eqtm_lconv; [| apply lequiv_sym, lmax_idem; exact I].
  apply eqtm_inr; try exact Hv; try (apply lequiv_refl; exact I); [| apply eqty_fin; assumption | exact Hbb].
  apply eqty_refl, wft_unit; [exact Hv | now rewrite Hi | exact I].
Qed.

Lemma fin_succ_conv {Γ m m'} : [ G ; Γ ⊢[ i ] m ≅ m' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] tyFin (succ m) ≅ tyFin (succ m') @ lzero ].
Proof using Hv. intros Hmm. apply eqty_fin; [exact Hv | now apply eqtm_succ]. Qed.

(** The head. *)
Lemma dvecHd_eqty {Γ l m m' F F'} :
  [ G ; Γ ⊢[ i ] m : tyNat @ lzero ] -> [ G ; Γ ⊢[ i ] m' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] m ≅ m' : tyNat @ lzero ] ->
  [ G ; Γ ,, tyFin (succ m) @ lzero ⊢[ i ] F @ l ] ->
  [ G ; Γ ,, tyFin (succ m) @ lzero ⊢[ i ] F ≅ F' @ l ] ->
  [ G ; Γ ⊢[ i ] dvecHd m F ≅ dvecHd m' F' @ l ].
Proof using Hi Hv Hc.
  intros Hm Hm' Hmm HF HFF.
  pose proof (fin_inl_wf Hi Hv Hc Hm) as H1.
  assert (H2 : [ G ; Γ ⊢[ i ] tmInl lzero lzero (tyUnit lzero) (tyFin m') (tmTriv lzero) : tyFin (succ m) @ lzero ])
    by (eapply wf_conv; [exact (fin_inl_wf Hi Hv Hc Hm') | rewrite Hi; apply fin_succ_conv; exact Hmm]).
  eapply eqty_trans.
  - exact (wf_ty_func Hi HF (lsub_eq_single Hi H1 H2 (fin_inl_eq Hm Hmm))).
  - exact (eqty_single Hi HFF H2).
Qed.

(** The tail's family. *)
Lemma dvecMv_wf {Γ l m F} : [ G ; Γ ⊢[ i ] m : tyNat @ lzero ] ->
  [ G ; Γ ,, tyFin (succ m) @ lzero ⊢[ i ] F @ l ] ->
  [ G ; Γ ,, tyFin m @ lzero ⊢[ i ] dvecMv m F @ l ].
Proof using Hi Hv Hc.
  intros Hm HF. pose proof (ctx_of_wf_tm Hi Hm) as HΓ.
  assert (HΓ1 : [ G ; Γ ,, tyFin m @ lzero ⊢[ i ] ]) by (apply (ext_wf Hi); [now apply wft_fin | exact I]).
  assert (Hm1 : [ G ; Γ ,, tyFin m @ lzero ⊢[ i ] m⟨↑⟩ : tyNat @ lzero ])
    by exact (wk1_tm G i Hi _ _ _ _ _ _ HΓ1 Hm).
  assert (HΓ2 : [ G ; Γ ,, tyFin m @ lzero ,, tyFin (succ m⟨↑⟩) @ lzero ⊢[ i ] ])
    by (apply (ext_wf Hi); [apply wft_fin; [exact Hv | now apply wf_succ] | exact I]).
  assert (HF1 : [ G ; Γ ,, tyFin m @ lzero ,, tyFin (succ m⟨↑⟩) @ lzero ⊢[ i ] F⟨rlift ↑⟩ @ l ])
    by (apply (wk_under_ty Hi (X := tyFin (succ m))); [exact HΓ2 | exact HF]).
  unfold dvecMv. eapply (wf_ty_single Hi); [exact HF1|].
  apply (fin_inr_wf Hi Hv Hc); [exact Hm1 | exact (var0_wf G i Hi _ _ _ HΓ1)].
Qed.

Lemma dvecMv_eqty {Γ l m m' F F'} :
  [ G ; Γ ⊢[ i ] m : tyNat @ lzero ] -> [ G ; Γ ⊢[ i ] m' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] m ≅ m' : tyNat @ lzero ] ->
  [ G ; Γ ,, tyFin (succ m) @ lzero ⊢[ i ] F @ l ] ->
  [ G ; Γ ,, tyFin (succ m) @ lzero ⊢[ i ] F ≅ F' @ l ] ->
  [ G ; Γ ,, tyFin m @ lzero ⊢[ i ] dvecMv m F ≅ dvecMv m' F' @ l ].
Proof using Hi Hv Hc.
  intros Hm Hm' Hmm HF HFF. pose proof (ctx_of_wf_tm Hi Hm) as HΓ.
  assert (HΓ1 : [ G ; Γ ,, tyFin m @ lzero ⊢[ i ] ]) by (apply (ext_wf Hi); [now apply wft_fin | exact I]).
  assert (Hm1 : [ G ; Γ ,, tyFin m @ lzero ⊢[ i ] m⟨↑⟩ : tyNat @ lzero ])
    by exact (wk1_tm G i Hi _ _ _ _ _ _ HΓ1 Hm).
  assert (Hm1' : [ G ; Γ ,, tyFin m @ lzero ⊢[ i ] m'⟨↑⟩ : tyNat @ lzero ])
    by exact (wk1_tm G i Hi _ _ _ _ _ _ HΓ1 Hm').
  assert (Hmm1 : [ G ; Γ ,, tyFin m @ lzero ⊢[ i ] m⟨↑⟩ ≅ m'⟨↑⟩ : tyNat @ lzero ])
    by exact (wk1_eqtm G i Hi _ _ _ _ _ _ _ HΓ1 Hmm).
  assert (HΓ2 : [ G ; Γ ,, tyFin m @ lzero ,, tyFin (succ m⟨↑⟩) @ lzero ⊢[ i ] ])
    by (apply (ext_wf Hi); [apply wft_fin; [exact Hv | now apply wf_succ] | exact I]).
  assert (HF1 : [ G ; Γ ,, tyFin m @ lzero ,, tyFin (succ m⟨↑⟩) @ lzero ⊢[ i ] F⟨rlift ↑⟩ @ l ])
    by (apply (wk_under_ty Hi (X := tyFin (succ m))); [exact HΓ2 | exact HF]).
  assert (HFF1 : [ G ; Γ ,, tyFin m @ lzero ,, tyFin (succ m⟨↑⟩) @ lzero ⊢[ i ] F⟨rlift ↑⟩ ≅ F'⟨rlift ↑⟩ @ l ])
    by (apply (wk_under_eqty Hi (X := tyFin (succ m))); [exact HΓ2 | exact HFF]).
  pose proof (var0_wf G i Hi _ _ _ HΓ1) as H0.
  pose proof (fin_inr_wf Hi Hv Hc Hm1 H0) as H1.
  assert (H2 : [ G ; Γ ,, tyFin m @ lzero ⊢[ i ] tmInr lzero lzero (tyUnit lzero) (tyFin m'⟨↑⟩) (var 0)
                 : tyFin (succ m⟨↑⟩) @ lzero ]).
  { eapply wf_conv; [apply (fin_inr_wf Hi Hv Hc Hm1'); eapply wf_conv; [exact H0 |] | rewrite Hi; apply fin_succ_conv; exact Hmm1].
    rewrite Hi. cbn. apply eqty_fin; [exact Hv | apply eqtm_sym; exact Hmm1]. }
  unfold dvecMv. eapply eqty_trans.
  - exact (wf_ty_func Hi HF1 (lsub_eq_single Hi H1 H2 (fin_inr_eq Hm1 Hmm1 (eqtm_refl _ _ _ _ _ _ H0)))).
  - exact (eqty_single Hi HFF1 H2).
Qed.

(** The tail, in the head's context. *)
Lemma dvecTl_eqty {Γ l l' m m' F F' X lx} : lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ i ] m : tyNat @ lzero ] -> [ G ; Γ ⊢[ i ] m' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] m ≅ m' : tyNat @ lzero ] ->
  [ G ; Γ ,, tyFin (succ m) @ lzero ⊢[ i ] F @ l ] ->
  [ G ; Γ ,, tyFin (succ m) @ lzero ⊢[ i ] F ≅ F' @ l ] ->
  [ G ; Γ ,, X @ lx ⊢[ i ] ] ->
  [ G ; Γ ,, X @ lx ⊢[ i ] dvecTl l m F ≅ dvecTl l' m' F' @ l ].
Proof using Hi Hv Hc.
  intros Hl Hm Hm' Hmm HF HFF HΓX. rewrite !dvecTl_eq.
  apply (wk1_eqty G i Hi); [exact HΓX|].
  apply eqty_dvec; auto. exact (dvecMv_wf Hm HF). exact (dvecMv_eqty Hm Hm' Hmm HF HFF).
Qed.

(** The whole successor reduct. *)
Lemma dvec_sig_eqty {Γ l l' m m' F F'} : lequiv (gL G) l l' -> lwf (gL G) l ->
  [ G ; Γ ⊢[ i ] m : tyNat @ lzero ] -> [ G ; Γ ⊢[ i ] m' : tyNat @ lzero ] ->
  [ G ; Γ ⊢[ i ] m ≅ m' : tyNat @ lzero ] ->
  [ G ; Γ ,, tyFin (succ m) @ lzero ⊢[ i ] F @ l ] ->
  [ G ; Γ ,, tyFin (succ m) @ lzero ⊢[ i ] F ≅ F' @ l ] ->
  [ G ; Γ ⊢[ i ] tySig l l (dvecHd m F) (dvecTl l m F) ≅ tySig l' l' (dvecHd m' F') (dvecTl l' m' F') @ lmax l l ].
Proof using Hi Hv Hc.
  intros Hl Hw Hm Hm' Hmm HF HFF.
  assert (HH : [ G ; Γ ⊢[ i ] dvecHd m F @ l ]) by exact (wf_ty_single Hi HF (fin_inl_wf Hi Hv Hc Hm)).
  apply eqty_sig; auto.
  - exact (dvecHd_eqty Hm Hm' Hmm HF HFF).
  - apply dvecTl_eqty; auto. apply (ext_wf Hi); [exact HH | exact Hw].
Qed.

End DVecEq.
