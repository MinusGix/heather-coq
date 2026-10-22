(** * Presupposition: indexed coinductive types (M18b)

    The per-former lemmas of [presupposition]'s [M] cases, as
    [PresupIWf]'s: the equations of the step and out types, the
    signature's weakenings and conversions, the right-hand sides of the
    congruences, and β's reduct [mOutCorec] typed at [out]'s type. *)
From DeLaM.Typing Require Export PresupAux.

(** ** Equations

    [meq] compares two types or terms built from the signature by
    renamings and substitutions: congruence down to the leaves, where both
    sides become one substitution each, compared pointwise; a leaf whose
    substitution is the identity up to a normal entry closes by
    [subst_id] with the entry's normality in the context. *)
Ltac mrs := repeat first [ rewrite llk_r2l | rewrite llk_lcomp | rewrite llk_llift | rewrite llk_lren
                         | progress rlk_simpl | progress cbn [llk lsingle lsingle2 lsingle3 subst_tm ren_tm rlk Nat.add] ].
Ltac mhead t := lazymatch t with ?f _ => mhead f | _ => t end.
Ltac meq_leaf := repeat first [ rewrite ren_as_r2l_ty | rewrite ren_as_r2l ];
  repeat first [ rewrite subst_comp_ty | rewrite subst_comp ];
  first [ reflexivity
        | apply subst_ext_ty | apply subst_ext
        | apply subst_id_ty; [assumption|] | apply subst_id; [assumption|]
        | symmetry; apply subst_id_ty; [assumption|] | symmetry; apply subst_id; [assumption|] ];
  intros [|[|[|[|[|[|?n]]]]]]; mrs; try reflexivity; try (f_equal; lia).
Ltac meq_opaque h := lazymatch h with
  | ren_ty => idtac | ren_tm => idtac | @ren => idtac
  | subst_ty => idtac | subst_tm => idtac | @subst => idtac end.
Ltac meq_cong := lazymatch goal with
  | |- ?x = ?y => let h := mhead x in let h' := mhead y in
      tryif meq_opaque h then meq_leaf else
      tryif meq_opaque h' then meq_leaf else first [reflexivity | f_equal]
  end.
Ltac meq := push_ren; push_subst; repeat meq_cong.

Section Eqs.
Variables (l l' li k : lvl) (X A B Y : ty) (C j s y : tm).
Hypotheses (NX : nfty X) (NA : nfty A) (NB : nfty B) (NY : nfty Y) (NC : nftm C) (Nj : nftm j) (Ns : nftm s).

(** The step at the index and the seed. *)
Lemma M_E_step : (mStepTy l l' li X A B C k Y)⟨↑⟩[lsingle2 j y] = (mStepTy l l' li X A B C k Y)[lsingle j].
Proof using. meq. Qed.

(** The step's second component at its first, and [out]'s at a shape. *)
Lemma M_E_snd : (mStepSnd l l' li X A B C k Y j)[lsingle s] =
  tyPi l' (lmax k (mlvl l l' li)) B[lsingle2 j s]
    (tySum k (mlvl l l' li) Y⟨rlift ↑⟩[lsingle C[llift (lsingle2 j s)]]
       (tyM l l' li X⟨↑⟩ A⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩ C⟨rlift (rlift (rlift ↑))⟩ C[llift (lsingle2 j s)])).
Proof using NX NA NB NC Nj. meq. Qed.

Lemma M_E_pair :
  (tyPi l' (mlvl l l' li) B[llift (lsingle j)]
     (tyM l l' li X⟨↑⟩⟨↑⟩ A⟨rlift ↑⟩⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩
        C⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩ C[llift (llift (lsingle j))]))[lsingle s]
  = tyPi l' (mlvl l l' li) B[lsingle2 j s]
      (tyM l l' li X⟨↑⟩ A⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩ C⟨rlift (rlift (rlift ↑))⟩ C[llift (lsingle2 j s)]).
Proof using NX NA NB NC Nj. meq. Qed.
End Eqs.

(** Shapes of the shifted signature. *)
Lemma M_E_X3 (X : ty) : X⟨↑⟩⟨↑⟩⟨↑⟩⟨rlift (rlift (rlift ↑))⟩ = X⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩.
Proof. ren_comm. Qed.
Lemma M_E_X3s (X : ty) d : nfty X -> LK nftm d ->
  X⟨↑⟩⟨↑⟩⟨↑⟩[llift (llift (llift d))] = X[d]⟨↑⟩⟨↑⟩⟨↑⟩.
Proof. intros. rewrite !shift_llift_ty. reflexivity. Qed.

Lemma M_lv_f L l l' li : lwf L l -> lwf L l' -> lwf L li ->
  lequiv L (lmax l' (mlvl l l' li)) (mlvl l l' li).
Proof. intros. apply leqv_lequiv; [cbn; tauto .. |]. intros v; cbn; lia. Qed.
Lemma M_lv_kf L l l' li k : lwf L l -> lwf L l' -> lwf L li -> lwf L k ->
  lequiv L (lmax l' (lmax k (mlvl l l' li))) (lmax k (mlvl l l' li)).
Proof. intros. apply leqv_lequiv; [cbn; tauto .. |]. intros v; cbn; lia. Qed.

(** The signature's instances under [out]'s and β's binders, and the
    renamings of the step's typing and of [corec]'s seed in β's reduct. *)
Lemma M_E_X3j (X : ty) j : nfty X -> X⟨↑⟩⟨↑⟩⟨↑⟩[llift (llift (lsingle j))] = X⟨↑⟩⟨↑⟩.
Proof. intros. meq. Qed.
Lemma M_E_X3s2 (X : ty) j s : nfty X -> X⟨↑⟩⟨↑⟩⟨↑⟩[llift (lsingle2 j s)] = X⟨↑⟩.
Proof. intros. meq. Qed.
Lemma M_E_r0 (T : ty) : nfty T -> T⟨rlift ↑⟩[lsingle (var 0)] = T.
Proof. intros. meq. Qed.
Lemma M_E_mot (T : ty) a : (T⟨↑⟩⟨rlift ↑⟩)[lsingle a] = T⟨↑⟩.
Proof. meq. Qed.
Lemma M_E_seed (Y : ty) o : (Y⟨rlift ↑⟩[lsingle o])⟨↑⟩ = Y⟨rlift ↑⟩⟨rlift ↑⟩[lsingle o⟨↑⟩].
Proof. meq. Qed.
Lemma M_E_stepwk l l' li (X A B : ty) (C : tm) k (Y : ty) :
  (mStepTy l l' li X A B C k Y)⟨↑⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩
  = (mStepTy l l' li X⟨↑⟩⟨↑⟩ A⟨rlift ↑⟩⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩
       C⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩ k Y⟨rlift ↑⟩⟨rlift ↑⟩)⟨↑⟩.
Proof. meq. Qed.

Section MAux.
Context {G : gctx} {i : layer} (Hi : typeof i = i) (Hv : i <> lV).

(** The signature: the index type, the shapes, the positions and the
    child index. *)
Definition MSig Γ l l' li X A B C : Prop :=
  lwf (gL G) l /\ lwf (gL G) l' /\ lwf (gL G) li /\
  [ G ; Γ ⊢[ i ] X @ li ] /\ [ G ; Γ ,, X @ li ⊢[ i ] A @ l ] /\
  [ G ; Γ ,, X @ li ,, A @ l ⊢[ i ] B @ l' ] /\
  [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ⊢[ i ] C : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ].

(** Two signatures along equal components: the left one, the equations, and
    the right components typed in the left contexts. *)
Definition MEq Γ l l' li k k' ki X X' A A' B B' C C' : Prop :=
  lequiv (gL G) l k /\ lequiv (gL G) l' k' /\ lequiv (gL G) li ki /\ MSig Γ l l' li X A B C /\
  [ G ; Γ ⊢[ i ] X ≅ X' @ li ] /\ [ G ; Γ ,, X @ li ⊢[ i ] A ≅ A' @ l ] /\
  [ G ; Γ ,, X @ li ,, A @ l ⊢[ i ] B ≅ B' @ l' ] /\
  [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ⊢[ i ] C ≅ C' : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] /\
  [ G ; Γ ⊢[ i ] X' @ li ] /\ [ G ; Γ ,, X @ li ⊢[ i ] A' @ l ] /\
  [ G ; Γ ,, X @ li ,, A @ l ⊢[ i ] B' @ l' ] /\
  [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ⊢[ i ] C' : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ].

(** [MEq] with its equations first, so that a proof search solving the
    premises in order fixes the left components from them. *)
Lemma MEq_intro {Γ l l' li k k' ki X X' A A' B B' C C'} :
  lequiv (gL G) l k -> lequiv (gL G) l' k' -> lequiv (gL G) li ki ->
  [ G ; Γ ⊢[ i ] X ≅ X' @ li ] -> [ G ; Γ ,, X @ li ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ,, X @ li ,, A @ l ⊢[ i ] B ≅ B' @ l' ] ->
  [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ⊢[ i ] C ≅ C' : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] ->
  lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) li ->
  [ G ; Γ ⊢[ i ] X @ li ] -> [ G ; Γ ,, X @ li ⊢[ i ] A @ l ] ->
  [ G ; Γ ,, X @ li ,, A @ l ⊢[ i ] B @ l' ] ->
  [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ⊢[ i ] C : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] ->
  [ G ; Γ ⊢[ i ] X' @ li ] -> [ G ; Γ ,, X @ li ⊢[ i ] A' @ l ] ->
  [ G ; Γ ,, X @ li ,, A @ l ⊢[ i ] B' @ l' ] ->
  [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ⊢[ i ] C' : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] ->
  MEq Γ l l' li k k' ki X X' A A' B B' C C'.
Proof using. intros. unfold MEq, MSig. tauto. Qed.

Lemma MSig_nf {Γ l l' li X A B C} : MSig Γ l l' li X A B C ->
  nfty X /\ nfty A /\ nfty B /\ nftm C.
Proof using.
  intros (_ & _ & _ & HX & HA & HB & HC).
  repeat split; first [exact (wf_ty_nf HX) | exact (wf_ty_nf HA) | exact (wf_ty_nf HB) | exact (wf_tm_nf HC)].
Qed.

Lemma MSig_ctx {Γ l l' li X A B C} : MSig Γ l l' li X A B C -> [ G ; Γ ⊢[ i ] ].
Proof using Hi. intros (_ & _ & _ & HX & _). exact (ctx_of_wf_ty Hi HX). Qed.

(** The type at an index. *)
Lemma M_ty_wf {Γ l l' li X A B C j} : MSig Γ l l' li X A B C -> [ G ; Γ ⊢[ i ] j : X @ li ] ->
  [ G ; Γ ⊢[ i ] tyM l l' li X A B C j @ mlvl l l' li ].
Proof using Hi Hv.
  intros (Hl & Hl' & Hli & HX & HA & HB & HC) Hj. apply wft_M; auto using compt_self.
Qed.

(** Weakening, past one more local and under the signature's binders. *)
Ltac wkr_tac := repeat (eapply wkr_up'; [|reflexivity]); apply wkr_shift1.
Lemma M_wk_ty {Δ Γ T l r} : [ G ; Γ ⊢[ i ] T @ l ] -> wkr r Δ Γ -> [ G ; Δ ⊢[ i ] ] ->
  [ G ; Δ ⊢[ i ] T⟨r⟩ @ l ].
Proof using Hi. intros H Hr HΔ. exact (proj1 weakening_r _ _ _ _ _ H Hi _ _ Hr HΔ). Qed.
Lemma M_wk_tm {Δ Γ t T l r} : [ G ; Γ ⊢[ i ] t : T @ l ] -> wkr r Δ Γ -> [ G ; Δ ⊢[ i ] ] ->
  [ G ; Δ ⊢[ i ] t⟨r⟩ : T⟨r⟩ @ l ].
Proof using Hi. intros H Hr HΔ. exact (proj1 (proj2 weakening_r) _ _ _ _ _ _ H Hi _ _ Hr HΔ). Qed.
Lemma M_wk_eqty {Δ Γ T T' l r} : [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> wkr r Δ Γ -> [ G ; Δ ⊢[ i ] ] ->
  [ G ; Δ ⊢[ i ] T⟨r⟩ ≅ T'⟨r⟩ @ l ].
Proof using Hi. intros H Hr HΔ. exact (proj1 (proj2 (proj2 weakening_r)) _ _ _ _ _ _ H Hi _ _ Hr HΔ). Qed.
Lemma M_wk_eqtm {Δ Γ t t' T l r} : [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> wkr r Δ Γ -> [ G ; Δ ⊢[ i ] ] ->
  [ G ; Δ ⊢[ i ] t⟨r⟩ ≅ t'⟨r⟩ : T⟨r⟩ @ l ].
Proof using Hi. intros H Hr HΔ. exact (proj2 (proj2 (proj2 weakening_r)) _ _ _ _ _ _ _ H Hi _ _ Hr HΔ). Qed.

Lemma MSig_wk1 {Γ Y ly l l' li X A B C} : MSig Γ l l' li X A B C -> [ G ; Γ ,, Y @ ly ⊢[ i ] ] ->
  MSig (Γ ,, Y @ ly) l l' li X⟨↑⟩ A⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩ C⟨rlift (rlift (rlift ↑))⟩.
Proof using Hi Hv.
  intros (Hl & Hl' & Hli & HX & HA & HB & HC) HΓY.
  assert (HX1 : [ G ; Γ ,, Y @ ly ⊢[ i ] X⟨↑⟩ @ li ]) by exact (M_wk_ty HX (wkr_shift1 _ _ _) HΓY).
  assert (H1 : [ G ; Γ ,, Y @ ly ,, X⟨↑⟩ @ li ⊢[ i ] ]) by exact (ext_wf Hi HX1 Hli).
  assert (HA1 : [ G ; Γ ,, Y @ ly ,, X⟨↑⟩ @ li ⊢[ i ] A⟨rlift ↑⟩ @ l ])
    by (eapply M_wk_ty; [exact HA | wkr_tac | exact H1]).
  assert (H2 : [ G ; Γ ,, Y @ ly ,, X⟨↑⟩ @ li ,, A⟨rlift ↑⟩ @ l ⊢[ i ] ]) by exact (ext_wf Hi HA1 Hl).
  assert (HB1 : [ G ; Γ ,, Y @ ly ,, X⟨↑⟩ @ li ,, A⟨rlift ↑⟩ @ l ⊢[ i ] B⟨rlift (rlift ↑)⟩ @ l' ])
    by (eapply M_wk_ty; [exact HB | wkr_tac | exact H2]).
  assert (H3 : [ G ; Γ ,, Y @ ly ,, X⟨↑⟩ @ li ,, A⟨rlift ↑⟩ @ l ,, B⟨rlift (rlift ↑)⟩ @ l' ⊢[ i ] ])
    by exact (ext_wf Hi HB1 Hl').
  refine (conj Hl (conj Hl' (conj Hli (conj HX1 (conj HA1 (conj HB1 _)))))).
  eapply wf_tm_retype; [eapply M_wk_tm; [exact HC | wkr_tac | exact H3] | apply M_E_X3].
Qed.

Lemma MEq_wk1 {Γ Y ly l l' li k k' ki X X' A A' B B' C C'} :
  MEq Γ l l' li k k' ki X X' A A' B B' C C' -> [ G ; Γ ,, Y @ ly ⊢[ i ] ] ->
  MEq (Γ ,, Y @ ly) l l' li k k' ki X⟨↑⟩ X'⟨↑⟩ A⟨rlift ↑⟩ A'⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩ B'⟨rlift (rlift ↑)⟩
    C⟨rlift (rlift (rlift ↑))⟩ C'⟨rlift (rlift (rlift ↑))⟩.
Proof using Hi Hv.
  intros (Hlk & Hlk' & Hlik & HS & HXX & HAA & HBB & HCC & HX' & HA' & HB' & HC') HΓY.
  pose proof (MSig_wk1 HS HΓY) as HS1.
  pose proof HS1 as (_ & _ & _ & HX1 & HA1 & HB1 & _).
  pose proof HS as (Hl & Hl' & Hli & _).
  assert (H1 : [ G ; Γ ,, Y @ ly ,, X⟨↑⟩ @ li ⊢[ i ] ]) by exact (ext_wf Hi HX1 Hli).
  assert (H2 : [ G ; Γ ,, Y @ ly ,, X⟨↑⟩ @ li ,, A⟨rlift ↑⟩ @ l ⊢[ i ] ]) by exact (ext_wf Hi HA1 Hl).
  assert (H3 : [ G ; Γ ,, Y @ ly ,, X⟨↑⟩ @ li ,, A⟨rlift ↑⟩ @ l ,, B⟨rlift (rlift ↑)⟩ @ l' ⊢[ i ] ])
    by exact (ext_wf Hi HB1 Hl').
  refine (conj Hlk (conj Hlk' (conj Hlik (conj HS1 _)))).
  repeat split.
  - exact (M_wk_eqty HXX (wkr_shift1 _ _ _) HΓY).
  - eapply M_wk_eqty; [exact HAA | wkr_tac | exact H1].
  - eapply M_wk_eqty; [exact HBB | wkr_tac | exact H2].
  - eapply eq_tm_retype; [eapply M_wk_eqtm; [exact HCC | wkr_tac | exact H3] | apply M_E_X3].
  - exact (M_wk_ty HX' (wkr_shift1 _ _ _) HΓY).
  - eapply M_wk_ty; [exact HA' | wkr_tac | exact H1].
  - eapply M_wk_ty; [exact HB' | wkr_tac | exact H2].
  - eapply wf_tm_retype; [eapply M_wk_tm; [exact HC' | wkr_tac | exact H3] | apply M_E_X3].
Qed.

(** Moving a judgment along the identity between converted contexts. *)
Lemma M_mv_ty {Δ Δ' T k} : [ G ; Δ' ⊢[ i ] lshift 0 : Δ ] -> [ G ; Δ ⊢[ i ] T @ k ] -> [ G ; Δ' ⊢[ i ] T @ k ].
Proof using Hi.
  intros Hid H. pose proof (wf_ty_subst Hi H Hid) as X. rewrite nf_id_ty in X by exact (wf_ty_nf H). exact X.
Qed.
Lemma M_mv_tm {Δ Δ' t T k} : [ G ; Δ' ⊢[ i ] lshift 0 : Δ ] -> [ G ; Δ ⊢[ i ] t : T @ k ] ->
  [ G ; Δ' ⊢[ i ] t : T @ k ].
Proof using Hi.
  intros Hid H. pose proof (wf_tm_subst Hi H Hid) as X.
  rewrite nf_id in X by exact (wf_tm_nf H). rewrite nf_id_ty in X by exact (wf_tm_nf_ty H). exact X.
Qed.
Lemma M_mv_eqty {Δ Δ' T T' k} : [ G ; Δ' ⊢[ i ] lshift 0 : Δ ] -> [ G ; Δ ⊢[ i ] T ≅ T' @ k ] ->
  [ G ; Δ' ⊢[ i ] T ≅ T' @ k ].
Proof using Hi.
  intros Hid H. pose proof (eqty_subst Hi H Hid) as X.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 typed_nf)))) _ _ _ _ _ _ H) as [N1 N2].
  rewrite !nf_id_ty in X by assumption. exact X.
Qed.
Lemma M_mv_eqtm {Δ Δ' t t' T k} : [ G ; Δ' ⊢[ i ] lshift 0 : Δ ] -> [ G ; Δ ⊢[ i ] t ≅ t' : T @ k ] ->
  [ G ; Δ' ⊢[ i ] t ≅ t' : T @ k ].
Proof using Hi.
  intros Hid H. pose proof (eqtm_subst Hi H Hid) as X.
  pose proof (proj2 (proj2 (proj2 (proj2 (proj2 typed_nf)))) _ _ _ _ _ _ _ H) as (N1 & N2 & N3).
  rewrite !nf_id, nf_id_ty in X by assumption. exact X.
Qed.

(** The identity from a converted last entry. *)
Lemma M_id {Γ Γ' l k A A'} : [ G ; Γ' ⊢[ i ] lshift 0 : Γ ] ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] A ≅ A' @ l ] ->
  [ G ; Γ ⊢[ i ] A' @ l ] -> lequiv (gL G) l k ->
  [ G ; Γ' ,, A' @ k ⊢[ i ] lshift 0 : Γ ,, A @ l ].
Proof using Hi. intros Hid HA HAA HA' Hlk. exact (proj2 (ctx_conv_ext Hi Hid HA HAA HA' Hlk)). Qed.

(** The right signature, in its own contexts, with the identities between
    the two signatures' contexts. *)
Lemma MEq_ids {Γ l l' li k k' ki X X' A A' B B' C C'} :
  MEq Γ l l' li k k' ki X X' A A' B B' C C' ->
  [ G ; Γ ,, X' @ ki ⊢[ i ] lshift 0 : Γ ,, X @ li ] /\
  [ G ; Γ ,, X' @ ki ,, A' @ k ⊢[ i ] lshift 0 : Γ ,, X @ li ,, A @ l ] /\
  [ G ; Γ ,, X' @ ki ,, A' @ k ,, B' @ k' ⊢[ i ] lshift 0 : Γ ,, X @ li ,, A @ l ,, B @ l' ].
Proof using Hi Hv.
  intros (Hlk & Hlk' & Hlik & (Hl & Hl' & Hli & HX & HA & HB & HC) & HXX & HAA & HBB & HCC & HX' & HA' & HB' & HC').
  assert (Hid0 : [ G ; Γ ⊢[ i ] lshift 0 : Γ ]) by (eapply lsub_wf_id; eauto using ctx_of_wf_ty).
  pose proof (M_id Hid0 HX HXX HX' Hlik) as Hid1.
  pose proof (M_id Hid1 HA HAA HA' Hlk) as Hid2.
  pose proof (M_id Hid2 HB HBB HB' Hlk') as Hid3.
  tauto.
Qed.

Lemma MEq_sig_r {Γ l l' li k k' ki X X' A A' B B' C C'} :
  MEq Γ l l' li k k' ki X X' A A' B B' C C' -> MSig Γ k k' ki X' A' B' C'.
Proof using Hi Hv.
  intros HE. pose proof (MEq_ids HE) as (Hid1 & Hid2 & Hid3).
  destruct HE as (Hlk & Hlk' & Hlik & (Hl & Hl' & Hli & HX & HA & HB & HC) & HXX & HAA & HBB & HCC
                  & HX' & HA' & HB' & HC').
  assert (HΓXAB : [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ⊢[ i ] ]) by exact (ctx_of_wf_tm Hi HC).
  assert (EX3 : [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ⊢[ i ] X'⟨↑⟩⟨↑⟩⟨↑⟩ ≅ X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ])
    by (eapply wk3_eqty; [exact Hi | exact HΓXAB | exact (eqty_sym _ _ _ _ _ _ HXX)]).
  refine (conj (lequiv_wf_r _ _ _ Hlk) (conj (lequiv_wf_r _ _ _ Hlk') (conj (lequiv_wf_r _ _ _ Hlik)
            (conj _ (conj _ (conj _ _)))))).
  - eapply wft_lconv; [exact HX' | apply lequiv_sym, Hlik].
  - eapply wft_lconv; [exact (M_mv_ty Hid1 HA') | apply lequiv_sym, Hlk].
  - eapply wft_lconv; [exact (M_mv_ty Hid2 HB') | apply lequiv_sym, Hlk'].
  - eapply wf_lconv; [| apply lequiv_sym, Hlik]. exact (M_mv_tm Hid3 (conv_tm' Hi HC' EX3)).
Qed.

(** The types along equal components. *)
Lemma M_ty_eq {Γ l l' li k k' ki X X' A A' B B' C C' j j'} :
  MEq Γ l l' li k k' ki X X' A A' B B' C C' -> [ G ; Γ ⊢[ i ] j ≅ j' : X @ li ] ->
  [ G ; Γ ⊢[ i ] tyM l l' li X A B C j ≅ tyM k k' ki X' A' B' C' j' @ mlvl l l' li ].
Proof using Hi Hv.
  intros (Hlk & Hlk' & Hlik & (Hl & Hl' & Hli & HX & HA & HB & HC) & HXX & HAA & HBB & HCC & _) Hjj.
  apply eqty_M; auto using compt_self.
Qed.

Lemma pre_M_r {Γ l l' li k k' ki X X' A A' B B' C C' j'} :
  MEq Γ l l' li k k' ki X X' A A' B B' C C' -> [ G ; Γ ⊢[ i ] j' : X @ li ] ->
  [ G ; Γ ⊢[ i ] tyM k k' ki X' A' B' C' j' @ mlvl l l' li ].
Proof using Hi Hv.
  intros HE Hj'. pose proof (MEq_sig_r HE) as HS'.
  destruct HE as (Hlk & Hlk' & Hlik & _ & HXX & _).
  eapply wft_lconv; [| exact (lequiv_max _ _ _ _ _ (lequiv_max _ _ _ _ _ Hlk Hlk') Hlik)].
  apply (M_ty_wf HS').
  eapply wf_lconv; [eapply (conv_tm' Hi); [exact Hj' | exact (eqty_sym _ _ _ _ _ _ HXX)] | apply lequiv_sym, Hlik].
Qed.

(** Two instances along equal components and equal substitutions. *)
Lemma M_func2_ty {Γ Δ T T' l d d'} : [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Γ ⊢[ i ] T ≅ T' @ l ] ->
  [ G ; Δ ⊢[ i ] d ≅ d' : Γ ] -> [ G ; Δ ⊢[ i ] T[d] ≅ T'[d'] @ l ].
Proof using Hi.
  intros HT HTT Hd. eapply eqty_trans; [exact (wf_ty_func Hi HT Hd) | exact (eqty_subst Hi HTT (lsub_eq_r Hd))].
Qed.
Lemma M_func2_tm {Γ Δ t t' T l d d'} : [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] ->
  [ G ; Δ ⊢[ i ] d ≅ d' : Γ ] -> T[d] = T[d'] -> [ G ; Δ ⊢[ i ] t[d] ≅ t'[d'] : T[d] @ l ].
Proof using Hi.
  intros Ht Htt Hd E. eapply eqtm_trans; [exact (wf_tm_func Hi Ht Hd) |].
  rewrite E. exact (eqtm_subst Hi Htt (lsub_eq_r Hd)).
Qed.

(** The lifted index into the shapes' context. *)
Lemma M_lift1 {Γ X A li l j} : [ G ; Γ ,, X @ li ⊢[ i ] A @ l ] -> lwf (gL G) l -> [ G ; Γ ⊢[ i ] j : X @ li ] ->
  [ G ; Γ ,, A[lsingle j] @ l ⊢[ i ] llift (lsingle j) : Γ ,, X @ li ,, A @ l ].
Proof using Hi.
  intros HA Hl Hj. eapply (lsub_wf_lift' G i Hi);
    [exact (lsub_wf_single G i Hi _ _ _ _ (ctx_of_wf_tm Hi Hj) Hj) | exact (wf_ty_single Hi HA Hj) | exact Hl | reflexivity].
Qed.

(** [out]'s type at an index: its second component, and the whole. *)
Lemma M_outB_wf {Γ l l' li X A B C j} : MSig Γ l l' li X A B C -> [ G ; Γ ⊢[ i ] j : X @ li ] ->
  [ G ; Γ ,, A[lsingle j] @ l ⊢[ i ] tyPi l' (mlvl l l' li) B[llift (lsingle j)]
      (tyM l l' li X⟨↑⟩⟨↑⟩ A⟨rlift ↑⟩⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩
         C⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩ C[llift (llift (lsingle j))]) @ mlvl l l' li ].
Proof using Hi Hv.
  intros HS Hj. pose proof HS as (Hl & Hl' & Hli & HX & HA & HB & HC).
  assert (Hf : lwf (gL G) (mlvl l l' li)) by (cbn; repeat split; assumption).
  pose proof (M_lift1 HA Hl Hj) as H1.
  assert (HAj : [ G ; Γ ⊢[ i ] A[lsingle j] @ l ]) by exact (wf_ty_single Hi HA Hj).
  assert (HBj : [ G ; Γ ,, A[lsingle j] @ l ⊢[ i ] B[llift (lsingle j)] @ l' ]) by exact (wf_ty_subst Hi HB H1).
  assert (HΓ1 : [ G ; Γ ,, A[lsingle j] @ l ⊢[ i ] ]) by exact (ext_wf Hi HAj Hl).
  assert (HΓ2 : [ G ; Γ ,, A[lsingle j] @ l ,, B[llift (lsingle j)] @ l' ⊢[ i ] ]) by exact (ext_wf Hi HBj Hl').
  assert (H2 : [ G ; Γ ,, A[lsingle j] @ l ,, B[llift (lsingle j)] @ l' ⊢[ i ] llift (llift (lsingle j))
                 : Γ ,, X @ li ,, A @ l ,, B @ l' ])
    by (eapply (lsub_wf_lift' G i Hi); [exact H1 | exact HBj | exact Hl' | reflexivity]).
  eapply wft_lconv; [| apply lequiv_sym, M_lv_f; assumption].
  apply wft_pi; [exact Hv | exact Hl' | exact Hf | exact HBj |].
  apply (M_ty_wf (MSig_wk1 (MSig_wk1 HS HΓ1) HΓ2)).
  eapply wf_tm_retype; [exact (wf_tm_subst Hi HC H2) | apply M_E_X3j, (wf_ty_nf HX)].
Qed.

Lemma M_out_wf {Γ l l' li X A B C j} : MSig Γ l l' li X A B C -> [ G ; Γ ⊢[ i ] j : X @ li ] ->
  [ G ; Γ ⊢[ i ] mOutTy l l' li X A B C j @ lmax l (mlvl l l' li) ].
Proof using Hi Hv.
  intros HS Hj. pose proof HS as (Hl & Hl' & Hli & HX & HA & _).
  apply wft_sig; [exact Hv | exact Hl | cbn; repeat split; assumption | exact (wf_ty_single Hi HA Hj)
                 | exact (M_outB_wf HS Hj)].
Qed.

Lemma M_out_eq {Γ l l' li k k' ki X X' A A' B B' C C' j j'} :
  MEq Γ l l' li k k' ki X X' A A' B B' C C' ->
  [ G ; Γ ⊢[ i ] j : X @ li ] -> [ G ; Γ ⊢[ i ] j' : X @ li ] -> [ G ; Γ ⊢[ i ] j ≅ j' : X @ li ] ->
  [ G ; Γ ⊢[ i ] mOutTy l l' li X A B C j ≅ mOutTy k k' ki X' A' B' C' j' @ lmax l (mlvl l l' li) ].
Proof using Hi Hv.
  intros HE Hj Hj' Hjj. pose proof HE as (Hlk & Hlk' & Hlik & HS & HXX & HAA & HBB & HCC & _).
  pose proof HS as (Hl & Hl' & Hli & HX & HA & HB & HC).
  assert (Hff : lequiv (gL G) (mlvl l l' li) (mlvl k k' ki))
    by exact (lequiv_max _ _ _ _ _ (lequiv_max _ _ _ _ _ Hlk Hlk') Hlik).
  assert (HAj : [ G ; Γ ⊢[ i ] A[lsingle j] @ l ]) by exact (wf_ty_single Hi HA Hj).
  assert (E0 : [ G ; Γ ⊢[ i ] lsingle j ≅ lsingle j' : Γ ,, X @ li ]) by exact (lsub_eq_single Hi Hj Hj' Hjj).
  assert (E1 : [ G ; Γ ,, A[lsingle j] @ l ⊢[ i ] llift (lsingle j) ≅ llift (lsingle j') : Γ ,, X @ li ,, A @ l ])
    by (eapply (lsub_eq_lift Hi); [exact E0 | exact HAj | exact Hl | exact (wf_ty_func Hi HA E0) | reflexivity]).
  assert (HBj : [ G ; Γ ,, A[lsingle j] @ l ⊢[ i ] B[llift (lsingle j)] @ l' ])
    by exact (wf_ty_subst Hi HB (lsub_eq_l E1)).
  assert (E2 : [ G ; Γ ,, A[lsingle j] @ l ,, B[llift (lsingle j)] @ l' ⊢[ i ]
                 llift (llift (lsingle j)) ≅ llift (llift (lsingle j')) : Γ ,, X @ li ,, A @ l ,, B @ l' ])
    by (eapply (lsub_eq_lift Hi); [exact E1 | exact HBj | exact Hl' | exact (wf_ty_func Hi HB E1) | reflexivity]).
  assert (HΓ1 : [ G ; Γ ,, A[lsingle j] @ l ⊢[ i ] ]) by exact (ext_wf Hi HAj Hl).
  assert (HΓ2 : [ G ; Γ ,, A[lsingle j] @ l ,, B[llift (lsingle j)] @ l' ⊢[ i ] ]) by exact (ext_wf Hi HBj Hl').
  apply eqty_sig; [exact Hv | exact Hlk | exact Hff | exact HAj | exact (M_func2_ty HA HAA E0) |].
  eapply eqty_lconv; [| apply lequiv_sym, M_lv_f; assumption].
  apply eqty_pi; [exact Hv | exact Hlk' | exact Hff | exact HBj | exact (M_func2_ty HB HBB E1) |].
  apply (M_ty_eq (MEq_wk1 (MEq_wk1 HE HΓ1) HΓ2)).
  assert (NX : nfty X) by exact (wf_ty_nf HX).
  pose proof (M_func2_tm HC HCC E2 ltac:(rewrite !M_E_X3j by exact NX; reflexivity)) as X0.
  rewrite M_E_X3j in X0 by exact NX. exact X0.
Qed.

Lemma pre_out_r {Γ l l' li k k' ki X X' A A' B B' C C' j j' m'} :
  MEq Γ l l' li k k' ki X X' A A' B B' C C' ->
  [ G ; Γ ⊢[ i ] j : X @ li ] -> [ G ; Γ ⊢[ i ] j' : X @ li ] -> [ G ; Γ ⊢[ i ] j ≅ j' : X @ li ] ->
  [ G ; Γ ⊢[ i ] m' : tyM l l' li X A B C j @ mlvl l l' li ] ->
  [ G ; Γ ⊢[ i ] tmOut k k' ki X' A' B' C' j' m' : mOutTy l l' li X A B C j @ lmax l (mlvl l l' li) ].
Proof using Hi Hv.
  intros HE Hj Hj' Hjj Hm'. pose proof (MEq_sig_r HE) as HS'.
  pose proof HE as (Hlk & Hlk' & Hlik & _ & HXX & _).
  pose proof HS' as (Hk & Hk' & Hki & HX' & HA' & HB' & HC').
  assert (Hff : lequiv (gL G) (mlvl l l' li) (mlvl k k' ki))
    by exact (lequiv_max _ _ _ _ _ (lequiv_max _ _ _ _ _ Hlk Hlk') Hlik).
  assert (HL : lequiv (gL G) (lmax l (mlvl l l' li)) (lmax k (mlvl k k' ki))) by exact (lequiv_max _ _ _ _ _ Hlk Hff).
  assert (Hj'k : [ G ; Γ ⊢[ i ] j' : X' @ ki ])
    by (eapply wf_lconv; [eapply (conv_tm' Hi); [exact Hj' | exact (eqty_sym _ _ _ _ _ _ HXX)] | apply lequiv_sym, Hlik]).
  assert (Hm'k : [ G ; Γ ⊢[ i ] m' : tyM k k' ki X' A' B' C' j' @ mlvl k k' ki ])
    by (eapply wf_lconv; [eapply (conv_tm' Hi); [exact Hm' | exact (eqty_sym _ _ _ _ _ _ (M_ty_eq HE Hjj))]
                         | apply lequiv_sym, Hff]).
  eapply wf_lconv; [| exact HL].
  eapply (conv_tm' Hi); [apply wf_out; auto using compt_self |].
  eapply eqty_lconv; [exact (M_out_eq HE Hj Hj' Hjj) | apply lequiv_sym, HL].
Qed.

(** The step type, in the index's context: the contexts of its
    components, its second component, and the whole. *)
Lemma M_X3_ctx {Γ l l' li X A B C} : MSig Γ l l' li X A B C ->
  [ G ; Γ ,, X @ li ,, X⟨↑⟩ @ li ⊢[ i ] ] /\ [ G ; Γ ,, X @ li ,, A @ l ,, X⟨↑⟩⟨↑⟩ @ li ⊢[ i ] ] /\
  [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ,, X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ⊢[ i ] ].
Proof using Hi Hv.
  intros (Hl & Hl' & Hli & HX & HA & HB & _).
  assert (HΓX : [ G ; Γ ,, X @ li ⊢[ i ] ]) by exact (ext_wf Hi HX Hli).
  assert (HΓXA : [ G ; Γ ,, X @ li ,, A @ l ⊢[ i ] ]) by exact (ext_wf Hi HA Hl).
  assert (HΓ3 : [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ⊢[ i ] ]) by exact (ext_wf Hi HB Hl').
  pose proof (M_wk_ty HX (wkr_shift1 _ _ _) HΓX) as X1.
  pose proof (M_wk_ty X1 (wkr_shift1 _ _ _) HΓXA) as X2.
  pose proof (M_wk_ty X2 (wkr_shift1 _ _ _) HΓ3) as X3.
  exact (conj (ext_wf Hi X1 Hli) (conj (ext_wf Hi X2 Hli) (ext_wf Hi X3 Hli))).
Qed.

Lemma M_Y3_wf {Γ l l' li X A B C Y k} : MSig Γ l l' li X A B C -> [ G ; Γ ,, X @ li ⊢[ i ] Y @ k ] ->
  [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ,, X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ⊢[ i ] Y⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ @ k ].
Proof using Hi Hv.
  intros HS HY. pose proof (M_X3_ctx HS) as (H1 & H2 & H3).
  exact (wk_under_ty Hi H3 (wk_under_ty Hi H2 (wk_under_ty Hi H1 HY))).
Qed.
Lemma M_Y3_eq {Γ l l' li X A B C Y Y' k} : MSig Γ l l' li X A B C -> [ G ; Γ ,, X @ li ⊢[ i ] Y ≅ Y' @ k ] ->
  [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ,, X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ⊢[ i ]
      Y⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ ≅ Y'⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ @ k ].
Proof using Hi Hv.
  intros HS HY. pose proof (M_X3_ctx HS) as (H1 & H2 & H3).
  exact (wk_under_eqty Hi H3 (wk_under_eqty Hi H2 (wk_under_eqty Hi H1 HY))).
Qed.

Lemma M_stepB_wf {Γ l l' li X A B C Y k} : MSig Γ l l' li X A B C -> lwf (gL G) k ->
  [ G ; Γ ,, X @ li ⊢[ i ] Y @ k ] ->
  [ G ; Γ ,, X @ li ,, A @ l ⊢[ i ] tyPi l' (lmax k (mlvl l l' li)) B
      (tySum k (mlvl l l' li) Y⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle C]
         (tyM l l' li X⟨↑⟩⟨↑⟩⟨↑⟩ A⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩
            B⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩
            C⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩ C))
      @ lmax k (mlvl l l' li) ].
Proof using Hi Hv.
  intros HS Hk HY. pose proof HS as (Hl & Hl' & Hli & HX & HA & HB & HC).
  assert (Hf : lwf (gL G) (mlvl l l' li)) by (cbn; repeat split; assumption).
  assert (HΓX : [ G ; Γ ,, X @ li ⊢[ i ] ]) by exact (ext_wf Hi HX Hli).
  assert (HΓXA : [ G ; Γ ,, X @ li ,, A @ l ⊢[ i ] ]) by exact (ext_wf Hi HA Hl).
  assert (HΓ3 : [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ⊢[ i ] ]) by exact (ext_wf Hi HB Hl').
  eapply wft_lconv; [| apply lequiv_sym, M_lv_kf; assumption].
  apply wft_pi; [exact Hv | exact Hl' | cbn; repeat split; assumption | exact HB |].
  apply wft_sum; [exact Hv | exact Hk | exact Hf | exact (wf_ty_single Hi (M_Y3_wf HS HY) HC) |].
  exact (M_ty_wf (MSig_wk1 (MSig_wk1 (MSig_wk1 HS HΓX) HΓXA) HΓ3) HC).
Qed.

Lemma M_step_wf {Γ l l' li X A B C Y k} : MSig Γ l l' li X A B C -> lwf (gL G) k ->
  [ G ; Γ ,, X @ li ⊢[ i ] Y @ k ] ->
  [ G ; Γ ,, X @ li ⊢[ i ] mStepTy l l' li X A B C k Y @ lmax l (lmax k (mlvl l l' li)) ].
Proof using Hi Hv.
  intros HS Hk HY. pose proof HS as (Hl & Hl' & Hli & HX & HA & _).
  apply wft_sig; [exact Hv | exact Hl | cbn; repeat split; assumption | exact HA | exact (M_stepB_wf HS Hk HY)].
Qed.

Lemma M_step_eq {Γ l l' li k k' ki X X' A A' B B' C C' Y Y' kc kc'} :
  MEq Γ l l' li k k' ki X X' A A' B B' C C' -> lequiv (gL G) kc kc' ->
  [ G ; Γ ,, X @ li ⊢[ i ] Y @ kc ] -> [ G ; Γ ,, X @ li ⊢[ i ] Y ≅ Y' @ kc ] ->
  [ G ; Γ ,, X @ li ⊢[ i ] mStepTy l l' li X A B C kc Y ≅ mStepTy k k' ki X' A' B' C' kc' Y'
      @ lmax l (lmax kc (mlvl l l' li)) ].
Proof using Hi Hv.
  intros HE Hkc HY HYY. pose proof HE as (Hlk & Hlk' & Hlik & HS & HXX & HAA & HBB & HCC & HX' & HA' & HB' & HC').
  pose proof HS as (Hl & Hl' & Hli & HX & HA & HB & HC).
  assert (Hff : lequiv (gL G) (mlvl l l' li) (mlvl k k' ki))
    by exact (lequiv_max _ _ _ _ _ (lequiv_max _ _ _ _ _ Hlk Hlk') Hlik).
  assert (Hkf : lequiv (gL G) (lmax kc (mlvl l l' li)) (lmax kc' (mlvl k k' ki))) by exact (lequiv_max _ _ _ _ _ Hkc Hff).
  assert (HΓX : [ G ; Γ ,, X @ li ⊢[ i ] ]) by exact (ext_wf Hi HX Hli).
  assert (HΓXA : [ G ; Γ ,, X @ li ,, A @ l ⊢[ i ] ]) by exact (ext_wf Hi HA Hl).
  assert (HΓ3 : [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ⊢[ i ] ]) by exact (ext_wf Hi HB Hl').
  apply eqty_sig; [exact Hv | exact Hlk | exact Hkf | exact HA | exact HAA |].
  eapply eqty_lconv; [| apply lequiv_sym, M_lv_kf; first [assumption | exact (lequiv_wf_l _ _ _ Hkc)]].
  apply eqty_pi; [exact Hv | exact Hlk' | exact Hkf | exact HB | exact HBB |].
  apply eqty_sum; [exact Hv | exact Hkc | exact Hff | |].
  - exact (M_func2_ty (M_Y3_wf HS HY) (M_Y3_eq HS HYY) (lsub_eq_single Hi HC HC' HCC)).
  - exact (M_ty_eq (MEq_wk1 (MEq_wk1 (MEq_wk1 HE HΓX) HΓXA) HΓ3) HCC).
Qed.

Lemma pre_corec_r {Γ l l' li k k' ki X X' A A' B B' C C' kc kc' Y Y' c' j j' y'} :
  MEq Γ l l' li k k' ki X X' A A' B B' C C' -> lequiv (gL G) kc kc' ->
  [ G ; Γ ,, X @ li ⊢[ i ] Y ≅ Y' @ kc ] -> [ G ; Γ ,, X @ li ⊢[ i ] Y @ kc ] ->
  [ G ; Γ ,, X @ li ⊢[ i ] Y' @ kc ] ->
  [ G ; Γ ,, X @ li ,, Y @ kc ⊢[ i ] c' : (mStepTy l l' li X A B C kc Y)⟨↑⟩ @ lmax l (lmax kc (mlvl l l' li)) ] ->
  [ G ; Γ ⊢[ i ] j : X @ li ] -> [ G ; Γ ⊢[ i ] j' : X @ li ] -> [ G ; Γ ⊢[ i ] j ≅ j' : X @ li ] ->
  [ G ; Γ ⊢[ i ] y' : Y[lsingle j] @ kc ] ->
  [ G ; Γ ⊢[ i ] tmCorec k k' ki X' A' B' C' kc' Y' c' j' y' : tyM l l' li X A B C j @ mlvl l l' li ].
Proof using Hi Hv.
  intros HE Hkc HYY HY HY' Hc' Hj Hj' Hjj Hy'.
  pose proof (MEq_sig_r HE) as HS'. pose proof (MEq_ids HE) as (Hid1 & _).
  pose proof HE as (Hlk & Hlk' & Hlik & HS & HXX & _).
  pose proof HS as (Hl & Hl' & Hli & HX & _).
  pose proof HS' as (Hk & Hk' & Hki & HX' & HA' & HB' & HC').
  assert (Hff : lequiv (gL G) (mlvl l l' li) (mlvl k k' ki))
    by exact (lequiv_max _ _ _ _ _ (lequiv_max _ _ _ _ _ Hlk Hlk') Hlik).
  assert (HLc : lequiv (gL G) (lmax l (lmax kc (mlvl l l' li))) (lmax k (lmax kc' (mlvl k k' ki))))
    by exact (lequiv_max _ _ _ _ _ Hlk (lequiv_max _ _ _ _ _ Hkc Hff)).
  assert (HΓXY : [ G ; Γ ,, X @ li ,, Y @ kc ⊢[ i ] ]) by exact (ext_wf Hi HY (lequiv_wf_l _ _ _ Hkc)).
  pose proof (M_id Hid1 HY HYY HY' Hkc) as HidY.
  assert (HY'k : [ G ; Γ ,, X' @ ki ⊢[ i ] Y' @ kc' ])
    by (eapply wft_lconv; [exact (M_mv_ty Hid1 HY') | apply lequiv_sym, Hkc]).
  assert (ES : [ G ; Γ ,, X @ li ,, Y @ kc ⊢[ i ] (mStepTy l l' li X A B C kc Y)⟨↑⟩
                 ≅ (mStepTy k k' ki X' A' B' C' kc' Y')⟨↑⟩ @ lmax l (lmax kc (mlvl l l' li)) ])
    by exact (M_wk_eqty (M_step_eq HE Hkc HY HYY) (wkr_shift1 _ _ _) HΓXY).
  assert (Hc'k : [ G ; Γ ,, X' @ ki ,, Y' @ kc' ⊢[ i ] c' : (mStepTy k k' ki X' A' B' C' kc' Y')⟨↑⟩
                   @ lmax k (lmax kc' (mlvl k k' ki)) ])
    by (eapply wf_lconv; [exact (M_mv_tm HidY (conv_tm' Hi Hc' (eqty_sym _ _ _ _ _ _ ES))) | apply lequiv_sym, HLc]).
  assert (Hj'k : [ G ; Γ ⊢[ i ] j' : X' @ ki ])
    by (eapply wf_lconv; [eapply (conv_tm' Hi); [exact Hj' | exact (eqty_sym _ _ _ _ _ _ HXX)] | apply lequiv_sym, Hlik]).
  assert (Hy'k : [ G ; Γ ⊢[ i ] y' : Y'[lsingle j'] @ kc' ])
    by (eapply wf_lconv;
        [ eapply (conv_tm' Hi);
          [exact Hy' | apply eqty_sym, (M_func2_ty HY HYY (lsub_eq_single Hi Hj Hj' Hjj))]
        | apply lequiv_sym, Hkc ]).
  eapply wf_lconv; [| exact Hff].
  eapply (conv_tm' Hi); [apply wf_corec; auto using compt_self; exact (lequiv_wf_r _ _ _ Hkc) |].
  eapply eqty_lconv; [exact (M_ty_eq HE Hjj) | apply lequiv_sym, Hff].
Qed.

(** β's left-hand side, and its reduct at [out]'s type: the pair of the
    step's first projection and the λ over the positions whose body cases
    on the step's second projection, continuing with [corec] from the
    carrier or returning the [M] node. *)
Lemma pre_out_corec_l {Γ l l' li X A B C k Y c j y} : MSig Γ l l' li X A B C -> lwf (gL G) k ->
  [ G ; Γ ,, X @ li ⊢[ i ] Y @ k ] ->
  [ G ; Γ ,, X @ li ,, Y @ k ⊢[ i ] c : (mStepTy l l' li X A B C k Y)⟨↑⟩ @ lmax l (lmax k (mlvl l l' li)) ] ->
  [ G ; Γ ⊢[ i ] j : X @ li ] -> [ G ; Γ ⊢[ i ] y : Y[lsingle j] @ k ] ->
  [ G ; Γ ⊢[ i ] tmOut l l' li X A B C j (tmCorec l l' li X A B C k Y c j y) : mOutTy l l' li X A B C j
      @ lmax l (mlvl l l' li) ].
Proof using Hi Hv.
  intros (Hl & Hl' & Hli & HX & HA & HB & HC) Hk HY Hc Hj Hy.
  apply wf_out; auto using compt_self. apply wf_corec; auto using compt_self.
Qed.

(** β's reduct's components: the step's first projection, and the λ over
    the positions at its type at that projection. *)
Lemma pre_out_corec_parts {Γ l l' li X A B C k Y c j y} : MSig Γ l l' li X A B C -> lwf (gL G) k ->
  [ G ; Γ ,, X @ li ⊢[ i ] Y @ k ] ->
  [ G ; Γ ,, X @ li ,, Y @ k ⊢[ i ] c : (mStepTy l l' li X A B C k Y)⟨↑⟩ @ lmax l (lmax k (mlvl l l' li)) ] ->
  [ G ; Γ ⊢[ i ] j : X @ li ] -> [ G ; Γ ⊢[ i ] y : Y[lsingle j] @ k ] ->
  forall P a b, mOutCorec l l' li X A B C k Y c j y = tmPair l (mlvl l l' li) A[lsingle j] P a b ->
  [ G ; Γ ⊢[ i ] a : A[lsingle j] @ l ] /\
  [ G ; Γ ⊢[ i ] b : tyPi l' (mlvl l l' li) B[lsingle2 j a]
      (tyM l l' li X⟨↑⟩ A⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩ C⟨rlift (rlift (rlift ↑))⟩ C[llift (lsingle2 j a)])
      @ mlvl l l' li ].
Proof using Hi Hv.
  intros HS Hk HY Hc Hj Hy P0 a0 b0 Eq0.
  pose proof HS as (Hl & Hl' & Hli & HX & HA & HB & HC).
  pose proof (MSig_nf HS) as (NX & NA & NB & NC).
  assert (Nj : nftm j) by exact (wf_tm_nf Hj).
  assert (Hf : lwf (gL G) (mlvl l l' li)) by (cbn; repeat split; assumption).
  assert (Hkf : lwf (gL G) (lmax k (mlvl l l' li))) by (cbn; repeat split; assumption).
  assert (HΓ : [ G ; Γ ⊢[ i ] ]) by exact (ctx_of_wf_tm Hi Hj).
  assert (HAj : [ G ; Γ ⊢[ i ] A[lsingle j] @ l ]) by exact (wf_ty_single Hi HA Hj).
  pose proof (M_lift1 HA Hl Hj) as H1.
  (* the step at the index and the seed, and its projections *)
  assert (Hr : [ G ; Γ ⊢[ i ] c[lsingle2 j y]
                 : tySig l (lmax k (mlvl l l' li)) A[lsingle j] (mStepSnd l l' li X A B C k Y j)
                 @ lmax l (lmax k (mlvl l l' li)) ]).
  { pose proof (wf_tm_subst Hi Hc (lsub_wf_single2' Hi HΓ Hj Hy)) as X0.
    rewrite M_E_step in X0. exact X0. }
  assert (HSnd : [ G ; Γ ,, A[lsingle j] @ l ⊢[ i ] mStepSnd l l' li X A B C k Y j @ lmax k (mlvl l l' li) ])
    by exact (wf_ty_subst Hi (M_stepB_wf HS Hk HY) H1).
  assert (Hs : [ G ; Γ ⊢[ i ] mOutFst l l' li X A B C k Y c j y : A[lsingle j] @ l ])
    by (apply wf_fst; [exact Hv | exact Hl | exact Hkf | exact HAj | exact HSnd | exact Hr]).
  assert (Hsnd : [ G ; Γ ⊢[ i ] tmSnd l (lmax k (mlvl l l' li)) A[lsingle j] (mStepSnd l l' li X A B C k Y j)
                     c[lsingle2 j y]
                   : tyPi l' (lmax k (mlvl l l' li)) B[lsingle2 j (mOutFst l l' li X A B C k Y c j y)]
                       (tySum k (mlvl l l' li) Y⟨rlift ↑⟩[lsingle (mOutIdx l l' li X A B C k Y c j y)]
                          (tyM l l' li X⟨↑⟩ A⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩ C⟨rlift (rlift (rlift ↑))⟩
                             (mOutIdx l l' li X A B C k Y c j y)))
                   @ lmax l' (lmax k (mlvl l l' li)) ]).
  { eapply wf_lconv; [| exact (M_lv_kf _ _ _ _ _ Hl Hl' Hli Hk)].
    pose proof (wf_snd _ _ _ _ _ _ _ _ Hv Hl Hkf HAj HSnd Hr) as X0.
    rewrite M_E_snd in X0 by assumption. exact X0. }
  (* the positions' context [Γ, p : B[j, s]] and the child index there *)
  assert (Hjs : [ G ; Γ ⊢[ i ] lsingle2 j (mOutFst l l' li X A B C k Y c j y) : Γ ,, X @ li ,, A @ l ])
    by exact (lsub_wf_single2' Hi HΓ Hj Hs).
  assert (HBjs : [ G ; Γ ⊢[ i ] B[lsingle2 j (mOutFst l l' li X A B C k Y c j y)] @ l' ])
    by exact (wf_ty_subst Hi HB Hjs).
  assert (HΓ1 : [ G ; Γ ,, B[lsingle2 j (mOutFst l l' li X A B C k Y c j y)] @ l' ⊢[ i ] ])
    by exact (ext_wf Hi HBjs Hl').
  assert (Ho : [ G ; Γ ,, B[lsingle2 j (mOutFst l l' li X A B C k Y c j y)] @ l' ⊢[ i ]
                 mOutIdx l l' li X A B C k Y c j y : X⟨↑⟩ @ li ]).
  { assert (H1s : [ G ; Γ ,, B[lsingle2 j (mOutFst l l' li X A B C k Y c j y)] @ l' ⊢[ i ]
                    llift (lsingle2 j (mOutFst l l' li X A B C k Y c j y)) : Γ ,, X @ li ,, A @ l ,, B @ l' ])
      by (eapply (lsub_wf_lift' G i Hi); [exact Hjs | exact HBjs | exact Hl' | reflexivity]).
    pose proof (wf_tm_subst Hi HC H1s) as X0. rewrite M_E_X3s2 in X0 by exact NX. exact X0. }
  pose proof (MSig_wk1 HS HΓ1) as HS1.
  pose proof HS1 as (_ & _ & _ & HX1 & _).
  assert (HMB := M_ty_wf HS1 Ho).
  assert (HY1 := wk_under_ty Hi (ext_wf Hi HX1 Hli) HY).
  assert (HYA := wf_ty_single Hi HY1 Ho).
  assert (HSum := wft_sum _ _ _ _ _ _ _ Hv Hk Hf HYA HMB).
  (* the case's scrutinee: the step's second projection at the position *)
  assert (Hscr : [ G ; Γ ,, B[lsingle2 j (mOutFst l l' li X A B C k Y c j y)] @ l' ⊢[ i ]
                   app (tmSnd l (lmax k (mlvl l l' li)) A[lsingle j] (mStepSnd l l' li X A B C k Y j)
                          c[lsingle2 j y])⟨↑⟩
                     l' (lmax k (mlvl l l' li)) B[lsingle2 j (mOutFst l l' li X A B C k Y c j y)]⟨↑⟩
                     (tySum k (mlvl l l' li) Y⟨rlift ↑⟩[lsingle (mOutIdx l l' li X A B C k Y c j y)]
                        (tyM l l' li X⟨↑⟩ A⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩ C⟨rlift (rlift (rlift ↑))⟩
                           (mOutIdx l l' li X A B C k Y c j y)))⟨rlift ↑⟩
                     (var 0)
                   : tySum k (mlvl l l' li) Y⟨rlift ↑⟩[lsingle (mOutIdx l l' li X A B C k Y c j y)]
                       (tyM l l' li X⟨↑⟩ A⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩ C⟨rlift (rlift (rlift ↑))⟩
                          (mOutIdx l l' li X A B C k Y c j y))
                   @ lmax k (mlvl l l' li) ]).
  { assert (HB1 := M_wk_ty HBjs (wkr_shift1 _ _ _) HΓ1).
    assert (HΓ1B := ext_wf Hi HB1 Hl').
    eapply wf_tm_retype.
    - apply wf_app; [exact Hv | exact Hl' | exact Hkf | exact HB1 | exact (wk_under_ty Hi HΓ1B HSum)
                    | exact (M_wk_tm Hsnd (wkr_shift1 _ _ _) HΓ1)
                    | apply wf_var; [rewrite Hi; exact HΓ1 | constructor]].
    - apply M_E_r0, (wf_ty_nf HSum). }
  (* the branches: [corec] at the child from the carrier, and the node *)
  assert (HΓ1S := ext_wf Hi HSum Hkf).
  assert (HΓ1Y := ext_wf Hi HYA Hk).
  assert (HΓ1M := ext_wf Hi HMB Hf).
  assert (Hc1 : [ G ; Γ ,, B[lsingle2 j (mOutFst l l' li X A B C k Y c j y)] @ l'
                    ,, Y⟨rlift ↑⟩[lsingle (mOutIdx l l' li X A B C k Y c j y)] @ k ⊢[ i ]
                  tmCorec l l' li X⟨↑⟩⟨↑⟩ A⟨rlift ↑⟩⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩
                    C⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩ k Y⟨rlift ↑⟩⟨rlift ↑⟩
                    c⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩ (mOutIdx l l' li X A B C k Y c j y)⟨↑⟩ (var 0)
                  : (tyM l l' li X⟨↑⟩ A⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩ C⟨rlift (rlift (rlift ↑))⟩
                       (mOutIdx l l' li X A B C k Y c j y))⟨↑⟩ @ mlvl l l' li ]).
  { pose proof (MSig_wk1 HS1 HΓ1Y) as HS2.
    pose proof HS2 as (_ & _ & _ & HX2 & HA2 & HB2 & HC2).
    assert (HΓ1X := ext_wf Hi HX1 Hli).
    assert (HΓ1XY := ext_wf Hi HY1 Hk).
    assert (HΔX := ext_wf Hi HX2 Hli).
    assert (HY2 := wk_under_ty Hi HΔX HY1).
    assert (HΔXY := ext_wf Hi HY2 Hk).
    assert (Hc2 : [ G ; _ ⊢[ i ] c⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩ : _ @ _ ])
      by (eapply M_wk_tm; [eapply M_wk_tm; [exact Hc | wkr_tac | exact HΓ1XY] | wkr_tac | exact HΔXY]).
    rewrite M_E_stepwk in Hc2.
    apply wf_corec; auto using compt_self.
    - exact (M_wk_tm Ho (wkr_shift1 _ _ _) HΓ1Y).
    - eapply wf_tm_retype; [apply wf_var; [rewrite Hi; exact HΓ1Y | constructor] | apply M_E_seed]. }
  (* the λ over the positions *)
  unfold mOutCorec in Eq0. injection Eq0; intros; subst a0 b0. split; [exact Hs|].
  eapply wf_lconv; [| apply lequiv_sym, M_lv_f; assumption].
  apply wf_lam; [exact Hv | exact Hl' | exact Hf | exact HBjs |].
  eapply wf_tm_retype; [| apply shift_single_ty, (wf_ty_nf HMB)].
  apply wf_case; [exact Hv | exact Hk | exact Hf | exact Hf | exact HYA | exact HMB
                 | exact (M_wk_ty HMB (wkr_shift1 _ _ _) HΓ1S) | | | exact Hscr].
  - rewrite M_E_mot. exact Hc1.
  - rewrite M_E_mot. apply wf_var; [rewrite Hi; exact HΓ1M | constructor].
Qed.


Lemma pre_out_corec {Γ l l' li X A B C k Y c j y} : MSig Γ l l' li X A B C -> lwf (gL G) k ->
  [ G ; Γ ,, X @ li ⊢[ i ] Y @ k ] ->
  [ G ; Γ ,, X @ li ,, Y @ k ⊢[ i ] c : (mStepTy l l' li X A B C k Y)⟨↑⟩ @ lmax l (lmax k (mlvl l l' li)) ] ->
  [ G ; Γ ⊢[ i ] j : X @ li ] -> [ G ; Γ ⊢[ i ] y : Y[lsingle j] @ k ] ->
  [ G ; Γ ⊢[ i ] mOutCorec l l' li X A B C k Y c j y : mOutTy l l' li X A B C j @ lmax l (mlvl l l' li) ].
Proof using Hi Hv.
  intros HS Hk HY Hc Hj Hy.
  pose proof HS as (Hl & Hl' & Hli & HX & HA & HB & HC).
  pose proof (MSig_nf HS) as (NX & NA & NB & NC).
  assert (Nj : nftm j) by exact (wf_tm_nf Hj).
  assert (Hf : lwf (gL G) (mlvl l l' li)) by (cbn; repeat split; assumption).
  destruct (pre_out_corec_parts HS Hk HY Hc Hj Hy _ _ _ ltac:(unfold mOutCorec; reflexivity)) as [Hs Hb].
  unfold mOutCorec.
  apply wf_pair; [exact Hv | exact Hl | exact Hf | exact (wf_ty_single Hi HA Hj) | exact (M_outB_wf HS Hj) | exact Hs |].
  rewrite M_E_pair by assumption. exact Hb.
Qed.

End MAux.
