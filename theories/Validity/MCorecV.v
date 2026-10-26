(** * Validity of [corec], the depth induction (M18_DESIGN.md, M18b)

    Related [corec]s, at related premises, are related at [M] at every
    depth [n]: at depth [S n] their [out]s step to [mOutCorec]'s pairs,
    whose first components are the steps' first projections and whose
    second components' applications [case] on the steps' continuations,
    a further [corec] (related at depth [n] by the induction hypothesis)
    or a finished [M] term (related at every depth). *)
From DeLaM.Validity Require Export MCorec.
From DeLaM.Validity Require Import RelIntro MStepV.
From DeLaM.LogRel Require Import MAux MIdx.
From DeLaM.Typing Require Import PresupM.

Local Ltac mfold := repeat change (ren_ty ?x ?r) with x⟨r⟩; repeat change (subst_ty ?x ?e) with x[e];
  repeat change (ren_tm ?x ?r) with x⟨r⟩; repeat change (subst_tm ?x ?e) with x[e].
Local Ltac meq' := meq; repeat (rewrite ?Nat.add_0_r, ?llk_llift; mfold; meq).

(** The step type at an index is a [Σ] over the second component. *)
Lemma mStepTy_single l l' li X A B C k Y j :
  (mStepTy l l' li X A B C k Y)[lsingle j] =
  tySig l (lmax k (mlvl l l' li)) A[lsingle j] (mStepSnd l l' li X A B C k Y j).
Proof using . reflexivity. Qed.

(** The step's continuation type at a position. *)
Lemma mSum_single l l' li k (X A B Y : ty) (C j s p : tm) :
  nfty X -> nfty A -> nfty B -> nfty Y -> nftm C -> nftm j -> nftm s ->
  (tySum k (mlvl l l' li) Y⟨rlift ↑⟩[lsingle C[llift (lsingle2 j s)]]
     (tyM l l' li X⟨↑⟩ A⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩ C⟨rlift (rlift (rlift ↑))⟩ C[llift (lsingle2 j s)]))[lsingle p] =
  tySum k (mlvl l l' li) Y[lsingle C[lsingle3 j s p]] (tyM l l' li X A B C C[lsingle3 j s p]).
Proof using . intros. meq'. Qed.

(** The step type and the seed past one more local. *)
Lemma mStepTy_wk l l' li X A B C k Y :
  (mStepTy l l' li X A B C k Y)⟨↑⟩⟨rlift (rlift ↑)⟩ =
  (mStepTy l l' li X⟨↑⟩ A⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩ C⟨rlift (rlift (rlift ↑))⟩ k Y⟨rlift ↑⟩)⟨↑⟩.
Proof using . meq'. Qed.
Lemma seed_wk (Y : ty) o : (Y[lsingle o])⟨↑⟩ = Y⟨rlift ↑⟩[lsingle o⟨↑⟩].
Proof using . meq'. Qed.

Local Ltac wkr_tac := repeat (eapply wkr_up'; [|reflexivity]); apply wkr_shift1.

Section MCorecV.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.
(** The pieces of β's reduct's [case] at a child index [o]: the
    summands, the motive, the branches. *)
Lemma case_parts {G Γ l l' li X A B C kc Y c o} :
  MSig (G := G) (i := ge_layer) Γ l l' li X A B C -> lwf (gL G) kc ->
  [ G ; Γ ,, X @ li ⊢g Y @ kc ] ->
  [ G ; Γ ,, X @ li ,, Y @ kc ⊢g c : (mStepTy l l' li X A B C kc Y)⟨↑⟩ @ lmax l (lmax kc (mlvl l l' li)) ] ->
  [ G ; Γ ⊢g o : X @ li ] ->
  [ G ; Γ ⊢g Y[lsingle o] @ kc ] /\ [ G ; Γ ⊢g tyM l l' li X A B C o @ mlvl l l' li ] /\
  [ G ; Γ ,, tySum kc (mlvl l l' li) Y[lsingle o] (tyM l l' li X A B C o) @ lmax kc (mlvl l l' li)
      ⊢g (tyM l l' li X A B C o)⟨↑⟩ @ mlvl l l' li ] /\
  [ G ; Γ ,, Y[lsingle o] @ kc ⊢g tmCorec l l' li X⟨↑⟩ A⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩ C⟨rlift (rlift (rlift ↑))⟩
       kc Y⟨rlift ↑⟩ c⟨rlift (rlift ↑)⟩ o⟨↑⟩ (var 0) : (tyM l l' li X A B C o)⟨↑⟩ @ mlvl l l' li ] /\
  [ G ; Γ ,, tyM l l' li X A B C o @ mlvl l l' li ⊢g var 0 : (tyM l l' li X A B C o)⟨↑⟩ @ mlvl l l' li ].
Proof using EL.
  intros HS Hk HY Hc Ho.
  pose proof HS as (Hl & Hl' & Hli & HX & HA & HB & HC).
  assert (Hf : lwf (gL G) (mlvl l l' li)) by (cbn; repeat split; assumption).
  pose proof (wf_ty_single ge_typeof HY Ho) as HYo.
  pose proof (M_ty_wf ge_typeof ge_notV HS Ho) as HMo.
  pose proof (wft_sum _ _ _ _ _ _ _ ge_notV Hk Hf HYo HMo) as HSum.
  pose proof (ext_wf_g HSum (lwf_max Hk Hf)) as HΓS.
  pose proof (ext_wf_g HYo Hk) as HΓY. pose proof (ext_wf_g HMo Hf) as HΓM.
  refine (conj HYo (conj HMo (conj (M_wk_ty ge_typeof HMo (wkr_shift1 _ _ _) HΓS) (conj _ _)))).
  - pose proof (MSig_wk1 ge_typeof ge_notV HS HΓY) as HS1.
    pose proof HS1 as (_ & _ & _ & HX1 & HA1 & HB1 & HC1).
    pose proof (ext_wf_g HX1 Hli) as HΓYX.
    pose proof (wk_under_ty ge_typeof HΓYX HY) as HY1.
    pose proof (ext_wf_g HY1 Hk) as HΓYXY.
    assert (Hc1 : [ G ; Γ ,, Y[lsingle o] @ kc ,, X⟨↑⟩ @ li ,, Y⟨rlift ↑⟩ @ kc ⊢g c⟨rlift (rlift ↑)⟩
                    : (mStepTy l l' li X⟨↑⟩ A⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩ C⟨rlift (rlift (rlift ↑))⟩ kc Y⟨rlift ↑⟩)⟨↑⟩
                    @ lmax l (lmax kc (mlvl l l' li)) ]).
    { rewrite <- mStepTy_wk. eapply (M_wk_tm ge_typeof); [exact Hc | wkr_tac | exact HΓYXY]. }
    eapply wf_tm_retype; [apply wf_corec; auto using ge_compt |].
    + exact (M_wk_tm ge_typeof Ho (wkr_shift1 _ _ _) HΓY).
    + rewrite <- seed_wk. apply wf_var; [rewrite ge_typeof; exact HΓY | constructor].
    + reflexivity.
  - apply wf_var; [rewrite ge_typeof; exact HΓM | constructor].
Qed.


(** ** [case] at a non-dependent motive, typed

    β's reduct cases at the motive [M(o)⟨↑⟩]: the scrutinee's reduct
    decides the branch, as in [V_case]. *)
Lemma shift_inj_single (T : ty) u : T⟨↑⟩⟨rlift ↑⟩[lsingle u] = T⟨↑⟩.
Proof using . rewrite shift_lift_ty. apply shift_single_ty, ren_nf_ty. Qed.

Lemma case_red_inl {G Δ k f Ya Mb c1 c2 e k1 k2 C D a} :
  lwf (gL G) k -> lwf (gL G) f -> [ G ; Δ ⊢g Ya @ k ] -> [ G ; Δ ⊢g Mb @ f ] ->
  [ G ; Δ ,, tySum k f Ya Mb @ lmax k f ⊢g Mb⟨↑⟩ @ f ] ->
  [ G ; Δ ,, Ya @ k ⊢g c1 : Mb⟨↑⟩ @ f ] -> [ G ; Δ ,, Mb @ f ⊢g c2 : Mb⟨↑⟩ @ f ] ->
  [ G ; Δ ⊢g e ⤳* tmInl k1 k2 C D a : tySum k f Ya Mb @ lmax k f ] ->
  lequiv (gL G) k1 k -> lequiv (gL G) k2 f -> [ G ; Δ ⊢g Ya ≅ C @ k ] -> [ G ; Δ ⊢g Mb ≅ D @ f ] ->
  [ G ; Δ ⊢g a : Ya @ k ] ->
  [ G ; Δ ⊢g tmCase k f f Ya Mb Mb⟨↑⟩ c1 c2 e ⤳* c1[lsingle a] : Mb @ f ].
Proof using EL.
  intros Hk Hf HY HM HM1 Hc1 Hc2 Hr H1 H2 HC HD Ha. pose proof (wf_ty_nf HM) as NM.
  rewrite <- (shift_inj_single Mb (tmInl k f Ya⟨↑⟩ Mb⟨↑⟩ (var 0))) in Hc1.
  rewrite <- (shift_inj_single Mb (tmInr k f Ya⟨↑⟩ Mb⟨↑⟩ (var 0))) in Hc2.
  pose proof (case_inl_eq Hk Hf Hf HY HM HM1 Hc1 Hc2 (tmred_eq _ _ _ _ _ _ _ Hr) H1 H2 HC HD Ha) as Eq.
  rewrite (shift_single_ty _ _ NM) in Eq.
  split; [exact (eqtm_wf_l ge_typeof Eq) | | exact Eq].
  eapply reds_trans; [apply reds_case, (tmred_red _ _ _ _ _ _ _ Hr)|].
  econstructor; [apply red_case_inl | constructor].
Qed.

Lemma case_red_inr {G Δ k f Ya Mb c1 c2 e k1 k2 C D b} :
  lwf (gL G) k -> lwf (gL G) f -> [ G ; Δ ⊢g Ya @ k ] -> [ G ; Δ ⊢g Mb @ f ] ->
  [ G ; Δ ,, tySum k f Ya Mb @ lmax k f ⊢g Mb⟨↑⟩ @ f ] ->
  [ G ; Δ ,, Ya @ k ⊢g c1 : Mb⟨↑⟩ @ f ] -> [ G ; Δ ,, Mb @ f ⊢g c2 : Mb⟨↑⟩ @ f ] ->
  [ G ; Δ ⊢g e ⤳* tmInr k1 k2 C D b : tySum k f Ya Mb @ lmax k f ] ->
  lequiv (gL G) k1 k -> lequiv (gL G) k2 f -> [ G ; Δ ⊢g Ya ≅ C @ k ] -> [ G ; Δ ⊢g Mb ≅ D @ f ] ->
  [ G ; Δ ⊢g b : Mb @ f ] ->
  [ G ; Δ ⊢g tmCase k f f Ya Mb Mb⟨↑⟩ c1 c2 e ⤳* c2[lsingle b] : Mb @ f ].
Proof using EL.
  intros Hk Hf HY HM HM1 Hc1 Hc2 Hr H1 H2 HC HD Hb. pose proof (wf_ty_nf HM) as NM.
  rewrite <- (shift_inj_single Mb (tmInl k f Ya⟨↑⟩ Mb⟨↑⟩ (var 0))) in Hc1.
  rewrite <- (shift_inj_single Mb (tmInr k f Ya⟨↑⟩ Mb⟨↑⟩ (var 0))) in Hc2.
  pose proof (case_inr_eq Hk Hf Hf HY HM HM1 Hc1 Hc2 (tmred_eq _ _ _ _ _ _ _ Hr) H1 H2 HC HD Hb) as Eq.
  rewrite (shift_single_ty _ _ NM) in Eq.
  split; [exact (eqtm_wf_l ge_typeof Eq) | | exact Eq].
  eapply reds_trans; [apply reds_case, (tmred_red _ _ _ _ _ _ _ Hr)|].
  econstructor; [apply red_case_inr | constructor].
Qed.

Lemma case_red_ne {G Δ k f Ya Mb c1 c2 e ν} :
  lwf (gL G) k -> lwf (gL G) f -> [ G ; Δ ⊢g Ya @ k ] -> [ G ; Δ ⊢g Mb @ f ] ->
  [ G ; Δ ,, tySum k f Ya Mb @ lmax k f ⊢g Mb⟨↑⟩ @ f ] ->
  [ G ; Δ ,, Ya @ k ⊢g c1 : Mb⟨↑⟩ @ f ] -> [ G ; Δ ,, Mb @ f ⊢g c2 : Mb⟨↑⟩ @ f ] ->
  [ G ; Δ ⊢g e ⤳* ν : tySum k f Ya Mb @ lmax k f ] ->
  [ G ; Δ ⊢g tmCase k f f Ya Mb Mb⟨↑⟩ c1 c2 e ⤳* tmCase k f f Ya Mb Mb⟨↑⟩ c1 c2 ν : Mb @ f ].
Proof using EL.
  intros Hk Hf HY HM HM1 Hc1 Hc2 Hr. pose proof (wf_ty_nf HM) as NM.
  rewrite <- (shift_inj_single Mb (tmInl k f Ya⟨↑⟩ Mb⟨↑⟩ (var 0))) in Hc1.
  rewrite <- (shift_inj_single Mb (tmInr k f Ya⟨↑⟩ Mb⟨↑⟩ (var 0))) in Hc2.
  pose proof (case_cong Hk Hf Hf HY HM HM1 Hc1 Hc2 (tmred_eq _ _ _ _ _ _ _ Hr)) as Eq.
  rewrite (shift_single_ty _ _ NM) in Eq.
  split; [exact (eqtm_wf_l ge_typeof Eq) | apply reds_case, (tmred_red _ _ _ _ _ _ _ Hr) | exact Eq].
Qed.


(** A child's type at a position. *)
Lemma kid_single l l' li (X A B : ty) (C j a p : tm) :
  nfty X -> nfty A -> nfty B -> nftm C -> nftm j -> nftm a ->
  (tyM l l' li X⟨↑⟩ A⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩ C⟨rlift (rlift (rlift ↑))⟩ C[llift (lsingle2 j a)])[lsingle p] =
  tyM l l' li X A B C C[lsingle3 j a p].
Proof using . intros. meq'. Qed.

(** ** β's reduct applied to a position: its λ's β. *)
Lemma lam_app_red {G Γ l l' li X A B C kc Y c j y p la lb A1 B1} :
  MSig (G := G) (i := ge_layer) Γ l l' li X A B C -> lwf (gL G) kc ->
  [ G ; Γ ,, X @ li ⊢g Y @ kc ] ->
  [ G ; Γ ,, X @ li ,, Y @ kc ⊢g c : (mStepTy l l' li X A B C kc Y)⟨↑⟩ @ lmax l (lmax kc (mlvl l l' li)) ] ->
  [ G ; Γ ⊢g j : X @ li ] -> [ G ; Γ ⊢g y : Y[lsingle j] @ kc ] ->
  [ G ; Γ ⊢g p : B[lsingle2 j (mOutFst l l' li X A B C kc Y c j y)] @ l' ] ->
  lequiv (gL G) la l' -> lequiv (gL G) lb (mlvl l l' li) ->
  [ G ; Γ ⊢g B[lsingle2 j (mOutFst l l' li X A B C kc Y c j y)] ≅ A1 @ l' ] ->
  [ G ; Γ ,, B[lsingle2 j (mOutFst l l' li X A B C kc Y c j y)] @ l'
      ⊢g tyM l l' li X⟨↑⟩ A⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩ C⟨rlift (rlift (rlift ↑))⟩
           C[llift (lsingle2 j (mOutFst l l' li X A B C kc Y c j y))] ≅ B1 @ mlvl l l' li ] ->
  [ G ; Γ ⊢g app (mLam l l' li X A B C kc Y c j y) la lb A1 B1 p
      ⤳* (mBody l l' li X A B C kc Y c j y)[lsingle p]
      : tyM l l' li X A B C (mIdxP l l' li X A B C kc Y c j y p) @ mlvl l l' li ].
Proof using EL.
  intros HS Hk HY Hc Hj Hy Hp Hla Hlb HA1 HB1.
  pose proof HS as (Hl & Hl' & Hli & HX & HA & HB & HC).
  assert (Hf : lwf (gL G) (mlvl l l' li)) by (cbn; repeat split; assumption).
  destruct (pre_out_corec_parts ge_typeof ge_notV HS Hk HY Hc Hj Hy _ _ (mBody l l' li X A B C kc Y c j y)
              ltac:(unfold mOutCorec, mBody; reflexivity)) as (Ha & HBa & Hb).
  pose proof (eqty_wf_l ge_typeof HB1) as HB0.
  pose proof (tmred_beta Hl' Hf Hla Hlb HBa HB0 Hb Hp HA1 HB1) as R.
  rewrite kid_single in R by first [exact (wf_ty_nf HX) | exact (wf_ty_nf HA) | exact (wf_ty_nf HB)
                                   | exact (wf_tm_nf HC) | exact (wf_tm_nf Hj) | exact (wf_tm_nf Ha)].
  exact R.
Qed.


(** ** β's reduct's projections *)
Lemma out_parts {G Γ l l' li X A B C kc Y c j y} :
  MSig (G := G) (i := ge_layer) Γ l l' li X A B C -> lwf (gL G) kc ->
  [ G ; Γ ,, X @ li ⊢g Y @ kc ] ->
  [ G ; Γ ,, X @ li ,, Y @ kc ⊢g c : (mStepTy l l' li X A B C kc Y)⟨↑⟩ @ lmax l (lmax kc (mlvl l l' li)) ] ->
  [ G ; Γ ⊢g j : X @ li ] -> [ G ; Γ ⊢g y : Y[lsingle j] @ kc ] ->
  [ G ; Γ ⊢g A[lsingle j] @ l ] /\
  [ G ; Γ ,, A[lsingle j] @ l ⊢g tyPi l' (mlvl l l' li) B[llift (lsingle j)] (mKidTy l l' li X A B C j) @ mlvl l l' li ] /\
  [ G ; Γ ⊢g mOutFst l l' li X A B C kc Y c j y : A[lsingle j] @ l ] /\
  [ G ; Γ ⊢g mLam l l' li X A B C kc Y c j y
      : (tyPi l' (mlvl l l' li) B[llift (lsingle j)] (mKidTy l l' li X A B C j))[lsingle (mOutFst l l' li X A B C kc Y c j y)]
      @ mlvl l l' li ].
Proof using EL.
  intros HS Hk HY Hc Hj Hy.
  pose proof HS as (Hl & Hl' & Hli & HX & HA & HB & HC).
  pose proof (MSig_nf HS) as (NX & NA & NB & NC).
  assert (Hf : lwf (gL G) (mlvl l l' li)) by (cbn; repeat split; assumption).
  destruct (pre_out_corec_parts ge_typeof ge_notV HS Hk HY Hc Hj Hy _ _ (mBody l l' li X A B C kc Y c j y)
              ltac:(unfold mOutCorec, mBody; reflexivity)) as (Ha & HBa & Hb).
  assert (Nj : nftm j) by exact (wf_tm_nf Hj).
  refine (conj (wf_ty_single ge_typeof HA Hj) (conj (M_outB_wf ge_typeof ge_notV HS Hj) (conj Ha _))).
  rewrite M_E_pair by assumption.
  eapply wf_lconv; [| apply lequiv_sym, M_lv_f; assumption].
  unfold mLam. apply wf_lam; auto using ge_notV.
Qed.

Section OutProj.
Context {G : gctx} {Γ : ctx} {l l' li : lvl} {X A B : ty} {C : tm} {kc : lvl} {Y : ty} {c j y : tm}
  {la lb : lvl} {A1 B1 : ty}
  (HS : MSig (G := G) (i := ge_layer) Γ l l' li X A B C) (Hk : lwf (gL G) kc)
  (HY : [ G ; Γ ,, X @ li ⊢g Y @ kc ])
  (Hc : [ G ; Γ ,, X @ li ,, Y @ kc ⊢g c : (mStepTy l l' li X A B C kc Y)⟨↑⟩ @ lmax l (lmax kc (mlvl l l' li)) ])
  (Hj : [ G ; Γ ⊢g j : X @ li ]) (Hy : [ G ; Γ ⊢g y : Y[lsingle j] @ kc ])
  (Hla : lequiv (gL G) la l) (Hlb : lequiv (gL G) lb (mlvl l l' li))
  (HA1 : [ G ; Γ ⊢g A[lsingle j] ≅ A1 @ l ])
  (HB1 : [ G ; Γ ,, A[lsingle j] @ l ⊢g tyPi l' (mlvl l l' li) B[llift (lsingle j)] (mKidTy l l' li X A B C j)
           ≅ B1 @ mlvl l l' li ]).

Lemma out_fst_red :
  [ G ; Γ ⊢g tmFst la lb A1 B1 (mOutCorec l l' li X A B C kc Y c j y) ⤳* mOutFst l l' li X A B C kc Y c j y
      : A[lsingle j] @ l ].
Proof using EL HS Hk HY Hc Hj Hy Hla Hlb HA1 HB1.
  pose proof HS as (Hl & Hl' & Hli & _).
  assert (Hf : lwf (gL G) (mlvl l l' li)) by (cbn; repeat split; assumption).
  destruct (out_parts HS Hk HY Hc Hj Hy) as (HA0 & HB0 & Ha & Hb).
  rewrite mOutCorec_pair. exact (tmred_fst_beta Hl Hf Hla Hlb HA0 HB0 Ha Hb HA1 HB1).
Qed.

Lemma out_snd_red :
  [ G ; Γ ⊢g tmSnd la lb A1 B1 (mOutCorec l l' li X A B C kc Y c j y) ⤳* mLam l l' li X A B C kc Y c j y
      : tyPi l' (mlvl l l' li) B[lsingle2 j (tmFst la lb A1 B1 (mOutCorec l l' li X A B C kc Y c j y))]
          (tyM l l' li X⟨↑⟩ A⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩ C⟨rlift (rlift (rlift ↑))⟩
             C[llift (lsingle2 j (tmFst la lb A1 B1 (mOutCorec l l' li X A B C kc Y c j y)))])
      @ lmax l' (mlvl l l' li) ].
Proof using EL HS Hk HY Hc Hj Hy Hla Hlb HA1 HB1.
  pose proof HS as (Hl & Hl' & Hli & _).
  pose proof (MSig_nf HS) as (NX & NA & NB & NC). assert (Nj : nftm j) by exact (wf_tm_nf Hj).
  assert (Hf : lwf (gL G) (mlvl l l' li)) by (cbn; repeat split; assumption).
  destruct (out_parts HS Hk HY Hc Hj Hy) as (HA0 & HB0 & Ha & Hb).
  pose proof (tmred_eq _ _ _ _ _ _ _ out_fst_red) as Ef.
  pose proof (eqtm_wf_l ge_typeof Ef) as Hx.
  pose proof (wf_ty_func ge_typeof HB0 (lsub_eq_single ge_typeof Ha Hx (eqtm_sym _ _ _ _ _ _ _ Ef))) as EB.
  rewrite mOutCorec_pair in Hx, EB |- *.
  pose proof (tmred_conv _ _ _ _ _ ge_typeof (tmred_snd_beta Hl Hf Hla Hlb HA0 HB0 Ha Hb HA1 HB1) EB) as R.
  rewrite M_E_pair in R by assumption.
  exact (tmred_lconv _ _ _ _ _ R (M_lv_f _ _ _ _ Hl Hl' Hli)).
Qed.

End OutProj.

(** ** The λ's application annotations, from a shape to an equal one *)
Lemma single2_split (B : ty) j a : nftm j -> B[llift (lsingle j)][lsingle a] = B[lsingle2 j a].
Proof using . intros. meq'. Qed.
Lemma single2_split_tm (C : tm) j a : nftm j -> C[llift (llift (lsingle j))][llift (lsingle a)] = C[llift (lsingle2 j a)].
Proof using . intros. meq'. Qed.

Lemma ann_conv {G Γ l l' li X A B C j a1 a2 A1 B1} :
  MSig (G := G) (i := ge_layer) Γ l l' li X A B C -> [ G ; Γ ⊢g j : X @ li ] ->
  [ G ; Γ ⊢g a1 ≅ a2 : A[lsingle j] @ l ] ->
  [ G ; Γ ⊢ B[lsingle2 j a2] ≈ A1 @ l' ] ->
  [ G ; Γ ,, B[lsingle2 j a2] @ l' ⊢ tyM l l' li X⟨↑⟩ A⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩ C⟨rlift (rlift (rlift ↑))⟩
                                       C[llift (lsingle2 j a2)] ≈ B1 @ mlvl l l' li ] ->
  [ G ; Γ ⊢g B[lsingle2 j a1] ≅ A1 @ l' ] /\
  [ G ; Γ ,, B[lsingle2 j a1] @ l' ⊢g tyM l l' li X⟨↑⟩ A⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩ C⟨rlift (rlift (rlift ↑))⟩
                                        C[llift (lsingle2 j a1)] ≅ B1 @ mlvl l l' li ].
Proof using EL.
  intros HS Hj Ea HA1 HB1.
  pose proof HS as (Hl & Hl' & Hli & HX & HA & HB & HC).
  pose proof (wf_tm_nf Hj) as Nj.
  pose proof (M_lift1 ge_typeof HA Hl Hj) as H1.
  pose proof (wf_ty_single ge_typeof HA Hj) as HAj.
  pose proof (wf_ty_subst ge_typeof HB H1) as HBj.
  pose proof (eqtm_wf_l ge_typeof Ea) as Ha1. pose proof (eqtm_wf_r ge_typeof Ea) as Ha2.
  pose proof (lsub_eq_single ge_typeof Ha1 Ha2 Ea) as Es.
  pose proof (wf_ty_func ge_typeof HBj Es) as EB0. rewrite !single2_split in EB0 by exact Nj.
  split; [exact (eqty_trans _ _ _ _ _ _ _ EB0 (geq_ty_sound HA1)) |].
  pose proof (eqty_wf_l ge_typeof EB0) as HBa1.
  pose proof (ext_wf_g HAj Hl) as HΓ1. pose proof (ext_wf_g HBj Hl') as HΓ2.
  assert (H2 : [ G ; Γ ,, A[lsingle j] @ l ,, B[llift (lsingle j)] @ l' ⊢[ ge_layer ] llift (llift (lsingle j))
                 : Γ ,, X @ li ,, A @ l ,, B @ l' ])
    by (eapply (lsub_wf_lift' G ge_layer ge_typeof); [exact H1 | exact HBj | exact Hl' | reflexivity]).
  assert (HCj : [ G ; Γ ,, A[lsingle j] @ l ,, B[llift (lsingle j)] @ l' ⊢g C[llift (llift (lsingle j))]
                  : X⟨↑⟩⟨↑⟩ @ li ])
    by (eapply wf_tm_retype; [exact (wf_tm_subst ge_typeof HC H2) | apply M_E_X3j, (wf_ty_nf HX)]).
  assert (Es2 : [ G ; Γ ,, B[lsingle2 j a1] @ l' ⊢[ ge_layer ] llift (lsingle a1) ≅ llift (lsingle a2)
                  : Γ ,, A[lsingle j] @ l ,, B[llift (lsingle j)] @ l' ]).
  { eapply (lsub_eq_lift_g G ge_layer); rewrite ?ge_typeof.
    - exact Es.
    - exact HBa1.
    - exact Hl'.
    - rewrite !single2_split by exact Nj. exact EB0.
    - symmetry. apply single2_split, Nj. }
  pose proof (wf_tm_func ge_typeof HCj Es2) as EC.
  rewrite !single2_split_tm in EC by exact Nj.
  pose proof (ext_wf_g HBa1 Hl') as HΓB.
  pose proof (MSig_wk1 ge_typeof ge_notV HS HΓB) as HS1.
  pose proof (eqtm_wf_l ge_typeof EC) as Hix.
  assert (EX : (X⟨↑⟩⟨↑⟩)[llift (lsingle a1)] = X⟨↑⟩) by (pose proof (wf_ty_nf HX); meq').
  rewrite EX in EC, Hix.
  pose proof (MEq_of_MAnn HS1 (MAnn_refl HS1 Hix)) as HE1.
  pose proof (M_ty_eq ge_typeof ge_notV HE1 EC) as EM.
  pose proof (geq_ty_ctxconv (eqty_sym _ _ _ _ _ _ EB0) (lequiv_refl _ _ Hl') HΓB HB1) as HB1'.
  exact (eqty_trans _ _ _ _ _ _ _ EM (geq_ty_sound HB1')).
Qed.


(** The [corec] branch at a payload. *)
Lemma br_single l l' li (X A B : ty) (C : tm) k (Y : ty) (c o b : tm) :
  nfty X -> nfty A -> nfty B -> nftm C -> nfty Y -> nftm c -> nftm o ->
  (tmCorec l l' li X⟨↑⟩ A⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩ C⟨rlift (rlift (rlift ↑))⟩ k Y⟨rlift ↑⟩
     c⟨rlift (rlift ↑)⟩ o⟨↑⟩ (var 0))[lsingle b] = tmCorec l l' li X A B C k Y c o b.
Proof using . intros. meq'. Qed.


(** The types of related terms are generically equal. *)
Lemma LRtm_tyeq {l0 G Γ T T' t t'} : LRtm l0 G Γ T T' t t' -> [ G ; Γ ⊢ T ≈ T' @ l0 ].
Proof using EL. intros (R & HR & _). exact (proj2 (proj2 (escape_ty _ _ _ _ _ _ _ _ HR))). Qed.
Lemma LRty_tyeq {l0 G Γ T T'} : LRty l0 G Γ T T' -> [ G ; Γ ⊢ T ≈ T' @ l0 ].
Proof using EL. intros (R & HR). exact (proj2 (proj2 (escape_ty _ _ _ _ _ _ _ _ HR))). Qed.

Lemma ktyl_tyPi {G Γ} (ρ : kwk G Γ) l l' A B : ktyl ρ (tyPi l l' A B) = tyPi l l' (ktyl ρ A) (ktyll ρ B).
Proof using . unfold ktyl, ktyll. now rewrite gwa_tyPi. Qed.

Lemma ktmll_self {G Γ} (HΓ : [ G ; Γ ⊢g ]) t : nftm t -> ktmll (kw_self HΓ) t = t.
Proof using .
  intros H. unfold ktmll, kw_self, kw_loc; cbn [kw_γ kw_gk kw_r kw_rk gwa wk_ren kw_mk].
  rewrite <- (ren_id_tm t H) at 2. apply ren_ext_tm. intros [|[|n]]; rlk_simpl; cbn; lia.
Qed.

(** [MObs] along included shapes' relations and including positions'
    relations, as [MRn_impl]. *)
Lemma MObs_impl n {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C'}
    (shR shR' : MShRel G Γ) (posR posR' : MPosRel G Γ) m m' t t' :
  (forall ρ x x' a a', shR ρ x x' a a' -> shR' ρ x x' a a') ->
  (forall ρ x x' a a' p p', posR' ρ x x' a a' p p' -> posR ρ x x' a a' p p') ->
  MObs (MRn n) G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' shR posR m m' t t' ->
  MObs (MRn n) G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' shR' posR' m m' t t'.
Proof using .
  intros Hs Hp Ho; unfold MObs; intros * HA HA'.
  eapply SigRel_impl; [| | exact (Ho _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HA HA')].
  - intros ρ a a'. apply Hs.
  - intros ρ a a' h h' u u'. apply PiRel_impl.
    + intros ρ' p p'. apply Hp.
    + intros ρ' p p' hp hp' v v'. apply MRn_impl; intros *; [apply Hs | apply Hp].
Qed.

(** A child's type in a world. *)
(** [MOutR] at every depth is [MOutR] at [MR], as in [MR_out]. *)
Lemma MOutR_lim {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' shR posR m m' u u'} :
  (forall n, MOutR (MRn n) G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' shR posR m m' u u') ->
  MOutR MR G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' shR posR m m' u u'.
Proof using .
  intros Hn. unfold MOutR in Hn |- *. refine (SigRel_lim _ _ Hn).
  - intros n ρ0 a a' h h' v v' Hv. exact Hv.
  - intros ρ0 a a' h v v' Hv. refine (PiRel_lim _ Hv).
    intros ρ' p p' hp w w' Hw n. exact (Hw n).
Qed.

Lemma kw_kid {G Γ} (ρ : kwk G Γ) l l' li (X A B : ty) (C j a : tm) :
  ktyl ρ (tyM l l' li X⟨↑⟩ A⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩ C⟨rlift (rlift (rlift ↑))⟩ C[llift (lsingle2 j a)]) =
  tyM l l' li (kty ρ X)⟨↑⟩ (ktyl ρ A)⟨rlift ↑⟩ (ktyll ρ B)⟨rlift (rlift ↑)⟩ (ktmlll ρ C)⟨rlift (rlift (rlift ↑))⟩
    (ktmlll ρ C)[llift (lsingle2 (ktm ρ j) (ktm ρ a))].
Proof using .
  unfold ktyl, ktyll, kty, ktmlll, ktm. rewrite gwa_tyM, !gwa_ren_ty, !gwa_ren, gwa_subst.
  rewrite (subst_ext _ (llift (lsingle2 j a))⟦kw_γ ρ⟧ (llift (lsingle2 j⟦kw_γ ρ⟧ a⟦kw_γ ρ⟧)))
    by (intros n; rewrite llk_llift_gwa, gwa_lsingle2; reflexivity).
  meq. all: now rewrite ?Nat.add_0_r.
Qed.

(** ** [corec] at related premises *)

Section CorecV.
Context {G : gctx} {Γ : ctx} {l l' li k k' ki kc kc' : lvl} {X X' A A' B B' Y Y' : ty} {C C' c c' : tm}
  (Hwl : lwf (gL G) l) (Hwl' : lwf (gL G) l') (Hwli : lwf (gL G) li) (Hwc : lwf (gL G) kc)
  (Hk : lequiv (gL G) k l) (Hk' : lequiv (gL G) k' l') (Hki : lequiv (gL G) ki li) (Hkc : lequiv (gL G) kc' kc)
  (VX : VTyG G Γ X X' li) (VA : VTyG G (Γ ,, X @ li) A A' l)
  (VB : VTyG G (Γ ,, X @ li ,, A @ l) B B' l')
  (VC : VTmG G (Γ ,, X @ li ,, A @ l ,, B @ l') C C' X⟨↑⟩⟨↑⟩⟨↑⟩ li)
  (VY : VTyG G (Γ ,, X @ li) Y Y' kc)
  (Vstep : VTyG G (Γ ,, X @ li) (mStepTy l l' li X A B C kc Y) (mStepTy k k' ki X' A' B' C' kc' Y')
             (lmax l (lmax kc (mlvl l l' li))))
  (Vc : VTmG G (Γ ,, X @ li ,, Y @ kc) c c' (mStepTy l l' li X A B C kc Y)⟨↑⟩ (lmax l (lmax kc (mlvl l l' li))))
  {Δ : ctx} {d d' : lsub} (Hd : SubRel G Γ Δ d d').

Let Lc := lmax l (lmax kc (mlvl l l' li)).
Let Nd := proj1 (SubRel_nf _ _ _ _ _ Hd).
Let Nd' := proj2 (SubRel_nf _ _ _ _ _ Hd).

(** The premises in a world [U], at [d] and at [d']. *)
Local Notation sX U := (kty U X[d]).
Local Notation sA U := (ktyl U A[llift d]).
Local Notation sB U := (ktyll U B[llift (llift d)]).
Local Notation sC U := (ktmlll U C[llift (llift (llift d))]).
Local Notation sY U := (ktyl U Y[llift d]).
Local Notation sc U := (ktmll U c[llift (llift d)]).
Local Notation qX U := (kty U X[d']).
Local Notation qY U := (ktyl U Y[llift d']).
Local Notation rX U := (kty U X'[d']).
Local Notation rA U := (ktyl U A'[llift d']).
Local Notation rB U := (ktyll U B'[llift (llift d')]).
Local Notation rC U := (ktmlll U C'[llift (llift (llift d'))]).
Local Notation rY U := (ktyl U Y'[llift d']).
Local Notation rc U := (ktmll U c'[llift (llift d')]).

(** The step at related indices and seeds, at both sides' own step
    types. *)
Lemma c_at (U : kwk G Δ) j0 j0' y0 y0' :
  LRtm li (kw_G U) (kw_Δ U) (sX U) (qX U) j0 j0' ->
  LRtm kc (kw_G U) (kw_Δ U) (sY U)[lsingle j0] (qY U)[lsingle j0'] y0 y0' ->
  LRtm Lc (kw_G U) (kw_Δ U)
    (mStepTy l l' li (sX U) (sA U) (sB U) (sC U) kc (sY U))[lsingle j0]
    (mStepTy k k' ki (rX U) (rA U) (rB U) (rC U) kc' (rY U))[lsingle j0']
    (sc U)[lsingle2 j0 y0] (rc U)[lsingle2 j0' y0'].
Proof using EL VL VN Vc Vstep Hd.
  intros hj hy. pose proof (SubRel_kw _ _ _ U _ _ Hd) as HdU.
  rewrite !kty_subst in hj. rewrite !ktyl_subst_single in hy.
  pose proof (Vc _ _ (kw_gok U)) as VcU. rewrite !gwa_cext, gwa_ren_ty, gwa_mStepTy in VcU.
  pose proof (VcU _ _ _ (SubRel_cons (SubRel_cons HdU hj) hy)) as Xc.
  rewrite !shift_cons_ty', <- !(ktmll_single2 _ _ _ _ _ Nd), <- !(ktmll_single2 _ _ _ _ _ Nd') in Xc.
  pose proof (Vstep _ _ (kw_gok U)) as VsU. rewrite gwa_cext, !gwa_mStepTy in VsU.
  pose proof (VsU _ _ _ (SubRel_cons HdU hj)) as Xs.
  rewrite <- (lift_single_ty _ _ _ (kwsub_nf U _ Nd)), <- (lift_single_ty _ _ _ (kwsub_nf U _ Nd')) in Xc.
  rewrite <- (lift_single_ty _ _ _ (kwsub_nf U _ Nd)), <- (lift_single_ty _ _ _ (kwsub_nf U _ Nd')) in Xs.
  rewrite <- !gwa_mStepTy, (kw_mStepTy U _ _ _ _ _ _ _ _ _ _ Nd), (kw_mStepTy U _ _ _ _ _ _ _ _ _ _ Nd') in Xc.
  rewrite <- !gwa_mStepTy, (kw_mStepTy U _ _ _ _ _ _ _ _ _ _ Nd), (kw_mStepTy U _ _ _ _ _ _ _ _ _ _ Nd') in Xs.
  exact (LRtm_irrel_r Xc Xs).
Qed.

(** The premises' escapes in a world: the signatures, the carrier and
    the step (both steps in the left-hand context at the left-hand step
    type). *)
Lemma esc_at (U : kwk G Δ) :
  MGeq (kw_G U) (kw_Δ U) l l' li (sX U) (sA U) (sB U) (sC U) k k' ki (rX U) (rA U) (rB U) (rC U) /\
  [ kw_G U ; kw_Δ U ,, sX U @ li ⊢g sY U @ kc ] /\ [ kw_G U ; kw_Δ U ,, sX U @ li ⊢ sY U ≈ rY U @ kc ] /\
  [ kw_G U ; kw_Δ U ,, sX U @ li ,, sY U @ kc ⊢g sc U
      : (mStepTy l l' li (sX U) (sA U) (sB U) (sC U) kc (sY U))⟨↑⟩ @ Lc ] /\
  [ kw_G U ; kw_Δ U ,, sX U @ li ,, sY U @ kc ⊢g rc U
      : (mStepTy l l' li (sX U) (sA U) (sB U) (sC U) kc (sY U))⟨↑⟩ @ Lc ] /\
  [ kw_G U ; kw_Δ U ,, sX U @ li ,, sY U @ kc ⊢ sc U ≈ rc U
      : (mStepTy l l' li (sX U) (sA U) (sB U) (sC U) kc (sY U))⟨↑⟩ @ Lc ].
Proof using EL VL VN VX VA VB VC VY Vc Hwl Hwl' Hwli Hwc Hk Hk' Hki Hd.
  pose proof (MSide_kw U (m_side Hwl Hwl' Hwli Hk Hk' Hki VX VA VB VC Hd)) as HM.
  pose proof (SubRel_kw _ _ _ U _ _ Hd) as HdU.
  pose proof (VTyG_loc (VTyG_gwk VX (kw_gok U))) as VXU.
  destruct (VXU _ _ _ HdU) as [RX HRX]. destruct (escape_ty _ _ _ _ _ _ _ _ HRX) as (HXD & _ & _).
  pose proof (SubRel_lift HdU (VTy_refl_l VXU) HXD (kw_lwf U Hwli)) as Hl1.
  pose proof (VY _ _ (kw_gok U)) as VYU. rewrite gwa_cext in VYU.
  destruct (VYU _ _ _ Hl1) as [RY HRY]. destruct (escape_ty _ _ _ _ _ _ _ _ HRY) as (HYD & _ & EY).
  pose proof (SubRel_lift Hl1 (VTy_refl_l VYU) HYD (kw_lwf U Hwc)) as Hl2.
  pose proof (Vc _ _ (kw_gok U)) as VcU. rewrite !gwa_cext, gwa_ren_ty, gwa_mStepTy in VcU.
  pose proof (VcU _ _ _ Hl2) as Xc. destruct (LRtm_escape Xc) as [Hc Hc']. pose proof (LRtm_geq Xc) as Ec.
  rewrite !shift_llift_ty, <- !gwa_mStepTy, (kw_mStepTy U _ _ _ _ _ _ _ _ _ _ Nd) in Hc, Hc', Ec.
  rewrite <- !(ktmll_subst_lift2 U c d) in Hc, Ec. rewrite <- !(ktmll_subst_lift2 U c' d') in Hc', Ec.
  rewrite <- !(ktyl_subst_lift U d Y) in HYD, EY, Hc, Hc', Ec.
  rewrite <- !(ktyl_subst_lift U d' Y') in EY.
  rewrite <- !(kty_subst U X d) in HYD, EY, Hc, Hc', Ec.
  exact (conj (ms_geq HM) (conj HYD (conj EY (conj Hc (conj Hc' Ec))))).
Qed.

(** The two sides' [corec]s in a world, and the canonical relations. *)
Local Notation crL U j0 y0 := (tmCorec l l' li (sX U) (sA U) (sB U) (sC U) kc (sY U) (sc U) j0 y0).
Local Notation crR U j0 y0 := (tmCorec k k' ki (rX U) (rA U) (rB U) (rC U) kc' (rY U) (rc U) j0 y0).
Local Notation mI := (mIdx (G := G) (X := X) (X' := X') (l := l) (l' := l') (li := li) Δ d d').
Local Notation mS := (mSh (G := G) (A := A) (A' := A') (l := l) (l' := l') (li := li) Δ d d').
Local Notation mP := (mPos (G := G) (B := B) (B' := B') (l := l) (l' := l') (li := li) Δ d d').

(** The arguments of related [corec]s in a world: indices [i], [i']
    related by [mI] that the [corec]s claim, their own indices [j0], [j0']
    related to the claimed ones, and seeds related at the carrier at the
    own indices. Their typings and generic equalities, at the left. *)
Lemma args_at (U : kwk G Δ) i i' j0 j0' y y' :
  mI U i i' -> LRtm li (kw_G U) (kw_Δ U) (sX U) (sX U) i j0 -> LRtm li (kw_G U) (kw_Δ U) (qX U) (qX U) i' j0' ->
  LRtm kc (kw_G U) (kw_Δ U) (sY U)[lsingle j0] (qY U)[lsingle j0'] y y' ->
  LRtm li (kw_G U) (kw_Δ U) (sX U) (qX U) j0 j0' /\
  [ kw_G U ; kw_Δ U ⊢g i : sX U @ li ] /\ [ kw_G U ; kw_Δ U ⊢g i' : sX U @ li ] /\
  [ kw_G U ; kw_Δ U ⊢g j0 : sX U @ li ] /\ [ kw_G U ; kw_Δ U ⊢g j0' : sX U @ li ] /\
  [ kw_G U ; kw_Δ U ⊢ i ≈ i' : sX U @ li ] /\ [ kw_G U ; kw_Δ U ⊢ i ≈ j0 : sX U @ li ] /\
  [ kw_G U ; kw_Δ U ⊢ j0 ≈ j0' : sX U @ li ] /\
  [ kw_G U ; kw_Δ U ⊢g y : (sY U)[lsingle j0] @ kc ] /\ [ kw_G U ; kw_Δ U ⊢g y' : (sY U)[lsingle j0] @ kc ] /\
  [ kw_G U ; kw_Δ U ⊢ y ≈ y' : (sY U)[lsingle j0] @ kc ].
Proof using EL VL VN VX Hd.
  intros hi hj hj' hy. pose proof (proj1 (mIdx_iff VX Hd U i i') hi) as Hii.
  pose proof (LRtm_trans (LRtm_sym hj) (LRtm_trans Hii hj')) as hjj.
  destruct (LRtm_escape Hii) as [Hi Hi']. destruct (LRtm_escape hjj) as [Hj0 Hj0'].
  destruct (LRtm_escape hy) as [Hy Hy'].
  exact (conj hjj (conj Hi (conj Hi' (conj Hj0 (conj Hj0' (conj (LRtm_geq Hii) (conj (LRtm_geq hj)
           (conj (LRtm_geq hjj) (conj Hy (conj Hy' (LRtm_geq hy))))))))))).
Qed.

(** Both sides typed at the left signature at the claimed index, and
    generically equal there. *)
Lemma typ_at (U : kwk G Δ) i i' j0 j0' y y' :
  mI U i i' -> LRtm li (kw_G U) (kw_Δ U) (sX U) (sX U) i j0 -> LRtm li (kw_G U) (kw_Δ U) (qX U) (qX U) i' j0' ->
  LRtm kc (kw_G U) (kw_Δ U) (sY U)[lsingle j0] (qY U)[lsingle j0'] y y' ->
  [ kw_G U ; kw_Δ U ⊢g crL U j0 y : tyM l l' li (sX U) (sA U) (sB U) (sC U) i @ mlvl l l' li ] /\
  [ kw_G U ; kw_Δ U ⊢g crR U j0' y' : tyM l l' li (sX U) (sA U) (sB U) (sC U) i @ mlvl l l' li ] /\
  [ kw_G U ; kw_Δ U ⊢ crL U j0 y ≈ crR U j0' y' : tyM l l' li (sX U) (sA U) (sB U) (sC U) i @ mlvl l l' li ].
Proof using EL VL VN VX VA VB VC VY Vc Hwl Hwl' Hwli Hwc Hk Hk' Hki Hkc Hd.
  intros hi hj hj' hy.
  destruct (args_at U i i' j0 j0' y y' hi hj hj' hy)
    as (hjj & Hi & Hi' & Hj0 & Hj0' & Eii & Eij & Ejj & Hy & Hy' & Eyy).
  destruct (esc_at U) as (HG & HY & EY & Hc & Hc' & Ec).
  pose proof (MEq_of_MGeq HG) as HE. pose proof HE as (_ & _ & _ & HS & _).
  pose proof HG as (H1 & H2 & H3 & _ & EX & EA & EB & EC).
  pose proof HS as (W1 & W2 & Wi & HX & HA & HB & HC).
  pose proof (kw_lwf U Hwc) as Wc.
  pose proof (geq_ty_sound EY) as DY. pose proof (eqty_wf_r ge_typeof DY) as HY'.
  pose proof (geq_tm_sound Eij) as Dij.
  pose proof (MEq_of_MAnn HS (MAnn_refl HS Hi)) as HE0.
  assert (Ei : [ kw_G U ; kw_Δ U ⊢g tyM l l' li (sX U) (sA U) (sB U) (sC U) i
                  ≅ tyM l l' li (sX U) (sA U) (sB U) (sC U) j0 @ mlvl l l' li ])
    by exact (M_ty_eq ge_typeof ge_notV HE0 Dij).
  assert (HL : [ kw_G U ; kw_Δ U ⊢g crL U j0 y : tyM l l' li (sX U) (sA U) (sB U) (sC U) j0 @ mlvl l l' li ])
    by (apply wf_corec; auto using ge_compt).
  assert (Hyi' : [ kw_G U ; kw_Δ U ⊢g y' : (sY U)[lsingle i] @ kc ]).
  { eapply wf_conv; [exact Hy' | rewrite ge_typeof].
    apply (wf_ty_func ge_typeof HY), (lsub_eq_single ge_typeof); [exact Hi | exact Hj0 | exact Dij]. }
  assert (HR : [ kw_G U ; kw_Δ U ⊢g crR U j0' y' : tyM l l' li (sX U) (sA U) (sB U) (sC U) i @ mlvl l l' li ]).
  { eapply (pre_corec_r ge_typeof ge_notV HE (lequiv_sym _ _ _ (kw_lequiv U Hkc)) DY HY HY' Hc' Hi Hj0').
    - eapply eqtm_trans; [exact Dij | exact (geq_tm_sound Ejj)].
    - exact Hyi'. }
  refine (conj (wf_conv _ _ _ _ _ _ _ HL _) (conj HR _)); [rewrite ge_typeof; exact Ei |].
  eapply geq_tm_conv; [| apply eqty_sym, Ei].
  apply geq_tm_corec; auto using geq_ty_sound, geq_tm_sound, lequiv_sym, kw_lequiv.
Qed.

(** The step's projections at the own indices: its first projections,
    and its continuations at related positions. *)
Local Notation fL U j0 y0 := (mOutFst l l' li (sX U) (sA U) (sB U) (sC U) kc (sY U) (sc U) j0 y0).
Local Notation fR U j0 y0 := (mOutFst k k' ki (rX U) (rA U) (rB U) (rC U) kc' (rY U) (rc U) j0 y0).
Local Notation iL U j0 y0 p := ((sC U)[lsingle3 j0 (fL U j0 y0) p]).
Local Notation iR U j0 y0 p := ((rC U)[lsingle3 j0 (fR U j0 y0) p]).
Local Notation scL U j0 y0 p :=
  (app (tmSnd l (lmax kc (mlvl l l' li)) (sA U)[lsingle j0]
          (mStepSnd l l' li (sX U) (sA U) (sB U) (sC U) kc (sY U) j0) (sc U)[lsingle2 j0 y0])
     l' (lmax kc (mlvl l l' li)) (sB U)[lsingle2 j0 (fL U j0 y0)]
     (tySum kc (mlvl l l' li) (sY U)⟨rlift ↑⟩[lsingle (mOutIdx l l' li (sX U) (sA U) (sB U) (sC U) kc (sY U) (sc U) j0 y0)]
        (tyM l l' li (sX U)⟨↑⟩ (sA U)⟨rlift ↑⟩ (sB U)⟨rlift (rlift ↑)⟩ (sC U)⟨rlift (rlift (rlift ↑))⟩
           (mOutIdx l l' li (sX U) (sA U) (sB U) (sC U) kc (sY U) (sc U) j0 y0))) p).
Local Notation scR U j0 y0 p :=
  (app (tmSnd k (lmax kc' (mlvl k k' ki)) (rA U)[lsingle j0]
          (mStepSnd k k' ki (rX U) (rA U) (rB U) (rC U) kc' (rY U) j0) (rc U)[lsingle2 j0 y0])
     k' (lmax kc' (mlvl k k' ki)) (rB U)[lsingle2 j0 (fR U j0 y0)]
     (tySum kc' (mlvl k k' ki) (rY U)⟨rlift ↑⟩[lsingle (mOutIdx k k' ki (rX U) (rA U) (rB U) (rC U) kc' (rY U) (rc U) j0 y0)]
        (tyM k k' ki (rX U)⟨↑⟩ (rA U)⟨rlift ↑⟩ (rB U)⟨rlift (rlift ↑)⟩ (rC U)⟨rlift (rlift (rlift ↑))⟩
           (mOutIdx k k' ki (rX U) (rA U) (rB U) (rC U) kc' (rY U) (rc U) j0 y0))) p).

Lemma steps_at (U : kwk G Δ) j0 j0' y y' :
  LRtm li (kw_G U) (kw_Δ U) (sX U) (qX U) j0 j0' ->
  LRtm kc (kw_G U) (kw_Δ U) (sY U)[lsingle j0] (qY U)[lsingle j0'] y y' ->
  LRtm l (kw_G U) (kw_Δ U) (sA U)[lsingle j0] (rA U)[lsingle j0'] (fL U j0 y) (fR U j0' y') /\
  forall p p', LRtm l' (kw_G U) (kw_Δ U) (sB U)[lsingle2 j0 (fL U j0 y)] (rB U)[lsingle2 j0' (fR U j0' y')] p p' ->
  LRtm (lmax kc (mlvl l l' li)) (kw_G U) (kw_Δ U)
    (tySum kc (mlvl l l' li) (sY U)[lsingle (iL U j0 y p)] (tyM l l' li (sX U) (sA U) (sB U) (sC U) (iL U j0 y p)))
    (tySum kc' (mlvl k k' ki) (rY U)[lsingle (iR U j0' y' p')] (tyM k k' ki (rX U) (rA U) (rB U) (rC U) (iR U j0' y' p')))
    (scL U j0 y p) (scR U j0' y' p').
Proof using EL VL VN Vc Vstep Hd.
  intros hjj hy. pose proof (c_at U j0 j0' y y' hjj hy) as Xc.
  rewrite !mStepTy_single in Xc. destruct (LRtm_sig_proj Xc) as [Ff Fs].
  split; [exact Ff|]. intros p p' hp.
  destruct (LRtm_escape hjj) as [Hj0 Hj0']. destruct (LRtm_escape Ff) as [Hf Hf'].
  rewrite (M_E_snd _ _ _ _ _ _ _ _ _ j0) in Fs by first [kw_nf | exact (wf_tm_nf Hj0)].
  rewrite (M_E_snd _ _ _ _ _ _ _ _ _ j0') in Fs by first [kw_nf | exact (wf_tm_nf Hj0')].
  pose proof (LRtm_pi_app Fs hp) as Xa.
  rewrite (mSum_single _ _ _ _ _ _ _ _ _ j0) in Xa by first [kw_nf | exact (wf_tm_nf Hj0) | exact (wf_tm_nf Hf)].
  rewrite (mSum_single _ _ _ _ _ _ _ _ _ j0') in Xa by first [kw_nf | exact (wf_tm_nf Hj0') | exact (wf_tm_nf Hf')].
  exact Xa.
Qed.

(** The right-hand side at its own signature, carrier, step and types. *)
Lemma rside_at (U : kwk G Δ) i i' j0 j0' y y' :
  mI U i i' -> LRtm li (kw_G U) (kw_Δ U) (sX U) (sX U) i j0 -> LRtm li (kw_G U) (kw_Δ U) (qX U) (qX U) i' j0' ->
  LRtm kc (kw_G U) (kw_Δ U) (sY U)[lsingle j0] (qY U)[lsingle j0'] y y' ->
  MSig (G := kw_G U) (i := ge_layer) (kw_Δ U) k k' ki (rX U) (rA U) (rB U) (rC U) /\
  [ kw_G U ; kw_Δ U ,, rX U @ ki ⊢g rY U @ kc' ] /\
  [ kw_G U ; kw_Δ U ,, rX U @ ki ,, rY U @ kc' ⊢g rc U
      : (mStepTy k k' ki (rX U) (rA U) (rB U) (rC U) kc' (rY U))⟨↑⟩ @ lmax k (lmax kc' (mlvl k k' ki)) ] /\
  [ kw_G U ; kw_Δ U ⊢g i' : rX U @ ki ] /\ [ kw_G U ; kw_Δ U ⊢g j0' : rX U @ ki ] /\
  [ kw_G U ; kw_Δ U ⊢g j0' ≅ i' : rX U @ ki ] /\
  [ kw_G U ; kw_Δ U ⊢g y' : (rY U)[lsingle j0'] @ kc' ].
Proof using EL VL VN VX VA VB VC VY Vc Hwl Hwl' Hwli Hwc Hk Hk' Hki Hkc Hd.
  intros hi hj hj' hy.
  destruct (args_at U i i' j0 j0' y y' hi hj hj' hy)
    as (hjj & Hi & Hi' & Hj0 & Hj0' & Eii & Eij & Ejj & Hy & Hy' & Eyy).
  destruct (esc_at U) as (HG & HY & EY & Hc & Hc' & Ec).
  pose proof (MEq_of_MGeq HG) as HE. pose proof (MEq_sig_r ge_typeof ge_notV HE) as HS'.
  pose proof HG as (H1 & H2 & H3 & _ & EX & _).
  pose proof (kw_lequiv U Hkc) as Hkc'.
  pose proof (geq_ty_sound EY) as DY. pose proof (eqty_wf_r ge_typeof DY) as HY'.
  destruct (pre_step_r HE (lequiv_sym _ _ _ Hkc') DY HY HY' Hc') as [HYr Hcr].
  pose proof (geq_ty_sound EX) as DX.
  assert (CX : forall t, [ kw_G U ; kw_Δ U ⊢g t : sX U @ li ] -> [ kw_G U ; kw_Δ U ⊢g t : rX U @ ki ]).
  { intros t Ht. eapply wf_lconv; [eapply wf_conv; [exact Ht | rewrite ge_typeof; exact (eqty_sym _ _ _ _ _ _ DX)]
                                  | exact (lequiv_sym _ _ _ H3)]. }
  assert (Ej : [ kw_G U ; kw_Δ U ⊢g j0' ≅ i' : sX U @ li ]).
  { eapply eqtm_trans; [exact (eqtm_sym _ _ _ _ _ _ _ (geq_tm_sound Ejj)) |].
    eapply eqtm_trans; [exact (eqtm_sym _ _ _ _ _ _ _ (geq_tm_sound Eij)) | exact (geq_tm_sound Eii)]. }
  refine (conj HS' (conj HYr (conj Hcr (conj (CX _ Hi') (conj (CX _ Hj0') (conj _ _)))))).
  - eapply eqtm_lconv; [eapply eqtm_conv; [exact Ej | rewrite ge_typeof; exact (eqty_sym _ _ _ _ _ _ DX)]
                       | exact (lequiv_sym _ _ _ H3)].
  - eapply wf_lconv; [| exact Hkc'].
    eapply wf_conv; [exact Hy' | rewrite ge_typeof].
    eapply eqty_trans; [exact (eqty_sym _ _ _ _ _ _ (eqty_single ge_typeof DY Hj0')) |].
    apply eqty_sym, (wf_ty_func ge_typeof HY), (lsub_eq_single ge_typeof); [exact Hj0 | exact Hj0' |].
    exact (geq_tm_sound Ejj).
Qed.

(** [out] of both sides steps to β's reduct, at the claimed indices. *)
Lemma red_at (U : kwk G Δ) i i' j0 j0' y y' :
  mI U i i' -> LRtm li (kw_G U) (kw_Δ U) (sX U) (sX U) i j0 -> LRtm li (kw_G U) (kw_Δ U) (qX U) (qX U) i' j0' ->
  LRtm kc (kw_G U) (kw_Δ U) (sY U)[lsingle j0] (qY U)[lsingle j0'] y y' ->
  forall k1 k2 ki1 X1 A1 B1 C1 m1 k1' k2' ki1' X1' A1' B1' C1' m1',
  MAnn (kw_G U) (kw_Δ U) l l' li (sX U) (sA U) (sB U) (sC U) i k1 k2 ki1 X1 A1 B1 C1 m1 ->
  MAnn (kw_G U) (kw_Δ U) k k' ki (rX U) (rA U) (rB U) (rC U) i' k1' k2' ki1' X1' A1' B1' C1' m1' ->
  [ kw_G U ; kw_Δ U ⊢g tmOut k1 k2 ki1 X1 A1 B1 C1 m1 (crL U j0 y)
      ⤳* mOutCorec l l' li (sX U) (sA U) (sB U) (sC U) kc (sY U) (sc U) j0 y
      : mOutTy l l' li (sX U) (sA U) (sB U) (sC U) i @ lmax l (mlvl l l' li) ] /\
  [ kw_G U ; kw_Δ U ⊢g tmOut k1' k2' ki1' X1' A1' B1' C1' m1' (crR U j0' y')
      ⤳* mOutCorec k k' ki (rX U) (rA U) (rB U) (rC U) kc' (rY U) (rc U) j0' y'
      : mOutTy k k' ki (rX U) (rA U) (rB U) (rC U) i' @ lmax l (mlvl l l' li) ].
Proof using EL VL VN VX VA VB VC VY Vc Hwl Hwl' Hwli Hwc Hk Hk' Hki Hkc Hd.
  intros hi hj hj' hy * Ann Ann'.
  destruct (args_at U i i' j0 j0' y y' hi hj hj' hy)
    as (hjj & Hi & Hi' & Hj0 & Hj0' & Eii & Eij & Ejj & Hy & Hy' & Eyy).
  destruct (esc_at U) as (HG & HY & EY & Hc & Hc' & Ec).
  destruct (rside_at U i i' j0 j0' y y' hi hj hj' hy) as (HS' & HYr & Hcr & Hir & Hj0r & Ejr & Hyr).
  pose proof (MEq_of_MGeq HG) as HE. pose proof HE as (_ & _ & _ & HS & _).
  pose proof HG as (H1 & H2 & H3 & _).
  split.
  - exact (tmred_out_corec HS (kw_lwf U Hwc) HY Hc Hj0 Hy
             (eqtm_sym _ _ _ _ _ _ _ (geq_tm_sound Eij)) Ann).
  - eapply tmred_lconv; [| exact (lequiv_max _ _ _ _ _ H1 (lequiv_mlvl H1 H2 H3))].
    exact (tmred_out_corec HS' (lequiv_wf_l _ _ _ (kw_lequiv U Hkc)) HYr Hcr Hj0r Hyr Ejr Ann').
Qed.

(** ** The signature's families at related arguments, in a world, at any
    related substitutions [e], [e'] (the premises' own, or one side's
    twice). *)
Section Fam.
Context {e e' : lsub} (He : SubRel G Γ Δ e e') (U : kwk G Δ).

Let Ne := proj1 (SubRel_nf _ _ _ _ _ He).
Let Ne' := proj2 (SubRel_nf _ _ _ _ _ He).

Lemma rA1 {T T' l0} (VT : VTyG G (Γ ,, X @ li) T T' l0) x x' :
  LRtm li (kw_G U) (kw_Δ U) (kty U X[e]) (kty U X[e']) x x' ->
  LRty l0 (kw_G U) (kw_Δ U) (ktyl U T[llift e])[lsingle x] (ktyl U T'[llift e'])[lsingle x'].
Proof using EL VL VN He.
  intros hx. rewrite !kty_subst in hx.
  pose proof (VT _ _ (kw_gok U)) as VTU. rewrite gwa_cext in VTU.
  destruct (VTU _ _ _ (SubRel_cons (SubRel_kw _ _ _ U _ _ He) hx)) as [R HR].
  rewrite <- !ktyl_subst_single in HR. exact (ex_intro _ _ HR).
Qed.

Lemma rB2 {T T' l0} (VT : VTyG G (Γ ,, X @ li ,, A @ l) T T' l0) x x' a a' :
  LRtm li (kw_G U) (kw_Δ U) (kty U X[e]) (kty U X[e']) x x' ->
  LRtm l (kw_G U) (kw_Δ U) (ktyl U A[llift e])[lsingle x] (ktyl U A[llift e'])[lsingle x'] a a' ->
  LRty l0 (kw_G U) (kw_Δ U) (ktyll U T[llift (llift e)])[lsingle2 x a] (ktyll U T'[llift (llift e')])[lsingle2 x' a'].
Proof using EL VL VN He.
  intros hx ha. rewrite !kty_subst in hx. rewrite !ktyl_subst_single in ha.
  pose proof (VT _ _ (kw_gok U)) as VTU. rewrite !gwa_cext in VTU.
  destruct (VTU _ _ _ (SubRel_cons (SubRel_cons (SubRel_kw _ _ _ U _ _ He) hx) ha)) as [R HR].
  rewrite <- (ktyll_subst_single2 U e Ne), <- (ktyll_subst_single2 U e' Ne') in HR. exact (ex_intro _ _ HR).
Qed.

Lemma rC3 {t t'} (Vt : VTmG G (Γ ,, X @ li ,, A @ l ,, B @ l') t t' X⟨↑⟩⟨↑⟩⟨↑⟩ li) x x' a a' q q' :
  LRtm li (kw_G U) (kw_Δ U) (kty U X[e]) (kty U X[e']) x x' ->
  LRtm l (kw_G U) (kw_Δ U) (ktyl U A[llift e])[lsingle x] (ktyl U A[llift e'])[lsingle x'] a a' ->
  LRtm l' (kw_G U) (kw_Δ U) (ktyll U B[llift (llift e)])[lsingle2 x a] (ktyll U B[llift (llift e')])[lsingle2 x' a']
    q q' ->
  LRtm li (kw_G U) (kw_Δ U) (kty U X[e]) (kty U X[e'])
    (ktmlll U t[llift (llift (llift e))])[lsingle3 x a q] (ktmlll U t'[llift (llift (llift e'))])[lsingle3 x' a' q'].
Proof using EL VL VN He.
  intros hx ha hq. rewrite !kty_subst in hx |- *. rewrite !ktyl_subst_single in ha.
  rewrite (ktyll_subst_single2 U e Ne), (ktyll_subst_single2 U e' Ne') in hq.
  pose proof (Vt _ _ (kw_gok U)) as VtU. rewrite !gwa_cext, !gwa_ren_ty in VtU.
  pose proof (VtU _ _ _ (SubRel_cons (SubRel_cons (SubRel_cons (SubRel_kw _ _ _ U _ _ He) hx) ha) hq)) as Y0.
  rewrite !shift_cons_ty' in Y0.
  rewrite (ktmlll_subst_single3 U e Ne), (ktmlll_subst_single3 U e' Ne'). exact Y0.
Qed.

End Fam.

(** A claimed shape and position, seen from the own ones: the position
    at the own shape (for the step's continuation), and the claimed child
    indices related to the own ones and to each other. *)
Lemma pos_at (U : kwk G Δ) i i' j0 j0' y y' a a' p p' :
  mI U i i' -> LRtm li (kw_G U) (kw_Δ U) (sX U) (sX U) i j0 -> LRtm li (kw_G U) (kw_Δ U) (qX U) (qX U) i' j0' ->
  LRtm kc (kw_G U) (kw_Δ U) (sY U)[lsingle j0] (qY U)[lsingle j0'] y y' ->
  mS U i i' a a' ->
  LRtm l (kw_G U) (kw_Δ U) (sA U)[lsingle i] (sA U)[lsingle i] a (fL U j0 y) ->
  LRtm l (kw_G U) (kw_Δ U) (ktyl U A[llift d'])[lsingle i'] (ktyl U A[llift d'])[lsingle i'] a' (fR U j0' y') ->
  mP U i i' a a' p p' ->
  LRtm l' (kw_G U) (kw_Δ U) (sB U)[lsingle2 j0 (fL U j0 y)] (rB U)[lsingle2 j0' (fR U j0' y')] p p' /\
  LRtm li (kw_G U) (kw_Δ U) (sX U) (sX U) (sC U)[lsingle3 i a p] (iL U j0 y p) /\
  LRtm li (kw_G U) (kw_Δ U) (qX U) (qX U) (rC U)[lsingle3 i' a' p'] (iR U j0' y' p') /\
  mI U (sC U)[lsingle3 i a p] (rC U)[lsingle3 i' a' p'].
Proof using EL VL VN VX VA VB VC Hd.
  intros hi hj hj' hy ha ha0 ha0' hp.
  pose proof (proj1 (mSh_iff VX VA Hd U i i' a a' hi) ha) as haA.
  pose proof (proj1 (mPos_iff VX VA VB Hd U i i' a a' p p' hi ha) hp) as hpB.
  pose proof (SubRel_refl_l Hd) as Hdl. pose proof (SubRel_refl_r Hd) as Hdr.
  (* the left side, at [d] twice *)
  pose proof (rA1 Hdl U (VTyG_refl_l VA) i j0 hj) as TAl.
  pose proof (LRtm_conv_r ha0 TAl) as hal.
  pose proof (rB2 Hdl U (VTyG_refl_l VB) i j0 a (fL U j0 y) hj hal) as TBl.
  pose proof (LRtm_conv_r (LRtm_trans hpB (LRtm_sym hpB)) TBl) as hpl.
  (* the right side, at [d'] twice *)
  pose proof (rA1 Hdr U (VTyG_refl_l VA) i' j0' hj') as TAr.
  pose proof (LRtm_conv_r ha0' TAr) as har.
  pose proof (rB2 Hdr U (VTyG_refl_l VB) i' j0' a' (fR U j0' y') hj' har) as TBr.
  pose proof (LRtm_conv_r (LRtm_trans (LRtm_sym hpB) hpB) TBr) as hpr.
  refine (conj _ (conj _ (conj _ (m_ch VX VA VB VC Hd U i i' a a' p p' hi ha hp)))).
  - eapply LRtm_conv_r; [eapply LRtm_conv_l; [exact hpB | exact (LRty_sym TBl)] |].
    exact (rB2 Hdr U VB i' j0' a' (fR U j0' y') hj' har).
  - exact (rC3 Hdl U (VTmG_trans VC (VTmG_sym VC)) i j0 a (fL U j0 y) p p hj hal hpl).
  - exact (rC3 Hdr U (VTmG_trans (VTmG_sym VC) VC) i' j0' a' (fR U j0' y') p' p' hj' har hpr).
Qed.


(** ** [MRn] at related indices

    The canonical relations are irrelevant in both indices, so [MRn] at
    the [corec]'s own indices is [MRn] at any related claimed ones
    ([MRn_idx]). *)
Lemma mS_irr : MShIrr mI mS.
Proof using EL VL VN VX VA Hd.
  intros ρ x y y' hy hy' a a'.
  rewrite (mSh_iff VX VA Hd ρ x y a a' hy), (mSh_iff VX VA Hd ρ x y' a a' hy').
  pose proof (rA1 Hd ρ (VTyG_refl_l VA) x y (proj1 (mIdx_iff VX Hd ρ _ _) hy)) as T1.
  pose proof (rA1 Hd ρ (VTyG_refl_l VA) x y' (proj1 (mIdx_iff VX Hd ρ _ _) hy')) as T2.
  split; intros H; [exact (LRtm_irrel_r H T2) | exact (LRtm_irrel_r H T1)].
Qed.

Lemma mS_irr_l : MShIrr (mflipI mI) (mflipS mS).
Proof using EL VL VN VX VA Hd.
  intros ρ x y y' hy hy' a a'. unfold mflipI, mflipS in *.
  rewrite (mSh_iff VX VA Hd ρ y x a' a hy), (mSh_iff VX VA Hd ρ y' x a' a hy').
  pose proof (rA1 Hd ρ (VTyG_refl_l VA) y x (proj1 (mIdx_iff VX Hd ρ _ _) hy)) as T1.
  pose proof (rA1 Hd ρ (VTyG_refl_l VA) y' x (proj1 (mIdx_iff VX Hd ρ _ _) hy')) as T2.
  split; intros H; [exact (LRtm_irrel_l H T2) | exact (LRtm_irrel_l H T1)].
Qed.

Lemma mP_irr : MPosIrr mI mS mP.
Proof using EL VL VN VX VA VB Hd.
  intros ρ x y y' a b b' hy hy' hb hb' p p'.
  rewrite (mPos_iff VX VA VB Hd ρ x y a b p p' hy hb), (mPos_iff VX VA VB Hd ρ x y' a b' p p' hy' hb').
  pose proof (rB2 Hd ρ (VTyG_refl_l VB) x y a b (proj1 (mIdx_iff VX Hd ρ _ _) hy)
                (proj1 (mSh_iff VX VA Hd ρ _ _ _ _ hy) hb)) as T1.
  pose proof (rB2 Hd ρ (VTyG_refl_l VB) x y' a b' (proj1 (mIdx_iff VX Hd ρ _ _) hy')
                (proj1 (mSh_iff VX VA Hd ρ _ _ _ _ hy') hb')) as T2.
  split; intros H; [exact (LRtm_irrel_r H T2) | exact (LRtm_irrel_r H T1)].
Qed.

Lemma mP_irr_l : MPosIrr (mflipI mI) (mflipS mS) (mflipP mP).
Proof using EL VL VN VX VA VB Hd.
  intros ρ x y y' a b b' hy hy' hb hb' p p'. unfold mflipI, mflipS, mflipP in *.
  rewrite (mPos_iff VX VA VB Hd ρ y x b a p' p hy hb), (mPos_iff VX VA VB Hd ρ y' x b' a p' p hy' hb').
  pose proof (rB2 Hd ρ (VTyG_refl_l VB) y x b a (proj1 (mIdx_iff VX Hd ρ _ _) hy)
                (proj1 (mSh_iff VX VA Hd ρ _ _ _ _ hy) hb)) as T1.
  pose proof (rB2 Hd ρ (VTyG_refl_l VB) y' x b' a (proj1 (mIdx_iff VX Hd ρ _ _) hy')
                (proj1 (mSh_iff VX VA Hd ρ _ _ _ _ hy') hb')) as T2.
  split; intros H; [exact (LRtm_irrel_l H T2) | exact (LRtm_irrel_l H T1)].
Qed.

(** In a world. *)
Lemma mrn_idx_at n (U : kwk G Δ) m m' m1 m1' t t' :
  mI U m m' -> mI U m m1' -> mI U m1 m1' ->
  MRn n (kw_G U) (kw_Δ U) l l' li (sX U) (sA U) (sB U) (sC U) k k' ki (rX U) (rA U) (rB U) (rC U)
    (fun ρ => mS (kw_comp U ρ)) (fun ρ => mP (kw_comp U ρ)) m m' t t' ->
  MRn n (kw_G U) (kw_Δ U) l l' li (sX U) (sA U) (sB U) (sC U) k k' ki (rX U) (rA U) (rB U) (rC U)
    (fun ρ => mS (kw_comp U ρ)) (fun ρ => mP (kw_comp U ρ)) m1 m1' t t'.
Proof using EL VL VN VX VA VB VC Hwl Hwl' Hwli Hk Hk' Hki Hd.
  intros h1 h2 h3.
  assert (NF : forall x x', mI U x x' -> nftm x /\ nftm x').
  { intros x x' hx. destruct (LRtm_escape (proj1 (mIdx_iff VX Hd U _ _) hx)) as [Hx Hx'].
    exact (conj (wf_tm_nf Hx) (wf_tm_nf Hx')). }
  destruct (NF _ _ h1) as [N N']. destruct (NF _ _ h3) as [N1 N1'].
  apply (MRn_idx n (MSide_kw U (m_side Hwl Hwl' Hwli Hk Hk' Hki VX VA VB VC Hd))
           (MShIrr_kw U mS_irr) (MPosIrr_kw U mP_irr) (MShIrr_kw U mS_irr_l) (MPosIrr_kw U mP_irr_l)
           N N' N1 N1'); intros ρ.
  - exact (m_imon VX Hd U ρ _ _ h1).
  - exact (m_imon VX Hd U ρ _ _ h2).
  - exact (m_imon VX Hd U ρ _ _ h3).
Qed.

(** ** β's reduct's [case] at a neutral continuation *)
Local Notation mL U o := (tyM l l' li (sX U) (sA U) (sB U) (sC U) o).
Local Notation mR U o := (tyM k k' ki (rX U) (rA U) (rB U) (rC U) o).
Local Notation brL U o := (tmCorec l l' li (sX U)⟨↑⟩ (sA U)⟨rlift ↑⟩ (sB U)⟨rlift (rlift ↑)⟩
  (sC U)⟨rlift (rlift (rlift ↑))⟩ kc (sY U)⟨rlift ↑⟩ (sc U)⟨rlift (rlift ↑)⟩ o⟨↑⟩ (var 0)).
Local Notation brR U o := (tmCorec k k' ki (rX U)⟨↑⟩ (rA U)⟨rlift ↑⟩ (rB U)⟨rlift (rlift ↑)⟩
  (rC U)⟨rlift (rlift (rlift ↑))⟩ kc' (rY U)⟨rlift ↑⟩ (rc U)⟨rlift (rlift ↑)⟩ o⟨↑⟩ (var 0)).

Lemma case_ne_at (W : kwk G Δ) o o' ν ν' :
  LRtm li (kw_G W) (kw_Δ W) (sX W) (qX W) o o' ->
  [ kw_G W ; kw_Δ W ⊢ ν ~ ν' : tySum kc (mlvl l l' li) (sY W)[lsingle o] (mL W o) @ lmax kc (mlvl l l' li) ] ->
  [ kw_G W ; kw_Δ W ⊢ tmCase kc (mlvl l l' li) (mlvl l l' li) (sY W)[lsingle o] (mL W o) (mL W o)⟨↑⟩
                        (brL W o) (var 0) ν
                    ~ tmCase kc' (mlvl k k' ki) (mlvl k k' ki) (rY W)[lsingle o'] (mR W o') (mR W o')⟨↑⟩
                        (brR W o') (var 0) ν' : mL W o @ mlvl l l' li ].
Proof using EL VL VN VX VA VB VC VY Vc Hwl Hwl' Hwli Hwc Hk Hk' Hki Hkc Hd.
  intros h Hν.
  destruct (esc_at W) as (HG & HY & EY & Hc & Hc' & Ec).
  pose proof HG as (H1 & H2 & H3 & HS & EX & EA & EB & EC).
  pose proof (kw_lwf W Hwc) as Wc. pose proof (kw_lwf W Hwli) as Wli.
  pose proof HS as (W1 & W2 & Wi & _).
  assert (Hf : lwf (gL (kw_G W)) (mlvl l l' li)) by (cbn; repeat split; assumption).
  destruct (LRtm_escape h) as [Ho _].
  destruct (case_parts HS Wc HY Hc Ho) as (HYo & HMo & HM1 & _ & Hv).
  destruct (rA1 Hd W VY o o' h) as [RY HRY]. destruct (escape_ty _ _ _ _ _ _ _ _ HRY) as (_ & _ & EYo).
  pose proof (MGeq_M HG (LRtm_geq h)) as EMo.
  pose proof (wft_sum _ _ _ _ _ _ _ ge_notV Wc Hf HYo HMo) as HSum.
  pose proof (ext_wf_g HSum (lwf_max Wc Hf)) as HΓS.
  pose proof (geq_ty_wk (wkr_shift1 _ _ _) HΓS EMo) as EM.
  pose proof (lequiv_sym _ _ _ (kw_lequiv W Hkc)) as Hkc'.
  pose proof (lequiv_mlvl H1 H2 H3) as Hff.
  (* the [corec] branches *)
  pose proof (ext_wf_g HYo Wc) as HΓY.
  pose proof (MGeq_wk1 HG HΓY) as HG1. pose proof HG1 as (_ & _ & _ & HS1 & EX1 & EA1 & EB1 & EC1).
  pose proof HS1 as (_ & _ & _ & HX1 & HA1 & HB1 & HC1).
  pose proof (ext_wf_g HX1 Wli) as HΓYX.
  pose proof (wk_under_ty ge_typeof HΓYX HY) as HY1.
  pose proof (ext_wf_g HY1 Wc) as HΓYXY.
  pose proof (geq_ty_wk (wkr_up _ _ _ _ _ (wkr_shift1 _ _ _)) HΓYX EY) as EY1.
  assert (Ec1 : [ kw_G W ; kw_Δ W ,, (sY W)[lsingle o] @ kc ,, (sX W)⟨↑⟩ @ li ,, (sY W)⟨rlift ↑⟩ @ kc
                  ⊢ (sc W)⟨rlift (rlift ↑)⟩ ≈ (rc W)⟨rlift (rlift ↑)⟩
                  : (mStepTy l l' li (sX W)⟨↑⟩ (sA W)⟨rlift ↑⟩ (sB W)⟨rlift (rlift ↑)⟩
                       (sC W)⟨rlift (rlift (rlift ↑))⟩ kc (sY W)⟨rlift ↑⟩)⟨↑⟩ @ Lc ]).
  { rewrite <- mStepTy_wk. apply (geq_tm_wk (r := rlift (rlift ↑)) (Γ := kw_Δ W ,, sX W @ li ,, sY W @ kc));
      [wkr_tac | exact HΓYXY | exact Ec]. }
  assert (Hvar : [ kw_G W ; kw_Δ W ,, (sY W)[lsingle o] @ kc ⊢ var 0 ≈ var 0
                   : (sY W)⟨rlift ↑⟩[lsingle o⟨↑⟩] @ kc ]).
  { rewrite <- seed_wk. apply gne_tm_geq, gne_tm_var. apply wf_var; [rewrite ge_typeof; exact HΓY | constructor]. }
  pose proof (geq_tm_sound (geq_tm_wk (wkr_shift1 _ _ _) HΓY (LRtm_geq h))) as Eoo.
  pose proof (geq_tm_corec H1 H2 H3 Hkc' HX1 (geq_ty_sound EX1) HA1 (geq_ty_sound EA1) HB1 (geq_ty_sound EB1)
                HC1 (geq_tm_sound EC1) Eoo HY1 EY1 Ec1 Hvar) as Eb1.
  pose proof (gne_tm_geq (gne_tm_var Hv)) as Eb2.
  pose proof (gne_tm_case (M := (mL W o)⟨↑⟩) (M' := (mR W o')⟨↑⟩) Hkc' Hff Hff HYo EYo HMo EMo HM1 EM
                ltac:(rewrite shift_inj_single; exact Eb1) ltac:(rewrite shift_inj_single; exact Eb2) Hν) as Hne.
  rewrite shift_single_ty in Hne by exact (wf_ty_nf HMo). exact Hne.
Qed.

(** ** The depth induction's step at a child *)
Local Notation lamL U j0 y0 := (mLam l l' li (sX U) (sA U) (sB U) (sC U) kc (sY U) (sc U) j0 y0).
Local Notation lamR U j0 y0 := (mLam k k' ki (rX U) (rA U) (rB U) (rC U) kc' (rY U) (rc U) j0 y0).

(** Related [corec]s at depth [n], at their own indices. *)
Definition CorecAt n : Prop := forall (U : kwk G Δ) j0 j0' y y',
  mI U j0 j0' -> LRtm kc (kw_G U) (kw_Δ U) (sY U)[lsingle j0] (qY U)[lsingle j0'] y y' ->
  MRn n (kw_G U) (kw_Δ U) l l' li (sX U) (sA U) (sB U) (sC U) k k' ki (rX U) (rA U) (rB U) (rC U)
    (fun ρ => mS (kw_comp U ρ)) (fun ρ => mP (kw_comp U ρ)) j0 j0' (crL U j0 y) (crR U j0' y').

(** The λs applied to related positions at related shapes, at the
    claimed child indices. *)
Lemma kid_at n (IH : CorecAt n) (W : kwk G Δ) j0 j0' y y' a a' p p' la lb A1 B1 la' lb' A1' B1' :
  mI W j0 j0' -> LRtm kc (kw_G W) (kw_Δ W) (sY W)[lsingle j0] (qY W)[lsingle j0'] y y' ->
  mS W j0 j0' a a' ->
  LRtm l (kw_G W) (kw_Δ W) (sA W)[lsingle j0] (sA W)[lsingle j0] a (fL W j0 y) ->
  LRtm l (kw_G W) (kw_Δ W) (ktyl W A[llift d'])[lsingle j0'] (ktyl W A[llift d'])[lsingle j0'] a' (fR W j0' y') ->
  mP W j0 j0' a a' p p' ->
  lequiv (gL (kw_G W)) la l' -> lequiv (gL (kw_G W)) lb (mlvl l l' li) ->
  lequiv (gL (kw_G W)) la' l' -> lequiv (gL (kw_G W)) lb' (mlvl l l' li) ->
  [ kw_G W ; kw_Δ W ⊢ (sB W)[lsingle2 j0 a] ≈ A1 @ l' ] ->
  [ kw_G W ; kw_Δ W ,, (sB W)[lsingle2 j0 a] @ l'
      ⊢ tyM l l' li (sX W)⟨↑⟩ (sA W)⟨rlift ↑⟩ (sB W)⟨rlift (rlift ↑)⟩ (sC W)⟨rlift (rlift (rlift ↑))⟩
          (sC W)[llift (lsingle2 j0 a)] ≈ B1 @ mlvl l l' li ] ->
  [ kw_G W ; kw_Δ W ⊢ (rB W)[lsingle2 j0' a'] ≈ A1' @ l' ] ->
  [ kw_G W ; kw_Δ W ,, (rB W)[lsingle2 j0' a'] @ l'
      ⊢ tyM k k' ki (rX W)⟨↑⟩ (rA W)⟨rlift ↑⟩ (rB W)⟨rlift (rlift ↑)⟩ (rC W)⟨rlift (rlift (rlift ↑))⟩
          (rC W)[llift (lsingle2 j0' a')] ≈ B1' @ mlvl l l' li ] ->
  MRn n (kw_G W) (kw_Δ W) l l' li (sX W) (sA W) (sB W) (sC W) k k' ki (rX W) (rA W) (rB W) (rC W)
    (fun ρ => mS (kw_comp W ρ)) (fun ρ => mP (kw_comp W ρ)) (sC W)[lsingle3 j0 a p] (rC W)[lsingle3 j0' a' p']
    (app (lamL W j0 y) la lb A1 B1 p) (app (lamR W j0' y') la' lb' A1' B1' p').
Proof using EL VL VN VX VA VB VC VY Vc Vstep Hwl Hwl' Hwli Hwc Hk Hk' Hki Hkc Hd.
  intros hjj hy ha ha0 ha0' hp Hla Hlb Hla' Hlb' HA1 HB1 HA1' HB1'.
  pose proof (proj1 (mIdx_iff VX Hd W _ _) hjj) as hjL.
  pose proof (LRtm_trans hjL (LRtm_sym hjL)) as hj. pose proof (LRtm_trans (LRtm_sym hjL) hjL) as hj'.
  destruct (args_at W j0 j0' j0 j0' y y' hjj hj hj' hy)
    as (_ & Hj0 & _ & _ & Hj0' & _ & _ & _ & Hy & _ & _).
  destruct (esc_at W) as (HG & HY & EY & Hc & Hc' & Ec).
  destruct (rside_at W j0 j0' j0 j0' y y' hjj hj hj' hy) as (HS' & HYr & Hcr & _ & Hj0r & _ & Hyr).
  pose proof HG as (H1 & H2 & H3 & HS & _).
  pose proof HS as (W1 & W2 & Wi & _).
  pose proof (kw_lwf W Hwc) as Wc. pose proof (lequiv_wf_l _ _ _ (kw_lequiv W Hkc)) as Wc'.
  assert (Hf : lwf (gL (kw_G W)) (mlvl l l' li)) by (cbn; repeat split; assumption).
  pose proof (lequiv_mlvl H1 H2 H3) as Hff.
  destruct (pos_at W j0 j0' j0 j0' y y' a a' p p' hjj hj hj' hy ha ha0 ha0' hp) as (hpB & hcl & hcr & hc).
  destruct (steps_at W j0 j0' y y' hjL hy) as [Ff Fs]. pose proof (Fs p p' hpB) as Xs.
  (* the indices *)
  pose proof (proj1 (mIdx_iff VX Hd W _ _) hc) as hcL.
  pose proof (LRtm_trans (LRtm_sym hcl) (LRtm_trans hcL hcr)) as hiLR.
  assert (hI : mI W (iL W j0 y p) (iR W j0' y' p')) by exact (proj2 (mIdx_iff VX Hd W _ _) hiLR).
  assert (hI2 : mI W (iL W j0 y p) (rC W)[lsingle3 j0' a' p'])
    by exact (proj2 (mIdx_iff VX Hd W _ _) (LRtm_trans (LRtm_sym hcl) hcL)).
  (* anti-reduction, and the claimed indices *)
  enough (Fin : exists tL tR,
     MRn n (kw_G W) (kw_Δ W) l l' li (sX W) (sA W) (sB W) (sC W) k k' ki (rX W) (rA W) (rB W) (rC W)
       (fun ρ => mS (kw_comp W ρ)) (fun ρ => mP (kw_comp W ρ)) (iL W j0 y p) (iR W j0' y' p') tL tR /\
     [ kw_G W ; kw_Δ W ⊢g app (lamL W j0 y) la lb A1 B1 p ⤳* tL : mL W (iL W j0 y p) @ mlvl l l' li ] /\
     [ kw_G W ; kw_Δ W ⊢g app (lamR W j0' y') la' lb' A1' B1' p' ⤳* tR : mR W (iR W j0' y' p') @ mlvl l l' li ]).
  { destruct Fin as (tL & tR & HM & RL & RR).
    apply (mrn_idx_at n W _ _ _ _ _ _ hI hI2 hc).
    exact (MRn_red n HG HM RL RR). }
  (* β on both sides *)
  pose proof (kw_lequiv W Hk') as Hk'W. pose proof (kw_lequiv W Hkc) as HkcW.
  destruct (LRtm_escape hpB) as [Hp Hp0].
  pose proof (geq_ty_sound (LRtm_tyeq hpB)) as EpB.
  assert (Hp' : [ kw_G W ; kw_Δ W ⊢g p' : (rB W)[lsingle2 j0' (fR W j0' y')] @ k' ]).
  { eapply wf_lconv; [eapply wf_conv; [exact Hp0 | rewrite ge_typeof; exact (eqty_sym _ _ _ _ _ _ EpB)] | exact Hk'W]. }
  pose proof (eqtm_sym _ _ _ _ _ _ _ (geq_tm_sound (LRtm_geq ha0))) as Eaf.
  destruct (ann_conv HS Hj0 Eaf HA1 HB1) as [HA1d HB1d].
  pose proof (lam_app_red HS Wc HY Hc Hj0 Hy Hp Hla Hlb HA1d HB1d) as LA.
  rewrite mBody_single in LA by first [kw_nf | exact (wf_tm_nf Hj0) | exact (wf_tm_nf Hy)].
  pose proof (geq_ty_sound (LRty_tyeq (rA1 (SubRel_refl_r Hd) W VA j0' j0' hj'))) as EAr.
  assert (Eaf' : [ kw_G W ; kw_Δ W ⊢g fR W j0' y' ≅ a' : (rA W)[lsingle j0'] @ k ]).
  { eapply eqtm_lconv; [eapply eqtm_conv; [exact (eqtm_sym _ _ _ _ _ _ _ (geq_tm_sound (LRtm_geq ha0')))
                                           | rewrite ge_typeof; exact (eqty_sym _ _ _ _ _ _ EAr)] | exact (kw_lequiv W Hk)]. }
  pose proof (eqty_wf_l ge_typeof (geq_ty_sound HA1')) as HrBa.
  assert (HA1'k : [ kw_G W ; kw_Δ W ⊢ (rB W)[lsingle2 j0' a'] ≈ A1' @ k' ]) by exact (geq_ty_lconv HA1' Hk'W).
  assert (HB1'k : [ kw_G W ; kw_Δ W ,, (rB W)[lsingle2 j0' a'] @ k'
      ⊢ tyM k k' ki (rX W)⟨↑⟩ (rA W)⟨rlift ↑⟩ (rB W)⟨rlift (rlift ↑)⟩ (rC W)⟨rlift (rlift (rlift ↑))⟩
          (rC W)[llift (lsingle2 j0' a')] ≈ B1' @ mlvl k k' ki ]).
  { eapply geq_ty_lconv; [| exact (lequiv_sym _ _ _ Hff)].
    eapply geq_ty_ctxconv; [exact (eqty_refl _ _ _ _ _ HrBa) | exact (lequiv_sym _ _ _ Hk'W) | | exact HB1'].
    apply ext_wf_g; [eapply wft_lconv; [exact HrBa | exact Hk'W] | exact (lequiv_wf_l _ _ _ Hk'W)]. }
  destruct (ann_conv HS' Hj0r Eaf' HA1'k HB1'k) as [HA1r HB1r].
  pose proof (lam_app_red HS' Wc' HYr Hcr Hj0r Hyr Hp' (lequiv_trans _ _ _ _ Hla' (lequiv_sym _ _ _ Hk'W))
                (lequiv_trans _ _ _ _ Hlb' Hff) HA1r HB1r) as LA'.
  rewrite mBody_single in LA' by first [kw_nf | exact (wf_tm_nf Hj0r) | exact (wf_tm_nf Hyr)].
  (* the [case]s' pieces *)
  destruct (LRtm_escape hcl) as [_ HiL]. destruct (LRtm_escape hcr) as [_ HiRq].
  pose proof (geq_ty_sound (LRty_tyeq (VTyG_kw W VX (SubRel_refl_r Hd)))) as EXr.
  assert (HiR : [ kw_G W ; kw_Δ W ⊢g iR W j0' y' p' : rX W @ ki ]).
  { eapply wf_lconv; [eapply wf_conv; [exact HiRq | rewrite ge_typeof; exact (eqty_sym _ _ _ _ _ _ EXr)]
                     | exact (kw_lequiv W Hki)]. }
  destruct (case_parts HS Wc HY Hc HiL) as (HYo & HMo & HM1 & Hbr & Hv).
  destruct (case_parts HS' Wc' HYr Hcr HiR) as (HYo' & HMo' & HM1' & Hbr' & Hv').
  pose proof (geq_ty_sound (LRtm_tyeq Xs)) as ESum.
  assert (Hlv : lequiv (gL (kw_G W)) (lmax kc' (mlvl k k' ki)) (lmax kc (mlvl l l' li)))
    by exact (lequiv_max _ _ _ _ _ HkcW (lequiv_sym _ _ _ Hff)).
  pose proof (lequiv_wf_r _ _ _ Hff) as Hf'.
  destruct (LRtm_sum_rel Xs) as (w & w' & Hrw & Hrw' & _ & Nww).
  pose proof (tmred_lconv _ _ _ _ _ (tmred_conv _ _ _ _ _ ge_typeof Hrw' ESum) Hlv) as HrwR.
  (* the children's types, side to side *)
  pose proof (LR_M_kw Hwl Hwl' Hwli Hk Hk' Hki VX VA VB VC Hd W _ _ hI) as HRM.
  destruct (escape_ty _ _ _ _ _ _ _ _ HRM) as (_ & _ & ETM).
  pose proof (geq_ty_sound ETM) as DM.
  pose proof (geq_ty_sound (LRty_tyeq (rA1 Hd W VY _ _ hiLR))) as DY.
  pose proof (lequiv_sym _ _ _ Hff) as Hf'f.
  assert (CY : forall T, [ kw_G W ; kw_Δ W ⊢ (sY W)[lsingle (iL W j0 y p)] ≈ T @ kc ] ->
                 [ kw_G W ; kw_Δ W ⊢g (rY W)[lsingle (iR W j0' y' p')] ≅ T @ kc' ]).
  { intros T ET. eapply eqty_lconv; [| exact HkcW].
    exact (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ DY) (geq_ty_sound ET)). }
  assert (CM : forall T, [ kw_G W ; kw_Δ W ⊢ mL W (iL W j0 y p) ≈ T @ mlvl l l' li ] ->
                 [ kw_G W ; kw_Δ W ⊢g mR W (iR W j0' y' p') ≅ T @ mlvl k k' ki ]).
  { intros T ET. eapply eqty_lconv; [| exact Hf'f].
    exact (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ DM) (geq_ty_sound ET)). }
  pose proof (tmred_lconv _ _ _ _ _ LA' Hff) as LAf.
  destruct Nww as [k1 k2 k1' k2' Ca Da Ca' Da' b b' Hk1 Hk2 Hk1' Hk2' ECa ECa' EDa EDa' Rb
                  | k1 k2 k1' k2' Ca Da Ca' Da' b b' Hk1 Hk2 Hk1' Hk2' ECa ECa' EDa EDa' Rb
                  | ν ν' Hν].
  - (* [inl]: a further [corec], related at depth [n] *)
    destruct (LRtm_escape Rb) as [Hb Hb0].
    assert (Hb' : [ kw_G W ; kw_Δ W ⊢g b' : (rY W)[lsingle (iR W j0' y' p')] @ kc' ]).
    { eapply wf_lconv; [eapply wf_conv; [exact Hb0 | rewrite ge_typeof; exact (eqty_sym _ _ _ _ _ _ DY)] | exact HkcW]. }
    pose proof (case_red_inl Wc Hf HYo HMo HM1 Hbr Hv Hrw Hk1 Hk2 (geq_ty_sound ECa) (geq_ty_sound EDa) Hb) as RL.
    pose proof (case_red_inl Wc' Hf' HYo' HMo' HM1' Hbr' Hv' HrwR
                  (lequiv_trans _ _ _ _ Hk1' (lequiv_sym _ _ _ HkcW)) (lequiv_trans _ _ _ _ Hk2' Hff)
                  (CY _ ECa') (CM _ EDa') Hb') as RR.
    rewrite br_single in RL by first [kw_nf | exact (wf_tm_nf HiL)].
    rewrite br_single in RR by first [kw_nf | exact (wf_tm_nf HiR)].
    exists (crL W (iL W j0 y p) b), (crR W (iR W j0' y' p') b').
    refine (conj _ (conj (tmred_trans _ _ _ _ _ LA RL) (tmred_trans _ _ _ _ _ LAf (tmred_lconv _ _ _ _ _ RR Hff)))).
    exact (IH W _ _ _ _ hI (LRtm_irrel_r Rb (rA1 Hd W (VTyG_refl_l VY) _ _ hiLR))).
  - (* [inr]: a finished [M] term, related at every depth *)
    destruct (LRtm_escape Rb) as [Hb Hb0].
    assert (Hb' : [ kw_G W ; kw_Δ W ⊢g b' : mR W (iR W j0' y' p') @ mlvl k k' ki ]).
    { eapply wf_lconv; [eapply wf_conv; [exact Hb0 | rewrite ge_typeof; exact (eqty_sym _ _ _ _ _ _ DM)] | exact Hf'f]. }
    pose proof (case_red_inr Wc Hf HYo HMo HM1 Hbr Hv Hrw Hk1 Hk2 (geq_ty_sound ECa) (geq_ty_sound EDa) Hb) as RL.
    pose proof (case_red_inr Wc' Hf' HYo' HMo' HM1' Hbr' Hv' HrwR
                  (lequiv_trans _ _ _ _ Hk1' (lequiv_sym _ _ _ HkcW)) (lequiv_trans _ _ _ _ Hk2' Hff)
                  (CY _ ECa') (CM _ EDa') Hb') as RR.
    change ((var 0)[lsingle b]) with b in RL. change ((var 0)[lsingle b']) with b' in RR.
    exists b, b'.
    refine (conj _ (conj (tmred_trans _ _ _ _ _ LA RL) (tmred_trans _ _ _ _ _ LAf (tmred_lconv _ _ _ _ _ RR Hff)))).
    exact (LRtm_inv HRM Rb n).
  - (* a neutral continuation: a neutral [case] *)
    pose proof (case_red_ne Wc Hf HYo HMo HM1 Hbr Hv Hrw) as RL.
    pose proof (case_red_ne Wc' Hf' HYo' HMo' HM1' Hbr' Hv' HrwR) as RR.
    eexists _, _.
    refine (conj _ (conj (tmred_trans _ _ _ _ _ LA RL) (tmred_trans _ _ _ _ _ LAf (tmred_lconv _ _ _ _ _ RR Hff)))).
    pose proof (case_ne_at W _ _ ν ν' hiLR Hν) as Hne.
    exact (LR_neutral _ _ _ _ _ _ _ HRM _ _ Hne (gne_tm_conv Hne DM) n).
Qed.

(** ** The λs, related at [Π] *)

(** Related children escape: generically equal at the left type. *)
Lemma mrn_esc n (U : kwk G Δ) m m' t t' : mI U m m' ->
  MRn n (kw_G U) (kw_Δ U) l l' li (sX U) (sA U) (sB U) (sC U) k k' ki (rX U) (rA U) (rB U) (rC U)
    (fun ρ => mS (kw_comp U ρ)) (fun ρ => mP (kw_comp U ρ)) m m' t t' ->
  [ kw_G U ; kw_Δ U ⊢ t ≈ t' : mL U m @ mlvl l l' li ].
Proof using EL VL VN VX VA VB VC Hwl Hwl' Hwli Hk Hk' Hki Hd.
  intros h Ht. destruct (MRn_gen Ht) as (w & w' & R1 & R2 & _ & _ & E1 & _).
  pose proof (LR_M_kw Hwl Hwl' Hwli Hk Hk' Hki VX VA VB VC Hd U _ _ h) as HRM.
  destruct (escape_ty _ _ _ _ _ _ _ _ HRM) as (_ & _ & ETM).
  eapply geq_tm_exp; [exact R1 | | exact E1].
  exact (tmred_conv _ _ _ _ _ ge_typeof R2 (eqty_sym _ _ _ _ _ _ (geq_ty_sound ETM))).
Qed.

Local Notation kidL U j a := (tyM l l' li (sX U)⟨↑⟩ (sA U)⟨rlift ↑⟩ (sB U)⟨rlift (rlift ↑)⟩
  (sC U)⟨rlift (rlift (rlift ↑))⟩ (sC U)[llift (lsingle2 j a)]).
Local Notation kidR U j a := (tyM k k' ki (rX U)⟨↑⟩ (rA U)⟨rlift ↑⟩ (rB U)⟨rlift (rlift ↑)⟩
  (rC U)⟨rlift (rlift (rlift ↑))⟩ (rC U)[llift (lsingle2 j a)]).

(** The λs of related [corec]s' β-reducts at related shapes, related at
    [Π] over the positions' relation, at depth [n] at the children. *)
Lemma lam_at n (IH : CorecAt n) (W : kwk G Δ) j0 j0' y y' a a' :
  mI W j0 j0' -> LRtm kc (kw_G W) (kw_Δ W) (sY W)[lsingle j0] (qY W)[lsingle j0'] y y' ->
  mS W j0 j0' a a' ->
  LRtm l (kw_G W) (kw_Δ W) (sA W)[lsingle j0] (sA W)[lsingle j0] a (fL W j0 y) ->
  LRtm l (kw_G W) (kw_Δ W) (ktyl W A[llift d'])[lsingle j0'] (ktyl W A[llift d'])[lsingle j0'] a' (fR W j0' y') ->
  PiRel (kw_G W) (kw_Δ W) l' (mlvl l l' li) k' (mlvl k k' ki)
    (sB W)[lsingle2 j0 a] (kidL W j0 a) (rB W)[lsingle2 j0' a'] (kidR W j0' a')
    (fun ρ p p' => mP (kw_comp W ρ) (ktm ρ j0) (ktm ρ j0') (ktm ρ a) (ktm ρ a') p p')
    (fun ρ p p' _ => MRn n (kw_G (kw_comp W ρ)) (kw_Δ (kw_comp W ρ)) l l' li
        (sX (kw_comp W ρ)) (sA (kw_comp W ρ)) (sB (kw_comp W ρ)) (sC (kw_comp W ρ))
        k k' ki (rX (kw_comp W ρ)) (rA (kw_comp W ρ)) (rB (kw_comp W ρ)) (rC (kw_comp W ρ))
        (fun ρ'' => mS (kw_comp (kw_comp W ρ) ρ'')) (fun ρ'' => mP (kw_comp (kw_comp W ρ) ρ''))
        (sC (kw_comp W ρ))[lsingle3 (ktm ρ j0) (ktm ρ a) p] (rC (kw_comp W ρ))[lsingle3 (ktm ρ j0') (ktm ρ a') p'])
    (lamL W j0 y) (lamR W j0' y').
Proof using EL VL VN VX VA VB VC VY Vc Vstep Hwl Hwl' Hwli Hwc Hk Hk' Hki Hkc Hd.
  intros hjj hy ha ha0 ha0'.
  pose proof (m_side Hwl Hwl' Hwli Hk Hk' Hki VX VA VB VC Hd) as HMD.
  pose proof (proj1 (mIdx_iff VX Hd W _ _) hjj) as hjL.
  pose proof (LRtm_trans hjL (LRtm_sym hjL)) as hj. pose proof (LRtm_trans (LRtm_sym hjL) hjL) as hj'.
  destruct (args_at W j0 j0' j0 j0' y y' hjj hj hj' hy)
    as (_ & Hj0 & _ & _ & Hj0' & _ & _ & _ & Hy & _ & _).
  destruct (esc_at W) as (HG & HY & EY & Hc & Hc' & Ec).
  destruct (rside_at W j0 j0' j0 j0' y y' hjj hj hj' hy) as (HS' & HYr & Hcr & _ & Hj0r & _ & Hyr).
  pose proof HG as (H1 & H2 & H3 & HS & _).
  pose proof HS as (W1 & W2 & Wi & _).
  pose proof (MGeq_ctx HG) as HΔW.
  pose proof (kw_lwf W Hwc) as Wc. pose proof (lequiv_wf_l _ _ _ (kw_lequiv W Hkc)) as Wc'.
  assert (Hf : lwf (gL (kw_G W)) (mlvl l l' li)) by (cbn; repeat split; assumption).
  pose proof (lequiv_mlvl H1 H2 H3) as Hff. pose proof (lequiv_wf_r _ _ _ Hff) as Hf'.
  pose proof (kw_lequiv W Hk') as Hk'W.
  (* the types *)
  pose proof (ms_gBa HMD W _ _ _ _ hjj ha) as GB.
  pose proof (geq_ty_sound GB) as DB.
  pose proof (eqty_wf_l ge_typeof DB) as HBa. pose proof (eqty_wf_r ge_typeof DB) as HBa'.
  pose proof (MGeq_M (MGeq_wk1 HG (ext_wf_g HBa W2)) (ms_gCa HMD W _ _ _ _ hjj ha)) as GK.
  pose proof (eqty_wf_l ge_typeof (geq_ty_sound GK)) as HK.
  assert (GK' : [ kw_G W ; kw_Δ W ,, (rB W)[lsingle2 j0' a'] @ l' ⊢ kidR W j0' a' ≈ kidL W j0 a @ mlvl l l' li ])
    by exact (geq_ty_ctxconv DB (lequiv_refl _ _ W2) (ext_wf_g HBa' W2) (geq_ty_sym GK)).
  pose proof (geq_ty_sound (geq_ty_pi (lequiv_sym _ _ _ Hk'W) Hff HBa GB GK)) as ES.
  (* the λs, at the shapes' instances *)
  destruct (pre_out_corec_parts ge_typeof ge_notV HS Wc HY Hc Hj0 Hy _ _
              (mBody l l' li (sX W) (sA W) (sB W) (sC W) kc (sY W) (sc W) j0 y)
              ltac:(unfold mOutCorec, mBody; reflexivity)) as (_ & HBf & Hb).
  assert (Hl0 : [ kw_G W ; kw_Δ W ⊢g lamL W j0 y
                  : tyPi l' (mlvl l l' li) (sB W)[lsingle2 j0 (fL W j0 y)] (kidL W j0 (fL W j0 y))
                  @ lmax l' (mlvl l l' li) ])
    by (unfold mLam; apply wf_lam; auto using ge_notV).
  pose proof (eqtm_sym _ _ _ _ _ _ _ (geq_tm_sound (LRtm_geq ha0))) as Eaf.
  destruct (ann_conv HS Hj0 Eaf (geq_ty_trans GB (geq_ty_sym GB)) (geq_ty_trans GK (geq_ty_sym GK)))
    as [EB1 EK1].
  assert (Hw : [ kw_G W ; kw_Δ W ⊢g lamL W j0 y : tyPi l' (mlvl l l' li) (sB W)[lsingle2 j0 a] (kidL W j0 a)
                 @ lmax l' (mlvl l l' li) ]).
  { eapply wf_conv; [exact Hl0 | rewrite ge_typeof; apply eqty_sym].
    apply eqty_pi; auto using ge_notV, lequiv_refl. }
  destruct (pre_out_corec_parts ge_typeof ge_notV HS' Wc' HYr Hcr Hj0r Hyr _ _
              (mBody k k' ki (rX W) (rA W) (rB W) (rC W) kc' (rY W) (rc W) j0' y')
              ltac:(unfold mOutCorec, mBody; reflexivity)) as (_ & HBf' & Hb').
  pose proof HS' as (W1' & W2' & Wi' & _).
  assert (Hf'' : lwf (gL (kw_G W)) (mlvl k k' ki)) by (cbn; repeat split; assumption).
  assert (Hr0 : [ kw_G W ; kw_Δ W ⊢g lamR W j0' y'
                  : tyPi k' (mlvl k k' ki) (rB W)[lsingle2 j0' (fR W j0' y')] (kidR W j0' (fR W j0' y'))
                  @ lmax k' (mlvl k k' ki) ])
    by (unfold mLam; apply wf_lam; auto using ge_notV).
  pose proof (geq_ty_sound (LRty_tyeq (rA1 (SubRel_refl_r Hd) W VA j0' j0' hj'))) as EAr.
  assert (Eaf' : [ kw_G W ; kw_Δ W ⊢g fR W j0' y' ≅ a' : (rA W)[lsingle j0'] @ k ]).
  { eapply eqtm_lconv; [eapply eqtm_conv; [exact (eqtm_sym _ _ _ _ _ _ _ (geq_tm_sound (LRtm_geq ha0')))
                                           | rewrite ge_typeof; exact (eqty_sym _ _ _ _ _ _ EAr)] | exact (kw_lequiv W Hk)]. }
  assert (GKr : [ kw_G W ; kw_Δ W ,, (rB W)[lsingle2 j0' a'] @ k' ⊢ kidR W j0' a' ≈ kidR W j0' a' @ mlvl k k' ki ]).
  { eapply geq_ty_lconv; [| exact (lequiv_sym _ _ _ Hff)].
    eapply geq_ty_ctxconv; [exact (eqty_refl _ _ _ _ _ HBa') | exact (lequiv_sym _ _ _ Hk'W) | |
                            exact (geq_ty_trans GK' (geq_ty_sym GK'))].
    apply ext_wf_g; [eapply wft_lconv; [exact HBa' | exact Hk'W] | exact (lequiv_wf_l _ _ _ Hk'W)]. }
  destruct (ann_conv HS' Hj0r Eaf' (geq_ty_lconv (geq_ty_trans (geq_ty_sym GB) GB) Hk'W) GKr) as [EB1' EK1'].
  assert (Hw' : [ kw_G W ; kw_Δ W ⊢g lamR W j0' y' : tyPi k' (mlvl k k' ki) (rB W)[lsingle2 j0' a'] (kidR W j0' a')
                  @ lmax l' (mlvl l l' li) ]).
  { eapply wf_lconv; [| exact (lequiv_max _ _ _ _ _ H2 Hff)].
    eapply wf_conv; [exact Hr0 | rewrite ge_typeof; apply eqty_sym].
    apply eqty_pi; auto using ge_notV, lequiv_refl. }
  destruct (LRtm_escape ha0) as [Ha _]. destruct (LRtm_escape ha0') as [Ha' _].
  refine (PiRel_intro HΔW W2 Hf HBa HK HBa' (geq_ty_trans GB (geq_ty_sym GB)) (geq_ty_trans GK (geq_ty_sym GK))
            (geq_ty_sym GB) GK' ES Hw Hw' ltac:(unfold mLam; apply whnf_lam) ltac:(unfold mLam; apply whnf_lam) _ _ _).
  - (* the variable *)
    intros Hw1 HΔA. set (ρ1 := kw_loc wk1 Hw1 HΔA).
    pose proof (m_imon VX Hd W ρ1 _ _ hjj) as hx1. pose proof (m_shmon VX VA Hd W ρ1 _ _ _ _ hjj ha) as ha1.
    apply (proj2 (mPos_iff VX VA VB Hd _ _ _ _ _ _ _ hx1 ha1)).
    pose proof (rB2 Hd (kw_comp W ρ1) (VTyG_refl_l VB) _ _ _ _ (proj1 (mIdx_iff VX Hd _ _ _) hx1)
                  (proj1 (mSh_iff VX VA Hd _ _ _ _ _ hx1) ha1)) as TB.
    rewrite !(ktyll_comp W ρ1), <- !(kty_lsingle2 ρ1) in TB |- *. unfold ρ1 in TB |- *. rewrite !kwk1_ty in TB |- *.
    exact (var0_LRtm TB HΔA).
  - (* escape *)
    intros ρ p p' h u u' Hu.
    pose proof (m_imon VX Hd W ρ _ _ hjj) as hx. pose proof (m_shmon VX VA Hd W ρ _ _ _ _ hjj ha) as hs.
    rewrite kw_kid_single by first [kw_nf | exact (wf_tm_nf Hj0) | exact (wf_tm_nf Ha)].
    rewrite <- (kty_comp W ρ), <- (ktyl_comp W ρ), <- (ktyll_comp W ρ), <- !(ktmlll_comp W ρ).
    exact (mrn_esc n (kw_comp W ρ) _ _ u u' (m_ch VX VA VB VC Hd (kw_comp W ρ) _ _ _ _ p p' hx hs h) Hu).
  - (* the Kripke clause *)
    intros ρ p p' hp la lb la' lb' A1 B1 A1' B1' Hla Hlb Hla' Hlb' HA1 HB1 HA1' HB1'. cbv beta.
    pose proof (m_imon VX Hd W ρ _ _ hjj) as hx. pose proof (m_shmon VX VA Hd W ρ _ _ _ _ hjj ha) as hs.
    pose proof (LRtm_kw ρ hy) as hy3. rewrite !kty_lsingle, <- !(ktyl_comp W ρ) in hy3.
    pose proof (LRtm_kw ρ ha0) as ha3. rewrite !kty_lsingle, <- !(ktyl_comp W ρ), ktm_mOutFst in ha3.
    pose proof (LRtm_kw ρ ha0') as ha3'. rewrite !kty_lsingle, <- !(ktyl_comp W ρ), ktm_mOutFst in ha3'.
    rewrite <- (kty_comp W ρ), <- !(ktyl_comp W ρ), <- (ktyll_comp W ρ), <- (ktmlll_comp W ρ), <- (ktmll_comp' W ρ)
      in ha3, ha3'.
    rewrite !kty_lsingle2, <- !(ktyll_comp W ρ) in HA1, HA1', HB1, HB1'.
    rewrite !kw_kid in HB1, HB1'.
    rewrite <- (kty_comp W ρ), <- (ktyl_comp W ρ), <- (ktyll_comp W ρ), <- !(ktmlll_comp W ρ) in HB1, HB1'.
    rewrite !ktm_mLam, <- !(kty_comp W ρ), <- !(ktyl_comp W ρ), <- !(ktyll_comp W ρ), <- !(ktmlll_comp W ρ),
      <- !(ktmll_comp' W ρ).
    exact (kid_at n IH (kw_comp W ρ) _ _ _ _ _ _ p p' la lb A1 B1 la' lb' A1' B1' hx hy3 hs ha3 ha3' hp
             (kw_lequiv ρ Hla) (kw_lequiv ρ Hlb) (kw_lequiv ρ Hla') (kw_lequiv ρ Hlb') HA1 HB1 HA1' HB1').
Qed.

(** ** The β-reducts of related [corec]s, related at [out]'s type *)
Lemma pair_at n (IH : CorecAt n) (W : kwk G Δ) j0 j0' y y' :
  mI W j0 j0' -> LRtm kc (kw_G W) (kw_Δ W) (sY W)[lsingle j0] (qY W)[lsingle j0'] y y' ->
  MOutR (MRn n) (kw_G W) (kw_Δ W) l l' li (sX W) (sA W) (sB W) (sC W) k k' ki (rX W) (rA W) (rB W) (rC W)
    (fun ρ => mS (kw_comp W ρ)) (fun ρ => mP (kw_comp W ρ)) j0 j0'
    (mOutCorec l l' li (sX W) (sA W) (sB W) (sC W) kc (sY W) (sc W) j0 y)
    (mOutCorec k k' ki (rX W) (rA W) (rB W) (rC W) kc' (rY W) (rc W) j0' y').
Proof using EL VL VN VX VA VB VC VY Vc Vstep Hwl Hwl' Hwli Hwc Hk Hk' Hki Hkc Hd.
  intros hjj hy. unfold MOutR.
  pose proof (m_side Hwl Hwl' Hwli Hk Hk' Hki VX VA VB VC Hd) as HMD.
  pose proof (MSide_kw W HMD) as HMW.
  pose proof (proj1 (mIdx_iff VX Hd W _ _) hjj) as hjL.
  pose proof (LRtm_trans hjL (LRtm_sym hjL)) as hj. pose proof (LRtm_trans (LRtm_sym hjL) hjL) as hj'.
  destruct (args_at W j0 j0' j0 j0' y y' hjj hj hj' hy)
    as (_ & Hj0 & _ & _ & Hj0' & _ & _ & _ & Hy & _ & _).
  destruct (esc_at W) as (HG & _).
  pose proof HG as (H1 & H2 & H3 & HS & _).
  pose proof HS as (W1 & W2 & Wi & _).
  pose proof (MGeq_ctx HG) as HΔW.
  assert (Hf : lwf (gL (kw_G W)) (mlvl l l' li)) by (cbn; repeat split; assumption).
  pose proof (lequiv_mlvl H1 H2 H3) as Hff.
  assert (I : forall ρ, mI (kw_comp W ρ) (ktm ρ j0) (ktm ρ j0')) by (intros ρ; exact (m_imon VX Hd W ρ _ _ hjj)).
  destruct (MSide_root HMW (wf_tm_nf Hj0) (wf_tm_nf Hj0') I) as (Em & EA & EB & EC).
  pose proof (M_outB_geq HG EB EC) as EPi.
  pose proof (geq_ty_sound EA) as DA.
  pose proof (eqty_wf_l ge_typeof DA) as HA. pose proof (eqty_wf_r ge_typeof DA) as HA'.
  pose proof (geq_ty_ctxconv DA (lequiv_refl _ _ W1) (ext_wf_g HA' W1) (geq_ty_sym EPi)) as RB'.
  pose proof (eqty_wf_l ge_typeof (geq_ty_sound EPi)) as HB.
  pose proof (eqty_wf_l ge_typeof (geq_ty_sound RB')) as HB'.
  pose proof (M_out_eq ge_typeof ge_notV (MEq_of_MGeq HG) Hj0 Hj0' (geq_tm_sound Em)) as ES.
  destruct (esc_at W) as (_ & HY & _ & Hc & _).
  destruct (rside_at W j0 j0' j0 j0' y y' hjj hj hj' hy) as (HS' & HYr & Hcr & _ & Hj0r & _ & Hyr).
  pose proof (pre_out_corec ge_typeof ge_notV HS (kw_lwf W Hwc) HY Hc Hj0 Hy) as Hw.
  pose proof (tmred_wf _ _ _ _ _ _ _ (tmred_lconv _ _ _ _ _
                (tmred_refl _ _ _ (pre_out_corec ge_typeof ge_notV HS' (lequiv_wf_l _ _ _ (kw_lequiv W Hkc))
                                     HYr Hcr Hj0r Hyr))
                (lequiv_max _ _ _ _ _ H1 Hff))) as Hw'.
  refine (SigRel_intro HΔW W1 Hf HA HB HA' HB' (geq_ty_trans EA (geq_ty_sym EA)) (geq_ty_trans EPi (geq_ty_sym EPi))
            (geq_ty_sym EA) RB' ES Hw Hw' ltac:(unfold mOutCorec; apply whnf_pair)
            ltac:(unfold mOutCorec; apply whnf_pair) _ _ _).
  - (* the shapes escape *)
    intros ρ x x' h. rewrite kty_lsingle. exact (ms_eS HMW ρ _ _ x x' (I ρ) h).
  - (* the children's functions escape *)
    intros ρ x x' h u u' Hu. cbv beta in Hu.
    rewrite !ktyl_Pi_single. rewrite !kw_B_single, !kw_mKid in Hu. rewrite !kw_B_single, !kw_mKid.
    rewrite !mKid_single in Hu by kw_nf. rewrite !mKid_single by kw_nf.
    pose proof (ms_gBa HMW ρ _ _ x x' (I ρ) h) as GB.
    pose proof (eqty_wf_l ge_typeof (geq_ty_sound GB)) as HBx.
    pose proof (MGeq_M (MGeq_wk1 (MGeq_kw ρ HG) (ext_wf_g HBx (kw_lwf ρ W2))) (ms_gCa HMW ρ _ _ x x' (I ρ) h)) as K.
    eapply geq_tm_lconv; [| apply lequiv_sym, M_lv_f; apply (kw_lwf ρ); assumption].
    exact (PiRel_geq Hu (geq_ty_sound (geq_ty_pi (kw_lequiv ρ H2) (kw_lequiv ρ Hff) HBx GB K))).
  - (* the Kripke clause *)
    intros ρ la lb la' lb' Aa Ba Aa' Ba' Hla Hlb Hla' Hlb' HA1 HB1 HA1' HB1'. cbv beta.
    (* the world's own premises *)
    pose proof (I ρ) as hjj2.
    pose proof (LRtm_kw ρ hy) as hy2. rewrite !kty_lsingle, <- !(ktyl_comp W ρ) in hy2.
    pose proof (proj1 (mIdx_iff VX Hd _ _ _) hjj2) as hjL2.
    pose proof (LRtm_trans hjL2 (LRtm_sym hjL2)) as hj2. pose proof (LRtm_trans (LRtm_sym hjL2) hjL2) as hj2'.
    destruct (args_at (kw_comp W ρ) _ _ _ _ _ _ hjj2 hj2 hj2' hy2)
      as (_ & Hj2 & _ & _ & Hj2' & _ & _ & _ & Hy2 & _ & _).
    destruct (esc_at (kw_comp W ρ)) as (HG2 & HY2 & _ & Hc2 & _).
    destruct (rside_at (kw_comp W ρ) _ _ _ _ _ _ hjj2 hj2 hj2' hy2) as (HS2' & HYr2 & Hcr2 & _ & Hj2r & _ & Hyr2).
    pose proof HG2 as (_ & _ & _ & HS2 & _).
    pose proof (kw_lwf (kw_comp W ρ) Hwc) as Wc2.
    pose proof (lequiv_wf_l _ _ _ (kw_lequiv (kw_comp W ρ) Hkc)) as Wc2'.
    destruct (steps_at (kw_comp W ρ) _ _ _ _ hjL2 hy2) as [Ff _].
    (* the annotations at the world's own types *)
    rewrite !kty_lsingle, <- !(ktyl_comp W ρ) in HA1, HA1', HB1, HB1'.
    rewrite !ktyl_tyPi, !ktyl_llift_single, !kw_mKid in HB1, HB1'.
    rewrite <- (kty_comp W ρ), <- (ktyl_comp W ρ), <- !(ktyll_comp W ρ), <- (ktmlll_comp W ρ) in HB1, HB1'.
    (* the pairs at the world's own premises *)
    rewrite !ktm_mOutCorec, <- !(kty_comp W ρ), <- !(ktyl_comp W ρ), <- !(ktyll_comp W ρ), <- !(ktmlll_comp W ρ),
      <- !(ktmll_comp' W ρ).
    (* the first projections *)
    pose proof (kw_lequiv (kw_comp W ρ) Hk) as HkW.
    pose proof (kw_lequiv ρ Hff) as Hffρ.
    pose proof (out_fst_red HS2 Wc2 HY2 Hc2 Hj2 Hy2 (kw_lequiv ρ Hla) (kw_lequiv ρ Hlb)
                  (geq_ty_sound HA1) (geq_ty_sound HB1)) as RF.
    pose proof (eqty_wf_l ge_typeof (geq_ty_sound HA1')) as HrA.
    assert (HB1r : [ kw_G ρ ; kw_Δ ρ ,, (rA (kw_comp W ρ))[lsingle (ktm ρ j0')] @ k
                     ⊢g tyPi k' (mlvl k k' ki) (rB (kw_comp W ρ))[llift (lsingle (ktm ρ j0'))]
                          (mKidTy k k' ki (rX (kw_comp W ρ)) (rA (kw_comp W ρ)) (rB (kw_comp W ρ)) (rC (kw_comp W ρ))
                             (ktm ρ j0')) ≅ Ba' @ mlvl k k' ki ]).
    { apply geq_ty_sound. eapply geq_ty_lconv; [| exact (lequiv_sym _ _ _ Hffρ)].
      eapply geq_ty_ctxconv; [exact (eqty_refl _ _ _ _ _ HrA) | exact (lequiv_sym _ _ _ HkW) | | exact HB1'].
      apply ext_wf_g; [eapply wft_lconv; [exact HrA | exact HkW] | exact (lequiv_wf_l _ _ _ HkW)]. }
    pose proof (out_fst_red HS2' Wc2' HYr2 Hcr2 Hj2r Hyr2
                  (lequiv_trans _ _ _ _ (kw_lequiv ρ Hla') (lequiv_sym _ _ _ HkW))
                  (lequiv_trans _ _ _ _ (kw_lequiv ρ Hlb') Hffρ)
                  (geq_ty_sound (geq_ty_lconv HA1' HkW)) HB1r) as RF'.
    pose proof (tmred_lconv _ _ _ _ _ RF' (lequiv_sym _ _ _ HkW)) as RF'l.
    pose proof (LRtm_red Ff RF RF'l) as Xf.
    assert (h := proj2 (mSh_iff VX VA Hd _ _ _ _ _ hjj2) (LRtm_irrel_r Xf (rA1 Hd _ (VTyG_refl_l VA) _ _ hjL2))).
    refine (ex_intro _ h _).
    (* the second projections, the λs *)
    rewrite !kw_B_single, <- !(ktyll_comp W ρ), !kw_mKid. rewrite !mKid_single by kw_nf.
    rewrite <- ?(kty_comp W ρ), <- ?(ktyl_comp W ρ), <- ?(ktyll_comp W ρ), <- ?(ktmlll_comp W ρ).
    pose proof (out_snd_red HS2 Wc2 HY2 Hc2 Hj2 Hy2 (kw_lequiv ρ Hla) (kw_lequiv ρ Hlb)
                  (geq_ty_sound HA1) (geq_ty_sound HB1)) as RS.
    pose proof (out_snd_red HS2' Wc2' HYr2 Hcr2 Hj2r Hyr2
                  (lequiv_trans _ _ _ _ (kw_lequiv ρ Hla') (lequiv_sym _ _ _ HkW))
                  (lequiv_trans _ _ _ _ (kw_lequiv ρ Hlb') Hffρ)
                  (geq_ty_sound (geq_ty_lconv HA1' HkW)) HB1r) as RS'.
    refine (PiRel_red _ RS (tmred_lconv _ _ _ _ _ RS' (lequiv_max _ _ _ _ _ (kw_lequiv ρ H2) Hffρ))).
    pose proof (LRtm_red_l (LRtm_trans Ff (LRtm_sym Ff)) RF) as hx0.
    pose proof (LRtm_red_l (LRtm_trans (LRtm_sym Ff) Ff) RF'l) as hx1.
    pose proof (LRtm_irrel_r (LRtm_conv_l hx1 (rA1 (SubRel_refl_r Hd) _ VA _ _ hj2'))
                  (rA1 (SubRel_refl_r Hd) _ (VTyG_refl_l VA) _ _ hj2')) as hx0'.
    eapply PiRel_impl; [| | exact (lam_at n IH (kw_comp W ρ) _ _ _ _ _ _ hjj2 hy2 h hx0 hx0')].
    + intros ρ' p p' hp. cbv beta in hp |- *. rewrite !(ktm_comp ρ ρ') in hp. exact hp.
    + intros ρ' p p' hh hh' u u' Hu. cbv beta in Hu |- *.
      rewrite ?kty_comp, ?ktyl_comp, ?ktyll_comp, ?ktmlll_comp, ?ktm_comp in Hu.
      rewrite ?kty_comp, ?ktyl_comp, ?ktyll_comp, ?ktmlll_comp, ?ktm_comp. exact Hu.
Qed.

(** ** The observations of related [corec]s *)
Lemma obs_at n (IH : CorecAt n) (W : kwk G Δ) j0 j0' y y' :
  mI W j0 j0' -> LRtm kc (kw_G W) (kw_Δ W) (sY W)[lsingle j0] (qY W)[lsingle j0'] y y' ->
  MObs (MRn n) (kw_G W) (kw_Δ W) l l' li (sX W) (sA W) (sB W) (sC W) k k' ki (rX W) (rA W) (rB W) (rC W)
    (fun ρ => mS (kw_comp W ρ)) (fun ρ => mP (kw_comp W ρ)) j0 j0' (crL W j0 y) (crR W j0' y').
Proof using EL VL VN VX VA VB VC VY Vc Vstep Hwl Hwl' Hwli Hwc Hk Hk' Hki Hkc Hd.
  intros hjj hy. unfold MObs. intros * Ann Ann'.
  pose proof (proj1 (mIdx_iff VX Hd W _ _) hjj) as hjL.
  pose proof (LRtm_trans hjL (LRtm_sym hjL)) as hj. pose proof (LRtm_trans (LRtm_sym hjL) hjL) as hj'.
  destruct (red_at W _ _ _ _ _ _ hjj hj hj' hy _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Ann Ann') as [RL RR].
  exact (SigRel_red (pair_at n IH W j0 j0' y y' hjj hy) RL RR).
Qed.

(** ** The depth induction *)
Lemma gen_at (U : kwk G Δ) j0 j0' y y' :
  mI U j0 j0' -> LRtm kc (kw_G U) (kw_Δ U) (sY U)[lsingle j0] (qY U)[lsingle j0'] y y' ->
  MGen (kw_G U) (kw_Δ U) l l' li (sX U) (sA U) (sB U) (sC U) k k' ki (rX U) (rA U) (rB U) (rC U)
    j0 j0' (crL U j0 y) (crR U j0' y').
Proof using EL VL VN VX VA VB VC VY Vc Hwl Hwl' Hwli Hwc Hk Hk' Hki Hkc Hd.
  intros hjj hy.
  pose proof (proj1 (mIdx_iff VX Hd U _ _) hjj) as hjL.
  pose proof (LRtm_trans hjL (LRtm_sym hjL)) as hj. pose proof (LRtm_trans (LRtm_sym hjL) hjL) as hj'.
  destruct (typ_at U j0 j0' j0 j0' y y' hjj hj hj' hy) as (HL & HR & Ecr).
  pose proof (LR_M_kw Hwl Hwl' Hwli Hk Hk' Hki VX VA VB VC Hd U _ _ hjj) as HRM.
  destruct (escape_ty _ _ _ _ _ _ _ _ HRM) as (_ & _ & ETM). pose proof (geq_ty_sound ETM) as DM.
  exists (crL U j0 y), (crR U j0' y').
  refine (conj (tmred_refl _ _ _ HL) (conj (tmred_refl _ _ _ _) (conj (whnf_corec _ _ _ _ _ _ _ _ _ _ _ _)
            (conj (whnf_corec _ _ _ _ _ _ _ _ _ _ _ _) (conj Ecr (geq_tm_conv Ecr DM)))))).
  eapply wf_conv; [exact HR | rewrite ge_typeof; exact (eqty_sym _ _ _ _ _ _ DM)].
Qed.

Lemma corec_all n : CorecAt n.
Proof using EL VL VN VX VA VB VC VY Vc Vstep Hwl Hwl' Hwli Hwc Hk Hk' Hki Hkc Hd.
  induction n as [|n IH]; intros U j0 j0' y y' hjj hy;
    (split; [exact (gen_at U j0 j0' y y' hjj hy) |]); [exact Logic.I |].
  intros ρ. cbv beta.
  pose proof (m_imon VX Hd U ρ _ _ hjj) as hjj2.
  pose proof (LRtm_kw ρ hy) as hy2. rewrite !kty_lsingle, <- !(ktyl_comp U ρ) in hy2.
  pose proof (obs_at n IH (kw_comp U ρ) _ _ _ _ hjj2 hy2) as Ho.
  rewrite !ktm_corec, <- ?(kty_comp U ρ), <- ?(ktyl_comp U ρ), <- ?(ktyll_comp U ρ), <- ?(ktmlll_comp U ρ),
    <- ?(ktmll_comp' U ρ).
  exact Ho.
Qed.

End CorecV.

(** ** The rules *)

Section CorecRules.
Context {G : gctx} {Γ : ctx} {l l' li k k' ki kc kc' : lvl} {X X' A A' B B' Y Y' : ty} {C C' c c' m m' y y' : tm}
  (Hwl : lwf (gL G) l) (Hwl' : lwf (gL G) l') (Hwli : lwf (gL G) li) (Hwc : lwf (gL G) kc)
  (Hk : lequiv (gL G) k l) (Hk' : lequiv (gL G) k' l') (Hki : lequiv (gL G) ki li) (Hkc : lequiv (gL G) kc' kc)
  (VX : VTyG G Γ X X' li) (VA : VTyG G (Γ ,, X @ li) A A' l)
  (VB : VTyG G (Γ ,, X @ li ,, A @ l) B B' l')
  (VC : VTmG G (Γ ,, X @ li ,, A @ l ,, B @ l') C C' X⟨↑⟩⟨↑⟩⟨↑⟩ li)
  (VY : VTyG G (Γ ,, X @ li) Y Y' kc)
  (Vc : VTmG G (Γ ,, X @ li ,, Y @ kc) c c' (mStepTy l l' li X A B C kc Y)⟨↑⟩ (lmax l (lmax kc (mlvl l l' li))))
  (HX : [ G ; Γ ⊢g X @ li ]) (HA : [ G ; Γ ,, X @ li ⊢g A @ l ]) (HB : [ G ; Γ ,, X @ li ,, A @ l ⊢g B @ l' ])
  (HC : [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ⊢g C : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ]) (HY : [ G ; Γ ,, X @ li ⊢g Y @ kc ])
  (Vm : VTm G Γ m m' X li) (Vy : VTm G Γ y y' Y[lsingle m] kc).

(** The premises at related substitutions, in the identity world: the
    index related by the canonical relation, the seed at the carrier,
    and the normal forms the identity world's renamings need. *)
Lemma corec_self {Δ d d'} (Hd : SubRel G Γ Δ d d') (HΔ : [ G ; Δ ⊢g ]) :
  mIdx (G := G) (X := X) (X' := X') (l := l) (l' := l') (li := li) Δ d d' (kw_self HΔ) m[d] m'[d'] /\
  LRtm kc G Δ Y[llift d][lsingle m[d]] Y[llift d'][lsingle m'[d']] y[d] y'[d'] /\
  nftm m[d] /\ nftm m'[d'] /\ nftm y[d] /\ nftm y'[d'] /\
  nfty Y[llift d] /\ nfty Y[llift d'] /\ nfty Y'[llift d'] /\ nftm c[llift (llift d)] /\ nftm c'[llift (llift d')].
Proof using EL VL VN VX VY Vc Hwli Hwc Vm Vy.
  destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  pose proof (Vm _ _ _ Hd) as Xm. pose proof (Vy _ _ _ Hd) as Xy.
  rewrite (single_subst_ty _ Nd), (single_subst_ty _ Nd') in Xy.
  destruct (LRtm_escape Xm) as [Hmd Hm'd]. destruct (LRtm_escape Xy) as [Hyd Hy'd].
  pose proof (VTy_refl_l (VTyG_loc VY) _ _ _ (SubRel_cons Hd Xm)) as TY.
  rewrite <- (lift_single_ty _ _ _ Nd), <- (lift_single_ty _ _ _ Nd') in TY.
  destruct (VTyG_loc VX _ _ _ Hd) as [RX HRX]. destruct (escape_ty _ _ _ _ _ _ _ _ HRX) as (HXD & _ & _).
  pose proof (SubRel_lift Hd (VTy_refl_l (VTyG_loc VX)) HXD Hwli) as Hl1.
  destruct (VTyG_loc VY _ _ _ Hl1) as [RY HRY]. destruct (escape_ty _ _ _ _ _ _ _ _ HRY) as (HYD & HYD' & _).
  destruct (VTy_refl_l (VTyG_loc VY) _ _ _ Hl1) as [RY0 HRY0].
  destruct (escape_ty _ _ _ _ _ _ _ _ HRY0) as (_ & HYD0 & _).
  pose proof (SubRel_lift Hl1 (VTy_refl_l (VTyG_loc VY)) HYD Hwc) as Hl2.
  destruct (LRtm_escape (VTmG_loc Vc _ _ _ Hl2)) as [Hcd Hc'd].
  refine (conj _ (conj (LRtm_irrel_r Xy TY) (conj (wf_tm_nf Hmd) (conj (wf_tm_nf Hm'd) (conj (wf_tm_nf Hyd)
            (conj (wf_tm_nf Hy'd) (conj (wf_ty_nf HYD) (conj (wf_ty_nf HYD0) (conj (wf_ty_nf HYD') (conj (wf_tm_nf Hcd) (wf_tm_nf Hc'd))))))))))).
  apply (mIdx_iff VX Hd). pose proof (LRtm_kw (kw_self HΔ) Xm) as Z.
  rewrite !ktm_self in Z by exact (wf_tm_nf Hmd) || exact (wf_tm_nf Hm'd). exact Z.
Qed.

Lemma V_corec : VTm G Γ (tmCorec l l' li X A B C kc Y c m y) (tmCorec k k' ki X' A' B' C' kc' Y' c' m' y')
  (tyM l l' li X A B C m) (mlvl l l' li).
Proof using EL VL VN VX VA VB VC VY Vc Hwl Hwl' Hwli Hwc Hk Hk' Hki Hkc HX HA HB HC HY Vm Vy.
  pose proof (VG_mStepTy Hwl Hwl' Hwli Hwc Hk Hk' Hki Hkc VX VA VB VC VY HX HA HB HC HY) as Vstep.
  intros Δ d d' Hd. pose proof (SubRel_ctx Hd) as HΔ.
  rewrite !subst_corec, !subst_tyM.
  pose proof (Vm _ _ _ Hd) as Xm.
  destruct (corec_self Hd HΔ) as (hjj & hy & Nm & Nm' & Ny & Ny' & NY & NYd & NY' & Nc & Nc').
  destruct (MGeq_nf (ms_geq (m_side Hwl Hwl' Hwli Hk Hk' Hki VX VA VB VC Hd)))
    as (NX & NA & NB & NC & NX' & NA' & NB' & NC').
  eapply LRtm_irrel_r.
  - eexists; split; [exact (LR_M_at Hwl Hwl' Hwli Hk Hk' Hki VX VA VB VC _ _ _ _ _ Hd Xm) |].
    intros n.
    assert (hy' : LRtm kc (kw_G (kw_self HΔ)) (kw_Δ (kw_self HΔ)) (ktyl (kw_self HΔ) Y[llift d])[lsingle m[d]]
                    (ktyl (kw_self HΔ) Y[llift d'])[lsingle m'[d']] y[d] y'[d'])
      by (rewrite !ktyl_self by assumption; exact hy).
    pose proof (corec_all Hwl Hwl' Hwli Hwc Hk Hk' Hki Hkc VX VA VB VC VY Vstep Vc Hd n (kw_self HΔ) _ _ _ _ hjj hy')
      as H.
    rewrite !kty_self, !ktyl_self, !ktyll_self, !ktmlll_self, !ktmll_self in H by assumption.
    exact H.
  - pose proof (VTm_trans Vm (VTm_sym Vm) _ _ _ Hd) as Xmm.
    eexists. exact (LR_M_at Hwl Hwl' Hwli (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwl') (lequiv_refl _ _ Hwli)
                      (VTyG_refl_l VX) (VTyG_refl_l VA) (VTyG_refl_l VB) (VTmG_trans VC (VTmG_sym VC))
                      _ _ _ _ _ Hd Xmm).
Qed.

Lemma V_out_corec :
  VTm G Γ (tmOut l l' li X A B C m (tmCorec l l' li X A B C kc Y c m y)) (mOutCorec k k' ki X' A' B' C' kc' Y' c' m' y')
    (mOutTy l l' li X A B C m) (lmax l (mlvl l l' li)).
Proof using EL VL VN VX VA VB VC VY Vc Hwl Hwl' Hwli Hwc Hk Hk' Hki Hkc HX HA HB HC HY Vm Vy.
  pose proof (VG_mStepTy Hwl Hwl' Hwli Hwc Hk Hk' Hki Hkc VX VA VB VC VY HX HA HB HC HY) as Vstep.
  intros Δ d d' Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd']. pose proof (SubRel_ctx Hd) as HΔ.
  rewrite subst_out, subst_corec, !subst_mOutTy, (subst_mOutCorec _ _ _ _ _ _ _ _ _ _ _ _ _ Nd') by assumption.
  pose proof (Vm _ _ _ Hd) as Xm. destruct (LRtm_escape Xm) as [Hmd Hm'd].
  destruct (corec_self Hd HΔ) as (hjj & hy & Nm & Nm' & Ny & Ny' & NY & NYd & NY' & Nc & Nc').
  pose proof (ms_geq (m_side Hwl Hwl' Hwli Hk Hk' Hki VX VA VB VC Hd)) as HG.
  destruct (MGeq_nf HG) as (NX & NA & NB & NC & NX' & NA' & NB' & NC').
  pose proof (MEq_of_MGeq HG) as HE. pose proof (MEq_sig_r ge_typeof ge_notV HE) as HS'.
  pose proof HE as (_ & _ & _ & HS & HXX & _).
  assert (Hm'' : [ G ; Δ ⊢g m'[d'] : X'[d'] @ ki ]).
  { eapply wf_lconv; [eapply wf_conv; [exact Hm'd | rewrite ge_typeof; exact (eqty_sym _ _ _ _ _ _ HXX)] | exact Hki]. }
  set (ρ0 := kw_self HΔ).
  assert (hy' : LRtm kc (kw_G ρ0) (kw_Δ ρ0) (ktyl ρ0 Y[llift d])[lsingle m[d]]
                  (ktyl ρ0 Y[llift d'])[lsingle m'[d']] y[d] y'[d'])
    by (unfold ρ0; rewrite !ktyl_self by assumption; exact hy).
  (* the reducts, related at [out]'s type *)
  assert (Hn := fun n => pair_at Hwl Hwl' Hwli Hwc Hk Hk' Hki Hkc VX VA VB VC VY Vstep Vc Hd n
                  (corec_all Hwl Hwl' Hwli Hwc Hk Hk' Hki Hkc VX VA VB VC VY Vstep Vc Hd n) ρ0 _ _ _ _ hjj hy').
  pose proof (MOutR_lim Hn) as Hp.
  pose proof (LR_out_kw Hwl Hwl' Hwli Hk Hk' Hki VX VA VB VC Hd ρ0 _ _ Nm Nm' (fun ρ => m_imon VX Hd ρ0 ρ _ _ hjj))
    as Hout.
  (* [out] of the left [corec] steps to its reduct *)
  pose proof (proj1 (mIdx_iff VX Hd ρ0 _ _) hjj) as hjL.
  pose proof (LRtm_trans hjL (LRtm_sym hjL)) as hj. pose proof (LRtm_trans (LRtm_sym hjL) hjL) as hj'.
  pose proof (red_at Hwl Hwl' Hwli Hwc Hk Hk' Hki Hkc VX VA VB VC VY Vc Hd ρ0 _ _ _ _ _ _ hjj hj hj' hy') as R.
  unfold ρ0 in Hp, Hout, R.
  rewrite !kty_self, !ktyl_self, !ktyll_self, !ktmlll_self in Hp, Hout, R by assumption.
  rewrite !ktmll_self in Hp by assumption. rewrite !ktmll_self in R by assumption.
  rewrite ?(ktyl_self HΔ Y[llift d] NY), ?(ktyl_self HΔ Y'[llift d'] NY') in R.
  rewrite ?(ktyl_self HΔ Y[llift d] NY), ?(ktyl_self HΔ Y'[llift d'] NY') in Hp.
  destruct (R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (MAnn_refl HS Hmd) (MAnn_refl HS' Hm'')) as [RL RR].
  (* the right-hand type: [out]'s type at the left signature on both sides *)
  pose proof (VTm_trans Vm (VTm_sym Vm) _ _ _ Hd) as Xmm.
  pose proof (wf_tm_nf (proj2 (LRtm_escape Xmm))) as Nmd'.
  assert (hi0 : forall ρ : kwk (kw_G ρ0) (kw_Δ ρ0),
             mIdx (X := X) (X' := X) (l := l) (l' := l') (li := li) Δ d d' (kw_comp ρ0 ρ) (ktm ρ m[d]) (ktm ρ m[d'])).
  { intros ρ. apply (mIdx_iff (VTyG_refl_l VX) Hd). pose proof (LRtm_kw (kw_comp ρ0 ρ) Xmm) as Z.
    rewrite !ktm_comp in Z. unfold ρ0 in Z. rewrite !ktm_self in Z by assumption. exact Z. }
  pose proof (LR_out_kw Hwl Hwl' Hwli (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwl') (lequiv_refl _ _ Hwli)
                (VTyG_refl_l VX) (VTyG_refl_l VA) (VTyG_refl_l VB) (VTmG_trans VC (VTmG_sym VC)) Hd ρ0 _ _
                Nm Nmd' hi0) as Hout0.
  destruct (MGeq_nf (ms_geq (m_side Hwl Hwl' Hwli (lequiv_refl _ _ Hwl) (lequiv_refl _ _ Hwl')
              (lequiv_refl _ _ Hwli) (VTyG_refl_l VX) (VTyG_refl_l VA) (VTyG_refl_l VB)
              (VTmG_trans VC (VTmG_sym VC)) Hd))) as (_ & _ & _ & _ & NX0 & NA0 & NB0 & NC0).
  unfold ρ0 in Hout0. rewrite !kty_self, !ktyl_self, !ktyll_self, !ktmlll_self in Hout0 by assumption.
  eapply LRtm_irrel_r.
  - eapply LRtm_red; [| exact RL | exact (tmred_refl _ _ _ (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ RR)))].
    unfold LRtm, LRrel. rewrite lmeasure_out. eexists. split; [exact Hout | exact Hp].
  - unfold LRty, LogRel. rewrite lmeasure_out. eexists. exact Hout0.
Qed.

End CorecRules.

End MCorecV.
