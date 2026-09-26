(** * The algorithmic instance of the generic equivalence (M6_DESIGN.md H4)

    At a computing layer [i], each relation is the declarative one paired
    with the algorithmic derivation: [geq_ty] is [T ≅ T'] and [ac_ty T T'],
    [gne_tm] the declarative neutral relation and an [ac_tmne] at an
    inferred type equal to [T]. By soundness and presupposition this is the
    design's bundle of typings and derivation; keeping the declarative
    relation makes each law the declarative law plus its algorithmic half. *)
From DeLaM.Validity Require Export AlgLift.

Section Alg.
Context (i : layer) (Hi : compt i).
Let Hty : typeof i = i := compt_typeof_self i Hi.
Let Hv : i <> lV := compt_notV Hi.

Definition alg_ne_ty G Γ V V' l := decl_ne_ty i G Γ V V' l /\ ac_tyne G Γ V V'.
Definition alg_eq_ty G Γ T T' l := [ G ; Γ ⊢[ i ] T ≅ T' @ l ] /\ ac_ty G Γ T T'.
Definition alg_ne_tm G Γ t t' T l :=
  decl_ne_tm i G Γ t t' T l /\ exists T0, ac_tmne G Γ t t' T0 /\ [ G ; Γ ⊢[ i ] T ≅ T0 @ l ].
Definition alg_eq_tm G Γ t t' T l := [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] /\ ac_tm G Γ t t' T.

Definition AlgEq : GenericEq := {|
  ge_layer := i ;
  ge_compt := Hi ;
  gne_ty := alg_ne_ty ;
  geq_ty := alg_eq_ty ;
  gne_tm := alg_ne_tm ;
  geq_tm := alg_eq_tm
|}.

Local Notation DE := (DeclEq i Hi).
Local Notation DEL := (DeclEqLaws i Hi).

(** ** Helpers *)

(** A neutral pair at a type equal to [T] is neutral at its reduced type. *)
Lemma ne_nee {G Γ t t' T0 T l} : ac_tmne G Γ t t' T0 -> [ G ; Γ ⊢[ i ] T ≅ T0 @ l ] ->
  exists W0, ac_tmnee G Γ t t' W0 /\ whnf_ty W0 /\ [ G ; Γ ⊢[ i ] T ≅ W0 @ l ].
Proof.
  intros D ET. destruct (tgt_whnf Hi (eqty_wf_r Hty ET)) as (W0 & Hr & Hw & E0).
  exists W0. exact (conj (actmnee_red _ _ _ _ _ _ D Hr Hw) (conj Hw (eqty_trans _ _ _ _ _ _ _ ET E0))).
Qed.

(** Reduction reaches a whnf through every reduct. *)
Lemma reds_whnf_mid t u z : reds t u -> reds t z -> whnf z -> reds u z.
Proof.
  intros H; induction H as [t | t v u Htv Hvu IH]; intros Hz Hw; [exact Hz |].
  inversion Hz; subst.
  - destruct (whnf_no_red _ _ Hw Htv).
  - match goal with Htv' : red t ?v', Hv'z : Relation_Operators.clos_refl_trans_1n _ _ ?v' z |- _ =>
      rewrite (red_det _ _ _ Htv Htv') in IH; exact (IH Hv'z Hw) end.
Qed.

(** The left side of a term derivation may take reduction steps. *)
Lemma ac_tm_red_l {G Γ u v u' T} : ac_tm G Γ u u' T -> reds u v -> ac_tm G Γ v u' T.
Proof.
  intros D Hr. destruct (ainv_tm D) as (W & w & w' & HrT & HwT & Hr1 & Hr2 & Hw & Hw' & D').
  exact (actm_red _ _ _ _ _ _ _ _ HrT HwT (reds_whnf_mid _ _ _ Hr Hr1 Hw) Hr2 Hw Hw' D').
Qed.
Lemma ac_tm_red_r {G Γ u u' v' T} : ac_tm G Γ u u' T -> reds u' v' -> ac_tm G Γ u v' T.
Proof.
  intros D Hr. destruct (ainv_tm D) as (W & w & w' & HrT & HwT & Hr1 & Hr2 & Hw & Hw' & D').
  exact (actm_red _ _ _ _ _ _ _ _ HrT HwT Hr1 (reds_whnf_mid _ _ _ Hr Hr2 Hw') Hw Hw' D').
Qed.

(** Normalization of a typed term. *)
Lemma tgt_whnf_tm {G Γ t T k} : [ G ; Γ ⊢[ i ] t : T @ k ] -> exists w, reds t w /\ whnf w.
Proof.
  intros Ht. destruct Hi as [-> | ->].
  - exact (decl_whnf_normalization_tm Ht).
  - exact (declM_whnf_normalization_tm Ht).
Qed.

(** ** The laws needing more than one step *)

Lemma alg_ctx_ext {G Γ A A' la la'} : [ G ; Γ ⊢[ i ] A ≅ A' @ la ] -> lequiv (gL G) la la' ->
  [ G ⊢[ i ] Γ ,, A @ la ≅ Γ ,, A' @ la' ] /\ [ ⊢ G ].
Proof.
  intros EA Hl. pose proof (ctx_of_eqty Hty EA) as HΓ.
  split; [apply eqc_ext; [exact (eqc_refl _ _ _ HΓ) | exact (eqty_wf_l Hty EA) | exact EA | exact Hl]
         | exact (ctx_glob _ _ _ HΓ)].
Qed.

Lemma alg_tyne_ctxconv {G Γ A A' la la' V V' l} : [ G ; Γ ⊢[ i ] A ≅ A' @ la ] -> lequiv (gL G) la la' ->
  [ G ; Γ ,, A' @ la' ⊢[ i ] ] -> alg_ne_ty G (Γ ,, A @ la) V V' l -> alg_ne_ty G (Γ ,, A' @ la') V V' l.
Proof.
  intros EA Hl HΓ' ((Hn & Hn' & E) & D). destruct (alg_ctx_ext EA Hl) as [Hctx HG].
  refine (conj (conj Hn (conj Hn' (stab_eqty Hty EA Hl HΓ' E))) _).
  exact (proj1 (proj2 (proj2 ac_conv_all)) _ _ _ _ D i G _ l l Hi (GEq_refl _ HG) Hctx
           (eqty_wf_l Hty E) (eqty_wf_r Hty E)).
Qed.

Lemma alg_ty_ctxconv {G Γ A A' la la' T T' l} : [ G ; Γ ⊢[ i ] A ≅ A' @ la ] -> lequiv (gL G) la la' ->
  [ G ; Γ ,, A' @ la' ⊢[ i ] ] -> alg_eq_ty G (Γ ,, A @ la) T T' l -> alg_eq_ty G (Γ ,, A' @ la') T T' l.
Proof.
  intros EA Hl HΓ' (E & D). destruct (alg_ctx_ext EA Hl) as [Hctx HG].
  refine (conj (stab_eqty Hty EA Hl HΓ' E) _).
  exact (proj1 ac_conv_all _ _ _ _ D i G _ l l Hi (GEq_refl _ HG) Hctx (eqty_wf_l Hty E) (eqty_wf_r Hty E)).
Qed.

Lemma alg_tmne_ctxconv {G Γ A A' la la' t t' T l} : [ G ; Γ ⊢[ i ] A ≅ A' @ la ] -> lequiv (gL G) la la' ->
  [ G ; Γ ,, A' @ la' ⊢[ i ] ] -> alg_ne_tm G (Γ ,, A @ la) t t' T l -> alg_ne_tm G (Γ ,, A' @ la') t t' T l.
Proof.
  intros EA Hl HΓ' ((Hn & Hn' & E) & T0 & D & ET). destruct (alg_ctx_ext EA Hl) as [Hctx HG].
  refine (conj (conj Hn (conj Hn' (stab_eqtm Hty EA Hl HΓ' E))) _).
  destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ac_conv_all)))))) _ _ _ _ _ D i G _ l l T T Hi
              (GEq_refl _ HG) Hctx (eqtm_wf_l Hty E) (eqtm_wf_r Hty E)) as (T2 & D2 & E2).
  exists T2. split; [exact D2 |].
  exact (stab_eqty Hty EA Hl HΓ' (eqty_trans _ _ _ _ _ _ _ ET (eqty_sym _ _ _ _ _ _ E2))).
Qed.

Lemma alg_tm_ctxconv {G Γ A A' la la' t t' T l} : [ G ; Γ ⊢[ i ] A ≅ A' @ la ] -> lequiv (gL G) la la' ->
  [ G ; Γ ,, A' @ la' ⊢[ i ] ] -> alg_eq_tm G (Γ ,, A @ la) t t' T l -> alg_eq_tm G (Γ ,, A' @ la') t t' T l.
Proof.
  intros EA Hl HΓ' (E & D). destruct (alg_ctx_ext EA Hl) as [Hctx HG].
  refine (conj (stab_eqtm Hty EA Hl HΓ' E) _).
  exact (proj1 (proj2 (proj2 (proj2 (proj2 ac_conv_all)))) _ _ _ _ _ D i G _ T l Hi (GEq_refl _ HG) Hctx
           (eqtm_wf_l Hty E) (eqtm_wf_r Hty E) (eqty_refl _ _ _ _ _ (eqtm_wf_ty Hty E))).
Qed.

(** η: the terms reduce to whnfs, and the premise's applications along. *)
Lemma alg_funext {G Γ l l' A B t t'} : [ G ; Γ ⊢[ i ] t : tyPi l l' A B @ lmax l l' ] ->
  [ G ; Γ ⊢[ i ] t' : tyPi l l' A B @ lmax l l' ] ->
  ac_tm G (Γ ,, A @ l) (app t⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0)) (app t'⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0)) B ->
  ac_tm G Γ t t' (tyPi l l' A B).
Proof.
  intros Ht Ht' D. destruct (tgt_whnf_tm Ht) as (w & Hr & Hw). destruct (tgt_whnf_tm Ht') as (w' & Hr' & Hw').
  eapply actm_red; [constructor | exact (whnf_tyPi _ _ _ _) | exact Hr | exact Hr' | exact Hw | exact Hw' |].
  apply actmnf_eta.
  eapply ac_tm_red_r; [eapply ac_tm_red_l; [exact D |] |]; apply reds_app, reds_ren; assumption.
Qed.

Lemma alg_natrec {G Γ l l' M M' s s' z z' ν ν' T0} : leqv l l' ->
  ac_ty G (Γ ,, tyNat @ lzero) M M' -> ac_tm G Γ s s' M[lsingle zero] ->
  ac_tm G (Γ ,, tyNat @ lzero ,, M @ l) z z' M[lsucc] ->
  ac_tmne G Γ ν ν' T0 -> [ G ; Γ ⊢[ i ] tyNat ≅ T0 @ lzero ] ->
  [ G ; Γ ⊢[ i ] natrec l M s z ν : M[lsingle ν] @ l ] ->
  exists T1, ac_tmne G Γ (natrec l M s z ν) (natrec l' M' s' z' ν') T1 /\ [ G ; Γ ⊢[ i ] M[lsingle ν] ≅ T1 @ l ].
Proof.
  intros Hl DM Ds Dz Dν ET Hx. destruct (ne_nee Dν ET) as (W0 & Xν & _).
  exists M[lsingle ν]. split; [exact (actmne_natrec _ _ _ _ _ _ _ _ _ _ _ _ _ Hl DM Ds Dz Xν) |].
  exact (eqty_refl _ _ _ _ _ (wf_tm_ty Hty Hx)).
Qed.

Lemma alg_app {G Γ l1 l2 l3 l4 A A' B B' ν ν' s s' T0} :
  [ G ; Γ ⊢[ i ] tyPi l1 l2 A B ≅ T0 @ lmax l1 l2 ] -> ac_tmne G Γ ν ν' T0 ->
  [ G ; Γ ⊢[ i ] s : A @ l1 ] -> [ G ; Γ ⊢[ i ] s' : A @ l1 ] -> ac_tm G Γ s s' A ->
  exists T1, ac_tmne G Γ (app ν l1 l2 A B s) (app ν' l3 l4 A' B' s') T1 /\
    [ G ; Γ ⊢[ i ] B[lsingle s] ≅ T1 @ l2 ].
Proof.
  intros ET Dν Hs Hs' Ds. destruct (ne_nee Dν ET) as (W0 & Xν & Hw0 & EW).
  destruct (head_pi W0 (eq_sym (decl_head_c Hi EW (whnf_tyPi _ _ _ _) Hw0))) as (m & m' & A0 & B0 & ->).
  destruct (pi_inj_c Hi EW) as (_ & _ & EA0 & EB0).
  pose proof (ctx_of_wf_tm Hty Hs) as HΓ.
  pose proof (cv_tm (ctx_glob _ _ _ HΓ) Hi Ds (eqc_refl _ _ _ HΓ) Hs Hs' (eqty_sym _ _ _ _ _ _ EA0)) as Ds'.
  exists B0[lsingle s]. split; [eapply actmne_app; [exact Xν | exact Ds'] |].
  exact (eqty_single Hty EB0 Hs).
Qed.

(** The substitutions of global variables. *)
Lemma alg_lsub {G Γ d d' Δ} : @geq_lsub AlgEq G Γ d d' Δ -> @geq_lsub DE G Γ d d' Δ /\ ac_sub G Γ d d' Δ.
Proof.
  intros [HΓ Ht Hd Ht' Hd' Hw Hw' He]. split.
  - constructor; auto. intros n A k Hin. exact (proj1 (He n A k Hin)).
  - apply acs_pt. intros n A k Hin. exact (proj2 (He n A k Hin)).
Qed.

(** ** The laws *)

Lemma AlgEqLaws : @GenericEqLaws AlgEq.
Proof.
  constructor; cbn; unfold alg_ne_ty, alg_eq_ty, alg_ne_tm, alg_eq_tm, decl_ne_ty, decl_ne_tm.
  (* neutral forms *)
  5-8: intros * ((Hn & Hn' & _) & _); assumption.
  (* subsumption *)
  - intros * ((Hn & Hn' & E) & D). split; [exact E |].
    eapply act_red; [constructor | constructor | apply whnf_ty_ne, Hn | apply whnf_ty_ne, Hn' | apply actnf_ne, D].
  - intros * (E & _); exact E.
  - intros * ((Hn & Hn' & E) & T0 & D & ET). split; [exact E |].
    exact (lift_c Hi (eqtm_wf_ty Hty E) _ _ _ (eqtm_wf_l Hty E) (eqtm_wf_r Hty E) D ET).
  - intros * (E & _); exact E.
  (* PER *)
  - intros * ((Hn & Hn' & E) & D). refine (conj (conj Hn' (conj Hn (eqty_sym _ _ _ _ _ _ E))) _).
    exact (proj1 (proj2 (proj2 ac_sym_all)) _ _ _ _ D i l l Hi (eqty_wf_l Hty E) (eqty_wf_r Hty E)).
  - intros * ((Hn & _ & E1) & D1) ((_ & Hn'' & E2) & D2).
    refine (conj (conj Hn (conj Hn'' (eqty_trans _ _ _ _ _ _ _ E1 E2))) _).
    exact (proj1 (proj2 (proj2 ac_trans_all)) _ _ _ _ D1 _ i l l l Hi (eqty_wf_l Hty E1) (eqty_wf_r Hty E1)
             (eqty_wf_r Hty E2) D2).
  - intros * (E & D). refine (conj (eqty_sym _ _ _ _ _ _ E) _).
    exact (proj1 ac_sym_all _ _ _ _ D i l l Hi (eqty_wf_l Hty E) (eqty_wf_r Hty E)).
  - intros * (E1 & D1) (E2 & D2). refine (conj (eqty_trans _ _ _ _ _ _ _ E1 E2) _).
    exact (proj1 ac_trans_all _ _ _ _ D1 _ i l l l Hi (eqty_wf_l Hty E1) (eqty_wf_r Hty E1) (eqty_wf_r Hty E2) D2).
  - intros * ((Hn & Hn' & E) & T0 & D & ET).
    refine (conj (conj Hn' (conj Hn (eqtm_sym _ _ _ _ _ _ _ E))) _).
    destruct (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ac_sym_all)))))) _ _ _ _ _ D i l l T T Hi
                (eqtm_wf_l Hty E) (eqtm_wf_r Hty E)) as (T1 & D1).
    destruct (ac_ne_sound' D1 Hi (eqtm_wf_r Hty E) (eqtm_wf_l Hty E)) as (E1 & _ & _).
    exact (ex_intro _ T1 (conj D1 E1)).
  - intros * ((Hn & _ & E1) & T0 & D1 & ET1) ((_ & Hn'' & E2) & T1 & D2 & _).
    refine (conj (conj Hn (conj Hn'' (eqtm_trans _ _ _ _ _ _ _ _ E1 E2))) (ex_intro _ T0 (conj _ ET1))).
    exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ac_trans_all)))))) _ _ _ _ _ D1 _ T1 i l l l T T T Hi
             (eqtm_wf_l Hty E1) (eqtm_wf_r Hty E1) (eqtm_wf_r Hty E2) D2).
  - intros * (E & D). refine (conj (eqtm_sym _ _ _ _ _ _ _ E) _).
    exact (proj1 (proj2 (proj2 (proj2 (proj2 ac_sym_all)))) _ _ _ _ _ D i l Hi (eqtm_wf_l Hty E) (eqtm_wf_r Hty E)).
  - intros * (E1 & D1) (E2 & D2). refine (conj (eqtm_trans _ _ _ _ _ _ _ _ E1 E2) _).
    exact (proj1 (proj2 (proj2 (proj2 (proj2 ac_trans_all)))) _ _ _ _ _ D1 _ i l Hi (eqtm_wf_l Hty E1)
             (eqtm_wf_r Hty E1) (eqtm_wf_r Hty E2) D2).
  (* level equivalence of syntax *)
  - intros * ((Hn & _ & E) & D) ((Hn' & _ & E') & _) Hq.
    refine (conj (conj Hn (conj Hn' (leq_eqty Hi (eqty_wf_l Hty E) (eqty_wf_l Hty E') Hq))) _).
    exact (proj1 (proj2 (proj2 ac_leq_all)) _ _ _ _ D _ Hq).
  - intros * (E & D) (E' & _) Hq. refine (conj (leq_eqty Hi (eqty_wf_l Hty E) (eqty_wf_l Hty E') Hq) _).
    exact (proj1 ac_leq_all _ _ _ _ D _ Hq).
  - intros * ((Hn & _ & E) & T0 & D & ET) ((Hn' & _ & E') & _) Hq.
    refine (conj (conj Hn (conj Hn' (leq_eqtm Hi (eqtm_wf_l Hty E) (eqtm_wf_l Hty E') Hq))) (ex_intro _ T0 (conj _ ET))).
    exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ac_leq_all)))))) _ _ _ _ _ D _ Hq).
  - intros * (E & D) (E' & _) Hq. refine (conj (leq_eqtm Hi (eqtm_wf_l Hty E) (eqtm_wf_l Hty E') Hq) _).
    exact (proj1 (proj2 (proj2 (proj2 (proj2 ac_leq_all)))) _ _ _ _ _ D _ Hq).
  (* conversion *)
  - intros * ((Hn & Hn' & E) & T0 & D & ET) EC.
    refine (conj (conj Hn (conj Hn' (eqtm_conv _ _ _ _ _ _ _ _ E _))) (ex_intro _ T0 (conj D _))).
    + rewrite Hty; exact (eqty_sym _ _ _ _ _ _ EC).
    + exact (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EC) ET).
  - intros * (E & D) EC. refine (conj (eqtm_conv _ _ _ _ _ _ _ _ E _) _); [rewrite Hty; exact (eqty_sym _ _ _ _ _ _ EC) |].
    pose proof (ctx_of_eqtm Hty E) as HΓ.
    exact (cv_tm (ctx_glob _ _ _ HΓ) Hi D (eqc_refl _ _ _ HΓ) (eqtm_wf_l Hty E) (eqtm_wf_r Hty E) (eqty_sym _ _ _ _ _ _ EC)).
  - intros * ((Hn & Hn' & E) & D) Hl. exact (conj (conj Hn (conj Hn' (eqty_lconv _ _ _ _ _ _ _ E Hl))) D).
  - intros * (E & D) Hl. exact (conj (eqty_lconv _ _ _ _ _ _ _ E Hl) D).
  - intros * ((Hn & Hn' & E) & T0 & D & ET) Hl.
    exact (conj (conj Hn (conj Hn' (eqtm_lconv _ _ _ _ _ _ _ _ E Hl))) (ex_intro _ T0 (conj D (eqty_lconv _ _ _ _ _ _ _ ET Hl)))).
  - intros * (E & D) Hl. exact (conj (eqtm_lconv _ _ _ _ _ _ _ _ E Hl) D).
  (* weakening *)
  - intros * Hr HΔ ((Hn & Hn' & E) & D).
    refine (conj (@gne_ty_wk DE DEL _ _ _ _ _ _ _ Hr HΔ (conj Hn (conj Hn' E))) _).
    exact (proj1 (proj2 (proj2 ac_wk_all)) _ _ _ _ D _ _ Hr).
  - intros * Hr HΔ (E & D). refine (conj (@geq_ty_wk DE DEL _ _ _ _ _ _ _ Hr HΔ E) _).
    exact (proj1 ac_wk_all _ _ _ _ D _ _ Hr).
  - intros * Hr HΔ ((Hn & Hn' & E) & T0 & D & ET).
    refine (conj (@gne_tm_wk DE DEL _ _ _ _ _ _ _ _ Hr HΔ (conj Hn (conj Hn' E))) (ex_intro _ T0⟨r⟩ (conj _ _))).
    + exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ac_wk_all)))))) _ _ _ _ _ D _ _ Hr).
    + exact (@geq_ty_wk DE DEL _ _ _ _ _ _ _ Hr HΔ ET).
  - intros * Hr HΔ (E & D). refine (conj (@geq_tm_wk DE DEL _ _ _ _ _ _ _ _ Hr HΔ E) _).
    exact (proj1 (proj2 (proj2 (proj2 (proj2 ac_wk_all)))) _ _ _ _ _ D _ _ Hr).
  (* context conversion *)
  - intros * EA Hl HΓ' X. exact (alg_tyne_ctxconv EA Hl HΓ' X).
  - intros * EA Hl HΓ' X. exact (alg_ty_ctxconv EA Hl HΓ' X).
  - intros * EA Hl HΓ' X. exact (alg_tmne_ctxconv EA Hl HΓ' X).
  - intros * EA Hl HΓ' X. exact (alg_tm_ctxconv EA Hl HΓ' X).
  (* weak head closure *)
  - intros * HT HT' (E & D). refine (conj (@geq_ty_exp DE DEL _ _ _ _ _ _ _ HT HT' E) _).
    destruct (ainv_ty D) as (W0 & W0' & Hr & Hr' & Hw & Hw' & D').
    exact (act_red _ _ _ _ _ _ (reds_ty_trans _ _ _ (tyred_red _ _ _ _ _ _ HT) Hr)
             (reds_ty_trans _ _ _ (tyred_red _ _ _ _ _ _ HT') Hr') Hw Hw' D').
  - intros * Ht Ht' (E & D). refine (conj (@geq_tm_exp DE DEL _ _ _ _ _ _ _ _ Ht Ht' E) _).
    destruct (ainv_tm D) as (W0 & w0 & w0' & HrT & HwT & Hr & Hr' & Hw & Hw' & D').
    exact (actm_red _ _ _ _ _ _ _ _ HrT HwT (reds_trans _ _ _ (tmred_red _ _ _ _ _ _ _ Ht) Hr)
             (reds_trans _ _ _ (tmred_red _ _ _ _ _ _ _ Ht') Hr') Hw Hw' D').
  (* type constructors *)
  - intros * HΓ. refine (conj (@geq_ty_nat DE DEL _ _ HΓ) _).
    eapply act_red; [constructor | constructor | exact whnf_tyNat | exact whnf_tyNat | apply actnf_nat].
  - intros * HΓ Hl. refine (conj (@geq_ty_U DE DEL _ _ _ _ HΓ Hl) _).
    eapply act_red; [constructor | constructor | apply whnf_tyU | apply whnf_tyU | apply actnf_U, (lequiv_leqv _ _ _ Hl)].
  - intros * H13 H24 HA (EA & DA) (EB & DB).
    refine (conj (@geq_ty_pi DE DEL _ _ _ _ _ _ _ _ _ _ H13 H24 HA EA EB) _).
    eapply act_red; [constructor | constructor | apply whnf_tyPi | apply whnf_tyPi |].
    exact (actnf_pi _ _ _ _ _ _ _ _ _ _ (lequiv_leqv _ _ _ H13) (lequiv_leqv _ _ _ H24) DA DB).
  - intros * HΓ. refine (conj (@geq_tm_code_nat DE DEL _ _ HΓ) _).
    eapply actm_red; [constructor | apply whnf_tyU | constructor | constructor | exact whnf_tmNat | exact whnf_tmNat |].
    apply actmnf_code_nat.
  - intros * HΓ Hl. refine (conj (@geq_tm_code_U DE DEL _ _ _ _ HΓ Hl) _).
    eapply actm_red; [constructor | apply whnf_tyU | constructor | constructor | apply whnf_tmU | apply whnf_tmU |].
    apply actmnf_code_U, (lequiv_leqv _ _ _ Hl).
  - intros * H13 H24 Hs (Es & Ds) (Et & Dt).
    refine (conj (@geq_tm_code_pi DE DEL _ _ _ _ _ _ _ _ _ _ H13 H24 Hs Es Et) _).
    eapply actm_red; [constructor | apply whnf_tyU | constructor | constructor | apply whnf_tmPi | apply whnf_tmPi |].
    exact (actmnf_code_pi _ _ _ _ _ _ _ _ _ _ _ (lequiv_leqv _ _ _ H13) (lequiv_leqv _ _ _ H24) Ds Dt).
  (* neutral types *)
  - intros * Hl ((Hn & Hn' & E) & T0 & D & ET).
    refine (conj (@gne_ty_El DE DEL _ _ _ _ _ _ Hl (conj Hn (conj Hn' E))) _).
    destruct (ne_nee D ET) as (W0 & X & _). exact (actne_El _ _ _ _ _ _ _ (lequiv_leqv _ _ _ Hl) X).
  (* term congruences *)
  - intros * HΓ. refine (conj (@geq_tm_zero DE DEL _ _ HΓ) _).
    eapply actm_red; [constructor | exact whnf_tyNat | constructor | constructor | exact whnf_zero | exact whnf_zero |].
    apply actmnf_zero.
  - intros * (E & D). refine (conj (@geq_tm_succ DE DEL _ _ _ _ E) _).
    eapply actm_red; [constructor | exact whnf_tyNat | constructor | constructor | apply whnf_succ | apply whnf_succ |].
    exact (actmnf_succ _ _ _ _ D).
  - intros * Hl Hl' HA HB Ht Ht' (E & D).
    exact (conj (@geq_tm_funext DE DEL _ _ _ _ _ _ _ _ Hl Hl' HA HB Ht Ht' E) (alg_funext Ht Ht' D)).
  (* neutral congruences *)
  - intros * Ht. refine (conj (@gne_tm_var DE DEL _ _ _ _ _ Ht) _).
    destruct (inv_var Hty Ht) as (T0 & l0 & (_ & Hin) & _ & HX).
    exact (ex_intro _ T0 (conj (actmne_var _ _ _ _ _ Hin) HX)).
  - intros * Hl HM (EM & DM) (Es & Ds) (Ez & Dz) ((Hn & Hn' & Eν) & T0 & Dν & ETν).
    pose proof (@gne_tm_natrec DE DEL _ _ _ _ _ _ _ _ _ _ _ _ Hl HM EM Es Ez (conj Hn (conj Hn' Eν))) as X.
    refine (conj X _). destruct X as (_ & _ & EX).
    exact (alg_natrec (lequiv_leqv _ _ _ Hl) DM Ds Dz Dν ETν (eqtm_wf_l Hty EX)).
  - intros * H13 H24 HA (EA & DA) (EB & DB) ((Hn & Hn' & Eν) & T0 & Dν & ETν) (Es & Ds).
    refine (conj (@gne_tm_app DE DEL _ _ _ _ _ _ _ _ _ _ _ _ _ _ H13 H24 HA EA EB (conj Hn (conj Hn' Eν)) Es) _).
    exact (alg_app ETν Dν (eqtm_wf_l Hty Es) (eqtm_wf_r Hty Es) Ds).
  (* global weakening *)
  - intros * Hγ HG' ((Hn & Hn' & E) & D).
    refine (conj (@gne_ty_gwk DE DEL _ _ _ _ _ _ _ Hγ HG' (conj Hn (conj Hn' E))) _).
    exact (proj1 (proj2 (proj2 ac_gwk_all)) _ _ _ _ D _ _ Hγ).
  - intros * Hγ HG' (E & D). refine (conj (@geq_ty_gwk DE DEL _ _ _ _ _ _ _ Hγ HG' E) _).
    exact (proj1 ac_gwk_all _ _ _ _ D _ _ Hγ).
  - intros * Hγ HG' ((Hn & Hn' & E) & T0 & D & ET).
    refine (conj (@gne_tm_gwk DE DEL _ _ _ _ _ _ _ _ Hγ HG' (conj Hn (conj Hn' E))) (ex_intro _ T0⟪γ⟫ (conj _ _))).
    + exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ac_gwk_all)))))) _ _ _ _ _ D _ _ Hγ).
    + exact (@geq_ty_gwk DE DEL _ _ _ _ _ _ _ Hγ HG' ET).
  - intros * Hγ HG' (E & D). refine (conj (@geq_tm_gwk DE DEL _ _ _ _ _ _ _ _ Hγ HG' E) _).
    exact (proj1 (proj2 (proj2 (proj2 (proj2 ac_gwk_all)))) _ _ _ _ _ D _ _ Hγ).
  (* universe substitution *)
  - intros * Hφ ((Hn & Hn' & E) & D).
    refine (conj (@gne_ty_us DE DEL _ _ _ _ _ _ _ Hφ (conj Hn (conj Hn' E))) _).
    exact (proj1 (proj2 (proj2 ac_us_all)) _ _ _ _ D _ _).
  - intros * Hφ (E & D). refine (conj (@geq_ty_us DE DEL _ _ _ _ _ _ _ Hφ E) _).
    exact (proj1 ac_us_all _ _ _ _ D _ _).
  - intros * Hφ ((Hn & Hn' & E) & T0 & D & ET).
    refine (conj (@gne_tm_us DE DEL _ _ _ _ _ _ _ _ Hφ (conj Hn (conj Hn' E))) (ex_intro _ (usubst_ty T0 φ) (conj _ _))).
    + exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ac_us_all)))))) _ _ _ _ _ D _ _).
    + exact (@geq_ty_us DE DEL _ _ _ _ _ _ _ Hφ ET).
  - intros * Hφ (E & D). refine (conj (@geq_tm_us DE DEL _ _ _ _ _ _ _ _ Hφ E) _).
    exact (proj1 (proj2 (proj2 (proj2 (proj2 ac_us_all)))) _ _ _ _ _ D _ _).
  (* global variables *)
  - intros * Hin Hle Hls. destruct (alg_lsub Hls) as [Hd Hs].
    exact (conj (@gne_ty_gvar DE DEL _ _ _ _ _ _ _ _ Hin Hle Hd) (actne_gvar _ _ _ _ _ _ _ _ Hin Hs)).
  - intros * Hin Hle Hls. destruct (alg_lsub Hls) as [Hd Hs].
    pose proof (@gne_tm_gvar DE DEL _ _ _ _ _ _ _ _ _ Hin Hle Hd) as X.
    refine (conj X (ex_intro _ T[d] (conj (actmne_gvar _ _ _ _ _ _ _ _ _ Hin Hs) _))).
    destruct X as (_ & _ & EX). exact (eqty_refl _ _ _ _ _ (eqtm_wf_ty Hty EX)).
Qed.

End Alg.
