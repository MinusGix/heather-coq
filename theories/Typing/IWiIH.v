(** * [elim_IWi]'s synthesized induction hypothesis, typed (M19b)

    As [IWfIH]'s, with a second binder: [iwiIH] is
    [λ^{0}(i : Fin N[a/x]). λ^{lp}(y : D[a/x, i]). elim_IWi(…; C[a/x, i, y];
    app(dnth(cs; i), y))], at the [ih] entry's instance
    [Π^{0}(Fin N[a/x]). Π^{lp}(D[a/x, i]). M[C[a/x, i, y], app(dnth(cs; i), y)]].
    The declarative β states the induction hypothesis typed
    (M19_DESIGN.md); [elim_IWi]'s validity types it here, at a [sup] of
    related components. *)
From DeLaM.Typing Require Export PresupIWi DNth IWfIH.

(** The children's [dnth] and the child at the bound position and domain
    element, the body and its codomain, in [Γ, i : Fin N[a/x], y : D[a/x, i]]. *)
Notation iwidnth l lp li X A N D Ot C a cs :=
  (tmDNth (iwiL l lp li) N[lsingle a]⟨↑⟩⟨↑⟩ (iwiFam l lp li X A N D Ot C a)⟨rlift ↑⟩⟨rlift ↑⟩ cs⟨↑⟩⟨↑⟩ (var 1)).
Notation iwiapp l lp li X A N D Ot C a cs :=
  (app (iwidnth l lp li X A N D Ot C a cs) lp (iwiL l lp li) D[llift (lsingle a)]⟨↑⟩
     (iwiFamCod l lp li X A N D Ot C a)⟨rlift ↑⟩ (var 0)).
Notation iwibody l lp li l' X A N D Ot C M c a cs :=
  (tmElimIWi l lp li l' X⟨↑⟩⟨↑⟩ A⟨↑⟩⟨↑⟩ N⟨rlift ↑⟩⟨rlift ↑⟩ D⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩
     Ot⟨rlift ↑⟩⟨rlift ↑⟩ C⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩
     M⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩ c⟨rlift (rlift (rlift ↑))⟩⟨rlift (rlift (rlift ↑))⟩
     C[llift (llift (lsingle a))] (iwiapp l lp li X A N D Ot C a cs)).
Notation iwicod l lp li X A N D Ot C M a cs :=
  (M⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩[lsingle2 C[llift (llift (lsingle a))] (iwiapp l lp li X A N D Ot C a cs)]).

Lemma iwiIH_body l lp li l' X A N D Ot C M c a cs :
  iwiIH l lp li l' X A N D Ot C M c a cs =
  lam lzero (lmax lp l') (tyFin N[lsingle a]) (lam lp l' D[llift (lsingle a)] (iwibody l lp li l' X A N D Ot C M c a cs)).
Proof. reflexivity. Qed.

(** The telescope weakened past one local, under its binders. *)
Local Ltac rq := repeat first [rewrite lsingle2_ren_ty | rewrite ren_tmDNth | progress push_ren];
  repeat (first [solve [ren_comm] | f_equal]).
Lemma IWi_cs_ren l lp li (X A : ty) (N : tm) (D : ty) (Ot C : tm) :
  (iwicsty l lp li X A N D Ot C)⟨rlift ↑⟩ =
  iwicsty l lp li X⟨↑⟩ A⟨↑⟩ N⟨rlift ↑⟩ D⟨rlift (rlift ↑)⟩ Ot⟨rlift ↑⟩ C⟨rlift (rlift (rlift ↑))⟩.
Proof. rq. Qed.
Lemma IWi_ih_ren l lp li l' (X A : ty) (N : tm) (D : ty) (Ot C : tm) (M : ty) :
  (iwiihty l lp li l' X A N D Ot C M)⟨rlift (rlift ↑)⟩ =
  iwiihty l lp li l' X⟨↑⟩ A⟨↑⟩ N⟨rlift ↑⟩ D⟨rlift (rlift ↑)⟩ Ot⟨rlift ↑⟩ C⟨rlift (rlift (rlift ↑))⟩ M⟨rlift (rlift ↑)⟩.
Proof. rq. Qed.
Lemma IWi_step_ren l lp li (X A : ty) (N : tm) (D : ty) (Ot C : tm) (M : ty) :
  (iwistepty l lp li X A N D Ot C M)⟨rlift (rlift (rlift ↑))⟩ =
  iwistepty l lp li X⟨↑⟩ A⟨↑⟩ N⟨rlift ↑⟩ D⟨rlift (rlift ↑)⟩ Ot⟨rlift ↑⟩ C⟨rlift (rlift (rlift ↑))⟩ M⟨rlift (rlift ↑)⟩.
Proof. rq. Qed.

(** The [ih] entry's instance at a shape and children. *)
Lemma IWi_E4 l lp li l' (X A : ty) (N : tm) (D : ty) (Ot C : tm) (M : ty) a cs :
  nfty X -> nfty A -> nftm N -> nfty D -> nftm Ot -> nftm C -> nftm a -> nftm cs ->
  (iwiihty l lp li l' X A N D Ot C M)[lsingle2 a cs] =
  tyPi lzero (lmax lp l') (tyFin N[lsingle a])
    (tyPi lp l' D[llift (lsingle a)] (iwicod l lp li X A N D Ot C M a cs)).
Proof.
  intros NX NA NN ND NO NC Na Ncs. rewrite subst_tyPi. f_equal; [push_subst; f_equal; teq_core|]. rewrite subst_tyPi. f_equal; [teq_core|].
  match goal with |- (_[lsingle2 ?u ?v])[_] = _ => set (vv := v); set (uu := u) end.
  set (u0 := C[llift (llift (lsingle a))]). set (v0 := iwiapp l lp li X A N D Ot C a cs).
  assert (Eu : uu[llift (llift (lsingle2 a cs))] = u0) by (subst uu u0; teq_core).
  assert (Ev : vv[llift (llift (lsingle2 a cs))] = v0).
  { subst vv v0. push_subst. rewrite subst_tmDNth by (intros [|[|[|[|n]]]]; rewrite ?llk_llift; cbn; auto using ren_nf).
  unfold iwiFam, iwiFamCod. push_ren. push_subst.
  repeat (first [solve [teq_core; rewrite ?ren_as_r2l, ?subst_comp; reflexivity] | solve [rewrite ?llk_llift; cbn; reflexivity] | f_equal]). }
  clearbody uu vv u0 v0.
  rewrite single2_subst_ty by (intros [|[|[|[|n]]]]; rewrite ?llk_llift; cbn; auto using ren_nf).
  rewrite Eu, Ev. f_equal. teq_core.
Qed.

Section IWiIH.
Context {G : gctx} {i : layer} (Hi : typeof i = i) (Hv : i <> lV).
Local Notation IWiSig := (@IWiSig G i).

Ltac wkn H := first [ exact H | eapply (wk1_ty G i Hi); [eassumption | wkn H] | eapply (wk1_tm G i Hi); [eassumption | wkn H] ].

Lemma iwiL_wf {l lp li} : lwf (gL G) l -> lwf (gL G) lp -> lwf (gL G) li -> lwf (gL G) (iwiL l lp li).
Proof using. intros. repeat split; assumption. Qed.

(** The child at the bound position, in [Γ, i : Fin N[a/x]]. *)
Lemma IWi_dnth0_wf {Γ l lp li X A N D Ot C a cs} : IWiSig Γ l lp li X A N D Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] cs : tyDVec (iwiL l lp li) N[lsingle a] (iwiFam l lp li X A N D Ot C a) @ iwiL l lp li ] ->
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ]
      tmDNth (iwiL l lp li) N[lsingle a]⟨↑⟩ (iwiFam l lp li X A N D Ot C a)⟨rlift ↑⟩ cs⟨↑⟩ (var 0)
      : iwiFam l lp li X A N D Ot C a @ iwiL l lp li ].
Proof using Hi Hv.
  intros HS Ha Hcs. pose proof HS as (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC).
  assert (HNa : [ G ; Γ ⊢[ i ] N[lsingle a] : tyNat @ lzero ]) by exact (wf_tm_single Hi HN Ha).
  assert (HF : [ G ; Γ ⊢[ i ] tyFin N[lsingle a] @ lzero ]) by (apply wft_fin; auto).
  assert (HΓ1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] ]) by (apply (ext_wf Hi); [exact HF | exact I]).
  assert (HN1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] N[lsingle a]⟨↑⟩ : tyNat @ lzero ])
    by (eapply wf_tm_retype; [wkn HNa | reflexivity]).
  pose proof (IWi_fam_wf Hi Hv HS Ha) as HFam.
  assert (HΓ2 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, tyFin N[lsingle a]⟨↑⟩ @ lzero ⊢[ i ] ])
    by (apply (ext_wf Hi); [apply wft_fin; [exact Hv | exact HN1] | exact I]).
  assert (HFam1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, tyFin N[lsingle a]⟨↑⟩ @ lzero
                    ⊢[ i ] (iwiFam l lp li X A N D Ot C a)⟨rlift ↑⟩ @ iwiL l lp li ])
    by (eapply weakening_r; [exact HFam | exact Hi | | exact HΓ2];
        eapply wkr_up'; [apply wkr_shift1 | reflexivity]).
  assert (Hcs1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] cs⟨↑⟩
                   : tyDVec (iwiL l lp li) N[lsingle a]⟨↑⟩ (iwiFam l lp li X A N D Ot C a)⟨rlift ↑⟩ @ iwiL l lp li ])
    by (eapply wf_tm_retype; [wkn Hcs | reflexivity]).
  assert (Hv0 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] var 0 : tyFin N[lsingle a]⟨↑⟩ @ lzero ])
    by (apply wf_var; [rewrite Hi; exact HΓ1 | constructor]).
  pose proof (dnth_wf (compt_self Hi Hv) (iwiL_wf Hl Hlp Hli) HN1 HFam1 Hcs1 Hv0) as X0.
  rewrite liftshift_single_var_ty in X0 by exact (wf_ty_nf HFam). exact X0.
Qed.

(** The child applied to the bound domain element, in
    [Γ, i : Fin N[a/x], y : D[a/x, i]]. *)
Lemma IWi_app_wf {Γ l lp li X A N D Ot C a cs} : IWiSig Γ l lp li X A N D Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] cs : tyDVec (iwiL l lp li) N[lsingle a] (iwiFam l lp li X A N D Ot C a) @ iwiL l lp li ] ->
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, D[llift (lsingle a)] @ lp ⊢[ i ]
      iwiapp l lp li X A N D Ot C a cs : iwiFamCod l lp li X A N D Ot C a @ iwiL l lp li ].
Proof using Hi Hv.
  intros HS Ha Hcs. pose proof HS as (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC).
  pose proof (iwiL_wf Hl Hlp Hli) as HwL.
  pose proof (IWi_dom_wf Hi Hv HS Ha) as HDa.
  pose proof (ext_wf Hi HDa Hlp) as HΓ2.
  pose proof (IWi_dnth0_wf HS Ha Hcs) as Hd.
  assert (Hd1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, D[llift (lsingle a)] @ lp ⊢[ i ]
                  iwidnth l lp li X A N D Ot C a cs
                  : tyPi lp (iwiL l lp li) D[llift (lsingle a)]⟨↑⟩ (iwiFamCod l lp li X A N D Ot C a)⟨rlift ↑⟩
                  @ iwiL l lp li ]).
  { pose proof (wk1_tm G i Hi _ _ _ _ _ _ HΓ2 Hd) as Y. rewrite ren_tmDNth in Y. exact Y. }
  assert (HDa1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, D[llift (lsingle a)] @ lp ⊢[ i ]
                   D[llift (lsingle a)]⟨↑⟩ @ lp ]) by wkn HDa.
  pose proof (ext_wf Hi HDa1 Hlp) as HΓ3.
  assert (HCod1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, D[llift (lsingle a)] @ lp ,, D[llift (lsingle a)]⟨↑⟩ @ lp
                    ⊢[ i ] (iwiFamCod l lp li X A N D Ot C a)⟨rlift ↑⟩ @ iwiL l lp li ])
    by (eapply weakening_r; [exact (IWi_famcod_wf Hi Hv HS Ha) | exact Hi | | exact HΓ3];
        eapply wkr_up'; [apply wkr_shift1 | reflexivity]).
  assert (Hv0 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, D[llift (lsingle a)] @ lp ⊢[ i ]
                  var 0 : D[llift (lsingle a)]⟨↑⟩ @ lp ])
    by (apply wf_var; [rewrite Hi; exact HΓ2 | constructor]).
  pose proof (wf_app _ _ _ _ _ _ _ _ _ Hv Hlp HwL HDa1 HCod1
                (wf_lconv _ _ _ _ _ _ _ Hd1 (lequiv_sym _ _ _ (iwiL_pi _ _ _ _ Hl Hlp Hli))) Hv0) as X0.
  rewrite liftshift_single_var_ty in X0 by exact (wf_ty_nf (IWi_famcod_wf Hi Hv HS Ha)). exact X0.
Qed.
(** The motive, the induction hypothesis's type and the step, weakened
    past one local under their binders. *)
Lemma IWi_tele_wk1 {Γ Y ly l lp li l' X A N D Ot C M c} : IWiSig Γ l lp li X A N D Ot C ->
  [ G ; Γ ,, Y @ ly ⊢[ i ] ] -> lwf (gL G) l' ->
  [ G ; Γ ,, X @ li ,, iwimotty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ]
      iwiihty l lp li l' X A N D Ot C M @ lmax lzero (lmax lp l') ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ,, iwiihty l lp li l' X A N D Ot C M @ lmax lzero (lmax lp l')
      ⊢[ i ] c : iwistepty l lp li X A N D Ot C M @ l' ] ->
  let X1 := X⟨↑⟩ in let A1 := A⟨↑⟩ in let N1 := N⟨rlift ↑⟩ in let D1 := D⟨rlift (rlift ↑)⟩ in
  let O1 := Ot⟨rlift ↑⟩ in let C1 := C⟨rlift (rlift (rlift ↑))⟩ in let M1 := M⟨rlift (rlift ↑)⟩ in
  [ G ; Γ ,, Y @ ly ,, X1 @ li ,, iwimotty l lp li X1 A1 N1 D1 O1 C1 @ iwiL l lp li ⊢[ i ] M1 @ l' ] /\
  [ G ; Γ ,, Y @ ly ,, A1 @ l ,, iwicsty l lp li X1 A1 N1 D1 O1 C1 @ iwiL l lp li ⊢[ i ]
      iwiihty l lp li l' X1 A1 N1 D1 O1 C1 M1 @ lmax lzero (lmax lp l') ] /\
  [ G ; Γ ,, Y @ ly ,, A1 @ l ,, iwicsty l lp li X1 A1 N1 D1 O1 C1 @ iwiL l lp li
      ,, iwiihty l lp li l' X1 A1 N1 D1 O1 C1 M1 @ lmax lzero (lmax lp l')
      ⊢[ i ] c⟨rlift (rlift (rlift ↑))⟩ : iwistepty l lp li X1 A1 N1 D1 O1 C1 M1 @ l' ].
Proof using Hi Hv.
  intros HS HΓY Hl' HM HI Hc X1 A1 N1 D1 O1 C1 M1.
  pose proof HS as (Hl & Hlp & Hli & _).
  pose proof (IWiSig_wk1 Hi Hv HS HΓY) as HS1. pose proof HS1 as (_ & _ & _ & HX1 & HA1 & _).
  pose proof (ext_wf Hi HA1 Hl) as HΓA.
  pose proof (IWi_cs_wf Hi Hv HS1) as HCs1.
  assert (HΓAC : [ G ; Γ ,, Y @ ly ,, A1 @ l ,, iwicsty l lp li X1 A1 N1 D1 O1 C1 @ iwiL l lp li ⊢[ i ] ])
    by (apply (ext_wf Hi); [exact HCs1 | exact (iwiL_wf Hl Hlp Hli)]).
  assert (HI1 : [ G ; Γ ,, Y @ ly ,, A1 @ l ,, iwicsty l lp li X1 A1 N1 D1 O1 C1 @ iwiL l lp li ⊢[ i ]
                  iwiihty l lp li l' X1 A1 N1 D1 O1 C1 M1 @ lmax lzero (lmax lp l') ]).
  { subst X1 A1 N1 D1 O1 C1 M1. rewrite <- IWi_ih_ren. eapply weakening_r; [exact HI | exact Hi | | exact HΓAC].
    eapply wkr_up'; [eapply wkr_up'; [apply wkr_shift1 | reflexivity] | symmetry; apply IWi_cs_ren]. }
  refine (conj (IWi_M_wk1 Hi Hv HS HΓY HM) (conj HI1 _)).
  subst X1 A1 N1 D1 O1 C1 M1. rewrite <- IWi_step_ren. eapply weakening_r; [exact Hc | exact Hi | |].
  - eapply wkr_up'; [eapply wkr_up'; [eapply wkr_up'; [apply wkr_shift1 | reflexivity]
                                     | symmetry; apply IWi_cs_ren] | symmetry; apply IWi_ih_ren].
  - apply (ext_wf Hi); [exact HI1 | repeat split; auto].
Qed.

(** The body, at the codomain. *)
Lemma IWi_IH_body_wf {Γ l lp li l' X A N D Ot C M c a cs} : IWiSig Γ l lp li X A N D Ot C -> lwf (gL G) l' ->
  [ G ; Γ ,, X @ li ,, iwimotty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ]
      iwiihty l lp li l' X A N D Ot C M @ lmax lzero (lmax lp l') ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ,, iwiihty l lp li l' X A N D Ot C M @ lmax lzero (lmax lp l')
      ⊢[ i ] c : iwistepty l lp li X A N D Ot C M @ l' ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] cs : tyDVec (iwiL l lp li) N[lsingle a] (iwiFam l lp li X A N D Ot C a) @ iwiL l lp li ] ->
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, D[llift (lsingle a)] @ lp ⊢[ i ] iwibody l lp li l' X A N D Ot C M c a cs
      : iwicod l lp li X A N D Ot C M a cs @ l' ].
Proof using Hi Hv.
  intros HS Hl' HM HI Hc Ha Hcs. pose proof HS as (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC).
  assert (HF : [ G ; Γ ⊢[ i ] tyFin N[lsingle a] @ lzero ])
    by (apply wft_fin; [exact Hv | exact (wf_tm_single Hi HN Ha)]).
  assert (HΓ1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] ]) by (apply (ext_wf Hi); [exact HF | exact I]).
  pose proof (ext_wf Hi (IWi_dom_wf Hi Hv HS Ha) Hlp) as HΓ2.
  pose proof (IWiSig_wk1 Hi Hv HS HΓ1) as HS1.
  pose proof (IWiSig_wk1 Hi Hv HS1 HΓ2) as HS2.
  destruct (IWi_tele_wk1 HS HΓ1 Hl' HM HI Hc) as (HM1 & HI1 & Hc1).
  destruct (IWi_tele_wk1 HS1 HΓ2 Hl' HM1 HI1 Hc1) as (HM2 & HI2 & Hc2).
  pose proof HS2 as (_ & _ & _ & HX2 & HA2 & HN2 & HD2 & HO2 & HC2).
  apply wf_elimIWi; first [exact Hv | assumption | idtac].
  - exact (IWi_mot_wf Hi Hv HS2).
  - exact (IWi_cs_wf Hi Hv HS2).
  - exact (IWi_ci_wf Hi Hv HS Ha).
  - exact (IWi_app_wf HS Ha Hcs).
Qed.

Lemma IWi_IH_wf {Γ l lp li l' X A N D Ot C M c a cs} : IWiSig Γ l lp li X A N D Ot C -> lwf (gL G) l' ->
  [ G ; Γ ,, X @ li ,, iwimotty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ]
      iwiihty l lp li l' X A N D Ot C M @ lmax lzero (lmax lp l') ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ,, iwiihty l lp li l' X A N D Ot C M @ lmax lzero (lmax lp l')
      ⊢[ i ] c : iwistepty l lp li X A N D Ot C M @ l' ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] cs : tyDVec (iwiL l lp li) N[lsingle a] (iwiFam l lp li X A N D Ot C a) @ iwiL l lp li ] ->
  [ G ; Γ ⊢[ i ] iwiIH l lp li l' X A N D Ot C M c a cs
      : (iwiihty l lp li l' X A N D Ot C M)[lsingle2 a cs] @ lmax lzero (lmax lp l') ].
Proof using Hi Hv.
  intros HS Hl' HM HI Hc Ha Hcs. pose proof HS as (Hl & Hlp & Hli & HX & HA & HN & HD & HO & HC).
  pose proof (IWiSig_nf HS) as (NX & NA & NN & ND & NO & NC).
  pose proof (wf_tm_nf Ha) as Na. pose proof (wf_tm_nf Hcs) as Ncs.
  rewrite IWi_E4 by assumption. rewrite iwiIH_body.
  apply wf_lam; [exact Hv | exact I | repeat split; assumption | apply wft_fin; [exact Hv | exact (wf_tm_single Hi HN Ha)] |].
  apply wf_lam; [exact Hv | exact Hlp | exact Hl' | exact (IWi_dom_wf Hi Hv HS Ha) |].
  exact (IWi_IH_body_wf HS Hl' HM HI Hc Ha Hcs).
Qed.

End IWiIH.
