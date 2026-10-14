(** * [elim_IWf]'s synthesized induction hypothesis, typed (M17b)

    As [PresupAux]'s [Wf_IH_body_wf] and [Wf_IH_wf], with [dnth] for
    [nth] and the child index threaded through: [iwfIH] is
    [λ^{0,l'}(i : Fin N[a/x]). elim_IWf(…↑; C[a/x, i]; dnth(cs↑; i))], at the
    [ih] entry's instance [Π^{0,l'}(Fin N[a/x]). M[C[a/x, i], dnth(cs↑; i)]].
    The declarative rules state the induction hypothesis's type a premise
    and β's induction hypothesis typed, so nothing in [Presupposition]
    needs this; [elim_IWf]'s validity does (its λs at a [sup_i]), and the
    type checker the [ih] entry's type from the motive ([IWf_ihty_wf]). The
    right-hand side of a congruence is typed in the right-hand signature,
    whose premises [IWf_prem_r] moves there ([pre_elimIWf_r]'s
    conversions). *)
From DeLaM.Typing Require Export PresupIWf DNth.

(** The induction hypothesis's body and codomain, in [Γ, i : Fin N[a/x]]. *)
Notation iwfdnth l li X A N Ot C a cs :=
  (tmDNth (lmax l li) N[lsingle a]⟨↑⟩ (iwfFam l li X A N Ot C a)⟨rlift ↑⟩ cs⟨↑⟩ (var 0)).
Notation iwfbody l li l' X A N Ot C M c a cs :=
  (tmElimIWf l li l' X⟨↑⟩ A⟨↑⟩ N⟨rlift ↑⟩ Ot⟨rlift ↑⟩ C⟨rlift (rlift ↑)⟩ M⟨rlift (rlift ↑)⟩
     c⟨rlift (rlift (rlift ↑))⟩ C[llift (lsingle a)] (iwfdnth l li X A N Ot C a cs)).
Notation iwfcod l li X A N Ot C M a cs :=
  (M⟨rlift (rlift ↑)⟩[lsingle2 C[llift (lsingle a)] (iwfdnth l li X A N Ot C a cs)]).

(** The telescope weakened past one local, under its binders. *)
Local Ltac rq := repeat first [rewrite lsingle2_ren_ty | rewrite ren_tmDNth | progress push_ren];
  repeat (first [solve [ren_comm] | f_equal]).
Lemma IWf_cs_ren l li (X A : ty) (N Ot C : tm) :
  (iwfcsty l li X A N Ot C)⟨rlift ↑⟩ = iwfcsty l li X⟨↑⟩ A⟨↑⟩ N⟨rlift ↑⟩ Ot⟨rlift ↑⟩ C⟨rlift (rlift ↑)⟩.
Proof. rq. Qed.
Lemma IWf_ih_ren l li l' (X A : ty) (N Ot C : tm) (M : ty) :
  (iwfihty l li l' X A N Ot C M)⟨rlift (rlift ↑)⟩ =
  iwfihty l li l' X⟨↑⟩ A⟨↑⟩ N⟨rlift ↑⟩ Ot⟨rlift ↑⟩ C⟨rlift (rlift ↑)⟩ M⟨rlift (rlift ↑)⟩.
Proof. rq. Qed.
Lemma IWf_step_ren l li (X A : ty) (N Ot C : tm) (M : ty) :
  (iwfstepty l li X A N Ot C M)⟨rlift (rlift (rlift ↑))⟩ =
  iwfstepty l li X⟨↑⟩ A⟨↑⟩ N⟨rlift ↑⟩ Ot⟨rlift ↑⟩ C⟨rlift (rlift ↑)⟩ M⟨rlift (rlift ↑)⟩.
Proof. rq. Qed.

(** The [ih] entry's instance at a shape and children. *)
Lemma IWf_E4 l li l' (X A : ty) (N Ot C : tm) (M : ty) a cs :
  nfty X -> nfty A -> nftm N -> nftm Ot -> nftm C -> nftm a -> nftm cs ->
  (iwfihty l li l' X A N Ot C M)[lsingle2 a cs] =
  tyPi lzero l' (tyFin N[lsingle a]) (iwfcod l li X A N Ot C M a cs).
Proof.
  intros NX NA NN NO NC Na Ncs. rewrite subst_tyPi. f_equal.
  - push_subst. f_equal. teq_core.
  - set (u0 := C[llift (lsingle a)]). set (v0 := iwfdnth l li X A N Ot C a cs).
    set (u := C⟨rlift ↑⟩).
    set (v := tmDNth (lmax l li) N⟨↑⟩⟨↑⟩
                (tyIWf l li X⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ A⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ N⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩
                   Ot⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩
                   C⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩ C⟨rlift ↑⟩⟨rlift ↑⟩)
                (var 1) (var 0)).
    assert (Eu : u[llift (lsingle2 a cs)] = u0) by (subst u u0; teq_core).
    assert (Ev : v[llift (lsingle2 a cs)] = v0).
    { subst v v0. rewrite subst_tmDNth by (intros [|[|[|n]]]; rewrite ?llk_llift; cbn; auto using ren_nf). unfold iwfFam.
      push_ren. push_subst. f_equal.
      all: try solve [rewrite ?llk_llift; cbn; reflexivity | teq_core].
      f_equal. all: try teq_core.
      rewrite <- ren_as_r2l. ren_comm. }
    rewrite subst_comp_ty, !ren_ren_comp_ty.
    rewrite (ren_subst_ty M _ _ (lcons (lcons (lshift 1) u0) v0)),
      (ren_subst_ty M (rlift (rlift ↑)) _ (lcons (lcons (lshift 1) u0) v0)); auto.
    all: intros [|[|n]]; pw.
    all: first [exact Eu | exact (eq_sym Eu) | exact Ev | exact (eq_sym Ev) | idtac].
    rewrite <- Ev. f_equal. subst v. rewrite ?ren_ren_comp_ty. reflexivity.
Qed.

(** The [ih] entry's type as its codomain at the bound shape and children,
    under the twice-weakened signature. *)
Lemma IWf_E_ihcod l li l' (X A : ty) (N Ot C : tm) (M : ty) :
  iwfihty l li l' X A N Ot C M =
  tyPi lzero l' (tyFin (N⟨rlift ↑⟩⟨rlift ↑⟩)[lsingle (var 1)])
    (iwfcod l li X⟨↑⟩⟨↑⟩ A⟨↑⟩⟨↑⟩ N⟨rlift ↑⟩⟨rlift ↑⟩ Ot⟨rlift ↑⟩⟨rlift ↑⟩
       C⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩ M⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩ (var 1) (var 0)).
Proof.
  f_equal.
  - f_equal. teq_core.
  - rewrite !ren_ren_comp_ty. f_equal. f_equal.
    + teq_core.
    + unfold iwfFam. f_equal; [teq_core |]. push_ren. f_equal; first [teq_core | ren_comm].
Qed.

Section IWfIH.
Context {G : gctx} {i : layer} (Hi : typeof i = i) (Hv : i <> lV).
Local Notation IWfSig := (@IWfSig G i).
Local Notation IWfEq := (@IWfEq G i).

Ltac wkn H := first [ exact H | eapply (wk1_ty G i Hi); [eassumption | wkn H] | eapply (wk1_tm G i Hi); [eassumption | wkn H] ].

(** The child index at a shape, in [Γ, i : Fin N[a/x]]. *)
Lemma IWf_ci_wf {Γ l li X A N Ot C a} : IWfSig Γ l li X A N Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] C[llift (lsingle a)] : X⟨↑⟩ @ li ].
Proof using Hi Hv.
  intros HS Ha. pose proof HS as (Hl & Hli & HX & HA & HN & HO & HC).
  assert (Hd : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] llift (lsingle a) : Γ ,, A @ l ,, tyFin N @ lzero ])
    by (eapply (lsub_wf_lift' G i Hi); [exact (lsub_wf_single G i Hi _ _ _ _ (ctx_of_wf_tm Hi Ha) Ha)
                                        | apply wft_fin; [exact Hv | exact (wf_tm_single Hi HN Ha)] | exact I
                                        | reflexivity]).
  pose proof (wf_tm_subst Hi HC Hd) as X0. rewrite IWf_E_C in X0 by exact (wf_ty_nf HX). exact X0.
Qed.

(** The child at the bound index, in [Γ, i : Fin N[a/x]]. *)
Lemma IWf_dnth_wf {Γ l li X A N Ot C a cs} : IWfSig Γ l li X A N Ot C -> [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] cs : tyDVec (lmax l li) N[lsingle a] (iwfFam l li X A N Ot C a) @ lmax l li ] ->
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] iwfdnth l li X A N Ot C a cs : iwfFam l li X A N Ot C a @ lmax l li ].
Proof using Hi Hv.
  intros HS Ha Hcs. pose proof HS as (Hl & Hli & HX & HA & HN & HO & HC).
  assert (HNa : [ G ; Γ ⊢[ i ] N[lsingle a] : tyNat @ lzero ]) by exact (wf_tm_single Hi HN Ha).
  assert (HF : [ G ; Γ ⊢[ i ] tyFin N[lsingle a] @ lzero ]) by (apply wft_fin; auto).
  assert (HΓ1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] ]) by (apply (ext_wf Hi); [exact HF | exact I]).
  assert (HN1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] N[lsingle a]⟨↑⟩ : tyNat @ lzero ])
    by (eapply wf_tm_retype; [wkn HNa | reflexivity]).
  pose proof (IWf_fam_wf Hi Hv HS Ha) as HFam.
  assert (HΓ2 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, tyFin N[lsingle a]⟨↑⟩ @ lzero ⊢[ i ] ])
    by (apply (ext_wf Hi); [apply wft_fin; [exact Hv | exact HN1] | exact I]).
  assert (HFam1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, tyFin N[lsingle a]⟨↑⟩ @ lzero
                    ⊢[ i ] (iwfFam l li X A N Ot C a)⟨rlift ↑⟩ @ lmax l li ])
    by (eapply weakening_r; [exact HFam | exact Hi | | exact HΓ2];
        eapply wkr_up'; [apply wkr_shift1 | reflexivity]).
  assert (Hcs1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] cs⟨↑⟩
                   : tyDVec (lmax l li) N[lsingle a]⟨↑⟩ (iwfFam l li X A N Ot C a)⟨rlift ↑⟩ @ lmax l li ])
    by (eapply wf_tm_retype; [wkn Hcs | reflexivity]).
  assert (Hv0 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] var 0 : tyFin N[lsingle a]⟨↑⟩ @ lzero ])
    by (apply wf_var; [rewrite Hi; exact HΓ1 | constructor]).
  pose proof (dnth_wf (compt_self Hi Hv) (lwf_max Hl Hli) HN1 HFam1 Hcs1 Hv0) as X0.
  rewrite liftshift_single_var_ty in X0 by exact (wf_ty_nf HFam). exact X0.
Qed.

(** The body, at the codomain. *)
Lemma IWf_IH_body_wf {Γ l li l' X A N Ot C M c a cs} : IWfSig Γ l li X A N Ot C -> lwf (gL G) l' ->
  [ G ; Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ⊢[ i ] iwfihty l li l' X A N Ot C M @ lmax lzero l' ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ,, iwfihty l li l' X A N Ot C M @ lmax lzero l'
      ⊢[ i ] c : iwfstepty l li X A N Ot C M @ l' ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] cs : tyDVec (lmax l li) N[lsingle a] (iwfFam l li X A N Ot C a) @ lmax l li ] ->
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] iwfbody l li l' X A N Ot C M c a cs
      : iwfcod l li X A N Ot C M a cs @ l' ].
Proof using Hi Hv.
  intros HS Hl' HM HI Hc Ha Hcs. pose proof HS as (Hl & Hli & HX & HA & HN & HO & HC).
  assert (HF : [ G ; Γ ⊢[ i ] tyFin N[lsingle a] @ lzero ])
    by (apply wft_fin; [exact Hv | exact (wf_tm_single Hi HN Ha)]).
  assert (HΓ1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] ]) by (apply (ext_wf Hi); [exact HF | exact I]).
  pose proof (IWfSig_wk1 Hi Hv HS HΓ1) as HS1.
  pose proof HS1 as (_ & _ & HX1 & HA1 & HN1 & HO1 & HC1).
  assert (HΓ1A : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, A⟨↑⟩ @ l ⊢[ i ] ]) by exact (ext_wf Hi HA1 Hl).
  pose proof (IWf_cs_wf Hi Hv HS1) as HCs1.
  assert (HΓ1AC : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, A⟨↑⟩ @ l
                    ,, iwfcsty l li X⟨↑⟩ A⟨↑⟩ N⟨rlift ↑⟩ Ot⟨rlift ↑⟩ C⟨rlift (rlift ↑)⟩ @ lmax l li ⊢[ i ] ])
    by (apply (ext_wf Hi); [exact HCs1 | exact (lwf_max Hl Hli)]).
  assert (HI1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ,, A⟨↑⟩ @ l
                  ,, iwfcsty l li X⟨↑⟩ A⟨↑⟩ N⟨rlift ↑⟩ Ot⟨rlift ↑⟩ C⟨rlift (rlift ↑)⟩ @ lmax l li
                  ⊢[ i ] iwfihty l li l' X⟨↑⟩ A⟨↑⟩ N⟨rlift ↑⟩ Ot⟨rlift ↑⟩ C⟨rlift (rlift ↑)⟩ M⟨rlift (rlift ↑)⟩
                  @ lmax lzero l' ]).
  { rewrite <- IWf_ih_ren. eapply weakening_r; [exact HI | exact Hi | | exact HΓ1AC].
    eapply wkr_up'; [eapply wkr_up'; [apply wkr_shift1 | reflexivity] | symmetry; apply IWf_cs_ren]. }
  apply wf_elimIWf; first [exact Hv | exact (compt_self Hi Hv) | assumption | idtac].
  - exact (IWf_mot_wf Hi Hv HS1).
  - exact (IWf_M_wk1 Hi Hv HS HΓ1 HM).
  - (* the step, weakened under the telescope *)
    rewrite <- IWf_step_ren. eapply weakening_r; [exact Hc | exact Hi | |].
    + eapply wkr_up'; [eapply wkr_up'; [eapply wkr_up'; [apply wkr_shift1 | reflexivity]
                                       | symmetry; apply IWf_cs_ren] | symmetry; apply IWf_ih_ren].
    + apply (ext_wf Hi); [exact HI1 | apply lwf_max; [exact I | exact Hl']].
  - exact (IWf_ci_wf HS Ha).
  - exact (IWf_dnth_wf HS Ha Hcs).
Qed.

Lemma IWf_IH_wf {Γ l li l' X A N Ot C M c a cs} : IWfSig Γ l li X A N Ot C -> lwf (gL G) l' ->
  [ G ; Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ⊢[ i ] iwfihty l li l' X A N Ot C M @ lmax lzero l' ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ,, iwfihty l li l' X A N Ot C M @ lmax lzero l'
      ⊢[ i ] c : iwfstepty l li X A N Ot C M @ l' ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] cs : tyDVec (lmax l li) N[lsingle a] (iwfFam l li X A N Ot C a) @ lmax l li ] ->
  [ G ; Γ ⊢[ i ] iwfIH l li l' X A N Ot C M c a cs : (iwfihty l li l' X A N Ot C M)[lsingle2 a cs] @ lmax lzero l' ].
Proof using Hi Hv.
  intros HS Hl' HM HI Hc Ha Hcs. pose proof HS as (Hl & Hli & HX & HA & HN & HO & HC).
  pose proof (IWfSig_nf HS) as (NX & NA & NN & NO & NC).
  pose proof (wf_tm_nf Ha) as Na. pose proof (wf_tm_nf Hcs) as Ncs.
  rewrite IWf_E4 by assumption. unfold iwfIH.
  apply wf_lam; [exact Hv | exact I | exact Hl' | apply wft_fin; [exact Hv | exact (wf_tm_single Hi HN Ha)] |].
  exact (IWf_IH_body_wf HS Hl' HM HI Hc Ha Hcs).
Qed.

(** A congruence's right-hand premises, moved into the right-hand
    signature's contexts. *)
Lemma IWf_prem_r {Γ l li l' k ki k' X X' A A' N N' Ot Ot' C C' M M' c'} :
  IWfEq Γ l li k ki X X' A A' N N' Ot Ot' C C' -> lequiv (gL G) l' k' ->
  [ G ; Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li ⊢[ i ] M ≅ M' @ l' ] ->
  [ G ; Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li ⊢[ i ] M' @ l' ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ⊢[ i ] iwfihty l li l' X A N Ot C M @ lmax lzero l' ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ⊢[ i ]
      iwfihty l li l' X A N Ot C M ≅ iwfihty k ki k' X' A' N' Ot' C' M' @ lmax lzero l' ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ⊢[ i ] iwfihty k ki k' X' A' N' Ot' C' M' @ lmax lzero l' ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ,, iwfihty l li l' X A N Ot C M @ lmax lzero l'
      ⊢[ i ] c' : iwfstepty l li X A N Ot C M @ l' ] ->
  IWfSig Γ k ki X' A' N' Ot' C' /\ lwf (gL G) k' /\
  [ G ; Γ ,, X' @ ki ,, iwfmotty k ki X' A' N' Ot' C' @ lmax k ki ⊢[ i ] M' @ k' ] /\
  [ G ; Γ ,, A' @ k ,, iwfcsty k ki X' A' N' Ot' C' @ lmax k ki ⊢[ i ]
      iwfihty k ki k' X' A' N' Ot' C' M' @ lmax lzero k' ] /\
  [ G ; Γ ,, A' @ k ,, iwfcsty k ki X' A' N' Ot' C' @ lmax k ki ,, iwfihty k ki k' X' A' N' Ot' C' M' @ lmax lzero k'
      ⊢[ i ] c' : iwfstepty k ki X' A' N' Ot' C' M' @ k' ].
Proof using Hi Hv.
  intros HE H' HM HMM HM' HI EI HI' Hc'.
  pose proof (IWfEq_sig_r Hi Hv HE) as HS'.
  pose proof HE as (Hlk & Hlik & HS & HXX & HAA & HNN & HOO & HCC & HX' & HA' & HN' & HO' & HC').
  pose proof HS as (Hl & Hli & HX & HA & HN & HO & HC).
  pose proof (lequiv_wf_l _ _ _ H') as Hl'. pose proof (lequiv_wf_r _ _ _ H') as Hk'.
  assert (HLK : lequiv (gL G) (lmax l li) (lmax k ki)) by (apply lequiv_max; assumption).
  assert (HLI : lequiv (gL G) (lmax lzero l') (lmax lzero k'))
    by (apply lequiv_max; [apply lequiv_refl; exact I | exact H']).
  (* the motive *)
  pose proof (proj2 (ctx_conv_ext Hi (IWf_id1 Hi HX HXX HX' Hlik) (IWf_mot_wf Hi Hv HS) (IWf_mot_eq Hi Hv HE) (IWf_mot_r Hi Hv HE) HLK))
    as Hidm.
  assert (HM'p : [ G ; Γ ,, X' @ ki ,, iwfmotty k ki X' A' N' Ot' C' @ lmax k ki ⊢[ i ] M' @ k' ])
    by (eapply wft_lconv; [exact (mv_ty Hi Hidm HM') | exact (lequiv_sym _ _ _ H')]).
  (* the induction hypothesis's type and the step *)
  pose proof (proj2 (ctx_conv_ext Hi (IWf_id1 Hi HA HAA HA' Hlk) (IWf_cs_wf Hi Hv HS) (IWf_cs_eq Hi Hv HE) (IWf_cs_r Hi Hv HE) HLK))
    as Hid2.
  assert (HI'p : [ G ; Γ ,, A' @ k ,, iwfcsty k ki X' A' N' Ot' C' @ lmax k ki ⊢[ i ]
                   iwfihty k ki k' X' A' N' Ot' C' M' @ lmax lzero k' ])
    by (eapply wft_lconv; [exact (mv_ty Hi Hid2 HI') | exact (lequiv_sym _ _ _ HLI)]).
  pose proof (proj2 (ctx_conv_ext Hi Hid2 HI EI HI' HLI)) as Hid3.
  assert (HΘ : [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ,, iwfihty l li l' X A N Ot C M @ lmax lzero l' ⊢[ i ] ])
    by (apply (ext_wf Hi); [exact HI | apply lwf_max; [exact I | exact Hl']]).
  pose proof (IWf_step_eq Hi Hv HE HM HMM HΘ) as ES.
  refine (conj HS' (conj Hk' (conj HM'p (conj HI'p _)))).
  pose proof (wf_tm_subst Hi Hc' Hid3) as X0.
  pose proof (eqty_subst Hi ES Hid3) as Y0.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 typed_nf)))) _ _ _ _ _ _ ES) as [N1 N2].
  rewrite nf_id in X0 by exact (wf_tm_nf Hc').
  rewrite (nf_id_ty (iwfstepty l li X A N Ot C M)) in X0, Y0 by exact N1.
  rewrite (nf_id_ty (iwfstepty k ki X' A' N' Ot' C' M')) in Y0 by exact N2.
  eapply wf_lconv; [eapply (conv_tm' Hi); [exact X0 | exact (eqty_sym' Y0)] | exact (lequiv_sym _ _ _ H')].
Qed.

(** The induction hypothesis's codomain and type, typed from the motive:
    the premise [wf_elimIWf] states is admissible once [dnth] is typed
    (the type checker builds it). *)
Lemma IWf_cod_wf {Γ l li l' X A N Ot C M a cs} : IWfSig Γ l li X A N Ot C ->
  [ G ; Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ⊢[ i ] a : A @ l ] ->
  [ G ; Γ ⊢[ i ] cs : tyDVec (lmax l li) N[lsingle a] (iwfFam l li X A N Ot C a) @ lmax l li ] ->
  [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] iwfcod l li X A N Ot C M a cs @ l' ].
Proof using Hi Hv.
  intros HS HM Ha Hcs. pose proof HS as (Hl & Hli & HX & HA & HN & HO & HC).
  pose proof (IWfSig_nf HS) as (NX & NA & NN & NO & NC).
  assert (HF : [ G ; Γ ⊢[ i ] tyFin N[lsingle a] @ lzero ])
    by (apply wft_fin; [exact Hv | exact (wf_tm_single Hi HN Ha)]).
  assert (HΓ1 : [ G ; Γ ,, tyFin N[lsingle a] @ lzero ⊢[ i ] ]) by (apply (ext_wf Hi); [exact HF | exact I]).
  pose proof (IWf_M_wk1 Hi Hv HS HΓ1 HM) as HM1.
  pose proof (IWf_ci_wf HS Ha) as Hci.
  pose proof (IWf_dnth_wf HS Ha Hcs) as Hd.
  assert (E : iwfFam l li X A N Ot C a
             = (iwfmotty l li X⟨↑⟩ A⟨↑⟩ N⟨rlift ↑⟩ Ot⟨rlift ↑⟩ C⟨rlift (rlift ↑)⟩)[lsingle C[llift (lsingle a)]])
    by (unfold iwfFam; rewrite IWf_E_mot by auto using ren_nf_ty, ren_nf; reflexivity).
  exact (wf_ty_subst Hi HM1 (lsub_wf_single2' Hi HΓ1 Hci (ltac:(eapply wf_tm_retype; [exact Hd | exact E])))).
Qed.

Lemma IWf_ihty_wf {Γ l li l' X A N Ot C M} : IWfSig Γ l li X A N Ot C -> lwf (gL G) l' ->
  [ G ; Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ⊢[ i ] iwfihty l li l' X A N Ot C M @ lmax lzero l' ].
Proof using Hi Hv.
  intros HS Hl' HM. pose proof HS as (Hl & Hli & HX & HA & HN & HO & HC).
  pose proof (IWfSig_nf HS) as (NX & NA & NN & NO & NC).
  pose proof (ext_wf Hi HA Hl) as HΓA.
  pose proof (IWf_cs_wf Hi Hv HS) as HCs.
  assert (HΘ : [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ⊢[ i ] ])
    by (apply (ext_wf Hi); [exact HCs | exact (lwf_max Hl Hli)]).
  pose proof (IWfSig_wk1 Hi Hv HS HΓA) as HS1.
  pose proof (IWfSig_wk1 Hi Hv HS1 HΘ) as HS2.
  pose proof (IWf_M_wk1 Hi Hv HS1 HΘ (IWf_M_wk1 Hi Hv HS HΓA HM)) as HM2.
  assert (Ha : [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ⊢[ i ] var 1 : A⟨↑⟩⟨↑⟩ @ l ])
    by (apply wf_var; [rewrite Hi; exact HΘ | repeat constructor]).
  assert (Hcs : [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ⊢[ i ] var 0
                  : tyDVec (lmax l li) (N⟨rlift ↑⟩⟨rlift ↑⟩)[lsingle (var 1)]
                      (iwfFam l li X⟨↑⟩⟨↑⟩ A⟨↑⟩⟨↑⟩ N⟨rlift ↑⟩⟨rlift ↑⟩ Ot⟨rlift ↑⟩⟨rlift ↑⟩
                         C⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩ (var 1)) @ lmax l li ]).
  { eapply wf_tm_retype; [apply wf_var; [rewrite Hi; exact HΘ | constructor] |].
    unfold iwfFam. push_ren. push_subst. f_equal; [teq_core |]. f_equal; first [teq_core | ren_comm]. }
  rewrite IWf_E_ihcod. apply wft_pi; [exact Hv | exact I | exact Hl' | |].
  - apply wft_fin; [exact Hv | exact (wf_tm_single Hi (proj1 (proj2 (proj2 (proj2 (proj2 HS2))))) Ha)].
  - exact (IWf_cod_wf HS2 HM2 Ha Hcs).
Qed.

End IWfIH.
