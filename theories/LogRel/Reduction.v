(** * Closure under typed weak-head expansion (ch. 7, Weak Head Expansion)

    Types (and terms) that reduce to related ones are related, with the
    same term relation. *)
From DeLaM.LogRel Require Export Neutral.
From DeLaM.LogRel Require Import MAux.

Section Reduction.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

Lemma tmred_along {G Γ t u T W l l'} :
  [ G ; Γ ⊢g t ⤳* u : T @ l ] -> [ G ; Γ ⊢g T ⤳* W @ l ] -> lequiv (gL G) l' l ->
  [ G ; Γ ⊢g t ⤳* u : W @ l' ].
Proof.
  intros Ht HT Hl. eapply tmred_lconv; [|exact Hl].
  eapply tmred_conv; [apply ge_typeof | exact Ht | apply HT].
Qed.

Lemma ModRel_red_ty {G Γ T T' l R T1 T1'} : ModRel G Γ T T' l R ->
  [ G ; Γ ⊢g T1 ⤳* T @ l ] -> [ G ; Γ ⊢g T1' ⤳* T' @ l ] -> ModRel G Γ T1 T1' l R.
Proof.
  destruct 1 as [T T' l Δ Δ' k k' R Hl Hk HT HT' HΔ Hgeq HR
                | T T' l Δ Δ' A A' k k' R Hl Hk HT HT' HΔ HA HA' Hgeq HR]; intros H1 H1'.
  - exact (MRctyp _ _ _ _ _ _ _ _ _ _ Hl Hk (tyred_trans _ _ _ _ H1 HT) (tyred_trans _ _ _ _ H1' HT')
             HΔ Hgeq HR).
  - exact (MRctrm _ _ _ _ _ _ _ _ _ _ _ _ Hl Hk (tyred_trans _ _ _ _ H1 HT)
             (tyred_trans _ _ _ _ H1' HT') HΔ HA HA' Hgeq HR).
Qed.

Lemma ModRel_red_tm {G Γ T T' l R} : ModRel G Γ T T' l R -> forall t t' t1 t1', R t t' ->
  [ G ; Γ ⊢g t1 ⤳* t : T @ l ] -> [ G ; Γ ⊢g t1' ⤳* t' : T' @ l ] -> R t1 t1'.
Proof.
  destruct 1 as [T T' l Δ Δ' k k' R Hl Hk HT HT' HΔ Hgeq HR
                | T T' l Δ Δ' A A' k k' R Hl Hk HT HT' HΔ HA HA' Hgeq HR];
    intros t t' t1 t1' Htt H1 H1'; apply HR; apply HR in Htt;
    destruct Htt as (w & w' & Hw & Hw' & Htt);
    exists w, w'; refine (conj _ (conj _ Htt)).
  all: eapply tmred_trans; [|eassumption].
  all: eapply tmred_along; [eassumption | eassumption | solve [apply lequiv_sym; assumption]].
Qed.

(** ** [M] (M18b): [out] of the expansions reduces to [out] of the
    terms, so [Σ]'s relation at [out]'s observations extends to them; the
    children are unchanged. *)

Lemma SigRel_red {G Γ l1 l2 l3 l4 A B A' B' domR codR t t' u u'} :
  SigRel G Γ l1 l2 l3 l4 A B A' B' domR codR u u' ->
  [ G ; Γ ⊢g t ⤳* u : tySig l1 l2 A B @ lmax l1 l2 ] -> [ G ; Γ ⊢g t' ⤳* u' : tySig l3 l4 A' B' @ lmax l1 l2 ] ->
  SigRel G Γ l1 l2 l3 l4 A B A' B' domR codR t t'.
Proof.
  intros (w & w' & R1 & R2 & Hrest) H1 H2. exists w, w'.
  exact (conj (tmred_trans _ _ _ _ _ H1 R1) (conj (tmred_trans _ _ _ _ _ H2 R2) Hrest)).
Qed.

Lemma tmred_out_cong {G Γ l l' li X A B C j t w} :
  MSig (G := G) (i := ge_layer) Γ l l' li X A B C -> [ G ; Γ ⊢g j : X @ li ] ->
  [ G ; Γ ⊢g t ⤳* w : tyM l l' li X A B C j @ mlvl l l' li ] ->
  [ G ; Γ ⊢g tmOut l l' li X A B C j t ⤳* tmOut l l' li X A B C j w : mOutTy l l' li X A B C j @ lmax l (mlvl l l' li) ].
Proof.
  intros (Hl & Hl' & Hli & HX & HA & HB & HC) Hj [Ht Hr Heq]. split.
  - apply wf_out; auto using ge_compt.
  - now apply reds_out.
  - apply eqtm_out; auto using ge_compt, lequiv_refl, eqty_refl, eqtm_refl.
Qed.

(** At any annotations equal to the signature and index. *)
Lemma tmred_out_ann {G Γ l l' li X A B C j k k' ki X1 A1 B1 C1 j1 t w} :
  MSig (G := G) (i := ge_layer) Γ l l' li X A B C -> MAnn G Γ l l' li X A B C j k k' ki X1 A1 B1 C1 j1 ->
  [ G ; Γ ⊢g t ⤳* w : tyM l l' li X A B C j @ mlvl l l' li ] ->
  [ G ; Γ ⊢g tmOut k k' ki X1 A1 B1 C1 j1 t ⤳* tmOut k k' ki X1 A1 B1 C1 j1 w
      : mOutTy l l' li X A B C j @ lmax l (mlvl l l' li) ].
Proof.
  intros HS Ann Ht. pose proof (MEq_of_MAnn HS Ann) as HE1.
  pose proof (MEq_sig_r ge_typeof ge_notV HE1) as HS1.
  pose proof Ann as (K1 & K2 & Ki & EX1 & _ & _ & _ & Ej1).
  pose proof (eqtm_wf_l ge_typeof Ej1) as Hj. pose proof (eqtm_wf_r ge_typeof Ej1) as Hj'.
  assert (Hj1 : [ G ; Γ ⊢g j1 : X1 @ ki ]).
  { eapply wf_lconv; [| exact Ki]. eapply wf_conv; [exact Hj' | rewrite ge_typeof; exact (eqty_sym _ _ _ _ _ _ EX1)]. }
  assert (Ht1 : [ G ; Γ ⊢g t ⤳* w : tyM k k' ki X1 A1 B1 C1 j1 @ mlvl k k' ki ]).
  { eapply tmred_lconv; [| exact (lequiv_mlvl K1 K2 Ki)].
    eapply tmred_conv; [exact ge_typeof | exact Ht | exact (M_ty_eq ge_typeof ge_notV HE1 Ej1)]. }
  eapply tmred_conv; [exact ge_typeof | | exact (eqty_sym _ _ _ _ _ _ (M_out_eq ge_typeof ge_notV HE1 Hj Hj' Ej1))].
  eapply tmred_lconv; [exact (tmred_out_cong HS1 Hj1 Ht1) |].
  exact (lequiv_sym _ _ _ (lequiv_max _ _ _ _ _ K1 (lequiv_mlvl K1 K2 Ki))).
Qed.

Lemma MRn_red k {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' shR posR m m' t t' t1 t1'} :
  MGeq G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' ->
  MRn k G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' shR posR m m' t t' ->
  [ G ; Γ ⊢g t1 ⤳* t : tyM l1 l2 li X A B C m @ mlvl l1 l2 li ] ->
  [ G ; Γ ⊢g t1' ⤳* t' : tyM r1 r2 ri X' A' B' C' m' @ mlvl l1 l2 li ] ->
  MRn k G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' shR posR m m' t1 t1'.
Proof.
  intros HG. destruct k as [|k]; intros [(w & w' & R1 & R2 & Hrest) Ho] H1 H1'.
  all: split; [exists w, w'; exact (conj (tmred_trans _ _ _ _ _ H1 R1) (conj (tmred_trans _ _ _ _ _ H1' R2) Hrest)) |].
  1: exact Logic.I.
  pose proof HG as (Q1 & Q2 & Qi & _).
  assert (Hm : lequiv (gL G) (mlvl l1 l2 li) (mlvl r1 r2 ri)) by (apply lequiv_mlvl; assumption).
  intros ρ. specialize (Ho ρ). unfold MObs in Ho |- *.
  intros k1 k2 ki X1 A1 B1 C1 j1 k1' k2' ki' X1' A1' B1' C1' j1' Ann Ann'.
  specialize (Ho k1 k2 ki X1 A1 B1 C1 j1 k1' k2' ki' X1' A1' B1' C1' j1' Ann Ann').
  pose proof (MGeq_kw ρ HG) as HGρ.
  pose proof HGρ as (_ & _ & _ & HSρ & _).
  pose proof (MEq_sig_r ge_typeof ge_notV (MEq_of_MGeq HGρ)) as HSρ'.
  pose proof (kw_tmred ρ H1) as Y. pose proof (kw_tmred ρ H1') as Y'. rewrite kty_tyM in Y, Y'.
  refine (SigRel_red Ho (tmred_out_ann HSρ Ann Y) _).
  eapply tmred_lconv; [exact (tmred_out_ann HSρ' Ann' (tmred_lconv _ _ _ _ _ Y' (kw_lequiv ρ (lequiv_sym _ _ _ Hm)))) |].
  exact (kw_lequiv ρ (lequiv_max _ _ _ _ _ Q1 Hm)).
Qed.

Theorem LR_red_ty n rec G Γ T T' l R :
  LR n rec G Γ T T' l R -> forall T1 T1',
  [ G ; Γ ⊢g T1 ⤳* T @ l ] -> [ G ; Γ ⊢g T1' ⤳* T' @ l ] -> LR n rec G Γ T1 T1' l R.
Proof.
  destruct 1 as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l l1 l2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l l1 l2 U1 U1' instR R Hj Hl Hl2 Hw1 HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' l1 l2 l3 l4 U1 U1' instR R Hj Hl Hl3 Hl4 Hw1 Hw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l l1 l2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l l1 l2 A A' N N' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l l1 l2 A A' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR
                | G Γ T T' l il1 ilp1 ili1 il2 ilp2 ili2 iX iX' iA iA' iN iN' iD iD' iO iO' iC iC' im im' iidxR idomR ipdR R
                    Hl Hil2 Hilp2 Hili2 Hiw Hiwp Hiwi HT HT' HiX HiX' HiA HiA' HiN HiN' HiD HiD' HiO HiO' HiC HiC' Him Him'
                    HiXX HiAA HiNN HiDD HiOO HiCC Himm iidxAd Hiisym Hiistr idomAd iarAd iotAd ipdAd ipdE ichAd igC iixAd HR];
    intros T1 T1' H1 H1'.
  - eapply LRnat; eauto using tyred_trans.
  - eapply LRU with (l1 := l1) (l2 := l2); eauto using tyred_trans.
  - eapply LRne with (V := V) (V' := V'); eauto using tyred_trans.
  - eapply (LRpi n rec G Γ T1 T1' l l1 l2 l3 l4 A B A' B' domR codR); [split|..]; eauto using tyred_trans.
  - apply LRmod; [exact Hj | exact (ModRel_red_ty HM H1 H1')].
  - eapply (LRcpi n rec G Γ T1 T1' l l1 l2 U1 U1' instR); eauto using tyred_trans.
  - eapply (LRtpi n rec G Γ T1 T1' l Δ1 Δ1' l1 l2 l3 l4 U1 U1' instR); eauto using tyred_trans.
  - eapply (LRsig n rec G Γ T1 T1' l l1 l2 l3 l4 A B A' B' domR codR); [split|..]; eauto using tyred_trans.
  - eapply (LRunit n rec G Γ T1 T1' l l1 l2); eauto using tyred_trans.
  - eapply (LRseq n rec G Γ T1 T1' l s1 s2); eauto using tyred_trans.
  - eapply (LRsempty n rec G Γ T1 T1' l s1 s2); eauto using tyred_trans.
  - eapply (LRid n rec G Γ T1 T1' l s1 s2); eauto using tyred_trans.
  - eapply (LRempty n rec G Γ T1 T1' l s1 s2); eauto using tyred_trans.
  - eapply (LRsum n rec G Γ T1 T1' l u1 u2 u3 u4 UA UA' UB UB' RA RB); eauto using tyred_trans.
  - eapply (LRw n rec G Γ T1 T1' l l1 l2 l3 l4 A B A' B' domR codR); [split|..]; eauto using tyred_trans.
  - eapply (LRwf n rec G Γ T1 T1' l l1 l2 A A' N N' domR); eauto using tyred_trans.
  - eapply (LRsq n rec G Γ T1 T1' l l1 l2 A A' RQ); eauto using tyred_trans.
  - eapply (LRiwf n rec G Γ T1 T1' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR);
      eauto using tyred_trans.
  - exact (LRm n rec G Γ T1 T1' l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ midxR mshR mposR R Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi
             (tyred_trans _ _ _ _ H1 HT) (tyred_trans _ _ _ _ H1' HT') HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
             HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR).
  - exact (LRiwi n rec G Γ T1 T1' l _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ iidxR idomR ipdR R
             Hl Hil2 Hilp2 Hili2 Hiw Hiwp Hiwi (tyred_trans _ _ _ _ H1 HT) (tyred_trans _ _ _ _ H1' HT')
             HiX HiX' HiA HiA' HiN HiN' HiD HiD' HiO HiO' HiC HiC' Him Him'
             HiXX HiAA HiNN HiDD HiOO HiCC Himm iidxAd Hiisym Hiistr idomAd iarAd iotAd ipdAd ipdE ichAd igC iixAd HR).
Qed.

Theorem LR_red_tm n rec G Γ T T' l R :
  LR n rec G Γ T T' l R -> forall t t' t1 t1', R t t' ->
  [ G ; Γ ⊢g t1 ⤳* t : T @ l ] -> [ G ; Γ ⊢g t1' ⤳* t' : T' @ l ] -> R t1 t1'.
Proof.
  destruct 1 as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l l1 l2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l l1 l2 T1 T1' instR R Hj Hl Hl2 Hw1 HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' l1 l2 l3 l4 T1 T1' instR R Hj Hl Hl3 Hl4 Hw1 Hw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l l1 l2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l l1 l2 A A' N N' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l l1 l2 A A' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR
                | G Γ T T' l il1 ilp1 ili1 il2 ilp2 ili2 iX iX' iA iA' iN iN' iD iD' iO iO' iC iC' im im' iidxR idomR ipdR R
                    Hl Hil2 Hilp2 Hili2 Hiw Hiwp Hiwi HT HT' HiX HiX' HiA HiA' HiN HiN' HiD HiD' HiO HiO' HiC HiC' Him Him'
                    HiXX HiAA HiNN HiDD HiOO HiCC Himm iidxAd Hiisym Hiistr idomAd iarAd iotAd ipdAd ipdE ichAd igC iixAd HR];
    intros t t' t1 t1' Htt H1 H1';
    first [exact (ModRel_red_tm HM _ _ _ _ Htt H1 H1') | apply HR; apply HR in Htt].
  - inversion Htt as [? ? w w' Hw Hw' Heq Hnf]; subst.
    econstructor; [| |exact Heq|exact Hnf].
    + eapply tmred_trans; [|exact Hw]. eapply tmred_along; [exact H1 | exact HT | solve [apply lequiv_sym; assumption]].
    + eapply tmred_trans; [|exact Hw']. eapply tmred_along; [exact H1' | exact HT' | solve [apply lequiv_sym; assumption]].
  - destruct Htt as (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & HK).
    exists w, w'. refine (conj _ (conj _ (conj Hnf (conj Hnf' (conj Heq HK))))).
    + eapply tmred_trans; [|exact Hw]. eapply tmred_along; [exact H1 | exact HT | solve [apply lequiv_sym; assumption]].
    + eapply tmred_trans; [|exact Hw']. eapply (tmred_lconv _ _ _ _ l); [|solve [apply lequiv_sym; assumption]].
      eapply tmred_conv; [apply ge_typeof | exact H1' |].
      eapply eqty_trans; [apply HT'|]. eapply eqty_lconv.
      * apply eqty_U; [exact ge_notV | rewrite ge_typeof; eapply tyred_ctx, HT | exact Hl2].
      * eapply lequiv_trans; [exact Hl | apply lequiv_suc, lequiv_sym, Hl2].
  - destruct Htt as (ν & ν' & Hν & Hν' & Hn & Hn').
    exists ν, ν'. refine (conj _ (conj _ (conj Hn Hn'))).
    + eapply tmred_trans; [|exact Hν]. eapply tmred_conv; [apply ge_typeof | exact H1 | apply HT].
    + eapply tmred_trans; [|exact Hν']. eapply tmred_conv; [apply ge_typeof | exact H1' | apply HT'].
  - destruct Htt as (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
    exists w, w'. refine (conj _ (conj _ (conj Hnf (conj Hnf' (conj Heq (conj Heq' HK)))))).
    + eapply tmred_trans; [|exact Hw]. eapply tmred_along; [exact H1 | exact HT | solve [apply lequiv_sym; assumption]].
    + eapply tmred_trans; [|exact Hw']. eapply tmred_along; [exact H1' | exact HT' | solve [apply lequiv_sym; assumption]].
  - (* CΠ *)
    destruct Htt as (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
    exists w, w'. refine (conj _ (conj _ (conj Hnf (conj Hnf' (conj Heq (conj Heq' HK)))))).
    + eapply tmred_trans; [|exact Hw]. eapply tmred_along; [exact H1 | exact HT | solve [apply lequiv_sym; assumption]].
    + eapply tmred_trans; [|exact Hw']. eapply tmred_along; [exact H1' | exact HT' | solve [apply lequiv_sym; assumption]].
  - (* TΠ *)
    destruct Htt as (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
    exists w, w'. refine (conj _ (conj _ (conj Hnf (conj Hnf' (conj Heq (conj Heq' HK)))))).
    + eapply tmred_trans; [|exact Hw]. eapply tmred_along; [exact H1 | exact HT | solve [apply lequiv_sym; assumption]].
    + eapply tmred_trans; [|exact Hw']. eapply tmred_along; [exact H1' | exact HT' | solve [apply lequiv_sym; assumption]].
  - (* Σ *)
    destruct Htt as (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
    exists w, w'. refine (conj _ (conj _ (conj Hnf (conj Hnf' (conj Heq (conj Heq' HK)))))).
    + eapply tmred_trans; [|exact Hw]. eapply tmred_along; [exact H1 | exact HT | solve [apply lequiv_sym; assumption]].
    + eapply tmred_trans; [|exact Hw']. eapply tmred_along; [exact H1' | exact HT' | solve [apply lequiv_sym; assumption]].
  - (* Unit *)
    destruct Htt as (w & w' & Hr & Hr' & Hn & Hn'). exists w, w'.
    refine (conj _ (conj _ (conj Hn Hn'))).
    + eapply tmred_trans; [|exact Hr]. eapply tmred_along; [exact H1 | exact HT | solve [apply lequiv_sym; assumption]].
    + eapply tmred_trans; [|exact Hr']. apply (unit_tmred_conv Hl2).
      eapply tmred_along; [exact H1' | exact HT' | eapply lequiv_trans; [exact Hl2 | solve [apply lequiv_sym; assumption]]].
  - (* sEq: the right side at the left's type *)
    destruct Htt as (w & w' & Hr & Hr' & Hn & Hn'). exists w, w'.
    refine (conj _ (conj _ (conj Hn Hn'))).
    + eapply tmred_trans; [|exact Hr]. eapply tmred_along; [exact H1 | exact HT | solve [apply lequiv_sym; assumption]].
    + eapply tmred_trans; [|exact Hr']. eapply (tmred_lconv _ _ _ _ l); [|solve [apply lequiv_sym; assumption]].
      eapply tmred_conv; [apply ge_typeof | exact H1' |].
      eapply eqty_trans; [apply HT'|]. eapply eqty_lconv; [|exact Hl].
      apply eqty_sym, geq_ty_sound, geq_ty_seq; auto using lequiv_sym.
  - (* sEmpty *)
    destruct Htt as (w & w' & Hr & Hr' & Hn & Hn'). exists w, w'.
    refine (conj _ (conj _ (conj Hn Hn'))).
    + eapply tmred_trans; [|exact Hr]. eapply tmred_along; [exact H1 | exact HT | solve [apply lequiv_sym; assumption]].
    + eapply tmred_trans; [|exact Hr']. apply (sempty_tmred_conv Hl2).
      eapply tmred_along; [exact H1' | exact HT' | eapply lequiv_trans; [exact Hl2 | solve [apply lequiv_sym; assumption]]].
  - (* Id: the right side at the left's type, as for sEq *)
    destruct Htt as (w & w' & Hr & Hr' & Heq & Hn). exists w, w'.
    refine (conj _ (conj _ (conj Heq Hn))).
    + eapply tmred_trans; [|exact Hr]. eapply tmred_along; [exact H1 | exact HT | solve [apply lequiv_sym; assumption]].
    + eapply tmred_trans; [|exact Hr']. eapply (tmred_lconv _ _ _ _ l); [|solve [apply lequiv_sym; assumption]].
      eapply tmred_conv; [apply ge_typeof | exact H1' |].
      eapply eqty_trans; [apply HT'|]. eapply eqty_lconv; [|exact Hl].
      apply eqty_sym, geq_ty_sound, geq_ty_id; auto using lequiv_sym.
  - (* Empty *)
    destruct Htt as (w & w' & Hr & Hr' & Hn). exists w, w'.
    refine (conj _ (conj _ Hn)).
    + eapply tmred_trans; [|exact Hr]. eapply tmred_along; [exact H1 | exact HT | solve [apply lequiv_sym; assumption]].
    + eapply tmred_trans; [|exact Hr']. apply (empty_tmred_conv Hl2).
      eapply tmred_along; [exact H1' | exact HT' | eapply lequiv_trans; [exact Hl2 | solve [apply lequiv_sym; assumption]]].
  - (* +: the right side at the left's type, as for Id *)
    destruct Htt as (w & w' & Hr & Hr' & Heq & Hn). exists w, w'.
    refine (conj _ (conj _ (conj Heq Hn))).
    + eapply tmred_trans; [|exact Hr]. eapply tmred_along; [exact H1 | exact HT | solve [apply lequiv_sym; assumption]].
    + eapply tmred_trans; [|exact Hr']. eapply (tmred_lconv _ _ _ _ l); [|solve [apply lequiv_sym; assumption]].
      eapply tmred_conv; [apply ge_typeof | exact H1' |].
      eapply eqty_trans; [apply HT'|]. eapply eqty_lconv; [|exact Hl].
      apply eqty_sym, geq_ty_sound, geq_ty_sum; auto using lequiv_sym.
  - (* W: the right side at the left's type, as for + *)
    destruct (WRel_inv Htt) as (w & w' & Hr & Hr' & Heq & Hn).
    econstructor; [| | exact Heq | exact Hn].
    + eapply tmred_trans; [|exact Hr]. eapply tmred_along; [exact H1 | exact HT | solve [apply lequiv_sym; assumption]].
    + eapply tmred_trans; [|exact Hr']. eapply (tmred_lconv _ _ _ _ l); [|solve [apply lequiv_sym; assumption]].
      eapply tmred_conv; [apply ge_typeof | exact H1' |].
      eapply eqty_trans; [apply HT'|]. eapply eqty_lconv; [|exact Hl].
      apply eqty_sym, geq_ty_sound, geq_ty_W; auto using lequiv_sym.
  - (* Wf: as W *)
    destruct (WfRel_inv Htt) as (w & w' & Hr & Hr' & Heq & Hn).
    econstructor; [| | exact Heq | exact Hn].
    + eapply tmred_trans; [|exact Hr]. eapply tmred_along; [exact H1 | exact HT | solve [apply lequiv_sym; assumption]].
    + eapply tmred_trans; [|exact Hr']. eapply (tmred_lconv _ _ _ _ l); [|solve [apply lequiv_sym; assumption]].
      eapply tmred_conv; [apply ge_typeof | exact H1' |].
      eapply eqty_trans; [apply HT'|]. eapply eqty_lconv; [|exact Hl].
      apply eqty_sym, geq_ty_sound, geq_ty_wf; auto using lequiv_sym.
  - (* ∥·∥: each side alone, the right one at the left's type *)
    destruct Htt as [(w & Hr & Hn) (w' & Hr' & Hn')]. split.
    + exists w. split; [| exact Hn].
      eapply tmred_trans; [|exact Hr]. eapply tmred_along; [exact H1 | exact HT | solve [apply lequiv_sym; assumption]].
    + exists w'. split; [| exact Hn'].
      eapply tmred_trans; [|exact Hr']. eapply (tmred_lconv _ _ _ _ l); [|solve [apply lequiv_sym; assumption]].
      eapply tmred_conv; [apply ge_typeof | exact H1' |].
      eapply eqty_trans; [apply HT'|]. eapply eqty_lconv; [|exact Hl].
      apply eqty_sym, geq_ty_sound, geq_ty_sq; auto using lequiv_sym.
  - (* IWf: as W *)
    destruct (IWfRel_inv Htt) as (w & w' & Hr & Hr' & Heq & Hn).
    econstructor; [| | exact Heq | exact Hn].
    + eapply tmred_trans; [|exact Hr]. eapply tmred_along; [exact H1 | exact HT | solve [apply lequiv_sym; assumption]].
    + eapply tmred_trans; [|exact Hr']. eapply (tmred_lconv _ _ _ _ l); [|solve [apply lequiv_sym; assumption]].
      eapply tmred_conv; [apply ge_typeof | exact H1' |].
      eapply eqty_trans; [apply HT'|]. eapply eqty_lconv; [|exact Hl].
      apply eqty_sym, geq_ty_sound, geq_ty_iwf; auto using lequiv_sym.
  - (* M: by [MRn_red] at every depth *)
    pose proof (MSide_of_LR Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HmX HmA HmB HmC HmXX HmAA HmBB HmCC
                  midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon) as HM.
    intros k. refine (MRn_red k (ms_geq HM) (Htt k) _ _).
    + eapply tmred_along; [exact H1 | exact HT | solve [apply lequiv_sym; assumption]].
    + eapply tmred_along; [exact H1' | exact HT' | solve [apply lequiv_sym; assumption]].
  - (* IWi: as IWf *)
    destruct (IWiRel_inv Htt) as (w & w' & Hr & Hr' & Heq & Hn).
    econstructor; [| | exact Heq | exact Hn].
    + eapply tmred_trans; [|exact Hr]. eapply tmred_along; [exact H1 | exact HT | solve [apply lequiv_sym; assumption]].
    + eapply tmred_trans; [|exact Hr']. eapply (tmred_lconv _ _ _ _ l); [|solve [apply lequiv_sym; assumption]].
      eapply tmred_conv; [apply ge_typeof | exact H1' |].
      eapply eqty_trans; [apply HT'|]. eapply eqty_lconv; [|exact Hl].
      apply eqty_sym, geq_ty_sound, geq_ty_iwi; auto using lequiv_sym.
Qed.

End Reduction.
