(** * Decidability of algorithmic conversion: indexed infinitary trees (M19b)

    One of the parts [AlgDec] puts together (see [AlgDecDef]), as
    [AlgDecIWf]'s cases with the domain: the right signature is moved into
    the left contexts once the index type and the shape are compared, its
    domain once the arities are, its children's indices once the domains
    are ([IWi_r_mv]); the right motive, induction hypothesis type and step
    once the signatures are ([IWi_*_left]). *)
From DeLaM.Validity Require Export AlgDecDef.

Lemma Dc_actnf_iwi {G Γ l lp li k kp ki X X0 A A0 N N0 D D0 Ot Ot0 C C0 m m0} :
  Dc_ty G Γ X X0 -> Dc_ty G Γ A A0 -> Dc_tm G (Γ ,, A @ l) N N0 tyNat ->
  Dc_ty G (Γ ,, A @ l ,, tyFin N @ lzero) D D0 ->
  Dc_tm G (Γ ,, A @ l) Ot Ot0 X⟨↑⟩ -> Dc_tm G (Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp) C C0 X⟨↑⟩⟨↑⟩⟨↑⟩ ->
  Dc_tm G Γ m m0 X ->
  Dc_tynf G Γ (tyIWi l lp li X A N D Ot C m) (tyIWi k kp ki X0 A0 N0 D0 Ot0 C0 m0).
Proof.
  intros IHX IHA IHN IHD IHO IHC IHm Y i q q' Hc HY HY'.
  pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  destruct Y; try solve [refute_con | refute].
  match goal with |- Dec (ac_tynf _ _ _ (tyIWi ?p1 ?p2 ?p3 ?p4 ?p5 ?p6 ?p7 ?p8 ?p9 ?p10)) =>
    rename p1 into l5, p2 into lp5, p3 into li5, p4 into X', p5 into A', p6 into N', p7 into D',
      p8 into Ot', p9 into C', p10 into m' end.
  destruct (inv_ty_iwi HY) as ((_ & W1 & W2 & W3 & HX & HA & HN & HD & HO & HC & Hm) & _).
  destruct (inv_ty_iwi HY') as ((_ & W4 & W5 & W6 & HX' & HA' & HN' & HD' & HO' & HC' & Hm') & _).
  destruct (leqv_dec l l5) as [H1 | Hneg]; [| refute].
  destruct (leqv_dec lp lp5) as [H2 | Hneg]; [| refute].
  destruct (leqv_dec li li5) as [H3 | Hneg]; [| refute].
  pose proof (leqv_lequiv _ _ _ W1 W4 H1) as E1. pose proof (leqv_lequiv _ _ _ W2 W5 H2) as E2.
  pose proof (leqv_lequiv _ _ _ W3 W6 H3) as E3.
  assert (HS : IWiSig (G := G) (i := i) Γ l lp li X A N D Ot C) by (unfold IWiSig; auto 10).
  assert (HS' : IWiSig (G := G) (i := i) Γ l5 lp5 li5 X' A' N' D' Ot' C') by (unfold IWiSig; auto 10).
  destruct (IHX X' i _ _ Hc HX HX') as [DX | Hneg]; [| refute].
  destruct (IHA A' i _ _ Hc HA HA') as [DA | Hneg]; [| refute].
  pose proof (ac_ty_sound Hc DX HX (wft_lconv _ _ _ _ _ _ HX' E3)) as EX.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E1)) as EA.
  destruct (IWi_r_mv Hi Hv HS HS' E1 E2 E3 EX EA) as (_ & _ & HN'l & HO'l & HDC).
  destruct (IHN N' i lzero Hc HN HN'l) as [DN | Hneg]; [| refute].
  pose proof (ac_tm_sound Hc DN HN HN'l) as EN.
  destruct (HDC EN) as (HD'l & HC'l).
  destruct (IHD D' i lp lp Hc HD HD'l) as [DD | Hneg]; [| refute].
  pose proof (ac_ty_sound Hc DD HD HD'l) as ED.
  destruct (IHO Ot' i li Hc HO HO'l) as [DO | Hneg]; [| refute].
  destruct (IHC C' i li Hc HC (HC'l ED)) as [DC | Hneg]; [| refute].
  assert (Hm'l : [ G ; Γ ⊢[ i ] m' : X @ li ])
    by (eapply (conv_tm' Hi); [eapply wf_lconv; [exact Hm' | exact E3] | exact EX]).
  destruct (IHm m' i li Hc Hm Hm'l) as [Dm | Hneg]; [left; apply actnf_iwi; assumption | refute].
Qed.

Lemma Dc_actmnf_supii {G Γ l lp li X A N D Ot C m k kp ki X1 A1 N1 D1 O1 C1 k0 kp0 ki0 X0 A0 N0 D0 O0 C0
    a a0 cs cs0} :
  Dc_tm G Γ a a0 A -> Dc_tm G Γ cs cs0 (tyDVec (iwiL l lp li) N[lsingle a] (iwiFam l lp li X A N D Ot C a)) ->
  Dc_tmnf G Γ (tmSupii k kp ki X1 A1 N1 D1 O1 C1 a cs) (tmSupii k0 kp0 ki0 X0 A0 N0 D0 O0 C0 a0 cs0)
    (tyIWi l lp li X A N D Ot C m).
Proof.
  intros IHa IHcs x i q Hc Hw Hx.
  pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  destruct x; try solve [refute_con | refute].
  match goal with |- Dec (ac_tmnf _ _ _ (tmSupii _ _ _ _ _ _ _ _ _ ?e ?g) _) => rename e into a', g into cs' end.
  destruct (supii_parts Hc Hw) as (HS & _ & Ha & Hcs & _ & _).
  destruct (supii_parts Hc Hx) as (_ & _ & Ha' & Hcs'0 & _ & _).
  destruct (IHa a' i l Hc Ha Ha') as [Da | Hneg]; [| refute].
  pose proof (ac_tm_sound Hc Da Ha Ha') as Ea.
  assert (Hcs' : [ G ; Γ ⊢[ i ] cs' : tyDVec (iwiL l lp li) N[lsingle a] (iwiFam l lp li X A N D Ot C a)
                   @ iwiL l lp li ])
    by (eapply (conv_tm' Hi); [exact Hcs'0 | exact (IWi_csa_eq Hi Hv (IWiEq_refl HS) Ha Ha' Ea)]).
  destruct (IHcs cs' i _ Hc Hcs Hcs') as [Dcs | Hneg]; [left; apply actmnf_supii; assumption | refute].
Qed.

Lemma Dc_actmne_elimIWi {G Γ l lp li l' k kp ki k' X X0 A A0 N N0 D D0 Ot Ot0 C C0 M M0 c c0 m m0 ν ν0 W} :
  Dc_ty G (Γ ,, X @ li ,, iwimotty l lp li X A N D Ot C @ iwiL l lp li) M M0 ->
  Dc_tm G (Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ,,
             iwiihty l lp li l' X A N D Ot C M @ lmax lzero (lmax lp l'))
    c c0 (iwistepty l lp li X A N D Ot C M) ->
  ac_tmnee G Γ ν ν0 W -> Dc_nee G Γ ν ν0 W ->
  Dc_ne G Γ (tmElimIWi l lp li l' X A N D Ot C M c m ν) (tmElimIWi k kp ki k' X0 A0 N0 D0 Ot0 C0 M0 c0 m0 ν0)
    M[lsingle2 m ν].
Proof.
  intros IHM IHc Dν0 IHν x i q q' T T' Hc Hx Hx'.
  pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmne _ _ _ (tmElimIWi ?p1 ?p2 ?p3 ?p4 ?p5 ?p6 ?p7 ?p8 ?p9 ?p10 ?p11 ?p12 ?p13 ?p14) _) =>
    rename p1 into l5, p2 into lp5, p3 into li5, p4 into l5', p5 into X', p6 into A', p7 into N', p8 into D',
      p9 into Ot', p10 into C', p11 into M', p12 into c', p13 into m', p14 into ν' end.
  destruct (inv_elimIWi Hi Hx)
    as ((_ & W3 & W1 & W2 & W4 & HX & HA & HN & HD & HO & HC & _ & HM & _ & HI & Hc0 & Hm & Hν) & _ & _).
  destruct (inv_elimIWi Hi Hx')
    as ((_ & W3' & W1' & W2' & W4' & HX' & HA' & HN' & HD' & HO' & HC' & _ & HM' & _ & HI' & Hc0' & Hm' & Hν')
        & _ & _).
  destruct (IHν ν' i _ _ _ _ Hc Hν Hν') as [Dν | Hneg];
    [| right; intros D2; destruct (ainv_elimIWi D2)
         as (k2 & kp2 & ki2 & k2' & X2 & A2 & N2 & D2' & O2 & C2 & M2 & c2 & m2 & ν2 & W0 & E
             & _ & _ & _ & Dν2);
       injection E as <- <- <- <- <- <- <- <- <- <- <- <- <- <-;
       rewrite <- (ac_nee_uniq Dν0 Dν2) in Dν2; exact (Hneg Dν2)].
  assert (HS : IWiSig (G := G) (i := i) Γ l lp li X A N D Ot C) by (unfold IWiSig; auto 10).
  (* the signatures, through the scrutinees' types *)
  destruct (ac_nee_sound' Dν Hc Hν Hν') as (F0 & F1 & _).
  destruct (IWi_annots Hi Hc HS F0 F1) as (HE0 & _).
  destruct (leqv_dec l' l5') as [H3 | Hneg]; [| refute].
  pose proof (leqv_lequiv _ _ _ W3 W3' H3) as E3.
  pose proof (IWi_mot_left Hi Hv HE0 E3 HM') as HM'l.
  destruct (IHM M' i l' l' Hc HM HM'l) as [DM | Hneg]; [| refute].
  pose proof (ac_ty_sound Hc DM HM HM'l) as EM.
  pose proof (IWi_ih_left Hi Hv HE0 E3 HI') as HI'l.
  pose proof (IWi_ihty_eq Hc HE0 E3 EM HI HI'l) as EI.
  pose proof (IWi_step_left Hi Hv HE0 E3 HM EM HI HI' EI Hc0') as Hc0'l.
  destruct (IHc c' i l' Hc Hc0 Hc0'l) as [Dc | Hneg]; [left; eapply actmne_elimIWi; eassumption | refute].
Qed.
