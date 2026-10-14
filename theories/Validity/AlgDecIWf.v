(** * Decidability of algorithmic conversion: indexed finitary trees (M17b)

    One of the parts [AlgDec] puts together (see [AlgDecDef]). As [AlgDecW]'s
    [Wf] cases: the right signature is moved into the left contexts once the
    index type and the shape are compared ([IWf_r_mv]), the right motive,
    induction hypothesis type and step once the signatures are ([IWf_*_left]). *)
From DeLaM.Validity Require Export AlgDecDef.

Lemma Dc_actnf_iwf {G Γ l li k ki X X0 A A0 N N0 Ot Ot0 C C0 m m0} :
  Dc_ty G Γ X X0 -> Dc_ty G Γ A A0 -> Dc_tm G (Γ ,, A @ l) N N0 tyNat ->
  Dc_tm G (Γ ,, A @ l) Ot Ot0 X⟨↑⟩ -> Dc_tm G (Γ ,, A @ l ,, tyFin N @ lzero) C C0 X⟨↑⟩⟨↑⟩ ->
  Dc_tm G Γ m m0 X ->
  Dc_tynf G Γ (tyIWf l li X A N Ot C m) (tyIWf k ki X0 A0 N0 Ot0 C0 m0).
Proof.
  intros IHX IHA IHN IHO IHC IHm Y i q q' Hc HY HY'.
  pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV Hc) as Hv.
  destruct Y; try solve [refute_con | refute].
  match goal with |- Dec (ac_tynf _ _ _ (tyIWf ?p1 ?p2 ?p3 ?p4 ?p5 ?p6 ?p7 ?p8)) =>
    rename p1 into l5, p2 into li5, p3 into X', p4 into A', p5 into N', p6 into Ot', p7 into C', p8 into m' end.
  destruct (inv_ty_iwf HY) as ((_ & W1 & W2 & HX & HA & HN & HO & HC & Hm) & _).
  destruct (inv_ty_iwf HY') as ((_ & W3 & W4 & HX' & HA' & HN' & HO' & HC' & Hm') & _).
  destruct (leqv_dec l l5) as [H1 | Hneg]; [| refute].
  destruct (leqv_dec li li5) as [H2 | Hneg]; [| refute].
  pose proof (leqv_lequiv _ _ _ W1 W3 H1) as E1. pose proof (leqv_lequiv _ _ _ W2 W4 H2) as E2.
  assert (HS : IWfSig (G := G) (i := i) Γ l li X A N Ot C) by (unfold IWfSig; auto 8).
  assert (HS' : IWfSig (G := G) (i := i) Γ l5 li5 X' A' N' Ot' C') by (unfold IWfSig; auto 8).
  destruct (IHX X' i _ _ Hc HX HX') as [DX | Hneg]; [| refute].
  destruct (IHA A' i _ _ Hc HA HA') as [DA | Hneg]; [| refute].
  pose proof (ac_ty_sound Hc DX HX (wft_lconv _ _ _ _ _ _ HX' E2)) as EX.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E1)) as EA.
  destruct (IWf_r_mv Hi Hv HS HS' E1 E2 EX EA) as (_ & _ & HN'l & HO'l & HC'l).
  destruct (IHN N' i lzero Hc HN HN'l) as [DN | Hneg]; [| refute].
  pose proof (ac_tm_sound Hc DN HN HN'l) as EN.
  destruct (IHO Ot' i li Hc HO HO'l) as [DO | Hneg]; [| refute].
  destruct (IHC C' i li Hc HC (HC'l EN)) as [DC | Hneg]; [| refute].
  assert (Hm'l : [ G ; Γ ⊢[ i ] m' : X @ li ])
    by (eapply (conv_tm' Hi); [eapply wf_lconv; [exact Hm' | exact E2] | exact EX]).
  destruct (IHm m' i li Hc Hm Hm'l) as [Dm | Hneg]; [left; apply actnf_iwf; assumption | refute].
Qed.

Lemma Dc_actmnf_supi {G Γ l li X A N Ot C m k ki X1 A1 N1 O1 C1 k0 ki0 X0 A0 N0 O0 C0 a a0 cs cs0} :
  Dc_tm G Γ a a0 A -> Dc_tm G Γ cs cs0 (tyDVec (lmax l li) N[lsingle a] (iwfFam l li X A N Ot C a)) ->
  Dc_tmnf G Γ (tmSupi k ki X1 A1 N1 O1 C1 a cs) (tmSupi k0 ki0 X0 A0 N0 O0 C0 a0 cs0)
    (tyIWf l li X A N Ot C m).
Proof.
  intros IHa IHcs x i q Hc Hw Hx.
  pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV Hc) as Hv.
  destruct x; try solve [refute_con | refute].
  match goal with |- Dec (ac_tmnf _ _ _ (tmSupi _ _ _ _ _ _ _ ?e ?g) _) => rename e into a', g into cs' end.
  destruct (supi_parts Hc Hw) as (HS & _ & Ha & Hcs & _ & _).
  destruct (supi_parts Hc Hx) as (_ & _ & Ha' & Hcs'0 & _ & _).
  destruct (IHa a' i l Hc Ha Ha') as [Da | Hneg]; [| refute].
  pose proof (ac_tm_sound Hc Da Ha Ha') as Ea.
  assert (Hcs' : [ G ; Γ ⊢[ i ] cs' : tyDVec (lmax l li) N[lsingle a] (iwfFam l li X A N Ot C a) @ lmax l li ])
    by (eapply (conv_tm' Hi); [exact Hcs'0 | exact (IWf_csa_eq Hi Hv (IWfEq_refl HS) Ha Ha' Ea)]).
  destruct (IHcs cs' i _ Hc Hcs Hcs') as [Dcs | Hneg]; [left; apply actmnf_supi; assumption | refute].
Qed.

Lemma Dc_actmne_elimIWf {G Γ l li l' k ki k' X X0 A A0 N N0 Ot Ot0 C C0 M M0 c c0 m m0 ν ν0 W} :
  Dc_ty G Γ X X0 -> Dc_ty G Γ A A0 -> Dc_tm G (Γ ,, A @ l) N N0 tyNat ->
  Dc_tm G (Γ ,, A @ l) Ot Ot0 X⟨↑⟩ -> Dc_tm G (Γ ,, A @ l ,, tyFin N @ lzero) C C0 X⟨↑⟩⟨↑⟩ ->
  Dc_ty G (Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li) M M0 ->
  Dc_ty G (Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li)
    (iwfihty l li l' X A N Ot C M) (iwfihty k ki k' X0 A0 N0 Ot0 C0 M0) ->
  Dc_tm G (Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ,, iwfihty l li l' X A N Ot C M @ lmax lzero l')
    c c0 (iwfstepty l li X A N Ot C M) ->
  Dc_tm G Γ m m0 X ->
  ac_tmnee G Γ ν ν0 W -> Dc_nee G Γ ν ν0 W ->
  Dc_ne G Γ (tmElimIWf l li l' X A N Ot C M c m ν) (tmElimIWf k ki k' X0 A0 N0 Ot0 C0 M0 c0 m0 ν0)
    M[lsingle2 m ν].
Proof.
  intros IHX IHA IHN IHO IHC IHM IHI IHc IHm Dν0 IHν x i q q' T T' Hc Hx Hx'.
  pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV Hc) as Hv.
  destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmne _ _ _ (tmElimIWf ?p1 ?p2 ?p3 ?p4 ?p5 ?p6 ?p7 ?p8 ?p9 ?p10 ?p11 ?p12) _) =>
    rename p1 into l5, p2 into li5, p3 into l5', p4 into X', p5 into A', p6 into N', p7 into Ot',
      p8 into C', p9 into M', p10 into c', p11 into m', p12 into ν' end.
  destruct (inv_elimIWf Hi Hx)
    as ((_ & W3 & W1 & W2 & HX & HA & HN & HO & HC & _ & HM & _ & HI & Hc0 & Hm & Hν) & _ & _).
  destruct (inv_elimIWf Hi Hx')
    as ((_ & W3' & W1' & W2' & HX' & HA' & HN' & HO' & HC' & _ & HM' & _ & HI' & Hc0' & Hm' & Hν') & _ & _).
  destruct (IHν ν' i _ _ _ _ Hc Hν Hν') as [Dν | Hneg];
    [| right; intros D; destruct (ainv_elimIWf D)
         as (k2 & ki2 & k2' & X2 & A2 & N2 & O2 & C2 & M2 & c2 & m2 & ν2 & W0 & E
             & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Dν2);
       injection E as <- <- <- <- <- <- <- <- <- <- <- <-;
       rewrite <- (ac_nee_uniq Dν0 Dν2) in Dν2; exact (Hneg Dν2)].
  destruct (leqv_dec l l5) as [H1 | Hneg]; [| refute].
  destruct (leqv_dec li li5) as [H2 | Hneg]; [| refute].
  destruct (leqv_dec l' l5') as [H3 | Hneg]; [| refute].
  pose proof (leqv_lequiv _ _ _ W1 W1' H1) as E1. pose proof (leqv_lequiv _ _ _ W2 W2' H2) as E2.
  pose proof (leqv_lequiv _ _ _ W3 W3' H3) as E3.
  assert (HS : IWfSig (G := G) (i := i) Γ l li X A N Ot C) by (unfold IWfSig; auto 8).
  assert (HS' : IWfSig (G := G) (i := i) Γ l5 li5 X' A' N' Ot' C') by (unfold IWfSig; auto 8).
  destruct (IHX X' i _ _ Hc HX HX') as [DX | Hneg]; [| refute].
  destruct (IHA A' i _ _ Hc HA HA') as [DA | Hneg]; [| refute].
  pose proof (ac_ty_sound Hc DX HX (wft_lconv _ _ _ _ _ _ HX' E2)) as EX.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E1)) as EA.
  destruct (IWf_r_mv Hi Hv HS HS' E1 E2 EX EA) as (_ & _ & HN'l & HO'l & HC'l).
  destruct (IHN N' i lzero Hc HN HN'l) as [DN | Hneg]; [| refute].
  pose proof (ac_tm_sound Hc DN HN HN'l) as EN.
  destruct (IHO Ot' i li Hc HO HO'l) as [DO | Hneg]; [| refute].
  pose proof (ac_tm_sound Hc DO HO HO'l) as EO.
  destruct (IHC C' i li Hc HC (HC'l EN)) as [DC | Hneg]; [| refute].
  pose proof (ac_tm_sound Hc DC HC (HC'l EN)) as EC.
  pose proof (IWfEq_of_eqs Hi HS E1 E2 EX EA EN EO EC) as HE0.
  pose proof (IWf_mot_left Hi Hv HE0 E3 HM') as HM'l.
  destruct (IHM M' i l' l' Hc HM HM'l) as [DM | Hneg]; [| refute].
  pose proof (ac_ty_sound Hc DM HM HM'l) as EM.
  pose proof (IWf_ih_left Hi Hv HE0 E3 HI') as HI'l.
  destruct (IHI _ i _ _ Hc HI HI'l) as [DI | Hneg]; [| refute].
  pose proof (ac_ty_sound Hc DI HI HI'l) as EI.
  pose proof (IWf_step_left Hi Hv HE0 E3 HM EM HI HI' EI Hc0') as Hc0'l.
  destruct (IHc c' i l' Hc Hc0 Hc0'l) as [Dc | Hneg]; [| refute].
  assert (Hm'l : [ G ; Γ ⊢[ i ] m' : X @ li ])
    by (eapply (conv_tm' Hi); [eapply wf_lconv; [exact Hm' | exact E2] | exact EX]).
  destruct (IHm m' i li Hc Hm Hm'l) as [Dm | Hneg]; [left; eapply actmne_elimIWf; eassumption | refute].
Qed.
