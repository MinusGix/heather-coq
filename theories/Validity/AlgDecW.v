(** * Decidability of algorithmic conversion: W, Wf, sums and the projections

    One of the parts [AlgDec] puts together (see [AlgDecDef]). *)
From DeLaM.Validity Require Export AlgDecDef.

(** Well-founded trees (M13a). *)
Lemma Dc_actnf_W {G Γ l1 l2 l3 l4 A A0 B B0} :
  Dc_ty G Γ A A0 -> Dc_ty G (Γ ,, A @ l1) B B0 -> Dc_tynf G Γ (tyW l1 l2 A B) (tyW l3 l4 A0 B0).
Proof.
  intros IHA IHB X i k k' Hc HX HX'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct X; try solve [refute_con | refute].
  match goal with |- Dec (ac_tynf _ _ _ (tyW ?a ?b ?c ?d)) =>
    rename a into l5, b into l6, c into A', d into B' end.
  destruct (inv_ty_W HX) as ((Hv & W1 & W2 & HA & HB) & _).
  destruct (inv_ty_W HX') as ((_ & W5 & W6 & HA' & HB') & _).
  destruct (leqv_dec l1 l5) as [H15 | N]; [| refute]. destruct (leqv_dec l2 l6) as [H26 | N]; [| refute].
  destruct (IHA A' i _ _ Hc HA HA') as [DA | N]; [| refute].
  pose proof (leqv_lequiv _ _ _ W1 W5 H15) as E15.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E15)) as EA.
  pose proof (ctx_of_wf_ty Hi HA) as HΓ.
  assert (HΓA : [ G ; Γ ,, A @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HA | exact W1]).
  assert (EA' : [ G ; Γ ⊢[ i ] A' ≅ A @ l5 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E15)]).
  pose proof (stab_ty Hi EA' (lequiv_sym _ _ _ E15) HΓA HB') as HB1.
  destruct (IHB B' i _ _ Hc HB HB1) as [DB | N]; [left; apply actnf_W; assumption | refute].
Qed.

Lemma Dc_actmnf_sup {G Γ l l' A B k1 k2 k3 k4 C D C0 D0 a a0 f f0} :
  Dc_tm G Γ a a0 A -> Dc_tm G Γ f f0 (tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩) ->
  Dc_tmnf G Γ (tmSup k1 k2 C D a f) (tmSup k3 k4 C0 D0 a0 f0) (tyW l l' A B).
Proof.
  intros IHa IHf x i m Hc Hw Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute_con | refute].
  match goal with |- Dec (ac_tmnf _ _ _ (tmSup _ _ _ _ ?e ?g) _) => rename e into a', g into f' end.
  destruct (sup_parts Hc Hw) as (Wl & Wl' & HA & HB & Ha & Hf).
  destruct (sup_parts Hc Hx) as (_ & _ & _ & _ & Ha' & Hf').
  destruct (IHa a' i l Hc Ha Ha') as [Da | N]; [| refute].
  pose proof (fty_conv Hc Wl Wl' HA HB Ha' Ha (ac_tm_sound Hc Da Ha Ha')) as EF.
  assert (Hf'1 : [ G ; Γ ⊢[ i ] f' : tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩ @ lmax l' (lmax l l') ])
    by (eapply wf_conv; [exact Hf' | rewrite Hi; exact EF]).
  destruct (IHf f' i _ Hc Hf Hf'1) as [Df | N]; [left; apply actmnf_sup; assumption | refute].
Qed.

Lemma Dc_actmne_elimW {G Γ l1 l2 l3 l4 l5 l6 A A0 B B0 M M0 c c0 ν ν0 W} :
  Dc_ty G (Γ ,, tyW l1 l2 A B @ lmax l1 l2) M M0 ->
  Dc_tm G (Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, wihty l1 l2 l3 A B M @ lmax l2 l3)
    c c0 (wstepty l1 l2 A B M) ->
  ac_tmnee G Γ ν ν0 W -> Dc_nee G Γ ν ν0 W ->
  Dc_ne G Γ (tmElimW l1 l2 l3 A B M c ν) (tmElimW l4 l5 l6 A0 B0 M0 c0 ν0) M[lsingle ν].
Proof.
  intros IHM IHc Dν0 IHν x i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmne _ _ _ (tmElimW ?p1 ?p2 ?p3 ?p4 ?p5 ?p6 ?p7 ?p8) _) =>
    rename p1 into l7, p2 into l8, p3 into l9, p4 into A', p5 into B', p6 into M', p7 into c', p8 into ν' end.
  destruct (inv_elimW Hi Hx) as ((_ & W1 & W2 & W3 & HA & HB & HM & HF & HI & Hc0 & Hν) & _ & _).
  destruct (inv_elimW Hi Hx') as ((_ & W7 & W8 & W9 & HA' & HB' & HM' & HF' & HI' & Hc0' & Hν') & _ & _).
  destruct (IHν ν' i _ _ _ _ Hc Hν Hν') as [Dν | N];
    [| right; intros D; destruct (ainv_elimW D) as (l10 & l11 & l12 & A2 & B2 & M2 & c2 & ν2 & W0 & E
                                                    & _ & _ & _ & Dν2);
       injection E as <- <- <- <- <- <- <- <-; rewrite <- (ac_nee_uniq Dν0 Dν2) in Dν2; exact (N Dν2)].
  (* the shapes and the positions, through the scrutinees' types *)
  destruct (ac_nee_sound' Dν Hc Hν Hν') as (E0 & E1 & _).
  destruct (W_annots Hi Hc W1 W2 E0 E1) as (E17 & E28 & EA & EB).
  destruct (leqv_dec l3 l9) as [H39 | N]; [| refute].
  pose proof (leqv_lequiv _ _ _ W3 W9 H39) as E39.
  pose proof (ext_wf Hi HA W1) as HΓA.
  assert (EA7 : [ G ; Γ ⊢[ i ] A' ≅ A @ l7 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E17)]).
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty Hi EA7 (lequiv_sym _ _ _ E17) HΓA HB') E28) as HB'A.
  assert (WL : lwf (gL G) (lmax l1 l2)) by (cbn; split; assumption).
  assert (HL : lequiv (gL G) (lmax l7 l8) (lmax l1 l2)) by (apply lequiv_max; solve [apply lequiv_sym; assumption]).
  assert (HW : [ G ; Γ ⊢[ i ] tyW l1 l2 A B @ lmax l1 l2 ]) by (apply wft_W; first [assumption | (apply compt_notV; eassumption)]).
  assert (EW' : [ G ; Γ ⊢[ i ] tyW l7 l8 A' B' ≅ tyW l1 l2 A B @ lmax l7 l8 ]).
  { eapply eqty_lconv; [apply eqty_sym, eqty_W; first [assumption | (apply compt_notV; eassumption)] | exact HL]. }
  pose proof (ext_wf Hi HW WL) as HΓW.
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty Hi EW' HL HΓW HM') E39) as HM'3.
  destruct (IHM M' i _ _ Hc HM HM'3) as [DM | N]; [| refute].
  pose proof (ac_ty_sound Hc DM HM HM'3) as EM.
  pose proof (elimW_step_left Hc E17 E28 E39 HA HA' EA HB HB' EB HM HM' EM HF HI Hc0') as Hc0'2.
  destruct (IHc c' i l3 Hc Hc0 Hc0'2) as [Dc | N]; [left; eapply actmne_elimW; eassumption | refute].
Qed.

(** Finitary well-founded trees (M15a). *)
Lemma Dc_actnf_wf {G Γ l1 l3 A A0 N N0} :
  Dc_ty G Γ A A0 -> Dc_tm G (Γ ,, A @ l1) N N0 tyNat -> Dc_tynf G Γ (tyWf l1 A N) (tyWf l3 A0 N0).
Proof.
  intros IHA IHN X i k k' Hc HX HX'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct X; try solve [refute_con | refute].
  match goal with |- Dec (ac_tynf _ _ _ (tyWf ?a ?b ?c)) => rename a into l5, b into A', c into N' end.
  destruct (inv_ty_wf HX) as ((_ & W1 & HA & HN) & _).
  destruct (inv_ty_wf HX') as ((_ & W5 & HA' & HN') & _).
  destruct (leqv_dec l1 l5) as [H15 | Hneg]; [| refute].
  destruct (IHA A' i _ _ Hc HA HA') as [DA | Hneg]; [| refute].
  pose proof (leqv_lequiv _ _ _ W1 W5 H15) as E15.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E15)) as EA.
  pose proof (ext_wf Hi HA W1) as HΓA.
  assert (EA' : [ G ; Γ ⊢[ i ] A' ≅ A @ l5 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E15)]).
  pose proof (stab_tm Hi EA' (lequiv_sym _ _ _ E15) HΓA HN') as HN1.
  destruct (IHN N' i lzero Hc HN HN1) as [DN | Hneg]; [left; apply actnf_wf; assumption | refute].
Qed.

Lemma Dc_actmnf_supf {G Γ l A N k k0 C D C0 D0 a a0 cs cs0} :
  Dc_tm G Γ a a0 A -> Dc_tm G Γ cs cs0 (tyVec l (tyWf l A N) N[lsingle a]) ->
  Dc_tmnf G Γ (tmSupf k C D a cs) (tmSupf k0 C0 D0 a0 cs0) (tyWf l A N).
Proof.
  intros IHa IHcs x i m Hc Hw Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute_con | refute].
  match goal with |- Dec (ac_tmnf _ _ _ (tmSupf _ _ _ ?e ?g) _) => rename e into a', g into cs' end.
  destruct (supf_parts Hc Hw) as (Wl & HA & HN & Ha & Hcs).
  destruct (supf_parts Hc Hx) as (_ & _ & _ & Ha' & Hcs').
  destruct (IHa a' i l Hc Ha Ha') as [Da | Hneg]; [| refute].
  pose proof (wf_cs_conv Hc Wl HA HN Ha Ha' (ac_tm_sound Hc Da Ha Ha')) as EC.
  assert (Hcs'1 : [ G ; Γ ⊢[ i ] cs' : tyVec l (tyWf l A N) N[lsingle a] @ l ])
    by (eapply wf_conv; [exact Hcs' | rewrite Hi; exact EC]).
  destruct (IHcs cs' i _ Hc Hcs Hcs'1) as [Dcs | Hneg]; [left; apply actmnf_supf; assumption | refute].
Qed.

Lemma Dc_actmne_elimWf {G Γ l1 l2 l3 l4 A A0 N N0 M M0 c c0 ν ν0 W} :
  Dc_ty G (Γ ,, tyWf l1 A N @ l1) M M0 ->
  Dc_tm G (Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ,, wfihty l1 l2 A N M @ lmax lzero l2)
    c c0 (wfstepty l1 A N M) ->
  ac_tmnee G Γ ν ν0 W -> Dc_nee G Γ ν ν0 W ->
  Dc_ne G Γ (tmElimWf l1 l2 A N M c ν) (tmElimWf l3 l4 A0 N0 M0 c0 ν0) M[lsingle ν].
Proof.
  intros IHM IHc Dν0 IHν x i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmne _ _ _ (tmElimWf ?p1 ?p2 ?p3 ?p4 ?p5 ?p6 ?p7) _) =>
    rename p1 into l5, p2 into l6, p3 into A', p4 into N', p5 into M', p6 into c', p7 into ν' end.
  destruct (inv_elimWf Hi Hx) as ((_ & W1 & W2 & HA & HN & HM & HC & HI & Hc0 & Hν) & _ & _).
  destruct (inv_elimWf Hi Hx') as ((_ & W5 & W6 & HA' & HN' & HM' & HC' & HI' & Hc0' & Hν') & _ & _).
  destruct (IHν ν' i _ _ _ _ Hc Hν Hν') as [Dν | Hneg];
    [| right; intros D; destruct (ainv_elimWf D) as (l7 & l8 & A2 & N2 & M2 & c2 & ν2 & W0 & E
                                                     & _ & _ & _ & Dν2);
       injection E as <- <- <- <- <- <- <-; rewrite <- (ac_nee_uniq Dν0 Dν2) in Dν2; exact (Hneg Dν2)].
  (* the shapes and the arities, through the scrutinees' types *)
  destruct (ac_nee_sound' Dν Hc Hν Hν') as (E0 & E1 & _).
  destruct (Wf_annots Hi Hc W1 E0 E1) as (E15 & EA & EN).
  destruct (leqv_dec l2 l6) as [H26 | Hneg]; [| refute].
  pose proof (leqv_lequiv _ _ _ W2 W6 H26) as E26.
  pose proof (ext_wf Hi HA W1) as HΓA.
  assert (EA5 : [ G ; Γ ⊢[ i ] A' ≅ A @ l5 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E15)]).
  pose proof (stab_tm Hi EA5 (lequiv_sym _ _ _ E15) HΓA HN') as HN'A.
  assert (HW : [ G ; Γ ⊢[ i ] tyWf l1 A N @ l1 ]) by (apply wft_wf; first [(apply compt_notV; exact Hc) | assumption]).
  assert (EW' : [ G ; Γ ⊢[ i ] tyWf l5 A' N' ≅ tyWf l1 A N @ l5 ]).
  { eapply eqty_lconv; [apply eqty_sym, eqty_wf; first [(apply compt_notV; exact Hc) | assumption] | exact (lequiv_sym _ _ _ E15)]. }
  pose proof (ext_wf Hi HW W1) as HΓW.
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty Hi EW' (lequiv_sym _ _ _ E15) HΓW HM') E26) as HM'3.
  destruct (IHM M' i _ _ Hc HM HM'3) as [DM | Hneg]; [| refute].
  pose proof (ac_ty_sound Hc DM HM HM'3) as EM.
  pose proof (elimWf_step_left Hc E15 E26 HA HA' EA HN HN' EN HM HM' EM HI Hc0') as Hc0'2.
  destruct (IHc c' i l2 Hc Hc0 Hc0'2) as [Dc | Hneg]; [left; eapply actmne_elimWf; eassumption | refute].
Qed.

(** Binary sums (M12b). *)
Lemma Dc_actnf_sum {G Γ l1 l2 l3 l4 A A0 B B0} :
  Dc_ty G Γ A A0 -> Dc_ty G Γ B B0 -> Dc_tynf G Γ (tySum l1 l2 A B) (tySum l3 l4 A0 B0).
Proof.
  intros IHA IHB X i k k' Hc HX HX'.
  destruct X; try solve [refute_con | refute].
  match goal with |- Dec (ac_tynf _ _ _ (tySum ?a ?b ?c ?d)) =>
    rename a into l5, b into l6, c into A', d into B' end.
  destruct (inv_ty_sum HX) as ((_ & W1 & W2 & HA & HB) & _).
  destruct (inv_ty_sum HX') as ((_ & W5 & W6 & HA' & HB') & _).
  destruct (leqv_dec l1 l5) as [H15 | N]; [| refute]. destruct (leqv_dec l2 l6) as [H26 | N]; [| refute].
  destruct (IHA A' i _ _ Hc HA HA') as [DA | N]; [| refute].
  destruct (IHB B' i _ _ Hc HB HB') as [DB | N]; [left; apply actnf_sum; assumption | refute].
Qed.

Lemma Dc_actmnf_inl {G Γ l l' A B k1 k2 k3 k4 C D C0 D0 a a0} :
  Dc_tm G Γ a a0 A -> Dc_tmnf G Γ (tmInl k1 k2 C D a) (tmInl k3 k4 C0 D0 a0) (tySum l l' A B).
Proof.
  intros IHa x i m Hc Hw Hx.
  destruct x; try solve [refute_con | refute].
  match goal with |- Dec (ac_tmnf _ _ _ (tmInl _ _ _ _ ?e) _) => rename e into a' end.
  destruct (IHa a' i l Hc (inl_payload Hc Hw) (inl_payload Hc Hx)) as [Da | N];
    [left; apply actmnf_inl; exact Da | refute].
Qed.
Lemma Dc_actmnf_inr {G Γ l l' A B k1 k2 k3 k4 C D C0 D0 b b0} :
  Dc_tm G Γ b b0 B -> Dc_tmnf G Γ (tmInr k1 k2 C D b) (tmInr k3 k4 C0 D0 b0) (tySum l l' A B).
Proof.
  intros IHb x i m Hc Hw Hx.
  destruct x; try solve [refute_con | refute].
  match goal with |- Dec (ac_tmnf _ _ _ (tmInr _ _ _ _ ?e) _) => rename e into b' end.
  destruct (IHb b' i l' Hc (inr_payload Hc Hw) (inr_payload Hc Hx)) as [Db | N];
    [left; apply actmnf_inr; exact Db | refute].
Qed.

Lemma Dc_actmne_case {G Γ l1 l2 l3 l4 l5 l6 A A0 B B0 M M0 c1 c10 c2 c20 ν ν0 W} :
  Dc_ty G (Γ ,, tySum l1 l2 A B @ lmax l1 l2) M M0 ->
  Dc_tm G (Γ ,, A @ l1) c1 c10 M⟨rlift ↑⟩[lsingle (tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] -> Dc_tm G (Γ ,, B @ l2) c2 c20 M⟨rlift ↑⟩[lsingle (tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] ->
  ac_tmnee G Γ ν ν0 W -> Dc_nee G Γ ν ν0 W ->
  Dc_ne G Γ (tmCase l1 l2 l3 A B M c1 c2 ν) (tmCase l4 l5 l6 A0 B0 M0 c10 c20 ν0) M[lsingle ν].
Proof.
  intros IHM IHc1 IHc2 Dν0 IHν x i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmne _ _ _ (tmCase ?p1 ?p2 ?p3 ?p4 ?p5 ?p6 ?p7 ?p8 ?p9) _) =>
    rename p1 into l7, p2 into l8, p3 into l9, p4 into A', p5 into B', p6 into M', p7 into c1', p8 into c2',
      p9 into ν' end.
  destruct (inv_case Hi Hx) as ((_ & W1 & W2 & W3 & HA & HB & HM & Hc1 & Hc2 & Hν) & _ & _).
  destruct (inv_case Hi Hx') as ((_ & W7 & W8 & W9 & HA' & HB' & HM' & Hc1' & Hc2' & Hν') & _ & _).
  destruct (IHν ν' i _ _ _ _ Hc Hν Hν') as [Dν | N];
    [| right; intros D; destruct (ainv_case D) as (l10 & l11 & l12 & A2 & B2 & M2 & c12 & c22 & ν2 & W0 & E
                                                   & _ & _ & _ & _ & Dν2);
       injection E as <- <- <- <- <- <- <- <- <-; rewrite <- (ac_nee_uniq Dν0 Dν2) in Dν2; exact (N Dν2)].
  (* the summands, through the scrutinees' types *)
  destruct (ac_nee_sound' Dν Hc Hν Hν') as (E0 & E1 & _).
  destruct (case_annots Hi Hc W1 W2 E0 E1) as (E17 & E28 & EA & EB).
  destruct (leqv_dec l3 l9) as [H39 | N]; [| refute].
  pose proof (leqv_lequiv _ _ _ W3 W9 H39) as E39.
  destruct (case_right_left (M := M) (c1' := c1') (c2' := c2') (ν' := ν') Hc E17 E28 E39 HA HB HA' HB' EA EB HM')
    as [HM'3 Hbr].
  destruct (IHM M' i _ _ Hc HM HM'3) as [DM | N]; [| refute].
  pose proof (ac_ty_sound Hc DM HM HM'3) as EM.
  destruct (Hbr HM EM Hc1' Hc2' Hν') as (_ & _ & Hc1'2 & Hc2'2 & _).
  destruct (IHc1 c1' i l3 Hc Hc1 Hc1'2) as [Dc1 | N]; [| refute].
  destruct (IHc2 c2' i l3 Hc Hc2 Hc2'2) as [Dc2 | N]; [left; eapply actmne_case; eassumption | refute].
Qed.

Lemma Dc_actmne_fst {G Γ l1 l2 l3 l4 A A0 B Bb ν ν0 m m' A0' B0} :
  ac_tmnee G Γ ν ν0 (tySig m m' A0' B0) -> Dc_nee G Γ ν ν0 (tySig m m' A0' B0) ->
  Dc_ne G Γ (tmFst l1 l2 A B ν) (tmFst l3 l4 A0 Bb ν0) A0'.
Proof.
  intros Dν0 IHν x i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmne _ _ _ (tmFst ?a ?b ?c ?d ?e) _) =>
    rename a into l5, b into l6, c into A', d into B', e into ν' end.
  destruct (inv_fst Hi Hx) as ((_ & _ & _ & _ & _ & Hν) & _ & _).
  destruct (inv_fst Hi Hx') as ((_ & _ & _ & _ & _ & Hν') & _ & _).
  destruct (IHν ν' i _ _ _ _ Hc Hν Hν') as [Dν | N]; [left; eapply actmne_fst; exact Dν |].
  right; intros D. destruct (ainv_fst D) as (l7 & l8 & A2 & B2 & ν2 & m2 & m2' & A1 & B1 & E & Dν2).
  injection E as <- <- <- <- <-. rewrite <- (ac_nee_uniq Dν0 Dν2) in Dν2. exact (N Dν2).
Qed.

Lemma Dc_actmne_snd {G Γ l1 l2 l3 l4 A A0 B Bb ν ν0 m m' A0' B0} :
  ac_tmnee G Γ ν ν0 (tySig m m' A0' B0) -> Dc_nee G Γ ν ν0 (tySig m m' A0' B0) ->
  Dc_ne G Γ (tmSnd l1 l2 A B ν) (tmSnd l3 l4 A0 Bb ν0) B0[lsingle (tmFst m m' A0' B0 ν)].
Proof.
  intros Dν0 IHν x i k k' X X' Hc Hx Hx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct x; try solve [refute_con].
  match goal with |- Dec (ac_tmne _ _ _ (tmSnd ?a ?b ?c ?d ?e) _) =>
    rename a into l5, b into l6, c into A', d into B', e into ν' end.
  destruct (inv_snd Hi Hx) as ((_ & _ & _ & _ & _ & Hν) & _ & _).
  destruct (inv_snd Hi Hx') as ((_ & _ & _ & _ & _ & Hν') & _ & _).
  destruct (IHν ν' i _ _ _ _ Hc Hν Hν') as [Dν | N]; [left; eapply actmne_snd; exact Dν |].
  right; intros D. destruct (ainv_snd D) as (l7 & l8 & A2 & B2 & ν2 & m2 & m2' & A1 & B1 & E & Dν2).
  injection E as <- <- <- <- <-. rewrite <- (ac_nee_uniq Dν0 Dν2) in Dν2. exact (N Dν2).
Qed.

