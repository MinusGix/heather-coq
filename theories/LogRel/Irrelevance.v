(** * Irrelevance (ch. 7, Right Irrelevance)

    Two derivations relating the same left type [T] to [T'] and to [T'']
    give equivalent term relations.  The left type fixes the shape (weak
    head normal forms are unique), the universe level and the Π components;
    the right-hand types only enter through conversion. *)
From DeLaM.LogRel Require Export Modal.

Section Irrelevance.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

(** ** Declarative helpers at the instance's layer *)

Lemma tyred_eq' {G Γ T W l} : [ G ; Γ ⊢g T ⤳* W @ l ] -> [ G ; Γ ⊢g T ≅ W @ l ].
Proof using . now intros []. Qed.

(** Right-hand types related to the same left type are convertible. *)
Lemma right_conv {n rec G Γ T T' T'' l R R'} :
  LR n rec G Γ T T' l R -> LR n rec G Γ T T'' l R' -> [ G ; Γ ⊢g T' ≅ T'' @ l ].
Proof using EL.
  intros H1 H2. apply escape_ty in H1 as (_ & _ & H1), H2 as (_ & _ & H2).
  apply geq_ty_sound in H1, H2. eapply eqty_trans; [apply eqty_sym, H1 | exact H2].
Qed.

(** ** Shapes: typed reductions of one type to two whnfs agree *)

Lemma red_whnf_agree {G Γ T W W' l l'} :
  [ G ; Γ ⊢g T ⤳* W @ l ] -> [ G ; Γ ⊢g T ⤳* W' @ l' ] -> whnf_ty W -> whnf_ty W' -> W = W'.
Proof using . apply tyred_whnf_det. Qed.

Ltac whnf_of V :=
  match goal with
  | H : [ _ ; _ ⊢ V ~ _ @ _ ] |- _ => exact (whnf_ty_ne _ (gne_ty_whne_l H))
  | _ => solve [eauto with whnf]
  end.

(** Two reductions of the same type: identify the targets, or refute. *)
Ltac agree :=
  match goal with
  | H1 : tyred ?G ?i ?Γ ?T ?W1 ?l, H2 : tyred ?G ?i ?Γ ?T ?W2 ?l' |- _ =>
      let Heq := fresh "Heq" in
      assert (Heq : W1 = W2) by (eapply red_whnf_agree; [exact H1 | exact H2 | whnf_of W1 | whnf_of W2]);
      clear H2;
      first [ discriminate Heq
            | injection Heq; intros; subst
            | subst W1
            | subst W2
            | clear Heq ]
  end.

(** Expose the reduction of the left type of a contextual-type case. *)
Ltac open_mod :=
  match goal with HM : ModRel _ _ _ _ _ _ |- _ => destruct HM end.

Ltac ne_absurd :=
  match goal with
  | H : [ _ ; _ ⊢ ?V ~ _ @ _ ] |- _ =>
      let Hw := fresh in pose proof (gne_ty_whne_l H) as Hw; solve [inversion Hw]
  end.

(** ** The neutral case *)

Lemma NeRel_conv {G Γ V V' V'' l t t'} :
  [ G ; Γ ⊢g V' ≅ V'' @ l ] -> NeRel G Γ V V' l t t' -> NeRel G Γ V V'' l t t'.
Proof using EL.
  intros HV (ν & ν' & H1 & H2 & H3 & H4). exists ν, ν'.
  refine (conj H1 (conj _ (conj H3 _))).
  - eapply tmred_conv; eauto using ge_typeof.
  - eapply gne_tm_conv; eauto.
Qed.

(** ** The Π case, one direction *)

Section PiDir.
Context {G Γ l1 l2 l3 l4 m3 m4 A B A' B' A'' B''}
  {domR : DomRel G Γ} {codR : CodRel G Γ domR}
  {domR' : DomRel G Γ} {codR' : CodRel G Γ domR'}
  (Hl1 : lwf (gL G) l1)
  (HA : [ G ; Γ ⊢g A @ l1 ]) (HA' : [ G ; Γ ⊢g A' @ l1 ]) (HA'' : [ G ; Γ ⊢g A'' @ l1 ])
  (HAA' : [ G ; Γ ⊢ A ≈ A' @ l1 ]) (HAA'' : [ G ; Γ ⊢ A ≈ A'' @ l1 ])
  (HBB' : [ G ; Γ ,, A @ l1 ⊢ B ≈ B' @ l2 ]) (HBB'' : [ G ; Γ ,, A @ l1 ⊢ B ≈ B'' @ l2 ])
  (HP : [ G ; Γ ⊢g tyPi l3 l4 A' B' ≅ tyPi m3 m4 A'' B'' @ lmax l1 l2 ])
  (Hdom : forall ρ, releq (domR ρ) (domR' ρ))
  (Hcod : forall ρ a a' ha ha', releq (codR ρ a a' ha) (codR' ρ a a' ha')).

Lemma PiRel_dir t t' :
  PiRel G Γ l1 l2 l3 l4 A B A' B' domR codR t t' ->
  PiRel G Γ l1 l2 m3 m4 A B A'' B'' domR' codR' t t'.
Proof using EL HA HA' HA'' HAA' HAA'' HBB' HBB'' HP Hcod Hdom Hl1.
  intros (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
  exists w, w'. refine (conj Hw (conj _ (conj Hnf (conj Hnf' (conj Heq (conj _ _)))))).
  - eapply tmred_conv; eauto using ge_typeof.
  - eapply geq_tm_conv; eauto.
  - intros ρ a a' ha' la lb la' lb' A1 B1 A1' B1' H1 H2 H3 H4 HA1 HB1 HA1' HB1'.
    pose proof ((proj2 (Hdom ρ a a')) ha') as ha.
    apply (Hcod ρ a a' ha ha').
    (* the annotations of the right application, in terms of [A'], [B'] *)
    pose proof (kw_lwf ρ Hl1) as Hl1'.
    pose proof (kw_ext ρ HA'' Hl1) as HΔA''.
    pose proof (kw_ext ρ HA' Hl1) as HΔA'.
    assert (E1 : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A ≈ kty ρ A' @ l1 ]) by exact (kw_geq_ty ρ HAA').
    assert (E2 : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A ≈ kty ρ A'' @ l1 ]) by exact (kw_geq_ty ρ HAA'').
    assert (E3 : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l1 ⊢ ktyl ρ B' ≈ ktyl ρ B'' @ l2 ]).
    { eapply geq_ty_trans; [apply geq_ty_sym, (kw_geq_ty_l ρ HA Hl1 HBB')
                            | exact (kw_geq_ty_l ρ HA Hl1 HBB'')]. }
    refine (HK ρ a a' ha la lb la' lb' A1 B1 A1' B1' H1 H2 H3 H4 HA1 HB1 _ _).
    + eapply geq_ty_trans; [|exact HA1'].
      eapply geq_ty_trans; [apply geq_ty_sym, E1 | exact E2].
    + (* move [B'⟨r⟩ ≈ B''⟨r⟩] to [Δ, A''⟨r⟩], compose, move to [Δ, A'⟨r⟩] *)
      assert (E4 : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A'' @ l1 ⊢ ktyl ρ B' ≈ B1' @ l2 ]).
      { eapply geq_ty_trans; [|exact HB1'].
        eapply geq_ty_ctxconv; [apply geq_ty_sound, E2 | now apply lequiv_refl | exact HΔA'' | exact E3]. }
      eapply geq_ty_ctxconv; [| now apply lequiv_refl | exact HΔA' | exact E4].
      apply geq_ty_sound. eapply geq_ty_trans; [apply geq_ty_sym, E2 | exact E1].
Qed.

End PiDir.

(** ** The Σ case, one direction *)

Section SigDir.
Context {G Γ l1 l2 l3 l4 m3 m4 A B A' B' A'' B''}
  {domR : DomRel G Γ} {codR : CodRel G Γ domR}
  {domR' : DomRel G Γ} {codR' : CodRel G Γ domR'}
  (Hl1 : lwf (gL G) l1)
  (HA : [ G ; Γ ⊢g A @ l1 ]) (HA' : [ G ; Γ ⊢g A' @ l1 ]) (HA'' : [ G ; Γ ⊢g A'' @ l1 ])
  (HAA' : [ G ; Γ ⊢ A ≈ A' @ l1 ]) (HAA'' : [ G ; Γ ⊢ A ≈ A'' @ l1 ])
  (HBB' : [ G ; Γ ,, A @ l1 ⊢ B ≈ B' @ l2 ]) (HBB'' : [ G ; Γ ,, A @ l1 ⊢ B ≈ B'' @ l2 ])
  (HP : [ G ; Γ ⊢g tySig l3 l4 A' B' ≅ tySig m3 m4 A'' B'' @ lmax l1 l2 ])
  (Hdom : forall ρ, releq (domR ρ) (domR' ρ))
  (Hcod : forall ρ a a' ha ha', releq (codR ρ a a' ha) (codR' ρ a a' ha')).

Lemma SigRel_dir t t' :
  SigRel G Γ l1 l2 l3 l4 A B A' B' domR codR t t' ->
  SigRel G Γ l1 l2 m3 m4 A B A'' B'' domR' codR' t t'.
Proof using EL HA HA' HA'' HAA' HAA'' HBB' HBB'' HP Hcod Hdom Hl1.
  intros (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
  exists w, w'. refine (conj Hw (conj _ (conj Hnf (conj Hnf' (conj Heq (conj _ _)))))).
  - eapply tmred_conv; eauto using ge_typeof.
  - eapply geq_tm_conv; eauto.
  - intros ρ la lb la' lb' A1 B1 A1' B1' H1 H2 H3 H4 HA1 HB1 HA1' HB1'.
    (* the annotations of the right application, in terms of [A'], [B'] *)
    pose proof (kw_lwf ρ Hl1) as Hl1'.
    pose proof (kw_ext ρ HA'' Hl1) as HΔA''.
    pose proof (kw_ext ρ HA' Hl1) as HΔA'.
    assert (E1 : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A ≈ kty ρ A' @ l1 ]) by exact (kw_geq_ty ρ HAA').
    assert (E2 : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A ≈ kty ρ A'' @ l1 ]) by exact (kw_geq_ty ρ HAA'').
    assert (E3 : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l1 ⊢ ktyl ρ B' ≈ ktyl ρ B'' @ l2 ]).
    { eapply geq_ty_trans; [apply geq_ty_sym, (kw_geq_ty_l ρ HA Hl1 HBB')
                            | exact (kw_geq_ty_l ρ HA Hl1 HBB'')]. }
    assert (X1 : [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ A' ≈ A1' @ l1 ]).
    { eapply geq_ty_trans; [|exact HA1']. eapply geq_ty_trans; [apply geq_ty_sym, E1 | exact E2]. }
    assert (X2 : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A' @ l1 ⊢ ktyl ρ B' ≈ B1' @ l2 ]).
    { (* move [B'⟨r⟩ ≈ B''⟨r⟩] to [Δ, A''⟨r⟩], compose, move to [Δ, A'⟨r⟩] *)
      assert (E4 : [ kw_G ρ ; kw_Δ ρ ,, kty ρ A'' @ l1 ⊢ ktyl ρ B' ≈ B1' @ l2 ]).
      { eapply geq_ty_trans; [|exact HB1'].
        eapply geq_ty_ctxconv; [apply geq_ty_sound, E2 | now apply lequiv_refl | exact HΔA'' | exact E3]. }
      eapply geq_ty_ctxconv; [| now apply lequiv_refl | exact HΔA' | exact E4].
      apply geq_ty_sound. eapply geq_ty_trans; [apply geq_ty_sym, E2 | exact E1]. }
    destruct (HK ρ la lb la' lb' A1 B1 A1' B1' H1 H2 H3 H4 HA1 HB1 X1 X2) as [h Hc].
    exists (proj1 (Hdom ρ _ _) h). exact (proj1 (Hcod ρ _ _ h _ _ _) Hc).
Qed.

End SigDir.

(** The binder cases ([Π], [Σ]): the right types are convertible, the
    domain and codomain relations irrelevant, and the term relations move
    along them by [dir]. *)
Ltac poly_irrel F geqF dir :=
  let HP := fresh "HP" in let Hdom := fresh "Hdom" in let Hcod := fresh "Hcod" in
  match goal with
  | |- releq (_ ?G ?Γ ?l1 ?l2 ?l3 ?l4 ?A ?B ?A' ?B' ?dR ?cR)
             (_ _ _ _ _ ?k3 ?k4 _ _ ?C' ?D' ?dR' ?cR') =>
      assert (HP : [ G ; Γ ⊢g F l3 l4 A' B' ≅ F k3 k4 C' D' @ lmax l1 l2 ])
        by (eapply (eqty_trans _ _ _ _ (F l1 l2 A B)); [apply eqty_sym|];
            apply geq_ty_sound, geqF; eauto using lequiv_sym);
      assert (Hdom : forall ρ, releq (dR ρ) (dR' ρ))
        by (intros; match goal with IH : forall (ρ : kwk _ _) T'' R', _ -> releq (dR _) _ |- _ =>
                                        eapply IH end; eauto);
      assert (Hcod : forall ρ a a' ha ha', releq (cR ρ a a' ha) (cR' ρ a a' ha'))
        by (intros; match goal with IH : forall (ρ : kwk _ _) a a' ha T'' R', _ -> releq (cR _ _ _ _) _ |- _ =>
                                        eapply IH end; eauto)
  end;
  intros t t'; split;
  [ eapply dir; eassumption
  | eapply dir; try eassumption;
    [ now apply eqty_sym | intros; apply releq_sym, Hdom | intros; apply releq_sym, Hcod ] ].

(** ** The meta-function cases, one direction *)

Lemma CPiRel_dir {G Γ l1 l2 m2 T1 T1' T1''} {instR instR' : CInstRel G Γ} :
  [ G ; Γ ⊢g tyCPi l2 T1' ≅ tyCPi m2 T1'' @ l1 ] ->
  (forall ρ Δ Δ' h, releq (instR ρ Δ Δ' h) (instR' ρ Δ Δ' h)) ->
  forall t t', CPiRel G Γ l1 l2 T1 T1' instR t t' -> CPiRel G Γ l1 m2 T1 T1'' instR' t t'.
Proof using EL.
  intros HP Hinst t t' (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
  exists w, w'. refine (conj Hw (conj _ (conj Hnf (conj Hnf' (conj Heq (conj _ _)))))).
  - eapply tmred_conv; eauto using ge_typeof.
  - eapply geq_tm_conv; eauto.
  - intros ρ Δ Δ' h. apply (Hinst ρ Δ Δ' h), HK.
Qed.

Lemma TPiRel_dir {G Γ Δ1 Δ1' Δ1'' l1 l2 l3 l4 m3 m4 T1 T1' T1''} {instR instR' : TInstRel G Γ Δ1 l1} :
  [ G ; Γ ⊢g tyTPi Δ1' l3 l4 T1' ≅ tyTPi Δ1'' m3 m4 T1'' @ l2 ] ->
  (forall ρ A A' h, releq (instR ρ A A' h) (instR' ρ A A' h)) ->
  forall t t', TPiRel G Γ Δ1 Δ1' l1 l2 l3 l4 T1 T1' instR t t' ->
    TPiRel G Γ Δ1 Δ1'' l1 l2 m3 m4 T1 T1'' instR' t t'.
Proof using EL.
  intros HP Hinst t t' (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
  exists w, w'. refine (conj Hw (conj _ (conj Hnf (conj Hnf' (conj Heq (conj _ _)))))).
  - eapply tmred_conv; eauto using ge_typeof.
  - eapply geq_tm_conv; eauto.
  - intros ρ A A' h. apply (Hinst ρ A A' h), HK.
Qed.

(** ** Irrelevance *)

Theorem LR_irrel n rec G Γ T T' T'' l R R' :
  LR n rec G Γ T T' l R -> LR n rec G Γ T T'' l R' -> releq R R'.
Proof using EL VL.
  intros H1; revert T'' R'.
  induction H1 as [G Γ T T' l R Hl HT HT' HR
                  | G Γ T T' l l1 l2 R Hl Hl2 Hn HT HT' HR
                  | G Γ T T' l V V' R HT HT' HV HR
                  | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                      [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd IHdom codAd IHcod HR
                  | G Γ T T' l R Hj HM
                  | G Γ T T' l l1 l2 T1 T1' instR R Hj Hl Hl2 Hw1 HT HT' HT1 HT1' Hgeq instAd IHinst HR
                  | G Γ T T' l Δ1 Δ1' l1 l2 l3 l4 T1 T1' instR R Hj Hl Hl3 Hl4 Hw1 Hw2 HT HT' HΔ HT1 HT1'
                      Hgeq instAd IHinst HR
                  | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                      [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd IHdom codAd IHcod HR
                  | G Γ T T' l l1 l2 R Hl Hl2 Hw HT HT' HR
                  | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                  | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA IHRA Hra Hrb Hps Hpt HR
                  | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                  | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                      HRA IHRA HRB IHRB Hpa Hta Hpb Htb HR
                  | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                      [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd IHdom codAd IHcod HR
                  | G Γ T T' l l1 l2 A A' N N' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd IHdom arAd HR
                  | G Γ T T' l l1 l2 A A' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ IHRQ Hqs Hqt HR
                  | G Γ T T' l l1 li1 l2 li2 X X' A A' N N' Ot Ot' Ch Ch' m m' idxR domR R Hl Hl2 Hli2 Hw Hwi
                      HT HT' HX HX' HA HA' HN HN' HO HO' HCh HCh' Hmt Hmt' HXX HAA HNN HOO HChh Hmm
                      idxAd IHidx Hisym Histr domAd IHdom arAd otAd chAd ixAd HR
                  | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                      Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                      HmXX HmAA HmBB HmCC Hmmm midxAd IHmidx mshAd IHmsh mposAd IHmpos mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR];
    intros T'' R' H2;
    inversion H2 as [? ? ? ? ? ? Hk HTk HTk' HkR
                    | ? ? ? ? ? k1 k2 ? Hk Hk2 Hkn HTk HTk' HkR
                    | ? ? ? ? ? W W' ? HTk HTk' HW HkR
                    | ? ? ? ? ? k1 k2 k3 k4 C D C' D' domR' codR' ?
                        [Hk Hk3 Hk4 Hkw1 Hkw2 HTk HTk' HC HC' HD HD' HCC HDD] domAd' codAd' HkR
                    | ? ? ? ? ? ? Hkj HkM
                    | ? ? ? ? ? k1 k2 U1 U1' instR' ? Hkj Hk Hk2 Hkw1 HTk HTk' HU1 HU1' Hkgeq instAd' HkR
                    | ? ? ? ? ? Θ1 Θ1' k1 k2 k3 k4 U1 U1' instR' ? Hkj Hk Hk3 Hk4 Hkw1 Hkw2 HTk HTk' HΘ
                        HU1 HU1' Hkgeq instAd' HkR
                    | ? ? ? ? ? k1 k2 k3 k4 C D C' D' domR' codR' ?
                        [Hk Hk3 Hk4 Hkw1 Hkw2 HTk HTk' HC HC' HD HD' HCC HDD] domAd' codAd' HkR
                    | ? ? ? ? ? k1 k2 ? Hk Hk2 Hkn HTk HTk' HkR
                    | ? ? ? ? ? t1 t2 C C' c c' d d' ? Hk Hk2 Hkn HTk HTk' HC HCC Hcc Hdd HkR
                    | ? ? ? ? ? t1 t2 ? Hk Hk2 Hkn HTk HTk' HkR
                    | ? ? ? ? ? t1 t2 C C' c c' d d' RA' ? Hk Hk2 Hkn HTk HTk' HC HCC Hcc Hdd
                        HRA' Hra' Hrb' Hps' Hpt' HkR
                    | ? ? ? ? ? t1 t2 ? Hk Hk2 Hkn HTk HTk' HkR
                    | ? ? ? ? ? t1 t2 t3 t4 C C' D D' RA' RB' ? Hk Hk3 Hk4 Hkw1 Hkw2 HTk HTk' HC HCC HD HDD
                        HRA' HRB' Hpa' Hta' Hpb' Htb' HkR
                    | ? ? ? ? ? k1 k2 k3 k4 C D C' D' domR' codR' ?
                        [Hk Hk3 Hk4 Hkw1 Hkw2 HTk HTk' HC HC' HD HD' HCC HDD] domAd' codAd' HkR
                    | ? ? ? ? ? k1 k2 C C' M M' domR' ? Hk Hk2 Hkw HTk HTk' HC HC' HkN HkN' HCC HkNN domAd' arAd' HkR
                    | ? ? ? ? ? k1 k2 C C' RQ' ? Hk Hk2 Hkw HTk HTk' HC HCC HRQ' Hqs' Hqt' HkR
                    | ? ? ? ? ? k1 ki1 k2 ki2 jX jX' jA jA' jN jN' jO jO' jC jC' q q' idxR' domR' ? Hk Hk2 Hki2 Hkw Hkwi
                        HTk HTk' HjX HjX' HjA HjA' HjN HjN' HjO HjO' HjC HjC' Hq Hq' HjXX HjAA HjNN HjOO HjCC Hqq
                        idxAd' Hisym' Histr' domAd' arAd' otAd' chAd' ixAd' HkR];
    subst; try (agree; try ne_absurd).
  (* contextual types, and mismatches with them *)
  all: try solve [eapply ModRel_irrel; eassumption].
  all: try solve [open_mod; agree; try ne_absurd].
  all: eapply releq_trans; [exact HR | eapply releq_trans; [| apply releq_sym, HkR]].
  (* same shape *)
  - apply releq_refl.
  - apply releq_refl.
  - assert (HVV : [ G ; Γ ⊢g V' ≅ W' @ l ]).
    { eapply eqty_trans; [apply eqty_sym|]; apply geq_ty_sound, gne_ty_geq; eassumption. }
    intros t t'; split; apply NeRel_conv; [exact HVV | now apply eqty_sym].
  - poly_irrel tyPi @geq_ty_pi @PiRel_dir.
  - (* CΠ: the right types are convertible, the instances irrelevant *)
    match goal with
    | |- releq (CPiRel _ _ ?a1 ?a2 ?A1 ?A1' ?iR) (CPiRel _ _ _ ?b2 _ ?B1' ?iR') =>
        assert (HP : [ G ; Γ ⊢g tyCPi a2 A1' ≅ tyCPi b2 B1' @ a1 ])
          by (eapply eqty_trans; [apply eqty_sym, geq_ty_sound; eassumption | apply geq_ty_sound; eassumption]);
        assert (Hinst : forall ρ Δ Δ' h, releq (iR ρ Δ Δ' h) (iR' ρ Δ Δ' h))
          by (intros; eapply IHinst; eauto)
    end.
    intros t t'; split.
    + eapply CPiRel_dir; eassumption.
    + eapply CPiRel_dir; [now apply eqty_sym | intros; apply releq_sym, Hinst].
  - (* TΠ *)
    match goal with
    | |- releq (TPiRel _ _ _ ?D1' ?a1 ?a2 ?a3 ?a4 _ ?A1' ?iR) (TPiRel _ _ _ ?E1' _ _ ?b3 ?b4 _ ?B1' ?iR') =>
        assert (HP : [ G ; Γ ⊢g tyTPi D1' a3 a4 A1' ≅ tyTPi E1' b3 b4 B1' @ a2 ])
          by (eapply eqty_trans; [apply eqty_sym, geq_ty_sound; eassumption | apply geq_ty_sound; eassumption]);
        assert (Hinst : forall ρ A A' h, releq (iR ρ A A' h) (iR' ρ A A' h))
          by (intros; eapply IHinst; eauto)
    end.
    intros t t'; split.
    + eapply TPiRel_dir; eassumption.
    + eapply TPiRel_dir; [now apply eqty_sym | intros; apply releq_sym, Hinst].
  - poly_irrel tySig @geq_ty_sig @SigRel_dir.
  - apply releq_refl.
  - apply releq_refl.
  - apply releq_refl.
  - (* Id: the carriers' relations agree *)
    apply IdRel_releq. eapply IHRA; eassumption.
  - apply releq_refl.
  - (* +: the summands' relations agree *)
    apply SumRel_releq; [eapply IHRA | eapply IHRB]; eassumption.
  - (* W: the shapes' and positions' relations agree *)
    apply WRel_releq.
    + intros; match goal with IH : forall (ρ : kwk _ _) T'' R', _ -> releq (domR _) _ |- _ =>
                                eapply IH end; eauto.
    + intros; match goal with IH : forall (ρ : kwk _ _) a a' ha T'' R', _ -> releq (codR _ _ _ _) _ |- _ =>
                                eapply IH end; eauto.
  - (* Wf: the shapes' relations agree *)
    apply WfRel_releq.
    intros; match goal with IH : forall (ρ : kwk _ _) T'' R', _ -> releq (domR _) _ |- _ =>
                              eapply IH end; eauto.
  - (* ∥·∥: the carriers' relations agree *)
    apply SqRel_releq. eapply IHRQ; eassumption.
  - (* IWf: the index's and the shapes' relations agree *)
    apply IWfRel_releq.
    + intros; match goal with IH : forall (ρ : kwk _ _) T'' R', _ -> releq (idxR _) _ |- _ =>
                                eapply IH end; eauto.
    + intros; match goal with IH : forall (ρ : kwk _ _) T'' R', _ -> releq (domR _) _ |- _ =>
                                eapply IH end; eauto.
Qed.

(** ** Inversion by the left type's normal form *)

Section Inversion.
Context {n : nat} {rec : lvl -> RedRel} {G : gctx} {Γ : ctx} {T T' : ty} {l : lvl}
  {R : tm -> tm -> Prop} (H : LR n rec G Γ T T' l R).

Lemma LR_inv_nat {l'} : [ G ; Γ ⊢g T ⤳* tyNat @ l' ] ->
  lequiv (gL G) l lzero /\ [ G ; Γ ⊢g T' ⤳* tyNat @ l ] /\ releq R (NatRel G Γ).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l l1 l2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
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
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR];
    intros HN; try open_mod; agree; try ne_absurd; auto.
Qed.

Lemma LR_inv_U {l1 l'} : [ G ; Γ ⊢g T ⤳* tyU l1 @ l' ] ->
  exists l2, lequiv (gL G) l (lsuc l1) /\ lequiv (gL G) l2 l1 /\ lmeasure l1 < n /\
    [ G ; Γ ⊢g T' ⤳* tyU l2 @ l ] /\ releq R (URel rec G Γ l1).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR];
    intros HN; try open_mod; agree; try ne_absurd; eauto 7.
Qed.

Lemma LR_inv_unit {l1 l'} : [ G ; Γ ⊢g T ⤳* tyUnit l1 @ l' ] ->
  exists l2, lequiv (gL G) l l1 /\ lequiv (gL G) l2 l1 /\ lwf (gL G) l1 /\
    [ G ; Γ ⊢g T' ⤳* tyUnit l2 @ l ] /\ releq R (UnitRel G Γ l1).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR];
    intros HN; try open_mod; agree; try ne_absurd; eauto 7.
Qed.

Lemma LR_inv_seq {l1 X x y l'} : [ G ; Γ ⊢g T ⤳* tySEq l1 X x y @ l' ] ->
  exists l2 X' x' y', lequiv (gL G) l l1 /\ lequiv (gL G) l2 l1 /\ lwf (gL G) l1 /\
    [ G ; Γ ⊢g T' ⤳* tySEq l2 X' x' y' @ l ] /\ [ G ; Γ ⊢g X @ l1 ] /\ [ G ; Γ ⊢ X ≈ X' @ l1 ] /\
    [ G ; Γ ⊢ x ≈ x' : X @ l1 ] /\ [ G ; Γ ⊢ y ≈ y' : X @ l1 ] /\
    releq R (SEqRel G Γ (tySEq l1 X x y) l1).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR];
    intros HN; try open_mod; agree; try ne_absurd; eauto 15.
Qed.

Lemma LR_inv_id {l1 X x y l'} : [ G ; Γ ⊢g T ⤳* tyId l1 X x y @ l' ] ->
  exists l2 X' x' y' RA, lequiv (gL G) l l1 /\ lequiv (gL G) l2 l1 /\ lwf (gL G) l1 /\
    [ G ; Γ ⊢g T' ⤳* tyId l2 X' x' y' @ l ] /\ [ G ; Γ ⊢g X @ l1 ] /\ [ G ; Γ ⊢ X ≈ X' @ l1 ] /\
    [ G ; Γ ⊢ x ≈ x' : X @ l1 ] /\ [ G ; Γ ⊢ y ≈ y' : X @ l1 ] /\
    LR n rec G Γ X X' l1 RA /\ RA x x' /\ RA y y' /\
    (forall u v, RA u v -> RA v u) /\ (forall u v w, RA u v -> RA v w -> RA u w) /\
    releq R (IdRel G Γ l1 X x y RA).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR];
    intros HN; try open_mod; agree; try ne_absurd; eauto 20.
Qed.

(** Binary sums (M12b). *)
Lemma LR_inv_sum {l1 l2 X Y l'} : [ G ; Γ ⊢g T ⤳* tySum l1 l2 X Y @ l' ] ->
  exists l3 l4 X' Y' RA RB, lequiv (gL G) l (lmax l1 l2) /\ lequiv (gL G) l3 l1 /\ lequiv (gL G) l4 l2 /\
    lwf (gL G) l1 /\ lwf (gL G) l2 /\
    [ G ; Γ ⊢g T' ⤳* tySum l3 l4 X' Y' @ l ] /\ [ G ; Γ ⊢g X @ l1 ] /\ [ G ; Γ ⊢ X ≈ X' @ l1 ] /\
    [ G ; Γ ⊢g Y @ l2 ] /\ [ G ; Γ ⊢ Y ≈ Y' @ l2 ] /\
    LR n rec G Γ X X' l1 RA /\ LR n rec G Γ Y Y' l2 RB /\
    (forall u v, RA u v -> RA v u) /\ (forall u v w, RA u v -> RA v w -> RA u w) /\
    (forall u v, RB u v -> RB v u) /\ (forall u v w, RB u v -> RB v w -> RB u w) /\
    releq R (SumRel G Γ l1 l2 X Y RA RB).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR];
    intros HN; try open_mod; agree; try ne_absurd; do 6 eexists; eauto 25.
Qed.

Lemma LR_inv_sempty {l1 l'} : [ G ; Γ ⊢g T ⤳* tySEmpty l1 @ l' ] ->
  exists l2, lequiv (gL G) l l1 /\ lequiv (gL G) l2 l1 /\ lwf (gL G) l1 /\
    [ G ; Γ ⊢g T' ⤳* tySEmpty l2 @ l ] /\ releq R (SEmptyRel G Γ l1).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR];
    intros HN; try open_mod; agree; try ne_absurd; eauto 7.
Qed.

(** The empty type (M12a). *)
Lemma LR_inv_empty {l1 l'} : [ G ; Γ ⊢g T ⤳* tyEmpty l1 @ l' ] ->
  exists l2, lequiv (gL G) l l1 /\ lequiv (gL G) l2 l1 /\ lwf (gL G) l1 /\
    [ G ; Γ ⊢g T' ⤳* tyEmpty l2 @ l ] /\ releq R (EmptyRel G Γ l1).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR];
    intros HN; try open_mod; agree; try ne_absurd; eauto 7.
Qed.


Lemma LR_inv_ne {V l'} : [ G ; Γ ⊢g T ⤳* V @ l' ] -> whne_ty V ->
  exists V', [ G ; Γ ⊢g T' ⤳* V' @ l ] /\ [ G ; Γ ⊢ V ~ V' @ l ] /\ releq R (NeRel G Γ V V' l).
Proof using EL H.
  intros HN HV0; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l W W' R HT HT' HW HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR];
    intros HN; try open_mod; agree; try solve [inversion HV0]; eauto.
Qed.

Lemma LR_inv_pi {m1 m2 C D l'} : [ G ; Γ ⊢g T ⤳* tyPi m1 m2 C D @ l' ] ->
  exists m3 m4 C' D' (domR : DomRel G Γ) (codR : CodRel G Γ domR),
    PolyFacts G Γ tyPi T T' l m1 m2 m3 m4 C D C' D' /\
    (forall ρ : kwk G Γ, LR n rec (kw_G ρ) (kw_Δ ρ) (kty ρ C) (kty ρ C') m1 (domR ρ)) /\
    (forall (ρ : kwk G Γ) a a' (ha : domR ρ a a'),
        LR n rec (kw_G ρ) (kw_Δ ρ) (ktyl ρ D)[lsingle a] (ktyl ρ D')[lsingle a'] m2
           (codR ρ a a' ha)) /\
    releq R (PiRel G Γ m1 m2 m3 m4 C D C' D' domR codR).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR];
    intros HN; try open_mod; agree; try ne_absurd.
  do 6 eexists; refine (conj _ _); [split|]; eauto 20.
Qed.

Lemma LR_inv_sig {m1 m2 C D l'} : [ G ; Γ ⊢g T ⤳* tySig m1 m2 C D @ l' ] ->
  exists m3 m4 C' D' (domR : DomRel G Γ) (codR : CodRel G Γ domR),
    PolyFacts G Γ tySig T T' l m1 m2 m3 m4 C D C' D' /\
    (forall ρ : kwk G Γ, LR n rec (kw_G ρ) (kw_Δ ρ) (kty ρ C) (kty ρ C') m1 (domR ρ)) /\
    (forall (ρ : kwk G Γ) a a' (ha : domR ρ a a'),
        LR n rec (kw_G ρ) (kw_Δ ρ) (ktyl ρ D)[lsingle a] (ktyl ρ D')[lsingle a'] m2
           (codR ρ a a' ha)) /\
    releq R (SigRel G Γ m1 m2 m3 m4 C D C' D' domR codR).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR];
    intros HN; try open_mod; agree; try ne_absurd.
  do 6 eexists; refine (conj _ _); [split|]; eauto 20.
Qed.

Lemma LR_inv_W {m1 m2 C D l'} : [ G ; Γ ⊢g T ⤳* tyW m1 m2 C D @ l' ] ->
  exists m3 m4 C' D' (domR : DomRel G Γ) (codR : CodRel G Γ domR),
    PolyFacts G Γ tyW T T' l m1 m2 m3 m4 C D C' D' /\
    (forall ρ : kwk G Γ, LR n rec (kw_G ρ) (kw_Δ ρ) (kty ρ C) (kty ρ C') m1 (domR ρ)) /\
    (forall (ρ : kwk G Γ) a a' (ha : domR ρ a a'),
        LR n rec (kw_G ρ) (kw_Δ ρ) (ktyl ρ D)[lsingle a] (ktyl ρ D')[lsingle a'] m2
           (codR ρ a a' ha)) /\
    releq R (WRel G Γ m1 m2 C D domR codR).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR];
    intros HN; try open_mod; agree; try ne_absurd.
  do 6 eexists; refine (conj _ _); [split|]; eauto 20.
Qed.

Lemma LR_inv_wf {m1 C M l'} : [ G ; Γ ⊢g T ⤳* tyWf m1 C M @ l' ] ->
  exists m2 C' M' (domR : DomRel G Γ),
    lequiv (gL G) l m1 /\ lequiv (gL G) m2 m1 /\ lwf (gL G) m1 /\
    [ G ; Γ ⊢g T ⤳* tyWf m1 C M @ l ] /\ [ G ; Γ ⊢g T' ⤳* tyWf m2 C' M' @ l ] /\
    [ G ; Γ ⊢g C @ m1 ] /\ [ G ; Γ ⊢g C' @ m1 ] /\
    [ G ; Γ ,, C @ m1 ⊢g M : tyNat @ lzero ] /\ [ G ; Γ ,, C' @ m1 ⊢g M' : tyNat @ lzero ] /\
    [ G ; Γ ⊢ C ≈ C' @ m1 ] /\ [ G ; Γ ,, C @ m1 ⊢ M ≈ M' : tyNat @ lzero ] /\
    (forall ρ : kwk G Γ, LR n rec (kw_G ρ) (kw_Δ ρ) (kty ρ C) (kty ρ C') m1 (domR ρ)) /\
    (forall (ρ : kwk G Γ) a a', domR ρ a a' ->
        NatRel (kw_G ρ) (kw_Δ ρ) (ktml ρ M)[lsingle a] (ktml ρ M')[lsingle a']) /\
    releq R (WfRel G Γ m1 C M domR).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR];
    intros HN; try open_mod; agree; try ne_absurd.
  do 4 eexists; eauto 20.
Qed.

(** Indexed W-types (M17b). *)
Lemma LR_inv_iwf {iL iLi iX iA iN iO iC im l'} : [ G ; Γ ⊢g T ⤳* tyIWf iL iLi iX iA iN iO iC im @ l' ] ->
  exists k2 ki2 X' A' N' Ot' C' m' (idxR domR : DomRel G Γ),
    lequiv (gL G) l (lmax iL iLi) /\ lequiv (gL G) k2 iL /\ lequiv (gL G) ki2 iLi /\
    lwf (gL G) iL /\ lwf (gL G) iLi /\
    [ G ; Γ ⊢g T ⤳* tyIWf iL iLi iX iA iN iO iC im @ l ] /\
    [ G ; Γ ⊢g T' ⤳* tyIWf k2 ki2 X' A' N' Ot' C' m' @ l ] /\
    [ G ; Γ ⊢g iX @ iLi ] /\ [ G ; Γ ⊢g X' @ iLi ] /\ [ G ; Γ ⊢g iA @ iL ] /\ [ G ; Γ ⊢g A' @ iL ] /\
    [ G ; Γ ,, iA @ iL ⊢g iN : tyNat @ lzero ] /\ [ G ; Γ ,, A' @ iL ⊢g N' : tyNat @ lzero ] /\
    [ G ; Γ ,, iA @ iL ⊢g iO : iX⟨↑⟩ @ iLi ] /\ [ G ; Γ ,, A' @ iL ⊢g Ot' : X'⟨↑⟩ @ iLi ] /\
    [ G ; Γ ,, iA @ iL ,, tyFin iN @ lzero ⊢g iC : iX⟨↑⟩⟨↑⟩ @ iLi ] /\
    [ G ; Γ ,, A' @ iL ,, tyFin N' @ lzero ⊢g C' : X'⟨↑⟩⟨↑⟩ @ iLi ] /\
    [ G ; Γ ⊢g im : iX @ iLi ] /\ [ G ; Γ ⊢g m' : X' @ iLi ] /\
    [ G ; Γ ⊢ iX ≈ X' @ iLi ] /\ [ G ; Γ ⊢ iA ≈ A' @ iL ] /\ [ G ; Γ ,, iA @ iL ⊢ iN ≈ N' : tyNat @ lzero ] /\
    [ G ; Γ ,, iA @ iL ⊢ iO ≈ Ot' : iX⟨↑⟩ @ iLi ] /\
    [ G ; Γ ,, iA @ iL ,, tyFin iN @ lzero ⊢ iC ≈ C' : iX⟨↑⟩⟨↑⟩ @ iLi ] /\
    [ G ; Γ ⊢ im ≈ m' : iX @ iLi ] /\
    (forall ρ : kwk G Γ, LR n rec (kw_G ρ) (kw_Δ ρ) (kty ρ iX) (kty ρ X') iLi (idxR ρ)) /\
    (forall (ρ : kwk G Γ) x y, idxR ρ x y -> idxR ρ y x) /\
    (forall (ρ : kwk G Γ) x y z, idxR ρ x y -> idxR ρ y z -> idxR ρ x z) /\
    (forall ρ : kwk G Γ, LR n rec (kw_G ρ) (kw_Δ ρ) (kty ρ iA) (kty ρ A') iL (domR ρ)) /\
    (forall (ρ : kwk G Γ) a a', domR ρ a a' ->
        NatRel (kw_G ρ) (kw_Δ ρ) (ktml ρ iN)[lsingle a] (ktml ρ N')[lsingle a']) /\
    (forall (ρ : kwk G Γ) a a', domR ρ a a' ->
        idxR ρ (ktml ρ iO)[lsingle a] (ktml ρ Ot')[lsingle a']) /\
    (forall (ρ : kwk G Γ) a a', domR ρ a a' -> forall p p',
        PosRel (kw_G ρ) (kw_Δ ρ) (ktml ρ iN)[lsingle a] (ktml ρ N')[lsingle a'] p p' ->
        idxR ρ (ktmll ρ iC)[lsingle2 a p] (ktmll ρ C')[lsingle2 a' p']) /\
    (forall ρ : kwk G Γ, idxR ρ (ktm ρ im) (ktm ρ m')) /\
    releq R (IWfRel G Γ iL iLi iX iA iN iO iC idxR domR im).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR];
    intros HN; try open_mod; agree; try ne_absurd.
  do 10 eexists; eauto 40.
Qed.

(** Propositional truncation (M16a). *)
Lemma LR_inv_sq {m1 C l'} : [ G ; Γ ⊢g T ⤳* tySq m1 C @ l' ] ->
  exists m2 C' RC, lequiv (gL G) l m1 /\ lequiv (gL G) m2 m1 /\ lwf (gL G) m1 /\
    [ G ; Γ ⊢g T ⤳* tySq m1 C @ l ] /\ [ G ; Γ ⊢g T' ⤳* tySq m2 C' @ l ] /\
    [ G ; Γ ⊢g C @ m1 ] /\ [ G ; Γ ⊢ C ≈ C' @ m1 ] /\ LR n rec G Γ C C' m1 RC /\
    (forall u v, RC u v -> RC v u) /\ (forall u v w, RC u v -> RC v w -> RC u w) /\
    releq R (SqRel G Γ m1 C RC).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR];
    intros HN; try open_mod; agree; try ne_absurd.
  do 3 eexists; eauto 20.
Qed.

Lemma LR_inv_CTyp {Δ k l'} : [ G ; Γ ⊢g T ⤳* tyCTyp Δ k @ l' ] -> lr_j = jM /\ ModRel G Γ T T' l R.
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR];
    intros HN; first [exact (conj Hj HM) | agree; try ne_absurd].
Qed.

Lemma LR_inv_CTrm {Δ A k l'} : [ G ; Γ ⊢g T ⤳* tyCTrm Δ A k @ l' ] -> lr_j = jM /\ ModRel G Γ T T' l R.
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l k1 k2 l3 l4 A0 B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l k1 k2 l3 l4 A0 B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l k1 k2 l3 l4 A0 B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR];
    intros HN; first [exact (conj Hj HM) | agree; try ne_absurd].
Qed.

Lemma LR_inv_cpi {m1 U1 l'} : [ G ; Γ ⊢g T ⤳* tyCPi m1 U1 @ l' ] ->
  exists m2 U1' (instR : CInstRel G Γ),
    lr_j = jM /\ lequiv (gL G) l m1 /\ lequiv (gL G) m2 m1 /\ lwf (gL G) m1 /\
    [ G ; Γ ⊢g T' ⤳* tyCPi m2 U1' @ l ] /\
    [ gext G gdCtx ; Γ⟪S⟫ ⊢g U1 @ m1 ] /\ [ gext G gdCtx ; Γ⟪S⟫ ⊢g U1' @ m1 ] /\
    [ G ; Γ ⊢ tyCPi m1 U1 ≈ tyCPi m2 U1' @ m1 ] /\
    (forall (ρ : kwk G Γ) Δ Δ' (h : vp_ctx lr_vp (kw_G ρ) Δ Δ'),
        LR n rec (kw_G ρ) (kw_Δ ρ) (kbody ρ U1)⦃gsingle (GCtx Δ)⦄ (kbody ρ U1')⦃gsingle (GCtx Δ')⦄
           m1 (instR ρ Δ Δ' h)) /\
    releq R (CPiRel G Γ m1 m2 U1 U1' instR).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR];
    intros HN; try open_mod; agree; try ne_absurd.
  do 3 eexists; eauto 20.
Qed.

Lemma LR_inv_tpi {Θ m1 m2 U1 l'} : [ G ; Γ ⊢g T ⤳* tyTPi Θ m1 m2 U1 @ l' ] ->
  exists Θ' m3 m4 U1' (instR : TInstRel G Γ Θ m1),
    lr_j = jM /\ lequiv (gL G) l m2 /\ lequiv (gL G) m3 m1 /\ lequiv (gL G) m4 m2 /\
    lwf (gL G) m1 /\ lwf (gL G) m2 /\
    [ G ; Γ ⊢g T' ⤳* tyTPi Θ' m3 m4 U1' @ l ] /\ vp_ctx lr_vp G Θ Θ' /\
    [ gext G (gdTy Θ lD m1) ; Γ⟪S⟫ ⊢g U1 @ m2 ] /\ [ gext G (gdTy Θ' lD m3) ; Γ⟪S⟫ ⊢g U1' @ m4 ] /\
    [ G ; Γ ⊢ tyTPi Θ m1 m2 U1 ≈ tyTPi Θ' m3 m4 U1' @ m2 ] /\
    (forall (ρ : kwk G Γ) A A' (h : vp_ty lr_vp (kw_G ρ) Θ⟦kw_γ ρ⟧ A A' m1),
        LR n rec (kw_G ρ) (kw_Δ ρ) (kbody ρ U1)⦃gsingle (GTy A)⦄ (kbody ρ U1')⦃gsingle (GTy A')⦄
           m2 (instR ρ A A' h)) /\
    releq R (TPiRel G Γ Θ Θ' m1 m2 m3 m4 U1 U1' instR).
Proof using EL H.
  intros HN; revert HN.
  destruct H as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l n1 n2 T1 T1' instR R Hj Hn1 Hn2 Hnw HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' n1 n2 n3 n4 T1 T1' instR R Hj Hn1 Hn3 Hn4 Hnw1 Hnw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l k1 k2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 SA SA' sa sa' sb sb' R Hl Hl2 Hw HT HT' HSA HSAA Hsaa Hsbb HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l s1 s2 IA IA' ia ia' ib ib' RA R Hl Hl2 Hw HT HT' HIA HIAA Hiaa Hibb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l k1 k2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l q1 q2 WA WA' WN WN' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l q1 q2 WA WA' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ Hqs Hqt HR
                | G Γ T T' l wl1 wli1 wl2 wli2 wX wX' wA wA' wN wN' wO wO' wC wC' wm wm' widxR wdomR R Hl Hl2 Hwli2 Hw Hwwi
                    HT HT' HwX HwX' HwA HwA' HwN HwN' HwO HwO' HwC HwC' Hwm Hwm' HwXX HwAA HwNN HwOO HwCC Hwmm
                    widxAd Hwisym Hwistr wdomAd warAd wotAd wchAd wixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR];
    intros HN; try open_mod; agree; try ne_absurd.
  do 5 eexists; eauto 20.
Qed.

End Inversion.

End Irrelevance.
