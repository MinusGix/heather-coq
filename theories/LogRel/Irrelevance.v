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
Proof. now intros []. Qed.

(** Right-hand types related to the same left type are convertible. *)
Lemma right_conv {n rec G Γ T T' T'' l R R'} :
  LR n rec G Γ T T' l R -> LR n rec G Γ T T'' l R' -> [ G ; Γ ⊢g T' ≅ T'' @ l ].
Proof.
  intros H1 H2. apply escape_ty in H1 as (_ & _ & H1), H2 as (_ & _ & H2).
  apply geq_ty_sound in H1, H2. eapply eqty_trans; [apply eqty_sym, H1 | exact H2].
Qed.

(** ** Shapes: typed reductions of one type to two whnfs agree *)

Lemma red_whnf_agree {G Γ T W W' l l'} :
  [ G ; Γ ⊢g T ⤳* W @ l ] -> [ G ; Γ ⊢g T ⤳* W' @ l' ] -> whnf_ty W -> whnf_ty W' -> W = W'.
Proof. apply tyred_whnf_det. Qed.

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
Proof.
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
Proof.
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
Proof.
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
Proof.
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
Proof.
  intros HP Hinst t t' (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
  exists w, w'. refine (conj Hw (conj _ (conj Hnf (conj Hnf' (conj Heq (conj _ _)))))).
  - eapply tmred_conv; eauto using ge_typeof.
  - eapply geq_tm_conv; eauto.
  - intros ρ A A' h. apply (Hinst ρ A A' h), HK.
Qed.

(** ** Irrelevance *)

Theorem LR_irrel n rec G Γ T T' T'' l R R' :
  LR n rec G Γ T T' l R -> LR n rec G Γ T T'' l R' -> releq R R'.
Proof.
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
                  | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR];
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
                    | ? ? ? ? ? t1 t2 ? Hk Hk2 Hkn HTk HTk' HkR];
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
Qed.

(** ** Inversion by the left type's normal form *)

Section Inversion.
Context {n : nat} {rec : lvl -> RedRel} {G : gctx} {Γ : ctx} {T T' : ty} {l : lvl}
  {R : tm -> tm -> Prop} (H : LR n rec G Γ T T' l R).

Lemma LR_inv_nat {l'} : [ G ; Γ ⊢g T ⤳* tyNat @ l' ] ->
  lequiv (gL G) l lzero /\ [ G ; Γ ⊢g T' ⤳* tyNat @ l ] /\ releq R (NatRel G Γ).
Proof.
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
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR];
    intros HN; try open_mod; agree; try ne_absurd; auto.
Qed.

Lemma LR_inv_U {l1 l'} : [ G ; Γ ⊢g T ⤳* tyU l1 @ l' ] ->
  exists l2, lequiv (gL G) l (lsuc l1) /\ lequiv (gL G) l2 l1 /\ lmeasure l1 < n /\
    [ G ; Γ ⊢g T' ⤳* tyU l2 @ l ] /\ releq R (URel rec G Γ l1).
Proof.
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
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR];
    intros HN; try open_mod; agree; try ne_absurd; eauto 7.
Qed.

Lemma LR_inv_unit {l1 l'} : [ G ; Γ ⊢g T ⤳* tyUnit l1 @ l' ] ->
  exists l2, lequiv (gL G) l l1 /\ lequiv (gL G) l2 l1 /\ lwf (gL G) l1 /\
    [ G ; Γ ⊢g T' ⤳* tyUnit l2 @ l ] /\ releq R (UnitRel G Γ l1).
Proof.
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
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR];
    intros HN; try open_mod; agree; try ne_absurd; eauto 7.
Qed.

Lemma LR_inv_seq {l1 X x y l'} : [ G ; Γ ⊢g T ⤳* tySEq l1 X x y @ l' ] ->
  exists l2 X' x' y', lequiv (gL G) l l1 /\ lequiv (gL G) l2 l1 /\ lwf (gL G) l1 /\
    [ G ; Γ ⊢g T' ⤳* tySEq l2 X' x' y' @ l ] /\ [ G ; Γ ⊢g X @ l1 ] /\ [ G ; Γ ⊢ X ≈ X' @ l1 ] /\
    [ G ; Γ ⊢ x ≈ x' : X @ l1 ] /\ [ G ; Γ ⊢ y ≈ y' : X @ l1 ] /\
    releq R (SEqRel G Γ (tySEq l1 X x y) l1).
Proof.
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
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR];
    intros HN; try open_mod; agree; try ne_absurd; eauto 15.
Qed.

Lemma LR_inv_id {l1 X x y l'} : [ G ; Γ ⊢g T ⤳* tyId l1 X x y @ l' ] ->
  exists l2 X' x' y' RA, lequiv (gL G) l l1 /\ lequiv (gL G) l2 l1 /\ lwf (gL G) l1 /\
    [ G ; Γ ⊢g T' ⤳* tyId l2 X' x' y' @ l ] /\ [ G ; Γ ⊢g X @ l1 ] /\ [ G ; Γ ⊢ X ≈ X' @ l1 ] /\
    [ G ; Γ ⊢ x ≈ x' : X @ l1 ] /\ [ G ; Γ ⊢ y ≈ y' : X @ l1 ] /\
    LR n rec G Γ X X' l1 RA /\ RA x x' /\ RA y y' /\
    (forall u v, RA u v -> RA v u) /\ (forall u v w, RA u v -> RA v w -> RA u w) /\
    releq R (IdRel G Γ l1 X x y RA).
Proof.
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
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR];
    intros HN; try open_mod; agree; try ne_absurd; eauto 20.
Qed.

Lemma LR_inv_sempty {l1 l'} : [ G ; Γ ⊢g T ⤳* tySEmpty l1 @ l' ] ->
  exists l2, lequiv (gL G) l l1 /\ lequiv (gL G) l2 l1 /\ lwf (gL G) l1 /\
    [ G ; Γ ⊢g T' ⤳* tySEmpty l2 @ l ] /\ releq R (SEmptyRel G Γ l1).
Proof.
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
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR];
    intros HN; try open_mod; agree; try ne_absurd; eauto 7.
Qed.

(** The empty type (M12a). *)
Lemma LR_inv_empty {l1 l'} : [ G ; Γ ⊢g T ⤳* tyEmpty l1 @ l' ] ->
  exists l2, lequiv (gL G) l l1 /\ lequiv (gL G) l2 l1 /\ lwf (gL G) l1 /\
    [ G ; Γ ⊢g T' ⤳* tyEmpty l2 @ l ] /\ releq R (EmptyRel G Γ l1).
Proof.
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
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR];
    intros HN; try open_mod; agree; try ne_absurd; eauto 7.
Qed.


Lemma LR_inv_ne {V l'} : [ G ; Γ ⊢g T ⤳* V @ l' ] -> whne_ty V ->
  exists V', [ G ; Γ ⊢g T' ⤳* V' @ l ] /\ [ G ; Γ ⊢ V ~ V' @ l ] /\ releq R (NeRel G Γ V V' l).
Proof.
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
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR];
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
Proof.
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
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR];
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
Proof.
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
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR];
    intros HN; try open_mod; agree; try ne_absurd.
  do 6 eexists; refine (conj _ _); [split|]; eauto 20.
Qed.

Lemma LR_inv_CTyp {Δ k l'} : [ G ; Γ ⊢g T ⤳* tyCTyp Δ k @ l' ] -> lr_j = jM /\ ModRel G Γ T T' l R.
Proof.
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
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR];
    intros HN; first [exact (conj Hj HM) | agree; try ne_absurd].
Qed.

Lemma LR_inv_CTrm {Δ A k l'} : [ G ; Γ ⊢g T ⤳* tyCTrm Δ A k @ l' ] -> lr_j = jM /\ ModRel G Γ T T' l R.
Proof.
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
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR];
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
Proof.
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
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR];
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
Proof.
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
                | G Γ T T' l s1 s2 R Hl Hl2 Hw HT HT' HR];
    intros HN; try open_mod; agree; try ne_absurd.
  do 5 eexists; eauto 20.
Qed.

End Inversion.

End Irrelevance.
