(** * Irrelevance (ch. 7, Right Irrelevance)

    Two derivations relating the same left type [T] to [T'] and to [T'']
    give equivalent term relations.  The left type fixes the shape (weak
    head normal forms are unique), the universe level and the Π components;
    the right-hand types only enter through conversion. *)
From DeLaM.LogRel Require Export Basics.

Section Irrelevance.
Context `{E : GenericEq} `{EL : !GenericEqLaws}.

(** ** Declarative helpers at the instance's layer *)

Lemma wf_ty_wk {G Γ Δ r T l} :
  wkr r Δ Γ -> [ G ; Δ ⊢g ] -> [ G ; Γ ⊢g T @ l ] -> [ G ; Δ ⊢g T⟨r⟩ @ l ].
Proof. intros; eapply weakening_r; eauto using ge_typeof. Qed.

Lemma ext_wf_g {G Γ A l} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l -> [ G ; Γ ,, A @ l ⊢g ].
Proof. intros; apply wfc_ext; eauto using ctx_of_ty. Qed.

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
            | subst W2 ]
  end.

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
  (Hdom : forall Δ r Hr HΔ, releq (domR Δ r Hr HΔ) (domR' Δ r Hr HΔ))
  (Hcod : forall Δ r Hr HΔ a a' ha ha',
            releq (codR Δ r Hr HΔ a a' ha) (codR' Δ r Hr HΔ a a' ha')).

Lemma PiRel_dir t t' :
  PiRel G Γ l1 l2 l3 l4 A B A' B' domR codR t t' ->
  PiRel G Γ l1 l2 m3 m4 A B A'' B'' domR' codR' t t'.
Proof.
  intros (w & w' & Hw & Hw' & Hnf & Hnf' & Heq & Heq' & HK).
  exists w, w'. refine (conj Hw (conj _ (conj Hnf (conj Hnf' (conj Heq (conj _ _)))))).
  - eapply tmred_conv; eauto using ge_typeof.
  - eapply geq_tm_conv; eauto.
  - intros Δ r Hr HΔ a a' ha' la lb la' lb' A1 B1 A1' B1' H1 H2 H3 H4 HA1 HB1 HA1' HB1'.
    pose proof ((proj2 (Hdom Δ r Hr HΔ a a')) ha') as ha.
    apply (Hcod Δ r Hr HΔ a a' ha ha').
    (* the annotations of the right application, in terms of [A'], [B'] *)
    assert (HAr : [ G ; Δ ⊢g A⟨r⟩ @ l1 ]) by exact (wf_ty_wk Hr HΔ HA).
    assert (HA'r : [ G ; Δ ⊢g A'⟨r⟩ @ l1 ]) by exact (wf_ty_wk Hr HΔ HA').
    assert (HA''r : [ G ; Δ ⊢g A''⟨r⟩ @ l1 ]) by exact (wf_ty_wk Hr HΔ HA'').
    assert (HΔA : [ G ; Δ ,, A⟨r⟩ @ l1 ⊢g ]) by now apply ext_wf_g.
    assert (HΔA' : [ G ; Δ ,, A'⟨r⟩ @ l1 ⊢g ]) by now apply ext_wf_g.
    assert (HΔA'' : [ G ; Δ ,, A''⟨r⟩ @ l1 ⊢g ]) by now apply ext_wf_g.
    assert (Hrr : wkr (rlift r) (Δ ,, A⟨r⟩ @ l1) (Γ ,, A @ l1)) by now constructor.
    assert (E1 : [ G ; Δ ⊢ A⟨r⟩ ≈ A'⟨r⟩ @ l1 ]) by exact (geq_ty_wk Hr HΔ HAA').
    assert (E2 : [ G ; Δ ⊢ A⟨r⟩ ≈ A''⟨r⟩ @ l1 ]) by exact (geq_ty_wk Hr HΔ HAA'').
    assert (E3 : [ G ; Δ ,, A⟨r⟩ @ l1 ⊢ B'⟨rlift r⟩ ≈ B''⟨rlift r⟩ @ l2 ]).
    { eapply geq_ty_trans; [apply geq_ty_sym, (geq_ty_wk Hrr HΔA HBB')
                            | exact (geq_ty_wk Hrr HΔA HBB'')]. }
    refine (HK Δ r Hr HΔ a a' ha la lb la' lb' A1 B1 A1' B1' H1 H2 H3 H4 HA1 HB1 _ _).
    + eapply geq_ty_trans; [|exact HA1'].
      eapply geq_ty_trans; [apply geq_ty_sym, E1 | exact E2].
    + (* move [B'⟨r⟩ ≈ B''⟨r⟩] to [Δ, A''⟨r⟩], compose, move to [Δ, A'⟨r⟩] *)
      assert (E4 : [ G ; Δ ,, A''⟨r⟩ @ l1 ⊢ B'⟨rlift r⟩ ≈ B1' @ l2 ]).
      { eapply geq_ty_trans; [|exact HB1'].
        eapply geq_ty_ctxconv; [apply geq_ty_sound, E2 | now apply lequiv_refl | exact HΔA'' | exact E3]. }
      eapply geq_ty_ctxconv; [| now apply lequiv_refl | exact HΔA' | exact E4].
      apply geq_ty_sound. eapply geq_ty_trans; [apply geq_ty_sym, E2 | exact E1].
Qed.

End PiDir.

(** ** Irrelevance *)

Theorem LR_irrel n rec G Γ T T' T'' l R R' :
  LR n rec G Γ T T' l R -> LR n rec G Γ T T'' l R' -> releq R R'.
Proof.
  intros H1; revert T'' R'.
  induction H1 as [G Γ T T' l Hl HT HT'
                  | G Γ T T' l l1 l2 Hl Hl2 Hn HT HT'
                  | G Γ T T' l V V' HT HT' HV
                  | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR Hl Hl3 Hl4 Hw1 Hw2 HT HT'
                      HA HA' HB HB' HAA HBB domAd IHdom codAd IHcod];
    intros T'' R' H2;
    inversion H2 as [? ? ? ? ? Hk HTk HTk'
                    | ? ? ? ? ? k1 k2 Hk Hk2 Hkn HTk HTk'
                    | ? ? ? ? ? W W' HTk HTk' HW
                    | ? ? ? ? ? k1 k2 k3 k4 C D C' D' domR' codR' Hk Hk3 Hk4 Hkw1 Hkw2 HTk HTk'
                        HC HC' HD HD' HCC HDD domAd' codAd'];
    subst; try (agree; try ne_absurd).
  (* same shape *)
  - intros ??; reflexivity.
  - intros ??; reflexivity.
  - assert (HVV : [ G ; Γ ⊢g V' ≅ W' @ l ]).
    { eapply eqty_trans; [apply eqty_sym|]; apply geq_ty_sound, gne_ty_geq; eassumption. }
    intros t t'; split; apply NeRel_conv; [exact HVV | now apply eqty_sym].
  - match goal with
    | |- releq (PiRel _ _ ?l1 ?l2 ?l3 ?l4 ?A ?B ?A' ?B' ?dR ?cR)
               (PiRel _ _ _ _ ?k3 ?k4 _ _ ?C' ?D' ?dR' ?cR') =>
        assert (HP : [ G ; Γ ⊢g tyPi l3 l4 A' B' ≅ tyPi k3 k4 C' D' @ lmax l1 l2 ])
          by (eapply (eqty_trans _ _ _ _ (tyPi l1 l2 A B)); [apply eqty_sym|];
              apply geq_ty_sound, geq_ty_pi; eauto using lequiv_sym);
        assert (Hdom : forall Δ r Hr HΔ, releq (dR Δ r Hr HΔ) (dR' Δ r Hr HΔ))
          by (intros; match goal with IH : forall Δ r Hr HΔ T'' R', _ -> releq (dR _ _ _ _) _ |- _ =>
                                          eapply IH end; eauto);
        assert (Hcod : forall Δ r Hr HΔ a a' ha ha',
                   releq (cR Δ r Hr HΔ a a' ha) (cR' Δ r Hr HΔ a a' ha'))
          by (intros; match goal with IH : forall Δ r Hr HΔ a a' ha T'' R', _ -> releq (cR _ _ _ _ _ _ _) _ |- _ =>
                                          eapply IH end; eauto)
    end.
    intros t t'; split.
    + eapply PiRel_dir; eassumption.
    + eapply PiRel_dir; try eassumption.
      * now apply eqty_sym.
      * intros; intros ??; symmetry; apply Hdom.
      * intros; intros ??; symmetry; apply Hcod.
Qed.

End Irrelevance.
