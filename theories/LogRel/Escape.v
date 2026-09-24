(** * Escape: related types and terms are well formed and generically equal *)
From DeLaM.LogRel Require Export Def.

Section Escape.
Context `{E : GenericEq} `{EL : !GenericEqLaws}.

Lemma ge_typeof : typeof ge_layer = ge_layer.
Proof. apply compt_typeof_self, ge_compt. Qed.
Lemma ge_notV : ge_layer <> lV.
Proof. destruct ge_compt as [-> | ->]; discriminate. Qed.

(** ** Declarative conversion helpers at the instance's layer *)

Lemma ctx_of_ty {G Γ T l} : [ G ; Γ ⊢g T @ l ] -> [ G ; Γ ⊢g ].
Proof. intros H. pose proof (proj1 (proj2 (proj2 ctx_extract)) _ _ _ _ _ H) as Hc.
       now rewrite ge_typeof in Hc. Qed.
Lemma ctx_of_tm {G Γ t T l} : [ G ; Γ ⊢g t : T @ l ] -> [ G ; Γ ⊢g ].
Proof. intros H. pose proof (proj1 (proj2 (proj2 (proj2 ctx_extract))) _ _ _ _ _ _ H) as Hc.
       now rewrite ge_typeof in Hc. Qed.

Lemma conv_tm {G Γ t T T' l l'} :
  [ G ; Γ ⊢g t : T @ l ] -> [ G ; Γ ⊢g T' ≅ T @ l' ] -> lequiv (gL G) l' l ->
  [ G ; Γ ⊢g t : T' @ l' ].
Proof.
  intros Ht HT Hl. eapply wf_conv; [eapply wf_lconv; eauto|]. now rewrite ge_typeof.
Qed.

Lemma conv_geq_tm {G Γ t t' T T' l l'} :
  [ G ; Γ ⊢ t ≈ t' : T @ l ] -> [ G ; Γ ⊢g T ≅ T' @ l' ] -> lequiv (gL G) l' l ->
  [ G ; Γ ⊢ t ≈ t' : T' @ l' ].
Proof.
  intros Ht HT Hl. eapply geq_tm_conv; [eapply geq_tm_lconv; eauto|]. auto.
Qed.

Lemma tyred_ctx {G Γ T W l} : [ G ; Γ ⊢g T ⤳* W @ l ] -> [ G ; Γ ⊢g ].
Proof. intros []; eauto using ctx_of_ty. Qed.

(** ** Escape for types *)

Theorem escape_ty n rec G Γ T T' l R :
  LR n rec G Γ T T' l R ->
  [ G ; Γ ⊢g T @ l ] /\ [ G ; Γ ⊢g T' @ l ] /\ [ G ; Γ ⊢ T ≈ T' @ l ].
Proof.
  destruct 1 as [G Γ T T' l Hl HT HT'
                | G Γ T T' l l0 l1 l2 Hl Hl1 Hl2 Hn HT HT'
                | G Γ T T' l V V' HT HT' HV
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR Hl Hl3 Hl4 Hw1 Hw2 HT HT'
                    HA HA' HB HB' HP domAd codAd].
  all: split; [apply HT | split; [apply HT' | eapply geq_ty_exp; [exact HT | exact HT' |]]].
  - eapply geq_ty_lconv; [|exact Hl]. eapply geq_ty_nat, tyred_ctx, HT.
  - eapply geq_ty_lconv; [eapply geq_ty_U; [eapply tyred_ctx, HT|]|].
    + eapply lequiv_trans; [exact Hl1|]. now apply lequiv_sym.
    + eapply lequiv_trans; [exact Hl|]. apply lequiv_suc. now apply lequiv_sym.
  - now apply gne_ty_geq.
  - eapply geq_ty_lconv; eauto.
Qed.

(** ** Escape for terms *)

Theorem escape_tm n rec G Γ T T' l R :
  LR n rec G Γ T T' l R -> forall t t', R t t' ->
  [ G ; Γ ⊢g t : T @ l ] /\ [ G ; Γ ⊢g t' : T @ l ] /\ [ G ; Γ ⊢ t ≈ t' : T @ l ].
Proof.
  destruct 1 as [G Γ T T' l Hl HT HT'
                | G Γ T T' l l0 l1 l2 Hl Hl1 Hl2 Hn HT HT'
                | G Γ T T' l V V' HT HT' HV
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR Hl Hl3 Hl4 Hw1 Hw2 HT HT'
                    HA HA' HB HB' HP domAd codAd];
    intros t t' Htt.
  - (* Nat *)
    destruct Htt as [t t' w w' Hw Hw' Heq _].
    assert (HTN : [ G ; Γ ⊢g T ≅ tyNat @ l ]) by apply HT.
    assert (Hl' : lequiv (gL G) l lzero) by exact Hl.
    repeat split.
    + eapply conv_tm; [apply Hw | exact HTN | exact Hl'].
    + eapply conv_tm; [apply Hw' | exact HTN | exact Hl'].
    + eapply conv_geq_tm; [eapply geq_tm_exp; eauto | apply eqty_sym, HTN | exact Hl'].
  - (* U *)
    destruct Htt as (w & w' & Hw & Hw' & _ & _ & Heq & _).
    assert (HTU : [ G ; Γ ⊢g T ≅ tyU l0 @ l ]).
    { eapply eqty_trans; [apply HT|]. eapply eqty_lconv; [eapply eqty_U|].
      - exact ge_notV.
      - rewrite ge_typeof. eapply tyred_ctx, HT.
      - exact Hl1.
      - eapply lequiv_trans; [exact Hl|]. apply lequiv_suc. now apply lequiv_sym. }
    repeat split.
    + eapply conv_tm; [apply Hw | exact HTU | exact Hl].
    + eapply conv_tm; [apply Hw' | exact HTU | exact Hl].
    + eapply conv_geq_tm; [eapply geq_tm_exp; eauto | apply eqty_sym, HTU | exact Hl].
  - (* neutral *)
    destruct Htt as (ν & ν' & Hν & Hν' & Hne & Hne').
    assert (HTV : [ G ; Γ ⊢g T ≅ V @ l ]) by apply HT.
    assert (HVV' : [ G ; Γ ⊢g V ≅ V' @ l ]) by (now apply geq_ty_sound, gne_ty_geq).
    assert (Hν'' : [ G ; Γ ⊢g t' ⤳* ν' : V @ l ]).
    { eapply tmred_conv; [apply ge_typeof | exact Hν' | now apply eqty_sym]. }
    repeat split.
    + eapply wf_conv; [apply Hν | now rewrite ge_typeof].
    + eapply wf_conv; [apply Hν'' | now rewrite ge_typeof].
    + eapply geq_tm_conv; [eapply geq_tm_exp; [exact Hν | exact Hν'' | now apply gne_tm_geq]
                          | now apply eqty_sym].
  - (* Π *)
    destruct Htt as (w & w' & Hw & Hw' & _ & _ & Heq & _ & _).
    assert (HTP : [ G ; Γ ⊢g T ≅ tyPi l1 l2 A B @ l ]) by apply HT.
    assert (HPP : [ G ; Γ ⊢g tyPi l1 l2 A B ≅ tyPi l3 l4 A' B' @ lmax l1 l2 ])
      by now apply geq_ty_sound.
    assert (Hw'' : [ G ; Γ ⊢g t' ⤳* w' : tyPi l1 l2 A B @ lmax l1 l2 ]).
    { eapply tmred_conv; [apply ge_typeof | exact Hw' | now apply eqty_sym]. }
    repeat split.
    + eapply conv_tm; [apply Hw | exact HTP | exact Hl].
    + eapply conv_tm; [apply Hw'' | exact HTP | exact Hl].
    + eapply conv_geq_tm; [eapply geq_tm_exp; [exact Hw | exact Hw'' | exact Heq]
                          | apply eqty_sym, HTP | exact Hl].
Qed.

End Escape.
