(** * Escape: related types and terms are well formed and generically equal *)
From DeLaM.LogRel Require Export Def.

Section Escape.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

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

(** ** Escape for contextual types *)

Lemma ModRel_escape_ty {G Γ T T' l R} : ModRel G Γ T T' l R ->
  [ G ; Γ ⊢g T @ l ] /\ [ G ; Γ ⊢g T' @ l ] /\ [ G ; Γ ⊢ T ≈ T' @ l ].
Proof.
  destruct 1 as [T T' l Δ Δ' k k' R Hl Hk HT HT' HΔ Hgeq HR
                | T T' l Δ Δ' A A' k k' R Hl Hk HT HT' HΔ HA HA' Hgeq HR].
  all: split; [apply HT | split; [apply HT' | eapply geq_ty_exp; [exact HT | exact HT' |]]].
  all: eapply geq_ty_lconv; [exact Hgeq | exact Hl].
Qed.

(** The shape shared by the two term relations of contextual types. *)
Lemma box_escape_tm {G Γ T C C' l t t' w w'} :
  [ G ; Γ ⊢g T ≅ C @ l ] -> lequiv (gL G) l lzero -> [ G ; Γ ⊢ C ≈ C' @ lzero ] ->
  [ G ; Γ ⊢g t ⤳* w : C @ lzero ] -> [ G ; Γ ⊢g t' ⤳* w' : C' @ lzero ] ->
  [ G ; Γ ⊢ w ≈ w' : C @ lzero ] ->
  [ G ; Γ ⊢g t : T @ l ] /\ [ G ; Γ ⊢g t' : T @ l ] /\ [ G ; Γ ⊢ t ≈ t' : T @ l ].
Proof.
  intros HTC Hl HCC Hw Hw' Heq.
  assert (Hw'' : [ G ; Γ ⊢g t' ⤳* w' : C @ lzero ]).
  { eapply tmred_conv; [apply ge_typeof | exact Hw' | apply eqty_sym, geq_ty_sound, HCC]. }
  repeat split.
  - eapply conv_tm; [apply Hw | exact HTC | exact Hl].
  - eapply conv_tm; [apply Hw'' | exact HTC | exact Hl].
  - eapply conv_geq_tm; [eapply geq_tm_exp; eauto | apply eqty_sym, HTC | exact Hl].
Qed.

Lemma ModRel_escape_tm {G Γ T T' l R} : ModRel G Γ T T' l R -> forall t t', R t t' ->
  [ G ; Γ ⊢g t : T @ l ] /\ [ G ; Γ ⊢g t' : T @ l ] /\ [ G ; Γ ⊢ t ≈ t' : T @ l ].
Proof.
  destruct 1 as [T T' l Δ Δ' k k' R Hl Hk HT HT' HΔ Hgeq HR
                | T T' l Δ Δ' A A' k k' R Hl Hk HT HT' HΔ HA HA' Hgeq HR];
    intros t t' Htt; apply HR in Htt; destruct Htt as (w & w' & Hw & Hw' & Heq & _ & _ & _).
  all: exact (box_escape_tm (tyred_eq _ _ _ _ _ _ HT) Hl Hgeq Hw Hw' Heq).
Qed.

(** ** Escape for types *)

Theorem escape_ty n rec G Γ T T' l R :
  LR n rec G Γ T T' l R ->
  [ G ; Γ ⊢g T @ l ] /\ [ G ; Γ ⊢g T' @ l ] /\ [ G ; Γ ⊢ T ≈ T' @ l ].
Proof.
  destruct 1 as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l l1 l2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R Hl Hl3 Hl4 Hw1 Hw2 HT HT'
                    HA HA' HB HB' HAA HBB domAd codAd HR
                | G Γ T T' l R Hj HM].
  all: try solve [exact (ModRel_escape_ty HM)].
  all: split; [apply HT | split; [apply HT' | eapply geq_ty_exp; [exact HT | exact HT' |]]].
  - eapply geq_ty_lconv; [|exact Hl]. eapply geq_ty_nat, tyred_ctx, HT.
  - eapply geq_ty_lconv; [eapply geq_ty_U; [eapply tyred_ctx, HT|]|].
    + now apply lequiv_sym.
    + exact Hl.
  - now apply gne_ty_geq.
  - eapply geq_ty_lconv; [|exact Hl]. apply geq_ty_pi; auto using lequiv_sym.
Qed.

(** ** Escape for terms *)

Theorem escape_tm n rec G Γ T T' l R :
  LR n rec G Γ T T' l R -> forall t t', R t t' ->
  [ G ; Γ ⊢g t : T @ l ] /\ [ G ; Γ ⊢g t' : T @ l ] /\ [ G ; Γ ⊢ t ≈ t' : T @ l ].
Proof.
  destruct 1 as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l l1 l2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R Hl Hl3 Hl4 Hw1 Hw2 HT HT'
                    HA HA' HB HB' HAA HBB domAd codAd HR
                | G Γ T T' l R Hj HM];
    intros t t' Htt; first [exact (ModRel_escape_tm HM _ _ Htt) | apply HR in Htt].
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
    assert (HTU : [ G ; Γ ⊢g T ≅ tyU l1 @ l ]) by apply HT.
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
      by (apply geq_ty_sound, geq_ty_pi; auto using lequiv_sym).
    assert (Hw'' : [ G ; Γ ⊢g t' ⤳* w' : tyPi l1 l2 A B @ lmax l1 l2 ]).
    { eapply tmred_conv; [apply ge_typeof | exact Hw' | now apply eqty_sym]. }
    repeat split.
    + eapply conv_tm; [apply Hw | exact HTP | exact Hl].
    + eapply conv_tm; [apply Hw'' | exact HTP | exact Hl].
    + eapply conv_geq_tm; [eapply geq_tm_exp; [exact Hw | exact Hw'' | exact Heq]
                          | apply eqty_sym, HTP | exact Hl].
Qed.

(** ** Local weakening at the instance's layer *)

Lemma wf_ty_wkr {G Γ Δ r T l} :
  wkr r Δ Γ -> [ G ; Δ ⊢g ] -> [ G ; Γ ⊢g T @ l ] -> [ G ; Δ ⊢g T⟨r⟩ @ l ].
Proof. intros; eapply weakening_r; eauto using ge_typeof. Qed.
Lemma wf_tm_wkr {G Γ Δ r t T l} :
  wkr r Δ Γ -> [ G ; Δ ⊢g ] -> [ G ; Γ ⊢g t : T @ l ] -> [ G ; Δ ⊢g t⟨r⟩ : T⟨r⟩ @ l ].
Proof. intros; eapply weakening_r; eauto using ge_typeof. Qed.
Lemma eqty_wkr {G Γ Δ r T T' l} :
  wkr r Δ Γ -> [ G ; Δ ⊢g ] -> [ G ; Γ ⊢g T ≅ T' @ l ] -> [ G ; Δ ⊢g T⟨r⟩ ≅ T'⟨r⟩ @ l ].
Proof. intros; eapply weakening_r; eauto using ge_typeof. Qed.

(** The Kripke index is OPE data; the generic laws take its renaming. *)
Lemma wf_ty_wk {G Γ Δ} {ρ : wk} {T l} :
  ρ : Δ ≤ Γ -> [ G ; Δ ⊢g ] -> [ G ; Γ ⊢g T @ l ] -> [ G ; Δ ⊢g T⟨ρ⟩ @ l ].
Proof. intros Hρ; apply wf_ty_wkr, wk_wf_wkr, Hρ. Qed.
Lemma wf_tm_wk {G Γ Δ} {ρ : wk} {t T l} :
  ρ : Δ ≤ Γ -> [ G ; Δ ⊢g ] -> [ G ; Γ ⊢g t : T @ l ] -> [ G ; Δ ⊢g t⟨ρ⟩ : T⟨ρ⟩ @ l ].
Proof. intros Hρ; apply wf_tm_wkr, wk_wf_wkr, Hρ. Qed.
Lemma eqty_wk {G Γ Δ} {ρ : wk} {T T' l} :
  ρ : Δ ≤ Γ -> [ G ; Δ ⊢g ] -> [ G ; Γ ⊢g T ≅ T' @ l ] -> [ G ; Δ ⊢g T⟨ρ⟩ ≅ T'⟨ρ⟩ @ l ].
Proof. intros Hρ; apply eqty_wkr, wk_wf_wkr, Hρ. Qed.
Lemma geq_ty_wk' {G Γ Δ} {ρ : wk} {T T' l} :
  ρ : Δ ≤ Γ -> [ G ; Δ ⊢g ] -> [ G ; Γ ⊢ T ≈ T' @ l ] -> [ G ; Δ ⊢ T⟨ρ⟩ ≈ T'⟨ρ⟩ @ l ].
Proof. intros Hρ; apply geq_ty_wk, wk_wf_wkr, Hρ. Qed.
Lemma gne_ty_wk' {G Γ Δ} {ρ : wk} {V V' l} :
  ρ : Δ ≤ Γ -> [ G ; Δ ⊢g ] -> [ G ; Γ ⊢ V ~ V' @ l ] -> [ G ; Δ ⊢ V⟨ρ⟩ ~ V'⟨ρ⟩ @ l ].
Proof. intros Hρ; apply gne_ty_wk, wk_wf_wkr, Hρ. Qed.
Lemma geq_tm_wk' {G Γ Δ} {ρ : wk} {t t' T l} :
  ρ : Δ ≤ Γ -> [ G ; Δ ⊢g ] -> [ G ; Γ ⊢ t ≈ t' : T @ l ] -> [ G ; Δ ⊢ t⟨ρ⟩ ≈ t'⟨ρ⟩ : T⟨ρ⟩ @ l ].
Proof. intros Hρ; apply geq_tm_wk, wk_wf_wkr, Hρ. Qed.
Lemma gne_tm_wk' {G Γ Δ} {ρ : wk} {t t' T l} :
  ρ : Δ ≤ Γ -> [ G ; Δ ⊢g ] -> [ G ; Γ ⊢ t ~ t' : T @ l ] -> [ G ; Δ ⊢ t⟨ρ⟩ ~ t'⟨ρ⟩ : T⟨ρ⟩ @ l ].
Proof. intros Hρ; apply gne_tm_wk, wk_wf_wkr, Hρ. Qed.
Lemma tyred_wk' {G Γ Δ} {ρ : wk} {T W l} :
  ρ : Δ ≤ Γ -> [ G ; Δ ⊢g ] -> [ G ; Γ ⊢g T ⤳* W @ l ] -> [ G ; Δ ⊢g T⟨ρ⟩ ⤳* W⟨ρ⟩ @ l ].
Proof. intros Hρ HΔ H; eapply tyred_wk; eauto using ge_typeof, wk_wf_wkr. Qed.
Lemma tmred_wk' {G Γ Δ} {ρ : wk} {t w T l} :
  ρ : Δ ≤ Γ -> [ G ; Δ ⊢g ] -> [ G ; Γ ⊢g t ⤳* w : T @ l ] ->
  [ G ; Δ ⊢g t⟨ρ⟩ ⤳* w⟨ρ⟩ : T⟨ρ⟩ @ l ].
Proof. intros Hρ HΔ H; eapply tmred_wk; eauto using ge_typeof, wk_wf_wkr. Qed.

Lemma wkr_lift {Γ Δ} {ρ : wk} {A l} :
  ρ : Δ ≤ Γ -> wkr (rlift ρ) (Δ ,, A⟨ρ⟩ @ l) (Γ ,, A @ l).
Proof. intros Hρ; constructor; now apply wk_wf_wkr. Qed.

Lemma ext_wf_g {G Γ A l} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l -> [ G ; Γ ,, A @ l ⊢g ].
Proof. intros; apply wfc_ext; eauto using ctx_of_ty. Qed.

(** ** Global weakening of the generic relations, as [⟦γ⟧] *)

Ltac gwa_generic :=
  intros Hγ HG H; match type of Hγ with gwk_ok ?g _ _ => destruct g end; cbn [gwa];
    [rewrite (gwk_ok_id_inv Hγ); exact H | first [ exact (gne_ty_gwk Hγ HG H) | exact (geq_ty_gwk Hγ HG H)
                                          | exact (gne_tm_gwk Hγ HG H) | exact (geq_tm_gwk Hγ HG H) ] ..].

Lemma gne_ty_gwa {γ G' G Γ V V' l} : gwk_ok γ G' G -> [ ⊢ G' ] ->
  [ G ; Γ ⊢ V ~ V' @ l ] -> [ G' ; Γ⟦γ⟧ ⊢ V⟦γ⟧ ~ V'⟦γ⟧ @ l ].
Proof. gwa_generic. Qed.
Lemma geq_ty_gwa {γ G' G Γ T T' l} : gwk_ok γ G' G -> [ ⊢ G' ] ->
  [ G ; Γ ⊢ T ≈ T' @ l ] -> [ G' ; Γ⟦γ⟧ ⊢ T⟦γ⟧ ≈ T'⟦γ⟧ @ l ].
Proof. gwa_generic. Qed.
Lemma gne_tm_gwa {γ G' G Γ t t' T l} : gwk_ok γ G' G -> [ ⊢ G' ] ->
  [ G ; Γ ⊢ t ~ t' : T @ l ] -> [ G' ; Γ⟦γ⟧ ⊢ t⟦γ⟧ ~ t'⟦γ⟧ : T⟦γ⟧ @ l ].
Proof. gwa_generic. Qed.
Lemma geq_tm_gwa {γ G' G Γ t t' T l} : gwk_ok γ G' G -> [ ⊢ G' ] ->
  [ G ; Γ ⊢ t ≈ t' : T @ l ] -> [ G' ; Γ⟦γ⟧ ⊢ t⟦γ⟧ ≈ t'⟦γ⟧ : T⟦γ⟧ @ l ].
Proof. gwa_generic. Qed.

Lemma gwa_tyred {γ G' G i Γ T W l} : gwk_ok γ G' G -> [ ⊢ G' ] ->
  [ G ; Γ ⊢[ i ] T ⤳* W @ l ] -> [ G' ; Γ⟦γ⟧ ⊢[ i ] T⟦γ⟧ ⤳* W⟦γ⟧ @ l ].
Proof. intros Hγ HG []; split; eauto using gwa_ty, reds_ty_gwa, gwa_eqty. Qed.
Lemma gwa_tmred {γ G' G i Γ t w T l} : gwk_ok γ G' G -> [ ⊢ G' ] ->
  [ G ; Γ ⊢[ i ] t ⤳* w : T @ l ] -> [ G' ; Γ⟦γ⟧ ⊢[ i ] t⟦γ⟧ ⤳* w⟦γ⟧ : T⟦γ⟧ @ l ].
Proof. intros Hγ HG []; split; eauto using gwa_tm, reds_gwa, gwa_eqtm. Qed.

(** ** Kripke weakenings *)

Lemma kw_gL {G Γ} (ρ : kwk G Γ) : gL (kw_G ρ) = gL G.
Proof. exact (proj1 (kw_gok ρ)). Qed.
Lemma kw_glob {G Γ} (ρ : kwk G Γ) : [ ⊢ kw_G ρ ].
Proof. exact (ctx_glob _ _ _ (kw_ctx ρ)). Qed.
Lemma kw_lequiv {G Γ} (ρ : kwk G Γ) {l l'} : lequiv (gL G) l l' -> lequiv (gL (kw_G ρ)) l l'.
Proof. now rewrite kw_gL. Qed.
Lemma kw_lwf {G Γ} (ρ : kwk G Γ) {l} : lwf (gL G) l -> lwf (gL (kw_G ρ)) l.
Proof. now rewrite kw_gL. Qed.

Section Kw.
Context {G : gctx} {Γ : ctx} (ρ : kwk G Γ).
Local Notation Hγ := (kw_gok ρ).
Local Notation HG' := (kw_glob ρ).
Local Notation Hr := (kw_wf ρ).
Local Notation HΔ := (kw_ctx ρ).

Lemma kw_ty {T l} : [ G ; Γ ⊢g T @ l ] -> [ kw_G ρ ; kw_Δ ρ ⊢g kty ρ T @ l ].
Proof. intros H. exact (wf_ty_wk Hr HΔ (gwa_ty Hγ HG' H)). Qed.
Lemma kw_tm {t T l} : [ G ; Γ ⊢g t : T @ l ] -> [ kw_G ρ ; kw_Δ ρ ⊢g ktm ρ t : kty ρ T @ l ].
Proof. intros H. exact (wf_tm_wk Hr HΔ (gwa_tm Hγ HG' H)). Qed.
Lemma kw_eqty {T T' l} : [ G ; Γ ⊢g T ≅ T' @ l ] ->
  [ kw_G ρ ; kw_Δ ρ ⊢g kty ρ T ≅ kty ρ T' @ l ].
Proof. intros H. exact (eqty_wk Hr HΔ (gwa_eqty Hγ HG' H)). Qed.
Lemma kw_geq_ty {T T' l} : [ G ; Γ ⊢ T ≈ T' @ l ] -> [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ T ≈ kty ρ T' @ l ].
Proof. intros H. exact (geq_ty_wk' Hr HΔ (geq_ty_gwa Hγ HG' H)). Qed.
Lemma kw_gne_ty {V V' l} : [ G ; Γ ⊢ V ~ V' @ l ] -> [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ V ~ kty ρ V' @ l ].
Proof. intros H. exact (gne_ty_wk' Hr HΔ (gne_ty_gwa Hγ HG' H)). Qed.
Lemma kw_geq_tm {t t' T l} : [ G ; Γ ⊢ t ≈ t' : T @ l ] ->
  [ kw_G ρ ; kw_Δ ρ ⊢ ktm ρ t ≈ ktm ρ t' : kty ρ T @ l ].
Proof. intros H. exact (geq_tm_wk' Hr HΔ (geq_tm_gwa Hγ HG' H)). Qed.
Lemma kw_gne_tm {t t' T l} : [ G ; Γ ⊢ t ~ t' : T @ l ] ->
  [ kw_G ρ ; kw_Δ ρ ⊢ ktm ρ t ~ ktm ρ t' : kty ρ T @ l ].
Proof. intros H. exact (gne_tm_wk' Hr HΔ (gne_tm_gwa Hγ HG' H)). Qed.
Lemma kw_tyred {T W l} : [ G ; Γ ⊢g T ⤳* W @ l ] -> [ kw_G ρ ; kw_Δ ρ ⊢g kty ρ T ⤳* kty ρ W @ l ].
Proof. intros H. exact (tyred_wk' Hr HΔ (gwa_tyred Hγ HG' H)). Qed.
Lemma kw_tmred {t w T l} : [ G ; Γ ⊢g t ⤳* w : T @ l ] ->
  [ kw_G ρ ; kw_Δ ρ ⊢g ktm ρ t ⤳* ktm ρ w : kty ρ T @ l ].
Proof. intros H. exact (tmred_wk' Hr HΔ (gwa_tmred Hγ HG' H)). Qed.

(** Under one local binder. *)
Lemma kw_ext {A l} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l -> [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ⊢g ].
Proof. intros HA Hl. apply ext_wf_g; [now apply kw_ty | now apply kw_lwf]. Qed.

Lemma kw_wkr_l {A l} : wkr (rlift (kw_r ρ)) (kw_Δ ρ ,, kty ρ A @ l) ((Γ ,, A @ l)⟦kw_γ ρ⟧).
Proof. rewrite gwa_cext. exact (wkr_lift Hr). Qed.

Lemma kw_ty_l {A l B l'} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l ->
  [ G ; Γ ,, A @ l ⊢g B @ l' ] -> [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ⊢g ktyl ρ B @ l' ].
Proof.
  intros HA Hl H. exact (wf_ty_wkr kw_wkr_l (kw_ext HA Hl) (gwa_ty Hγ HG' H)).
Qed.
Lemma kw_tm_l {A l t T l'} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l ->
  [ G ; Γ ,, A @ l ⊢g t : T @ l' ] -> [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ⊢g ktml ρ t : ktyl ρ T @ l' ].
Proof.
  intros HA Hl H. exact (wf_tm_wkr kw_wkr_l (kw_ext HA Hl) (gwa_tm Hγ HG' H)).
Qed.
Lemma kw_geq_ty_l {A l B B' l'} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l ->
  [ G ; Γ ,, A @ l ⊢ B ≈ B' @ l' ] ->
  [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ⊢ ktyl ρ B ≈ ktyl ρ B' @ l' ].
Proof.
  intros HA Hl H. exact (geq_ty_wk kw_wkr_l (kw_ext HA Hl) (geq_ty_gwa Hγ HG' H)).
Qed.

End Kw.

(** ** Composition of Kripke weakenings on syntax *)

Lemma ren_wk_comp_ty (T : ty) (ρ ρ' : wk) : T⟨ρ⟩⟨ρ'⟩ = T⟨wk_comp ρ' ρ⟩.
Proof. apply ren_ren_ty; intros; now rewrite rlk_wk_comp. Qed.
Lemma ren_wk_comp (t : tm) (ρ ρ' : wk) : t⟨ρ⟩⟨ρ'⟩ = t⟨wk_comp ρ' ρ⟩.
Proof. apply ren_ren; intros; now rewrite rlk_wk_comp. Qed.
Lemma ren_wk_comp_lift_ty (T : ty) (ρ ρ' : wk) :
  T⟨rlift ρ⟩⟨rlift ρ'⟩ = T⟨rlift (wk_comp ρ' ρ)⟩.
Proof.
  apply ren_ren_ty; intros [|n]; rewrite !rlk_rlift; auto. now rewrite rlk_wk_comp.
Qed.

Lemma kty_comp {G Γ} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) T :
  kty (kw_comp ρ ρ') T = kty ρ' (kty ρ T).
Proof. unfold kty; cbn. now rewrite gwa_ren_ty, gwa_comp_ty, ren_wk_comp_ty. Qed.
Lemma ktm_comp {G Γ} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) t :
  ktm (kw_comp ρ ρ') t = ktm ρ' (ktm ρ t).
Proof. unfold ktm; cbn. now rewrite gwa_ren, gwa_comp_tm, ren_wk_comp. Qed.
Lemma ktyl_comp {G Γ} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) T :
  ktyl (kw_comp ρ ρ') T = ktyl ρ' (ktyl ρ T).
Proof. unfold ktyl; cbn. now rewrite gwa_ren_ty, gwa_comp_ty, ren_wk_comp_lift_ty. Qed.

(** ** Kripke weakenings on constructors *)

Section KwPush.
Context {G : gctx} {Γ : ctx} (ρ : kwk G Γ).
Lemma kty_tyNat : kty ρ tyNat = tyNat. Proof. unfold kty; now rewrite gwa_tyNat. Qed.
Lemma kty_tyU l : kty ρ (tyU l) = tyU l. Proof. unfold kty; now rewrite gwa_tyU. Qed.
Lemma kty_tyPi l l' A B : kty ρ (tyPi l l' A B) = tyPi l l' (kty ρ A) (ktyl ρ B).
Proof. unfold kty, ktyl; now rewrite gwa_tyPi. Qed.
Lemma kty_tyEl l t : kty ρ (tyEl l t) = tyEl l (ktm ρ t).
Proof. unfold kty, ktm; now rewrite gwa_tyEl. Qed.
Lemma ktm_zero : ktm ρ zero = zero. Proof. unfold ktm; now rewrite gwa_zero. Qed.
Lemma ktm_succ t : ktm ρ (succ t) = succ (ktm ρ t). Proof. unfold ktm; now rewrite gwa_succ. Qed.
Lemma ktm_lam l l' A t : ktm ρ (lam l l' A t) = lam l l' (kty ρ A) (ktml ρ t).
Proof. unfold ktm, kty, ktml; now rewrite gwa_lam. Qed.
End KwPush.

End Escape.
