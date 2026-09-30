(** * Escape: related types and terms are well formed and generically equal *)
From DeLaM.LogRel Require Export Def.

Section Escape.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

Lemma ge_typeof : typeof ge_layer = ge_layer.
Proof. apply compt_typeof_self, ge_compt. Qed.
Lemma ge_lle_D : lle lD ge_layer.
Proof. destruct ge_compt as [-> | ->]; unfold lle; cbn; lia. Qed.
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

(** The unit type's term relation at equivalent levels. *)
Lemma unit_conv {G Γ t l l'} : lequiv (gL G) l l' ->
  [ G ; Γ ⊢g t : tyUnit l @ l ] -> [ G ; Γ ⊢g t : tyUnit l' @ l' ].
Proof.
  intros Hl Ht. eapply conv_tm; [exact Ht | | exact (lequiv_sym _ _ _ Hl)].
  apply eqty_unit; [exact ge_notV | rewrite ge_typeof; exact (ctx_of_tm Ht) | exact (lequiv_sym _ _ _ Hl)].
Qed.

Lemma unit_tmred_conv {G Γ t w l l'} : lequiv (gL G) l l' ->
  [ G ; Γ ⊢g t ⤳* w : tyUnit l @ l ] -> [ G ; Γ ⊢g t ⤳* w : tyUnit l' @ l' ].
Proof.
  intros Hl H. eapply tmred_lconv; [| exact (lequiv_sym _ _ _ Hl)].
  eapply tmred_conv; [apply ge_typeof | exact H |].
  apply eqty_unit; [exact ge_notV | rewrite ge_typeof; exact (ctx_of_tm (tmred_wf _ _ _ _ _ _ _ H)) | exact Hl].
Qed.

Lemma UnitRel_lconv {G Γ l l'} : lequiv (gL G) l l' -> releq (UnitRel G Γ l) (UnitRel G Γ l').
Proof.
  intros Hl t t'; split; intros (w & w' & Hw & Hw' & Hn & Hn'); exists w, w';
    refine (conj _ (conj _ (conj Hn Hn'))); eauto using unit_tmred_conv, lequiv_sym.
Qed.

Lemma UnitRel_sym {G Γ l t t'} : UnitRel G Γ l t t' -> UnitRel G Γ l t' t.
Proof. intros (w & w' & Hw & Hw' & Hn & Hn'). exists w', w. auto. Qed.

Lemma UnitRel_trans {G Γ l t1 t2 t3} : UnitRel G Γ l t1 t2 -> UnitRel G Γ l t2 t3 -> UnitRel G Γ l t1 t3.
Proof. intros (w1 & _ & Hw1 & _ & Hn1 & _) (_ & w3 & _ & Hw3 & _ & Hn3). exists w1, w3. auto. Qed.

Lemma UnitRel_wf {G Γ l t t'} : UnitRel G Γ l t t' ->
  [ G ; Γ ⊢g t : tyUnit l @ l ] /\ [ G ; Γ ⊢g t' : tyUnit l @ l ].
Proof. intros (w & w' & Hw & Hw' & _ & _). exact (conj (tmred_wf _ _ _ _ _ _ _ Hw) (tmred_wf _ _ _ _ _ _ _ Hw')). Qed.

(** ** Strict equality (M10a) *)

Lemma SEqRel_wf {G Γ V l t t'} : SEqRel G Γ V l t t' -> [ G ; Γ ⊢g t : V @ l ] /\ [ G ; Γ ⊢g t' : V @ l ].
Proof. intros (w & w' & Hw & Hw' & _ & _). exact (conj (tmred_wf _ _ _ _ _ _ _ Hw) (tmred_wf _ _ _ _ _ _ _ Hw')). Qed.
Lemma SEqRel_sym {G Γ V l t t'} : SEqRel G Γ V l t t' -> SEqRel G Γ V l t' t.
Proof. intros (w & w' & Hw & Hw' & Hn & Hn'). exists w', w. auto. Qed.
Lemma SEqRel_trans {G Γ V l t1 t2 t3} : SEqRel G Γ V l t1 t2 -> SEqRel G Γ V l t2 t3 -> SEqRel G Γ V l t1 t3.
Proof. intros (w1 & _ & Hw1 & _ & Hn1 & _) (_ & w3 & _ & Hw3 & _ & Hn3). exists w1, w3. auto. Qed.
(** Along equal types and equivalent levels. *)
Lemma SEqRel_conv {G Γ V V' l l'} : [ G ; Γ ⊢g V ≅ V' @ l ] -> lequiv (gL G) l l' ->
  releq (SEqRel G Γ V l) (SEqRel G Γ V' l').
Proof.
  intros HV Hl t t'.
  assert (F : forall u w, [ G ; Γ ⊢g u ⤳* w : V @ l ] -> [ G ; Γ ⊢g u ⤳* w : V' @ l' ]).
  { intros u w H. eapply tmred_lconv; [| exact (lequiv_sym _ _ _ Hl)].
    eapply tmred_conv; [apply ge_typeof | exact H | exact HV]. }
  assert (B : forall u w, [ G ; Γ ⊢g u ⤳* w : V' @ l' ] -> [ G ; Γ ⊢g u ⤳* w : V @ l ]).
  { intros u w H. eapply tmred_lconv; [| exact Hl].
    eapply tmred_conv; [apply ge_typeof | exact H |]. apply eqty_sym. eapply eqty_lconv; [exact HV|].
    exact (lequiv_sym _ _ _ Hl). }
  split; intros (w & w' & Hw & Hw' & Hn & Hn'); exists w, w'; auto.
Qed.

Lemma SEmptyRel_wf {G Γ l t t'} : SEmptyRel G Γ l t t' ->
  [ G ; Γ ⊢g t : tySEmpty l @ l ] /\ [ G ; Γ ⊢g t' : tySEmpty l @ l ].
Proof. intros (w & w' & Hw & Hw' & _ & _). exact (conj (tmred_wf _ _ _ _ _ _ _ Hw) (tmred_wf _ _ _ _ _ _ _ Hw')). Qed.
Lemma SEmptyRel_sym {G Γ l t t'} : SEmptyRel G Γ l t t' -> SEmptyRel G Γ l t' t.
Proof. intros (w & w' & Hw & Hw' & Hn & Hn'). exists w', w. auto. Qed.
Lemma SEmptyRel_trans {G Γ l t1 t2 t3} : SEmptyRel G Γ l t1 t2 -> SEmptyRel G Γ l t2 t3 -> SEmptyRel G Γ l t1 t3.
Proof. intros (w1 & _ & Hw1 & _ & Hn1 & _) (_ & w3 & _ & Hw3 & _ & Hn3). exists w1, w3. auto. Qed.

(** ** The identity type (M11a) *)

Lemma IdNf_releq {G Γ l A a b RA RA'} : releq RA RA' ->
  forall w w', IdNf G Γ l A a b RA w w' -> IdNf G Γ l A a b RA' w w'.
Proof.
  intros HR w w' [k k' C C' c c' Hk Hk' HC HC' H1 H2 H3 H4 | ν ν' Hν].
  - apply idnf_refl; auto; apply HR; assumption.
  - now apply idnf_ne.
Qed.

Lemma IdRel_releq {G Γ l A a b RA RA'} : releq RA RA' ->
  releq (IdRel G Γ l A a b RA) (IdRel G Γ l A a b RA').
Proof.
  intros HR t t'; split; intros (w & w' & Hw & Hw' & Heq & Hn); exists w, w';
    refine (conj Hw (conj Hw' (conj Heq _))).
  - exact (IdNf_releq HR _ _ Hn).
  - exact (IdNf_releq (fun x y => iff_sym (HR x y)) _ _ Hn).
Qed.

Lemma IdRel_wf {G Γ l A a b RA t t'} : IdRel G Γ l A a b RA t t' ->
  [ G ; Γ ⊢g t : tyId l A a b @ l ] /\ [ G ; Γ ⊢g t' : tyId l A a b @ l ].
Proof. intros (w & w' & Hw & Hw' & _ & _). exact (conj (tmred_wf _ _ _ _ _ _ _ Hw) (tmred_wf _ _ _ _ _ _ _ Hw')). Qed.

Lemma sempty_eqty {G Γ l l'} : [ G ; Γ ⊢g ] -> lequiv (gL G) l l' -> [ G ; Γ ⊢g tySEmpty l ≅ tySEmpty l' @ l ].
Proof. intros HΓ Hl. apply eqty_sempty; [exact ge_notV | rewrite ge_typeof; exact HΓ | exact Hl]. Qed.

Lemma sempty_tmred_conv {G Γ t w l l'} : lequiv (gL G) l l' ->
  [ G ; Γ ⊢g t ⤳* w : tySEmpty l @ l ] -> [ G ; Γ ⊢g t ⤳* w : tySEmpty l' @ l' ].
Proof.
  intros Hl H. eapply tmred_lconv; [| exact (lequiv_sym _ _ _ Hl)].
  eapply tmred_conv; [apply ge_typeof | exact H |].
  apply sempty_eqty; [exact (ctx_of_tm (tmred_wf _ _ _ _ _ _ _ H)) | exact Hl].
Qed.

Lemma SEmptyRel_lconv {G Γ l l'} : lequiv (gL G) l l' -> releq (SEmptyRel G Γ l) (SEmptyRel G Γ l').
Proof.
  intros Hl t t'.
  assert (C : forall l1 l2 u w, lequiv (gL G) l1 l2 -> [ G ; Γ ⊢g u ⤳* w : tySEmpty l1 @ l1 ] ->
            [ G ; Γ ⊢g u ⤳* w : tySEmpty l2 @ l2 ]).
  { intros l1 l2 u w H12 H. eapply tmred_lconv; [| exact (lequiv_sym _ _ _ H12)].
    eapply tmred_conv; [apply ge_typeof | exact H |].
    apply sempty_eqty; [exact (ctx_of_tm (tmred_wf _ _ _ _ _ _ _ H)) | exact H12]. }
  assert (N : forall l1 l2 ν, lequiv (gL G) l1 l2 ->
            [ G ; Γ ⊢ ν ~ ν : tySEmpty l1 @ l1 ] -> [ G ; Γ ⊢ ν ~ ν : tySEmpty l2 @ l2 ]).
  { intros l1 l2 ν H12 H. eapply gne_tm_lconv; [| exact (lequiv_sym _ _ _ H12)].
    eapply gne_tm_conv; [exact H |]. apply sempty_eqty; [| exact H12].
    exact (ctx_of_tm (eqtm_wf_l ge_typeof (geq_tm_sound (gne_tm_geq H)))). }
  split; intros (w & w' & Hw & Hw' & Hn & Hn'); exists w, w';
    refine (conj _ (conj _ (conj _ _))); eauto using lequiv_sym.
Qed.

(** ** The empty type (M12a): related neutrals *)

Lemma EmptyRel_wf {G Γ l t t'} : EmptyRel G Γ l t t' ->
  [ G ; Γ ⊢g t : tyEmpty l @ l ] /\ [ G ; Γ ⊢g t' : tyEmpty l @ l ].
Proof. intros (w & w' & Hw & Hw' & _). exact (conj (tmred_wf _ _ _ _ _ _ _ Hw) (tmred_wf _ _ _ _ _ _ _ Hw')). Qed.
Lemma EmptyRel_sym {G Γ l t t'} : EmptyRel G Γ l t t' -> EmptyRel G Γ l t' t.
Proof. intros (w & w' & Hw & Hw' & Hn). exists w', w. auto using gne_tm_sym. Qed.
Lemma EmptyRel_trans {G Γ l t1 t2 t3} : EmptyRel G Γ l t1 t2 -> EmptyRel G Γ l t2 t3 -> EmptyRel G Γ l t1 t3.
Proof.
  intros (w1 & w2 & Hw1 & Hw2 & Hn12) (w2' & w3 & Hw2' & Hw3 & Hn23).
  pose proof (tmred_whnf_det _ _ _ _ _ _ _ _ _ _ Hw2 Hw2' (whnf_ne _ (gne_tm_whne_r Hn12)) (whnf_ne _ (gne_tm_whne_l Hn23))) as <-.
  exists w1, w3. eauto using gne_tm_trans.
Qed.

Lemma empty_eqty {G Γ l l'} : [ G ; Γ ⊢g ] -> lequiv (gL G) l l' -> [ G ; Γ ⊢g tyEmpty l ≅ tyEmpty l' @ l ].
Proof. intros HΓ Hl. apply eqty_empty; [exact ge_notV | rewrite ge_typeof; exact HΓ | exact Hl]. Qed.

Lemma empty_tmred_conv {G Γ t w l l'} : lequiv (gL G) l l' ->
  [ G ; Γ ⊢g t ⤳* w : tyEmpty l @ l ] -> [ G ; Γ ⊢g t ⤳* w : tyEmpty l' @ l' ].
Proof.
  intros Hl H. eapply tmred_lconv; [| exact (lequiv_sym _ _ _ Hl)].
  eapply tmred_conv; [apply ge_typeof | exact H |].
  apply empty_eqty; [exact (ctx_of_tm (tmred_wf _ _ _ _ _ _ _ H)) | exact Hl].
Qed.

Lemma empty_ne_conv {G Γ ν ν' l l'} : lequiv (gL G) l l' ->
  [ G ; Γ ⊢ ν ~ ν' : tyEmpty l @ l ] -> [ G ; Γ ⊢ ν ~ ν' : tyEmpty l' @ l' ].
Proof.
  intros H12 H. eapply gne_tm_lconv; [| exact (lequiv_sym _ _ _ H12)].
  eapply gne_tm_conv; [exact H |]. apply empty_eqty; [| exact H12].
  exact (ctx_of_tm (eqtm_wf_l ge_typeof (geq_tm_sound (gne_tm_geq H)))).
Qed.

Lemma EmptyRel_lconv {G Γ l l'} : lequiv (gL G) l l' -> releq (EmptyRel G Γ l) (EmptyRel G Γ l').
Proof.
  intros Hl t t'.
  split; intros (w & w' & Hw & Hw' & Hn); exists w, w';
    refine (conj _ (conj _ _)); eauto using empty_tmred_conv, empty_ne_conv, lequiv_sym.
Qed.

(** ** Binary sums (M12b) *)

Lemma SumNf_releq {G Γ l l' A B RA RA' RB RB'} : releq RA RA' -> releq RB RB' ->
  forall w w', SumNf G Γ l l' A B RA RB w w' -> SumNf G Γ l l' A B RA' RB' w w'.
Proof.
  intros HA HB w w' [k1 k2 k1' k2' C D C' D' a a' ? ? ? ? ? ? ? ? Ha
                    | k1 k2 k1' k2' C D C' D' b b' ? ? ? ? ? ? ? ? Hb | ν ν' Hν].
  - apply sumnf_inl; auto. apply HA, Ha.
  - apply sumnf_inr; auto. apply HB, Hb.
  - now apply sumnf_ne.
Qed.

Lemma SumRel_releq {G Γ l l' A B RA RA' RB RB'} : releq RA RA' -> releq RB RB' ->
  releq (SumRel G Γ l l' A B RA RB) (SumRel G Γ l l' A B RA' RB').
Proof.
  intros HA HB t t'; split; intros (w & w' & Hw & Hw' & Heq & Hn); exists w, w';
    refine (conj Hw (conj Hw' (conj Heq _))).
  - exact (SumNf_releq HA HB _ _ Hn).
  - exact (SumNf_releq (fun x y => iff_sym (HA x y)) (fun x y => iff_sym (HB x y)) _ _ Hn).
Qed.

Lemma SumRel_wf {G Γ l l' A B RA RB t t'} : SumRel G Γ l l' A B RA RB t t' ->
  [ G ; Γ ⊢g t : tySum l l' A B @ lmax l l' ] /\ [ G ; Γ ⊢g t' : tySum l l' A B @ lmax l l' ].
Proof. intros (w & w' & Hw & Hw' & _ & _). exact (conj (tmred_wf _ _ _ _ _ _ _ Hw) (tmred_wf _ _ _ _ _ _ _ Hw')). Qed.

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
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l l1 l2 T1 T1' instR R Hj Hl Hl2 Hw1 HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' l1 l2 l3 l4 T1 T1' instR R Hj Hl Hl3 Hl4 Hw1 Hw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l l1 l2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l l1 l2 A A' a a' b b' R Hl Hl2 Hw HT HT' HA HAA Haa Hbb HR
                | G Γ T T' l l1 l2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l l1 l2 A A' a a' b b' RA R Hl Hl2 Hw HT HT' HA HAA Haa Hbb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l l1 l2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR].
  all: try solve [exact (ModRel_escape_ty HM)].
  all: split; [apply HT | split; [apply HT' | eapply geq_ty_exp; [exact HT | exact HT' |]]].
  - eapply geq_ty_lconv; [|exact Hl]. eapply geq_ty_nat, tyred_ctx, HT.
  - eapply geq_ty_lconv; [eapply geq_ty_U; [eapply tyred_ctx, HT|]|].
    + now apply lequiv_sym.
    + exact Hl.
  - now apply gne_ty_geq.
  - eapply geq_ty_lconv; [|exact Hl]. apply geq_ty_pi; auto using lequiv_sym.
  - eapply geq_ty_lconv; [exact Hgeq | exact Hl].
  - eapply geq_ty_lconv; [exact Hgeq | exact Hl].
  - eapply geq_ty_lconv; [|exact Hl]. apply geq_ty_sig; auto using lequiv_sym.
  - eapply geq_ty_lconv; [|exact Hl]. apply geq_ty_unit; [eapply tyred_ctx, HT | now apply lequiv_sym].
  - eapply geq_ty_lconv; [|exact Hl]. apply geq_ty_seq; auto using lequiv_sym.
  - eapply geq_ty_lconv; [|exact Hl]. apply geq_ty_sempty; [eapply tyred_ctx, HT | now apply lequiv_sym].
  - eapply geq_ty_lconv; [|exact Hl]. apply geq_ty_id; auto using lequiv_sym.
  - eapply geq_ty_lconv; [|exact Hl]. apply geq_ty_empty; [eapply tyred_ctx, HT | now apply lequiv_sym].
  - eapply geq_ty_lconv; [|exact Hl]. apply geq_ty_sum; auto using lequiv_sym.
Qed.

(** ** Escape for terms *)

Theorem escape_tm n rec G Γ T T' l R :
  LR n rec G Γ T T' l R -> forall t t', R t t' ->
  [ G ; Γ ⊢g t : T @ l ] /\ [ G ; Γ ⊢g t' : T @ l ] /\ [ G ; Γ ⊢ t ≈ t' : T @ l ].
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
                | G Γ T T' l l1 l2 A A' a a' b b' R Hl Hl2 Hw HT HT' HA HAA Haa Hbb HR
                | G Γ T T' l l1 l2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l l1 l2 A A' a a' b b' RA R Hl Hl2 Hw HT HT' HA HAA Haa Hbb HRA Hra Hrb Hps Hpt HR
                | G Γ T T' l l1 l2 R Hl Hl2 Hw HT HT' HR
                | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                    HRA HRB Hpa Hta Hpb Htb HR];
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
  - (* CΠ *)
    destruct Htt as (w & w' & Hw & Hw' & _ & _ & Heq & _ & _).
    assert (HTP : [ G ; Γ ⊢g T ≅ tyCPi l1 T1 @ l ]) by apply HT.
    assert (Hw'' : [ G ; Γ ⊢g t' ⤳* w' : tyCPi l1 T1 @ l1 ]).
    { eapply tmred_conv; [apply ge_typeof | exact Hw' | apply eqty_sym, geq_ty_sound, Hgeq]. }
    repeat split.
    + eapply conv_tm; [apply Hw | exact HTP | exact Hl].
    + eapply conv_tm; [apply Hw'' | exact HTP | exact Hl].
    + eapply conv_geq_tm; [eapply geq_tm_exp; [exact Hw | exact Hw'' | exact Heq]
                          | apply eqty_sym, HTP | exact Hl].
  - (* TΠ *)
    destruct Htt as (w & w' & Hw & Hw' & _ & _ & Heq & _ & _).
    assert (HTP : [ G ; Γ ⊢g T ≅ tyTPi Δ1 l1 l2 T1 @ l ]) by apply HT.
    assert (Hw'' : [ G ; Γ ⊢g t' ⤳* w' : tyTPi Δ1 l1 l2 T1 @ l2 ]).
    { eapply tmred_conv; [apply ge_typeof | exact Hw' | apply eqty_sym, geq_ty_sound, Hgeq]. }
    repeat split.
    + eapply conv_tm; [apply Hw | exact HTP | exact Hl].
    + eapply conv_tm; [apply Hw'' | exact HTP | exact Hl].
    + eapply conv_geq_tm; [eapply geq_tm_exp; [exact Hw | exact Hw'' | exact Heq]
                          | apply eqty_sym, HTP | exact Hl].
  - (* Σ *)
    destruct Htt as (w & w' & Hw & Hw' & _ & _ & Heq & _ & _).
    assert (HTP : [ G ; Γ ⊢g T ≅ tySig l1 l2 A B @ l ]) by apply HT.
    assert (HPP : [ G ; Γ ⊢g tySig l1 l2 A B ≅ tySig l3 l4 A' B' @ lmax l1 l2 ])
      by (apply geq_ty_sound, geq_ty_sig; auto using lequiv_sym).
    assert (Hw'' : [ G ; Γ ⊢g t' ⤳* w' : tySig l1 l2 A B @ lmax l1 l2 ]).
    { eapply tmred_conv; [apply ge_typeof | exact Hw' | now apply eqty_sym]. }
    repeat split.
    + eapply conv_tm; [apply Hw | exact HTP | exact Hl].
    + eapply conv_tm; [apply Hw'' | exact HTP | exact Hl].
    + eapply conv_geq_tm; [eapply geq_tm_exp; [exact Hw | exact Hw'' | exact Heq]
                          | apply eqty_sym, HTP | exact Hl].
  - (* Unit: irrelevant, escape from η *)
    destruct (UnitRel_wf Htt) as [Ht Ht'].
    assert (HTU : [ G ; Γ ⊢g T ≅ tyUnit l1 @ l ]) by apply HT.
    repeat split.
    + eapply conv_tm; [exact Ht | exact HTU | exact Hl].
    + eapply conv_tm; [exact Ht' | exact HTU | exact Hl].
    + eapply conv_geq_tm; [exact (geq_tm_unit_eta Hw Ht Ht') | apply eqty_sym, HTU | exact Hl].
  - (* sEq: irrelevant *)
    destruct (SEqRel_wf Htt) as [Ht Ht'].
    assert (HTU : [ G ; Γ ⊢g T ≅ tySEq l1 A a b @ l ]) by apply HT.
    repeat split.
    + eapply conv_tm; [exact Ht | exact HTU | exact Hl].
    + eapply conv_tm; [exact Ht' | exact HTU | exact Hl].
    + eapply conv_geq_tm; [exact (geq_tm_seq_irr Hw Ht Ht') | apply eqty_sym, HTU | exact Hl].
  - (* sEmpty: irrelevant *)
    destruct (SEmptyRel_wf Htt) as [Ht Ht'].
    assert (HTU : [ G ; Γ ⊢g T ≅ tySEmpty l1 @ l ]) by apply HT.
    repeat split.
    + eapply conv_tm; [exact Ht | exact HTU | exact Hl].
    + eapply conv_tm; [exact Ht' | exact HTU | exact Hl].
    + eapply conv_geq_tm; [exact (geq_tm_sempty_irr Hw Ht Ht') | apply eqty_sym, HTU | exact Hl].
  - (* Id: related weak-head normal forms *)
    destruct Htt as (w & w' & Hw' & Hw'' & Heq & _).
    assert (HTI : [ G ; Γ ⊢g T ≅ tyId l1 A a b @ l ]) by apply HT.
    repeat split.
    + eapply conv_tm; [apply Hw' | exact HTI | exact Hl].
    + eapply conv_tm; [apply Hw'' | exact HTI | exact Hl].
    + eapply conv_geq_tm; [eapply geq_tm_exp; eauto | apply eqty_sym, HTI | exact Hl].
  - (* Empty: related neutrals *)
    destruct Htt as (w & w' & Hw' & Hw'' & Hne). pose proof (gne_tm_geq Hne) as Heq.
    assert (HTE : [ G ; Γ ⊢g T ≅ tyEmpty l1 @ l ]) by apply HT.
    repeat split.
    + eapply conv_tm; [apply Hw' | exact HTE | exact Hl].
    + eapply conv_tm; [apply Hw'' | exact HTE | exact Hl].
    + eapply conv_geq_tm; [eapply geq_tm_exp; eauto | apply eqty_sym, HTE | exact Hl].
  - (* +: related weak-head normal forms *)
    destruct Htt as (w & w' & Hw' & Hw'' & Heq & _).
    assert (HTS : [ G ; Γ ⊢g T ≅ tySum u1 u2 UA UB @ l ]) by apply HT.
    repeat split.
    + eapply conv_tm; [apply Hw' | exact HTS | exact Hl].
    + eapply conv_tm; [apply Hw'' | exact HTS | exact Hl].
    + eapply conv_geq_tm; [eapply geq_tm_exp; eauto | apply eqty_sym, HTS | exact Hl].
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
    [ let D := fresh "D" in
      first [ pose proof (geq_ty_sound (gne_ty_geq H)) as D | pose proof (geq_ty_sound H) as D
            | pose proof (geq_tm_sound (gne_tm_geq H)) as D | pose proof (geq_tm_sound H) as D ];
      first [ apply (gne_ty_gwk Hγ HG) in H | apply (geq_ty_gwk Hγ HG) in H
            | apply (gne_tm_gwk Hγ HG) in H | apply (geq_tm_gwk Hγ HG) in H ];
      rewrite ?gren_id_ctx', ?gren_id_ty', ?gren_id_tm' in H by dnf_of D; exact H
    | first [ exact (gne_ty_gwk Hγ HG H) | exact (geq_ty_gwk Hγ HG H)
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

Lemma kw_gL {G Γ} (ρ : kwk G Γ) : gL G <= gL (kw_G ρ).
Proof. exact (proj1 (kw_gok ρ)). Qed.
Lemma kw_glob {G Γ} (ρ : kwk G Γ) : [ ⊢ kw_G ρ ].
Proof. exact (ctx_glob _ _ _ (kw_ctx ρ)). Qed.
Lemma kw_lequiv {G Γ} (ρ : kwk G Γ) {l l'} : lequiv (gL G) l l' -> lequiv (gL (kw_G ρ)) l l'.
Proof. apply lequiv_weaken, kw_gL. Qed.
Lemma kw_lwf {G Γ} (ρ : kwk G Γ) {l} : lwf (gL G) l -> lwf (gL (kw_G ρ)) l.
Proof. apply lwf_weaken, kw_gL. Qed.
(** A level of the world equivalent to one of the base is one of the base
    (M3_DESIGN.md E14). *)
Lemma kw_lequiv_shrink {G Γ} (ρ : kwk G Γ) {l l'} : lequiv (gL (kw_G ρ)) l l' -> lwf (gL G) l' ->
  lequiv (gL G) l l'.
Proof. apply lequiv_shrink. Qed.

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

(** Under one global binder (the meta-functions, M5): [⇑γ], then the
    local renaming. *)
Lemma kw_gok_up D : gwk_ok (gwk_up' (kw_γ ρ)) (gext (kw_G ρ) (gdecl_gwa (kw_γ ρ) D)) (gext G D).
Proof.
  pose proof (kw_gok ρ) as [HL Hw]. split; [exact HL|]. cbn [gΨ gext].
  destruct (kw_γ ρ) as [|γ0|γ0] eqn:Eγ; cbn [gwk_up' gdecl_gwa].
  - assert (EΨ : gΨ (kw_G ρ) = gΨ G) by (inversion Hw; reflexivity). rewrite EΨ. constructor.
  - apply gwkwf_up. exact Hw.
  - apply gwkwf_up. exact Hw.
Qed.

Lemma kw_body_ctx D : [ ⊢ gext (kw_G ρ) (gdecl_gwa (kw_γ ρ) D) ] ->
  [ gext (kw_G ρ) (gdecl_gwa (kw_γ ρ) D) ; (kw_Δ ρ)⟪S⟫ ⊢g ].
Proof.
  intros HG. exact (gwk_ctx (gwk_ok_step (G := kw_G ρ) (D := gdecl_gwa (kw_γ ρ) D)) HG HΔ).
Qed.

Lemma kw_wkr_g : wkr (kw_r ρ) (kw_Δ ρ)⟪S⟫ (Γ⟦kw_γ ρ⟧)⟪S⟫.
Proof. apply wkr_gren, wk_wf_wkr, Hr. Qed.

Lemma kw_body_ty {D T l} : [ ⊢ gext (kw_G ρ) (gdecl_gwa (kw_γ ρ) D) ] ->
  [ gext G D ; Γ⟪S⟫ ⊢g T @ l ] -> [ gext (kw_G ρ) (gdecl_gwa (kw_γ ρ) D) ; (kw_Δ ρ)⟪S⟫ ⊢g kbody ρ T @ l ].
Proof.
  intros HG H. pose proof (gwa_ty (kw_gok_up D) HG H) as X. rewrite gwa_up'_shift in X.
  exact (wf_ty_wkr kw_wkr_g (kw_body_ctx D HG) X).
Qed.
Lemma kw_body_eqty {D T T' l} : [ ⊢ gext (kw_G ρ) (gdecl_gwa (kw_γ ρ) D) ] ->
  [ gext G D ; Γ⟪S⟫ ⊢g T ≅ T' @ l ] ->
  [ gext (kw_G ρ) (gdecl_gwa (kw_γ ρ) D) ; (kw_Δ ρ)⟪S⟫ ⊢g kbody ρ T ≅ kbody ρ T' @ l ].
Proof.
  intros HG H. pose proof (gwa_eqty (kw_gok_up D) HG H) as X. rewrite !gwa_up'_shift in X.
  exact (eqty_wkr kw_wkr_g (kw_body_ctx D HG) X).
Qed.
Lemma kw_body_tm {D t T l} : [ ⊢ gext (kw_G ρ) (gdecl_gwa (kw_γ ρ) D) ] ->
  [ gext G D ; Γ⟪S⟫ ⊢g t : T @ l ] ->
  [ gext (kw_G ρ) (gdecl_gwa (kw_γ ρ) D) ; (kw_Δ ρ)⟪S⟫ ⊢g kbodyt ρ t : kbody ρ T @ l ].
Proof.
  intros HG H. pose proof (gwa_tm (kw_gok_up D) HG H) as X. rewrite gwa_up'_shift in X.
  exact (wf_tm_wkr kw_wkr_g (kw_body_ctx D HG) X).
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

Lemma gwk_up'_comp γ' γ : gwk_comp (gwk_up' γ') (gwk_up' γ) = gwk_up' (gwk_comp γ' γ).
Proof. destruct γ', γ; cbn; rewrite ?gwk_comp_id_r; reflexivity. Qed.

Lemma kbody_comp {G Γ} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) T :
  kbody (kw_comp ρ ρ') T = kbody ρ' (kbody ρ T).
Proof. unfold kbody; cbn. now rewrite gwa_ren_ty, gwa_comp_ty, gwk_up'_comp, ren_wk_comp_ty. Qed.
Lemma kbodyt_comp {G Γ} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) t :
  kbodyt (kw_comp ρ ρ') t = kbodyt ρ' (kbodyt ρ t).
Proof. unfold kbodyt; cbn. now rewrite gwa_ren, gwa_comp_tm, gwk_up'_comp, ren_wk_comp. Qed.

Lemma gwa_comp_ctx' (Δ : ctx) {G Γ} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) :
  Δ⟦kw_γ (kw_comp ρ ρ')⟧ = Δ⟦kw_γ ρ⟧⟦kw_γ ρ'⟧.
Proof. cbn. now rewrite gwa_comp_ctx. Qed.

(** ** Kripke weakenings on constructors *)

Section KwPush.
Context {G : gctx} {Γ : ctx} (ρ : kwk G Γ).
Lemma kty_tyNat : kty ρ tyNat = tyNat. Proof. unfold kty; now rewrite gwa_tyNat. Qed.
Lemma kty_tyU l : kty ρ (tyU l) = tyU l. Proof. unfold kty; now rewrite gwa_tyU. Qed.
Lemma kty_tyUnit l : kty ρ (tyUnit l) = tyUnit l. Proof. unfold kty; now rewrite gwa_tyUnit. Qed.
Lemma kty_tySEq l A a b : kty ρ (tySEq l A a b) = tySEq l (kty ρ A) (ktm ρ a) (ktm ρ b).
Proof. unfold kty, ktm; now rewrite gwa_tySEq. Qed.
Lemma kty_tySEmpty l : kty ρ (tySEmpty l) = tySEmpty l. Proof. unfold kty; now rewrite gwa_tySEmpty. Qed.
Lemma kty_tyEmpty l : kty ρ (tyEmpty l) = tyEmpty l. Proof. unfold kty; now rewrite gwa_tyEmpty. Qed.
Lemma kty_tySum l l' A B : kty ρ (tySum l l' A B) = tySum l l' (kty ρ A) (kty ρ B).
Proof. unfold kty; now rewrite gwa_tySum. Qed.
Lemma ktm_inl l l' A B a : ktm ρ (tmInl l l' A B a) = tmInl l l' (kty ρ A) (kty ρ B) (ktm ρ a).
Proof. unfold ktm, kty; now rewrite gwa_inl. Qed.
Lemma ktm_inr l l' A B a : ktm ρ (tmInr l l' A B a) = tmInr l l' (kty ρ A) (kty ρ B) (ktm ρ a).
Proof. unfold ktm, kty; now rewrite gwa_inr. Qed.
Lemma ktm_elimEmpty l l' M t : ktm ρ (elimEmpty l l' M t) = elimEmpty l l' (ktyl ρ M) (ktm ρ t).
Proof. unfold ktm, ktyl; now rewrite gwa_elimEmpty. Qed.
Lemma ktm_srefl l A a : ktm ρ (srefl l A a) = srefl l (kty ρ A) (ktm ρ a).
Proof. unfold ktm, kty; now rewrite gwa_srefl. Qed.
Lemma ktm_elimSEmpty l l' M e : ktm ρ (elimSEmpty l l' M e) = elimSEmpty l l' (kty ρ M) (ktm ρ e).
Proof. unfold ktm, kty; now rewrite gwa_elimSEmpty. Qed.
Lemma kty_tyId l A a b : kty ρ (tyId l A a b) = tyId l (kty ρ A) (ktm ρ a) (ktm ρ b).
Proof. unfold kty, ktm; now rewrite gwa_tyId. Qed.
Lemma ktm_refl l A a : ktm ρ (tmRefl l A a) = tmRefl l (kty ρ A) (ktm ρ a).
Proof. unfold ktm, kty; now rewrite gwa_refl. Qed.
Lemma kty_tyPi l l' A B : kty ρ (tyPi l l' A B) = tyPi l l' (kty ρ A) (ktyl ρ B).
Proof. unfold kty, ktyl; now rewrite gwa_tyPi. Qed.
Lemma kty_tySig l l' A B : kty ρ (tySig l l' A B) = tySig l l' (kty ρ A) (ktyl ρ B).
Proof. unfold kty, ktyl; now rewrite gwa_tySig. Qed.
Lemma ktm_fst l l' A B p : ktm ρ (tmFst l l' A B p) = tmFst l l' (kty ρ A) (ktyl ρ B) (ktm ρ p).
Proof. unfold ktm, kty, ktyl; now rewrite gwa_fst. Qed.
Lemma ktm_snd l l' A B p : ktm ρ (tmSnd l l' A B p) = tmSnd l l' (kty ρ A) (ktyl ρ B) (ktm ρ p).
Proof. unfold ktm, kty, ktyl; now rewrite gwa_snd. Qed.
Lemma ktm_pair l l' A B a b :
  ktm ρ (tmPair l l' A B a b) = tmPair l l' (kty ρ A) (ktyl ρ B) (ktm ρ a) (ktm ρ b).
Proof. unfold ktm, kty, ktyl; now rewrite gwa_pair. Qed.
Lemma kty_tyEl l t : kty ρ (tyEl l t) = tyEl l (ktm ρ t).
Proof. unfold kty, ktm; now rewrite gwa_tyEl. Qed.
Lemma ktm_zero : ktm ρ zero = zero. Proof. unfold ktm; now rewrite gwa_zero. Qed.
Lemma ktm_succ t : ktm ρ (succ t) = succ (ktm ρ t). Proof. unfold ktm; now rewrite gwa_succ. Qed.
Lemma ktm_lam l l' A t : ktm ρ (lam l l' A t) = lam l l' (kty ρ A) (ktml ρ t).
Proof. unfold ktm, kty, ktml; now rewrite gwa_lam. Qed.
(** The meta-functions (M5): the body moves under [⇑γ]. *)
Lemma kty_tyCPi l T : kty ρ (tyCPi l T) = tyCPi l (kbody ρ T).
Proof. unfold kty, kbody; now destruct (kw_γ ρ). Qed.
Lemma kty_tyTPi Δ l l' T : kty ρ (tyTPi Δ l l' T) = tyTPi Δ⟦kw_γ ρ⟧ l l' (kbody ρ T).
Proof. unfold kty, kbody; now destruct (kw_γ ρ). Qed.
Lemma ktm_clam l T t : ktm ρ (clam l T t) = clam l (kbody ρ T) (kbodyt ρ t).
Proof. unfold ktm, kbody, kbodyt; now destruct (kw_γ ρ). Qed.
Lemma ktm_tlam Δ l l' T t : ktm ρ (tlam Δ l l' T t) = tlam Δ⟦kw_γ ρ⟧ l l' (kbody ρ T) (kbodyt ρ t).
Proof. unfold ktm, kbody, kbodyt; now destruct (kw_γ ρ). Qed.
Lemma ktm_capp t Δ : ktm ρ (capp t Δ) = capp (ktm ρ t) Δ⟦kw_γ ρ⟧.
Proof. unfold ktm; now destruct (kw_γ ρ). Qed.
Lemma ktm_tapp t A : ktm ρ (tapp t A) = tapp (ktm ρ t) A⟦kw_γ ρ⟧.
Proof. unfold ktm; now destruct (kw_γ ρ). Qed.
End KwPush.

End Escape.
