(** * Escape: related types and terms are well formed and generically equal *)
From DeLaM.Typing Require Export Presupposition.
From DeLaM.LogRel Require Export Def.

Lemma ren_id_tm (t : tm) : nftm t -> t⟨rshift 0⟩ = t.
Proof. intros H. rewrite (ren_as_subst _ _ (lshift 0)); [apply subst_id; auto|]; intros; cbn; f_equal; lia. Qed.

Section Escape.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

Lemma ge_typeof : typeof ge_layer = ge_layer.
Proof using . apply compt_typeof_self, ge_compt. Qed.
Lemma ge_lle_D : lle lD ge_layer.
Proof using . destruct ge_compt as [-> | ->]; unfold lle; cbn; lia. Qed.
Lemma ge_notV : ge_layer <> lV.
Proof using . destruct ge_compt as [-> | ->]; discriminate. Qed.

(** ** Declarative conversion helpers at the instance's layer *)

Lemma ctx_of_ty {G Γ T l} : [ G ; Γ ⊢g T @ l ] -> [ G ; Γ ⊢g ].
Proof using . intros H. pose proof (proj1 (proj2 (proj2 ctx_extract)) _ _ _ _ _ H) as Hc.
       now rewrite ge_typeof in Hc. Qed.
Lemma ctx_of_tm {G Γ t T l} : [ G ; Γ ⊢g t : T @ l ] -> [ G ; Γ ⊢g ].
Proof using . intros H. pose proof (proj1 (proj2 (proj2 (proj2 ctx_extract))) _ _ _ _ _ _ H) as Hc.
       now rewrite ge_typeof in Hc. Qed.

Lemma conv_tm {G Γ t T T' l l'} :
  [ G ; Γ ⊢g t : T @ l ] -> [ G ; Γ ⊢g T' ≅ T @ l' ] -> lequiv (gL G) l' l ->
  [ G ; Γ ⊢g t : T' @ l' ].
Proof using .
  intros Ht HT Hl. eapply wf_conv; [eapply wf_lconv; eauto|]. now rewrite ge_typeof.
Qed.

Lemma conv_geq_tm {G Γ t t' T T' l l'} :
  [ G ; Γ ⊢ t ≈ t' : T @ l ] -> [ G ; Γ ⊢g T ≅ T' @ l' ] -> lequiv (gL G) l' l ->
  [ G ; Γ ⊢ t ≈ t' : T' @ l' ].
Proof using EL.
  intros Ht HT Hl. eapply geq_tm_conv; [eapply geq_tm_lconv; eauto|]. auto.
Qed.

Lemma tyred_ctx {G Γ T W l} : [ G ; Γ ⊢g T ⤳* W @ l ] -> [ G ; Γ ⊢g ].
Proof using . intros []; eauto using ctx_of_ty. Qed.

(** The unit type's term relation at equivalent levels. *)
Lemma unit_conv {G Γ t l l'} : lequiv (gL G) l l' ->
  [ G ; Γ ⊢g t : tyUnit l @ l ] -> [ G ; Γ ⊢g t : tyUnit l' @ l' ].
Proof using .
  intros Hl Ht. eapply conv_tm; [exact Ht | | exact (lequiv_sym _ _ _ Hl)].
  apply eqty_unit; [exact ge_notV | rewrite ge_typeof; exact (ctx_of_tm Ht) | exact (lequiv_sym _ _ _ Hl)].
Qed.

Lemma unit_tmred_conv {G Γ t w l l'} : lequiv (gL G) l l' ->
  [ G ; Γ ⊢g t ⤳* w : tyUnit l @ l ] -> [ G ; Γ ⊢g t ⤳* w : tyUnit l' @ l' ].
Proof using .
  intros Hl H. eapply tmred_lconv; [| exact (lequiv_sym _ _ _ Hl)].
  eapply tmred_conv; [apply ge_typeof | exact H |].
  apply eqty_unit; [exact ge_notV | rewrite ge_typeof; exact (ctx_of_tm (tmred_wf _ _ _ _ _ _ _ H)) | exact Hl].
Qed.

Lemma UnitRel_lconv {G Γ l l'} : lequiv (gL G) l l' -> releq (UnitRel G Γ l) (UnitRel G Γ l').
Proof using .
  intros Hl t t'; split; intros (w & w' & Hw & Hw' & Hn & Hn'); exists w, w';
    refine (conj _ (conj _ (conj Hn Hn'))); eauto using unit_tmred_conv, lequiv_sym.
Qed.

Lemma UnitRel_sym {G Γ l t t'} : UnitRel G Γ l t t' -> UnitRel G Γ l t' t.
Proof using . intros (w & w' & Hw & Hw' & Hn & Hn'). exists w', w. auto. Qed.

Lemma UnitRel_trans {G Γ l t1 t2 t3} : UnitRel G Γ l t1 t2 -> UnitRel G Γ l t2 t3 -> UnitRel G Γ l t1 t3.
Proof using . intros (w1 & _ & Hw1 & _ & Hn1 & _) (_ & w3 & _ & Hw3 & _ & Hn3). exists w1, w3. auto. Qed.

Lemma UnitRel_wf {G Γ l t t'} : UnitRel G Γ l t t' ->
  [ G ; Γ ⊢g t : tyUnit l @ l ] /\ [ G ; Γ ⊢g t' : tyUnit l @ l ].
Proof using . intros (w & w' & Hw & Hw' & _ & _). exact (conj (tmred_wf _ _ _ _ _ _ _ Hw) (tmred_wf _ _ _ _ _ _ _ Hw')). Qed.

(** ** Strict equality (M10a) *)

Lemma SEqRel_wf {G Γ V l t t'} : SEqRel G Γ V l t t' -> [ G ; Γ ⊢g t : V @ l ] /\ [ G ; Γ ⊢g t' : V @ l ].
Proof using . intros (w & w' & Hw & Hw' & _ & _). exact (conj (tmred_wf _ _ _ _ _ _ _ Hw) (tmred_wf _ _ _ _ _ _ _ Hw')). Qed.
Lemma SEqRel_sym {G Γ V l t t'} : SEqRel G Γ V l t t' -> SEqRel G Γ V l t' t.
Proof using . intros (w & w' & Hw & Hw' & Hn & Hn'). exists w', w. auto. Qed.
Lemma SEqRel_trans {G Γ V l t1 t2 t3} : SEqRel G Γ V l t1 t2 -> SEqRel G Γ V l t2 t3 -> SEqRel G Γ V l t1 t3.
Proof using . intros (w1 & _ & Hw1 & _ & Hn1 & _) (_ & w3 & _ & Hw3 & _ & Hn3). exists w1, w3. auto. Qed.
(** Along equal types and equivalent levels. *)
Lemma SEqRel_conv {G Γ V V' l l'} : [ G ; Γ ⊢g V ≅ V' @ l ] -> lequiv (gL G) l l' ->
  releq (SEqRel G Γ V l) (SEqRel G Γ V' l').
Proof using .
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
Proof using . intros (w & w' & Hw & Hw' & _ & _). exact (conj (tmred_wf _ _ _ _ _ _ _ Hw) (tmred_wf _ _ _ _ _ _ _ Hw')). Qed.
Lemma SEmptyRel_sym {G Γ l t t'} : SEmptyRel G Γ l t t' -> SEmptyRel G Γ l t' t.
Proof using . intros (w & w' & Hw & Hw' & Hn & Hn'). exists w', w. auto. Qed.
Lemma SEmptyRel_trans {G Γ l t1 t2 t3} : SEmptyRel G Γ l t1 t2 -> SEmptyRel G Γ l t2 t3 -> SEmptyRel G Γ l t1 t3.
Proof using . intros (w1 & _ & Hw1 & _ & Hn1 & _) (_ & w3 & _ & Hw3 & _ & Hn3). exists w1, w3. auto. Qed.

(** ** The identity type (M11a) *)

Lemma IdNf_releq {G Γ l A a b RA RA'} : releq RA RA' ->
  forall w w', IdNf G Γ l A a b RA w w' -> IdNf G Γ l A a b RA' w w'.
Proof using .
  intros HR w w' [k k' C C' c c' Hk Hk' HC HC' H1 H2 H3 H4 | ν ν' Hν].
  - apply idnf_refl; auto; apply HR; assumption.
  - now apply idnf_ne.
Qed.

Lemma IdRel_releq {G Γ l A a b RA RA'} : releq RA RA' ->
  releq (IdRel G Γ l A a b RA) (IdRel G Γ l A a b RA').
Proof using .
  intros HR t t'; split; intros (w & w' & Hw & Hw' & Heq & Hn); exists w, w';
    refine (conj Hw (conj Hw' (conj Heq _))).
  - exact (IdNf_releq HR _ _ Hn).
  - exact (IdNf_releq (fun x y => iff_sym (HR x y)) _ _ Hn).
Qed.

Lemma IdRel_wf {G Γ l A a b RA t t'} : IdRel G Γ l A a b RA t t' ->
  [ G ; Γ ⊢g t : tyId l A a b @ l ] /\ [ G ; Γ ⊢g t' : tyId l A a b @ l ].
Proof using . intros (w & w' & Hw & Hw' & _ & _). exact (conj (tmred_wf _ _ _ _ _ _ _ Hw) (tmred_wf _ _ _ _ _ _ _ Hw')). Qed.

Lemma sempty_eqty {G Γ l l'} : [ G ; Γ ⊢g ] -> lequiv (gL G) l l' -> [ G ; Γ ⊢g tySEmpty l ≅ tySEmpty l' @ l ].
Proof using . intros HΓ Hl. apply eqty_sempty; [exact ge_notV | rewrite ge_typeof; exact HΓ | exact Hl]. Qed.

Lemma sempty_tmred_conv {G Γ t w l l'} : lequiv (gL G) l l' ->
  [ G ; Γ ⊢g t ⤳* w : tySEmpty l @ l ] -> [ G ; Γ ⊢g t ⤳* w : tySEmpty l' @ l' ].
Proof using .
  intros Hl H. eapply tmred_lconv; [| exact (lequiv_sym _ _ _ Hl)].
  eapply tmred_conv; [apply ge_typeof | exact H |].
  apply sempty_eqty; [exact (ctx_of_tm (tmred_wf _ _ _ _ _ _ _ H)) | exact Hl].
Qed.

Lemma SEmptyRel_lconv {G Γ l l'} : lequiv (gL G) l l' -> releq (SEmptyRel G Γ l) (SEmptyRel G Γ l').
Proof using EL.
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

(** ** The empty type (M12a): self-related neutrals, as at [sEmpty] *)

Lemma EmptyRel_wf {G Γ l t t'} : EmptyRel G Γ l t t' ->
  [ G ; Γ ⊢g t : tyEmpty l @ l ] /\ [ G ; Γ ⊢g t' : tyEmpty l @ l ].
Proof using . intros (w & w' & Hw & Hw' & _ & _). exact (conj (tmred_wf _ _ _ _ _ _ _ Hw) (tmred_wf _ _ _ _ _ _ _ Hw')). Qed.
Lemma EmptyRel_sym {G Γ l t t'} : EmptyRel G Γ l t t' -> EmptyRel G Γ l t' t.
Proof using . intros (w & w' & Hw & Hw' & Hn & Hn'). exists w', w. auto. Qed.
Lemma EmptyRel_trans {G Γ l t1 t2 t3} : EmptyRel G Γ l t1 t2 -> EmptyRel G Γ l t2 t3 -> EmptyRel G Γ l t1 t3.
Proof using . intros (w1 & _ & Hw1 & _ & Hn1 & _) (_ & w3 & _ & Hw3 & _ & Hn3). exists w1, w3. auto. Qed.

Lemma empty_eqty {G Γ l l'} : [ G ; Γ ⊢g ] -> lequiv (gL G) l l' -> [ G ; Γ ⊢g tyEmpty l ≅ tyEmpty l' @ l ].
Proof using . intros HΓ Hl. apply eqty_empty; [exact ge_notV | rewrite ge_typeof; exact HΓ | exact Hl]. Qed.

Lemma empty_tmred_conv {G Γ t w l l'} : lequiv (gL G) l l' ->
  [ G ; Γ ⊢g t ⤳* w : tyEmpty l @ l ] -> [ G ; Γ ⊢g t ⤳* w : tyEmpty l' @ l' ].
Proof using .
  intros Hl H. eapply tmred_lconv; [| exact (lequiv_sym _ _ _ Hl)].
  eapply tmred_conv; [apply ge_typeof | exact H |].
  apply empty_eqty; [exact (ctx_of_tm (tmred_wf _ _ _ _ _ _ _ H)) | exact Hl].
Qed.

Lemma empty_ne_conv {G Γ ν ν' l l'} : lequiv (gL G) l l' ->
  [ G ; Γ ⊢ ν ~ ν' : tyEmpty l @ l ] -> [ G ; Γ ⊢ ν ~ ν' : tyEmpty l' @ l' ].
Proof using EL.
  intros H12 H. eapply gne_tm_lconv; [| exact (lequiv_sym _ _ _ H12)].
  eapply gne_tm_conv; [exact H |]. apply empty_eqty; [| exact H12].
  exact (ctx_of_tm (eqtm_wf_l ge_typeof (geq_tm_sound (gne_tm_geq H)))).
Qed.

Lemma EmptyRel_lconv {G Γ l l'} : lequiv (gL G) l l' -> releq (EmptyRel G Γ l) (EmptyRel G Γ l').
Proof using EL.
  intros Hl t t'.
  split; intros (w & w' & Hw & Hw' & Hn & Hn'); exists w, w';
    refine (conj _ (conj _ (conj _ _))); eauto using empty_tmred_conv, empty_ne_conv, lequiv_sym.
Qed.

(** ** Binary sums (M12b) *)

Lemma SumNf_releq {G Γ l l' A B RA RA' RB RB'} : releq RA RA' -> releq RB RB' ->
  forall w w', SumNf G Γ l l' A B RA RB w w' -> SumNf G Γ l l' A B RA' RB' w w'.
Proof using .
  intros HA HB w w' [k1 k2 k1' k2' C D C' D' a a' ? ? ? ? ? ? ? ? Ha
                    | k1 k2 k1' k2' C D C' D' b b' ? ? ? ? ? ? ? ? Hb | ν ν' Hν].
  - apply sumnf_inl; auto. apply HA, Ha.
  - apply sumnf_inr; auto. apply HB, Hb.
  - now apply sumnf_ne.
Qed.

Lemma SumRel_releq {G Γ l l' A B RA RA' RB RB'} : releq RA RA' -> releq RB RB' ->
  releq (SumRel G Γ l l' A B RA RB) (SumRel G Γ l l' A B RA' RB').
Proof using .
  intros HA HB t t'; split; intros (w & w' & Hw & Hw' & Heq & Hn); exists w, w';
    refine (conj Hw (conj Hw' (conj Heq _))).
  - exact (SumNf_releq HA HB _ _ Hn).
  - exact (SumNf_releq (fun x y => iff_sym (HA x y)) (fun x y => iff_sym (HB x y)) _ _ Hn).
Qed.

Lemma SumRel_wf {G Γ l l' A B RA RB t t'} : SumRel G Γ l l' A B RA RB t t' ->
  [ G ; Γ ⊢g t : tySum l l' A B @ lmax l l' ] /\ [ G ; Γ ⊢g t' : tySum l l' A B @ lmax l l' ].
Proof using . intros (w & w' & Hw & Hw' & _ & _). exact (conj (tmred_wf _ _ _ _ _ _ _ Hw) (tmred_wf _ _ _ _ _ _ _ Hw')). Qed.

(** ** Propositional truncation (M16a): a product of two unary predicates

    Reflexivity, symmetry and transitivity are free, since nothing is
    compared; the carrier changes along equal types, reading only the
    diagonal of its relation ([probes/SquashProbe.v]). *)

Lemma SqRel_sym {G Γ l A RA t t'} : SqRel G Γ l A RA t t' -> SqRel G Γ l A RA t' t.
Proof using . intros [H H']; exact (conj H' H). Qed.

Lemma SqRel_trans {G Γ l A RA t1 t2 t3} :
  SqRel G Γ l A RA t1 t2 -> SqRel G Γ l A RA t2 t3 -> SqRel G Γ l A RA t1 t3.
Proof using . intros [H1 _] [_ H3]; exact (conj H1 H3). Qed.

Lemma SqRel_refl_l {G Γ l A RA t t'} : SqRel G Γ l A RA t t' -> SqRel G Γ l A RA t t.
Proof using . intros [H _]; exact (conj H H). Qed.

Lemma SqRel_refl_r {G Γ l A RA t t'} : SqRel G Γ l A RA t t' -> SqRel G Γ l A RA t' t'.
Proof using . intros [_ H]; exact (conj H H). Qed.

Lemma SqU_wf {G Γ l A RA t} : SqU G Γ l A RA t -> [ G ; Γ ⊢g t : tySq l A @ l ].
Proof using . intros (w & Hw & _). exact (tmred_wf _ _ _ _ _ _ _ Hw). Qed.

Lemma SqRel_wf {G Γ l A RA t t'} : SqRel G Γ l A RA t t' ->
  [ G ; Γ ⊢g t : tySq l A @ l ] /\ [ G ; Γ ⊢g t' : tySq l A @ l ].
Proof using . intros [H H']. exact (conj (SqU_wf H) (SqU_wf H')). Qed.

Lemma SqU_conv {G Γ l l' A A' RA RA' t} :
  lequiv (gL G) l l' -> [ G ; Γ ⊢g A @ l ] -> [ G ; Γ ⊢ A ≈ A' @ l ] ->
  (forall a, RA a a -> RA' a a) ->
  SqU G Γ l A RA t -> SqU G Γ l' A' RA' t.
Proof using EL.
  intros Hl HA HAA HR (w & Hw & Hn).
  pose proof (lequiv_sym _ _ _ Hl) as Hl'.
  assert (HV : [ G ; Γ ⊢g tySq l A ≅ tySq l' A' @ l ]) by exact (geq_ty_sound (geq_ty_sq Hl HA HAA)).
  exists w. split.
  - eapply tmred_lconv; [eapply tmred_conv; [apply ge_typeof | exact Hw | exact HV] | exact Hl'].
  - destruct Hn as [k C a Hk HC Ha | ν Hν].
    + apply sqnf_sq; [exact (lequiv_trans _ _ _ _ Hk Hl) | | exact (HR _ Ha)].
      eapply geq_ty_lconv; [eapply geq_ty_trans; [apply geq_ty_sym, HAA | exact HC] | exact Hl'].
    + apply sqnf_ne. eapply gne_tm_lconv; [eapply gne_tm_conv; [exact Hν | exact HV] | exact Hl'].
Qed.

Lemma SqRel_conv {G Γ l l' A A' RA RA'} :
  lequiv (gL G) l l' -> [ G ; Γ ⊢g A @ l ] -> [ G ; Γ ⊢ A ≈ A' @ l ] ->
  (forall a, RA a a <-> RA' a a) ->
  releq (SqRel G Γ l A RA) (SqRel G Γ l' A' RA').
Proof using EL.
  intros Hl HA HAA HR.
  pose proof (lequiv_sym _ _ _ Hl) as Hl'.
  assert (HA' : [ G ; Γ ⊢g A' @ l' ])
    by (eapply wft_lconv; [exact (eqty_wf_r ge_typeof (geq_ty_sound HAA)) | exact Hl']).
  assert (HA'A : [ G ; Γ ⊢ A' ≈ A @ l' ]) by exact (geq_ty_lconv (geq_ty_sym HAA) Hl').
  intros t t'; split; intros [H H']; split.
  all: first [ eapply (SqU_conv Hl HA HAA); [intros a; apply HR | assumption]
             | eapply (SqU_conv Hl' HA' HA'A); [intros a; apply HR | assumption] ].
Qed.

(** The carrier's relation matters only on its diagonal, up to [releq]. *)
Lemma SqRel_releq {G Γ l A RA RA'} : releq RA RA' ->
  releq (SqRel G Γ l A RA) (SqRel G Γ l A RA').
Proof using .
  intros HR t t'; split; intros [H H']; split.
  all: match goal with H : SqU _ _ _ _ _ ?u |- SqU _ _ _ _ _ ?u =>
         destruct H as (w & Hw & Hn); exists w; split; [exact Hw|];
         destruct Hn as [k C a Hk HC Ha | ν Hν];
         [apply sqnf_sq; [exact Hk | exact HC | apply HR, Ha] | now apply sqnf_ne] end.
Qed.

(** ** Well-founded trees (M13a) *)

Lemma releq_sym' {R R' : tm -> tm -> Prop} : releq R R' -> releq R' R.
Proof using . intros H ??; symmetry; apply H. Qed.

Lemma WRel_inv {G Γ l1 l2 A B domR codR t t'} : WRel G Γ l1 l2 A B domR codR t t' ->
  exists w w', [ G ; Γ ⊢g t ⤳* w : tyW l1 l2 A B @ lmax l1 l2 ] /\
    [ G ; Γ ⊢g t' ⤳* w' : tyW l1 l2 A B @ lmax l1 l2 ] /\
    [ G ; Γ ⊢ w ≈ w' : tyW l1 l2 A B @ lmax l1 l2 ] /\ WNf G Γ l1 l2 A B domR codR w w'.
Proof using . destruct 1; eauto 7. Qed.

Lemma WRel_wf {G Γ l1 l2 A B domR codR t t'} : WRel G Γ l1 l2 A B domR codR t t' ->
  [ G ; Γ ⊢g t : tyW l1 l2 A B @ lmax l1 l2 ] /\ [ G ; Γ ⊢g t' : tyW l1 l2 A B @ lmax l1 l2 ].
Proof using .
  intros (w & w' & Hw & Hw' & _ & _)%WRel_inv.
  exact (conj (tmred_wf _ _ _ _ _ _ _ Hw) (tmred_wf _ _ _ _ _ _ _ Hw')).
Qed.

(** [WhRel] is symmetric and moves along type equalities. *)
Lemma WhRel_sym {G Γ T l t t'} : WhRel G Γ T l t t' -> WhRel G Γ T l t' t.
Proof using EL.
  intros (w & w' & H & H' & N & N' & Ew). exists w', w.
  exact (conj H' (conj H (conj N' (conj N (geq_tm_sym Ew))))).
Qed.

Lemma WhRel_conv {G Γ T T' l l' t t'} : WhRel G Γ T l t t' -> [ G ; Γ ⊢g T ≅ T' @ l ] ->
  lequiv (gL G) l' l -> WhRel G Γ T' l' t t'.
Proof using EL.
  intros (w & w' & H & H' & N & N' & Ew) HT Hl. exists w, w'.
  refine (conj _ (conj _ (conj N (conj N' _)))).
  - eapply tmred_lconv; [eapply tmred_conv; [apply ge_typeof | exact H | exact HT] | exact Hl].
  - eapply tmred_lconv; [eapply tmred_conv; [apply ge_typeof | exact H' | exact HT] | exact Hl].
  - eapply geq_tm_lconv; [eapply geq_tm_conv; [exact Ew | exact HT] | exact Hl].
Qed.

(** [WRel] along pointwise equivalent shape and position relations. *)
Lemma WRel_dir :
  forall G Γ l1 l2 A B domR codR t t', WRel G Γ l1 l2 A B domR codR t t' ->
  forall (domR' : DomRel G Γ) (codR' : CodRel G Γ domR'),
    (forall ρ, releq (domR ρ) (domR' ρ)) ->
    (forall ρ x y h h', releq (codR ρ x y h) (codR' ρ x y h')) ->
    WRel G Γ l1 l2 A B domR' codR' t t'.
Proof using .
  apply (WRel_mut
    (fun G Γ l1 l2 A B domR codR t t' _ => forall (domR' : DomRel G Γ) (codR' : CodRel G Γ domR'),
       (forall ρ, releq (domR ρ) (domR' ρ)) -> (forall ρ x y h h', releq (codR ρ x y h) (codR' ρ x y h')) ->
       WRel G Γ l1 l2 A B domR' codR' t t')
    (fun G Γ l1 l2 A B domR codR t t' _ => forall (domR' : DomRel G Γ) (codR' : CodRel G Γ domR'),
       (forall ρ, releq (domR ρ) (domR' ρ)) -> (forall ρ x y h h', releq (codR ρ x y h) (codR' ρ x y h')) ->
       WNf G Γ l1 l2 A B domR' codR' t t')).
  - intros * Hw Hw' Heq _ IH domR' codR' Hd Hc. econstructor; [exact Hw | exact Hw' | exact Heq | now apply IH].
  - intros * Hk1 Hk2 Hk1' Hk2' HC HC' HD HD' Ha Hwf Hf IH domR' codR' Hd Hc.
    apply wnf_sup; auto.
    + intros ρ; apply Hd, Ha.
    + intros ρ ha' b b' Hbb * H1 H2 H3 H4 HA1 HB1 HA1' HB1'.
      apply (IH ρ (Ha ρ) b b' (proj2 (Hc ρ _ _ (Ha ρ) ha' b b') Hbb) la lb A1 B1 la' lb' A1' B1'
               H1 H2 H3 H4 HA1 HB1 HA1' HB1'); cbn.
      * intros ρ'; apply Hd.
      * intros ρ' x y h h'; apply Hc.
  - intros * Hν domR' codR' _ _. now apply wnf_ne.
Qed.

Lemma WRel_releq {G Γ l1 l2 A B} {domR domR' : DomRel G Γ} {codR : CodRel G Γ domR} {codR' : CodRel G Γ domR'} :
  (forall ρ, releq (domR ρ) (domR' ρ)) -> (forall ρ x y h h', releq (codR ρ x y h) (codR' ρ x y h')) ->
  releq (WRel G Γ l1 l2 A B domR codR) (WRel G Γ l1 l2 A B domR' codR').
Proof using .
  intros Hd Hc t t'; split; intros H; eapply WRel_dir; try exact H.
  - exact Hd.
  - exact Hc.
  - intros ρ; apply releq_sym', Hd.
  - intros ρ x y h h'; apply releq_sym', Hc.
Qed.

(** ** Finitary well-founded trees (M15a) *)

Lemma WfRel_inv {G Γ l A N domR t t'} : WfRel G Γ l A N domR t t' ->
  exists w w', [ G ; Γ ⊢g t ⤳* w : tyWf l A N @ l ] /\ [ G ; Γ ⊢g t' ⤳* w' : tyWf l A N @ l ] /\
    [ G ; Γ ⊢ w ≈ w' : tyWf l A N @ l ] /\ WfNf G Γ l A N domR w w'.
Proof using . destruct 1; eauto 7. Qed.

Lemma WfRel_wf {G Γ l A N domR t t'} : WfRel G Γ l A N domR t t' ->
  [ G ; Γ ⊢g t : tyWf l A N @ l ] /\ [ G ; Γ ⊢g t' : tyWf l A N @ l ].
Proof using .
  intros (w & w' & Hw & Hw' & _ & _)%WfRel_inv.
  exact (conj (tmred_wf _ _ _ _ _ _ _ Hw) (tmred_wf _ _ _ _ _ _ _ Hw')).
Qed.

(** The three families along a pointwise equivalent shape relation. *)
Lemma WfRel_dir_all :
  (forall G Γ l A N domR t t', WfRel G Γ l A N domR t t' ->
     forall domR' : DomRel G Γ, (forall ρ, releq (domR ρ) (domR' ρ)) -> WfRel G Γ l A N domR' t t') /\
  (forall G Γ l A N domR t t', WfNf G Γ l A N domR t t' ->
     forall domR' : DomRel G Γ, (forall ρ, releq (domR ρ) (domR' ρ)) -> WfNf G Γ l A N domR' t t') /\
  (forall G Γ l A N domR k t t', VecSp G Γ l A N domR k t t' ->
     forall domR' : DomRel G Γ, (forall ρ, releq (domR ρ) (domR' ρ)) -> VecSp G Γ l A N domR' k t t').
Proof using .
  apply WfRel_comb; intros.
  all: try solve [econstructor; eauto].
  all: try solve [eapply vsp_succ; eauto].
  all: apply wfnf_sup; auto.
  all: intros ρ; apply H0, d.
Qed.

Lemma WfRel_releq {G Γ l A N} {domR domR' : DomRel G Γ} :
  (forall ρ, releq (domR ρ) (domR' ρ)) ->
  releq (WfRel G Γ l A N domR) (WfRel G Γ l A N domR').
Proof using .
  intros Hd t t'; split; intros H; eapply (proj1 WfRel_dir_all); try exact H.
  - exact Hd.
  - intros ρ; apply releq_sym', Hd.
Qed.

(** ** Indexed W-types (M17b) *)

Lemma IWfRel_inv {G Γ l li X A N Ot C idxR domR m t t'} : IWfRel G Γ l li X A N Ot C idxR domR m t t' ->
  exists w w', [ G ; Γ ⊢g t ⤳* w : tyIWf l li X A N Ot C m @ lmax l li ] /\
    [ G ; Γ ⊢g t' ⤳* w' : tyIWf l li X A N Ot C m @ lmax l li ] /\
    [ G ; Γ ⊢ w ≈ w' : tyIWf l li X A N Ot C m @ lmax l li ] /\ IWfNf G Γ l li X A N Ot C idxR domR m w w'.
Proof using . destruct 1; eauto 7. Qed.

Lemma IWfRel_wf {G Γ l li X A N Ot C idxR domR m t t'} : IWfRel G Γ l li X A N Ot C idxR domR m t t' ->
  [ G ; Γ ⊢g t : tyIWf l li X A N Ot C m @ lmax l li ] /\ [ G ; Γ ⊢g t' : tyIWf l li X A N Ot C m @ lmax l li ].
Proof using .
  intros (w & w' & Hw & Hw' & _ & _)%IWfRel_inv.
  exact (conj (tmred_wf _ _ _ _ _ _ _ Hw) (tmred_wf _ _ _ _ _ _ _ Hw')).
Qed.

(** The three families along pointwise equivalent index and shape relations. *)
Lemma IWfRel_dir_all :
  (forall G Γ l li X A N Ot C idxR domR m t t', IWfRel G Γ l li X A N Ot C idxR domR m t t' ->
     forall idxR' domR' : DomRel G Γ, (forall ρ, releq (idxR ρ) (idxR' ρ)) -> (forall ρ, releq (domR ρ) (domR' ρ)) ->
     IWfRel G Γ l li X A N Ot C idxR' domR' m t t') /\
  (forall G Γ l li X A N Ot C idxR domR m t t', IWfNf G Γ l li X A N Ot C idxR domR m t t' ->
     forall idxR' domR' : DomRel G Γ, (forall ρ, releq (idxR ρ) (idxR' ρ)) -> (forall ρ, releq (domR ρ) (domR' ρ)) ->
     IWfNf G Γ l li X A N Ot C idxR' domR' m t t') /\
  (forall G Γ l li X A N Ot C idxR domR c k t t', DVecISp G Γ l li X A N Ot C idxR domR c k t t' ->
     forall idxR' domR' : DomRel G Γ, (forall ρ, releq (idxR ρ) (idxR' ρ)) -> (forall ρ, releq (domR ρ) (domR' ρ)) ->
     DVecISp G Γ l li X A N Ot C idxR' domR' c k t t').
Proof using .
  apply IWfRel_comb; intros.
  all: try solve [econstructor; eauto].
  all: try solve [eapply visp_succ; eauto].
  apply iwfnf_sup; auto.
  all: intros ρ; match goal with
                 | E : forall ρ, releq (?R ρ) (?R' ρ), H : forall ρ, ?R ρ _ _ |- ?R' _ _ _ => apply E, H
                 end.
Qed.

Lemma IWfRel_releq {G Γ l li X A N Ot C} {idxR idxR' domR domR' : DomRel G Γ} {m} :
  (forall ρ, releq (idxR ρ) (idxR' ρ)) -> (forall ρ, releq (domR ρ) (domR' ρ)) ->
  releq (IWfRel G Γ l li X A N Ot C idxR domR m) (IWfRel G Γ l li X A N Ot C idxR' domR' m).
Proof using .
  intros Hi Hd t t'; split; intros H; eapply (proj1 IWfRel_dir_all); try exact H.
  - exact Hi.
  - exact Hd.
  - intros ρ; apply releq_sym', Hi.
  - intros ρ; apply releq_sym', Hd.
Qed.

(** ** Heather's indexed [M] (M18b) *)

Lemma MRn_gen {n G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' shR posR m m' t t'} :
  MRn n G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' shR posR m m' t t' ->
  MGen G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' m m' t t'.
Proof using . destruct n; intros H; exact (proj1 H). Qed.

Lemma MR_gen {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' shR posR m m' t t'} :
  MR G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' shR posR m m' t t' ->
  MGen G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' m m' t t'.
Proof using . intros H. exact (MRn_gen (H 0)). Qed.

(** [Σ]'s and [Π]'s relations along included component relations (the
    domain contravariantly at [Π]). *)
Lemma SigRel_impl {G Γ l1 l2 l3 l4 A B A' B'} {domR domR' : DomRel G Γ}
    {codR : CodRel G Γ domR} {codR' : CodRel G Γ domR'} {t t'} :
  (forall ρ a a', domR ρ a a' -> domR' ρ a a') ->
  (forall ρ a a' h h' u u', codR ρ a a' h u u' -> codR' ρ a a' h' u u') ->
  SigRel G Γ l1 l2 l3 l4 A B A' B' domR codR t t' -> SigRel G Γ l1 l2 l3 l4 A B A' B' domR' codR' t t'.
Proof using .
  intros Hd Hc (w & w' & H1 & H2 & H3 & H4 & H5 & H6 & HK).
  exists w, w'. do 6 (split; [assumption|]).
  intros ρ la lb la' lb' A1 B1 A1' B1' Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8.
  destruct (HK ρ la lb la' lb' A1 B1 A1' B1' Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8) as [h Hh].
  exists (Hd _ _ _ h). exact (Hc _ _ _ h _ _ _ Hh).
Qed.

Lemma PiRel_impl {G Γ l1 l2 l3 l4 A B A' B'} {domR domR' : DomRel G Γ}
    {codR : CodRel G Γ domR} {codR' : CodRel G Γ domR'} {t t'} :
  (forall ρ a a', domR' ρ a a' -> domR ρ a a') ->
  (forall ρ a a' h h' u u', codR ρ a a' h u u' -> codR' ρ a a' h' u u') ->
  PiRel G Γ l1 l2 l3 l4 A B A' B' domR codR t t' -> PiRel G Γ l1 l2 l3 l4 A B A' B' domR' codR' t t'.
Proof using .
  intros Hd Hc (w & w' & H1 & H2 & H3 & H4 & H5 & H6 & HK).
  exists w, w'. do 6 (split; [assumption|]).
  intros ρ a a' ha la lb la' lb' A1 B1 A1' B1' Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8.
  exact (Hc _ _ _ (Hd _ _ _ ha) ha _ _ (HK ρ a a' (Hd _ _ _ ha) la lb la' lb' A1 B1 A1' B1' Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8)).
Qed.

(** [MRn] along included shapes' relations and including positions'
    relations. *)
Lemma MRn_impl n : forall G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C'
    (shR shR' : MShRel G Γ) (posR posR' : MPosRel G Γ) m m' t t',
  (forall ρ x x' a a', shR ρ x x' a a' -> shR' ρ x x' a a') ->
  (forall ρ x x' a a' p p', posR' ρ x x' a a' p p' -> posR ρ x x' a a' p p') ->
  MRn n G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' shR posR m m' t t' ->
  MRn n G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' shR' posR' m m' t t'.
Proof using .
  induction n as [|n IH]; intros * Hs Hp [Hg Ho]; (split; [exact Hg|]); [exact I|].
  intros ρ0; unfold MObs; intros * HA HA'. eapply SigRel_impl; [| | exact (Ho ρ0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HA HA')].
  - intros ρ a a'. apply Hs.
  - intros ρ a a' h h' u u'. apply PiRel_impl.
    + intros ρ' p p'. apply Hp.
    + intros ρ' p p' hp hp' v v'. apply IH; intros *; [apply Hs | apply Hp].
Qed.

Lemma MR_releq {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C'} {shR shR' : MShRel G Γ}
    {posR posR' : MPosRel G Γ} {m m'} :
  (forall ρ x x', releq (shR ρ x x') (shR' ρ x x')) ->
  (forall ρ x x' a a', releq (posR ρ x x' a a') (posR' ρ x x' a a')) ->
  releq (MR G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' shR posR m m')
        (MR G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' shR' posR' m m').
Proof using .
  intros Hs Hp t t'; split; intros H n; eapply MRn_impl; try exact (H n); intros *; first [apply Hs | apply Hp].
Qed.

(** ** Escape for contextual types *)

Lemma ModRel_escape_ty {G Γ T T' l R} : ModRel G Γ T T' l R ->
  [ G ; Γ ⊢g T @ l ] /\ [ G ; Γ ⊢g T' @ l ] /\ [ G ; Γ ⊢ T ≈ T' @ l ].
Proof using EL.
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
Proof using EL.
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
Proof using EL.
  destruct 1 as [T T' l Δ Δ' k k' R Hl Hk HT HT' HΔ Hgeq HR
                | T T' l Δ Δ' A A' k k' R Hl Hk HT HT' HΔ HA HA' Hgeq HR];
    intros t t' Htt; apply HR in Htt; destruct Htt as (w & w' & Hw & Hw' & Heq & _ & _ & _).
  all: exact (box_escape_tm (tyred_eq _ _ _ _ _ _ HT) Hl Hgeq Hw Hw' Heq).
Qed.

(** ** Escape for types *)

Theorem escape_ty n rec G Γ T T' l R :
  LR n rec G Γ T T' l R ->
  [ G ; Γ ⊢g T @ l ] /\ [ G ; Γ ⊢g T' @ l ] /\ [ G ; Γ ⊢ T ≈ T' @ l ].
Proof using EL.
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
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l l1 l2 A A' N N' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l l1 l2 A A' RA R Hl Hl2 Hw HT HT' HA HAA HRA Hps Hpt HR
                | G Γ T T' l l1 li1 l2 li2 X X' A A' N N' Ot Ot' C C' m m' idxR domR R Hl Hl2 Hli2 Hw Hwi
                    HT HT' HX HX' HA HA' HN HN' HO HO' HC HC' Hmt Hmt' HXX HAA HNN HOO HCC Hmm
                    idxAd Hisym Histr domAd arAd otAd chAd ixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR].
  all: try solve [exact (ModRel_escape_ty HM)].
  all: split; [apply HT | split; [apply HT' | eapply geq_ty_exp; [exact HT | exact HT' |]]].
  - eapply geq_ty_lconv; [|exact Hl]. eapply geq_ty_nat, tyred_ctx, HT.
  - eapply geq_ty_lconv; [eapply geq_ty_U; [eapply tyred_ctx, HT|]|].
    + solve [apply lequiv_sym; assumption].
    + exact Hl.
  - now apply gne_ty_geq.
  - eapply geq_ty_lconv; [|exact Hl]. apply geq_ty_pi; auto using lequiv_sym.
  - eapply geq_ty_lconv; [exact Hgeq | exact Hl].
  - eapply geq_ty_lconv; [exact Hgeq | exact Hl].
  - eapply geq_ty_lconv; [|exact Hl]. apply geq_ty_sig; auto using lequiv_sym.
  - eapply geq_ty_lconv; [|exact Hl]. apply geq_ty_unit; [eapply tyred_ctx, HT | solve [apply lequiv_sym; assumption]].
  - eapply geq_ty_lconv; [|exact Hl]. apply geq_ty_seq; auto using lequiv_sym.
  - eapply geq_ty_lconv; [|exact Hl]. apply geq_ty_sempty; [eapply tyred_ctx, HT | solve [apply lequiv_sym; assumption]].
  - eapply geq_ty_lconv; [|exact Hl]. apply geq_ty_id; auto using lequiv_sym.
  - eapply geq_ty_lconv; [|exact Hl]. apply geq_ty_empty; [eapply tyred_ctx, HT | solve [apply lequiv_sym; assumption]].
  - eapply geq_ty_lconv; [|exact Hl]. apply geq_ty_sum; auto using lequiv_sym.
  - eapply geq_ty_lconv; [|exact Hl]. apply geq_ty_W; auto using lequiv_sym.
  - eapply geq_ty_lconv; [|exact Hl]. apply geq_ty_wf; auto using lequiv_sym.
  - eapply geq_ty_lconv; [|exact Hl]. apply geq_ty_sq; auto using lequiv_sym.
  - eapply geq_ty_lconv; [|exact Hl]. apply geq_ty_iwf; auto using lequiv_sym.
  - eapply geq_ty_lconv; [|exact Hl]. apply geq_ty_M; auto using lequiv_sym.
Qed.

(** ** Escape for terms *)

Theorem escape_tm n rec G Γ T T' l R :
  LR n rec G Γ T T' l R -> forall t t', R t t' ->
  [ G ; Γ ⊢g t : T @ l ] /\ [ G ; Γ ⊢g t' : T @ l ] /\ [ G ; Γ ⊢ t ≈ t' : T @ l ].
Proof using EL.
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
                    HRA HRB Hpa Hta Hpb Htb HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                    [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l l1 l2 A A' N N' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN domAd arAd HR
                | G Γ T T' l l1 l2 A A' RA R Hl Hl2 Hw HT HT' HA HAA HRA Hps Hpt HR
                | G Γ T T' l l1 li1 l2 li2 X X' A A' N N' Ot Ot' C C' m m' idxR domR R Hl Hl2 Hli2 Hw Hwi
                    HT HT' HX HX' HA HA' HN HN' HO HO' HC HC' Hmt Hmt' HXX HAA HNN HOO HCC Hmm
                    idxAd Hisym Histr domAd arAd otAd chAd ixAd HR
                | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                    Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                    HmXX HmAA HmBB HmCC Hmmm midxAd mshAd mposAd mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR];
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
  - (* Empty: irrelevant *)
    destruct (EmptyRel_wf Htt) as [Ht Ht'].
    assert (HTE : [ G ; Γ ⊢g T ≅ tyEmpty l1 @ l ]) by apply HT.
    repeat split.
    + eapply conv_tm; [exact Ht | exact HTE | exact Hl].
    + eapply conv_tm; [exact Ht' | exact HTE | exact Hl].
    + eapply conv_geq_tm; [exact (geq_tm_empty_irr Hw Ht Ht') | apply eqty_sym, HTE | exact Hl].
  - (* +: related weak-head normal forms *)
    destruct Htt as (w & w' & Hw' & Hw'' & Heq & _).
    assert (HTS : [ G ; Γ ⊢g T ≅ tySum u1 u2 UA UB @ l ]) by apply HT.
    repeat split.
    + eapply conv_tm; [apply Hw' | exact HTS | exact Hl].
    + eapply conv_tm; [apply Hw'' | exact HTS | exact Hl].
    + eapply conv_geq_tm; [eapply geq_tm_exp; eauto | apply eqty_sym, HTS | exact Hl].
  - (* W: related weak-head normal forms *)
    destruct (WRel_inv Htt) as (w & w' & Hw' & Hw'' & Heq & _).
    assert (HTW : [ G ; Γ ⊢g T ≅ tyW l1 l2 A B @ l ]) by apply HT.
    repeat split.
    + eapply conv_tm; [apply Hw' | exact HTW | exact Hl].
    + eapply conv_tm; [apply Hw'' | exact HTW | exact Hl].
    + eapply conv_geq_tm; [eapply geq_tm_exp; eauto | apply eqty_sym, HTW | exact Hl].
  - (* Wf: related weak-head normal forms *)
    destruct (WfRel_inv Htt) as (w & w' & Hw' & Hw'' & Heq & _).
    assert (HTW : [ G ; Γ ⊢g T ≅ tyWf l1 A N @ l ]) by apply HT.
    repeat split.
    + eapply conv_tm; [apply Hw' | exact HTW | exact Hl].
    + eapply conv_tm; [apply Hw'' | exact HTW | exact Hl].
    + eapply conv_geq_tm; [eapply geq_tm_exp; eauto | apply eqty_sym, HTW | exact Hl].
  - (* ∥·∥: irrelevant *)
    destruct (SqRel_wf Htt) as [Ht Ht'].
    assert (HTS : [ G ; Γ ⊢g T ≅ tySq l1 A @ l ]) by apply HT.
    repeat split.
    + eapply conv_tm; [exact Ht | exact HTS | exact Hl].
    + eapply conv_tm; [exact Ht' | exact HTS | exact Hl].
    + eapply conv_geq_tm; [exact (geq_tm_sq_irr Hw Ht Ht') | apply eqty_sym, HTS | exact Hl].
  - (* IWf: related weak-head normal forms *)
    destruct (IWfRel_inv Htt) as (w & w' & Hw' & Hw'' & Heq & _).
    assert (HTW : [ G ; Γ ⊢g T ≅ tyIWf l1 li1 X A N Ot C m @ l ]) by apply HT.
    repeat split.
    + eapply conv_tm; [apply Hw' | exact HTW | exact Hl].
    + eapply conv_tm; [apply Hw'' | exact HTW | exact Hl].
    + eapply conv_geq_tm; [eapply geq_tm_exp; eauto | apply eqty_sym, HTW | exact Hl].
  - (* M: the generic clause *)
    destruct (MR_gen Htt) as (w & w' & Hw' & Hw'' & _ & _ & Heq & _).
    assert (HTW : [ G ; Γ ⊢g T ≅ tyM ml1 ml2 mli mX mA mB mC mm @ l ]) by apply HT.
    assert (HM' : [ G ; Γ ⊢g tyM ml1 ml2 mli mX mA mB mC mm ≅ tyM mr1 mr2 mri mX' mA' mB' mC' mm' @ mlvl ml1 ml2 mli ])
      by (apply geq_ty_sound, geq_ty_M; auto using lequiv_sym).
    assert (Hw3 : [ G ; Γ ⊢g t' ⤳* w' : tyM ml1 ml2 mli mX mA mB mC mm @ mlvl ml1 ml2 mli ])
      by (eapply tmred_conv; [apply ge_typeof | exact Hw'' | apply eqty_sym, HM']).
    repeat split.
    + eapply conv_tm; [apply Hw' | exact HTW | exact Hl].
    + eapply conv_tm; [apply Hw3 | exact HTW | exact Hl].
    + eapply conv_geq_tm; [eapply geq_tm_exp; eauto | apply eqty_sym, HTW | exact Hl].
Qed.

(** ** Local weakening at the instance's layer *)

Lemma wf_ty_wkr {G Γ Δ r T l} :
  wkr r Δ Γ -> [ G ; Δ ⊢g ] -> [ G ; Γ ⊢g T @ l ] -> [ G ; Δ ⊢g T⟨r⟩ @ l ].
Proof using . intros; eapply weakening_r; eauto using ge_typeof. Qed.
Lemma wf_tm_wkr {G Γ Δ r t T l} :
  wkr r Δ Γ -> [ G ; Δ ⊢g ] -> [ G ; Γ ⊢g t : T @ l ] -> [ G ; Δ ⊢g t⟨r⟩ : T⟨r⟩ @ l ].
Proof using . intros; eapply weakening_r; eauto using ge_typeof. Qed.
Lemma eqty_wkr {G Γ Δ r T T' l} :
  wkr r Δ Γ -> [ G ; Δ ⊢g ] -> [ G ; Γ ⊢g T ≅ T' @ l ] -> [ G ; Δ ⊢g T⟨r⟩ ≅ T'⟨r⟩ @ l ].
Proof using . intros; eapply weakening_r; eauto using ge_typeof. Qed.

(** The Kripke index is OPE data; the generic laws take its renaming. *)
Lemma wf_ty_wk {G Γ Δ} {ρ : wk} {T l} :
  ρ : Δ ≤ Γ -> [ G ; Δ ⊢g ] -> [ G ; Γ ⊢g T @ l ] -> [ G ; Δ ⊢g T⟨ρ⟩ @ l ].
Proof using . intros Hρ; apply wf_ty_wkr, wk_wf_wkr, Hρ. Qed.
Lemma wf_tm_wk {G Γ Δ} {ρ : wk} {t T l} :
  ρ : Δ ≤ Γ -> [ G ; Δ ⊢g ] -> [ G ; Γ ⊢g t : T @ l ] -> [ G ; Δ ⊢g t⟨ρ⟩ : T⟨ρ⟩ @ l ].
Proof using . intros Hρ; apply wf_tm_wkr, wk_wf_wkr, Hρ. Qed.
Lemma eqty_wk {G Γ Δ} {ρ : wk} {T T' l} :
  ρ : Δ ≤ Γ -> [ G ; Δ ⊢g ] -> [ G ; Γ ⊢g T ≅ T' @ l ] -> [ G ; Δ ⊢g T⟨ρ⟩ ≅ T'⟨ρ⟩ @ l ].
Proof using . intros Hρ; apply eqty_wkr, wk_wf_wkr, Hρ. Qed.
Lemma geq_ty_wk' {G Γ Δ} {ρ : wk} {T T' l} :
  ρ : Δ ≤ Γ -> [ G ; Δ ⊢g ] -> [ G ; Γ ⊢ T ≈ T' @ l ] -> [ G ; Δ ⊢ T⟨ρ⟩ ≈ T'⟨ρ⟩ @ l ].
Proof using EL. intros Hρ; apply geq_ty_wk, wk_wf_wkr, Hρ. Qed.
Lemma gne_ty_wk' {G Γ Δ} {ρ : wk} {V V' l} :
  ρ : Δ ≤ Γ -> [ G ; Δ ⊢g ] -> [ G ; Γ ⊢ V ~ V' @ l ] -> [ G ; Δ ⊢ V⟨ρ⟩ ~ V'⟨ρ⟩ @ l ].
Proof using EL. intros Hρ; apply gne_ty_wk, wk_wf_wkr, Hρ. Qed.
Lemma geq_tm_wk' {G Γ Δ} {ρ : wk} {t t' T l} :
  ρ : Δ ≤ Γ -> [ G ; Δ ⊢g ] -> [ G ; Γ ⊢ t ≈ t' : T @ l ] -> [ G ; Δ ⊢ t⟨ρ⟩ ≈ t'⟨ρ⟩ : T⟨ρ⟩ @ l ].
Proof using EL. intros Hρ; apply geq_tm_wk, wk_wf_wkr, Hρ. Qed.
Lemma gne_tm_wk' {G Γ Δ} {ρ : wk} {t t' T l} :
  ρ : Δ ≤ Γ -> [ G ; Δ ⊢g ] -> [ G ; Γ ⊢ t ~ t' : T @ l ] -> [ G ; Δ ⊢ t⟨ρ⟩ ~ t'⟨ρ⟩ : T⟨ρ⟩ @ l ].
Proof using EL. intros Hρ; apply gne_tm_wk, wk_wf_wkr, Hρ. Qed.
Lemma tyred_wk' {G Γ Δ} {ρ : wk} {T W l} :
  ρ : Δ ≤ Γ -> [ G ; Δ ⊢g ] -> [ G ; Γ ⊢g T ⤳* W @ l ] -> [ G ; Δ ⊢g T⟨ρ⟩ ⤳* W⟨ρ⟩ @ l ].
Proof using . intros Hρ HΔ H; eapply tyred_wk; eauto using ge_typeof, wk_wf_wkr. Qed.
Lemma tmred_wk' {G Γ Δ} {ρ : wk} {t w T l} :
  ρ : Δ ≤ Γ -> [ G ; Δ ⊢g ] -> [ G ; Γ ⊢g t ⤳* w : T @ l ] ->
  [ G ; Δ ⊢g t⟨ρ⟩ ⤳* w⟨ρ⟩ : T⟨ρ⟩ @ l ].
Proof using . intros Hρ HΔ H; eapply tmred_wk; eauto using ge_typeof, wk_wf_wkr. Qed.

Lemma wkr_lift {Γ Δ} {ρ : wk} {A l} :
  ρ : Δ ≤ Γ -> wkr (rlift ρ) (Δ ,, A⟨ρ⟩ @ l) (Γ ,, A @ l).
Proof using . intros Hρ; constructor; now apply wk_wf_wkr. Qed.

Lemma ext_wf_g {G Γ A l} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l -> [ G ; Γ ,, A @ l ⊢g ].
Proof using . intros; apply wfc_ext; eauto using ctx_of_ty. Qed.

(** The type of a [sup]'s children, along equalities of its pieces. *)
Lemma W_fty_eq {G Γ l1 l2 l3 l4 A A' B B' a a'} :
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢g A @ l1 ] -> [ G ; Γ ⊢ A ≈ A' @ l1 ] -> [ G ; Γ ,, A @ l1 ⊢ B ≈ B' @ l2 ] ->
  [ G ; Γ ⊢ B[lsingle a] ≈ B'[lsingle a'] @ l2 ] ->
  [ G ; Γ ⊢ tyPi l2 (lmax l1 l2) B[lsingle a] (tyW l1 l2 A B)⟨↑⟩
          ≈ tyPi l4 (lmax l3 l4) B'[lsingle a'] (tyW l3 l4 A' B')⟨↑⟩ @ lmax l2 (lmax l1 l2) ].
Proof using EL.
  intros H13 H24 HA HAA HBB HBa.
  pose proof (eqty_wf_l ge_typeof (geq_ty_sound HBa)) as HBa'.
  assert (HΔ : [ G ; Γ ,, B[lsingle a] @ l2 ⊢g ]) by (apply ext_wf_g; [exact HBa' | exact (lequiv_wf_l _ _ _ H24)]).
  apply geq_ty_pi; [exact H24 | now apply lequiv_max | exact HBa' | exact HBa |].
  exact (geq_ty_wk (wkr_shift1 _ _ _) HΔ (geq_ty_W H13 H24 HA HAA HBB)).
Qed.

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
Proof using EL. gwa_generic. Qed.
Lemma geq_ty_gwa {γ G' G Γ T T' l} : gwk_ok γ G' G -> [ ⊢ G' ] ->
  [ G ; Γ ⊢ T ≈ T' @ l ] -> [ G' ; Γ⟦γ⟧ ⊢ T⟦γ⟧ ≈ T'⟦γ⟧ @ l ].
Proof using EL. gwa_generic. Qed.
Lemma gne_tm_gwa {γ G' G Γ t t' T l} : gwk_ok γ G' G -> [ ⊢ G' ] ->
  [ G ; Γ ⊢ t ~ t' : T @ l ] -> [ G' ; Γ⟦γ⟧ ⊢ t⟦γ⟧ ~ t'⟦γ⟧ : T⟦γ⟧ @ l ].
Proof using EL. gwa_generic. Qed.
Lemma geq_tm_gwa {γ G' G Γ t t' T l} : gwk_ok γ G' G -> [ ⊢ G' ] ->
  [ G ; Γ ⊢ t ≈ t' : T @ l ] -> [ G' ; Γ⟦γ⟧ ⊢ t⟦γ⟧ ≈ t'⟦γ⟧ : T⟦γ⟧ @ l ].
Proof using EL. gwa_generic. Qed.

Lemma gwa_tyred {γ G' G i Γ T W l} : gwk_ok γ G' G -> [ ⊢ G' ] ->
  [ G ; Γ ⊢[ i ] T ⤳* W @ l ] -> [ G' ; Γ⟦γ⟧ ⊢[ i ] T⟦γ⟧ ⤳* W⟦γ⟧ @ l ].
Proof using . intros Hγ HG []; split; eauto using gwa_ty, reds_ty_gwa, gwa_eqty. Qed.
Lemma gwa_tmred {γ G' G i Γ t w T l} : gwk_ok γ G' G -> [ ⊢ G' ] ->
  [ G ; Γ ⊢[ i ] t ⤳* w : T @ l ] -> [ G' ; Γ⟦γ⟧ ⊢[ i ] t⟦γ⟧ ⤳* w⟦γ⟧ : T⟦γ⟧ @ l ].
Proof using . intros Hγ HG []; split; eauto using gwa_tm, reds_gwa, gwa_eqtm. Qed.

(** ** Kripke weakenings *)

Lemma kw_gL {G Γ} (ρ : kwk G Γ) : gL G <= gL (kw_G ρ).
Proof using . exact (proj1 (kw_gok ρ)). Qed.
Lemma kw_glob {G Γ} (ρ : kwk G Γ) : [ ⊢ kw_G ρ ].
Proof using . exact (ctx_glob _ _ _ (kw_ctx ρ)). Qed.
Lemma kw_lequiv {G Γ} (ρ : kwk G Γ) {l l'} : lequiv (gL G) l l' -> lequiv (gL (kw_G ρ)) l l'.
Proof using . apply lequiv_weaken, kw_gL. Qed.
Lemma kw_lwf {G Γ} (ρ : kwk G Γ) {l} : lwf (gL G) l -> lwf (gL (kw_G ρ)) l.
Proof using . apply lwf_weaken, kw_gL. Qed.
(** A level of the world equivalent to one of the base is one of the base
    (M3_DESIGN.md E14). *)
Lemma kw_lequiv_shrink {G Γ} (ρ : kwk G Γ) {l l'} : lequiv (gL (kw_G ρ)) l l' -> lwf (gL G) l' ->
  lequiv (gL G) l l'.
Proof using . apply lequiv_shrink. Qed.

Section Kw.
Context {G : gctx} {Γ : ctx} (ρ : kwk G Γ).
Local Notation Hγ := (kw_gok ρ).
Local Notation HG' := (kw_glob ρ).
Local Notation Hr := (kw_wf ρ).
Local Notation HΔ := (kw_ctx ρ).

Lemma kw_ty {T l} : [ G ; Γ ⊢g T @ l ] -> [ kw_G ρ ; kw_Δ ρ ⊢g kty ρ T @ l ].
Proof using . intros H. exact (wf_ty_wk Hr HΔ (gwa_ty Hγ HG' H)). Qed.
Lemma kw_tm {t T l} : [ G ; Γ ⊢g t : T @ l ] -> [ kw_G ρ ; kw_Δ ρ ⊢g ktm ρ t : kty ρ T @ l ].
Proof using . intros H. exact (wf_tm_wk Hr HΔ (gwa_tm Hγ HG' H)). Qed.
Lemma kw_eqty {T T' l} : [ G ; Γ ⊢g T ≅ T' @ l ] ->
  [ kw_G ρ ; kw_Δ ρ ⊢g kty ρ T ≅ kty ρ T' @ l ].
Proof using . intros H. exact (eqty_wk Hr HΔ (gwa_eqty Hγ HG' H)). Qed.
Lemma kw_geq_ty {T T' l} : [ G ; Γ ⊢ T ≈ T' @ l ] -> [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ T ≈ kty ρ T' @ l ].
Proof using EL. intros H. exact (geq_ty_wk' Hr HΔ (geq_ty_gwa Hγ HG' H)). Qed.
Lemma kw_gne_ty {V V' l} : [ G ; Γ ⊢ V ~ V' @ l ] -> [ kw_G ρ ; kw_Δ ρ ⊢ kty ρ V ~ kty ρ V' @ l ].
Proof using EL. intros H. exact (gne_ty_wk' Hr HΔ (gne_ty_gwa Hγ HG' H)). Qed.
Lemma kw_geq_tm {t t' T l} : [ G ; Γ ⊢ t ≈ t' : T @ l ] ->
  [ kw_G ρ ; kw_Δ ρ ⊢ ktm ρ t ≈ ktm ρ t' : kty ρ T @ l ].
Proof using EL. intros H. exact (geq_tm_wk' Hr HΔ (geq_tm_gwa Hγ HG' H)). Qed.
Lemma kw_gne_tm {t t' T l} : [ G ; Γ ⊢ t ~ t' : T @ l ] ->
  [ kw_G ρ ; kw_Δ ρ ⊢ ktm ρ t ~ ktm ρ t' : kty ρ T @ l ].
Proof using EL. intros H. exact (gne_tm_wk' Hr HΔ (gne_tm_gwa Hγ HG' H)). Qed.
Lemma kw_tyred {T W l} : [ G ; Γ ⊢g T ⤳* W @ l ] -> [ kw_G ρ ; kw_Δ ρ ⊢g kty ρ T ⤳* kty ρ W @ l ].
Proof using . intros H. exact (tyred_wk' Hr HΔ (gwa_tyred Hγ HG' H)). Qed.
Lemma kw_tmred {t w T l} : [ G ; Γ ⊢g t ⤳* w : T @ l ] ->
  [ kw_G ρ ; kw_Δ ρ ⊢g ktm ρ t ⤳* ktm ρ w : kty ρ T @ l ].
Proof using . intros H. exact (tmred_wk' Hr HΔ (gwa_tmred Hγ HG' H)). Qed.

(** Under one local binder. *)
Lemma kw_ext {A l} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l -> [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ⊢g ].
Proof using . intros HA Hl. apply ext_wf_g; [now apply kw_ty | now apply kw_lwf]. Qed.

Lemma kw_wkr_l {A l} : wkr (rlift (kw_r ρ)) (kw_Δ ρ ,, kty ρ A @ l) ((Γ ,, A @ l)⟦kw_γ ρ⟧).
Proof using . rewrite gwa_cext. exact (wkr_lift Hr). Qed.

Lemma kw_ty_l {A l B l'} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l ->
  [ G ; Γ ,, A @ l ⊢g B @ l' ] -> [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ⊢g ktyl ρ B @ l' ].
Proof using .
  intros HA Hl H. exact (wf_ty_wkr kw_wkr_l (kw_ext HA Hl) (gwa_ty Hγ HG' H)).
Qed.
Lemma kw_tm_l {A l t T l'} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l ->
  [ G ; Γ ,, A @ l ⊢g t : T @ l' ] -> [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ⊢g ktml ρ t : ktyl ρ T @ l' ].
Proof using .
  intros HA Hl H. exact (wf_tm_wkr kw_wkr_l (kw_ext HA Hl) (gwa_tm Hγ HG' H)).
Qed.
Lemma kw_geq_ty_l {A l B B' l'} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l ->
  [ G ; Γ ,, A @ l ⊢ B ≈ B' @ l' ] ->
  [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ⊢ ktyl ρ B ≈ ktyl ρ B' @ l' ].
Proof using EL.
  intros HA Hl H. exact (geq_ty_wk kw_wkr_l (kw_ext HA Hl) (geq_ty_gwa Hγ HG' H)).
Qed.
Lemma kw_geq_nat_l {A l t t'} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l ->
  [ G ; Γ ,, A @ l ⊢ t ≈ t' : tyNat @ lzero ] ->
  [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ⊢ ktml ρ t ≈ ktml ρ t' : tyNat @ lzero ].
Proof using EL.
  intros HA Hl H. pose proof (geq_tm_wk kw_wkr_l (kw_ext HA Hl) (geq_tm_gwa Hγ HG' H)) as X.
  rewrite gwa_tyNat in X. exact X.
Qed.
Lemma kw_tm_nat_l {A l t} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l ->
  [ G ; Γ ,, A @ l ⊢g t : tyNat @ lzero ] -> [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ⊢g ktml ρ t : tyNat @ lzero ].
Proof using .
  intros HA Hl H. pose proof (kw_tm_l HA Hl H) as X. unfold ktyl in X. rewrite gwa_tyNat in X. exact X.
Qed.

(** Under one global binder (the meta-functions, M5): [⇑γ], then the
    local renaming. *)
Lemma kw_gok_up D : gwk_ok (gwk_up' (kw_γ ρ)) (gext (kw_G ρ) (gdecl_gwa (kw_γ ρ) D)) (gext G D).
Proof using .
  pose proof (kw_gok ρ) as [HL Hw]. split; [exact HL|]. cbn [gΨ gext].
  destruct (kw_γ ρ) as [|γ0|γ0] eqn:Eγ; cbn [gwk_up' gdecl_gwa].
  - assert (EΨ : gΨ (kw_G ρ) = gΨ G) by (inversion Hw; reflexivity). rewrite EΨ. constructor.
  - apply gwkwf_up. exact Hw.
  - apply gwkwf_up. exact Hw.
Qed.

Lemma kw_body_ctx D : [ ⊢ gext (kw_G ρ) (gdecl_gwa (kw_γ ρ) D) ] ->
  [ gext (kw_G ρ) (gdecl_gwa (kw_γ ρ) D) ; (kw_Δ ρ)⟪S⟫ ⊢g ].
Proof using .
  intros HG. exact (gwk_ctx (gwk_ok_step (G := kw_G ρ) (D := gdecl_gwa (kw_γ ρ) D)) HG HΔ).
Qed.

Lemma kw_wkr_g : wkr (kw_r ρ) (kw_Δ ρ)⟪S⟫ (Γ⟦kw_γ ρ⟧)⟪S⟫.
Proof using . apply wkr_gren, wk_wf_wkr, Hr. Qed.

Lemma kw_body_ty {D T l} : [ ⊢ gext (kw_G ρ) (gdecl_gwa (kw_γ ρ) D) ] ->
  [ gext G D ; Γ⟪S⟫ ⊢g T @ l ] -> [ gext (kw_G ρ) (gdecl_gwa (kw_γ ρ) D) ; (kw_Δ ρ)⟪S⟫ ⊢g kbody ρ T @ l ].
Proof using .
  intros HG H. pose proof (gwa_ty (kw_gok_up D) HG H) as X. rewrite gwa_up'_shift in X.
  exact (wf_ty_wkr kw_wkr_g (kw_body_ctx D HG) X).
Qed.
Lemma kw_body_eqty {D T T' l} : [ ⊢ gext (kw_G ρ) (gdecl_gwa (kw_γ ρ) D) ] ->
  [ gext G D ; Γ⟪S⟫ ⊢g T ≅ T' @ l ] ->
  [ gext (kw_G ρ) (gdecl_gwa (kw_γ ρ) D) ; (kw_Δ ρ)⟪S⟫ ⊢g kbody ρ T ≅ kbody ρ T' @ l ].
Proof using .
  intros HG H. pose proof (gwa_eqty (kw_gok_up D) HG H) as X. rewrite !gwa_up'_shift in X.
  exact (eqty_wkr kw_wkr_g (kw_body_ctx D HG) X).
Qed.
Lemma kw_body_tm {D t T l} : [ ⊢ gext (kw_G ρ) (gdecl_gwa (kw_γ ρ) D) ] ->
  [ gext G D ; Γ⟪S⟫ ⊢g t : T @ l ] ->
  [ gext (kw_G ρ) (gdecl_gwa (kw_γ ρ) D) ; (kw_Δ ρ)⟪S⟫ ⊢g kbodyt ρ t : kbody ρ T @ l ].
Proof using .
  intros HG H. pose proof (gwa_tm (kw_gok_up D) HG H) as X. rewrite gwa_up'_shift in X.
  exact (wf_tm_wkr kw_wkr_g (kw_body_ctx D HG) X).
Qed.

End Kw.

(** ** Composition of Kripke weakenings on syntax *)

Lemma ren_wk_comp_ty (T : ty) (ρ ρ' : wk) : T⟨ρ⟩⟨ρ'⟩ = T⟨wk_comp ρ' ρ⟩.
Proof using . apply ren_ren_ty; intros; now rewrite rlk_wk_comp. Qed.
Lemma ren_wk_comp (t : tm) (ρ ρ' : wk) : t⟨ρ⟩⟨ρ'⟩ = t⟨wk_comp ρ' ρ⟩.
Proof using . apply ren_ren; intros; now rewrite rlk_wk_comp. Qed.
Lemma ren_wk_comp_lift_ty (T : ty) (ρ ρ' : wk) :
  T⟨rlift ρ⟩⟨rlift ρ'⟩ = T⟨rlift (wk_comp ρ' ρ)⟩.
Proof using .
  apply ren_ren_ty; intros [|n]; rewrite !rlk_rlift; auto. now rewrite rlk_wk_comp.
Qed.

Lemma kty_comp {G Γ} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) T :
  kty (kw_comp ρ ρ') T = kty ρ' (kty ρ T).
Proof using . unfold kty; rewrite kw_γ_comp, kw_r_comp. now rewrite gwa_ren_ty, gwa_comp_ty, ren_wk_comp_ty. Qed.
Lemma ktm_comp {G Γ} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) t :
  ktm (kw_comp ρ ρ') t = ktm ρ' (ktm ρ t).
Proof using . unfold ktm; rewrite kw_γ_comp, kw_r_comp. now rewrite gwa_ren, gwa_comp_tm, ren_wk_comp. Qed.
Lemma ktyl_comp {G Γ} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) T :
  ktyl (kw_comp ρ ρ') T = ktyl ρ' (ktyl ρ T).
Proof using . unfold ktyl; rewrite kw_γ_comp, kw_r_comp. now rewrite gwa_ren_ty, gwa_comp_ty, ren_wk_comp_lift_ty. Qed.

Lemma gwk_up'_comp γ' γ : gwk_comp (gwk_up' γ') (gwk_up' γ) = gwk_up' (gwk_comp γ' γ).
Proof using . destruct γ', γ; cbn; rewrite ?gwk_comp_id_r; reflexivity. Qed.

Lemma kbody_comp {G Γ} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) T :
  kbody (kw_comp ρ ρ') T = kbody ρ' (kbody ρ T).
Proof using . unfold kbody; rewrite kw_γ_comp, kw_r_comp. now rewrite gwa_ren_ty, gwa_comp_ty, gwk_up'_comp, ren_wk_comp_ty. Qed.
Lemma kbodyt_comp {G Γ} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) t :
  kbodyt (kw_comp ρ ρ') t = kbodyt ρ' (kbodyt ρ t).
Proof using . unfold kbodyt; rewrite kw_γ_comp, kw_r_comp. now rewrite gwa_ren, gwa_comp_tm, gwk_up'_comp, ren_wk_comp. Qed.

Lemma gwa_comp_ctx' (Δ : ctx) {G Γ} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) :
  Δ⟦kw_γ (kw_comp ρ ρ')⟧ = Δ⟦kw_γ ρ⟧⟦kw_γ ρ'⟧.
Proof using . rewrite kw_γ_comp. now rewrite gwa_comp_ctx. Qed.

(** ** Kripke weakenings on constructors *)

Section KwPush.
Context {G : gctx} {Γ : ctx} (ρ : kwk G Γ).
Lemma kty_tyNat : kty ρ tyNat = tyNat. Proof using . unfold kty; now rewrite gwa_tyNat. Qed.
Lemma kty_tyU l : kty ρ (tyU l) = tyU l. Proof using . unfold kty; now rewrite gwa_tyU. Qed.
Lemma kty_tyUnit l : kty ρ (tyUnit l) = tyUnit l. Proof using . unfold kty; now rewrite gwa_tyUnit. Qed.
Lemma kty_tySEq l A a b : kty ρ (tySEq l A a b) = tySEq l (kty ρ A) (ktm ρ a) (ktm ρ b).
Proof using . unfold kty, ktm; now rewrite gwa_tySEq. Qed.
Lemma kty_tySEmpty l : kty ρ (tySEmpty l) = tySEmpty l. Proof using . unfold kty; now rewrite gwa_tySEmpty. Qed.
Lemma kty_tyEmpty l : kty ρ (tyEmpty l) = tyEmpty l. Proof using . unfold kty; now rewrite gwa_tyEmpty. Qed.
Lemma kty_tySum l l' A B : kty ρ (tySum l l' A B) = tySum l l' (kty ρ A) (kty ρ B).
Proof using . unfold kty; now rewrite gwa_tySum. Qed.
Lemma ktm_inl l l' A B a : ktm ρ (tmInl l l' A B a) = tmInl l l' (kty ρ A) (kty ρ B) (ktm ρ a).
Proof using . unfold ktm, kty; now rewrite gwa_inl. Qed.
Lemma ktm_inr l l' A B a : ktm ρ (tmInr l l' A B a) = tmInr l l' (kty ρ A) (kty ρ B) (ktm ρ a).
Proof using . unfold ktm, kty; now rewrite gwa_inr. Qed.
Lemma ktm_elimEmpty l l' M t : ktm ρ (elimEmpty l l' M t) = elimEmpty l l' (ktyl ρ M) (ktm ρ t).
Proof using . unfold ktm, ktyl; now rewrite gwa_elimEmpty. Qed.
Lemma ktm_srefl l A a : ktm ρ (srefl l A a) = srefl l (kty ρ A) (ktm ρ a).
Proof using . unfold ktm, kty; now rewrite gwa_srefl. Qed.
Lemma ktm_elimSEmpty l l' M e : ktm ρ (elimSEmpty l l' M e) = elimSEmpty l l' (kty ρ M) (ktm ρ e).
Proof using . unfold ktm, kty; now rewrite gwa_elimSEmpty. Qed.
Lemma kty_tyId l A a b : kty ρ (tyId l A a b) = tyId l (kty ρ A) (ktm ρ a) (ktm ρ b).
Proof using . unfold kty, ktm; now rewrite gwa_tyId. Qed.
Lemma ktm_refl l A a : ktm ρ (tmRefl l A a) = tmRefl l (kty ρ A) (ktm ρ a).
Proof using . unfold ktm, kty; now rewrite gwa_refl. Qed.
Lemma kty_tyPi l l' A B : kty ρ (tyPi l l' A B) = tyPi l l' (kty ρ A) (ktyl ρ B).
Proof using . unfold kty, ktyl; now rewrite gwa_tyPi. Qed.
Lemma kty_tySig l l' A B : kty ρ (tySig l l' A B) = tySig l l' (kty ρ A) (ktyl ρ B).
Proof using . unfold kty, ktyl; now rewrite gwa_tySig. Qed.
Lemma kty_tyW l l' A B : kty ρ (tyW l l' A B) = tyW l l' (kty ρ A) (ktyl ρ B).
Proof using . unfold kty, ktyl; now rewrite gwa_tyW. Qed.
Lemma ktm_sup l l' A B a f : ktm ρ (tmSup l l' A B a f) = tmSup l l' (kty ρ A) (ktyl ρ B) (ktm ρ a) (ktm ρ f).
Proof using . unfold ktm, kty, ktyl; now rewrite gwa_sup. Qed.
Lemma ktm_app t l l' A B s : ktm ρ (app t l l' A B s) = app (ktm ρ t) l l' (kty ρ A) (ktyl ρ B) (ktm ρ s).
Proof using . unfold ktm, kty, ktyl; now rewrite gwa_app. Qed.
Lemma ktm_fst l l' A B p : ktm ρ (tmFst l l' A B p) = tmFst l l' (kty ρ A) (ktyl ρ B) (ktm ρ p).
Proof using . unfold ktm, kty, ktyl; now rewrite gwa_fst. Qed.
Lemma ktm_snd l l' A B p : ktm ρ (tmSnd l l' A B p) = tmSnd l l' (kty ρ A) (ktyl ρ B) (ktm ρ p).
Proof using . unfold ktm, kty, ktyl; now rewrite gwa_snd. Qed.
Lemma ktm_pair l l' A B a b :
  ktm ρ (tmPair l l' A B a b) = tmPair l l' (kty ρ A) (ktyl ρ B) (ktm ρ a) (ktm ρ b).
Proof using . unfold ktm, kty, ktyl; now rewrite gwa_pair. Qed.
Lemma kty_tyEl l t : kty ρ (tyEl l t) = tyEl l (ktm ρ t).
Proof using . unfold kty, ktm; now rewrite gwa_tyEl. Qed.
Lemma ktm_zero : ktm ρ zero = zero. Proof using . unfold ktm; now rewrite gwa_zero. Qed.
Lemma ktm_succ t : ktm ρ (succ t) = succ (ktm ρ t). Proof using . unfold ktm; now rewrite gwa_succ. Qed.
Lemma ktm_lam l l' A t : ktm ρ (lam l l' A t) = lam l l' (kty ρ A) (ktml ρ t).
Proof using . unfold ktm, kty, ktml; now rewrite gwa_lam. Qed.
(** The meta-functions (M5): the body moves under [⇑γ]. *)
Lemma kty_tyCPi l T : kty ρ (tyCPi l T) = tyCPi l (kbody ρ T).
Proof using . unfold kty, kbody; now destruct (kw_γ ρ). Qed.
Lemma kty_tyTPi Δ l l' T : kty ρ (tyTPi Δ l l' T) = tyTPi Δ⟦kw_γ ρ⟧ l l' (kbody ρ T).
Proof using . unfold kty, kbody; now destruct (kw_γ ρ). Qed.
Lemma ktm_clam l T t : ktm ρ (clam l T t) = clam l (kbody ρ T) (kbodyt ρ t).
Proof using . unfold ktm, kbody, kbodyt; now destruct (kw_γ ρ). Qed.
Lemma ktm_tlam Δ l l' T t : ktm ρ (tlam Δ l l' T t) = tlam Δ⟦kw_γ ρ⟧ l l' (kbody ρ T) (kbodyt ρ t).
Proof using . unfold ktm, kbody, kbodyt; now destruct (kw_γ ρ). Qed.
Lemma ktm_capp t Δ : ktm ρ (capp t Δ) = capp (ktm ρ t) Δ⟦kw_γ ρ⟧.
Proof using . unfold ktm; now destruct (kw_γ ρ). Qed.
Lemma ktm_tapp t A : ktm ρ (tapp t A) = tapp (ktm ρ t) A⟦kw_γ ρ⟧.
Proof using . unfold ktm; now destruct (kw_γ ρ). Qed.
(** Vectors, finite indices and finitary trees (M14a, M15a). *)
Lemma kty_tyVec l A n : kty ρ (tyVec l A n) = tyVec l (kty ρ A) (ktm ρ n).
Proof using . unfold kty, ktm; now rewrite gwa_tyVec. Qed.
Lemma kty_tyFin n : kty ρ (tyFin n) = tyFin (ktm ρ n).
Proof using . unfold kty, ktm; now rewrite gwa_tyFin. Qed.
Lemma kty_tyWf l A N : kty ρ (tyWf l A N) = tyWf l (kty ρ A) (ktml ρ N).
Proof using . unfold kty, ktml; now rewrite gwa_tyWf. Qed.
Lemma ktm_supf l A N a cs : ktm ρ (tmSupf l A N a cs) = tmSupf l (kty ρ A) (ktml ρ N) (ktm ρ a) (ktm ρ cs).
Proof using . unfold ktm, kty, ktml; now rewrite gwa_supf. Qed.
(** Propositional truncation (M16a). *)
Lemma kty_tySq l A : kty ρ (tySq l A) = tySq l (kty ρ A).
Proof using . unfold kty; now rewrite gwa_tySq. Qed.
(** Dependent tuples (M17a). *)
Lemma kty_tyDVec l n F : kty ρ (tyDVec l n F) = tyDVec l (ktm ρ n) (ktyl ρ F).
Proof using . unfold kty, ktm, ktyl; now rewrite gwa_tyDVec. Qed.
Lemma ktm_sq l A a : ktm ρ (tmSq l A a) = tmSq l (kty ρ A) (ktm ρ a).
Proof using . unfold ktm, kty; now rewrite gwa_sq. Qed.
Lemma ktml_shift (t : tm) : ktml ρ t⟨↑⟩ = (ktm ρ t)⟨↑⟩.
Proof using . unfold ktm, ktml. now rewrite gwa_ren, shift_lift. Qed.
Lemma ktm_single (t : tm) a : ktm ρ t[lsingle a] = (ktml ρ t)[lsingle (ktm ρ a)].
Proof using . unfold ktm, ktml. now rewrite gwa_subst, gwa_lsingle, lsingle_ren. Qed.
End KwPush.

Lemma ren_wk_comp_lift (t : tm) (ρ ρ' : wk) :
  t⟨rlift ρ⟩⟨rlift ρ'⟩ = t⟨rlift (wk_comp ρ' ρ)⟩.
Proof using .
  apply ren_ren; intros [|n]; rewrite !rlk_rlift; auto. now rewrite rlk_wk_comp.
Qed.
Lemma ktml_comp {G Γ} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) t :
  ktml (kw_comp ρ ρ') t = ktml ρ' (ktml ρ t).
Proof using . unfold ktml; rewrite kw_γ_comp, kw_r_comp. now rewrite gwa_ren, gwa_comp_tm, ren_wk_comp_lift. Qed.

(** ** Natural numbers: the normal forms' shapes (M15a) *)

Lemma NatNf_whnf_l {G Γ w w'} : NatNf G Γ w w' -> whnf w.
Proof using EL. destruct 1; eauto using gne_tm_whne_l with whnf. Qed.
Lemma NatNf_whnf_r {G Γ w w'} : NatNf G Γ w w' -> whnf w'.
Proof using EL. destruct 1; eauto using gne_tm_whne_r with whnf. Qed.

Lemma NatRel_geq {G Γ t t'} : NatRel G Γ t t' -> [ G ; Γ ⊢ t ≈ t' : tyNat @ lzero ].
Proof using EL. destruct 1 as [t t' w w' Hw Hw' Heq _]. exact (geq_tm_exp Hw Hw' Heq). Qed.

(** How the right side of a [NatRel] reduces, given how the left one does. *)
Lemma NatRel_inv_zero {G Γ k k'} : NatRel G Γ k k' -> [ G ; Γ ⊢g k ⤳* zero : tyNat @ lzero ] ->
  [ G ; Γ ⊢g k' ⤳* zero : tyNat @ lzero ].
Proof using EL.
  destruct 1 as [k k' w w' Hw Hw' _ Hn]; intros Hz.
  assert (Ew : w = zero)
    by (eapply tmred_whnf_det; [exact Hw | exact Hz | exact (NatNf_whnf_l Hn) | constructor]).
  subst w. inversion Hn; subst; [exact Hw'|].
  match goal with H : [ _ ; _ ⊢ zero ~ _ : _ @ _ ] |- _ =>
    pose proof (gne_tm_whne_l H) as X; inversion X end.
Qed.

Lemma NatRel_inv_succ {G Γ k k' m} : NatRel G Γ k k' -> [ G ; Γ ⊢g k ⤳* succ m : tyNat @ lzero ] ->
  exists m', [ G ; Γ ⊢g k' ⤳* succ m' : tyNat @ lzero ] /\ NatRel G Γ m m'.
Proof using EL.
  destruct 1 as [k k' w w' Hw Hw' _ Hn]; intros Hs.
  assert (Ew : w = succ m)
    by (eapply tmred_whnf_det; [exact Hw | exact Hs | exact (NatNf_whnf_l Hn) | constructor]).
  subst w. inversion Hn; subst; [eexists; split; [exact Hw' | assumption]|].
  match goal with H : [ _ ; _ ⊢ succ _ ~ _ : _ @ _ ] |- _ =>
    pose proof (gne_tm_whne_l H) as X; inversion X end.
Qed.

Lemma NatRel_inv_ne {G Γ k k' ν} : NatRel G Γ k k' -> [ G ; Γ ⊢g k ⤳* ν : tyNat @ lzero ] -> whne ν ->
  exists ν', [ G ; Γ ⊢g k' ⤳* ν' : tyNat @ lzero ] /\ [ G ; Γ ⊢ ν ~ ν' : tyNat @ lzero ].
Proof using EL.
  destruct 1 as [k k' w w' Hw Hw' _ Hn]; intros Hν Nν.
  assert (Ew : w = ν)
    by (eapply tmred_whnf_det; [exact Hw | exact Hν | exact (NatNf_whnf_l Hn) | now constructor]).
  subst w. inversion Hn; subst; try solve [inversion Nν].
  eexists; split; [exact Hw' | assumption].
Qed.

(** Neutrals along convertible types on both sides. *)
Lemma NeRel_conv2 {G Γ V V' W W' l t t'} : [ G ; Γ ⊢g V ≅ W @ l ] -> [ G ; Γ ⊢g V' ≅ W' @ l ] ->
  NeRel G Γ V V' l t t' -> NeRel G Γ W W' l t t'.
Proof using EL.
  intros HV HV' (ν & ν' & H1 & H2 & H3 & H4). exists ν, ν'.
  refine (conj _ (conj _ (conj _ _))).
  - eapply tmred_conv; [apply ge_typeof | exact H1 | exact HV].
  - eapply tmred_conv; [apply ge_typeof | exact H2 | exact HV'].
  - eapply gne_tm_conv; [exact H3 | exact HV].
  - eapply gne_tm_conv; [exact H4 | exact HV'].
Qed.

(** ** Vectors at related lengths (M14a, M15a) *)

Lemma tyred_step {G Γ T W l} :
  [ G ; Γ ⊢g T @ l ] -> red_ty T W -> [ G ; Γ ⊢g T ≅ W @ l ] -> [ G ; Γ ⊢g T ⤳* W @ l ].
Proof using . intros HT Hr HE; split; auto. econstructor; [exact Hr | constructor]. Qed.

Lemma wf_zero_g {G Δ} : [ G ; Δ ⊢g ] -> [ G ; Δ ⊢g zero : tyNat @ lzero ].
Proof using . intros HΔ. apply wf_zero; [exact ge_notV | now rewrite ge_typeof]. Qed.

Lemma tyred_vec {G Δ l A m w} : lwf (gL G) l -> [ G ; Δ ⊢g A @ l ] ->
  [ G ; Δ ⊢g m ⤳* w : tyNat @ lzero ] -> [ G ; Δ ⊢g tyVec l A m ⤳* tyVec l A w @ l ].
Proof using .
  intros Hw HA [Hm Hr He]. split.
  - apply wft_vec; [exact ge_notV | exact Hw | exact HA | exact Hm].
  - now apply reds_vec.
  - apply eqty_vec; [exact ge_notV | now apply lequiv_refl | exact HA | now apply eqty_refl | exact He].
Qed.

Lemma tyred_vec_zero {G Δ l A} : lwf (gL G) l -> [ G ; Δ ⊢g A @ l ] ->
  [ G ; Δ ⊢g tyVec l A zero ⤳* tyUnit l @ l ].
Proof using .
  intros Hw HA. pose proof (wf_zero_g (ctx_of_ty HA)) as Hz.
  apply tyred_step; [apply wft_vec; [exact ge_notV | exact Hw | exact HA | exact Hz] | constructor |].
  apply eqty_vec_zero; [exact ge_compt | exact Hw | exact HA].
Qed.

Lemma tyred_vec_succ {G Δ l A k} : lwf (gL G) l -> [ G ; Δ ⊢g A @ l ] ->
  [ G ; Δ ⊢g k : tyNat @ lzero ] ->
  [ G ; Δ ⊢g tyVec l A (succ k) ⤳* tySig l l A (tyVec l A⟨↑⟩ k⟨↑⟩) @ l ].
Proof using .
  intros Hw HA Hk. assert (Hs : [ G ; Δ ⊢g succ k : tyNat @ lzero ]) by (apply wf_succ; [exact ge_notV | exact Hk]).
  apply tyred_step; [apply wft_vec; [exact ge_notV | exact Hw | exact HA | exact Hs] | constructor |].
  apply eqty_vec_succ; [exact ge_compt | exact Hw | exact HA | exact Hk].
Qed.

(** [DVec]'s reductions (M17a). *)
Lemma tyred_dvec {G Δ l F m w} : lwf (gL G) l -> [ G ; Δ ,, tyFin m @ lzero ⊢g F @ l ] ->
  [ G ; Δ ⊢g m ⤳* w : tyNat @ lzero ] -> [ G ; Δ ⊢g tyDVec l m F ⤳* tyDVec l w F @ l ].
Proof using .
  intros Hw HF [Hm Hr He]. split.
  - apply wft_dvec; [exact (compt_notV _ ge_compt) | exact Hw | exact Hm | exact HF].
  - now apply reds_dvec.
  - apply eqty_dvec; [exact (compt_notV _ ge_compt) | now apply lequiv_refl | exact Hm | exact He | exact HF | now apply eqty_refl].
Qed.

Lemma tyred_dvec_zero {G Δ l F} : lwf (gL G) l -> [ G ; Δ ,, tyFin zero @ lzero ⊢g F @ l ] ->
  [ G ; Δ ⊢g tyDVec l zero F ⤳* tyUnit l @ l ].
Proof using .
  intros Hw HF. assert (HΔ : [ G ; Δ ⊢g ]) by (pose proof (ctx_of_ty HF) as X; inversion X; assumption).
  pose proof (wf_zero_g HΔ) as Hz.
  apply tyred_step; [apply wft_dvec; [exact (compt_notV _ ge_compt) | exact Hw | exact Hz | exact HF] | constructor |].
  apply eqty_dvec_zero; [exact ge_compt | exact Hw | exact HF].
Qed.

Lemma tyred_dvec_succ {G Δ l F k} : lwf (gL G) l -> [ G ; Δ ,, tyFin (succ k) @ lzero ⊢g F @ l ] ->
  [ G ; Δ ⊢g k : tyNat @ lzero ] ->
  [ G ; Δ ⊢g tyDVec l (succ k) F ⤳* tySig l l (dvecHd k F) (dvecTl l k F) @ l ].
Proof using .
  intros Hw HF Hk. assert (Hs : [ G ; Δ ⊢g succ k : tyNat @ lzero ]) by (apply wf_succ; [exact ge_notV | exact Hk]).
  apply tyred_step; [apply wft_dvec; [exact (compt_notV _ ge_compt) | exact Hw | exact Hs | exact HF] | constructor |].
  apply eqty_dvec_succ; [exact ge_compt | exact Hw | exact Hk | exact HF].
Qed.

(** [Vec] types at [NatRel]-related lengths are generically equal. *)
Lemma geq_vec_nat {G Γ} : forall k k', NatRel G Γ k k' ->
  forall l l' T T', lequiv (gL G) l l' -> [ G ; Γ ⊢g T @ l ] -> [ G ; Γ ⊢ T ≈ T' @ l ] ->
  [ G ; Γ ⊢ tyVec l T k ≈ tyVec l' T' k' @ l ].
Proof using EL.
  apply (NatRel_mut G Γ
    (fun k k' _ => forall l l' T T', lequiv (gL G) l l' -> [ G ; Γ ⊢g T @ l ] -> [ G ; Γ ⊢ T ≈ T' @ l ] ->
       [ G ; Γ ⊢ tyVec l T k ≈ tyVec l' T' k' @ l ])
    (fun k k' _ => forall l l' T T', lequiv (gL G) l l' -> [ G ; Γ ⊢g T @ l ] -> [ G ; Γ ⊢ T ≈ T' @ l ] ->
       [ G ; Γ ⊢ tyVec l T k ≈ tyVec l' T' k' @ l ])).
  - intros t t' w w' Ht Ht' _ _ IH l l' T T' Hl HT HTT.
    pose proof (lequiv_wf_l _ _ _ Hl) as Hw. pose proof (lequiv_wf_r _ _ _ Hl) as Hw'.
    pose proof (eqty_wf_r ge_typeof (geq_ty_sound HTT)) as HT'.
    assert (HT'l : [ G ; Γ ⊢g T' @ l' ]) by (eapply wft_lconv; [exact HT' | solve [apply lequiv_sym; assumption]]).
    eapply geq_ty_exp; [exact (tyred_vec Hw HT Ht) | | exact (IH l l' T T' Hl HT HTT)].
    exact (tyred_lconv _ _ _ _ (tyred_vec Hw' HT'l Ht') Hl).
  - intros l l' T T' Hl HT HTT.
    pose proof (lequiv_wf_l _ _ _ Hl) as Hw. pose proof (lequiv_wf_r _ _ _ Hl) as Hw'.
    pose proof (eqty_wf_r ge_typeof (geq_ty_sound HTT)) as HT'.
    assert (HT'l : [ G ; Γ ⊢g T' @ l' ]) by (eapply wft_lconv; [exact HT' | solve [apply lequiv_sym; assumption]]).
    eapply geq_ty_exp; [exact (tyred_vec_zero Hw HT) | exact (tyred_lconv _ _ _ _ (tyred_vec_zero Hw' HT'l) Hl) |].
    exact (geq_ty_unit (ctx_of_ty HT) Hl).
  - intros t t' Htt IH l l' T T' Hl HT HTT.
    pose proof (lequiv_wf_l _ _ _ Hl) as Hw. pose proof (lequiv_wf_r _ _ _ Hl) as Hw'.
    pose proof (eqty_wf_r ge_typeof (geq_ty_sound HTT)) as HT'.
    assert (HT'l : [ G ; Γ ⊢g T' @ l' ]) by (eapply wft_lconv; [exact HT' | solve [apply lequiv_sym; assumption]]).
    destruct Htt as [t t' u u' Hu Hu' Huu Hn].
    pose proof (tmred_wf _ _ _ _ _ _ _ Hu) as Hk. pose proof (tmred_wf _ _ _ _ _ _ _ Hu') as Hk'.
    assert (HΓT : [ G ; Γ ,, T @ l ⊢g ]) by now apply ext_wf_g.
    eapply geq_ty_exp; [exact (tyred_vec_succ Hw HT Hk) | exact (tyred_lconv _ _ _ _ (tyred_vec_succ Hw' HT'l Hk') Hl) |].
    eapply geq_ty_lconv; [apply geq_ty_sig; [exact Hl | exact Hl | exact HT | exact HTT |] | apply lequiv_sym, lmax_idem, Hw].
    exact (geq_ty_wk (wkr_shift1 _ _ _) HΓT (IH l l' T T' Hl HT HTT)).
  - intros ν ν' Hνν l l' T T' Hl HT HTT.
    exact (gne_ty_geq (gne_ty_vec Hl HT HTT Hνν)).
Qed.

(** The type of a nonempty vector's projections, along equal data. *)
Lemma sigvec_eq {G Γ l l' T T' m m'} : lequiv (gL G) l l' -> lwf (gL G) l ->
  [ G ; Γ ⊢g T @ l ] -> [ G ; Γ ⊢g T ≅ T' @ l ] -> [ G ; Γ ⊢g m ≅ m' : tyNat @ lzero ] ->
  [ G ; Γ ⊢g tySig l l T (tyVec l T⟨↑⟩ m⟨↑⟩) ≅ tySig l' l' T' (tyVec l' T'⟨↑⟩ m'⟨↑⟩) @ lmax l l ].
Proof using .
  intros Hl Hw HT HTT Hm.
  assert (HΓT : [ G ; Γ ,, T @ l ⊢[ typeof ge_layer ] ]) by (rewrite ge_typeof; now apply ext_wf_g).
  apply eqty_sig; [exact ge_notV | exact Hl | exact Hl | exact HT | exact HTT |].
  apply eqty_vec; [exact ge_notV | exact Hl | | |].
  - exact (wk1_ty_g _ _ _ _ _ _ _ HΓT HT).
  - exact (wk1_eqty_g _ _ _ _ _ _ _ _ HΓT HTT).
  - exact (wk1_eqtm_g _ _ _ _ _ _ _ _ _ HΓT Hm).
Qed.

(** The world of the context itself, and of its extension by one entry. *)
Definition kw_self {G Γ} (HΓ : [ G ; Γ ⊢g ]) : kwk G Γ := kw_id HΓ.
Definition kw_wk1 {G Γ A l} (HΓA : [ G ; Γ ,, A @ l ⊢g ]) : kwk G Γ :=
  kw_loc wk1 (wkwf_step _ _ _ _ _ (wkwf_id Γ)) HΓA.

Lemma ktm_self {G Γ} (HΓ : [ G ; Γ ⊢g ]) t : nftm t -> ktm (kw_self HΓ) t = t.
Proof using . intros H. unfold ktm, kw_self, kw_loc; cbn [kw_γ kw_gk kw_r kw_rk gwa wk_ren kw_mk]. now apply ren_id_tm. Qed.
Lemma ktml_self {G Γ} (HΓ : [ G ; Γ ⊢g ]) t : nftm t -> ktml (kw_self HΓ) t = t.
Proof using .
  intros H. unfold ktml, kw_self, kw_loc; cbn [kw_γ kw_gk kw_r kw_rk gwa wk_ren kw_mk].
  rewrite <- (ren_id_tm t H) at 2. apply ren_ext_tm. intros [|n]; rlk_simpl; cbn; lia.
Qed.
Lemma kty_self {G Γ} (HΓ : [ G ; Γ ⊢g ]) T : nfty T -> kty (kw_self HΓ) T = T.
Proof using . intros H. unfold kty, kw_self, kw_loc; cbn [kw_γ kw_gk kw_r kw_rk gwa wk_ren kw_mk]. now apply ren_id_ty. Qed.

End Escape.
