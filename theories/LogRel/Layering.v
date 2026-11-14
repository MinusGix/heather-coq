(** * Layering Restriction (07a:1057)

    On types of MLTT, the types with no contextual type in their type
    structure ([mltt_ty]), the relation does not depend on its parameters
    ([lr_j], [lr_vp]): the contextual-type cases are unreachable, and the
    universe cases decode codes into MLTT types again.  So the [j = P] and
    [j = M] relations coincide there, with the same term relations.

    [mltt_ty] is syntactic and only inspects the type structure, not terms
    (a code never decodes to a contextual type).  Types formed below layer
    M are MLTT types. *)
From DeLaM.LogRel Require Export Def.

(** ** MLTT types *)

Fixpoint mltt_ty (T : ty) : Prop :=
  match T with
  | tyPi _ _ A B | tySig _ _ A B | tySum _ _ A B | tyW _ _ A B => mltt_ty A /\ mltt_ty B
  (* the identity type's relation recurses into its carrier (M11a) *)
  | tyId _ A _ _ => mltt_ty A
  (* [Vec]'s element type is its reduct's first component (M14a) *)
  | tyVec _ A _ => mltt_ty A
  (* [Wf]'s shape relation is a relation at its index type (M15a) *)
  | tyWf _ A _ => mltt_ty A
  (* [∥·∥]'s relation keeps its carrier's (M16a) *)
  | tySq _ A => mltt_ty A
  (* [DVec]'s family is its reducts' components (M17a) *)
  | tyDVec _ _ F => mltt_ty F
  (* [IWf]'s index and shape relations are relations at those types (M17b) *)
  | tyIWf _ _ X A _ _ _ _ => mltt_ty X /\ mltt_ty A
  (* [M]'s index, shape and position relations are relations at those
     types (M18b) *)
  | tyM _ _ _ X A B _ _ => mltt_ty X /\ mltt_ty A /\ mltt_ty B
  | tyIWi _ _ _ X A _ D _ _ _ => mltt_ty X /\ mltt_ty A /\ mltt_ty D
  | tyCTyp _ _ | tyCTrm _ _ _ | tyCPi _ _ | tyTPi _ _ _ _ => False
  | _ => True
  end.

Fixpoint mltt_ctx (Γ : ctx) : Prop :=
  match Γ with
  | cext Γ A _ => mltt_ctx Γ /\ mltt_ty A
  | _ => True
  end.

Lemma mltt_ren (T : ty) r0 : mltt_ty T -> mltt_ty T⟨r0⟩.
Proof.
  revert r0; induction T; intros r0 H; cbn in *; try tauto.
  all: first [destruct H as (H1 & H2 & H3); split; [|split]; [apply IHT1 | apply IHT2 | apply IHT3]; assumption
             | destruct H; split; [apply IHT1 | apply IHT2]; assumption | apply IHT; assumption].
Qed.

Lemma mltt_subst (T : ty) e : mltt_ty T -> mltt_ty T[e].
Proof.
  revert e; induction T; intros e H; cbn in *; try tauto.
  all: first [destruct H as (H1 & H2 & H3); split; [|split]; [apply IHT1 | apply IHT2 | apply IHT3]; assumption
             | destruct H; split; [apply IHT1 | apply IHT2]; assumption | apply IHT; assumption].
Qed.

Lemma mltt_gren (T : ty) ξ : mltt_ty T -> mltt_ty T⟪ξ⟫.
Proof. induction T; cbn in *; tauto. Qed.

Lemma mltt_gwa (T : ty) γ : mltt_ty T -> mltt_ty T⟦γ⟧.
Proof. destruct γ; cbn; [exact id | apply mltt_gren ..]. Qed.

Lemma mltt_ctx_ren (Γ : ctx) ξ : mltt_ctx Γ -> mltt_ctx Γ⟪ξ⟫.
Proof. induction Γ; cbn; try tauto. intros [H1 H2]; split; [apply IHΓ | apply mltt_gren]; assumption. Qed.

Lemma mltt_ctx_gwa (Γ : ctx) γ : mltt_ctx Γ -> mltt_ctx Γ⟦γ⟧.
Proof. destruct γ; cbn; [exact id | apply mltt_ctx_ren ..]. Qed.

Lemma mltt_red {T W} : reds_ty T W -> mltt_ty T -> mltt_ty W.
Proof.
  induction 1 as [| T U W Hs _ IH]; [exact id |].
  intros H; apply IH; destruct Hs; cbn in *; try tauto.
  - split; [exact H | apply mltt_ren, H].
  - split; [apply mltt_subst, H | apply mltt_subst, mltt_ren, mltt_ren, H].
Qed.

Lemma mltt_ctx_lookup {Γ n A l} : in_ctx Γ n A l -> mltt_ctx Γ -> mltt_ty A.
Proof.
  induction 1; cbn; intros [H1 H2]; apply mltt_ren; auto.
Qed.

(** Types formed below layer M. *)
Lemma mltt_wf_ty {G i Γ T l} : [ G ; Γ ⊢[ i ] T @ l ] -> i <> lM -> mltt_ty T.
Proof. induction 1; intros Hi; cbn; try tauto; congruence. Qed.

Lemma mltt_wf_ctx {G i Γ} : [ G ; Γ ⊢[ i ] ] -> i <> lM -> mltt_ctx Γ.
Proof.
  induction 1; intros Hi; cbn; try tauto.
  split; [auto | eapply mltt_wf_ty; eassumption].
Qed.

(** ** The relation at two parameter choices *)

Section Layering.
Context `{E : GenericEq} (LP1 LP2 : LRParams).

Lemma ModRel_mltt {G Γ T T' l R} : @ModRel E LP1 G Γ T T' l R -> mltt_ty T -> False.
Proof.
  intros HM Hm; destruct HM;
    match goal with HT : tyred _ _ _ T _ _ |- _ => exact (mltt_red (tyred_red _ _ _ _ _ _ HT) Hm) end.
Qed.

Lemma URel_layer {rec1 rec2 : lvl -> RedRel} {n G Γ l0} : lmeasure l0 < n ->
  (forall l0, lmeasure l0 < n -> forall G Γ T T' l R, mltt_ty T -> mltt_ty T' ->
     rec1 l0 G Γ T T' l R -> rec2 l0 G Γ T T' l R) ->
  forall t t', URel rec1 G Γ l0 t t' -> URel rec2 G Γ l0 t t'.
Proof.
  intros Hl Hrec t t' (w & w' & H1 & H2 & H3 & H4 & H5 & H6).
  exists w, w'; do 5 (split; [assumption |]).
  intros la lb Ha Hb. destruct (H6 la lb Ha Hb) as [R HR].
  exists R; apply Hrec; cbn; auto.
Qed.

(** One direction, at a stage whose earlier stages go both ways. *)
Lemma LR_layer_dir n (rec1 rec2 : lvl -> RedRel) :
  (forall l0, lmeasure l0 < n -> forall G Γ T T' l R, mltt_ty T -> mltt_ty T' ->
     (rec1 l0 G Γ T T' l R <-> rec2 l0 G Γ T T' l R)) ->
  forall G Γ T T' l R, @LR E LP1 n rec1 G Γ T T' l R -> mltt_ty T -> mltt_ty T' ->
    @LR E LP2 n rec2 G Γ T T' l R.
Proof.
  intros Hrec G Γ T T' l R H.
  induction H as [G Γ T T' l R Hl HT HT' HR | G Γ T T' l l1 l2 R Hl Hl2 Hn HT HT' HR
                 | G Γ T T' l V V' R HT HT' Hne HR
                 | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                     [Hl H3 H4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] Hdom IHdom Hcod IHcod HR
                 | G Γ T T' l R Hj HM
                 | G Γ T T' l l1 l2 T1 T1' instR R Hj
                 | G Γ T T' l Δ1 Δ1' l1 l2 l3 l4 T1 T1' instR R Hj
                 | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                     [Hl H3 H4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] Hdom IHdom Hcod IHcod HR
                 | G Γ T T' l l1 l2 R Hl Hl2 Hw HT HT' HR
                 | G Γ T T' l l1 l2 A A' a a' b b' R Hl Hl2 Hw HT HT' HA HAA Haa Hbb HR
                 | G Γ T T' l l1 l2 R Hl Hl2 Hw HT HT' HR
                 | G Γ T T' l l1 l2 A A' a a' b b' RA R Hl Hl2 Hw HT HT' HA HAA Haa Hbb
                     HRA IHRA Hra Hrb Hps Hpt HR
                 | G Γ T T' l l1 l2 R Hl Hl2 Hw HT HT' HR
                 | G Γ T T' l u1 u2 u3 u4 UA UA' UB UB' RA RB R Hl Hl3 Hl4 Hw1 Hw2 HT HT' HUA HUAA HUB HUBB
                     HRA IHRA HRB IHRB Hpa Hta Hpb Htb HR
                 | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R
                     [Hl H3 H4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] Hdom IHdom Hcod IHcod HR
                 | G Γ T T' l l1 l2 A A' N N' domR R Hl Hl2 Hw HT HT' HA HA' HNt HNt' HAA HNN
                     Hdom IHdom arAd HR
                 | G Γ T T' l l1 l2 A A' RQ R Hl Hl2 Hw HT HT' HA HAA HRQ IHRQ Hqs Hqt HR
                 | G Γ T T' l l1 li1 l2 li2 X X' A A' N N' Ot Ot' C C' m m' idxR domR R Hl Hl2 Hli2 Hw Hwi
                     HT HT' HX HX' HA HA' HN HN' HO HO' HC HC' Hmt Hmt' HXX HAA HNN HOO HCC Hmm
                     Hidx IHidx Hisym Histr Hdom IHdom Har Hot Hch Hix HR
                 | G Γ T T' l ml1 ml2 mli mr1 mr2 mri mX mX' mA mA' mB mB' mC mC' mm mm' midxR mshR mposR R
                     Hl Hmr1 Hmr2 Hmri Hmw1 Hmw2 Hmwi HT HT' HmX HmX' HmA HmA' HmB HmB' HmC HmC' Hmm Hmm'
                     HmXX HmAA HmBB HmCC Hmmm midxAd IHmidx mshAd IHmsh mposAd IHmpos mchAd mgB mgC mgCa mimon mshmon mposmon mixAd HR]; intros Hm Hm'.
  - eapply LRnat; eassumption.
  - eapply LRU; try eassumption.
    intros t t'; rewrite (HR t t'); split; apply (URel_layer (n := n) Hn);
      intros; apply Hrec; assumption.
  - eapply LRne; eassumption.
  - pose proof (mltt_red (tyred_red _ _ _ _ _ _ HT) Hm) as [HmA HmB].
    pose proof (mltt_red (tyred_red _ _ _ _ _ _ HT') Hm') as [HmA' HmB'].
    eapply LRpi; [split|..]; try eassumption.
    + intros ρ; apply IHdom; apply mltt_ren, mltt_gwa; assumption.
    + intros ρ a a' ha; apply IHcod; apply mltt_subst, mltt_ren, mltt_gwa; assumption.
  - destruct (ModRel_mltt HM Hm).
  (* meta-functions are not MLTT types *)
  - match goal with HT : tyred _ _ _ T _ _ |- _ => exact (False_ind _ (mltt_red (tyred_red _ _ _ _ _ _ HT) Hm)) end.
  - match goal with HT : tyred _ _ _ T _ _ |- _ => exact (False_ind _ (mltt_red (tyred_red _ _ _ _ _ _ HT) Hm)) end.
  - pose proof (mltt_red (tyred_red _ _ _ _ _ _ HT) Hm) as [HmA HmB].
    pose proof (mltt_red (tyred_red _ _ _ _ _ _ HT') Hm') as [HmA' HmB'].
    eapply LRsig; [split|..]; try eassumption.
    + intros ρ; apply IHdom; apply mltt_ren, mltt_gwa; assumption.
    + intros ρ a a' ha; apply IHcod; apply mltt_subst, mltt_ren, mltt_gwa; assumption.
  - eapply LRunit; eassumption.
  - eapply LRseq; eassumption.
  - eapply LRsempty; eassumption.
  - pose proof (mltt_red (tyred_red _ _ _ _ _ _ HT) Hm) as HmA.
    pose proof (mltt_red (tyred_red _ _ _ _ _ _ HT') Hm') as HmA'.
    eapply LRid; try eassumption. apply IHRA; assumption.
  - eapply LRempty; eassumption.
  - pose proof (mltt_red (tyred_red _ _ _ _ _ _ HT) Hm) as [HmA HmB].
    pose proof (mltt_red (tyred_red _ _ _ _ _ _ HT') Hm') as [HmA' HmB'].
    eapply (LRsum _ _ _ _ _ _ _ u1 u2 u3 u4 UA UA' UB UB' RA RB); try eassumption;
      [apply IHRA | apply IHRB]; assumption.
  - pose proof (mltt_red (tyred_red _ _ _ _ _ _ HT) Hm) as [HmA HmB].
    pose proof (mltt_red (tyred_red _ _ _ _ _ _ HT') Hm') as [HmA' HmB'].
    eapply LRw; [split|..]; try eassumption.
    + intros ρ; apply IHdom; apply mltt_ren, mltt_gwa; assumption.
    + intros ρ a a' ha; apply IHcod; apply mltt_subst, mltt_ren, mltt_gwa; assumption.
  - pose proof (mltt_red (tyred_red _ _ _ _ _ _ HT) Hm) as HmA.
    pose proof (mltt_red (tyred_red _ _ _ _ _ _ HT') Hm') as HmA'.
    eapply LRwf; try eassumption.
    intros ρ; apply IHdom; apply mltt_ren, mltt_gwa; assumption.
  - pose proof (mltt_red (tyred_red _ _ _ _ _ _ HT) Hm) as HmA.
    pose proof (mltt_red (tyred_red _ _ _ _ _ _ HT') Hm') as HmA'.
    eapply LRsq; try eassumption. apply IHRQ; assumption.
  - pose proof (mltt_red (tyred_red _ _ _ _ _ _ HT) Hm) as [HmX HmA].
    pose proof (mltt_red (tyred_red _ _ _ _ _ _ HT') Hm') as [HmX' HmA'].
    eapply LRiwf; try eassumption; intros ρ; [apply IHidx | apply IHdom]; apply mltt_ren, mltt_gwa; assumption.
  - pose proof (mltt_red (tyred_red _ _ _ _ _ _ HT) Hm) as (LX & LA & LB).
    pose proof (mltt_red (tyred_red _ _ _ _ _ _ HT') Hm') as (LX' & LA' & LB').
    eapply LRm; try eassumption.
    + intros ρ; apply IHmidx; apply mltt_ren, mltt_gwa; assumption.
    + intros ρ x x' hx; apply IHmsh; [exact hx | ..]; apply mltt_subst, mltt_ren, mltt_gwa; assumption.
    + intros ρ x x' a a' hx ha; apply IHmpos; [exact hx | exact ha | ..];
        apply mltt_subst, mltt_ren, mltt_gwa; assumption.
Qed.

End Layering.

Lemma LR_layer `{E : GenericEq} (LP1 LP2 : LRParams) n (rec1 rec2 : lvl -> RedRel) :
  (forall l0, lmeasure l0 < n -> forall G Γ T T' l R, mltt_ty T -> mltt_ty T' ->
     (rec1 l0 G Γ T T' l R <-> rec2 l0 G Γ T T' l R)) ->
  forall G Γ T T' l R, mltt_ty T -> mltt_ty T' ->
    (@LR E LP1 n rec1 G Γ T T' l R <-> @LR E LP2 n rec2 G Γ T T' l R).
Proof.
  intros Hrec G Γ T T' l R Hm Hm'; split; intros H.
  - exact (LR_layer_dir LP1 LP2 n rec1 rec2 Hrec _ _ _ _ _ _ H Hm Hm').
  - refine (LR_layer_dir LP2 LP1 n rec2 rec1 _ _ _ _ _ _ _ H Hm Hm').
    intros; symmetry; apply Hrec; assumption.
Qed.

(** The stages, by induction on the measure. *)
Lemma LR_stage_layer `{E : GenericEq} (LP1 LP2 : LRParams) n :
  forall G Γ T T' l R, mltt_ty T -> mltt_ty T' ->
    (@LR E LP1 n (@LRbelow E LP1 n) G Γ T T' l R <-> @LR E LP2 n (@LRbelow E LP2 n) G Γ T T' l R).
Proof.
  induction n as [n IH] using lt_wf_ind.
  apply LR_layer. intros l0 Hl0 G Γ T T' l R Hm Hm'.
  rewrite !LRbelow_spec by exact Hl0. exact (IH _ Hl0 _ _ _ _ _ _ Hm Hm').
Qed.

Lemma LogRel_layer `{E : GenericEq} (LP1 LP2 : LRParams) l0 G Γ T T' l R :
  mltt_ty T -> mltt_ty T' ->
  (@LogRel E LP1 l0 G Γ T T' l R <-> @LogRel E LP2 l0 G Γ T T' l R).
Proof. apply LR_stage_layer. Qed.
