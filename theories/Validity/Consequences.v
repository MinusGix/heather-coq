(** * Consequences of reducibility

    Canonicity, injectivity and discrimination of type formers, and
    weak-head normalization follow from the reducibility of every
    judgment, which the fundamental theorems give ([Reducible]).  Closed
    canonicity also needs a global context without type or term
    bindings, since global variables are closed neutrals. *)
From DeLaM.Validity Require Export Fundamental.

(** The head of a type, neutral types sharing one. *)
Definition ty_head (T : ty) : nat :=
  match T with
  | tyGvar _ _ | tyEl _ _ => 0 | tyNat => 1 | tyU _ => 2 | tyPi _ _ _ _ => 3
  | tyCTyp _ _ => 4 | tyCTrm _ _ _ => 5 | tyUPi _ _ _ => 6 | tyCPi _ _ => 7 | tyTPi _ _ _ _ => 8
  | tyErr => 9 | tySig _ _ _ _ => 10
  end.

Lemma whne_ty_head V : whne_ty V -> ty_head V = 0.
Proof. destruct 1; reflexivity. Qed.

Section Consequences.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}
  (red_eqty : forall G Γ T T' l, [ G ; Γ ⊢g T ≅ T' @ l ] -> lwf (gL G) l -> LRty l G Γ T T')
  (red_eqtm : forall G Γ t t' T l, [ G ; Γ ⊢g t ≅ t' : T @ l ] -> lwf (gL G) l -> LRtm l G Γ T T t t').

(** The relation is at well-formed levels: at ω (M4), the consequences
    come from the relation at ω instead ([DeclConsequences]). *)

Lemma reducible_ty {G Γ T l} : [ G ; Γ ⊢g T @ l ] -> lwf (gL G) l -> LRty l G Γ T T.
Proof. intros H Hl; apply red_eqty; [apply eqty_refl, H | exact Hl]. Qed.

Lemma reducible_tm {G Γ t T l} : [ G ; Γ ⊢g t : T @ l ] -> lwf (gL G) l -> LRtm l G Γ T T t t.
Proof. intros H Hl; apply red_eqtm; [apply eqtm_refl, H | exact Hl]. Qed.

(** ** Canonicity of natural numbers: every typed natural reduces to a
    related normal form ([zero], a successor, or a neutral). *)

Lemma nat_canonicity {G Γ t} : [ G ; Γ ⊢g t : tyNat @ lzero ] -> NatRel G Γ t t.
Proof. intros H; exact (proj1 LRtm_nat (reducible_tm H I)). Qed.

(** ** Injectivity of type formers *)

Lemma pi_inj {G Γ l l1 l2 l3 l4 A A' B B'} :
  [ G ; Γ ⊢g tyPi l1 l2 A B ≅ tyPi l3 l4 A' B' @ l ] -> lwf (gL G) l ->
  lequiv (gL G) l3 l1 /\ lequiv (gL G) l4 l2 /\
  [ G ; Γ ⊢ A ≈ A' @ l1 ] /\ [ G ; Γ ,, A @ l1 ⊢ B ≈ B' @ l2 ].
Proof.
  intros H Hl. destruct (red_eqty _ _ _ _ _ H Hl) as [R HR].
  pose proof (eqty_wf_l ge_typeof H) as HP.
  destruct (LR_inv_pi HR (tyred_refl _ _ HP))
    as (m3 & m4 & C' & D' & domR & codR & [_ H3 H4 _ _ _ HT' _ _ _ _ HAA HBB] & _).
  pose proof (tyred_refl _ _ (eqty_wf_r ge_typeof H)) as HT'0.
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT' HT'0 (whnf_tyPi _ _ _ _) (whnf_tyPi _ _ _ _)) as Heq.
  injection Heq as <- <- <- <-. auto.
Qed.

Lemma sig_inj {G Γ l l1 l2 l3 l4 A A' B B'} :
  [ G ; Γ ⊢g tySig l1 l2 A B ≅ tySig l3 l4 A' B' @ l ] -> lwf (gL G) l ->
  lequiv (gL G) l3 l1 /\ lequiv (gL G) l4 l2 /\
  [ G ; Γ ⊢ A ≈ A' @ l1 ] /\ [ G ; Γ ,, A @ l1 ⊢ B ≈ B' @ l2 ].
Proof.
  intros H Hl. destruct (red_eqty _ _ _ _ _ H Hl) as [R HR].
  pose proof (eqty_wf_l ge_typeof H) as HP.
  destruct (LR_inv_sig HR (tyred_refl _ _ HP))
    as (m3 & m4 & C' & D' & domR & codR & [_ H3 H4 _ _ _ HT' _ _ _ _ HAA HBB] & _).
  pose proof (tyred_refl _ _ (eqty_wf_r ge_typeof H)) as HT'0.
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT' HT'0 (whnf_tySig _ _ _ _) (whnf_tySig _ _ _ _)) as Heq.
  injection Heq as <- <- <- <-. auto.
Qed.

(** A type convertible to a [Π] reduces to one. *)
Lemma pi_red {G Γ l l1 l2 A B T} : [ G ; Γ ⊢g tyPi l1 l2 A B ≅ T @ l ] -> lwf (gL G) l ->
  exists l3 l4 C D, [ G ; Γ ⊢g T ⤳* tyPi l3 l4 C D @ l ].
Proof.
  intros H Hl. destruct (red_eqty _ _ _ _ _ H Hl) as [R HR].
  pose proof (eqty_wf_l ge_typeof H) as HP.
  destruct (LR_inv_pi HR (tyred_refl _ _ HP)) as (m3 & m4 & C' & D' & _ & _ & [_ _ _ _ _ _ HT' _ _ _ _ _ _] & _).
  eauto.
Qed.

Lemma U_inj {G Γ l l' k} : [ G ; Γ ⊢g tyU l ≅ tyU l' @ k ] -> lwf (gL G) k -> lequiv (gL G) l' l.
Proof.
  intros H Hk. destruct (red_eqty _ _ _ _ _ H Hk) as [R HR].
  destruct (LR_inv_U HR (tyred_refl _ _ (eqty_wf_l ge_typeof H))) as (l2 & _ & Hl2 & _ & HT' & _).
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT' (tyred_refl _ _ (eqty_wf_r ge_typeof H))
                (whnf_tyU _) (whnf_tyU _)) as Heq.
  now injection Heq as <-.
Qed.

(** ** Weak-head normalization *)

Lemma tmred_back {G Γ t w T W l l'} :
  [ G ; Γ ⊢g t ⤳* w : W @ l' ] -> [ G ; Γ ⊢g T ⤳* W @ l ] -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢g t ⤳* w : T @ l ].
Proof.
  intros Ht HT Hl. eapply tmred_conv; [apply ge_typeof | eapply tmred_lconv; [exact Ht | exact Hl] |].
  apply eqty_sym, (tyred_eq _ _ _ _ _ _ HT).
Qed.

Lemma LR_whnf_ty n rec G Γ T T' l R :
  LR n rec G Γ T T' l R -> exists W, [ G ; Γ ⊢g T ⤳* W @ l ] /\ whnf_ty W.
Proof.
  destruct 1 as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l l1 l2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l l1 l2 T1 T1' instR R Hj Hl Hl2 Hw1 HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' l1 l2 l3 l4 T1 T1' instR R Hj Hl Hl3 Hl4 Hw1 Hw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR];
    try match goal with HM : ModRel _ _ _ _ _ _ |- _ => destruct HM end;
    eexists; split; eauto using whnf_ty, gne_ty_whne_l.
Qed.

Lemma ModRel_whnf_tm {G Γ T T' l R} : ModRel G Γ T T' l R -> forall t t', R t t' ->
  exists w, [ G ; Γ ⊢g t ⤳* w : T @ l ] /\ whnf w.
Proof.
  destruct 1 as [T T' l Δ Δ' k k' R Hl Hk HT HT' HΔ Hgeq HR
                | T T' l Δ Δ' A A' k k' R Hl Hk HT HT' HΔ HA HA' Hgeq HR];
    intros t t' Ht; apply HR in Ht; destruct Ht as (w & w' & Hw & _ & _ & _ & Hn & _);
    exists w; (split; [exact (tmred_back Hw HT Hl) |]).
  - exact (CTypNf_whnf_l Hn).
  - exact (CTrmNf_whnf_l Hn).
Qed.

Lemma LR_whnf_tm n rec G Γ T T' l R :
  LR n rec G Γ T T' l R -> forall t t', R t t' ->
  exists w, [ G ; Γ ⊢g t ⤳* w : T @ l ] /\ whnf w.
Proof.
  destruct 1 as [G Γ T T' l R Hl HT HT' HR
                | G Γ T T' l l1 l2 R Hl Hl2 Hn HT HT' HR
                | G Γ T T' l V V' R HT HT' HV HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR
                | G Γ T T' l R Hj HM
                | G Γ T T' l l1 l2 T1 T1' instR R Hj Hl Hl2 Hw1 HT HT' HT1 HT1' Hgeq instAd HR
                | G Γ T T' l Δ1 Δ1' l1 l2 l3 l4 T1 T1' instR R Hj Hl Hl3 Hl4 Hw1 Hw2 HT HT' HΔ HT1 HT1'
                    Hgeq instAd HR
                | G Γ T T' l l1 l2 l3 l4 A B A' B' domR codR R [Hl Hl3 Hl4 Hw1 Hw2 HT HT' HA HA' HB HB' HAA HBB] domAd codAd HR];
    intros t t' Ht; first [exact (ModRel_whnf_tm HM _ _ Ht) | apply HR in Ht].
  - destruct Ht as [t t' w w' Hw _ _ Hnf]. exists w; split; [exact (tmred_back Hw HT Hl)|].
    destruct Hnf; eauto using whnf, gne_tm_whne_l.
  - destruct Ht as (w & w' & Hw & _ & Hwh & _). exists w; split; [exact (tmred_back Hw HT Hl) | exact Hwh].
  - destruct Ht as (ν & ν' & Hν & _ & Hne & _). exists ν; split.
    + eapply tmred_conv; [apply ge_typeof | exact Hν | apply eqty_sym, (tyred_eq _ _ _ _ _ _ HT)].
    + eauto using whnf, gne_tm_whne_l.
  - destruct Ht as (w & w' & Hw & _ & Hwh & _). exists w; split; [exact (tmred_back Hw HT Hl) | exact Hwh].
  - destruct Ht as (w & w' & Hw & _ & Hwh & _). exists w; split; [exact (tmred_back Hw HT Hl) | exact Hwh].
  - destruct Ht as (w & w' & Hw & _ & Hwh & _). exists w; split; [exact (tmred_back Hw HT Hl) | exact Hwh].
  - destruct Ht as (w & w' & Hw & _ & Hwh & _). exists w; split; [exact (tmred_back Hw HT Hl) | exact Hwh].
Qed.

Theorem whnf_normalization_ty {G Γ T l} : [ G ; Γ ⊢g T @ l ] -> lwf (gL G) l ->
  exists W, [ G ; Γ ⊢g T ⤳* W @ l ] /\ whnf_ty W.
Proof. intros H Hl. destruct (reducible_ty H Hl) as [R HR]. exact (LR_whnf_ty _ _ _ _ _ _ _ _ HR). Qed.

Theorem whnf_normalization_tm {G Γ t T l} : [ G ; Γ ⊢g t : T @ l ] -> lwf (gL G) l ->
  exists w, [ G ; Γ ⊢g t ⤳* w : T @ l ] /\ whnf w.
Proof.
  intros H Hl. destruct (reducible_tm H Hl) as (R & HR & Ht).
  exact (LR_whnf_tm _ _ _ _ _ _ _ _ HR _ _ Ht).
Qed.

(** ** Closed canonicity

    With no term bindings in the global context, a typed neutral needs a
    local variable at its head: there are no closed neutrals. *)

(** Global contexts binding context variables only. *)
Definition ctx_only (G : gctx) : Prop := forall n D, in_gctx (gΨ G) n D -> D = gdCtx.

(** Boxed global variables mention a type or term binding. *)
Lemma tyGvar_decl {G i Γ U d l} : [ G ; Γ ⊢[ i ] tyGvar U d @ l ] ->
  exists Δ i' l', in_gctx (gΨ G) U (gdTy Δ i' l').
Proof.
  intros H; remember (tyGvar U d) as T eqn:Heq; revert Heq.
  induction H; intros Heq; try discriminate; eauto. injection Heq as -> ->; eauto.
Qed.
Lemma gvar_decl {G i Γ u d A l} : [ G ; Γ ⊢[ i ] gvar u d : A @ l ] ->
  exists Δ i' T l', in_gctx (gΨ G) u (gdTm Δ i' T l').
Proof.
  intros H; remember (gvar u d) as t eqn:Heq; revert Heq.
  induction H; intros Heq; try discriminate; eauto. injection Heq as -> ->; eauto.
Qed.
Lemma boxT_inv {G i Γ T A l} : [ G ; Γ ⊢[ i ] boxT T : A @ l ] -> exists Δ l', [ G ; Δ ⊢[ lC ] T @ l' ].
Proof.
  intros H; remember (boxT T) as t eqn:Heq; revert Heq.
  induction H; intros Heq; try discriminate; eauto. injection Heq as ->; eauto.
Qed.
Lemma boxt_inv {G i Γ t A l} : [ G ; Γ ⊢[ i ] boxt t : A @ l ] -> exists Δ T l', [ G ; Δ ⊢[ lC ] t : T @ l' ].
Proof.
  intros H; remember (boxt t) as x eqn:Heq; revert Heq.
  induction H; intros Heq; try discriminate; eauto. injection Heq as ->; eauto.
Qed.

Lemma no_closed_neutral {G i Γ t T l} :
  [ G ; Γ ⊢[ i ] t : T @ l ] -> Γ = cnil -> ctx_only G -> ~ whne t.
Proof.
  induction 1; intros -> HG Hne; inversion Hne; subst;
    match goal with
    | H : in_ctx cnil _ _ _ |- _ => inversion H
    | Hin : in_gctx _ _ (gdTm _ _ _ _) |- _ => discriminate (HG _ _ Hin)
    | IH : cnil = cnil -> ctx_only _ -> ~ whne ?x, H : whne ?x |- _ => exact (IH eq_refl HG H)
    (* recursors on boxed global variables *)
    | H : wf_tm _ _ _ (boxT (tyGvar _ _)) _ _ |- _ =>
        destruct (boxT_inv H) as (? & ? & HT); destruct (tyGvar_decl HT) as (? & ? & ? & Hin);
        discriminate (HG _ _ Hin)
    | H : wf_tm _ _ _ (boxt (gvar _ _)) _ _ |- _ =>
        destruct (boxt_inv H) as (? & ? & ? & Ht); destruct (gvar_decl Ht) as (? & ? & ? & ? & Hin);
        discriminate (HG _ _ Hin)
    end.
Qed.

Fixpoint numeral (n : nat) : tm := match n with 0 => zero | S n => succ (numeral n) end.

Theorem closed_nat_canonicity {G t} : ctx_only G -> [ G ; cnil ⊢g t : tyNat @ lzero ] ->
  exists n, [ G ; cnil ⊢g t ≅ numeral n : tyNat @ lzero ].
Proof.
  intros HG H. pose proof (nat_canonicity H) as Hn.
  refine (NatRel_mut G cnil (fun t _ _ => exists n, [ G ; cnil ⊢g t ≅ numeral n : tyNat @ lzero ])
            (fun w _ _ => exists n, [ G ; cnil ⊢g w ≅ numeral n : tyNat @ lzero ]) _ _ _ _ t t Hn).
  - intros t0 t0' w w' Hw _ _ _ (n & Hwn). exists n.
    eapply eqtm_trans; [exact (tmred_eq _ _ _ _ _ _ _ Hw) | exact Hwn].
  - exists 0. apply eqtm_refl, wf_zero; [exact ge_notV | rewrite ge_typeof; eapply ctx_of_tm, H].
  - intros t0 t0' _ (n & Hn'). exists (S n). cbn. apply eqtm_succ; [exact ge_notV | exact Hn'].
  - intros ν ν' Hνν. exfalso.
    exact (no_closed_neutral (gne_tm_typed_l Hνν) eq_refl HG (gne_tm_whne_l Hνν)).
Qed.

(** ** Discrimination of type formers *)

Lemma nat_not_pi {G Γ k l l' A B} : lwf (gL G) k -> ~ [ G ; Γ ⊢g tyNat ≅ tyPi l l' A B @ k ].
Proof.
  intros Hk H. destruct (red_eqty _ _ _ _ _ H Hk) as [R HR].
  destruct (LR_inv_nat HR (tyred_refl _ _ (eqty_wf_l ge_typeof H))) as (_ & HT' & _).
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT' (tyred_refl _ _ (eqty_wf_r ge_typeof H))
                whnf_tyNat (whnf_tyPi _ _ _ _)) as Heq. discriminate.
Qed.

Lemma nat_not_U {G Γ k l} : lwf (gL G) k -> ~ [ G ; Γ ⊢g tyNat ≅ tyU l @ k ].
Proof.
  intros Hk H. destruct (red_eqty _ _ _ _ _ H Hk) as [R HR].
  destruct (LR_inv_nat HR (tyred_refl _ _ (eqty_wf_l ge_typeof H))) as (_ & HT' & _).
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT' (tyred_refl _ _ (eqty_wf_r ge_typeof H))
                whnf_tyNat (whnf_tyU _)) as Heq. discriminate.
Qed.

Lemma U_not_pi {G Γ k l l1 l2 A B} : lwf (gL G) k -> ~ [ G ; Γ ⊢g tyU l ≅ tyPi l1 l2 A B @ k ].
Proof.
  intros Hk H. destruct (red_eqty _ _ _ _ _ H Hk) as [R HR].
  destruct (LR_inv_U HR (tyred_refl _ _ (eqty_wf_l ge_typeof H))) as (l2' & _ & _ & _ & HT' & _).
  pose proof (tyred_whnf_det _ _ _ _ _ _ _ _ HT' (tyred_refl _ _ (eqty_wf_r ge_typeof H))
                (whnf_tyU _) (whnf_tyPi _ _ _ _)) as Heq. discriminate.
Qed.

(** ** Discrimination, uniformly: convertible whnf types have the same head *)

Lemma LR_head n rec G Γ T T' l R : LR n rec G Γ T T' l R ->
  exists W W', ([ G ; Γ ⊢g T ⤳* W @ l ]) /\ ([ G ; Γ ⊢g T' ⤳* W' @ l ]) /\
    whnf_ty W /\ whnf_ty W' /\ ty_head W = ty_head W'.
Proof.
  destruct 1; open_poly; try match goal with HM : ModRel _ _ _ _ _ _ |- _ => destruct HM end;
  match goal with |- exists _ _, [ _ ; _ ⊢g ?a ⤳* _ @ _ ] /\ [ _ ; _ ⊢g ?b ⤳* _ @ _ ] /\ _ =>
    match goal with HT : [ _ ; _ ⊢g a ⤳* ?X @ _ ], HT' : [ _ ; _ ⊢g b ⤳* ?X' @ _ ] |- _ =>
      exists X, X'; refine (conj HT (conj HT' _)) end end;
  first [ match goal with Hn : [ _ ; _ ⊢ _ ~ _ @ _ ] |- _ =>
            pose proof (gne_ty_whne_l Hn); pose proof (gne_ty_whne_r Hn) end;
          refine (conj _ (conj _ _)); [apply whnf_ty_ne; assumption | apply whnf_ty_ne; assumption |];
          rewrite !whne_ty_head by assumption; reflexivity
        | refine (conj _ (conj _ eq_refl)); eauto using whnf_ty ].
Qed.

Lemma eqty_head {G Γ W W' l} : [ G ; Γ ⊢g W ≅ W' @ l ] -> lwf (gL G) l -> whnf_ty W -> whnf_ty W' ->
  ty_head W = ty_head W'.
Proof.
  intros H Hl Hw Hw'. destruct (red_eqty _ _ _ _ _ H Hl) as [R HR].
  destruct (LR_head _ _ _ _ _ _ _ _ HR) as (X & X' & HX & HX' & Hx & Hx' & Eh).
  rewrite <- (tyred_whnf_det _ _ _ _ _ _ _ _ HX (tyred_refl _ _ (eqty_wf_l ge_typeof H)) Hx Hw).
  rewrite <- (tyred_whnf_det _ _ _ _ _ _ _ _ HX' (tyred_refl _ _ (eqty_wf_r ge_typeof H)) Hx' Hw').
  exact Eh.
Qed.

End Consequences.
