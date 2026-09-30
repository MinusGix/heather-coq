(** * Typed syntax is in (deep) normal form

    Moved ahead of global weakening, whose level-growth case needs the
    identity laws of global renaming (M3_DESIGN.md E14). *)
From DeLaM.Syntax Require Export SubstCommute.
From DeLaM.Typing Require Export RecWf.

(** ** Typed terms are in (deep) normal form *)

Lemma lk_lsingle a : nftm a -> LK nftm (lsingle a).
Proof. intros H [|n]; cbn; auto. Qed.
Lemma lk_lsingle2 t q : nftm t -> nftm q -> LK nftm (lsingle2 t q).
Proof. intros H1 H2 [|[|n]]; cbn; auto. Qed.
Lemma lk_lsucc : LK nftm lsucc.
Proof. intros [|n]; cbn; auto. Qed.
#[export] Hint Resolve lk_lsingle lk_lsingle2 lk_lsucc : nf.

Lemma lk_dnf_lsingle a : dnftm a -> LK dnftm (lsingle a).
Proof. intros H [|n]; cbn; auto. Qed.
Lemma lk_dnf_lsingle2 t q : dnftm t -> dnftm q -> LK dnftm (lsingle2 t q).
Proof. intros H1 H2 [|[|n]]; cbn; auto. Qed.
Lemma lk_dnf_lsucc : LK dnftm lsucc.
Proof. intros [|n]; cbn; auto. Qed.
Lemma lk_dnf_lshift k : LK dnftm (lshift k).
Proof. intros n; exact I. Qed.
#[export] Hint Resolve lk_dnf_lsingle lk_dnf_lsingle2 lk_dnf_lsucc lk_dnf_lshift : nf.

Lemma in_ctx_dnf Γ n T l : dnfctx Γ -> in_ctx Γ n T l -> dnfty T.
Proof. intros H Hin; induction Hin; cbn in *; apply ren_dnf_ty; tauto. Qed.

Definition dnf_decl (D : gdecl) : Prop :=
  match D with
  | gdCtx => True | gdTy Δ _ _ => dnfctx Δ | gdTm Δ _ T _ => dnfctx Δ /\ dnfty T
  | gdDef Δ T _ t => dnfctx Δ /\ dnfty T /\ dnftm t
  end.
Lemma in_gctx_dnf Ψ n D : in_gctx Ψ n D -> dnf_decl D.
Proof. destruct 1 as [? D0|? D0 ? ? _]; destruct D0; cbn; repeat split; apply gren_dnf_all. Qed.

Lemma dnfo_gsingle o : dnfo o -> forall i, dnfo (gsingle o i).
Proof. intros H [|i]; cbn; auto. Qed.
Lemma dnfo_gup σ : (forall i, dnfo (σ i)) -> forall i, dnfo (gup σ i).
Proof. intros H [|i]; cbn; auto using dnfo_goren. Qed.

(** Deep normal forms of the recursors' bundles, motive instances and reducts. *)
Lemma dnf_wrap nu ng nl b : dnftm b -> dnftm (wrap nu ng nl b).
Proof. intros H; unfold wrap. induction nu; cbn; auto. induction ng; cbn; auto. induction nl; cbn; auto. Qed.
Lemma dnf_mkrb MT Mt bs : dnfty MT -> dnfty Mt -> (forall k, k < nbr -> dnftm (bs k)) ->
  dnftm (mkrb MT Mt bs).
Proof.
  intros H1 H2 H3. unfold mkrb. cbn [tup_from br_ar dnftm wrapMT wrapMt].
  repeat split; auto; apply dnf_wrap, H3; lia.
Qed.
Lemma dnf_tup_nth t k : dnftm t -> dnftm (tup_nth t k).
Proof. revert t; induction k; intros [] H; cbn in *; try tauto; apply IHk; tauto. Qed.
Lemma dnf_peelU b l : dnftm (peelU b l).
Proof. destruct b; cbn; auto. apply usubst_dnf_all. Qed.
Lemma dnf_peelG b o : dnftm b -> dnfo o -> dnftm (peelG b o).
Proof. destruct b; cbn; auto. intros; apply gsubst_dnf_all; auto. now apply dnfo_gsingle. Qed.
Lemma dnf_peelL b a : dnftm b -> dnftm a -> dnftm (peelL b a).
Proof. destruct b; cbn; auto. intros; apply subst_dnf; auto with nf. Qed.
Lemma dnf_getTy t : dnftm t -> dnfty (getTy t).
Proof. destruct t; cbn; auto. Qed.
Lemma dnf_motT w lv g c : dnfctx g -> dnftm c -> dnfty (motT w lv g c).
Proof. intros; unfold motT. apply dnf_getTy, dnf_peelL, H0. apply dnf_peelG, H; apply dnf_peelU. Qed.
Lemma dnf_mott w lv g U c : dnfctx g -> dnfty U -> dnftm c -> dnfty (mott w lv g U c).
Proof.
  intros; unfold mott. apply dnf_getTy, dnf_peelL; auto.
  apply dnf_peelG; cbn; auto. apply dnf_peelG; cbn; auto. apply dnf_peelU.
Qed.

#[local] Hint Resolve dnf_peelU dnf_peelG dnf_peelL dnf_tup_nth : dnfr.

Lemma dnf_redT l1 l2 rb l Δ c r : dnftm rb -> dnfctx Δ -> dnfty c ->
  redT l1 l2 rb l Δ c = Some r -> dnftm r.
Proof.
  intros Hrb HΔ Hc E. unfold rb_br in E.
  destruct c; cbn [redT] in E; inversion E; subst; cbn in Hc;
    repeat first [ apply dnf_peelL | apply dnf_peelG | apply dnf_peelU | apply dnf_tup_nth ];
    cbn [dnfo dnftm dnfty dnfctx recT rect]; intuition auto.
Qed.
Lemma dnf_redt l1 l2 rb l Δ T c r : dnftm rb -> dnfctx Δ -> dnfty T -> dnftm c ->
  redt l1 l2 rb l Δ T c = Some r -> dnftm r.
Proof.
  intros Hrb HΔ HT Hc E. unfold rb_br in E.
  destruct c; cbn [redt] in E; redt_case T; inversion E; subst; cbn in Hc, HT;
    repeat first [ apply dnf_peelL | apply dnf_peelG | apply dnf_peelU | apply dnf_tup_nth ];
    cbn [dnfo dnftm dnfty dnfctx recT rect]; intuition auto.
  all: apply subst_dnf_ty; [intuition auto | first [apply lk_dnf_lsucc | apply lk_dnf_lsingle; first [exact I | intuition auto]]].
Qed.

Theorem typed_dnf :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> dnfctx Γ) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> dnfty T) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> dnftm t /\ dnfty T) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> dnfty T /\ dnfty T') /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> dnftm t /\ dnftm t' /\ dnfty T) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> dnfctx Γ /\ dnfctx Γ').
Proof.
  apply typing_mut; intros; cbn in *;
    try match goal with H : in_gctx _ _ _ |- _ => pose proof (in_gctx_dnf _ _ _ H); cbn in * end;
    intuition eauto using subst_dnf_ty, subst_dnf, ren_dnf_ty, ren_dnf, in_ctx_dnf with nf.
  all: try solve [apply subst_dnf; [assumption | apply lk_dnf_lsingle2; cbn; tauto]].
  all: try solve [apply subst_dnf_ty; auto; intros n; apply dnfl_llk; auto].
  all: try solve [apply subst_dnf; auto; intros n; apply dnfl_llk; auto].
  all: try solve [apply gsubst_dnf_all; auto; apply dnfo_gsingle; cbn; auto].
  (* the recursors: branches, motive instances, reducts *)
  all: try match goal with
       | IH : forall k, k < nbr -> dnftm (?bs k) /\ _ |- dnftm (?bs ?n) => apply (IH n); lia
       end.
  all: try solve [ repeat first [ apply subst_dnf_ty | apply gsubst_dnf_all | apply usubst_dnf_all
                                | apply uren_dnf_all | apply dnfo_gup | apply dnfo_gsingle | apply lk_dnf_lsingle ];
                   cbn; intuition auto ].
  all: try solve [ eapply dnf_redT; [ .. | eassumption ]; cbn; intuition auto
                 | eapply dnf_redt; [ .. | eassumption ]; cbn; intuition auto ].
  (* η of the meta-functions (M5): the weakened function *)
  all: apply gren_dnf_all.
Qed.

Theorem typed_nf :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> True) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> nfty T) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> nftm t /\ nfty T) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> nfty T /\ nfty T') /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> nftm t /\ nftm t' /\ nfty T).
Proof.
  destruct typed_dnf as (_ & _ & H1 & H2 & H3 & H4 & _).
  refine (conj (fun _ _ => I) (conj (fun _ _ _ _ => I) (conj _ (conj _ (conj _ _))))); intros.
  - apply dnfty_nfty; eauto.
  - destruct (H2 _ _ _ _ _ _ H); split; auto using dnftm_nftm, dnfty_nfty.
  - destruct (H3 _ _ _ _ _ _ H); split; auto using dnfty_nfty.
  - destruct (H4 _ _ _ _ _ _ _ H) as (? & ? & ?); repeat split; auto using dnftm_nftm, dnfty_nfty.
Qed.

Lemma wf_ty_nf {G i Γ T l} : [ G ; Γ ⊢[ i ] T @ l ] -> nfty T.
Proof. apply typed_nf. Qed.
Lemma wf_tm_nf {G i Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> nftm t.
Proof. apply typed_nf. Qed.
Lemma wf_tm_nf_ty {G i Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> nfty T.
Proof. apply typed_nf. Qed.
Lemma wf_ty_dnf {G i Γ T l} : [ G ; Γ ⊢[ i ] T @ l ] -> dnfty T.
Proof. apply typed_dnf. Qed.
Lemma wf_tm_dnf {G i Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> dnftm t.
Proof. apply typed_dnf. Qed.
Lemma wf_tm_dnf_ty {G i Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> dnfty T.
Proof. apply typed_dnf. Qed.
Lemma wf_ctx_dnf {G i Γ} : [ G ; Γ ⊢[ i ] ] -> dnfctx Γ.
Proof. apply typed_dnf. Qed.


(** Every judgment's context is deep-normal. *)
Theorem typed_dnf_ctx :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> dnfctx Γ) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> dnfctx Γ) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> dnfctx Γ) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> dnfctx Γ) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> dnfctx Γ) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> dnfctx Γ /\ dnfctx Γ').
Proof.
  destruct typed_dnf as (_ & _ & Hty & _ & Heq & _).
  apply typing_mut; intros; cbn in *; try exact I; eauto; try tauto.
  all: repeat split; try tauto; eauto; eapply Heq; eassumption.
Qed.

Lemma wf_ty_dnf_ctx {G i Γ T l} : [ G ; Γ ⊢[ i ] T @ l ] -> dnfctx Γ.
Proof. apply typed_dnf_ctx. Qed.
Lemma wf_tm_dnf_ctx {G i Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] -> dnfctx Γ.
Proof. apply typed_dnf_ctx. Qed.
Lemma eqty_dnf_ctx {G i Γ T T' l} : [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> dnfctx Γ.
Proof. apply typed_dnf_ctx. Qed.
Lemma eqtm_dnf_ctx {G i Γ t t' T l} : [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> dnfctx Γ.
Proof. apply typed_dnf_ctx. Qed.
Lemma eqty_dnf {G i Γ T T' l} : [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> dnfty T /\ dnfty T'.
Proof. apply typed_dnf. Qed.
Lemma eqtm_dnf {G i Γ t t' T l} : [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> dnftm t /\ dnftm t' /\ dnfty T.
Proof. apply typed_dnf. Qed.
Lemma eqctx_dnf {G i Γ Γ'} : [ G ⊢[ i ] Γ ≅ Γ' ] -> dnfctx Γ /\ dnfctx Γ'.
Proof. apply typed_dnf_ctx. Qed.
