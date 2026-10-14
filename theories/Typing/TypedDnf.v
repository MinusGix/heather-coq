(** * Typed syntax is in (deep) normal form

    Moved ahead of global weakening, whose level-growth case needs the
    identity laws of global renaming (M3_DESIGN.md E14). *)
From DeLaM.Syntax Require Export SubstCommute.
From DeLaM.Typing Require Export Declarative.

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

(** [elim_W]'s β (M13a): the step's instance and the induction hypothesis. *)
Lemma lk_dnf_lsingle3 a f h : dnftm a -> dnftm f -> dnftm h -> LK dnftm (lsingle3 a f h).
Proof. intros H1 H2 H3 [|[|[|n]]]; cbn; auto. Qed.
Lemma dnf_wIH l l' l'' A B M c a f : dnfty A -> dnfty B -> dnfty M -> dnftm c -> dnftm a -> dnftm f ->
  dnftm (wIH l l' l'' A B M c a f).
Proof.
  intros; unfold wIH; cbn [dnftm dnfty]; repeat split;
    auto using ren_dnf_ty, ren_dnf, subst_dnf_ty, lk_dnf_lsingle.
Qed.

(** [nth] and [elim_Wf]'s induction hypothesis (M15a). *)
Lemma dnf_tmNth l T k cs i : dnfty T -> dnftm k -> dnftm cs -> dnftm i -> dnftm (tmNth l T k cs i).
Proof.
  intros; unfold tmNth, nthMot, nthBase, nthStep; cbn [dnftm dnfty]; repeat split;
    repeat apply ren_dnf_ty; repeat apply ren_dnf; auto.
Qed.
Lemma dnf_wfIH l l' A N M c a cs : dnfty A -> dnftm N -> dnfty M -> dnftm c -> dnftm a -> dnftm cs ->
  dnftm (wfIH l l' A N M c a cs).
Proof.
  intros; unfold wfIH.
  assert (Hn : dnftm (tmNth l (tyWf l A N)⟨↑⟩ N[lsingle a]⟨↑⟩ cs⟨↑⟩ (var 0))).
  { apply dnf_tmNth; cbn [dnftm dnfty]; repeat split; auto using ren_dnf_ty, ren_dnf, subst_dnf, lk_dnf_lsingle. }
  revert Hn; generalize (tmNth l (tyWf l A N)⟨↑⟩ N[lsingle a]⟨↑⟩ cs⟨↑⟩ (var 0)); intros x Hn.
  cbn [dnftm dnfty]; repeat split; auto using ren_dnf_ty, ren_dnf, subst_dnf, lk_dnf_lsingle.
Qed.

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

(** [dnth] and [elim_IWf]'s family and induction hypothesis (M17b). *)
Lemma dnf_tmDNth l n F cs i : dnftm n -> dnfty F -> dnftm cs -> dnftm i -> dnftm (tmDNth l n F cs i).
Proof.
  intros; unfold tmDNth, dnthMot, dnthBase, dnthStep, dnthEmb, dnthFam, dnthRes, dnthFamS.
  (* [exact I] and [split] only on goals of their shape: tried on a
     [dnftm] of a renaming, they unfold it *)
  cbn [dnftm dnfty];
    repeat first [ lazymatch goal with |- True => exact I | |- _ /\ _ => split end
                 | assumption | apply ren_dnf_ty | apply ren_dnf
                 | apply lk_dnf_lsingle | (apply subst_dnf_ty; [|apply lk_dnf_lsingle])
                 | (apply subst_dnf; [|apply lk_dnf_lsingle]) | progress cbn [dnftm dnfty] ].
Qed.
Lemma dnf_iwfFam l li X A N Ot C a : dnfty X -> dnfty A -> dnftm N -> dnftm Ot -> dnftm C -> dnftm a ->
  dnfty (iwfFam l li X A N Ot C a).
Proof.
  intros; unfold iwfFam; cbn [dnfty dnftm]; repeat split; auto using ren_dnf_ty, ren_dnf.
  apply subst_dnf; auto. apply lk_dnf_llift, lk_dnf_lsingle; auto.
Qed.
Lemma dnf_iwfIH l li l' X A N Ot C M c a cs : dnfty X -> dnfty A -> dnftm N -> dnftm Ot -> dnftm C ->
  dnfty M -> dnftm c -> dnftm a -> dnftm cs -> dnftm (iwfIH l li l' X A N Ot C M c a cs).
Proof.
  intros; unfold iwfIH.
  assert (Hn : dnftm (tmDNth (lmax l li) N[lsingle a]⟨↑⟩ (iwfFam l li X A N Ot C a)⟨rlift ↑⟩ cs⟨↑⟩ (var 0))).
  { apply dnf_tmDNth; auto using ren_dnf_ty, ren_dnf, dnf_iwfFam; [|exact I].
    apply ren_dnf, subst_dnf; auto using lk_dnf_lsingle. }
  pose proof (dnf_iwfFam l li X A N Ot C a ltac:(assumption) ltac:(assumption) ltac:(assumption)
                ltac:(assumption) ltac:(assumption) ltac:(assumption)) as HF.
  unfold iwfFam in HF; cbn [dnfty dnftm] in HF.
  revert Hn; generalize (tmDNth (lmax l li) N[lsingle a]⟨↑⟩ (iwfFam l li X A N Ot C a)⟨rlift ↑⟩ cs⟨↑⟩ (var 0)); intros x Hn.
  cbn [dnftm dnfty]; intuition auto using ren_dnf_ty, ren_dnf, subst_dnf, lk_dnf_lsingle.
Qed.

Lemma dnf_redT l1 l2 rb l Δ c r : dnftm rb -> dnfctx Δ -> dnfty c ->
  redT l1 l2 rb l Δ c = Some r -> dnftm r.
Proof.
  intros Hrb HΔ Hc E. unfold rb_br in E.
  destruct c; cbn [redT] in E; first [discriminate E | apply Some_inj in E; subst r]; cbn in Hc;
    repeat first [ apply dnf_peelL | apply dnf_peelG | apply dnf_peelU | apply dnf_tup_nth ];
    cbn [dnfo dnftm dnfty dnfctx recT rect]; intuition auto.
  (* [IWf]'s (M17c): its components under the shape's binder *)
  all: repeat first [ lazymatch goal with |- True => exact I | |- _ /\ _ => split end | assumption
                    | apply ren_dnf_ty | apply ren_dnf | progress cbn [dnftm dnfty] ].
Qed.
Lemma dnf_redt l1 l2 rb l Δ T c r : dnftm rb -> dnfctx Δ -> dnfty T -> dnftm c ->
  redt l1 l2 rb l Δ T c = Some r -> dnftm r.
Proof.
  intros Hrb HΔ HT Hc E. unfold rb_br in E.
  destruct c; cbn [redt] in E; redt_case T; first [discriminate E | apply Some_inj in E; subst r]; cbn in Hc, HT;
    repeat first [ apply dnf_peelL | apply dnf_peelG | apply dnf_peelU | apply dnf_tup_nth ];
    cbn [dnfo dnftm dnfty dnfctx recT rect]; intuition auto.
  all: first
    [ apply ren_dnf_ty; intuition auto | apply ren_dnf; intuition auto
    (* [case]'s branch types (M12c): the motive and the summands shifted *)
    | solve [apply subst_dnf_ty; [apply ren_dnf_ty; intuition auto
                                 | apply lk_dnf_lsingle; cbn [dnftm]; repeat split; try exact I;
                                   apply ren_dnf_ty; intuition auto]]
    | apply subst_dnf_ty; [intuition auto | first [apply lk_dnf_lsucc | apply lk_dnf_lsingle; first [exact I | intuition auto]
                                                  | apply lk_dnf_lsingle2; cbn [dnftm]; intuition auto]]
    (* [sup_f]'s children's length (M15b) *)
    | apply subst_dnf; [intuition auto | apply lk_dnf_lsingle; intuition auto]
    (* [sup_i]'s and [elim_IWf]'s (M17c), below *)
    | idtac ].
  (* [elimW]'s step telescope (M13b): renamings nested under the payload binders *)
  all: repeat first [ progress cbn [dnftm dnfty] | apply ren_dnf_ty | apply ren_dnf | apply subst_dnf_ty
                    | apply lk_dnf_lsingle | split | exact I ]; intuition auto.
  (* [sup_i]'s children and [elim_IWf]'s step telescope (M17c) *)
  all: repeat first [ lazymatch goal with |- True => exact I | |- _ /\ _ => split end | assumption
                    | apply dnf_iwfFam | apply dnf_tmDNth | apply ren_dnf_ty | apply ren_dnf
                    | apply subst_dnf_ty | apply subst_dnf | apply lk_dnf_lsingle | apply lk_dnf_lsingle2
                    | apply lk_dnf_llift | progress cbn [dnftm dnfty] ].
Qed.

(* [IWf] (M17b): [dnth], the family and the induction hypothesis stay folded
   in [typed_dnf], for their lemmas *)
Local Arguments tmDNth : simpl never. Local Arguments iwfFam : simpl never.
Local Arguments iwfIH : simpl never.
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
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    repeat split; eauto using subst_dnf_ty, subst_dnf, ren_dnf_ty, ren_dnf, in_ctx_dnf, dnf_tmDNth, dnf_iwfFam with nf.
  all: try solve [apply subst_dnf; [assumption | apply lk_dnf_lsingle2; cbn; tauto]].
  all: try solve [apply subst_dnf_ty; auto; intros n; apply dnfl_llk; auto].
  all: try solve [apply subst_dnf; auto; intros n; apply dnfl_llk; auto].
  all: try solve [apply gsubst_dnf_all; auto; apply dnfo_gsingle; cbn; auto].
  (* the recursors: branches, motive instances, reducts *)
  all: try match goal with
       | IH : forall k, k < nbr -> dnftm (?bs k) /\ _ |- dnftm (?bs ?n) => exact (proj1 (IH n ltac:(lia)))
       end.
  all: try solve [ repeat first [ apply subst_dnf_ty | apply gsubst_dnf_all | apply usubst_dnf_all
                                | apply uren_dnf_all | apply dnfo_gup | apply dnfo_gsingle | apply lk_dnf_lsingle ];
                   cbn; intuition auto ].
  all: try solve [ eapply dnf_redT; [ .. | eassumption ]; cbn; intuition auto
                 | eapply dnf_redt; [ .. | eassumption ]; cbn; intuition auto ].
  all: try solve [apply subst_dnf; [assumption | apply lk_dnf_lsingle3; auto using dnf_wIH, dnf_wfIH, dnf_iwfIH]].
  (* [DVec]'s successor reduct (M17a): the head's and the tail's instances *)
  all: try solve [ repeat first [ progress cbn [dnftm dnfty] | apply subst_dnf_ty | apply ren_dnf_ty | apply ren_dnf
                                | apply lk_dnf_lsingle | split | exact I ]; intuition auto ].
  (* [elim_IWf]'s β (M17b): the motive at the [sup_i]'s index and itself *)
  all: try solve [apply subst_dnf_ty; [assumption | apply lk_dnf_lsingle2; cbn [dnftm dnfty];
                  intuition auto using subst_dnf, lk_dnf_lsingle]].
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
