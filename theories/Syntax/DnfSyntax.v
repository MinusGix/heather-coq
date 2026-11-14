(** * Deep normal forms of the syntax's operations

    The untyped half of [TypedDnf]: the local substitutions', the
    recursors' bundles', motive instances' and reducts' deep normal
    forms. They use only the syntax, so they build while [SubstCommute]
    and the typing rules do, which only the typed half waits for. *)
From DeLaM.Syntax Require Export Universe Recursor.

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

(** [IWi]'s field type and induction hypothesis (M19). *)
Lemma dnf_iwiFamCod l lp li X A N D Ot C a : dnfty X -> dnfty A -> dnftm N -> dnfty D -> dnftm Ot ->
  dnftm C -> dnftm a -> dnfty (iwiFamCod l lp li X A N D Ot C a).
Proof.
  intros; unfold iwiFamCod; cbn [dnfty dnftm]; repeat split; auto using ren_dnf_ty, ren_dnf.
  apply subst_dnf; auto. apply lk_dnf_llift, lk_dnf_llift, lk_dnf_lsingle; auto.
Qed.
Lemma dnf_iwiFam l lp li X A N D Ot C a : dnfty X -> dnfty A -> dnftm N -> dnfty D -> dnftm Ot ->
  dnftm C -> dnftm a -> dnfty (iwiFam l lp li X A N D Ot C a).
Proof.
  intros; unfold iwiFam; cbn [dnfty]; split; auto using dnf_iwiFamCod.
  apply subst_dnf_ty; auto. apply lk_dnf_llift, lk_dnf_lsingle; auto.
Qed.
Lemma dnf_iwiIH l lp li l' X A N D Ot C M c a cs : dnfty X -> dnfty A -> dnftm N -> dnfty D -> dnftm Ot ->
  dnftm C -> dnfty M -> dnftm c -> dnftm a -> dnftm cs -> dnftm (iwiIH l lp li l' X A N D Ot C M c a cs).
Proof.
  intros; unfold iwiIH.
  pose proof (dnf_iwiFam l lp li X A N D Ot C a ltac:(assumption) ltac:(assumption) ltac:(assumption)
                ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)) as HF.
  pose proof (dnf_iwiFamCod l lp li X A N D Ot C a ltac:(assumption) ltac:(assumption) ltac:(assumption)
                ltac:(assumption) ltac:(assumption) ltac:(assumption) ltac:(assumption)) as HB.
  assert (HD : dnfty D[llift (lsingle a)]) by (apply subst_dnf_ty; auto; apply lk_dnf_llift, lk_dnf_lsingle; auto).
  assert (Hn : dnftm (tmDNth (iwiL l lp li) N[lsingle a]⟨↑⟩⟨↑⟩ (iwiFam l lp li X A N D Ot C a)⟨rlift ↑⟩⟨rlift ↑⟩
                        cs⟨↑⟩⟨↑⟩ (var 1))).
  { apply dnf_tmDNth; auto using ren_dnf_ty, ren_dnf; [|exact I].
    apply ren_dnf, ren_dnf, subst_dnf; auto using lk_dnf_lsingle. }
  revert Hn HF HB HD.
  generalize (tmDNth (iwiL l lp li) N[lsingle a]⟨↑⟩⟨↑⟩ (iwiFam l lp li X A N D Ot C a)⟨rlift ↑⟩⟨rlift ↑⟩ cs⟨↑⟩⟨↑⟩ (var 1))
             (iwiFam l lp li X A N D Ot C a) (iwiFamCod l lp li X A N D Ot C a) D[llift (lsingle a)].
  intros x F B D' Hn HF HB HD.
  cbn [dnftm dnfty]; intuition auto using ren_dnf_ty, ren_dnf, subst_dnf, lk_dnf_lsingle, lk_dnf_llift.
Qed.

(** Goal-directed: each lemma chosen by the goal's head. Left to a
    [first] of [apply]s, each failing one unfolded its conclusion against
    the goal (13 s of [dnf_redt], 0.5 s now; docs/gotchas.md). *)
Ltac dnf_step := lazymatch goal with
  | |- True => exact I
  | |- _ /\ _ => split
  | |- dnftm (peelL _ _) => apply dnf_peelL
  | |- dnftm (peelG _ _) => apply dnf_peelG
  | |- dnftm (peelU _ _) => apply dnf_peelU
  | |- dnftm (tup_nth _ _) => apply dnf_tup_nth
  | |- dnftm (rb_br _ _) => unfold rb_br
  | |- dnfty (iwfFam _ _ _ _ _ _ _ _) => apply dnf_iwfFam
  | |- dnftm (tmDNth _ _ _ _ _) => apply dnf_tmDNth
  | |- dnftm (tmNth _ _ _ _ _) => apply dnf_tmNth
  | |- dnftm (wIH _ _ _ _ _ _ _ _ _) => apply dnf_wIH
  | |- dnftm (wfIH _ _ _ _ _ _ _ _) => apply dnf_wfIH
  | |- dnftm (iwfIH _ _ _ _ _ _ _ _ _ _ _ _) => apply dnf_iwfIH
  | |- dnfty (iwiFam _ _ _ _ _ _ _ _ _ _) => apply dnf_iwiFam
  | |- dnfty (iwiFamCod _ _ _ _ _ _ _ _ _ _) => apply dnf_iwiFamCod
  | |- dnftm (iwiIH _ _ _ _ _ _ _ _ _ _ _ _ _ _) => apply dnf_iwiIH
  | |- dnfty (ren _ _) => apply ren_dnf_ty
  | |- dnfty (ren_ty _ _) => apply ren_dnf_ty
  | |- dnftm (ren _ _) => apply ren_dnf
  | |- dnftm (ren_tm _ _) => apply ren_dnf
  | |- dnfty (subst _ _) => apply subst_dnf_ty
  | |- dnfty (subst_ty _ _) => apply subst_dnf_ty
  | |- dnftm (subst _ _) => apply subst_dnf
  | |- dnftm (subst_tm _ _) => apply subst_dnf
  | |- LK dnftm (lsingle _) => apply lk_dnf_lsingle
  | |- LK dnftm (lsingle2 _ _) => apply lk_dnf_lsingle2
  | |- LK dnftm (llift _) => apply lk_dnf_llift
  | |- LK dnftm lsucc => apply lk_dnf_lsucc
  | |- dnftm (recT _ _ _ _ _ _) => unfold recT
  | |- dnftm (rect _ _ _ _ _ _ _) => unfold rect
  | |- _ => first [assumption | progress cbn [dnfo dnftm dnfty dnfctx]]
  end.

Lemma dnf_redT l1 l2 rb l Δ c r : dnftm rb -> dnfctx Δ -> dnfty c ->
  redT l1 l2 rb l Δ c = Some r -> dnftm r.
Proof.
  intros Hrb HΔ Hc E. unfold rb_br in E.
  destruct c; cbn [redT] in E; first [discriminate E | apply Some_inj in E; subst r]; cbn in Hc;
    repeat match goal with H : _ /\ _ |- _ => destruct H end; repeat dnf_step.
Qed.
Lemma dnf_redt l1 l2 rb l Δ T c r : dnftm rb -> dnfctx Δ -> dnfty T -> dnftm c ->
  redt l1 l2 rb l Δ T c = Some r -> dnftm r.
Proof.
  intros Hrb HΔ HT Hc E. unfold rb_br in E.
  destruct c; cbn [redt] in E; redt_case T; first [discriminate E | apply Some_inj in E; subst r]; cbn in Hc, HT;
    repeat match goal with H : _ /\ _ |- _ => destruct H end; repeat dnf_step.
Qed.

(** [M] (M18b): [out]-of-[corec]'s reduct, and the instances in its rules. *)
Ltac dnf_M := repeat first
  [ lazymatch goal with |- True => exact I | |- _ /\ _ => split end | assumption
  | apply ren_dnf_ty | apply ren_dnf
  | apply subst_dnf_ty | apply subst_dnf | apply lk_dnf_lsingle | apply lk_dnf_lsingle2
  | apply lk_dnf_llift | progress cbn [dnftm dnfty] ].
Lemma dnf_mOutCorec l l' li X A B C k Y c j y : dnfty X -> dnfty A -> dnfty B -> dnftm C ->
  dnfty Y -> dnftm c -> dnftm j -> dnftm y -> dnftm (mOutCorec l l' li X A B C k Y c j y).
Proof. intros; unfold mOutCorec; dnf_M. Qed.
