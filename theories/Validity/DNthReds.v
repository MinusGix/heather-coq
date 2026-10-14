(** * How [dnth] computes, untyped (M17_DESIGN.md, M17b)

    [elim_IWf]'s motive at the spine compares eliminations at terms with
    the same weak-head normal form as a [dnth] into the children, as
    [elim_Wf]'s does for [nth] ([WfNthReds]). [dnth] is a [natrec] on the
    length applied to an embedding, the tuple and the index, and its
    successor step recurses at the embedding [λy. e (inr y)]: so the state
    of the computation ([DNat]) is that application at any length,
    embedding, tuple and index, with any annotations (reduction never
    reads them) and the [natrec]'s base and step at any normal [n] and
    [F]. At a successor length and an [inl] index it reduces to the head
    projection of the tuple; at an [inr j], to the state at the
    predecessor, the tail projection and [j]; at a zero or neutral
    length, or a neutral index, to a neutral. *)
From DeLaM.Validity Require Import WfNthReds DVecNthReds.

(** ** [dnth]'s base and step under renamings and substitutions

    By [Reduction.tmDNth_ren]'s and [SubstCommute.subst_tmDNth]'s scripts. *)

Lemma ren_dnthBase l n F r : (dnthBase l n F)⟨r⟩ = dnthBase l n⟨r⟩ F⟨rlift r⟩.
Proof.
  unfold dnthBase.
  rewrite ?lsingle_ren_ty, ?lsingle_ren. cbn [ren Ren_tm Ren_ty ren_tm ren_ty rlk]. fold ren_ty ren_tm.
  rewrite ?lsingle_ren_ty, ?lsingle_ren. cbn [ren Ren_tm Ren_ty ren_tm ren_ty rlk]. fold ren_ty ren_tm.
  repeat ren_cong.
Qed.
Lemma ren_dnthMot l n F r : (dnthMot l n F)⟨rlift r⟩ = dnthMot l n⟨r⟩ F⟨rlift r⟩.
Proof.
  unfold dnthMot, dnthEmb, dnthFam, dnthRes.
  rewrite ?lsingle_ren_ty, ?lsingle_ren. cbn [ren Ren_tm Ren_ty ren_tm ren_ty rlk]. fold ren_ty ren_tm.
  rewrite ?lsingle_ren_ty, ?lsingle_ren. cbn [ren Ren_tm Ren_ty ren_tm ren_ty rlk]. fold ren_ty ren_tm.
  repeat ren_cong.
Qed.
Lemma ren_dnthStep l n F r : (dnthStep l n F)⟨rlift (rlift r)⟩ = dnthStep l n⟨r⟩ F⟨rlift r⟩.
Proof.
  unfold dnthStep, dnthEmb, dnthFam, dnthRes, dnthFamS.
  rewrite ?lsingle_ren_ty, ?lsingle_ren. cbn [ren Ren_tm Ren_ty ren_tm ren_ty rlk]. fold ren_ty ren_tm.
  rewrite ?lsingle_ren_ty, ?lsingle_ren. cbn [ren Ren_tm Ren_ty ren_tm ren_ty rlk]. fold ren_ty ren_tm.
  repeat ren_cong.
Qed.

(** [SubstCommute.subst_tmDNth]'s script, at the base and the step. *)
Local Ltac dsub Hd :=
  repeat progress (
    repeat match goal with
      | |- context [subst (subst ?B (lsingle ?u)) ?e] =>
          let H := fresh in assert (H : LK nftm e) by (repeat apply lk_llift; exact Hd);
          rewrite (single_subst_ty e H B u); clear H; push_subst
      end;
    rewrite ?llk_llift; cbn [llk];
    rewrite ?shift_llift_ty, ?shift_llift, ?liftshift_llift_ty, ?liftshift_llift).

Lemma subst_dnthBase l n F d : LK nftm d -> (dnthBase l n F)[d] = dnthBase l n[d] F[llift d].
Proof. intros Hd. unfold dnthBase. push_subst. dsub Hd. reflexivity. Qed.
Lemma subst_dnthStep l n F d : LK nftm d -> (dnthStep l n F)[llift (llift d)] = dnthStep l n[d] F[llift d].
Proof.
  intros Hd. unfold dnthStep, dnthEmb, dnthFam, dnthRes, dnthFamS. push_subst. dsub Hd.
  cbn [ren_tm rlk]. rewrite ?rlk_shift1. pw.
Qed.

(** [dnth]'s base, step and motive are normal at normal [n] and [F]: each
    is its own renaming at the identity. *)
Lemma nf_lift_id (F : ty) : nfty F -> F⟨rlift (rshift 0)⟩ = F.
Proof. intros NF. rewrite <- (ren_id_ty F NF) at 2. apply ren_ext_ty. intros [|k]; rlk_simpl; reflexivity. Qed.
Lemma nf_dnthBase l n F : nftm n -> nfty F -> nftm (dnthBase l n F).
Proof.
  intros Nn NF. rewrite <- (ren_id_tm n Nn), <- (nf_lift_id F NF), <- ren_dnthBase. apply ren_nf.
Qed.
Lemma nf_dnthStep l n F : nftm n -> nfty F -> nftm (dnthStep l n F).
Proof.
  intros Nn NF. rewrite <- (ren_id_tm n Nn), <- (nf_lift_id F NF), <- ren_dnthStep. apply ren_nf.
Qed.
Lemma nf_dnthMot l n F : nftm n -> nfty F -> nfty (dnthMot l n F).
Proof.
  intros Nn NF. rewrite <- (ren_id_tm n Nn), <- (nf_lift_id F NF), <- ren_dnthMot. apply ren_nf_ty.
Qed.

Local Ltac lkn := repeat apply lk_llift; intros [|[|?]]; cbn; auto using ren_nf.
(** Normality goals, by structure only: [split], [exact I] or [assumption]
    at a substitution would compute it. *)
Local Ltac nfs2 := repeat first [
    match goal with
    | |- True => exact I
    | |- nftm ?x => is_var x; assumption
    | |- nfty ?x => is_var x; assumption
    | |- _ /\ _ => split
    | |- nftm (subst _ _) => apply subst_nf
    | |- nfty (subst _ _) => apply subst_nf_ty
    | |- nftm (ren _ _) => apply ren_nf
    | |- nfty (ren _ _) => apply ren_nf_ty
    | |- nftm (ren_tm _ _) => apply ren_nf
    | |- nfty (ren_ty _ _) => apply ren_nf_ty
    | |- nftm (dnthBase _ _ _) => apply nf_dnthBase
    | |- nftm (dnthStep _ _ _) => apply nf_dnthStep
    | |- nfty (dnthMot _ _ _) => apply nf_dnthMot
    | |- LK nftm (llift _) => apply lk_llift
    | |- LK nftm (lsingle2 _ _) => apply lk_lsingle2
    | |- LK nftm (lsingle _) => apply lk_lsingle
    | |- nftm (dvecHd _ _) => unfold dvecHd
    | |- nfty (dnthFamS _ _) => unfold dnthFamS
    end
  | progress cbn [nftm nfty] ].
Local Ltac dsimp := repeat first [ rewrite ren_dnthBase | rewrite ren_dnthStep
  | rewrite subst_dnthBase by lkn | rewrite subst_dnthStep by lkn ].

Local Ltac rstep0 := eapply Relation_Operators.rt1n_trans;
  [repeat first [apply red_natrec_zero | apply red_app] |].

(** ** The computation's states *)

Section DNthReds.

(** [dnth]'s [natrec] at the length [K], applied to the embedding [e],
    the tuple [c0] and the index [i], at any level and annotations. *)
Definition DNat (K e c0 i u : tm) : Prop :=
  exists L n F Mot A1 B1 A2 B2 A3 B3, nftm n /\ nfty F /\ nfty Mot /\
    u = app (app (app (natrec L Mot (dnthBase L n F) (dnthStep L n F) K) lzero L A1 B1 e)
               L L A2 B2 c0) lzero L A3 B3 i.

Lemma dn_top {L n F cs i} : nftm n -> nfty F ->
  DNat n (lam lzero lzero (tyFin n) (var 0)) cs i (tmDNth L n F cs i).
Proof using .
  intros Nn NF. do 10 eexists. split; [| split; [| split; [| reflexivity]]].
  - exact Nn.
  - exact NF.
  - apply nf_dnthMot; assumption.
Qed.

Lemma dn_cong {K K' e c0 i u} : reds K K' -> DNat K e c0 i u -> exists u', DNat K' e c0 i u' /\ reds u u'.
Proof using .
  intros Hk (L & n & F & Mot & A1 & B1 & A2 & B2 & A3 & B3 & Nn & NF & NM & ->).
  eexists. split; [do 10 eexists; split; [exact Nn | split; [exact NF | split; [exact NM | reflexivity]]]|].
  now apply reds_app, reds_app, reds_app, reds_natrec.
Qed.

Lemma dn_inl {K m e c0 i u k1 k2 C D a} : nftm m -> nftm e -> nftm c0 -> nftm i -> reds K (succ m) ->
  reds i (tmInl k1 k2 C D a) -> DNat K e c0 i u -> exists L A B, reds u (tmFst L L A B c0).
Proof using .
  intros Nm Ne Nc Ni Hk Hi (L & n & F & Mot & A1 & B1 & A2 & B2 & A3 & B3 & Nn & NF & NM & ->).
  do 3 eexists.
  eapply reds_trans; [apply reds_app, reds_app, reds_app, reds_natrec, Hk|].
  rstep. unfold dnthStep at 1. tpush.
  rstep. tpush.
  rstep. tpush.
  rstep. tpush.
  eapply reds_trans; [apply reds_case, Hi|].
  rstep. tpush. apply reds_eq. f_equal. teq.
Qed.

Lemma dn_inr {K m e c0 i u k1 k2 C D j} : nftm m -> nftm e -> nftm c0 -> nftm i -> nftm j -> reds K (succ m) ->
  reds i (tmInr k1 k2 C D j) -> DNat K e c0 i u ->
  exists e' L A B u', nftm e' /\ nftm (tmSnd L L A B c0) /\ DNat m e' (tmSnd L L A B c0) j u' /\ reds u u'.
Proof using .
  intros Nm Ne Nc Ni Nj Hk Hi (L & n & F & Mot & A1 & B1 & A2 & B2 & A3 & B3 & Nn & NF & NM & ->).
  do 5 eexists. split; [|split; [|split; [do 10 eexists; split; [|split; [|split]]|]]].
  7: eapply reds_trans; [apply reds_app, reds_app, reds_app, reds_natrec, Hk|];
     rstep; unfold dnthStep at 1; tpush;
     rstep; tpush;
     rstep; tpush;
     rstep; tpush;
     eapply reds_trans; [apply reds_case, Hi|];
     rstep; tpush; apply reds_eq; reflexivity.
  6: dsimp; repeat f_equal.
  all: try teq.
  all: nfs2.
Qed.

Lemma dn_case_ne {K m e c0 i u ν} : nftm m -> nftm e -> nftm c0 -> nftm i -> reds K (succ m) ->
  reds i ν -> whne ν -> DNat K e c0 i u -> exists X, reds u X /\ whne X.
Proof using .
  intros Nm Ne Nc Ni Hk Hi Hν (L & n & F & Mot & A1 & B1 & A2 & B2 & A3 & B3 & Nn & NF & NM & ->).
  eexists. split.
  - eapply reds_trans; [apply reds_app, reds_app, reds_app, reds_natrec, Hk|].
    rstep. unfold dnthStep at 1. tpush.
    rstep. tpush.
    rstep. tpush.
    rstep. tpush.
    apply reds_case, Hi.
  - now apply whne_case.
Qed.

Lemma dn_zero {K e c0 i u ν} : reds K zero -> reds i ν -> whne ν -> DNat K e c0 i u -> exists X, reds u X /\ whne X.
Proof using .
  intros Hk Hi Hν (L & n & F & Mot & A1 & B1 & A2 & B2 & A3 & B3 & Nn & NF & NM & ->).
  eexists. split.
  - eapply reds_trans; [apply reds_app, reds_app, reds_app, reds_natrec, Hk|].
    rstep0. unfold dnthBase at 1. tpush.
    rstep. tpush.
    rstep. tpush.
    rstep. tpush.
    apply reds_elimEmpty, Hi.
  - now apply whne_elimEmpty.
Qed.

Lemma dn_ne {K e c0 i u ν} : reds K ν -> whne ν -> DNat K e c0 i u -> exists X, reds u X /\ whne X.
Proof using .
  intros Hk Hν (L & n & F & Mot & A1 & B1 & A2 & B2 & A3 & B3 & Nn & NF & NM & ->).
  eexists. split; [apply reds_app, reds_app, reds_app, reds_natrec, Hk|].
  now apply whne_app, whne_app, whne_app, whne_natrec.
Qed.

End DNthReds.

(** ** Joinability up to neutral projections

    The children reached through [dnth]'s states carry the annotations
    its [natrec] step writes, not the spine's: two terms are joinable when
    they reduce to a common term or both to neutrals. A projection of a
    tuple reducing to a pair or a neutral is joinable with that
    projection at any annotations. *)

Lemma reds_cmp t x w : reds t x -> reds t w -> reds x w \/ reds w x.
Proof.
  intros H; revert w; induction H as [t|t u x Htu Hux IH]; intros w Hw.
  - left; exact Hw.
  - destruct Hw as [|? ? Htv Hvw].
    + right. econstructor; eassumption.
    + rewrite (red_det _ _ _ Htu Htv) in IH. exact (IH _ Hvw).
Qed.

Lemma reds_toward_whnf t x w : reds t x -> reds t w -> whnf w -> reds x w.
Proof.
  intros Hx Hw Nw. destruct (reds_cmp t x w Hx Hw) as [H|H]; [exact H|].
  destruct H as [|? ? Hr _]; [constructor | exfalso; exact (whnf_no_red _ _ Nw Hr)].
Qed.

Lemma reds_from_whnf w x : whnf w -> reds w x -> x = w.
Proof. intros Nw H. destruct H as [|? ? Hr _]; [reflexivity | exfalso; exact (whnf_no_red _ _ Nw Hr)]. Qed.

Definition Join (s t : tm) : Prop :=
  (exists x, reds s x /\ reds t x) \/ (exists x y, reds s x /\ reds t y /\ whne x /\ whne y).

Lemma join_refl t : Join t t.
Proof. left. exists t. split; constructor. Qed.

Lemma join_reds_l s s1 t : reds s s1 -> Join s1 t -> Join s t.
Proof.
  intros Hs [(x & H1 & H2)|(x & y & H1 & H2 & N1 & N2)].
  - left. exists x. split; [exact (reds_trans _ _ _ Hs H1) | exact H2].
  - right. exists x, y. split; [exact (reds_trans _ _ _ Hs H1) | auto].
Qed.

Lemma join_red s t w : Join s t -> reds t w -> whnf w -> Join s w.
Proof.
  intros [(x & H1 & H2)|(x & y & H1 & H2 & N1 & N2)] Hw Nw.
  - left. exists w. split; [exact (reds_trans _ _ _ H1 (reds_toward_whnf _ _ _ H2 Hw Nw)) | constructor].
  - right. exists x, w. assert (y = w) as <- by exact (reds_whnf_det _ _ _ H2 Hw (whnf_ne _ N2) Nw).
    split; [exact H1 | split; [constructor | split; assumption]].
Qed.

Lemma join_ne s t : Join s t -> whne t -> exists X, reds s X /\ whne X.
Proof.
  intros [(x & H1 & H2)|(x & y & H1 & H2 & N1 & N2)] Nt.
  - exists x. split; [exact H1|]. now rewrite (reds_from_whnf _ _ (whnf_ne _ Nt) H2).
  - exists x. split; assumption.
Qed.

Lemma join_whnf s t : Join s t -> whnf t -> ~ whne t -> reds s t.
Proof.
  intros [(x & H1 & H2)|(x & y & H1 & H2 & N1 & N2)] Nt Ht.
  - now rewrite (reds_from_whnf _ _ Nt H2) in H1.
  - exfalso. apply Ht. now rewrite (reds_from_whnf _ _ Nt H2) in N2.
Qed.

(** A whnf whose first projection reaches a whnf is a pair or neutral. *)
Lemma fst_cases la lb A B w v : whnf w -> reds (tmFst la lb A B w) v -> whnf v ->
  (exists l l' A' B' a b, w = tmPair l l' A' B' a b) \/ whne w.
Proof.
  intros Nw H Nv. destruct H.
  - right. inversion Nv; subst. match goal with Hn : whne (tmFst _ _ _ _ _) |- _ => now inversion Hn end.
  - match goal with Hr : red (tmFst _ _ _ _ _) _ |- _ => inversion Hr; subst end.
    + left. do 6 eexists. reflexivity.
    + exfalso. match goal with Hr : red w _ |- _ => exact (whnf_no_red _ _ Nw Hr) end.
Qed.

Definition PairOrNe (w : tm) : Prop := (exists l l' A' B' a b, w = tmPair l l' A' B' a b) \/ whne w.

(** Tuples joinable up to neutrals: [dnth]'s states hold a tuple reducing
    with the spine's. *)
Definition TC (c0 cs : tm) : Prop :=
  (exists u, reds c0 u /\ reds cs u) \/ (exists ν ν', reds c0 ν /\ whne ν /\ reds cs ν' /\ whne ν').

Lemma tc_refl c : TC c c.
Proof. left. exists c. split; constructor. Qed.

(** The tuple of a joinable pair reaches the spine's whnf, or both are
    neutral. *)
Lemma tc_whnf c0 cs w : TC c0 cs -> reds cs w -> whnf w -> reds c0 w \/ (exists ν, reds c0 ν /\ whne ν /\ whne w).
Proof.
  intros [(u & H1 & H2)|(ν & ν' & H1 & N1 & H2 & N2)] Hw Nw.
  - left. exact (reds_trans _ _ _ H1 (reds_toward_whnf _ _ _ H2 Hw Nw)).
  - right. exists ν. assert (ν' = w) as <- by exact (reds_whnf_det _ _ _ H2 Hw (whnf_ne _ N2) Nw). auto.
Qed.

Lemma join_fst c0 cs w L L' A B la lb A2 B2 : TC c0 cs -> reds cs w -> whnf w -> PairOrNe w ->
  Join (tmFst L L' A B c0) (tmFst la lb A2 B2 w).
Proof.
  intros Htc Hw Nw Pw. destruct (tc_whnf _ _ _ Htc Hw Nw) as [Hc0|(ν & Hν & Nν & Nw')].
  - destruct Pw as [(l & l' & A' & B' & a & b & ->)|Nw'].
    + left. exists a. split.
      * eapply reds_trans; [apply reds_fst, Hc0|]. econstructor; [apply red_fst_beta | constructor].
      * econstructor; [apply red_fst_beta | constructor].
    + right. exists (tmFst L L' A B w), (tmFst la lb A2 B2 w).
      split; [apply reds_fst, Hc0 | split; [constructor | split; now constructor]].
  - right. exists (tmFst L L' A B ν), (tmFst la lb A2 B2 w).
    split; [apply reds_fst, Hν | split; [constructor | split; now constructor]].
Qed.

Lemma tc_snd c0 cs w L L' A B la lb A2 B2 : TC c0 cs -> reds cs w -> whnf w -> PairOrNe w ->
  TC (tmSnd L L' A B c0) (tmSnd la lb A2 B2 w).
Proof.
  intros Htc Hw Nw Pw. destruct (tc_whnf _ _ _ Htc Hw Nw) as [Hc0|(ν & Hν & Nν & Nw')].
  - destruct Pw as [(l & l' & A' & B' & a & b & ->)|Nw'].
    + left. exists b. split.
      * eapply reds_trans; [apply reds_snd, Hc0|]. econstructor; [apply red_snd_beta | constructor].
      * econstructor; [apply red_snd_beta | constructor].
    + right. exists (tmSnd L L' A B w), (tmSnd la lb A2 B2 w).
      split; [apply reds_snd, Hc0 | split; [now constructor | split; [constructor | now constructor]]].
  - right. exists (tmSnd L L' A B ν), (tmSnd la lb A2 B2 w).
    split; [apply reds_snd, Hν | split; [now constructor | split; [constructor | now constructor]]].
Qed.
