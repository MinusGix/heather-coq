(** * Validity of [elim_IWf] (M17_DESIGN.md, M17b)

    As [elim_Wf]'s ([WfElim]), by induction on [IWfRel] at every global
    weakening and related substitution, with two differences.

    - The motive is index-agnostic: at a tree [t], any two terms related
      at [IWf] at any index [m] and joinable with [t] have related
      eliminations at [m]. The induction runs at the tree's own index, a
      [sup_i] sits at its output index [Ot[a]], and the eliminations are
      compared at the scrutinee's: [IWfNf] relates [Ot[a]] to it.
    - At the spine, the motive is stated at [dnth]'s states ([DNat]): the
      child the induction hypothesis reaches is a projection of the tuple
      at the annotations [dnth]'s [natrec] step writes, not at the
      spine's, so the tuples and the children are compared up to
      reduction to a common term or to neutrals ([TC], [Join]), which
      projections of a pair or a neutral respect at any annotations.

    The induction hypothesis's type is related left to right ([Vih]):
    the right-hand λ is typed in the right-hand signature
    ([IWf_prem_r]). *)
From DeLaM.Validity Require Export IWf DVecNth WfElim DNthReds.
From DeLaM.Typing Require Import IWfIH.
From DeLaM.LogRel Require Import IWfAux.
From DeLaM.Validity Require Import IWfSp.

(** ** Syntax *)

Lemma gwa_elimIWf γ l li l' X A N Ot C M c m t :
  (tmElimIWf l li l' X A N Ot C M c m t)⟦γ⟧ =
  tmElimIWf l li l' X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧ M⟦γ⟧ c⟦γ⟧ m⟦γ⟧ t⟦γ⟧.
Proof. now destruct γ. Qed.
Lemma gwa_tmDNth γ l n F cs i : (tmDNth l n F cs i)⟦γ⟧ = tmDNth l n⟦γ⟧ F⟦γ⟧ cs⟦γ⟧ i⟦γ⟧.
Proof. destruct γ; cbn [gwa]; [reflexivity | apply gren_tmDNth ..]. Qed.
Lemma gwa_iwfIH γ l li l' X A N Ot C M c a cs :
  (iwfIH l li l' X A N Ot C M c a cs)⟦γ⟧ = iwfIH l li l' X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧ M⟦γ⟧ c⟦γ⟧ a⟦γ⟧ cs⟦γ⟧.
Proof. destruct γ; cbn [gwa]; [reflexivity | apply gren_iwfIH ..]. Qed.
Lemma gwa_iwfFam γ l li X A N Ot C a :
  (iwfFam l li X A N Ot C a)⟦γ⟧ = iwfFam l li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧ a⟦γ⟧.
Proof. destruct γ; cbn [gwa]; [reflexivity | apply gren_iwfFam ..]. Qed.

Local Ltac gwpush := repeat first [ rewrite gwa_tyPi | rewrite gwa_tyFin | rewrite gwa_subst_ty | rewrite gwa_subst
  | rewrite gwa_lsingle | rewrite gwa_lsingle2 | rewrite gwa_tmDNth | rewrite gwa_var | rewrite gwa_ren_ty
  | rewrite gwa_ren | rewrite gwa_tyIWf | rewrite gwa_tyDVec | rewrite gwa_supi | rewrite gwa_iwfFam
  ].

Lemma gwa_iwfmotty γ l li X A N Ot C :
  (iwfmotty l li X A N Ot C)⟦γ⟧ = iwfmotty l li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧.
Proof using . gwpush. reflexivity. Qed.
Lemma gwa_iwfcsty γ l li X A N Ot C :
  (iwfcsty l li X A N Ot C)⟦γ⟧ = iwfcsty l li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧.
Proof using . gwpush. reflexivity. Qed.
Lemma gwa_iwfihty γ l li l' X A N Ot C (M : ty) :
  (iwfihty l li l' X A N Ot C M)⟦γ⟧ = iwfihty l li l' X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧ M⟦γ⟧.
Proof using . gwpush. reflexivity. Qed.
Lemma gwa_iwfstepty γ l li X A N Ot C (M : ty) :
  (iwfstepty l li X A N Ot C M)⟦γ⟧ = iwfstepty l li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧ M⟦γ⟧.
Proof using . gwpush. reflexivity. Qed.

Section Telescope.
Context (d : lsub) (Hd : LK nftm d).

Local Ltac tsub := push_subst;
  repeat first [ rewrite subst_tmDNth by (repeat apply lk_llift; exact Hd) | progress push_subst
               | match goal with |- context [@subst ty _ (@subst ty _ ?M (lsingle2 ?t ?q)) ?e] =>
                   rewrite (single2_subst_ty e ltac:(repeat apply lk_llift; exact Hd) M t q) end
               | rewrite shift_llift_ty | rewrite shift_llift | rewrite liftshift_llift_ty | rewrite liftshift_llift
               | rewrite lift2shift_llift | rewrite lift2shift_llift_ty | rewrite lift3shift_llift ];
  rewrite ?llk_llift_S, ?llk_llift0; push_ren; rlk_simpl; try reflexivity.

Lemma iwfmotty_llift l li (X A : ty) (N Ot C : tm) :
  (iwfmotty l li X A N Ot C)[llift d] = iwfmotty l li X[d] A[d] N[llift d] Ot[llift d] C[llift (llift d)].
Proof using Hd. tsub. Qed.
Lemma iwfcsty_llift l li (X A : ty) (N Ot C : tm) :
  (iwfcsty l li X A N Ot C)[llift d] = iwfcsty l li X[d] A[d] N[llift d] Ot[llift d] C[llift (llift d)].
Proof using Hd. tsub. Qed.
Lemma iwfihty_llift2 l li l' (X A : ty) (N Ot C : tm) (M : ty) :
  (iwfihty l li l' X A N Ot C M)[llift (llift d)] =
  iwfihty l li l' X[d] A[d] N[llift d] Ot[llift d] C[llift (llift d)] M[llift (llift d)].
Proof using Hd. tsub. Qed.
Lemma iwfstepty_llift3 l li (X A : ty) (N Ot C : tm) (M : ty) :
  (iwfstepty l li X A N Ot C M)[llift (llift (llift d))] =
  iwfstepty l li X[d] A[d] N[llift d] Ot[llift d] C[llift (llift d)] M[llift (llift d)].
Proof using Hd. tsub. Qed.

End Telescope.

(** ** The children's [dnth] under the step's telescope

    [iwfihty]'s [dnth], in [Γ, x : A, cs : csty, i : Fin N], at the family
    [iwfFc] (its family binder at [Fin N]); at a substitution it is the
    induction hypothesis's [dnth] at the shape and children. *)
Notation iwfFc l li X A N Ot C :=
  (tyIWf l li X⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ A⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ N⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩
     Ot⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩
     C⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩ C⟨rlift ↑⟩⟨rlift ↑⟩).

Lemma liftshift_llift_cons (t : tm) d u : t⟨rlift ↑⟩[llift (lcons d u)] = t[llift d].
Proof. apply ren_subst. intros [|n]; rlk_simpl; rewrite ?llk_llift; reflexivity. Qed.
Lemma lift2shift_llift2_cons (t : tm) d u : t⟨rlift (rlift ↑)⟩[llift (llift (lcons d u))] = t[llift (llift d)].
Proof. apply ren_subst. intros [|[|n]]; rlk_simpl; rewrite ?llk_llift; reflexivity. Qed.
Lemma n3_single (N : tm) : N⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (var 2)] = N⟨↑⟩⟨↑⟩.
Proof.
  rewrite !ren_ren_comp, ren_as_r2l, (ren_as_r2l N), subst_comp. apply subst_ext.
  intros [|n]; pw.
Qed.
Lemma c3_single (C : tm) :
  C⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩[llift (lsingle (var 2))] = C⟨rlift ↑⟩⟨rlift ↑⟩.
Proof.
  rewrite !ren_ren_comp, ren_as_r2l, (ren_as_r2l C), subst_comp. apply subst_ext.
  intros [|[|n]]; pw.
Qed.
Lemma iwfFc_fam l li (X A : ty) (N Ot C : tm) :
  iwfFc l li X A N Ot C =
  iwfFam l li X⟨↑⟩⟨↑⟩⟨↑⟩ A⟨↑⟩⟨↑⟩⟨↑⟩ N⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ Ot⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩
    C⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩⟨rlift (rlift ↑)⟩ (var 2).
Proof. unfold iwfFam. now rewrite c3_single. Qed.

Lemma llift2_single_cons (C : tm) d a : LK nftm d -> C[llift (llift d)][llift (lsingle a)] = C[llift (lcons d a)].
Proof.
  intros Hd. apply subst_subst. intros [|[|n]]; rewrite ?llk_llift; cbn; rewrite ?llk_llift; cbn; try reflexivity.
  change (ren_tm (ren_tm ?x ?r) ?r') with x⟨r⟩⟨r'⟩. change (ren_tm ?x ?r) with x⟨r⟩.
  rewrite shift_llift, shift_single by apply Hd. reflexivity.
Qed.

Lemma iwfFc_subst l li (X A : ty) (N Ot C : tm) d a cs y : LK nftm d ->
  (iwfFc l li X A N Ot C)[llift (lcons (lcons (lcons d a) cs) y)] =
  iwfFam l li X[d] A[d] N[llift d] Ot[llift d] C[llift (llift d)] a.
Proof.
  intros Hd. unfold iwfFam. push_subst.
  rewrite !shift_llift_ty, !liftshift_llift, !lift2shift_llift, !shift_subst_ty, !liftshift_llift_cons,
    !lift2shift_llift2_cons. cbn [ldrop].
  f_equal. symmetry. apply llift2_single_cons, Hd.
Qed.

Lemma iwf_dnthv_subst l li (X A : ty) (N Ot C : tm) d a cs y : LK nftm d -> nftm a -> nftm cs -> nftm y ->
  (tmDNth (lmax l li) N⟨↑⟩⟨↑⟩ (iwfFc l li X A N Ot C) (var 1) (var 0))[lcons (lcons (lcons d a) cs) y] =
  tmDNth (lmax l li) N[llift d][lsingle a] (iwfFam l li X[d] A[d] N[llift d] Ot[llift d] C[llift (llift d)] a) cs y.
Proof.
  intros Hd Na Ncs Ny.
  assert (Hd3 : LK nftm (lcons (lcons (lcons d a) cs) y)) by (intros [|[|[|n]]]; cbn; auto).
  rewrite subst_tmDNth, iwfFc_subst by first [exact Hd3 | exact Hd].
  rewrite !shift_subst_tm. cbn [ldrop]. rewrite lift_single_tm by exact Hd. reflexivity.
Qed.

Lemma iwfFc_single_subst l li (X A : ty) (N Ot C : tm) d a cs y : LK nftm d -> nftm a -> nftm cs -> nftm y ->
  nfty X[d] -> nfty A[d] -> nftm N[llift d] -> nftm Ot[llift d] -> nftm C[llift (llift d)] ->
  (iwfFc l li X A N Ot C)[lsingle (var 0)][lcons (lcons (lcons d a) cs) y] =
  tyIWf l li X[d] A[d] N[llift d] Ot[llift d] C[llift (llift d)] C[llift (llift d)][lsingle2 a y].
Proof.
  intros Hd Na Ncs Ny NX NA NN NO NC.
  assert (Hd3 : LK nftm (lcons (lcons (lcons d a) cs) y)) by (intros [|[|[|n]]]; cbn; auto).
  rewrite single_subst_ty, iwfFc_subst by first [exact Hd3 | exact Hd]. cbn [subst_tm llk].
  rewrite iwfFam_T, iwfFamT_single, llift_single_single by assumption. reflexivity.
Qed.

Section IWfElim.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

(** ** Kripke weakenings of the step's pieces *)

Definition ktyll {G Δ} (ρ : kwk G Δ) (T : ty) : ty := T⟦kw_γ ρ⟧⟨rlift (rlift (kw_r ρ))⟩.

Section KwSubst2.
Context {G : gctx} {Δ : ctx} (ρ : kwk G Δ) (e : lsub).

Lemma ktyll_subst_lift (T : ty) : ktyll ρ T[llift (llift e)] = T⟦kw_γ ρ⟧[llift (llift (kwsub ρ e))].
Proof using .
  unfold ktyll, kwsub. rewrite gwa_subst_ty, subst_ren_lren_ty.
  apply subst_ext_ty. intros n. rewrite llk_lren.
  destruct n as [|[|n]]; repeat rewrite ?llk_llift_gwa, ?llk_llift, ?llk_lren; try reflexivity.
  change (ren_tm ?x ?r') with x⟨r'⟩. rewrite !ren_ren_comp. apply ren_ext_tm. intros k. rlk_simpl. lia.
Qed.
Lemma ktmll_subst_lift (t : tm) : ktmll ρ t[llift (llift e)] = t⟦kw_γ ρ⟧[llift (llift (kwsub ρ e))].
Proof using .
  unfold ktmll, kwsub. rewrite gwa_subst, subst_ren_lren.
  apply subst_ext. intros n. rewrite llk_lren.
  destruct n as [|[|n]]; repeat rewrite ?llk_llift_gwa, ?llk_llift, ?llk_lren; try reflexivity.
  change (ren_tm ?x ?r') with x⟨r'⟩. rewrite !ren_ren_comp. apply ren_ext_tm. intros k. rlk_simpl. lia.
Qed.

End KwSubst2.

Lemma kγ_tyll {G Δ} (ρ : kwk G Δ) (T : ty) γ e :
  ktyll ρ T⟦γ⟧[llift (llift e)] = T⟦gwk_comp (kw_γ ρ) γ⟧[llift (llift (kwsub ρ e))].
Proof using . now rewrite ktyll_subst_lift, gwa_comp_ty. Qed.
Lemma kγ_tmll {G Δ} (ρ : kwk G Δ) (t : tm) γ e :
  ktmll ρ t⟦γ⟧[llift (llift e)] = t⟦gwk_comp (kw_γ ρ) γ⟧[llift (llift (kwsub ρ e))].
Proof using . now rewrite ktmll_subst_lift, gwa_comp_tm. Qed.

Lemma ktm_iwfIH {G Δ} (ρ : kwk G Δ) l li l' X A N Ot C M c a cs :
  ktm ρ (iwfIH l li l' X A N Ot C M c a cs) =
  iwfIH l li l' (kty ρ X) (kty ρ A) (ktml ρ N) (ktml ρ Ot) (ktmll ρ C) (ktyll ρ M) (ktm3 ρ c) (ktm ρ a) (ktm ρ cs).
Proof using . unfold ktm, kty, ktml, ktmll, ktyll, ktm3. now rewrite gwa_iwfIH, ren_iwfIH. Qed.

(** The induction hypothesis's body and codomain at a position. *)
Lemma lift2shift_llift2_single (t y : tm) : nftm t -> t⟨rlift (rlift ↑)⟩[llift (llift (lsingle y))] = t.
Proof using .
  intros Nt. rewrite (ren_subst _ _ _ (lshift 0)).
  - apply subst_id; [exact Nt | intros; cbn; f_equal; lia].
  - intros [|[|n]]; pw.
Qed.
Lemma lift2shift_llift2_single_ty (T : ty) y : nfty T -> T⟨rlift (rlift ↑)⟩[llift (llift (lsingle y))] = T.
Proof using .
  intros NT. rewrite (ren_subst_ty _ _ _ (lshift 0)).
  - apply subst_id_ty; [exact NT | intros; cbn; f_equal; lia].
  - intros [|[|n]]; pw.
Qed.

Lemma iwfdnth_single l li (X A : ty) (N Ot C a cs y : tm) :
  nfty X -> nfty A -> nftm N -> nftm Ot -> nftm C -> nftm a -> nftm cs -> nftm y ->
  (iwfdnth l li X A N Ot C a cs)[lsingle y] =
  tmDNth (lmax l li) N[lsingle a] (iwfFam l li X A N Ot C a) cs y.
Proof using .
  intros NX NA NN NO NC Na Ncs Ny. rewrite subst_tmDNth by (apply lk_lsingle, Ny).
  assert (NNa : nftm N[lsingle a]) by (apply subst_nf; [exact NN | apply lk_lsingle, Na]).
  assert (NF : nfty (iwfFam l li X A N Ot C a)).
  { unfold iwfFam. cbn. repeat split; first [apply ren_nf_ty | apply ren_nf | apply subst_nf]; try assumption.
    apply lk_llift, lk_lsingle, Na. }
  rewrite shift_single, liftshift_llift_single_ty, shift_single by assumption. reflexivity.
Qed.

Lemma iwfbody_single l li l' (X A : ty) (N Ot C : tm) (M : ty) (c a cs y : tm) :
  nfty X -> nfty A -> nftm N -> nftm Ot -> nftm C -> nfty M -> nftm c -> nftm a -> nftm cs -> nftm y ->
  (iwfbody l li l' X A N Ot C M c a cs)[lsingle y] =
  tmElimIWf l li l' X A N Ot C M c C[lsingle2 a y] (tmDNth (lmax l li) N[lsingle a] (iwfFam l li X A N Ot C a) cs y).
Proof using .
  intros NX NA NN NO NC NM Nc Na Ncs Ny.
  rewrite subst_elimIWf, (iwfdnth_single l li X A N Ot C a cs y) by assumption.
  rewrite shift_single_ty, shift_single_ty, liftshift_llift_single, liftshift_llift_single,
    lift2shift_llift2_single, lift2shift_llift2_single_ty, lift3shift_llift3_single, llift_single_single
    by assumption.
  reflexivity.
Qed.

Lemma iwfcod_single l li (X A : ty) (N Ot C : tm) (M : ty) (a cs y : tm) :
  nfty X -> nfty A -> nftm N -> nftm Ot -> nftm C -> nfty M -> nftm a -> nftm cs -> nftm y ->
  (iwfcod l li X A N Ot C M a cs)[lsingle y] =
  M[lsingle2 C[lsingle2 a y] (tmDNth (lmax l li) N[lsingle a] (iwfFam l li X A N Ot C a) cs y)].
Proof using .
  intros NX NA NN NO NC NM Na Ncs Ny.
  rewrite (single2_subst_ty (lsingle y)) by (apply lk_lsingle, Ny).
  rewrite lift2shift_llift2_single_ty, llift_single_single, (iwfdnth_single l li X A N Ot C a cs y) by assumption.
  reflexivity.
Qed.

Lemma ktml_iwfbody {G Δ} (ρ : kwk G Δ) l li l' X A N Ot C M c a cs :
  ktml ρ (iwfbody l li l' X A N Ot C M c a cs) =
  iwfbody l li l' (kty ρ X) (kty ρ A) (ktml ρ N) (ktml ρ Ot) (ktmll ρ C) (ktyll ρ M) (ktm3 ρ c) (ktm ρ a) (ktm ρ cs).
Proof using .
  pose proof (ktm_iwfIH ρ l li l' X A N Ot C M c a cs) as H. unfold iwfIH in H. rewrite ktm_lam in H.
  injection H as _ H. exact H.
Qed.

Lemma ktml_iwfdnth {G Δ} (ρ : kwk G Δ) l li X A N Ot C a cs :
  ktml ρ (iwfdnth l li X A N Ot C a cs) =
  iwfdnth l li (kty ρ X) (kty ρ A) (ktml ρ N) (ktml ρ Ot) (ktmll ρ C) (ktm ρ a) (ktm ρ cs).
Proof using .
  pose proof (ktml_iwfbody ρ l li lzero X A N Ot C tyNat (var 0) a cs) as H.
  unfold ktml in H. rewrite gwa_elimIWf in H. cbn [ren_tm] in H. injection H; intros.
  match goal with Hd : _ = tmDNth _ _ _ _ _ |- _ => exact Hd end.
Qed.

Lemma ktyl_iwfcod {G Δ} (ρ : kwk G Δ) l li (X A : ty) (N Ot C : tm) (M : ty) (a cs : tm) :
  ktyl ρ (iwfcod l li X A N Ot C M a cs) =
  iwfcod l li (kty ρ X) (kty ρ A) (ktml ρ N) (ktml ρ Ot) (ktmll ρ C) (ktyll ρ M) (ktm ρ a) (ktm ρ cs).
Proof using .
  rewrite <- ktml_iwfdnth, ktmll_llift_single.
  unfold ktyl, ktml, ktyll. rewrite gwa_subst_ty, gwa_lsingle2, gwa_ren_ty, lsingle2_ren_ty. f_equal.
  rewrite !ren_ren_comp_ty. apply ren_ext_ty. intros [|[|n]]; rlk_simpl; reflexivity.
Qed.


(** ** Validity under inserted binders *)

Lemma lift1_subst_ty (T : ty) e : T⟨rlift ↑⟩[e] = T[lcons (ldrop 1 (ldrop 1 e)) (llk e 0)].
Proof using .
  apply ren_subst_ty. intros [|m]; rewrite rlk_rlift; [reflexivity|].
  change (llk (ldrop 1 (ldrop 1 e)) m = llk e (S (rlk ↑ m))). rewrite !llk_ldrop, rlk_shift1. f_equal.
Qed.
Lemma lift1_subst_tm (t : tm) e : t⟨rlift ↑⟩[e] = t[lcons (ldrop 1 (ldrop 1 e)) (llk e 0)].
Proof using .
  apply ren_subst. intros [|m]; rewrite rlk_rlift; [reflexivity|].
  change (llk (ldrop 1 (ldrop 1 e)) m = llk e (S (rlk ↑ m))). rewrite !llk_ldrop, rlk_shift1. f_equal.
Qed.
Lemma lift2_subst_ty (T : ty) e :
  T⟨rlift (rlift ↑)⟩[e] = T[lcons (lcons (ldrop 1 (ldrop 1 (ldrop 1 e))) (llk (ldrop 1 e) 0)) (llk e 0)].
Proof using .
  apply ren_subst_ty.
  intros [|[|m]]; rlk_simpl; cbn [llk]; rewrite ?llk_ldrop; try reflexivity; f_equal; lia.
Qed.
Lemma lift2_subst_tm (t : tm) e :
  t⟨rlift (rlift ↑)⟩[e] = t[lcons (lcons (ldrop 1 (ldrop 1 (ldrop 1 e))) (llk (ldrop 1 e) 0)) (llk e 0)].
Proof using .
  apply ren_subst.
  intros [|[|m]]; rlk_simpl; cbn [llk]; rewrite ?llk_ldrop; try reflexivity; f_equal; lia.
Qed.

Lemma VTm_lift1 {G Γ A t t' T D kd k l} : VTm G (Γ ,, A @ k) t t' T l ->
  VTm G (Γ ,, D @ kd ,, A⟨↑⟩ @ k) t⟨rlift ↑⟩ t'⟨rlift ↑⟩ T⟨rlift ↑⟩ l.
Proof using .
  intros H Δ d d' [[Hd _] Ha]. rewrite !shift_subst_ty in Ha.
  rewrite !lift1_subst_ty, !lift1_subst_tm. exact (H _ _ _ (SubRel_cons Hd Ha)).
Qed.
Lemma VG_lift1_tm {G Γ A t t' T D kd k l} : VTmG G (Γ ,, A @ k) t t' T l ->
  VTmG G (Γ ,, D @ kd ,, A⟨↑⟩ @ k) t⟨rlift ↑⟩ t'⟨rlift ↑⟩ T⟨rlift ↑⟩ l.
Proof using . intros. gl_lift. now apply VTm_lift1. Qed.

Lemma VTm_lift2 {G Γ A B t t' T D kd ka k l} : VTm G (Γ ,, A @ ka ,, B @ k) t t' T l ->
  VTm G (Γ ,, D @ kd ,, A⟨↑⟩ @ ka ,, B⟨rlift ↑⟩ @ k) t⟨rlift (rlift ↑)⟩ t'⟨rlift (rlift ↑)⟩ T⟨rlift (rlift ↑)⟩ l.
Proof using .
  intros H Δ d d' [[[Hd _] Ha] Hb]. rewrite !shift_subst_ty in Ha. rewrite !lift1_subst_ty in Hb.
  rewrite !lift2_subst_ty, !lift2_subst_tm. exact (H _ _ _ (SubRel_cons (SubRel_cons Hd Ha) Hb)).
Qed.
Lemma VG_lift2_tm {G Γ A B t t' T D kd ka k l} : VTmG G (Γ ,, A @ ka ,, B @ k) t t' T l ->
  VTmG G (Γ ,, D @ kd ,, A⟨↑⟩ @ ka ,, B⟨rlift ↑⟩ @ k) t⟨rlift (rlift ↑)⟩ t'⟨rlift (rlift ↑)⟩ T⟨rlift (rlift ↑)⟩ l.
Proof using . intros. gl_lift. now apply VTm_lift2. Qed.


Lemma VG_iwf {G Γ l li l' li' X X' A A' N N' Ot Ot' C C' m m'} :
  lwf (gL G) l -> lwf (gL G) li -> lequiv (gL G) l' l -> lequiv (gL G) li' li ->
  VTyG G Γ X X' li -> VTyG G Γ A A' l -> VTmG G (Γ ,, A @ l) N N' tyNat lzero ->
  VTmG G (Γ ,, A @ l) Ot Ot' X⟨↑⟩ li -> VTmG G (Γ ,, A @ l ,, tyFin N @ lzero) C C' X⟨↑⟩⟨↑⟩ li ->
  VTmG G Γ m m' X li ->
  VTyG G Γ (tyIWf l li X A N Ot C m) (tyIWf l' li' X' A' N' Ot' C' m') (lmax l li).
Proof using EL VL VN.
  intros Hwl Hwli Hl' Hli' VX VA VNt VO VC Vm. apply VTyG_intro. intros G' γ Hγ _.
  pose proof (VTyG_gwk VX Hγ) as VXγ. pose proof (VTyG_gwk VA Hγ) as VAγ.
  pose proof (VTmG_gwk VNt Hγ) as VNγ. rewrite gwa_cext, gwa_tyNat in VNγ.
  pose proof (VTmG_gwk VO Hγ) as VOγ. rewrite gwa_cext, gwa_ren_ty in VOγ.
  pose proof (VTmG_gwk VC Hγ) as VCγ. rewrite !gwa_cext, gwa_tyFin, !gwa_ren_ty in VCγ.
  pose proof (VTmG_loc (VTmG_gwk Vm Hγ)) as Vmγ.
  rewrite !gwa_tyIWf.
  exact (V_iwf (lwf_weaken _ _ _ (proj1 Hγ) Hwl) (lwf_weaken _ _ _ (proj1 Hγ) Hwli)
           (lequiv_weaken _ _ _ _ (proj1 Hγ) Hl') (lequiv_weaken _ _ _ _ (proj1 Hγ) Hli') VXγ VAγ VNγ VOγ VCγ Vmγ).
Qed.

(** The motive's scrutinee type at an index. *)
Lemma iwfmotty_cons l li (X A : ty) (N Ot C : tm) e x : LK nftm e ->
  nfty X[e] -> nfty A[e] -> nftm N[llift e] -> nftm Ot[llift e] -> nftm C[llift (llift e)] ->
  (iwfmotty l li X A N Ot C)[lcons e x] = tyIWf l li X[e] A[e] N[llift e] Ot[llift e] C[llift (llift e)] x.
Proof using .
  intros Ne NX NA NN NO NC. rewrite <- lift_single_ty by exact Ne. rewrite iwfmotty_llift by exact Ne.
  apply IWf_E_mot; assumption.
Qed.

(** ** The eliminator at related premises *)

Section ElimAt.
Context {G : gctx} {Γ : ctx} {l li l' l3 li3 l4 : lvl} {X X' A A' : ty} {N N' Ot Ot' C C' : tm}
  {M M' : ty} {c c' : tm}
  (Hwl : lwf (gL G) l) (Hwli : lwf (gL G) li) (Hwl' : lwf (gL G) l')
  (H13 : lequiv (gL G) l l3) (Hi3 : lequiv (gL G) li li3) (H24 : lequiv (gL G) l' l4)
  (HS : IWfSig (G := G) (i := ge_layer) Γ l li X A N Ot C)
  (VX : VTyG G Γ X X' li) (VA : VTyG G Γ A A' l)
  (VNt : VTmG G (Γ ,, A @ l) N N' tyNat lzero)
  (VO : VTmG G (Γ ,, A @ l) Ot Ot' X⟨↑⟩ li)
  (VC : VTmG G (Γ ,, A @ l ,, tyFin N @ lzero) C C' X⟨↑⟩⟨↑⟩ li)
  (Vmot : VTyG G (Γ ,, X @ li) (iwfmotty l li X A N Ot C) (iwfmotty l li X A N Ot C) (lmax l li))
  (VM : VTyG G (Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li) M M' l')
  (Vcs : VTyG G (Γ ,, A @ l) (iwfcsty l li X A N Ot C) (iwfcsty l li X A N Ot C) (lmax l li))
  (Vih : VTyG G (Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li)
           (iwfihty l li l' X A N Ot C M) (iwfihty l3 li3 l4 X' A' N' Ot' C' M') (lmax lzero l'))
  (Vc : VTmG G (Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ,, iwfihty l li l' X A N Ot C M @ lmax lzero l')
          c c' (iwfstepty l li X A N Ot C M) l').

(** The premises at a global weakening, localized. *)
Lemma elimIWf_loc {G0 γ} : gwk_ok γ G0 G ->
  VTyG G0 Γ⟦γ⟧ X⟦γ⟧ X'⟦γ⟧ li /\ VTyG G0 Γ⟦γ⟧ A⟦γ⟧ A'⟦γ⟧ l /\
  VTmG G0 (Γ⟦γ⟧ ,, A⟦γ⟧ @ l) N⟦γ⟧ N'⟦γ⟧ tyNat lzero /\
  VTmG G0 (Γ⟦γ⟧ ,, A⟦γ⟧ @ l) Ot⟦γ⟧ Ot'⟦γ⟧ X⟦γ⟧⟨↑⟩ li /\
  VTmG G0 (Γ⟦γ⟧ ,, A⟦γ⟧ @ l ,, tyFin N⟦γ⟧ @ lzero) C⟦γ⟧ C'⟦γ⟧ X⟦γ⟧⟨↑⟩⟨↑⟩ li /\
  VTy G0 (Γ⟦γ⟧ ,, X⟦γ⟧ @ li) (iwfmotty l li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧)
    (iwfmotty l li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧) (lmax l li) /\
  VTy G0 (Γ⟦γ⟧ ,, X⟦γ⟧ @ li ,, iwfmotty l li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧ @ lmax l li) M⟦γ⟧ M'⟦γ⟧ l' /\
  VTy G0 (Γ⟦γ⟧ ,, A⟦γ⟧ @ l) (iwfcsty l li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧)
    (iwfcsty l li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧) (lmax l li) /\
  VTy G0 (Γ⟦γ⟧ ,, A⟦γ⟧ @ l ,, iwfcsty l li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧ @ lmax l li)
    (iwfihty l li l' X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧ M⟦γ⟧) (iwfihty l3 li3 l4 X'⟦γ⟧ A'⟦γ⟧ N'⟦γ⟧ Ot'⟦γ⟧ C'⟦γ⟧ M'⟦γ⟧)
    (lmax lzero l') /\
  VTm G0 (Γ⟦γ⟧ ,, A⟦γ⟧ @ l ,, iwfcsty l li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧ @ lmax l li
            ,, iwfihty l li l' X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧ M⟦γ⟧ @ lmax lzero l')
    c⟦γ⟧ c'⟦γ⟧ (iwfstepty l li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧ M⟦γ⟧) l'.
Proof using VA VC VM VNt VO VX Vc Vcs Vih Vmot.
  intros Hγ.
  pose proof (VTyG_gwk VX Hγ) as VXγ. pose proof (VTyG_gwk VA Hγ) as VAγ.
  pose proof (VTmG_gwk VNt Hγ) as VNγ. rewrite gwa_cext, gwa_tyNat in VNγ.
  pose proof (VTmG_gwk VO Hγ) as VOγ. rewrite gwa_cext, gwa_ren_ty in VOγ.
  pose proof (VTmG_gwk VC Hγ) as VCγ. rewrite !gwa_cext, gwa_tyFin, !gwa_ren_ty in VCγ.
  pose proof (Vmot _ _ Hγ) as Vmotγ. rewrite gwa_cext, gwa_iwfmotty in Vmotγ.
  pose proof (VM _ _ Hγ) as VMγ. rewrite !gwa_cext, gwa_iwfmotty in VMγ.
  pose proof (Vcs _ _ Hγ) as Vcsγ. rewrite gwa_cext, gwa_iwfcsty in Vcsγ.
  pose proof (Vih _ _ Hγ) as Vihγ. rewrite !gwa_cext, gwa_iwfcsty, !gwa_iwfihty in Vihγ.
  pose proof (Vc _ _ Hγ) as Vcγ. rewrite !gwa_cext, gwa_iwfcsty, gwa_iwfihty, gwa_iwfstepty in Vcγ.
  repeat split; assumption.
Qed.

(** Abbreviations: the premises at a global weakening and a substitution. *)
Local Notation sX γ e := (X⟦γ⟧[e]).
Local Notation sX' γ e := (X'⟦γ⟧[e]).
Local Notation sA γ e := (A⟦γ⟧[e]).
Local Notation sA' γ e := (A'⟦γ⟧[e]).
Local Notation sN γ e := (N⟦γ⟧[llift e]).
Local Notation sN' γ e := (N'⟦γ⟧[llift e]).
Local Notation sO γ e := (Ot⟦γ⟧[llift e]).
Local Notation sO' γ e := (Ot'⟦γ⟧[llift e]).
Local Notation sC γ e := (C⟦γ⟧[llift (llift e)]).
Local Notation sC' γ e := (C'⟦γ⟧[llift (llift e)]).
Local Notation sM γ e := (M⟦γ⟧[llift (llift e)]).
Local Notation sM' γ e := (M'⟦γ⟧[llift (llift e)]).
Local Notation sc γ e := (c⟦γ⟧[llift (llift (llift e))]).
Local Notation sc' γ e := (c'⟦γ⟧[llift (llift (llift e))]).
Local Notation tyL γ e m := (tyIWf l li (sX γ e) (sA γ e) (sN γ e) (sO γ e) (sC γ e) m).
Local Notation elL γ e m t :=
  (tmElimIWf l li l' (sX γ e) (sA γ e) (sN γ e) (sO γ e) (sC γ e) (sM γ e) (sc γ e) m t).
Local Notation elR γ e m t :=
  (tmElimIWf l3 li3 l4 (sX' γ e) (sA' γ e) (sN' γ e) (sO' γ e) (sC' γ e) (sM' γ e) (sc' γ e) m t).

(** The premises at a related substitution after a global weakening. *)
Lemma elimIWf_at {G0 γ Δ0 e e'} : gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' ->
  [ G0 ; Δ0 ⊢g sX γ e @ li ] /\ [ G0 ; Δ0 ⊢ sX γ e ≈ sX' γ e' @ li ] /\
  [ G0 ; Δ0 ⊢g sA γ e @ l ] /\ [ G0 ; Δ0 ⊢ sA γ e ≈ sA' γ e' @ l ] /\
  [ G0 ; Δ0 ,, sA γ e @ l ⊢g sN γ e : tyNat @ lzero ] /\
  [ G0 ; Δ0 ,, sA γ e @ l ⊢ sN γ e ≈ sN' γ e' : tyNat @ lzero ] /\
  [ G0 ; Δ0 ,, sA γ e @ l ⊢g sO γ e : (sX γ e)⟨↑⟩ @ li ] /\
  [ G0 ; Δ0 ,, sA γ e @ l ⊢ sO γ e ≈ sO' γ e' : (sX γ e)⟨↑⟩ @ li ] /\
  [ G0 ; Δ0 ,, sA γ e @ l ,, tyFin (sN γ e) @ lzero ⊢g sC γ e : (sX γ e)⟨↑⟩⟨↑⟩ @ li ] /\
  [ G0 ; Δ0 ,, sA γ e @ l ,, tyFin (sN γ e) @ lzero ⊢ sC γ e ≈ sC' γ e' : (sX γ e)⟨↑⟩⟨↑⟩ @ li ] /\
  [ G0 ; Δ0 ,, sX γ e @ li ⊢g iwfmotty l li (sX γ e) (sA γ e) (sN γ e) (sO γ e) (sC γ e) @ lmax l li ] /\
  [ G0 ; Δ0 ,, sX γ e @ li ,, iwfmotty l li (sX γ e) (sA γ e) (sN γ e) (sO γ e) (sC γ e) @ lmax l li
      ⊢g sM γ e @ l' ] /\
  [ G0 ; Δ0 ,, sX γ e @ li ,, iwfmotty l li (sX γ e) (sA γ e) (sN γ e) (sO γ e) (sC γ e) @ lmax l li
      ⊢ sM γ e ≈ sM' γ e' @ l' ] /\
  [ G0 ; Δ0 ,, sA γ e @ l ⊢g iwfcsty l li (sX γ e) (sA γ e) (sN γ e) (sO γ e) (sC γ e) @ lmax l li ] /\
  [ G0 ; Δ0 ,, sA γ e @ l ,, iwfcsty l li (sX γ e) (sA γ e) (sN γ e) (sO γ e) (sC γ e) @ lmax l li
      ⊢g iwfihty l li l' (sX γ e) (sA γ e) (sN γ e) (sO γ e) (sC γ e) (sM γ e) @ lmax lzero l' ] /\
  [ G0 ; Δ0 ,, sA γ e @ l ,, iwfcsty l li (sX γ e) (sA γ e) (sN γ e) (sO γ e) (sC γ e) @ lmax l li
      ⊢ iwfihty l li l' (sX γ e) (sA γ e) (sN γ e) (sO γ e) (sC γ e) (sM γ e)
        ≈ iwfihty l3 li3 l4 (sX' γ e') (sA' γ e') (sN' γ e') (sO' γ e') (sC' γ e') (sM' γ e') @ lmax lzero l' ] /\
  [ G0 ; Δ0 ,, sA γ e @ l ,, iwfcsty l li (sX γ e) (sA γ e) (sN γ e) (sO γ e) (sC γ e) @ lmax l li
      ,, iwfihty l li l' (sX γ e) (sA γ e) (sN γ e) (sO γ e) (sC γ e) (sM γ e) @ lmax lzero l'
      ⊢ sc γ e ≈ sc' γ e' : iwfstepty l li (sX γ e) (sA γ e) (sN γ e) (sO γ e) (sC γ e) (sM γ e) @ l' ].
Proof using EL Hwl Hwl' Hwli VA VC VL VM VN VNt VO VX Vc Vcs Vih Vmot.
  intros Hγ He. destruct (SubRel_nf _ _ _ _ _ He) as [Ne Ne'].
  destruct (elimIWf_loc Hγ) as (VXγ & VAγ & VNγ & VOγ & VCγ & Vmotγ & VMγ & Vcsγ & Vihγ & Vcγ).
  pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwl) as Hwl0. pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwli) as Hwli0.
  pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwl') as Hwl'0.
  assert (HwL : lwf (gL G0) (lmax l li)) by (split; assumption).
  assert (HwI : lwf (gL G0) (lmax lzero l')) by (split; [exact I | exact Hwl'0]).
  destruct (VTyG_loc VXγ _ _ _ He) as [RX HRX]. destruct (escape_ty _ _ _ _ _ _ _ _ HRX) as (HX0 & _ & EX).
  destruct (VTyG_loc VAγ _ _ _ He) as [RA HRA]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HA0 & _ & EA).
  pose proof (SubRel_lift He (VTy_refl_l (VTyG_loc VAγ)) HA0 Hwl0) as H1.
  pose proof (VTmG_loc VNγ _ _ _ H1) as XN. rewrite !subst_tyNat in XN.
  destruct (LRtm_escape XN) as [HN0 _]. pose proof (LRtm_geq XN) as EN.
  pose proof (VTmG_loc VOγ _ _ _ H1) as XO. rewrite !shift_llift_ty in XO.
  destruct (LRtm_escape XO) as [HO0 _]. pose proof (LRtm_geq XO) as EO.
  assert (HF0 : [ G0 ; Δ0 ,, sA γ e @ l ⊢g (tyFin N⟦γ⟧)[llift e] @ lzero ])
    by (rewrite subst_tyFin; apply wft_fin; [exact ge_notV | exact HN0]).
  pose proof (SubRel_lift H1 (V_fin (VTmG_loc (VTmG_refl_l VNγ))) HF0 I) as H1F.
  pose proof (VTmG_loc VCγ _ _ _ H1F) as XC. rewrite subst_tyFin, !shift_llift_ty in XC.
  destruct (LRtm_escape XC) as [HC0 _]. pose proof (LRtm_geq XC) as EC.
  (* the motive *)
  pose proof (SubRel_lift He (VTy_refl_l (VTyG_loc VXγ)) HX0 Hwli0) as H1X.
  destruct (Vmotγ _ _ _ H1X) as [RMo HRMo]. destruct (escape_ty _ _ _ _ _ _ _ _ HRMo) as (HMot0 & _ & _).
  pose proof (SubRel_lift H1X Vmotγ HMot0 HwL) as H2X.
  destruct (VMγ _ _ _ H2X) as [RM HRM]. destruct (escape_ty _ _ _ _ _ _ _ _ HRM) as (HM0 & _ & EM).
  rewrite iwfmotty_llift in HMot0, HM0, EM by exact Ne.
  (* the step's telescope *)
  destruct (Vcsγ _ _ _ H1) as [RC HRC]. destruct (escape_ty _ _ _ _ _ _ _ _ HRC) as (Hcs0 & _ & _).
  pose proof (SubRel_lift H1 Vcsγ Hcs0 HwL) as H2.
  destruct (Vihγ _ _ _ H2) as [RI HRI]. destruct (escape_ty _ _ _ _ _ _ _ _ HRI) as (HI0 & _ & EI).
  pose proof (SubRel_lift H2 (VTy_refl_l Vihγ) HI0 HwI) as H3.
  pose proof (LRtm_geq (Vcγ _ _ _ H3)) as Ec.
  rewrite iwfcsty_llift in Hcs0, HI0, EI, Ec by exact Ne.
  rewrite !iwfihty_llift2 in HI0, EI, Ec by assumption.
  rewrite iwfstepty_llift3 in Ec by exact Ne.
  rewrite (iwfihty_llift2 e' Ne') in EI.
  repeat split; assumption.
Qed.

Lemma elimIWf_nf {G0 γ Δ0 e e'} : gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' ->
  nfty (sX γ e) /\ nfty (sA γ e) /\ nftm (sN γ e) /\ nftm (sO γ e) /\ nftm (sC γ e) /\ nfty (sM γ e) /\
  nftm (sc γ e).
Proof.
  intros Hγ He.
  destruct (elimIWf_at Hγ He) as (HX0 & _ & HA0 & _ & HN0 & _ & HO0 & _ & HC0 & _ & _ & HM0 & _ & _ & _ & _ & Ec).
  repeat split; first [exact (wf_ty_nf HX0) | exact (wf_ty_nf HA0) | exact (wf_tm_nf HN0) | exact (wf_tm_nf HO0)
                      | exact (wf_tm_nf HC0) | exact (wf_ty_nf HM0)
                      | exact (wf_tm_nf (eqtm_wf_l ge_typeof (geq_tm_sound Ec)))].
Qed.

(** [elim_IWf]'s congruence and typed reductions in the scrutinee. *)
Section Cong.
Context {G0 γ Δ0 e e'} (Hγ : gwk_ok γ G0 G) (He : SubRel G0 Γ⟦γ⟧ Δ0 e e').

Lemma elimIWf_cong {m m' t t'} :
  [ G0 ; Δ0 ⊢g m ≅ m' : sX γ e @ li ] -> [ G0 ; Δ0 ⊢g t ≅ t' : tyL γ e m @ lmax l li ] ->
  [ G0 ; Δ0 ⊢g elL γ e m t ≅ elR γ e' m' t' : (sM γ e)[lsingle2 m t] @ l' ].
Proof.
  intros Hm Ht.
  destruct (elimIWf_at Hγ He)
    as (HX0 & EX & HA0 & EA & HN0 & EN & HO0 & EO & HC0 & EC & HMot0 & HM0 & EM & Hcs0 & HI0 & EI & Ec).
  apply eqtm_elimIWf; first [exact ge_compt | apply (lequiv_weaken _ _ _ _ (proj1 Hγ)); assumption
                            | apply geq_ty_sound; assumption | apply geq_tm_sound; assumption | assumption].
Qed.

Lemma elimIWf_cong_l {m m' t t'} :
  [ G0 ; Δ0 ⊢g m ≅ m' : sX γ e @ li ] -> [ G0 ; Δ0 ⊢g t ≅ t' : tyL γ e m @ lmax l li ] ->
  [ G0 ; Δ0 ⊢g elL γ e m t ≅ elL γ e m' t' : (sM γ e)[lsingle2 m t] @ l' ].
Proof.
  intros Hm Ht.
  destruct (elimIWf_at Hγ He)
    as (HX0 & EX & HA0 & EA & HN0 & EN & HO0 & EO & HC0 & EC & HMot0 & HM0 & EM & Hcs0 & HI0 & EI & Ec).
  pose proof (eqtm_wf_l ge_typeof (geq_tm_sound Ec)) as Hc0.
  apply eqtm_elimIWf; first [exact ge_compt | apply lequiv_refl, (lwf_weaken _ _ _ (proj1 Hγ)); assumption
                            | apply eqty_refl; assumption | apply eqtm_refl; assumption | assumption].
Qed.

Lemma elimIWf_red_l {m t w} : [ G0 ; Δ0 ⊢g m : sX γ e @ li ] ->
  [ G0 ; Δ0 ⊢g t ⤳* w : tyL γ e m @ lmax l li ] ->
  [ G0 ; Δ0 ⊢g elL γ e m t ⤳* elL γ e m w : (sM γ e)[lsingle2 m t] @ l' ].
Proof.
  intros Hm Hr. pose proof (elimIWf_cong_l (eqtm_refl _ _ _ _ _ _ Hm) (tmred_eq _ _ _ _ _ _ _ Hr)) as Y.
  split; [exact (eqtm_wf_l ge_typeof Y) | apply reds_elimIWf, (tmred_red _ _ _ _ _ _ _ Hr) | exact Y].
Qed.

Lemma elimIWf_red_r {m m' t t' w'} :
  [ G0 ; Δ0 ⊢g m ≅ m' : sX γ e @ li ] -> [ G0 ; Δ0 ⊢g t ≅ t' : tyL γ e m @ lmax l li ] ->
  [ G0 ; Δ0 ⊢g t' ⤳* w' : tyL γ e m @ lmax l li ] ->
  [ G0 ; Δ0 ⊢g elR γ e' m' t' ⤳* elR γ e' m' w' : (sM γ e)[lsingle2 m t] @ l' ].
Proof.
  intros Hm Htt Hr. pose proof (elimIWf_cong Hm Htt) as Y1.
  pose proof (elimIWf_cong Hm (eqtm_trans _ _ _ _ _ _ _ _ Htt (tmred_eq _ _ _ _ _ _ _ Hr))) as Y2.
  split; [exact (eqtm_wf_r ge_typeof Y1) | apply reds_elimIWf, (tmred_red _ _ _ _ _ _ _ Hr) |].
  eapply eqtm_trans; [apply eqtm_sym, Y1 | exact Y2].
Qed.

End Cong.

(** The relation at [IWf] at an index, its index and shape relations
    canonical. *)
Lemma elimIWf_WLR {G0 γ Δ0 e e' x x'} : gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' ->
  LRtm li G0 Δ0 (sX γ e) (sX γ e') x x' ->
  exists ix dm : DomRel G0 Δ0,
    LogRel (lmax l li) G0 Δ0 (tyL γ e x) (tyIWf l li (sX γ e') (sA γ e') (sN γ e') (sO γ e') (sC γ e') x')
      (lmax l li) (IWfRel G0 Δ0 l li (sX γ e) (sA γ e) (sN γ e) (sO γ e) (sC γ e) ix dm x) /\
    KDom G0 Δ0 (lmeasure (lmax l li)) li (sX γ e) ix /\ KDom G0 Δ0 (lmeasure (lmax l li)) l (sA γ e) dm.
Proof.
  intros Hγ He Hx. destruct (elimIWf_loc Hγ) as (VXγ & VAγ & VNγ & VOγ & VCγ & _).
  pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwl) as Hwl0. pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwli) as Hwli0.
  eexists _, _. split; [|split].
  - exact (LR_IWf_at Hwl0 Hwli0 (lequiv_refl _ _ Hwl0) (lequiv_refl _ _ Hwli0) (VTyG_refl_l VXγ) (VTyG_refl_l VAγ)
             (VTmG_refl_l VNγ) (VTmG_refl_l VOγ) (VTmG_refl_l VCγ) _ _ _ _ _ He Hx).
  - intros ρ. eexists. exact (iwfIdx_canon (l := l) (li := li) (VTyG_refl_l VXγ) He ρ).
  - intros ρ. eexists. exact (iwfDom_canon (l := l) (li := li) (VTyG_refl_l VAγ) He ρ).
Qed.

Lemma elimIWf_mot {G0 γ Δ0 e e' x x' s s'} : gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' ->
  LRtm li G0 Δ0 (sX γ e) (sX γ e') x x' ->
  LRtm (lmax l li) G0 Δ0 (tyL γ e x) (tyIWf l li (sX γ e') (sA γ e') (sN γ e') (sO γ e') (sC γ e') x') s s' ->
  LRty l' G0 Δ0 (sM γ e)[lsingle2 x s] (sM γ e')[lsingle2 x' s'].
Proof.
  intros Hγ He Hx Hs. destruct (SubRel_nf _ _ _ _ _ He) as [Ne Ne'].
  destruct (elimIWf_loc Hγ) as (_ & _ & _ & _ & _ & _ & VMγ & _).
  destruct (elimIWf_nf Hγ He) as (NX & NA & NN & NO & NC & _).
  destruct (elimIWf_nf Hγ (SubRel_refl_r He)) as (NX' & NA' & NN' & NO' & NC' & _).
  rewrite <- (iwfmotty_cons l li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧ e x Ne NX NA NN NO NC),
    <- (iwfmotty_cons l li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧ e' x' Ne' NX' NA' NN' NO' NC') in Hs.
  pose proof (VTy_refl_l VMγ _ _ _ (SubRel_cons (SubRel_cons He Hx) Hs)) as Y.
  now rewrite <- (lift_single2_ty e Ne), <- (lift_single2_ty e' Ne') in Y.
Qed.

(** [IWfRel] at canonical relations is the relation at [IWf]. *)
Lemma elimIWf_rel {G0 γ Δ0 e e'} {ix dm : DomRel G0 Δ0} {x s s'} : gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' ->
  LRtm li G0 Δ0 (sX γ e) (sX γ e) x x ->
  KDom G0 Δ0 (lmeasure (lmax l li)) li (sX γ e) ix -> KDom G0 Δ0 (lmeasure (lmax l li)) l (sA γ e) dm ->
  IWfRel G0 Δ0 l li (sX γ e) (sA γ e) (sN γ e) (sO γ e) (sC γ e) ix dm x s s' ->
  LRtm (lmax l li) G0 Δ0 (tyL γ e x) (tyL γ e x) s s'.
Proof.
  intros Hγ He Hx HX HA Hs. destruct (elimIWf_WLR Hγ (SubRel_refl_l He) Hx) as (ix0 & dm0 & HW & HX0 & HA0).
  eapply LRtm_of; [exact HW|].
  eapply (proj1 IWfRel_dir_all); [exact Hs | exact (KDom_releq HX HX0) | exact (KDom_releq HA HA0)].
Qed.

(** The elimination at related terms, from the elimination at their whnfs. *)
Lemma elimIWf_back {G0 γ Δ0 e e'} {ix dm : DomRel G0 Δ0} {x x' s s' w w'} :
  gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' -> LRtm li G0 Δ0 (sX γ e) (sX γ e) x x' ->
  KDom G0 Δ0 (lmeasure (lmax l li)) li (sX γ e) ix -> KDom G0 Δ0 (lmeasure (lmax l li)) l (sA γ e) dm ->
  IWfRel G0 Δ0 l li (sX γ e) (sA γ e) (sN γ e) (sO γ e) (sC γ e) ix dm x s s' ->
  [ G0 ; Δ0 ⊢g s ⤳* w : tyL γ e x @ lmax l li ] -> [ G0 ; Δ0 ⊢g s' ⤳* w' : tyL γ e x @ lmax l li ] ->
  whnf w -> whnf w' ->
  LRtm l' G0 Δ0 (sM γ e)[lsingle2 x w] (sM γ e)[lsingle2 x w] (elL γ e x w) (elR γ e' x' w') ->
  LRtm l' G0 Δ0 (sM γ e)[lsingle2 x s] (sM γ e)[lsingle2 x s] (elL γ e x s) (elR γ e' x' s').
Proof.
  intros Hγ He Hxx HX HA Hss Hs Hs' Nw Nw' Y.
  pose proof (LRtm_trans Hxx (LRtm_sym Hxx)) as Hx.
  destruct (IWfRel_inv Hss) as (w0 & w0' & Hw0 & Hw0' & Ew & Nn).
  assert (w0 = w) as -> by (eapply tmred_whnf_det; [exact Hw0 | exact Hs | exact (IWfNf_whnf_l Nn) | exact Nw]).
  assert (w0' = w') as -> by (eapply tmred_whnf_det; [exact Hw0' | exact Hs' | exact (IWfNf_whnf_r Nn) | exact Nw']).
  pose proof (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hs)) as Hwt.
  pose proof (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hs')) as Hw't.
  assert (Rsw' : IWfRel G0 Δ0 l li (sX γ e) (sA γ e) (sN γ e) (sO γ e) (sC γ e) ix dm x s w')
    by (eapply iwfrel; [exact Hs | exact (tmred_refl _ _ _ Hw't) | exact Ew | exact Nn]).
  assert (Rww' : IWfRel G0 Δ0 l li (sX γ e) (sA γ e) (sN γ e) (sO γ e) (sC γ e) ix dm x w w')
    by (eapply iwfrel; [exact (tmred_refl _ _ _ Hwt) | exact (tmred_refl _ _ _ Hw't) | exact Ew | exact Nn]).
  pose proof (elimIWf_rel Hγ He Hx HX HA Rsw') as Xsw'. pose proof (elimIWf_rel Hγ He Hx HX HA Rww') as Xww'.
  pose proof (LRtm_trans Xsw' (LRtm_sym Xww')) as Xsw. pose proof (LRtm_trans Xsw (LRtm_sym Xsw)) as Xss.
  pose proof (elimIWf_mot Hγ (SubRel_refl_l He) Hx Xsw) as XT.
  pose proof (elimIWf_mot Hγ (SubRel_refl_l He) Hx Xss) as XTT.
  pose proof (LRtm_irrel_r (LRtm_conv_l Y XT) XTT) as Y2.
  pose proof (geq_tm_sound (LRtm_geq (elimIWf_rel Hγ He Hx HX HA Hss))) as Hss'.
  destruct (LRtm_escape Hxx) as [Hxt _]. pose proof (geq_tm_sound (LRtm_geq Hxx)) as Exx.
  exact (LRtm_red Y2 (elimIWf_red_l Hγ He Hxt Hs) (elimIWf_red_r Hγ He Exx Hss' Hs')).
Qed.

(** At a term reducing to a neutral, the elimination is neutral. *)
Lemma elimIWf_ne {G0 γ Δ0 e e'} {ix dm : DomRel G0 Δ0} {x x' s s' ν} :
  gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' -> LRtm li G0 Δ0 (sX γ e) (sX γ e) x x' ->
  KDom G0 Δ0 (lmeasure (lmax l li)) li (sX γ e) ix -> KDom G0 Δ0 (lmeasure (lmax l li)) l (sA γ e) dm ->
  IWfRel G0 Δ0 l li (sX γ e) (sA γ e) (sN γ e) (sO γ e) (sC γ e) ix dm x s s' -> reds s ν -> whne ν ->
  LRtm l' G0 Δ0 (sM γ e)[lsingle2 x s] (sM γ e)[lsingle2 x s] (elL γ e x s) (elR γ e' x' s').
Proof.
  intros Hγ He Hxx HX HA Hss Hsν Nν.
  pose proof (LRtm_trans Hxx (LRtm_sym Hxx)) as Hx.
  destruct (IWfRel_inv Hss) as (w & w' & Hw & Hw' & Ew & Nn).
  assert (w = ν) as ->.
  { eapply reds_whnf_det; [exact (tmred_red _ _ _ _ _ _ _ Hw) | exact Hsν | exact (IWfNf_whnf_l Nn)
                          | now apply whnf_ne]. }
  pose proof (IWfNf_ne_inv Nν Nn) as Hne.
  destruct (elimIWf_at Hγ He)
    as (HX0 & EX & HA0 & EA & HN0 & EN & HO0 & EO & HC0 & EC & HMot0 & HM0 & EM & Hcs0 & HI0 & EI & Ec).
  pose proof (gne_tm_elimIWf (lequiv_weaken _ _ _ _ (proj1 Hγ) H13) (lequiv_weaken _ _ _ _ (proj1 Hγ) Hi3)
                (lequiv_weaken _ _ _ _ (proj1 Hγ) H24) HX0 EX HA0 EA HN0 EN HO0 EO HC0 EC HM0 EM EI Ec
                (LRtm_geq Hxx) Hne) as HE.
  pose proof (gne_tm_refl_l Hne) as Hνν.
  pose proof (eqtm_wf_l ge_typeof (geq_tm_sound (gne_tm_geq Hνν))) as Hνt.
  assert (Rνν : IWfRel G0 Δ0 l li (sX γ e) (sA γ e) (sN γ e) (sO γ e) (sC γ e) ix dm x ν ν).
  { eapply iwfrel; [exact (tmred_refl _ _ _ Hνt) | exact (tmred_refl _ _ _ Hνt) | exact (gne_tm_geq Hνν) |].
    apply iwfnf_ne, Hνν. }
  destruct (elimIWf_mot Hγ (SubRel_refl_l He) Hx (elimIWf_rel Hγ He Hx HX HA Rνν)) as [RL HRL].
  eapply elimIWf_back; [exact Hγ | exact He | exact Hxx | exact HX | exact HA | exact Hss | exact Hw | exact Hw'
                       | now apply whnf_ne | exact (IWfNf_whnf_r Nn) |].
  exact (LRtm_of HRL (LR_neutral _ _ _ _ _ _ _ HRL _ _ HE HE)).
Qed.

(** The signature at a related substitution, with its generic reflexivity. *)
Lemma elimIWf_sig {G0 γ Δ0 e e'} : gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' ->
  IWfEq (G := G0) (i := ge_layer) Δ0 l li l li (sX γ e) (sX γ e) (sA γ e) (sA γ e) (sN γ e) (sN γ e)
    (sO γ e) (sO γ e) (sC γ e) (sC γ e) /\
  IWfGeq G0 Δ0 l li (sX γ e) (sX γ e) (sA γ e) (sA γ e) (sN γ e) (sN γ e) (sO γ e) (sO γ e) (sC γ e) (sC γ e).
Proof.
  intros Hγ He.
  destruct (elimIWf_at Hγ He) as (HX0 & EX & HA0 & EA & HN0 & EN & HO0 & EO & HC0 & EC & _).
  pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwl) as Hwl0. pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwli) as Hwli0.
  split.
  - apply IWfEq_intro; first [apply lequiv_refl; assumption | apply eqty_refl; assumption
                             | apply eqtm_refl; assumption | assumption].
  - refine (conj (geq_ty_trans EX (geq_ty_sym EX)) (conj (geq_ty_trans EA (geq_ty_sym EA))
              (conj (geq_tm_trans EN (geq_tm_sym EN)) (conj (geq_tm_trans EO (geq_tm_sym EO))
                 (geq_tm_trans EC (geq_tm_sym EC)))))).
Qed.

Local Ltac gwkn H := first [ exact H | eapply (wk1_ty _ _ ge_typeof); [eassumption | gwkn H]
                           | eapply (wk1_tm _ _ ge_typeof); [eassumption | gwkn H] ].
Local Ltac gvar := eapply wf_tm_retype; [eapply wf_var; [rewrite ge_typeof; eassumption | repeat constructor]
                                        | cbn; try reflexivity].
Local Ltac vvar := eapply VG_var; [repeat constructor | cbn; try reflexivity].

(** M17_DESIGN.md's index lemma at the [ih] entry's [dnth]. *)
Lemma elimIWf_Vdnth :
  VTmG G (Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ,, tyFin N⟨↑⟩ @ lzero)
    (tmDNth (lmax l li) N⟨↑⟩⟨↑⟩ (iwfFc l li X A N Ot C) (var 1) (var 0))
    (tmDNth (lmax l3 li3) N'⟨↑⟩⟨↑⟩ (iwfFc l3 li3 X' A' N' Ot' C') (var 1) (var 0))
    (iwfFc l li X A N Ot C)[lsingle (var 0)] (lmax l li).
Proof.
  pose proof HS as (_ & _ & HX & HA & HN & HO & HC).
  assert (HwL : lwf (gL G) (lmax l li)) by (split; assumption).
  assert (HLL : lequiv (gL G) (lmax l li) (lmax l3 li3)) by (apply lequiv_max; assumption).
  pose proof (IWf_cs_wf ge_typeof ge_notV HS) as HCs.
  pose proof (ext_wf_g HA Hwl) as H1. pose proof (ext_wf_g HCs HwL) as H2.
  assert (HN1 : [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ⊢g N⟨↑⟩ : tyNat @ lzero ])
    by (eapply wf_tm_retype; [gwkn HN | reflexivity]).
  assert (HF1 : [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ⊢g tyFin N⟨↑⟩ @ lzero ])
    by (apply wft_fin; [exact ge_notV | exact HN1]).
  assert (Hw0 : lwf (gL G) lzero) by exact I. pose proof (ext_wf_g HF1 Hw0) as H3.
  assert (HN2 : [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ,, tyFin N⟨↑⟩ @ lzero
                  ⊢g N⟨↑⟩⟨↑⟩ : tyNat @ lzero ])
    by (eapply wf_tm_retype; [gwkn HN1 | reflexivity]).
  pose proof (IWfSig_wk1 ge_typeof ge_notV (IWfSig_wk1 ge_typeof ge_notV (IWfSig_wk1 ge_typeof ge_notV HS H1) H2) H3)
    as HS3.
  assert (Hv2 : [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ,, tyFin N⟨↑⟩ @ lzero
                  ⊢g var 2 : A⟨↑⟩⟨↑⟩⟨↑⟩ @ l ]) by gvar.
  pose proof (IWf_fam_wf ge_typeof ge_notV HS3 Hv2) as HFam. rewrite n3_single, <- iwfFc_fam in HFam.
  assert (VF : VTyG G (Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ,, tyFin N⟨↑⟩ @ lzero
                       ,, tyFin N⟨↑⟩⟨↑⟩ @ lzero)
                 (iwfFc l li X A N Ot C) (iwfFc l3 li3 X' A' N' Ot' C') (lmax l li)).
  { apply VG_iwf; [exact Hwl | exact Hwli | exact (lequiv_sym _ _ _ H13) | exact (lequiv_sym _ _ _ Hi3)
                  | exact (VG_shift (VG_shift (VG_shift (VG_shift VX))))
                  | exact (VG_shift (VG_shift (VG_shift (VG_shift VA)))) | | | |].
    - eapply VTmG_retype; [exact (VG_lift1_tm (VG_lift1_tm (VG_lift1_tm (VG_lift1_tm VNt)))) | reflexivity].
    - eapply VTmG_retype; [exact (VG_lift1_tm (VG_lift1_tm (VG_lift1_tm (VG_lift1_tm VO)))) |].
      now rewrite !IWf_E_ren.
    - eapply VTmG_retype; [exact (VG_lift2_tm (VG_lift2_tm (VG_lift2_tm (VG_lift2_tm VC)))) |].
      now rewrite !IWf_E_ren2.
    - eapply VTmG_retype; [exact (VG_lift1_tm (VG_lift1_tm VC)) |]. now rewrite !IWf_E_ren. }
  apply (V_dnth HwL HLL HN2 (VTmG_retype (VG_shift_tm (VG_shift_tm VNt)) eq_refl) HFam VF).
  - vvar. push_ren. f_equal. f_equal; ren_comm.
  - vvar.
Qed.

(** The [dnth] in the induction hypothesis's body at a Kripke weakening of
    the shape and children's substitution, at related indices. *)
Lemma elimIWf_dnth_kw {G0 γ Δ0 e e' a a' cs cs'} (ρ : kwk G0 Δ0) {y y'} :
  gwk_ok γ G0 G ->
  SubRel G0 (Γ⟦γ⟧ ,, A⟦γ⟧ @ l ,, iwfcsty l li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧ @ lmax l li) Δ0
    (lcons (lcons e a) cs) (lcons (lcons e' a') cs') ->
  LRtm lzero (kw_G ρ) (kw_Δ ρ) (tyFin (ktml ρ (sN γ e))[lsingle (ktm ρ a)])
    (tyFin (ktml ρ (sN γ e'))[lsingle (ktm ρ a')]) y y' ->
  LRtm (lmax l li) (kw_G ρ) (kw_Δ ρ)
    (tyIWf l li (kty ρ (sX γ e)) (kty ρ (sA γ e)) (ktml ρ (sN γ e)) (ktml ρ (sO γ e)) (ktmll ρ (sC γ e))
       (ktmll ρ (sC γ e))[lsingle2 (ktm ρ a) y])
    (tyIWf l li (kty ρ (sX γ e')) (kty ρ (sA γ e')) (ktml ρ (sN γ e')) (ktml ρ (sO γ e')) (ktmll ρ (sC γ e'))
       (ktmll ρ (sC γ e'))[lsingle2 (ktm ρ a') y'])
    (tmDNth (lmax l li) (ktml ρ (sN γ e))[lsingle (ktm ρ a)]
       (iwfFam l li (kty ρ (sX γ e)) (kty ρ (sA γ e)) (ktml ρ (sN γ e)) (ktml ρ (sO γ e)) (ktmll ρ (sC γ e))
          (ktm ρ a)) (ktm ρ cs) y)
    (tmDNth (lmax l3 li3) (ktml ρ (sN' γ e'))[lsingle (ktm ρ a')]
       (iwfFam l3 li3 (kty ρ (sX' γ e')) (kty ρ (sA' γ e')) (ktml ρ (sN' γ e')) (ktml ρ (sO' γ e'))
          (ktmll ρ (sC' γ e')) (ktm ρ a')) (ktm ρ cs') y').
Proof.
  intros Hγ HSc Hy.
  pose proof (SubRel_kw _ _ _ ρ _ _ HSc) as HSρ.
  rewrite !gwa_cext, gwa_iwfcsty, gwa_comp_ctx, !gwa_comp_ty, !gwa_comp_tm in HSρ.
  pose proof (elimIWf_Vdnth _ _ (gwk_ok_comp (kw_gok ρ) Hγ)) as Vn.
  rewrite !gwa_cext, gwa_iwfcsty in Vn.
  repeat first [rewrite gwa_tyFin in Vn | rewrite gwa_tmDNth in Vn | rewrite gwa_ren_ty in Vn | rewrite gwa_ren in Vn
               | rewrite gwa_tyIWf in Vn | rewrite gwa_var in Vn | rewrite gwa_subst_ty in Vn
               | rewrite gwa_lsingle in Vn].
  assert (Ne : LK nftm (kwsub ρ e)) by (intros n; rewrite llk_kwsub; apply ren_nf).
  assert (Ne' : LK nftm (kwsub ρ e')) by (intros n; rewrite llk_kwsub; apply ren_nf).
  assert (Xy : LRtm lzero (kw_G ρ) (kw_Δ ρ) (tyFin N⟦gwk_comp (kw_γ ρ) γ⟧⟨↑⟩)[kwsub ρ (lcons (lcons e a) cs)]
                 (tyFin N⟦gwk_comp (kw_γ ρ) γ⟧⟨↑⟩)[kwsub ρ (lcons (lcons e' a') cs')] y y').
  { rewrite (subst_ext_ty _ _ _ (kwsub_cons2 ρ e a cs)), (subst_ext_ty _ _ _ (kwsub_cons2 ρ e' a' cs')).
    rewrite !finv_subst, <- !kγ_tml by assumption. exact Hy. }
  pose proof (Vn _ _ _ (SubRel_cons HSρ Xy)) as X0.
  rewrite (subst_ext_ty _ _ _ (kwsub_cons3 ρ e a cs y)), (subst_ext_ty _ _ _ (kwsub_cons3 ρ e' a' cs' y')),
    (subst_ext _ _ _ (kwsub_cons3 ρ e a cs y)), (subst_ext _ _ _ (kwsub_cons3 ρ e' a' cs' y')) in X0.
  pose proof (wf_tm_nf (proj1 (LRtm_escape Hy))) as Ny. pose proof (wf_tm_nf (proj2 (LRtm_escape Hy))) as Ny'.
  assert (Na : nftm (ktm ρ a)) by apply ren_nf. assert (Na' : nftm (ktm ρ a')) by apply ren_nf.
  assert (Ncs : nftm (ktm ρ cs)) by apply ren_nf. assert (Ncs' : nftm (ktm ρ cs')) by apply ren_nf.
  rewrite !iwf_dnthv_subst in X0 by assumption.
  rewrite !iwfFc_single_subst in X0
    by first [assumption | rewrite <- kγ_ty; apply ren_nf_ty | rewrite <- kγ_tml; apply ren_nf
             | rewrite <- kγ_tmll; apply ren_nf].
  rewrite <- !kγ_ty, <- !kγ_tml, <- !kγ_tmll in X0.
  exact X0.
Qed.

(** ** The core: related eliminations at related trees *)

(** The eliminations at two indices and terms, after a global weakening
    and at a related substitution, related at the motive. *)
Definition elimIWf_goal G0 Δ0 γ e e' x x' s s' : Prop :=
  LRtm l' G0 Δ0 (sM γ e)[lsingle2 x s] (sM γ e)[lsingle2 x s] (elL γ e x s) (elR γ e' x' s').

(** The relation's indices are the premises' at a global weakening and a
    related substitution, and its index and shape relations are
    canonical. *)
Definition elimIWf_hyp G0 Δ0 k1 ki1 X0 A0 N0 O0 C0 (ix dm : DomRel G0 Δ0) γ e e' : Prop :=
  gwk_ok γ G0 G /\ SubRel G0 Γ⟦γ⟧ Δ0 e e' /\ k1 = l /\ ki1 = li /\ X0 = sX γ e /\ A0 = sA γ e /\
  N0 = sN γ e /\ O0 = sO γ e /\ C0 = sC γ e /\
  KDom G0 Δ0 (lmeasure (lmax l li)) li X0 ix /\ KDom G0 Δ0 (lmeasure (lmax l li)) l A0 dm.

(** The motive at a tree, whatever its index: any two terms related at
    [IWf] at any related indices and joinable with it have related
    eliminations. *)
Definition elimIWf_mrel G0 Δ0 k1 ki1 X0 A0 N0 O0 C0 (ix dm : DomRel G0 Δ0) (t t' : tm) : Prop :=
  forall γ e e', elimIWf_hyp G0 Δ0 k1 ki1 X0 A0 N0 O0 C0 ix dm γ e e' ->
  forall x x', LRtm li G0 Δ0 X0 X0 x x' ->
  forall s s', IWfRel G0 Δ0 l li X0 A0 N0 O0 C0 ix dm x s s' -> Join s t -> Join s' t' ->
  elimIWf_goal G0 Δ0 γ e e' x x' s s'.

(** The motive at a spine, at a family of child indices well formed and
    generically reflexive at related positions: at tuples joinable with
    it and related indices, any two terms related at [IWf] reducing to
    [dnth]'s states have related eliminations. *)
Definition elimIWf_mspine G0 Δ0 k1 ki1 X0 A0 N0 O0 C0 (ix dm : DomRel G0 Δ0) (cf k cs cs' : tm) : Prop :=
  forall γ e e', elimIWf_hyp G0 Δ0 k1 ki1 X0 A0 N0 O0 C0 ix dm γ e e' ->
  [ G0 ; Δ0 ,, tyFin k @ lzero ⊢g iwfFamT l li X0 A0 N0 O0 C0 cf @ lmax l li ] ->
  (forall (ρ : kwk G0 Δ0) p p', PosRel (kw_G ρ) (kw_Δ ρ) (ktm ρ k) (ktm ρ k) p p' ->
     [ kw_G ρ ; kw_Δ ρ ⊢ (ktml ρ cf)[lsingle p] ≈ (ktml ρ cf)[lsingle p'] : kty ρ X0 @ li ]) ->
  forall c0 c0', nftm c0 -> nftm c0' -> TC c0 cs -> TC c0' cs' ->
  forall k' i i', NatRel G0 Δ0 k k' -> LRtm lzero G0 Δ0 (tyFin k) (tyFin k') i i' ->
  forall e1 e1' u u', nftm e1 -> nftm e1' -> DNat k e1 c0 i u -> DNat k' e1' c0' i' u' ->
  forall x x' s s', LRtm li G0 Δ0 X0 X0 x x' -> IWfRel G0 Δ0 l li X0 A0 N0 O0 C0 ix dm x s s' ->
  reds s u -> reds s' u' -> elimIWf_goal G0 Δ0 γ e e' x x' s s'.

Lemma elimIWf_c_rel {G0 Δ0 k1 ki1 X0 A0 N0 O0 C0} {ix dm : DomRel G0 Δ0} {m t t' w w'} :
  [ G0 ; Δ0 ⊢g t ⤳* w : tyIWf k1 ki1 X0 A0 N0 O0 C0 m @ lmax k1 ki1 ] ->
  [ G0 ; Δ0 ⊢g t' ⤳* w' : tyIWf k1 ki1 X0 A0 N0 O0 C0 m @ lmax k1 ki1 ] ->
  IWfNf G0 Δ0 k1 ki1 X0 A0 N0 O0 C0 ix dm m w w' ->
  elimIWf_mrel G0 Δ0 k1 ki1 X0 A0 N0 O0 C0 ix dm w w' -> elimIWf_mrel G0 Δ0 k1 ki1 X0 A0 N0 O0 C0 ix dm t t'.
Proof.
  intros Hw Hw' Nn IH γ e e' Hh x x' Hx s s' Hss Js Js'. apply (IH γ e e' Hh x x' Hx s s' Hss).
  - exact (join_red _ _ _ Js (tmred_red _ _ _ _ _ _ _ Hw) (IWfNf_whnf_l Nn)).
  - exact (join_red _ _ _ Js' (tmred_red _ _ _ _ _ _ _ Hw') (IWfNf_whnf_r Nn)).
Qed.

Lemma elimIWf_c_ne {G0 Δ0 k1 ki1 X0 A0 N0 O0 C0} {ix dm : DomRel G0 Δ0} {m ν ν'} :
  [ G0 ; Δ0 ⊢ ν ~ ν' : tyIWf k1 ki1 X0 A0 N0 O0 C0 m @ lmax k1 ki1 ] ->
  elimIWf_mrel G0 Δ0 k1 ki1 X0 A0 N0 O0 C0 ix dm ν ν'.
Proof.
  intros Hν γ e e' (Hγ & He & E1 & E2 & E3 & E4 & E5 & E6 & E7 & HX & HA) x x' Hx s s' Hss Js _.
  subst k1 ki1 X0 A0 N0 O0 C0.
  destruct (join_ne _ _ Js (gne_tm_whne_l Hν)) as (X1 & HX1 & NX1).
  exact (elimIWf_ne Hγ He Hx HX HA Hss HX1 NX1).
Qed.

Lemma elimIWf_c_zero {G0 Δ0 k1 ki1 X0 A0 N0 O0 C0} {ix dm : DomRel G0 Δ0} {cf k cs cs'} :
  [ G0 ; Δ0 ⊢g k ⤳* zero : tyNat @ lzero ] -> elimIWf_mspine G0 Δ0 k1 ki1 X0 A0 N0 O0 C0 ix dm cf k cs cs'.
Proof.
  intros Hk γ e e' (Hγ & He & E1 & E2 & E3 & E4 & E5 & E6 & E7 & HX & HA) _ _ c0 c0' _ _ _ _ k' i i' _ Hi
    e1 e1' u u' _ _ Du _ x x' s s' Hx Hss Hs _.
  subst k1 ki1 X0 A0 N0 O0 C0.
  destruct (fin_idx_zero Hi Hk) as (ν & Hiν & Nν).
  destruct (dn_zero (tmred_red _ _ _ _ _ _ _ Hk) Hiν Nν Du) as (X1 & HX1 & NX1).
  exact (elimIWf_ne Hγ He Hx HX HA Hss (reds_trans _ _ _ Hs HX1) NX1).
Qed.

Lemma elimIWf_c_vne {G0 Δ0 k1 ki1 X0 A0 N0 O0 C0} {ix dm : DomRel G0 Δ0} {cf k ν cs cs'} :
  [ G0 ; Δ0 ⊢g k ⤳* ν : tyNat @ lzero ] -> [ G0 ; Δ0 ⊢ ν ~ ν : tyNat @ lzero ] ->
  elimIWf_mspine G0 Δ0 k1 ki1 X0 A0 N0 O0 C0 ix dm cf k cs cs'.
Proof.
  intros Hk Hν γ e e' (Hγ & He & E1 & E2 & E3 & E4 & E5 & E6 & E7 & HX & HA) _ _ c0 c0' _ _ _ _ k' i i' _ _
    e1 e1' u u' _ _ Du _ x x' s s' Hx Hss Hs _.
  subst k1 ki1 X0 A0 N0 O0 C0.
  destruct (dn_ne (tmred_red _ _ _ _ _ _ _ Hk) (gne_tm_whne_l Hν) Du) as (X1 & HX1 & NX1).
  exact (elimIWf_ne Hγ He Hx HX HA Hss (reds_trans _ _ _ Hs HX1) NX1).
Qed.

Lemma elimIWf_c_succ {G0 Δ0 k1 ki1 X0 A0 N0 O0 C0} {ix dm : DomRel G0 Δ0} {cf k m cs cs' w w'} :
  [ G0 ; Δ0 ⊢g k ⤳* succ m : tyNat @ lzero ] ->
  [ G0 ; Δ0 ⊢g cs ⤳* w : tySig (lmax k1 ki1) (lmax k1 ki1) (dvecHd m (iwfFamT k1 ki1 X0 A0 N0 O0 C0 cf))
                          (dvecTl (lmax k1 ki1) m (iwfFamT k1 ki1 X0 A0 N0 O0 C0 cf))
                          @ lmax (lmax k1 ki1) (lmax k1 ki1) ] ->
  [ G0 ; Δ0 ⊢g cs' ⤳* w' : tySig (lmax k1 ki1) (lmax k1 ki1) (dvecHd m (iwfFamT k1 ki1 X0 A0 N0 O0 C0 cf))
                          (dvecTl (lmax k1 ki1) m (iwfFamT k1 ki1 X0 A0 N0 O0 C0 cf))
                          @ lmax (lmax k1 ki1) (lmax k1 ki1) ] ->
  whnf w -> whnf w' ->
  (forall la lb A2 B2 la' lb' A2' B2',
     lequiv (gL G0) la (lmax k1 ki1) -> lequiv (gL G0) lb (lmax k1 ki1) ->
     lequiv (gL G0) la' (lmax k1 ki1) -> lequiv (gL G0) lb' (lmax k1 ki1) ->
     [ G0 ; Δ0 ⊢ dvecHd m (iwfFamT k1 ki1 X0 A0 N0 O0 C0 cf) ≈ A2 @ lmax k1 ki1 ] ->
     [ G0 ; Δ0 ,, dvecHd m (iwfFamT k1 ki1 X0 A0 N0 O0 C0 cf) @ lmax k1 ki1
         ⊢ dvecTl (lmax k1 ki1) m (iwfFamT k1 ki1 X0 A0 N0 O0 C0 cf) ≈ B2 @ lmax k1 ki1 ] ->
     [ G0 ; Δ0 ⊢ dvecHd m (iwfFamT k1 ki1 X0 A0 N0 O0 C0 cf) ≈ A2' @ lmax k1 ki1 ] ->
     [ G0 ; Δ0 ,, dvecHd m (iwfFamT k1 ki1 X0 A0 N0 O0 C0 cf) @ lmax k1 ki1
         ⊢ dvecTl (lmax k1 ki1) m (iwfFamT k1 ki1 X0 A0 N0 O0 C0 cf) ≈ B2' @ lmax k1 ki1 ] ->
     IWfRel G0 Δ0 k1 ki1 X0 A0 N0 O0 C0 ix dm cf[lsingle (posHd m)]
       (tmFst la lb A2 B2 w) (tmFst la' lb' A2' B2' w')) ->
  (forall la lb A2 B2 la' lb' A2' B2',
     lequiv (gL G0) la (lmax k1 ki1) -> lequiv (gL G0) lb (lmax k1 ki1) ->
     lequiv (gL G0) la' (lmax k1 ki1) -> lequiv (gL G0) lb' (lmax k1 ki1) ->
     [ G0 ; Δ0 ⊢ dvecHd m (iwfFamT k1 ki1 X0 A0 N0 O0 C0 cf) ≈ A2 @ lmax k1 ki1 ] ->
     [ G0 ; Δ0 ,, dvecHd m (iwfFamT k1 ki1 X0 A0 N0 O0 C0 cf) @ lmax k1 ki1
         ⊢ dvecTl (lmax k1 ki1) m (iwfFamT k1 ki1 X0 A0 N0 O0 C0 cf) ≈ B2 @ lmax k1 ki1 ] ->
     [ G0 ; Δ0 ⊢ dvecHd m (iwfFamT k1 ki1 X0 A0 N0 O0 C0 cf) ≈ A2' @ lmax k1 ki1 ] ->
     [ G0 ; Δ0 ,, dvecHd m (iwfFamT k1 ki1 X0 A0 N0 O0 C0 cf) @ lmax k1 ki1
         ⊢ dvecTl (lmax k1 ki1) m (iwfFamT k1 ki1 X0 A0 N0 O0 C0 cf) ≈ B2' @ lmax k1 ki1 ] ->
     elimIWf_mrel G0 Δ0 k1 ki1 X0 A0 N0 O0 C0 ix dm (tmFst la lb A2 B2 w) (tmFst la' lb' A2' B2' w')) ->
  (forall la lb A2 B2 la' lb' A2' B2',
     lequiv (gL G0) la (lmax k1 ki1) -> lequiv (gL G0) lb (lmax k1 ki1) ->
     lequiv (gL G0) la' (lmax k1 ki1) -> lequiv (gL G0) lb' (lmax k1 ki1) ->
     [ G0 ; Δ0 ⊢ dvecHd m (iwfFamT k1 ki1 X0 A0 N0 O0 C0 cf) ≈ A2 @ lmax k1 ki1 ] ->
     [ G0 ; Δ0 ,, dvecHd m (iwfFamT k1 ki1 X0 A0 N0 O0 C0 cf) @ lmax k1 ki1
         ⊢ dvecTl (lmax k1 ki1) m (iwfFamT k1 ki1 X0 A0 N0 O0 C0 cf) ≈ B2 @ lmax k1 ki1 ] ->
     [ G0 ; Δ0 ⊢ dvecHd m (iwfFamT k1 ki1 X0 A0 N0 O0 C0 cf) ≈ A2' @ lmax k1 ki1 ] ->
     [ G0 ; Δ0 ,, dvecHd m (iwfFamT k1 ki1 X0 A0 N0 O0 C0 cf) @ lmax k1 ki1
         ⊢ dvecTl (lmax k1 ki1) m (iwfFamT k1 ki1 X0 A0 N0 O0 C0 cf) ≈ B2' @ lmax k1 ki1 ] ->
     elimIWf_mspine G0 Δ0 k1 ki1 X0 A0 N0 O0 C0 ix dm (posMv m cf) m
       (tmSnd la lb A2 B2 w) (tmSnd la' lb' A2' B2' w')) ->
  elimIWf_mspine G0 Δ0 k1 ki1 X0 A0 N0 O0 C0 ix dm cf k cs cs'.
Proof.
  intros Hk Hcs Hcs' Nw Nw' Hf IHf IHs γ e e' Hh HF HP c0 c0' Nc0 Nc0' Tc Tc' k' i i' Hkk Hi
    e1 e1' u u' Ne1 Ne1' Du Du' x x' s s' Hx Hss Hs Hs'.
  pose proof Hh as (Hγ & He & E1 & E2 & E3 & E4 & E5 & E6 & E7 & HX & HA). subst k1 ki1 X0 A0 N0 O0 C0.
  pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwl) as Hwl0. pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwli) as Hwli0.
  assert (HwL : lwf (gL G0) (lmax l li)) by (split; assumption).
  pose proof (lequiv_refl _ _ HwL) as HLL.
  destruct (NatRel_inv_succ Hkk Hk) as (m' & Hk' & Hmm).
  destruct (NatRel_escape Hmm) as (Hm & Hm' & _). pose proof (wf_tm_nf Hm) as Nm. pose proof (wf_tm_nf Hm') as Nm'.
  destruct (LRtm_escape Hi) as [Hit Hi't]. pose proof (wf_tm_nf Hit) as Ni. pose proof (wf_tm_nf Hi't) as Ni'.
  (* the canonical annotations *)
  destruct (elimIWf_sig Hγ He) as [HE HG].
  pose proof (fin_stab_ty' (tmred_eq _ _ _ _ _ _ _ Hk) HF) as HF1.
  destruct (iwf_succ_geq HE HG Hk Hk (NatRel_refl_l _ _ _ _ Hmm) (eqty_refl _ _ _ _ _ HF) HP) as [Ghd Gtl].
  pose proof (tyred_dvec_succ HwL HF1 Hm) as HDs.
  destruct (inv_ty_sig (eqty_wf_r ge_typeof (tyred_eq _ _ _ _ _ _ HDs))) as ((_ & _ & _ & Hhd & _) & _).
  pose proof (Gtl _ _ (ext_wf_g Hhd HwL)) as Gtl'.
  (* the tuples are pairs or neutral: their heads reach whnfs *)
  pose proof (Hf _ _ _ _ _ _ _ _ HLL HLL HLL HLL Ghd Gtl' Ghd Gtl') as Rhd.
  destruct (IWfRel_inv Rhd) as (v & v' & Hv & Hv' & _ & Nv).
  assert (Pw : PairOrNe w) by exact (fst_cases _ _ _ _ _ _ Nw (tmred_red _ _ _ _ _ _ _ Hv) (IWfNf_whnf_l Nv)).
  assert (Pw' : PairOrNe w') by exact (fst_cases _ _ _ _ _ _ Nw' (tmred_red _ _ _ _ _ _ _ Hv') (IWfNf_whnf_r Nv)).
  destruct (fin_idx_succ Hi Hk Hmm)
    as [(k2 & k3 & C1 & D1 & u0 & k2' & k3' & C1' & D1' & u0' & Hi1 & Hi1')
       |[(k2 & k3 & C1 & D1 & j & k2' & k3' & C1' & D1' & j' & Hi1 & Hi1' & Hjj) | (ν & Hiν & Nν)]].
  - (* [inl]: the heads *)
    destruct (dn_inl Nm Ne1 Nc0 Ni (tmred_red _ _ _ _ _ _ _ Hk) Hi1 Du) as (L1 & A1 & B1 & Hu).
    destruct (dn_inl Nm' Ne1' Nc0' Ni' (tmred_red _ _ _ _ _ _ _ Hk') Hi1' Du') as (L1' & A1' & B1' & Hu').
    apply (IHf _ _ _ _ _ _ _ _ HLL HLL HLL HLL Ghd Gtl' Ghd Gtl' γ e e' Hh x x' Hx s s' Hss).
    + eapply join_reds_l; [exact (reds_trans _ _ _ Hs Hu)|].
      exact (join_fst _ _ _ _ _ _ _ _ _ _ _ Tc (tmred_red _ _ _ _ _ _ _ Hcs) Nw Pw).
    + eapply join_reds_l; [exact (reds_trans _ _ _ Hs' Hu')|].
      exact (join_fst _ _ _ _ _ _ _ _ _ _ _ Tc' (tmred_red _ _ _ _ _ _ _ Hcs') Nw' Pw').
  - (* [inr]: [dnth] at the tails, along the moved family *)
    pose proof (wf_tm_nf (proj1 (LRtm_escape Hjj))) as Nj. pose proof (wf_tm_nf (proj2 (LRtm_escape Hjj))) as Nj'.
    destruct (dn_inr Nm Ne1 Nc0 Ni Nj (tmred_red _ _ _ _ _ _ _ Hk) Hi1 Du)
      as (e2 & L1 & A1 & B1 & u2 & Ne2 & Nsnd & Du2 & Hu2).
    destruct (dn_inr Nm' Ne1' Nc0' Ni' Nj' (tmred_red _ _ _ _ _ _ _ Hk') Hi1' Du')
      as (e2' & L1' & A1' & B1' & u2' & Ne2' & Nsnd' & Du2' & Hu2').
    assert (HFmv : [ G0 ; Δ0 ,, tyFin m @ lzero
                     ⊢g iwfFamT l li (sX γ e) (sA γ e) (sN γ e) (sO γ e) (sC γ e) (posMv m cf) @ lmax l li ]).
    { rewrite <- iwfFamT_mv. exact (dvecMv_wf ge_typeof ge_notV ge_compt Hm HF1). }
    assert (HPmv : forall (ρ : kwk G0 Δ0) p p', PosRel (kw_G ρ) (kw_Δ ρ) (ktm ρ m) (ktm ρ m) p p' ->
              [ kw_G ρ ; kw_Δ ρ ⊢ (ktml ρ (posMv m cf))[lsingle p] ≈ (ktml ρ (posMv m cf))[lsingle p']
                : kty ρ (sX γ e) @ li ]).
    { intros ρ p p' Hp. rewrite !(ktml_posMv_single ρ) by exact Nm. apply HP.
      pose proof (kw_tmred_succ Hk ρ) as Hkρ. eapply pos_tl; [exact Hkρ | exact Hkρ | exact Hp]. }
    apply (IHs _ _ _ _ _ _ _ _ HLL HLL HLL HLL Ghd Gtl' Ghd Gtl' γ e e' Hh HFmv HPmv _ _ Nsnd Nsnd'
             (tc_snd _ _ _ _ _ _ _ _ _ _ _ Tc (tmred_red _ _ _ _ _ _ _ Hcs) Nw Pw)
             (tc_snd _ _ _ _ _ _ _ _ _ _ _ Tc' (tmred_red _ _ _ _ _ _ _ Hcs') Nw' Pw')
             m' j j' Hmm Hjj _ _ _ _ Ne2 Ne2' Du2 Du2' x x' s s' Hx Hss).
    + exact (reds_trans _ _ _ Hs Hu2).
    + exact (reds_trans _ _ _ Hs' Hu2').
  - (* a neutral index *)
    destruct (dn_case_ne Nm Ne1 Nc0 Ni (tmred_red _ _ _ _ _ _ _ Hk) Hiν Nν Du) as (X1 & HX1 & NX1).
    exact (elimIWf_ne Hγ He Hx HX HA Hss (reds_trans _ _ _ Hs HX1) NX1).
Qed.

(** ** The step at a [sup_i] *)

(** A child index in a world, at related shapes and positions. *)
Lemma elimIWf_ci_kw {G0 γ Δ0 e e2 Cr} (ρ : kwk G0 Δ0) {b b' p p'} :
  gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e2 ->
  VTmG G0 (Γ⟦γ⟧ ,, A⟦γ⟧ @ l ,, tyFin N⟦γ⟧ @ lzero) C⟦γ⟧ Cr X⟦γ⟧⟨↑⟩⟨↑⟩ li ->
  LRtm l (kw_G ρ) (kw_Δ ρ) (kty ρ (sA γ e)) (kty ρ (sA γ e2)) b b' ->
  LRtm lzero (kw_G ρ) (kw_Δ ρ) (tyFin (ktml ρ (sN γ e))[lsingle b]) (tyFin (ktml ρ (sN γ e2))[lsingle b']) p p' ->
  LRtm li (kw_G ρ) (kw_Δ ρ) (kty ρ (sX γ e)) (kty ρ (sX γ e))
    (ktmll ρ (sC γ e))[lsingle2 b p] (ktmll ρ Cr[llift (llift e2)])[lsingle2 b' p'].
Proof.
  intros Hγ He VCr Hb Hp.
  destruct (elimIWf_loc Hγ) as (VXγ & _).
  pose proof (SubRel_kw _ _ _ ρ _ _ He) as Heρ.
  rewrite !kty_subst in Hb. rewrite !ktml_subst_single in Hp.
  assert (Hp' : LRtm lzero (kw_G ρ) (kw_Δ ρ) (tyFin N⟦γ⟧⟦kw_γ ρ⟧)[lcons (kwsub ρ e) b]
                  (tyFin N⟦γ⟧⟦kw_γ ρ⟧)[lcons (kwsub ρ e2) b'] p p') by (rewrite !subst_tyFin; exact Hp).
  pose proof (VCr _ _ (kw_gok ρ)) as VCρ. rewrite !gwa_cext, gwa_tyFin, !gwa_ren_ty in VCρ.
  pose proof (VCρ _ _ _ (SubRel_cons (SubRel_cons Heρ Hb) Hp')) as Y.
  rewrite <- !ktmll_subst_single2, !shift_cons_ty, <- !kty_subst in Y.
  eapply LRtm_irrel_r; [exact Y | exact (VTyG_kw ρ (VTyG_refl_l VXγ) (SubRel_refl_l He))].
Qed.

(** The motive at the children's [dnth] in a world, at related positions:
    the induction hypothesis's body there. *)
Lemma elimIWf_kgoal {G0 Δ0} {ix dm : DomRel G0 Δ0} {a a' cs cs' γ e e'} (ρ : kwk G0 Δ0) {y y'} :
  gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' ->
  KDom G0 Δ0 (lmeasure (lmax l li)) li (sX γ e) ix -> KDom G0 Δ0 (lmeasure (lmax l li)) l (sA γ e) dm ->
  LRtm l G0 Δ0 (sA γ e) (sA γ e') a a' ->
  LRtm (lmax l li) G0 Δ0 (iwfcsty l li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧)[lcons e a]
    (iwfcsty l li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧)[lcons e' a'] cs cs' ->
  (forall ρ : kwk G0 Δ0,
     elimIWf_mspine (kw_G ρ) (kw_Δ ρ) l li (kty ρ (sX γ e)) (kty ρ (sA γ e)) (ktml ρ (sN γ e)) (ktml ρ (sO γ e))
       (ktmll ρ (sC γ e)) (fun ρ' => ix (kw_comp ρ ρ')) (fun ρ' => dm (kw_comp ρ ρ'))
       (ktmll ρ (sC γ e))[llift (lsingle (ktm ρ a))] (ktml ρ (sN γ e))[lsingle (ktm ρ a)] (ktm ρ cs) (ktm ρ cs')) ->
  LRtm lzero (kw_G ρ) (kw_Δ ρ) (tyFin (ktml ρ (sN γ e))[lsingle (ktm ρ a)])
    (tyFin (ktml ρ (sN' γ e'))[lsingle (ktm ρ a')]) y y' ->
  LRtm l' (kw_G ρ) (kw_Δ ρ)
    (ktyll ρ (sM γ e))[lsingle2 (ktmll ρ (sC γ e))[lsingle2 (ktm ρ a) y]
       (tmDNth (lmax l li) (ktml ρ (sN γ e))[lsingle (ktm ρ a)]
          (iwfFam l li (kty ρ (sX γ e)) (kty ρ (sA γ e)) (ktml ρ (sN γ e)) (ktml ρ (sO γ e)) (ktmll ρ (sC γ e))
             (ktm ρ a)) (ktm ρ cs) y)]
    (ktyll ρ (sM γ e))[lsingle2 (ktmll ρ (sC γ e))[lsingle2 (ktm ρ a) y]
       (tmDNth (lmax l li) (ktml ρ (sN γ e))[lsingle (ktm ρ a)]
          (iwfFam l li (kty ρ (sX γ e)) (kty ρ (sA γ e)) (ktml ρ (sN γ e)) (ktml ρ (sO γ e)) (ktmll ρ (sC γ e))
             (ktm ρ a)) (ktm ρ cs) y)]
    (tmElimIWf l li l' (kty ρ (sX γ e)) (kty ρ (sA γ e)) (ktml ρ (sN γ e)) (ktml ρ (sO γ e)) (ktmll ρ (sC γ e))
       (ktyll ρ (sM γ e)) (ktm3 ρ (sc γ e)) (ktmll ρ (sC γ e))[lsingle2 (ktm ρ a) y]
       (tmDNth (lmax l li) (ktml ρ (sN γ e))[lsingle (ktm ρ a)]
          (iwfFam l li (kty ρ (sX γ e)) (kty ρ (sA γ e)) (ktml ρ (sN γ e)) (ktml ρ (sO γ e)) (ktmll ρ (sC γ e))
             (ktm ρ a)) (ktm ρ cs) y))
    (tmElimIWf l3 li3 l4 (kty ρ (sX' γ e')) (kty ρ (sA' γ e')) (ktml ρ (sN' γ e')) (ktml ρ (sO' γ e'))
       (ktmll ρ (sC' γ e')) (ktyll ρ (sM' γ e')) (ktm3 ρ (sc' γ e')) (ktmll ρ (sC' γ e'))[lsingle2 (ktm ρ a') y']
       (tmDNth (lmax l3 li3) (ktml ρ (sN' γ e'))[lsingle (ktm ρ a')]
          (iwfFam l3 li3 (kty ρ (sX' γ e')) (kty ρ (sA' γ e')) (ktml ρ (sN' γ e')) (ktml ρ (sO' γ e'))
             (ktmll ρ (sC' γ e')) (ktm ρ a')) (ktm ρ cs') y')).
Proof.
  intros Hγ He HX HA Xa Xcs IH Hy.
  pose proof (SubRel_ctx He) as HΔ0. destruct (SubRel_nf _ _ _ _ _ He) as [Ne Ne'].
  destruct (elimIWf_loc Hγ) as (VXγ & VAγ & VNγ & VOγ & VCγ & _).
  destruct (elimIWf_nf Hγ He) as (NX & NA & NN & NO & NC & NM & Nc).
  pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwl) as Hwl0. pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwli) as Hwli0.
  assert (HwL : lwf (gL G0) (lmax l li)) by (split; assumption).
  destruct (LRtm_escape Xa) as [Hat Ha't]. pose proof (wf_tm_nf Hat) as Na. pose proof (wf_tm_nf Ha't) as Na'.
  destruct (LRtm_escape Xcs) as [Hcst Hcs't]. pose proof (wf_tm_nf Hcst) as Ncs. pose proof (wf_tm_nf Hcs't) as Ncs'.
  pose proof (SubRel_cons He Xa) as HS1. pose proof (SubRel_cons HS1 Xcs) as HS2.
  (* the arities *)
  pose proof (VTmG_loc VNγ _ _ _ HS1) as XN. rewrite !subst_tyNat in XN.
  apply LRtm_nat in XN. rewrite <- !lift_single_tm in XN by assumption. rename XN into Hkk.
  pose proof (NatRel_kw ρ _ _ Hkk) as Hkkρ. rewrite !ktm_single in Hkkρ.
  pose proof (LRtm_trans Xa (LRtm_sym Xa)) as Xaa.
  pose proof (VTmG_loc (VTmG_refl_l VNγ) _ _ _ (SubRel_cons (SubRel_refl_l He) Xaa)) as XN.
  rewrite !subst_tyNat in XN. apply LRtm_nat in XN. rewrite <- !lift_single_tm in XN by assumption.
  rename XN into Hkk0.
  (* the shapes in the world *)
  pose proof (LRtm_kw ρ Xa) as Xaρ.
  (* the position at the left arity, both sides *)
  pose proof (VTmG_loc (VTmG_refl_l VNγ) _ _ _ HS1) as XN. rewrite !subst_tyNat in XN.
  apply LRtm_nat in XN. rewrite <- !lift_single_tm in XN by assumption.
  pose proof (NatRel_kw ρ _ _ XN) as Hkkl. rewrite !ktm_single in Hkkl.
  pose proof (LRtm_irrel_r Hy (LR_fin_nat (kw_ctx ρ) Hkkl)) as Yl.
  (* the children's [dnth]s, related at [IWf] *)
  destruct (elimIWf_dnth_kw ρ Hγ HS2 Yl) as (RN & HRN & Hn).
  apply (proj1 (LR_iwf_rel HRN (KDom_comp ρ HX) (KDom_comp ρ HA) _ _)) in Hn.
  (* the child indices *)
  pose proof (elimIWf_ci_kw ρ Hγ He VCγ Xaρ Yl) as Xx.
  (* the induction hypothesis *)
  assert (He1 : SubRel (kw_G ρ) Γ⟦gwk_comp (kw_γ ρ) γ⟧ (kw_Δ ρ) (kwsub ρ e) (kwsub ρ e')).
  { pose proof (SubRel_kw _ _ _ ρ _ _ He) as Z. now rewrite gwa_comp_ctx in Z. }
  assert (Hh : elimIWf_hyp (kw_G ρ) (kw_Δ ρ) l li (kty ρ (sX γ e)) (kty ρ (sA γ e)) (ktml ρ (sN γ e))
                 (ktml ρ (sO γ e)) (ktmll ρ (sC γ e)) (fun ρ' => ix (kw_comp ρ ρ')) (fun ρ' => dm (kw_comp ρ ρ'))
                 (gwk_comp (kw_γ ρ) γ) (kwsub ρ e) (kwsub ρ e')).
  { refine (conj (gwk_ok_comp (kw_gok ρ) Hγ) (conj He1 (conj eq_refl (conj eq_refl (conj (kγ_ty ρ X γ e)
              (conj (kγ_ty ρ A γ e) (conj (kγ_tml ρ N γ e) (conj (kγ_tml ρ Ot γ e) (conj (kγ_tmll ρ C γ e)
              (conj (KDom_comp ρ HX) (KDom_comp ρ HA))))))))))). }
  (* the family at the world, typed and generically reflexive at related positions *)
  destruct (elimIWf_sig Hγ He) as [HE0 _].
  pose proof (IWfEq_kw ρ HE0) as (_ & _ & HSρ & _).
  destruct (LRtm_escape Xaρ) as [Haρ _].
  pose proof (IWf_fam_wf ge_typeof ge_notV HSρ Haρ) as HFam. rewrite iwfFam_T in HFam.
  assert (HP : forall (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) p p',
             PosRel (kw_G ρ') (kw_Δ ρ') (ktm ρ' (ktml ρ (sN γ e))[lsingle (ktm ρ a)])
               (ktm ρ' (ktml ρ (sN γ e))[lsingle (ktm ρ a)]) p p' ->
             [ kw_G ρ' ; kw_Δ ρ' ⊢ (ktml ρ' (ktmll ρ (sC γ e))[llift (lsingle (ktm ρ a))])[lsingle p]
                 ≈ (ktml ρ' (ktmll ρ (sC γ e))[llift (lsingle (ktm ρ a))])[lsingle p'] : kty ρ' (kty ρ (sX γ e)) @ li ]).
  { intros ρ' p p' Hp. rewrite !ktml_comp_child, <- kty_comp. rewrite !ktm_comp_single in Hp.
    pose proof (NatRel_kw (kw_comp ρ ρ') _ _ Hkk0) as Hk2. rewrite !ktm_single in Hk2.
    pose proof (elimIWf_ci_kw (kw_comp ρ ρ') Hγ (SubRel_refl_l He) (VTmG_refl_l VCγ) (LRtm_kw (kw_comp ρ ρ') Xaa)
                  (PosRel_LRtm Hp Hk2)) as Y.
    exact (LRtm_geq Y). }
  destruct (NatRel_escape Hkkρ) as (Hk & Hk' & _). pose proof (wf_tm_nf Hk) as Nk. pose proof (wf_tm_nf Hk') as Nk'.
  pose proof (wf_ty_nf HFam) as NF.
  assert (NF' : nfty (iwfFam l3 li3 (kty ρ (sX' γ e')) (kty ρ (sA' γ e')) (ktml ρ (sN' γ e')) (ktml ρ (sO' γ e'))
                        (ktmll ρ (sC' γ e')) (ktm ρ a'))).
  { unfold iwfFam. cbn. repeat split; first [apply ren_nf_ty | apply ren_nf | apply subst_nf]; try apply ren_nf.
    apply lk_llift, lk_lsingle, ren_nf. }
  assert (Ncsρ : nftm (ktm ρ cs)) by apply ren_nf. assert (Ncs'ρ : nftm (ktm ρ cs')) by apply ren_nf.
  assert (Ne1 : nftm (lam lzero lzero (tyFin (ktml ρ (sN γ e))[lsingle (ktm ρ a)]) (var 0))) by (cbn; auto).
  assert (Ne1' : nftm (lam lzero lzero (tyFin (ktml ρ (sN' γ e'))[lsingle (ktm ρ a')]) (var 0))) by (cbn; auto).
  pose proof (IH ρ _ _ _ Hh HFam HP (ktm ρ cs) (ktm ρ cs') Ncsρ Ncs'ρ (tc_refl _) (tc_refl _) _ _ _ Hkkρ Hy
                _ _ _ _ Ne1 Ne1' (dn_top Nk NF) (dn_top Nk' NF') _ _ _ _ Xx Hn (reds_refl _) (reds_refl _)) as X0.
  unfold elimIWf_goal in X0.
  rewrite <- (kγ_ty ρ X γ e), <- (kγ_ty ρ A γ e), <- (kγ_tml ρ N γ e), <- (kγ_tml ρ Ot γ e), <- (kγ_tmll ρ C γ e),
    <- (kγ_tyll ρ M γ e), <- (kγ_tm3 ρ c γ e), <- (kγ_ty ρ X' γ e'), <- (kγ_ty ρ A' γ e'), <- (kγ_tml ρ N' γ e'),
    <- (kγ_tml ρ Ot' γ e'), <- (kγ_tmll ρ C' γ e'), <- (kγ_tyll ρ M' γ e'), <- (kγ_tm3 ρ c' γ e') in X0.
  exact X0.
Qed.

End ElimAt.

End IWfElim.
