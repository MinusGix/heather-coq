(** * With definitions, closed canonicity fails at M (M9 open item 1)

    Heather keeps the code recursor stuck on a boxed global, defined or
    not ([whne_elimt_gdef]; M9_DESIGN.md step 4). So a global context with
    one definition already has a closed, typed M-term that does not
    compute: the recursor run on the boxed definition.

    The witness: [Ψ = (u : Trm(· ⊢ Nat) := zero)], and
    [elim_Trm(x. Nat; 0, …, 0; box(u^id))] at type [Nat], with the
    constant motive [Nat] and every branch [zero]. It is typed
    ([stuck_rec_wf]), neutral ([stuck_rec_whne]), has no value
    ([stuck_rec_no_value]) and equals no numeral ([stuck_rec_not_numeral]).
    The global context has no opaque bindings ([Gdef_no_opaque]), so
    [closed_ok] (canonicity at D with definitions) cannot extend to M
    ([closed_canonicity_fails_M]). *)
From DeLaM.Typing Require Import RecAdm.
From DeLaM.Validity Require Export Canonicity.

(** ** The global context and the term *)

Definition Gdef : gctx := mkG 0 (gdDef cnil tyNat lzero zero :: nil).
Definition u_def : tm := gdef 0 zero (lshift 0).
Definition stuck_rec : tm :=
  elimt lzero lzero (mkrb tyNat tyNat (fun _ => zero)) lzero cnil tyNat (boxt u_def).

Lemma Gdef_wf : [ ⊢ Gdef ].
Proof.
  apply wfg_def.
  - apply wfg_nil.
  - apply wft_nat; [discriminate | apply wfc_nil, wfg_nil].
  - exact I.
  - apply wf_zero; [discriminate | apply wfc_nil, wfg_nil].
Qed.

Lemma Gdef_no_opaque : no_opaque Gdef.
Proof.
  intros n D Hin. inversion Hin as [Ψ D0 | Ψ D0 D' m Hm]; subst.
  - right. do 4 eexists. reflexivity.
  - inversion Hm.
Qed.

Lemma Gdef_not_ctx_only : ~ ctx_only Gdef.
Proof. intros H. discriminate (H 0 _ (ing_here nil (gdDef cnil tyNat lzero zero))). Qed.

(** ** Typing *)

Lemma u_def_wf : [ Gdef ; cnil ⊢[ lC ] u_def : tyNat @ lzero ].
Proof.
  refine (wf_gdef Gdef lC cnil 0 cnil tyNat lzero zero zero (lshift 0) _
            (ing_here nil (gdDef cnil tyNat lzero zero)) (tm_leq_refl _) (le_n _) _ I _ _).
  - exact (wfc_nil _ _ Gdef_wf).
  - exact (tail_id _).
  - intros n A k Hin; inversion Hin.
  - apply wf_zero; [discriminate | exact (wfc_nil _ _ Gdef_wf)].
Qed.

Lemma brRes_nat k : k < nbr -> brRes k (wrapMT tyNat) (wrapMt tyNat) = tyNat.
Proof. intros Hk; br_all ltac:(destruct k as [|k]; [reflexivity|]); lia. Qed.

Lemma brLv_zero k : brLv k lzero lzero = lzero.
Proof. unfold brLv; destruct (br_isT k); reflexivity. Qed.

Lemma stuck_rec_wf : [ Gdef ; cnil ⊢[ lM ] stuck_rec : tyNat @ lzero ].
Proof.
  pose proof (wfc_nil _ lM Gdef_wf) as HΓ.
  assert (HMT : [ recGT Gdef ; recΓT cnil ⊢[ lM ] tyNat @ lvren lzero (ush 1) ])
    by (apply wft_nat; [discriminate | exact (wf_recΓT _ _ HΓ)]).
  assert (HMt : [ recGt Gdef ; recΓt cnil ⊢[ lM ] tyNat @ lvren lzero (ush 1) ])
    by (apply wft_nat; [discriminate | exact (wf_recΓt _ _ HΓ)]).
  refine (wf_elimt_adm (G := Gdef) (Γ := cnil) (l1 := lzero) (l2 := lzero) (MT := tyNat) (Mt := tyNat)
            (bs := fun _ => zero) (l := lzero) (Δ := cnil) (T := tyNat) (t := boxt u_def)
            I I I (wfc_nil _ _ Gdef_wf) HMT HMt _ _ _).
  - intros k Hk. rewrite brRes_nat, brLv_zero by exact Hk.
    apply wf_zero; [discriminate | exact (brΓ_wf (l1 := lzero) (l2 := lzero) HΓ I I HMT HMt k Hk)].
  - apply wft_nat; [discriminate | exact (wfc_nil _ _ Gdef_wf)].
  - apply wf_boxt; [exact HΓ | exact I | exact (wfc_nil _ _ Gdef_wf) | | exact u_def_wf].
    apply wft_nat; [discriminate | exact (wfc_nil _ _ Gdef_wf)].
Qed.

(** ** It does not compute *)

Lemma stuck_rec_whne : whne stuck_rec.
Proof. apply whne_elimt_gdef. Qed.

Theorem stuck_rec_no_value : ~ exists w, reds stuck_rec w /\ ~ whne w.
Proof.
  intros (w & Hr & Hn). rewrite (reds_whnf_self (whnf_ne _ stuck_rec_whne) Hr) in Hn.
  exact (Hn stuck_rec_whne).
Qed.

Lemma numeral_whnf n : whnf (numeral n).
Proof. destruct n; [exact whnf_zero | exact (whnf_succ _)]. Qed.

(** Nor is it equal to a numeral: the relation at [Nat] pairs a neutral
    only with a neutral. *)
Theorem stuck_rec_not_numeral n : ~ [ Gdef ; cnil ⊢[ lM ] stuck_rec ≅ numeral n : tyNat @ lzero ].
Proof.
  intros H. pose proof (redM_eqtm _ _ _ _ _ _ H I) as X.
  pose proof (proj1 (LRtm_nat (E := DeclEq lM compt_M) (LP := LR_M (DeclEq lD compt_D) (DeclEq lM compt_M))) X)
    as N.
  inversion N as [t t' w w' Hw Hw' _ Hnf]; subst.
  rewrite (reds_whnf_self (whnf_ne _ stuck_rec_whne) (tmred_red _ _ _ _ _ _ _ Hw)) in Hnf.
  rewrite (reds_whnf_self (numeral_whnf n) (tmred_red _ _ _ _ _ _ _ Hw')) in Hnf.
  inversion Hnf as [| | ν ν' Hνν]; subst.
  pose proof (gne_tm_whne_r Hνν) as Hn. destruct n; inversion Hn.
Qed.

(** Closed canonicity's conclusion ([closed_canonicity]) fails for it. *)
Theorem closed_canonicity_fails_M :
  no_opaque Gdef /\ [ Gdef ; cnil ⊢[ lM ] stuck_rec : tyNat @ lzero ] /\
  ~ exists W w, reds_ty tyNat W /\ whnf_ty W /\ ~ whne_ty W /\
      reds stuck_rec w /\ whnf w /\ ~ whne w /\ [ Gdef ; cnil ⊢[ lM ] stuck_rec ≅ w : tyNat @ lzero ] /\
      canon_head (ty_head W) w.
Proof.
  split; [exact Gdef_no_opaque | split; [exact stuck_rec_wf |]].
  intros (W & w & _ & _ & _ & Hr & _ & Hn & _). exact (stuck_rec_no_value (ex_intro _ w (conj Hr Hn))).
Qed.

Print Assumptions closed_canonicity_fails_M.
Print Assumptions stuck_rec_not_numeral.
