(** * IWf lowerings, in the formalization's own rules: the cases left open

    [IwfLowering.v] checked the generator's lowerings of Heather's
    [docs/iwf-former-design.md] §8 for [Vec], F1–F3, [All] (§12.1) and
    [Even]/[Odd] (§12.2) and left two cases unchecked ([M17_DESIGN.md],
    "The generator's lowerings"). This file checks them by the same
    method (the M17b rules only, through the checker of [IwfCheck.v]):
    - a mutual pair over a tag-dependent index [Σ(b : Bool). I_b] with
      [I_inl := Nat] and [I_inr := Bool], whose motive cases on [snd j] at
      a type that depends on [fst j] (the convoy);
    - form A whose result is a value of the family itself at a [List a]
      index ([allTail : All P (x :: xs) → All P xs]), which needs [List]'s,
      the shapes' and [All]'s own codes.
    Compile after [IwfCheck.v] (see [IwfLowering.v]'s header):
    [coqc -Q theories DeLaM -Q probes Probes probes/IwfLowering2.v]. *)
From DeLaM.Typing Require Import RecWfBase IWfIH PresupAux.
From DeLaM.Validity Require Import RecReduct DeclConsequencesP AlgComplete.
From Probes Require Import IwfCheck.

(** ** A mutual pair over [Σ(b : Bool). I_b] with [I_b] varying

    [A : Nat → Type] and [B : Bool → Type] (with [true := inl ⟨⟩]):
    [anil : A 0], [acons(n, y : Nat, h : B true) : A (S n)],
    [bleaf : B false], [bnode(n, c : A n) : B true]. Each constructor's
    child is in the other family. One family over
    [X := Σ(b : Bool). El(case b of inl ⇒ ⌜Nat⌝ | inr ⇒ ⌜Bool⌝)]: the index
    type's second component is a large elimination of the tag, so a pair
    [(tag, v)] is typed through [case]'s β. The shape is the tag's sum of
    each family's shapes, [(Unit + Σ(n : Nat). Nat) + (Unit + Nat)], and
    the arity, output index and child index case on the tag and then on
    the constructor. The family is closed. *)
Notation Bool0 := (tySum L0 L0 U0 U0).
Notation tA := (tmInl L0 L0 U0 U0 tt0).
Notation tB := (tmInr L0 L0 U0 U0 tt0).
Notation bT := (tmInl L0 L0 U0 U0 tt0).
Notation bF := (tmInr L0 L0 U0 U0 tt0).
Notation BoolC := (tmSum L0 L0 (tmUnit L0) (tmUnit L0)).
(** [I_b]'s code, at a tag [t]. *)
Notation IfC t := (tmCase L0 L0 (lsuc L0) U0 U0 (tyU L0) tmNat BoolC t).
Notation If := (tyEl L0 (IfC (var 0))).                                    (* b *)
Notation XI := (tySig L0 L0 Bool0 If).
Notation pr b v := (tmPair L0 L0 Bool0 If b v).

Notation aPay := (tySig L0 L0 tyNat tyNat).
Notation SA := (tySum L0 L0 U0 aPay).
Notation SB := (tySum L0 L0 U0 tyNat).
Notation abS := (tySum L0 L0 SA SB).
Notation inA a := (tmInl L0 L0 SA SB a).
Notation inB b := (tmInr L0 L0 SA SB b).
Notation abN_at a := (tmCase L0 L0 L0 SA SB tyNat
                   (tmCase L0 L0 L0 U0 aPay tyNat zero (succ zero) (var 0))
                   (tmCase L0 L0 L0 U0 tyNat tyNat zero (succ zero) (var 0))
                   a).
Notation abN := (abN_at (var 0)).                                                (* x *)
Notation abO_at a := (tmCase L0 L0 L0 SA SB XI
                   (tmCase L0 L0 L0 U0 aPay XI (pr tA zero) (pr tA (succ (tmFst L0 L0 tyNat tyNat (var 0)))) (var 0))
                   (tmCase L0 L0 L0 U0 tyNat XI (pr tB bF) (pr tB bT) (var 0))
                   a).
Notation abO := (abO_at (var 0)).                                                (* x *)
Notation abC_at a := (tmCase L0 L0 L0 SA SB XI
                   (tmCase L0 L0 L0 U0 aPay XI (pr tA zero) (pr tB bT) (var 0))
                   (tmCase L0 L0 L0 U0 tyNat XI (pr tA zero) (pr tA (var 0)) (var 0))
                   a).
Notation abC := (abC_at (var 1)).                                                (* x, i *)
Notation AB m := (tyIWf L0 L0 XI abS abN abO abC m).
Notation absupi a cs := (tmSupi L0 L0 XI abS abN abO abC a cs).
Notation anil := (absupi (inA (tmInl L0 L0 U0 aPay tt0)) (tmTriv LL)).
Notation acons n y h := (absupi (inA (tmInr L0 L0 U0 aPay (tmPair L0 L0 tyNat tyNat n y)))
                           (tmPair LL LL (AB (pr tB bT)) (tyUnit LL) h (tmTriv LL))).
Notation bleaf := (absupi (inB (tmInl L0 L0 U0 tyNat tt0)) (tmTriv LL)).
Notation bnode n c := (absupi (inB (tmInr L0 L0 U0 tyNat n))
                         (tmPair LL LL (AB (pr tA n)) (tyUnit LL) c (tmTriv LL))).

(** [size] counts the constructors of both families, one [elim_IWf]. Its
    step uses the induction hypothesis at a literal position, so each case
    on the shape carries it (the convoy of [IwfLowering.v]'s [len]): the
    inner case's motive is the outer one's at [inl]/[inr] of its own
    variable. *)
Notation abIH N := (tyPi L0 L0 (tyFin N) tyNat).
Notation p0 := (tmInl L0 L0 U0 (tyFin zero) tt0).
Notation sizeArm := (lam LL L0 (abIH (succ zero)) (succ (app (var 0) L0 L0 (tyFin (succ zero)) tyNat p0))).
Notation sizeStep :=
  (app (tmCase L0 L0 LL SA SB (tyPi LL L0 (abIH abN) tyNat)
          (tmCase L0 L0 LL U0 aPay (tyPi LL L0 (abIH abN[lsingle (inA (var 0))]⟨rlift ↑⟩) tyNat)
             (lam LL L0 (abIH zero) zero) sizeArm (var 0))
          (tmCase L0 L0 LL U0 tyNat (tyPi LL L0 (abIH abN[lsingle (inB (var 0))]⟨rlift ↑⟩) tyNat)
             (lam LL L0 (abIH zero) zero) sizeArm (var 0))
          (var 2))
     LL L0 (abIH abN⟨rshift 2⟩) tyNat (var 0)).
Notation size m t := (tmElimIWf L0 L0 L0 XI abS abN abO abC tyNat sizeStep m t).

(** [pay] reads [acons]'s [y] and [bnode]'s [n], by form A. The motive
    cases on the index: on the tag, and then on [snd j], whose type
    [El(I_{fst j})] depends on the tag. A case on [fst j] does not refine
    [snd j]'s type, so the case on the tag returns a function of [I_b] and
    is applied to [snd j] (the convoy, now in the motive):
    [El((case fst j of inl ⇒ λ(k : Nat). natrec(⌜Unit⌝; _ _. ⌜Nat⌝; k)
                      | inr ⇒ λ(b : Bool). case b of inl ⇒ ⌜Nat⌝ | inr ⇒ ⌜Unit⌝) (snd j))].
    [⌜Nat⌝] at [A]'s successor indices and at [B true], [⌜Unit⌝] at the
    others. The step reads only the payload, so it needs no convoy. *)
Notation Mpay j :=
  (tyEl L0 (app (tmCase L0 L0 (lmax L0 (lsuc L0)) U0 U0 (tyPi L0 (lsuc L0) If (tyU L0))
                   (lam L0 (lsuc L0) tyNat (natrec (lsuc L0) (tyU L0) (tmUnit L0) tmNat (var 0)))
                   (lam L0 (lsuc L0) Bool0 (tmCase L0 L0 (lsuc L0) U0 U0 (tyU L0) tmNat (tmUnit L0) (var 0)))
                   (tmFst L0 L0 Bool0 If j))
              L0 (lsuc L0) (tyEl L0 (IfC (tmFst L0 L0 Bool0 If j))) (tyU L0) (tmSnd L0 L0 Bool0 If j))).
Notation payStep :=
  (tmCase L0 L0 L0 SA SB (Mpay abO)
     (tmCase L0 L0 L0 U0 aPay (Mpay abO[lsingle (inA (var 0))]⟨rlift ↑⟩) tt0 (tmSnd L0 L0 tyNat tyNat (var 0)) (var 0))
     (tmCase L0 L0 L0 U0 tyNat (Mpay abO[lsingle (inB (var 0))]⟨rlift ↑⟩) tt0 (var 0) (var 0))
     (var 2)).
Notation pay m t := (tmElimIWf L0 L0 L0 XI abS abN abO abC (Mpay (var 1)) payStep m t).

Section Probe2.
Context {G : gctx} (HG : [ ⊢ G ]).

Let Hv : lD <> lV. Proof. discriminate. Qed.

(** *** The mutual pair: typing *)

(** The index type's pieces, the signature's components in any context
    and the motive at any index, once (each would otherwise be retyped at
    every use, and [pay]'s typing ran out of memory). *)
Lemma If_wf {Γ t} : [ G ; Γ ⊢[ lD ] ] -> [ G ; Γ ⊢[ lD ] t : Bool0 @ LL ] -> [ G ; Γ ⊢[ lD ] tyEl L0 (IfC t) @ L0 ].
Proof. intros HΓ Ht. pty. Qed.
Ltac pfam_ty ::= ty_rule @If_wf.
Lemma pr_wf {Γ b v} : [ G ; Γ ⊢[ lD ] ] -> [ G ; Γ ⊢[ lD ] b : Bool0 @ L0 ] ->
  [ G ; Γ ⊢[ lD ] v : tyEl L0 (IfC b) @ L0 ] -> [ G ; Γ ⊢[ lD ] pr b v : XI @ L0 ].
Proof. intros HΓ Hb Hv'. ptm. Qed.
Ltac pfam_tm ::= tm_rule @pr_wf.
Lemma abN_wf {Γ} : [ G ; Γ ⊢[ lD ] ] -> [ G ; Γ ,, abS @ L0 ⊢[ lD ] abN : tyNat @ L0 ].
Proof. intros HΓ. ptm. Qed.
Lemma abO_wf {Γ} : [ G ; Γ ⊢[ lD ] ] -> [ G ; Γ ,, abS @ L0 ⊢[ lD ] abO : XI @ L0 ].
Proof. intros HΓ. ptm. Qed.
Lemma abC_wf {Γ} : [ G ; Γ ⊢[ lD ] ] -> [ G ; Γ ,, abS @ L0 ,, tyFin abN @ L0 ⊢[ lD ] abC : XI @ L0 ].
Proof. intros HΓ. ptm. Qed.
Ltac pfam_tm ::= first [ tm_rule @pr_wf | tm_rule @abN_wf | tm_rule @abO_wf | tm_rule @abC_wf ].
Lemma Mpay_wf {Γ j} : [ G ; Γ ⊢[ lD ] ] -> [ G ; Γ ⊢[ lD ] j : XI @ LL ] -> [ G ; Γ ⊢[ lD ] Mpay j @ L0 ].
Proof. intros HΓ Hj. pty. Qed.
Ltac pfam_ty ::= first [ ty_rule @If_wf | ty_rule @Mpay_wf ].

Lemma AB_wf {Γ m} : [ G ; Γ ⊢[ lD ] ] -> [ G ; Γ ⊢[ lD ] m : XI @ L0 ] -> [ G ; Γ ⊢[ lD ] AB m @ LL ].
Proof. intros HΓ Hm. pty. Qed.
Ltac pfam_ty ::= first [ ty_rule @AB_wf | ty_rule @If_wf | ty_rule @Mpay_wf ].
Lemma AB_conv {Γ m m'} : [ G ; Γ ⊢[ lD ] ] -> [ G ; Γ ⊢[ lD ] m ≅ m' : XI @ L0 ] ->
  [ G ; Γ ⊢[ lD ] AB m ≅ AB m' @ LL ].
Proof. intros HΓ Hm. pconv. Qed.
Ltac pfam_conv ::= conv_rule @AB_conv.

(** The two steps, typed once in their telescope (each β retypes the step
    otherwise, and [apay_beta] ran out of memory). The hook normalizes the
    lemma's statement as the checker normalizes goals, and fires at the
    step's head only. *)
Ltac pstep L := let H := fresh "Hstep" in pose proof L as H; pn_in H; eapply H; pgoal.
Lemma sizeStep_wf {Γ} : [ G ; Γ ⊢[ lD ] ] ->
  [ G ; Γ ,, abS @ L0 ,, iwfcsty L0 L0 XI abS abN abO abC @ LL ,, iwfihty L0 L0 L0 XI abS abN abO abC tyNat @ lmax L0 L0
      ⊢[ lD ] sizeStep : iwfstepty L0 L0 XI abS abN abO abC tyNat @ L0 ].
Proof. intros HΓ. ptm. Qed.
Lemma payStep_wf {Γ} : [ G ; Γ ⊢[ lD ] ] ->
  [ G ; Γ ,, abS @ L0 ,, iwfcsty L0 L0 XI abS abN abO abC @ LL ,, iwfihty L0 L0 L0 XI abS abN abO abC (Mpay (var 1)) @ lmax L0 L0
      ⊢[ lD ] payStep : iwfstepty L0 L0 XI abS abN abO abC (Mpay (var 1)) @ L0 ].
Proof. intros HΓ. ptm. Qed.
Ltac pfam_step :=
  lazymatch goal with
  | |- [ _ ; _ ⊢[ _ ] app (tmCase L0 L0 LL SA SB _ _ _ (var 2)) LL L0 _ tyNat (var 0) : _ @ _ ] => pstep @sizeStep_wf
  | |- [ _ ; _ ⊢[ _ ] tmCase L0 L0 L0 SA SB _ _ _ (var 2) : _ @ _ ] => pstep @payStep_wf
  end.
Ltac pfam_tm ::= first [ pfam_step | tm_rule @pr_wf | tm_rule @abN_wf | tm_rule @abO_wf | tm_rule @abC_wf ].

Lemma ab_ty : [ G ; cnil ,, XI @ L0 ⊢[ lD ] AB (var 0) @ LL ].
Proof. pty. Qed.

Lemma anil_wf : [ G ; cnil ⊢[ lD ] anil : AB (pr tA zero) @ LL ].
Proof. ptm. Qed.

Lemma acons_wf : [ G ; cnil ,, tyNat @ L0 ,, tyNat @ L0 ,, AB (pr tB bT) @ LL ⊢[ lD ]
                   acons (var 2) (var 1) (var 0) : AB (pr tA (succ (var 2))) @ LL ].
Proof. ptm. Qed.

Lemma bleaf_wf : [ G ; cnil ⊢[ lD ] bleaf : AB (pr tB bF) @ LL ].
Proof. ptm. Qed.

Lemma bnode_wf : [ G ; cnil ,, tyNat @ L0 ,, AB (pr tA (var 0)) @ LL ⊢[ lD ]
                   bnode (var 1) (var 0) : AB (pr tB bT) @ LL ].
Proof. ptm. Qed.

(** *** β across the tags *)

Lemma size_wf : [ G ; cnil ,, XI @ L0 ,, AB (var 0) @ LL ⊢[ lD ] size (var 1) (var 0) : tyNat @ L0 ].
Proof. ptm. Qed.

(** [size (acons n y h) ≡ S (size h)], the child at [B]'s index [true]. *)
Lemma size_acons : [ G ; cnil ,, tyNat @ L0 ,, tyNat @ L0 ,, AB (pr tB bT) @ LL ⊢[ lD ]
                     size (pr tA (succ (var 2))) (acons (var 2) (var 1) (var 0))
                     ≅ succ (size (pr tB bT) (var 0)) : tyNat @ L0 ].
Proof. ptmconv. Qed.

(** [size (bnode n c) ≡ S (size c)], the child at [A]'s index [n]. *)
Lemma size_bnode : [ G ; cnil ,, tyNat @ L0 ,, AB (pr tA (var 0)) @ LL ⊢[ lD ]
                     size (pr tB bT) (bnode (var 1) (var 0)) ≅ succ (size (pr tA (var 1)) (var 0)) : tyNat @ L0 ].
Proof. ptmconv. Qed.

(** *** Form A, the motive's convoy on [snd j] *)

Lemma pay_wf : [ G ; cnil ,, XI @ L0 ,, AB (var 0) @ LL ⊢[ lD ] pay (var 1) (var 0) : Mpay (var 1) @ L0 ].
Proof. ptm. Qed.

(** At [A (S n)] the result is a number. *)
Lemma apay_wf : [ G ; cnil ,, tyNat @ L0 ,, AB (pr tA (succ (var 0))) @ LL ⊢[ lD ]
                  pay (pr tA (succ (var 1))) (var 0) : tyNat @ L0 ].
Proof. ptm. Qed.

(** [pay (acons n y h) ≡ y]. *)
Lemma apay_beta : [ G ; cnil ,, tyNat @ L0 ,, tyNat @ L0 ,, AB (pr tB bT) @ LL ⊢[ lD ]
                    pay (pr tA (succ (var 2))) (acons (var 2) (var 1) (var 0)) ≅ var 1 : tyNat @ L0 ].
Proof. ptmconv. Qed.

(** At [B true] too, through the [Bool] arm. *)
Lemma bpay_wf : [ G ; cnil ,, AB (pr tB bT) @ LL ⊢[ lD ] pay (pr tB bT) (var 0) : tyNat @ L0 ].
Proof. ptm. Qed.

(** [pay (bnode n c) ≡ n]. *)
Lemma bpay_beta : [ G ; cnil ,, tyNat @ L0 ,, AB (pr tA (var 0)) @ LL ⊢[ lD ]
                    pay (pr tB bT) (bnode (var 1) (var 0)) ≅ var 1 : tyNat @ L0 ].
Proof. ptmconv. Qed.

(** *** Negative controls

    [bleaf] is not at [B true]: the indices [(inr, false)] and
    [(inr, true)] differ in the second component only, at the type
    [El(I_inr)], so the separating elimination is the motive's convoy
    again, with [⌜Unit⌝] at [true] and [⌜Empty⌝] at [false]. [anil] is not
    in [B] at all: the tags differ ([Dt] of [IwfLowering.v], at this
    index type). *)
Notation Dv j :=
  (tyEl L0 (app (tmCase L0 L0 (lmax L0 (lsuc L0)) U0 U0 (tyPi L0 (lsuc L0) If (tyU L0))
                   (lam L0 (lsuc L0) tyNat (tmUnit L0))
                   (lam L0 (lsuc L0) Bool0 (tmCase L0 L0 (lsuc L0) U0 U0 (tyU L0) (tmUnit L0) (tmEmpty L0) (var 0)))
                   (tmFst L0 L0 Bool0 If j))
              L0 (lsuc L0) (tyEl L0 (IfC (tmFst L0 L0 Bool0 If j))) (tyU L0) (tmSnd L0 L0 Bool0 If j))).
Notation Dtag j := (tyEl L0 (tmCase L0 L0 (lsuc L0) U0 U0 (tyU L0) (tmUnit L0) (tmEmpty L0) (tmFst L0 L0 Bool0 If j))).

(** [Dv]'s congruence at the index's conversion [E]: the argument [snd j]
    by [E], the function (a case on the literal tags) by reduction. *)
Ltac dv_cong E :=
  eapply eqty_El; [exact Hv | lalg | eapply eqtm_cl; [eapply eqtm_app;
    first [ solve [eapply eqtm_cl; [eapply eqtm_snd; by_idx E | lalg | pgoal]] | pgoal ] | lalg | pgoal]].
Ltac dtag_cong E :=
  eapply eqty_El; [exact Hv | lalg | eapply eqtm_cl; [eapply eqtm_case;
    first [ solve [eapply eqtm_cl; [eapply eqtm_fst; by_idx E | lalg | pgoal]] | pgoal ] | lalg | pgoal]].

Lemma bleaf_not_true : ~ [ G ; cnil ⊢[ lD ] bleaf : AB (pr tB bT) @ LL ].
Proof.
  intros H. inv_idx H Em. assert (HΓ : [ G ; cnil ⊢[ lD ] ]) by (apply wfc_nil; exact HG).
  lazymatch type of Em with [ _ ; _ ⊢[ _ ] ?m ≅ ?m' : _ @ _ ] =>
    refine (unit_not_empty (G := G) (Γ := cnil) (T := Dv m) (T' := Dv m') _ _ _); [dv_cong Em | pconv | pconv] end.
Qed.

Lemma anil_not_B : ~ [ G ; cnil ⊢[ lD ] anil : AB (pr tB bF) @ LL ].
Proof.
  intros H. inv_idx H Em. apply eqtm_sym in Em. assert (HΓ : [ G ; cnil ⊢[ lD ] ]) by (apply wfc_nil; exact HG).
  lazymatch type of Em with [ _ ; _ ⊢[ _ ] ?m ≅ ?m' : _ @ _ ] =>
    refine (unit_not_empty (G := G) (Γ := cnil) (T := Dtag m) (T' := Dtag m') _ _ _); [dtag_cong Em | pconv | pconv] end.
Qed.

End Probe2.

(** No axioms: each headline lemma is closed under the global context. *)
Print Assumptions size_acons.
Print Assumptions size_bnode.
Print Assumptions apay_beta.
Print Assumptions bpay_beta.
Print Assumptions bleaf_not_true.
Print Assumptions anil_not_B.
