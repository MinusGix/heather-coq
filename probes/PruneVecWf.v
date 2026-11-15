(** * Pruning [Vec] and [Wf] into [DVec] and [IWf]: what survives

    Heather's [docs/iwf-former-design.md] §10 lists retiring [Vec] and
    [Wf] as translations: [Vec^l(T; k)] as [DVec^l(k; _. T)] and
    [Wf^l(A; x. N)] as [IWf^{l,0}(Unit; A; x. N; _. ⟨⟩; _ _. ⟨⟩)(⟨⟩)].
    The pruned system is a subsystem of today's (it drops rules, adds
    none), so it proves nothing new. This probe checks the other direction:
    which of the dropped rules the translation still derives, and which
    equations it loses.

    Everything is at a generic instance: the shape is [El a] for a code
    variable [a], the arity [nf x] for a function variable [nf], so every
    [Wf] whose shape has a code at level 0 is a substitution instance.
    The judgments are found by [IwfCheck.v]'s syntax-directed checker at
    layer D. Findings (recorded in [PRUNE_VEC_WF.md]):

    - typing, introduction and the computation rules of [Vec] and [Wf]
      translate (§1, §2), levels through [lmax l 0 ≈ l];
    - the eliminator translates, β on open data included, with its motive
      moved to the generic index by [Unit]'s η at layer D (§3), which
      layer C does not have: there the two indices are different types
      (§4, [generic_index_not_C]);
    - [nth]'s tail equation [nth(S k; cs; inr j) ≡ nth(k; snd cs; j)] holds
      at a neutral [k] (§5, [nth_tail]); [dnth]'s, which [elim_IWf]'s
      induction hypothesis reads through, is not a conversion
      ([dnth_tail_not_conv], through the algorithm's completeness).

    Against a [.vos] tree, [Print Assumptions] lists the tree's lemmas
    that this file uses ([ac_complete_tm], the determinism of reduction)
    as axioms, because [-vok] loads their statements only; they are
    proved in the tree.

    Compile against the built tree or a restored [.vos] tree:
    [coqc -Q theories DeLaM -Q probes Probes -vos probes/IwfCheck.v], then
    [coqc -Q theories DeLaM -Q probes Probes -vok probes/PruneVecWf.v]. *)
From DeLaM.Typing Require Import RecWfBase IWfIH PresupAux StaticCodeEq.
From DeLaM.Validity Require Import RecReduct DeclConsequencesP AlgComplete.
From Probes Require Import IwfCheck.
Import Relation_Operators.

(** ** The generic instance

    [ΓW]: [a : Ty 0, nf : El a → Nat]. The shape [S0] in [ΓW], the arity
    [N0] in [ΓW, x : S0]. *)
Notation ΓW := (cnil ,, tyU L0 @ lsuc L0 ,, tyPi L0 L0 (tyEl L0 (var 0)) tyNat @ LL).
Notation S0 := (tyEl L0 (var 1)).                                              (* ΓW *)
Notation N0 := (app (var 1) L0 L0 (tyEl L0 (var 2)) tyNat (var 0)).            (* ΓW, x *)

(** Today's [Wf], and its translation [τWf] at index [m], at depth [k]
    past [ΓW]. [Ot] and [C] are the closed [⟨⟩], so they need no shift. *)
Notation Wf k := (tyWf L0 S0⟨rshift k⟩ N0⟨rlift (rshift k)⟩).
Notation τWf k m := (tyIWf L0 L0 U0 S0⟨rshift k⟩ N0⟨rlift (rshift k)⟩ tt0 tt0 m).
Notation supf k a cs := (tmSupf L0 S0⟨rshift k⟩ N0⟨rlift (rshift k)⟩ a cs).
Notation τsupf k a cs := (tmSupi L0 L0 U0 S0⟨rshift k⟩ N0⟨rlift (rshift k)⟩ tt0 tt0 a cs).

Section Probe.
Context {G : gctx} (HG : [ ⊢ G ]).

(** ** 1. [Vec] as [DVec] at a constant family

    [ΓV]: [a : Ty 0, n : Nat]. [Vec^0(El a; n)] is [DVec^0(n; _. El a)];
    its successor reduct is [Σ(El a). DVec(n; _. El a)], [eqty_vec_succ]'s
    right-hand side translated. *)
Notation ΓV := (cnil ,, tyU L0 @ lsuc L0 ,, tyNat @ L0).

Lemma vec_as_dvec_ty : [ G ; ΓV ⊢[ lD ] tyDVec L0 (var 0) (tyEl L0 (var 2)) @ L0 ].
Proof. pty. Qed.

Lemma vec_as_dvec_zero : [ G ; ΓV ⊢[ lD ] tyDVec L0 zero (tyEl L0 (var 2)) ≅ tyUnit L0 @ L0 ].
Proof. pconv. Qed.

Lemma vec_as_dvec_succ : [ G ; ΓV ⊢[ lD ]
  tyDVec L0 (succ (var 0)) (tyEl L0 (var 2))
  ≅ tySig L0 L0 (tyEl L0 (var 1)) (tyDVec L0 (var 1) (tyEl L0 (var 3))) @ L0 ].
Proof. pconv. Qed.

(** ** 2. [Wf] as [IWf] at [Unit]: formation, introduction

    The translated type lives at [lmax 0 0]; [wft_lconv] takes it to [0],
    [Wf]'s level. *)
Lemma wf_as_iwf_ty : [ G ; ΓW ⊢[ lD ] τWf 0 tt0 @ L0 ].
Proof. pty. Qed.

(** [supf a cs] with [cs : Vec^0(Wf; N[a])] translated to [DVec^0(N[a]; _. τWf)]:
    [supi]'s children are at [DVec^{0 ⊔ 0}(N[a]; k. τWf(C[a,k]))], which
    the checker meets by conversion ([C] is [⟨⟩] after substitution, the
    level by [lmax 0 0 ≈ 0]). *)
Notation ΓS := (ΓW ,, S0 @ L0 ,, tyDVec L0 N0 (τWf 2 tt0) @ L0).

Lemma supf_as_supi : [ G ; ΓS ⊢[ lD ] τsupf 2 (var 1) (var 0) : τWf 2 tt0 @ L0 ].
Proof. ptm. Qed.


(** ** 3. [elim_Wf] as [elim_IWf]: the motive moves to the generic index

    [elim_IWf]'s motive is over [Γ, j : Unit, z : τWf(j)], [elim_Wf]'s
    over [Γ, z : Wf]. The translated motive is the old one, weakened past
    [j], and it has to be retyped with [z] at [τWf(j)] where it had
    [τWf(⟨⟩)]. At layer D [Unit]'s η makes [j ≡ ⟨⟩], so every motive
    retypes. The motive below needs it: it applies a context function
    [f : τWf(⟨⟩) → Nat] to [z].

    [ΓE]: [ΓW, f : τWf(⟨⟩) → Nat, t : τWf(⟨⟩)]. The motive
    [M(z) := Fin(f z) → Fin(f z)], the step the identity. *)
Notation ΓE := (ΓW ,, tyPi LL L0 (τWf 0 tt0) tyNat @ LL ,, τWf 1 tt0 @ LL).
Notation ME := (tyPi L0 L0 (tyFin (app (var 3) LL L0 (τWf 4 tt0) tyNat (var 0)))
                  (tyFin (app (var 4) LL L0 (τWf 5 tt0) tyNat (var 1)))).          (* ΓE, j, z *)
Notation cE := (lam L0 L0 (tyFin (app (var 4) LL L0 (τWf 5 tt0) tyNat (τsupf 5 (var 2) (var 1))))
                  (var 0)).                                                         (* ΓE, a, cs, ih *)
Notation τelim k M c m t := (tmElimIWf L0 L0 L0 U0 S0⟨rshift k⟩ N0⟨rlift (rshift k)⟩ tt0 tt0 M c m t).

(** The motive at the generic index: [z : τWf(j)] goes where [τWf(⟨⟩)] is
    expected, through [j ≡ ⟨⟩ : Unit]. *)
Lemma motive_retypes : [ G ; ΓE ,, U0 @ L0 ,, τWf 3 (var 0) @ LL ⊢[ lD ] ME @ L0 ].
Proof. pty. Qed.

Lemma elim_as_elimIWf : [ G ; ΓE ⊢[ lD ] τelim 2 ME cE tt0 (var 0)
  : tyPi L0 L0 (tyFin (app (var 1) LL L0 (τWf 2 tt0) tyNat (var 0)))
      (tyFin (app (var 2) LL L0 (τWf 3 tt0) tyNat (var 1))) @ L0 ].
Proof. ptm. Qed.

(** [elim_Wf]'s β translated: on [supi a cs] with [a], [cs] open, the
    eliminator is the step at [a], [cs] and [iwfIH]. *)
Notation ΓB := (ΓE ,, S0⟨rshift 2⟩ @ L0 ,, tyDVec L0 N0⟨rlift (rshift 2)⟩ (τWf 4 tt0) @ L0).

Lemma elim_as_elimIWf_beta : [ G ; ΓB ⊢[ lD ] τelim 4 ME⟨rlift (rlift (rshift 2))⟩
    cE⟨rlift (rlift (rlift (rshift 2)))⟩ tt0 (τsupf 4 (var 1) (var 0))
  ≅ lam L0 L0 (tyFin (app (var 3) LL L0 (τWf 4 tt0) tyNat (τsupf 4 (var 1) (var 0)))) (var 0)
  : tyPi L0 L0 (tyFin (app (var 3) LL L0 (τWf 4 tt0) tyNat (τsupf 4 (var 1) (var 0))))
      (tyFin (app (var 4) LL L0 (τWf 5 tt0) tyNat (τsupf 5 (var 2) (var 1)))) @ L0 ].
Proof. ptmconv. Qed.

(** ** 4. Layer C has no [Unit]-η: the motive does not move there

    At layer D the generic index converts with [⟨⟩] (Unit's η), which is
    what [motive_retypes] used. At layer C equality is syntactic up to
    levels (the Static Code Lemma, [static_code_eqty]), so [τWf(j)] and
    [τWf(⟨⟩)] are different types there, and a motive that uses [z] where
    the fixed instance is expected (as [ME] does, or [Id(Wf; z; w)] for a
    [w] of the context) has no [elim_IWf] spelling at C. *)
Lemma generic_index_D : [ G ; ΓW ,, U0 @ L0 ⊢[ lD ] τWf 1 (var 0) ≅ τWf 1 tt0 @ LL ].
Proof. pconv. Qed.

Lemma generic_index_not_C {Γ l} : ~ [ G ; Γ ⊢[ lC ] τWf 1 (var 0) ≅ τWf 1 tt0 @ l ].
Proof.
  intros H. apply static_code_eqty in H; [| unfold lle; cbn; lia].
  cbn in H. repeat match goal with H : _ /\ _ |- _ => destruct H as [? H] end.
  all: assumption || tauto.
Qed.

End Probe.

(** ** 5. [nth]'s tail equation, and [dnth]'s

    [ΓT]: [a : Ty 0, k : Nat, cs : Vec^0(El a; S k), j : Fin k], with [k]
    a variable. Today [nth(S k; cs; inr j)] unfolds, by [natrec]'s β at
    the successor, a [λ]-β pair and [case]'s β, to [nth(k; snd cs; j)]
    itself: the same [natrec], at the same motive, at [k]. *)
Notation ΓT := (cnil ,, tyU L0 @ lsuc L0 ,, tyNat @ L0 ,, tyVec L0 (tyEl L0 (var 1)) (succ (var 0)) @ L0
                ,, tyFin (var 1) @ L0).
Notation ElA := (tyEl L0 (var 3)).                                                     (* ΓT *)
Notation inrj := (tmInr L0 L0 (tyUnit L0) (tyFin (var 2)) (var 0)).                   (* ΓT *)
Notation sndcs := (tmSnd L0 L0 ElA (tyVec L0 (tyEl L0 (var 4)) (var 3)) (var 1)).      (* ΓT *)

Section Tail.
Context {G : gctx} (HG : [ ⊢ G ]).

Lemma nth_tail : [ G ; ΓT ⊢[ lD ] tmNth L0 ElA (succ (var 2)) (var 1) inrj
                   ≅ tmNth L0 ElA (var 2) sndcs (var 0) : ElA @ L0 ].
Proof.
  assert (HL : [ G ; ΓT ⊢[ lD ] tmNth L0 ElA (succ (var 2)) (var 1) inrj : ElA @ L0 ])
    by (eapply (nth_wf (G := G) (i := lD) eq_refl lD_not_lV); pgoal).
  assert (HR : [ G ; ΓT ⊢[ lD ] tmNth L0 ElA (var 2) sndcs (var 0) : ElA @ L0 ])
    by (eapply (nth_wf (G := G) (i := lD) eq_refl lD_not_lV); pgoal).
  eapply tconv_red_l; [ unfold tmNth, nthMot, nthBase, nthStep; whr | exact HL | ].
  unfold tmNth, nthMot, nthBase, nthStep in HR |- *. pn_in HR. pn.
  apply eqtm_refl. exact HR.
Qed.

End Tail.

(** [dnth] at a constant family over [DVec^0(S k; _. El a)]: its unfolding
    at [inr j] is the [natrec] at [k] whose motive embeds [Fin k̂] into
    [Fin (S k)], applied to the embedding [λy. inr y]; [dnth(k; snd cs; j)]
    is the [natrec] at [k] whose motive embeds into [Fin k], applied to
    the identity. Both are stuck on [k]. The conversion algorithm compares
    two stuck [natrec]s by their motives ([actmne_natrec]), and
    [Fin (S k)] (a sum after one step) never meets [Fin k] (neutral), so
    by the algorithm's completeness ([ac_complete_tm]) the tail equation
    is not a conversion. [ΓD]: [a : Ty 0, k : Nat, cs : DVec^0(S k; _. El a),
    j : Fin k]. *)
Lemma fin_succ_not_fin {G Γ ν} : whne ν -> ~ ac_ty G Γ (tyFin (succ ν)) (tyFin ν).
Proof.
  intros Hn H. inversion H as [? ? ? ? W W' R R' HW HW' Hnf]; subst.
  assert (W = tySum lzero lzero (tyUnit lzero) (tyFin ν)) as ->.
  { eapply reds_ty_whnf_det; [exact R | eapply rt1n_trans; [apply red_fin_succ | apply rt1n_refl] | exact HW | apply whnf_tySum]. }
  assert (W' = tyFin ν) as ->.
  { eapply reds_ty_whnf_det; [exact R' | apply rt1n_refl | exact HW' | apply whnf_ty_ne, whne_tyFin, Hn]. }
  inversion Hnf; subst. match goal with H : ac_tyne _ _ _ _ |- _ => inversion H end.
Qed.

Ltac ac_whnf_pi H :=
  let Rd := fresh in let Rd' := fresh in let HW := fresh in let HW' := fresh in let Hnf := fresh in
  inversion H as [? ? ? ? ? ? Rd Rd' HW HW' Hnf]; subst;
  rewrite (reds_ty_whnf_det _ _ _ Rd (rt1n_refl _ _ _) HW (whnf_tyPi _ _ _ _)) in Hnf;
  rewrite (reds_ty_whnf_det _ _ _ Rd' (rt1n_refl _ _ _) HW' (whnf_tyPi _ _ _ _)) in Hnf;
  inversion Hnf; subst; try match goal with H : ac_tyne _ _ _ _ |- _ => inversion H end.

Lemma emb_mot_ne {G Γ l1 l2 l3 l4 m1 m2 m3 m4 D D' R R' ν} : whne ν ->
  ~ ac_ty G Γ (tyPi l1 l2 (tyPi m1 m2 D (tyFin (succ ν))) R) (tyPi l3 l4 (tyPi m3 m4 D' (tyFin ν)) R').
Proof.
  intros Hn H. ac_whnf_pi H.
  match goal with Hd : ac_ty _ _ (tyPi _ _ _ _) _ |- _ => ac_whnf_pi Hd end.
  match goal with Hc : ac_ty _ _ (tyFin (succ _)) _ |- _ => exact (fin_succ_not_fin Hn Hc) end.
Qed.

Lemma ne_app_inv {G Γ f f' l1 l2 l3 l4 A A' B B' s s' T} :
  ac_tmne G Γ (app f l1 l2 A B s) (app f' l3 l4 A' B' s') T -> exists T', ac_tmne G Γ f f' T'.
Proof.
  intros H; inversion H; subst.
  match goal with H : ac_tmnee _ _ _ _ _ |- _ => inversion H; subst; eauto end.
Qed.

Lemma ne_natrec_inv {G Γ l l' M M' s s' z z' ν ν' T} :
  ac_tmne G Γ (natrec l M s z ν) (natrec l' M' s' z' ν') T -> ac_ty G (Γ ,, tyNat @ lzero) M M'.
Proof. intros H; inversion H; subst; assumption. Qed.

Notation ΓD := (cnil ,, tyU L0 @ lsuc L0 ,, tyNat @ L0 ,, tyDVec L0 (succ (var 0)) (tyEl L0 (var 2)) @ L0
                ,, tyFin (var 1) @ L0).
Notation FA := (tyEl L0 (var 4)).
Notation sndcsD := (tmSnd L0 L0 (tyEl L0 (var 3)) (tyDVec L0 (var 3) (tyEl L0 (var 5))) (var 1)).

Theorem dnth_tail_not_conv {G} :
  ~ [ G ; ΓD ⊢[ lD ] tmDNth L0 (succ (var 2)) FA (var 1) inrj ≅ tmDNth L0 (var 2) FA sndcsD (var 0)
      : tyEl L0 (var 3) @ L0 ].
Proof.
  intros H. apply (ac_complete_tm compt_D) in H.
  inversion H as [? ? ? ? ? ? ? W RT HW R R' Hw Hw' Hnf]; subst.
  eassert (R1 : reds (tmDNth L0 (succ (var 2)) FA (var 1) inrj) _) by whr.
  eassert (R2 : reds (tmDNth L0 (var 2) FA sndcsD (var 0)) _) by whr.
  rewrite (reds_whnf_det _ _ _ R R1 Hw ltac:(repeat constructor)) in Hnf.
  rewrite (reds_whnf_det _ _ _ R' R2 Hw' ltac:(repeat constructor)) in Hnf.
  rewrite (reds_ty_whnf_det _ _ _ RT (rt1n_refl _ _ _) HW ltac:(repeat constructor)) in Hnf.
  inversion Hnf; subst.
  match goal with H : ac_tmnee _ _ _ _ _ |- _ => inversion H as [? ? ? ? ? ? Hne _ _]; subst end.
  apply ne_app_inv in Hne as [? Hne]. apply ne_app_inv in Hne as [? Hne]. apply ne_app_inv in Hne as [? Hne].
  apply ne_natrec_inv in Hne. revert Hne. pn.
  apply emb_mot_ne. repeat constructor.
Qed.
