(** * IWf lowerings, in the formalization's own rules

    Heather's [docs/iwf-former-design.md] §8 lowers a surface inductive
    family [D : I → Type] to one [IWf] (§8.1), lifts route 2b's F1–F3
    (§8.2) and inverts at a constructor-headed index by casing the motive
    on the index (§8.3, tier 1, form A). §12.1 (a parameterized or
    container index type) and §12.2 (a mutual pair as one family over
    [Σ(tag). I_tag]) are open. [IwfProbe.v] checks the lowerings in plain
    Coq; this probe checks them in the formalization's syntax, at layer D,
    with the M17b rules ([wft_iwf], [wf_supi], [wf_elimIWf],
    [eqtm_elimIWf_supi]) and nothing else: every judgment below is a
    derivation of [Typing/Declarative.v], and every computation a
    conversion it derives (through [Preservation]'s soundness of
    reduction, whose β for [elim_IWf] is the declarative one).

    The families are written in de Bruijn syntax over a concrete context
    whose variables are the parameters and the open data, so that
    substitutions compute by [cbn] and a small syntax-directed checker
    ([pt], below) finds the derivations. See [probes/README.md] for the
    findings. Compile against the built tree:
    [coqc -Q theories DeLaM probes/IwfLowering.v]. *)
From DeLaM.Typing Require Import RecWfBase IWfIH.
From DeLaM.Validity Require Import RecReduct DeclConsequencesP AlgComplete.

Notation L0 := lzero.
Notation LL := (lmax lzero lzero).
Notation U0 := (tyUnit lzero).
Notation tt0 := (tmTriv lzero).

(** ** Normalization of the concrete syntax *)

(** Substitutions and renamings computed through concrete terms. [pn]
    keeps [dnth] folded (it appears only in the step telescope, which the
    generic lemmas type); [rn], for reduction, unfolds it. *)
Ltac pn :=
  try unfold iwfFam;
  lazy [typeof ren Ren_ty Ren_tm Ren_lsub subst Subst_ty Subst_tm Subst_lsub ren_ty ren_tm lren r2l rdrop
       rshift1 rlift rup lcons' rlk subst_ty subst_tm lcomp lnorm ldrop llift llk lsingle lsingle2 lsingle3
       lsucc Nat.eqb Nat.add iwfFam].
Ltac pn_in H :=
  try unfold iwfFam in H;
  lazy [typeof ren Ren_ty Ren_tm Ren_lsub subst Subst_ty Subst_tm Subst_lsub ren_ty ren_tm lren r2l rdrop
       rshift1 rlift rup lcons' rlk subst_ty subst_tm lcomp lnorm ldrop llift llk lsingle lsingle2 lsingle3
       lsucc Nat.eqb Nat.add iwfFam] in H.
Ltac rn :=
  try unfold iwfFam, tmDNth, dnthMot, dnthBase, dnthStep, dnthEmb, dnthFam, dnthRes, dnthFamS;
  lazy [typeof ren Ren_ty Ren_tm Ren_lsub subst Subst_ty Subst_tm Subst_lsub ren_ty ren_tm lren r2l rdrop
       rshift1 rlift rup lcons' rlk subst_ty subst_tm lcomp lnorm ldrop llift llk lsingle lsingle2 lsingle3
       lsucc Nat.eqb Nat.add iwfFam tmDNth dnthMot dnthBase dnthStep dnthEmb dnthFam dnthRes dnthFamS].

(** ** Weak-head reduction, stepped *)

Ltac rs1 := first
  [ apply red_natrec_zero | apply red_natrec_succ | apply red_beta | apply red_fst_beta | apply red_snd_beta
  | apply red_case_inl | apply red_case_inr | apply red_elimIWf_supi
  | apply red_natrec; rs1 | apply red_app; rs1 | apply red_fst; rs1 | apply red_snd; rs1
  | apply red_case; rs1 | apply red_elimIWf; rs1 | apply red_elimEmpty; rs1 ].
Ltac rsty1 := first
  [ apply red_El_nat | apply red_El_U | apply red_El_pi | apply red_El_sig | apply red_El_unit
  | apply red_El_empty | apply red_El_sum | apply red_El_fin | apply red_El_iwf | apply red_El_dvec
  | apply red_fin_zero | apply red_fin_succ | apply red_dvec_zero | apply red_dvec_succ
  | apply red_El; rs1 | apply red_fin; rs1 | apply red_dvec; rs1 ].
(** [reds t ?w] to the weak-head normal form. *)
Ltac whr := rn; repeat (eapply Relation_Operators.rt1n_trans; [rs1 | rn]); apply Relation_Operators.rt1n_refl.
Ltac whr_ty := rn; repeat (eapply Relation_Operators.rt1n_trans; [rsty1 | rn]); apply Relation_Operators.rt1n_refl.
Ltac is_red t := assert_succeeds (eassert (red t _) by (rn; rs1)).
Ltac is_red_ty T := assert_succeeds (eassert (red_ty T _) by (rn; rsty1)).


(** ** Vec, as an [IWf] over [Nat] (§8.1)

    [vnil : V 0], [vcons(n, y : El a, xs : V n) : V (S n)], over the code
    [a : Ty 0], the only entry of [ΓA]. The shape is the tag's sum of the
    payload records, and [vcons]'s payload stores its child's index [n]:
    [Unit + Σ(n : Nat). El a]. The arity, the output index and the child
    index each case on the tag. Everything is stated at depth [k], the
    number of entries the context has past [ΓA]. *)
Notation ΓA := (cnil ,, tyU L0 @ lsuc L0).
Notation vPay := (tySig L0 L0 tyNat (tyEl L0 (var 1))).                     (* ΓA *)
Notation vS := (tySum L0 L0 U0 vPay).                                       (* ΓA *)
Notation vN := (tmCase L0 L0 L0 U0 vPay⟨↑⟩ tyNat zero (succ zero) (var 0)).  (* ΓA, x *)
Notation vO := (tmCase L0 L0 L0 U0 vPay⟨↑⟩ tyNat zero
                  (succ (tmFst L0 L0 tyNat (tyEl L0 (var 3)) (var 0))) (var 0)). (* ΓA, x *)
Notation vC := (tmCase L0 L0 L0 U0 vPay⟨↑⟩⟨↑⟩ tyNat zero
                  (tmFst L0 L0 tyNat (tyEl L0 (var 4)) (var 0)) (var 1)).   (* ΓA, x, i *)
Notation V k m := (tyIWf L0 L0 tyNat vS⟨rshift k⟩ vN⟨rlift (rshift k)⟩ vO⟨rlift (rshift k)⟩
                     vC⟨rlift (rlift (rshift k))⟩ m).
Notation vsupi k a cs := (tmSupi L0 L0 tyNat vS⟨rshift k⟩ vN⟨rlift (rshift k)⟩ vO⟨rlift (rshift k)⟩
                            vC⟨rlift (rlift (rshift k))⟩ a cs).
Notation vnil k := (vsupi k (tmInl L0 L0 U0 vPay⟨rshift k⟩ tt0) (tmTriv LL)).
Notation vcons k n y xs :=
  (vsupi k (tmInr L0 L0 U0 vPay⟨rshift k⟩ (tmPair L0 L0 tyNat (tyEl L0 (var (S k))) n y))
     (tmPair LL LL (V k n) (tyUnit LL) xs (tmTriv LL))).

(** [vhead], by form A: the motive cases on the index by [Nat]'s
    eliminator into [Ty 0] (a large elimination, through the codes):
    [El(natrec(⌜Unit⌝; _ _. a; j))]. In the step, the [inl] arm is at
    index [0] and gets [Unit]; the [inr] arm is at [S n] and gets [a],
    its payload's second component. [d] is the depth of the step's
    context. *)
Notation Mhead d j := (tyEl L0 (natrec (lsuc L0) (tyU L0) (tmUnit L0) (var (d + 2)) j)).
Notation headStep d := (tmCase L0 L0 L0 U0 vPay⟨rshift d⟩ (Mhead (S d) vO⟨rlift (rshift d)⟩) tt0
                          (tmSnd L0 L0 tyNat (tyEl L0 (var (d + 2))) (var 0)) (var 2)).
Notation vhead k m t := (tmElimIWf L0 L0 L0 tyNat vS⟨rshift k⟩ vN⟨rlift (rshift k)⟩ vO⟨rlift (rshift k)⟩
                           vC⟨rlift (rlift (rshift k))⟩ (Mhead (k + 2) (var 1)) (headStep (k + 3)) m t).

(** [len], whose step needs the children's induction hypothesis at a
    literal position. The arity is a function of the shape, so the step
    cases on the shape first and passes the induction hypothesis through
    the case (the convoy): the case's motive is
    [Π(_ : Π(i : Fin N[z]). Nat). Nat]. *)
Notation lenIH d := (tyPi L0 L0 (tyFin vN⟨rlift (rshift d)⟩) tyNat).
Notation lenStep d :=
  (app (tmCase L0 L0 LL U0 vPay⟨rshift d⟩ (tyPi LL L0 (lenIH d) tyNat)
          (lam LL L0 (tyPi L0 L0 (tyFin zero) tyNat) zero)
          (lam LL L0 (tyPi L0 L0 (tyFin (succ zero)) tyNat)
             (succ (app (var 0) L0 L0 (tyFin (succ zero)) tyNat (tmInl L0 L0 U0 (tyFin zero) tt0))))
          (var 2))
     LL L0 (tyPi L0 L0 (tyFin vN⟨rlift (rshift d)⟩[lsingle (var 2)]) tyNat) tyNat (var 0)).
Notation len k m t := (tmElimIWf L0 L0 L0 tyNat vS⟨rshift k⟩ vN⟨rlift (rshift k)⟩ vO⟨rlift (rshift k)⟩
                         vC⟨rlift (rlift (rshift k))⟩ tyNat (lenStep (k + 3)) m t).

Section Probe.
Context {G : gctx} (HG : [ ⊢ G ]).

Let Hv : lD <> lV. Proof. discriminate. Qed.

Ltac lvok := cbn; repeat split; try lia.

(** ** Rule wrappers: a level conversion and a type conversion around a rule *)

Lemma wf_cl {Γ t T T' l l'} : [ G ; Γ ⊢[ lD ] t : T' @ l' ] -> lequiv (gL G) l l' ->
  T' = T \/ [ G ; Γ ⊢[ lD ] T ≅ T' @ l ] -> [ G ; Γ ⊢[ lD ] t : T @ l ].
Proof using.
  intros H Hl [<- | E]; [exact (wf_lconv _ _ _ _ _ _ _ H Hl) |].
  exact (wf_conv _ _ _ _ _ _ _ (wf_lconv _ _ _ _ _ _ _ H Hl) E).
Qed.
Lemma eqtm_cl {Γ t t' T T' l l'} : [ G ; Γ ⊢[ lD ] t ≅ t' : T' @ l' ] -> lequiv (gL G) l l' ->
  T' = T \/ [ G ; Γ ⊢[ lD ] T ≅ T' @ l ] -> [ G ; Γ ⊢[ lD ] t ≅ t' : T @ l ].
Proof using.
  intros H Hl [<- | E]; [exact (eqtm_lconv _ _ _ _ _ _ _ _ H Hl) |].
  exact (eqtm_conv _ _ _ _ _ _ _ _ (eqtm_lconv _ _ _ _ _ _ _ _ H Hl) E).
Qed.

(** Conversion through weak-head normal forms (soundness of reduction). *)
Lemma conv_red_l {Γ T T' W l} : reds_ty T W -> [ G ; Γ ⊢[ lD ] T @ l ] ->
  [ G ; Γ ⊢[ lD ] W ≅ T' @ l ] -> [ G ; Γ ⊢[ lD ] T ≅ T' @ l ].
Proof using.
  intros R H E. exact (eqty_trans _ _ _ _ _ _ _ (reds_sound_ty rec_red_typed compt_D H R) E).
Qed.
Lemma conv_red_r {Γ T T' W' l} : reds_ty T' W' -> [ G ; Γ ⊢[ lD ] T' @ l ] ->
  [ G ; Γ ⊢[ lD ] T ≅ W' @ l ] -> [ G ; Γ ⊢[ lD ] T ≅ T' @ l ].
Proof using.
  intros R H E. exact (eqty_trans _ _ _ _ _ _ _ E (eqty_sym _ _ _ _ _ _ (reds_sound_ty rec_red_typed compt_D H R))).
Qed.
Lemma tconv_red_l {Γ t t' w T l} : reds t w -> [ G ; Γ ⊢[ lD ] t : T @ l ] ->
  [ G ; Γ ⊢[ lD ] w ≅ t' : T @ l ] -> [ G ; Γ ⊢[ lD ] t ≅ t' : T @ l ].
Proof using.
  intros R H E. exact (eqtm_trans _ _ _ _ _ _ _ _ (reds_sound_tm rec_red_typed compt_D H R) E).
Qed.
Lemma tconv_red_r {Γ t t' w' T l} : reds t' w' -> [ G ; Γ ⊢[ lD ] t' : T @ l ] ->
  [ G ; Γ ⊢[ lD ] t ≅ w' : T @ l ] -> [ G ; Γ ⊢[ lD ] t ≅ t' : T @ l ].
Proof using.
  intros R H E.
  exact (eqtm_trans _ _ _ _ _ _ _ _ E (eqtm_sym _ _ _ _ _ _ _ (reds_sound_tm rec_red_typed compt_D H R))).
Qed.

(** ** [elim_IWf] from its signature, motive and step

    The motive's scrutinee type, the children's type and the induction
    hypothesis's type are [wf_elimIWf]'s premises; they follow from the
    signature and the motive ([IWfIH]). The step is typed in its own
    context, which the same lemmas give. *)
Section Elim.
Context {Γ : ctx} {l' : lvl} {X A M : ty} {N Ot C c : tm}.
Hypothesis (HX : [ G ; Γ ⊢[ lD ] X @ L0 ]) (HA : [ G ; Γ ⊢[ lD ] A @ L0 ])
  (HN : [ G ; Γ ,, A @ L0 ⊢[ lD ] N : tyNat @ L0 ]) (HO : [ G ; Γ ,, A @ L0 ⊢[ lD ] Ot : X⟨↑⟩ @ L0 ])
  (HC : [ G ; Γ ,, A @ L0 ,, tyFin N @ L0 ⊢[ lD ] C : X⟨↑⟩⟨↑⟩ @ L0 ]) (Hl' : lwf (gL G) l')
  (HM : [ G ; Γ ,, X @ L0 ,, iwfmotty L0 L0 X A N Ot C @ LL ⊢[ lD ] M @ l' ]).

Let HS : IWfSig (G := G) (i := lD) Γ L0 L0 X A N Ot C.
Proof. repeat split; assumption. Qed.

Lemma step_ctx : [ G ; Γ ,, A @ L0 ,, iwfcsty L0 L0 X A N Ot C @ LL
                   ,, iwfihty L0 L0 l' X A N Ot C M @ lmax L0 l' ⊢[ lD ] ].
Proof using HX HA HN HO HC Hl' HM.
  pose proof (IWf_cs_wf (i := lD) eq_refl Hv HS) as Hcs.
  pose proof (IWf_ihty_wf (i := lD) eq_refl Hv HS Hl' HM) as Hih.
  apply wfc_ext; [apply wfc_ext; [| exact Hcs | lvok] | exact Hih | split; [exact I | exact Hl']].
  apply wfc_ext; [exact (ctx_of_wf_ty eq_refl HA) | exact HA | exact I].
Qed.

Hypothesis (Hc : [ G ; Γ ,, A @ L0 ,, iwfcsty L0 L0 X A N Ot C @ LL
                   ,, iwfihty L0 L0 l' X A N Ot C M @ lmax L0 l' ⊢[ lD ] ] ->
                 [ G ; Γ ,, A @ L0 ,, iwfcsty L0 L0 X A N Ot C @ LL
                   ,, iwfihty L0 L0 l' X A N Ot C M @ lmax L0 l' ⊢[ lD ] c : iwfstepty L0 L0 X A N Ot C M @ l' ]).

Lemma elimIWf_wf {m t} : [ G ; Γ ⊢[ lD ] m : X @ L0 ] -> [ G ; Γ ⊢[ lD ] t : tyIWf L0 L0 X A N Ot C m @ LL ] ->
  [ G ; Γ ⊢[ lD ] tmElimIWf L0 L0 l' X A N Ot C M c m t : M[lsingle2 m t] @ l' ].
Proof using HX HA HN HO HC Hl' HM Hc.
  intros Hm Ht. apply wf_elimIWf; try assumption; try exact I.
  - exact (IWf_mot_wf (i := lD) eq_refl Hv HS).
  - exact (IWf_cs_wf (i := lD) eq_refl Hv HS).
  - exact (IWf_ihty_wf (i := lD) eq_refl Hv HS Hl' HM).
  - exact (Hc step_ctx).
Qed.

(** β at a [sup_i], at its output index: [eqtm_elimIWf_supi], its
    induction hypothesis typed by [IWf_IH_wf]. *)
Lemma elimIWf_beta {a cs} : [ G ; Γ ⊢[ lD ] a : A @ L0 ] ->
  [ G ; Γ ⊢[ lD ] cs : tyDVec LL N[lsingle a] (iwfFam L0 L0 X A N Ot C a) @ LL ] ->
  [ G ; Γ ⊢[ lD ] tmElimIWf L0 L0 l' X A N Ot C M c Ot[lsingle a] (tmSupi L0 L0 X A N Ot C a cs)
      ≅ c[lsingle3 a cs (iwfIH L0 L0 l' X A N Ot C M c a cs)]
      : M[lsingle2 Ot[lsingle a] (tmSupi L0 L0 X A N Ot C a cs)] @ l' ].
Proof using HX HA HN HO HC Hl' HM Hc.
  intros Ha Hcs. apply eqtm_elimIWf_supi; try assumption; try lvok; try exact compt_D.
  - exact (IWf_mot_wf (i := lD) eq_refl Hv HS).
  - exact (IWf_cs_wf (i := lD) eq_refl Hv HS).
  - exact (IWf_ihty_wf (i := lD) eq_refl Hv HS Hl' HM).
  - exact (Hc step_ctx).
  - exact (IWf_IH_wf (i := lD) eq_refl Hv HS Hl' HM (IWf_ihty_wf (i := lD) eq_refl Hv HS Hl' HM) (Hc step_ctx) Ha Hcs).
Qed.

(** The induction hypothesis, folded: [IWf_IH_wf]. *)
Lemma elimIH_wf {a cs} : [ G ; Γ ⊢[ lD ] a : A @ L0 ] ->
  [ G ; Γ ⊢[ lD ] cs : tyDVec LL N[lsingle a] (iwfFam L0 L0 X A N Ot C a) @ LL ] ->
  [ G ; Γ ⊢[ lD ] iwfIH L0 L0 l' X A N Ot C M c a cs
      : (iwfihty L0 L0 l' X A N Ot C M)[lsingle2 a cs] @ lmax L0 l' ].
Proof using HX HA HN HO HC Hl' HM Hc.
  intros Ha Hcs.
  exact (IWf_IH_wf (i := lD) eq_refl Hv HS Hl' HM (IWf_ihty_wf (i := lD) eq_refl Hv HS Hl' HM) (Hc step_ctx) Ha Hcs).
Qed.

(** The congruence at one signature, motive and step: the index and the
    scrutinee may differ. *)
Lemma elimIWf_cong {m m' t t'} : [ G ; Γ ⊢[ lD ] m ≅ m' : X @ L0 ] ->
  [ G ; Γ ⊢[ lD ] t ≅ t' : tyIWf L0 L0 X A N Ot C m @ LL ] ->
  [ G ; Γ ⊢[ lD ] tmElimIWf L0 L0 l' X A N Ot C M c m t ≅ tmElimIWf L0 L0 l' X A N Ot C M c m' t'
      : M[lsingle2 m t] @ l' ].
Proof using HX HA HN HO HC Hl' HM Hc.
  intros Hm Ht. pose proof (IWf_ihty_wf (i := lD) eq_refl Hv HS Hl' HM) as Hih.
  apply eqtm_elimIWf; try assumption.
  all: first [ exact Hv | assumption | solve [lvok]
             | exact (IWf_mot_wf (i := lD) eq_refl Hv HS) | exact (IWf_cs_wf (i := lD) eq_refl Hv HS)
             | solve [eapply lequiv_refl; lvok] | exact (lequiv_refl _ _ Hl')
             | apply eqty_refl; assumption | apply eqtm_refl; assumption
             | apply eqtm_refl; exact (Hc step_ctx) ].
Qed.
End Elim.

(** ** The checker

    Syntax directed. Each judgment is proved by its former's rule, wrapped
    in a level conversion and, when the rule's type is not the expected one
    syntactically, a type conversion. Conversions go through weak-head
    normal forms ([whr]) and then structurally. A context's
    well-formedness is proved once, when a judgment first meets it, and
    kept as a hypothesis (rederiving it at each leaf is exponential). *)

Ltac pctx :=
  lazymatch goal with
  | |- [ ?G ; ?Γ ⊢[ ?i ] ] =>
      first [ assumption
            | lazymatch Γ with
              | cnil => apply wfc_nil; assumption
              | ?Γ' ,, ?A @ ?l =>
                  let H := fresh "HΓ" in assert (H : [ G ; Γ' ⊢[ i ] ]) by pctx;
                  apply wfc_ext; [ exact H | pty | lvok ]
              end ]
  end
with ensure :=
  lazymatch goal with
  | |- [ ?G ; ?Γ ⊢[ ?i ] _ @ _ ] => ensure_at G Γ i
  | |- [ ?G ; ?Γ ⊢[ ?i ] _ : _ @ _ ] => ensure_at G Γ i
  | |- [ ?G ; ?Γ ⊢[ ?i ] _ ≅ _ @ _ ] => ensure_at G Γ i
  | |- [ ?G ; ?Γ ⊢[ ?i ] _ ≅ _ : _ @ _ ] => ensure_at G Γ i
  end
with ensure_at G Γ i :=
  first [ lazymatch goal with H : [ G ; Γ ⊢[ i ] ] |- _ => idtac end
        | let H := fresh "HΓ" in assert (H : [ G ; Γ ⊢[ i ] ]) by pctx ]
with pgoal :=
  lazymatch goal with
  | |- _ <> lV => discriminate
  | |- compt _ => exact compt_D
  | |- lwf _ _ => lvok
  | |- lequiv _ _ _ => lalg
  | |- [ _ ; _ ⊢[ _ ] ] => pn; pctx
  | |- [ _ ; _ ⊢[ _ ] ] -> _ => let H := fresh "HΓ" in intro H; pn_in H; pn; pgoal
  | |- [ _ ; _ ⊢[ _ ] _ @ _ ] => pty
  | |- [ _ ; _ ⊢[ _ ] _ : _ @ _ ] => ptm
  | |- [ _ ; _ ⊢[ _ ] _ ≅ _ @ _ ] => pconv
  | |- [ _ ; _ ⊢[ _ ] _ ≅ _ : _ @ _ ] => ptmconv
  | |- in_ctx _ _ _ _ => repeat constructor
  | |- _ = _ \/ _ => first [ left; pn; reflexivity | right; pconv ]
  | |- ?g => idtac "pgoal: no rule for" g; fail
  end
with ty_rule R :=
  eapply wft_lconv; [ eapply R; pgoal | lalg ]
with tm_rule R :=
  eapply wf_cl; [ eapply R; pgoal | lalg | pgoal ]
with pty :=
  pn; ensure;
  lazymatch goal with
  | |- [ _ ; _ ⊢[ _ ] tyNat @ _ ] => ty_rule wft_nat
  | |- [ _ ; _ ⊢[ _ ] tyUnit _ @ _ ] => ty_rule wft_unit
  | |- [ _ ; _ ⊢[ _ ] tyEmpty _ @ _ ] => ty_rule wft_empty
  | |- [ _ ; _ ⊢[ _ ] tyU _ @ _ ] => ty_rule wft_U
  | |- [ _ ; _ ⊢[ _ ] tyEl _ _ @ _ ] => ty_rule wft_El
  | |- [ _ ; _ ⊢[ _ ] tyPi _ _ _ _ @ _ ] => ty_rule wft_pi
  | |- [ _ ; _ ⊢[ _ ] tySig _ _ _ _ @ _ ] => ty_rule wft_sig
  | |- [ _ ; _ ⊢[ _ ] tySum _ _ _ _ @ _ ] => ty_rule wft_sum
  | |- [ _ ; _ ⊢[ _ ] tyFin _ @ _ ] => ty_rule wft_fin
  | |- [ _ ; _ ⊢[ _ ] tyDVec _ _ _ @ _ ] => ty_rule wft_dvec
  | |- [ _ ; _ ⊢[ _ ] tyIWf _ _ _ _ _ _ _ _ @ _ ] => ty_rule wft_iwf
  | |- ?g => idtac "pty: no rule for" g; fail
  end
with ptm :=
  pn; ensure;
  lazymatch goal with
  | |- [ _ ; _ ⊢[ _ ] var _ : _ @ _ ] => tm_rule wf_var
  | |- [ _ ; _ ⊢[ _ ] zero : _ @ _ ] => tm_rule wf_zero
  | |- [ _ ; _ ⊢[ _ ] succ _ : _ @ _ ] => tm_rule wf_succ
  | |- [ _ ; _ ⊢[ _ ] natrec _ _ _ _ _ : _ @ _ ] => tm_rule wf_natrec
  | |- [ _ ; _ ⊢[ _ ] lam _ _ _ _ : tyPi _ _ _ _ @ _ ] => tm_rule wf_lam
  | |- [ _ ; _ ⊢[ _ ] app _ _ _ _ _ _ : _ @ _ ] => tm_rule wf_app
  | |- [ _ ; _ ⊢[ _ ] tmPair _ _ _ _ _ _ : _ @ _ ] => tm_rule wf_pair
  | |- [ _ ; _ ⊢[ _ ] tmFst _ _ _ _ _ : _ @ _ ] => tm_rule wf_fst
  | |- [ _ ; _ ⊢[ _ ] tmSnd _ _ _ _ _ : _ @ _ ] => tm_rule wf_snd
  | |- [ _ ; _ ⊢[ _ ] tmTriv _ : _ @ _ ] => tm_rule wf_triv
  | |- [ _ ; _ ⊢[ _ ] tmInl _ _ _ _ _ : _ @ _ ] => tm_rule wf_inl
  | |- [ _ ; _ ⊢[ _ ] tmInr _ _ _ _ _ : _ @ _ ] => tm_rule wf_inr
  | |- [ _ ; _ ⊢[ _ ] tmCase _ _ _ _ _ _ _ _ _ : _ @ _ ] => tm_rule wf_case
  | |- [ _ ; _ ⊢[ _ ] elimEmpty _ _ _ _ : _ @ _ ] => tm_rule wf_elimEmpty
  | |- [ _ ; _ ⊢[ _ ] tmSupi _ _ _ _ _ _ _ _ _ : _ @ _ ] => tm_rule wf_supi
  | |- [ _ ; _ ⊢[ _ ] tmElimIWf _ _ _ _ _ _ _ _ _ _ _ _ : _ @ _ ] => tm_rule @elimIWf_wf
  | |- [ _ ; _ ⊢[ _ ] iwfIH _ _ _ _ _ _ _ _ _ _ _ _ : _ @ _ ] => tm_rule @elimIH_wf
  | |- [ _ ; _ ⊢[ _ ] tmNat : _ @ _ ] => tm_rule wf_code_nat
  | |- [ _ ; _ ⊢[ _ ] tmUnit _ : _ @ _ ] => tm_rule wf_code_unit
  | |- [ _ ; _ ⊢[ _ ] tmEmpty _ : _ @ _ ] => tm_rule wf_code_empty
  | |- [ _ ; _ ⊢[ _ ] tmSum _ _ _ _ : _ @ _ ] => tm_rule wf_code_sum
  | |- [ _ ; _ ⊢[ _ ] tmSig _ _ _ _ : _ @ _ ] => tm_rule wf_code_sig
  | |- [ _ ; _ ⊢[ _ ] tmFin _ : _ @ _ ] => tm_rule wf_code_fin
  | |- [ _ ; _ ⊢[ _ ] tmIWf _ _ _ _ _ _ _ _ : _ @ _ ] => tm_rule wf_code_iwf
  | |- ?g => idtac "ptm: no rule for" g; fail
  end
with pconv :=
  pn; ensure;
  lazymatch goal with
  | |- [ _ ; _ ⊢[ _ ] ?T ≅ ?T @ _ ] => apply eqty_refl; pty
  | |- [ _ ; _ ⊢[ _ ] ?T ≅ ?T' @ _ ] =>
      tryif is_red_ty T then (eapply conv_red_l; [ whr_ty | pty | pconv ])
      else tryif is_red_ty T' then (eapply conv_red_r; [ whr_ty | pty | pconv ])
      else pconv_nf
  end
with pconv_nf :=
  lazymatch goal with
  | |- [ _ ; _ ⊢[ _ ] tyEl _ _ ≅ tyEl _ _ @ _ ] => eapply eqty_lconv; [ eapply eqty_El; pgoal | lalg ]
  | |- [ _ ; _ ⊢[ _ ] tyIWf _ _ _ _ _ _ _ _ ≅ tyIWf _ _ _ _ _ _ _ _ @ _ ] =>
      eapply eqty_lconv; [ eapply eqty_iwf; pgoal | lalg ]
  | |- [ _ ; _ ⊢[ _ ] tyPi _ _ _ _ ≅ tyPi _ _ _ _ @ _ ] => eapply eqty_lconv; [ eapply eqty_pi; pgoal | lalg ]
  | |- [ _ ; _ ⊢[ _ ] tySig _ _ _ _ ≅ tySig _ _ _ _ @ _ ] => eapply eqty_lconv; [ eapply eqty_sig; pgoal | lalg ]
  | |- [ _ ; _ ⊢[ _ ] tySum _ _ _ _ ≅ tySum _ _ _ _ @ _ ] => eapply eqty_lconv; [ eapply eqty_sum; pgoal | lalg ]
  | |- [ _ ; _ ⊢[ _ ] tyFin _ ≅ tyFin _ @ _ ] => eapply eqty_lconv; [ eapply eqty_fin; pgoal | lalg ]
  | |- [ _ ; _ ⊢[ _ ] tyDVec _ _ _ ≅ tyDVec _ _ _ @ _ ] => eapply eqty_lconv; [ eapply eqty_dvec; pgoal | lalg ]
  | |- [ _ ; _ ⊢[ _ ] tyU _ ≅ tyU _ @ _ ] => eapply eqty_lconv; [ eapply eqty_U; pgoal | lalg ]
  | |- [ _ ; _ ⊢[ _ ] tyUnit _ ≅ tyUnit _ @ _ ] => eapply eqty_lconv; [ eapply eqty_unit; pgoal | lalg ]
  | |- [ _ ; _ ⊢[ _ ] tyEmpty _ ≅ tyEmpty _ @ _ ] => eapply eqty_lconv; [ eapply eqty_empty; pgoal | lalg ]
  | |- ?g => idtac "pconv: no rule for" g; fail
  end
with ptmconv :=
  pn; ensure;
  lazymatch goal with
  | |- [ _ ; _ ⊢[ _ ] ?t ≅ ?t : _ @ _ ] => apply eqtm_refl; ptm
  | |- [ _ ; _ ⊢[ _ ] _ ≅ _ : tyUnit _ @ _ ] => apply eqtm_unit_eta; pgoal
  | |- [ _ ; _ ⊢[ _ ] ?t ≅ ?t' : _ @ _ ] =>
      tryif is_red t then (eapply tconv_red_l; [ whr | ptm | ptmconv ])
      else tryif is_red t' then (eapply tconv_red_r; [ whr | ptm | ptmconv ])
      else ptmconv_nf
  end
with tmeq_rule R :=
  eapply eqtm_cl; [ eapply R; pgoal | lalg | pgoal ]
with ptmconv_nf :=
  lazymatch goal with
  | |- [ _ ; _ ⊢[ _ ] succ _ ≅ succ _ : _ @ _ ] => tmeq_rule eqtm_succ
  | |- [ _ ; _ ⊢[ _ ] tmInl _ _ _ _ _ ≅ tmInl _ _ _ _ _ : _ @ _ ] => tmeq_rule eqtm_inl
  | |- [ _ ; _ ⊢[ _ ] tmInr _ _ _ _ _ ≅ tmInr _ _ _ _ _ : _ @ _ ] => tmeq_rule eqtm_inr
  | |- [ _ ; _ ⊢[ _ ] tmPair _ _ _ _ _ _ ≅ tmPair _ _ _ _ _ _ : _ @ _ ] => tmeq_rule eqtm_pair
  | |- [ _ ; _ ⊢[ _ ] tmFst _ _ _ _ _ ≅ tmFst _ _ _ _ _ : _ @ _ ] => tmeq_rule eqtm_fst
  | |- [ _ ; _ ⊢[ _ ] tmSnd _ _ _ _ _ ≅ tmSnd _ _ _ _ _ : _ @ _ ] => tmeq_rule eqtm_snd
  | |- [ _ ; _ ⊢[ _ ] tmFin _ ≅ tmFin _ : _ @ _ ] => tmeq_rule eqtm_code_fin
  | |- [ _ ; _ ⊢[ _ ] tmSum _ _ _ _ ≅ tmSum _ _ _ _ : _ @ _ ] => tmeq_rule eqtm_code_sum
  | |- [ _ ; _ ⊢[ _ ] tmUnit _ ≅ tmUnit _ : _ @ _ ] => tmeq_rule eqtm_code_unit
  | |- [ _ ; _ ⊢[ _ ] tmElimIWf _ _ _ _ _ _ _ _ _ _ _ _ ≅ tmElimIWf _ _ _ _ _ _ _ _ _ _ _ _ : _ @ _ ] =>
      tmeq_rule @elimIWf_cong
  | |- ?g => idtac "ptmconv: no rule for" g; fail
  end.


(** *** Vec: typing *)

(** [ΓV]: [a : Ty 0, n : Nat, y : El a, xs : V n], all open. *)
Notation ΓV := (ΓA ,, tyNat @ L0 ,, tyEl L0 (var 1) @ L0 ,, V 2 (var 1) @ LL).

Lemma vec_ty : [ G ; ΓA ,, tyNat @ L0 ⊢[ lD ] V 1 (var 0) @ LL ].
Proof. pty. Qed.

Lemma vnil_wf : [ G ; ΓA ⊢[ lD ] vnil 0 : V 0 zero @ LL ].
Proof. ptm. Qed.

Lemma vcons_wf : [ G ; ΓV ⊢[ lD ] vcons 3 (var 2) (var 1) (var 0) : V 3 (succ (var 2)) @ LL ].
Proof. ptm. Qed.

(** *** Vec: β at an open index, and form A *)

Lemma vhead_wf : [ G ; ΓA ,, tyNat @ L0 ,, V 1 (succ (var 0)) @ LL ⊢[ lD ]
                   vhead 2 (succ (var 1)) (var 0) : tyEl L0 (var 2) @ L0 ].
Proof. ptm. Qed.

(** [vhead (vcons n y xs) ≡ y], everything open. *)
Lemma vhead_beta : [ G ; ΓV ⊢[ lD ] vhead 3 (succ (var 2)) (vcons 3 (var 2) (var 1) (var 0)) ≅ var 1
                     : tyEl L0 (var 3) @ L0 ].
Proof. ptmconv. Qed.

Lemma len_wf : [ G ; ΓV ⊢[ lD ] len 3 (var 2) (var 0) : tyNat @ L0 ].
Proof. ptm. Qed.

(** [len (vcons n y xs) ≡ S (len xs)]: β, then the induction hypothesis
    at position [0] reaches the child through [dnth]. *)
Lemma len_beta : [ G ; ΓV ⊢[ lD ] len 3 (succ (var 2)) (vcons 3 (var 2) (var 1) (var 0))
                   ≅ succ (len 3 (var 2) (var 0)) : tyNat @ L0 ].
Proof. ptmconv. Qed.

End Probe.
