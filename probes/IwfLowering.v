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
    substitutions compute by [lazy] and a small syntax-directed checker
    ([pty], [ptm], [pconv], [ptmconv], below) finds the derivations. The
    findings are in [M17_DESIGN.md] ("The generator's lowerings"). Compile
    against the built tree (about 25 minutes, 6 GB of memory):
    [coqc -Q theories DeLaM probes/IwfLowering.v]. *)
From DeLaM.Typing Require Import RecWfBase IWfIH PresupAux.
From DeLaM.Validity Require Import RecReduct DeclConsequencesP AlgComplete.

Notation L0 := lzero.
Notation LL := (lmax lzero lzero).
Notation U0 := (tyUnit lzero).
Notation tt0 := (tmTriv lzero).

(** ** Normalization of the concrete syntax *)

(** Substitutions and renamings computed through concrete terms. [pn]
    keeps [dnth] folded (it appears only in the step telescope, which the
    generic lemmas type); [rn], for reduction, unfolds it. Both keep the
    induction hypothesis [iwfIH] folded, so that a term holding it is typed
    by [IWf_IH_wf] ([elimIH_wf] below) rather than through [dnth]'s
    unfolding. [lazy], not [cbn]: [cbn]'s refolding made [dnth]'s steps
    take minutes. *)
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
  | apply red_case_inl | apply red_case_inr | apply red_elimIWf_supi | apply red_elimWf_supf
  | apply red_natrec; rs1 | apply red_app; rs1 | apply red_fst; rs1 | apply red_snd; rs1
  | apply red_case; rs1 | apply red_elimIWf; rs1 | apply red_elimWf; rs1 | apply red_elimEmpty; rs1 ].
Ltac rsty1 := first
  [ apply red_El_nat | apply red_El_U | apply red_El_pi | apply red_El_sig | apply red_El_unit
  | apply red_El_empty | apply red_El_sum | apply red_El_fin | apply red_El_iwf | apply red_El_dvec | apply red_El_wf
  | apply red_fin_zero | apply red_fin_succ | apply red_dvec_zero | apply red_dvec_succ
  | apply red_vec_zero | apply red_vec_succ
  | apply red_El; rs1 | apply red_fin; rs1 | apply red_dvec; rs1 | apply red_vec; rs1 ].
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

(** ** [elim_Wf] from its shape, arity, motive and step

    For the index type [List A] of §12.1, which tier 0 lowers to [Wf].
    The children's and the induction hypothesis's types follow from
    [PresupAux]. *)
Section ElimWf.
Context {Γ : ctx} {l' : lvl} {A M : ty} {N c : tm}.
Hypothesis (HA : [ G ; Γ ⊢[ lD ] A @ L0 ]) (HN : [ G ; Γ ,, A @ L0 ⊢[ lD ] N : tyNat @ L0 ])
  (Hl' : lwf (gL G) l') (HM : [ G ; Γ ,, tyWf L0 A N @ L0 ⊢[ lD ] M @ l' ]).

Let HW : [ G ; Γ ⊢[ lD ] tyWf L0 A N @ L0 ].
Proof. apply wft_wf; [exact Hv | lvok | exact HA | exact HN]. Qed.
Let Hcs : [ G ; Γ ,, A @ L0 ⊢[ lD ] wfcsty L0 A N @ L0 ].
Proof. exact (Wf_cs_wf (G := G) (i := lD) (l := L0) eq_refl Hv I HW HN). Qed.
Let Hctx2 : [ G ; Γ ,, A @ L0 ,, wfcsty L0 A N @ L0 ⊢[ lD ] ].
Proof.
  apply wfc_ext; [apply wfc_ext; [exact (ctx_of_wf_ty eq_refl HA) | exact HA | lvok] | exact Hcs | lvok].
Qed.
Let Hih : [ G ; Γ ,, A @ L0 ,, wfcsty L0 A N @ L0 ⊢[ lD ] wfihty L0 l' A N M @ lmax L0 l' ].
Proof.
  refine (Wf_ih_wf (G := G) (i := lD) (l := L0) (l' := l') eq_refl Hv I Hl' HW HN HM Hctx2 _ (lequiv_refl (gL G) L0 I)).
  apply eqty_refl; exact Hcs.
Qed.

Lemma wf_step_ctx : [ G ; Γ ,, A @ L0 ,, wfcsty L0 A N @ L0 ,, wfihty L0 l' A N M @ lmax L0 l' ⊢[ lD ] ].
Proof using HA HN Hl' HM. apply wfc_ext; [exact Hctx2 | exact Hih | split; [exact I | exact Hl']]. Qed.

Hypothesis (Hc : [ G ; Γ ,, A @ L0 ,, wfcsty L0 A N @ L0 ,, wfihty L0 l' A N M @ lmax L0 l' ⊢[ lD ] ] ->
                 [ G ; Γ ,, A @ L0 ,, wfcsty L0 A N @ L0 ,, wfihty L0 l' A N M @ lmax L0 l'
                     ⊢[ lD ] c : wfstepty L0 A N M @ l' ]).

Lemma elimWf_wf {t} : [ G ; Γ ⊢[ lD ] t : tyWf L0 A N @ L0 ] ->
  [ G ; Γ ⊢[ lD ] tmElimWf L0 l' A N M c t : M[lsingle t] @ l' ].
Proof using HA HN Hl' HM Hc.
  intros Ht. apply wf_elimWf.
  all: first [ exact Hv | assumption | solve [lvok] | exact (Hc wf_step_ctx) ].
Qed.
End ElimWf.

(** ** The checker

    Syntax directed. Each judgment is proved by its former's rule, wrapped
    in a level conversion and, when the rule's type is not the expected one
    syntactically, a type conversion. Conversions go through weak-head
    normal forms ([whr]) and then structurally. A context's
    well-formedness is proved once, when a judgment first meets it, and
    kept as a hypothesis (rederiving it at each leaf is exponential). *)

(** Hooks for lemmas proved once and reused: a family's type at any index, a signature component in any context. *)
Ltac pfam_ty := fail.
Ltac pfam_tm := fail.
Ltac pfam_conv := fail.

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
  | |- in_ctx ?Γ ?n _ _ =>
      first [ assumption
            | let H := fresh "Hin" in
              eassert (H : in_ctx Γ n _ _) by (repeat apply in_there; first [ apply in_here | eassumption ]);
              exact H ]
  | |- _ = _ \/ _ => first [ left; pn; reflexivity | right; pconv ]
  | |- ?g => idtac "pgoal: no rule for" g; fail
  end
with ty_rule R :=
  eapply wft_lconv; [ eapply R; pgoal | lalg ]
with tm_rule R :=
  eapply wf_cl; [ eapply R; pgoal | lalg | pgoal ]
with pty :=
  pn; ensure; first [ assumption | pfam_ty | pty_r ]
with pty_r :=
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
  | |- [ _ ; _ ⊢[ _ ] tyWf _ _ _ @ _ ] => ty_rule wft_wf
  | |- [ _ ; _ ⊢[ _ ] tyVec _ _ _ @ _ ] => ty_rule wft_vec
  | |- ?g => idtac "pty: no rule for" g; fail
  end
with ptm :=
  pn; ensure; first [ assumption | pfam_tm | ptm_r ]
with ptm_r :=
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
  | |- [ _ ; _ ⊢[ _ ] tmSupf _ _ _ _ _ : _ @ _ ] => tm_rule wf_supf
  | |- [ _ ; _ ⊢[ _ ] tmElimWf _ _ _ _ _ _ _ : _ @ _ ] => tm_rule @elimWf_wf
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
with conv_rule R :=
  eapply eqty_lconv; [ eapply R; pgoal | lalg ]
with pconv_nf := first [ pfam_conv | pconv_r ]
with pconv_r :=
  lazymatch goal with
  | |- [ _ ; _ ⊢[ _ ] tyEl _ _ ≅ tyEl _ _ @ _ ] => eapply eqty_lconv; [ eapply eqty_El; pgoal | lalg ]
  | |- [ _ ; _ ⊢[ _ ] tyIWf _ _ _ _ _ _ _ _ ≅ tyIWf _ _ _ _ _ _ _ _ @ _ ] =>
      eapply eqty_lconv; [ eapply eqty_iwf; pgoal | lalg ]
  | |- [ _ ; _ ⊢[ _ ] tyPi _ _ _ _ ≅ tyPi _ _ _ _ @ _ ] => eapply eqty_lconv; [ eapply eqty_pi; pgoal | lalg ]
  | |- [ _ ; _ ⊢[ _ ] tySig _ _ _ _ ≅ tySig _ _ _ _ @ _ ] => eapply eqty_lconv; [ eapply eqty_sig; pgoal | lalg ]
  | |- [ _ ; _ ⊢[ _ ] tySum _ _ _ _ ≅ tySum _ _ _ _ @ _ ] => eapply eqty_lconv; [ eapply eqty_sum; pgoal | lalg ]
  | |- [ _ ; _ ⊢[ _ ] tyFin _ ≅ tyFin _ @ _ ] => eapply eqty_lconv; [ eapply eqty_fin; pgoal | lalg ]
  | |- [ _ ; _ ⊢[ _ ] tyDVec _ _ _ ≅ tyDVec _ _ _ @ _ ] => eapply eqty_lconv; [ eapply eqty_dvec; pgoal | lalg ]
  | |- [ _ ; _ ⊢[ _ ] tyWf _ _ _ ≅ tyWf _ _ _ @ _ ] => eapply eqty_lconv; [ eapply eqty_wf; pgoal | lalg ]
  | |- [ _ ; _ ⊢[ _ ] tyVec _ _ _ ≅ tyVec _ _ _ @ _ ] => eapply eqty_lconv; [ eapply eqty_vec; pgoal | lalg ]
  | |- [ _ ; _ ⊢[ _ ] tyU _ ≅ tyU _ @ _ ] => eapply eqty_lconv; [ eapply eqty_U; pgoal | lalg ]
  | |- [ _ ; _ ⊢[ _ ] tyUnit _ ≅ tyUnit _ @ _ ] => eapply eqty_lconv; [ eapply eqty_unit; pgoal | lalg ]
  | |- [ _ ; _ ⊢[ _ ] tyEmpty _ ≅ tyEmpty _ @ _ ] => eapply eqty_lconv; [ eapply eqty_empty; pgoal | lalg ]
  | |- ?g => idtac "pconv: no rule for" g; fail
  end
with ptmconv :=
  pn; ensure; first [ assumption | ptmconv_r ]
with ptmconv_r :=
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
  | |- [ _ ; _ ⊢[ _ ] natrec _ _ _ _ _ ≅ natrec _ _ _ _ _ : _ @ _ ] => tmeq_rule eqtm_natrec
  | |- [ _ ; _ ⊢[ _ ] tmSupf _ _ _ _ _ ≅ tmSupf _ _ _ _ _ : _ @ _ ] => tmeq_rule eqtm_supf
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

(** ** F3: a payload field typed by the child's index (§8.2)

    [Cons(n, x : Fin n, xs : V n) : V (S n)]. The payload stores [n], so
    [x : Fin n] is an ordinary dependent field: the shape is
    [Unit + Σ(n : Nat). Fin n]. The family is closed, so its signature
    needs no shifting at any depth. [head3 : V (S n) → Fin n] is form A
    with a result type that depends on the index:
    [El(natrec(⌜Unit⌝; k _. ⌜Fin k⌝; j))]. *)
Notation f3Pay := (tySig L0 L0 tyNat (tyFin (var 0))).
Notation f3S := (tySum L0 L0 U0 f3Pay).
Notation f3N := (tmCase L0 L0 L0 U0 f3Pay tyNat zero (succ zero) (var 0)).
Notation f3O := (tmCase L0 L0 L0 U0 f3Pay tyNat zero (succ (tmFst L0 L0 tyNat (tyFin (var 0)) (var 0))) (var 0)).
Notation f3C := (tmCase L0 L0 L0 U0 f3Pay tyNat zero (tmFst L0 L0 tyNat (tyFin (var 0)) (var 0)) (var 1)).
Notation F3T m := (tyIWf L0 L0 tyNat f3S f3N f3O f3C m).
Notation cons3 n x xs := (tmSupi L0 L0 tyNat f3S f3N f3O f3C
                            (tmInr L0 L0 U0 f3Pay (tmPair L0 L0 tyNat (tyFin (var 0)) n x))
                            (tmPair LL LL (F3T n) (tyUnit LL) xs (tmTriv LL))).
Notation nil3 := (tmSupi L0 L0 tyNat f3S f3N f3O f3C (tmInl L0 L0 U0 f3Pay tt0) (tmTriv LL)).
Notation M3 j := (tyEl L0 (natrec (lsuc L0) (tyU L0) (tmUnit L0) (tmFin (var 1)) j)).
Notation head3Step := (tmCase L0 L0 L0 U0 f3Pay (M3 f3O) tt0 (tmSnd L0 L0 tyNat (tyFin (var 0)) (var 0)) (var 2)).
Notation head3 m t := (tmElimIWf L0 L0 L0 tyNat f3S f3N f3O f3C (M3 (var 1)) head3Step m t).

(** The family at any index, once. *)
Lemma F3T_wf {Γ m} : [ G ; Γ ⊢[ lD ] ] -> [ G ; Γ ⊢[ lD ] m : tyNat @ L0 ] -> [ G ; Γ ⊢[ lD ] F3T m @ LL ].
Proof. intros HΓ Hm. pty. Qed.
Ltac pfam_ty ::= ty_rule @F3T_wf.
Lemma F3T_conv {Γ m m'} : [ G ; Γ ⊢[ lD ] ] -> [ G ; Γ ⊢[ lD ] m ≅ m' : tyNat @ L0 ] ->
  [ G ; Γ ⊢[ lD ] F3T m ≅ F3T m' @ LL ].
Proof. intros HΓ Hm. pconv. Qed.
Ltac pfam_conv ::= conv_rule @F3T_conv.

(** [Γ3]: [n : Nat, x : Fin n, xs : V n]. *)
Notation Γ3 := (cnil ,, tyNat @ L0 ,, tyFin (var 0) @ L0 ,, F3T (var 1) @ LL).

Lemma f3_ty : [ G ; cnil ,, tyNat @ L0 ⊢[ lD ] F3T (var 0) @ LL ].
Proof. pty. Qed.

Lemma nil3_wf : [ G ; cnil ⊢[ lD ] nil3 : F3T zero @ LL ].
Proof. ptm. Qed.

Lemma cons3_wf : [ G ; Γ3 ⊢[ lD ] cons3 (var 2) (var 1) (var 0) : F3T (succ (var 2)) @ LL ].
Proof. ptm. Qed.

Lemma head3_wf : [ G ; cnil ,, tyNat @ L0 ,, F3T (succ (var 0)) @ LL ⊢[ lD ]
                   head3 (succ (var 1)) (var 0) : tyFin (var 1) @ L0 ].
Proof. ptm. Qed.

(** [head3 (cons3 n x xs) ≡ x : Fin n], everything open. *)
Lemma head3_beta : [ G ; Γ3 ⊢[ lD ] head3 (succ (var 2)) (cons3 (var 2) (var 1) (var 0)) ≅ var 1
                     : tyFin (var 2) @ L0 ].
Proof. ptmconv. Qed.

(** ** F1: a child at a non-variable index (§8.2)

    [Leaf : T 0], [Node(n, l : T 0, r : T n) : T (S n)]. The shape is
    [Unit + Nat] (the node stores [n]), the arity [0 | 2]. The child index
    cases on the tag and then on the position, and since the position's
    type [Fin N[x]] mentions the tag, the case on the tag carries it as a
    [Π] (the convoy): [c(x, i) := (case x of inl ⇒ λi. 0 | inr n ⇒
    λ(i : Fin 2). case i of inl ⇒ 0 | inr ⇒ n) i]. *)
Notation f1S := (tySum L0 L0 U0 tyNat).
Notation f1N := (tmCase L0 L0 L0 U0 tyNat tyNat zero (succ (succ zero)) (var 0)).
Notation f1O := (tmCase L0 L0 L0 U0 tyNat tyNat zero (succ (var 0)) (var 0)).
Notation f1C := (app (tmCase L0 L0 LL U0 tyNat (tyPi L0 L0 (tyFin f1N) tyNat)
                        (lam L0 L0 (tyFin zero) zero)
                        (lam L0 L0 (tyFin (succ (succ zero)))
                           (tmCase L0 L0 L0 U0 (tyFin (succ zero)) tyNat zero (var 2) (var 0)))
                        (var 1))
                   L0 L0 (tyFin (tmCase L0 L0 L0 U0 tyNat tyNat zero (succ (succ zero)) (var 1))) tyNat (var 0)).
Notation F1T m := (tyIWf L0 L0 tyNat f1S f1N f1O f1C m).
Notation leaf1 := (tmSupi L0 L0 tyNat f1S f1N f1O f1C (tmInl L0 L0 U0 tyNat tt0) (tmTriv LL)).
Notation node1 n l r :=
  (tmSupi L0 L0 tyNat f1S f1N f1O f1C (tmInr L0 L0 U0 tyNat n)
     (tmPair LL LL (F1T zero) (tySig LL LL (F1T n⟨↑⟩) (tyUnit LL)) l
        (tmPair LL LL (F1T n) (tyUnit LL) r (tmTriv LL)))).

(** The child index, and the family at any index, once. *)
Lemma f1C_wf {Γ} : [ G ; Γ ⊢[ lD ] ] -> [ G ; Γ ,, f1S @ L0 ,, tyFin f1N @ L0 ⊢[ lD ] f1C : tyNat @ L0 ].
Proof. intros HΓ. ptm. Qed.
Ltac pfam_tm ::= tm_rule @f1C_wf.
Lemma F1T_wf {Γ m} : [ G ; Γ ⊢[ lD ] ] -> [ G ; Γ ⊢[ lD ] m : tyNat @ L0 ] -> [ G ; Γ ⊢[ lD ] F1T m @ LL ].
Proof. intros HΓ Hm. pty. Qed.
Ltac pfam_ty ::= first [ ty_rule @F3T_wf | ty_rule @F1T_wf ].
Lemma F1T_conv {Γ m m'} : [ G ; Γ ⊢[ lD ] ] -> [ G ; Γ ⊢[ lD ] m ≅ m' : tyNat @ L0 ] ->
  [ G ; Γ ⊢[ lD ] F1T m ≅ F1T m' @ LL ].
Proof. intros HΓ Hm. pconv. Qed.
Ltac pfam_conv ::= first [ conv_rule @F3T_conv | conv_rule @F1T_conv ].

(** [left1 : T (S n) → T 0], by form A. Its result is a value of the
    family itself, so the motive's index case returns the family's own
    code: [El(natrec(⌜Unit⌝; _ _. ⌜T 0⌝; j))], with [⌜T 0⌝ := tmIWf(⌜Nat⌝;
    ⌜Unit + Nat⌝; n; o; c; 0)]. The step cases on the tag and carries the
    children through the case (their type [DVec N[a] …] mentions the tag). *)
Notation f1Code := (tmIWf L0 L0 tmNat (tmSum L0 L0 (tmUnit L0) tmNat) f1N f1O f1C zero).
Notation Mleft j := (tyEl LL (natrec (lsuc LL) (tyU LL) (tmUnit LL) f1Code j)).
Notation left1Step :=
  (app (tmCase L0 L0 LL U0 tyNat (tyPi LL LL (tyDVec LL f1N (F1T f1C)) (Mleft f1O⟨↑⟩))
          (lam LL LL (tyUnit LL) (tmTriv LL))
          (lam LL LL (tySig LL LL (F1T zero) (tySig LL LL (F1T (var 1)) (tyUnit LL)))
             (tmFst LL LL (F1T zero) (tySig LL LL (F1T (var 2)) (tyUnit LL)) (var 0)))
          (var 2))
     LL LL (tyDVec LL f1N⟨rshift 2⟩ (F1T f1C⟨rlift (rshift 2)⟩)) (Mleft f1O⟨rshift 3⟩) (var 1)).
Notation left1 m t := (tmElimIWf L0 L0 LL tyNat f1S f1N f1O f1C (Mleft (var 1)) left1Step m t).

(** [Γ1]: [n : Nat, l : T 0, r : T n]. *)
Notation Γ1 := (cnil ,, tyNat @ L0 ,, F1T zero @ LL ,, F1T (var 1) @ LL).

Lemma f1_ty : [ G ; cnil ,, tyNat @ L0 ⊢[ lD ] F1T (var 0) @ LL ].
Proof. pty. Qed.

Lemma leaf1_wf : [ G ; cnil ⊢[ lD ] leaf1 : F1T zero @ LL ].
Proof. ptm. Qed.

Lemma node1_wf : [ G ; Γ1 ⊢[ lD ] node1 (var 2) (var 1) (var 0) : F1T (succ (var 2)) @ LL ].
Proof. ptm. Qed.

Lemma left1_wf : [ G ; cnil ,, tyNat @ L0 ,, F1T (succ (var 0)) @ LL ⊢[ lD ]
                   left1 (succ (var 1)) (var 0) : F1T zero @ LL ].
Proof. ptm. Qed.

(** [left1 (node1 n l r) ≡ l : T 0]. *)
Lemma left1_beta : [ G ; Γ1 ⊢[ lD ] left1 (succ (var 2)) (node1 (var 2) (var 1) (var 0)) ≅ var 1
                     : F1T zero @ LL ].
Proof. ptmconv. Qed.

(** ** F2: two children at one index (§8.2)

    [Leaf : T 0], [Node(n, l : T n, r : T n) : T (n + n)], with [n + n :=
    natrec(n; _ k. S k; n)]. The child index ignores the position, and no
    coherence between the children is stated. The output index is stuck
    at an open [n], so form A does not apply (tier 2's index abstraction
    would); the β of [size] holds at the stuck index. *)
Notation f2O := (tmCase L0 L0 L0 U0 tyNat tyNat zero (natrec L0 tyNat (var 0) (succ (var 0)) (var 0)) (var 0)).
Notation f2C := (tmCase L0 L0 L0 U0 tyNat tyNat zero (var 0) (var 1)).
Notation F2T m := (tyIWf L0 L0 tyNat f1S f1N f2O f2C m).
Notation plus2 n := (natrec L0 tyNat n (succ (var 0)) n).
Notation node2 n l r :=
  (tmSupi L0 L0 tyNat f1S f1N f2O f2C (tmInr L0 L0 U0 tyNat n)
     (tmPair LL LL (F2T n) (tySig LL LL (F2T n⟨↑⟩) (tyUnit LL)) l
        (tmPair LL LL (F2T n) (tyUnit LL) r (tmTriv LL)))).
Notation pos0 := (tmInl L0 L0 U0 (tyFin (succ zero)) tt0).
Notation pos1 := (tmInr L0 L0 U0 (tyFin (succ zero)) (tmInl L0 L0 U0 (tyFin zero) tt0)).
(** [size2]: the length of the right spine, [1 + size r], through the
    induction hypothesis at position [1]. (The checker's reduction keeps
    the induction hypothesis folded, so a step that passes it under a
    binder, such as [natrec]'s for [size l + size r], does not compute
    here; see [probes/README.md].) *)
Notation size2Step :=
  (app (tmCase L0 L0 LL U0 tyNat (tyPi LL L0 (tyPi L0 L0 (tyFin f1N) tyNat) tyNat)
          (lam LL L0 (tyPi L0 L0 (tyFin zero) tyNat) zero)
          (lam LL L0 (tyPi L0 L0 (tyFin (succ (succ zero))) tyNat)
             (succ (app (var 0) L0 L0 (tyFin (succ (succ zero))) tyNat pos1)))
          (var 2))
     LL L0 (tyPi L0 L0 (tyFin f1N⟨rshift 2⟩) tyNat) tyNat (var 0)).
Notation size2 m t := (tmElimIWf L0 L0 L0 tyNat f1S f1N f2O f2C tyNat size2Step m t).

Lemma F2T_wf {Γ m} : [ G ; Γ ⊢[ lD ] ] -> [ G ; Γ ⊢[ lD ] m : tyNat @ L0 ] -> [ G ; Γ ⊢[ lD ] F2T m @ LL ].
Proof. intros HΓ Hm. pty. Qed.
Ltac pfam_ty ::= first [ ty_rule @F3T_wf | ty_rule @F1T_wf | ty_rule @F2T_wf ].
Lemma F2T_conv {Γ m m'} : [ G ; Γ ⊢[ lD ] ] -> [ G ; Γ ⊢[ lD ] m ≅ m' : tyNat @ L0 ] ->
  [ G ; Γ ⊢[ lD ] F2T m ≅ F2T m' @ LL ].
Proof. intros HΓ Hm. pconv. Qed.
Ltac pfam_conv ::= first [ conv_rule @F3T_conv | conv_rule @F1T_conv | conv_rule @F2T_conv ].

(** [Γ2]: [n : Nat, l r : T n]. *)
Notation Γ2 := (cnil ,, tyNat @ L0 ,, F2T (var 0) @ LL ,, F2T (var 1) @ LL).

Lemma node2_wf : [ G ; Γ2 ⊢[ lD ] node2 (var 2) (var 1) (var 0) : F2T (plus2 (var 2)) @ LL ].
Proof. ptm. Qed.

Lemma size2_wf : [ G ; Γ2 ⊢[ lD ] size2 (var 2) (var 0) : tyNat @ L0 ].
Proof. ptm. Qed.

(** [size2 (node2 n l r) ≡ S (size2 r)] at the stuck index [n + n]: the
    child at position [1] is at index [n], by the child index's case. *)
Lemma size2_beta : [ G ; Γ2 ⊢[ lD ] size2 (plus2 (var 2)) (node2 (var 2) (var 1) (var 0))
                     ≅ succ (size2 (var 2) (var 0)) : tyNat @ L0 ].
Proof. ptmconv. Qed.


(** ** §12.1: a family at a parameterized index type

    [All P : List A → Type], over [a : Ty 0] and [p : El a → Ty 0], with
    [allNil : All P nil] and [allCons(xs, x, px : El (p x), rest : All P xs)
    : All P (cons x xs)]. [List A] is tier 0's lowering, a [Wf] with shape
    [Unit + El a] and arity [0 | 1]; nothing about it is special. The
    payload is ordered [Σ(xs : List). Σ(x : El a). El (p x)] (the record's
    fields in any dependency-respecting order). Everything is stated at
    depth [d] past [ΓP]: [p] is [var d], [a] is [var (S d)]. *)
Notation ΓP := (cnil ,, tyU L0 @ lsuc L0 ,, tyPi L0 (lsuc L0) (tyEl L0 (var 0)) (tyU L0) @ lmax L0 (lsuc L0)).
Notation elA d := (tyEl L0 (var (S d))).
Notation pAt d x := (app (var d) L0 (lsuc L0) (tyEl L0 (var (S d))) (tyU L0) x).
Notation LS d := (tySum L0 L0 U0 (elA d)).
Notation LN d := (tmCase L0 L0 L0 U0 (elA (S d)) tyNat zero (succ zero) (var 0)).
Notation List d := (tyWf L0 (LS d) (LN d)).
Notation lnil d := (tmSupf L0 (LS d) (LN d) (tmInl L0 L0 U0 (elA d) tt0) (tmTriv L0)).
Notation lcons d x xs := (tmSupf L0 (LS d) (LN d) (tmInr L0 L0 U0 (elA d) x)
                            (tmPair L0 L0 (List d) (tyUnit L0) xs (tmTriv L0))).

Notation XPay d := (tySig L0 L0 (elA d) (tyEl L0 (pAt (S d) (var 0)))).
Notation APay d := (tySig L0 L0 (List d) (XPay (S d))).
Notation AS d := (tySum L0 L0 U0 (APay d)).
(** The payload [q], [var 0] at depth [D], and its fields. *)
Notation xsOf D := (tmFst L0 L0 (List D) (XPay (S D)) (var 0)).
Notation sndq D := (tmSnd L0 L0 (List D) (XPay (S D)) (var 0)).
Notation xOf D := (tmFst L0 L0 (elA D) (tyEl L0 (pAt (S D) (var 0))) (sndq D)).
Notation pxOf D := (tmSnd L0 L0 (elA D) (tyEl L0 (pAt (S D) (var 0))) (sndq D)).
Notation AN d := (tmCase L0 L0 L0 U0 (APay (S d)) tyNat zero (succ zero) (var 0)).
Notation AO d := (tmCase L0 L0 L0 U0 (APay (S d)) (List (S (S d))) (lnil (S (S d)))
                    (lcons (S (S d)) (xOf (S (S d))) (xsOf (S (S d)))) (var 0)).
Notation AC d := (tmCase L0 L0 L0 U0 (APay (S (S d))) (List (S (S (S d)))) (lnil (S (S (S d))))
                    (xsOf (S (S (S d)))) (var 1)).
Notation AllT d m := (tyIWf L0 L0 (List d) (AS d) (AN d) (AO d) (AC d) m).
Notation allNil d := (tmSupi L0 L0 (List d) (AS d) (AN d) (AO d) (AC d) (tmInl L0 L0 U0 (APay d) tt0) (tmTriv LL)).
Notation allCons d xs x px rest :=
  (tmSupi L0 L0 (List d) (AS d) (AN d) (AO d) (AC d)
     (tmInr L0 L0 U0 (APay d)
        (tmPair L0 L0 (List d) (XPay (S d)) xs (tmPair L0 L0 (elA d) (tyEl L0 (pAt (S d) (var 0))) x px)))
     (tmPair LL LL (AllT d xs) (tyUnit LL) rest (tmTriv LL))).

(** [allHead : All P (cons x xs) → El (p x)], by form A: the motive cases
    on the index by [List]'s own eliminator, a large [elim_Wf] into [Ty 0]
    whose [cons] arm is [p] at the head:
    [El(elim_Wf(j; b _ _. case b of nil ⇒ ⌜Unit⌝ | cons y ⇒ p y))]. *)
Notation LhStep E := (tmCase L0 L0 (lsuc L0) U0 (elA E) (tyU L0) (tmUnit L0) (pAt (S E) (var 0)) (var 2)).
Notation MallH D j := (tyEl L0 (tmElimWf L0 (lsuc L0) (LS D) (LN D) (tyU L0) (LhStep (S (S (S D)))) j)).
Notation allHeadStep E := (tmCase L0 L0 L0 U0 (APay E) (MallH (S E) (AO E)) tt0 (pxOf (S E)) (var 2)).
Notation allHead D m t := (tmElimIWf L0 L0 L0 (List D) (AS D) (AN D) (AO D) (AC D)
                             (MallH (S (S D)) (var 1)) (allHeadStep (S (S (S D)))) m t).

(** [List] and [All] at each depth the tests reach, once: over any
    context whose entries at [d] and [S d] are [p] and [a]. *)
Lemma List_wf_0 {Δ} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 1 (tyU L0) (lsuc L0) -> [ G ; Δ ⊢[ lD ] List 0 @ L0 ].
Proof. intros HΔ Ha. pty. Qed.
Lemma List_wf_1 {Δ} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 2 (tyU L0) (lsuc L0) -> [ G ; Δ ⊢[ lD ] List 1 @ L0 ].
Proof. intros HΔ Ha. pty. Qed.
Lemma List_wf_2 {Δ} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 3 (tyU L0) (lsuc L0) -> [ G ; Δ ⊢[ lD ] List 2 @ L0 ].
Proof. intros HΔ Ha. pty. Qed.
Lemma List_wf_3 {Δ} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 4 (tyU L0) (lsuc L0) -> [ G ; Δ ⊢[ lD ] List 3 @ L0 ].
Proof. intros HΔ Ha. pty. Qed.
Lemma List_wf_4 {Δ} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 5 (tyU L0) (lsuc L0) -> [ G ; Δ ⊢[ lD ] List 4 @ L0 ].
Proof. intros HΔ Ha. pty. Qed.
Lemma List_wf_5 {Δ} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 6 (tyU L0) (lsuc L0) -> [ G ; Δ ⊢[ lD ] List 5 @ L0 ].
Proof. intros HΔ Ha. pty. Qed.
Lemma List_wf_6 {Δ} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 7 (tyU L0) (lsuc L0) -> [ G ; Δ ⊢[ lD ] List 6 @ L0 ].
Proof. intros HΔ Ha. pty. Qed.
Lemma List_wf_7 {Δ} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 8 (tyU L0) (lsuc L0) -> [ G ; Δ ⊢[ lD ] List 7 @ L0 ].
Proof. intros HΔ Ha. pty. Qed.
Lemma List_wf_8 {Δ} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 9 (tyU L0) (lsuc L0) -> [ G ; Δ ⊢[ lD ] List 8 @ L0 ].
Proof. intros HΔ Ha. pty. Qed.
Lemma List_wf_9 {Δ} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 10 (tyU L0) (lsuc L0) -> [ G ; Δ ⊢[ lD ] List 9 @ L0 ].
Proof. intros HΔ Ha. pty. Qed.
Lemma List_wf_10 {Δ} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 11 (tyU L0) (lsuc L0) -> [ G ; Δ ⊢[ lD ] List 10 @ L0 ].
Proof. intros HΔ Ha. pty. Qed.
Lemma List_wf_11 {Δ} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 12 (tyU L0) (lsuc L0) -> [ G ; Δ ⊢[ lD ] List 11 @ L0 ].
Proof. intros HΔ Ha. pty. Qed.
Ltac pfam_list := first [ ty_rule @List_wf_0 | ty_rule @List_wf_1 | ty_rule @List_wf_2 | ty_rule @List_wf_3 | ty_rule @List_wf_4 | ty_rule @List_wf_5 | ty_rule @List_wf_6 | ty_rule @List_wf_7 | ty_rule @List_wf_8 | ty_rule @List_wf_9 | ty_rule @List_wf_10 | ty_rule @List_wf_11 ].
Ltac pfam_ty ::= first [ ty_rule @F3T_wf | ty_rule @F1T_wf | ty_rule @F2T_wf | pfam_list ].
Lemma AllT_wf_0 {Δ m} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 1 (tyU L0) (lsuc L0) -> in_ctx Δ 0 (tyPi L0 (lsuc L0) (tyEl L0 (var 1)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m : List 0 @ L0 ] -> [ G ; Δ ⊢[ lD ] AllT 0 m @ LL ].
Proof. intros HΔ Ha Hp Hm. pty. Qed.
Lemma AllT_conv_0 {Δ m m'} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 1 (tyU L0) (lsuc L0) -> in_ctx Δ 0 (tyPi L0 (lsuc L0) (tyEl L0 (var 1)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m ≅ m' : List 0 @ L0 ] -> [ G ; Δ ⊢[ lD ] AllT 0 m ≅ AllT 0 m' @ LL ].
Proof. intros HΔ Ha Hp Hm. pconv. Qed.
Ltac pfam_ty ::= first [ ty_rule @F3T_wf | ty_rule @F1T_wf | ty_rule @F2T_wf | pfam_list | ty_rule @AllT_wf_0 ].
Ltac pfam_conv ::= first [ conv_rule @F3T_conv | conv_rule @F1T_conv | conv_rule @F2T_conv | conv_rule @AllT_conv_0 ].
Lemma AllT_wf_1 {Δ m} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 2 (tyU L0) (lsuc L0) -> in_ctx Δ 1 (tyPi L0 (lsuc L0) (tyEl L0 (var 2)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m : List 1 @ L0 ] -> [ G ; Δ ⊢[ lD ] AllT 1 m @ LL ].
Proof. intros HΔ Ha Hp Hm. pty. Qed.
Lemma AllT_conv_1 {Δ m m'} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 2 (tyU L0) (lsuc L0) -> in_ctx Δ 1 (tyPi L0 (lsuc L0) (tyEl L0 (var 2)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m ≅ m' : List 1 @ L0 ] -> [ G ; Δ ⊢[ lD ] AllT 1 m ≅ AllT 1 m' @ LL ].
Proof. intros HΔ Ha Hp Hm. pconv. Qed.
Ltac pfam_ty ::= first [ ty_rule @F3T_wf | ty_rule @F1T_wf | ty_rule @F2T_wf | pfam_list | ty_rule @AllT_wf_0 | ty_rule @AllT_wf_1 ].
Ltac pfam_conv ::= first [ conv_rule @F3T_conv | conv_rule @F1T_conv | conv_rule @F2T_conv | conv_rule @AllT_conv_0 | conv_rule @AllT_conv_1 ].
Lemma AllT_wf_2 {Δ m} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 3 (tyU L0) (lsuc L0) -> in_ctx Δ 2 (tyPi L0 (lsuc L0) (tyEl L0 (var 3)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m : List 2 @ L0 ] -> [ G ; Δ ⊢[ lD ] AllT 2 m @ LL ].
Proof. intros HΔ Ha Hp Hm. pty. Qed.
Lemma AllT_conv_2 {Δ m m'} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 3 (tyU L0) (lsuc L0) -> in_ctx Δ 2 (tyPi L0 (lsuc L0) (tyEl L0 (var 3)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m ≅ m' : List 2 @ L0 ] -> [ G ; Δ ⊢[ lD ] AllT 2 m ≅ AllT 2 m' @ LL ].
Proof. intros HΔ Ha Hp Hm. pconv. Qed.
Ltac pfam_ty ::= first [ ty_rule @F3T_wf | ty_rule @F1T_wf | ty_rule @F2T_wf | pfam_list | ty_rule @AllT_wf_0 | ty_rule @AllT_wf_1 | ty_rule @AllT_wf_2 ].
Ltac pfam_conv ::= first [ conv_rule @F3T_conv | conv_rule @F1T_conv | conv_rule @F2T_conv | conv_rule @AllT_conv_0 | conv_rule @AllT_conv_1 | conv_rule @AllT_conv_2 ].
Lemma AllT_wf_3 {Δ m} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 4 (tyU L0) (lsuc L0) -> in_ctx Δ 3 (tyPi L0 (lsuc L0) (tyEl L0 (var 4)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m : List 3 @ L0 ] -> [ G ; Δ ⊢[ lD ] AllT 3 m @ LL ].
Proof. intros HΔ Ha Hp Hm. pty. Qed.
Lemma AllT_conv_3 {Δ m m'} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 4 (tyU L0) (lsuc L0) -> in_ctx Δ 3 (tyPi L0 (lsuc L0) (tyEl L0 (var 4)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m ≅ m' : List 3 @ L0 ] -> [ G ; Δ ⊢[ lD ] AllT 3 m ≅ AllT 3 m' @ LL ].
Proof. intros HΔ Ha Hp Hm. pconv. Qed.
Ltac pfam_ty ::= first [ ty_rule @F3T_wf | ty_rule @F1T_wf | ty_rule @F2T_wf | pfam_list | ty_rule @AllT_wf_0 | ty_rule @AllT_wf_1 | ty_rule @AllT_wf_2 | ty_rule @AllT_wf_3 ].
Ltac pfam_conv ::= first [ conv_rule @F3T_conv | conv_rule @F1T_conv | conv_rule @F2T_conv | conv_rule @AllT_conv_0 | conv_rule @AllT_conv_1 | conv_rule @AllT_conv_2 | conv_rule @AllT_conv_3 ].
Lemma AllT_wf_4 {Δ m} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 5 (tyU L0) (lsuc L0) -> in_ctx Δ 4 (tyPi L0 (lsuc L0) (tyEl L0 (var 5)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m : List 4 @ L0 ] -> [ G ; Δ ⊢[ lD ] AllT 4 m @ LL ].
Proof. intros HΔ Ha Hp Hm. pty. Qed.
Lemma AllT_conv_4 {Δ m m'} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 5 (tyU L0) (lsuc L0) -> in_ctx Δ 4 (tyPi L0 (lsuc L0) (tyEl L0 (var 5)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m ≅ m' : List 4 @ L0 ] -> [ G ; Δ ⊢[ lD ] AllT 4 m ≅ AllT 4 m' @ LL ].
Proof. intros HΔ Ha Hp Hm. pconv. Qed.
Ltac pfam_ty ::= first [ ty_rule @F3T_wf | ty_rule @F1T_wf | ty_rule @F2T_wf | pfam_list | ty_rule @AllT_wf_0 | ty_rule @AllT_wf_1 | ty_rule @AllT_wf_2 | ty_rule @AllT_wf_3 | ty_rule @AllT_wf_4 ].
Ltac pfam_conv ::= first [ conv_rule @F3T_conv | conv_rule @F1T_conv | conv_rule @F2T_conv | conv_rule @AllT_conv_0 | conv_rule @AllT_conv_1 | conv_rule @AllT_conv_2 | conv_rule @AllT_conv_3 | conv_rule @AllT_conv_4 ].
Lemma AllT_wf_5 {Δ m} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 6 (tyU L0) (lsuc L0) -> in_ctx Δ 5 (tyPi L0 (lsuc L0) (tyEl L0 (var 6)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m : List 5 @ L0 ] -> [ G ; Δ ⊢[ lD ] AllT 5 m @ LL ].
Proof. intros HΔ Ha Hp Hm. pty. Qed.
Lemma AllT_conv_5 {Δ m m'} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 6 (tyU L0) (lsuc L0) -> in_ctx Δ 5 (tyPi L0 (lsuc L0) (tyEl L0 (var 6)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m ≅ m' : List 5 @ L0 ] -> [ G ; Δ ⊢[ lD ] AllT 5 m ≅ AllT 5 m' @ LL ].
Proof. intros HΔ Ha Hp Hm. pconv. Qed.
Ltac pfam_ty ::= first [ ty_rule @F3T_wf | ty_rule @F1T_wf | ty_rule @F2T_wf | pfam_list | ty_rule @AllT_wf_0 | ty_rule @AllT_wf_1 | ty_rule @AllT_wf_2 | ty_rule @AllT_wf_3 | ty_rule @AllT_wf_4 | ty_rule @AllT_wf_5 ].
Ltac pfam_conv ::= first [ conv_rule @F3T_conv | conv_rule @F1T_conv | conv_rule @F2T_conv | conv_rule @AllT_conv_0 | conv_rule @AllT_conv_1 | conv_rule @AllT_conv_2 | conv_rule @AllT_conv_3 | conv_rule @AllT_conv_4 | conv_rule @AllT_conv_5 ].
Lemma AllT_wf_6 {Δ m} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 7 (tyU L0) (lsuc L0) -> in_ctx Δ 6 (tyPi L0 (lsuc L0) (tyEl L0 (var 7)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m : List 6 @ L0 ] -> [ G ; Δ ⊢[ lD ] AllT 6 m @ LL ].
Proof. intros HΔ Ha Hp Hm. pty. Qed.
Lemma AllT_conv_6 {Δ m m'} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 7 (tyU L0) (lsuc L0) -> in_ctx Δ 6 (tyPi L0 (lsuc L0) (tyEl L0 (var 7)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m ≅ m' : List 6 @ L0 ] -> [ G ; Δ ⊢[ lD ] AllT 6 m ≅ AllT 6 m' @ LL ].
Proof. intros HΔ Ha Hp Hm. pconv. Qed.
Ltac pfam_ty ::= first [ ty_rule @F3T_wf | ty_rule @F1T_wf | ty_rule @F2T_wf | pfam_list | ty_rule @AllT_wf_0 | ty_rule @AllT_wf_1 | ty_rule @AllT_wf_2 | ty_rule @AllT_wf_3 | ty_rule @AllT_wf_4 | ty_rule @AllT_wf_5 | ty_rule @AllT_wf_6 ].
Ltac pfam_conv ::= first [ conv_rule @F3T_conv | conv_rule @F1T_conv | conv_rule @F2T_conv | conv_rule @AllT_conv_0 | conv_rule @AllT_conv_1 | conv_rule @AllT_conv_2 | conv_rule @AllT_conv_3 | conv_rule @AllT_conv_4 | conv_rule @AllT_conv_5 | conv_rule @AllT_conv_6 ].
Lemma AllT_wf_7 {Δ m} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 8 (tyU L0) (lsuc L0) -> in_ctx Δ 7 (tyPi L0 (lsuc L0) (tyEl L0 (var 8)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m : List 7 @ L0 ] -> [ G ; Δ ⊢[ lD ] AllT 7 m @ LL ].
Proof. intros HΔ Ha Hp Hm. pty. Qed.
Lemma AllT_conv_7 {Δ m m'} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 8 (tyU L0) (lsuc L0) -> in_ctx Δ 7 (tyPi L0 (lsuc L0) (tyEl L0 (var 8)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m ≅ m' : List 7 @ L0 ] -> [ G ; Δ ⊢[ lD ] AllT 7 m ≅ AllT 7 m' @ LL ].
Proof. intros HΔ Ha Hp Hm. pconv. Qed.
Ltac pfam_ty ::= first [ ty_rule @F3T_wf | ty_rule @F1T_wf | ty_rule @F2T_wf | pfam_list | ty_rule @AllT_wf_0 | ty_rule @AllT_wf_1 | ty_rule @AllT_wf_2 | ty_rule @AllT_wf_3 | ty_rule @AllT_wf_4 | ty_rule @AllT_wf_5 | ty_rule @AllT_wf_6 | ty_rule @AllT_wf_7 ].
Ltac pfam_conv ::= first [ conv_rule @F3T_conv | conv_rule @F1T_conv | conv_rule @F2T_conv | conv_rule @AllT_conv_0 | conv_rule @AllT_conv_1 | conv_rule @AllT_conv_2 | conv_rule @AllT_conv_3 | conv_rule @AllT_conv_4 | conv_rule @AllT_conv_5 | conv_rule @AllT_conv_6 | conv_rule @AllT_conv_7 ].
Lemma AllT_wf_8 {Δ m} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 9 (tyU L0) (lsuc L0) -> in_ctx Δ 8 (tyPi L0 (lsuc L0) (tyEl L0 (var 9)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m : List 8 @ L0 ] -> [ G ; Δ ⊢[ lD ] AllT 8 m @ LL ].
Proof. intros HΔ Ha Hp Hm. pty. Qed.
Lemma AllT_conv_8 {Δ m m'} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 9 (tyU L0) (lsuc L0) -> in_ctx Δ 8 (tyPi L0 (lsuc L0) (tyEl L0 (var 9)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m ≅ m' : List 8 @ L0 ] -> [ G ; Δ ⊢[ lD ] AllT 8 m ≅ AllT 8 m' @ LL ].
Proof. intros HΔ Ha Hp Hm. pconv. Qed.
Ltac pfam_ty ::= first [ ty_rule @F3T_wf | ty_rule @F1T_wf | ty_rule @F2T_wf | pfam_list | ty_rule @AllT_wf_0 | ty_rule @AllT_wf_1 | ty_rule @AllT_wf_2 | ty_rule @AllT_wf_3 | ty_rule @AllT_wf_4 | ty_rule @AllT_wf_5 | ty_rule @AllT_wf_6 | ty_rule @AllT_wf_7 | ty_rule @AllT_wf_8 ].
Ltac pfam_conv ::= first [ conv_rule @F3T_conv | conv_rule @F1T_conv | conv_rule @F2T_conv | conv_rule @AllT_conv_0 | conv_rule @AllT_conv_1 | conv_rule @AllT_conv_2 | conv_rule @AllT_conv_3 | conv_rule @AllT_conv_4 | conv_rule @AllT_conv_5 | conv_rule @AllT_conv_6 | conv_rule @AllT_conv_7 | conv_rule @AllT_conv_8 ].

(** [ΓPc]: [xs : List, x : El a, px : El (p x), rest : All P xs]. *)
Notation ΓPc := (ΓP ,, List 0 @ L0 ,, elA 1 @ L0 ,, tyEl L0 (pAt 2 (var 0)) @ L0 ,, AllT 3 (var 2) @ LL).

Lemma list_ty : [ G ; ΓP ⊢[ lD ] List 0 @ L0 ].
Proof. pty. Qed.

Lemma all_ty : [ G ; ΓP ,, List 0 @ L0 ⊢[ lD ] AllT 1 (var 0) @ LL ].
Proof. pty. Qed.

Lemma allNil_wf : [ G ; ΓP ⊢[ lD ] allNil 0 : AllT 0 (lnil 0) @ LL ].
Proof. ptm. Qed.

Lemma allCons_wf : [ G ; ΓPc ⊢[ lD ] allCons 4 (var 3) (var 2) (var 1) (var 0) : AllT 4 (lcons 4 (var 2) (var 3)) @ LL ].
Proof. ptm. Qed.

Lemma allHead_wf : [ G ; ΓP ,, List 0 @ L0 ,, elA 1 @ L0 ,, AllT 2 (lcons 2 (var 0) (var 1)) @ LL ⊢[ lD ]
                     allHead 3 (lcons 3 (var 1) (var 2)) (var 0) : tyEl L0 (pAt 3 (var 1)) @ L0 ].
Proof. ptm. Qed.

(** [allHead (allCons xs x px rest) ≡ px], everything open. *)
Lemma allHead_beta : [ G ; ΓPc ⊢[ lD ] allHead 4 (lcons 4 (var 2) (var 3)) (allCons 4 (var 3) (var 2) (var 1) (var 0))
                       ≅ var 1 : tyEl L0 (pAt 4 (var 2)) @ L0 ].
Proof. ptmconv. Qed.

(** ** §12.2: a mutual pair as one family over [Σ(tag). I_tag]

    [Even, Odd : Nat → Type], [ezero : Even 0], [esucc(n, o : Odd n) :
    Even (S n)], [osucc(n, e : Even n) : Odd (S n)], lowered to one family
    over [I := Σ(b : Bool). Nat] with [Bool := Unit + Unit]
    ([Even n := E (inl, n)], [Odd n := E (inr, n)]). The shape is
    [Unit + (Nat + Nat)], one summand per constructor of either family,
    and the output and child indices pair a tag with a number. The family
    is closed. *)
Notation Bool0 := (tySum L0 L0 U0 U0).
Notation tE := (tmInl L0 L0 U0 U0 tt0).
Notation tO := (tmInr L0 L0 U0 U0 tt0).
Notation EOI := (tySig L0 L0 Bool0 tyNat).
Notation ix b n := (tmPair L0 L0 Bool0 tyNat b n).
Notation eoS := (tySum L0 L0 U0 (tySum L0 L0 tyNat tyNat)).
Notation eoN := (tmCase L0 L0 L0 U0 (tySum L0 L0 tyNat tyNat) tyNat zero (succ zero) (var 0)).
Notation eoO := (tmCase L0 L0 L0 U0 (tySum L0 L0 tyNat tyNat) EOI (ix tE zero)
                   (tmCase L0 L0 L0 tyNat tyNat EOI (ix tE (succ (var 0))) (ix tO (succ (var 0))) (var 0))
                   (var 0)).
Notation eoC := (tmCase L0 L0 L0 U0 (tySum L0 L0 tyNat tyNat) EOI (ix tE zero)
                   (tmCase L0 L0 L0 tyNat tyNat EOI (ix tO (var 0)) (ix tE (var 0)) (var 0))
                   (var 1)).
Notation EO m := (tyIWf L0 L0 EOI eoS eoN eoO eoC m).
Notation eosupi a cs := (tmSupi L0 L0 EOI eoS eoN eoO eoC a cs).
Notation ezero := (eosupi (tmInl L0 L0 U0 (tySum L0 L0 tyNat tyNat) tt0) (tmTriv LL)).
Notation esucc n o := (eosupi (tmInr L0 L0 U0 (tySum L0 L0 tyNat tyNat) (tmInl L0 L0 tyNat tyNat n))
                         (tmPair LL LL (EO (ix tO n)) (tyUnit LL) o (tmTriv LL))).
Notation osucc n e := (eosupi (tmInr L0 L0 U0 (tySum L0 L0 tyNat tyNat) (tmInr L0 L0 tyNat tyNat n))
                         (tmPair LL LL (EO (ix tE n)) (tyUnit LL) e (tmTriv LL))).

Lemma EO_wf {Γ m} : [ G ; Γ ⊢[ lD ] ] -> [ G ; Γ ⊢[ lD ] m : EOI @ L0 ] -> [ G ; Γ ⊢[ lD ] EO m @ LL ].
Proof. intros HΓ Hm. pty. Qed.
Ltac pfam_ty ::= first [ ty_rule @F3T_wf | ty_rule @F1T_wf | ty_rule @F2T_wf | ty_rule @EO_wf ].
Lemma EO_conv {Γ m m'} : [ G ; Γ ⊢[ lD ] ] -> [ G ; Γ ⊢[ lD ] m ≅ m' : EOI @ L0 ] ->
  [ G ; Γ ⊢[ lD ] EO m ≅ EO m' @ LL ].
Proof. intros HΓ Hm. pconv. Qed.
Ltac pfam_conv ::= first [ conv_rule @F3T_conv | conv_rule @F1T_conv | conv_rule @F2T_conv | conv_rule @EO_conv ].

Lemma eo_ty : [ G ; cnil ,, EOI @ L0 ⊢[ lD ] EO (var 0) @ LL ].
Proof. pty. Qed.

Lemma ezero_wf : [ G ; cnil ⊢[ lD ] ezero : EO (ix tE zero) @ LL ].
Proof. ptm. Qed.

Lemma esucc_wf : [ G ; cnil ,, tyNat @ L0 ,, EO (ix tO (var 0)) @ LL ⊢[ lD ]
                   esucc (var 1) (var 0) : EO (ix tE (succ (var 1))) @ LL ].
Proof. ptm. Qed.

Lemma osucc_wf : [ G ; cnil ,, tyNat @ L0 ,, EO (ix tE (var 0)) @ LL ⊢[ lD ]
                   osucc (var 1) (var 0) : EO (ix tO (succ (var 1))) @ LL ].
Proof. ptm. Qed.

(** Mutual recursion is one [elim_IWf]: [toNat] counts the constructors
    of either family. The step cases on the shape and carries the
    induction hypothesis through the case (convoy). *)
Notation eoIH := (tyPi L0 L0 (tyFin eoN) tyNat).
Notation toNatStep :=
  (app (tmCase L0 L0 LL U0 (tySum L0 L0 tyNat tyNat) (tyPi LL L0 eoIH tyNat)
          (lam LL L0 (tyPi L0 L0 (tyFin zero) tyNat) zero)
          (lam LL L0 (tyPi L0 L0 (tyFin (succ zero)) tyNat)
             (succ (app (var 0) L0 L0 (tyFin (succ zero)) tyNat (tmInl L0 L0 U0 (tyFin zero) tt0))))
          (var 2))
     LL L0 (tyPi L0 L0 (tyFin eoN⟨rshift 2⟩) tyNat) tyNat (var 0)).
Notation toNat m t := (tmElimIWf L0 L0 L0 EOI eoS eoN eoO eoC tyNat toNatStep m t).

Lemma toNat_wf : [ G ; cnil ,, EOI @ L0 ,, EO (var 0) @ LL ⊢[ lD ] toNat (var 1) (var 0) : tyNat @ L0 ].
Proof. ptm. Qed.

(** β across the families: [toNat (esucc n o) ≡ S (toNat o)], the child at
    the odd index [(inr, n)], everything open. *)
Lemma toNat_beta : [ G ; cnil ,, tyNat @ L0 ,, EO (ix tO (var 0)) @ LL ⊢[ lD ]
                     toNat (ix tE (succ (var 1))) (esucc (var 1) (var 0))
                     ≅ succ (toNat (ix tO (var 1)) (var 0)) : tyNat @ L0 ].
Proof. ptmconv. Qed.

(** [Odd 0] is empty, by form A at the Σ index: the motive cases on the
    tag ([fst j]) and then on the number ([snd j]) by [I]'s components'
    eliminators, and every constructor's index lands in a [Unit] arm:
    [El(case fst j of inl ⇒ ⌜Unit⌝ | inr ⇒ natrec(⌜Empty⌝; _ _. ⌜Unit⌝;
    snd j))]. No η for [Σ] is needed: the output indices are pairs. *)
Notation MOdd j := (tyEl L0 (tmCase L0 L0 (lsuc L0) U0 U0 (tyU L0) (tmUnit L0)
                      (natrec (lsuc L0) (tyU L0) (tmEmpty L0) (tmUnit L0) (tmSnd L0 L0 Bool0 tyNat j⟨↑⟩))
                      (tmFst L0 L0 Bool0 tyNat j))).
Notation oddStep := (tmCase L0 L0 L0 U0 (tySum L0 L0 tyNat tyNat) (MOdd eoO) tt0
                       (tmCase L0 L0 L0 tyNat tyNat (MOdd eoO[lsingle (tmInr L0 L0 U0 (tySum L0 L0 tyNat tyNat) (var 0))]⟨rlift ↑⟩) tt0 tt0 (var 0))
                       (var 2)).
Notation oddZero t := (tmElimIWf L0 L0 L0 EOI eoS eoN eoO eoC (MOdd (var 1)) oddStep (ix tO zero) t).

Lemma oddZero_wf : [ G ; cnil ,, EO (ix tO zero) @ LL ⊢[ lD ] oddZero (var 0) : tyEmpty L0 @ L0 ].
Proof. ptm. Qed.

(** ** Negative controls

    A constructor at an index other than its output index has no
    derivation: [inv_supi] gives the type's conversion with its own
    [IWf] at [o[a]], [decl_IWf_inj] the indices' conversion, and a large
    elimination into [⌜Unit⌝]/[⌜Empty⌝] turns that into [Unit ≅ Empty],
    which [decl_head] refutes. [Dz] separates [0] from a successor, [Dt]
    the tags of [Bool]. *)
Notation Dz t := (tyEl L0 (natrec (lsuc L0) (tyU L0) (tmEmpty L0) (tmUnit L0) t)).
Notation Dt t := (tyEl L0 (tmCase L0 L0 (lsuc L0) U0 U0 (tyU L0) (tmUnit L0) (tmEmpty L0) t)).

Ltac by_idx E := first [ solve [eapply eqtm_cl; [exact E | lalg | left; pn; reflexivity]] | pgoal ].
(** [Dz]'s and [Dt]'s congruence at the index's conversion [E], the rest by reflexivity. *)
Ltac dz_cong E :=
  eapply eqty_El; [exact Hv | lalg | eapply eqtm_cl; [eapply eqtm_natrec; by_idx E | lalg | pgoal]].
Ltac dt_cong E :=
  eapply eqty_El; [exact Hv | lalg | eapply eqtm_cl; [eapply eqtm_case;
    first [ solve [eapply eqtm_cl; [eapply eqtm_fst; by_idx E | lalg | pgoal]] | pgoal ] | lalg | pgoal]].
(** Inverting a constructor's typing to its index's conversion. *)
Ltac inv_idx H Em :=
  apply inv_supi in H as (_ & _ & Em); [| reflexivity];
  apply decl_IWf_inj in Em as (_ & _ & _ & _ & _ & _ & _ & Em).

Lemma unit_not_empty {Γ T T' k} : [ G ; Γ ⊢[ lD ] T ≅ T' @ k ] ->
  [ G ; Γ ⊢[ lD ] tyUnit L0 ≅ T @ k ] -> [ G ; Γ ⊢[ lD ] tyEmpty L0 ≅ T' @ k ] -> False.
Proof using.
  intros E E1 E2.
  pose proof (eqty_trans _ _ _ _ _ _ _ (eqty_trans _ _ _ _ _ _ _ E1 E) (eqty_sym _ _ _ _ _ _ E2)) as E3.
  apply decl_head in E3; [cbn in E3; discriminate E3 | apply whnf_tyUnit | apply whnf_tyEmpty].
Qed.

Lemma nil3_not_at_one : ~ [ G ; cnil ⊢[ lD ] nil3 : F3T (succ zero) @ LL ].
Proof.
  intros H. inv_idx H Em. assert (HΓ : [ G ; cnil ⊢[ lD ] ]) by (apply wfc_nil; exact HG).
  lazymatch type of Em with [ _ ; _ ⊢[ _ ] ?m ≅ ?m' : _ @ _ ] =>
    refine (unit_not_empty (Γ := cnil) (T := Dz m) (T' := Dz m') _ _ _); [dz_cong Em | pconv | pconv] end.
Qed.

Lemma leaf1_not_at_one : ~ [ G ; cnil ⊢[ lD ] leaf1 : F1T (succ zero) @ LL ].
Proof.
  intros H. inv_idx H Em. assert (HΓ : [ G ; cnil ⊢[ lD ] ]) by (apply wfc_nil; exact HG).
  lazymatch type of Em with [ _ ; _ ⊢[ _ ] ?m ≅ ?m' : _ @ _ ] =>
    refine (unit_not_empty (Γ := cnil) (T := Dz m) (T' := Dz m') _ _ _); [dz_cong Em | pconv | pconv] end.
Qed.

(** [node1 0 leaf leaf : T 1], not [T 0]. *)
Lemma node1_not_at_zero : ~ [ G ; cnil ⊢[ lD ] node1 zero leaf1 leaf1 : F1T zero @ LL ].
Proof.
  intros H. inv_idx H Em. apply eqtm_sym in Em. assert (HΓ : [ G ; cnil ⊢[ lD ] ]) by (apply wfc_nil; exact HG).
  lazymatch type of Em with [ _ ; _ ⊢[ _ ] ?m ≅ ?m' : _ @ _ ] =>
    refine (unit_not_empty (Γ := cnil) (T := Dz m) (T' := Dz m') _ _ _); [dz_cong Em | pconv | pconv] end.
Qed.

(** The tag separates the mutual families: [ezero] is not odd. *)
Lemma ezero_not_odd : ~ [ G ; cnil ⊢[ lD ] ezero : EO (ix tO zero) @ LL ].
Proof.
  intros H. inv_idx H Em. apply eqtm_sym in Em. assert (HΓ : [ G ; cnil ⊢[ lD ] ]) by (apply wfc_nil; exact HG).
  lazymatch type of Em with [ _ ; _ ⊢[ _ ] ?m ≅ ?m' : _ @ _ ] =>
    refine (unit_not_empty (Γ := cnil) (T := Dt (tmFst L0 L0 Bool0 tyNat m)) (T' := Dt (tmFst L0 L0 Bool0 tyNat m')) _ _ _);
      [dt_cong Em | pconv | pconv] end.
Qed.

End Probe.

(** No axioms: each headline lemma is closed under the global context. *)
Print Assumptions vhead_beta.
Print Assumptions len_beta.
Print Assumptions head3_beta.
Print Assumptions left1_beta.
Print Assumptions size2_beta.
Print Assumptions allHead_beta.
Print Assumptions toNat_beta.
Print Assumptions oddZero_wf.
Print Assumptions ezero_not_odd.
