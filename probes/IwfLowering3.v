(** * IWf lowerings, in the formalization's own rules: form A into the family itself

    The second case [IwfLowering.v] left unchecked ([M17_DESIGN.md], "The
    generator's lowerings"): form A whose result is a value of the family
    itself at a [List a] index, [allTail : All P (x :: xs) → All P xs]. It
    needs [List]'s, the shapes' and [All]'s own codes. [All], [List] and
    their typing lemmas at each depth are [IwfLowering.v]'s; the method is
    the same (the M17b rules only, through [IwfCheck.v]'s checker).
    Compile after [IwfLowering.v]:
    [coqc -Q theories DeLaM -Q probes Probes probes/IwfLowering3.v]. *)
From DeLaM.Typing Require Import RecWfBase IWfIH PresupAux.
From DeLaM.Validity Require Import RecReduct DeclConsequencesP AlgComplete.
From Probes Require Import IwfCheck IwfLowering.

(** ** [All], as [IwfLowering.v] writes it (its notations are local to its
    section); its typing lemmas at each depth are that file's. *)
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

(** ** Form A into the family itself: [allTail : All P (x :: xs) → All P xs]

    [All] of [IwfLowering.v] (§12.1), over [a : Ty 0] and [p : El a → Ty 0].
    The result is [All P] at the tail of the index, so the motive's index
    case returns [All]'s own code, at the [cons] child of the index:
    [El(elim_Wf(j; b cs _. (case b of nil ⇒ λcs. ⌜Unit⌝
                                    | cons _ ⇒ λ(cs : Vec(1; List)). ⌜All P (fst cs)⌝) cs))].
    The arm needs [cs], whose type [Vec(N[b]; List)] mentions the shape, so
    the case carries it (a convoy, in the motive's own elimination). The
    code [⌜All P m⌝ := tmIWf(⌜List a⌝; ⌜S⌝; n; o; c; m)] needs [List]'s
    code, [tmWf(⌜Unit⌝ + a; n)], and the shapes',
    [⌜Unit⌝ + Σ(xs : ⌜List a⌝). Σ(x : a). p x]: [a] and [p x] are codes, so
    both exist, and [El ⌜All P m⌝] reduces to [All P m] up to the
    components' [El] (the conversion [AllC_conv] below). The step reads the
    child, so it carries the children through its case on the shape, as
    [IwfLowering.v]'s [left1]. *)
Notation ListC d := (tmWf L0 (tmSum L0 L0 (tmUnit L0) (var (S d))) (LN d)).
Notation ASC d := (tmSum L0 L0 (tmUnit L0) (tmSig L0 L0 (ListC d) (tmSig L0 L0 (var (S (S d))) (pAt (S (S d)) (var 0))))).
Notation AllC d m := (tmIWf L0 L0 (ListC d) (ASC d) (AN d) (AO d) (AC d) m).
(** The motive's [elim_Wf] step, at depth [E] (its [b], [cs], [ih]). *)
Notation LtCs E := (tyVec L0 (List (S E)) (LN E)).                         (* E, v *)
Notation LtStep E :=
  (app (tmCase L0 L0 (lmax L0 (lsuc LL)) U0 (elA E) (tyPi L0 (lsuc LL) (LtCs E) (tyU LL))
          (lam L0 (lsuc LL) (tyVec L0 (List (S E)) zero) (tmUnit LL))
          (lam L0 (lsuc LL) (tyVec L0 (List (S E)) (succ zero))
             (AllC (S (S E)) (tmFst L0 L0 (List (S (S E))) (tyVec L0 (List (S (S (S E)))) zero) (var 0))))
          (var 2))
     L0 (lsuc LL) (LtCs E)[lsingle (var 2)] (tyU LL) (var 1)).
Notation MallT D j := (tyEl LL (tmElimWf L0 (lsuc LL) (LS D) (LN D) (tyU LL) (LtStep (S (S (S D)))) j)).
(** The step, at depth [E] (its [x], [cs], [ih]); [csA] is the children's
    type at the case's variable. *)
Notation csA E := (tyDVec LL (AN E) (AllT (S (S E)) (AC E))).              (* E, v *)
Notation tailStep E :=
  (app (tmCase L0 L0 LL U0 (APay E) (tyPi LL LL (csA E) (MallT (S (S E)) (AO E)⟨↑⟩))
          (lam LL LL (tyUnit LL) (tmTriv LL))
          (lam LL LL (tySig LL LL (AllT (S E) (xsOf (S E))) (tyUnit LL))
             (tmFst LL LL (AllT (S (S E)) (xsOf (S E))⟨↑⟩) (tyUnit LL) (var 0)))
          (var 2))
     LL LL (csA E)[lsingle (var 2)] (MallT (S (S E)) (AO E)⟨↑⟩)[llift (lsingle (var 2))] (var 1)).
Notation allTail D m t := (tmElimIWf L0 L0 LL (List D) (AS D) (AN D) (AO D) (AC D)
                             (MallT (S (S D)) (var 1)) (tailStep (S (S (S D)))) m t).

(** [ΓPc]: [xs : List, x : El a, px : El (p x), rest : All P xs] (as [IwfLowering.v]'s). *)
Notation ΓPc := (ΓP ,, List 0 @ L0 ,, elA 1 @ L0 ,, tyEl L0 (pAt 2 (var 0)) @ L0 ,, AllT 3 (var 2) @ LL).

Section Probe3.
Context {G : gctx} (HG : [ ⊢ G ]).

(** [List] and [All] at each depth, once ([IwfLowering.v]'s to depth 11 and
    8; the motive's and the step's eliminations reach further). *)
Lemma List_wf_12 {Δ} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 13 (tyU L0) (lsuc L0) -> [ G ; Δ ⊢[ lD ] List 12 @ L0 ].
Proof. intros HΔ Ha. pty. Qed.
Lemma List_wf_13 {Δ} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 14 (tyU L0) (lsuc L0) -> [ G ; Δ ⊢[ lD ] List 13 @ L0 ].
Proof. intros HΔ Ha. pty. Qed.
Lemma List_wf_14 {Δ} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 15 (tyU L0) (lsuc L0) -> [ G ; Δ ⊢[ lD ] List 14 @ L0 ].
Proof. intros HΔ Ha. pty. Qed.
Lemma List_wf_15 {Δ} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 16 (tyU L0) (lsuc L0) -> [ G ; Δ ⊢[ lD ] List 15 @ L0 ].
Proof. intros HΔ Ha. pty. Qed.
Ltac pfam_list := first [ ty_rule @List_wf_0 | ty_rule @List_wf_1 | ty_rule @List_wf_2 | ty_rule @List_wf_3 | ty_rule @List_wf_4 | ty_rule @List_wf_5 | ty_rule @List_wf_6 | ty_rule @List_wf_7 | ty_rule @List_wf_8 | ty_rule @List_wf_9 | ty_rule @List_wf_10 | ty_rule @List_wf_11 | ty_rule @List_wf_12 | ty_rule @List_wf_13 | ty_rule @List_wf_14 | ty_rule @List_wf_15 ].
Ltac pfam_ty ::= first [ pfam_list | ty_rule @AllT_wf_0 | ty_rule @AllT_wf_1 | ty_rule @AllT_wf_2 | ty_rule @AllT_wf_3 | ty_rule @AllT_wf_4 | ty_rule @AllT_wf_5 | ty_rule @AllT_wf_6 | ty_rule @AllT_wf_7 | ty_rule @AllT_wf_8 ].
Ltac pfam_conv ::= first [ conv_rule @AllT_conv_0 | conv_rule @AllT_conv_1 | conv_rule @AllT_conv_2 | conv_rule @AllT_conv_3 | conv_rule @AllT_conv_4 | conv_rule @AllT_conv_5 | conv_rule @AllT_conv_6 | conv_rule @AllT_conv_7 | conv_rule @AllT_conv_8 ].
Lemma AllT_wf_9 {Δ m} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 10 (tyU L0) (lsuc L0) -> in_ctx Δ 9 (tyPi L0 (lsuc L0) (tyEl L0 (var 10)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m : List 9 @ L0 ] -> [ G ; Δ ⊢[ lD ] AllT 9 m @ LL ].
Proof. intros HΔ Ha Hp Hm. pty. Qed.
Lemma AllT_conv_9 {Δ m m'} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 10 (tyU L0) (lsuc L0) -> in_ctx Δ 9 (tyPi L0 (lsuc L0) (tyEl L0 (var 10)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m ≅ m' : List 9 @ L0 ] -> [ G ; Δ ⊢[ lD ] AllT 9 m ≅ AllT 9 m' @ LL ].
Proof. intros HΔ Ha Hp Hm. pconv. Qed.
Ltac pfam_ty ::= first [ pfam_list | ty_rule @AllT_wf_0 | ty_rule @AllT_wf_1 | ty_rule @AllT_wf_2 | ty_rule @AllT_wf_3 | ty_rule @AllT_wf_4 | ty_rule @AllT_wf_5 | ty_rule @AllT_wf_6 | ty_rule @AllT_wf_7 | ty_rule @AllT_wf_8 | ty_rule @AllT_wf_9 ].
Ltac pfam_conv ::= first [ conv_rule @AllT_conv_0 | conv_rule @AllT_conv_1 | conv_rule @AllT_conv_2 | conv_rule @AllT_conv_3 | conv_rule @AllT_conv_4 | conv_rule @AllT_conv_5 | conv_rule @AllT_conv_6 | conv_rule @AllT_conv_7 | conv_rule @AllT_conv_8 | conv_rule @AllT_conv_9 ].
Lemma AllT_wf_10 {Δ m} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 11 (tyU L0) (lsuc L0) -> in_ctx Δ 10 (tyPi L0 (lsuc L0) (tyEl L0 (var 11)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m : List 10 @ L0 ] -> [ G ; Δ ⊢[ lD ] AllT 10 m @ LL ].
Proof. intros HΔ Ha Hp Hm. pty. Qed.
Lemma AllT_conv_10 {Δ m m'} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 11 (tyU L0) (lsuc L0) -> in_ctx Δ 10 (tyPi L0 (lsuc L0) (tyEl L0 (var 11)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m ≅ m' : List 10 @ L0 ] -> [ G ; Δ ⊢[ lD ] AllT 10 m ≅ AllT 10 m' @ LL ].
Proof. intros HΔ Ha Hp Hm. pconv. Qed.
Ltac pfam_ty ::= first [ pfam_list | ty_rule @AllT_wf_0 | ty_rule @AllT_wf_1 | ty_rule @AllT_wf_2 | ty_rule @AllT_wf_3 | ty_rule @AllT_wf_4 | ty_rule @AllT_wf_5 | ty_rule @AllT_wf_6 | ty_rule @AllT_wf_7 | ty_rule @AllT_wf_8 | ty_rule @AllT_wf_9 | ty_rule @AllT_wf_10 ].
Ltac pfam_conv ::= first [ conv_rule @AllT_conv_0 | conv_rule @AllT_conv_1 | conv_rule @AllT_conv_2 | conv_rule @AllT_conv_3 | conv_rule @AllT_conv_4 | conv_rule @AllT_conv_5 | conv_rule @AllT_conv_6 | conv_rule @AllT_conv_7 | conv_rule @AllT_conv_8 | conv_rule @AllT_conv_9 | conv_rule @AllT_conv_10 ].
Lemma AllT_wf_11 {Δ m} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 12 (tyU L0) (lsuc L0) -> in_ctx Δ 11 (tyPi L0 (lsuc L0) (tyEl L0 (var 12)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m : List 11 @ L0 ] -> [ G ; Δ ⊢[ lD ] AllT 11 m @ LL ].
Proof. intros HΔ Ha Hp Hm. pty. Qed.
Lemma AllT_conv_11 {Δ m m'} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 12 (tyU L0) (lsuc L0) -> in_ctx Δ 11 (tyPi L0 (lsuc L0) (tyEl L0 (var 12)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m ≅ m' : List 11 @ L0 ] -> [ G ; Δ ⊢[ lD ] AllT 11 m ≅ AllT 11 m' @ LL ].
Proof. intros HΔ Ha Hp Hm. pconv. Qed.
Ltac pfam_ty ::= first [ pfam_list | ty_rule @AllT_wf_0 | ty_rule @AllT_wf_1 | ty_rule @AllT_wf_2 | ty_rule @AllT_wf_3 | ty_rule @AllT_wf_4 | ty_rule @AllT_wf_5 | ty_rule @AllT_wf_6 | ty_rule @AllT_wf_7 | ty_rule @AllT_wf_8 | ty_rule @AllT_wf_9 | ty_rule @AllT_wf_10 | ty_rule @AllT_wf_11 ].
Ltac pfam_conv ::= first [ conv_rule @AllT_conv_0 | conv_rule @AllT_conv_1 | conv_rule @AllT_conv_2 | conv_rule @AllT_conv_3 | conv_rule @AllT_conv_4 | conv_rule @AllT_conv_5 | conv_rule @AllT_conv_6 | conv_rule @AllT_conv_7 | conv_rule @AllT_conv_8 | conv_rule @AllT_conv_9 | conv_rule @AllT_conv_10 | conv_rule @AllT_conv_11 ].
Lemma AllT_wf_12 {Δ m} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 13 (tyU L0) (lsuc L0) -> in_ctx Δ 12 (tyPi L0 (lsuc L0) (tyEl L0 (var 13)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m : List 12 @ L0 ] -> [ G ; Δ ⊢[ lD ] AllT 12 m @ LL ].
Proof. intros HΔ Ha Hp Hm. pty. Qed.
Lemma AllT_conv_12 {Δ m m'} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 13 (tyU L0) (lsuc L0) -> in_ctx Δ 12 (tyPi L0 (lsuc L0) (tyEl L0 (var 13)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m ≅ m' : List 12 @ L0 ] -> [ G ; Δ ⊢[ lD ] AllT 12 m ≅ AllT 12 m' @ LL ].
Proof. intros HΔ Ha Hp Hm. pconv. Qed.
Ltac pfam_ty ::= first [ pfam_list | ty_rule @AllT_wf_0 | ty_rule @AllT_wf_1 | ty_rule @AllT_wf_2 | ty_rule @AllT_wf_3 | ty_rule @AllT_wf_4 | ty_rule @AllT_wf_5 | ty_rule @AllT_wf_6 | ty_rule @AllT_wf_7 | ty_rule @AllT_wf_8 | ty_rule @AllT_wf_9 | ty_rule @AllT_wf_10 | ty_rule @AllT_wf_11 | ty_rule @AllT_wf_12 ].
Ltac pfam_conv ::= first [ conv_rule @AllT_conv_0 | conv_rule @AllT_conv_1 | conv_rule @AllT_conv_2 | conv_rule @AllT_conv_3 | conv_rule @AllT_conv_4 | conv_rule @AllT_conv_5 | conv_rule @AllT_conv_6 | conv_rule @AllT_conv_7 | conv_rule @AllT_conv_8 | conv_rule @AllT_conv_9 | conv_rule @AllT_conv_10 | conv_rule @AllT_conv_11 | conv_rule @AllT_conv_12 ].

(** The codes, [El] of [⌜All⌝]'s reduct and the motive at each depth the
    eliminations reach, once. *)
Lemma AllC_wf_8 {Δ m} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 9 (tyU L0) (lsuc L0) -> in_ctx Δ 8 (tyPi L0 (lsuc L0) (tyEl L0 (var 9)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m : tyEl L0 (ListC 8) @ L0 ] -> [ G ; Δ ⊢[ lD ] AllC 8 m : tyU LL @ lsuc LL ].
Proof. intros HΔ Ha Hp Hm. ptm. Qed.
Lemma AllCr_conv_8 {Δ m m'} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 9 (tyU L0) (lsuc L0) -> in_ctx Δ 8 (tyPi L0 (lsuc L0) (tyEl L0 (var 9)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m ≅ m' : tyEl L0 (ListC 8) @ L0 ] ->
  [ G ; Δ ⊢[ lD ] tyIWf L0 L0 (tyEl L0 (ListC 8)) (tyEl L0 (ASC 8)) (AN 8) (AO 8) (AC 8) m ≅ AllT 8 m' @ LL ].
Proof. intros HΔ Ha Hp Hm. pconv. Qed.
Lemma AllC_wf_9 {Δ m} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 10 (tyU L0) (lsuc L0) -> in_ctx Δ 9 (tyPi L0 (lsuc L0) (tyEl L0 (var 10)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m : tyEl L0 (ListC 9) @ L0 ] -> [ G ; Δ ⊢[ lD ] AllC 9 m : tyU LL @ lsuc LL ].
Proof. intros HΔ Ha Hp Hm. ptm. Qed.
Lemma AllCr_conv_9 {Δ m m'} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 10 (tyU L0) (lsuc L0) -> in_ctx Δ 9 (tyPi L0 (lsuc L0) (tyEl L0 (var 10)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m ≅ m' : tyEl L0 (ListC 9) @ L0 ] ->
  [ G ; Δ ⊢[ lD ] tyIWf L0 L0 (tyEl L0 (ListC 9)) (tyEl L0 (ASC 9)) (AN 9) (AO 9) (AC 9) m ≅ AllT 9 m' @ LL ].
Proof. intros HΔ Ha Hp Hm. pconv. Qed.
Lemma AllC_wf_10 {Δ m} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 11 (tyU L0) (lsuc L0) -> in_ctx Δ 10 (tyPi L0 (lsuc L0) (tyEl L0 (var 11)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m : tyEl L0 (ListC 10) @ L0 ] -> [ G ; Δ ⊢[ lD ] AllC 10 m : tyU LL @ lsuc LL ].
Proof. intros HΔ Ha Hp Hm. ptm. Qed.
Lemma AllCr_conv_10 {Δ m m'} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 11 (tyU L0) (lsuc L0) -> in_ctx Δ 10 (tyPi L0 (lsuc L0) (tyEl L0 (var 11)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m ≅ m' : tyEl L0 (ListC 10) @ L0 ] ->
  [ G ; Δ ⊢[ lD ] tyIWf L0 L0 (tyEl L0 (ListC 10)) (tyEl L0 (ASC 10)) (AN 10) (AO 10) (AC 10) m ≅ AllT 10 m' @ LL ].
Proof. intros HΔ Ha Hp Hm. pconv. Qed.
Lemma AllC_wf_11 {Δ m} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 12 (tyU L0) (lsuc L0) -> in_ctx Δ 11 (tyPi L0 (lsuc L0) (tyEl L0 (var 12)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m : tyEl L0 (ListC 11) @ L0 ] -> [ G ; Δ ⊢[ lD ] AllC 11 m : tyU LL @ lsuc LL ].
Proof. intros HΔ Ha Hp Hm. ptm. Qed.
Lemma AllCr_conv_11 {Δ m m'} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 12 (tyU L0) (lsuc L0) -> in_ctx Δ 11 (tyPi L0 (lsuc L0) (tyEl L0 (var 12)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m ≅ m' : tyEl L0 (ListC 11) @ L0 ] ->
  [ G ; Δ ⊢[ lD ] tyIWf L0 L0 (tyEl L0 (ListC 11)) (tyEl L0 (ASC 11)) (AN 11) (AO 11) (AC 11) m ≅ AllT 11 m' @ LL ].
Proof. intros HΔ Ha Hp Hm. pconv. Qed.
Lemma AllC_wf_12 {Δ m} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 13 (tyU L0) (lsuc L0) -> in_ctx Δ 12 (tyPi L0 (lsuc L0) (tyEl L0 (var 13)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m : tyEl L0 (ListC 12) @ L0 ] -> [ G ; Δ ⊢[ lD ] AllC 12 m : tyU LL @ lsuc LL ].
Proof. intros HΔ Ha Hp Hm. ptm. Qed.
Lemma AllCr_conv_12 {Δ m m'} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 13 (tyU L0) (lsuc L0) -> in_ctx Δ 12 (tyPi L0 (lsuc L0) (tyEl L0 (var 13)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m ≅ m' : tyEl L0 (ListC 12) @ L0 ] ->
  [ G ; Δ ⊢[ lD ] tyIWf L0 L0 (tyEl L0 (ListC 12)) (tyEl L0 (ASC 12)) (AN 12) (AO 12) (AC 12) m ≅ AllT 12 m' @ LL ].
Proof. intros HΔ Ha Hp Hm. pconv. Qed.
Lemma AllC_wf_13 {Δ m} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 14 (tyU L0) (lsuc L0) -> in_ctx Δ 13 (tyPi L0 (lsuc L0) (tyEl L0 (var 14)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m : tyEl L0 (ListC 13) @ L0 ] -> [ G ; Δ ⊢[ lD ] AllC 13 m : tyU LL @ lsuc LL ].
Proof. intros HΔ Ha Hp Hm. ptm. Qed.
Lemma AllCr_conv_13 {Δ m m'} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 14 (tyU L0) (lsuc L0) -> in_ctx Δ 13 (tyPi L0 (lsuc L0) (tyEl L0 (var 14)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m ≅ m' : tyEl L0 (ListC 13) @ L0 ] ->
  [ G ; Δ ⊢[ lD ] tyIWf L0 L0 (tyEl L0 (ListC 13)) (tyEl L0 (ASC 13)) (AN 13) (AO 13) (AC 13) m ≅ AllT 13 m' @ LL ].
Proof. intros HΔ Ha Hp Hm. pconv. Qed.
Lemma AllC_wf_14 {Δ m} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 15 (tyU L0) (lsuc L0) -> in_ctx Δ 14 (tyPi L0 (lsuc L0) (tyEl L0 (var 15)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m : tyEl L0 (ListC 14) @ L0 ] -> [ G ; Δ ⊢[ lD ] AllC 14 m : tyU LL @ lsuc LL ].
Proof. intros HΔ Ha Hp Hm. ptm. Qed.
Lemma AllCr_conv_14 {Δ m m'} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 15 (tyU L0) (lsuc L0) -> in_ctx Δ 14 (tyPi L0 (lsuc L0) (tyEl L0 (var 15)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] m ≅ m' : tyEl L0 (ListC 14) @ L0 ] ->
  [ G ; Δ ⊢[ lD ] tyIWf L0 L0 (tyEl L0 (ListC 14)) (tyEl L0 (ASC 14)) (AN 14) (AO 14) (AC 14) m ≅ AllT 14 m' @ LL ].
Proof. intros HΔ Ha Hp Hm. pconv. Qed.
Ltac pfam_tm ::= first [ tm_rule @AllC_wf_8 | tm_rule @AllC_wf_9 | tm_rule @AllC_wf_10 | tm_rule @AllC_wf_11 | tm_rule @AllC_wf_12 | tm_rule @AllC_wf_13 | tm_rule @AllC_wf_14 ].
Ltac pfam_conv ::= first [ conv_rule @AllT_conv_0 | conv_rule @AllT_conv_1 | conv_rule @AllT_conv_2 | conv_rule @AllT_conv_3 | conv_rule @AllT_conv_4 | conv_rule @AllT_conv_5 | conv_rule @AllT_conv_6 | conv_rule @AllT_conv_7 | conv_rule @AllT_conv_8 | conv_rule @AllT_conv_9 | conv_rule @AllT_conv_10 | conv_rule @AllT_conv_11 | conv_rule @AllT_conv_12 | conv_rule @AllCr_conv_8 | conv_rule @AllCr_conv_9 | conv_rule @AllCr_conv_10 | conv_rule @AllCr_conv_11 | conv_rule @AllCr_conv_12 | conv_rule @AllCr_conv_13 | conv_rule @AllCr_conv_14 ].
Lemma MallT_wf_6 {Δ j} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 7 (tyU L0) (lsuc L0) -> in_ctx Δ 6 (tyPi L0 (lsuc L0) (tyEl L0 (var 7)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] j : List 6 @ L0 ] -> [ G ; Δ ⊢[ lD ] MallT 6 j @ LL ].
Proof. intros HΔ Ha Hp Hm. pty. Qed.
Lemma MallT_wf_7 {Δ j} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 8 (tyU L0) (lsuc L0) -> in_ctx Δ 7 (tyPi L0 (lsuc L0) (tyEl L0 (var 8)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] j : List 7 @ L0 ] -> [ G ; Δ ⊢[ lD ] MallT 7 j @ LL ].
Proof. intros HΔ Ha Hp Hm. pty. Qed.
Lemma MallT_wf_8 {Δ j} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 9 (tyU L0) (lsuc L0) -> in_ctx Δ 8 (tyPi L0 (lsuc L0) (tyEl L0 (var 9)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] j : List 8 @ L0 ] -> [ G ; Δ ⊢[ lD ] MallT 8 j @ LL ].
Proof. intros HΔ Ha Hp Hm. pty. Qed.
Lemma MallT_wf_9 {Δ j} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 10 (tyU L0) (lsuc L0) -> in_ctx Δ 9 (tyPi L0 (lsuc L0) (tyEl L0 (var 10)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ⊢[ lD ] j : List 9 @ L0 ] -> [ G ; Δ ⊢[ lD ] MallT 9 j @ LL ].
Proof. intros HΔ Ha Hp Hm. pty. Qed.

Ltac pfam_ty ::= first [ pfam_list | ty_rule @AllT_wf_0 | ty_rule @AllT_wf_1 | ty_rule @AllT_wf_2 | ty_rule @AllT_wf_3 | ty_rule @AllT_wf_4 | ty_rule @AllT_wf_5 | ty_rule @AllT_wf_6 | ty_rule @AllT_wf_7 | ty_rule @AllT_wf_8 | ty_rule @AllT_wf_9 | ty_rule @AllT_wf_10 | ty_rule @AllT_wf_11 | ty_rule @AllT_wf_12 | ty_rule @MallT_wf_6 | ty_rule @MallT_wf_7 | ty_rule @MallT_wf_8 | ty_rule @MallT_wf_9 ].

(** The step, typed once in its telescope at the depth the tests use
    (as [IwfLowering2.v]'s steps): the hook normalizes the lemma's
    statement as the checker normalizes goals, and fires at the step's
    head only. *)
Ltac pstep L := let H := fresh "Hstep" in pose proof L as H; pn_in H; eapply H; pgoal.
Lemma tailStep_wf_4 {Δ} : [ G ; Δ ⊢[ lD ] ] -> in_ctx Δ 5 (tyU L0) (lsuc L0) -> in_ctx Δ 4 (tyPi L0 (lsuc L0) (tyEl L0 (var 5)) (tyU L0)) (lmax L0 (lsuc L0)) ->
  [ G ; Δ ,, AS 4 @ L0 ,, iwfcsty L0 L0 (List 4) (AS 4) (AN 4) (AO 4) (AC 4) @ LL
      ,, iwfihty L0 L0 LL (List 4) (AS 4) (AN 4) (AO 4) (AC 4) (MallT 6 (var 1)) @ lmax L0 LL
      ⊢[ lD ] tailStep 7 : iwfstepty L0 L0 (List 4) (AS 4) (AN 4) (AO 4) (AC 4) (MallT 6 (var 1)) @ LL ].
Proof. intros HΔ Ha Hp. ptm. Qed.
Ltac pfam_step :=
  lazymatch goal with
  | |- [ _ ; _ ⊢[ _ ] app (tmCase L0 L0 LL U0 _ _ _ _ (var 2)) LL LL _ _ (var 1) : _ @ _ ] =>
      pstep @tailStep_wf_4
  end.
Ltac pfam_tm ::= first [ pfam_step | tm_rule @AllC_wf_8 | tm_rule @AllC_wf_9 | tm_rule @AllC_wf_10 | tm_rule @AllC_wf_11 | tm_rule @AllC_wf_12 | tm_rule @AllC_wf_13 | tm_rule @AllC_wf_14 ].

(** *** The codes *)

Lemma allC_ty : [ G ; ΓP ,, List 0 @ L0 ⊢[ lD ] AllC 1 (var 0) : tyU LL @ lsuc LL ].
Proof. ptm. Qed.

(** [El ⌜All P m⌝ ≅ All P m]: [El] of the codes' components. *)
Lemma allC_el : [ G ; ΓP ,, List 0 @ L0 ⊢[ lD ] tyEl LL (AllC 1 (var 0)) ≅ AllT 1 (var 0) @ LL ].
Proof. pconv. Qed.

(** *** [allTail]: typing and β *)

(** At [ΓPc]'s depth, so that one step lemma serves both ([px] is unused). *)
Lemma allTail_wf : [ G ; ΓP ,, List 0 @ L0 ,, elA 1 @ L0 ,, tyEl L0 (pAt 2 (var 0)) @ L0
                       ,, AllT 3 (lcons 3 (var 1) (var 2)) @ LL ⊢[ lD ]
                     allTail 4 (lcons 4 (var 2) (var 3)) (var 0) : AllT 4 (var 3) @ LL ].
Proof. ptm. Qed.

(** [allTail (allCons xs x px rest) ≡ rest], everything open. *)
Lemma allTail_beta : [ G ; ΓPc ⊢[ lD ] allTail 4 (lcons 4 (var 2) (var 3)) (allCons 4 (var 3) (var 2) (var 1) (var 0))
                       ≅ var 0 : AllT 4 (var 3) @ LL ].
Proof. ptmconv. Qed.

End Probe3.

(** No axioms: each headline lemma is closed under the global context. *)
Print Assumptions allC_el.
Print Assumptions allTail_wf.
Print Assumptions allTail_beta.
