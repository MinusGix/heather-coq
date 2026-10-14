(** * Consequences for the declarative system at P

    At layer P ([DeclEq lD]) and at layer M ([DeclEq lM], relation
    [LR_M]), for arbitrary well-formed global contexts: reducibility
    comes from the fundamental theorems with global substitutions
    ([Reducible]).  Closed canonicity needs a global context without type
    or term bindings: context variables, and at P definitions too
    ([closed_ok]); an opaque global variable would be a closed neutral. *)
From DeLaM.Typing Require Export DeclInstance.
From DeLaM.Validity Require Export ReducibleP.

Section DeclConsequencesP.

Local Notation DEP := (DeclEq lD compt_D).
Local Notation DELP := (DeclEqLaws lD compt_D).
Local Notation DEM := (DeclEq lM compt_M).
Local Notation DELM := (DeclEqLaws lM compt_M).
Local Notation LRM := (LR_M DEP DEM).

Local Instance DeclEqM_inst : GenericEqM DEP DEM := DeclEqM.
Local Instance LRM_laws : VPLaws (@lr_vp LRM) := vpM_laws DEP DEM.

(** ** Reducibility *)

Lemma redP_eqty G Γ T T' l : [ G ; Γ ⊢[ lD ] T ≅ T' @ l ] -> @LRty DEP LR_P l G Γ T T'.
Proof. intros H; exact (proj1 (reducibleP_eqty DEP DEM H)). Qed.
Lemma redP_eqtm G Γ t t' T l : [ G ; Γ ⊢[ lD ] t ≅ t' : T @ l ] -> @LRtm DEP LR_P l G Γ T T t t'.
Proof. intros H; exact (proj1 (reducibleP_eqtm DEP DEM H)). Qed.

Local Definition redP_ty G Γ T T' l (H : [ G ; Γ ⊢[ lD ] T ≅ T' @ l ]) (_ : lwf (gL G) l) :=
  redP_eqty G Γ T T' l H.
Local Definition redP_tm G Γ t t' T l (H : [ G ; Γ ⊢[ lD ] t ≅ t' : T @ l ]) (_ : lwf (gL G) l) :=
  redP_eqtm G Γ t t' T l H.

(** Levels at P are well formed (ω is at M only). *)
Lemma lwfD_ty {G Γ T l} : [ G ; Γ ⊢[ lD ] T @ l ] -> lwf (gL G) l.
Proof. intros H. destruct (proj1 (proj2 (proj2 judg_lvl)) _ _ _ _ _ H) as [? | [E _]]; [assumption | discriminate E]. Qed.
Lemma lwfD_tm {G Γ t T l} : [ G ; Γ ⊢[ lD ] t : T @ l ] -> lwf (gL G) l.
Proof.
  intros H. destruct (proj1 (proj2 (proj2 (proj2 judg_lvl))) _ _ _ _ _ _ H) as [? | [E _]];
    [assumption | discriminate E].
Qed.
Lemma lwfD_eqty {G Γ T T' l} : [ G ; Γ ⊢[ lD ] T ≅ T' @ l ] -> lwf (gL G) l.
Proof.
  intros H. destruct (proj1 (proj2 (proj2 (proj2 (proj2 judg_lvl)))) _ _ _ _ _ _ H) as [? | [E _]];
    [assumption | discriminate E].
Qed.

(** ** Layer P *)

Theorem decl_pi_inj {G Γ l l1 l2 l3 l4 A A' B B'} :
  [ G ; Γ ⊢[ lD ] tyPi l1 l2 A B ≅ tyPi l3 l4 A' B' @ l ] ->
  lequiv (gL G) l3 l1 /\ lequiv (gL G) l4 l2 /\
  [ G ; Γ ⊢[ lD ] A ≅ A' @ l1 ] /\ [ G ; Γ ,, A @ l1 ⊢[ lD ] B ≅ B' @ l2 ].
Proof. intros H; exact (pi_inj (E := DEP) (LP := LR_P) redP_ty H (lwfD_eqty H)). Qed.

Theorem decl_sig_inj {G Γ l l1 l2 l3 l4 A A' B B'} :
  [ G ; Γ ⊢[ lD ] tySig l1 l2 A B ≅ tySig l3 l4 A' B' @ l ] ->
  lequiv (gL G) l3 l1 /\ lequiv (gL G) l4 l2 /\
  [ G ; Γ ⊢[ lD ] A ≅ A' @ l1 ] /\ [ G ; Γ ,, A @ l1 ⊢[ lD ] B ≅ B' @ l2 ].
Proof. intros H; exact (sig_inj (E := DEP) (LP := LR_P) redP_ty H (lwfD_eqty H)). Qed.

Theorem decl_unit_inj {G Γ l l1 l2} :
  [ G ; Γ ⊢[ lD ] tyUnit l1 ≅ tyUnit l2 @ l ] -> lequiv (gL G) l2 l1.
Proof. intros H; exact (unit_inj (E := DEP) (LP := LR_P) redP_ty H (lwfD_eqty H)). Qed.

Theorem decl_id_inj {G Γ l l1 l2 A A' a a' b b'} :
  [ G ; Γ ⊢[ lD ] tyId l1 A a b ≅ tyId l2 A' a' b' @ l ] ->
  lequiv (gL G) l2 l1 /\ [ G ; Γ ⊢[ lD ] A ≅ A' @ l1 ] /\
  [ G ; Γ ⊢[ lD ] a ≅ a' : A @ l1 ] /\ [ G ; Γ ⊢[ lD ] b ≅ b' : A @ l1 ].
Proof. intros H; exact (id_inj (E := DEP) (LP := LR_P) redP_ty H (lwfD_eqty H)). Qed.

Theorem decl_sum_inj {G Γ l l1 l2 l3 l4 A A' B B'} :
  [ G ; Γ ⊢[ lD ] tySum l1 l2 A B ≅ tySum l3 l4 A' B' @ l ] ->
  lequiv (gL G) l3 l1 /\ lequiv (gL G) l4 l2 /\ [ G ; Γ ⊢[ lD ] A ≅ A' @ l1 ] /\ [ G ; Γ ⊢[ lD ] B ≅ B' @ l2 ].
Proof. intros H; exact (sum_inj (E := DEP) (LP := LR_P) redP_ty H (lwfD_eqty H)). Qed.

Theorem decl_W_inj {G Γ l l1 l2 l3 l4 A A' B B'} :
  [ G ; Γ ⊢[ lD ] tyW l1 l2 A B ≅ tyW l3 l4 A' B' @ l ] ->
  lequiv (gL G) l3 l1 /\ lequiv (gL G) l4 l2 /\
  [ G ; Γ ⊢[ lD ] A ≅ A' @ l1 ] /\ [ G ; Γ ,, A @ l1 ⊢[ lD ] B ≅ B' @ l2 ].
Proof. intros H; exact (W_inj (E := DEP) (LP := LR_P) redP_ty H (lwfD_eqty H)). Qed.

Theorem decl_sq_inj {G Γ l l1 l2 A A'} :
  [ G ; Γ ⊢[ lD ] tySq l1 A ≅ tySq l2 A' @ l ] -> lequiv (gL G) l2 l1 /\ [ G ; Γ ⊢[ lD ] A ≅ A' @ l1 ].
Proof. intros H; exact (sq_inj (E := DEP) (LP := LR_P) redP_ty H (lwfD_eqty H)). Qed.

Theorem decl_Wf_inj {G Γ l l1 l2 A A' N N'} :
  [ G ; Γ ⊢[ lD ] tyWf l1 A N ≅ tyWf l2 A' N' @ l ] ->
  lequiv (gL G) l2 l1 /\ [ G ; Γ ⊢[ lD ] A ≅ A' @ l1 ] /\ [ G ; Γ ,, A @ l1 ⊢[ lD ] N ≅ N' : tyNat @ lzero ].
Proof. intros H; exact (Wf_inj (E := DEP) (LP := LR_P) redP_ty H (lwfD_eqty H)). Qed.

Theorem decl_IWf_inj {G Γ l l1 li1 l2 li2 X X' A A' N N' Ot Ot' C C' m m'} :
  [ G ; Γ ⊢[ lD ] tyIWf l1 li1 X A N Ot C m ≅ tyIWf l2 li2 X' A' N' Ot' C' m' @ l ] ->
  lequiv (gL G) l2 l1 /\ lequiv (gL G) li2 li1 /\ [ G ; Γ ⊢[ lD ] X ≅ X' @ li1 ] /\ [ G ; Γ ⊢[ lD ] A ≅ A' @ l1 ] /\
  [ G ; Γ ,, A @ l1 ⊢[ lD ] N ≅ N' : tyNat @ lzero ] /\ [ G ; Γ ,, A @ l1 ⊢[ lD ] Ot ≅ Ot' : X⟨↑⟩ @ li1 ] /\
  [ G ; Γ ,, A @ l1 ,, tyFin N @ lzero ⊢[ lD ] C ≅ C' : X⟨↑⟩⟨↑⟩ @ li1 ] /\ [ G ; Γ ⊢[ lD ] m ≅ m' : X @ li1 ].
Proof. intros H; exact (IWf_inj (E := DEP) (LP := LR_P) redP_ty H (lwfD_eqty H)). Qed.

Theorem decl_seq_inj {G Γ l l1 l2 A A' a a' b b'} :
  [ G ; Γ ⊢[ lD ] tySEq l1 A a b ≅ tySEq l2 A' a' b' @ l ] ->
  lequiv (gL G) l2 l1 /\ [ G ; Γ ⊢[ lD ] A ≅ A' @ l1 ] /\
  [ G ; Γ ⊢[ lD ] a ≅ a' : A @ l1 ] /\ [ G ; Γ ⊢[ lD ] b ≅ b' : A @ l1 ].
Proof. intros H; exact (seq_inj (E := DEP) (LP := LR_P) redP_ty H (lwfD_eqty H)). Qed.

Theorem decl_pi_red {G Γ l l1 l2 A B T} : [ G ; Γ ⊢[ lD ] tyPi l1 l2 A B ≅ T @ l ] ->
  exists l3 l4 C D, [ G ; Γ ⊢[ lD ] T ⤳* tyPi l3 l4 C D @ l ].
Proof. intros H; exact (pi_red (E := DEP) (LP := LR_P) redP_ty H (lwfD_eqty H)). Qed.

Theorem decl_U_inj {G Γ l l' k} : [ G ; Γ ⊢[ lD ] tyU l ≅ tyU l' @ k ] -> lequiv (gL G) l' l.
Proof. intros H; exact (U_inj (E := DEP) (LP := LR_P) redP_ty H (lwfD_eqty H)). Qed.

(** Convertible whnf types have the same head (M6_DESIGN.md step 4). *)
Theorem decl_head {G Γ W W' l} : [ G ; Γ ⊢[ lD ] W ≅ W' @ l ] -> whnf_ty W -> whnf_ty W' ->
  ty_head W = ty_head W'.
Proof. intros H; exact (eqty_head (E := DEP) (LP := LR_P) redP_ty H (lwfD_eqty H)). Qed.

Theorem decl_whnf_normalization_tm {G Γ t T l} : [ G ; Γ ⊢[ lD ] t : T @ l ] ->
  exists w, reds t w /\ whnf w.
Proof.
  intros H. destruct (whnf_normalization_tm (E := DEP) (LP := LR_P) redP_tm H (lwfD_tm H)) as (w & Hw & Hwh).
  exists w; split; [exact (tmred_red _ _ _ _ _ _ _ Hw) | exact Hwh].
Qed.

Theorem decl_whnf_normalization_ty {G Γ T l} : [ G ; Γ ⊢[ lD ] T @ l ] ->
  exists W, reds_ty T W /\ whnf_ty W.
Proof.
  intros H. destruct (whnf_normalization_ty (E := DEP) (LP := LR_P) redP_ty H (lwfD_ty H)) as (W & HW & HWh).
  exists W; split; [exact (tyred_red _ _ _ _ _ _ HW) | exact HWh].
Qed.

(** The typed forms (the reduction with its equation), for the soundness of
    algorithmic conversion (M6_DESIGN.md H6). *)
Theorem decl_whnf_tyred {G Γ T l} : [ G ; Γ ⊢[ lD ] T @ l ] ->
  exists W, [ G ; Γ ⊢[ lD ] T ⤳* W @ l ] /\ whnf_ty W.
Proof. intros H. exact (whnf_normalization_ty (E := DEP) (LP := LR_P) redP_ty H (lwfD_ty H)). Qed.

Theorem decl_whnf_tmred {G Γ t T l} : [ G ; Γ ⊢[ lD ] t : T @ l ] ->
  exists w, [ G ; Γ ⊢[ lD ] t ⤳* w : T @ l ] /\ whnf w.
Proof. intros H. exact (whnf_normalization_tm (E := DEP) (LP := LR_P) redP_tm H (lwfD_tm H)). Qed.

Theorem decl_closed_nat_canonicity {G t} : closed_ok lD G -> [ G ; cnil ⊢[ lD ] t : tyNat @ lzero ] ->
  exists n, [ G ; cnil ⊢[ lD ] t ≅ numeral n : tyNat @ lzero ].
Proof. exact (closed_nat_canonicity (E := DEP) (LP := LR_P) redP_tm). Qed.

Theorem decl_nat_not_pi {G Γ k l l' A B} : ~ [ G ; Γ ⊢[ lD ] tyNat ≅ tyPi l l' A B @ k ].
Proof. intros H; exact (nat_not_pi (E := DEP) (LP := LR_P) redP_ty (lwfD_eqty H) H). Qed.
Theorem decl_nat_not_U {G Γ k l} : ~ [ G ; Γ ⊢[ lD ] tyNat ≅ tyU l @ k ].
Proof. intros H; exact (nat_not_U (E := DEP) (LP := LR_P) redP_ty (lwfD_eqty H) H). Qed.
Theorem decl_U_not_pi {G Γ k l l1 l2 A B} : ~ [ G ; Γ ⊢[ lD ] tyU l ≅ tyPi l1 l2 A B @ k ].
Proof. intros H; exact (U_not_pi (E := DEP) (LP := LR_P) redP_ty (lwfD_eqty H) H). Qed.

End DeclConsequencesP.
