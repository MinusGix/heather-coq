(** * Consequences for the declarative system (at a computing layer) *)
From DeLaM.Typing Require Export DeclInstance.
From DeLaM.Validity Require Export Consequences.

Section DeclConsequences.
Context (i : layer) (Hi : compt i).

Theorem decl_pi_inj {G Γ l l1 l2 l3 l4 A A' B B'} :
  [ G ; Γ ⊢[ i ] tyPi l1 l2 A B ≅ tyPi l3 l4 A' B' @ l ] ->
  lequiv (gL G) l3 l1 /\ lequiv (gL G) l4 l2 /\
  [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] /\ [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ].
Proof. exact (@pi_inj (DeclEq i Hi) (DeclEqLaws i Hi) G Γ l l1 l2 l3 l4 A A' B B'). Qed.

Theorem decl_U_inj {G Γ l l' k} : [ G ; Γ ⊢[ i ] tyU l ≅ tyU l' @ k ] -> lequiv (gL G) l' l.
Proof. exact (@U_inj (DeclEq i Hi) (DeclEqLaws i Hi) G Γ l l' k). Qed.

Theorem decl_whnf_normalization_tm {G Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] ->
  exists w, reds t w /\ whnf w.
Proof.
  intros H. destruct (@whnf_normalization_tm (DeclEq i Hi) (DeclEqLaws i Hi) G Γ t T l H)
    as (w & Hw & Hwh).
  exists w; split; [exact (tmred_red _ _ _ _ _ _ _ Hw) | exact Hwh].
Qed.

Theorem decl_whnf_normalization_ty {G Γ T l} : [ G ; Γ ⊢[ i ] T @ l ] ->
  exists W, reds_ty T W /\ whnf_ty W.
Proof.
  intros H. destruct (@whnf_normalization_ty (DeclEq i Hi) (DeclEqLaws i Hi) G Γ T l H)
    as (W & HW & HWh).
  exists W; split; [exact (tyred_red _ _ _ _ _ _ HW) | exact HWh].
Qed.

End DeclConsequences.
