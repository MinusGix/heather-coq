(** * Consequences for the declarative system

    M2 transition: stated at layer P and for global contexts binding
    context variables only (see [fundamental]); the layered relation will
    restore layer M and global term/type bindings. *)
From DeLaM.Typing Require Export DeclInstance.
From DeLaM.Validity Require Export Consequences.

Section DeclConsequences.

Local Notation DE := (DeclEq lD compt_D).
Local Notation DEL := (DeclEqLaws lD compt_D).

Theorem decl_pi_inj {G Γ l l1 l2 l3 l4 A A' B B'} : ctx_only G ->
  [ G ; Γ ⊢[ lD ] tyPi l1 l2 A B ≅ tyPi l3 l4 A' B' @ l ] ->
  lequiv (gL G) l3 l1 /\ lequiv (gL G) l4 l2 /\
  [ G ; Γ ⊢[ lD ] A ≅ A' @ l1 ] /\ [ G ; Γ ,, A @ l1 ⊢[ lD ] B ≅ B' @ l2 ].
Proof. exact (@pi_inj DE DEL eq_refl G Γ l l1 l2 l3 l4 A A' B B'). Qed.

Theorem decl_U_inj {G Γ l l' k} : ctx_only G -> [ G ; Γ ⊢[ lD ] tyU l ≅ tyU l' @ k ] -> lequiv (gL G) l' l.
Proof. exact (@U_inj DE DEL eq_refl G Γ l l' k). Qed.

Theorem decl_whnf_normalization_tm {G Γ t T l} : ctx_only G -> [ G ; Γ ⊢[ lD ] t : T @ l ] ->
  exists w, reds t w /\ whnf w.
Proof.
  intros HG H. destruct (@whnf_normalization_tm DE DEL eq_refl G Γ t T l HG H) as (w & Hw & Hwh).
  exists w; split; [exact (tmred_red _ _ _ _ _ _ _ Hw) | exact Hwh].
Qed.

Theorem decl_whnf_normalization_ty {G Γ T l} : ctx_only G -> [ G ; Γ ⊢[ lD ] T @ l ] ->
  exists W, reds_ty T W /\ whnf_ty W.
Proof.
  intros HG H. destruct (@whnf_normalization_ty DE DEL eq_refl G Γ T l HG H) as (W & HW & HWh).
  exists W; split; [exact (tyred_red _ _ _ _ _ _ HW) | exact HWh].
Qed.

Theorem decl_closed_nat_canonicity {G t} : ctx_only G -> [ G ; cnil ⊢[ lD ] t : tyNat @ lzero ] ->
  exists n, [ G ; cnil ⊢[ lD ] t ≅ numeral n : tyNat @ lzero ].
Proof. exact (@closed_nat_canonicity DE DEL eq_refl G t). Qed.

Theorem decl_nat_not_pi {G Γ k l l' A B} : ctx_only G -> ~ [ G ; Γ ⊢[ lD ] tyNat ≅ tyPi l l' A B @ k ].
Proof. exact (@nat_not_pi DE DEL eq_refl G Γ k l l' A B). Qed.
Theorem decl_nat_not_U {G Γ k l} : ctx_only G -> ~ [ G ; Γ ⊢[ lD ] tyNat ≅ tyU l @ k ].
Proof. exact (@nat_not_U DE DEL eq_refl G Γ k l). Qed.
Theorem decl_U_not_pi {G Γ k l l1 l2 A B} : ctx_only G -> ~ [ G ; Γ ⊢[ lD ] tyU l ≅ tyPi l1 l2 A B @ k ].
Proof. exact (@U_not_pi DE DEL eq_refl G Γ k l l1 l2 A B). Qed.

End DeclConsequences.
