(** * Uniform statements over the computing layers (M7_DESIGN.md B2)

    The D and M consequences were proved separately ([decl_*], [declM_*]).
    Here they are stated once for [compt i], together with the
    characterization of declarative equality by the algorithm and
    decidability for types at possibly different levels. Injectivity of [Π]
    and [U] and head discrimination already have [compt i] forms
    ([pi_inj_c], [U_inj_c], [decl_head_c]). *)
From DeLaM.Validity Require Export RecReduct AlgDec.

(** ** Normalization, with the equation *)

Theorem whnf_normalization_ty_c {G i Γ T k} : compt i -> [ G ; Γ ⊢[ i ] T @ k ] ->
  exists W, reds_ty T W /\ whnf_ty W /\ [ G ; Γ ⊢[ i ] T ≅ W @ k ].
Proof. apply tgt_whnf. Qed.

Theorem whnf_normalization_tm_c {G i Γ t T k} : compt i -> [ G ; Γ ⊢[ i ] t : T @ k ] ->
  exists w, reds t w /\ whnf w /\ [ G ; Γ ⊢[ i ] t ≅ w : T @ k ].
Proof.
  intros Hc Ht. destruct (tgt_whnf_tm i Hc Ht) as (w & Hr & Hw).
  exists w. exact (conj Hr (conj Hw (reductions_sound_tm Hc Ht Hr))).
Qed.

(** ** Closed canonicity at [Nat] *)

Theorem closed_nat_canonicity_c {G i t} : compt i -> ctx_only G -> [ G ; cnil ⊢[ i ] t : tyNat @ lzero ] ->
  exists n, [ G ; cnil ⊢[ i ] t ≅ numeral n : tyNat @ lzero ].
Proof. intros [-> | ->]; [apply decl_closed_nat_canonicity | apply declM_closed_nat_canonicity]. Qed.

(** ** Declarative equality is the algorithm's *)

Theorem ac_ty_iff {G i Γ T T' k} : compt i -> [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T' @ k ] ->
  ac_ty G Γ T T' <-> [ G ; Γ ⊢[ i ] T ≅ T' @ k ].
Proof. intros Hc HT HT'. split; [intros D; exact (ac_ty_sound Hc D HT HT') | exact (ac_complete_ty Hc)]. Qed.

Theorem ac_tm_iff {G i Γ t t' T k} : compt i -> [ G ; Γ ⊢[ i ] t : T @ k ] -> [ G ; Γ ⊢[ i ] t' : T @ k ] ->
  ac_tm G Γ t t' T <-> [ G ; Γ ⊢[ i ] t ≅ t' : T @ k ].
Proof. intros Hc Ht Ht'. split; [intros D; exact (ac_tm_sound Hc D Ht Ht') | exact (ac_complete_tm Hc)]. Qed.

(** ** Decidability for types at different levels

    Equal types are well formed at the judgment's level, and a type's
    level is unique up to equivalence ([ty_lvl_uniq]). *)

Lemma lvl_eq_syn_dec (k k' : lvl) : {k = k'} + {k <> k'}.
Proof. decide equality; apply Nat.eq_dec. Defined.

Theorem decl_eqty_dec_lv {G i Γ T T' k k'} : compt i -> [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T' @ k' ] ->
  Dec ([ G ; Γ ⊢[ i ] T ≅ T' @ k ]).
Proof.
  intros Hc HT HT'. pose proof (compt_typeof_self _ Hc) as Hi.
  assert (HL : Dec (k' = k \/ lequiv (gL G) k' k)).
  { destruct (lvl_eq_syn_dec k' k) as [E | E]; [left; left; exact E |].
    destruct (lequiv_dec (gL G) k' k) as [Q | Q]; [left; right; exact Q | right; intros [X | X]; contradiction]. }
  destruct HL as [[-> | Q] | N].
  - exact (decl_eqty_dec Hc HT HT').
  - exact (decl_eqty_dec Hc HT (wft_lconv _ _ _ _ _ _ HT' (lequiv_sym _ _ _ Q))).
  - right; intros E. apply N.
    destruct (ty_lvl_uniq HT' (eqty_wf_r Hi E)) as [X | X]; [left; exact X | right; exact X].
Qed.
