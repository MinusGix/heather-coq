(** * Soundness of reduction and preservation (06:148, 06:264; M7_DESIGN.md A2)

    M1 typed reduction by carrying its equation (TypedRed), because β needs
    Π-injectivity. With injectivity available (the consequences of the
    fundamental theorems), the paper's statements hold for plain untyped
    reduction: at a computing layer, a typed term (type) is equal to its
    one-step reduct, which is therefore typed (well formed) at the same
    type and level.

    Each redex is inverted; its annotations are related to the inverted
    typing's by injectivity, and the β rule applies at the inverted
    annotations, congruence moving back to the redex's. A recursor's
    β-reduct is typed by the hypothesis [RecRedTyped], a premise of the
    theorems here. *)
From DeLaM.Validity Require Export Canonicity.
From DeLaM.Typing Require Import IWfIH.

(* the Σ rules ask for [i <> lV] (M8d); a computing layer is not V *)
Local Hint Resolve compt_notV : core.

(** ** Levels and types of an inverted typing *)

Lemma retype_eqtm {G i Γ t t' T A k l} : typeof i = i -> [ G ; Γ ⊢[ i ] t ≅ t' : A @ l ] ->
  lvl_eq (gL G) k l -> [ G ; Γ ⊢[ i ] T ≅ A @ k ] -> [ G ; Γ ⊢[ i ] t ≅ t' : T @ k ].
Proof.
  intros Hi E Hk ET. eapply eqtm_conv; [| rewrite Hi; exact ET].
  destruct Hk as [-> | Hk]; [exact E | exact (eqtm_lconv _ _ _ _ _ _ _ _ E Hk)].
Qed.

Lemma retype_eqty {G i Γ T T' k l} : lvl_eq (gL G) k l -> [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> [ G ; Γ ⊢[ i ] T ≅ T' @ k ].
Proof. intros [-> | Hk] E; [exact E | exact (eqty_lconv _ _ _ _ _ _ _ E Hk)]. Qed.

Lemma U_inj_c {G i Γ l l' k} : compt i -> [ G ; Γ ⊢[ i ] tyU l ≅ tyU l' @ k ] -> lequiv (gL G) l' l.
Proof. intros [-> | ->]; [apply decl_U_inj | apply declM_U_inj]. Qed.

(** ** The statements *)

Definition RS_tm (t t' : tm) : Prop := forall G i Γ T k, compt i ->
  [ G ; Γ ⊢[ i ] t : T @ k ] -> [ G ; Γ ⊢[ i ] t ≅ t' : T @ k ].
Definition RS_ty (T T' : ty) : Prop := forall G i Γ k, compt i ->
  [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T ≅ T' @ k ].

(** ** Natural numbers and functions *)

Lemma RS_natrec_zero l M s z : RS_tm (natrec l M s z zero) s.
Proof.
  intros G i Γ T k Hc Ht. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_natrec Hi Ht) as ((Hv & Wl & HM & Hs & Hz & H0) & Hk & ET).
  exact (retype_eqtm Hi (eqtm_natrec_zero _ _ _ _ _ _ _ Hc Wl HM Hs Hz) Hk ET).
Qed.

Lemma RS_natrec_succ l M s z t : RS_tm (natrec l M s z (succ t)) (z[lsingle2 t (natrec l M s z t)]).
Proof.
  intros G i Γ T k Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_natrec Hi Hx) as ((Hv & Wl & HM & Hs & Hz & H0) & Hk & ET).
  destruct (inv_succ Hi H0) as ((_ & Ht) & _).
  exact (retype_eqtm Hi (eqtm_natrec_succ _ _ _ _ _ _ _ _ Hc Wl HM Hs Hz Ht) Hk ET).
Qed.

Lemma RS_natrec l M s z t t' : RS_tm t t' -> RS_tm (natrec l M s z t) (natrec l M s z t').
Proof.
  intros IH G i Γ T k Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_natrec Hi Hx) as ((Hv & Wl & HM & Hs & Hz & H0) & Hk & ET).
  refine (retype_eqtm Hi _ Hk ET).
  exact (eqtm_natrec _ _ _ _ _ _ _ _ _ _ _ _ _ Hv (lequiv_refl _ _ Wl) HM (eqty_refl _ _ _ _ _ HM)
           (eqtm_refl _ _ _ _ _ _ Hs) (eqtm_refl _ _ _ _ _ _ Hz) (IH _ _ _ _ _ Hc H0)).
Qed.

Lemma RS_beta l l' A b l1 l2 A' B s : RS_tm (app (lam l l' A b) l1 l2 A' B s) (b[lsingle s]).
Proof.
  intros G i Γ T k Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_app Hi Hx) as ((Hv & W1 & W2 & HA1 & HB1 & Hf & Ha) & Hk & ET).
  destruct (inv_lam Hi Hf) as (B0 & (_ & Wl & Wl' & HA0 & Hb) & _ & EP).
  destruct (pi_inj_c Hc EP) as (E1 & E2 & EA & EB).
  pose proof (wf_tm_ty Hi Hb) as HB0.
  pose proof (retype Hi Ha E1 (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EA) E1)) as Ha0.
  (* the redex at the λ's annotations *)
  assert (Eq1 : [ G ; Γ ⊢[ i ] app (lam l l' A b) l1 l2 A' B s ≅ app (lam l l' A b) l l' A B0 s
                    : B[lsingle s] @ l2 ]).
  { apply eqtm_app; [exact Hv | exact (lequiv_sym _ _ _ E1) | exact (lequiv_sym _ _ _ E2) | exact HA1 | exact EA
                    | exact EB | exact (eqtm_refl _ _ _ _ _ _ Hf) | exact (eqtm_refl _ _ _ _ _ _ Ha)]. }
  pose proof (eqtm_beta _ _ _ _ _ _ _ _ _ Hc Wl Wl' HA0 HB0 Hb Ha0) as Eq2.
  assert (EBs : [ G ; Γ ⊢[ typeof i ] B[lsingle s] ≅ B0[lsingle s] @ l2 ])
    by (rewrite Hi; exact (eqty_single Hi EB Ha)).
  pose proof (eqtm_conv _ _ _ _ _ _ _ _ (eqtm_lconv _ _ _ _ _ _ _ _ Eq2 (lequiv_sym _ _ _ E2)) EBs) as Eq2'.
  exact (retype_eqtm Hi (eqtm_trans _ _ _ _ _ _ _ _ Eq1 Eq2') Hk ET).
Qed.

Lemma RS_app t t' l l' A B s : RS_tm t t' -> RS_tm (app t l l' A B s) (app t' l l' A B s).
Proof.
  intros IH G i Γ T k Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_app Hi Hx) as ((Hv & W1 & W2 & HA & HB & Hf & Ha) & Hk & ET).
  refine (retype_eqtm Hi _ Hk ET).
  exact (eqtm_app _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hv (lequiv_refl _ _ W1) (lequiv_refl _ _ W2) HA
           (eqty_refl _ _ _ _ _ HA) (eqty_refl _ _ _ _ _ HB) (IH _ _ _ _ _ Hc Hf) (eqtm_refl _ _ _ _ _ _ Ha)).
Qed.

(** ** Dependent pairs (M8) *)

Lemma RS_fst_beta l l' A B a b k k' A' B' : RS_tm (tmFst k k' A' B' (tmPair l l' A B a b)) a.
Proof.
  intros G i Γ T k0 Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_fst Hi Hx) as ((_ & Wk & Wk' & HA1 & HB1 & Hp) & Hk & ET).
  destruct (inv_pair Hi Hp) as ((_ & Wl & Wl' & HA0 & HB0 & Ha & Hb) & _ & EP).
  destruct (sig_inj_c Hc EP) as (E1 & E2 & EA & EB).
  (* the redex at the pair's annotations *)
  assert (Eq1 : [ G ; Γ ⊢[ i ] tmFst k k' A' B' (tmPair l l' A B a b) ≅ tmFst l l' A B (tmPair l l' A B a b)
                    : A' @ k ])
    by (apply eqtm_fst; auto using lequiv_sym, eqtm_refl).
  pose proof (eqtm_fst_beta _ _ _ _ _ _ _ _ _ Hc Wl Wl' HA0 HB0 Ha Hb) as Eq2.
  assert (Eq2' : [ G ; Γ ⊢[ i ] tmFst l l' A B (tmPair l l' A B a b) ≅ a : A' @ k ]).
  { eapply eqtm_conv; [exact (eqtm_lconv _ _ _ _ _ _ _ _ Eq2 (lequiv_sym _ _ _ E1)) | rewrite Hi; exact EA]. }
  exact (retype_eqtm Hi (eqtm_trans _ _ _ _ _ _ _ _ Eq1 Eq2') Hk ET).
Qed.

Lemma RS_snd_beta l l' A B a b k k' A' B' : RS_tm (tmSnd k k' A' B' (tmPair l l' A B a b)) b.
Proof.
  intros G i Γ T k0 Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  destruct (inv_snd Hi Hx) as ((_ & Wk & Wk' & HA1 & HB1 & Hp) & Hk & ET).
  destruct (inv_pair Hi Hp) as ((_ & Wl & Wl' & HA0 & HB0 & Ha & Hb) & _ & EP).
  destruct (sig_inj_c Hc EP) as (E1 & E2 & EA & EB).
  assert (Hf : [ G ; Γ ⊢[ i ] tmFst k k' A' B' (tmPair l l' A B a b) : A' @ k ])
    by (apply wf_fst; assumption).
  pose proof (RS_fst_beta _ _ _ _ _ _ _ _ _ _ G i Γ _ _ Hc Hf) as Ef.
  assert (Ha' : [ G ; Γ ⊢[ i ] a : A' @ k ]) by exact (retype Hi Ha (lequiv_sym _ _ _ E1) EA).
  assert (EBa : [ G ; Γ ⊢[ i ] B'[lsingle (tmFst k k' A' B' (tmPair l l' A B a b))] ≅ B[lsingle a] @ k' ])
    by (eapply sig_fam_eq; first [exact Hi | exact Hv | eassumption]).
  assert (Eq1 : [ G ; Γ ⊢[ i ] tmSnd k k' A' B' (tmPair l l' A B a b) ≅ tmSnd l l' A B (tmPair l l' A B a b)
                    : B'[lsingle (tmFst k k' A' B' (tmPair l l' A B a b))] @ k' ])
    by (apply eqtm_snd; auto using lequiv_sym, eqtm_refl).
  pose proof (eqtm_snd_beta _ _ _ _ _ _ _ _ _ Hc Wl Wl' HA0 HB0 Ha Hb) as Eq2.
  assert (Eq2' : [ G ; Γ ⊢[ i ] tmSnd l l' A B (tmPair l l' A B a b) ≅ b
                     : B'[lsingle (tmFst k k' A' B' (tmPair l l' A B a b))] @ k' ]).
  { eapply eqtm_conv; [exact (eqtm_lconv _ _ _ _ _ _ _ _ Eq2 (lequiv_sym _ _ _ E2)) | rewrite Hi; exact EBa]. }
  exact (retype_eqtm Hi (eqtm_trans _ _ _ _ _ _ _ _ Eq1 Eq2') Hk ET).
Qed.

Lemma RS_fst l l' A B p p' : RS_tm p p' -> RS_tm (tmFst l l' A B p) (tmFst l l' A B p').
Proof.
  intros IH G i Γ T k Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_fst Hi Hx) as ((_ & W1 & W2 & HA & HB & Hp) & Hk & ET).
  refine (retype_eqtm Hi _ Hk ET).
  apply eqtm_fst; auto using lequiv_refl, eqty_refl.
Qed.

Lemma RS_snd l l' A B p p' : RS_tm p p' -> RS_tm (tmSnd l l' A B p) (tmSnd l l' A B p').
Proof.
  intros IH G i Γ T k Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_snd Hi Hx) as ((_ & W1 & W2 & HA & HB & Hp) & Hk & ET).
  refine (retype_eqtm Hi _ Hk ET).
  apply eqtm_snd; auto using lequiv_refl, eqty_refl.
Qed.

(** ** Decoding codes *)

Lemma RS_El_nat l : RS_ty (tyEl l tmNat) tyNat.
Proof.
  intros G i Γ k Hc HT. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_El HT) as ((Hv & Wl & Ht) & Hk).
  destruct (inv_code_nat Hi Ht) as ((_ & HΓ) & _ & EU).
  pose proof (U_inj_c Hc EU) as E0.
  apply (retype_eqty Hk). eapply eqty_trans.
  - exact (eqty_El _ _ _ _ _ _ _ Hv (lequiv_sym _ _ _ E0) (eqtm_refl _ _ _ _ _ _ Ht)).
  - exact (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ (eqty_El_nat _ _ _ Hc HΓ)) (lequiv_sym _ _ _ E0)).
Qed.

Lemma RS_El_U l l0 : RS_ty (tyEl l (tmU l0)) (tyU l0).
Proof.
  intros G i Γ k Hc HT. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_El HT) as ((Hv & Wl & Ht) & Hk).
  destruct (inv_code_U Hi Ht) as ((_ & HΓ & Wl0) & _ & EU).
  pose proof (U_inj_c Hc EU) as E0.
  apply (retype_eqty Hk). eapply eqty_trans.
  - exact (eqty_El _ _ _ _ _ _ _ Hv (lequiv_sym _ _ _ E0) (eqtm_refl _ _ _ _ _ _ Ht)).
  - exact (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ (eqty_El_U _ _ _ _ Hc HΓ Wl0)) (lequiv_sym _ _ _ E0)).
Qed.

Lemma RS_El_pi l l1 l2 s t : RS_ty (tyEl l (tmPi l1 l2 s t)) (tyPi l1 l2 (tyEl l1 s) (tyEl l2 t)).
Proof.
  intros G i Γ k Hc HT. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_El HT) as ((Hv & Wl & Ht) & Hk).
  destruct (inv_code_pi Hi Ht) as ((_ & W1 & W2 & Hs & Hb) & _ & EU).
  pose proof (U_inj_c Hc EU) as E0.
  apply (retype_eqty Hk). eapply eqty_trans.
  - exact (eqty_El _ _ _ _ _ _ _ Hv (lequiv_sym _ _ _ E0) (eqtm_refl _ _ _ _ _ _ Ht)).
  - exact (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ (eqty_El_pi _ _ _ _ _ _ _ Hc W1 W2 Hs Hb))
             (lequiv_sym _ _ _ E0)).
Qed.

Lemma RS_El_sig l l1 l2 s t : RS_ty (tyEl l (tmSig l1 l2 s t)) (tySig l1 l2 (tyEl l1 s) (tyEl l2 t)).
Proof.
  intros G i Γ k Hc HT. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_El HT) as ((Hv & Wl & Ht) & Hk).
  destruct (inv_code_sig Hi Ht) as ((_ & W1 & W2 & Hs & Hb) & _ & EU).
  pose proof (U_inj_c Hc EU) as E0.
  apply (retype_eqty Hk). eapply eqty_trans.
  - exact (eqty_El _ _ _ _ _ _ _ Hv (lequiv_sym _ _ _ E0) (eqtm_refl _ _ _ _ _ _ Ht)).
  - exact (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ (eqty_El_sig _ _ _ _ _ _ _ Hc W1 W2 Hs Hb))
             (lequiv_sym _ _ _ E0)).
Qed.
Lemma RS_El_W l l1 l2 s t : RS_ty (tyEl l (tmW l1 l2 s t)) (tyW l1 l2 (tyEl l1 s) (tyEl l2 t)).
Proof.
  intros G i Γ k Hc HT. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_El HT) as ((Hv & Wl & Ht) & Hk).
  destruct (inv_code_W Hi Ht) as ((_ & W1 & W2 & Hs & Hb) & _ & EU).
  pose proof (U_inj_c Hc EU) as E0.
  apply (retype_eqty Hk). eapply eqty_trans.
  - exact (eqty_El _ _ _ _ _ _ _ Hv (lequiv_sym _ _ _ E0) (eqtm_refl _ _ _ _ _ _ Ht)).
  - exact (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ (eqty_El_W _ _ _ _ _ _ _ Hc W1 W2 Hs Hb))
             (lequiv_sym _ _ _ E0)).
Qed.

(** The codes of [Vec] and [Fin] (M14b). *)
Lemma RS_El_vec l l0 s n : RS_ty (tyEl l (tmVec l0 s n)) (tyVec l0 (tyEl l0 s) n).
Proof.
  intros G i Γ k Hc HT. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_El HT) as ((Hv & Wl & Ht) & Hk).
  destruct (inv_code_vec Hi Ht) as ((_ & Wl0 & Hs & Hn) & _ & EU).
  pose proof (U_inj_c Hc EU) as E0.
  apply (retype_eqty Hk). eapply eqty_trans.
  - exact (eqty_El _ _ _ _ _ _ _ Hv (lequiv_sym _ _ _ E0) (eqtm_refl _ _ _ _ _ _ Ht)).
  - exact (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ (eqty_El_vec _ _ _ _ _ _ Hc Wl0 Hs Hn))
             (lequiv_sym _ _ _ E0)).
Qed.
(** The code of [Wf] (M15b). *)
Lemma RS_El_wf l l0 s n : RS_ty (tyEl l (tmWf l0 s n)) (tyWf l0 (tyEl l0 s) n).
Proof.
  intros G i Γ k Hc HT. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_El HT) as ((Hv & Wl & Ht) & Hk).
  destruct (inv_code_wf Hi Ht) as ((_ & Wl0 & Hs & Hn) & _ & EU).
  pose proof (U_inj_c Hc EU) as E0.
  apply (retype_eqty Hk). eapply eqty_trans.
  - exact (eqty_El _ _ _ _ _ _ _ Hv (lequiv_sym _ _ _ E0) (eqtm_refl _ _ _ _ _ _ Ht)).
  - exact (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ (eqty_El_wf _ _ _ _ _ _ Hc Wl0 Hs Hn))
             (lequiv_sym _ _ _ E0)).
Qed.
(** The code of [∥·∥] (M16b). *)
Lemma RS_El_sq l l0 s : RS_ty (tyEl l (tmSqCode l0 s)) (tySq l0 (tyEl l0 s)).
Proof.
  intros G i Γ k Hc HT. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_El HT) as ((Hv & Wl & Ht) & Hk).
  destruct (inv_code_sq Hi Ht) as ((_ & Wl0 & Hs) & _ & EU).
  pose proof (U_inj_c Hc EU) as E0.
  apply (retype_eqty Hk). eapply eqty_trans.
  - exact (eqty_El _ _ _ _ _ _ _ Hv (lequiv_sym _ _ _ E0) (eqtm_refl _ _ _ _ _ _ Ht)).
  - exact (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ (eqty_El_sq _ _ _ _ _ Hc Wl0 Hs))
             (lequiv_sym _ _ _ E0)).
Qed.
Lemma RS_El_fin l n : RS_ty (tyEl l (tmFin n)) (tyFin n).
Proof.
  intros G i Γ k Hc HT. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_El HT) as ((Hv & Wl & Ht) & Hk).
  destruct (inv_code_fin Hi Ht) as ((_ & Hn) & _ & EU).
  pose proof (U_inj_c Hc EU) as E0.
  apply (retype_eqty Hk). eapply eqty_trans.
  - exact (eqty_El _ _ _ _ _ _ _ Hv (lequiv_sym _ _ _ E0) (eqtm_refl _ _ _ _ _ _ Ht)).
  - exact (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ (eqty_El_fin _ _ _ _ Hc Hn)) (lequiv_sym _ _ _ E0)).
Qed.

Lemma RS_El_unit l l0 : RS_ty (tyEl l (tmUnit l0)) (tyUnit l0).
Proof.
  intros G i Γ k Hc HT. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_El HT) as ((Hv & Wl & Ht) & Hk).
  destruct (inv_code_unit Hi Ht) as ((_ & HΓ & Wl0) & _ & EU).
  pose proof (U_inj_c Hc EU) as E0.
  apply (retype_eqty Hk). eapply eqty_trans.
  - exact (eqty_El _ _ _ _ _ _ _ Hv (lequiv_sym _ _ _ E0) (eqtm_refl _ _ _ _ _ _ Ht)).
  - exact (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ (eqty_El_unit _ _ _ _ Hc HΓ Wl0)) (lequiv_sym _ _ _ E0)).
Qed.

(** The identity type's code (M11b). *)
Lemma RS_El_id l l0 s t u : RS_ty (tyEl l (tmId l0 s t u)) (tyId l0 (tyEl l0 s) t u).
Proof.
  intros G i Γ k Hc HT. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_El HT) as ((Hv & Wl & Ht) & Hk).
  destruct (inv_code_id Hi Ht) as ((_ & Wl0 & Hs & Ht0 & Hu) & _ & EU).
  pose proof (U_inj_c Hc EU) as E0.
  apply (retype_eqty Hk). eapply eqty_trans.
  - exact (eqty_El _ _ _ _ _ _ _ Hv (lequiv_sym _ _ _ E0) (eqtm_refl _ _ _ _ _ _ Ht)).
  - exact (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ (eqty_El_id _ _ _ _ _ _ _ Hc Wl0 Hs Ht0 Hu))
             (lequiv_sym _ _ _ E0)).
Qed.

(** Strict equality's codes (M10c). *)
Lemma RS_El_seq l l0 s t u : RS_ty (tyEl l (tmSEq l0 s t u)) (tySEq l0 (tyEl l0 s) t u).
Proof.
  intros G i Γ k Hc HT. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_El HT) as ((Hv & Wl & Ht) & Hk).
  destruct (inv_code_seq Hi Ht) as ((_ & Wl0 & Hs & Ht0 & Hu) & _ & EU).
  pose proof (U_inj_c Hc EU) as E0.
  apply (retype_eqty Hk). eapply eqty_trans.
  - exact (eqty_El _ _ _ _ _ _ _ Hv (lequiv_sym _ _ _ E0) (eqtm_refl _ _ _ _ _ _ Ht)).
  - exact (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ (eqty_El_seq _ _ _ _ _ _ _ Hc Wl0 Hs Ht0 Hu))
             (lequiv_sym _ _ _ E0)).
Qed.

Lemma RS_El_sempty l l0 : RS_ty (tyEl l (tmSEmpty l0)) (tySEmpty l0).
Proof.
  intros G i Γ k Hc HT. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_El HT) as ((Hv & Wl & Ht) & Hk).
  destruct (inv_code_sempty Hi Ht) as ((_ & HΓ & Wl0) & _ & EU).
  pose proof (U_inj_c Hc EU) as E0.
  apply (retype_eqty Hk). eapply eqty_trans.
  - exact (eqty_El _ _ _ _ _ _ _ Hv (lequiv_sym _ _ _ E0) (eqtm_refl _ _ _ _ _ _ Ht)).
  - exact (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ (eqty_El_sempty _ _ _ _ Hc HΓ Wl0)) (lequiv_sym _ _ _ E0)).
Qed.

(** The codes of [Empty] and [+] (M12c). *)
Lemma RS_El_empty l l0 : RS_ty (tyEl l (tmEmpty l0)) (tyEmpty l0).
Proof.
  intros G i Γ k Hc HT. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_El HT) as ((Hv & Wl & Ht) & Hk).
  destruct (inv_code_empty Hi Ht) as ((_ & HΓ & Wl0) & _ & EU).
  pose proof (U_inj_c Hc EU) as E0.
  apply (retype_eqty Hk). eapply eqty_trans.
  - exact (eqty_El _ _ _ _ _ _ _ Hv (lequiv_sym _ _ _ E0) (eqtm_refl _ _ _ _ _ _ Ht)).
  - exact (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ (eqty_El_empty _ _ _ _ Hc HΓ Wl0)) (lequiv_sym _ _ _ E0)).
Qed.
Lemma RS_El_sum l l1 l2 s t : RS_ty (tyEl l (tmSum l1 l2 s t)) (tySum l1 l2 (tyEl l1 s) (tyEl l2 t)).
Proof.
  intros G i Γ k Hc HT. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_El HT) as ((Hv & Wl & Ht) & Hk).
  destruct (inv_code_sum Hi Ht) as ((_ & W1 & W2 & Hs & Hb) & _ & EU).
  pose proof (U_inj_c Hc EU) as E0.
  apply (retype_eqty Hk). eapply eqty_trans.
  - exact (eqty_El _ _ _ _ _ _ _ Hv (lequiv_sym _ _ _ E0) (eqtm_refl _ _ _ _ _ _ Ht)).
  - exact (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ (eqty_El_sum _ _ _ _ _ _ _ Hc W1 W2 Hs Hb))
             (lequiv_sym _ _ _ E0)).
Qed.

Lemma RS_El l t t' : RS_tm t t' -> RS_ty (tyEl l t) (tyEl l t').
Proof.
  intros IH G i Γ k Hc HT. destruct (inv_ty_El HT) as ((Hv & Wl & Ht) & Hk).
  apply (retype_eqty Hk). exact (eqty_El _ _ _ _ _ _ _ Hv (lequiv_refl _ _ Wl) (IH _ _ _ _ _ Hc Ht)).
Qed.

(** ** Boxes *)

Lemma lle_CD : lle lC lD. Proof. unfold lle; cbn; lia. Qed.

Lemma RS_letboxT_beta l' l Δ M t' T : RS_tm (letboxT l' l Δ M t' (boxT T)) (t'⦃gsingle (GTy T)⦄).
Proof.
  intros G i Γ X k Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_letboxT Hi Hx) as ((-> & W1 & W2 & HΔ & HM & Hb & Hs) & Hk & ET).
  destruct (inv_boxT (i := lM) eq_refl Hs) as (Δ1 & l1 & (_ & _ & Wl1 & HΔ1 & HT1) & _ & EC).
  destruct (declM_CTyp_inj EC) as (Ec & El).
  pose proof (wft_lconv _ _ _ _ _ _ (sc_cty (i := lC) lle_CD (eqctx_sym_D Ec) HT1) El) as HT.
  exact (retype_eqtm Hi (eqtm_letboxT_beta _ _ _ _ _ _ _ _ W1 W2 HΔ HT HM Hb) Hk ET).
Qed.

Lemma RS_letboxt_beta l' l Δ A M t' c : RS_tm (letboxt l' l Δ A M t' (boxt c)) (t'⦃gsingle (GTm c)⦄).
Proof.
  intros G i Γ X k Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_letboxt Hi Hx) as ((-> & W1 & W2 & HΔ & HA & HM & Hb & Hs) & Hk & ET).
  destruct (inv_boxt (i := lM) eq_refl Hs) as (Δ1 & A1 & l1 & (_ & _ & Wl1 & HΔ1 & HA1 & Hc1) & _ & EC).
  destruct (declM_CTrm_inj EC) as (Ec & EA & El).
  pose proof (wf_lconv _ _ _ _ _ _ _ (sc_ctm (i := lC) lle_CD (eqctx_sym_D Ec) Hc1) El) as Hc2.
  pose proof (sc_conv (i := lC) lle_CD Hc2 EA) as Hc0.
  exact (retype_eqtm Hi (eqtm_letboxt_beta _ _ _ _ _ _ _ _ _ W1 W2 HΔ Hc0 HA HM Hb) Hk ET).
Qed.

Lemma RS_letboxT l' l Δ M t' t t0 : RS_tm t t0 -> RS_tm (letboxT l' l Δ M t' t) (letboxT l' l Δ M t' t0).
Proof.
  intros IH G i Γ X k Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_letboxT Hi Hx) as ((-> & W1 & W2 & HΔ & HM & Hb & Hs) & Hk & ET).
  refine (retype_eqtm Hi _ Hk ET).
  exact (eqtm_letboxT _ _ _ _ _ _ _ _ _ _ _ _ _ _ (lequiv_refl _ _ W1) (lequiv_refl _ _ W2) HΔ HΔ
           (eqc_refl _ _ _ HΔ) HM (eqty_refl _ _ _ _ _ HM) HM (eqtm_refl _ _ _ _ _ _ Hb) Hb
           (IH _ _ _ _ _ compt_M Hs)).
Qed.

Lemma RS_letboxt l' l Δ A M t' t t0 : RS_tm t t0 -> RS_tm (letboxt l' l Δ A M t' t) (letboxt l' l Δ A M t' t0).
Proof.
  intros IH G i Γ X k Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_letboxt Hi Hx) as ((-> & W1 & W2 & HΔ & HA & HM & Hb & Hs) & Hk & ET).
  refine (retype_eqtm Hi _ Hk ET).
  exact (eqtm_letboxt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (lequiv_refl _ _ W1) (lequiv_refl _ _ W2) HΔ HΔ
           (eqc_refl _ _ _ HΔ) HA HA (eqty_refl _ _ _ _ _ HA) HM (eqty_refl _ _ _ _ _ HM) HM
           (eqtm_refl _ _ _ _ _ _ Hb) Hb (IH _ _ _ _ _ compt_M Hs)).
Qed.

(** ** Universe polymorphism *)

Lemma RS_ubeta n l T1 b ls : length ls = n -> RS_tm (uapp (ulam n l T1 b) ls) b[uext ls lvar]ᵤ.
Proof.
  intros Hn0 G i Γ X k Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_uapp Hi Hx) as (n0 & l0 & T0 & (-> & Wl0 & HT0 & Hlen & Hls & Hf) & Hk & ET).
  destruct (inv_ulam (i := lM) eq_refl Hf) as ((_ & HΓ & Hn & Wl & HT1 & Hb) & _ & EP).
  destruct (declM_upi_inj EP) as (En & El & EB). subst n n0.
  pose proof (ctx_glob _ _ _ HΓ) as HG. pose proof (wf_ctx_dnf HΓ) as HΓd.
  pose proof (eqtm_ubeta _ _ _ _ _ _ _ HΓ Hn Wl HT1 Hb eq_refl Hls) as Eq.
  pose proof (uinst_eqty HG HΓd Hls EB) as EBs.
  pose proof (lequiv_lvsubst _ _ _ _ _ (usub_ok_uext _ _ _ _ Hls (usub_ok_id _)) El) as Els.
  refine (retype_eqtm Hi _ Hk ET).
  exact (eqtm_conv _ _ _ _ _ _ _ _ (eqtm_lconv _ _ _ _ _ _ _ _ Eq Els) EBs).
Qed.

Lemma RS_uapp t t' ls : RS_tm t t' -> RS_tm (uapp t ls) (uapp t' ls).
Proof.
  intros IH G i Γ X k Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_uapp Hi Hx) as (n0 & l0 & T0 & (-> & Wl0 & HT0 & Hlen & Hls & Hf) & Hk & ET).
  refine (retype_eqtm Hi _ Hk ET).
  exact (eqtm_uapp _ _ _ _ _ _ _ _ _ Wl0 HT0 Hlen (lequivs_refl _ _ Hls) (IH _ _ _ _ _ compt_M Hf)).
Qed.

(** ** Meta-functions *)

Lemma RS_cbeta l T1 b Δ : RS_tm (capp (clam l T1 b) Δ) b⦃gsingle (GCtx Δ)⦄.
Proof.
  intros G i Γ X k Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_capp Hi Hx) as (l0 & T0 & (-> & Wl0 & HT0 & HΔ & Hf & HTs) & Hk & ET).
  destruct (inv_clam (i := lM) eq_refl Hf) as ((_ & HΓ & Wl & HT1 & Hb) & _ & EP).
  destruct (declM_cpi_inj EP) as (El & EB).
  pose proof (eqtm_cbeta _ _ _ _ _ _ HΓ Wl HT1 Hb HΔ) as Eq.
  pose proof (inst_eqty (o := GCtx Δ) (D := gdCtx) HΓ (wf_ctx_dnf HΔ) I HΔ EB) as EBs.
  refine (retype_eqtm Hi _ Hk ET).
  exact (eqtm_conv _ _ _ _ _ _ _ _ (eqtm_lconv _ _ _ _ _ _ _ _ Eq (lequiv_sym _ _ _ El)) EBs).
Qed.

Lemma RS_capp t t' Δ : RS_tm t t' -> RS_tm (capp t Δ) (capp t' Δ).
Proof.
  intros IH G i Γ X k Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_capp Hi Hx) as (l0 & T0 & (-> & Wl0 & HT0 & HΔ & Hf & HTs) & Hk & ET).
  refine (retype_eqtm Hi _ Hk ET).
  exact (eqtm_capp _ _ _ _ _ _ _ _ Wl0 HT0 HΔ HΔ (eqc_refl _ _ _ HΔ) (eqty_refl _ _ _ _ _ HTs)
           (IH _ _ _ _ _ compt_M Hf)).
Qed.

Lemma RS_tbeta Δ1 l l' T1 b A : RS_tm (tapp (tlam Δ1 l l' T1 b) A) b⦃gsingle (GTy A)⦄.
Proof.
  intros G i Γ X k Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_tapp Hi Hx) as (Δ0 & l0 & l0' & T0 & (-> & Hf & HΔ0 & Wl0 & Wl0' & HT0 & HA & HTs) & Hk & ET).
  destruct (inv_tlam (i := lM) eq_refl Hf) as ((_ & HΓ & HΔ1 & Wl & Wl' & HT1 & Hb) & _ & EP).
  destruct (declM_tpi_inj EP) as (Ec & E1 & E2 & EB).
  pose proof (wft_lconv _ _ _ _ _ _ (mvD Ec HA) E1) as HA1.
  pose proof (eqtm_tbeta _ _ _ _ _ _ _ _ HΓ HΔ1 Wl Wl' HT1 Hb HA1) as Eq.
  pose proof (inst_eqty (o := GTy A) (D := gdTy Δ0 lD l0) HΓ (wf_ty_dnf HA) (wf_ty_dnf_ctx HA) HA EB) as EBs.
  refine (retype_eqtm Hi _ Hk ET).
  exact (eqtm_conv _ _ _ _ _ _ _ _ (eqtm_lconv _ _ _ _ _ _ _ _ Eq (lequiv_sym _ _ _ E2)) EBs).
Qed.

Lemma RS_tapp t t' A : RS_tm t t' -> RS_tm (tapp t A) (tapp t' A).
Proof.
  intros IH G i Γ X k Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_tapp Hi Hx) as (Δ0 & l0 & l0' & T0 & (-> & Hf & HΔ0 & Wl0 & Wl0' & HT0 & HA & HTs) & Hk & ET).
  refine (retype_eqtm Hi _ Hk ET).
  exact (eqtm_tapp _ _ _ _ _ _ _ _ _ _ (IH _ _ _ _ _ compt_M Hf) HΔ0 Wl0 Wl0' HT0 HA (eqty_refl _ _ _ _ _ HA)
           (eqty_refl _ _ _ _ _ HTs)).
Qed.

(** ** The recursors *)

(** The typing of a recursor's β-reduct (discharged in [RecReduct]). *)
Definition RecRedTyped : Prop :=
  (forall G Γ l1 l2 rb l Δ c r T k, [ G ; Γ ⊢[ lM ] elimT l1 l2 rb l Δ (boxT c) : T @ k ] ->
     redT l1 l2 rb l Δ c = Some r -> [ G ; Γ ⊢[ lM ] r : T @ k ]) /\
  (forall G Γ l1 l2 rb l Δ A c r T k, [ G ; Γ ⊢[ lM ] elimt l1 l2 rb l Δ A (boxt c) : T @ k ] ->
     redt l1 l2 rb l Δ A c = Some r -> [ G ; Γ ⊢[ lM ] r : T @ k ]).

Lemma RS_elimT_beta (HR : RecRedTyped) l1 l2 rb l Δ c r : redT l1 l2 rb l Δ c = Some r ->
  RS_tm (elimT l1 l2 rb l Δ (boxT c)) r.
Proof.
  intros Hred G i Γ T k Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_elimT Hi Hx) as (MT & Mt & bs & (_ & -> & _) & _).
  exact (eqtm_elimT_beta _ _ _ _ _ _ _ _ _ _ _ Hx Hred (proj1 HR _ _ _ _ _ _ _ _ _ _ _ Hx Hred)).
Qed.

Lemma RS_elimt_beta (HR : RecRedTyped) l1 l2 rb l Δ A c r : redt l1 l2 rb l Δ A c = Some r ->
  RS_tm (elimt l1 l2 rb l Δ A (boxt c)) r.
Proof.
  intros Hred G i Γ T k Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_elimt Hi Hx) as (MT & Mt & bs & (_ & -> & _) & _).
  exact (eqtm_elimt_beta _ _ _ _ _ _ _ _ _ _ _ _ Hx Hred (proj2 HR _ _ _ _ _ _ _ _ _ _ _ _ Hx Hred)).
Qed.

Lemma RS_elimT l1 l2 rb l Δ t t' : RS_tm t t' -> RS_tm (elimT l1 l2 rb l Δ t) (elimT l1 l2 rb l Δ t').
Proof.
  intros IH G i Γ T k Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_elimT Hi Hx) as (MT & Mt & bs & (-> & -> & _ & W1 & W2 & Wl & HΔ & HMT & HMt & Hbc & Hbs & Hs)
                                 & Hk & ET).
  pose proof (IH _ _ _ _ _ compt_M Hs) as Es.
  refine (retype_eqtm Hi _ Hk ET).
  apply eqtm_elimT; try assumption; try (apply lequiv_refl; assumption).
  - exact (motT_eq_scrut HMT Wl HΔ Es).
  - now apply eqc_refl.
  - now apply eqty_refl.
  - now apply eqty_refl.
  - intros j Hj; apply eqtm_refl, Hbs, Hj.
Qed.

Lemma RS_elimt l1 l2 rb l Δ A t t' : RS_tm t t' -> RS_tm (elimt l1 l2 rb l Δ A t) (elimt l1 l2 rb l Δ A t').
Proof.
  intros IH G i Γ T k Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_elimt Hi Hx) as (MT & Mt & bs & (-> & -> & _ & W1 & W2 & Wl & HΔ & HMT & HMt & Hbc & Hbs
                                                  & HA & Hs) & Hk & ET).
  pose proof (IH _ _ _ _ _ compt_M Hs) as Es.
  refine (retype_eqtm Hi _ Hk ET).
  apply eqtm_elimt; try assumption; try (apply lequiv_refl; assumption).
  - exact (mott_eq_scrut HMt Wl HΔ HA Es).
  - now apply eqc_refl.
  - now apply eqty_refl.
  - now apply eqty_refl.
  - now apply eqty_refl.
  - intros j Hj; apply eqtm_refl, Hbs, Hj.
Qed.

(** The index, under a boxed [λ]. *)
Lemma RS_elimt_idx l1 l2 rb l Δ A A' k0 k0' B b : RS_ty A A' ->
  RS_tm (elimt l1 l2 rb l Δ A (boxt (lam k0 k0' B b))) (elimt l1 l2 rb l Δ A' (boxt (lam k0 k0' B b))).
Proof.
  intros IH G i Γ T k Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_elimt Hi Hx) as (MT & Mt & bs & (-> & -> & _ & W1 & W2 & Wl & HΔ & HMT & HMt & Hbc & Hbs
                                                  & HA & Hs) & Hk & ET).
  pose proof (IH _ _ _ _ compt_D HA) as EA.
  refine (retype_eqtm Hi _ Hk ET).
  apply eqtm_elimt; try assumption; try (apply lequiv_refl; assumption).
  - exact (declM_mott_eq (eqty_refl _ _ _ _ _ HMt) W2 (lequiv_refl _ _ Wl) (eqc_refl _ _ _ HΔ) EA
             (eqtm_refl _ _ _ _ _ _ Hs)).
  - now apply eqc_refl.
  - exact (eqty_wf_r (i := lD) eq_refl EA).
  - now apply eqty_refl.
  - now apply eqty_refl.
  - intros j Hj; apply eqtm_refl, Hbs, Hj.
  - now apply eqtm_refl.
Qed.

(** δ: a defined global unfolds to its carried body's instance (M9). *)
Lemma RS_delta u b d : RS_tm (gdef u b d) b[d].
Proof.
  intros G i Γ T k Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_gdef Hi Hx) as (Δ & T0 & l0 & t0 & (HΓ & Hin & Hl & _ & Ht & Hn & He & Hb) & Hk & HT).
  eapply eqtm_conv; [| rewrite Hi; exact HT].
  destruct Hk as [-> | Hk]; [| eapply eqtm_lconv; [| exact Hk]];
    (eapply eqtm_delta; [exact Hc | exact HΓ | exact Hin | exact Hl | exact Ht | exact Hn | exact He | exact Hb]).
Qed.

(** The irrelevant empty type's eliminator reduces its scrutinee (M10a). *)
Lemma RS_elimSEmpty l l' M e e' : RS_tm e e' -> RS_tm (elimSEmpty l l' M e) (elimSEmpty l l' M e').
Proof.
  intros IH G i Γ T k Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_elimSEmpty Hi Hx) as ((_ & W1 & W2 & HM & He) & Hk & ET).
  refine (retype_eqtm Hi _ Hk ET).
  apply eqtm_elimSEmpty; auto using lequiv_refl, eqty_refl.
Qed.

(** [Empty]'s eliminator (M12a): the congruence at the scrutinee. *)
Lemma RS_elimEmpty l l' M e e' : RS_tm e e' -> RS_tm (elimEmpty l l' M e) (elimEmpty l l' M e').
Proof.
  intros IH G i Γ T k Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_elimEmpty Hi Hx) as ((_ & W1 & W2 & HM & He) & Hk & ET).
  refine (retype_eqtm Hi _ Hk ET).
  exact (eqtm_elimEmpty _ _ _ _ _ _ _ _ _ _ _ (compt_notV _ Hc) (lequiv_refl _ _ W1) (lequiv_refl _ _ W2) HM
           (eqty_refl _ _ _ _ _ HM) (IH _ _ _ _ _ Hc He)).
Qed.

(** [J] (M11a): the congruence at the scrutinee, and β at any [refl] of
    the [Id] type (its point equals both endpoints, by injectivity). *)
Lemma RS_J l l' A a M c u e e' : RS_tm e e' -> RS_tm (tmJ l l' A a M c u e) (tmJ l l' A a M c u e').
Proof.
  intros IH G i Γ T k Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_J Hi Hx) as ((_ & W1 & W2 & HA & Ha & HI & HM & Hcc & Hu & He) & Hk & ET).
  refine (retype_eqtm Hi _ Hk ET).
  apply eqtm_J; [(apply compt_notV; exact Hc) | apply lequiv_refl, W1 | apply lequiv_refl, W2 | exact HA | apply eqty_refl, HA
                | apply eqtm_refl, Ha | exact HI | exact HM | apply eqty_refl, HM | apply eqtm_refl, Hcc
                | apply eqtm_refl, Hu | exact (IH _ _ _ _ _ Hc He)].
Qed.

Lemma RS_J_beta l l' A a M c u k B b : RS_tm (tmJ l l' A a M c u (tmRefl k B b)) c.
Proof.
  intros G i Γ T m Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  assert (Hv : i <> lV) by (destruct Hc as [-> | ->]; discriminate).
  destruct (inv_J Hi Hx) as ((_ & W1 & W2 & HA & Ha & HI & HM & Hcc & Hu & He) & Hk & ET).
  refine (retype_eqtm Hi _ Hk ET).
  destruct (inv_idrefl Hi He) as (_ & _ & EId).
  destruct (id_inj_c Hc EId) as (Ekl & EAB & Eab & Eub).
  assert (Hau : [ G ; Γ ⊢[ i ] a ≅ u : A @ l ]) by (eapply eqtm_trans; [exact Eab | apply eqtm_sym, Eub]).
  assert (HIdu : [ G ; Γ ⊢[ i ] tyId l A a a ≅ tyId l A a u @ l ]).
  { apply eqty_id; [exact Hv | apply lequiv_refl, W1 | exact HA | apply eqty_refl, HA | apply eqtm_refl, Ha
                   | exact Hau]. }
  assert (Hrr : [ G ; Γ ⊢[ i ] tmRefl l A a ≅ tmRefl k B b : tyId l A a a @ l ])
    by (apply eqtm_idrefl; [exact Hv | apply lequiv_sym, Ekl | exact HA | exact EAB | exact Eab]).
  assert (Her : [ G ; Γ ⊢[ i ] tmRefl k B b ≅ tmRefl l A a : tyId l A a u @ l ]).
  { apply eqtm_sym. eapply eqtm_conv; [exact Hrr | rewrite Hi; apply eqty_sym, HIdu]. }
  assert (Hcong : [ G ; Γ ⊢[ i ] tmJ l l' A a M c u (tmRefl k B b) ≅ tmJ l l' A a M c a (tmRefl l A a)
                     : M[lsingle2 u (tmRefl k B b)] @ l' ]).
  { apply eqtm_J; [(apply compt_notV; exact Hc) | apply lequiv_refl, W1 | apply lequiv_refl, W2 | exact HA | apply eqty_refl, HA
                  | apply eqtm_refl, Ha | exact HI | exact HM | apply eqty_refl, HM | apply eqtm_refl, Hcc
                  | apply eqtm_sym, Hau | exact Her]. }
  pose proof (eqtm_J_beta _ _ _ _ _ _ _ _ _ Hc W1 W2 HA Ha HI HM Hcc) as Hb.
  pose proof (lsub_eq_J Hi Hv W1 HA Ha Hu Ha (eqtm_sym _ _ _ _ _ _ _ Hau) He (eqtm_wf_r Hi Her) Her) as Hs.
  eapply eqtm_trans; [exact Hcong |].
  eapply eqtm_conv; [exact Hb | rewrite Hi; exact (wf_ty_func Hi HM Hs)].
Qed.

(** [case] (M12b): the congruence at the scrutinee, and β at an injection
    of any annotations (they equal the [case]'s, by injectivity). *)
Lemma RS_case l l' l'' A B M c1 c2 t t' : RS_tm t t' ->
  RS_tm (tmCase l l' l'' A B M c1 c2 t) (tmCase l l' l'' A B M c1 c2 t').
Proof.
  intros IH G i Γ T k Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_case Hi Hx) as ((_ & W1 & W2 & W3 & HA & HB & HM & Hc1 & Hc2 & Ht) & Hk & ET).
  refine (retype_eqtm Hi _ Hk ET).
  apply eqtm_case; [now apply compt_notV | apply lequiv_refl, W1 | apply lequiv_refl, W2 | apply lequiv_refl, W3 | exact HA
                   | apply eqty_refl, HA | exact HB | apply eqty_refl, HB | exact HM | apply eqty_refl, HM
                   | apply eqtm_refl, Hc1 | apply eqtm_refl, Hc2 | exact (IH _ _ _ _ _ Hc Ht)].
Qed.

Lemma RS_case_inl l l' l'' A B M c1 c2 k k' C D a :
  RS_tm (tmCase l l' l'' A B M c1 c2 (tmInl k k' C D a)) c1[lsingle a].
Proof.
  intros G i Γ T m Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_case Hi Hx) as ((_ & W1 & W2 & W3 & HA & HB & HM & Hc1 & Hc2 & Ht) & Hk & ET).
  refine (retype_eqtm Hi _ Hk ET).
  destruct (inv_inl Hi Ht) as (_ & _ & EInl).
  destruct (sum_inj_c Hc EInl) as (Ekl & Ek'l' & EAC & EBD).
  pose proof (inl_payload Hc Ht) as Ha.
  assert (Hinl : [ G ; Γ ⊢[ i ] tmInl l l' A B a ≅ tmInl k k' C D a : tySum l l' A B @ lmax l l' ])
    by (apply eqtm_inl; [now apply compt_notV | apply lequiv_sym, Ekl | apply lequiv_sym, Ek'l' | exact EAC | exact EBD
                        | apply eqtm_refl, Ha]).
  assert (Hcong : [ G ; Γ ⊢[ i ] tmCase l l' l'' A B M c1 c2 (tmInl k k' C D a)
                     ≅ tmCase l l' l'' A B M c1 c2 (tmInl l l' A B a) : M[lsingle (tmInl k k' C D a)] @ l'' ]).
  { apply eqtm_case; [now apply compt_notV | apply lequiv_refl, W1 | apply lequiv_refl, W2 | apply lequiv_refl, W3 | exact HA
                     | apply eqty_refl, HA | exact HB | apply eqty_refl, HB | exact HM | apply eqty_refl, HM
                     | apply eqtm_refl, Hc1 | apply eqtm_refl, Hc2 | apply eqtm_sym, Hinl]. }
  pose proof (eqtm_case_inl _ _ _ _ _ _ _ _ _ _ _ _ Hc W1 W2 W3 HA HB HM Hc1 Hc2 Ha) as Hb.
  eapply eqtm_trans; [exact Hcong |].
  eapply eqtm_conv; [exact Hb | rewrite Hi].
  exact (wf_ty_func Hi HM (lsub_eq_single Hi Ht (eqtm_wf_l Hi Hinl) (eqtm_sym _ _ _ _ _ _ _ Hinl))).
Qed.

Lemma RS_case_inr l l' l'' A B M c1 c2 k k' C D b :
  RS_tm (tmCase l l' l'' A B M c1 c2 (tmInr k k' C D b)) c2[lsingle b].
Proof.
  intros G i Γ T m Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_case Hi Hx) as ((_ & W1 & W2 & W3 & HA & HB & HM & Hc1 & Hc2 & Ht) & Hk & ET).
  refine (retype_eqtm Hi _ Hk ET).
  destruct (inv_inr Hi Ht) as (_ & _ & EInr).
  destruct (sum_inj_c Hc EInr) as (Ekl & Ek'l' & EAC & EBD).
  pose proof (inr_payload Hc Ht) as Hb0.
  assert (Hinr : [ G ; Γ ⊢[ i ] tmInr l l' A B b ≅ tmInr k k' C D b : tySum l l' A B @ lmax l l' ])
    by (apply eqtm_inr; [now apply compt_notV | apply lequiv_sym, Ekl | apply lequiv_sym, Ek'l' | exact EAC | exact EBD
                        | apply eqtm_refl, Hb0]).
  assert (Hcong : [ G ; Γ ⊢[ i ] tmCase l l' l'' A B M c1 c2 (tmInr k k' C D b)
                     ≅ tmCase l l' l'' A B M c1 c2 (tmInr l l' A B b) : M[lsingle (tmInr k k' C D b)] @ l'' ]).
  { apply eqtm_case; [now apply compt_notV | apply lequiv_refl, W1 | apply lequiv_refl, W2 | apply lequiv_refl, W3 | exact HA
                     | apply eqty_refl, HA | exact HB | apply eqty_refl, HB | exact HM | apply eqty_refl, HM
                     | apply eqtm_refl, Hc1 | apply eqtm_refl, Hc2 | apply eqtm_sym, Hinr]. }
  pose proof (eqtm_case_inr _ _ _ _ _ _ _ _ _ _ _ _ Hc W1 W2 W3 HA HB HM Hc1 Hc2 Hb0) as Hb.
  eapply eqtm_trans; [exact Hcong |].
  eapply eqtm_conv; [exact Hb | rewrite Hi].
  exact (wf_ty_func Hi HM (lsub_eq_single Hi Ht (eqtm_wf_l Hi Hinr) (eqtm_sym _ _ _ _ _ _ _ Hinr))).
Qed.

(** [ind_∥∥] (M16a): the congruence at the scrutinee, and β at a [squash]
    of any annotations (they equal the eliminator's, by injectivity). *)
Lemma RS_elimSq l l' A M c t t' : RS_tm t t' -> RS_tm (tmElimSq l l' A M c t) (tmElimSq l l' A M c t').
Proof.
  intros IH G i Γ T k Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_elimSq Hi Hx) as ((_ & W1 & W2 & HA & HM & Hcc & Ht) & Hk & ET).
  refine (retype_eqtm Hi _ Hk ET).
  exact (eqtm_elimSq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ltac:(apply compt_notV; exact Hc) (lequiv_refl _ _ W1) (lequiv_refl _ _ W2) HA
           (eqty_refl _ _ _ _ _ HA) HM (eqty_refl _ _ _ _ _ HM) (eqtm_refl _ _ _ _ _ _ Hcc) (IH _ _ _ _ _ Hc Ht)).
Qed.

Lemma RS_elimSq_sq l l' A M c k C a : RS_tm (tmElimSq l l' A M c (tmSq k C a)) c[lsingle a].
Proof.
  intros G i Γ T m Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  destruct (inv_elimSq Hi Hx) as ((_ & W1 & W2 & HA & HM & Hcc & Ht) & Hk & ET).
  refine (retype_eqtm Hi _ Hk ET).
  destruct (inv_sq Hi Ht) as ((_ & Wk & _ & Ha) & _ & ESq).
  destruct (sq_inj_c Hc ESq) as (Ekl & EAC).
  assert (Ha' : [ G ; Γ ⊢[ i ] a : A @ l ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Ha | exact (lequiv_sym _ _ _ Ekl)] | rewrite Hi; exact EAC]).
  assert (Hsq : [ G ; Γ ⊢[ i ] tmSq l A a ≅ tmSq k C a : tySq l A @ l ])
    by (apply eqtm_sq_irr; [exact Hc | exact W1 | apply wf_sq; assumption | exact Ht]).
  assert (Hcong : [ G ; Γ ⊢[ i ] tmElimSq l l' A M c (tmSq k C a)
                     ≅ tmElimSq l l' A M c (tmSq l A a) : tySq l' M[lsingle (tmSq k C a)] @ l' ])
    by exact (eqtm_elimSq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ltac:(apply compt_notV; exact Hc) (lequiv_refl _ _ W1) (lequiv_refl _ _ W2) HA
                (eqty_refl _ _ _ _ _ HA) HM (eqty_refl _ _ _ _ _ HM) (eqtm_refl _ _ _ _ _ _ Hcc)
                (eqtm_sym _ _ _ _ _ _ _ Hsq)).
  pose proof (eqtm_elimSq_sq _ _ _ _ _ _ _ _ _ Hc W1 W2 HA HM Hcc Ha') as Hb.
  eapply eqtm_trans; [exact Hcong |].
  eapply eqtm_conv; [exact Hb | rewrite Hi].
  apply eqty_sq; [exact Hv | exact (lequiv_refl _ _ W2) | exact (wf_ty_single Hi HM Ht) |].
  exact (wf_ty_func Hi HM (lsub_eq_single Hi Ht (eqtm_wf_l Hi Hsq) (eqtm_sym _ _ _ _ _ _ _ Hsq))).
Qed.

(** [elim_W] (M13a): the congruence at the scrutinee, and β at a [sup] of
    any annotations (they equal the [elim_W]'s, by injectivity). *)
Lemma RS_elimW l l' l'' A B M c t t' : RS_tm t t' ->
  RS_tm (tmElimW l l' l'' A B M c t) (tmElimW l l' l'' A B M c t').
Proof.
  intros IH G i Γ T k Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_elimW Hi Hx) as ((_ & W1 & W2 & W3 & HA & HB & HM & HF & HI & Hc0 & Ht) & Hk & ET).
  refine (retype_eqtm Hi _ Hk ET).
  apply eqtm_elimW; first [exact Hc | now apply compt_notV | apply lequiv_refl; assumption | exact (IH _ _ _ _ _ Hc Ht) | assumption
                          | apply eqty_refl; assumption | apply eqtm_refl; assumption].
Qed.

Lemma RS_elimW_sup l l' l'' A B M c k k' C D a f :
  RS_tm (tmElimW l l' l'' A B M c (tmSup k k' C D a f)) c[lsingle3 a f (wIH l l' l'' A B M c a f)].
Proof.
  intros G i Γ T m Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_elimW Hi Hx) as ((_ & W1 & W2 & W3 & HA & HB & HM & HF & HI & Hc0 & Ht) & Hk & ET).
  refine (retype_eqtm Hi _ Hk ET).
  destruct (sup_parts Hc Ht) as (_ & _ & _ & _ & Ha & Hf).
  destruct (inv_sup Hi Ht) as (_ & _ & ESup).
  destruct (W_inj_c Hc ESup) as (Ekl & Ek'l' & EAC & EBD).
  assert (Hsup : [ G ; Γ ⊢[ i ] tmSup l l' A B a f ≅ tmSup k k' C D a f : tyW l l' A B @ lmax l l' ])
    by (apply eqtm_sup; first [exact Hc | now apply compt_notV | assumption | now apply lequiv_sym | apply eqtm_refl; assumption]).
  assert (Hcong : [ G ; Γ ⊢[ i ] tmElimW l l' l'' A B M c (tmSup k k' C D a f)
                     ≅ tmElimW l l' l'' A B M c (tmSup l l' A B a f) : M[lsingle (tmSup k k' C D a f)] @ l'' ]).
  { apply eqtm_elimW; first [exact Hc | now apply compt_notV | apply lequiv_refl; assumption | apply eqtm_sym, Hsup | assumption
                            | apply eqty_refl; assumption | apply eqtm_refl; assumption]. }
  pose proof (eqtm_elimW_sup _ _ _ _ _ _ _ _ _ _ _ _ Hc W1 W2 W3 HA HB HM HF HI Hc0 Ha Hf) as Hb.
  eapply eqtm_trans; [exact Hcong |].
  eapply eqtm_conv; [exact Hb | rewrite Hi].
  exact (wf_ty_func Hi HM (lsub_eq_single Hi Ht (eqtm_wf_l Hi Hsup) (eqtm_sym _ _ _ _ _ _ _ Hsup))).
Qed.

(** [elim_Wf] (M15a), as [elim_W]. *)
Lemma RS_elimWf l l' A N M c t t' : RS_tm t t' ->
  RS_tm (tmElimWf l l' A N M c t) (tmElimWf l l' A N M c t').
Proof.
  intros IH G i Γ T k Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_elimWf Hi Hx) as ((_ & W1 & W2 & HA & HN & HM & HC & HI & Hc0 & Ht) & Hk & ET).
  refine (retype_eqtm Hi _ Hk ET).
  apply eqtm_elimWf; first [(apply compt_notV; exact Hc) | exact Hc | apply lequiv_refl; assumption | exact (IH _ _ _ _ _ Hc Ht) | assumption
                           | apply eqty_refl; assumption | apply eqtm_refl; assumption].
Qed.

Lemma RS_elimWf_supf l l' A N M c k C D a cs :
  RS_tm (tmElimWf l l' A N M c (tmSupf k C D a cs)) c[lsingle3 a cs (wfIH l l' A N M c a cs)].
Proof.
  intros G i Γ T m Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_elimWf Hi Hx) as ((_ & W1 & W2 & HA & HN & HM & HC & HI & Hc0 & Ht) & Hk & ET).
  refine (retype_eqtm Hi _ Hk ET).
  destruct (supf_parts Hc Ht) as (_ & _ & _ & Ha & Hcs).
  destruct (inv_supf Hi Ht) as (_ & _ & ESup).
  destruct (Wf_inj_c Hc ESup) as (Ekl & EAC & END).
  assert (Hsup : [ G ; Γ ⊢[ i ] tmSupf l A N a cs ≅ tmSupf k C D a cs : tyWf l A N @ l ])
    by (apply eqtm_supf; first [(apply compt_notV; exact Hc) | exact Hc | assumption | now apply lequiv_sym | apply eqtm_refl; assumption]).
  assert (Hcong : [ G ; Γ ⊢[ i ] tmElimWf l l' A N M c (tmSupf k C D a cs)
                     ≅ tmElimWf l l' A N M c (tmSupf l A N a cs) : M[lsingle (tmSupf k C D a cs)] @ l' ]).
  { apply eqtm_elimWf; first [(apply compt_notV; exact Hc) | exact Hc | apply lequiv_refl; assumption | apply eqtm_sym, Hsup | assumption
                             | apply eqty_refl; assumption | apply eqtm_refl; assumption]. }
  pose proof (eqtm_elimWf_supf _ _ _ _ _ _ _ _ _ _ _ Hc W1 W2 HA HN HM HC HI Hc0 Ha Hcs) as Hb.
  eapply eqtm_trans; [exact Hcong |].
  eapply eqtm_conv; [exact Hb | rewrite Hi].
  exact (wf_ty_func Hi HM (lsub_eq_single Hi Ht (eqtm_wf_l Hi Hsup) (eqtm_sym _ _ _ _ _ _ _ Hsup))).
Qed.

(** [elim_IWf] (M17b), as [elim_Wf]. β fires at any index and any
    annotations: the [sup_i] is equal to the canonical one at the scrutinee's
    index (its output index is, by inversion), and the motive's two
    instances are related along both. *)
Lemma RS_elimIWf l li l' X A N Ot C M c m t t' : RS_tm t t' ->
  RS_tm (tmElimIWf l li l' X A N Ot C M c m t) (tmElimIWf l li l' X A N Ot C M c m t').
Proof.
  intros IH G i Γ T k Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_elimIWf Hi Hx)
    as ((_ & W3 & W1 & W2 & HX & HA & HN & HO & HC & Hmot & HM & HCs & HI & Hc0 & Hm & Ht) & Hk & ET).
  refine (retype_eqtm Hi _ Hk ET).
  apply eqtm_elimIWf; first [exact Hc | apply lequiv_refl; assumption | exact (IH _ _ _ _ _ Hc Ht) | assumption
                            | apply eqty_refl; assumption | apply eqtm_refl; assumption].
Qed.

Lemma RS_elimIWf_supi l li l' X A N Ot C M c m k ki X' A' N' Ot' C' a cs :
  RS_tm (tmElimIWf l li l' X A N Ot C M c m (tmSupi k ki X' A' N' Ot' C' a cs))
        c[lsingle3 a cs (iwfIH l li l' X A N Ot C M c a cs)].
Proof.
  intros G i Γ T q Hc Hx. pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  destruct (inv_elimIWf Hi Hx)
    as ((_ & W3 & W1 & W2 & HX & HA & HN & HO & HC & Hmot & HM & HCs & HI & Hc0 & Hm & Ht) & Hk & ET).
  refine (retype_eqtm Hi _ Hk ET).
  destruct (supi_parts Hc Ht) as (HS & HE & Ha & Hcs & Eom & _).
  pose proof HE as (Hlk & Hlik & _ & HXX & HAA & HNN & HOO & HCC & _).
  pose proof (IWfSig_nf HS) as (NX & NA & NN & NO & NC).
  assert (Hsup0 : [ G ; Γ ⊢[ i ] tmSupi l li X A N Ot C a cs ≅ tmSupi k ki X' A' N' Ot' C' a cs
                    : tyIWf l li X A N Ot C Ot[lsingle a] @ lmax l li ])
    by (apply eqtm_supi; first [exact Hc | assumption | apply eqtm_refl; assumption]).
  assert (Hsup : [ G ; Γ ⊢[ i ] tmSupi l li X A N Ot C a cs ≅ tmSupi k ki X' A' N' Ot' C' a cs
                   : tyIWf l li X A N Ot C m @ lmax l li ]).
  { eapply eqtm_conv; [exact Hsup0 | rewrite Hi].
    exact (eqty_sym _ _ _ _ _ _ (IWf_ty_eq_idx Hi Hv HS Eom)). }
  assert (Hcong : [ G ; Γ ⊢[ i ] tmElimIWf l li l' X A N Ot C M c m (tmSupi k ki X' A' N' Ot' C' a cs)
                     ≅ tmElimIWf l li l' X A N Ot C M c Ot[lsingle a] (tmSupi l li X A N Ot C a cs)
                     : M[lsingle2 m (tmSupi k ki X' A' N' Ot' C' a cs)] @ l' ]).
  { apply eqtm_elimIWf; first [exact Hc | apply lequiv_refl; assumption | apply eqtm_sym, Hsup
                             | apply eqtm_sym, Eom | assumption
                             | apply eqty_refl; assumption | apply eqtm_refl; assumption]. }
  pose proof (IWf_IH_wf Hi Hv HS W3 HM HI Hc0 Ha Hcs) as Hλ.
  pose proof (eqtm_elimIWf_supi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hc W1 W2 W3 HX HA HN HO HC Hmot HM HCs HI Hc0 Ha Hcs Hλ)
    as Hb.
  eapply eqtm_trans; [exact Hcong |].
  eapply eqtm_conv; [exact Hb | rewrite Hi].
  refine (wf_ty_func Hi HM (lsub_eq_single2 Hi Hm (eqtm_wf_l Hi Eom) (eqtm_sym _ _ _ _ _ _ _ Eom) _ _ _));
    rewrite IWf_E_mot by assumption;
    [exact Ht | exact (eqtm_wf_l Hi Hsup0) | exact (eqtm_sym _ _ _ _ _ _ _ Hsup)].
Qed.

(** [Vec] and [Fin] (M14a): the computation rules at a canonical length,
    and the congruence at the length. [Vec^l(A; 0) ⇝ Unit^l] keeps the
    level [l], which is what Heather's level-indexed [Unit] repaired. *)
Lemma RS_vec_zero l A : RS_ty (tyVec l A zero) (tyUnit l).
Proof.
  intros G i Γ k Hc HT. destruct (inv_ty_vec HT) as ((_ & Wl & HA & _) & Hk).
  apply (retype_eqty Hk). exact (eqty_vec_zero _ _ _ _ _ Hc Wl HA).
Qed.

Lemma RS_vec_succ l A n : RS_ty (tyVec l A (succ n)) (tySig l l A (tyVec l A⟨↑⟩ n⟨↑⟩)).
Proof.
  intros G i Γ k Hc HT. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_vec HT) as ((_ & Wl & HA & Hs) & Hk).
  destruct (inv_succ Hi Hs) as ((_ & Hn) & _).
  apply (retype_eqty Hk). exact (eqty_vec_succ _ _ _ _ _ _ Hc Wl HA Hn).
Qed.

Lemma RS_vec l A n n' : RS_tm n n' -> RS_ty (tyVec l A n) (tyVec l A n').
Proof.
  intros IH G i Γ k Hc HT. destruct (inv_ty_vec HT) as ((_ & Wl & HA & Hn) & Hk).
  apply (retype_eqty Hk).
  exact (eqty_vec _ _ _ _ _ _ _ _ _ (compt_notV _ Hc) (lequiv_refl _ _ Wl) HA (eqty_refl _ _ _ _ _ HA) (IH _ _ _ _ _ Hc Hn)).
Qed.

Lemma RS_fin_zero : RS_ty (tyFin zero) (tyEmpty lzero).
Proof.
  intros G i Γ k Hc HT. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_fin HT) as ((_ & Hz) & Hk).
  destruct (inv_zero Hi Hz) as ((_ & HΓ) & _).
  apply (retype_eqty Hk). exact (eqty_fin_zero _ _ _ Hc HΓ).
Qed.

Lemma RS_fin_succ n : RS_ty (tyFin (succ n)) (tySum lzero lzero (tyUnit lzero) (tyFin n)).
Proof.
  intros G i Γ k Hc HT. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_fin HT) as ((_ & Hs) & Hk).
  destruct (inv_succ Hi Hs) as ((_ & Hn) & _).
  apply (retype_eqty Hk). exact (eqty_fin_succ _ _ _ _ Hc Hn).
Qed.

Lemma RS_fin n n' : RS_tm n n' -> RS_ty (tyFin n) (tyFin n').
Proof.
  intros IH G i Γ k Hc HT. destruct (inv_ty_fin HT) as ((_ & Hn) & Hk).
  apply (retype_eqty Hk). exact (eqty_fin _ _ _ _ _ (compt_notV _ Hc) (IH _ _ _ _ _ Hc Hn)).
Qed.

Lemma RS_dvec_zero l F : RS_ty (tyDVec l zero F) (tyUnit l).
Proof.
  intros G i Γ k Hc HT. destruct (inv_ty_dvec HT) as ((_ & Wl & _ & HF) & Hk).
  apply (retype_eqty Hk). exact (eqty_dvec_zero _ _ _ _ _ Hc Wl HF).
Qed.

Lemma RS_dvec_succ l n F : RS_ty (tyDVec l (succ n) F) (tySig l l (dvecHd n F) (dvecTl l n F)).
Proof.
  intros G i Γ k Hc HT. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_dvec HT) as ((_ & Wl & Hs & HF) & Hk).
  destruct (inv_succ Hi Hs) as ((_ & Hn) & _).
  apply (retype_eqty Hk). exact (eqty_dvec_succ _ _ _ _ _ _ Hc Wl Hn HF).
Qed.

Lemma RS_dvec l n n' F : RS_tm n n' -> RS_ty (tyDVec l n F) (tyDVec l n' F).
Proof.
  intros IH G i Γ k Hc HT. destruct (inv_ty_dvec HT) as ((_ & Wl & Hn & HF) & Hk).
  apply (retype_eqty Hk).
  exact (eqty_dvec _ _ _ _ _ _ _ _ _ Hc (lequiv_refl _ _ Wl) Hn (IH _ _ _ _ _ Hc Hn) HF (eqty_refl _ _ _ _ _ HF)).
Qed.

(** ** Soundness of reduction *)

Theorem red_sound_all (HR : RecRedTyped) :
  (forall t t', red t t' -> RS_tm t t') /\ (forall T T', red_ty T T' -> RS_ty T T').
Proof.
  apply red_both; intros;
    first
    [ solve [apply RS_natrec_zero] | solve [apply RS_natrec_succ] | solve [apply RS_beta]
    | solve [apply RS_natrec; assumption] | solve [apply RS_app; assumption]
    | solve [apply RS_letboxT_beta] | solve [apply RS_letboxt_beta]
    | solve [apply RS_letboxT; assumption] | solve [apply RS_letboxt; assumption]
    | solve [apply (RS_elimT_beta HR); assumption] | solve [apply (RS_elimt_beta HR); assumption]
    | solve [apply RS_elimT; assumption] | solve [apply RS_elimt; assumption]
    | solve [apply RS_elimt_idx; assumption]
    | solve [apply RS_ubeta; assumption] | solve [apply RS_uapp; assumption]
    | solve [apply RS_cbeta] | solve [apply RS_capp; assumption]
    | solve [apply RS_tbeta] | solve [apply RS_tapp; assumption]
    | solve [apply RS_El_nat] | solve [apply RS_El_U] | solve [apply RS_El_pi]
    | solve [apply RS_El; assumption]
    | solve [apply RS_fst_beta] | solve [apply RS_snd_beta]
    | solve [apply RS_fst; assumption] | solve [apply RS_snd; assumption] | solve [apply RS_El_sig]
    | solve [apply RS_El_unit] | solve [apply RS_delta] | solve [apply RS_elimSEmpty; assumption]
    | solve [apply RS_J_beta] | solve [apply RS_J; assumption] | solve [apply RS_El_id]
    | solve [apply RS_El_seq] | solve [apply RS_El_sempty]
    | solve [apply RS_elimEmpty; assumption]
    | solve [apply RS_case_inl] | solve [apply RS_case_inr] | solve [apply RS_case; assumption]
    | solve [apply RS_elimSq_sq] | solve [apply RS_elimSq; assumption]
    | solve [apply RS_elimW_sup] | solve [apply RS_elimW; assumption]
    | solve [apply RS_elimWf_supf] | solve [apply RS_elimWf; assumption]
    | solve [apply RS_elimIWf_supi] | solve [apply RS_elimIWf; assumption]
    | solve [apply RS_El_empty] | solve [apply RS_El_sum] | solve [apply RS_El_W]
    | solve [apply RS_vec_zero] | solve [apply RS_vec_succ] | solve [apply RS_vec; assumption]
    | solve [apply RS_fin_zero] | solve [apply RS_fin_succ] | solve [apply RS_fin; assumption]
    | solve [apply RS_El_vec] | solve [apply RS_El_fin] | solve [apply RS_El_wf]
    | solve [apply RS_El_sq]
    | solve [apply RS_dvec_zero] | solve [apply RS_dvec_succ] | solve [apply RS_dvec; assumption] ].
Qed.

Section Consequences.
Variable HR : RecRedTyped.

Theorem red_sound_tm {G i Γ t t' T k} : compt i -> [ G ; Γ ⊢[ i ] t : T @ k ] -> red t t' ->
  [ G ; Γ ⊢[ i ] t ≅ t' : T @ k ].
Proof. intros Hc Ht Hr. exact (proj1 (red_sound_all HR) _ _ Hr _ _ _ _ _ Hc Ht). Qed.

Theorem red_sound_ty {G i Γ T T' k} : compt i -> [ G ; Γ ⊢[ i ] T @ k ] -> red_ty T T' ->
  [ G ; Γ ⊢[ i ] T ≅ T' @ k ].
Proof. intros Hc HT Hr. exact (proj2 (red_sound_all HR) _ _ Hr _ _ _ _ Hc HT). Qed.

Theorem preservation_tm {G i Γ t t' T k} : compt i -> [ G ; Γ ⊢[ i ] t : T @ k ] -> red t t' ->
  [ G ; Γ ⊢[ i ] t' : T @ k ].
Proof. intros Hc Ht Hr. exact (eqtm_wf_r (compt_typeof_self _ Hc) (red_sound_tm Hc Ht Hr)). Qed.

Theorem preservation_ty {G i Γ T T' k} : compt i -> [ G ; Γ ⊢[ i ] T @ k ] -> red_ty T T' ->
  [ G ; Γ ⊢[ i ] T' @ k ].
Proof. intros Hc HT Hr. exact (eqty_wf_r (compt_typeof_self _ Hc) (red_sound_ty Hc HT Hr)). Qed.

(** Multi-step. *)
Theorem reds_sound_tm {G i Γ t t' T k} : compt i -> [ G ; Γ ⊢[ i ] t : T @ k ] -> reds t t' ->
  [ G ; Γ ⊢[ i ] t ≅ t' : T @ k ].
Proof.
  intros Hc Ht Hr. induction Hr as [t | t t1 t' Hr1 Hrs IH].
  - exact (eqtm_refl _ _ _ _ _ _ Ht).
  - exact (eqtm_trans _ _ _ _ _ _ _ _ (red_sound_tm Hc Ht Hr1) (IH (preservation_tm Hc Ht Hr1))).
Qed.

Theorem reds_sound_ty {G i Γ T T' k} : compt i -> [ G ; Γ ⊢[ i ] T @ k ] -> reds_ty T T' ->
  [ G ; Γ ⊢[ i ] T ≅ T' @ k ].
Proof.
  intros Hc HT Hr. induction Hr as [T | T T1 T' Hr1 Hrs IH].
  - exact (eqty_refl _ _ _ _ _ HT).
  - exact (eqty_trans _ _ _ _ _ _ _ (red_sound_ty Hc HT Hr1) (IH (preservation_ty Hc HT Hr1))).
Qed.

End Consequences.
