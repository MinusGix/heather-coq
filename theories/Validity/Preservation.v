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
    | solve [apply RS_El_unit] ].
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
