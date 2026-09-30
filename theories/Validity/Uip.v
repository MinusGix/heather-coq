(** * UIP, stated (M11): the check of Heather's [docs/no-uip-model.md]

    The no-UIP model argues that [UIP₀] has no closed inhabitant. This
    file states UIP in the development's syntax and checks the model's
    predictions where the syntax can decide them:

    - [uip_pt] is UIP at a type and two endpoints, and [UIP0] the model's
      counterexample. The model uses [⌜Bool⌝]; the development has no sums,
      and [⌜Nat⌝] serves as well, since [ℕ] has a non-identity bijection.
      Both are well-formed types at every layer but V ([uip_pt_wf],
      [UIP0_wf]).
    - Where the model's fibres are discrete, UIP holds in the model, and
      the syntax proves it: [uip_unit] is a closed inhabitant of UIP at
      [Unit], by two [J]s and [Unit]-η. [Unit] enters the proof only
      through η ([u_eta]), which turns the motive's variable endpoint [y]
      back into [tt]. At [Ty 0] the same step would need [y ≅ ⌜Nat⌝] for a
      variable [y : Ty 0], and no rule gives it (there is no eliminator or
      η at [Ty l]): that is the room the model's non-discrete universe
      uses.
    - Closed proofs of an [Id] type are all convertible
      ([closed_id_uip], from canonicity). So the model's counterexample
      cannot be a closed term: it is the semantic [swap], which no closed
      proof denotes. This is UIP as a metatheorem, which the model does
      not contradict. *)
From DeLaM.Validity Require Import Canonicity.

(** ** The statement *)

(** [Π(p q : Id^l(A; a; b)). Id^l(Id^l(A; a; b); p; q)]. *)
Definition uip_pt (l : lvl) (A : ty) (a b : tm) : ty :=
  tyPi l (lmax l l) (tyId l A a b)
    (tyPi l l (tyId l A a b)⟨↑⟩ (tyId l (tyId l A a b)⟨↑⟩⟨↑⟩ (var 1) (var 0))).

(** The model's [UIP₀], at [⌜Nat⌝] in [Ty 0]. *)
Definition UIP0 : ty := uip_pt (lsuc lzero) (tyU lzero) tmNat tmNat.

Lemma uip_pt_wf {G i Γ l A a b} : i <> lV -> lwf (gL G) l ->
  [ G ; Γ ⊢[ i ] A @ l ] -> [ G ; Γ ⊢[ i ] a : A @ l ] -> [ G ; Γ ⊢[ i ] b : A @ l ] ->
  [ G ; Γ ⊢[ i ] uip_pt l A a b @ lmax l (lmax l l) ].
Proof.
  intros Hv Hl HA Ha Hb. unfold uip_pt.
  assert (HI : [ G ; Γ ⊢[ i ] tyId l A a b @ l ]) by (apply wft_id; assumption).
  pose proof (proj1 (proj2 (proj2 ctx_extract)) _ _ _ _ _ HI) as HΓ.
  assert (HΓ1 : [ G ; Γ ,, tyId l A a b @ l ⊢[ typeof i ] ])
    by (apply wfc_ext; [exact HΓ | exact (lift_ty HI (lle_self_typeof i)) | exact Hl]).
  assert (HI1 : [ G ; Γ ,, tyId l A a b @ l ⊢[ i ] (tyId l A a b)⟨↑⟩ @ l ]) by (apply wk1_ty_g; assumption).
  assert (HΓ2 : [ G ; Γ ,, tyId l A a b @ l ,, (tyId l A a b)⟨↑⟩ @ l ⊢[ typeof i ] ])
    by (apply wfc_ext; [exact HΓ1 | exact (lift_ty HI1 (lle_self_typeof i)) | exact Hl]).
  apply wft_pi; [exact Hv | exact Hl | exact (conj Hl Hl) | exact HI |].
  apply wft_pi; [exact Hv | exact Hl | exact Hl | exact HI1 |].
  apply wft_id; [exact Hv | exact Hl | apply wk1_ty_g; assumption | |].
  - apply wf_var; [exact HΓ2 | apply in_there, in_here].
  - apply wf_var; [exact HΓ2 | apply in_here].
Qed.

(** [UIP₀] is a closed type, at every layer but V, in any global context. *)
Theorem UIP0_wf {G i} : [ ⊢ G ] -> i <> lV ->
  [ G ; cnil ⊢[ i ] UIP0 @ lmax (lsuc lzero) (lmax (lsuc lzero) (lsuc lzero)) ].
Proof.
  intros HG Hv. unfold UIP0. apply uip_pt_wf; [exact Hv | exact I | apply wft_U | apply wf_code_nat | apply wf_code_nat].
  all: first [exact Hv | exact I | apply wfc_nil, HG].
Qed.

(** ** UIP at [Unit], by [J] and [Unit]-η *)

Local Notation uU := (tyUnit lzero).
Local Notation utt := (tmTriv lzero).
Local Notation uI := (tyId lzero uU utt utt).
Local Notation urefl := (tmRefl lzero uU utt).
(** [J]'s motive context over [Δ]: [y : Unit, p' : Id(Unit; tt; y)]. *)
Local Notation Jctx Δ := (Δ ,, uU @ lzero ,, tyId lzero uU⟨↑⟩ utt⟨↑⟩ (var 0) @ lzero).

(** [K]'s motive: [Id(Id(Unit; tt; y); refl; p')]. *)
Definition uK_mot : ty := tyId lzero (tyId lzero uU utt (var 1)) urefl (var 0).
(** [K(e) : Id(Id(Unit; tt; tt); refl; e)]. *)
Definition uK (e : tm) : tm := tmJ lzero lzero uU utt uK_mot (tmRefl lzero uI urefl) utt e.
(** UIP's motive, under [p q]: [Id(Id(Unit; tt; y); p'; q)]. *)
Definition uUIP_mot : ty := tyId lzero (tyId lzero uU utt (var 1)) (var 0) (var 2).
(** [λ p q. J(y p'. Id(p'; q); K(q); tt; p)]. *)
Definition uip_unit : tm :=
  lam lzero (lmax lzero lzero) uI
    (lam lzero lzero uI (tmJ lzero lzero uU utt uUIP_mot (uK (var 0)) utt (var 1))).

Section UnitUip.
Context {G : gctx}.

Let Hv : lD <> lV. Proof. discriminate. Qed.

Lemma u_ty {Δ} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lD ] uU @ lzero ].
Proof. intros HΔ. apply wft_unit; [discriminate | exact HΔ | exact I]. Qed.
Lemma u_tt {Δ} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lD ] utt : uU @ lzero ].
Proof. intros HΔ. apply wf_triv; [discriminate | exact HΔ | exact I]. Qed.
Lemma u_I {Δ} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lD ] uI @ lzero ].
Proof. intros HΔ. apply wft_id; [discriminate | exact I | exact (u_ty HΔ) | exact (u_tt HΔ) | exact (u_tt HΔ)]. Qed.
Lemma u_refl {Δ} : [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ ⊢[ lD ] urefl : uI @ lzero ].
Proof. intros HΔ. apply wf_idrefl; [discriminate | exact I | exact (u_ty HΔ) | exact (u_tt HΔ)]. Qed.

(** The one step that needs [Unit]: every point of [Unit] is [tt]. *)
Lemma u_eta {Δ t} : [ G ; Δ ⊢[ lD ] t : uU @ lzero ] -> [ G ; Δ ⊢[ lD ] t ≅ utt : uU @ lzero ].
Proof. intros Ht. apply eqtm_unit_eta; [exact compt_D | exact I | exact Ht | exact (u_tt (ctx_of_wf_tm eq_refl Ht))]. Qed.

(** [Id(Unit; tt; t) ≅ Id(Unit; tt; tt)], by η at [t]. *)
Lemma u_Id_eta {Δ t} : [ G ; Δ ⊢[ lD ] t : uU @ lzero ] ->
  [ G ; Δ ⊢[ lD ] tyId lzero uU utt t ≅ uI @ lzero ].
Proof.
  intros Ht. pose proof (ctx_of_wf_tm eq_refl Ht) as HΔ.
  apply eqty_id; [discriminate | exact (lequiv_refl (gL G) lzero I) | exact (u_ty HΔ) | exact (eqty_refl _ _ _ _ _ (u_ty HΔ))
                 | exact (eqtm_refl _ _ _ _ _ _ (u_tt HΔ)) | exact (u_eta Ht)].
Qed.

Lemma u_Jctx {Δ} : [ G ; Δ ⊢[ lD ] ] ->
  [ G ; Δ ,, uU @ lzero ⊢[ lD ] tyId lzero uU⟨↑⟩ utt⟨↑⟩ (var 0) @ lzero ] /\ [ G ; Jctx Δ ⊢[ lD ] ].
Proof.
  intros HΔ.
  assert (HΔU : [ G ; Δ ,, uU @ lzero ⊢[ lD ] ]) by (apply wfc_ext; [exact HΔ | exact (u_ty HΔ) | exact I]).
  assert (H : [ G ; Δ ,, uU @ lzero ⊢[ lD ] tyId lzero uU⟨↑⟩ utt⟨↑⟩ (var 0) @ lzero ]).
  { apply wft_id; [discriminate | exact I | exact (u_ty HΔU) | exact (u_tt HΔU) | apply wf_var; [exact HΔU | apply in_here]]. }
  split; [exact H | apply wfc_ext; [exact HΔU | exact H | exact I]].
Qed.

(** In [J]'s motive context, [y : Unit] and [p' : Id(Unit; tt; y)]. *)
Lemma u_y {Δ} : [ G ; Jctx Δ ⊢[ lD ] ] -> [ G ; Jctx Δ ⊢[ lD ] var 1 : uU @ lzero ].
Proof. intros H. exact (wf_var _ lD _ _ _ _ H (in_there _ _ _ _ _ _ (in_here _ _ _))). Qed.
Lemma u_p {Δ} : [ G ; Jctx Δ ⊢[ lD ] ] -> [ G ; Jctx Δ ⊢[ lD ] var 0 : tyId lzero uU utt (var 1) @ lzero ].
Proof. intros H. exact (wf_var _ lD _ _ _ _ H (in_here _ _ _)). Qed.
Lemma u_Idy {Δ} : [ G ; Jctx Δ ⊢[ lD ] ] -> [ G ; Jctx Δ ⊢[ lD ] tyId lzero uU utt (var 1) @ lzero ].
Proof. intros H. apply wft_id; [discriminate | exact I | exact (u_ty H) | exact (u_tt H) | exact (u_y H)]. Qed.

(** [K]: every proof of [Id(Unit; tt; tt)] equals [refl]. *)
Lemma uK_wf {Δ e} : [ G ; Δ ⊢[ lD ] e : uI @ lzero ] -> [ G ; Δ ⊢[ lD ] uK e : tyId lzero uI urefl e @ lzero ].
Proof.
  intros He. pose proof (ctx_of_wf_tm eq_refl He) as HΔ. destruct (u_Jctx HΔ) as [HI HM].
  refine (wf_J G lD _ lzero lzero _ _ _ _ _ _ Hv I I (u_ty HΔ) (u_tt HΔ) HI _ _ (u_tt HΔ) He).
  - apply wft_id; [discriminate | exact I | exact (u_Idy HM) | | exact (u_p HM)].
    eapply wf_conv; [exact (u_refl HM) | exact (u_Id_eta (u_y HM))].
  - apply wf_idrefl; [discriminate | exact I | exact (u_I HΔ) | exact (u_refl HΔ)].
Qed.

(** UIP at [Unit]. *)
Theorem uip_unit_wf {Γ} : [ G ; Γ ⊢[ lD ] ] ->
  [ G ; Γ ⊢[ lD ] uip_unit : uip_pt lzero uU utt utt @ lmax lzero (lmax lzero lzero) ].
Proof.
  intros HΓ.
  assert (HΓ1 : [ G ; Γ ,, uI @ lzero ⊢[ lD ] ]) by (apply wfc_ext; [exact HΓ | exact (u_I HΓ) | exact I]).
  assert (HΓ2 : [ G ; Γ ,, uI @ lzero ,, uI @ lzero ⊢[ lD ] ])
    by (apply wfc_ext; [exact HΓ1 | exact (u_I HΓ1) | exact I]).
  destruct (u_Jctx HΓ2) as [HI HM].
  unfold uip_unit, uip_pt.
  apply wf_lam; [discriminate | exact I | exact (conj I I) | exact (u_I HΓ) |].
  apply wf_lam; [discriminate | exact I | exact I | exact (u_I HΓ1) |].
  refine (wf_J G lD _ lzero lzero _ _ _ _ _ _ Hv I I (u_ty HΓ2) (u_tt HΓ2) HI _ _ (u_tt HΓ2) _).
  - (* the motive: [q : Id(Unit; tt; y)] by η *)
    apply wft_id; [discriminate | exact I | exact (u_Idy HM) | exact (u_p HM) |].
    eapply wf_conv; [apply wf_var; [exact HM | apply in_there, in_there, in_here] | exact (u_Id_eta (u_y HM))].
  - (* the base case at [(tt, refl)] is [K(q)] *)
    exact (uK_wf (wf_var _ lD _ _ _ _ HΓ2 (in_here _ _ _))).
  - exact (wf_var _ lD _ _ _ _ HΓ2 (in_there _ _ _ _ _ _ (in_here _ _ _))).
Qed.

End UnitUip.

(** ** UIP for closed proofs, from canonicity *)

(** Two [refl]s at one [Id] type are convertible: both points equal the
    left endpoint. *)
Lemma refl_refl_eq {G i Γ k k' C C' c c' T m} : compt i ->
  [ G ; Γ ⊢[ i ] tmRefl k C c : T @ m ] -> [ G ; Γ ⊢[ i ] tmRefl k' C' c' : T @ m ] ->
  [ G ; Γ ⊢[ i ] tmRefl k C c ≅ tmRefl k' C' c' : T @ m ].
Proof.
  intros Hc Ht Ht'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_idrefl Hi Ht) as ((Hv & _ & HC & _) & Hk & ET).
  destruct (inv_idrefl Hi Ht') as (_ & _ & ET').
  destruct (id_inj_c Hc (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ ET) ET')) as (Ekk & ECC & Ecc & _).
  pose proof (eqtm_idrefl _ _ _ _ _ _ _ _ _ Hv (lequiv_sym _ _ _ Ekk) HC ECC Ecc) as Econg.
  eapply eqtm_conv; [exact (lvl_eq_eqtm Hk Econg) | rewrite Hi; exact ET].
Qed.

(** Any two closed proofs of an [Id] type are convertible. *)
Theorem closed_id_uip {G i p q l A a b k} : compt i -> closed_ok i G ->
  [ G ; cnil ⊢[ i ] p : tyId l A a b @ k ] -> [ G ; cnil ⊢[ i ] q : tyId l A a b @ k ] ->
  [ G ; cnil ⊢[ i ] p ≅ q : tyId l A a b @ k ].
Proof.
  intros Hc HG Hp Hq. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (closed_canonicity_whnf Hc HG (whnf_tyId _ _ _ _) Hp) as (w & _ & _ & Ep & (l1 & A1 & a1 & ->)).
  destruct (closed_canonicity_whnf Hc HG (whnf_tyId _ _ _ _) Hq) as (w' & _ & _ & Eq & (l2 & A2 & a2 & ->)).
  pose proof (refl_refl_eq Hc (eqtm_wf_r Hi Ep) (eqtm_wf_r Hi Eq)) as Er.
  exact (eqtm_trans _ _ _ _ _ _ _ _ Ep (eqtm_trans _ _ _ _ _ _ _ _ Er (eqtm_sym _ _ _ _ _ _ _ Eq))).
Qed.

(** So at [UIP₀]'s carrier: closed proofs of [Id^1(Ty 0; ⌜Nat⌝; ⌜Nat⌝)]
    are all convertible (to [refl]), although [UIP₀] itself has no closed
    proof in the model. *)
Corollary closed_uip0_carrier {G p q k} : closed_ok lD G ->
  [ G ; cnil ⊢[ lD ] p : tyId (lsuc lzero) (tyU lzero) tmNat tmNat @ k ] ->
  [ G ; cnil ⊢[ lD ] q : tyId (lsuc lzero) (tyU lzero) tmNat tmNat @ k ] ->
  [ G ; cnil ⊢[ lD ] p ≅ q : tyId (lsuc lzero) (tyU lzero) tmNat tmNat @ k ].
Proof. exact (closed_id_uip compt_D). Qed.
