(** * Uniqueness of synthesized types (M7_DESIGN.md C1, J2, J3.4)

    A term whose type is determined by its syntax ([synth]: not a [λ] or a
    [box]) has one type up to equality and one level up to equivalence
    ([type_uniq]). For most heads, inversion equates both types with the
    same syntactic type (the abstractions' annotated formers included, C1b).
    For [uapp]/[capp]/[tapp] the function's types are equal (by induction;
    a checked function has a former of another head, [chk_head]), so their
    bodies are ([upi_inj], [cpi_inj], [tpi_inj]), and so are the instances. *)
From DeLaM.Typing Require Export DecSide.
From DeLaM.Validity Require Export TyInj.

(** ** Levels up to equivalence *)

Lemma lvl_eq_refl L k : lvl_eq L k k.
Proof. left; reflexivity. Qed.
Lemma lvl_eq_sym {L k l} : lvl_eq L k l -> lvl_eq L l k.
Proof. intros [->|H]; [left; reflexivity | right; exact (lequiv_sym _ _ _ H)]. Qed.
Lemma lvl_eq_trans {L a b c} : lvl_eq L a b -> lvl_eq L b c -> lvl_eq L a c.
Proof.
  intros [->|H1] [->|H2]; [left; reflexivity | right; exact H2 | right; exact H1 |].
  right; exact (lequiv_trans _ _ _ _ H1 H2).
Qed.

Lemma eqty_lvl {G i Γ T T' k l} : lvl_eq (gL G) k l -> [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> [ G ; Γ ⊢[ i ] T ≅ T' @ k ].
Proof. intros [->|Q] E; [exact E | exact (eqty_lconv _ _ _ _ _ _ _ E Q)]. Qed.
Lemma wft_lvl {G i Γ T k l} : lvl_eq (gL G) k l -> [ G ; Γ ⊢[ i ] T @ l ] -> [ G ; Γ ⊢[ i ] T @ k ].
Proof. intros [->|Q] E; [exact E | exact (wft_lconv _ _ _ _ _ _ E Q)]. Qed.
Lemma wf_lvl {G i Γ t T k l} : lvl_eq (gL G) k l -> [ G ; Γ ⊢[ i ] t : T @ l ] -> [ G ; Γ ⊢[ i ] t : T @ k ].
Proof. intros [->|Q] E; [exact E | exact (wf_lconv _ _ _ _ _ _ _ E Q)]. Qed.

(** Two types equal to related types. *)
Lemma uniq_fin {G j Γ T T' R R' k k' l0 l0'} :
  lvl_eq (gL G) k l0 -> lvl_eq (gL G) k' l0' -> lvl_eq (gL G) l0 l0' ->
  [ G ; Γ ⊢[ j ] T ≅ R @ k ] -> [ G ; Γ ⊢[ j ] T' ≅ R' @ k' ] -> [ G ; Γ ⊢[ j ] R ≅ R' @ l0 ] ->
  lvl_eq (gL G) k k' /\ [ G ; Γ ⊢[ j ] T ≅ T' @ k ].
Proof.
  intros H1 H2 H3 E E' ER.
  assert (Hkk : lvl_eq (gL G) k k') by exact (lvl_eq_trans H1 (lvl_eq_trans H3 (lvl_eq_sym H2))).
  split; [exact Hkk |].
  eapply eqty_trans; [exact E |]. eapply eqty_trans; [exact (eqty_lvl H1 ER) |].
  apply eqty_sym. exact (eqty_lvl Hkk E').
Qed.

Lemma uniq_same {G j Γ T T' R k k' l0} : lvl_eq (gL G) k l0 -> lvl_eq (gL G) k' l0 ->
  [ G ; Γ ⊢[ j ] T ≅ R @ k ] -> [ G ; Γ ⊢[ j ] T' ≅ R @ k' ] ->
  lvl_eq (gL G) k k' /\ [ G ; Γ ⊢[ j ] T ≅ T' @ k ].
Proof.
  intros H1 H2 E E'. assert (Hkk : lvl_eq (gL G) k k') by exact (lvl_eq_trans H1 (lvl_eq_sym H2)).
  split; [exact Hkk |]. eapply eqty_trans; [exact E |]. apply eqty_sym. exact (eqty_lvl Hkk E').
Qed.

(** ** Synthesizing and checked terms *)

Definition synth (t : tm) : Prop :=
  match t with lam _ _ _ _ | boxT _ | boxt _ => False | _ => True end.

Lemma synth_dec t : synth t \/ ~ synth t.
Proof. destruct t; cbn; tauto. Qed.

(** The head of a checked term's type. *)
Definition chk_head (t : tm) : nat :=
  match t with lam _ _ _ _ => 3 | boxT _ => 4 | boxt _ => 5 | _ => 0 end.

Lemma chk_ty {G i Γ t T k} : ~ synth t -> [ G ; Γ ⊢[ i ] t : T @ k ] ->
  exists F, whnf_ty F /\ ty_head F = chk_head t /\ [ G ; Γ ⊢[ typeof i ] T ≅ F @ k ].
Proof.
  intros Hs H. destruct t; cbn in Hs; try (exfalso; exact (Hs I)).
  - destruct (inva_lam H) as (B & _ & _ & E). eexists; split; [|split; [| exact E]]; auto with whnf.
  - pose proof (typed_m_only H I) as ->. destruct (inv_boxT eq_refl H) as (Δ & l & _ & _ & E).
    eexists; split; [|split; [| exact E]]; auto with whnf.
  - pose proof (typed_m_only H I) as ->. destruct (inv_boxt eq_refl H) as (Δ & A & l & _ & _ & E).
    eexists; split; [|split; [| exact E]]; auto with whnf.
Qed.

Lemma chk_at_whnf {G i Γ t W k} : ~ synth t -> [ G ; Γ ⊢[ i ] t : W @ k ] -> whnf_ty W ->
  ty_head W = chk_head t.
Proof.
  intros Hs H HW. destruct (chk_ty Hs H) as (F & HF & Eh & E).
  rewrite <- Eh. exact (decl_head_c (compt_typeof i) E HW HF).
Qed.


(** ** The theorem *)

Ltac uq_same :=
  match goal with
  | Hk : lvl_eq _ ?k ?l0, Hk' : lvl_eq _ ?k' ?l0, E : eq_ty _ _ _ ?T ?R ?k, E' : eq_ty _ _ _ ?T' ?R ?k'
    |- lvl_eq _ ?k ?k' /\ _ => exact (uniq_same Hk Hk' E E')
  end.

Theorem type_uniq t : synth t -> forall G i Γ T T' k k',
  [ G ; Γ ⊢[ i ] t : T @ k ] -> [ G ; Γ ⊢[ i ] t : T' @ k' ] ->
  lvl_eq (gL G) k k' /\ [ G ; Γ ⊢[ typeof i ] T ≅ T' @ k ].
Proof.
  induction t; intros Hs G0 i0 Γ0 Ty1 Ty2 k1 k2 H1 H2; cbn in Hs; try contradiction.
  all: try (exfalso; exact (no_junk H1 I)).
  (* the M-only heads are typed at M *)
  all: try (pose proof (typed_m_only H1 I) as ->).
  all: lazymatch type of H1 with
  | wf_tm _ _ _ (var _) _ _ =>
      destruct (inva_var H1) as (T0 & l0 & (_ & Hin) & Hk & E);
      destruct (inva_var H2) as (T1 & l1 & (_ & Hin') & Hk' & E');
      destruct (in_ctx_det Hin Hin') as [<- <-]; uq_same
  | wf_tm _ _ _ (gvar _ _) _ _ =>
      destruct (inva_gvar H1) as (Δ & j0 & T0 & l0 & (_ & Hin & _) & Hk & E);
      destruct (inva_gvar H2) as (Δ' & j1 & T1 & l1 & (_ & Hin' & _) & Hk' & E');
      let X := fresh "X" in pose proof (in_gctx_det Hin Hin') as X; injection X as <- <- <- <-; uq_same
  | wf_tm _ _ _ (gdef _ _ _) _ _ =>
      destruct (inva_gdef H1) as (Δ & T0 & l0 & t0 & (_ & Hin & _) & Hk & E);
      destruct (inva_gdef H2) as (Δ' & T1 & l1 & t1 & (_ & Hin' & _) & Hk' & E');
      let X := fresh "X" in pose proof (in_gctx_det Hin Hin') as X; injection X as <- <- <- <-; uq_same
  | wf_tm _ _ _ (elimT _ _ _ _ _ _) _ _ =>
      destruct (inv_elimT eq_refl H1) as (MT & Mt & bs & (Er & _) & Hk & E);
      destruct (inv_elimT eq_refl H2) as (MT' & Mt' & bs' & (Er' & _) & Hk' & E');
      rewrite Er in Er'; destruct (mkrb_inj_MT Er') as [<- <-]; uq_same
  | wf_tm _ _ _ (elimt _ _ _ _ _ _ _) _ _ =>
      destruct (inv_elimt eq_refl H1) as (MT & Mt & bs & (Er & _) & Hk & E);
      destruct (inv_elimt eq_refl H2) as (MT' & Mt' & bs' & (Er' & _) & Hk' & E');
      rewrite Er in Er'; destruct (mkrb_inj_MT Er') as [<- <-]; uq_same
  | wf_tm _ _ _ (uapp ?f ?ls) _ _ =>
      destruct (inv_uapp eq_refl H1) as (n & l & T0 & (_ & Hl & HT0 & Hlen & Hls & Ht) & Hk & E);
      destruct (inv_uapp eq_refl H2) as (n' & l' & T0' & (_ & Hl' & HT0' & Hlen' & _ & Ht') & Hk' & E');
      destruct (synth_dec f) as [Hst | Hst];
      [ destruct (IHt Hst _ _ _ _ _ _ _ Ht Ht') as (_ & EU);
        destruct (upi_inj EU) as (-> & Q & ET); subst n;
        let HΓ := fresh "HΓ" in pose proof (ctx_of_tm_any H1) as HΓ;
        refine (uniq_fin Hk Hk' _ E E' (uinst_eqty (ls := ls) (ctx_glob _ _ _ HΓ) (wf_ctx_dnf HΓ) Hls ET));
        right; exact (lequiv_lvsubst _ _ _ _ _ (usub_ok_uext _ _ _ _ Hls (usub_ok_id _)) Q)
      | let Eh := fresh "Eh" in pose proof (chk_at_whnf Hst Ht (whnf_tyUPi _ _ _)) as Eh;
        destruct f; cbn in Eh, Hst; first [discriminate Eh | exact (Hst I)] ]
  | wf_tm _ _ _ (capp ?f _) _ _ =>
      destruct (inv_capp eq_refl H1) as (l & T0 & (_ & Hl & HT0 & HΔ & Ht & _) & Hk & E);
      destruct (inv_capp eq_refl H2) as (l' & T0' & (_ & Hl' & HT0' & _ & Ht' & _) & Hk' & E');
      destruct (synth_dec f) as [Hst | Hst];
      [ destruct (IHt Hst _ _ _ _ _ _ _ Ht Ht') as (_ & EC);
        destruct (cpi_inj EC) as (Q & ET);
        let HΓ := fresh "HΓ" in pose proof (ctx_of_tm_any H1) as HΓ;
        exact (uniq_fin Hk Hk' (or_intror Q) E E' (inst_c_eqty HΓ HΔ ET))
      | let Eh := fresh "Eh" in pose proof (chk_at_whnf Hst Ht (whnf_tyCPi _ _)) as Eh;
        destruct f; cbn in Eh, Hst; first [discriminate Eh | exact (Hst I)] ]
  | wf_tm _ _ _ (tapp ?f _) _ _ =>
      destruct (inv_tapp eq_refl H1) as (Δ & l1 & l2 & T0 & (_ & Ht & HΔ & Hl1 & Hl2 & HT0 & HA & _) & Hk & E);
      destruct (inv_tapp eq_refl H2) as (Δ' & l1' & l2' & T0' & (_ & Ht' & _) & Hk' & E');
      destruct (synth_dec f) as [Hst | Hst];
      [ destruct (IHt Hst _ _ _ _ _ _ _ Ht Ht') as (Hl & EP);
        destruct (tpi_inj EP) as (Q1 & Q2 & EΔ & ET);
        let HΓ := fresh "HΓ" in pose proof (ctx_of_tm_any H1) as HΓ;
        exact (uniq_fin Hk Hk' (or_intror Q2) E E' (inst_t_eqty HΓ HA ET))
      | let Eh := fresh "Eh" in pose proof (chk_at_whnf Hst Ht (whnf_tyTPi _ _ _ _)) as Eh;
        destruct f; cbn in Eh, Hst; first [discriminate Eh | exact (Hst I)] ]
  | _ =>
      first
      [ destruct (inva_code_nat H1) as (_ & Hk & E); destruct (inva_code_nat H2) as (_ & Hk' & E'); uq_same
      | destruct (inva_code_pi H1) as (_ & Hk & E); destruct (inva_code_pi H2) as (_ & Hk' & E'); uq_same
      | destruct (inva_code_U H1) as (_ & Hk & E); destruct (inva_code_U H2) as (_ & Hk' & E'); uq_same
      | destruct (inva_zero H1) as (_ & Hk & E); destruct (inva_zero H2) as (_ & Hk' & E'); uq_same
      | destruct (inva_succ H1) as (_ & Hk & E); destruct (inva_succ H2) as (_ & Hk' & E'); uq_same
      | destruct (inva_natrec H1) as (_ & Hk & E); destruct (inva_natrec H2) as (_ & Hk' & E'); uq_same
      | destruct (inva_elimEmpty H1) as (_ & Hk & E); destruct (inva_elimEmpty H2) as (_ & Hk' & E'); uq_same
      | destruct (inva_app H1) as (_ & Hk & E); destruct (inva_app H2) as (_ & Hk' & E'); uq_same
      | destruct (inva_code_sig H1) as (_ & Hk & E); destruct (inva_code_sig H2) as (_ & Hk' & E'); uq_same
      | destruct (inva_pair H1) as (_ & Hk & E); destruct (inva_pair H2) as (_ & Hk' & E'); uq_same
      | destruct (inva_fst H1) as (_ & Hk & E); destruct (inva_fst H2) as (_ & Hk' & E'); uq_same
      | destruct (inva_snd H1) as (_ & Hk & E); destruct (inva_snd H2) as (_ & Hk' & E'); uq_same
      | destruct (inva_code_unit H1) as (_ & Hk & E); destruct (inva_code_unit H2) as (_ & Hk' & E'); uq_same
      | destruct (inva_triv H1) as (_ & Hk & E); destruct (inva_triv H2) as (_ & Hk' & E'); uq_same
      | destruct (inva_srefl H1) as (_ & Hk & E); destruct (inva_srefl H2) as (_ & Hk' & E'); uq_same
      | destruct (inva_elimSEmpty H1) as (_ & Hk & E); destruct (inva_elimSEmpty H2) as (_ & Hk' & E'); uq_same
      | destruct (inva_idrefl H1) as (_ & Hk & E); destruct (inva_idrefl H2) as (_ & Hk' & E'); uq_same
      | destruct (inva_J H1) as (_ & Hk & E); destruct (inva_J H2) as (_ & Hk' & E'); uq_same
      | destruct (inva_code_id H1) as (_ & Hk & E); destruct (inva_code_id H2) as (_ & Hk' & E'); uq_same
      | destruct (inva_code_seq H1) as (_ & Hk & E); destruct (inva_code_seq H2) as (_ & Hk' & E'); uq_same
      | destruct (inva_code_sempty H1) as (_ & Hk & E); destruct (inva_code_sempty H2) as (_ & Hk' & E'); uq_same
      | destruct (inv_letboxT eq_refl H1) as (_ & Hk & E); destruct (inv_letboxT eq_refl H2) as (_ & Hk' & E'); uq_same
      | destruct (inv_letboxt eq_refl H1) as (_ & Hk & E); destruct (inv_letboxt eq_refl H2) as (_ & Hk' & E'); uq_same
      | destruct (inv_ulam eq_refl H1) as (_ & Hk & E); destruct (inv_ulam eq_refl H2) as (_ & Hk' & E'); uq_same
      | destruct (inv_clam eq_refl H1) as (_ & Hk & E); destruct (inv_clam eq_refl H2) as (_ & Hk' & E'); uq_same
      | destruct (inv_tlam eq_refl H1) as (_ & Hk & E); destruct (inv_tlam eq_refl H2) as (_ & Hk' & E'); uq_same ]
  end.
Qed.
