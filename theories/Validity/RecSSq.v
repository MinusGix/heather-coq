(** * The recursion lemmas on code: propositional truncation (M16b)

    A part of [RecS.v]'s Section [Rec], reopened over the same data and
    hypotheses ([RecH.RecHyps], RecSBase.v) so that the parts build in
    parallel. *)
From DeLaM.Validity Require Import RecSBase.

Section Rec.
Context {EP EM : GenericEq} {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM} {EMl : GenericEqM EP EM}.

Local Notation LRM := (LR_M EP EM).
Local Notation GSubRel := (GSubRel EP EM).
Local Notation VCtxSM := (@VCtxS EP EM EM LRM).
Local Notation VTySM := (@VTyS EP EM EM LRM).
Local Notation VTmSM := (@VTmS EP EM EM LRM).
Local Notation SubRelM := (@SubRel EM LRM).
Local Notation LRtyM := (@LRty EM LRM).
Local Notation LRtmM := (@LRtm EM LRM).
#[local] Existing Instance LR_M_lawsRec2.

Context {G0 : gctx} {Γ0 : ctx} {L' : nat} {φ : nat -> lvl} {l1 l2 l1' l2' : lvl}
  {MT MT' Mt Mt' : ty} {bs bs' : nat -> tm}.
Context {G' : gctx} {σ σ' : gsub} {Θ : ctx} {e e' : lsub}.
Context {RH : @RecH.RecHyps EP EM G0 Γ0 L' φ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' G' σ σ' Θ e e'}.

Let Hφ := @RecH.Hφ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let HMT := @RecH.HMT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let HMT' := @RecH.HMT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let Hl1 := @RecH.Hl1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let VMT := @RecH.VMT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let VMTl := @RecH.VMTl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let VMTr := @RecH.VMTr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let HMt := @RecH.HMt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let HMt' := @RecH.HMt' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let Hl2 := @RecH.Hl2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let VMt := @RecH.VMt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let VMtl := @RecH.VMtl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let VMtr := @RecH.VMtr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let Hbs := @RecH.Hbs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let Hbs' := @RecH.Hbs' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let VBr := @RecH.VBr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let VBr' := @RecH.VBr' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let VΓ := @RecH.VΓ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let Hσ := @RecH.Hσ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let He := @RecH.He _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let HrbL := @RecH.HrbL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let HrbR := @RecH.HrbR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let EL := @RecH.EL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let HG0 := @RecH.HG0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let HΓ0 := @RecH.HΓ0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let VΓT := @RecH.VΓT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let VΓt := @RecH.VΓt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.
Let VΓbr := @RecH.VΓbr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ RH.

Local Notation MTL := ((usubst_ty MT (uup φ))⦃gup (guwk σ)⦄[llift (gwk (uwk e))]).
Local Notation MTR := ((usubst_ty MT' (uup φ))⦃gup (guwk σ')⦄[llift (gwk (uwk e'))]).
Local Notation MtL := ((usubst_ty Mt (uup φ))⦃gup (gup (guwk σ))⦄[llift (gwk (gwk (uwk e)))]).
Local Notation MtR := ((usubst_ty Mt' (uup φ))⦃gup (gup (guwk σ'))⦄[llift (gwk (gwk (uwk e')))]).
Local Notation bsL := (fun k => ((usubst_tm (bs k) (uupn (br_nu k) φ))⦃gbsub k σ⦄)[lliftn (br_nl k) (bsub k e)]).
Local Notation bsR := (fun k => ((usubst_tm (bs' k) (uupn (br_nu k) φ))⦃gbsub k σ'⦄)[lliftn (br_nl k) (bsub k e')]).

Local Notation recTL k Δ c := (elimT (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) k Δ (boxT c)).
Local Notation recTR k Δ c := (elimT (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) k Δ (boxT c)).
Local Notation rectL k Δ T c := (elimt (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) k Δ T (boxt c)).
Local Notation rectR k Δ T c := (elimt (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) k Δ T (boxt c)).
#[local] Existing Instance LR_M_permRec.
(** [RT]/[Rt] (RecSBase.v) at this section's data. *)
Local Notation RT := (@RecSBase.RT EP EM L' φ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' G' σ σ' Θ e e').
Local Notation Rt := (@RecSBase.Rt EP EM L' φ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' G' σ σ' Θ e e').

(** Propositional truncation (M16b): each branch in one lemma, as [Wf]'s,
    its calls through [RTcall]/[Rtcall] and its payloads through [GS_br]. *)
Lemma RT_sq {Δ k A} : lwf (gL G') k -> [ G' ; Δ ⊢[ lC ] A @ k ] -> RT Δ A k -> RT Δ (tySq k A) k.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtr VΓ.
  intros Hw HA IHA Hc ΔR kL kR c' HΔ HkL HkR E W. rewrite EL in Hw.
  pose proof (sc_ctx HCD Hc) as HΔL. pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1, H into Ek end.
  match goal with H : ty_leq A ?x |- _ => rename x into A', H into EA end.
  match goal with H : lwf L' k1 |- _ => rename H into Hw1 end.
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  destruct (RTcall HΔL HΔ Hw Hw1 Ek HA EA ltac:(assumption) IHA)
    as (HA' & HAA & HA'R & HA'R1 & CA & CA1 & X1 & X1r).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tySq k1 A' @ k1 ])
    by (apply wft_sq; [discriminate | rewrite EL; exact Hw1 | exact HA'R1]).
  assert (HcRL : [ G' ; Δ ⊢[ lC ] tySq k1 A' @ k ])
    by (eapply wft_lconv; [exact (ctxconv_ty (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | rewrite EL; exact Q]).
  refine (rec_T_br 51 (k :: nil) (k1 :: nil) (GCtx Δ :: GTy A :: nil) (GCtx ΔR :: GTy A' :: nil)
            (recTL k Δ A :: nil) (recTR k1 ΔR A' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ Ek (Forall2_nil _)))
            HΔL HΔ HkL HkR Q Hc HcRL HcR0 ltac:(cbn; repeat split; assumption)
            (GS_br EP EM 51 (k :: nil) eq_refl Hσ _) (GS_br EP EM 51 (k1 :: nil) eq_refl (GSubRel_refl_r EP EM Hσ) _) _ _ _ _ _ _ _).
  - gs_solve.
  - gs_solve.
  - sr_ctx; exact X1.
  - sr_ctx; exact X1r.
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redT_sq_inst; inst_side 51.
  - apply redT_sq_inst; inst_side 51.
Qed.

Lemma Rt_codesq {Δ k s} : lwf (gL G') k -> [ G' ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] ->
  Rt Δ s (tyU k) (lsuc k) -> Rt Δ (tmSqCode k s) (tyU k) (lsuc k).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hw Hs IHs Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1, H into Ek end.
  match goal with H : tm_leq s ?x |- _ => rename x into s', H into Es end.
  match goal with H : lwf L' k1 |- _ => rename H into Hw1 end.
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  assert (HUU : forall Δ j j', [ G' ; Δ ⊢[ lD ] ] -> lequiv L' j j' -> [ G' ; Δ ⊢[ lD ] tyU j ≅ tyU j' @ lsuc j ])
    by (intros; apply eqty_U; [discriminate | assumption | rewrite EL; assumption]).
  destruct (Rtcall (k := lsuc k) (k1 := lsuc k1) HΔL HΔ Hw Hw1 (leqv_lsuc _ _ Ek) (HUU _ _ _ HΔL Q) Hs Es ltac:(assumption) IHs)
    as (Hs' & Hss & Hs'R & Hs'R1 & X1 & X1r).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmSqCode k1 s' : tyU k1 @ lsuc k1 ])
    by (apply wf_code_sq; [discriminate | rewrite EL; exact Hw1 | exact Hs'R1]).
  assert (HcRL : [ G' ; Δ ⊢[ lC ] tmSqCode k1 s' : tyU k @ lsuc k ])
    by (eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0)
                                          | rewrite EL; apply lequiv_suc, Q] | exact (HUU _ _ _ HΔL Q)]).
  refine (rec_t_br 52 (k :: nil) (k1 :: nil) (GCtx Δ :: GTm s :: nil) (GCtx ΔR :: GTm s' :: nil)
            (rectL (lsuc k) Δ (tyU k) s :: nil) (rectR (lsuc k1) ΔR (tyU k1) s' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ Ek (Forall2_nil _)))
            HΔL HΔ HkL HkR (lequiv_suc _ _ _ Q) HTL HTR (HUU _ _ _ HΔR Q) Hc HcRL HcR0 ltac:(cbn; repeat split; assumption)
            (GS_br EP EM 52 (k :: nil) eq_refl Hσ _) (GS_br EP EM 52 (k1 :: nil) eq_refl (GSubRel_refl_r EP EM Hσ) _)
            _ _ _ _ _ _ _).
  - gs_solve.
  - gs_solve.
  - sr_ctx; exact X1.
  - sr_ctx; exact X1r.
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_codesq_inst; inst_side 52.
  - apply redt_codesq_inst; inst_side 52.
Qed.

Lemma Rt_sq {Δ k A a} : lwf (gL G') k ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ⊢[ lC ] a : A @ k ] ->
  RT Δ A k -> Rt Δ a A k -> Rt Δ (tmSq k A a) (tySq k A) k.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros Hw HA Ha IHA IHa Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1, H into Ek end.
  match goal with H : ty_leq A ?x |- _ => rename x into A', H into EA end.
  match goal with H : tm_leq a ?x |- _ => rename x into a', H into Ea end.
  match goal with H : lwf L' k1 |- _ => rename H into Hw1 end.
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q).
  destruct (RTcall HΔL HΔ Hw Hw1 Ek HA EA ltac:(assumption) IHA) as (HA' & HAA & HA'R & HA'R1 & CA & CA1 & X1 & X1r).
  destruct (Rtcall HΔL HΔ Hw Hw1 Ek HAA Ha Ea ltac:(assumption) IHa) as (Ha' & Haa & Ha'R0 & Ha'R1 & X2 & X2r).
  pose proof (lift_ty HA HCD) as HAD.
  assert (HSS : [ G' ; Δ ⊢[ lD ] tySq k A ≅ tySq k1 A' @ k ])
    by (apply eqty_sq; [discriminate | exact Qg | exact HAD | exact HAA]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmSq k1 A' a' : tySq k1 A' @ k1 ])
    by (apply wf_sq; [discriminate | rewrite EL; exact Hw1 | exact HA'R1 | exact Ha'R1]).
  assert (HcRL : [ G' ; Δ ⊢[ lC ] tmSq k1 A' a' : tySq k A @ k ])
    by (eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qg]
                        | exact HSS]).
  assert (Ha'Rk : [ G' ; ΔR ⊢[ lC ] a' : A' @ k ]) by (eapply wf_lconv; [exact Ha'R1 | exact Qg]).
  refine (rec_t_br 53 (k :: nil) (k1 :: nil) (GCtx Δ :: GTy A :: GTm a :: nil) (GCtx ΔR :: GTy A' :: GTm a' :: nil)
            (recTL k Δ A :: rectL k Δ A a :: nil) (recTR k1 ΔR A' :: rectR k1 ΔR A' a' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ Ek (Forall2_nil _)))
            HΔL HΔ HkL HkR Q HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl HSS) Hc HcRL HcR0
            ltac:(cbn; repeat split; assumption)
            (GS_br EP EM 53 (k :: nil) eq_refl Hσ _) (GS_br EP EM 53 (k1 :: nil) eq_refl (GSubRel_refl_r EP EM Hσ) _)
            _ _ _ _ _ _ _).
  - gs_solve.
  - gs_solve.
  - sr_ctx; [exact X1 | exact X2].
  - sr_ctx; [exact X1r | exact X2r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_sq_inst; inst_side 53.
  - apply redt_sq_inst; inst_side 53.
Qed.

(** [elim_Sq]'s step type, a squash of the motive at the squashed payload:
    its shifted carrier is computed before the global substitution reaches
    it, and its instance is put in the rule's [⟨rlift ↑⟩] form. *)
Ltac sq_step := unfold gv; W_cbn; inst_cbn; W_cbn; rewrite <- ?SubstCommute.liftshift_single_ty.
Ltac gs_solve_sq :=
  gs_dnf; cbn [rev List.app map brDecls GSall gdecl_usubst gdecl_gsubst uext lvsubst Nat.ltb Nat.leb length nth Nat.sub GSone];
  repeat split;
  first [ gs_leaf
        | unfold gv; W_cbn; gs_norm; W_cbn; rewrite <- ?SubstCommute.liftshift_single_ty;
          first [ assumption
                | solve [apply eqtm_refl; eapply lift_tm; [eassumption | unfold lle; cbn; lia]] ] ].

Lemma Rt_elimSq {Δ k k' A M c t} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ,, tySq k A @ k ⊢[ lC ] M @ k' ] ->
  [ G' ; Δ ,, A @ k ⊢[ lC ] c : tySq k' M⟨rlift ↑⟩[lsingle (tmSq k A⟨↑⟩ (var 0))] @ k' ] ->
  [ G' ; Δ ⊢[ lC ] t : tySq k A @ k ] ->
  RT Δ A k -> RT (Δ ,, tySq k A @ k) M k' ->
  Rt (Δ ,, A @ k) c (tySq k' M⟨rlift ↑⟩[lsingle (tmSq k A⟨↑⟩ (var 0))]) k' ->
  Rt Δ t (tySq k A) k ->
  Rt Δ (tmElimSq k k' A M c t) (tySq k' M[lsingle t]) k'.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros Hw Hw' HA HM Hc Ht IHA IHM IHc IHt Hc0 ΔR kL kR TL TR c0' HΔ HkL HkR HTL HTR E W.
  rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc0) as HΔL. pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1, H into Ek end.
  match goal with H : leqv k' ?x |- _ => rename x into k1', H into Ek' end.
  match goal with H : ty_leq A ?x |- _ => rename x into A', H into EA end.
  match goal with H : ty_leq M ?x |- _ => rename x into M', H into EM1 end.
  match goal with H : tm_leq c ?x |- _ => rename x into c', H into Ec end.
  match goal with H : tm_leq t ?x |- _ => rename x into t', H into Et end.
  match goal with H : lwf L' k1 |- _ => rename H into Hw1 end.
  match goal with H : lwf L' k1' |- _ => rename H into Hw1' end.
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q). assert (Qg' : lequiv (gL G') k' k1') by (rewrite EL; exact Q').
  assert (Qk : lequiv (gL G') k k) by (rewrite EL; exact (lequiv_refl _ _ Hw)).
  (* the carrier and its call *)
  destruct (RTcall HΔL HΔ Hw Hw1 Ek HA EA ltac:(assumption) IHA) as (HA' & HAA & HA'R & HA'R1 & CA & CA1 & X1 & X1r).
  pose proof (lift_ty HA HCD) as HAD. pose proof (lift_ty HA' HCD) as HA'D.
  (* the squash, and the motive over it *)
  assert (HSD : [ G' ; Δ ⊢[ lD ] tySq k A @ k ]) by (apply wft_sq; [discriminate | rewrite EL; exact Hw | exact HAD]).
  assert (HSS : [ G' ; Δ ⊢[ lD ] tySq k A ≅ tySq k1 A' @ k ])
    by (apply eqty_sq; [discriminate | exact Qg | exact HAD | exact HAA]).
  assert (HSS0 : [ G' ; Δ ⊢[ lD ] tySq k A ≅ tySq k A' @ k ])
    by (apply eqty_sq; [discriminate | exact Qk | exact HAD | exact HAA]).
  pose proof (ceq_ext HΔ HSD HSS0 (lequiv_refl _ _ Hw)) as CW. pose proof (ceq_ext HΔ HSD HSS Q) as CW1.
  destruct (RTcall (eqctx_wf_l (i := lD) eq_refl CW) CW1 Hw' Hw1' Ek' HM EM1 ltac:(assumption) IHM)
    as (HM' & HMM & _ & HM'R1 & _ & _ & X2 & X2r).
  pose proof (ctxconv_ty CW (i := lC) eq_refl HM') as HM'R.
  pose proof (lift_ty HM HCD) as HMD. pose proof (lift_ty HM' HCD) as HM'D.
  (* the step's type, at the right levels *)
  destruct (sq_facts_D (l3 := k1) (l4 := k1') Qg Qg' HAD HAA HA'D HMD HMM HM'D) as (_ & CAk & EB).
  pose proof (eqty_sym _ _ _ _ _ _ (ctxconv_eqty (eqctx_sym_D CAk) (i := lD) eq_refl EB)) as ES1.
  (* the step and the scrutinee, and their calls *)
  destruct (Rtcall (eqctx_wf_l (i := lD) eq_refl CA1) CA1 Hw' Hw1' Ek' ES1 Hc Ec ltac:(assumption) IHc)
    as (Hc' & Hcc & _ & Hc'R1 & X3 & X3r).
  destruct (Rtcall HΔL HΔ Hw Hw1 Ek HSS Ht Et ltac:(assumption) IHt) as (Ht' & Htt & Ht'R0 & Ht'R1 & X4 & X4r).
  (* the right step and scrutinee at the left levels, as [GS_br] takes them *)
  assert (Qk' : lequiv (gL G') k' k') by (rewrite EL; exact (lequiv_refl _ _ Hw')).
  destruct (sq_facts_D (l3 := k) (l4 := k') Qk Qk' HAD HAA HA'D HMD HMM HM'D) as (_ & CAk0 & EB0).
  pose proof (eqty_sym _ _ _ _ _ _ (ctxconv_eqty (eqctx_sym_D CAk0) (i := lD) eq_refl EB0)) as ES0.
  assert (Hc'R : [ G' ; ΔR ,, A' @ k ⊢[ lC ] c' : tySq k' M'⟨rlift ↑⟩[lsingle (tmSq k A'⟨↑⟩ (var 0))] @ k' ]).
  { eapply wf_conv; [exact (ctxconv_tm CA (i := lC) eq_refl Hc') |].
    exact (ctxconv_eqty CA (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ ES0)). }
  assert (Ht'R : [ G' ; ΔR ⊢[ lC ] t' : tySq k A' @ k ])
    by (eapply wf_conv; [exact Ht'R0 | exact (ctxconv_eqty HΔ (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ HSS0))]).
  (* the codes *)
  assert (Hr0 : [ G' ; Δ ⊢[ lD ] M[lsingle t] ≅ M'[lsingle t'] @ k' ])
    by exact (eqty_subst_single_D HMM HM'D Htt (lift_tm Ht HCD) (lift_tm Ht' HCD)).
  assert (Hr1 : [ G' ; Δ ⊢[ lD ] tySq k' M[lsingle t] ≅ tySq k1' M'[lsingle t'] @ k' ])
    by (apply eqty_sq; [discriminate | exact Qg' | exact (eqty_wf_l (i := lD) eq_refl Hr0) | exact Hr0]).
  pose proof (sc_elimSq_q (G := G') (i := lC) HCD ltac:(discriminate) Qg Qg'
                HA HA' (static_code_ty HCD HA HA' EA) HM HM' (static_code_ty HCD HM HM' EM1) Hc' Ht Ht'
                (static_code_tm HCD Ht Ht' Et)) as HcRL.
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmElimSq k1 k1' A' M' c' t' : tySq k1' M'[lsingle t'] @ k1' ]).
  { refine (ctxconv_tm HΔ (i := lC) eq_refl _).
    eapply wf_lconv; [eapply wf_conv; [exact HcRL | apply eqty_sym, Hr1] | apply lequiv_sym, Qg']. }
  refine (rec_t_br 54 (k :: k' :: nil) (k1 :: k1' :: nil)
            (GCtx Δ :: GTy A :: GTy M :: GTm c :: GTm t :: nil)
            (GCtx ΔR :: GTy A' :: GTy M' :: GTm c' :: GTm t' :: nil)
            (recTL k Δ A :: recTL k' (Δ ,, tySq k A @ k) M
             :: rectL k' (Δ ,, A @ k) (tySq k' M⟨rlift ↑⟩[lsingle (tmSq k A⟨↑⟩ (var 0))]) c
             :: rectL k Δ (tySq k A) t :: nil)
            (recTR k1 ΔR A' :: recTR k1' (ΔR ,, tySq k1 A' @ k1) M'
             :: rectR k1' (ΔR ,, A' @ k1) (tySq k1' M'⟨rlift ↑⟩[lsingle (tmSq k1 A'⟨↑⟩ (var 0))]) c'
             :: rectR k1 ΔR (tySq k1 A') t' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ Ek (Forall2_cons _ _ Ek' (Forall2_nil _))))
            HΔL HΔ HkL HkR Q' HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl Hr1) Hc0 HcRL HcR0
            ltac:(cbn; repeat split; assumption)
            (GS_br EP EM 54 (k :: k' :: nil) eq_refl Hσ _)
            (GS_br EP EM 54 (k1 :: k1' :: nil) eq_refl (GSubRel_refl_r EP EM Hσ) _) _ _ _ _ _ _ _).
  - gs_solve_sq.
  - gs_solve_sq.
  - sr_ctx; [exact X1 | exact X2 | sq_step; exact X3 | exact X4].
  - sr_ctx; [exact X1r | exact X2r | sq_step; exact X3r | exact X4r].
  - J_res.
  - J_res.
  - J_res.
  - apply redt_elimSq_inst; inst_side 54.
  - apply redt_elimSq_inst; inst_side 54.
Qed.

End Rec.
