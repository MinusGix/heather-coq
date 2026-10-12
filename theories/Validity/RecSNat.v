(** * The recursion lemmas on code: natural numbers, universes, the unit type, Π and W codes, application and [natrec]

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

Lemma rec_t_nat {ΔL ΔR kL kR TL TR} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lsuc lzero) kL -> lequiv L' (lsuc lzero) kR ->
  [ G' ; ΔL ⊢[ lD ] tyU lzero ≅ TL @ lsuc lzero ] -> [ G' ; ΔL ⊢[ lD ] tyU lzero ≅ TR @ lsuc lzero ] ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt tmNat)) (mott (wrapMt MtR) kR ΔR TR (boxt tmNat))
    (rectL kL ΔL TL tmNat) (rectR kR ΔR TR tmNat).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR HTL HTR.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hc : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lC ] tmNat : tyU lzero @ lsuc lzero ])
    by (intros; apply wf_code_nat; [discriminate | assumption]).
  assert (HU0 : [ G' ; ΔR ⊢[ lD ] tyU lzero @ lsuc lzero ]) by (apply wft_U; [discriminate | assumption | exact I]).
  refine (rec_t_br 5 nil nil (GCtx ΔL :: nil) (GCtx ΔR :: nil) nil nil
            ltac:(cbv; lia) eq_refl eq_refl eq_refl (Forall_nil _) (Forall_nil _) (fun i => leqv_refl _)
            HΔL HΔ HkL HkR (lequiv_refl L' (lsuc lzero) I) HTL HTR (eqty_refl _ _ _ _ _ HU0)
            (Hc _ HΔL) (Hc _ HΔL) (Hc _ HΔR) I
            (GS_ctx0 EP EM 5 nil eq_refl eq_refl Hσ HΔL HΔ)
            (GS_ctx0 EP EM 5 nil eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR)) _ _ _ _ _ _ _).
  1-2: sr_ctx.
  1-3: res_eq.
  - apply redt_nat_inst; inst_side 5.
  - apply redt_nat_inst; inst_side 5.
Qed.


Lemma rec_t_zero {ΔL ΔR kL kR TL TR} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lzero) kL -> lequiv L' (lzero) kR ->
  [ G' ; ΔL ⊢[ lD ] tyNat ≅ TL @ lzero ] -> [ G' ; ΔL ⊢[ lD ] tyNat ≅ TR @ lzero ] ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt zero)) (mott (wrapMt MtR) kR ΔR TR (boxt zero))
    (rectL kL ΔL TL zero) (rectR kR ΔR TR zero).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR HTL HTR.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hc : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lC ] zero : tyNat @ lzero ])
    by (intros; apply wf_zero; [discriminate | assumption]).
  assert (HN0 : [ G' ; ΔR ⊢[ lD ] tyNat @ lzero ]) by (apply wft_nat; [discriminate | assumption]).
  refine (rec_t_br 8 nil nil (GCtx ΔL :: nil) (GCtx ΔR :: nil) nil nil
            ltac:(cbv; lia) eq_refl eq_refl eq_refl (Forall_nil _) (Forall_nil _) (fun i => leqv_refl _)
            HΔL HΔ HkL HkR (lequiv_refl L' lzero I) HTL HTR (eqty_refl _ _ _ _ _ HN0)
            (Hc _ HΔL) (Hc _ HΔL) (Hc _ HΔR) I
            (GS_ctx0 EP EM 8 nil eq_refl eq_refl Hσ HΔL HΔ)
            (GS_ctx0 EP EM 8 nil eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR)) _ _ _ _ _ _ _).
  1-2: sr_ctx.
  1-3: res_eq.
  - apply redt_zero_inst; inst_side 8.
  - apply redt_zero_inst; inst_side 8.
Qed.


Lemma rec_t_U {ΔL ΔR kL kR TL TR j j'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lsuc (lsuc j)) kL -> lequiv L' (lsuc (lsuc j)) kR -> lwf L' j -> lwf L' j' -> leqv j j' ->
  [ G' ; ΔL ⊢[ lD ] tyU (lsuc j) ≅ TL @ lsuc (lsuc j) ] -> [ G' ; ΔL ⊢[ lD ] tyU (lsuc j) ≅ TR @ lsuc (lsuc j) ] ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmU j))) (mott (wrapMt MtR) kR ΔR TR (boxt (tmU j')))
    (rectL kL ΔL TL (tmU j)) (rectR kR ΔR TR (tmU j')).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hj Hj' E HTL HTR.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Q : lequiv L' j j') by exact (leqv_lequiv _ _ _ Hj Hj' E).
  assert (Q2 : lequiv L' (lsuc (lsuc j)) (lsuc (lsuc j'))) by (do 2 apply lequiv_suc; exact Q).
  assert (HUU : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lD ] tyU (lsuc j) ≅ tyU (lsuc j') @ lsuc (lsuc j) ])
    by (intros; apply eqty_U; [discriminate | assumption | rewrite EL; apply lequiv_suc, Q]).
  assert (Hc : forall Δ i, [ G' ; Δ ⊢[ lD ] ] -> lwf L' i -> [ G' ; Δ ⊢[ lC ] tmU i : tyU (lsuc i) @ lsuc (lsuc i) ])
    by (intros; apply wf_code_U; [discriminate | assumption | rewrite EL; assumption]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tmU j' : tyU (lsuc j) @ lsuc (lsuc j) ]).
  { eapply wf_lconv; [| rewrite EL; exact Q2].
    eapply wf_conv; [exact (Hc _ _ HΔL Hj') |].
    eapply eqty_lconv; [exact (HUU _ HΔL) | rewrite EL; apply lequiv_sym, Q2]. }
  refine (rec_t_br 7 (j :: nil) (j' :: nil) (GCtx ΔL :: nil) (GCtx ΔR :: nil) nil nil
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR Q2 HTL HTR (HUU _ HΔR)
            (Hc _ _ HΔL Hj) HcRL (Hc _ _ HΔR Hj') E
            (GS_ctx0 EP EM 7 (j :: nil) eq_refl eq_refl Hσ HΔL HΔ)
            (GS_ctx0 EP EM 7 (j' :: nil) eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR))
            _ _ _ _ _ _ _).
  1-2: sr_ctx.
  1-3: res_eq.
  - apply redt_U_inst; inst_side 7.
  - apply redt_U_inst; inst_side 7.
Qed.

(** The unit code and the unit element: branches without calls, like [U]. *)
Lemma rec_t_codeunit {ΔL ΔR kL kR TL TR j j'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lsuc j) kL -> lequiv L' (lsuc j) kR -> lwf L' j -> lwf L' j' -> leqv j j' ->
  [ G' ; ΔL ⊢[ lD ] tyU j ≅ TL @ lsuc j ] -> [ G' ; ΔL ⊢[ lD ] tyU j ≅ TR @ lsuc j ] ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmUnit j))) (mott (wrapMt MtR) kR ΔR TR (boxt (tmUnit j')))
    (rectL kL ΔL TL (tmUnit j)) (rectR kR ΔR TR (tmUnit j')).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hj Hj' E HTL HTR.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Q : lequiv L' j j') by exact (leqv_lequiv _ _ _ Hj Hj' E).
  assert (Q1 : lequiv L' (lsuc j) (lsuc j')) by (apply lequiv_suc; exact Q).
  assert (HUU : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lD ] tyU j ≅ tyU j' @ lsuc j ])
    by (intros; apply eqty_U; [discriminate | assumption | rewrite EL; exact Q]).
  assert (Hc : forall Δ i, [ G' ; Δ ⊢[ lD ] ] -> lwf L' i -> [ G' ; Δ ⊢[ lC ] tmUnit i : tyU i @ lsuc i ])
    by (intros; apply wf_code_unit; [discriminate | assumption | rewrite EL; assumption]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tmUnit j' : tyU j @ lsuc j ]).
  { eapply wf_lconv; [| rewrite EL; exact Q1].
    eapply wf_conv; [exact (Hc _ _ HΔL Hj') |].
    eapply eqty_lconv; [exact (HUU _ HΔL) | rewrite EL; apply lequiv_sym, Q1]. }
  refine (rec_t_br 19 (j :: nil) (j' :: nil) (GCtx ΔL :: nil) (GCtx ΔR :: nil) nil nil
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR Q1 HTL HTR (HUU _ HΔR)
            (Hc _ _ HΔL Hj) HcRL (Hc _ _ HΔR Hj') E
            (GS_ctx0 EP EM 19 (j :: nil) eq_refl eq_refl Hσ HΔL HΔ)
            (GS_ctx0 EP EM 19 (j' :: nil) eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR))
            _ _ _ _ _ _ _).
  1-2: sr_ctx.
  1-3: res_eq.
  - apply redt_codeunit_inst; inst_side 19.
  - apply redt_codeunit_inst; inst_side 19.
Qed.

Lemma rec_t_triv {ΔL ΔR kL kR TL TR j j'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' j kL -> lequiv L' j kR -> lwf L' j -> lwf L' j' -> leqv j j' ->
  [ G' ; ΔL ⊢[ lD ] tyUnit j ≅ TL @ j ] -> [ G' ; ΔL ⊢[ lD ] tyUnit j ≅ TR @ j ] ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmTriv j))) (mott (wrapMt MtR) kR ΔR TR (boxt (tmTriv j')))
    (rectL kL ΔL TL (tmTriv j)) (rectR kR ΔR TR (tmTriv j')).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hj Hj' E HTL HTR.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Q : lequiv L' j j') by exact (leqv_lequiv _ _ _ Hj Hj' E).
  assert (HUU : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lD ] tyUnit j ≅ tyUnit j' @ j ])
    by (intros; apply eqty_unit; [discriminate | assumption | rewrite EL; exact Q]).
  assert (Hc : forall Δ i, [ G' ; Δ ⊢[ lD ] ] -> lwf L' i -> [ G' ; Δ ⊢[ lC ] tmTriv i : tyUnit i @ i ])
    by (intros; apply wf_triv; [discriminate | assumption | rewrite EL; assumption]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tmTriv j' : tyUnit j @ j ]).
  { eapply wf_lconv; [| rewrite EL; exact Q].
    eapply wf_conv; [exact (Hc _ _ HΔL Hj') |].
    eapply eqty_lconv; [exact (HUU _ HΔL) | rewrite EL; apply lequiv_sym, Q]. }
  refine (rec_t_br 20 (j :: nil) (j' :: nil) (GCtx ΔL :: nil) (GCtx ΔR :: nil) nil nil
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR Q HTL HTR (HUU _ HΔR)
            (Hc _ _ HΔL Hj) HcRL (Hc _ _ HΔR Hj') E
            (GS_ctx0 EP EM 20 (j :: nil) eq_refl eq_refl Hσ HΔL HΔ)
            (GS_ctx0 EP EM 20 (j' :: nil) eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR))
            _ _ _ _ _ _ _).
  1-2: sr_ctx.
  1-3: res_eq.
  - apply redt_triv_inst; inst_side 20.
  - apply redt_triv_inst; inst_side 20.
Qed.


Lemma rec_t_succ {ΔL ΔR kL kR TL TR t t'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' lzero kL -> lequiv L' lzero kR ->
  [ G' ; ΔL ⊢[ lD ] tyNat ≅ TL @ lzero ] -> [ G' ; ΔL ⊢[ lD ] tyNat ≅ TR @ lzero ] ->
  [ G' ; ΔL ⊢[ lC ] t : tyNat @ lzero ] -> [ G' ; ΔL ⊢[ lC ] t' : tyNat @ lzero ] -> tm_leq t t' ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) lzero ΔL tyNat (boxt t)) (mott (wrapMt MtR) lzero ΔR tyNat (boxt t'))
    (rectL lzero ΔL tyNat t) (rectR lzero ΔR tyNat t') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (succ t))) (mott (wrapMt MtR) kR ΔR TR (boxt (succ t')))
    (rectL kL ΔL TL (succ t)) (rectR kR ΔR TR (succ t')).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR HTL HTR Ht Ht' Et IHt.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  assert (HN0 : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lD ] tyNat @ lzero ])
    by (intros; apply wft_nat; [discriminate | assumption]).
  (* the code and its call *)
  destruct (tcall (k := lzero) HΔL HΔ I (lequiv_refl L' lzero I) (eqty_refl _ _ _ _ _ (HN0 _ HΔL)) Ht Ht' Et IHt)
    as (Htt & Ht'R & _ & _ & X1).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHt) IHt) Hl2g') as X1r.
  assert (HcS : forall Δ u, [ G' ; Δ ⊢[ lC ] u : tyNat @ lzero ] -> [ G' ; Δ ⊢[ lC ] succ u : tyNat @ lzero ])
    by (intros; apply wf_succ; [discriminate | assumption]).
  refine (rec_t_br 9 nil nil (GCtx ΔL :: GTm t :: nil) (GCtx ΔR :: GTm t' :: nil)
            (rectL lzero ΔL tyNat t :: nil) (rectR lzero ΔR tyNat t' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl (Forall_nil _) (Forall_nil _) (fun i => leqv_refl _)
            HΔL HΔ HkL HkR (lequiv_refl L' lzero I) HTL HTR (eqty_refl _ _ _ _ _ (HN0 _ HΔR))
            (HcS _ _ Ht) (HcS _ _ Ht') (HcS _ _ Ht'R) Et
            (GS_succ EP EM Hσ HΔL HΔ Ht Ht'R Htt Et)
            (GS_succ EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) Ht'R Ht'R
               (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ht'R Hl1c)) (tm_leq_refl _)) _ _ _ _ _ _ _).
  - sr_ctx. exact X1.
  - sr_ctx. exact X1r.
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_succ_inst; inst_side 9.
  - apply redt_succ_inst; inst_side 9.
Qed.

(** A binder code ([Π], branch 6; [Σ], branch 15): its former [F], typing
    rule and reduct instance. *)
Ltac rec_t_bind kb F wfF inst ΔL ΔR k k' k1 k1' s0 t0 s1 t1 :=
  intros HΔL HΔ HkL HkR Hw Hw' Hw1 Hw1' E E' HTL HTR Hs Hs' Es Ht Ht' Et IHs IHt;
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR;
  assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia);
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E);
  assert (Q' : lequiv L' k' k1') by exact (leqv_lequiv _ _ _ Hw' Hw1' E');
  assert (Qm : lequiv L' (lmax k k') (lmax k1 k1')) by (apply lequiv_max; assumption);
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2));
  assert (HUU : forall Δ j j', [ G' ; Δ ⊢[ lD ] ] -> lequiv L' j j' -> [ G' ; Δ ⊢[ lD ] tyU j ≅ tyU j' @ lsuc j ])
    by (intros; apply eqty_U; [discriminate | assumption | rewrite EL; assumption]);
  (* the domain code and its call *)
  destruct (tcall (k := lsuc k) HΔL HΔ Hw (lequiv_suc _ _ _ Q) (HUU _ _ _ HΔL Q) Hs Hs' Es IHs) as (Hss & _ & Hs'R1 & _ & X1);
  pose proof (ctxconv_tm HΔ (i := lC) eq_refl Hs') as Hs'R;
  (* the codomain code under the domain's decoding, and its call *)
  assert (HElL : [ G' ; ΔL ⊢[ lD ] tyEl k s0 @ k ])
    by (apply wft_El; [discriminate | rewrite EL; exact Hw | exact (lift_tm (j := lD) Hs Hl1c)]);
  assert (CE : [ G' ⊢[ lD ] ΔL ,, tyEl k s0 @ k ≅ ΔR ,, tyEl k s1 @ k ])
    by (apply eqc_ext; [exact HΔ | exact HElL | apply eqty_El; [discriminate | rewrite EL; apply lequiv_refl, Hw | exact Hss]
                       | rewrite EL; apply lequiv_refl, Hw]);
  assert (CE1 : [ G' ⊢[ lD ] ΔL ,, tyEl k s0 @ k ≅ ΔR ,, tyEl k1 s1 @ k1 ])
    by (apply eqc_ext; [exact HΔ | exact HElL | apply eqty_El; [discriminate | rewrite EL; exact Q | exact Hss]
                       | rewrite EL; exact Q]);
  pose proof (eqctx_wf_l (i := lD) eq_refl CE) as HΔLE;
  destruct (tcall (k := lsuc k') HΔLE CE1 Hw' (lequiv_suc _ _ _ Q') (HUU _ _ _ HΔLE Q') Ht Ht' Et IHt) as (Htt & _ & Ht'R1 & _ & X2);
  pose proof (ctxconv_tm CE (i := lC) eq_refl Ht') as Ht'R;
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHs) IHs) Hl2g') as X1r;
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHt) IHt) Hl2g') as X2r;
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] F k k' s0 t0 : tyU (lmax k k') @ lsuc (lmax k k') ])
    by (apply wfF; [discriminate | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact Hs | exact Ht]);
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] F k1 k1' s1 t1 : tyU (lmax k1 k1') @ lsuc (lmax k1 k1') ])
    by (apply wfF; [discriminate | rewrite EL; exact Hw1 | rewrite EL; exact Hw1' | exact Hs'R1 | exact Ht'R1]);
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] F k1 k1' s1 t1 : tyU (lmax k k') @ lsuc (lmax k k') ])
    by (eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0)
                                          | rewrite EL; apply lequiv_suc, Qm] | exact (HUU _ _ _ HΔL Qm)]);
  refine (rec_t_br kb (k :: k' :: nil) (k1 :: k1' :: nil) (GCtx ΔL :: GTm s0 :: GTm t0 :: nil)
            (GCtx ΔR :: GTm s1 :: GTm t1 :: nil)
            (rectL (lsuc k) ΔL (tyU k) s0 :: rectL (lsuc k') (ΔL ,, tyEl k s0 @ k) (tyU k') t0 :: nil)
            (rectR (lsuc k1) ΔR (tyU k1) s1 :: rectR (lsuc k1') (ΔR ,, tyEl k1 s1 @ k1) (tyU k1') t1 :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl
            ltac:(repeat constructor; assumption) ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_cons _ _ E' (Forall2_nil _))))
            HΔL HΔ HkL HkR (lequiv_suc _ _ _ Qm) HTL HTR (HUU _ _ _ HΔR Qm) HcL0 HcRL HcR0
            ltac:(cbn; repeat split; assumption)
            (GS_pi' EP EM kb eq_refl eq_refl Hσ HΔL HΔ Hs Hs'R Hss Es Ht Ht'R Htt Et)
            (GS_pi' EP EM kb eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) Hs'R1 Hs'R1
               (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hs'R1 Hl1c)) (tm_leq_refl _) Ht'R1 Ht'R1
               (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ht'R1 Hl1c)) (tm_leq_refl _)) _ _ _ _ _ _ _);
  [ sr_ctx; [exact X1 | exact X2] | sr_ctx; [exact X1r | exact X2r] | res_eq | res_eq | res_eq
  | apply inst; inst_side kb | apply inst; inst_side kb ].

Lemma rec_t_pi {ΔL ΔR kL kR TL TR k k' k1 k1' s0 t0 s1 t1} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lsuc (lmax k k')) kL -> lequiv L' (lsuc (lmax k k')) kR ->
  lwf L' k -> lwf L' k' -> lwf L' k1 -> lwf L' k1' -> leqv k k1 -> leqv k' k1' ->
  [ G' ; ΔL ⊢[ lD ] tyU (lmax k k') ≅ TL @ lsuc (lmax k k') ] ->
  [ G' ; ΔL ⊢[ lD ] tyU (lmax k k') ≅ TR @ lsuc (lmax k k') ] ->
  [ G' ; ΔL ⊢[ lC ] s0 : tyU k @ lsuc k ] -> [ G' ; ΔL ⊢[ lC ] s1 : tyU k @ lsuc k ] -> tm_leq s0 s1 ->
  [ G' ; ΔL ,, tyEl k s0 @ k ⊢[ lC ] t0 : tyU k' @ lsuc k' ] ->
  [ G' ; ΔL ,, tyEl k s0 @ k ⊢[ lC ] t1 : tyU k' @ lsuc k' ] -> tm_leq t0 t1 ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lsuc k) ΔL (tyU k) (boxt s0))
    (mott (wrapMt MtR) (lsuc k1) ΔR (tyU k1) (boxt s1))
    (rectL (lsuc k) ΔL (tyU k) s0) (rectR (lsuc k1) ΔR (tyU k1) s1) ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lsuc k') (ΔL ,, tyEl k s0 @ k) (tyU k') (boxt t0))
    (mott (wrapMt MtR) (lsuc k1') (ΔR ,, tyEl k1 s1 @ k1) (tyU k1') (boxt t1))
    (rectL (lsuc k') (ΔL ,, tyEl k s0 @ k) (tyU k') t0) (rectR (lsuc k1') (ΔR ,, tyEl k1 s1 @ k1) (tyU k1') t1) ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmPi k k' s0 t0)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmPi k1 k1' s1 t1)))
    (rectL kL ΔL TL (tmPi k k' s0 t0)) (rectR kR ΔR TR (tmPi k1 k1' s1 t1)).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  rec_t_bind 6 tmPi wf_code_pi redt_pi_inst ΔL ΔR k k' k1 k1' s0 t0 s1 t1.
Qed.

Lemma rec_t_codesig {ΔL ΔR kL kR TL TR k k' k1 k1' s0 t0 s1 t1} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lsuc (lmax k k')) kL -> lequiv L' (lsuc (lmax k k')) kR ->
  lwf L' k -> lwf L' k' -> lwf L' k1 -> lwf L' k1' -> leqv k k1 -> leqv k' k1' ->
  [ G' ; ΔL ⊢[ lD ] tyU (lmax k k') ≅ TL @ lsuc (lmax k k') ] ->
  [ G' ; ΔL ⊢[ lD ] tyU (lmax k k') ≅ TR @ lsuc (lmax k k') ] ->
  [ G' ; ΔL ⊢[ lC ] s0 : tyU k @ lsuc k ] -> [ G' ; ΔL ⊢[ lC ] s1 : tyU k @ lsuc k ] -> tm_leq s0 s1 ->
  [ G' ; ΔL ,, tyEl k s0 @ k ⊢[ lC ] t0 : tyU k' @ lsuc k' ] ->
  [ G' ; ΔL ,, tyEl k s0 @ k ⊢[ lC ] t1 : tyU k' @ lsuc k' ] -> tm_leq t0 t1 ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lsuc k) ΔL (tyU k) (boxt s0))
    (mott (wrapMt MtR) (lsuc k1) ΔR (tyU k1) (boxt s1))
    (rectL (lsuc k) ΔL (tyU k) s0) (rectR (lsuc k1) ΔR (tyU k1) s1) ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lsuc k') (ΔL ,, tyEl k s0 @ k) (tyU k') (boxt t0))
    (mott (wrapMt MtR) (lsuc k1') (ΔR ,, tyEl k1 s1 @ k1) (tyU k1') (boxt t1))
    (rectL (lsuc k') (ΔL ,, tyEl k s0 @ k) (tyU k') t0) (rectR (lsuc k1') (ΔR ,, tyEl k1 s1 @ k1) (tyU k1') t1) ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmSig k k' s0 t0)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmSig k1 k1' s1 t1)))
    (rectL kL ΔL TL (tmSig k k' s0 t0)) (rectR kR ΔR TR (tmSig k1 k1' s1 t1)).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  rec_t_bind 15 tmSig wf_code_sig redt_codesig_inst ΔL ΔR k k' k1 k1' s0 t0 s1 t1.
Qed.

Lemma rec_t_codeW {ΔL ΔR kL kR TL TR k k' k1 k1' s0 t0 s1 t1} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lsuc (lmax k k')) kL -> lequiv L' (lsuc (lmax k k')) kR ->
  lwf L' k -> lwf L' k' -> lwf L' k1 -> lwf L' k1' -> leqv k k1 -> leqv k' k1' ->
  [ G' ; ΔL ⊢[ lD ] tyU (lmax k k') ≅ TL @ lsuc (lmax k k') ] ->
  [ G' ; ΔL ⊢[ lD ] tyU (lmax k k') ≅ TR @ lsuc (lmax k k') ] ->
  [ G' ; ΔL ⊢[ lC ] s0 : tyU k @ lsuc k ] -> [ G' ; ΔL ⊢[ lC ] s1 : tyU k @ lsuc k ] -> tm_leq s0 s1 ->
  [ G' ; ΔL ,, tyEl k s0 @ k ⊢[ lC ] t0 : tyU k' @ lsuc k' ] ->
  [ G' ; ΔL ,, tyEl k s0 @ k ⊢[ lC ] t1 : tyU k' @ lsuc k' ] -> tm_leq t0 t1 ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lsuc k) ΔL (tyU k) (boxt s0))
    (mott (wrapMt MtR) (lsuc k1) ΔR (tyU k1) (boxt s1))
    (rectL (lsuc k) ΔL (tyU k) s0) (rectR (lsuc k1) ΔR (tyU k1) s1) ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lsuc k') (ΔL ,, tyEl k s0 @ k) (tyU k') (boxt t0))
    (mott (wrapMt MtR) (lsuc k1') (ΔR ,, tyEl k1 s1 @ k1) (tyU k1') (boxt t1))
    (rectL (lsuc k') (ΔL ,, tyEl k s0 @ k) (tyU k') t0) (rectR (lsuc k1') (ΔR ,, tyEl k1 s1 @ k1) (tyU k1') t1) ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmW k k' s0 t0)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmW k1 k1' s1 t1)))
    (rectL kL ΔL TL (tmW k k' s0 t0)) (rectR kR ΔR TR (tmW k1 k1' s1 t1)).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  rec_t_bind 40 tmW wf_code_W redt_codeW_inst ΔL ΔR k k' k1 k1' s0 t0 s1 t1.
Qed.

Lemma rec_t_natrec {ΔL ΔR kL kR TL TR k k1 M M' s0 s1 z0 z1 t0 t1} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k kL -> lequiv L' k kR -> lwf L' k -> lwf L' k1 -> leqv k k1 ->
  [ G' ; ΔL ⊢[ lD ] M[lsingle t0] ≅ TL @ k ] -> [ G' ; ΔL ⊢[ lD ] M[lsingle t0] ≅ TR @ k ] ->
  [ G' ; ΔL ,, tyNat @ lzero ⊢[ lC ] M @ k ] -> [ G' ; ΔL ,, tyNat @ lzero ⊢[ lC ] M' @ k ] -> ty_leq M M' ->
  [ G' ; ΔL ⊢[ lC ] s0 : M[lsingle zero] @ k ] -> [ G' ; ΔL ⊢[ lC ] s1 : M[lsingle zero] @ k ] -> tm_leq s0 s1 ->
  [ G' ; ΔL ,, tyNat @ lzero ,, M @ k ⊢[ lC ] z0 : M[lsucc] @ k ] ->
  [ G' ; ΔL ,, tyNat @ lzero ,, M @ k ⊢[ lC ] z1 : M[lsucc] @ k ] -> tm_leq z0 z1 ->
  [ G' ; ΔL ⊢[ lC ] t0 : tyNat @ lzero ] -> [ G' ; ΔL ⊢[ lC ] t1 : tyNat @ lzero ] -> tm_leq t0 t1 ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k (ΔL ,, tyNat @ lzero) (boxT M))
    (motT (wrapMT MTR) k1 (ΔR ,, tyNat @ lzero) (boxT M'))
    (recTL k (ΔL ,, tyNat @ lzero) M) (recTR k1 (ΔR ,, tyNat @ lzero) M') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL (M[lsingle zero]) (boxt s0))
    (mott (wrapMt MtR) k1 ΔR (M'[lsingle zero]) (boxt s1))
    (rectL k ΔL (M[lsingle zero]) s0) (rectR k1 ΔR (M'[lsingle zero]) s1) ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k (ΔL ,, tyNat @ lzero ,, M @ k) (M[lsucc]) (boxt z0))
    (mott (wrapMt MtR) k1 (ΔR ,, tyNat @ lzero ,, M' @ k1) (M'[lsucc]) (boxt z1))
    (rectL k (ΔL ,, tyNat @ lzero ,, M @ k) (M[lsucc]) z0) (rectR k1 (ΔR ,, tyNat @ lzero ,, M' @ k1) (M'[lsucc]) z1) ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) lzero ΔL tyNat (boxt t0))
    (mott (wrapMt MtR) lzero ΔR tyNat (boxt t1))
    (rectL lzero ΔL tyNat t0) (rectR lzero ΔR tyNat t1) ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (natrec k M s0 z0 t0)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (natrec k1 M' s1 z1 t1)))
    (rectL kL ΔL TL (natrec k M s0 z0 t0)) (rectR kR ΔR TR (natrec k1 M' s1 z1 t1)).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw1 E HTL HTR HM HM' EMM Hs Hs' Es Hz Hz' Ez Ht Ht' Et IHM IHs IHz IHt.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q).
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1)).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  assert (HN0 : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lD ] tyNat @ lzero ])
    by (intros; apply wft_nat; [discriminate | assumption]).
  assert (CN : [ G' ⊢[ lD ] ΔL ,, tyNat @ lzero ≅ ΔR ,, tyNat @ lzero ]).
  { apply eqc_ext; [exact HΔ | exact (HN0 _ HΔL) | apply eqty_refl, HN0, HΔL | apply lequiv_refl; exact I]. }
  (* the motive and its call *)
  destruct (Tcall (eqctx_wf_l (i := lD) eq_refl CN) CN Hw Q HM HM' EMM IHM) as (HMM & HM'R & HM'R1 & CNMk & CNM & X1).
  pose proof (eqctx_wf_l (i := lD) eq_refl CNM) as HΔLNM.
  (* the motive's instances *)
  assert (HM0 : [ G' ; ΔL ⊢[ lD ] M[lsingle zero] ≅ M'[lsingle zero] @ k ])
    by exact (eqty_single (i := lD) eq_refl HMM (wf_zero _ lD _ ltac:(discriminate) HΔL)).
  assert (HMs : [ G' ; ΔL ,, tyNat @ lzero ,, M @ k ⊢[ lD ] M[lsucc] ≅ M'[lsucc] @ k ])
    by exact (eqty_subst (i := lD) eq_refl HMM (lsub_wf_lsucc (i := lD) eq_refl ltac:(discriminate) HΔLNM)).
  (* the cases and the scrutinee, and their calls *)
  destruct (tcall HΔL HΔ Hw Q HM0 Hs Hs' Es IHs) as (Hss & Hs'R & Hs'R1 & _ & X2).
  destruct (tcall HΔLNM CNM Hw Q HMs Hz Hz' Ez IHz) as (Hzz & _ & Hz'R1 & _ & X3).
  assert (Hz'R : [ G' ; ΔR ,, tyNat @ lzero ,, M' @ k ⊢[ lC ] z1 : M'[lsucc] @ k ]).
  { refine (ctxconv_tm CNMk (i := lC) eq_refl _). eapply wf_conv; [exact Hz' | apply eqty_sym, HMs]. }
  destruct (tcall (k := lzero) HΔL HΔ I (lequiv_refl L' lzero I) (eqty_refl _ _ _ _ _ (HN0 _ HΔL)) Ht Ht' Et IHt)
    as (Htt & Ht'R & _ & _ & X4).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHM) IHM) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHs) IHs) Hl2g') as X2r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHz) IHz) Hl2g') as X3r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHt) IHt) Hl2g') as X4r.
  assert (HMtt : [ G' ; ΔL ⊢[ lD ] M[lsingle t0] ≅ M'[lsingle t1] @ k ])
    by exact (eqty_subst_single_D HMM (lift_ty (j := lD) HM' Hl1c) Htt (lift_tm (j := lD) Ht Hl1c) (lift_tm (j := lD) Ht' Hl1c)).
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] natrec k M s0 z0 t0 : M[lsingle t0] @ k ])
    by (apply wf_natrec; [exact Hn | rewrite EL; exact Hw | exact HM | exact Hs | exact Hz | exact Ht]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] natrec k1 M' s1 z1 t1 : M'[lsingle t1] @ k1 ])
    by (apply wf_natrec; [exact Hn | rewrite EL; exact Hw1 | exact HM'R1 | exact Hs'R1 | exact Hz'R1 | exact Ht'R]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] natrec k1 M' s1 z1 t1 : M[lsingle t0] @ k ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qg] | exact HMtt]. }
  set (xsL := recTL k (ΔL ,, tyNat @ lzero) M :: rectL k ΔL (M[lsingle zero]) s0 ::
              rectL k (ΔL ,, tyNat @ lzero ,, M @ k) (M[lsucc]) z0 :: rectL lzero ΔL tyNat t0 :: nil).
  set (xsR := recTR k1 (ΔR ,, tyNat @ lzero) M' :: rectR k1 ΔR (M'[lsingle zero]) s1 ::
              rectR k1 (ΔR ,, tyNat @ lzero ,, M' @ k1) (M'[lsucc]) z1 :: rectR lzero ΔR tyNat t1 :: nil).
  refine (rec_t_br 10 (k :: nil) (k1 :: nil) (GCtx ΔL :: GTy M :: GTm s0 :: GTm z0 :: GTm t0 :: nil)
            (GCtx ΔR :: GTy M' :: GTm s1 :: GTm z1 :: GTm t1 :: nil) xsL xsR ltac:(cbv; lia) eq_refl eq_refl eq_refl
            ltac:(repeat constructor; assumption) ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR Q HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl HMtt) HcL0 HcRL HcR0
            ltac:(cbn; repeat split; assumption)
            (GS_natrec EP EM Hσ HΔL HΔ HM HM'R HMM EMM Hs Hs'R Hss Es Hz Hz'R Hzz Ez Ht Ht'R Htt Et)
            (GS_natrec EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HM'R1 HM'R1
               (eqty_refl _ _ _ _ _ (lift_ty (j := lD) HM'R1 Hl1c)) (ty_leq_refl _)
               Hs'R1 Hs'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hs'R1 Hl1c)) (tm_leq_refl _)
               Hz'R1 Hz'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hz'R1 Hl1c)) (tm_leq_refl _)
               Ht'R Ht'R (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ht'R Hl1c)) (tm_leq_refl _)) _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2 | exact X3 | exact X4].
  - sr_ctx; [exact X1r | exact X2r | exact X3r | exact X4r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_natrec_inst; inst_side 10.
  - apply redt_natrec_inst; inst_side 10.
Qed.

Lemma rec_t_app {ΔL ΔR kL kR TL TR k k' k1 k1' A B A' B' f f' a a'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k' kL -> lequiv L' k' kR -> lwf L' k -> lwf L' k' -> lwf L' k1 -> lwf L' k1' -> leqv k k1 -> leqv k' k1' ->
  [ G' ; ΔL ⊢[ lD ] B[lsingle a] ≅ TL @ k' ] -> [ G' ; ΔL ⊢[ lD ] B[lsingle a] ≅ TR @ k' ] ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] A' @ k ] -> ty_leq A A' ->
  [ G' ; ΔL ,, A @ k ⊢[ lC ] B @ k' ] -> [ G' ; ΔL ,, A @ k ⊢[ lC ] B' @ k' ] -> ty_leq B B' ->
  [ G' ; ΔL ⊢[ lC ] f : tyPi k k' A B @ lmax k k' ] -> [ G' ; ΔL ⊢[ lC ] f' : tyPi k k' A B @ lmax k k' ] -> tm_leq f f' ->
  [ G' ; ΔL ⊢[ lC ] a : A @ k ] -> [ G' ; ΔL ⊢[ lC ] a' : A @ k ] -> tm_leq a a' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k' (ΔL ,, A @ k) (boxT B)) (motT (wrapMT MTR) k1' (ΔR ,, A' @ k1) (boxT B'))
    (recTL k' (ΔL ,, A @ k) B) (recTR k1' (ΔR ,, A' @ k1) B') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lmax k k') ΔL (tyPi k k' A B) (boxt f))
    (mott (wrapMt MtR) (lmax k1 k1') ΔR (tyPi k1 k1' A' B') (boxt f'))
    (rectL (lmax k k') ΔL (tyPi k k' A B) f) (rectR (lmax k1 k1') ΔR (tyPi k1 k1' A' B') f') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL A (boxt a)) (mott (wrapMt MtR) k1 ΔR A' (boxt a'))
    (rectL k ΔL A a) (rectR k1 ΔR A' a') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (app f k k' A B a)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (app f' k1 k1' A' B' a')))
    (rectL kL ΔL TL (app f k k' A B a)) (rectR kR ΔR TR (app f' k1 k1' A' B' a')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw' Hw1 Hw1' E E' HTL HTR HA HA' EA HB HB' EB Hf Hf' Ef Ha Ha' Ea IHA IHB IHf IHa.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Q' : lequiv L' k' k1') by exact (leqv_lequiv _ _ _ Hw' Hw1' E').
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q). assert (Qg' : lequiv (gL G') k' k1') by (rewrite EL; exact Q').
  assert (Qm : lequiv L' (lmax k k') (lmax k1 k1')) by (apply lequiv_max; assumption).
  assert (Qmg : lequiv (gL G') (lmax k k') (lmax k1 k1')) by (rewrite EL; exact Qm).
  assert (Hwm : lwf L' (lmax k k')) by (cbn; auto).
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1)).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  (* the pieces and their calls *)
  destruct (Tcall HΔL HΔ Hw Q HA HA' EA IHA) as (HAA & HA'R & HA'R1 & CA & CA1 & X1).
  destruct (Tcall (eqctx_wf_l (i := lD) eq_refl CA) CA1 Hw' Q' HB HB' EB IHB) as (HBB & _ & HB'R1 & _ & _ & X2).
  pose proof (ctxconv_ty CA (i := lC) eq_refl HB') as HB'R.
  pose proof (lift_ty (j := lD) HA'R1 Hl1c) as HA'R1D. pose proof (lift_ty (j := lD) HB'R1 Hl1c) as HB'R1D.
  assert (HPP : [ G' ; ΔL ⊢[ lD ] tyPi k k' A B ≅ tyPi k1 k1' A' B' @ lmax k k' ])
    by (apply eqty_pi; [discriminate | exact Qg | exact Qg' | exact (lift_ty (j := lD) HA Hl1c) | exact HAA | exact HBB]).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHA) IHA) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHB) IHB) Hl1g') as X2r.
  (* the function and the argument, and their calls *)
  destruct (tcall HΔL HΔ Hwm Qm HPP Hf Hf' Ef IHf) as (Hff & Hf'R0 & Hf'R1 & _ & X3).
  assert (Hf'R : [ G' ; ΔR ⊢[ lC ] f' : tyPi k k' A' B' @ lmax k k' ]).
  { pose proof (lift_ty (j := lD) HA'R Hl1c) as HA'RD.
    eapply wf_conv; [exact Hf'R0 |].
    apply eqty_pi; [discriminate | exact Qg | exact Qg' | exact HA'RD | apply eqty_refl, HA'RD
                   | apply eqty_refl, (lift_ty (j := lD) HB'R Hl1c)]. }
  destruct (tcall HΔL HΔ Hw Q HAA Ha Ha' Ea IHa) as (Haa & Ha'R & Ha'R1 & _ & X4).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHf) IHf) Hl2g') as X3r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHa) IHa) Hl2g') as X4r.
  assert (HBa : [ G' ; ΔL ⊢[ lD ] B[lsingle a] ≅ B'[lsingle a'] @ k' ])
    by exact (eqty_subst_single_D HBB (lift_ty (j := lD) HB' Hl1c) Haa (lift_tm (j := lD) Ha Hl1c) (lift_tm (j := lD) Ha' Hl1c)).
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] app f k k' A B a : B[lsingle a] @ k' ])
    by (apply wf_app; [exact Hn | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HA | exact HB | exact Hf | exact Ha]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] app f' k1 k1' A' B' a' : B'[lsingle a'] @ k1' ])
    by (apply wf_app; [exact Hn | rewrite EL; exact Hw1 | rewrite EL; exact Hw1' | exact HA'R1 | exact HB'R1 | exact Hf'R1 | exact Ha'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] app f' k1 k1' A' B' a' : B[lsingle a] @ k' ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qg'] | exact HBa]. }
  set (xsL := recTL k ΔL A :: recTL k' (ΔL ,, A @ k) B :: rectL (lmax k k') ΔL (tyPi k k' A B) f :: rectL k ΔL A a :: nil).
  set (xsR := recTR k1 ΔR A' :: recTR k1' (ΔR ,, A' @ k1) B' :: rectR (lmax k1 k1') ΔR (tyPi k1 k1' A' B') f' :: rectR k1 ΔR A' a' :: nil).
  refine (rec_t_br 12 (k :: k' :: nil) (k1 :: k1' :: nil) (GCtx ΔL :: GTy A :: GTy B :: GTm f :: GTm a :: nil)
            (GCtx ΔR :: GTy A' :: GTy B' :: GTm f' :: GTm a' :: nil) xsL xsR ltac:(cbv; lia) eq_refl eq_refl eq_refl
            ltac:(repeat constructor; assumption) ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_cons _ _ E' (Forall2_nil _))))
            HΔL HΔ HkL HkR Q' HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl HBa) HcL0 HcRL HcR0
            ltac:(cbn; repeat split; assumption)
            (GS_app EP EM Hσ HΔL HΔ HA HA'R HAA EA HB HB'R HBB EB Hf Hf'R Hff Ef Ha Ha'R Haa Ea)
            (GS_app EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HA'R1 HA'R1
               (eqty_refl _ _ _ _ _ HA'R1D) (ty_leq_refl _) HB'R1 HB'R1 (eqty_refl _ _ _ _ _ HB'R1D) (ty_leq_refl _)
               Hf'R1 Hf'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hf'R1 Hl1c)) (tm_leq_refl _)
               Ha'R1 Ha'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ha'R1 Hl1c)) (tm_leq_refl _)) _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2 | exact X3 | exact X4].
  - sr_ctx; [exact X1r | exact X2r | exact X3r | exact X4r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_app_inst; inst_side 12.
  - apply redt_app_inst; inst_side 12.
Qed.

End Rec.
