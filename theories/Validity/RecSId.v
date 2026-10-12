(** * The recursion lemmas on code: the identity type

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

(** ** The identity type (M11b) *)

Lemma rec_T_id {ΔL ΔR kL kR k k1 A A' a a' b b'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k kL -> lequiv L' k kR -> lwf L' k -> lwf L' k1 -> leqv k k1 ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] A' @ k ] -> ty_leq A A' ->
  [ G' ; ΔL ⊢[ lC ] a : A @ k ] -> [ G' ; ΔL ⊢[ lC ] a' : A @ k ] -> tm_leq a a' ->
  [ G' ; ΔL ⊢[ lC ] b : A @ k ] -> [ G' ; ΔL ⊢[ lC ] b' : A @ k ] -> tm_leq b b' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL A (boxt a)) (mott (wrapMt MtR) k1 ΔR A' (boxt a'))
    (rectL k ΔL A a) (rectR k1 ΔR A' a') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL A (boxt b)) (mott (wrapMt MtR) k1 ΔR A' (boxt b'))
    (rectL k ΔL A b) (rectR k1 ΔR A' b') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL (boxT (tyId k A a b)))
    (motT (wrapMT MTR) kR ΔR (boxT (tyId k1 A' a' b')))
    (recTL kL ΔL (tyId k A a b)) (recTR kR ΔR (tyId k1 A' a' b')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw1 E HA HA' EA Ha Ha' Ea Hb Hb' Eb IHA IHa IHb.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q).
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1)).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  (* the pieces and their calls *)
  destruct (Tcall HΔL HΔ Hw Q HA HA' EA IHA) as (HAA & HA'R & HA'R1 & _ & _ & X1).
  destruct (tcall HΔL HΔ Hw Q HAA Ha Ha' Ea IHa) as (Haa & Ha'R & Ha'R1 & _ & X2).
  destruct (tcall HΔL HΔ Hw Q HAA Hb Hb' Eb IHb) as (Hbb & Hb'R & Hb'R1 & _ & X3).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHA) IHA) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHa) IHa) Hl2g') as X2r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHb) IHb) Hl2g') as X3r.
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] tyId k A a b @ k ])
    by (apply wft_id; [exact Hn | rewrite EL; exact Hw | exact HA | exact Ha | exact Hb]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tyId k1 A' a' b' @ k1 ])
    by (apply wft_id; [exact Hn | rewrite EL; exact Hw1 | exact HA'R1 | exact Ha'R1 | exact Hb'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tyId k1 A' a' b' @ k ])
    by (eapply wft_lconv; [exact (ctxconv_ty (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qg]).
  assert (Ec : ty_leq (tyId k A a b) (tyId k1 A' a' b')) by (cbn; repeat split; assumption).
  refine (rec_T_br 21 (k :: nil) (k1 :: nil) (GCtx ΔL :: GTy A :: GTm a :: GTm b :: nil)
            (GCtx ΔR :: GTy A' :: GTm a' :: GTm b' :: nil)
            (recTL k ΔL A :: rectL k ΔL A a :: rectL k ΔL A b :: nil)
            (recTR k1 ΔR A' :: rectR k1 ΔR A' a' :: rectR k1 ΔR A' b' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR Q HcL0 HcRL HcR0 Ec
            (GS_id EP EM 21 eq_refl eq_refl Hσ HΔL HΔ HA HA'R HAA EA Ha Ha'R Haa Ea Hb Hb'R Hbb Eb)
            (GS_id EP EM 21 eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HA'R1 HA'R1
               (eqty_refl _ _ _ _ _ (lift_ty (j := lD) HA'R1 Hl1c)) (ty_leq_refl _)
               Ha'R1 Ha'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ha'R1 Hl1c)) (tm_leq_refl _)
               Hb'R1 Hb'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hb'R1 Hl1c)) (tm_leq_refl _))
            _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2 | exact X3].
  - sr_ctx; [exact X1r | exact X2r | exact X3r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redT_id_inst; inst_side 21.
  - apply redT_id_inst; inst_side 21.
Qed.

Lemma rec_t_codeid {ΔL ΔR kL kR TL TR k k1 s s' t t' u u'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lsuc k) kL -> lequiv L' (lsuc k) kR -> lwf L' k -> lwf L' k1 -> leqv k k1 ->
  [ G' ; ΔL ⊢[ lD ] tyU k ≅ TL @ lsuc k ] -> [ G' ; ΔL ⊢[ lD ] tyU k ≅ TR @ lsuc k ] ->
  [ G' ; ΔL ⊢[ lC ] s : tyU k @ lsuc k ] -> [ G' ; ΔL ⊢[ lC ] s' : tyU k @ lsuc k ] -> tm_leq s s' ->
  [ G' ; ΔL ⊢[ lC ] t : tyEl k s @ k ] -> [ G' ; ΔL ⊢[ lC ] t' : tyEl k s @ k ] -> tm_leq t t' ->
  [ G' ; ΔL ⊢[ lC ] u : tyEl k s @ k ] -> [ G' ; ΔL ⊢[ lC ] u' : tyEl k s @ k ] -> tm_leq u u' ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lsuc k) ΔL (tyU k) (boxt s))
    (mott (wrapMt MtR) (lsuc k1) ΔR (tyU k1) (boxt s'))
    (rectL (lsuc k) ΔL (tyU k) s) (rectR (lsuc k1) ΔR (tyU k1) s') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL (tyEl k s) (boxt t)) (mott (wrapMt MtR) k1 ΔR (tyEl k1 s') (boxt t'))
    (rectL k ΔL (tyEl k s) t) (rectR k1 ΔR (tyEl k1 s') t') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL (tyEl k s) (boxt u)) (mott (wrapMt MtR) k1 ΔR (tyEl k1 s') (boxt u'))
    (rectL k ΔL (tyEl k s) u) (rectR k1 ΔR (tyEl k1 s') u') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmId k s t u)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmId k1 s' t' u')))
    (rectL kL ΔL TL (tmId k s t u)) (rectR kR ΔR TR (tmId k1 s' t' u')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw1 E HTL HTR Hs Hs' Es Ht Ht' Et Hu Hu' Eu IHs IHt IHu.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  assert (HUU : [ G' ; ΔL ⊢[ lD ] tyU k ≅ tyU k1 @ lsuc k ])
    by (apply eqty_U; [discriminate | exact HΔL | exact Qg]).
  (* the pieces and their calls *)
  destruct (tcall (k := lsuc k) HΔL HΔ Hw (lequiv_suc _ _ _ Q) HUU Hs Hs' Es IHs) as (Hss & _ & Hs'R1 & _ & X1).
  assert (HEl : [ G' ; ΔL ⊢[ lD ] tyEl k s ≅ tyEl k1 s' @ k ])
    by (apply eqty_El; [discriminate | exact Qg | exact Hss]).
  destruct (tcall HΔL HΔ Hw Q HEl Ht Ht' Et IHt) as (Htt & _ & Ht'R1 & _ & X2).
  destruct (tcall HΔL HΔ Hw Q HEl Hu Hu' Eu IHu) as (Huu & _ & Hu'R1 & _ & X3).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHs) IHs) Hl2g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHt) IHt) Hl2g') as X2r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHu) IHu) Hl2g') as X3r.
  (* the right pieces at the left level *)
  assert (HEl' : [ G' ; ΔL ⊢[ lD ] tyEl k s' ≅ tyEl k s @ k ]).
  { apply eqty_El; [discriminate | rewrite EL; exact (lequiv_refl _ _ Hw) | apply eqtm_sym; exact Hss]. }
  pose proof (ctxconv_tm HΔ (i := lC) eq_refl Hs') as Hs'R.
  assert (Ht'R : [ G' ; ΔR ⊢[ lC ] t' : tyEl k s' @ k ]).
  { eapply wf_conv; [exact (ctxconv_tm HΔ (i := lC) eq_refl Ht') | exact (ctxconv_eqty HΔ (i := lD) eq_refl HEl')]. }
  assert (Hu'R : [ G' ; ΔR ⊢[ lC ] u' : tyEl k s' @ k ]).
  { eapply wf_conv; [exact (ctxconv_tm HΔ (i := lC) eq_refl Hu') | exact (ctxconv_eqty HΔ (i := lD) eq_refl HEl')]. }
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] tmId k s t u : tyU k @ lsuc k ])
    by (apply wf_code_id; [exact Hn | rewrite EL; exact Hw | exact Hs | exact Ht | exact Hu]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmId k1 s' t' u' : tyU k1 @ lsuc k1 ])
    by (apply wf_code_id; [exact Hn | rewrite EL; exact Hw1 | exact Hs'R1 | exact Ht'R1 | exact Hu'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tmId k1 s' t' u' : tyU k @ lsuc k ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0)
                                      | exact (lequiv_suc _ _ _ Qg)] | exact HUU]. }
  assert (Ec : tm_leq (tmId k s t u) (tmId k1 s' t' u')) by (cbn; repeat split; assumption).
  refine (rec_t_br 22 (k :: nil) (k1 :: nil) (GCtx ΔL :: GTm s :: GTm t :: GTm u :: nil)
            (GCtx ΔR :: GTm s' :: GTm t' :: GTm u' :: nil)
            (rectL (lsuc k) ΔL (tyU k) s :: rectL k ΔL (tyEl k s) t :: rectL k ΔL (tyEl k s) u :: nil)
            (rectR (lsuc k1) ΔR (tyU k1) s' :: rectR k1 ΔR (tyEl k1 s') t' :: rectR k1 ΔR (tyEl k1 s') u' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR (lequiv_suc _ _ _ Q) HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl HUU) HcL0 HcRL HcR0 Ec
            (GS_codeid EP EM 22 eq_refl eq_refl Hσ HΔL HΔ Hs Hs'R Hss Es Ht Ht'R Htt Et Hu Hu'R Huu Eu)
            (GS_codeid EP EM 22 eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR)
               Hs'R1 Hs'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hs'R1 Hl1c)) (tm_leq_refl _)
               Ht'R1 Ht'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ht'R1 Hl1c)) (tm_leq_refl _)
               Hu'R1 Hu'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hu'R1 Hl1c)) (tm_leq_refl _))
            _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2 | exact X3].
  - sr_ctx; [exact X1r | exact X2r | exact X3r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_codeid_inst; inst_side 22.
  - apply redt_codeid_inst; inst_side 22.
Qed.

Lemma rec_t_refl {ΔL ΔR kL kR TL TR k k1 A A' a a'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k kL -> lequiv L' k kR -> lwf L' k -> lwf L' k1 -> leqv k k1 ->
  [ G' ; ΔL ⊢[ lD ] tyId k A a a ≅ TL @ k ] -> [ G' ; ΔL ⊢[ lD ] tyId k A a a ≅ TR @ k ] ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] A' @ k ] -> ty_leq A A' ->
  [ G' ; ΔL ⊢[ lC ] a : A @ k ] -> [ G' ; ΔL ⊢[ lC ] a' : A @ k ] -> tm_leq a a' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL A (boxt a)) (mott (wrapMt MtR) k1 ΔR A' (boxt a'))
    (rectL k ΔL A a) (rectR k1 ΔR A' a') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmRefl k A a)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmRefl k1 A' a')))
    (rectL kL ΔL TL (tmRefl k A a)) (rectR kR ΔR TR (tmRefl k1 A' a')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw1 E HTL HTR HA HA' EA Ha Ha' Ea IHA IHa.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q).
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1)).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  (* the pieces and their calls *)
  destruct (Tcall HΔL HΔ Hw Q HA HA' EA IHA) as (HAA & HA'R & HA'R1 & _ & _ & X1).
  destruct (tcall HΔL HΔ Hw Q HAA Ha Ha' Ea IHa) as (Haa & Ha'R & Ha'R1 & _ & X2).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHA) IHA) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHa) IHa) Hl2g') as X2r.
  assert (HII : [ G' ; ΔL ⊢[ lD ] tyId k A a a ≅ tyId k1 A' a' a' @ k ])
    by (apply eqty_id; [discriminate | exact Qg | exact (lift_ty (j := lD) HA Hl1c) | exact HAA | exact Haa | exact Haa]).
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] tmRefl k A a : tyId k A a a @ k ])
    by (apply wf_idrefl; [exact Hn | rewrite EL; exact Hw | exact HA | exact Ha]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmRefl k1 A' a' : tyId k1 A' a' a' @ k1 ])
    by (apply wf_idrefl; [exact Hn | rewrite EL; exact Hw1 | exact HA'R1 | exact Ha'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tmRefl k1 A' a' : tyId k A a a @ k ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qg]
                    | exact HII]. }
  assert (Ec : tm_leq (tmRefl k A a) (tmRefl k1 A' a')) by (cbn; repeat split; assumption).
  refine (rec_t_br 23 (k :: nil) (k1 :: nil) (GCtx ΔL :: GTy A :: GTm a :: nil)
            (GCtx ΔR :: GTy A' :: GTm a' :: nil)
            (recTL k ΔL A :: rectL k ΔL A a :: nil) (recTR k1 ΔR A' :: rectR k1 ΔR A' a' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR Q HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl HII) HcL0 HcRL HcR0 Ec
            (GS_refl EP EM 23 eq_refl eq_refl Hσ HΔL HΔ HA HA'R HAA EA Ha Ha'R Haa Ea)
            (GS_refl EP EM 23 eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HA'R1 HA'R1
               (eqty_refl _ _ _ _ _ (lift_ty (j := lD) HA'R1 Hl1c)) (ty_leq_refl _)
               Ha'R1 Ha'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ha'R1 Hl1c)) (tm_leq_refl _))
            _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2].
  - sr_ctx; [exact X1r | exact X2r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_refl_inst; inst_side 23.
  - apply redt_refl_inst; inst_side 23.
Qed.

End Rec.
