(** * The recursion lemmas on code: strict equality and the strict empty type, and [J]

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

(** ** Strict equality (M10c), as the identity type and the unit type *)

Lemma rec_T_seq {ΔL ΔR kL kR k k1 A A' a a' b b'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
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
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL (boxT (tySEq k A a b)))
    (motT (wrapMT MTR) kR ΔR (boxT (tySEq k1 A' a' b')))
    (recTL kL ΔL (tySEq k A a b)) (recTR kR ΔR (tySEq k1 A' a' b')).
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
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] tySEq k A a b @ k ])
    by (apply wft_seq; [exact Hn | rewrite EL; exact Hw | exact HA | exact Ha | exact Hb]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tySEq k1 A' a' b' @ k1 ])
    by (apply wft_seq; [exact Hn | rewrite EL; exact Hw1 | exact HA'R1 | exact Ha'R1 | exact Hb'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tySEq k1 A' a' b' @ k ])
    by (eapply wft_lconv; [exact (ctxconv_ty (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qg]).
  assert (Ec : ty_leq (tySEq k A a b) (tySEq k1 A' a' b')) by (cbn; repeat split; assumption).
  refine (rec_T_br 25 (k :: nil) (k1 :: nil) (GCtx ΔL :: GTy A :: GTm a :: GTm b :: nil)
            (GCtx ΔR :: GTy A' :: GTm a' :: GTm b' :: nil)
            (recTL k ΔL A :: rectL k ΔL A a :: rectL k ΔL A b :: nil)
            (recTR k1 ΔR A' :: rectR k1 ΔR A' a' :: rectR k1 ΔR A' b' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR Q HcL0 HcRL HcR0 Ec
            (GS_id EP EM 25 eq_refl eq_refl Hσ HΔL HΔ HA HA'R HAA EA Ha Ha'R Haa Ea Hb Hb'R Hbb Eb)
            (GS_id EP EM 25 eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HA'R1 HA'R1
               (eqty_refl _ _ _ _ _ (lift_ty (j := lD) HA'R1 Hl1c)) (ty_leq_refl _)
               Ha'R1 Ha'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ha'R1 Hl1c)) (tm_leq_refl _)
               Hb'R1 Hb'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hb'R1 Hl1c)) (tm_leq_refl _))
            _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2 | exact X3].
  - sr_ctx; [exact X1r | exact X2r | exact X3r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redT_seq_inst; inst_side 25.
  - apply redT_seq_inst; inst_side 25.
Qed.

Lemma rec_t_codeseq {ΔL ΔR kL kR TL TR k k1 s s' t t' u u'} :
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
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmSEq k s t u)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmSEq k1 s' t' u')))
    (rectL kL ΔL TL (tmSEq k s t u)) (rectR kR ΔR TR (tmSEq k1 s' t' u')).
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
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] tmSEq k s t u : tyU k @ lsuc k ])
    by (apply wf_code_seq; [exact Hn | rewrite EL; exact Hw | exact Hs | exact Ht | exact Hu]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmSEq k1 s' t' u' : tyU k1 @ lsuc k1 ])
    by (apply wf_code_seq; [exact Hn | rewrite EL; exact Hw1 | exact Hs'R1 | exact Ht'R1 | exact Hu'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tmSEq k1 s' t' u' : tyU k @ lsuc k ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0)
                                      | exact (lequiv_suc _ _ _ Qg)] | exact HUU]. }
  assert (Ec : tm_leq (tmSEq k s t u) (tmSEq k1 s' t' u')) by (cbn; repeat split; assumption).
  refine (rec_t_br 26 (k :: nil) (k1 :: nil) (GCtx ΔL :: GTm s :: GTm t :: GTm u :: nil)
            (GCtx ΔR :: GTm s' :: GTm t' :: GTm u' :: nil)
            (rectL (lsuc k) ΔL (tyU k) s :: rectL k ΔL (tyEl k s) t :: rectL k ΔL (tyEl k s) u :: nil)
            (rectR (lsuc k1) ΔR (tyU k1) s' :: rectR k1 ΔR (tyEl k1 s') t' :: rectR k1 ΔR (tyEl k1 s') u' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR (lequiv_suc _ _ _ Q) HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl HUU) HcL0 HcRL HcR0 Ec
            (GS_codeid EP EM 26 eq_refl eq_refl Hσ HΔL HΔ Hs Hs'R Hss Es Ht Ht'R Htt Et Hu Hu'R Huu Eu)
            (GS_codeid EP EM 26 eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR)
               Hs'R1 Hs'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hs'R1 Hl1c)) (tm_leq_refl _)
               Ht'R1 Ht'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ht'R1 Hl1c)) (tm_leq_refl _)
               Hu'R1 Hu'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hu'R1 Hl1c)) (tm_leq_refl _))
            _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2 | exact X3].
  - sr_ctx; [exact X1r | exact X2r | exact X3r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_codeseq_inst; inst_side 26.
  - apply redt_codeseq_inst; inst_side 26.
Qed.

Lemma rec_t_srefl {ΔL ΔR kL kR TL TR k k1 A A' a a'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k kL -> lequiv L' k kR -> lwf L' k -> lwf L' k1 -> leqv k k1 ->
  [ G' ; ΔL ⊢[ lD ] tySEq k A a a ≅ TL @ k ] -> [ G' ; ΔL ⊢[ lD ] tySEq k A a a ≅ TR @ k ] ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] A' @ k ] -> ty_leq A A' ->
  [ G' ; ΔL ⊢[ lC ] a : A @ k ] -> [ G' ; ΔL ⊢[ lC ] a' : A @ k ] -> tm_leq a a' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL A (boxt a)) (mott (wrapMt MtR) k1 ΔR A' (boxt a'))
    (rectL k ΔL A a) (rectR k1 ΔR A' a') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (srefl k A a)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (srefl k1 A' a')))
    (rectL kL ΔL TL (srefl k A a)) (rectR kR ΔR TR (srefl k1 A' a')).
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
  assert (HII : [ G' ; ΔL ⊢[ lD ] tySEq k A a a ≅ tySEq k1 A' a' a' @ k ])
    by (apply eqty_seq; [discriminate | exact Qg | exact (lift_ty (j := lD) HA Hl1c) | exact HAA | exact Haa | exact Haa]).
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] srefl k A a : tySEq k A a a @ k ])
    by (apply wf_srefl; [exact Hn | rewrite EL; exact Hw | exact HA | exact Ha]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] srefl k1 A' a' : tySEq k1 A' a' a' @ k1 ])
    by (apply wf_srefl; [exact Hn | rewrite EL; exact Hw1 | exact HA'R1 | exact Ha'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] srefl k1 A' a' : tySEq k A a a @ k ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qg]
                    | exact HII]. }
  assert (Ec : tm_leq (srefl k A a) (srefl k1 A' a')) by (cbn; repeat split; assumption).
  refine (rec_t_br 29 (k :: nil) (k1 :: nil) (GCtx ΔL :: GTy A :: GTm a :: nil)
            (GCtx ΔR :: GTy A' :: GTm a' :: nil)
            (recTL k ΔL A :: rectL k ΔL A a :: nil) (recTR k1 ΔR A' :: rectR k1 ΔR A' a' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR Q HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl HII) HcL0 HcRL HcR0 Ec
            (GS_refl EP EM 29 eq_refl eq_refl Hσ HΔL HΔ HA HA'R HAA EA Ha Ha'R Haa Ea)
            (GS_refl EP EM 29 eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HA'R1 HA'R1
               (eqty_refl _ _ _ _ _ (lift_ty (j := lD) HA'R1 Hl1c)) (ty_leq_refl _)
               Ha'R1 Ha'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ha'R1 Hl1c)) (tm_leq_refl _))
            _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2].
  - sr_ctx; [exact X1r | exact X2r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_srefl_inst; inst_side 29.
  - apply redt_srefl_inst; inst_side 29.
Qed.

Lemma rec_T_sempty {ΔL ΔR kL kR k k'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k kL -> lequiv L' k kR -> lwf L' k -> lwf L' k' -> leqv k k' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL (boxT (tySEmpty k))) (motT (wrapMT MTR) kR ΔR (boxT (tySEmpty k')))
    (recTL kL ΔL (tySEmpty k)) (recTR kR ΔR (tySEmpty k')).
Proof using EL ELM ELP EMl HMT HMT' Hbs Hbs' He Hl1 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw' E.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Q : lequiv L' k k') by exact (leqv_lequiv _ _ _ Hw Hw' E).
  assert (HU : forall Δ j, [ G' ; Δ ⊢[ lD ] ] -> lwf L' j -> [ G' ; Δ ⊢[ lC ] tySEmpty j @ j ])
    by (intros; apply wft_sempty; [discriminate | assumption | rewrite EL; assumption]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tySEmpty k' @ k ])
    by (eapply wft_lconv; [exact (HU _ _ HΔL Hw') | rewrite EL; exact Q]).
  refine (rec_T_br 27 (k :: nil) (k' :: nil) (GCtx ΔL :: nil) (GCtx ΔR :: nil) nil nil
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR Q (HU _ _ HΔL Hw) HcRL (HU _ _ HΔR Hw') E
            (GS_ctx0 EP EM 27 (k :: nil) eq_refl eq_refl Hσ HΔL HΔ)
            (GS_ctx0 EP EM 27 (k' :: nil) eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR))
            _ _ _ _ _ _ _).
  1-2: sr_ctx.
  1-3: res_eq.
  - apply redT_sempty_inst; inst_side 27.
  - apply redT_sempty_inst; inst_side 27.
Qed.

Lemma rec_t_codesempty {ΔL ΔR kL kR TL TR j j'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lsuc j) kL -> lequiv L' (lsuc j) kR -> lwf L' j -> lwf L' j' -> leqv j j' ->
  [ G' ; ΔL ⊢[ lD ] tyU j ≅ TL @ lsuc j ] -> [ G' ; ΔL ⊢[ lD ] tyU j ≅ TR @ lsuc j ] ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmSEmpty j))) (mott (wrapMt MtR) kR ΔR TR (boxt (tmSEmpty j')))
    (rectL kL ΔL TL (tmSEmpty j)) (rectR kR ΔR TR (tmSEmpty j')).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hj Hj' E HTL HTR.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Q : lequiv L' j j') by exact (leqv_lequiv _ _ _ Hj Hj' E).
  assert (Q1 : lequiv L' (lsuc j) (lsuc j')) by (apply lequiv_suc; exact Q).
  assert (HUU : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lD ] tyU j ≅ tyU j' @ lsuc j ])
    by (intros; apply eqty_U; [discriminate | assumption | rewrite EL; exact Q]).
  assert (Hc : forall Δ i, [ G' ; Δ ⊢[ lD ] ] -> lwf L' i -> [ G' ; Δ ⊢[ lC ] tmSEmpty i : tyU i @ lsuc i ])
    by (intros; apply wf_code_sempty; [discriminate | assumption | rewrite EL; assumption]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tmSEmpty j' : tyU j @ lsuc j ]).
  { eapply wf_lconv; [| rewrite EL; exact Q1].
    eapply wf_conv; [exact (Hc _ _ HΔL Hj') |].
    eapply eqty_lconv; [exact (HUU _ HΔL) | rewrite EL; apply lequiv_sym, Q1]. }
  refine (rec_t_br 28 (j :: nil) (j' :: nil) (GCtx ΔL :: nil) (GCtx ΔR :: nil) nil nil
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR Q1 HTL HTR (HUU _ HΔR)
            (Hc _ _ HΔL Hj) HcRL (Hc _ _ HΔR Hj') E
            (GS_ctx0 EP EM 28 (j :: nil) eq_refl eq_refl Hσ HΔL HΔ)
            (GS_ctx0 EP EM 28 (j' :: nil) eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR))
            _ _ _ _ _ _ _).
  1-2: sr_ctx.
  1-3: res_eq.
  - apply redt_codesempty_inst; inst_side 28.
  - apply redt_codesempty_inst; inst_side 28.
Qed.

(** [sEmpty]'s eliminator: the motive's call at the motive's level, the
    scrutinee's at [sEmpty]'s. *)
Lemma rec_t_elimSEmpty {ΔL ΔR kL kR TL TR k k' k1 k1' M M' e0 e0'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k' kL -> lequiv L' k' kR -> lwf L' k -> lwf L' k' -> lwf L' k1 -> lwf L' k1' ->
  leqv k k1 -> leqv k' k1' ->
  [ G' ; ΔL ⊢[ lD ] M ≅ TL @ k' ] -> [ G' ; ΔL ⊢[ lD ] M ≅ TR @ k' ] ->
  [ G' ; ΔL ⊢[ lC ] M @ k' ] -> [ G' ; ΔL ⊢[ lC ] M' @ k' ] -> ty_leq M M' ->
  [ G' ; ΔL ⊢[ lC ] e0 : tySEmpty k @ k ] -> [ G' ; ΔL ⊢[ lC ] e0' : tySEmpty k @ k ] -> tm_leq e0 e0' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k' ΔL (boxT M)) (motT (wrapMT MTR) k1' ΔR (boxT M'))
    (recTL k' ΔL M) (recTR k1' ΔR M') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL (tySEmpty k) (boxt e0))
    (mott (wrapMt MtR) k1 ΔR (tySEmpty k1) (boxt e0'))
    (rectL k ΔL (tySEmpty k) e0) (rectR k1 ΔR (tySEmpty k1) e0') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (elimSEmpty k k' M e0)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (elimSEmpty k1 k1' M' e0')))
    (rectL kL ΔL TL (elimSEmpty k k' M e0)) (rectR kR ΔR TR (elimSEmpty k1 k1' M' e0')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw' Hw1 Hw1' E E' HTL HTR HM HM' EM1 He0 He0' Ee IHM IHe.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Q' : lequiv L' k' k1') by exact (leqv_lequiv _ _ _ Hw' Hw1' E').
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q).
  assert (Qg' : lequiv (gL G') k' k1') by (rewrite EL; exact Q').
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1)).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  (* the motive and the scrutinee, and their calls *)
  destruct (Tcall HΔL HΔ Hw' Q' HM HM' EM1 IHM) as (HMM & HM'R & HM'R1 & _ & _ & X1).
  assert (HSE : [ G' ; ΔL ⊢[ lD ] tySEmpty k ≅ tySEmpty k1 @ k ])
    by (apply eqty_sempty; [discriminate | exact HΔL | exact Qg]).
  destruct (tcall HΔL HΔ Hw Q HSE He0 He0' Ee IHe) as (Hee & He'R0 & He'R1 & _ & X2).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHM) IHM) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHe) IHe) Hl2g') as X2r.
  (* the right scrutinee at the left level's [sEmpty] *)
  assert (He'R : [ G' ; ΔR ⊢[ lC ] e0' : tySEmpty k @ k ]).
  { eapply wf_conv; [exact He'R0 | exact (ctxconv_eqty HΔ (i := lD) eq_refl HSE)]. }
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] elimSEmpty k k' M e0 : M @ k' ])
    by (apply wf_elimSEmpty; [exact Hn | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HM | exact He0]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] elimSEmpty k1 k1' M' e0' : M' @ k1' ])
    by (apply wf_elimSEmpty; [exact Hn | rewrite EL; exact Hw1 | rewrite EL; exact Hw1' | exact HM'R1 | exact He'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] elimSEmpty k1 k1' M' e0' : M @ k' ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qg']
                    | exact HMM]. }
  assert (Ec : tm_leq (elimSEmpty k k' M e0) (elimSEmpty k1 k1' M' e0')) by (cbn; repeat split; assumption).
  refine (rec_t_br 30 (k' :: k :: nil) (k1' :: k1 :: nil) (GCtx ΔL :: GTy M :: GTm e0 :: nil)
            (GCtx ΔR :: GTy M' :: GTm e0' :: nil)
            (recTL k' ΔL M :: rectL k ΔL (tySEmpty k) e0 :: nil)
            (recTR k1' ΔR M' :: rectR k1 ΔR (tySEmpty k1) e0' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E' (Forall2_cons _ _ E (Forall2_nil _))))
            HΔL HΔ HkL HkR Q' HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl HMM) HcL0 HcRL HcR0 Ec
            (GS_elimSEmpty EP EM Hσ HΔL HΔ HM HM'R HMM EM1 He0 He'R Hee Ee)
            (GS_elimSEmpty EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR)
               HM'R1 HM'R1 (eqty_refl _ _ _ _ _ (lift_ty (j := lD) HM'R1 Hl1c)) (ty_leq_refl _)
               He'R1 He'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) He'R1 Hl1c)) (tm_leq_refl _))
            _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2].
  - sr_ctx; [exact X1r | exact X2r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_elimSEmpty_inst; inst_side 30.
  - apply redt_elimSEmpty_inst; inst_side 30.
Qed.


Lemma rec_t_J {ΔL ΔR kL kR TL TR k k' k1 k1' A A' a a' M M' c c' u u' e0 e0'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k' kL -> lequiv L' k' kR -> lwf L' k -> lwf L' k' -> lwf L' k1 -> lwf L' k1' ->
  leqv k k1 -> leqv k' k1' ->
  [ G' ; ΔL ⊢[ lD ] M[lsingle2 u e0] ≅ TL @ k' ] -> [ G' ; ΔL ⊢[ lD ] M[lsingle2 u e0] ≅ TR @ k' ] ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] A' @ k ] -> ty_leq A A' ->
  [ G' ; ΔL ⊢[ lC ] a : A @ k ] -> [ G' ; ΔL ⊢[ lC ] a' : A @ k ] -> tm_leq a a' ->
  [ G' ; ΔL ,, A @ k ⊢[ lC ] tyId k A⟨↑⟩ a⟨↑⟩ (var 0) @ k ] ->
  [ G' ; ΔL ,, A @ k ,, tyId k A⟨↑⟩ a⟨↑⟩ (var 0) @ k ⊢[ lC ] M @ k' ] ->
  [ G' ; ΔL ,, A @ k ,, tyId k A⟨↑⟩ a⟨↑⟩ (var 0) @ k ⊢[ lC ] M' @ k' ] -> ty_leq M M' ->
  [ G' ; ΔL ⊢[ lC ] c : M[lsingle2 a (tmRefl k A a)] @ k' ] ->
  [ G' ; ΔL ⊢[ lC ] c' : M[lsingle2 a (tmRefl k A a)] @ k' ] -> tm_leq c c' ->
  [ G' ; ΔL ⊢[ lC ] u : A @ k ] -> [ G' ; ΔL ⊢[ lC ] u' : A @ k ] -> tm_leq u u' ->
  [ G' ; ΔL ⊢[ lC ] e0 : tyId k A a u @ k ] -> [ G' ; ΔL ⊢[ lC ] e0' : tyId k A a u @ k ] -> tm_leq e0 e0' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL A (boxt a)) (mott (wrapMt MtR) k1 ΔR A' (boxt a'))
    (rectL k ΔL A a) (rectR k1 ΔR A' a') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k' (ΔL ,, A @ k ,, tyId k A⟨↑⟩ a⟨↑⟩ (var 0) @ k) (boxT M))
    (motT (wrapMT MTR) k1' (ΔR ,, A' @ k1 ,, tyId k1 A'⟨↑⟩ a'⟨↑⟩ (var 0) @ k1) (boxT M'))
    (recTL k' (ΔL ,, A @ k ,, tyId k A⟨↑⟩ a⟨↑⟩ (var 0) @ k) M)
    (recTR k1' (ΔR ,, A' @ k1 ,, tyId k1 A'⟨↑⟩ a'⟨↑⟩ (var 0) @ k1) M') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k' ΔL (M[lsingle2 a (tmRefl k A a)]) (boxt c))
    (mott (wrapMt MtR) k1' ΔR (M'[lsingle2 a' (tmRefl k1 A' a')]) (boxt c'))
    (rectL k' ΔL (M[lsingle2 a (tmRefl k A a)]) c) (rectR k1' ΔR (M'[lsingle2 a' (tmRefl k1 A' a')]) c') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL A (boxt u)) (mott (wrapMt MtR) k1 ΔR A' (boxt u'))
    (rectL k ΔL A u) (rectR k1 ΔR A' u') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL (tyId k A a u) (boxt e0))
    (mott (wrapMt MtR) k1 ΔR (tyId k1 A' a' u') (boxt e0'))
    (rectL k ΔL (tyId k A a u) e0) (rectR k1 ΔR (tyId k1 A' a' u') e0') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmJ k k' A a M c u e0)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmJ k1 k1' A' a' M' c' u' e0')))
    (rectL kL ΔL TL (tmJ k k' A a M c u e0)) (rectR kR ΔR TR (tmJ k1 k1' A' a' M' c' u' e0')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw' Hw1 Hw1' E E' HTL HTR HA HA' EA Ha Ha' Ea HI HM HM' EM1 Hc Hc' Ec Hu Hu' Eu
    He0 He0' Ee IHA IHa IHM IHc IHu IHe.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Q' : lequiv L' k' k1') by exact (leqv_lequiv _ _ _ Hw' Hw1' E').
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q).
  assert (Qg' : lequiv (gL G') k' k1') by (rewrite EL; exact Q').
  assert (Qk : lequiv (gL G') k k) by (rewrite EL; exact (lequiv_refl _ _ Hw)).
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1)).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  (* the carrier and the point *)
  destruct (Tcall HΔL HΔ Hw Q HA HA' EA IHA) as (HAA & HA'R & HA'R1 & _ & _ & X1).
  destruct (tcall HΔL HΔ Hw Q HAA Ha Ha' Ea IHa) as (Haa & Ha'R & Ha'R1 & _ & X2).
  pose proof (lift_ty (j := lD) HA Hl1c) as HAD. pose proof (lift_ty (j := lD) HA' Hl1c) as HA'D.
  pose proof (lift_tm (j := lD) Ha Hl1c) as HaD. pose proof (lift_tm (j := lD) Ha' Hl1c) as Ha'D.
  (* the motive, over the right context at both levels *)
  pose proof (J_ctx_eq' (i := lD) eq_refl ltac:(discriminate) Qg HΔ HAD HAA Haa) as CM1.
  pose proof (J_ctx_eq' (i := lD) eq_refl ltac:(discriminate) Qk HΔ HAD HAA Haa) as CM.
  pose proof (eqctx_wf_l (i := lD) eq_refl CM) as HΔM.
  destruct (Tcall HΔM CM1 Hw' Q' HM HM' EM1 IHM) as (HMM & _ & HM'R1 & _ & _ & X3).
  pose proof (ctxconv_ty CM (i := lC) eq_refl HM') as HM'R.
  (* the endpoint and the path *)
  destruct (tcall HΔL HΔ Hw Q HAA Hu Hu' Eu IHu) as (Huu & Hu'R & Hu'R1 & _ & X5).
  assert (HId1 : [ G' ; ΔL ⊢[ lD ] tyId k A a u ≅ tyId k1 A' a' u' @ k ])
    by (apply eqty_id; [discriminate | exact Qg | exact HAD | exact HAA | exact Haa | exact Huu]).
  destruct (tcall HΔL HΔ Hw Q HId1 He0 He0' Ee IHe) as (Hee & _ & He'R1 & _ & X6).
  (* the motive's instances *)
  pose proof (lift_ty (j := lD) HM' Hl1c) as HM'D.
  pose proof (lift_tm (j := lD) Hu Hl1c) as HuD. pose proof (lift_tm (j := lD) Hu' Hl1c) as Hu'D.
  pose proof (lift_tm (j := lD) He0 Hl1c) as HeD. pose proof (lift_tm (j := lD) He0' Hl1c) as He'D.
  destruct (J_facts_D (l3 := k1) Qg HAD HAA HA'D HaD Haa Ha'D HMM HM'D HuD Huu Hu'D HeD Hee He'D)
    as (_ & Hc1 & Hr1 & _).
  destruct (J_facts_D (l3 := k) Qk HAD HAA HA'D HaD Haa Ha'D HMM HM'D HuD Huu Hu'D HeD Hee He'D)
    as (_ & Hc0 & _ & HI0).
  destruct (tcall HΔL HΔ Hw' Q' Hc1 Hc Hc' Ec IHc) as (Hcc & _ & Hc'R1 & _ & X4).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHA) IHA) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHa) IHa) Hl2g') as X2r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHM) IHM) Hl1g') as X3r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHc) IHc) Hl2g') as X4r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHu) IHu) Hl2g') as X5r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHe) IHe) Hl2g') as X6r.
  (* the right pieces at the left levels *)
  assert (Hc'R : [ G' ; ΔR ⊢[ lC ] c' : M'[lsingle2 a' (tmRefl k A' a')] @ k' ]).
  { eapply wf_conv; [exact (ctxconv_tm HΔ (i := lC) eq_refl Hc')
                    | exact (ctxconv_eqty HΔ (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ Hc0))]. }
  assert (He'R : [ G' ; ΔR ⊢[ lC ] e0' : tyId k A' a' u' @ k ]).
  { eapply wf_conv; [exact (ctxconv_tm HΔ (i := lC) eq_refl He0')
                    | exact (ctxconv_eqty HΔ (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ HI0))]. }
  (* the codes *)
  assert (HI' : [ G' ; ΔR ,, A' @ k1 ⊢[ lC ] tyId k1 A'⟨↑⟩ a'⟨↑⟩ (var 0) @ k1 ]).
  { apply wf_Jid_g; [exact Hn | rewrite EL; exact Hw1 | | exact HA'R1 | exact Ha'R1].
    apply wfc_ext; [exact HΔR | exact (lift_ty (j := lD) HA'R1 Hl1c) | rewrite EL; exact Hw1]. }
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] tmJ k k' A a M c u e0 : M[lsingle2 u e0] @ k' ])
    by (apply wf_J; [exact Hn | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HA | exact Ha | exact HI
                    | exact HM | exact Hc | exact Hu | exact He0]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmJ k1 k1' A' a' M' c' u' e0' : M'[lsingle2 u' e0'] @ k1' ])
    by (apply wf_J; [exact Hn | rewrite EL; exact Hw1 | rewrite EL; exact Hw1' | exact HA'R1 | exact Ha'R1 | exact HI'
                    | exact HM'R1 | exact Hc'R1 | exact Hu'R1 | exact He'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tmJ k1 k1' A' a' M' c' u' e0' : M[lsingle2 u e0] @ k' ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qg']
                    | exact Hr1]. }
  assert (Ecc : tm_leq (tmJ k k' A a M c u e0) (tmJ k1 k1' A' a' M' c' u' e0')) by (cbn; repeat split; assumption).
  pose proof (lift_ty (j := lD) HA'R1 Hl1c) as HA'R1D. pose proof (lift_ty (j := lD) HM'R1 Hl1c) as HM'R1D.
  refine (rec_t_br 24 (k :: k' :: nil) (k1 :: k1' :: nil)
            (GCtx ΔL :: GTy A :: GTm a :: GTy M :: GTm c :: GTm u :: GTm e0 :: nil)
            (GCtx ΔR :: GTy A' :: GTm a' :: GTy M' :: GTm c' :: GTm u' :: GTm e0' :: nil)
            (recTL k ΔL A :: rectL k ΔL A a :: recTL k' (ΔL ,, A @ k ,, tyId k A⟨↑⟩ a⟨↑⟩ (var 0) @ k) M
             :: rectL k' ΔL (M[lsingle2 a (tmRefl k A a)]) c :: rectL k ΔL A u :: rectL k ΔL (tyId k A a u) e0 :: nil)
            (recTR k1 ΔR A' :: rectR k1 ΔR A' a' :: recTR k1' (ΔR ,, A' @ k1 ,, tyId k1 A'⟨↑⟩ a'⟨↑⟩ (var 0) @ k1) M'
             :: rectR k1' ΔR (M'[lsingle2 a' (tmRefl k1 A' a')]) c' :: rectR k1 ΔR A' u'
             :: rectR k1 ΔR (tyId k1 A' a' u') e0' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_cons _ _ E' (Forall2_nil _))))
            HΔL HΔ HkL HkR Q' HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl Hr1) HcL0 HcRL HcR0 Ecc
            (GS_J EP EM Hσ HΔL HΔ HA HA'R HAA EA Ha Ha'R Haa Ea HM HM'R HMM EM1 Hc Hc'R Hcc Ec Hu Hu'R Huu Eu
               He0 He'R Hee Ee)
            (GS_J EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR)
               HA'R1 HA'R1 (eqty_refl _ _ _ _ _ HA'R1D) (ty_leq_refl _)
               Ha'R1 Ha'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ha'R1 Hl1c)) (tm_leq_refl _)
               HM'R1 HM'R1 (eqty_refl _ _ _ _ _ HM'R1D) (ty_leq_refl _)
               Hc'R1 Hc'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hc'R1 Hl1c)) (tm_leq_refl _)
               Hu'R1 Hu'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hu'R1 Hl1c)) (tm_leq_refl _)
               He'R1 He'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) He'R1 Hl1c)) (tm_leq_refl _))
            _ _ _ _ _ _ _).
  - sr_ctx; J_cbn; [exact X1 | exact X2 | exact X3 | exact X4 | exact X5 | exact X6].
  - sr_ctx; J_cbn; [exact X1r | exact X2r | exact X3r | exact X4r | exact X5r | exact X6r].
  - J_res.
  - J_res.
  - J_res.
  - apply redt_J_inst; inst_side 24.
  - apply redt_J_inst; inst_side 24.
Qed.

End Rec.
