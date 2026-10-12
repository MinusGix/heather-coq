(** * The recursion lemmas on code: the empty type and binary sums

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

(** ** The empty type and binary sums (M12c) *)

Lemma rec_T_empty {ΔL ΔR kL kR k k'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k kL -> lequiv L' k kR -> lwf L' k -> lwf L' k' -> leqv k k' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL (boxT (tyEmpty k))) (motT (wrapMT MTR) kR ΔR (boxT (tyEmpty k')))
    (recTL kL ΔL (tyEmpty k)) (recTR kR ΔR (tyEmpty k')).
Proof using EL ELM ELP EMl HMT HMT' Hbs Hbs' He Hl1 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw' E.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Q : lequiv L' k k') by exact (leqv_lequiv _ _ _ Hw Hw' E).
  assert (HU : forall Δ j, [ G' ; Δ ⊢[ lD ] ] -> lwf L' j -> [ G' ; Δ ⊢[ lC ] tyEmpty j @ j ])
    by (intros; apply wft_empty; [discriminate | assumption | rewrite EL; assumption]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tyEmpty k' @ k ])
    by (eapply wft_lconv; [exact (HU _ _ HΔL Hw') | rewrite EL; exact Q]).
  refine (rec_T_br 31 (k :: nil) (k' :: nil) (GCtx ΔL :: nil) (GCtx ΔR :: nil) nil nil
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR Q (HU _ _ HΔL Hw) HcRL (HU _ _ HΔR Hw') E
            (GS_ctx0 EP EM 31 (k :: nil) eq_refl eq_refl Hσ HΔL HΔ)
            (GS_ctx0 EP EM 31 (k' :: nil) eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR))
            _ _ _ _ _ _ _).
  1-2: sr_ctx.
  1-3: res_eq.
  - apply redT_empty_inst; inst_side 31.
  - apply redT_empty_inst; inst_side 31.
Qed.

Lemma rec_t_codeempty {ΔL ΔR kL kR TL TR j j'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lsuc j) kL -> lequiv L' (lsuc j) kR -> lwf L' j -> lwf L' j' -> leqv j j' ->
  [ G' ; ΔL ⊢[ lD ] tyU j ≅ TL @ lsuc j ] -> [ G' ; ΔL ⊢[ lD ] tyU j ≅ TR @ lsuc j ] ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmEmpty j))) (mott (wrapMt MtR) kR ΔR TR (boxt (tmEmpty j')))
    (rectL kL ΔL TL (tmEmpty j)) (rectR kR ΔR TR (tmEmpty j')).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hj Hj' E HTL HTR.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Q : lequiv L' j j') by exact (leqv_lequiv _ _ _ Hj Hj' E).
  assert (Q1 : lequiv L' (lsuc j) (lsuc j')) by (apply lequiv_suc; exact Q).
  assert (HUU : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lD ] tyU j ≅ tyU j' @ lsuc j ])
    by (intros; apply eqty_U; [discriminate | assumption | rewrite EL; exact Q]).
  assert (Hc : forall Δ i, [ G' ; Δ ⊢[ lD ] ] -> lwf L' i -> [ G' ; Δ ⊢[ lC ] tmEmpty i : tyU i @ lsuc i ])
    by (intros; apply wf_code_empty; [discriminate | assumption | rewrite EL; assumption]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tmEmpty j' : tyU j @ lsuc j ]).
  { eapply wf_lconv; [| rewrite EL; exact Q1].
    eapply wf_conv; [exact (Hc _ _ HΔL Hj') |].
    eapply eqty_lconv; [exact (HUU _ HΔL) | rewrite EL; apply lequiv_sym, Q1]. }
  refine (rec_t_br 32 (j :: nil) (j' :: nil) (GCtx ΔL :: nil) (GCtx ΔR :: nil) nil nil
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR Q1 HTL HTR (HUU _ HΔR)
            (Hc _ _ HΔL Hj) HcRL (Hc _ _ HΔR Hj') E
            (GS_ctx0 EP EM 32 (j :: nil) eq_refl eq_refl Hσ HΔL HΔ)
            (GS_ctx0 EP EM 32 (j' :: nil) eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR))
            _ _ _ _ _ _ _).
  1-2: sr_ctx.
  1-3: res_eq.
  - apply redt_codeempty_inst; inst_side 32.
  - apply redt_codeempty_inst; inst_side 32.
Qed.

(** [Empty]'s eliminator: the motive's call over the scrutinee, the
    scrutinee's at [Empty]'s level. *)
Lemma rec_t_elimEmpty {ΔL ΔR kL kR TL TR k k' k1 k1' M M' t t'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k kL -> lequiv L' k kR -> lwf L' k -> lwf L' k' -> lwf L' k1 -> lwf L' k1' ->
  leqv k k1 -> leqv k' k1' ->
  [ G' ; ΔL ⊢[ lD ] M[lsingle t] ≅ TL @ k ] -> [ G' ; ΔL ⊢[ lD ] M[lsingle t] ≅ TR @ k ] ->
  [ G' ; ΔL ,, tyEmpty k' @ k' ⊢[ lC ] M @ k ] -> [ G' ; ΔL ,, tyEmpty k' @ k' ⊢[ lC ] M' @ k ] -> ty_leq M M' ->
  [ G' ; ΔL ⊢[ lC ] t : tyEmpty k' @ k' ] -> [ G' ; ΔL ⊢[ lC ] t' : tyEmpty k' @ k' ] -> tm_leq t t' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k (ΔL ,, tyEmpty k' @ k') (boxT M))
    (motT (wrapMT MTR) k1 (ΔR ,, tyEmpty k1' @ k1') (boxT M'))
    (recTL k (ΔL ,, tyEmpty k' @ k') M) (recTR k1 (ΔR ,, tyEmpty k1' @ k1') M') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k' ΔL (tyEmpty k') (boxt t))
    (mott (wrapMt MtR) k1' ΔR (tyEmpty k1') (boxt t'))
    (rectL k' ΔL (tyEmpty k') t) (rectR k1' ΔR (tyEmpty k1') t') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (elimEmpty k k' M t)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (elimEmpty k1 k1' M' t')))
    (rectL kL ΔL TL (elimEmpty k k' M t)) (rectR kR ΔR TR (elimEmpty k1 k1' M' t')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw' Hw1 Hw1' E E' HTL HTR HM HM' EM1 Ht Ht' Et IHM IHt.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Q' : lequiv L' k' k1') by exact (leqv_lequiv _ _ _ Hw' Hw1' E').
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q).
  assert (Qg' : lequiv (gL G') k' k1') by (rewrite EL; exact Q').
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1)).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  (* the scrutinee's type, and the motive's context *)
  assert (HED : [ G' ; ΔL ⊢[ lD ] tyEmpty k' @ k' ])
    by (apply wft_empty; [discriminate | exact HΔL | rewrite EL; exact Hw']).
  assert (HEE : forall j, lequiv L' k' j -> [ G' ; ΔL ⊢[ lD ] tyEmpty k' ≅ tyEmpty j @ k' ])
    by (intros; apply eqty_empty; [discriminate | exact HΔL | rewrite EL; assumption]).
  assert (CE : [ G' ⊢[ lD ] ΔL ,, tyEmpty k' @ k' ≅ ΔR ,, tyEmpty k' @ k' ])
    by (apply eqc_ext; [exact HΔ | exact HED | exact (HEE _ (lequiv_refl _ _ Hw')) | rewrite EL; exact (lequiv_refl _ _ Hw')]).
  assert (CE1 : [ G' ⊢[ lD ] ΔL ,, tyEmpty k' @ k' ≅ ΔR ,, tyEmpty k1' @ k1' ])
    by (apply eqc_ext; [exact HΔ | exact HED | exact (HEE _ Q') | exact Qg']).
  pose proof (eqctx_wf_l (i := lD) eq_refl CE) as HΔE.
  (* the motive and the scrutinee, and their calls *)
  destruct (Tcall HΔE CE1 Hw Q HM HM' EM1 IHM) as (HMM & _ & HM'R1 & _ & _ & X1).
  pose proof (ctxconv_ty CE (i := lC) eq_refl HM') as HM'R.
  destruct (tcall HΔL HΔ Hw' Q' (HEE _ Q') Ht Ht' Et IHt) as (Htt & Ht'R0 & Ht'R1 & _ & X2).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHM) IHM) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHt) IHt) Hl2g') as X2r.
  (* the right scrutinee at the left level's [Empty] *)
  assert (Ht'R : [ G' ; ΔR ⊢[ lC ] t' : tyEmpty k' @ k' ]).
  { eapply wf_conv; [exact Ht'R0 | exact (ctxconv_eqty HΔ (i := lD) eq_refl (HEE _ Q'))]. }
  (* the result types *)
  assert (Hr1 : [ G' ; ΔL ⊢[ lD ] M[lsingle t] ≅ M'[lsingle t'] @ k ])
    by exact (eqty_subst_single_D HMM (lift_ty (j := lD) HM' Hl1c) Htt (lift_tm (j := lD) Ht Hl1c)
                (lift_tm (j := lD) Ht' Hl1c)).
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] elimEmpty k k' M t : M[lsingle t] @ k ])
    by (apply wf_elimEmpty; [exact Hn | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HM | exact Ht]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] elimEmpty k1 k1' M' t' : M'[lsingle t'] @ k1 ])
    by (apply wf_elimEmpty; [exact Hn | rewrite EL; exact Hw1 | rewrite EL; exact Hw1' | exact HM'R1 | exact Ht'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] elimEmpty k1 k1' M' t' : M[lsingle t] @ k ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qg]
                    | exact Hr1]. }
  assert (Ec : tm_leq (elimEmpty k k' M t) (elimEmpty k1 k1' M' t')) by (cbn; repeat split; assumption).
  refine (rec_t_br 33 (k :: k' :: nil) (k1 :: k1' :: nil) (GCtx ΔL :: GTy M :: GTm t :: nil)
            (GCtx ΔR :: GTy M' :: GTm t' :: nil)
            (recTL k (ΔL ,, tyEmpty k' @ k') M :: rectL k' ΔL (tyEmpty k') t :: nil)
            (recTR k1 (ΔR ,, tyEmpty k1' @ k1') M' :: rectR k1' ΔR (tyEmpty k1') t' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_cons _ _ E' (Forall2_nil _))))
            HΔL HΔ HkL HkR Q HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl Hr1) HcL0 HcRL HcR0 Ec
            (GS_elimEmpty EP EM Hσ HΔL HΔ HM HM'R HMM EM1 Ht Ht'R Htt Et)
            (GS_elimEmpty EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR)
               HM'R1 HM'R1 (eqty_refl _ _ _ _ _ (lift_ty (j := lD) HM'R1 Hl1c)) (ty_leq_refl _)
               Ht'R1 Ht'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ht'R1 Hl1c)) (tm_leq_refl _))
            _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2].
  - sr_ctx; [exact X1r | exact X2r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_elimEmpty_inst; inst_side 33.
  - apply redt_elimEmpty_inst; inst_side 33.
Qed.

Lemma rec_T_sum {ΔL ΔR kL kR k k' k1 k1' A B A' B'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lmax k k') kL -> lequiv L' (lmax k k') kR ->
  lwf L' k -> lwf L' k' -> lwf L' k1 -> lwf L' k1' -> leqv k k1 -> leqv k' k1' ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] B @ k' ] ->
  [ G' ; ΔL ⊢[ lC ] A' @ k ] -> [ G' ; ΔL ⊢[ lC ] B' @ k' ] -> ty_leq A A' -> ty_leq B B' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k' ΔL (boxT B)) (motT (wrapMT MTR) k1' ΔR (boxT B'))
    (recTL k' ΔL B) (recTR k1' ΔR B') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL (boxT (tySum k k' A B)))
    (motT (wrapMT MTR) kR ΔR (boxT (tySum k1 k1' A' B')))
    (recTL kL ΔL (tySum k k' A B)) (recTR kR ΔR (tySum k1 k1' A' B')).
Proof using EL ELM ELP EMl HMT HMT' Hbs Hbs' He Hl1 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw' Hw1 Hw1' E E' HA HB HA' HB' EA EB IHA IHB.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Q' : lequiv L' k' k1') by exact (leqv_lequiv _ _ _ Hw' Hw1' E').
  assert (Qm : lequiv L' (lmax k k') (lmax k1 k1')) by (apply lequiv_max; assumption).
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1)).
  (* the summands and their calls *)
  destruct (Tcall HΔL HΔ Hw Q HA HA' EA IHA) as (HAA & HA'R & HA'R1 & _ & _ & X1).
  destruct (Tcall HΔL HΔ Hw' Q' HB HB' EB IHB) as (HBB & HB'R & HB'R1 & _ & _ & X2).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHA) IHA) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHB) IHB) Hl1g') as X2r.
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] tySum k k' A B @ lmax k k' ])
    by (apply wft_sum; [exact Hn | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HA | exact HB]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tySum k1 k1' A' B' @ lmax k1 k1' ])
    by (apply wft_sum; [exact Hn | rewrite EL; exact Hw1 | rewrite EL; exact Hw1' | exact HA'R1 | exact HB'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tySum k1 k1' A' B' @ lmax k k' ])
    by (eapply wft_lconv; [exact (ctxconv_ty (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | rewrite EL; exact Qm]).
  assert (Ec : ty_leq (tySum k k' A B) (tySum k1 k1' A' B')) by (cbn; repeat split; assumption).
  refine (rec_T_br 34 (k :: k' :: nil) (k1 :: k1' :: nil) (GCtx ΔL :: GTy A :: GTy B :: nil)
            (GCtx ΔR :: GTy A' :: GTy B' :: nil)
            (recTL k ΔL A :: recTL k' ΔL B :: nil) (recTR k1 ΔR A' :: recTR k1' ΔR B' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_cons _ _ E' (Forall2_nil _))))
            HΔL HΔ HkL HkR Qm HcL0 HcRL HcR0 Ec
            (GS_sum EP EM Hσ HΔL HΔ HA HA'R HAA EA HB HB'R HBB EB)
            (GS_sum EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HA'R1 HA'R1
               (eqty_refl _ _ _ _ _ (lift_ty (j := lD) HA'R1 Hl1c)) (ty_leq_refl _) HB'R1 HB'R1
               (eqty_refl _ _ _ _ _ (lift_ty (j := lD) HB'R1 Hl1c)) (ty_leq_refl _))
            _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2].
  - sr_ctx; [exact X1r | exact X2r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redT_sum_inst; inst_side 34.
  - apply redT_sum_inst; inst_side 34.
Qed.

Lemma rec_t_codesum {ΔL ΔR kL kR TL TR k k' k1 k1' s0 t0 s1 t1} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lsuc (lmax k k')) kL -> lequiv L' (lsuc (lmax k k')) kR ->
  lwf L' k -> lwf L' k' -> lwf L' k1 -> lwf L' k1' -> leqv k k1 -> leqv k' k1' ->
  [ G' ; ΔL ⊢[ lD ] tyU (lmax k k') ≅ TL @ lsuc (lmax k k') ] ->
  [ G' ; ΔL ⊢[ lD ] tyU (lmax k k') ≅ TR @ lsuc (lmax k k') ] ->
  [ G' ; ΔL ⊢[ lC ] s0 : tyU k @ lsuc k ] -> [ G' ; ΔL ⊢[ lC ] s1 : tyU k @ lsuc k ] -> tm_leq s0 s1 ->
  [ G' ; ΔL ⊢[ lC ] t0 : tyU k' @ lsuc k' ] -> [ G' ; ΔL ⊢[ lC ] t1 : tyU k' @ lsuc k' ] -> tm_leq t0 t1 ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lsuc k) ΔL (tyU k) (boxt s0))
    (mott (wrapMt MtR) (lsuc k1) ΔR (tyU k1) (boxt s1))
    (rectL (lsuc k) ΔL (tyU k) s0) (rectR (lsuc k1) ΔR (tyU k1) s1) ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lsuc k') ΔL (tyU k') (boxt t0))
    (mott (wrapMt MtR) (lsuc k1') ΔR (tyU k1') (boxt t1))
    (rectL (lsuc k') ΔL (tyU k') t0) (rectR (lsuc k1') ΔR (tyU k1') t1) ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmSum k k' s0 t0)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmSum k1 k1' s1 t1)))
    (rectL kL ΔL TL (tmSum k k' s0 t0)) (rectR kR ΔR TR (tmSum k1 k1' s1 t1)).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw' Hw1 Hw1' E E' HTL HTR Hs Hs' Es Ht Ht' Et IHs IHt.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Q' : lequiv L' k' k1') by exact (leqv_lequiv _ _ _ Hw' Hw1' E').
  assert (Qm : lequiv L' (lmax k k') (lmax k1 k1')) by (apply lequiv_max; assumption).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  assert (HUU : forall Δ j j', [ G' ; Δ ⊢[ lD ] ] -> lequiv L' j j' -> [ G' ; Δ ⊢[ lD ] tyU j ≅ tyU j' @ lsuc j ])
    by (intros; apply eqty_U; [discriminate | assumption | rewrite EL; assumption]).
  (* the summands' codes and their calls *)
  destruct (tcall (k := lsuc k) HΔL HΔ Hw (lequiv_suc _ _ _ Q) (HUU _ _ _ HΔL Q) Hs Hs' Es IHs) as (Hss & _ & Hs'R1 & _ & X1).
  destruct (tcall (k := lsuc k') HΔL HΔ Hw' (lequiv_suc _ _ _ Q') (HUU _ _ _ HΔL Q') Ht Ht' Et IHt) as (Htt & _ & Ht'R1 & _ & X2).
  pose proof (ctxconv_tm HΔ (i := lC) eq_refl Hs') as Hs'R.
  pose proof (ctxconv_tm HΔ (i := lC) eq_refl Ht') as Ht'R.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHs) IHs) Hl2g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHt) IHt) Hl2g') as X2r.
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] tmSum k k' s0 t0 : tyU (lmax k k') @ lsuc (lmax k k') ])
    by (apply wf_code_sum; [discriminate | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact Hs | exact Ht]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmSum k1 k1' s1 t1 : tyU (lmax k1 k1') @ lsuc (lmax k1 k1') ])
    by (apply wf_code_sum; [discriminate | rewrite EL; exact Hw1 | rewrite EL; exact Hw1' | exact Hs'R1 | exact Ht'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tmSum k1 k1' s1 t1 : tyU (lmax k k') @ lsuc (lmax k k') ])
    by (eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0)
                                          | rewrite EL; apply lequiv_suc, Qm] | exact (HUU _ _ _ HΔL Qm)]).
  refine (rec_t_br 35 (k :: k' :: nil) (k1 :: k1' :: nil) (GCtx ΔL :: GTm s0 :: GTm t0 :: nil)
            (GCtx ΔR :: GTm s1 :: GTm t1 :: nil)
            (rectL (lsuc k) ΔL (tyU k) s0 :: rectL (lsuc k') ΔL (tyU k') t0 :: nil)
            (rectR (lsuc k1) ΔR (tyU k1) s1 :: rectR (lsuc k1') ΔR (tyU k1') t1 :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl
            ltac:(repeat constructor; assumption) ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_cons _ _ E' (Forall2_nil _))))
            HΔL HΔ HkL HkR (lequiv_suc _ _ _ Qm) HTL HTR (HUU _ _ _ HΔR Qm) HcL0 HcRL HcR0
            ltac:(cbn; repeat split; assumption)
            (GS_codesum EP EM Hσ HΔL HΔ Hs Hs'R Hss Es Ht Ht'R Htt Et)
            (GS_codesum EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) Hs'R1 Hs'R1
               (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hs'R1 Hl1c)) (tm_leq_refl _) Ht'R1 Ht'R1
               (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ht'R1 Hl1c)) (tm_leq_refl _)) _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2].
  - sr_ctx; [exact X1r | exact X2r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_codesum_inst; inst_side 35.
  - apply redt_codesum_inst; inst_side 35.
Qed.

(** The injections: both summands' calls and the payload's. *)
Ltac rec_t_inj kb inj wf_inj inst U ΔL ΔR k k' k1 k1' A B A' B' a a' :=
  intros HΔL HΔ HkL HkR Hw Hw' Hw1 Hw1' E E' HTL HTR HA HA' EA HB HB' EB Ha Ha' Ea IHA IHB IHa;
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR;
  assert (Hn : lC <> lV) by discriminate; assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia);
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E);
  assert (Q' : lequiv L' k' k1') by exact (leqv_lequiv _ _ _ Hw' Hw1' E');
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q); assert (Qg' : lequiv (gL G') k' k1') by (rewrite EL; exact Q');
  assert (Qm : lequiv L' (lmax k k') (lmax k1 k1')) by (apply lequiv_max; assumption);
  assert (Qmg : lequiv (gL G') (lmax k k') (lmax k1 k1')) by (rewrite EL; exact Qm);
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1));
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2));
  (* the summands and their calls *)
  destruct (Tcall HΔL HΔ Hw Q HA HA' EA IHA) as (HAA & HA'R & HA'R1 & _ & _ & X1);
  destruct (Tcall HΔL HΔ Hw' Q' HB HB' EB IHB) as (HBB & HB'R & HB'R1 & _ & _ & X2);
  pose proof (lift_ty (j := lD) HA'R1 Hl1c) as HA'R1D; pose proof (lift_ty (j := lD) HB'R1 Hl1c) as HB'R1D;
  assert (HSS : [ G' ; ΔL ⊢[ lD ] tySum k k' A B ≅ tySum k1 k1' A' B' @ lmax k k' ])
    by (apply eqty_sum; [discriminate | exact Qg | exact Qg' | exact HAA | exact HBB]);
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHA) IHA) Hl1g') as X1r;
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHB) IHB) Hl1g') as X2r;
  (* the payload and its call *)
  let TC := lazymatch U with
             | 1 => constr:(tcall HΔL HΔ Hw Q HAA Ha Ha' Ea IHa)
             | _ => constr:(tcall HΔL HΔ Hw' Q' HBB Ha Ha' Ea IHa)
             end in
  destruct TC as (Haa & Ha'R & Ha'R1 & _ & X3);
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHa) IHa) Hl2g') as X3r;
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] inj k k' A B a : tySum k k' A B @ lmax k k' ])
    by (apply wf_inj; [exact Hn | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HA | exact HB | exact Ha]);
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] inj k1 k1' A' B' a' : tySum k1 k1' A' B' @ lmax k1 k1' ])
    by (apply wf_inj; [exact Hn | rewrite EL; exact Hw1 | rewrite EL; exact Hw1' | exact HA'R1 | exact HB'R1
                      | exact Ha'R1]);
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] inj k1 k1' A' B' a' : tySum k k' A B @ lmax k k' ])
    by (eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qmg]
                        | exact HSS]);
  assert (Ec : tm_leq (inj k k' A B a) (inj k1 k1' A' B' a')) by (cbn; repeat split; assumption);
  let xL := lazymatch U with 1 => constr:(rectL k ΔL A a) | _ => constr:(rectL k' ΔL B a) end in
  let xR := lazymatch U with 1 => constr:(rectR k1 ΔR A' a') | _ => constr:(rectR k1' ΔR B' a') end in
  let Hkb := lazymatch U with
             | 1 => uconstr:(or_introl (conj eq_refl (conj eq_refl (conj eq_refl eq_refl))))
             | _ => uconstr:(or_intror (conj eq_refl (conj eq_refl (conj eq_refl eq_refl))))
             end in
  refine (rec_t_br kb (k :: k' :: nil) (k1 :: k1' :: nil) (GCtx ΔL :: GTy A :: GTy B :: GTm a :: nil)
            (GCtx ΔR :: GTy A' :: GTy B' :: GTm a' :: nil)
            (recTL k ΔL A :: recTL k' ΔL B :: xL :: nil) (recTR k1 ΔR A' :: recTR k1' ΔR B' :: xR :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl
            ltac:(repeat constructor; assumption) ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_cons _ _ E' (Forall2_nil _))))
            HΔL HΔ HkL HkR Qm HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl HSS) HcL0 HcRL HcR0 Ec
            (GS_inj EP EM kb U Hkb Hσ HΔL HΔ HA HA'R HAA EA HB HB'R HBB EB
               Ha Ha'R Haa Ea)
            (GS_inj EP EM kb U Hkb (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR)
               HA'R1 HA'R1 (eqty_refl _ _ _ _ _ HA'R1D) (ty_leq_refl _)
               HB'R1 HB'R1 (eqty_refl _ _ _ _ _ HB'R1D) (ty_leq_refl _)
               Ha'R1 Ha'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ha'R1 Hl1c)) (tm_leq_refl _))
            _ _ _ _ _ _ _);
  [ sr_ctx; [exact X1 | exact X2 | exact X3] | sr_ctx; [exact X1r | exact X2r | exact X3r] | res_eq | res_eq | res_eq
  | apply inst; inst_side kb | apply inst; inst_side kb ].

Lemma rec_t_inl {ΔL ΔR kL kR TL TR k k' k1 k1' A B A' B' a a'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lmax k k') kL -> lequiv L' (lmax k k') kR -> lwf L' k -> lwf L' k' -> lwf L' k1 -> lwf L' k1' ->
  leqv k k1 -> leqv k' k1' ->
  [ G' ; ΔL ⊢[ lD ] tySum k k' A B ≅ TL @ lmax k k' ] -> [ G' ; ΔL ⊢[ lD ] tySum k k' A B ≅ TR @ lmax k k' ] ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] A' @ k ] -> ty_leq A A' ->
  [ G' ; ΔL ⊢[ lC ] B @ k' ] -> [ G' ; ΔL ⊢[ lC ] B' @ k' ] -> ty_leq B B' ->
  [ G' ; ΔL ⊢[ lC ] a : A @ k ] -> [ G' ; ΔL ⊢[ lC ] a' : A @ k ] -> tm_leq a a' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k' ΔL (boxT B)) (motT (wrapMT MTR) k1' ΔR (boxT B'))
    (recTL k' ΔL B) (recTR k1' ΔR B') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL A (boxt a)) (mott (wrapMt MtR) k1 ΔR A' (boxt a'))
    (rectL k ΔL A a) (rectR k1 ΔR A' a') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmInl k k' A B a)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmInl k1 k1' A' B' a')))
    (rectL kL ΔL TL (tmInl k k' A B a)) (rectR kR ΔR TR (tmInl k1 k1' A' B' a')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  rec_t_inj 36 tmInl wf_inl redt_inl_inst (1) ΔL ΔR k k' k1 k1' A B A' B' a a'.
Qed.

Lemma rec_t_inr {ΔL ΔR kL kR TL TR k k' k1 k1' A B A' B' a a'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lmax k k') kL -> lequiv L' (lmax k k') kR -> lwf L' k -> lwf L' k' -> lwf L' k1 -> lwf L' k1' ->
  leqv k k1 -> leqv k' k1' ->
  [ G' ; ΔL ⊢[ lD ] tySum k k' A B ≅ TL @ lmax k k' ] -> [ G' ; ΔL ⊢[ lD ] tySum k k' A B ≅ TR @ lmax k k' ] ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] A' @ k ] -> ty_leq A A' ->
  [ G' ; ΔL ⊢[ lC ] B @ k' ] -> [ G' ; ΔL ⊢[ lC ] B' @ k' ] -> ty_leq B B' ->
  [ G' ; ΔL ⊢[ lC ] a : B @ k' ] -> [ G' ; ΔL ⊢[ lC ] a' : B @ k' ] -> tm_leq a a' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k' ΔL (boxT B)) (motT (wrapMT MTR) k1' ΔR (boxT B'))
    (recTL k' ΔL B) (recTR k1' ΔR B') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k' ΔL B (boxt a)) (mott (wrapMt MtR) k1' ΔR B' (boxt a'))
    (rectL k' ΔL B a) (rectR k1' ΔR B' a') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmInr k k' A B a)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmInr k1 k1' A' B' a')))
    (rectL kL ΔL TL (tmInr k k' A B a)) (rectR kR ΔR TR (tmInr k1 k1' A' B' a')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  rec_t_inj 37 tmInr wf_inr redt_inr_inst (0) ΔL ΔR k k' k1 k1' A B A' B' a a'.
Qed.

(** [case]: the summands', the motive's (over the sum), the branches' (over
    their summands, at the motive's instances) and the scrutinee's calls.
    The branch scopes declare the branch types in their substituted form
    ([liftshift_cons_ty']); the calls carry the typing rule's. *)
Lemma rec_t_case {ΔL ΔR kL kR TL TR k k' k'' k1 k1' k1'' A A' B B' M M' c1 c1' c2 c2' t t'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k'' kL -> lequiv L' k'' kR -> lwf L' k -> lwf L' k' -> lwf L' k'' -> lwf L' k1 -> lwf L' k1' -> lwf L' k1'' ->
  leqv k k1 -> leqv k' k1' -> leqv k'' k1'' ->
  [ G' ; ΔL ⊢[ lD ] M[lsingle t] ≅ TL @ k'' ] -> [ G' ; ΔL ⊢[ lD ] M[lsingle t] ≅ TR @ k'' ] ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] A' @ k ] -> ty_leq A A' ->
  [ G' ; ΔL ⊢[ lC ] B @ k' ] -> [ G' ; ΔL ⊢[ lC ] B' @ k' ] -> ty_leq B B' ->
  [ G' ; ΔL ,, tySum k k' A B @ lmax k k' ⊢[ lC ] M @ k'' ] ->
  [ G' ; ΔL ,, tySum k k' A B @ lmax k k' ⊢[ lC ] M' @ k'' ] -> ty_leq M M' ->
  [ G' ; ΔL ,, A @ k ⊢[ lC ] c1 : M⟨rlift ↑⟩[lsingle (tmInl k k' A⟨↑⟩ B⟨↑⟩ (var 0))] @ k'' ] ->
  [ G' ; ΔL ,, A @ k ⊢[ lC ] c1' : M⟨rlift ↑⟩[lsingle (tmInl k k' A⟨↑⟩ B⟨↑⟩ (var 0))] @ k'' ] -> tm_leq c1 c1' ->
  [ G' ; ΔL ,, B @ k' ⊢[ lC ] c2 : M⟨rlift ↑⟩[lsingle (tmInr k k' A⟨↑⟩ B⟨↑⟩ (var 0))] @ k'' ] ->
  [ G' ; ΔL ,, B @ k' ⊢[ lC ] c2' : M⟨rlift ↑⟩[lsingle (tmInr k k' A⟨↑⟩ B⟨↑⟩ (var 0))] @ k'' ] -> tm_leq c2 c2' ->
  [ G' ; ΔL ⊢[ lC ] t : tySum k k' A B @ lmax k k' ] -> [ G' ; ΔL ⊢[ lC ] t' : tySum k k' A B @ lmax k k' ] ->
  tm_leq t t' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k' ΔL (boxT B)) (motT (wrapMT MTR) k1' ΔR (boxT B'))
    (recTL k' ΔL B) (recTR k1' ΔR B') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k'' (ΔL ,, tySum k k' A B @ lmax k k') (boxT M))
    (motT (wrapMT MTR) k1'' (ΔR ,, tySum k1 k1' A' B' @ lmax k1 k1') (boxT M'))
    (recTL k'' (ΔL ,, tySum k k' A B @ lmax k k') M) (recTR k1'' (ΔR ,, tySum k1 k1' A' B' @ lmax k1 k1') M') ->
  LRtmM (lvsubst l2 φ) G' Θ
    (mott (wrapMt MtL) k'' (ΔL ,, A @ k) (M⟨rlift ↑⟩[lsingle (tmInl k k' A⟨↑⟩ B⟨↑⟩ (var 0))]) (boxt c1))
    (mott (wrapMt MtR) k1'' (ΔR ,, A' @ k1) (M'⟨rlift ↑⟩[lsingle (tmInl k1 k1' A'⟨↑⟩ B'⟨↑⟩ (var 0))]) (boxt c1'))
    (rectL k'' (ΔL ,, A @ k) (M⟨rlift ↑⟩[lsingle (tmInl k k' A⟨↑⟩ B⟨↑⟩ (var 0))]) c1)
    (rectR k1'' (ΔR ,, A' @ k1) (M'⟨rlift ↑⟩[lsingle (tmInl k1 k1' A'⟨↑⟩ B'⟨↑⟩ (var 0))]) c1') ->
  LRtmM (lvsubst l2 φ) G' Θ
    (mott (wrapMt MtL) k'' (ΔL ,, B @ k') (M⟨rlift ↑⟩[lsingle (tmInr k k' A⟨↑⟩ B⟨↑⟩ (var 0))]) (boxt c2))
    (mott (wrapMt MtR) k1'' (ΔR ,, B' @ k1') (M'⟨rlift ↑⟩[lsingle (tmInr k1 k1' A'⟨↑⟩ B'⟨↑⟩ (var 0))]) (boxt c2'))
    (rectL k'' (ΔL ,, B @ k') (M⟨rlift ↑⟩[lsingle (tmInr k k' A⟨↑⟩ B⟨↑⟩ (var 0))]) c2)
    (rectR k1'' (ΔR ,, B' @ k1') (M'⟨rlift ↑⟩[lsingle (tmInr k1 k1' A'⟨↑⟩ B'⟨↑⟩ (var 0))]) c2') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lmax k k') ΔL (tySum k k' A B) (boxt t))
    (mott (wrapMt MtR) (lmax k1 k1') ΔR (tySum k1 k1' A' B') (boxt t'))
    (rectL (lmax k k') ΔL (tySum k k' A B) t) (rectR (lmax k1 k1') ΔR (tySum k1 k1' A' B') t') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmCase k k' k'' A B M c1 c2 t)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmCase k1 k1' k1'' A' B' M' c1' c2' t')))
    (rectL kL ΔL TL (tmCase k k' k'' A B M c1 c2 t)) (rectR kR ΔR TR (tmCase k1 k1' k1'' A' B' M' c1' c2' t')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw' Hw'' Hw1 Hw1' Hw1'' E E' E'' HTL HTR HA HA' EA HB HB' EB HM HM' EM1
    Hc1 Hc1' Ec1 Hc2 Hc2' Ec2 Ht Ht' Et IHA IHB IHM IHc1 IHc2 IHt.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Q' : lequiv L' k' k1') by exact (leqv_lequiv _ _ _ Hw' Hw1' E').
  assert (Q'' : lequiv L' k'' k1'') by exact (leqv_lequiv _ _ _ Hw'' Hw1'' E'').
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q).
  assert (Qg' : lequiv (gL G') k' k1') by (rewrite EL; exact Q').
  assert (Qg'' : lequiv (gL G') k'' k1'') by (rewrite EL; exact Q'').
  assert (Qk : lequiv (gL G') k k) by (rewrite EL; exact (lequiv_refl _ _ Hw)).
  assert (Qk' : lequiv (gL G') k' k') by (rewrite EL; exact (lequiv_refl _ _ Hw')).
  assert (Qm : lequiv L' (lmax k k') (lmax k1 k1')) by (apply lequiv_max; assumption).
  assert (Qmg : lequiv (gL G') (lmax k k') (lmax k1 k1')) by (rewrite EL; exact Qm).
  assert (Hwm : lwf L' (lmax k k')) by (cbn; auto).
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1)).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  (* the summands and their calls *)
  destruct (Tcall HΔL HΔ Hw Q HA HA' EA IHA) as (HAA & HA'R & HA'R1 & CA & CA1 & X1).
  destruct (Tcall HΔL HΔ Hw' Q' HB HB' EB IHB) as (HBB & HB'R & HB'R1 & CB & CB1 & X2).
  pose proof (lift_ty (j := lD) HA Hl1c) as HAD. pose proof (lift_ty (j := lD) HA' Hl1c) as HA'D.
  pose proof (lift_ty (j := lD) HB Hl1c) as HBD. pose proof (lift_ty (j := lD) HB' Hl1c) as HB'D.
  (* the sum, and the motive over it *)
  assert (HSD : [ G' ; ΔL ⊢[ lD ] tySum k k' A B @ lmax k k' ])
    by (apply wft_sum; [discriminate | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HAD | exact HBD]).
  assert (HSS : [ G' ; ΔL ⊢[ lD ] tySum k k' A B ≅ tySum k1 k1' A' B' @ lmax k k' ])
    by (apply eqty_sum; [discriminate | exact Qg | exact Qg' | exact HAA | exact HBB]).
  assert (HSS0 : [ G' ; ΔL ⊢[ lD ] tySum k k' A B ≅ tySum k k' A' B' @ lmax k k' ])
    by (apply eqty_sum; [discriminate | exact Qk | exact Qk' | exact HAA | exact HBB]).
  assert (CS : [ G' ⊢[ lD ] ΔL ,, tySum k k' A B @ lmax k k' ≅ ΔR ,, tySum k k' A' B' @ lmax k k' ])
    by (apply eqc_ext; [exact HΔ | exact HSD | exact HSS0 | rewrite EL; exact (lequiv_refl _ _ Hwm)]).
  assert (CS1 : [ G' ⊢[ lD ] ΔL ,, tySum k k' A B @ lmax k k' ≅ ΔR ,, tySum k1 k1' A' B' @ lmax k1 k1' ])
    by (apply eqc_ext; [exact HΔ | exact HSD | exact HSS | exact Qmg]).
  pose proof (eqctx_wf_l (i := lD) eq_refl CS) as HΔS.
  destruct (Tcall HΔS CS1 Hw'' Q'' HM HM' EM1 IHM) as (HMM & _ & HM'R1 & _ & _ & X3).
  pose proof (ctxconv_ty CS (i := lC) eq_refl HM') as HM'R.
  pose proof (lift_ty (j := lD) HM Hl1c) as HMD. pose proof (lift_ty (j := lD) HM' Hl1c) as HM'D.
  (* the branches' types *)
  destruct (case_facts_D Qg Qg' HAD HAA HA'D HBD HBB HB'D HMD HMM HM'D) as (_ & CAf & CBf & EC1 & EC2).
  destruct (case_facts_D Qk Qk' HAD HAA HA'D HBD HBB HB'D HMD HMM HM'D) as (_ & CAf0 & CBf0 & EC10 & EC20).
  pose proof (ctxconv_eqty (eqctx_sym_D CAf) (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ EC1)) as HC1.
  pose proof (ctxconv_eqty (eqctx_sym_D CBf) (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ EC2)) as HC2.
  pose proof (eqctx_wf_l (i := lD) eq_refl CA) as HΔA. pose proof (eqctx_wf_l (i := lD) eq_refl CB) as HΔB.
  destruct (tcall HΔA CA1 Hw'' Q'' HC1 Hc1 Hc1' Ec1 IHc1) as (Hcc1 & _ & Hc1'R1 & _ & X4).
  destruct (tcall HΔB CB1 Hw'' Q'' HC2 Hc2 Hc2' Ec2 IHc2) as (Hcc2 & _ & Hc2'R1 & _ & X5).
  (* the scrutinee and its call *)
  destruct (tcall HΔL HΔ Hwm Qm HSS Ht Ht' Et IHt) as (Htt & _ & Ht'R1 & _ & X6).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHA) IHA) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHB) IHB) Hl1g') as X2r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHM) IHM) Hl1g') as X3r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHc1) IHc1) Hl2g') as X4r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHc2) IHc2) Hl2g') as X5r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHt) IHt) Hl2g') as X6r.
  (* the right pieces at the left levels *)
  assert (Hc1'R : [ G' ; ΔR ,, A' @ k ⊢[ lC ] c1' : M'⟨rlift ↑⟩[lsingle (tmInl k k' A'⟨↑⟩ B'⟨↑⟩ (var 0))] @ k'' ]).
  { eapply wf_conv; [exact (ctxconv_tm CA (i := lC) eq_refl Hc1') |].
    exact (ctxconv_eqty CA (i := lD) eq_refl (ctxconv_eqty (eqctx_sym_D CAf0) (i := lD) eq_refl EC10)). }
  assert (Hc2'R : [ G' ; ΔR ,, B' @ k' ⊢[ lC ] c2' : M'⟨rlift ↑⟩[lsingle (tmInr k k' A'⟨↑⟩ B'⟨↑⟩ (var 0))] @ k'' ]).
  { eapply wf_conv; [exact (ctxconv_tm CB (i := lC) eq_refl Hc2') |].
    exact (ctxconv_eqty CB (i := lD) eq_refl (ctxconv_eqty (eqctx_sym_D CBf0) (i := lD) eq_refl EC20)). }
  assert (Ht'R : [ G' ; ΔR ⊢[ lC ] t' : tySum k k' A' B' @ lmax k k' ]).
  { eapply wf_conv; [exact (ctxconv_tm HΔ (i := lC) eq_refl Ht') |].
    exact (ctxconv_eqty HΔ (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ HSS0)). }
  (* the result types *)
  assert (Hr1 : [ G' ; ΔL ⊢[ lD ] M[lsingle t] ≅ M'[lsingle t'] @ k'' ])
    by exact (eqty_subst_single_D HMM HM'D Htt (lift_tm (j := lD) Ht Hl1c) (lift_tm (j := lD) Ht' Hl1c)).
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] tmCase k k' k'' A B M c1 c2 t : M[lsingle t] @ k'' ])
    by (apply wf_case; [exact Hn | rewrite EL; exact Hw | rewrite EL; exact Hw' | rewrite EL; exact Hw''
                       | exact HA | exact HB | exact HM | exact Hc1 | exact Hc2 | exact Ht]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmCase k1 k1' k1'' A' B' M' c1' c2' t' : M'[lsingle t'] @ k1'' ])
    by (apply wf_case; [exact Hn | rewrite EL; exact Hw1 | rewrite EL; exact Hw1' | rewrite EL; exact Hw1''
                       | exact HA'R1 | exact HB'R1 | exact HM'R1 | exact Hc1'R1 | exact Hc2'R1 | exact Ht'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tmCase k1 k1' k1'' A' B' M' c1' c2' t' : M[lsingle t] @ k'' ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qg'']
                    | exact Hr1]. }
  assert (Ecc : tm_leq (tmCase k k' k'' A B M c1 c2 t) (tmCase k1 k1' k1'' A' B' M' c1' c2' t'))
    by (cbn; repeat split; assumption).
  pose proof (lift_ty (j := lD) HA'R1 Hl1c) as HA'R1D. pose proof (lift_ty (j := lD) HB'R1 Hl1c) as HB'R1D.
  pose proof (lift_ty (j := lD) HM'R1 Hl1c) as HM'R1D.
  refine (rec_t_br 38 (k :: k' :: k'' :: nil) (k1 :: k1' :: k1'' :: nil)
            (GCtx ΔL :: GTy A :: GTy B :: GTy M :: GTm c1 :: GTm c2 :: GTm t :: nil)
            (GCtx ΔR :: GTy A' :: GTy B' :: GTy M' :: GTm c1' :: GTm c2' :: GTm t' :: nil)
            (recTL k ΔL A :: recTL k' ΔL B :: recTL k'' (ΔL ,, tySum k k' A B @ lmax k k') M
             :: rectL k'' (ΔL ,, A @ k) (M⟨rlift ↑⟩[lsingle (tmInl k k' A⟨↑⟩ B⟨↑⟩ (var 0))]) c1
             :: rectL k'' (ΔL ,, B @ k') (M⟨rlift ↑⟩[lsingle (tmInr k k' A⟨↑⟩ B⟨↑⟩ (var 0))]) c2
             :: rectL (lmax k k') ΔL (tySum k k' A B) t :: nil)
            (recTR k1 ΔR A' :: recTR k1' ΔR B' :: recTR k1'' (ΔR ,, tySum k1 k1' A' B' @ lmax k1 k1') M'
             :: rectR k1'' (ΔR ,, A' @ k1) (M'⟨rlift ↑⟩[lsingle (tmInl k1 k1' A'⟨↑⟩ B'⟨↑⟩ (var 0))]) c1'
             :: rectR k1'' (ΔR ,, B' @ k1') (M'⟨rlift ↑⟩[lsingle (tmInr k1 k1' A'⟨↑⟩ B'⟨↑⟩ (var 0))]) c2'
             :: rectR (lmax k1 k1') ΔR (tySum k1 k1' A' B') t' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_cons _ _ E' (Forall2_cons _ _ E'' (Forall2_nil _)))))
            HΔL HΔ HkL HkR Q'' HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl Hr1) HcL0 HcRL HcR0 Ecc
            (GS_case EP EM Hσ HΔL HΔ HA HA'R HAA EA HB HB'R HBB EB HM HM'R HMM EM1
               Hc1 Hc1'R Hcc1 Ec1 Hc2 Hc2'R Hcc2 Ec2 Ht Ht'R Htt Et)
            (GS_case EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR)
               HA'R1 HA'R1 (eqty_refl _ _ _ _ _ HA'R1D) (ty_leq_refl _)
               HB'R1 HB'R1 (eqty_refl _ _ _ _ _ HB'R1D) (ty_leq_refl _)
               HM'R1 HM'R1 (eqty_refl _ _ _ _ _ HM'R1D) (ty_leq_refl _)
               Hc1'R1 Hc1'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hc1'R1 Hl1c)) (tm_leq_refl _)
               Hc2'R1 Hc2'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hc2'R1 Hl1c)) (tm_leq_refl _)
               Ht'R1 Ht'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ht'R1 Hl1c)) (tm_leq_refl _))
            _ _ _ _ _ _ _).
  - sr_ctx; J_cbn; rewrite ?liftshift_cons_ty'; [exact X1 | exact X2 | exact X3 | exact X4 | exact X5 | exact X6].
  - sr_ctx; J_cbn; rewrite ?liftshift_cons_ty'; [exact X1r | exact X2r | exact X3r | exact X4r | exact X5r | exact X6r].
  - J_res.
  - J_res.
  - J_res.
  - apply redt_case_inst; inst_side 38.
  - apply redt_case_inst; inst_side 38.
Qed.

End Rec.
