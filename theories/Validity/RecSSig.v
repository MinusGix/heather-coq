(** * The recursion lemmas on code: Σ and [W]: pairs, projections and [sup]

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

(** ** The Σ eliminations and introduction (M8d) *)

Lemma rec_t_pair {ΔL ΔR kL kR TL TR k k' k1 k1' A B A' B' a a' b b'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lmax k k') kL -> lequiv L' (lmax k k') kR -> lwf L' k -> lwf L' k' -> lwf L' k1 -> lwf L' k1' ->
  leqv k k1 -> leqv k' k1' ->
  [ G' ; ΔL ⊢[ lD ] tySig k k' A B ≅ TL @ lmax k k' ] -> [ G' ; ΔL ⊢[ lD ] tySig k k' A B ≅ TR @ lmax k k' ] ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] A' @ k ] -> ty_leq A A' ->
  [ G' ; ΔL ,, A @ k ⊢[ lC ] B @ k' ] -> [ G' ; ΔL ,, A @ k ⊢[ lC ] B' @ k' ] -> ty_leq B B' ->
  [ G' ; ΔL ⊢[ lC ] a : A @ k ] -> [ G' ; ΔL ⊢[ lC ] a' : A @ k ] -> tm_leq a a' ->
  [ G' ; ΔL ⊢[ lC ] b : B[lsingle a] @ k' ] -> [ G' ; ΔL ⊢[ lC ] b' : B[lsingle a] @ k' ] -> tm_leq b b' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k' (ΔL ,, A @ k) (boxT B)) (motT (wrapMT MTR) k1' (ΔR ,, A' @ k1) (boxT B'))
    (recTL k' (ΔL ,, A @ k) B) (recTR k1' (ΔR ,, A' @ k1) B') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL A (boxt a)) (mott (wrapMt MtR) k1 ΔR A' (boxt a'))
    (rectL k ΔL A a) (rectR k1 ΔR A' a') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k' ΔL (B[lsingle a]) (boxt b)) (mott (wrapMt MtR) k1' ΔR (B'[lsingle a']) (boxt b'))
    (rectL k' ΔL (B[lsingle a]) b) (rectR k1' ΔR (B'[lsingle a']) b') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmPair k k' A B a b)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmPair k1 k1' A' B' a' b')))
    (rectL kL ΔL TL (tmPair k k' A B a b)) (rectR kR ΔR TR (tmPair k1 k1' A' B' a' b')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw' Hw1 Hw1' E E' HTL HTR HA HA' EA HB HB' EB Ha Ha' Ea Hb Hb' Eb IHA IHB IHa IHb.
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
  assert (HPP : [ G' ; ΔL ⊢[ lD ] tySig k k' A B ≅ tySig k1 k1' A' B' @ lmax k k' ])
    by (apply eqty_sig; [discriminate | exact Qg | exact Qg' | exact (lift_ty (j := lD) HA Hl1c) | exact HAA | exact HBB]).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHA) IHA) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHB) IHB) Hl1g') as X2r.
  (* the components and their calls *)
  destruct (tcall HΔL HΔ Hw Q HAA Ha Ha' Ea IHa) as (Haa & Ha'R & Ha'R1 & _ & X3).
  assert (HBa : [ G' ; ΔL ⊢[ lD ] B[lsingle a] ≅ B'[lsingle a'] @ k' ])
    by exact (eqty_subst_single_D HBB (lift_ty (j := lD) HB' Hl1c) Haa (lift_tm (j := lD) Ha Hl1c) (lift_tm (j := lD) Ha' Hl1c)).
  destruct (tcall HΔL HΔ Hw' Q' HBa Hb Hb' Eb IHb) as (Hbb & Hb'R & Hb'R1 & _ & X4).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHa) IHa) Hl2g') as X3r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHb) IHb) Hl2g') as X4r.
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] tmPair k k' A B a b : tySig k k' A B @ lmax k k' ])
    by (apply wf_pair; [exact Hn | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HA | exact HB | exact Ha | exact Hb]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmPair k1 k1' A' B' a' b' : tySig k1 k1' A' B' @ lmax k1 k1' ])
    by (apply wf_pair; [exact Hn | rewrite EL; exact Hw1 | rewrite EL; exact Hw1' | exact HA'R1 | exact HB'R1
                       | exact Ha'R1 | exact Hb'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tmPair k1 k1' A' B' a' b' : tySig k k' A B @ lmax k k' ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qmg] | exact HPP]. }
  assert (Ec : tm_leq (tmPair k k' A B a b) (tmPair k1 k1' A' B' a' b')) by (cbn; repeat split; assumption).
  set (xsL := recTL k ΔL A :: recTL k' (ΔL ,, A @ k) B :: rectL k ΔL A a :: rectL k' ΔL (B[lsingle a]) b :: nil).
  set (xsR := recTR k1 ΔR A' :: recTR k1' (ΔR ,, A' @ k1) B' :: rectR k1 ΔR A' a' :: rectR k1' ΔR (B'[lsingle a']) b' :: nil).
  refine (rec_t_br 16 (k :: k' :: nil) (k1 :: k1' :: nil) (GCtx ΔL :: GTy A :: GTy B :: GTm a :: GTm b :: nil)
            (GCtx ΔR :: GTy A' :: GTy B' :: GTm a' :: GTm b' :: nil) xsL xsR ltac:(cbv; lia) eq_refl eq_refl eq_refl
            ltac:(repeat constructor; assumption) ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_cons _ _ E' (Forall2_nil _))))
            HΔL HΔ HkL HkR Qm HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl HPP) HcL0 HcRL HcR0 Ec
            (GS_pair EP EM Hσ HΔL HΔ HA HA'R HAA EA HB HB'R HBB EB Ha Ha'R Haa Ea Hb Hb'R Hbb Eb)
            (GS_pair EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HA'R1 HA'R1
               (eqty_refl _ _ _ _ _ HA'R1D) (ty_leq_refl _) HB'R1 HB'R1 (eqty_refl _ _ _ _ _ HB'R1D) (ty_leq_refl _)
               Ha'R1 Ha'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ha'R1 Hl1c)) (tm_leq_refl _)
               Hb'R1 Hb'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hb'R1 Hl1c)) (tm_leq_refl _)) _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2 | exact X3 | exact X4].
  - sr_ctx; [exact X1r | exact X2r | exact X3r | exact X4r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_pair_inst; inst_side 16.
  - apply redt_pair_inst; inst_side 16.
Qed.

(** [sup] (branch 41): the children's call at their [Π] type over the shape. *)
Lemma rec_t_sup {ΔL ΔR kL kR TL TR k k' k1 k1' A B A' B' a a' f f'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lmax k k') kL -> lequiv L' (lmax k k') kR -> lwf L' k -> lwf L' k' -> lwf L' k1 -> lwf L' k1' ->
  leqv k k1 -> leqv k' k1' ->
  [ G' ; ΔL ⊢[ lD ] tyW k k' A B ≅ TL @ lmax k k' ] -> [ G' ; ΔL ⊢[ lD ] tyW k k' A B ≅ TR @ lmax k k' ] ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] A' @ k ] -> ty_leq A A' ->
  [ G' ; ΔL ,, A @ k ⊢[ lC ] B @ k' ] -> [ G' ; ΔL ,, A @ k ⊢[ lC ] B' @ k' ] -> ty_leq B B' ->
  [ G' ; ΔL ⊢[ lC ] a : A @ k ] -> [ G' ; ΔL ⊢[ lC ] a' : A @ k ] -> tm_leq a a' ->
  [ G' ; ΔL ⊢[ lC ] f : tyPi k' (lmax k k') B[lsingle a] (tyW k k' A B)⟨↑⟩ @ lmax k' (lmax k k') ] ->
  [ G' ; ΔL ⊢[ lC ] f' : tyPi k' (lmax k k') B[lsingle a] (tyW k k' A B)⟨↑⟩ @ lmax k' (lmax k k') ] -> tm_leq f f' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k' (ΔL ,, A @ k) (boxT B)) (motT (wrapMT MTR) k1' (ΔR ,, A' @ k1) (boxT B'))
    (recTL k' (ΔL ,, A @ k) B) (recTR k1' (ΔR ,, A' @ k1) B') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k ΔL A (boxt a)) (mott (wrapMt MtR) k1 ΔR A' (boxt a'))
    (rectL k ΔL A a) (rectR k1 ΔR A' a') ->
  LRtmM (lvsubst l2 φ) G' Θ
    (mott (wrapMt MtL) (lmax k' (lmax k k')) ΔL (tyPi k' (lmax k k') B[lsingle a] (tyW k k' A B)⟨↑⟩) (boxt f))
    (mott (wrapMt MtR) (lmax k1' (lmax k1 k1')) ΔR (tyPi k1' (lmax k1 k1') B'[lsingle a'] (tyW k1 k1' A' B')⟨↑⟩) (boxt f'))
    (rectL (lmax k' (lmax k k')) ΔL (tyPi k' (lmax k k') B[lsingle a] (tyW k k' A B)⟨↑⟩) f)
    (rectR (lmax k1' (lmax k1 k1')) ΔR (tyPi k1' (lmax k1 k1') B'[lsingle a'] (tyW k1 k1' A' B')⟨↑⟩) f') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmSup k k' A B a f)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmSup k1 k1' A' B' a' f')))
    (rectL kL ΔL TL (tmSup k k' A B a f)) (rectR kR ΔR TR (tmSup k1 k1' A' B' a' f')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw' Hw1 Hw1' E E' HTL HTR HA HA' EA HB HB' EB Ha Ha' Ea Hf Hf' Ef IHA IHB IHa IHf.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Q' : lequiv L' k' k1') by exact (leqv_lequiv _ _ _ Hw' Hw1' E').
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q). assert (Qg' : lequiv (gL G') k' k1') by (rewrite EL; exact Q').
  assert (Qm : lequiv L' (lmax k k') (lmax k1 k1')) by (apply lequiv_max; assumption).
  assert (Qmg : lequiv (gL G') (lmax k k') (lmax k1 k1')) by (rewrite EL; exact Qm).
  assert (Qf : lequiv L' (lmax k' (lmax k k')) (lmax k1' (lmax k1 k1'))) by (apply lequiv_max; assumption).
  assert (Hwf : lwf L' (lmax k' (lmax k k'))) by (cbn; auto).
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1)).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  (* the pieces and their calls *)
  destruct (Tcall HΔL HΔ Hw Q HA HA' EA IHA) as (HAA & HA'R & HA'R1 & CA & CA1 & X1).
  destruct (Tcall (eqctx_wf_l (i := lD) eq_refl CA) CA1 Hw' Q' HB HB' EB IHB) as (HBB & _ & HB'R1 & _ & _ & X2).
  pose proof (ctxconv_ty CA (i := lC) eq_refl HB') as HB'R.
  pose proof (lift_ty (j := lD) HA'R1 Hl1c) as HA'R1D. pose proof (lift_ty (j := lD) HB'R1 Hl1c) as HB'R1D.
  assert (HWW : [ G' ; ΔL ⊢[ lD ] tyW k k' A B ≅ tyW k1 k1' A' B' @ lmax k k' ])
    by (apply eqty_W; [discriminate | exact Qg | exact Qg' | exact (lift_ty (j := lD) HA Hl1c) | exact HAA | exact HBB]).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHA) IHA) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHB) IHB) Hl1g') as X2r.
  (* the components and their calls *)
  destruct (tcall HΔL HΔ Hw Q HAA Ha Ha' Ea IHa) as (Haa & Ha'R & Ha'R1 & _ & X3).
  pose proof (@W_sup_feq G' lD eq_refl ltac:(discriminate) _ _ _ _ _ _ _ _ _ _ _ Qg Qg' (lift_ty (j := lD) HA Hl1c) HAA
                (lift_ty (j := lD) HB Hl1c) HBB Haa (lift_tm (j := lD) Ha Hl1c) (lift_tm (j := lD) Ha' Hl1c)) as HFF.
  destruct (tcall HΔL HΔ Hwf Qf HFF Hf Hf' Ef IHf) as (Hff & _ & Hf'R1 & _ & X4).
  assert (Qk : lequiv (gL G') k k) by (rewrite EL; exact (lequiv_refl _ _ Hw)).
  assert (Qk' : lequiv (gL G') k' k') by (rewrite EL; exact (lequiv_refl _ _ Hw')).
  pose proof (@W_sup_feq G' lD eq_refl ltac:(discriminate) _ _ _ _ _ _ _ _ _ _ _ Qk Qk' (lift_ty (j := lD) HA Hl1c) HAA
                (lift_ty (j := lD) HB Hl1c) HBB Haa (lift_tm (j := lD) Ha Hl1c) (lift_tm (j := lD) Ha' Hl1c)) as HFF0.
  assert (Hf'R : [ G' ; ΔR ⊢[ lC ] f' : tyPi k' (lmax k k') B'[lsingle a'] (tyW k k' A' B')⟨↑⟩ @ lmax k' (lmax k k') ]).
  { eapply wf_conv; [exact (ctxconv_tm HΔ (i := lC) eq_refl Hf') |].
    exact (ctxconv_eqty HΔ (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ HFF0)). }
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHa) IHa) Hl2g') as X3r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHf) IHf) Hl2g') as X4r.
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] tmSup k k' A B a f : tyW k k' A B @ lmax k k' ])
    by (apply wf_sup; [exact Hn | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HA | exact HB | exact Ha | exact Hf]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmSup k1 k1' A' B' a' f' : tyW k1 k1' A' B' @ lmax k1 k1' ])
    by (apply wf_sup; [exact Hn | rewrite EL; exact Hw1 | rewrite EL; exact Hw1' | exact HA'R1 | exact HB'R1
                      | exact Ha'R1 | exact Hf'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tmSup k1 k1' A' B' a' f' : tyW k k' A B @ lmax k k' ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qmg] | exact HWW]. }
  assert (Ec : tm_leq (tmSup k k' A B a f) (tmSup k1 k1' A' B' a' f')) by (cbn; repeat split; assumption).
  set (xsL := recTL k ΔL A :: recTL k' (ΔL ,, A @ k) B :: rectL k ΔL A a
                :: rectL (lmax k' (lmax k k')) ΔL (tyPi k' (lmax k k') B[lsingle a] (tyW k k' A B)⟨↑⟩) f :: nil).
  set (xsR := recTR k1 ΔR A' :: recTR k1' (ΔR ,, A' @ k1) B' :: rectR k1 ΔR A' a'
                :: rectR (lmax k1' (lmax k1 k1')) ΔR (tyPi k1' (lmax k1 k1') B'[lsingle a'] (tyW k1 k1' A' B')⟨↑⟩) f' :: nil).
  refine (rec_t_br 41 (k :: k' :: nil) (k1 :: k1' :: nil) (GCtx ΔL :: GTy A :: GTy B :: GTm a :: GTm f :: nil)
            (GCtx ΔR :: GTy A' :: GTy B' :: GTm a' :: GTm f' :: nil) xsL xsR ltac:(cbv; lia) eq_refl eq_refl eq_refl
            ltac:(repeat constructor; assumption) ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_cons _ _ E' (Forall2_nil _))))
            HΔL HΔ HkL HkR Qm HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl HWW) HcL0 HcRL HcR0 Ec
            (GS_sup EP EM Hσ HΔL HΔ HA HA'R HAA EA HB HB'R HBB EB Ha Ha'R Haa Ea Hf Hf'R Hff Ef)
            (GS_sup EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HA'R1 HA'R1
               (eqty_refl _ _ _ _ _ HA'R1D) (ty_leq_refl _) HB'R1 HB'R1 (eqty_refl _ _ _ _ _ HB'R1D) (ty_leq_refl _)
               Ha'R1 Ha'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ha'R1 Hl1c)) (tm_leq_refl _)
               Hf'R1 Hf'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hf'R1 Hl1c)) (tm_leq_refl _)) _ _ _ _ _ _ _).
  - sr_ctx; W_cbn; [exact X1 | exact X2 | exact X3 | exact X4].
  - sr_ctx; W_cbn; [exact X1r | exact X2r | exact X3r | exact X4r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_sup_inst; inst_side 41.
  - apply redt_sup_inst; inst_side 41.
Qed.

(** The projections' common part: the pieces, the pair's call, and the
    first projections on both sides. *)
Ltac rec_t_proj_pre ΔL ΔR k k' k1 k1' A B A' B' p p' :=
  intros HΔL HΔ HkL HkR Hw Hw' Hw1 Hw1' E E' HTL HTR HA HA' EA HB HB' EB Hp Hp' Ep IHA IHB IHp;
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR;
  assert (Hn : lC <> lV) by discriminate;
  assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia);
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E);
  assert (Q' : lequiv L' k' k1') by exact (leqv_lequiv _ _ _ Hw' Hw1' E');
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q);
  assert (Qg' : lequiv (gL G') k' k1') by (rewrite EL; exact Q');
  assert (Qm : lequiv L' (lmax k k') (lmax k1 k1')) by (apply lequiv_max; assumption);
  assert (Qmg : lequiv (gL G') (lmax k k') (lmax k1 k1')) by (rewrite EL; exact Qm);
  assert (Hwm : lwf L' (lmax k k')) by (cbn; auto);
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1));
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2));
  destruct (Tcall HΔL HΔ Hw Q HA HA' EA IHA) as (HAA & HA'R & HA'R1 & CA & CA1 & X1);
  destruct (Tcall (eqctx_wf_l (i := lD) eq_refl CA) CA1 Hw' Q' HB HB' EB IHB) as (HBB & _ & HB'R1 & _ & _ & X2);
  pose proof (ctxconv_ty CA (i := lC) eq_refl HB') as HB'R;
  pose proof (lift_ty (j := lD) HA'R1 Hl1c) as HA'R1D;
  pose proof (lift_ty (j := lD) HB'R1 Hl1c) as HB'R1D;
  assert (HPP : [ G' ; ΔL ⊢[ lD ] tySig k k' A B ≅ tySig k1 k1' A' B' @ lmax k k' ])
    by (apply eqty_sig; [discriminate | exact Qg | exact Qg' | exact (lift_ty (j := lD) HA Hl1c) | exact HAA | exact HBB]);
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHA) IHA) Hl1g') as X1r;
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHB) IHB) Hl1g') as X2r;
  destruct (tcall HΔL HΔ Hwm Qm HPP Hp Hp' Ep IHp) as (Hpp & Hp'R0 & Hp'R1 & _ & X3);
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHp) IHp) Hl2g') as X3r;
  assert (Hp'R : [ G' ; ΔR ⊢[ lC ] p' : tySig k k' A' B' @ lmax k k' ])
    by (eapply wf_conv; [exact Hp'R0 |];
        apply eqty_sig; [discriminate | exact Qg | exact Qg' | exact (lift_ty (j := lD) HA'R Hl1c)
                        | apply eqty_refl, (lift_ty (j := lD) HA'R Hl1c) | apply eqty_refl, (lift_ty (j := lD) HB'R Hl1c)]);
  assert (HfL0 : [ G' ; ΔL ⊢[ lC ] tmFst k k' A B p : A @ k ])
    by (apply wf_fst; [exact Hn | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HA | exact HB | exact Hp]);
  assert (HfR0 : [ G' ; ΔR ⊢[ lC ] tmFst k1 k1' A' B' p' : A' @ k1 ])
    by (apply wf_fst; [exact Hn | rewrite EL; exact Hw1 | rewrite EL; exact Hw1' | exact HA'R1 | exact HB'R1 | exact Hp'R1]);
  assert (HfRL : [ G' ; ΔL ⊢[ lC ] tmFst k1 k1' A' B' p' : A @ k ])
    by (eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HfR0) | exact Qg] | exact HAA]);
  assert (Ef : tm_leq (tmFst k k' A B p) (tmFst k1 k1' A' B' p')) by (cbn; repeat split; assumption).

Lemma rec_t_fst {ΔL ΔR kL kR TL TR k k' k1 k1' A B A' B' p p'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k kL -> lequiv L' k kR -> lwf L' k -> lwf L' k' -> lwf L' k1 -> lwf L' k1' -> leqv k k1 -> leqv k' k1' ->
  [ G' ; ΔL ⊢[ lD ] A ≅ TL @ k ] -> [ G' ; ΔL ⊢[ lD ] A ≅ TR @ k ] ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] A' @ k ] -> ty_leq A A' ->
  [ G' ; ΔL ,, A @ k ⊢[ lC ] B @ k' ] -> [ G' ; ΔL ,, A @ k ⊢[ lC ] B' @ k' ] -> ty_leq B B' ->
  [ G' ; ΔL ⊢[ lC ] p : tySig k k' A B @ lmax k k' ] -> [ G' ; ΔL ⊢[ lC ] p' : tySig k k' A B @ lmax k k' ] -> tm_leq p p' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k' (ΔL ,, A @ k) (boxT B)) (motT (wrapMT MTR) k1' (ΔR ,, A' @ k1) (boxT B'))
    (recTL k' (ΔL ,, A @ k) B) (recTR k1' (ΔR ,, A' @ k1) B') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lmax k k') ΔL (tySig k k' A B) (boxt p))
    (mott (wrapMt MtR) (lmax k1 k1') ΔR (tySig k1 k1' A' B') (boxt p'))
    (rectL (lmax k k') ΔL (tySig k k' A B) p) (rectR (lmax k1 k1') ΔR (tySig k1 k1' A' B') p') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmFst k k' A B p)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmFst k1 k1' A' B' p')))
    (rectL kL ΔL TL (tmFst k k' A B p)) (rectR kR ΔR TR (tmFst k1 k1' A' B' p')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  rec_t_proj_pre ΔL ΔR k k' k1 k1' A B A' B' p p'.
  pose proof HfL0 as HcL0. pose proof HfR0 as HcR0. pose proof HfRL as HcRL. pose proof Ef as Ec.
  set (xsL := recTL k ΔL A :: recTL k' (ΔL ,, A @ k) B :: rectL (lmax k k') ΔL (tySig k k' A B) p :: nil).
  set (xsR := recTR k1 ΔR A' :: recTR k1' (ΔR ,, A' @ k1) B' :: rectR (lmax k1 k1') ΔR (tySig k1 k1' A' B') p' :: nil).
  refine (rec_t_br 17 (k :: k' :: nil) (k1 :: k1' :: nil) (GCtx ΔL :: GTy A :: GTy B :: GTm p :: nil)
            (GCtx ΔR :: GTy A' :: GTy B' :: GTm p' :: nil) xsL xsR ltac:(cbv; lia) eq_refl eq_refl eq_refl
            ltac:(repeat constructor; assumption) ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_cons _ _ E' (Forall2_nil _))))
            HΔL HΔ HkL HkR Q HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl HAA) HcL0 HcRL HcR0 Ec
            (GS_fst EP EM 17 eq_refl eq_refl Hσ HΔL HΔ HA HA'R HAA EA HB HB'R HBB EB Hp Hp'R Hpp Ep)
            (GS_fst EP EM 17 eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HA'R1 HA'R1
               (eqty_refl _ _ _ _ _ HA'R1D) (ty_leq_refl _) HB'R1 HB'R1 (eqty_refl _ _ _ _ _ HB'R1D) (ty_leq_refl _)
               Hp'R1 Hp'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hp'R1 Hl1c)) (tm_leq_refl _)) _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2 | exact X3].
  - sr_ctx; [exact X1r | exact X2r | exact X3r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_fst_inst; inst_side 17.
  - apply redt_fst_inst; inst_side 17.
Qed.

Lemma rec_t_snd {ΔL ΔR kL kR TL TR k k' k1 k1' A B A' B' p p'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k' kL -> lequiv L' k' kR -> lwf L' k -> lwf L' k' -> lwf L' k1 -> lwf L' k1' -> leqv k k1 -> leqv k' k1' ->
  [ G' ; ΔL ⊢[ lD ] B[lsingle (tmFst k k' A B p)] ≅ TL @ k' ] -> [ G' ; ΔL ⊢[ lD ] B[lsingle (tmFst k k' A B p)] ≅ TR @ k' ] ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] A' @ k ] -> ty_leq A A' ->
  [ G' ; ΔL ,, A @ k ⊢[ lC ] B @ k' ] -> [ G' ; ΔL ,, A @ k ⊢[ lC ] B' @ k' ] -> ty_leq B B' ->
  [ G' ; ΔL ⊢[ lC ] p : tySig k k' A B @ lmax k k' ] -> [ G' ; ΔL ⊢[ lC ] p' : tySig k k' A B @ lmax k k' ] -> tm_leq p p' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k' (ΔL ,, A @ k) (boxT B)) (motT (wrapMT MTR) k1' (ΔR ,, A' @ k1) (boxT B'))
    (recTL k' (ΔL ,, A @ k) B) (recTR k1' (ΔR ,, A' @ k1) B') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lmax k k') ΔL (tySig k k' A B) (boxt p))
    (mott (wrapMt MtR) (lmax k1 k1') ΔR (tySig k1 k1' A' B') (boxt p'))
    (rectL (lmax k k') ΔL (tySig k k' A B) p) (rectR (lmax k1 k1') ΔR (tySig k1 k1' A' B') p') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmSnd k k' A B p)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmSnd k1 k1' A' B' p')))
    (rectL kL ΔL TL (tmSnd k k' A B p)) (rectR kR ΔR TR (tmSnd k1 k1' A' B' p')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  rec_t_proj_pre ΔL ΔR k k' k1 k1' A B A' B' p p'.
  pose proof (lift_eqtm (j := lD) (static_code_tm Hl1c HfL0 HfRL Ef) Hl1c) as Hff.
  assert (HBf : [ G' ; ΔL ⊢[ lD ] B[lsingle (tmFst k k' A B p)] ≅ B'[lsingle (tmFst k1 k1' A' B' p')] @ k' ])
    by exact (eqty_subst_single_D HBB (lift_ty (j := lD) HB' Hl1c) Hff (lift_tm (j := lD) HfL0 Hl1c)
                (lift_tm (j := lD) HfRL Hl1c)).
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] tmSnd k k' A B p : B[lsingle (tmFst k k' A B p)] @ k' ])
    by (apply wf_snd; [exact Hn | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HA | exact HB | exact Hp]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmSnd k1 k1' A' B' p' : B'[lsingle (tmFst k1 k1' A' B' p')] @ k1' ])
    by (apply wf_snd; [exact Hn | rewrite EL; exact Hw1 | rewrite EL; exact Hw1' | exact HA'R1 | exact HB'R1 | exact Hp'R1]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tmSnd k1 k1' A' B' p' : B[lsingle (tmFst k k' A B p)] @ k' ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qg'] | exact HBf]. }
  assert (Ec : tm_leq (tmSnd k k' A B p) (tmSnd k1 k1' A' B' p')) by (cbn; repeat split; assumption).
  set (xsL := recTL k ΔL A :: recTL k' (ΔL ,, A @ k) B :: rectL (lmax k k') ΔL (tySig k k' A B) p :: nil).
  set (xsR := recTR k1 ΔR A' :: recTR k1' (ΔR ,, A' @ k1) B' :: rectR (lmax k1 k1') ΔR (tySig k1 k1' A' B') p' :: nil).
  refine (rec_t_br 18 (k :: k' :: nil) (k1 :: k1' :: nil) (GCtx ΔL :: GTy A :: GTy B :: GTm p :: nil)
            (GCtx ΔR :: GTy A' :: GTy B' :: GTm p' :: nil) xsL xsR ltac:(cbv; lia) eq_refl eq_refl eq_refl
            ltac:(repeat constructor; assumption) ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_cons _ _ E' (Forall2_nil _))))
            HΔL HΔ HkL HkR Q' HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl HBf) HcL0 HcRL HcR0 Ec
            (GS_fst EP EM 18 eq_refl eq_refl Hσ HΔL HΔ HA HA'R HAA EA HB HB'R HBB EB Hp Hp'R Hpp Ep)
            (GS_fst EP EM 18 eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HA'R1 HA'R1
               (eqty_refl _ _ _ _ _ HA'R1D) (ty_leq_refl _) HB'R1 HB'R1 (eqty_refl _ _ _ _ _ HB'R1D) (ty_leq_refl _)
               Hp'R1 Hp'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hp'R1 Hl1c)) (tm_leq_refl _)) _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2 | exact X3].
  - sr_ctx; [exact X1r | exact X2r | exact X3r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_snd_inst; inst_side 18.
  - apply redt_snd_inst; inst_side 18.
Qed.

End Rec.
