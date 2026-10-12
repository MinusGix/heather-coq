(** * The recursion lemmas on code: [elimW], vectors, [Fin] and variables

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

(** [elimW] (branch 42), as [case]: the step's telescope over the shape,
    read off [W_facts] at both sides' levels. *)
Lemma rec_t_elimW {ΔL ΔR kL kR TL TR k k' k'' k1 k1' k1'' A A' B B' M M' c c' t t'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k'' kL -> lequiv L' k'' kR -> lwf L' k -> lwf L' k' -> lwf L' k'' -> lwf L' k1 -> lwf L' k1' -> lwf L' k1'' ->
  leqv k k1 -> leqv k' k1' -> leqv k'' k1'' ->
  [ G' ; ΔL ⊢[ lD ] M[lsingle t] ≅ TL @ k'' ] -> [ G' ; ΔL ⊢[ lD ] M[lsingle t] ≅ TR @ k'' ] ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] A' @ k ] -> ty_leq A A' ->
  [ G' ; ΔL ,, A @ k ⊢[ lC ] B @ k' ] -> [ G' ; ΔL ,, A @ k ⊢[ lC ] B' @ k' ] -> ty_leq B B' ->
  [ G' ; ΔL ,, tyW k k' A B @ lmax k k' ⊢[ lC ] M @ k'' ] ->
  [ G' ; ΔL ,, tyW k k' A B @ lmax k k' ⊢[ lC ] M' @ k'' ] -> ty_leq M M' ->
  [ G' ; ΔL ,, A @ k ⊢[ lC ] wfty k k' A B @ lmax k' (lmax k k') ] ->
  [ G' ; ΔL ,, A @ k ,, wfty k k' A B @ lmax k' (lmax k k') ⊢[ lC ] wihty k k' k'' A B M @ lmax k' k'' ] ->
  [ G' ; ΔL ,, A @ k ,, wfty k k' A B @ lmax k' (lmax k k') ,, wihty k k' k'' A B M @ lmax k' k''
      ⊢[ lC ] c : wstepty k k' A B M @ k'' ] ->
  [ G' ; ΔL ,, A @ k ,, wfty k k' A B @ lmax k' (lmax k k') ,, wihty k k' k'' A B M @ lmax k' k''
      ⊢[ lC ] c' : wstepty k k' A B M @ k'' ] -> tm_leq c c' ->
  [ G' ; ΔL ⊢[ lC ] t : tyW k k' A B @ lmax k k' ] -> [ G' ; ΔL ⊢[ lC ] t' : tyW k k' A B @ lmax k k' ] ->
  tm_leq t t' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k' (ΔL ,, A @ k) (boxT B)) (motT (wrapMT MTR) k1' (ΔR ,, A' @ k1) (boxT B'))
    (recTL k' (ΔL ,, A @ k) B) (recTR k1' (ΔR ,, A' @ k1) B') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k'' (ΔL ,, tyW k k' A B @ lmax k k') (boxT M))
    (motT (wrapMT MTR) k1'' (ΔR ,, tyW k1 k1' A' B' @ lmax k1 k1') (boxT M'))
    (recTL k'' (ΔL ,, tyW k k' A B @ lmax k k') M) (recTR k1'' (ΔR ,, tyW k1 k1' A' B' @ lmax k1 k1') M') ->
  LRtmM (lvsubst l2 φ) G' Θ
    (mott (wrapMt MtL) k'' (ΔL ,, A @ k ,, wfty k k' A B @ lmax k' (lmax k k') ,, wihty k k' k'' A B M @ lmax k' k'')
       (wstepty k k' A B M) (boxt c))
    (mott (wrapMt MtR) k1'' (ΔR ,, A' @ k1 ,, wfty k1 k1' A' B' @ lmax k1' (lmax k1 k1')
                              ,, wihty k1 k1' k1'' A' B' M' @ lmax k1' k1'')
       (wstepty k1 k1' A' B' M') (boxt c'))
    (rectL k'' (ΔL ,, A @ k ,, wfty k k' A B @ lmax k' (lmax k k') ,, wihty k k' k'' A B M @ lmax k' k'')
       (wstepty k k' A B M) c)
    (rectR k1'' (ΔR ,, A' @ k1 ,, wfty k1 k1' A' B' @ lmax k1' (lmax k1 k1')
                 ,, wihty k1 k1' k1'' A' B' M' @ lmax k1' k1'')
       (wstepty k1 k1' A' B' M') c') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lmax k k') ΔL (tyW k k' A B) (boxt t))
    (mott (wrapMt MtR) (lmax k1 k1') ΔR (tyW k1 k1' A' B') (boxt t'))
    (rectL (lmax k k') ΔL (tyW k k' A B) t) (rectR (lmax k1 k1') ΔR (tyW k1 k1' A' B') t') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmElimW k k' k'' A B M c t)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmElimW k1 k1' k1'' A' B' M' c' t')))
    (rectL kL ΔL TL (tmElimW k k' k'' A B M c t)) (rectR kR ΔR TR (tmElimW k1 k1' k1'' A' B' M' c' t')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw' Hw'' Hw1 Hw1' Hw1'' E E' E'' HTL HTR HA HA' EA HB HB' EB HM HM' EM1 HF HI
    Hc Hc' Ec Ht Ht' Et IHA IHB IHM IHc IHt.
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
  assert (Qk'' : lequiv (gL G') k'' k'') by (rewrite EL; exact (lequiv_refl _ _ Hw'')).
  assert (Qm : lequiv L' (lmax k k') (lmax k1 k1')) by (apply lequiv_max; assumption).
  assert (Qmg : lequiv (gL G') (lmax k k') (lmax k1 k1')) by (rewrite EL; exact Qm).
  assert (Hwm : lwf L' (lmax k k')) by (cbn; auto).
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1)).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  (* the shape, the positions and their calls *)
  destruct (Tcall HΔL HΔ Hw Q HA HA' EA IHA) as (HAA & HA'R & HA'R1 & CA & CA1 & X1).
  destruct (Tcall (eqctx_wf_l (i := lD) eq_refl CA) CA1 Hw' Q' HB HB' EB IHB) as (HBB & _ & HB'R1 & _ & _ & X2).
  pose proof (ctxconv_ty CA (i := lC) eq_refl HB') as HB'R.
  pose proof (lift_ty (j := lD) HA Hl1c) as HAD. pose proof (lift_ty (j := lD) HA' Hl1c) as HA'D.
  pose proof (lift_ty (j := lD) HB Hl1c) as HBD. pose proof (lift_ty (j := lD) HB' Hl1c) as HB'D.
  (* the tree type, and the motive over it *)
  assert (HWD : [ G' ; ΔL ⊢[ lD ] tyW k k' A B @ lmax k k' ])
    by (apply wft_W; [discriminate | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HAD | exact HBD]).
  assert (HWW : [ G' ; ΔL ⊢[ lD ] tyW k k' A B ≅ tyW k1 k1' A' B' @ lmax k k' ])
    by (apply eqty_W; [discriminate | exact Qg | exact Qg' | exact HAD | exact HAA | exact HBB]).
  assert (HWW0 : [ G' ; ΔL ⊢[ lD ] tyW k k' A B ≅ tyW k k' A' B' @ lmax k k' ])
    by (apply eqty_W; [discriminate | exact Qk | exact Qk' | exact HAD | exact HAA | exact HBB]).
  assert (CW : [ G' ⊢[ lD ] ΔL ,, tyW k k' A B @ lmax k k' ≅ ΔR ,, tyW k k' A' B' @ lmax k k' ])
    by (apply eqc_ext; [exact HΔ | exact HWD | exact HWW0 | rewrite EL; exact (lequiv_refl _ _ Hwm)]).
  assert (CW1 : [ G' ⊢[ lD ] ΔL ,, tyW k k' A B @ lmax k k' ≅ ΔR ,, tyW k1 k1' A' B' @ lmax k1 k1' ])
    by (apply eqc_ext; [exact HΔ | exact HWD | exact HWW | exact Qmg]).
  pose proof (eqctx_wf_l (i := lD) eq_refl CW) as HΔW.
  destruct (Tcall HΔW CW1 Hw'' Q'' HM HM' EM1 IHM) as (HMM & _ & HM'R1 & _ & _ & X3).
  pose proof (ctxconv_ty CW (i := lC) eq_refl HM') as HM'R.
  pose proof (lift_ty (j := lD) HM Hl1c) as HMD. pose proof (lift_ty (j := lD) HM' Hl1c) as HM'D.
  pose proof (lift_ty (j := lD) HF Hl1c) as HFD. pose proof (lift_ty (j := lD) HI Hl1c) as HID.
  (* the step's telescope, at the right levels and at the left ones *)
  destruct (@W_facts G' lD eq_refl ltac:(discriminate) _ _ _ _ _ _ _ _ _ _ _ _ _ Qg Qg' Qg''
              HAA HAD HA'D HBB HBD HB'D HMM HMD HM'D HFD HID) as (_ & _ & CS1L & ES1).
  destruct (@W_facts G' lD eq_refl ltac:(discriminate) _ _ _ _ _ _ _ _ _ _ _ _ _ Qk Qk' Qk''
              HAA HAD HA'D HBB HBD HB'D HMM HMD HM'D HFD HID) as (_ & _ & CS0L & ES0).
  destruct (eqc_ext_inv CS1L) as (CS1a & _ & EI1 & QI1). destruct (eqc_ext_inv CS1a) as (_ & _ & EF1 & QF1).
  destruct (eqc_ext_inv CS0L) as (CS0a & _ & EI0 & QI0). destruct (eqc_ext_inv CS0a) as (_ & _ & EF0 & QF0).
  pose proof (eqctx_wf_l (i := lD) eq_refl CS1a) as HΔAF.
  assert (CS1 : [ G' ⊢[ lD ] ΔL ,, A @ k ,, wfty k k' A B @ lmax k' (lmax k k') ,, wihty k k' k'' A B M @ lmax k' k''
                  ≅ ΔR ,, A' @ k1 ,, wfty k1 k1' A' B' @ lmax k1' (lmax k1 k1') ,, wihty k1 k1' k1'' A' B' M' @ lmax k1' k1'' ])
    by (apply eqc_ext; [apply eqc_ext; [exact CA1 | exact HFD | exact EF1 | exact QF1] | exact HID | exact EI1 | exact QI1]).
  assert (CS0 : [ G' ⊢[ lD ] ΔL ,, A @ k ,, wfty k k' A B @ lmax k' (lmax k k') ,, wihty k k' k'' A B M @ lmax k' k''
                  ≅ ΔR ,, A' @ k ,, wfty k k' A' B' @ lmax k' (lmax k k') ,, wihty k k' k'' A' B' M' @ lmax k' k'' ])
    by (apply eqc_ext; [apply eqc_ext; [exact CA | exact HFD | exact EF0 | exact QF0] | exact HID | exact EI0 | exact QI0]).
  pose proof (eqctx_wf_l (i := lD) eq_refl CS1) as HΔS.
  (* the step and the scrutinee, and their calls *)
  destruct (tcall HΔS CS1 Hw'' Q'' ES1 Hc Hc' Ec IHc) as (Hcc & _ & Hc'R1 & _ & X4).
  destruct (tcall HΔL HΔ Hwm Qm HWW Ht Ht' Et IHt) as (Htt & _ & Ht'R1 & _ & X5).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHA) IHA) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHB) IHB) Hl1g') as X2r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHM) IHM) Hl1g') as X3r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHc) IHc) Hl2g') as X4r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHt) IHt) Hl2g') as X5r.
  (* the right pieces at the left levels *)
  assert (Hc'R : [ G' ; ΔR ,, A' @ k ,, wfty k k' A' B' @ lmax k' (lmax k k') ,, wihty k k' k'' A' B' M' @ lmax k' k''
                   ⊢[ lC ] c' : wstepty k k' A' B' M' @ k'' ]).
  { eapply wf_conv; [exact (ctxconv_tm CS0 (i := lC) eq_refl Hc') |].
    exact (ctxconv_eqty CS0 (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ ES0)). }
  assert (Ht'R : [ G' ; ΔR ⊢[ lC ] t' : tyW k k' A' B' @ lmax k k' ]).
  { eapply wf_conv; [exact (ctxconv_tm HΔ (i := lC) eq_refl Ht') |].
    exact (ctxconv_eqty HΔ (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ HWW0)). }
  (* the result types *)
  assert (Hr1 : [ G' ; ΔL ⊢[ lD ] M[lsingle t] ≅ M'[lsingle t'] @ k'' ])
    by exact (eqty_subst_single_D HMM HM'D Htt (lift_tm (j := lD) Ht Hl1c) (lift_tm (j := lD) Ht' Hl1c)).
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] tmElimW k k' k'' A B M c t : M[lsingle t] @ k'' ])
    by (apply wf_elimW; [exact Hn | rewrite EL; exact Hw | rewrite EL; exact Hw' | rewrite EL; exact Hw''
                        | exact HA | exact HB | exact HM | exact HF | exact HI | exact Hc | exact Ht]).
  pose proof (@sc_elimW_q G' lC Hl1c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hn Qg Qg' Qg''
                HA HA' (static_code_ty Hl1c HA HA' EA) HB HB' (static_code_ty Hl1c HB HB' EB)
                HM HM' (static_code_ty Hl1c HM HM' EM1) HF HI Hc' Ht Ht' (static_code_tm Hl1c Ht Ht' Et)) as HcRL.
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmElimW k1 k1' k1'' A' B' M' c' t' : M'[lsingle t'] @ k1'' ]).
  { refine (ctxconv_tm HΔ (i := lC) eq_refl _).
    eapply wf_lconv; [eapply wf_conv; [exact HcRL | apply eqty_sym, Hr1] | apply lequiv_sym, Qg'']. }
  assert (Ecc : tm_leq (tmElimW k k' k'' A B M c t) (tmElimW k1 k1' k1'' A' B' M' c' t'))
    by (cbn; repeat split; assumption).
  pose proof (lift_ty (j := lD) HA'R1 Hl1c) as HA'R1D. pose proof (lift_ty (j := lD) HB'R1 Hl1c) as HB'R1D.
  pose proof (lift_ty (j := lD) HM'R1 Hl1c) as HM'R1D.
  refine (rec_t_br 42 (k :: k' :: k'' :: nil) (k1 :: k1' :: k1'' :: nil)
            (GCtx ΔL :: GTy A :: GTy B :: GTy M :: GTm c :: GTm t :: nil)
            (GCtx ΔR :: GTy A' :: GTy B' :: GTy M' :: GTm c' :: GTm t' :: nil)
            (recTL k ΔL A :: recTL k' (ΔL ,, A @ k) B :: recTL k'' (ΔL ,, tyW k k' A B @ lmax k k') M
             :: rectL k'' (ΔL ,, A @ k ,, wfty k k' A B @ lmax k' (lmax k k') ,, wihty k k' k'' A B M @ lmax k' k'')
                  (wstepty k k' A B M) c
             :: rectL (lmax k k') ΔL (tyW k k' A B) t :: nil)
            (recTR k1 ΔR A' :: recTR k1' (ΔR ,, A' @ k1) B' :: recTR k1'' (ΔR ,, tyW k1 k1' A' B' @ lmax k1 k1') M'
             :: rectR k1'' (ΔR ,, A' @ k1 ,, wfty k1 k1' A' B' @ lmax k1' (lmax k1 k1')
                            ,, wihty k1 k1' k1'' A' B' M' @ lmax k1' k1'') (wstepty k1 k1' A' B' M') c'
             :: rectR (lmax k1 k1') ΔR (tyW k1 k1' A' B') t' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_cons _ _ E' (Forall2_cons _ _ E'' (Forall2_nil _)))))
            HΔL HΔ HkL HkR Q'' HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl Hr1) HcL0 HcRL HcR0 Ecc
            (GS_elimW EP EM Hσ HΔL HΔ HA HA'R HAA EA HB HB'R HBB EB HM HM'R HMM EM1 Hc Hc'R Hcc Ec Ht Ht'R Htt Et)
            (GS_elimW EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR)
               HA'R1 HA'R1 (eqty_refl _ _ _ _ _ HA'R1D) (ty_leq_refl _)
               HB'R1 HB'R1 (eqty_refl _ _ _ _ _ HB'R1D) (ty_leq_refl _)
               HM'R1 HM'R1 (eqty_refl _ _ _ _ _ HM'R1D) (ty_leq_refl _)
               Hc'R1 Hc'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hc'R1 Hl1c)) (tm_leq_refl _)
               Ht'R1 Ht'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Ht'R1 Hl1c)) (tm_leq_refl _))
            _ _ _ _ _ _ _).
  - sr_ctx_W; [exact X1 | exact X2 | exact X3 | exact X4 | exact X5].
  - sr_ctx_W; [exact X1r | exact X2r | exact X3r | exact X4r | exact X5r].
  - J_res.
  - J_res.
  - J_res.
  - apply redt_elimW_inst; inst_side 42.
  - apply redt_elimW_inst; inst_side 42.
Qed.

(** Length-indexed tuples and finite indices (M14b): the length's call is a
    term call at [Nat], as [succ]'s. *)
Lemma rec_T_vec {ΔL ΔR kL kR k k1 A A' n n'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k kL -> lequiv L' k kR -> lwf L' k -> lwf L' k1 -> leqv k k1 ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] A' @ k ] -> ty_leq A A' ->
  [ G' ; ΔL ⊢[ lC ] n : tyNat @ lzero ] -> [ G' ; ΔL ⊢[ lC ] n' : tyNat @ lzero ] -> tm_leq n n' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) lzero ΔL tyNat (boxt n)) (mott (wrapMt MtR) lzero ΔR tyNat (boxt n'))
    (rectL lzero ΔL tyNat n) (rectR lzero ΔR tyNat n') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL (boxT (tyVec k A n)))
    (motT (wrapMT MTR) kR ΔR (boxT (tyVec k1 A' n')))
    (recTL kL ΔL (tyVec k A n)) (recTR kR ΔR (tyVec k1 A' n')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw1 E HA HA' EA Hn Hn' En IHA IHn.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hv : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1)).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  assert (HN0 : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lD ] tyNat @ lzero ])
    by (intros; apply wft_nat; [discriminate | assumption]).
  (* the element type, the length, and their calls *)
  destruct (Tcall HΔL HΔ Hw Q HA HA' EA IHA) as (HAA & HA'R & HA'R1 & _ & _ & X1).
  destruct (tcall (k := lzero) HΔL HΔ I (lequiv_refl L' lzero I) (eqty_refl _ _ _ _ _ (HN0 _ HΔL)) Hn Hn' En IHn)
    as (Hnn & Hn'R & _ & _ & X2).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHA) IHA) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHn) IHn) Hl2g') as X2r.
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] tyVec k A n @ k ])
    by (apply wft_vec; [exact Hv | rewrite EL; exact Hw | exact HA | exact Hn]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tyVec k1 A' n' @ k1 ])
    by (apply wft_vec; [exact Hv | rewrite EL; exact Hw1 | exact HA'R1 | exact Hn'R]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tyVec k1 A' n' @ k ])
    by (eapply wft_lconv; [exact (ctxconv_ty (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | rewrite EL; exact Q]).
  assert (Ec : ty_leq (tyVec k A n) (tyVec k1 A' n')) by (cbn; repeat split; assumption).
  refine (rec_T_br 43 (k :: nil) (k1 :: nil) (GCtx ΔL :: GTy A :: GTm n :: nil)
            (GCtx ΔR :: GTy A' :: GTm n' :: nil)
            (recTL k ΔL A :: rectL lzero ΔL tyNat n :: nil) (recTR k1 ΔR A' :: rectR lzero ΔR tyNat n' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR Q HcL0 HcRL HcR0 Ec
            (GS_vec EP EM Hσ HΔL HΔ HA HA'R HAA EA Hn Hn'R Hnn En)
            (GS_vec EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HA'R1 HA'R1
               (eqty_refl _ _ _ _ _ (lift_ty (j := lD) HA'R1 Hl1c)) (ty_leq_refl _) Hn'R Hn'R
               (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hn'R Hl1c)) (tm_leq_refl _))
            _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2].
  - sr_ctx; [exact X1r | exact X2r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redT_vec_inst; inst_side 43.
  - apply redT_vec_inst; inst_side 43.
Qed.

Lemma rec_t_codevec {ΔL ΔR kL kR TL TR k k1 s0 s1 n n'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lsuc k) kL -> lequiv L' (lsuc k) kR -> lwf L' k -> lwf L' k1 -> leqv k k1 ->
  [ G' ; ΔL ⊢[ lD ] tyU k ≅ TL @ lsuc k ] -> [ G' ; ΔL ⊢[ lD ] tyU k ≅ TR @ lsuc k ] ->
  [ G' ; ΔL ⊢[ lC ] s0 : tyU k @ lsuc k ] -> [ G' ; ΔL ⊢[ lC ] s1 : tyU k @ lsuc k ] -> tm_leq s0 s1 ->
  [ G' ; ΔL ⊢[ lC ] n : tyNat @ lzero ] -> [ G' ; ΔL ⊢[ lC ] n' : tyNat @ lzero ] -> tm_leq n n' ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) (lsuc k) ΔL (tyU k) (boxt s0))
    (mott (wrapMt MtR) (lsuc k1) ΔR (tyU k1) (boxt s1))
    (rectL (lsuc k) ΔL (tyU k) s0) (rectR (lsuc k1) ΔR (tyU k1) s1) ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) lzero ΔL tyNat (boxt n)) (mott (wrapMt MtR) lzero ΔR tyNat (boxt n'))
    (rectL lzero ΔL tyNat n) (rectR lzero ΔR tyNat n') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmVec k s0 n)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (tmVec k1 s1 n')))
    (rectL kL ΔL TL (tmVec k s0 n)) (rectR kR ΔR TR (tmVec k1 s1 n')).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw1 E HTL HTR Hs Hs' Es Hn Hn' En IHs IHn.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  assert (HUU : forall Δ j j', [ G' ; Δ ⊢[ lD ] ] -> lequiv L' j j' -> [ G' ; Δ ⊢[ lD ] tyU j ≅ tyU j' @ lsuc j ])
    by (intros; apply eqty_U; [discriminate | assumption | rewrite EL; assumption]).
  assert (HN0 : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lD ] tyNat @ lzero ])
    by (intros; apply wft_nat; [discriminate | assumption]).
  (* the element code, the length, and their calls *)
  destruct (tcall (k := lsuc k) HΔL HΔ Hw (lequiv_suc _ _ _ Q) (HUU _ _ _ HΔL Q) Hs Hs' Es IHs) as (Hss & _ & Hs'R1 & _ & X1).
  destruct (tcall (k := lzero) HΔL HΔ I (lequiv_refl L' lzero I) (eqty_refl _ _ _ _ _ (HN0 _ HΔL)) Hn Hn' En IHn)
    as (Hnn & Hn'R & _ & _ & X2).
  pose proof (ctxconv_tm HΔ (i := lC) eq_refl Hs') as Hs'R.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHs) IHs) Hl2g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHn) IHn) Hl2g') as X2r.
  (* the codes *)
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] tmVec k s0 n : tyU k @ lsuc k ])
    by (apply wf_code_vec; [discriminate | rewrite EL; exact Hw | exact Hs | exact Hn]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmVec k1 s1 n' : tyU k1 @ lsuc k1 ])
    by (apply wf_code_vec; [discriminate | rewrite EL; exact Hw1 | exact Hs'R1 | exact Hn'R]).
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] tmVec k1 s1 n' : tyU k @ lsuc k ])
    by (eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0)
                                          | rewrite EL; apply lequiv_suc, Q] | exact (HUU _ _ _ HΔL Q)]).
  refine (rec_t_br 44 (k :: nil) (k1 :: nil) (GCtx ΔL :: GTm s0 :: GTm n :: nil)
            (GCtx ΔR :: GTm s1 :: GTm n' :: nil)
            (rectL (lsuc k) ΔL (tyU k) s0 :: rectL lzero ΔL tyNat n :: nil)
            (rectR (lsuc k1) ΔR (tyU k1) s1 :: rectR lzero ΔR tyNat n' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl
            ltac:(repeat constructor; assumption) ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_nil _)))
            HΔL HΔ HkL HkR (lequiv_suc _ _ _ Q) HTL HTR (HUU _ _ _ HΔR Q) HcL0 HcRL HcR0
            ltac:(cbn; repeat split; assumption)
            (GS_codevec EP EM Hσ HΔL HΔ Hs Hs'R Hss Es Hn Hn'R Hnn En)
            (GS_codevec EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) Hs'R1 Hs'R1
               (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hs'R1 Hl1c)) (tm_leq_refl _) Hn'R Hn'R
               (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hn'R Hl1c)) (tm_leq_refl _)) _ _ _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2].
  - sr_ctx; [exact X1r | exact X2r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_codevec_inst; inst_side 44.
  - apply redt_codevec_inst; inst_side 44.
Qed.

Lemma rec_T_fin {ΔL ΔR kL kR n n'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' lzero kL -> lequiv L' lzero kR ->
  [ G' ; ΔL ⊢[ lC ] n : tyNat @ lzero ] -> [ G' ; ΔL ⊢[ lC ] n' : tyNat @ lzero ] -> tm_leq n n' ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) lzero ΔL tyNat (boxt n)) (mott (wrapMt MtR) lzero ΔR tyNat (boxt n'))
    (rectL lzero ΔL tyNat n) (rectR lzero ΔR tyNat n') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL (boxT (tyFin n))) (motT (wrapMT MTR) kR ΔR (boxT (tyFin n')))
    (recTL kL ΔL (tyFin n)) (recTR kR ΔR (tyFin n')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hn Hn' En IHn.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  assert (HN0 : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lD ] tyNat @ lzero ])
    by (intros; apply wft_nat; [discriminate | assumption]).
  destruct (tcall (k := lzero) HΔL HΔ I (lequiv_refl L' lzero I) (eqty_refl _ _ _ _ _ (HN0 _ HΔL)) Hn Hn' En IHn)
    as (Hnn & Hn'R & _ & _ & X1).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHn) IHn) Hl2g') as X1r.
  assert (HcF : forall Δ u, [ G' ; Δ ⊢[ lC ] u : tyNat @ lzero ] -> [ G' ; Δ ⊢[ lC ] tyFin u @ lzero ])
    by (intros; apply wft_fin; [discriminate | assumption]).
  refine (rec_T_br 45 nil nil (GCtx ΔL :: GTm n :: nil) (GCtx ΔR :: GTm n' :: nil)
            (rectL lzero ΔL tyNat n :: nil) (rectR lzero ΔR tyNat n' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl (Forall_nil _) (Forall_nil _) (fun i => leqv_refl _)
            HΔL HΔ HkL HkR (lequiv_refl L' lzero I) (HcF _ _ Hn) (HcF _ _ Hn') (HcF _ _ Hn'R) En
            (GS_fin EP EM 45 eq_refl eq_refl Hσ HΔL HΔ Hn Hn'R Hnn En)
            (GS_fin EP EM 45 eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) Hn'R Hn'R
               (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hn'R Hl1c)) (tm_leq_refl _)) _ _ _ _ _ _ _).
  - sr_ctx. exact X1.
  - sr_ctx. exact X1r.
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redT_fin_inst; inst_side 45.
  - apply redT_fin_inst; inst_side 45.
Qed.

Lemma rec_t_codefin {ΔL ΔR kL kR TL TR n n'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lsuc lzero) kL -> lequiv L' (lsuc lzero) kR ->
  [ G' ; ΔL ⊢[ lD ] tyU lzero ≅ TL @ lsuc lzero ] -> [ G' ; ΔL ⊢[ lD ] tyU lzero ≅ TR @ lsuc lzero ] ->
  [ G' ; ΔL ⊢[ lC ] n : tyNat @ lzero ] -> [ G' ; ΔL ⊢[ lC ] n' : tyNat @ lzero ] -> tm_leq n n' ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) lzero ΔL tyNat (boxt n)) (mott (wrapMt MtR) lzero ΔR tyNat (boxt n'))
    (rectL lzero ΔL tyNat n) (rectR lzero ΔR tyNat n') ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (tmFin n))) (mott (wrapMt MtR) kR ΔR TR (boxt (tmFin n')))
    (rectL kL ΔL TL (tmFin n)) (rectR kR ΔR TR (tmFin n')).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR HTL HTR Hn Hn' En IHn.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  assert (HN0 : forall Δ, [ G' ; Δ ⊢[ lD ] ] -> [ G' ; Δ ⊢[ lD ] tyNat @ lzero ])
    by (intros; apply wft_nat; [discriminate | assumption]).
  destruct (tcall (k := lzero) HΔL HΔ I (lequiv_refl L' lzero I) (eqty_refl _ _ _ _ _ (HN0 _ HΔL)) Hn Hn' En IHn)
    as (Hnn & Hn'R & _ & _ & X1).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHn) IHn) Hl2g') as X1r.
  assert (HcF : forall Δ u, [ G' ; Δ ⊢[ lC ] u : tyNat @ lzero ] -> [ G' ; Δ ⊢[ lC ] tmFin u : tyU lzero @ lsuc lzero ])
    by (intros; apply wf_code_fin; [discriminate | assumption]).
  assert (HU0 : [ G' ; ΔR ⊢[ lD ] tyU lzero @ lsuc lzero ]) by (apply wft_U; [discriminate | assumption | exact I]).
  refine (rec_t_br 46 nil nil (GCtx ΔL :: GTm n :: nil) (GCtx ΔR :: GTm n' :: nil)
            (rectL lzero ΔL tyNat n :: nil) (rectR lzero ΔR tyNat n' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl (Forall_nil _) (Forall_nil _) (fun i => leqv_refl _)
            HΔL HΔ HkL HkR (lequiv_refl L' (lsuc lzero) I) HTL HTR (eqty_refl _ _ _ _ _ HU0)
            (HcF _ _ Hn) (HcF _ _ Hn') (HcF _ _ Hn'R) En
            (GS_fin EP EM 46 eq_refl eq_refl Hσ HΔL HΔ Hn Hn'R Hnn En)
            (GS_fin EP EM 46 eq_refl eq_refl (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) Hn'R Hn'R
               (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hn'R Hl1c)) (tm_leq_refl _)) _ _ _ _ _ _ _).
  - sr_ctx. exact X1.
  - sr_ctx. exact X1r.
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_codefin_inst; inst_side 46.
  - apply redt_codefin_inst; inst_side 46.
Qed.

Lemma rec_t_var {ΔL ΔR kL kR TL TR k T0 n} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] -> lequiv L' k kL -> lequiv L' k kR ->
  [ G' ; ΔL ⊢[ lD ] T0 ≅ TL @ k ] -> [ G' ; ΔL ⊢[ lD ] T0 ≅ TR @ k ] ->
  [ G' ; ΔL ⊢[ lV ] var n : T0 @ k ] ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (var n)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (var n)))
    (rectL kL ΔL TL (var n)) (rectR kR ΔR TR (var n)).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR HTL HTR Hv.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (HwL : lwf L' kL) by exact (lequiv_wf_r _ _ _ HkL).
  assert (HkLg : lequiv (gL G') k kL) by (rewrite EL; exact HkL).
  assert (HkRg : lequiv (gL G') k kR) by (rewrite EL; exact HkR).
  assert (QLR : lequiv L' kL kR) by exact (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ HkL) HkR).
  assert (QLRg : lequiv (gL G') kL kR) by (rewrite EL; exact QLR).
  pose proof (eqty_wf_r (i := lD) eq_refl HTL) as HTL0. pose proof (eqty_wf_r (i := lD) eq_refl HTR) as HTR0.
  assert (HTLk : [ G' ; ΔL ⊢[ lD ] TL @ kL ]) by (eapply wft_lconv; [exact HTL0 | apply lequiv_sym, HkLg]).
  assert (HTRk : [ G' ; ΔR ⊢[ lD ] TR @ kR ]).
  { eapply wft_lconv; [exact (ctxconv_ty HΔ (i := lD) eq_refl HTR0) | apply lequiv_sym, HkRg]. }
  assert (HTRkL : [ G' ; ΔR ⊢[ lD ] TR @ kL ]) by (eapply wft_lconv; [exact HTRk | exact QLRg]).
  assert (HTLR : [ G' ; ΔL ⊢[ lD ] TL ≅ TR @ kL ]).
  { eapply eqty_lconv; [exact (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ HTL) HTR) | apply lequiv_sym, HkLg]. }
  assert (HvL : [ G' ; ΔL ⊢[ lV ] var n : TL @ kL ])
    by (eapply wf_lconv; [eapply wf_conv; [exact Hv | apply eqty_sym, HTL] | apply lequiv_sym, HkLg]).
  assert (HvR : [ G' ; ΔR ⊢[ lV ] var n : TR @ kR ]).
  { refine (ctxconv_tm HΔ (i := lV) eq_refl _).
    eapply wf_lconv; [eapply wf_conv; [exact Hv | apply eqty_sym, HTR] | apply lequiv_sym, HkRg]. }
  assert (HvRL : [ G' ; ΔR ⊢[ lV ] var n : TR @ kL ]) by (eapply wf_lconv; [exact HvR | exact QLRg]).
  assert (Hlv : lle lV lC) by (unfold lle; cbn; lia).
  pose proof (lift_tm (j := lC) HvL Hlv) as HcL. pose proof (lift_tm (j := lC) HvR Hlv) as HcR.
  (* the branch: its index is the recursor's own *)
  refine (rec_t_br 4 (kL :: nil) (kR :: nil) (GCtx ΔL :: GTy TL :: GTm (var n) :: nil)
            (GCtx ΔR :: GTy TR :: GTm (var n) :: nil) nil nil ltac:(cbv; lia) eq_refl eq_refl eq_refl
            ltac:(repeat constructor; assumption) ltac:(repeat constructor; exact (lequiv_wf_r _ _ _ HkR))
            (uext_leqv (Forall2_cons _ _ (lequiv_leqv _ _ _ QLR) (Forall2_nil _)))
            HΔL HΔ (lequiv_refl _ _ HwL) QLR QLR (eqty_refl _ _ _ _ _ HTLk) HTLR
            (ctxconv_eqty HΔ (i := lD) eq_refl HTLR) HcL HcL HcR (tm_leq_refl _)
            (GS_var EP EM Hσ HΔL HΔ HTLk HTRkL HTLR HvL HvRL)
            (GS_var EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HTRk HTRk (eqty_refl _ _ _ _ _ HTRk) HvR HvR)
            _ _ _ _ _ _ _).
  - sr_ctx.
  - sr_ctx.
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_var_inst; inst_side 4.
  - apply redt_var_inst; inst_side 4.
Qed.

End Rec.
