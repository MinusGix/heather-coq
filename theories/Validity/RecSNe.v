(** * The recursion lemmas on code: λ, neutral scrutinees and globals

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

(** ** λ: the index is first reduced to its Π whnf *)
Lemma LRty_eqM {l T T'} : LRtyM l G' Θ T T' -> [ G' ; Θ ⊢[ lM ] T ≅ T' @ l ].
Proof using ELM EMl.
  intros [R HR]. destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (_ & _ & H).
  pose proof (geq_ty_sound H) as H'. rewrite (@gm_layer_M EP EM EMl) in H'. exact H'.
Qed.

Lemma rec_t_fin_lam {ΔL ΔR kL kR TL TR WL WR k k' A b k1 k1' A' b' rL rR} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ; ΔR ⊢[ lD ] ] -> lwf L' kL -> lwf L' kR ->
  [ G' ; ΔL ⊢[ lD ] TL @ kL ] -> [ G' ; ΔR ⊢[ lD ] TR @ kR ] ->
  [ G' ; ΔL ⊢[ lC ] lam k k' A b : TL @ kL ] -> [ G' ; ΔR ⊢[ lC ] lam k1 k1' A' b' : TR @ kR ] ->
  [ G' ; ΔL ⊢[ lD ] TL ⤳* WL @ kL ] -> [ G' ; ΔR ⊢[ lD ] TR ⤳* WR @ kR ] ->
  redt (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) kL ΔL WL (lam k k' A b) = Some rL ->
  redt (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) kR ΔR WR (lam k1 k1' A' b') = Some rR ->
  LRtyM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (lam k k' A b)))
    (mott (wrapMt MtL) kL ΔL WL (boxt (lam k k' A b))) ->
  LRtyM (lvsubst l2' φ) G' Θ (mott (wrapMt MtR) kR ΔR TR (boxt (lam k1 k1' A' b')))
    (mott (wrapMt MtR) kR ΔR WR (boxt (lam k1 k1' A' b'))) ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (lam k k' A b)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (lam k1 k1' A' b'))) rL rR ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (lam k k' A b)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (lam k1 k1' A' b')))
    (rectL kL ΔL TL (lam k k' A b)) (rectR kR ΔR TR (lam k1 k1' A' b')).
Proof using EL ELM ELP EMl Hl2 HrbL HrbR.
  intros HΔL HΔR HkL HkR HTL HTR HcL HcR HWL HWR HredL HredR ML MR W.
  assert (Hl2g : lequiv (gL G') (lvsubst l2 φ) (lvsubst l2' φ)) by (rewrite EL; exact Hl2).
  assert (HkLg : lwf (gL G') kL) by (rewrite EL; exact HkL). assert (HkRg : lwf (gL G') kR) by (rewrite EL; exact HkR).
  destruct (LRtm_escape W) as [HrL _]. destruct (LRtm_escape (LRtm_sym W)) as [HrR _].
  rewrite (@gm_layer_M EP EM EMl) in HrL, HrR.
  pose proof (ctx_of_wf_tm (i := lM) eq_refl HrL) as HΘ0.
  pose proof (LRty_eqM ML) as EqL. pose proof (LRty_eqM MR) as EqR.
  pose proof (eqty_wf_r (i := lD) eq_refl (tyred_eq _ _ _ _ _ _ HWL)) as HWL0.
  pose proof (eqty_wf_r (i := lD) eq_refl (tyred_eq _ _ _ _ _ _ HWR)) as HWR0.
  assert (HcLW : [ G' ; ΔL ⊢[ lC ] lam k k' A b : WL @ kL ])
    by (eapply wf_conv; [exact HcL | apply eqty_sym, (tyred_eq _ _ _ _ _ _ HWL)]).
  assert (HcRW : [ G' ; ΔR ⊢[ lC ] lam k1 k1' A' b' : WR @ kR ])
    by (eapply wf_conv; [exact HcR | apply eqty_sym, (tyred_eq _ _ _ _ _ _ HWR)]).
  pose proof (tmred_elimt_idx HrbL HkLg HΔL HWL (wf_boxt _ _ _ _ _ _ HΘ0 HkLg HΔL HTL HcL) EqL) as R1a.
  pose proof (tmred_elimt_beta HrbL HkLg HΔL HWL0 HcLW HredL
                ltac:(eapply wf_conv; [exact HrL | apply eqty_sym, EqL])) as R1b.
  pose proof (tmred_trans _ _ _ _ _ R1a (tmred_conv _ _ _ _ _ eq_refl R1b (eqty_sym _ _ _ _ _ _ EqL))) as R1.
  pose proof (wf_lconv _ _ _ _ _ _ _ HrR (lequiv_sym _ _ _ Hl2g)) as HrR'.
  pose proof (tmred_elimt_idx HrbR HkRg HΔR HWR (wf_boxt _ _ _ _ _ _ HΘ0 HkRg HΔR HTR HcR) EqR) as R2a.
  pose proof (tmred_elimt_beta HrbR HkRg HΔR HWR0 HcRW HredR
                ltac:(eapply wf_conv; [exact HrR' | apply eqty_sym, EqR])) as R2b.
  pose proof (tmred_trans _ _ _ _ _ R2a (tmred_conv _ _ _ _ _ eq_refl R2b (eqty_sym _ _ _ _ _ _ EqR))) as R2.
  pose proof (tmred_lconv _ _ _ _ _ R2 Hl2g) as R2'.
  rewrite <- (@gm_layer_M EP EM EMl) in R1, R2'.
  exact (LRtm_red W R1 R2').
Qed.

Lemma rec_t_lam {ΔL ΔR kL kR TL TR k k' k1 k1' A A' B0 b b'} :
  [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' (lmax k k') kL -> lequiv L' (lmax k k') kR -> lwf L' k -> lwf L' k' -> lwf L' k1 -> lwf L' k1' ->
  leqv k k1 -> leqv k' k1' ->
  [ G' ; ΔL ⊢[ lD ] tyPi k k' A B0 ≅ TL @ lmax k k' ] -> [ G' ; ΔL ⊢[ lD ] tyPi k k' A B0 ≅ TR @ lmax k k' ] ->
  [ G' ; ΔL ⊢[ lC ] A @ k ] -> [ G' ; ΔL ⊢[ lC ] A' @ k ] -> ty_leq A A' ->
  [ G' ; ΔL ,, A @ k ⊢[ lC ] b : B0 @ k' ] -> [ G' ; ΔL ,, A @ k ⊢[ lC ] b' : B0 @ k' ] -> tm_leq b b' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) k ΔL (boxT A)) (motT (wrapMT MTR) k1 ΔR (boxT A'))
    (recTL k ΔL A) (recTR k1 ΔR A') ->
  (forall BL BR, [ G' ; ΔL ,, A @ k ⊢[ lD ] B0 ≅ BL @ k' ] -> [ G' ; ΔL ,, A @ k ⊢[ lD ] B0 ≅ BR @ k' ] ->
     LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) k' (ΔL ,, A @ k) BL (boxt b))
       (mott (wrapMt MtR) k1' (ΔR ,, A' @ k1) BR (boxt b'))
       (rectL k' (ΔL ,, A @ k) BL b) (rectR k1' (ΔR ,, A' @ k1) BR b')) ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt (lam k k' A b)))
    (mott (wrapMt MtR) kR ΔR TR (boxt (lam k1 k1' A' b')))
    (rectL kL ΔL TL (lam k k' A b)) (rectR kR ΔR TR (lam k1 k1' A' b')).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros HΔL HΔ HkL HkR Hw Hw' Hw1 Hw1' E E' HTL HTR HA HA' EA Hb Hb' Eb IHA IHb.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. pose proof EL as EL'.
  assert (Hn : lC <> lV) by discriminate. assert (Hl1c : lle lC lD) by (unfold lle; cbn; lia).
  assert (Q : lequiv L' k k1) by exact (leqv_lequiv _ _ _ Hw Hw1 E).
  assert (Q' : lequiv L' k' k1') by exact (leqv_lequiv _ _ _ Hw' Hw1' E').
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q). assert (Qg' : lequiv (gL G') k' k1') by (rewrite EL; exact Q').
  assert (Qm : lequiv L' (lmax k k') (lmax k1 k1')) by (apply lequiv_max; assumption).
  assert (Qmg : lequiv (gL G') (lmax k k') (lmax k1 k1')) by (rewrite EL; exact Qm).
  assert (Hwm : lwf L' (lmax k k')) by (cbn; auto). assert (Hwm1 : lwf L' (lmax k1 k1')) by (cbn; auto).
  assert (Hkg : lequiv (gL G') k k) by (apply lequiv_refl; rewrite EL; exact Hw).
  assert (Hkg' : lequiv (gL G') k' k') by (apply lequiv_refl; rewrite EL; exact Hw').
  assert (HwL : lwf L' kL) by exact (lequiv_wf_r _ _ _ HkL). assert (HwR : lwf L' kR) by exact (lequiv_wf_r _ _ _ HkR).
  assert (Hwl2 : lwf L' (lvsubst l2 φ)) by (rewrite <- EL; exact (proj1 (proj2 HrbL))).
  assert (Hwl2' : lwf L' (lvsubst l2' φ)) by exact (lequiv_wf_r _ _ _ Hl2).
  assert (Hl1g' : lequiv (gL G') (lvsubst l1' φ) (lvsubst l1 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl1)).
  assert (Hl2g : lequiv (gL G') (lvsubst l2 φ) (lvsubst l2' φ)) by (rewrite EL; exact Hl2).
  assert (Hl2g' : lequiv (gL G') (lvsubst l2' φ) (lvsubst l2 φ)) by (rewrite EL; exact (lequiv_sym _ _ _ Hl2)).
  assert (HkLg : lequiv (gL G') (lmax k k') kL) by (rewrite EL; exact HkL).
  assert (HkRg : lequiv (gL G') (lmax k k') kR) by (rewrite EL; exact HkR).
  (* the domain and its call *)
  destruct (Tcall HΔL HΔ Hw Q HA HA' EA IHA) as (HAA & HA'R & HA'R1 & CA & CA1 & X1).
  pose proof (lift_ty (j := lD) HA Hl1c) as HAD. pose proof (eqctx_wf_l (i := lD) eq_refl CA) as HΔLA.
  pose proof (lift_ty (j := lD) HA'R1 Hl1c) as HA'R1D.
  (* the indices' Π whnfs *)
  destruct (decl_pi_red HTL) as (c1 & c2 & CL & BL & HWL).
  destruct (decl_pi_red (ctxconv_eqty HΔ (i := lD) eq_refl HTR)) as (c3 & c4 & CR & BR & HWR).
  assert (EqL : [ G' ; ΔL ⊢[ lD ] tyPi k k' A B0 ≅ tyPi c1 c2 CL BL @ lmax k k' ])
    by exact (eqty_trans _ _ _ _ _ _ _ HTL (tyred_eq _ _ _ _ _ _ HWL)).
  assert (EqR : [ G' ; ΔL ⊢[ lD ] tyPi k k' A B0 ≅ tyPi c3 c4 CR BR @ lmax k k' ])
    by exact (eqty_trans _ _ _ _ _ _ _ HTR (ctxconv_eqty (eqctx_sym_D HΔ) (i := lD) eq_refl (tyred_eq _ _ _ _ _ _ HWR))).
  destruct (decl_pi_inj EqL) as (_ & _ & _ & HB0BL). destruct (decl_pi_inj EqR) as (_ & _ & _ & HB0BR).
  pose proof (eqty_wf_r (i := lD) eq_refl HB0BL) as HBLD. pose proof (eqty_wf_r (i := lD) eq_refl HB0BR) as HBRD.
  assert (HBLBR : [ G' ; ΔL ,, A @ k ⊢[ lD ] BL ≅ BR @ k' ])
    by exact (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ HB0BL) HB0BR).
  pose proof (ctxconv_ty CA (i := lD) eq_refl HBRD) as HBRk.
  assert (HBR1 : [ G' ; ΔR ,, A' @ k1 ⊢[ lD ] BR @ k1' ])
    by (eapply wft_lconv; [exact (ctxconv_ty CA1 (i := lD) eq_refl HBRD) | apply lequiv_sym, Qg']).
  (* the body at the whnfs' codomains *)
  assert (HbL : [ G' ; ΔL ,, A @ k ⊢[ lC ] b : BL @ k' ]) by (eapply wf_conv; [exact Hb | apply eqty_sym, HB0BL]).
  assert (Hb'L : [ G' ; ΔL ,, A @ k ⊢[ lC ] b' : BL @ k' ]) by (eapply wf_conv; [exact Hb' | apply eqty_sym, HB0BL]).
  assert (Hb'R : [ G' ; ΔR ,, A' @ k ⊢[ lC ] b' : BR @ k' ]).
  { refine (ctxconv_tm CA (i := lC) eq_refl _). eapply wf_conv; [exact Hb' | apply eqty_sym, HB0BR]. }
  assert (Hb'R1 : [ G' ; ΔR ,, A' @ k1 ⊢[ lC ] b' : BR @ k1' ]).
  { eapply wf_lconv; [| apply lequiv_sym, Qg']. refine (ctxconv_tm CA1 (i := lC) eq_refl _).
    eapply wf_conv; [exact Hb' | apply eqty_sym, HB0BR]. }
  pose proof (lift_eqtm (j := lD) (static_code_tm Hl1c HbL Hb'L Eb) Hl1c) as Hbb.
pose proof (wf_ty_dnf HA'R) as NA'.
pose proof (wf_tm_dnf Hb'R) as Nb'.
  (* the codes *)
  assert (HΠ' : [ G' ; ΔL ⊢[ lD ] tyPi k k' A BL @ lmax k k' ])
    by (apply wft_pi; [discriminate | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HAD | exact HBLD]).
  assert (HΠΠ' : [ G' ; ΔL ⊢[ lD ] tyPi k k' A B0 ≅ tyPi k k' A BL @ lmax k k' ])
    by (apply eqty_pi; [discriminate | exact Hkg | exact Hkg' | exact HAD | apply eqty_refl, HAD | exact HB0BL]).
  assert (HΠ'R : [ G' ; ΔL ⊢[ lD ] tyPi k k' A BL ≅ tyPi k1 k1' A' BR @ lmax k k' ])
    by (apply eqty_pi; [discriminate | exact Qg | exact Qg' | exact HAD | exact HAA | exact HBLBR]).
  assert (HcL0 : [ G' ; ΔL ⊢[ lC ] lam k k' A b : tyPi k k' A BL @ lmax k k' ])
    by (apply wf_lam; [exact Hn | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HA | exact HbL]).
  assert (HcL : [ G' ; ΔL ⊢[ lC ] lam k k' A b : TL @ kL ]).
  { eapply wf_lconv; [eapply wf_conv; [exact HcL0 |] | apply lequiv_sym, HkLg].
    exact (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ HTL) HΠΠ'). }
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] lam k1 k1' A' b' : tyPi k1 k1' A' BR @ lmax k1 k1' ])
    by (apply wf_lam; [exact Hn | rewrite EL; exact Hw1 | rewrite EL; exact Hw1' | exact HA'R1 | exact Hb'R1]).
  pose proof (wf_tm_ty (i := lD) eq_refl (lift_tm (j := lD) HcR0 Hl1c)) as HΠR.
  assert (HcRL : [ G' ; ΔL ⊢[ lC ] lam k1 k1' A' b' : tyPi k k' A BL @ lmax k k' ]).
  { eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qmg] | exact HΠ'R]. }
  assert (HTRΠ : [ G' ; ΔR ⊢[ lD ] TR ≅ tyPi k1 k1' A' BR @ lmax k k' ]).
  { refine (ctxconv_eqty HΔ (i := lD) eq_refl _).
    exact (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ HTR) (eqty_trans _ _ _ _ _ _ _ HΠΠ' HΠ'R)). }
  assert (HcR : [ G' ; ΔR ⊢[ lC ] lam k1 k1' A' b' : TR @ kR ]).
  { eapply wf_lconv; [eapply wf_conv; [eapply wf_lconv; [exact HcR0 | exact Qmg] | exact HTRΠ] | apply lequiv_sym, HkRg]. }
  pose proof (eqty_wf_r (i := lD) eq_refl HTL) as HTL0. pose proof (eqty_wf_r (i := lD) eq_refl HTR) as HTR0.
  assert (HTLk : [ G' ; ΔL ⊢[ lD ] TL @ kL ]) by (eapply wft_lconv; [exact HTL0 | apply lequiv_sym, HkLg]).
  assert (HTRk : [ G' ; ΔR ⊢[ lD ] TR @ kR ]).
  { eapply wft_lconv; [exact (ctxconv_ty HΔ (i := lD) eq_refl HTR0) | apply lequiv_sym, HkRg]. }
  assert (Ec : tm_leq (lam k k' A b) (lam k1 k1' A' b')) by (cbn; repeat split; assumption).
  pose proof (box_rel_tm HTLk HwL HcL HcL (tm_leq_refl _)) as BL0.
  pose proof (box_rel_tm HTRk HwR HcR HcR (tm_leq_refl _)) as BR0.
  (* the index reductions *)
  pose proof (tyred_lconv _ _ _ _ HWL (lequiv_sym _ _ _ HkLg)) as HWLk.
  pose proof (tyred_lconv _ _ _ _ HWR (lequiv_sym _ _ _ HkRg)) as HWRk.
  pose proof (eqty_wf_r (i := lD) eq_refl (tyred_eq _ _ _ _ _ _ HWLk)) as HWL0.
  pose proof (eqty_wf_r (i := lD) eq_refl (tyred_eq _ _ _ _ _ _ HWRk)) as HWR0.
  assert (HcLW : [ G' ; ΔL ⊢[ lC ] lam k k' A b : tyPi c1 c2 CL BL @ kL ])
    by (eapply wf_conv; [exact HcL | apply eqty_sym, (tyred_eq _ _ _ _ _ _ HWLk)]).
  assert (HcRW : [ G' ; ΔR ⊢[ lC ] lam k1 k1' A' b' : tyPi c3 c4 CR BR @ kR ])
    by (eapply wf_conv; [exact HcR | apply eqty_sym, (tyred_eq _ _ _ _ _ _ HWRk)]).
  pose proof (MotRel_t EP EM G0 Γ0 L' φ Mt Mt l2 l2 HMt HMt (lequiv_refl _ _ Hwl2) Hφ VMtl VMtl VΓ G' σ σ Θ e e
             (GSubRel_refl_l EP EM Hσ) (SubRel_refl_l He) EL HwL (lequiv_refl _ _ HwL) HΔL (eqc_refl _ _ _ HΔL)
             (tyred_eq _ _ _ _ _ _ HWLk) HWL0 BL0 (box_rel_tm HWL0 HwL HcLW HcLW (tm_leq_refl _))) as ML.
  pose proof (MotRel_t EP EM G0 Γ0 L' φ Mt' Mt' l2' l2' HMt' HMt' (lequiv_refl _ _ Hwl2') Hφ VMtr VMtr VΓ
             G' σ' σ' Θ e' e' (GSubRel_refl_r EP EM Hσ) He'r EL HwR (lequiv_refl _ _ HwR) HΔR (eqc_refl _ _ _ HΔR)
             (tyred_eq _ _ _ _ _ _ HWRk) HWR0 BR0 (box_rel_tm HWR0 HwR HcRW HcRW (tm_leq_refl _))) as MR.
  (* the recursive calls *)
  pose proof (IHb BL BR HB0BL HB0BR) as IHb'.
  destruct (LRtm_escape IHA) as [Ha1 _]. destruct (LRtm_escape (LRtm_sym IHA)) as [Ha1' _].
  destruct (LRtm_escape IHb') as [Ha2 _]. destruct (LRtm_escape (LRtm_sym IHb')) as [Ha2' _].
  destruct (tcall HΔLA CA1 Hw' Q' HBLBR HbL Hb'L Eb IHb') as (_ & _ & _ & _ & X2).
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHA) IHA) Hl1g') as X1r.
  pose proof (LRtm_lconv (LRtm_trans (LRtm_sym IHb') IHb') Hl2g') as X2r.
  (* the reducts *)
  set (xsL := recTL k ΔL A :: rectL k' (ΔL ,, A @ k) BL b :: nil). set (xsR := recTR k1 ΔR A' :: rectR k1' (ΔR ,, A' @ k1) BR b' :: nil).
  set (rL := ((usubst_tm (bs 11) (uext (k :: k' :: nil) φ))⦃gext_s (GCtx ΔL :: GTy A :: GTy BL :: GTm b :: nil) σ⦄)[lext xsL e]).
  set (rR := ((usubst_tm (bs' 11) (uext (k1 :: k1' :: nil) φ))⦃gext_s (GCtx ΔR :: GTy A' :: GTy BR :: GTm b' :: nil) σ'⦄)[lext xsR e']).
  assert (HredL : redt (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) kL ΔL (tyPi c1 c2 CL BL) (lam k k' A b) = Some rL)
    by (apply redt_lam_inst; inst_side 11).
  assert (HredR : redt (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) kR ΔR (tyPi c3 c4 CR BR) (lam k1 k1' A' b') = Some rR)
    by (apply redt_lam_inst; inst_side 11).
  refine (rec_t_fin_lam HΔL HΔR HwL HwR HTLk HTRk HcL HcR HWLk HWRk HredL HredR ML MR _).
  refine (rec_t_br_core 11 (k :: k' :: nil) (k1 :: k1' :: nil) (GCtx ΔL :: GTy A :: GTy BL :: GTm b :: nil)
            (GCtx ΔR :: GTy A' :: GTy BR :: GTm b' :: nil) xsL xsR ltac:(cbv; lia) eq_refl eq_refl eq_refl
            ltac:(repeat constructor; assumption) ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ E (Forall2_cons _ _ E' (Forall2_nil _))))
            HΔL HΔ HkL HkR Qm (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ HΠΠ') HTL)
            (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ HΠΠ') HTR) (ctxconv_eqty HΔ (i := lD) eq_refl HΠ'R)
            HcL0 HcRL HcR0 Ec
            (GS_lam EP EM Hσ HΔL HΔ HA HA'R HAA EA HBLD HBRk HBLBR HbL Hb'R Hbb Eb)
            (GS_lam EP EM (GSubRel_refl_r EP EM Hσ) HΔR (eqc_refl _ _ _ HΔR) HA'R1 HA'R1
               (eqty_refl _ _ _ _ _ HA'R1D) (ty_leq_refl _) HBR1 HBR1 (eqty_refl _ _ _ _ _ HBR1)
               Hb'R1 Hb'R1 (eqtm_refl _ _ _ _ _ _ (lift_tm (j := lD) Hb'R1 Hl1c)) (tm_leq_refl _)) _ _ _ _ _).
  - sr_ctx; [exact X1 | exact X2].
  - sr_ctx; [exact X1r | exact X2r].
  - res_eq.
  - res_eq.
  - res_eq.
Qed.


(** ** Neutral scrutinees: the motives and branches under their binders
    (M3_DESIGN.md E13, E14) *)

#[local] Existing Instance LR_M_permRec.

Lemma EP_MT : @geq_ty EM (recGT G') (recΓT Θ) MTL MTR (lvren (lvsubst l1 φ) (ush 1)).
Proof using ELM ELP EMl HG0 He HΓ0 Hσ Hφ VMT VΓT.
  pose proof (gsw_glob _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as HG'.
  pose proof (VMT (S L') (uup φ) (usub_ok_uup _ _ _ Hφ)) as V.
  pose proof (VΓT (S L') (uup φ) (usub_ok_uup _ _ _ Hφ)) as VC.
  unfold G_us in V, VC. rewrite recGT_usubst, recΓT_usubst in V, VC. rewrite lvren_ush1_usubst in V.
  pose proof (GSubRel_uwkn EP EM (n := 1) HG0 Hσ) as X1.
  assert (HGr : [ ⊢ recGT G' ]) by exact (wf_recGT HG').
  pose proof (GSubRel_gup EP EM (D := gdCtx) X1 HGr eq_refl) as X2.
  change (guwkn 1 σ) with (guwk σ) in X2. change (guwkn 1 σ') with (guwk σ') in X2.
  pose proof (V _ _ _ X2 _ gwk_id (gwk_ok_id _)) as V'. cbn [gwa] in V'.
  pose proof (VC _ _ _ (GSubRel_refl_l EP EM X2) _ gwk_id (gwk_ok_id _)) as C. cbn [gwa] in C.
  rewrite (recΓT_gsubst _ _ Nσ) in V', C.
  pose proof (wf_ctx_lwf (gs_ctx EP EM Hσ HΓ0 compt_M)) as WΓ1.
  pose proof (SubRel_uwkn (n := 1) HG' WΓ1 He) as H1.
  pose proof (SubRel_gwkn (D := gdCtx) (Ds := nil) H1 HGr) as H2.
  pose proof (SubRel_cexts ((tyCTyp (cvar 0) (lvar 0), lzero) :: nil) _ _ _ _ H2 C
                ltac:(repeat constructor)) as H3.
  destruct (V' _ _ _ H3) as [R HR]. destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (_ & _ & Hg).
  exact Hg.
Qed.

Lemma EP_Mt : @geq_ty EM (recGt G') (recΓt Θ) MtL MtR (lvren (lvsubst l2 φ) (ush 1)).
Proof using ELM ELP EMl HG0 He HΓ0 Hσ Hφ VMt VΓt.
  pose proof (gsw_glob _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as HG'.
  pose proof (VMt (S L') (uup φ) (usub_ok_uup _ _ _ Hφ)) as V.
  pose proof (VΓt (S L') (uup φ) (usub_ok_uup _ _ _ Hφ)) as VC.
  unfold G_us in V, VC. rewrite recGt_usubst, recΓt_usubst in V, VC. rewrite lvren_ush1_usubst in V.
  pose proof (GSubRel_uwkn EP EM (n := 1) HG0 Hσ) as X1.
  assert (HGr : [ ⊢ recGT G' ]) by exact (wf_recGT HG').
  assert (HGr' : [ ⊢ recGt G' ]) by exact (wf_recGt HG').
  pose proof (GSubRel_gup EP EM (D := gdCtx) X1 HGr eq_refl) as X2.
  pose proof (GSubRel_gup EP EM (D := gdTy (cvar 0) lD (lvar 0)) X2 HGr' eq_refl) as X3.
  change (guwkn 1 σ) with (guwk σ) in X3. change (guwkn 1 σ') with (guwk σ') in X3.
  pose proof (V _ _ _ X3 _ gwk_id (gwk_ok_id _)) as V'. cbn [gwa] in V'.
  pose proof (VC _ _ _ (GSubRel_refl_l EP EM X3) _ gwk_id (gwk_ok_id _)) as C. cbn [gwa] in C.
  rewrite (recΓt_gsubst _ _ Nσ) in V', C.
  pose proof (wf_ctx_lwf (gs_ctx EP EM Hσ HΓ0 compt_M)) as WΓ1.
  pose proof (SubRel_uwkn (n := 1) HG' WΓ1 He) as H1.
  pose proof (SubRel_gwkn (D := gdTy (cvar 0) lD (lvar 0)) (Ds := gdCtx :: nil) H1 HGr') as H2.
  pose proof (SubRel_cexts ((tyCTrm (cvar 1) (gv 0) (lvar 0), lzero) :: nil) _ _ _ _ H2 C
                ltac:(repeat constructor)) as H3.
  destruct (V' _ _ _ H3) as [R HR]. destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (_ & _ & Hg).
  exact Hg.
Qed.


Lemma EP_br k : k < nbr ->
  @geq_tm EM (brG k G') (brΓ k Θ (wrapMT MTL) (wrapMt MtL) (lvsubst l1 φ) (lvsubst l2 φ)) (bsL k) (bsR k)
    (brRes k (wrapMT MTL) (wrapMt MtL)) (brLv k (lvsubst l1 φ) (lvsubst l2 φ)).
Proof using ELM ELP EMl HG0 He HrbL HΓ0 Hσ Hφ VBr VΓbr.
  intros Hk.
  pose proof (gsw_glob _ _ _ (gsr_wf_l _ _ _ _ _ _ Hσ)) as HG'.
  pose proof (usub_ok_uupn (br_nu k) _ _ _ Hφ) as Hψ.
  pose proof (VBr k Hk _ _ Hψ) as V. pose proof (VΓbr k Hk _ _ Hψ) as VC.
  unfold G_us in V, VC. rewrite (brG_usubst k G0 L' φ Hk) in V, VC.
  rewrite (brΓ_usubst k Γ0 _ _ l1 l2 φ Hk) in V, VC.
  rewrite (brRes_usubst k _ _ φ Hk), brLv_usubst in V.
  rewrite wrapMT_usubst, wrapMt_usubst in V, VC.
  (* the global substitution: [nu] fresh levels, then the branch's bindings *)
  pose proof (GSubRel_uwkn EP EM (n := br_nu k) HG0 Hσ) as X1.
  pose proof (GSubRel_gupn EP EM (brDecls k) X1 (closed_brDecls k Hk) (wf_brG HG' k Hk)) as X2.
  rewrite (brDecls_len k Hk) in X2.
  change (gupn (br_ng k) (guwkn (br_nu k) σ)) with (gbsub k σ) in X2.
  change (gupn (br_ng k) (guwkn (br_nu k) σ')) with (gbsub k σ') in X2.
  pose proof (V _ _ _ X2 _ gwk_id (gwk_ok_id _)) as V'. cbn [gwa] in V'.
  pose proof (VC _ _ _ (GSubRel_refl_l EP EM X2) _ gwk_id (gwk_ok_id _)) as C. cbn [gwa] in C.
  rewrite (brΓ_gsubst _ _ _ _ _ _ _ Hk Nσ), (brRes_gsubst _ _ _ _ Hk Nσ) in V'.
  rewrite (brΓ_gsubst _ _ _ _ _ _ _ Hk Nσ) in C.
  rewrite ?wrapMT_gsubst, ?wrapMt_gsubst in V', C.
  (* the local substitution: its fresh levels and bindings, then the recursive calls *)
  pose proof (wf_ctx_lwf (gs_ctx EP EM Hσ HΓ0 compt_M)) as WΓ1.
  pose proof (SubRel_uwkn (n := br_nu k) HG' WΓ1 He) as H1.
  destruct (brDecls_cons k Hk) as (D1 & Ds & ED).
  assert (HGb : [ ⊢ mkG (gL (gctx_uwk (br_nu k) G')) ((D1 :: Ds) ++ gΨ (gctx_uwk (br_nu k) G')) ]).
  { rewrite <- ED. exact (wf_brG HG' k Hk). }
  pose proof (SubRel_gwkn H1 HGb) as H2. rewrite <- ED, (brDecls_len k Hk) in H2.
  change (gwkn (br_ng k) (uwkn (br_nu k) e)) with (bsub k e) in H2.
  change (gwkn (br_ng k) (uwkn (br_nu k) e')) with (bsub k e') in H2.
  unfold brΓ in C.
  pose proof (SubRel_cexts _ _ _ _ _ H2 C (brLocs_lwf k _ _ _ _ _ Hk
                (lwf_lvren _ _ _ _ (uren_ok_ush _ _) (proj1 HrbL))
                (lwf_lvren _ _ _ _ (uren_ok_ush _ _) (proj1 (proj2 HrbL))))) as H3.
  rewrite (brLocs_subst _ _ _ _ _ _ Hk De), (brLocs_len _ _ _ _ _ Hk) in H3.
  pose proof (V' _ _ _ H3) as Y. rewrite (brRes_subst _ _ _ _ Hk De) in Y.
  exact (LRtm_geq Y).
Qed.


Lemma EP_all {kL kR ΔL ΔR} : lequiv (gL G') kL kR -> @geq_ctx EP G' ΔL ΔR ->
  ElimPrem EP EM G' Θ (lvsubst l1 φ) (lvsubst l2 φ) (lvsubst l1' φ) (lvsubst l2' φ) MTL MTR MtL MtR bsL bsR
    kL kR ΔL ΔR.
Proof using EL ELM ELP EMl HG0 He Hl1 Hl2 HrbL HrbR HΓ0 Hσ Hφ VBr VMT VMt VΓT VΓbr VΓt.
  intros Hk HΔ.
  destruct HrbL as (_ & _ & HMTL & HMtL & HbcL & HbL). destruct HrbR as (_ & _ & HMTR & HMtR & HbcR & HbR).
  constructor; first [ assumption | rewrite EL; assumption | exact EP_MT | exact EP_Mt | exact EP_br ].
Qed.

(** The neutral recursion on types. *)
Lemma rec_T_ne {ΔL ΔR kL kR ν ν'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lwf L' kL -> lequiv L' kL kR -> @geq_ctx EP G' ΔL ΔR ->
  @CtxRelG EP LR_P G' ΔL ΔR -> @CtxRelG EM LR_P G' ΔL ΔR ->
  @gne_tm EM G' Θ ν ν' (tyCTyp ΔL kL) lzero ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL ν) (motT (wrapMT MTR) kR ΔR ν')
    (elimT (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) kL ΔL ν)
    (elimT (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) kR ΔR ν').
Proof using EL ELM ELP EMl HG0 HMT HMT' He Hl1 Hl2 HrbL HrbR HΓ0 Hσ Hφ VBr VMT VMTr VMt VΓ VΓT VΓbr VΓt.
  intros HΔL HΔ Hw Hk HgΔ CP CM Hν.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (HΘ : [ G' ; Θ ⊢[ lM ] ]) by (pose proof (SubRel_ctx He) as X; rewrite (@gm_layer_M EP EM EMl) in X; exact X).
  assert (Hwg : lwf (gL G') kL) by (rewrite EL; exact Hw).
  assert (Hkg : lequiv (gL G') kL kR) by (rewrite EL; exact Hk).
  assert (HwR : lwf (gL G') kR) by exact (lequiv_wf_r _ _ _ Hkg).
  pose proof (CtxRelG_trans CP (CtxRelG_sym CP)) as CPL. pose proof (CtxRelG_trans CM (CtxRelG_sym CM)) as CML.
  pose proof (CtxRelG_trans (CtxRelG_sym CP) CP) as CPR. pose proof (CtxRelG_trans (CtxRelG_sym CM) CM) as CMR.
  pose proof (LR_ctyp EP EM HΘ HΔL HΔL Hwg (lequiv_refl _ _ Hwg) (conj (eqc_refl _ _ _ HΔL) (conj CPL CML))) as LL.
  pose proof (LR_ctyp EP EM HΘ HΔR HΔR HwR (lequiv_refl _ _ HwR) (conj (eqc_refl _ _ _ HΔR) (conj CPR CMR))) as LR0.
  assert (HCC : [ G' ; Θ ⊢[ lM ] tyCTyp ΔL kL ≅ tyCTyp ΔR kR @ lzero ]) by (apply eqty_CTyp; assumption).
  assert (Hν'R : @gne_tm EM G' Θ ν' ν' (tyCTyp ΔR kR) lzero).
  { apply (gne_tm_conv (gne_tm_refl_r Hν)). rewrite (@gm_layer_M EP EM EMl). exact HCC. }
  assert (BL : LRtmM lzero G' Θ (tyCTyp ΔL kL) (tyCTyp ΔL kL) ν ν')
    by (exists (@CTypRel EM LRM G' Θ ΔL ΔL kL kL); exact (conj LL (LR_neutral _ _ _ _ _ _ _ LL _ _ Hν Hν))).
  assert (BR : LRtmM lzero G' Θ (tyCTyp ΔR kR) (tyCTyp ΔR kR) ν' ν')
    by (exists (@CTypRel EM LRM G' Θ ΔR ΔR kR kR); exact (conj LR0 (LR_neutral _ _ _ _ _ _ _ LR0 _ _ Hν'R Hν'R))).
  pose proof (MotRel_T EP EM G0 Γ0 L' φ MT MT' l1 l1' HMT HMT' Hl1 Hφ VMT VMTr VΓ G' σ σ' Θ e e' Hσ He EL
                (kL := kL) (kR := kR) Hw Hk HΔL HΔ BL BR) as Mot.
  pose proof (LRty_eqM Mot) as Meq.
  pose proof (gne_tm_elimT (EP := EP) (EM := EM) Meq (EP_all Hkg HgΔ) Hν) as Hne.
  destruct Mot as [R HR].
  exists R. split; [exact HR|].
  apply (LR_neutral _ _ _ _ _ _ _ HR _ _ Hne).
  apply (gne_tm_conv Hne). rewrite (@gm_layer_M EP EM EMl). exact Meq.
Qed.

(** The neutral recursion on terms. *)
Lemma rec_t_ne {ΔL ΔR kL kR TL TR ν ν'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lwf L' kL -> lequiv L' kL kR -> @geq_ctx EP G' ΔL ΔR ->
  @CtxRelG EP LR_P G' ΔL ΔR -> @CtxRelG EM LR_P G' ΔL ΔR ->
  [ G' ; ΔL ⊢[ lD ] TL @ kL ] -> [ G' ; ΔL ⊢[ lD ] TL ≅ TR @ kL ] ->
  @VTyG EP LR_P G' ΔL TL TR kL -> @VTyG EM LR_P G' ΔL TL TR kL ->
  @gne_tm EM G' Θ ν ν' (tyCTrm ΔL TL kL) lzero ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL ν) (mott (wrapMt MtR) kR ΔR TR ν')
    (elimt (lvsubst l1 φ) (lvsubst l2 φ) (mkrb MTL MtL bsL) kL ΔL TL ν)
    (elimt (lvsubst l1' φ) (lvsubst l2' φ) (mkrb MTR MtR bsR) kR ΔR TR ν').
Proof using EL ELM ELP EMl HG0 HMt HMt' He Hl1 Hl2 HrbL HrbR HΓ0 Hσ Hφ VBr VMT VMt VMtr VΓ VΓT VΓbr VΓt.
  intros HΔL HΔ Hw Hk HgΔ CP CM HTL HTT VP VM Hν.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (HΘ : [ G' ; Θ ⊢[ lM ] ]) by (pose proof (SubRel_ctx He) as X; rewrite (@gm_layer_M EP EM EMl) in X; exact X).
  assert (Hwg : lwf (gL G') kL) by (rewrite EL; exact Hw).
  assert (Hkg : lequiv (gL G') kL kR) by (rewrite EL; exact Hk).
  assert (HwR : lwf (gL G') kR) by exact (lequiv_wf_r _ _ _ Hkg).
  pose proof (eqty_wf_r (i := lD) eq_refl HTT) as HTRL.
  assert (HTR : [ G' ; ΔR ⊢[ lD ] TR @ kR ]).
  { eapply wft_lconv; [exact (ctxconv_ty HΔ (i := lD) eq_refl HTRL) | exact (lequiv_sym _ _ _ Hkg)]. }
  pose proof (CtxRelG_trans CP (CtxRelG_sym CP)) as CPL. pose proof (CtxRelG_trans CM (CtxRelG_sym CM)) as CML.
  pose proof (CtxRelG_trans (CtxRelG_sym CP) CP) as CPR. pose proof (CtxRelG_trans (CtxRelG_sym CM) CM) as CMR.
  destruct (VTyG_escape_P EP EM CPL HΔL HTL HTRL VP) as [HgT _].
  (* the contextual types, each related to itself *)
  assert (VPL : @VTyG EP LR_P G' ΔL TL TL kL) by exact (VTyG_trans VP (VTyG_sym VP)).
  assert (VML : @VTyG EM LR_P G' ΔL TL TL kL) by exact (VTyG_trans VM (VTyG_sym VM)).
  assert (VPR : @VTyG EP LR_P G' ΔR TR TR kR).
  { eapply VTyG_lconv; [exact (VTyG_transport CP (VTyG_trans (VTyG_sym VP) VP)) | exact (lequiv_sym _ _ _ Hkg)]. }
  assert (VMR : @VTyG EM LR_P G' ΔR TR TR kR).
  { eapply VTyG_lconv; [exact (VTyG_transport CM (VTyG_trans (VTyG_sym VM) VM)) | exact (lequiv_sym _ _ _ Hkg)]. }
  pose proof (LR_ctrm EP EM HΘ HΔL HΔL HTL HTL Hwg (lequiv_refl _ _ Hwg) (conj (eqc_refl _ _ _ HΔL) (conj CPL CML))
                (conj (eqty_refl _ _ _ _ _ HTL) (conj VPL VML)) (conj (eqty_refl _ _ _ _ _ HTL) (conj VPL VML))) as LL.
  pose proof (LR_ctrm EP EM HΘ HΔR HΔR HTR HTR HwR (lequiv_refl _ _ HwR) (conj (eqc_refl _ _ _ HΔR) (conj CPR CMR))
                (conj (eqty_refl _ _ _ _ _ HTR) (conj VPR VMR)) (conj (eqty_refl _ _ _ _ _ HTR) (conj VPR VMR))) as LR0.
  assert (HCC : [ G' ; Θ ⊢[ lM ] tyCTrm ΔL TL kL ≅ tyCTrm ΔR TR kR @ lzero ]) by (apply eqty_CTrm; assumption).
  assert (Hν'R : @gne_tm EM G' Θ ν' ν' (tyCTrm ΔR TR kR) lzero).
  { apply (gne_tm_conv (gne_tm_refl_r Hν)). rewrite (@gm_layer_M EP EM EMl). exact HCC. }
  assert (BL : LRtmM lzero G' Θ (tyCTrm ΔL TL kL) (tyCTrm ΔL TL kL) ν ν')
    by (exists (@CTrmRel EM LRM G' Θ ΔL ΔL TL TL kL kL); exact (conj LL (LR_neutral _ _ _ _ _ _ _ LL _ _ Hν Hν))).
  assert (BR : LRtmM lzero G' Θ (tyCTrm ΔR TR kR) (tyCTrm ΔR TR kR) ν' ν')
    by (exists (@CTrmRel EM LRM G' Θ ΔR ΔR TR TR kR kR); exact (conj LR0 (LR_neutral _ _ _ _ _ _ _ LR0 _ _ Hν'R Hν'R))).
  pose proof (MotRel_t EP EM G0 Γ0 L' φ Mt Mt' l2 l2' HMt HMt' Hl2 Hφ VMt VMtr VΓ G' σ σ' Θ e e' Hσ He EL
                (kL := kL) (kR := kR) Hw Hk HΔL HΔ HTT HTR BL BR) as Mot.
  pose proof (LRty_eqM Mot) as Meq.
  pose proof (gne_tm_elimt (EP := EP) (EM := EM) Meq (EP_all Hkg HgΔ) HTL HTR HgT Hν) as Hne.
  destruct Mot as [R HR].
  exists R. split; [exact HR|].
  apply (LR_neutral _ _ _ _ _ _ _ HR _ _ Hne).
  apply (gne_tm_conv Hne). rewrite (@gm_layer_M EP EM EMl). exact Meq.
Qed.


(** Boxed global variables: the recursions are neutral. *)
Lemma rec_T_gvar {ΔL ΔR kL kR k U d d'} : [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k kL -> lequiv L' k kR ->
  [ G' ; ΔL ⊢[ lC ] tyGvar U d @ k ] -> [ G' ; ΔL ⊢[ lC ] tyGvar U d' @ k ] ->
  ty_leq (tyGvar U d) (tyGvar U d') ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL (boxT (tyGvar U d)))
    (motT (wrapMT MTR) kR ΔR (boxT (tyGvar U d')))
    (recTL kL ΔL (tyGvar U d)) (recTR kR ΔR (tyGvar U d')).
Proof using EL ELM ELP EMl HG0 HMT HMT' He Hl1 Hl2 HrbL HrbR HΓ0 Hσ Hφ VBr VMT VMTr VMt VΓ VΓT VΓbr VΓt.
  intros HΔL HΔ HkL HkR Hc Hc' Ec.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (HΘ : [ G' ; Θ ⊢[ lM ] ]) by (pose proof (SubRel_ctx He) as X; rewrite (@gm_layer_M EP EM EMl) in X; exact X).
  assert (HwL : lwf L' kL) by exact (lequiv_wf_r _ _ _ HkL). assert (HwR : lwf L' kR) by exact (lequiv_wf_r _ _ _ HkR).
  assert (Q : lequiv L' kL kR) by exact (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ HkL) HkR).
  assert (Qg : lequiv (gL G') kL kR) by (rewrite EL; exact Q).
  assert (HkLg : lequiv (gL G') k kL) by (rewrite EL; exact HkL). assert (HkRg : lequiv (gL G') k kR) by (rewrite EL; exact HkR).
  assert (HcL : [ G' ; ΔL ⊢[ lC ] tyGvar U d @ kL ]) by (eapply wft_lconv; [exact Hc | apply lequiv_sym, HkLg]).
  assert (Hc'L : [ G' ; ΔL ⊢[ lC ] tyGvar U d' @ kL ]) by (eapply wft_lconv; [exact Hc' | apply lequiv_sym, HkLg]).
  assert (Hc'R : [ G' ; ΔR ⊢[ lC ] tyGvar U d' @ kR ]).
  { eapply wft_lconv; [exact (ctxconv_ty HΔ (i := lC) eq_refl Hc') | apply lequiv_sym, HkRg]. }
  pose proof (box_rel HΔL HwL HcL Hc'L Ec) as BLR. pose proof (box_rel HΔR HwR Hc'R Hc'R (ty_leq_refl _)) as BRR.
  pose proof (MotRel_T EP EM G0 Γ0 L' φ MT MT' l1 l1' HMT HMT' Hl1 Hφ VMT VMTr VΓ G' σ σ' Θ e e' Hσ He EL
                (kL := kL) (kR := kR) HwL Q HΔL HΔ BLR BRR) as Mot.
  pose proof (LRty_eqM Mot) as Meq.
  destruct (CtxRelG_of_eq EP EM HΔ) as [CP _].
  destruct (CtxRelG_escape_P EP EM CP HΔL HΔR) as [HgΔ _].
  pose proof (geq_tm_sound (LRtm_geq BLR)) as Hbox. rewrite (@gm_layer_M EP EM EMl) in Hbox.
  pose proof (gne_tm_elimT_gvar (EP := EP) (EM := EM) Meq (EP_all Qg HgΔ) Hbox) as Hne.
  destruct Mot as [R HR]. exists R. split; [exact HR|].
  apply (LR_neutral _ _ _ _ _ _ _ HR _ _ Hne).
  apply (gne_tm_conv Hne). rewrite (@gm_layer_M EP EM EMl). exact (LRty_eqM (ex_intro _ R HR)).
Qed.

Lemma rec_t_glob {ΔL ΔR kL kR k T0 TL TR c c'} : boxed_global c -> boxed_global c' -> [ G' ; ΔL ⊢[ lD ] ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k kL -> lequiv L' k kR ->
  [ G' ; ΔL ⊢[ lD ] T0 ≅ TL @ k ] -> [ G' ; ΔL ⊢[ lD ] T0 ≅ TR @ k ] ->
  [ G' ; ΔL ⊢[ lC ] c : T0 @ k ] -> [ G' ; ΔL ⊢[ lC ] c' : T0 @ k ] ->
  tm_leq c c' ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt c))
    (mott (wrapMt MtR) kR ΔR TR (boxt c'))
    (rectL kL ΔL TL c) (rectR kR ΔR TR c').
Proof using EL ELM ELP EMl HG0 HMt HMt' He Hl1 Hl2 HrbL HrbR HΓ0 Hσ Hφ VBr VMT VMt VMtr VΓ VΓT VΓbr VΓt.
  intros Hg Hg' HΔL HΔ HkL HkR HTL HTR Hc Hc' Ec.
  pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR.
  assert (HΘ : [ G' ; Θ ⊢[ lM ] ]) by (pose proof (SubRel_ctx He) as X; rewrite (@gm_layer_M EP EM EMl) in X; exact X).
  assert (HwL : lwf L' kL) by exact (lequiv_wf_r _ _ _ HkL). assert (HwR : lwf L' kR) by exact (lequiv_wf_r _ _ _ HkR).
  assert (Q : lequiv L' kL kR) by exact (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ HkL) HkR).
  assert (Qg : lequiv (gL G') kL kR) by (rewrite EL; exact Q).
  assert (HkLg : lequiv (gL G') k kL) by (rewrite EL; exact HkL). assert (HkRg : lequiv (gL G') k kR) by (rewrite EL; exact HkR).
  pose proof (eqty_wf_r (i := lD) eq_refl HTL) as HTL0. pose proof (eqty_wf_r (i := lD) eq_refl HTR) as HTR0.
  assert (HTLk : [ G' ; ΔL ⊢[ lD ] TL @ kL ]) by (eapply wft_lconv; [exact HTL0 | apply lequiv_sym, HkLg]).
  assert (HTRk : [ G' ; ΔR ⊢[ lD ] TR @ kR ]).
  { eapply wft_lconv; [exact (ctxconv_ty HΔ (i := lD) eq_refl HTR0) | apply lequiv_sym, HkRg]. }
  assert (HTLR : [ G' ; ΔL ⊢[ lD ] TL ≅ TR @ kL ]).
  { eapply eqty_lconv; [exact (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ HTL) HTR) | apply lequiv_sym, HkLg]. }
  assert (HcL : [ G' ; ΔL ⊢[ lC ] c : TL @ kL ])
    by (eapply wf_lconv; [eapply wf_conv; [exact Hc | apply eqty_sym, HTL] | apply lequiv_sym, HkLg]).
  assert (Hc'L : [ G' ; ΔL ⊢[ lC ] c' : TL @ kL ])
    by (eapply wf_lconv; [eapply wf_conv; [exact Hc' | apply eqty_sym, HTL] | apply lequiv_sym, HkLg]).
  assert (Hc'R : [ G' ; ΔR ⊢[ lC ] c' : TR @ kR ]).
  { refine (ctxconv_tm HΔ (i := lC) eq_refl _).
    eapply wf_lconv; [eapply wf_conv; [exact Hc' | apply eqty_sym, HTR] | apply lequiv_sym, HkRg]. }
  pose proof (box_rel_tm HTLk HwL HcL Hc'L Ec) as BLR.
  pose proof (box_rel_tm HTRk HwR Hc'R Hc'R (tm_leq_refl _)) as BRR.
  pose proof (MotRel_t EP EM G0 Γ0 L' φ Mt Mt' l2 l2' HMt HMt' Hl2 Hφ VMt VMtr VΓ G' σ σ' Θ e e' Hσ He EL
                (kL := kL) (kR := kR) HwL Q HΔL HΔ HTLR HTRk BLR BRR) as Mot.
  pose proof (LRty_eqM Mot) as Meq.
  destruct (CtxRelG_of_eq EP EM HΔ) as [CP _]. destruct (CtxRelG_of_eq EP EM (eqc_refl _ _ _ HΔL)) as [CPL _].
  destruct (CtxRelG_escape_P EP EM CP HΔL HΔR) as [HgΔ _].
  destruct (VTyG_of_eq EP EM HTLR) as [VP _].
  destruct (VTyG_escape_P EP EM CPL HΔL HTLk (eqty_wf_r (i := lD) eq_refl HTLR) VP) as [HgT _].
  pose proof (geq_tm_sound (LRtm_geq BLR)) as Hbox. rewrite (@gm_layer_M EP EM EMl) in Hbox.
  pose proof (gne_tm_elimt_glob (EP := EP) (EM := EM) Hg Hg' Meq (EP_all Qg HgΔ) HTLk HTRk HgT Hbox) as Hne.
  destruct Mot as [R HR]. exists R. split; [exact HR|].
  apply (LR_neutral _ _ _ _ _ _ _ HR _ _ Hne).
  apply (gne_tm_conv Hne). rewrite (@gm_layer_M EP EM EMl). exact (LRty_eqM (ex_intro _ R HR)).
Qed.

End Rec.
