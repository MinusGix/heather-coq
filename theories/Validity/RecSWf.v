(** * The recursion lemmas on code: finitary well-founded trees

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

(** Finitary well-founded trees (M15b step 0): each branch in one lemma,
    its calls through [RTcall]/[Rtcall] and its payloads through [GS_br]. *)
Lemma RT_wf {Δ k A N} : lwf (gL G') k ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ,, A @ k ⊢[ lC ] N : tyNat @ lzero ] ->
  RT Δ A k -> Rt (Δ ,, A @ k) N tyNat lzero -> RT Δ (tyWf k A N) k.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtr VΓ.
  intros Hw HA HN IHA IHN Hc ΔR kL kR c' HΔ HkL HkR E W. rewrite EL in Hw.
  pose proof (sc_ctx HCD Hc) as HΔL. pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1, H into Ek end.
  match goal with H : ty_leq A ?x |- _ => rename x into A', H into EA end.
  match goal with H : tm_leq N ?x |- _ => rename x into N', H into EN end.
  match goal with H : lwf L' k1 |- _ => rename H into Hw1 end.
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  destruct (RTcall HΔL HΔ Hw Hw1 Ek HA EA ltac:(assumption) IHA)
    as (HA' & HAA & HA'R & HA'R1 & CA & CA1 & X1 & X1r).
  pose proof (eqctx_wf_l (i := lD) eq_refl CA) as HΔA.
  assert (HNat : [ G' ; Δ ,, A @ k ⊢[ lD ] tyNat ≅ tyNat @ lzero ]) by (apply eqty_refl, wft_nat; [discriminate | exact HΔA]).
  destruct (Rtcall (RH := RH) (k := lzero) (k1 := lzero) (T' := tyNat) HΔA CA1 I I (leqv_refl _) HNat HN EN ltac:(assumption) IHN)
    as (HN' & HNN & _ & HN'R1 & X2 & X2r).
  pose proof (ctxconv_tm CA (i := lC) eq_refl HN') as HN'R.
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tyWf k1 A' N' @ k1 ])
    by (apply wft_wf; [discriminate | rewrite EL; exact Hw1 | exact HA'R1 | exact HN'R1]).
  assert (HcRL : [ G' ; Δ ⊢[ lC ] tyWf k1 A' N' @ k ])
    by (eapply wft_lconv; [exact (ctxconv_ty (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | rewrite EL; exact Q]).
  refine (rec_T_br 47 (k :: nil) (k1 :: nil) (GCtx Δ :: GTy A :: GTm N :: nil) (GCtx ΔR :: GTy A' :: GTm N' :: nil)
            (recTL k Δ A :: rectL lzero (Δ ,, A @ k) tyNat N :: nil)
            (recTR k1 ΔR A' :: rectR lzero (ΔR ,, A' @ k1) tyNat N' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ Ek (Forall2_nil _)))
            HΔL HΔ HkL HkR Q Hc HcRL HcR0 ltac:(cbn; repeat split; assumption)
            (GS_br EP EM 47 (k :: nil) eq_refl Hσ _) (GS_br EP EM 47 (k1 :: nil) eq_refl (GSubRel_refl_r EP EM Hσ) _) _ _ _ _ _ _ _).
  - gs_solve.
  - gs_solve.
  - sr_ctx; [exact X1 | exact X2].
  - sr_ctx; [exact X1r | exact X2r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redT_wf_inst; inst_side 47.
  - apply redT_wf_inst; inst_side 47.
Qed.

Lemma Rt_codewf {Δ k s n} : lwf (gL G') k ->
  [ G' ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] -> [ G' ; Δ ,, tyEl k s @ k ⊢[ lC ] n : tyNat @ lzero ] ->
  Rt Δ s (tyU k) (lsuc k) -> Rt (Δ ,, tyEl k s @ k) n tyNat lzero -> Rt Δ (tmWf k s n) (tyU k) (lsuc k).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hw Hs Hn IHs IHn Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1, H into Ek end.
  match goal with H : tm_leq s ?x |- _ => rename x into s', H into Es end.
  match goal with H : tm_leq n ?x |- _ => rename x into n', H into En end.
  match goal with H : lwf L' k1 |- _ => rename H into Hw1 end.
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  assert (HUU : forall Δ j j', [ G' ; Δ ⊢[ lD ] ] -> lequiv L' j j' -> [ G' ; Δ ⊢[ lD ] tyU j ≅ tyU j' @ lsuc j ])
    by (intros; apply eqty_U; [discriminate | assumption | rewrite EL; assumption]).
  destruct (Rtcall (k := lsuc k) (k1 := lsuc k1) HΔL HΔ Hw Hw1 (leqv_lsuc _ _ Ek) (HUU _ _ _ HΔL Q) Hs Es ltac:(assumption) IHs)
    as (Hs' & Hss & Hs'R & Hs'R1 & X1 & X1r).
  assert (HEl : [ G' ; Δ ⊢[ lD ] tyEl k s @ k ]) by (apply wft_El; [discriminate | rewrite EL; exact Hw | exact (lift_tm Hs HCD)]).
  assert (CE : [ G' ⊢[ lD ] Δ ,, tyEl k s @ k ≅ ΔR ,, tyEl k s' @ k ])
    by (apply ceq_ext; [exact HΔ | exact HEl | apply eqty_El; [discriminate | rewrite EL; apply lequiv_refl, Hw | exact Hss]
                       | apply lequiv_refl, Hw]).
  assert (CE1 : [ G' ⊢[ lD ] Δ ,, tyEl k s @ k ≅ ΔR ,, tyEl k1 s' @ k1 ])
    by (apply ceq_ext; [exact HΔ | exact HEl | apply eqty_El; [discriminate | rewrite EL; exact Q | exact Hss] | exact Q]).
  pose proof (eqctx_wf_l (i := lD) eq_refl CE) as HΔE.
  assert (HNat : [ G' ; Δ ,, tyEl k s @ k ⊢[ lD ] tyNat ≅ tyNat @ lzero ]) by (apply eqty_refl, wft_nat; [discriminate | exact HΔE]).
  destruct (Rtcall (RH := RH) (k := lzero) (k1 := lzero) (T' := tyNat) HΔE CE1 I I (leqv_refl _) HNat Hn En ltac:(assumption) IHn)
    as (Hn' & Hnn & _ & Hn'R1 & X2 & X2r).
  pose proof (ctxconv_tm CE (i := lC) eq_refl Hn') as Hn'R.
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmWf k1 s' n' : tyU k1 @ lsuc k1 ])
    by (apply wf_code_wf; [discriminate | rewrite EL; exact Hw1 | exact Hs'R1 | exact Hn'R1]).
  assert (HcRL : [ G' ; Δ ⊢[ lC ] tmWf k1 s' n' : tyU k @ lsuc k ])
    by (eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0)
                                          | rewrite EL; apply lequiv_suc, Q] | exact (HUU _ _ _ HΔL Q)]).
  refine (rec_t_br 48 (k :: nil) (k1 :: nil) (GCtx Δ :: GTm s :: GTm n :: nil) (GCtx ΔR :: GTm s' :: GTm n' :: nil)
            (rectL (lsuc k) Δ (tyU k) s :: rectL lzero (Δ ,, tyEl k s @ k) tyNat n :: nil)
            (rectR (lsuc k1) ΔR (tyU k1) s' :: rectR lzero (ΔR ,, tyEl k1 s' @ k1) tyNat n' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ Ek (Forall2_nil _)))
            HΔL HΔ HkL HkR (lequiv_suc _ _ _ Q) HTL HTR (HUU _ _ _ HΔR Q) Hc HcRL HcR0 ltac:(cbn; repeat split; assumption)
            (GS_br EP EM 48 (k :: nil) eq_refl Hσ _) (GS_br EP EM 48 (k1 :: nil) eq_refl (GSubRel_refl_r EP EM Hσ) _)
            _ _ _ _ _ _ _).
  - gs_solve.
  - gs_solve.
  - sr_ctx; [exact X1 | exact X2].
  - sr_ctx; [exact X1r | exact X2r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_codewf_inst; inst_side 48.
  - apply redt_codewf_inst; inst_side 48.
Qed.

Lemma Rt_supf {Δ k A N a cs} : lwf (gL G') k ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ,, A @ k ⊢[ lC ] N : tyNat @ lzero ] -> [ G' ; Δ ⊢[ lC ] a : A @ k ] ->
  [ G' ; Δ ⊢[ lC ] cs : tyVec k (tyWf k A N) N[lsingle a] @ k ] ->
  RT Δ A k -> Rt (Δ ,, A @ k) N tyNat lzero -> Rt Δ a A k -> Rt Δ cs (tyVec k (tyWf k A N) N[lsingle a]) k ->
  Rt Δ (tmSupf k A N a cs) (tyWf k A N) k.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros Hw HA HN Ha Hcs IHA IHN IHa IHcs Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1, H into Ek end.
  match goal with H : ty_leq A ?x |- _ => rename x into A', H into EA end.
  match goal with H : tm_leq N ?x |- _ => rename x into N', H into EN end.
  match goal with H : tm_leq a ?x |- _ => rename x into a', H into Ea end.
  match goal with H : tm_leq cs ?x |- _ => rename x into cs', H into Ecs end.
  match goal with H : lwf L' k1 |- _ => rename H into Hw1 end.
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q).
  assert (Qk : lequiv (gL G') k k) by (rewrite EL; exact (lequiv_refl _ _ Hw)).
  (* the shape, the arity, the label, and their calls *)
  destruct (RTcall HΔL HΔ Hw Hw1 Ek HA EA ltac:(assumption) IHA) as (HA' & HAA & HA'R & HA'R1 & CA & CA1 & X1 & X1r).
  pose proof (eqctx_wf_l (i := lD) eq_refl CA) as HΔA.
  assert (HNat : [ G' ; Δ ,, A @ k ⊢[ lD ] tyNat ≅ tyNat @ lzero ]) by (apply eqty_refl, wft_nat; [discriminate | exact HΔA]).
  destruct (Rtcall (RH := RH) (k := lzero) (k1 := lzero) (T' := tyNat) HΔA CA1 I I (leqv_refl _) HNat HN EN ltac:(assumption) IHN)
    as (HN' & HNN & _ & HN'R1 & X2 & X2r).
  pose proof (ctxconv_tm CA (i := lC) eq_refl HN') as HN'R.
  destruct (Rtcall HΔL HΔ Hw Hw1 Ek HAA Ha Ea ltac:(assumption) IHa) as (Ha' & Haa & Ha'R0 & Ha'R1 & X3 & X3r).
  assert (Ha'R : [ G' ; ΔR ⊢[ lC ] a' : A' @ k ])
    by (eapply wf_conv; [exact Ha'R0 | exact (ctxconv_eqty HΔ (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ HAA))]).
  (* the children, at their vector type *)
  pose proof (lift_ty HA HCD) as HAD. pose proof (lift_tm HN HCD) as HND.
  pose proof (@Wf_cs_feq G' lD eq_refl ltac:(discriminate) _ _ _ _ _ _ _ _ _ Qg HAD HAA HND HNN Haa
                (lift_tm Ha HCD) (lift_tm Ha' HCD)) as HCC.
  pose proof (@Wf_cs_feq G' lD eq_refl ltac:(discriminate) _ _ _ _ _ _ _ _ _ Qk HAD HAA HND HNN Haa
                (lift_tm Ha HCD) (lift_tm Ha' HCD)) as HCC0.
  destruct (Rtcall (k1 := k1) HΔL HΔ Hw Hw1 Ek HCC Hcs Ecs ltac:(assumption) IHcs) as (Hcs' & Hcss & Hcs'R0 & Hcs'R1 & X4 & X4r).
  assert (Hcs'R : [ G' ; ΔR ⊢[ lC ] cs' : tyVec k (tyWf k A' N') N'[lsingle a'] @ k ])
    by (eapply wf_conv; [exact Hcs'R0 | exact (ctxconv_eqty HΔ (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ HCC0))]).
  (* the codes *)
  assert (HWW : [ G' ; Δ ⊢[ lD ] tyWf k A N ≅ tyWf k1 A' N' @ k ])
    by (apply eqty_wf; [discriminate | exact Qg | exact HAD | exact HAA | exact HNN]).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmSupf k1 A' N' a' cs' : tyWf k1 A' N' @ k1 ])
    by (apply wf_supf; [discriminate | rewrite EL; exact Hw1 | exact HA'R1 | exact HN'R1 | exact Ha'R1 | exact Hcs'R1]).
  assert (HcRL : [ G' ; Δ ⊢[ lC ] tmSupf k1 A' N' a' cs' : tyWf k A N @ k ])
    by (eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | exact Qg]
                        | exact HWW]).
  refine (rec_t_br 49 (k :: nil) (k1 :: nil) (GCtx Δ :: GTy A :: GTm N :: GTm a :: GTm cs :: nil)
            (GCtx ΔR :: GTy A' :: GTm N' :: GTm a' :: GTm cs' :: nil)
            (recTL k Δ A :: rectL lzero (Δ ,, A @ k) tyNat N :: rectL k Δ A a
               :: rectL k Δ (tyVec k (tyWf k A N) N[lsingle a]) cs :: nil)
            (recTR k1 ΔR A' :: rectR lzero (ΔR ,, A' @ k1) tyNat N' :: rectR k1 ΔR A' a'
               :: rectR k1 ΔR (tyVec k1 (tyWf k1 A' N') N'[lsingle a']) cs' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ Ek (Forall2_nil _)))
            HΔL HΔ HkL HkR Q HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl HWW) Hc HcRL HcR0
            ltac:(cbn; repeat split; assumption)
            (GS_br EP EM 49 (k :: nil) eq_refl Hσ _) (GS_br EP EM 49 (k1 :: nil) eq_refl (GSubRel_refl_r EP EM Hσ) _)
            _ _ _ _ _ _ _).
  - gs_solve.
  - gs_solve.
  - sr_ctx; [exact X1 | exact X2 | exact X3 | exact X4].
  - sr_ctx; [exact X1r | exact X2r | exact X3r | exact X4r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_supf_inst; inst_side 49.
  - apply redt_supf_inst; inst_side 49.
Qed.

Lemma Rt_elimWf {Δ k k' A N M c t} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ,, A @ k ⊢[ lC ] N : tyNat @ lzero ] ->
  [ G' ; Δ ,, tyWf k A N @ k ⊢[ lC ] M @ k' ] ->
  [ G' ; Δ ,, A @ k ⊢[ lC ] wfcsty k A N @ k ] ->
  [ G' ; Δ ,, A @ k ,, wfcsty k A N @ k ⊢[ lC ] wfihty k k' A N M @ lmax lzero k' ] ->
  [ G' ; Δ ,, A @ k ,, wfcsty k A N @ k ,, wfihty k k' A N M @ lmax lzero k' ⊢[ lC ] c : wfstepty k A N M @ k' ] ->
  [ G' ; Δ ⊢[ lC ] t : tyWf k A N @ k ] ->
  RT Δ A k -> Rt (Δ ,, A @ k) N tyNat lzero -> RT (Δ ,, tyWf k A N @ k) M k' ->
  Rt (Δ ,, A @ k ,, wfcsty k A N @ k ,, wfihty k k' A N M @ lmax lzero k') c (wfstepty k A N M) k' ->
  Rt Δ t (tyWf k A N) k ->
  Rt Δ (tmElimWf k k' A N M c t) (M[lsingle t]) k'.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros Hw Hw' HA HN HM HCs HI Hc Ht IHA IHN IHM IHc IHt Hc0 ΔR kL kR TL TR c0' HΔ HkL HkR HTL HTR E W.
  rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc0) as HΔL. pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1, H into Ek end.
  match goal with H : leqv k' ?x |- _ => rename x into k1', H into Ek' end.
  match goal with H : ty_leq A ?x |- _ => rename x into A', H into EA end.
  match goal with H : tm_leq N ?x |- _ => rename x into N', H into EN end.
  match goal with H : ty_leq M ?x |- _ => rename x into M', H into EM1 end.
  match goal with H : tm_leq c ?x |- _ => rename x into c', H into Ec end.
  match goal with H : tm_leq t ?x |- _ => rename x into t', H into Et end.
  match goal with H : lwf L' k1 |- _ => rename H into Hw1 end.
  match goal with H : lwf L' k1' |- _ => rename H into Hw1' end.
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q). assert (Qg' : lequiv (gL G') k' k1') by (rewrite EL; exact Q').
  assert (Qk : lequiv (gL G') k k) by (rewrite EL; exact (lequiv_refl _ _ Hw)).
  assert (Qk' : lequiv (gL G') k' k') by (rewrite EL; exact (lequiv_refl _ _ Hw')).
  (* the shape, the arity and their calls *)
  destruct (RTcall HΔL HΔ Hw Hw1 Ek HA EA ltac:(assumption) IHA) as (HA' & HAA & HA'R & HA'R1 & CA & CA1 & X1 & X1r).
  pose proof (eqctx_wf_l (i := lD) eq_refl CA) as HΔA.
  assert (HNat : [ G' ; Δ ,, A @ k ⊢[ lD ] tyNat ≅ tyNat @ lzero ]) by (apply eqty_refl, wft_nat; [discriminate | exact HΔA]).
  destruct (Rtcall (RH := RH) (k := lzero) (k1 := lzero) (T' := tyNat) HΔA CA1 I I (leqv_refl _) HNat HN EN ltac:(assumption) IHN)
    as (HN' & HNN & _ & HN'R1 & X2 & X2r).
  pose proof (ctxconv_tm CA (i := lC) eq_refl HN') as HN'R.
  pose proof (lift_ty HA HCD) as HAD. pose proof (lift_ty HA' HCD) as HA'D.
  pose proof (lift_tm HN HCD) as HND. pose proof (lift_tm HN' HCD) as HN'D.
  (* the tree type, and the motive over it *)
  assert (HWD : [ G' ; Δ ⊢[ lD ] tyWf k A N @ k ]) by (apply wft_wf; [discriminate | rewrite EL; exact Hw | exact HAD | exact HND]).
  assert (HWW : [ G' ; Δ ⊢[ lD ] tyWf k A N ≅ tyWf k1 A' N' @ k ])
    by (apply eqty_wf; [discriminate | exact Qg | exact HAD | exact HAA | exact HNN]).
  assert (HWW0 : [ G' ; Δ ⊢[ lD ] tyWf k A N ≅ tyWf k A' N' @ k ])
    by (apply eqty_wf; [discriminate | exact Qk | exact HAD | exact HAA | exact HNN]).
  pose proof (ceq_ext HΔ HWD HWW0 (lequiv_refl _ _ Hw)) as CW. pose proof (ceq_ext HΔ HWD HWW Q) as CW1.
  destruct (RTcall (eqctx_wf_l (i := lD) eq_refl CW) CW1 Hw' Hw1' Ek' HM EM1 ltac:(assumption) IHM)
    as (HM' & HMM & _ & HM'R1 & _ & _ & X3 & X3r).
  pose proof (ctxconv_ty CW (i := lC) eq_refl HM') as HM'R.
  pose proof (lift_ty HM HCD) as HMD. pose proof (lift_ty HM' HCD) as HM'D.
  (* the step's telescope, at the right levels and at the left ones *)
  destruct (@Wf_facts G' lD eq_refl ltac:(discriminate) _ _ _ _ _ _ _ _ _ _ _ Qg Qg'
              HAA HAD HA'D HNN HND HN'D HMM HMD (lift_ty HI HCD)) as (_ & _ & CS1L & ES1).
  destruct (@Wf_facts G' lD eq_refl ltac:(discriminate) _ _ _ _ _ _ _ _ _ _ _ Qk Qk'
              HAA HAD HA'D HNN HND HN'D HMM HMD (lift_ty HI HCD)) as (_ & _ & CS0L & ES0).
  destruct (eqc_ext_inv CS1L) as (CS1a & _ & EI1 & QI1). destruct (eqc_ext_inv CS1a) as (_ & _ & EF1 & QF1).
  destruct (eqc_ext_inv CS0L) as (CS0a & _ & EI0 & QI0). destruct (eqc_ext_inv CS0a) as (_ & _ & EF0 & QF0).
  assert (CS1 : [ G' ⊢[ lD ] Δ ,, A @ k ,, wfcsty k A N @ k ,, wfihty k k' A N M @ lmax lzero k'
                  ≅ ΔR ,, A' @ k1 ,, wfcsty k1 A' N' @ k1 ,, wfihty k1 k1' A' N' M' @ lmax lzero k1' ])
    by (apply eqc_ext; [apply eqc_ext; [exact CA1 | exact (lift_ty HCs HCD) | exact EF1 | exact QF1]
                       | exact (lift_ty HI HCD) | exact EI1 | exact QI1]).
  assert (CS0 : [ G' ⊢[ lD ] Δ ,, A @ k ,, wfcsty k A N @ k ,, wfihty k k' A N M @ lmax lzero k'
                  ≅ ΔR ,, A' @ k ,, wfcsty k A' N' @ k ,, wfihty k k' A' N' M' @ lmax lzero k' ])
    by (apply eqc_ext; [apply eqc_ext; [exact CA | exact (lift_ty HCs HCD) | exact EF0 | exact QF0]
                       | exact (lift_ty HI HCD) | exact EI0 | exact QI0]).
  (* the step and the scrutinee, and their calls *)
  destruct (Rtcall (eqctx_wf_l (i := lD) eq_refl CS1) CS1 Hw' Hw1' Ek' ES1 Hc Ec ltac:(assumption) IHc)
    as (Hc' & Hcc & _ & Hc'R1 & X4 & X4r).
  assert (Hc'R : [ G' ; ΔR ,, A' @ k ,, wfcsty k A' N' @ k ,, wfihty k k' A' N' M' @ lmax lzero k'
                   ⊢[ lC ] c' : wfstepty k A' N' M' @ k' ]).
  { eapply wf_conv; [exact (ctxconv_tm CS0 (i := lC) eq_refl Hc') |].
    exact (ctxconv_eqty CS0 (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ ES0)). }
  destruct (Rtcall HΔL HΔ Hw Hw1 Ek HWW Ht Et ltac:(assumption) IHt) as (Ht' & Htt & Ht'R0 & Ht'R1 & X5 & X5r).
  assert (Ht'R : [ G' ; ΔR ⊢[ lC ] t' : tyWf k A' N' @ k ])
    by (eapply wf_conv; [exact Ht'R0 | exact (ctxconv_eqty HΔ (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ HWW0))]).
  (* the codes *)
  assert (Hr1 : [ G' ; Δ ⊢[ lD ] M[lsingle t] ≅ M'[lsingle t'] @ k' ])
    by exact (eqty_subst_single_D HMM HM'D Htt (lift_tm Ht HCD) (lift_tm Ht' HCD)).
  pose proof (@sc_elimWf_q G' lC HCD _ _ _ _ _ _ _ _ _ _ _ _ _ _ ltac:(discriminate) Qg Qg'
                HA HA' (static_code_ty HCD HA HA' EA) HN HN' (static_code_tm HCD HN HN' EN)
                HM HM' (static_code_ty HCD HM HM' EM1) HI Hc' Ht Ht'
                (static_code_tm HCD Ht Ht' Et)) as HcRL.
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmElimWf k1 k1' A' N' M' c' t' : M'[lsingle t'] @ k1' ]).
  { refine (ctxconv_tm HΔ (i := lC) eq_refl _).
    eapply wf_lconv; [eapply wf_conv; [exact HcRL | apply eqty_sym, Hr1] | apply lequiv_sym, Qg']. }
  refine (rec_t_br 50 (k :: k' :: nil) (k1 :: k1' :: nil)
            (GCtx Δ :: GTy A :: GTm N :: GTy M :: GTm c :: GTm t :: nil)
            (GCtx ΔR :: GTy A' :: GTm N' :: GTy M' :: GTm c' :: GTm t' :: nil)
            (recTL k Δ A :: rectL lzero (Δ ,, A @ k) tyNat N :: recTL k' (Δ ,, tyWf k A N @ k) M
             :: rectL k' (Δ ,, A @ k ,, wfcsty k A N @ k ,, wfihty k k' A N M @ lmax lzero k') (wfstepty k A N M) c
             :: rectL k Δ (tyWf k A N) t :: nil)
            (recTR k1 ΔR A' :: rectR lzero (ΔR ,, A' @ k1) tyNat N' :: recTR k1' (ΔR ,, tyWf k1 A' N' @ k1) M'
             :: rectR k1' (ΔR ,, A' @ k1 ,, wfcsty k1 A' N' @ k1 ,, wfihty k1 k1' A' N' M' @ lmax lzero k1')
                  (wfstepty k1 A' N' M') c'
             :: rectR k1 ΔR (tyWf k1 A' N') t' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ Ek (Forall2_cons _ _ Ek' (Forall2_nil _))))
            HΔL HΔ HkL HkR Q' HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl Hr1) Hc0 HcRL HcR0
            ltac:(cbn; repeat split; assumption)
            (GS_br EP EM 50 (k :: k' :: nil) eq_refl Hσ _)
            (GS_br EP EM 50 (k1 :: k1' :: nil) eq_refl (GSubRel_refl_r EP EM Hσ) _) _ _ _ _ _ _ _).
  - gs_solve.
  - gs_solve.
  - sr_ctx_Wf; [exact X1 | exact X2 | exact X3 | exact X4 | exact X5].
  - sr_ctx_Wf; [exact X1r | exact X2r | exact X3r | exact X4r | exact X5r].
  - J_res.
  - J_res.
  - J_res.
  - apply redt_elimWf_inst; inst_side 50.
  - apply redt_elimWf_inst; inst_side 50.
Qed.

End Rec.
