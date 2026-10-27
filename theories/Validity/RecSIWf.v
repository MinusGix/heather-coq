(** * The recursion lemmas on code: dependent tuples and indexed trees (M17c)

    A part of [RecS.v]'s Section [Rec], reopened over the same data and
    hypotheses ([RecH.RecHyps], RecSBase.v) so that the parts build in
    parallel. *)
From DeLaM.Syntax Require Import LevelLwf.
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

(** Dependent tuples and indexed trees (M17c), as [Wf]'s (RecSWf.v): each
    branch in one lemma, its calls through [RTcall]/[Rtcall] and its
    payloads through [GS_br]. A right payload whose declared type mentions
    an earlier payload is typed at the right payloads' instance, by
    converting along the earlier calls' equations. *)
Lemma RT_dvec {Δ k n F} : lwf (gL G') k ->
  [ G' ; Δ ⊢[ lC ] n : tyNat @ lzero ] -> [ G' ; Δ ,, tyFin n @ lzero ⊢[ lC ] F @ k ] ->
  Rt Δ n tyNat lzero -> RT (Δ ,, tyFin n @ lzero) F k -> RT Δ (tyDVec k n F) k.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtr VΓ.
  intros Hw Hn HF IHn IHF Hc ΔR kL kR c' HΔ HkL HkR E W. rewrite EL in Hw.
  pose proof (sc_ctx HCD Hc) as HΔL. pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1, H into Ek end.
  match goal with H : tm_leq n ?x |- _ => rename x into n', H into En end.
  match goal with H : ty_leq F ?x |- _ => rename x into F', H into EF end.
  match goal with H : lwf L' k1 |- _ => rename H into Hw1 end.
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  assert (HNat : [ G' ; Δ ⊢[ lD ] tyNat ≅ tyNat @ lzero ]) by (apply eqty_refl, wft_nat; [discriminate | exact HΔL]).
  destruct (Rtcall (RH := RH) (k := lzero) (k1 := lzero) (T' := tyNat) HΔL HΔ I I (leqv_refl _) HNat Hn En ltac:(assumption) IHn)
    as (Hn' & Hnn & Hn'R & Hn'R1 & X1 & X1r).
  assert (HFin : [ G' ; Δ ⊢[ lD ] tyFin n @ lzero ]) by (apply wft_fin; [discriminate | exact (lift_tm Hn HCD)]).
  assert (CF : [ G' ⊢[ lD ] Δ ,, tyFin n @ lzero ≅ ΔR ,, tyFin n' @ lzero ])
    by (apply ceq_ext; [exact HΔ | exact HFin | apply eqty_fin; [discriminate | exact Hnn] | exact (lequiv_refl L' lzero I)]).
  pose proof (eqctx_wf_l (i := lD) eq_refl CF) as HΔF.
  destruct (RTcall HΔF CF Hw Hw1 Ek HF EF ltac:(assumption) IHF) as (HF' & HFF & HF'R & HF'R1 & _ & _ & X2 & X2r).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tyDVec k1 n' F' @ k1 ])
    by (apply wft_dvec; [discriminate | rewrite EL; exact Hw1 | exact Hn'R1 | exact HF'R1]).
  assert (HcRL : [ G' ; Δ ⊢[ lC ] tyDVec k1 n' F' @ k ])
    by (eapply wft_lconv; [exact (ctxconv_ty (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | rewrite EL; exact Q]).
  refine (rec_T_br 55 (k :: nil) (k1 :: nil) (GCtx Δ :: GTm n :: GTy F :: nil) (GCtx ΔR :: GTm n' :: GTy F' :: nil)
            (rectL lzero Δ tyNat n :: recTL k (Δ ,, tyFin n @ lzero) F :: nil)
            (rectR lzero ΔR tyNat n' :: recTR k1 (ΔR ,, tyFin n' @ lzero) F' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ Ek (Forall2_nil _)))
            HΔL HΔ HkL HkR Q Hc HcRL HcR0 ltac:(cbn; repeat split; assumption)
            (GS_br EP EM 55 (k :: nil) eq_refl Hσ _) (GS_br EP EM 55 (k1 :: nil) eq_refl (GSubRel_refl_r EP EM Hσ) _) _ _ _ _ _ _ _).
  - gs_solve.
  - gs_solve.
  - sr_ctx; [exact X1 | exact X2].
  - sr_ctx; [exact X1r | exact X2r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redT_dvec_inst; inst_side 55.
  - apply redT_dvec_inst; inst_side 55.
Qed.

Lemma Rt_codedvec {Δ k n f} : lwf (gL G') k ->
  [ G' ; Δ ⊢[ lC ] n : tyNat @ lzero ] -> [ G' ; Δ ,, tyFin n @ lzero ⊢[ lC ] f : tyU k @ lsuc k ] ->
  Rt Δ n tyNat lzero -> Rt (Δ ,, tyFin n @ lzero) f (tyU k) (lsuc k) -> Rt Δ (tmDVec k n f) (tyU k) (lsuc k).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hw Hn Hf IHn IHf Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1, H into Ek end.
  match goal with H : tm_leq n ?x |- _ => rename x into n', H into En end.
  match goal with H : tm_leq f ?x |- _ => rename x into f', H into Ef end.
  match goal with H : lwf L' k1 |- _ => rename H into Hw1 end.
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  assert (HUU : forall Δ j j', [ G' ; Δ ⊢[ lD ] ] -> lequiv L' j j' -> [ G' ; Δ ⊢[ lD ] tyU j ≅ tyU j' @ lsuc j ])
    by (intros; apply eqty_U; [discriminate | assumption | rewrite EL; assumption]).
  assert (HNat : [ G' ; Δ ⊢[ lD ] tyNat ≅ tyNat @ lzero ]) by (apply eqty_refl, wft_nat; [discriminate | exact HΔL]).
  destruct (Rtcall (RH := RH) (k := lzero) (k1 := lzero) (T' := tyNat) HΔL HΔ I I (leqv_refl _) HNat Hn En ltac:(assumption) IHn)
    as (Hn' & Hnn & Hn'R & Hn'R1 & X1 & X1r).
  assert (HFin : [ G' ; Δ ⊢[ lD ] tyFin n @ lzero ]) by (apply wft_fin; [discriminate | exact (lift_tm Hn HCD)]).
  assert (CF : [ G' ⊢[ lD ] Δ ,, tyFin n @ lzero ≅ ΔR ,, tyFin n' @ lzero ])
    by (apply ceq_ext; [exact HΔ | exact HFin | apply eqty_fin; [discriminate | exact Hnn] | exact (lequiv_refl L' lzero I)]).
  pose proof (eqctx_wf_l (i := lD) eq_refl CF) as HΔF.
  destruct (Rtcall (k := lsuc k) (k1 := lsuc k1) HΔF CF Hw Hw1 (leqv_lsuc _ _ Ek) (HUU _ _ _ HΔF Q) Hf Ef ltac:(assumption) IHf)
    as (Hf' & Hff & Hf'R & Hf'R1 & X2 & X2r).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmDVec k1 n' f' : tyU k1 @ lsuc k1 ])
    by (apply wf_code_dvec; [discriminate | rewrite EL; exact Hw1 | exact Hn'R1 | exact Hf'R1]).
  assert (HcRL : [ G' ; Δ ⊢[ lC ] tmDVec k1 n' f' : tyU k @ lsuc k ])
    by (eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0)
                                          | rewrite EL; apply lequiv_suc, Q] | exact (HUU _ _ _ HΔL Q)]).
  refine (rec_t_br 56 (k :: nil) (k1 :: nil) (GCtx Δ :: GTm n :: GTm f :: nil) (GCtx ΔR :: GTm n' :: GTm f' :: nil)
            (rectL lzero Δ tyNat n :: rectL (lsuc k) (Δ ,, tyFin n @ lzero) (tyU k) f :: nil)
            (rectR lzero ΔR tyNat n' :: rectR (lsuc k1) (ΔR ,, tyFin n' @ lzero) (tyU k1) f' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption) (uext_leqv (Forall2_cons _ _ Ek (Forall2_nil _)))
            HΔL HΔ HkL HkR (lequiv_suc _ _ _ Q) HTL HTR (HUU _ _ _ HΔR Q) Hc HcRL HcR0 ltac:(cbn; repeat split; assumption)
            (GS_br EP EM 56 (k :: nil) eq_refl Hσ _) (GS_br EP EM 56 (k1 :: nil) eq_refl (GSubRel_refl_r EP EM Hσ) _)
            _ _ _ _ _ _ _).
  - gs_solve.
  - gs_solve.
  - sr_ctx; [exact X1 | exact X2].
  - sr_ctx; [exact X1r | exact X2r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_codedvec_inst; inst_side 56.
  - apply redt_codedvec_inst; inst_side 56.
Qed.

Lemma RT_iwf {Δ k ki X A N Ot C m} : lwf (gL G') k -> lwf (gL G') ki ->
  [ G' ; Δ ⊢[ lC ] X @ ki ] -> [ G' ; Δ ⊢[ lC ] A @ k ] ->
  [ G' ; Δ ,, A @ k ⊢[ lC ] N : tyNat @ lzero ] -> [ G' ; Δ ,, A @ k ⊢[ lC ] Ot : X⟨↑⟩ @ ki ] ->
  [ G' ; Δ ,, A @ k ,, tyFin N @ lzero ⊢[ lC ] C : X⟨↑⟩⟨↑⟩ @ ki ] -> [ G' ; Δ ⊢[ lC ] m : X @ ki ] ->
  RT Δ X ki -> RT Δ A k -> Rt (Δ ,, A @ k) N tyNat lzero -> Rt (Δ ,, A @ k) Ot X⟨↑⟩ ki ->
  Rt (Δ ,, A @ k ,, tyFin N @ lzero) C X⟨↑⟩⟨↑⟩ ki -> Rt Δ m X ki ->
  RT Δ (tyIWf k ki X A N Ot C m) (lmax k ki).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtr VΓ.
  intros Hw Hwi HX HA HN HO HC Hm IHX IHA IHN IHO IHC IHm Hc ΔR kL kR c' HΔ HkL HkR E W.
  rewrite EL in Hw, Hwi.
  pose proof (sc_ctx HCD Hc) as HΔL. pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1, H into Ek end.
  match goal with H : leqv ki ?x |- _ => rename x into ki1, H into Eki end.
  match goal with H : ty_leq X ?x |- _ => rename x into X', H into EX end.
  match goal with H : ty_leq A ?x |- _ => rename x into A', H into EA end.
  match goal with H : tm_leq N ?x |- _ => rename x into N', H into EN end.
  match goal with H : tm_leq Ot ?x |- _ => rename x into Ot', H into EO end.
  match goal with H : tm_leq C ?x |- _ => rename x into C', H into EC end.
  match goal with H : tm_leq m ?x |- _ => rename x into m', H into Em end.
  match goal with H : lwf L' k1 |- _ => rename H into Hw1 end.
  match goal with H : lwf L' ki1 |- _ => rename H into Hwi1 end.
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  assert (Qi : lequiv L' ki ki1) by (apply lq; assumption).
  assert (QM : lequiv L' (lmax k ki) (lmax k1 ki1)) by (apply lequiv_max; assumption).
  assert (Qki : lequiv L' ki ki) by exact (lequiv_refl _ _ Hwi).
  (* the index type, the shapes, and the arity *)
  destruct (RTcall HΔL HΔ Hwi Hwi1 Eki HX EX ltac:(assumption) IHX)
    as (HX' & HXX & HX'R & HX'R1 & _ & _ & X1 & X1r).
  destruct (RTcall HΔL HΔ Hw Hw1 Ek HA EA ltac:(assumption) IHA)
    as (HA' & HAA & HA'R & HA'R1 & CA & CA1 & X2 & X2r).
  pose proof (eqctx_wf_l (i := lD) eq_refl CA) as HΔA.
  assert (HNat : [ G' ; Δ ,, A @ k ⊢[ lD ] tyNat ≅ tyNat @ lzero ]) by (apply eqty_refl, wft_nat; [discriminate | exact HΔA]).
  destruct (Rtcall (RH := RH) (k := lzero) (k1 := lzero) (T' := tyNat) HΔA CA1 I I (leqv_refl _) HNat HN EN ltac:(assumption) IHN)
    as (HN' & HNN & _ & HN'R1 & X3 & X3r).
  pose proof (ctxconv_tm CA (i := lC) eq_refl HN') as HN'R.
  (* the output index, under the shape *)
  pose proof (wk1_eqty_g G' lD _ _ _ _ _ _ HΔA HXX) as HXX1.
  assert (HXX1' : [ G' ; Δ ,, A @ k ⊢[ lD ] X⟨↑⟩ ≅ X'⟨↑⟩ @ ki ]) by exact HXX1.
  destruct (Rtcall (k := ki) (k1 := ki1) (T' := X'⟨↑⟩) HΔA CA1 Hwi Hwi1 Eki HXX1' HO EO ltac:(assumption) IHO)
    as (HO' & HOO & _ & HO'R1 & X4 & X4r).
  pose proof (ctxconv_tm CA (i := lC) eq_refl (wf_conv _ _ _ _ _ _ _ HO' (eqty_sym _ _ _ _ _ _ HXX1'))) as HO'R.
  (* the child index, under the shape and a position *)
  assert (HFin : [ G' ; Δ ,, A @ k ⊢[ lD ] tyFin N @ lzero ]) by (apply wft_fin; [discriminate | exact (lift_tm HN HCD)]).
  assert (EFin : [ G' ; Δ ,, A @ k ⊢[ lD ] tyFin N ≅ tyFin N' @ lzero ]) by (apply eqty_fin; [discriminate | exact HNN]).
  assert (CF : [ G' ⊢[ lD ] Δ ,, A @ k ,, tyFin N @ lzero ≅ ΔR ,, A' @ k ,, tyFin N' @ lzero ])
    by (apply ceq_ext; [exact CA | exact HFin | exact EFin | exact (lequiv_refl L' lzero I)]).
  assert (CF1 : [ G' ⊢[ lD ] Δ ,, A @ k ,, tyFin N @ lzero ≅ ΔR ,, A' @ k1 ,, tyFin N' @ lzero ])
    by (apply ceq_ext; [exact CA1 | exact HFin | exact EFin | exact (lequiv_refl L' lzero I)]).
  pose proof (eqctx_wf_l (i := lD) eq_refl CF) as HΔAF.
  pose proof (wk1_eqty_g G' lD _ _ _ _ _ _ HΔAF HXX1') as HXX2.
  assert (HXX2' : [ G' ; Δ ,, A @ k ,, tyFin N @ lzero ⊢[ lD ] X⟨↑⟩⟨↑⟩ ≅ X'⟨↑⟩⟨↑⟩ @ ki ]) by exact HXX2.
  destruct (Rtcall (k := ki) (k1 := ki1) (T' := X'⟨↑⟩⟨↑⟩) HΔAF CF1 Hwi Hwi1 Eki HXX2' HC EC ltac:(assumption) IHC)
    as (HC' & HCC & _ & HC'R1 & X5 & X5r).
  pose proof (ctxconv_tm CF (i := lC) eq_refl (wf_conv _ _ _ _ _ _ _ HC' (eqty_sym _ _ _ _ _ _ HXX2'))) as HC'R.
  (* the index *)
  destruct (Rtcall HΔL HΔ Hwi Hwi1 Eki HXX Hm Em ltac:(assumption) IHm) as (Hm' & Hmm & _ & Hm'R1 & X6 & X6r).
  pose proof (ctxconv_tm HΔ (i := lC) eq_refl (wf_conv _ _ _ _ _ _ _ Hm' (eqty_sym _ _ _ _ _ _ HXX))) as Hm'R.
  (* the codes *)
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tyIWf k1 ki1 X' A' N' Ot' C' m' @ lmax k1 ki1 ])
    by (apply wft_iwf; [discriminate | rewrite EL; exact Hw1 | rewrite EL; exact Hwi1 | exact HX'R1 | exact HA'R1
                       | exact HN'R1 | exact HO'R1 | exact HC'R1 | exact Hm'R1]).
  assert (HcRL : [ G' ; Δ ⊢[ lC ] tyIWf k1 ki1 X' A' N' Ot' C' m' @ lmax k ki ])
    by (eapply wft_lconv; [exact (ctxconv_ty (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0) | rewrite EL; exact QM]).
  refine (rec_T_br 57 (k :: ki :: nil) (k1 :: ki1 :: nil)
            (GCtx Δ :: GTy X :: GTy A :: GTm N :: GTm Ot :: GTm C :: GTm m :: nil)
            (GCtx ΔR :: GTy X' :: GTy A' :: GTm N' :: GTm Ot' :: GTm C' :: GTm m' :: nil)
            (recTL ki Δ X :: recTL k Δ A :: rectL lzero (Δ ,, A @ k) tyNat N :: rectL ki (Δ ,, A @ k) X⟨↑⟩ Ot
               :: rectL ki (Δ ,, A @ k ,, tyFin N @ lzero) X⟨↑⟩⟨↑⟩ C :: rectL ki Δ X m :: nil)
            (recTR ki1 ΔR X' :: recTR k1 ΔR A' :: rectR lzero (ΔR ,, A' @ k1) tyNat N'
               :: rectR ki1 (ΔR ,, A' @ k1) X'⟨↑⟩ Ot' :: rectR ki1 (ΔR ,, A' @ k1 ,, tyFin N' @ lzero) X'⟨↑⟩⟨↑⟩ C'
               :: rectR ki1 ΔR X' m' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ Ek (Forall2_cons _ _ Eki (Forall2_nil _))))
            HΔL HΔ HkL HkR QM Hc HcRL HcR0 ltac:(cbn; repeat split; assumption)
            (GS_br EP EM 57 (k :: ki :: nil) eq_refl Hσ _)
            (GS_br EP EM 57 (k1 :: ki1 :: nil) eq_refl (GSubRel_refl_r EP EM Hσ) _) _ _ _ _ _ _ _).
  - gs_solve.
  - gs_solve.
  - sr_ctx_IWf; [exact X1 | exact X2 | exact X3 | exact X4 | exact X5 | exact X6].
  - sr_ctx_IWf; [exact X1r | exact X2r | exact X3r | exact X4r | exact X5r | exact X6r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redT_iwf_inst; inst_side 57.
  - apply redT_iwf_inst; inst_side 57.
Qed.

Lemma Rt_codeiwf {Δ k ki x s n o c m} : lwf (gL G') k -> lwf (gL G') ki ->
  [ G' ; Δ ⊢[ lC ] x : tyU ki @ lsuc ki ] -> [ G' ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] ->
  [ G' ; Δ ,, tyEl k s @ k ⊢[ lC ] n : tyNat @ lzero ] ->
  [ G' ; Δ ,, tyEl k s @ k ⊢[ lC ] o : tyEl ki x⟨↑⟩ @ ki ] ->
  [ G' ; Δ ,, tyEl k s @ k ,, tyFin n @ lzero ⊢[ lC ] c : tyEl ki x⟨↑⟩⟨↑⟩ @ ki ] ->
  [ G' ; Δ ⊢[ lC ] m : tyEl ki x @ ki ] ->
  Rt Δ x (tyU ki) (lsuc ki) -> Rt Δ s (tyU k) (lsuc k) -> Rt (Δ ,, tyEl k s @ k) n tyNat lzero ->
  Rt (Δ ,, tyEl k s @ k) o (tyEl ki x⟨↑⟩) ki -> Rt (Δ ,, tyEl k s @ k ,, tyFin n @ lzero) c (tyEl ki x⟨↑⟩⟨↑⟩) ki ->
  Rt Δ m (tyEl ki x) ki ->
  Rt Δ (tmIWf k ki x s n o c m) (tyU (lmax k ki)) (lsuc (lmax k ki)).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hw Hwi Hx Hs Hn Ho Hc Hm IHx IHs IHn IHo IHc IHm Hc0 ΔR kL kR TL TR c0' HΔ HkL HkR HTL HTR E W.
  rewrite EL in Hw, Hwi.
  pose proof (sc_ctx_tm HCD Hc0) as HΔL. pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1, H into Ek end.
  match goal with H : leqv ki ?x |- _ => rename x into ki1, H into Eki end.
  match goal with H : tm_leq x ?y |- _ => rename y into x', H into Ex end.
  match goal with H : tm_leq s ?x |- _ => rename x into s', H into Es end.
  match goal with H : tm_leq n ?x |- _ => rename x into n', H into En end.
  match goal with H : tm_leq o ?x |- _ => rename x into o', H into Eo end.
  match goal with H : tm_leq c ?x |- _ => rename x into c', H into Ec end.
  match goal with H : tm_leq m ?x |- _ => rename x into m', H into Em end.
  match goal with H : lwf L' k1 |- _ => rename H into Hw1 end.
  match goal with H : lwf L' ki1 |- _ => rename H into Hwi1 end.
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  assert (Qi : lequiv L' ki ki1) by (apply lq; assumption).
  assert (QM : lequiv L' (lmax k ki) (lmax k1 ki1)) by (apply lequiv_max; assumption).
  assert (Qki : lequiv L' ki ki) by exact (lequiv_refl _ _ Hwi).
  assert (HUU : forall Δ j j', [ G' ; Δ ⊢[ lD ] ] -> lequiv L' j j' -> [ G' ; Δ ⊢[ lD ] tyU j ≅ tyU j' @ lsuc j ])
    by (intros; apply eqty_U; [discriminate | assumption | rewrite EL; assumption]).
  assert (HEE : forall Δ j j' t t', lequiv L' j j' -> [ G' ; Δ ⊢[ lD ] t ≅ t' : tyU j @ lsuc j ] ->
                  [ G' ; Δ ⊢[ lD ] tyEl j t ≅ tyEl j' t' @ j ])
    by (intros; apply eqty_El; [discriminate | rewrite EL; assumption | assumption]).
  (* the codes of the index type and of the shapes *)
  destruct (Rtcall (k := lsuc ki) (k1 := lsuc ki1) HΔL HΔ Hwi Hwi1 (leqv_lsuc _ _ Eki) (HUU _ _ _ HΔL Qi) Hx Ex
              ltac:(assumption) IHx) as (Hx' & Hxx & Hx'R & Hx'R1 & X1 & X1r).
  destruct (Rtcall (k := lsuc k) (k1 := lsuc k1) HΔL HΔ Hw Hw1 (leqv_lsuc _ _ Ek) (HUU _ _ _ HΔL Q) Hs Es
              ltac:(assumption) IHs) as (Hs' & Hss & Hs'R & Hs'R1 & X2 & X2r).
  assert (HEl : [ G' ; Δ ⊢[ lD ] tyEl k s @ k ]) by (apply wft_El; [discriminate | rewrite EL; exact Hw | exact (lift_tm Hs HCD)]).
  assert (CE : [ G' ⊢[ lD ] Δ ,, tyEl k s @ k ≅ ΔR ,, tyEl k s' @ k ])
    by (apply ceq_ext; [exact HΔ | exact HEl | exact (HEE _ _ _ _ _ (lequiv_refl _ _ Hw) Hss) | exact (lequiv_refl _ _ Hw)]).
  assert (CE1 : [ G' ⊢[ lD ] Δ ,, tyEl k s @ k ≅ ΔR ,, tyEl k1 s' @ k1 ])
    by (apply ceq_ext; [exact HΔ | exact HEl | exact (HEE _ _ _ _ _ Q Hss) | exact Q]).
  pose proof (eqctx_wf_l (i := lD) eq_refl CE) as HΔE.
  (* the arity *)
  assert (HNat : [ G' ; Δ ,, tyEl k s @ k ⊢[ lD ] tyNat ≅ tyNat @ lzero ]) by (apply eqty_refl, wft_nat; [discriminate | exact HΔE]).
  destruct (Rtcall (RH := RH) (k := lzero) (k1 := lzero) (T' := tyNat) HΔE CE1 I I (leqv_refl _) HNat Hn En ltac:(assumption) IHn)
    as (Hn' & Hnn & _ & Hn'R1 & X3 & X3r).
  pose proof (ctxconv_tm CE (i := lC) eq_refl Hn') as Hn'R.
  (* the output index *)
  pose proof (wk1_eqtm_g G' lD _ _ _ _ _ _ _ HΔE Hxx) as Hxx1.
  assert (Hxx1' : [ G' ; Δ ,, tyEl k s @ k ⊢[ lD ] x⟨↑⟩ ≅ x'⟨↑⟩ : tyU ki @ lsuc ki ]) by exact Hxx1.
  pose proof (HEE _ _ _ _ _ Qi Hxx1') as HTo. pose proof (HEE _ _ _ _ _ Qki Hxx1') as HTo0.
  destruct (Rtcall (k := ki) (k1 := ki1) HΔE CE1 Hwi Hwi1 Eki HTo Ho Eo ltac:(assumption) IHo)
    as (Ho' & Hoo & _ & Ho'R1 & X4 & X4r).
  pose proof (ctxconv_tm CE (i := lC) eq_refl (wf_conv _ _ _ _ _ _ _ Ho' (eqty_sym _ _ _ _ _ _ HTo0))) as Ho'R.
  (* the child index *)
  assert (HFin : [ G' ; Δ ,, tyEl k s @ k ⊢[ lD ] tyFin n @ lzero ]) by (apply wft_fin; [discriminate | exact (lift_tm Hn HCD)]).
  assert (EFin : [ G' ; Δ ,, tyEl k s @ k ⊢[ lD ] tyFin n ≅ tyFin n' @ lzero ]) by (apply eqty_fin; [discriminate | exact Hnn]).
  assert (CF : [ G' ⊢[ lD ] Δ ,, tyEl k s @ k ,, tyFin n @ lzero ≅ ΔR ,, tyEl k s' @ k ,, tyFin n' @ lzero ])
    by (apply ceq_ext; [exact CE | exact HFin | exact EFin | exact (lequiv_refl L' lzero I)]).
  assert (CF1 : [ G' ⊢[ lD ] Δ ,, tyEl k s @ k ,, tyFin n @ lzero ≅ ΔR ,, tyEl k1 s' @ k1 ,, tyFin n' @ lzero ])
    by (apply ceq_ext; [exact CE1 | exact HFin | exact EFin | exact (lequiv_refl L' lzero I)]).
  pose proof (eqctx_wf_l (i := lD) eq_refl CF) as HΔEF.
  pose proof (wk1_eqtm_g G' lD _ _ _ _ _ _ _ HΔEF Hxx1') as Hxx2.
  assert (Hxx2' : [ G' ; Δ ,, tyEl k s @ k ,, tyFin n @ lzero ⊢[ lD ] x⟨↑⟩⟨↑⟩ ≅ x'⟨↑⟩⟨↑⟩ : tyU ki @ lsuc ki ])
    by exact Hxx2.
  pose proof (HEE _ _ _ _ _ Qi Hxx2') as HTc. pose proof (HEE _ _ _ _ _ Qki Hxx2') as HTc0.
  destruct (Rtcall (k := ki) (k1 := ki1) HΔEF CF1 Hwi Hwi1 Eki HTc Hc Ec ltac:(assumption) IHc)
    as (Hc' & Hcc & _ & Hc'R1 & X5 & X5r).
  pose proof (ctxconv_tm CF (i := lC) eq_refl (wf_conv _ _ _ _ _ _ _ Hc' (eqty_sym _ _ _ _ _ _ HTc0))) as Hc'R.
  (* the index *)
  pose proof (HEE _ _ _ _ _ Qi Hxx) as HTm. pose proof (HEE _ _ _ _ _ Qki Hxx) as HTm0.
  destruct (Rtcall (k := ki) (k1 := ki1) HΔL HΔ Hwi Hwi1 Eki HTm Hm Em ltac:(assumption) IHm)
    as (Hm' & Hmm & _ & Hm'R1 & X6 & X6r).
  pose proof (ctxconv_tm HΔ (i := lC) eq_refl (wf_conv _ _ _ _ _ _ _ Hm' (eqty_sym _ _ _ _ _ _ HTm0))) as Hm'R.
  (* the codes *)
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmIWf k1 ki1 x' s' n' o' c' m' : tyU (lmax k1 ki1) @ lsuc (lmax k1 ki1) ])
    by (apply wf_code_iwf; [discriminate | rewrite EL; exact Hw1 | rewrite EL; exact Hwi1 | exact Hx'R1 | exact Hs'R1
                           | exact Hn'R1 | exact Ho'R1 | exact Hc'R1 | exact Hm'R1]).
  assert (HcRL : [ G' ; Δ ⊢[ lC ] tmIWf k1 ki1 x' s' n' o' c' m' : tyU (lmax k ki) @ lsuc (lmax k ki) ])
    by (eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0)
                                          | rewrite EL; apply lequiv_suc, QM] | exact (HUU _ _ _ HΔL QM)]).
  refine (rec_t_br 58 (k :: ki :: nil) (k1 :: ki1 :: nil)
            (GCtx Δ :: GTm x :: GTm s :: GTm n :: GTm o :: GTm c :: GTm m :: nil)
            (GCtx ΔR :: GTm x' :: GTm s' :: GTm n' :: GTm o' :: GTm c' :: GTm m' :: nil)
            (rectL (lsuc ki) Δ (tyU ki) x :: rectL (lsuc k) Δ (tyU k) s :: rectL lzero (Δ ,, tyEl k s @ k) tyNat n
               :: rectL ki (Δ ,, tyEl k s @ k) (tyEl ki x⟨↑⟩) o
               :: rectL ki (Δ ,, tyEl k s @ k ,, tyFin n @ lzero) (tyEl ki x⟨↑⟩⟨↑⟩) c
               :: rectL ki Δ (tyEl ki x) m :: nil)
            (rectR (lsuc ki1) ΔR (tyU ki1) x' :: rectR (lsuc k1) ΔR (tyU k1) s'
               :: rectR lzero (ΔR ,, tyEl k1 s' @ k1) tyNat n'
               :: rectR ki1 (ΔR ,, tyEl k1 s' @ k1) (tyEl ki1 x'⟨↑⟩) o'
               :: rectR ki1 (ΔR ,, tyEl k1 s' @ k1 ,, tyFin n' @ lzero) (tyEl ki1 x'⟨↑⟩⟨↑⟩) c'
               :: rectR ki1 ΔR (tyEl ki1 x') m' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ Ek (Forall2_cons _ _ Eki (Forall2_nil _))))
            HΔL HΔ HkL HkR (lequiv_suc _ _ _ QM) HTL HTR (HUU _ _ _ HΔR QM) Hc0 HcRL HcR0
            ltac:(cbn; repeat split; assumption)
            (GS_br EP EM 58 (k :: ki :: nil) eq_refl Hσ _)
            (GS_br EP EM 58 (k1 :: ki1 :: nil) eq_refl (GSubRel_refl_r EP EM Hσ) _)
            _ _ _ _ _ _ _).
  - gs_solve.
  - gs_solve.
  - sr_ctx_IWf; [exact X1 | exact X2 | exact X3 | exact X4 | exact X5 | exact X6].
  - sr_ctx_IWf; [exact X1r | exact X2r | exact X3r | exact X4r | exact X5r | exact X6r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_codeiwf_inst; inst_side 58.
  - apply redt_codeiwf_inst; inst_side 58.
Qed.

Lemma Rt_supi {Δ k ki X A N Ot C a cs} : lwf (gL G') k -> lwf (gL G') ki ->
  [ G' ; Δ ⊢[ lC ] X @ ki ] -> [ G' ; Δ ⊢[ lC ] A @ k ] ->
  [ G' ; Δ ,, A @ k ⊢[ lC ] N : tyNat @ lzero ] -> [ G' ; Δ ,, A @ k ⊢[ lC ] Ot : X⟨↑⟩ @ ki ] ->
  [ G' ; Δ ,, A @ k ,, tyFin N @ lzero ⊢[ lC ] C : X⟨↑⟩⟨↑⟩ @ ki ] -> [ G' ; Δ ⊢[ lC ] a : A @ k ] ->
  [ G' ; Δ ⊢[ lC ] cs : tyDVec (lmax k ki) N[lsingle a] (iwfFam k ki X A N Ot C a) @ lmax k ki ] ->
  RT Δ X ki -> RT Δ A k -> Rt (Δ ,, A @ k) N tyNat lzero -> Rt (Δ ,, A @ k) Ot X⟨↑⟩ ki ->
  Rt (Δ ,, A @ k ,, tyFin N @ lzero) C X⟨↑⟩⟨↑⟩ ki -> Rt Δ a A k ->
  Rt Δ cs (tyDVec (lmax k ki) N[lsingle a] (iwfFam k ki X A N Ot C a)) (lmax k ki) ->
  Rt Δ (tmSupi k ki X A N Ot C a cs) (tyIWf k ki X A N Ot C Ot[lsingle a]) (lmax k ki).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros Hw Hwi HX HA HN HO HC Ha Hcs IHX IHA IHN IHO IHC IHa IHcs Hc0 ΔR kL kR TL TR c0' HΔ HkL HkR HTL HTR E W.
  rewrite EL in Hw, Hwi.
  pose proof (sc_ctx_tm HCD Hc0) as HΔL. pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1, H into Ek end.
  match goal with H : leqv ki ?x |- _ => rename x into ki1, H into Eki end.
  match goal with H : ty_leq X ?x |- _ => rename x into X', H into EX end.
  match goal with H : ty_leq A ?x |- _ => rename x into A', H into EA end.
  match goal with H : tm_leq N ?x |- _ => rename x into N', H into EN end.
  match goal with H : tm_leq Ot ?x |- _ => rename x into Ot', H into EO end.
  match goal with H : tm_leq C ?x |- _ => rename x into C', H into EC end.
  match goal with H : tm_leq a ?x |- _ => rename x into a', H into Ea end.
  match goal with H : tm_leq cs ?x |- _ => rename x into cs', H into Ecs end.
  match goal with H : lwf L' k1 |- _ => rename H into Hw1 end.
  match goal with H : lwf L' ki1 |- _ => rename H into Hwi1 end.
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  assert (Qi : lequiv L' ki ki1) by (apply lq; assumption).
  assert (QM : lequiv L' (lmax k ki) (lmax k1 ki1)) by (apply lequiv_max; assumption).
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q).
  assert (Qgi : lequiv (gL G') ki ki1) by (rewrite EL; exact Qi).
  assert (Qk : lequiv (gL G') k k) by (rewrite EL; exact (lequiv_refl _ _ Hw)).
  assert (Qki : lequiv (gL G') ki ki) by (rewrite EL; exact (lequiv_refl _ _ Hwi)).
  (* the signature and its calls, as [RT_iwf] *)
  destruct (RTcall HΔL HΔ Hwi Hwi1 Eki HX EX ltac:(assumption) IHX)
    as (HX' & HXX & HX'R & HX'R1 & _ & _ & X1 & X1r).
  destruct (RTcall HΔL HΔ Hw Hw1 Ek HA EA ltac:(assumption) IHA)
    as (HA' & HAA & HA'R & HA'R1 & CA & CA1 & X2 & X2r).
  pose proof (eqctx_wf_l (i := lD) eq_refl CA) as HΔA.
  assert (HNat : [ G' ; Δ ,, A @ k ⊢[ lD ] tyNat ≅ tyNat @ lzero ]) by (apply eqty_refl, wft_nat; [discriminate | exact HΔA]).
  destruct (Rtcall (RH := RH) (k := lzero) (k1 := lzero) (T' := tyNat) HΔA CA1 I I (leqv_refl _) HNat HN EN ltac:(assumption) IHN)
    as (HN' & HNN & _ & HN'R1 & X3 & X3r).
  pose proof (ctxconv_tm CA (i := lC) eq_refl HN') as HN'R.
  pose proof (wk1_eqty_g G' lD _ _ _ _ _ _ HΔA HXX) as HXX1.
  assert (HXX1' : [ G' ; Δ ,, A @ k ⊢[ lD ] X⟨↑⟩ ≅ X'⟨↑⟩ @ ki ]) by exact HXX1.
  destruct (Rtcall (k := ki) (k1 := ki1) (T' := X'⟨↑⟩) HΔA CA1 Hwi Hwi1 Eki HXX1' HO EO ltac:(assumption) IHO)
    as (HO' & HOO & _ & HO'R1 & X4 & X4r).
  pose proof (ctxconv_tm CA (i := lC) eq_refl (wf_conv _ _ _ _ _ _ _ HO' (eqty_sym _ _ _ _ _ _ HXX1'))) as HO'R.
  assert (HFin : [ G' ; Δ ,, A @ k ⊢[ lD ] tyFin N @ lzero ]) by (apply wft_fin; [discriminate | exact (lift_tm HN HCD)]).
  assert (EFin : [ G' ; Δ ,, A @ k ⊢[ lD ] tyFin N ≅ tyFin N' @ lzero ]) by (apply eqty_fin; [discriminate | exact HNN]).
  assert (CF : [ G' ⊢[ lD ] Δ ,, A @ k ,, tyFin N @ lzero ≅ ΔR ,, A' @ k ,, tyFin N' @ lzero ])
    by (apply ceq_ext; [exact CA | exact HFin | exact EFin | exact (lequiv_refl L' lzero I)]).
  assert (CF1 : [ G' ⊢[ lD ] Δ ,, A @ k ,, tyFin N @ lzero ≅ ΔR ,, A' @ k1 ,, tyFin N' @ lzero ])
    by (apply ceq_ext; [exact CA1 | exact HFin | exact EFin | exact (lequiv_refl L' lzero I)]).
  pose proof (eqctx_wf_l (i := lD) eq_refl CF) as HΔAF.
  pose proof (wk1_eqty_g G' lD _ _ _ _ _ _ HΔAF HXX1') as HXX2.
  assert (HXX2' : [ G' ; Δ ,, A @ k ,, tyFin N @ lzero ⊢[ lD ] X⟨↑⟩⟨↑⟩ ≅ X'⟨↑⟩⟨↑⟩ @ ki ]) by exact HXX2.
  destruct (Rtcall (k := ki) (k1 := ki1) (T' := X'⟨↑⟩⟨↑⟩) HΔAF CF1 Hwi Hwi1 Eki HXX2' HC EC ltac:(assumption) IHC)
    as (HC' & HCC & _ & HC'R1 & X5 & X5r).
  pose proof (ctxconv_tm CF (i := lC) eq_refl (wf_conv _ _ _ _ _ _ _ HC' (eqty_sym _ _ _ _ _ _ HXX2'))) as HC'R.
  (* the shape *)
  destruct (Rtcall HΔL HΔ Hw Hw1 Ek HAA Ha Ea ltac:(assumption) IHa) as (Ha' & Haa & Ha'R0 & Ha'R1 & X6 & X6r).
  assert (Ha'R : [ G' ; ΔR ⊢[ lC ] a' : A' @ k ])
    by (eapply wf_conv; [exact Ha'R0 | exact (ctxconv_eqty HΔ (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ HAA))]).
  (* the signatures' equations, at the right levels and at the left ones *)
  pose proof (lift_ty HX HCD) as HXD. pose proof (lift_ty HA HCD) as HAD. pose proof (lift_tm HN HCD) as HND.
  pose proof (lift_tm HO HCD) as HOD. pose proof (lift_tm HC HCD) as HCd.
  pose proof (lift_ty HX' HCD) as HX'D. pose proof (lift_ty HA' HCD) as HA'D. pose proof (lift_tm HN' HCD) as HN'D.
  pose proof (lift_tm HO' HCD) as HO'D. pose proof (lift_tm HC' HCD) as HC'D.
  assert (Hw0 : lwf (gL G') k) by (rewrite EL; exact Hw). assert (Hwi0 : lwf (gL G') ki) by (rewrite EL; exact Hwi).
  pose proof (IWfEq_intro (i := lD) Qg Qgi HXX HAA HNN HOO HCC Hw0 Hwi0 HXD HAD HND HOD HCd HX'D HA'D HN'D HO'D HC'D)
    as HE.
  pose proof (IWfEq_intro (i := lD) Qk Qki HXX HAA HNN HOO HCC Hw0 Hwi0 HXD HAD HND HOD HCd HX'D HA'D HN'D HO'D HC'D)
    as HE0.
  (* the children, at their tuple type *)
  pose proof (IWf_csa_eq (i := lD) eq_refl ltac:(discriminate) HE (lift_tm Ha HCD) (lift_tm Ha' HCD) Haa) as HTcs.
  pose proof (IWf_csa_eq (i := lD) eq_refl ltac:(discriminate) HE0 (lift_tm Ha HCD) (lift_tm Ha' HCD) Haa) as HTcs0.
  destruct (Rtcall (k := lmax k ki) (k1 := lmax k1 ki1) HΔL HΔ (conj Hw Hwi) (conj Hw1 Hwi1) (leqv_lmax Ek Eki)
              HTcs Hcs Ecs ltac:(assumption) IHcs) as (Hcs' & Hcscs & Hcs'R0 & Hcs'R1 & X7 & X7r).
  assert (Hcs'R : [ G' ; ΔR ⊢[ lC ] cs' : tyDVec (lmax k ki) N'[lsingle a'] (iwfFam k ki X' A' N' Ot' C' a') @ lmax k ki ])
    by (eapply wf_conv; [exact Hcs'R0 | exact (ctxconv_eqty HΔ (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ HTcs0))]).
  (* the codes *)
  assert (HWW : [ G' ; Δ ⊢[ lD ] tyIWf k ki X A N Ot C Ot[lsingle a] ≅ tyIWf k1 ki1 X' A' N' Ot' C' Ot'[lsingle a'] @ lmax k ki ])
    by exact (IWf_ty_eq (i := lD) eq_refl ltac:(discriminate) HE
                (IWf_single_eq (i := lD) eq_refl (wf_ty_nf HX) HOD HOO (lift_tm Ha HCD) (lift_tm Ha' HCD) Haa)).
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmSupi k1 ki1 X' A' N' Ot' C' a' cs' : tyIWf k1 ki1 X' A' N' Ot' C' Ot'[lsingle a']
                    @ lmax k1 ki1 ])
    by (apply wf_supi; [discriminate | rewrite EL; exact Hw1 | rewrite EL; exact Hwi1 | exact HX'R1 | exact HA'R1
                       | exact HN'R1 | exact HO'R1 | exact HC'R1 | exact Ha'R1 | exact Hcs'R1]).
  assert (HcRL : [ G' ; Δ ⊢[ lC ] tmSupi k1 ki1 X' A' N' Ot' C' a' cs' : tyIWf k ki X A N Ot C Ot[lsingle a] @ lmax k ki ])
    by (eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0)
                                          | rewrite EL; exact QM] | exact HWW]).
  refine (rec_t_br 59 (k :: ki :: nil) (k1 :: ki1 :: nil)
            (GCtx Δ :: GTy X :: GTy A :: GTm N :: GTm Ot :: GTm C :: GTm a :: GTm cs :: nil)
            (GCtx ΔR :: GTy X' :: GTy A' :: GTm N' :: GTm Ot' :: GTm C' :: GTm a' :: GTm cs' :: nil)
            (recTL ki Δ X :: recTL k Δ A :: rectL lzero (Δ ,, A @ k) tyNat N :: rectL ki (Δ ,, A @ k) X⟨↑⟩ Ot
               :: rectL ki (Δ ,, A @ k ,, tyFin N @ lzero) X⟨↑⟩⟨↑⟩ C :: rectL k Δ A a
               :: rectL (lmax k ki) Δ (tyDVec (lmax k ki) N[lsingle a] (iwfFam k ki X A N Ot C a)) cs :: nil)
            (recTR ki1 ΔR X' :: recTR k1 ΔR A' :: rectR lzero (ΔR ,, A' @ k1) tyNat N'
               :: rectR ki1 (ΔR ,, A' @ k1) X'⟨↑⟩ Ot' :: rectR ki1 (ΔR ,, A' @ k1 ,, tyFin N' @ lzero) X'⟨↑⟩⟨↑⟩ C'
               :: rectR k1 ΔR A' a'
               :: rectR (lmax k1 ki1) ΔR (tyDVec (lmax k1 ki1) N'[lsingle a'] (iwfFam k1 ki1 X' A' N' Ot' C' a')) cs'
               :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ Ek (Forall2_cons _ _ Eki (Forall2_nil _))))
            HΔL HΔ HkL HkR QM HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl HWW) Hc0 HcRL HcR0
            ltac:(cbn; repeat split; assumption)
            (GS_br EP EM 59 (k :: ki :: nil) eq_refl Hσ _)
            (GS_br EP EM 59 (k1 :: ki1 :: nil) eq_refl (GSubRel_refl_r EP EM Hσ) _)
            _ _ _ _ _ _ _).
  - gs_solve.
  - gs_solve.
  - sr_ctx_IWf; [exact X1 | exact X2 | exact X3 | exact X4 | exact X5 | exact X6 | exact X7].
  - sr_ctx_IWf; [exact X1r | exact X2r | exact X3r | exact X4r | exact X5r | exact X6r | exact X7r].
  - res_eq_IWf.
  - res_eq_IWf.
  - res_eq_IWf.
  - apply redt_supi_inst; inst_side 59.
  - apply redt_supi_inst; inst_side 59.
Qed.
End Rec.
