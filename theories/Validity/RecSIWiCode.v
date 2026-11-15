(** * The recursion lemmas on code: indexed infinitary trees, the code (M19c)

    A part of [RecS.v]'s Section [Rec], reopened over the same data and
    hypotheses ([RecH.RecHyps], RecSBase.v) so that the parts build in
    parallel. As [Rt_codeiwf] (RecSIWfCode.v), with the domain's code
    under the shape and a position. *)
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

Lemma Rt_codeiwi {Δ k kp ki x s n d o c m} : lwf (gL G') k -> lwf (gL G') kp -> lwf (gL G') ki ->
  [ G' ; Δ ⊢[ lC ] x : tyU ki @ lsuc ki ] -> [ G' ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] ->
  [ G' ; Δ ,, tyEl k s @ k ⊢[ lC ] n : tyNat @ lzero ] ->
  [ G' ; Δ ,, tyEl k s @ k ,, tyFin n @ lzero ⊢[ lC ] d : tyU kp @ lsuc kp ] ->
  [ G' ; Δ ,, tyEl k s @ k ⊢[ lC ] o : tyEl ki x⟨↑⟩ @ ki ] ->
  [ G' ; Δ ,, tyEl k s @ k ,, tyFin n @ lzero ,, tyEl kp d @ kp ⊢[ lC ] c : tyEl ki x⟨↑⟩⟨↑⟩⟨↑⟩ @ ki ] ->
  [ G' ; Δ ⊢[ lC ] m : tyEl ki x @ ki ] ->
  Rt Δ x (tyU ki) (lsuc ki) -> Rt Δ s (tyU k) (lsuc k) -> Rt (Δ ,, tyEl k s @ k) n tyNat lzero ->
  Rt (Δ ,, tyEl k s @ k ,, tyFin n @ lzero) d (tyU kp) (lsuc kp) ->
  Rt (Δ ,, tyEl k s @ k) o (tyEl ki x⟨↑⟩) ki ->
  Rt (Δ ,, tyEl k s @ k ,, tyFin n @ lzero ,, tyEl kp d @ kp) c (tyEl ki x⟨↑⟩⟨↑⟩⟨↑⟩) ki ->
  Rt Δ m (tyEl ki x) ki ->
  Rt Δ (tmIWi k kp ki x s n d o c m) (tyU (iwiL k kp ki)) (lsuc (iwiL k kp ki)).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hw Hwp Hwi Hx Hs Hn Hd Ho Hc Hm IHx IHs IHn IHd IHo IHc IHm Hc0 ΔR kL kR TL TR c0' HΔ HkL HkR HTL HTR E W.
  rewrite EL in Hw, Hwp, Hwi.
  pose proof (sc_ctx_tm HCD Hc0) as HΔL. pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1, H into Ek end.
  match goal with H : leqv kp ?x |- _ => rename x into kp1, H into Ekp end.
  match goal with H : leqv ki ?x |- _ => rename x into ki1, H into Eki end.
  match goal with H : tm_leq x ?y |- _ => rename y into x', H into Ex end.
  match goal with H : tm_leq s ?x |- _ => rename x into s', H into Es end.
  match goal with H : tm_leq n ?x |- _ => rename x into n', H into En end.
  match goal with H : tm_leq d ?x |- _ => rename x into d', H into Ed end.
  match goal with H : tm_leq o ?x |- _ => rename x into o', H into Eo end.
  match goal with H : tm_leq c ?x |- _ => rename x into c', H into Ec end.
  match goal with H : tm_leq m ?x |- _ => rename x into m', H into Em end.
  match goal with H : lwf L' k1 |- _ => rename H into Hw1 end.
  match goal with H : lwf L' kp1 |- _ => rename H into Hwp1 end.
  match goal with H : lwf L' ki1 |- _ => rename H into Hwi1 end.
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  assert (Qp : lequiv L' kp kp1) by (apply lq; assumption).
  assert (Qi : lequiv L' ki ki1) by (apply lq; assumption).
  assert (QM : lequiv L' (iwiL k kp ki) (iwiL k1 kp1 ki1))
    by (apply lequiv_max; [apply lequiv_max |]; assumption).
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
  (* the domain's code, under the shape and a position *)
  assert (HFin : [ G' ; Δ ,, tyEl k s @ k ⊢[ lD ] tyFin n @ lzero ]) by (apply wft_fin; [discriminate | exact (lift_tm Hn HCD)]).
  assert (EFin : [ G' ; Δ ,, tyEl k s @ k ⊢[ lD ] tyFin n ≅ tyFin n' @ lzero ]) by (apply eqty_fin; [discriminate | exact Hnn]).
  assert (CF : [ G' ⊢[ lD ] Δ ,, tyEl k s @ k ,, tyFin n @ lzero ≅ ΔR ,, tyEl k s' @ k ,, tyFin n' @ lzero ])
    by (apply ceq_ext; [exact CE | exact HFin | exact EFin | exact (lequiv_refl L' lzero I)]).
  assert (CF1 : [ G' ⊢[ lD ] Δ ,, tyEl k s @ k ,, tyFin n @ lzero ≅ ΔR ,, tyEl k1 s' @ k1 ,, tyFin n' @ lzero ])
    by (apply ceq_ext; [exact CE1 | exact HFin | exact EFin | exact (lequiv_refl L' lzero I)]).
  pose proof (eqctx_wf_l (i := lD) eq_refl CF) as HΔEF.
  destruct (Rtcall (k := lsuc kp) (k1 := lsuc kp1) HΔEF CF1 Hwp Hwp1 (leqv_lsuc _ _ Ekp) (HUU _ _ _ HΔEF Qp) Hd Ed
              ltac:(assumption) IHd) as (Hd' & Hdd & _ & Hd'R1 & X4 & X4r).
  pose proof (ctxconv_tm CF (i := lC) eq_refl Hd') as Hd'R.
  (* the output index *)
  pose proof (wk1_eqtm_g G' lD _ _ _ _ _ _ _ HΔE Hxx) as Hxx1.
  assert (Hxx1' : [ G' ; Δ ,, tyEl k s @ k ⊢[ lD ] x⟨↑⟩ ≅ x'⟨↑⟩ : tyU ki @ lsuc ki ]) by exact Hxx1.
  pose proof (HEE _ _ _ _ _ Qi Hxx1') as HTo. pose proof (HEE _ _ _ _ _ Qki Hxx1') as HTo0.
  destruct (Rtcall (k := ki) (k1 := ki1) HΔE CE1 Hwi Hwi1 Eki HTo Ho Eo ltac:(assumption) IHo)
    as (Ho' & Hoo & _ & Ho'R1 & X5 & X5r).
  pose proof (ctxconv_tm CE (i := lC) eq_refl (wf_conv _ _ _ _ _ _ _ Ho' (eqty_sym _ _ _ _ _ _ HTo0))) as Ho'R.
  (* the child index, under the shape, a position and a domain point *)
  assert (HElD : [ G' ; Δ ,, tyEl k s @ k ,, tyFin n @ lzero ⊢[ lD ] tyEl kp d @ kp ])
    by (apply wft_El; [discriminate | rewrite EL; exact Hwp | exact (lift_tm Hd HCD)]).
  assert (CD : [ G' ⊢[ lD ] Δ ,, tyEl k s @ k ,, tyFin n @ lzero ,, tyEl kp d @ kp
                 ≅ ΔR ,, tyEl k s' @ k ,, tyFin n' @ lzero ,, tyEl kp d' @ kp ])
    by (apply ceq_ext; [exact CF | exact HElD | exact (HEE _ _ _ _ _ (lequiv_refl _ _ Hwp) Hdd)
                       | exact (lequiv_refl _ _ Hwp)]).
  assert (CD1 : [ G' ⊢[ lD ] Δ ,, tyEl k s @ k ,, tyFin n @ lzero ,, tyEl kp d @ kp
                  ≅ ΔR ,, tyEl k1 s' @ k1 ,, tyFin n' @ lzero ,, tyEl kp1 d' @ kp1 ])
    by (apply ceq_ext; [exact CF1 | exact HElD | exact (HEE _ _ _ _ _ Qp Hdd) | exact Qp]).
  pose proof (eqctx_wf_l (i := lD) eq_refl CD) as HΔEFD.
  pose proof (wk1_eqtm_g G' lD _ _ _ _ _ _ _ HΔEF Hxx1') as Hxx2.
  assert (Hxx2' : [ G' ; Δ ,, tyEl k s @ k ,, tyFin n @ lzero ⊢[ lD ] x⟨↑⟩⟨↑⟩ ≅ x'⟨↑⟩⟨↑⟩ : tyU ki @ lsuc ki ])
    by exact Hxx2.
  pose proof (wk1_eqtm_g G' lD _ _ _ _ _ _ _ HΔEFD Hxx2') as Hxx3.
  assert (Hxx3' : [ G' ; Δ ,, tyEl k s @ k ,, tyFin n @ lzero ,, tyEl kp d @ kp
                    ⊢[ lD ] x⟨↑⟩⟨↑⟩⟨↑⟩ ≅ x'⟨↑⟩⟨↑⟩⟨↑⟩ : tyU ki @ lsuc ki ])
    by exact Hxx3.
  pose proof (HEE _ _ _ _ _ Qi Hxx3') as HTc. pose proof (HEE _ _ _ _ _ Qki Hxx3') as HTc0.
  destruct (Rtcall (k := ki) (k1 := ki1) HΔEFD CD1 Hwi Hwi1 Eki HTc Hc Ec ltac:(assumption) IHc)
    as (Hc' & Hcc & _ & Hc'R1 & X6 & X6r).
  pose proof (ctxconv_tm CD (i := lC) eq_refl (wf_conv _ _ _ _ _ _ _ Hc' (eqty_sym _ _ _ _ _ _ HTc0))) as Hc'R.
  (* the index *)
  pose proof (HEE _ _ _ _ _ Qi Hxx) as HTm. pose proof (HEE _ _ _ _ _ Qki Hxx) as HTm0.
  destruct (Rtcall (k := ki) (k1 := ki1) HΔL HΔ Hwi Hwi1 Eki HTm Hm Em ltac:(assumption) IHm)
    as (Hm' & Hmm & _ & Hm'R1 & X7 & X7r).
  pose proof (ctxconv_tm HΔ (i := lC) eq_refl (wf_conv _ _ _ _ _ _ _ Hm' (eqty_sym _ _ _ _ _ _ HTm0))) as Hm'R.
  (* the codes *)
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmIWi k1 kp1 ki1 x' s' n' d' o' c' m' : tyU (iwiL k1 kp1 ki1)
                     @ lsuc (iwiL k1 kp1 ki1) ])
    by (apply wf_code_iwi; [discriminate | rewrite EL; exact Hw1 | rewrite EL; exact Hwp1 | rewrite EL; exact Hwi1
                           | exact Hx'R1 | exact Hs'R1 | exact Hn'R1 | exact Hd'R1 | exact Ho'R1 | exact Hc'R1
                           | exact Hm'R1]).
  assert (HcRL : [ G' ; Δ ⊢[ lC ] tmIWi k1 kp1 ki1 x' s' n' d' o' c' m' : tyU (iwiL k kp ki) @ lsuc (iwiL k kp ki) ])
    by (eapply wf_conv; [eapply wf_lconv; [exact (ctxconv_tm (eqctx_sym_D HΔ) (i := lC) eq_refl HcR0)
                                          | rewrite EL; apply lequiv_suc, QM] | exact (HUU _ _ _ HΔL QM)]).
  refine (rec_t_br 62 (k :: kp :: ki :: nil) (k1 :: kp1 :: ki1 :: nil)
            (GCtx Δ :: GTm x :: GTm s :: GTm n :: GTm d :: GTm o :: GTm c :: GTm m :: nil)
            (GCtx ΔR :: GTm x' :: GTm s' :: GTm n' :: GTm d' :: GTm o' :: GTm c' :: GTm m' :: nil)
            (rectL (lsuc ki) Δ (tyU ki) x :: rectL (lsuc k) Δ (tyU k) s :: rectL lzero (Δ ,, tyEl k s @ k) tyNat n
               :: rectL (lsuc kp) (Δ ,, tyEl k s @ k ,, tyFin n @ lzero) (tyU kp) d
               :: rectL ki (Δ ,, tyEl k s @ k) (tyEl ki x⟨↑⟩) o
               :: rectL ki (Δ ,, tyEl k s @ k ,, tyFin n @ lzero ,, tyEl kp d @ kp) (tyEl ki x⟨↑⟩⟨↑⟩⟨↑⟩) c
               :: rectL ki Δ (tyEl ki x) m :: nil)
            (rectR (lsuc ki1) ΔR (tyU ki1) x' :: rectR (lsuc k1) ΔR (tyU k1) s'
               :: rectR lzero (ΔR ,, tyEl k1 s' @ k1) tyNat n'
               :: rectR (lsuc kp1) (ΔR ,, tyEl k1 s' @ k1 ,, tyFin n' @ lzero) (tyU kp1) d'
               :: rectR ki1 (ΔR ,, tyEl k1 s' @ k1) (tyEl ki1 x'⟨↑⟩) o'
               :: rectR ki1 (ΔR ,, tyEl k1 s' @ k1 ,, tyFin n' @ lzero ,, tyEl kp1 d' @ kp1) (tyEl ki1 x'⟨↑⟩⟨↑⟩⟨↑⟩) c'
               :: rectR ki1 ΔR (tyEl ki1 x') m' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ Ek (Forall2_cons _ _ Ekp (Forall2_cons _ _ Eki (Forall2_nil _)))))
            HΔL HΔ HkL HkR (lequiv_suc _ _ _ QM) HTL HTR (HUU _ _ _ HΔR QM) Hc0 HcRL HcR0
            ltac:(cbn; repeat split; assumption)
            (GS_br EP EM 62 (k :: kp :: ki :: nil) eq_refl Hσ _)
            (GS_br EP EM 62 (k1 :: kp1 :: ki1 :: nil) eq_refl (GSubRel_refl_r EP EM Hσ) _)
            _ _ _ _ _ _ _).
  - gs_solve.
  - gs_solve.
  - sr_ctx_IWf; [exact X1 | exact X2 | exact X3 | exact X4 | exact X5 | exact X6 | exact X7].
  - sr_ctx_IWf; [exact X1r | exact X2r | exact X3r | exact X4r | exact X5r | exact X6r | exact X7r].
  - res_eq.
  - res_eq.
  - res_eq.
  - apply redt_codeiwi_inst; inst_side 62.
  - apply redt_codeiwi_inst; inst_side 62.
Qed.

End Rec.
