(** * The recursion lemmas on code: the indexed trees' constructor (M17c)

    A part of [RecS.v]'s Section [Rec], reopened over the same data and
    hypotheses ([RecH.RecHyps], RecSBase.v) beside [RecSIWf], so that the
    parts build in parallel. *)
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
