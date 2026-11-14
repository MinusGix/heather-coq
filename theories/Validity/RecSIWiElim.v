(** * The recursion lemmas on code: indexed infinitary trees, the eliminator (M19c)

    A part of [RecS.v]'s Section [Rec], reopened over the same data and
    hypotheses ([RecH.RecHyps], RecSBase.v) so that the parts build in
    parallel. As [Rt_elimIWf] (RecSIWfElim.v), with the domain. *)
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

Lemma Rt_elimIWi {Δ k kp ki k' X A N D Ot C M c m t} :
  lwf (gL G') k -> lwf (gL G') kp -> lwf (gL G') ki -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] X @ ki ] -> [ G' ; Δ ⊢[ lC ] A @ k ] ->
  [ G' ; Δ ,, A @ k ⊢[ lC ] N : tyNat @ lzero ] -> [ G' ; Δ ,, A @ k ,, tyFin N @ lzero ⊢[ lC ] D @ kp ] ->
  [ G' ; Δ ,, A @ k ⊢[ lC ] Ot : X⟨↑⟩ @ ki ] ->
  [ G' ; Δ ,, A @ k ,, tyFin N @ lzero ,, D @ kp ⊢[ lC ] C : X⟨↑⟩⟨↑⟩⟨↑⟩ @ ki ] ->
  [ G' ; Δ ,, X @ ki ,, iwimotty k kp ki X A N D Ot C @ iwiL k kp ki ⊢[ lC ] M @ k' ] ->
  [ G' ; Δ ,, A @ k ,, iwicsty k kp ki X A N D Ot C @ iwiL k kp ki ⊢[ lC ]
      iwiihty k kp ki k' X A N D Ot C M @ lmax lzero (lmax kp k') ] ->
  [ G' ; Δ ,, A @ k ,, iwicsty k kp ki X A N D Ot C @ iwiL k kp ki
      ,, iwiihty k kp ki k' X A N D Ot C M @ lmax lzero (lmax kp k')
      ⊢[ lC ] c : iwistepty k kp ki X A N D Ot C M @ k' ] ->
  [ G' ; Δ ⊢[ lC ] m : X @ ki ] -> [ G' ; Δ ⊢[ lC ] t : tyIWi k kp ki X A N D Ot C m @ iwiL k kp ki ] ->
  RT Δ X ki -> RT Δ A k -> Rt (Δ ,, A @ k) N tyNat lzero -> RT (Δ ,, A @ k ,, tyFin N @ lzero) D kp ->
  Rt (Δ ,, A @ k) Ot X⟨↑⟩ ki -> Rt (Δ ,, A @ k ,, tyFin N @ lzero ,, D @ kp) C X⟨↑⟩⟨↑⟩⟨↑⟩ ki ->
  RT (Δ ,, X @ ki ,, iwimotty k kp ki X A N D Ot C @ iwiL k kp ki) M k' ->
  Rt (Δ ,, A @ k ,, iwicsty k kp ki X A N D Ot C @ iwiL k kp ki
        ,, iwiihty k kp ki k' X A N D Ot C M @ lmax lzero (lmax kp k')) c
     (iwistepty k kp ki X A N D Ot C M) k' ->
  Rt Δ m X ki -> Rt Δ t (tyIWi k kp ki X A N D Ot C m) (iwiL k kp ki) ->
  Rt Δ (tmElimIWi k kp ki k' X A N D Ot C M c m t) (M[lsingle2 m t]) k'.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros Hw Hwp Hwi Hw' HX HA HN HD HO HC HM HI Hc Hm Ht IHX IHA IHN IHD IHO IHC IHM IHc IHm IHt
    Hc0 ΔR kL kR TL TR c0' HΔ HkL HkR HTL HTR E W.
  rewrite EL in Hw, Hwp, Hwi, Hw'.
  pose proof (sc_ctx_tm HCD Hc0) as HΔL. pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1, H into Ek end.
  match goal with H : leqv kp ?x |- _ => rename x into kp1, H into Ekp end.
  match goal with H : leqv ki ?x |- _ => rename x into ki1, H into Eki end.
  match goal with H : leqv k' ?x |- _ => rename x into k1', H into Ek' end.
  match goal with H : ty_leq X ?x |- _ => rename x into X', H into EX end.
  match goal with H : ty_leq A ?x |- _ => rename x into A', H into EA end.
  match goal with H : tm_leq N ?x |- _ => rename x into N', H into EN end.
  match goal with H : ty_leq D ?x |- _ => rename x into D', H into ED end.
  match goal with H : tm_leq Ot ?x |- _ => rename x into Ot', H into EO end.
  match goal with H : tm_leq C ?x |- _ => rename x into C', H into EC end.
  match goal with H : ty_leq M ?x |- _ => rename x into M', H into EM1 end.
  match goal with H : tm_leq c ?x |- _ => rename x into c', H into Ec end.
  match goal with H : tm_leq m ?x |- _ => rename x into m', H into Em end.
  match goal with H : tm_leq t ?x |- _ => rename x into t', H into Et end.
  match goal with H : lwf L' k1 |- _ => rename H into Hw1 end.
  match goal with H : lwf L' kp1 |- _ => rename H into Hwp1 end.
  match goal with H : lwf L' ki1 |- _ => rename H into Hwi1 end.
  match goal with H : lwf L' k1' |- _ => rename H into Hw1' end.
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  assert (Qp : lequiv L' kp kp1) by (apply lq; assumption).
  assert (Qi : lequiv L' ki ki1) by (apply lq; assumption).
  assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  assert (QM : lequiv L' (iwiL k kp ki) (iwiL k1 kp1 ki1))
    by (apply lequiv_max; [apply lequiv_max |]; assumption).
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q).
  assert (Qgp : lequiv (gL G') kp kp1) by (rewrite EL; exact Qp).
  assert (Qgi : lequiv (gL G') ki ki1) by (rewrite EL; exact Qi).
  assert (Qg' : lequiv (gL G') k' k1') by (rewrite EL; exact Q').
  assert (Qk : lequiv (gL G') k k) by (rewrite EL; exact (lequiv_refl _ _ Hw)).
  assert (Qkp : lequiv (gL G') kp kp) by (rewrite EL; exact (lequiv_refl _ _ Hwp)).
  assert (Qki : lequiv (gL G') ki ki) by (rewrite EL; exact (lequiv_refl _ _ Hwi)).
  (* the signature and its calls, as [RT_iwi] *)
  destruct (RTcall HΔL HΔ Hwi Hwi1 Eki HX EX ltac:(assumption) IHX)
    as (HX' & HXX & HX'R & HX'R1 & CX & CX1 & X1 & X1r).
  destruct (RTcall HΔL HΔ Hw Hw1 Ek HA EA ltac:(assumption) IHA)
    as (HA' & HAA & HA'R & HA'R1 & CA & CA1 & X2 & X2r).
  pose proof (eqctx_wf_l (i := lD) eq_refl CA) as HΔA.
  assert (HNat : [ G' ; Δ ,, A @ k ⊢[ lD ] tyNat ≅ tyNat @ lzero ]) by (apply eqty_refl, wft_nat; [discriminate | exact HΔA]).
  destruct (Rtcall (RH := RH) (k := lzero) (k1 := lzero) (T' := tyNat) HΔA CA1 I I (leqv_refl _) HNat HN EN ltac:(assumption) IHN)
    as (HN' & HNN & _ & HN'R1 & X3 & X3r).
  pose proof (ctxconv_tm CA (i := lC) eq_refl HN') as HN'R.
  assert (HFin : [ G' ; Δ ,, A @ k ⊢[ lD ] tyFin N @ lzero ]) by (apply wft_fin; [discriminate | exact (lift_tm HN HCD)]).
  assert (EFin : [ G' ; Δ ,, A @ k ⊢[ lD ] tyFin N ≅ tyFin N' @ lzero ]) by (apply eqty_fin; [discriminate | exact HNN]).
  assert (CF : [ G' ⊢[ lD ] Δ ,, A @ k ,, tyFin N @ lzero ≅ ΔR ,, A' @ k ,, tyFin N' @ lzero ])
    by (apply ceq_ext; [exact CA | exact HFin | exact EFin | exact (lequiv_refl L' lzero I)]).
  assert (CF1 : [ G' ⊢[ lD ] Δ ,, A @ k ,, tyFin N @ lzero ≅ ΔR ,, A' @ k1 ,, tyFin N' @ lzero ])
    by (apply ceq_ext; [exact CA1 | exact HFin | exact EFin | exact (lequiv_refl L' lzero I)]).
  pose proof (eqctx_wf_l (i := lD) eq_refl CF) as HΔAF.
  destruct (RTcall HΔAF CF1 Hwp Hwp1 Ekp HD ED ltac:(assumption) IHD)
    as (HD' & HDD & _ & HD'R1 & _ & CD1 & X4 & X4r).
  pose proof (ctxconv_ty CF (i := lC) eq_refl HD') as HD'R.
  pose proof (wk1_eqty_g G' lD _ _ _ _ _ _ HΔA HXX) as HXX1.
  assert (HXX1' : [ G' ; Δ ,, A @ k ⊢[ lD ] X⟨↑⟩ ≅ X'⟨↑⟩ @ ki ]) by exact HXX1.
  destruct (Rtcall (k := ki) (k1 := ki1) (T' := X'⟨↑⟩) HΔA CA1 Hwi Hwi1 Eki HXX1' HO EO ltac:(assumption) IHO)
    as (HO' & HOO & _ & HO'R1 & X5 & X5r).
  pose proof (ctxconv_tm CA (i := lC) eq_refl (wf_conv _ _ _ _ _ _ _ HO' (eqty_sym _ _ _ _ _ _ HXX1'))) as HO'R.
  assert (CD : [ G' ⊢[ lD ] Δ ,, A @ k ,, tyFin N @ lzero ,, D @ kp ≅ ΔR ,, A' @ k ,, tyFin N' @ lzero ,, D' @ kp ])
    by (apply ceq_ext; [exact CF | exact (lift_ty HD HCD) | exact HDD | exact (lequiv_refl L' kp Hwp)]).
  pose proof (eqctx_wf_l (i := lD) eq_refl CD) as HΔAFD.
  pose proof (wk1_eqty_g G' lD _ _ _ _ _ _ HΔAF HXX1') as HXX2.
  assert (HXX2' : [ G' ; Δ ,, A @ k ,, tyFin N @ lzero ⊢[ lD ] X⟨↑⟩⟨↑⟩ ≅ X'⟨↑⟩⟨↑⟩ @ ki ]) by exact HXX2.
  pose proof (wk1_eqty_g G' lD _ _ _ _ _ _ HΔAFD HXX2') as HXX3.
  assert (HXX3' : [ G' ; Δ ,, A @ k ,, tyFin N @ lzero ,, D @ kp ⊢[ lD ] X⟨↑⟩⟨↑⟩⟨↑⟩ ≅ X'⟨↑⟩⟨↑⟩⟨↑⟩ @ ki ])
    by exact HXX3.
  destruct (Rtcall (k := ki) (k1 := ki1) (T' := X'⟨↑⟩⟨↑⟩⟨↑⟩) HΔAFD CD1 Hwi Hwi1 Eki HXX3' HC EC ltac:(assumption) IHC)
    as (HC' & HCC & _ & HC'R1 & X6 & X6r).
  pose proof (ctxconv_tm CD (i := lC) eq_refl (wf_conv _ _ _ _ _ _ _ HC' (eqty_sym _ _ _ _ _ _ HXX3'))) as HC'R.
  (* the signatures' equations, at the right levels and at the left ones *)
  pose proof (lift_ty HX HCD) as HXD. pose proof (lift_ty HA HCD) as HAD. pose proof (lift_tm HN HCD) as HND.
  pose proof (lift_ty HD HCD) as HDd. pose proof (lift_tm HO HCD) as HOD. pose proof (lift_tm HC HCD) as HCd.
  pose proof (lift_ty HX' HCD) as HX'D. pose proof (lift_ty HA' HCD) as HA'D. pose proof (lift_tm HN' HCD) as HN'D.
  pose proof (lift_ty HD' HCD) as HD'D. pose proof (lift_tm HO' HCD) as HO'D. pose proof (lift_tm HC' HCD) as HC'D.
  assert (Hw0 : lwf (gL G') k) by (rewrite EL; exact Hw). assert (Hwp0 : lwf (gL G') kp) by (rewrite EL; exact Hwp).
  assert (Hwi0 : lwf (gL G') ki) by (rewrite EL; exact Hwi).
  pose proof (IWiEq_intro (i := lD) Qg Qgp Qgi HXX HAA HNN HDD HOO HCC Hw0 Hwp0 Hwi0 HXD HAD HND HDd HOD HCd
                HX'D HA'D HN'D HD'D HO'D HC'D) as HE.
  pose proof (IWiEq_intro (i := lD) Qk Qkp Qki HXX HAA HNN HDD HOO HCC Hw0 Hwp0 Hwi0 HXD HAD HND HDd HOD HCd
                HX'D HA'D HN'D HD'D HO'D HC'D) as HE0.
  assert (HS : @IWiSig G' lD Δ k kp ki X A N D Ot C)
    by (unfold IWiSig; repeat split; assumption).
  (* the motive, over the index and the tree *)
  pose proof (IWi_mot_wf (i := lD) eq_refl ltac:(discriminate) HS) as HMo.
  pose proof (ceq_ext CX1 HMo (IWi_mot_eq (i := lD) eq_refl ltac:(discriminate) HE) QM) as CM1.
  pose proof (ceq_ext CX HMo (IWi_mot_eq (i := lD) eq_refl ltac:(discriminate) HE0)
                (lequiv_refl L' (iwiL k kp ki) (conj (conj Hw Hwi) Hwp))) as CM0.
  destruct (RTcall (eqctx_wf_l (i := lD) eq_refl CM1) CM1 Hw' Hw1' Ek' HM EM1 ltac:(assumption) IHM)
    as (HM' & HMM & _ & HM'R1 & _ & _ & X7 & X7r).
  pose proof (ctxconv_ty CM0 (i := lC) eq_refl HM') as HM'R.
  pose proof (lift_ty HM HCD) as HMD.
  (* the step's telescope, at the right levels and at the left ones *)
  pose proof (IWi_cs_wf (i := lD) eq_refl ltac:(discriminate) HS) as HCs.
  pose proof (ceq_ext CA1 HCs (IWi_cs_eq (i := lD) eq_refl ltac:(discriminate) HE) QM) as CC1.
  pose proof (ceq_ext CA HCs (IWi_cs_eq (i := lD) eq_refl ltac:(discriminate) HE0)
                (lequiv_refl L' (iwiL k kp ki) (conj (conj Hw Hwi) Hwp))) as CC0.
  destruct (scr_ty HI (iwiihty_leq _ _ _ _ _ _ _ _ _ _ _ k1 kp1 ki1 k1' X' A' N' D' Ot' C' M'
                         Ek Ekp Eki Ek' EX EA EN ED EO EC EM1)
              ltac:(apply iwiihty_lwf; assumption)) as (HI' & EI1).
  destruct (scr_ty HI (iwiihty_leq _ _ _ _ _ _ _ _ _ _ _ k kp ki k' X' A' N' D' Ot' C' M'
                         (leqv_refl _) (leqv_refl _) (leqv_refl _) (leqv_refl _) EX EA EN ED EO EC EM1)
              ltac:(apply iwiihty_lwf; first [assumption | rewrite <- EL; assumption])) as (HI0 & EI0).
  pose proof (ceq_ext CC1 (lift_ty HI HCD) EI1
                (lequiv_max _ _ _ _ _ (lequiv_refl L' lzero I) (lequiv_max _ _ _ _ _ Qp Q'))) as CS1.
  pose proof (ceq_ext CC0 (lift_ty HI HCD) EI0 (lequiv_refl L' (lmax lzero (lmax kp k')) (conj I (conj Hwp Hw')))) as CS0.
  pose proof (eqctx_wf_l (i := lD) eq_refl CS1) as HΘ.
  pose proof (IWi_step_eq (i := lD) eq_refl ltac:(discriminate) HE HMD HMM HΘ) as ES1.
  pose proof (IWi_step_eq (i := lD) eq_refl ltac:(discriminate) HE0 HMD HMM HΘ) as ES0.
  (* the step, the index and the scrutinee, and their calls *)
  destruct (Rtcall HΘ CS1 Hw' Hw1' Ek' ES1 Hc Ec ltac:(assumption) IHc)
    as (Hc' & Hcc & _ & Hc'R1 & X8 & X8r).
  pose proof (ctxconv_tm CS0 (i := lC) eq_refl (wf_conv _ _ _ _ _ _ _ Hc' (eqty_sym _ _ _ _ _ _ ES0))) as Hc'R.
  pose proof (Rtcall HΔL HΔ Hwi Hwi1 Eki HXX Hm Em ltac:(assumption) IHm) as (Hm' & Hmm & _ & Hm'R1 & X9 & X9r).
  pose proof (ctxconv_tm HΔ (i := lC) eq_refl (wf_conv _ _ _ _ _ _ _ Hm' (eqty_sym _ _ _ _ _ _ HXX))) as Hm'R.
  pose proof (IWi_ty_eq (i := lD) eq_refl ltac:(discriminate) HE Hmm) as HWW.
  destruct (Rtcall (k := iwiL k kp ki) (k1 := iwiL k1 kp1 ki1) HΔL HΔ (conj (conj Hw Hwi) Hwp)
              (conj (conj Hw1 Hwi1) Hwp1) (leqv_lmax (leqv_lmax Ek Eki) Ekp)
              HWW Ht Et ltac:(assumption) IHt) as (Ht' & Htt & Ht'R0 & Ht'R1 & X10 & X10r).
  pose proof (IWi_ty_eq (i := lD) eq_refl ltac:(discriminate) HE0 Hmm) as HWW0.
  assert (Ht'R : [ G' ; ΔR ⊢[ lC ] t' : tyIWi k kp ki X' A' N' D' Ot' C' m' @ iwiL k kp ki ])
    by (eapply wf_conv; [exact Ht'R0 | exact (ctxconv_eqty HΔ (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ HWW0))]).
  (* the codes *)
  assert (Hr1 : [ G' ; Δ ⊢[ lD ] M[lsingle2 m t] ≅ M'[lsingle2 m' t'] @ k' ])
    by exact (IWi_mot_inst_eq (i := lD) eq_refl ltac:(discriminate) HS HMD HMM
                (lift_tm Hm HCD) (lift_tm Hm' HCD) Hmm (lift_tm Ht HCD) (lift_tm Ht' HCD) Htt).
  pose proof (sc_elimIWi_q (G := G') (i := lC) HCD ltac:(discriminate)
                Qg Qgp Qgi Qg' HX HX' (static_code_ty HCD HX HX' EX) HA HA' (static_code_ty HCD HA HA' EA)
                HN HN' (static_code_tm HCD HN HN' EN) HD HD' (static_code_ty HCD HD HD' ED)
                HO HO' (static_code_tm HCD HO HO' EO)
                HC HC' (static_code_tm HCD HC HC' EC) HM HM' (static_code_ty HCD HM HM' EM1)
                HI HI' (static_code_ty HCD HI HI' (iwiihty_leq _ _ _ _ _ _ _ _ _ _ _ k1 kp1 ki1 k1' X' A' N' D' Ot' C' M'
                                                   Ek Ekp Eki Ek' EX EA EN ED EO EC EM1))
                Hc' Hm Hm' (static_code_tm HCD Hm Hm' Em) Ht Ht' (static_code_tm HCD Ht Ht' Et)) as HcRL.
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmElimIWi k1 kp1 ki1 k1' X' A' N' D' Ot' C' M' c' m' t' : M'[lsingle2 m' t'] @ k1' ]).
  { refine (ctxconv_tm HΔ (i := lC) eq_refl _).
    eapply wf_lconv; [eapply wf_conv; [exact HcRL | apply eqty_sym, Hr1] | apply lequiv_sym, Qg']. }
  refine (rec_t_br 64 (k :: kp :: ki :: k' :: nil) (k1 :: kp1 :: ki1 :: k1' :: nil)
            (GCtx Δ :: GTy X :: GTy A :: GTm N :: GTy D :: GTm Ot :: GTm C :: GTy M :: GTm c :: GTm m :: GTm t :: nil)
            (GCtx ΔR :: GTy X' :: GTy A' :: GTm N' :: GTy D' :: GTm Ot' :: GTm C' :: GTy M' :: GTm c' :: GTm m'
               :: GTm t' :: nil)
            (recTL ki Δ X :: recTL k Δ A :: rectL lzero (Δ ,, A @ k) tyNat N
               :: recTL kp (Δ ,, A @ k ,, tyFin N @ lzero) D :: rectL ki (Δ ,, A @ k) X⟨↑⟩ Ot
               :: rectL ki (Δ ,, A @ k ,, tyFin N @ lzero ,, D @ kp) X⟨↑⟩⟨↑⟩⟨↑⟩ C
               :: recTL k' (Δ ,, X @ ki ,, iwimotty k kp ki X A N D Ot C @ iwiL k kp ki) M
               :: rectL k' (Δ ,, A @ k ,, iwicsty k kp ki X A N D Ot C @ iwiL k kp ki
                              ,, iwiihty k kp ki k' X A N D Ot C M @ lmax lzero (lmax kp k'))
                    (iwistepty k kp ki X A N D Ot C M) c
               :: rectL ki Δ X m :: rectL (iwiL k kp ki) Δ (tyIWi k kp ki X A N D Ot C m) t :: nil)
            (recTR ki1 ΔR X' :: recTR k1 ΔR A' :: rectR lzero (ΔR ,, A' @ k1) tyNat N'
               :: recTR kp1 (ΔR ,, A' @ k1 ,, tyFin N' @ lzero) D' :: rectR ki1 (ΔR ,, A' @ k1) X'⟨↑⟩ Ot'
               :: rectR ki1 (ΔR ,, A' @ k1 ,, tyFin N' @ lzero ,, D' @ kp1) X'⟨↑⟩⟨↑⟩⟨↑⟩ C'
               :: recTR k1' (ΔR ,, X' @ ki1 ,, iwimotty k1 kp1 ki1 X' A' N' D' Ot' C' @ iwiL k1 kp1 ki1) M'
               :: rectR k1' (ΔR ,, A' @ k1 ,, iwicsty k1 kp1 ki1 X' A' N' D' Ot' C' @ iwiL k1 kp1 ki1
                               ,, iwiihty k1 kp1 ki1 k1' X' A' N' D' Ot' C' M' @ lmax lzero (lmax kp1 k1'))
                    (iwistepty k1 kp1 ki1 X' A' N' D' Ot' C' M') c'
               :: rectR ki1 ΔR X' m' :: rectR (iwiL k1 kp1 ki1) ΔR (tyIWi k1 kp1 ki1 X' A' N' D' Ot' C' m') t' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ Ek (Forall2_cons _ _ Ekp (Forall2_cons _ _ Eki
                          (Forall2_cons _ _ Ek' (Forall2_nil _))))))
            HΔL HΔ HkL HkR Q' HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl Hr1) Hc0 HcRL HcR0
            ltac:(cbn; repeat split; assumption)
            (GS_br EP EM 64 (k :: kp :: ki :: k' :: nil) eq_refl Hσ _)
            (GS_br EP EM 64 (k1 :: kp1 :: ki1 :: k1' :: nil) eq_refl (GSubRel_refl_r EP EM Hσ) _) _ _ _ _ _ _ _).
  (* the side goals by shape, each in a worker, as [Rt_elimIWf]'s *)
  par: lazymatch goal with
    | |- context [GSall] => gs_solve
    | |- redt _ _ _ _ _ _ _ = _ => apply redt_elimIWi_inst; inst_side 64
    | |- context [brΓ _ _ (wrapMT MT') _ _ _] =>
        sr_ctx_IWf; [exact X1r | exact X2r | exact X3r | exact X4r | exact X5r | exact X6r | exact X7r | exact X8r
                    | exact X9r | exact X10r]
    | |- context [brΓ _ _ (wrapMT MT) _ _ _] =>
        sr_ctx_IWf; [exact X1 | exact X2 | exact X3 | exact X4 | exact X5 | exact X6 | exact X7 | exact X8 | exact X9
                    | exact X10]
    | |- _ => first [J_res | res_eq_IWf]
    end.
Qed.

End Rec.
