(** * The recursion lemmas on code: the indexed trees' eliminator (M17c)

    A part of [RecS.v]'s Section [Rec], reopened over the same data and
    hypotheses ([RecH.RecHyps], RecSBase.v) beside [RecSIWf]: alone, it
    takes half of that file's time. *)
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

Lemma Rt_elimIWf {Δ k ki k' X A N Ot C M c m t} : lwf (gL G') k -> lwf (gL G') ki -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] X @ ki ] -> [ G' ; Δ ⊢[ lC ] A @ k ] ->
  [ G' ; Δ ,, A @ k ⊢[ lC ] N : tyNat @ lzero ] -> [ G' ; Δ ,, A @ k ⊢[ lC ] Ot : X⟨↑⟩ @ ki ] ->
  [ G' ; Δ ,, A @ k ,, tyFin N @ lzero ⊢[ lC ] C : X⟨↑⟩⟨↑⟩ @ ki ] ->
  [ G' ; Δ ,, X @ ki ,, iwfmotty k ki X A N Ot C @ lmax k ki ⊢[ lC ] M @ k' ] ->
  [ G' ; Δ ,, A @ k ,, iwfcsty k ki X A N Ot C @ lmax k ki ⊢[ lC ] iwfihty k ki k' X A N Ot C M @ lmax lzero k' ] ->
  [ G' ; Δ ,, A @ k ,, iwfcsty k ki X A N Ot C @ lmax k ki ,, iwfihty k ki k' X A N Ot C M @ lmax lzero k'
      ⊢[ lC ] c : iwfstepty k ki X A N Ot C M @ k' ] ->
  [ G' ; Δ ⊢[ lC ] m : X @ ki ] -> [ G' ; Δ ⊢[ lC ] t : tyIWf k ki X A N Ot C m @ lmax k ki ] ->
  RT Δ X ki -> RT Δ A k -> Rt (Δ ,, A @ k) N tyNat lzero -> Rt (Δ ,, A @ k) Ot X⟨↑⟩ ki ->
  Rt (Δ ,, A @ k ,, tyFin N @ lzero) C X⟨↑⟩⟨↑⟩ ki ->
  RT (Δ ,, X @ ki ,, iwfmotty k ki X A N Ot C @ lmax k ki) M k' ->
  Rt (Δ ,, A @ k ,, iwfcsty k ki X A N Ot C @ lmax k ki ,, iwfihty k ki k' X A N Ot C M @ lmax lzero k') c
     (iwfstepty k ki X A N Ot C M) k' ->
  Rt Δ m X ki -> Rt Δ t (tyIWf k ki X A N Ot C m) (lmax k ki) ->
  Rt Δ (tmElimIWf k ki k' X A N Ot C M c m t) (M[lsingle2 m t]) k'.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros Hw Hwi Hw' HX HA HN HO HC HM HI Hc Hm Ht IHX IHA IHN IHO IHC IHM IHc IHm IHt
    Hc0 ΔR kL kR TL TR c0' HΔ HkL HkR HTL HTR E W.
  rewrite EL in Hw, Hwi, Hw'.
  pose proof (sc_ctx_tm HCD Hc0) as HΔL. pose proof (eqctx_wf_r (i := lD) eq_refl HΔ) as HΔR. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1, H into Ek end.
  match goal with H : leqv ki ?x |- _ => rename x into ki1, H into Eki end.
  match goal with H : leqv k' ?x |- _ => rename x into k1', H into Ek' end.
  match goal with H : ty_leq X ?x |- _ => rename x into X', H into EX end.
  match goal with H : ty_leq A ?x |- _ => rename x into A', H into EA end.
  match goal with H : tm_leq N ?x |- _ => rename x into N', H into EN end.
  match goal with H : tm_leq Ot ?x |- _ => rename x into Ot', H into EO end.
  match goal with H : tm_leq C ?x |- _ => rename x into C', H into EC end.
  match goal with H : ty_leq M ?x |- _ => rename x into M', H into EM1 end.
  match goal with H : tm_leq c ?x |- _ => rename x into c', H into Ec end.
  match goal with H : tm_leq m ?x |- _ => rename x into m', H into Em end.
  match goal with H : tm_leq t ?x |- _ => rename x into t', H into Et end.
  match goal with H : lwf L' k1 |- _ => rename H into Hw1 end.
  match goal with H : lwf L' ki1 |- _ => rename H into Hwi1 end.
  match goal with H : lwf L' k1' |- _ => rename H into Hw1' end.
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  assert (Qi : lequiv L' ki ki1) by (apply lq; assumption).
  assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  assert (QM : lequiv L' (lmax k ki) (lmax k1 ki1)) by (apply lequiv_max; assumption).
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q).
  assert (Qgi : lequiv (gL G') ki ki1) by (rewrite EL; exact Qi).
  assert (Qg' : lequiv (gL G') k' k1') by (rewrite EL; exact Q').
  assert (Qk : lequiv (gL G') k k) by (rewrite EL; exact (lequiv_refl _ _ Hw)).
  assert (Qki : lequiv (gL G') ki ki) by (rewrite EL; exact (lequiv_refl _ _ Hwi)).
  assert (Qk' : lequiv (gL G') k' k') by (rewrite EL; exact (lequiv_refl _ _ Hw')).
  (* the signature and its calls, as [RT_iwf] *)
  destruct (RTcall HΔL HΔ Hwi Hwi1 Eki HX EX ltac:(assumption) IHX)
    as (HX' & HXX & HX'R & HX'R1 & CX & CX1 & X1 & X1r).
  destruct (RTcall HΔL HΔ Hw Hw1 Ek HA EA ltac:(assumption) IHA)
    as (HA' & HAA & HA'R & HA'R1 & CA & CA1 & X2 & X2r).
  pose proof (eqctx_wf_l (i := lD) eq_refl CA) as HΔA.
  assert (HNat : [ G' ; Δ ,, A @ k ⊢[ lD ] tyNat ≅ tyNat @ lzero ]) by (apply eqty_refl, wft_nat; [discriminate | exact HΔA]).
  destruct (Rtcall (RH := RH) (k := lzero) (k1 := lzero) (T' := tyNat) HΔA CA1 I I (leqv_refl _) HNat HN EN ltac:(assumption) IHN)
    as (HN' & HNN & _ & HN'R1 & X3 & X3r).
  pose proof (wk1_eqty_g G' lD _ _ _ _ _ _ HΔA HXX) as HXX1.
  assert (HXX1' : [ G' ; Δ ,, A @ k ⊢[ lD ] X⟨↑⟩ ≅ X'⟨↑⟩ @ ki ]) by exact HXX1.
  destruct (Rtcall (k := ki) (k1 := ki1) (T' := X'⟨↑⟩) HΔA CA1 Hwi Hwi1 Eki HXX1' HO EO ltac:(assumption) IHO)
    as (HO' & HOO & _ & HO'R1 & X4 & X4r).
  pose proof (ctxconv_tm CA (i := lC) eq_refl HN') as HN'R.
  pose proof (ctxconv_tm CA (i := lC) eq_refl (wf_conv _ _ _ _ _ _ _ HO' (eqty_sym _ _ _ _ _ _ HXX1'))) as HO'R.
  assert (HFin : [ G' ; Δ ,, A @ k ⊢[ lD ] tyFin N @ lzero ]) by (apply wft_fin; [discriminate | exact (lift_tm HN HCD)]).
  assert (EFin : [ G' ; Δ ,, A @ k ⊢[ lD ] tyFin N ≅ tyFin N' @ lzero ]) by (apply eqty_fin; [discriminate | exact HNN]).
  assert (CF1 : [ G' ⊢[ lD ] Δ ,, A @ k ,, tyFin N @ lzero ≅ ΔR ,, A' @ k1 ,, tyFin N' @ lzero ])
    by (apply ceq_ext; [exact CA1 | exact HFin | exact EFin | exact (lequiv_refl L' lzero I)]).
  assert (CF : [ G' ⊢[ lD ] Δ ,, A @ k ,, tyFin N @ lzero ≅ ΔR ,, A' @ k ,, tyFin N' @ lzero ])
    by (apply ceq_ext; [exact CA | exact HFin | exact EFin | exact (lequiv_refl L' lzero I)]).
  pose proof (eqctx_wf_l (i := lD) eq_refl CF1) as HΔAF.
  pose proof (wk1_eqty_g G' lD _ _ _ _ _ _ HΔAF HXX1') as HXX2.
  assert (HXX2' : [ G' ; Δ ,, A @ k ,, tyFin N @ lzero ⊢[ lD ] X⟨↑⟩⟨↑⟩ ≅ X'⟨↑⟩⟨↑⟩ @ ki ]) by exact HXX2.
  destruct (Rtcall (k := ki) (k1 := ki1) (T' := X'⟨↑⟩⟨↑⟩) HΔAF CF1 Hwi Hwi1 Eki HXX2' HC EC ltac:(assumption) IHC)
    as (HC' & HCC & _ & HC'R1 & X5 & X5r).
  pose proof (ctxconv_tm CF (i := lC) eq_refl (wf_conv _ _ _ _ _ _ _ HC' (eqty_sym _ _ _ _ _ _ HXX2'))) as HC'R.
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
  assert (HS : @IWfSig G' lD Δ k ki X A N Ot C)
    by (unfold IWfSig; repeat split; assumption).
  (* the motive, over the index and the tree *)
  pose proof (IWf_mot_wf (i := lD) eq_refl ltac:(discriminate) HS) as HMo.
  pose proof (ceq_ext CX1 HMo (IWf_mot_eq (i := lD) eq_refl ltac:(discriminate) HE) QM) as CM1.
  pose proof (ceq_ext CX HMo (IWf_mot_eq (i := lD) eq_refl ltac:(discriminate) HE0)
                (lequiv_refl L' (lmax k ki) (conj Hw Hwi))) as CM0.
  destruct (RTcall (eqctx_wf_l (i := lD) eq_refl CM1) CM1 Hw' Hw1' Ek' HM EM1 ltac:(assumption) IHM)
    as (HM' & HMM & _ & HM'R1 & _ & _ & X6 & X6r).
  pose proof (ctxconv_ty CM0 (i := lC) eq_refl HM') as HM'R.
  pose proof (lift_ty HM HCD) as HMD.
  (* the step's telescope, at the right levels and at the left ones *)
  pose proof (IWf_cs_wf (i := lD) eq_refl ltac:(discriminate) HS) as HCs.
  pose proof (ceq_ext CA1 HCs (IWf_cs_eq (i := lD) eq_refl ltac:(discriminate) HE) QM) as CC1.
  pose proof (ceq_ext CA HCs (IWf_cs_eq (i := lD) eq_refl ltac:(discriminate) HE0)
                (lequiv_refl L' (lmax k ki) (conj Hw Hwi))) as CC0.
  destruct (scr_ty HI (iwfihty_leq _ _ _ _ _ _ _ _ _ k1 ki1 k1' X' A' N' Ot' C' M' Ek Eki Ek' EX EA EN EO EC EM1)
              ltac:(apply iwfihty_lwf; assumption)) as (HI' & EI1).
  destruct (scr_ty HI (iwfihty_leq _ _ _ _ _ _ _ _ _ k ki k' X' A' N' Ot' C' M'
                         (leqv_refl _) (leqv_refl _) (leqv_refl _) EX EA EN EO EC EM1)
              ltac:(apply iwfihty_lwf; first [assumption | rewrite <- EL; assumption])) as (HI0 & EI0).
  pose proof (ceq_ext CC1 (lift_ty HI HCD) EI1 (lequiv_max _ _ _ _ _ (lequiv_refl L' lzero I) Q')) as CS1.
  pose proof (ceq_ext CC0 (lift_ty HI HCD) EI0 (lequiv_refl L' (lmax lzero k') (conj I Hw'))) as CS0.
  pose proof (eqctx_wf_l (i := lD) eq_refl CS1) as HΘ.
  pose proof (IWf_step_eq (i := lD) eq_refl ltac:(discriminate) HE HMD HMM HΘ) as ES1.
  pose proof (IWf_step_eq (i := lD) eq_refl ltac:(discriminate) HE0 HMD HMM HΘ) as ES0.
  (* the step, the index and the scrutinee, and their calls *)
  destruct (Rtcall HΘ CS1 Hw' Hw1' Ek' ES1 Hc Ec ltac:(assumption) IHc)
    as (Hc' & Hcc & _ & Hc'R1 & X7 & X7r).
  pose proof (ctxconv_tm CS0 (i := lC) eq_refl (wf_conv _ _ _ _ _ _ _ Hc' (eqty_sym _ _ _ _ _ _ ES0))) as Hc'R.
  destruct (Rtcall HΔL HΔ Hwi Hwi1 Eki HXX Hm Em ltac:(assumption) IHm) as (Hm' & Hmm & _ & Hm'R1 & X8 & X8r).
  pose proof (ctxconv_tm HΔ (i := lC) eq_refl (wf_conv _ _ _ _ _ _ _ Hm' (eqty_sym _ _ _ _ _ _ HXX))) as Hm'R.
  pose proof (IWf_ty_eq (i := lD) eq_refl ltac:(discriminate) HE Hmm) as HWW.
  destruct (Rtcall (k := lmax k ki) (k1 := lmax k1 ki1) HΔL HΔ (conj Hw Hwi) (conj Hw1 Hwi1) (leqv_lmax Ek Eki)
              HWW Ht Et ltac:(assumption) IHt) as (Ht' & Htt & Ht'R0 & Ht'R1 & X9 & X9r).
  pose proof (IWf_ty_eq (i := lD) eq_refl ltac:(discriminate) HE0 Hmm) as HWW0.
  assert (Ht'R : [ G' ; ΔR ⊢[ lC ] t' : tyIWf k ki X' A' N' Ot' C' m' @ lmax k ki ])
    by (eapply wf_conv; [exact Ht'R0 | exact (ctxconv_eqty HΔ (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ HWW0))]).
  (* the codes *)
  assert (Hr1 : [ G' ; Δ ⊢[ lD ] M[lsingle2 m t] ≅ M'[lsingle2 m' t'] @ k' ])
    by exact (IWf_mot_inst_eq (i := lD) eq_refl ltac:(discriminate) HS HMD HMM
                (lift_tm Hm HCD) (lift_tm Hm' HCD) Hmm (lift_tm Ht HCD) (lift_tm Ht' HCD) Htt).
  pose proof (sc_elimIWf_q (G := G') (i := lC) HCD ltac:(discriminate)
                Qg Qgi Qg' HX HX' (static_code_ty HCD HX HX' EX) HA HA' (static_code_ty HCD HA HA' EA)
                HN HN' (static_code_tm HCD HN HN' EN) HO HO' (static_code_tm HCD HO HO' EO)
                HC HC' (static_code_tm HCD HC HC' EC) HM HM' (static_code_ty HCD HM HM' EM1)
                HI HI' (static_code_ty HCD HI HI' (iwfihty_leq _ _ _ _ _ _ _ _ _ k1 ki1 k1' X' A' N' Ot' C' M'
                                                   Ek Eki Ek' EX EA EN EO EC EM1))
                Hc' Hm Hm' (static_code_tm HCD Hm Hm' Em) Ht Ht' (static_code_tm HCD Ht Ht' Et)) as HcRL.
  assert (HcR0 : [ G' ; ΔR ⊢[ lC ] tmElimIWf k1 ki1 k1' X' A' N' Ot' C' M' c' m' t' : M'[lsingle2 m' t'] @ k1' ]).
  { refine (ctxconv_tm HΔ (i := lC) eq_refl _).
    eapply wf_lconv; [eapply wf_conv; [exact HcRL | apply eqty_sym, Hr1] | apply lequiv_sym, Qg']. }
  refine (rec_t_br 60 (k :: ki :: k' :: nil) (k1 :: ki1 :: k1' :: nil)
            (GCtx Δ :: GTy X :: GTy A :: GTm N :: GTm Ot :: GTm C :: GTy M :: GTm c :: GTm m :: GTm t :: nil)
            (GCtx ΔR :: GTy X' :: GTy A' :: GTm N' :: GTm Ot' :: GTm C' :: GTy M' :: GTm c' :: GTm m' :: GTm t' :: nil)
            (recTL ki Δ X :: recTL k Δ A :: rectL lzero (Δ ,, A @ k) tyNat N :: rectL ki (Δ ,, A @ k) X⟨↑⟩ Ot
               :: rectL ki (Δ ,, A @ k ,, tyFin N @ lzero) X⟨↑⟩⟨↑⟩ C
               :: recTL k' (Δ ,, X @ ki ,, iwfmotty k ki X A N Ot C @ lmax k ki) M
               :: rectL k' (Δ ,, A @ k ,, iwfcsty k ki X A N Ot C @ lmax k ki ,, iwfihty k ki k' X A N Ot C M @ lmax lzero k')
                    (iwfstepty k ki X A N Ot C M) c
               :: rectL ki Δ X m :: rectL (lmax k ki) Δ (tyIWf k ki X A N Ot C m) t :: nil)
            (recTR ki1 ΔR X' :: recTR k1 ΔR A' :: rectR lzero (ΔR ,, A' @ k1) tyNat N'
               :: rectR ki1 (ΔR ,, A' @ k1) X'⟨↑⟩ Ot' :: rectR ki1 (ΔR ,, A' @ k1 ,, tyFin N' @ lzero) X'⟨↑⟩⟨↑⟩ C'
               :: recTR k1' (ΔR ,, X' @ ki1 ,, iwfmotty k1 ki1 X' A' N' Ot' C' @ lmax k1 ki1) M'
               :: rectR k1' (ΔR ,, A' @ k1 ,, iwfcsty k1 ki1 X' A' N' Ot' C' @ lmax k1 ki1
                               ,, iwfihty k1 ki1 k1' X' A' N' Ot' C' M' @ lmax lzero k1')
                    (iwfstepty k1 ki1 X' A' N' Ot' C' M') c'
               :: rectR ki1 ΔR X' m' :: rectR (lmax k1 ki1) ΔR (tyIWf k1 ki1 X' A' N' Ot' C' m') t' :: nil)
            ltac:(cbv; lia) eq_refl eq_refl eq_refl ltac:(repeat constructor; assumption)
            ltac:(repeat constructor; assumption)
            (uext_leqv (Forall2_cons _ _ Ek (Forall2_cons _ _ Eki (Forall2_cons _ _ Ek' (Forall2_nil _)))))
            HΔL HΔ HkL HkR Q' HTL HTR (ctxconv_eqty HΔ (i := lD) eq_refl Hr1) Hc0 HcRL HcR0
            ltac:(cbn; repeat split; assumption)
            (GS_br EP EM 60 (k :: ki :: k' :: nil) eq_refl Hσ _)
            (GS_br EP EM 60 (k1 :: ki1 :: k1' :: nil) eq_refl (GSubRel_refl_r EP EM Hσ) _) _ _ _ _ _ _ _).
  - gs_solve.
  - gs_solve.
  - sr_ctx_IWf; [exact X1 | exact X2 | exact X3 | exact X4 | exact X5 | exact X6 | exact X7 | exact X8 | exact X9].
  - sr_ctx_IWf; [exact X1r | exact X2r | exact X3r | exact X4r | exact X5r | exact X6r | exact X7r | exact X8r | exact X9r].
  - first [J_res | res_eq_IWf].
  - first [J_res | res_eq_IWf].
  - first [J_res | res_eq_IWf].
  - apply redt_elimIWf_inst; inst_side 60.
  - apply redt_elimIWf_inst; inst_side 60.
Qed.

End Rec.
