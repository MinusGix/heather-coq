(** * The recursion lemmas on code (M3_DESIGN.md E13)

    The FT case of a recursor, unfolded: related global substitutions
    [σ ≈ σ'] into [G[φ]], related local ones [e ≈ e'] into [Γ[φ]⦃σ⦄],
    and the recursors moved there. This file relates the moved motives'
    instances (from the motives' validity at every [ψ]), the reducts (from
    the branches' validity at [ψ = levels ++ φ], [σ] extended by the
    code's pieces, [e] by the recursive calls), and proves the recursion
    lemmas by induction on the code's C-typing. *)
From DeLaM.Validity Require Export RecSBase RecSNat RecSSig RecSId RecSSEq RecSSum RecSW RecSNe RecSWf RecSSq RecSIWf RecSIWfCode RecSIWfSupi RecSIWfElim
  RecSIWi RecSIWiCode RecSIWiSupi RecSIWiElim.

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

Lemma RT_nat {Δ} : RT Δ tyNat lzero.
Proof using EL ELM ELP EMl HMT HMT' Hbs Hbs' He Hl1 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VΓ.
  intros Hc ΔR kL kR c' HΔ HkL HkR E W. pose proof (sc_ctx HCD Hc) as HΔL. leq_inv.
  exact (rec_T_nat HΔL HΔ HkL HkR).
Qed.

Lemma RT_U {Δ k} : RT Δ (tyU k) (lsuc k).
Proof using EL ELM ELP EMl HMT HMT' Hbs Hbs' He Hl1 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VΓ.
  intros Hc ΔR kL kR c' HΔ HkL HkR E W. pose proof (sc_ctx HCD Hc) as HΔL.
  pose proof (lequiv_wf_l _ _ _ HkL) as Hw; cbn in Hw. leq_inv.
  exact (rec_T_U HΔL HΔ HkL HkR Hw W E).
Qed.

Lemma RT_lconv {Δ c k k'} : lequiv (gL G') k k' -> [ G' ; Δ ⊢[ lC ] c @ k' ] -> RT Δ c k' -> RT Δ c k.
Proof using EL.
  intros Q Hc' IH _ ΔR kL kR c' HΔ HkL HkR E W. rewrite EL in Q.
  exact (IH Hc' ΔR kL kR c' HΔ (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ Q) HkL)
           (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ Q) HkR) E W).
Qed.

Lemma RT_gvar {Δ U d k} : RT Δ (tyGvar U d) k.
Proof using EL ELM ELP EMl HG0 HMT HMT' He Hl1 Hl2 HrbL HrbR HΓ0 Hσ Hφ VBr VMT VMTr VMt VΓ VΓT VΓbr VΓt.
  intros Hc ΔR kL kR c' HΔ HkL HkR E W. pose proof (sc_ctx HCD Hc) as HΔL.
  destruct (scr_ty Hc E W) as [Hc' _]. pose proof E as E0; revert E0. leq_inv. match goal with H : U = ?x |- _ => subst x end. intros E0.
  exact (rec_T_gvar HΔL HΔ HkL HkR Hc Hc' E0).
Qed.

Lemma RT_pi {Δ k1 k2 A B} : lwf (gL G') k1 -> lwf (gL G') k2 ->
  [ G' ; Δ ⊢[ lC ] A @ k1 ] -> [ G' ; Δ ,, A @ k1 ⊢[ lC ] B @ k2 ] ->
  RT Δ A k1 -> RT (Δ ,, A @ k1) B k2 -> RT Δ (tyPi k1 k2 A B) (lmax k1 k2).
Proof using EL ELM ELP EMl HMT HMT' Hbs Hbs' He Hl1 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VΓ.
  intros Hw1 Hw2 HA HB IHA IHB Hc ΔR kL kR c' HΔ HkL HkR E W. rewrite EL in Hw1, Hw2.
  pose proof (sc_ctx HCD Hc) as HΔL. leq_inv.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_ty HB ltac:(eassumption) ltac:(eassumption)) as [HB' HBB].
  refine (rec_T_pi HΔL HΔ HkL HkR Hw1 Hw2 _ _ _ _ HA HB HA' HB' _ _ _ _); try eassumption.
  - refine (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw1) (lq Hw1 _ _) _ _); eassumption.
  - refine (IHB HB _ _ _ _ (ceq_ext HΔ (lift_ty HA HCD) HAA (lq Hw1 _ _)) (lequiv_refl _ _ Hw2) (lq Hw2 _ _) _ _);
      eassumption.
Qed.

Lemma RT_El {Δ k t} : lwf (gL G') k -> [ G' ; Δ ⊢[ lC ] t : tyU k @ lsuc k ] ->
  Rt Δ t (tyU k) (lsuc k) -> RT Δ (tyEl k t) k.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtr VΓ.
  intros Hw Ht IH Hc ΔR kL kR c' HΔ HkL HkR E W. rewrite EL in Hw.
  pose proof (sc_ctx HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  destruct (scr_tm Ht ltac:(eassumption) ltac:(eassumption)) as [Ht' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  refine (rec_T_El HΔL HΔ HkL HkR Hw _ _ Ht Ht' _ _); try eassumption.
  refine (IH Ht _ _ _ _ _ _ HΔ (lequiv_refl L' (lsuc k) Hw) (lequiv_lsuc' _ _ _ Q) _ _ _ _); try eassumption.
  - apply eqty_refl, wft_U; [discriminate | exact HΔL | rewrite EL; exact Hw].
  - apply eqty_U; [discriminate | exact HΔL | rewrite EL; exact Q].
Qed.

Lemma Rt_conv {Δ t T T' k} : [ G' ; Δ ⊢[ lD ] T ≅ T' @ k ] -> [ G' ; Δ ⊢[ lC ] t : T' @ k ] ->
  Rt Δ t T' k -> Rt Δ t T k.
Proof using .
  intros HT Ht IH _ ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W.
  apply (IH Ht); try assumption;
    [exact (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ HT) HTL) | exact (eqty_trans _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ HT) HTR)].
Qed.

Lemma Rt_lconv {Δ t T k k'} : lequiv (gL G') k k' -> [ G' ; Δ ⊢[ lC ] t : T @ k' ] -> Rt Δ t T k' -> Rt Δ t T k.
Proof using EL.
  intros Q Ht IH _ ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. pose proof Q as Qg. rewrite EL in Q.
  exact (IH Ht ΔR kL kR TL TR c' HΔ (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ Q) HkL)
           (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ Q) HkR)
           (eqty_lconv _ _ _ _ _ _ _ HTL (lequiv_sym _ _ _ Qg)) (eqty_lconv _ _ _ _ _ _ _ HTR (lequiv_sym _ _ _ Qg)) E W).
Qed.

Lemma Rt_var {Δ n T k} : in_ctx Δ n T k -> Rt Δ (var n) T k.
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hin Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv. match goal with H : n = ?x |- _ => subst x end.
  refine (rec_t_var HΔL HΔ HkL HkR HTL HTR _).
  apply wf_var; assumption.
Qed.

Lemma Rt_gvar {Δ u d T k} : Rt Δ (gvar u d) T k.
Proof using EL ELM ELP EMl HG0 HMt HMt' He Hl1 Hl2 HrbL HrbR HΓ0 Hσ Hφ VBr VMT VMt VMtr VΓ VΓT VΓbr VΓt.
  intros Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. pose proof (sc_ctx_tm HCD Hc) as HΔL.
  destruct (scr_tm Hc E W) as [Hc' _]. pose proof E as E0; revert E0. leq_inv. match goal with H : u = ?x |- _ => subst x end. intros E0.
  refine (rec_t_glob _ _ HΔL HΔ HkL HkR HTL HTR Hc Hc' E0); exact I.
Qed.

(** A defined global is code the recursor does not enter (M9). *)
Lemma Rt_gdef {Δ u b d T k} : Rt Δ (gdef u b d) T k.
Proof using EL ELM ELP EMl HG0 HMt HMt' He Hl1 Hl2 HrbL HrbR HΓ0 Hσ Hφ VBr VMT VMt VMtr VΓ VΓT VΓbr VΓt.
  intros Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. pose proof (sc_ctx_tm HCD Hc) as HΔL.
  destruct (scr_tm Hc E W) as [Hc' _].
  refine (rec_t_glob _ _ HΔL HΔ HkL HkR HTL HTR Hc Hc' E); [exact I | exact (boxed_global_leq (gdef u b d) c' I E)].
Qed.

Lemma Rt_nat {Δ} : Rt Δ tmNat (tyU lzero) (lsuc lzero).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  exact (rec_t_nat HΔL HΔ HkL HkR HTL HTR).
Qed.
Lemma Rt_zero {Δ} : Rt Δ zero tyNat lzero.
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  exact (rec_t_zero HΔL HΔ HkL HkR HTL HTR).
Qed.
Lemma Rt_U {Δ j} : Rt Δ (tmU j) (tyU (lsuc j)) (lsuc (lsuc j)).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. pose proof (sc_ctx_tm HCD Hc) as HΔL.
  pose proof (lequiv_wf_l _ _ _ HkL) as Hw; cbn in Hw. leq_inv.
  exact (rec_t_U HΔL HΔ HkL HkR Hw W E HTL HTR).
Qed.

Lemma Rt_succ {Δ t} : [ G' ; Δ ⊢[ lC ] t : tyNat @ lzero ] -> Rt Δ t tyNat lzero -> Rt Δ (succ t) tyNat lzero.
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Ht IH Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  destruct (scr_tm Ht E W) as [Ht' _].
  refine (rec_t_succ HΔL HΔ HkL HkR HTL HTR Ht Ht' E _).
  assert (HN : [ G' ; Δ ⊢[ lD ] tyNat ≅ tyNat @ lzero ]) by (apply eqty_refl, wft_nat; [discriminate | exact HΔL]).
  exact (IH Ht _ _ _ _ _ _ HΔ (lequiv_refl L' lzero I) (lequiv_refl L' lzero I) HN HN E W).
Qed.

Lemma Rt_pi {Δ k k' s t} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] -> [ G' ; Δ ,, tyEl k s @ k ⊢[ lC ] t : tyU k' @ lsuc k' ] ->
  Rt Δ s (tyU k) (lsuc k) -> Rt (Δ ,, tyEl k s @ k) t (tyU k') (lsuc k') ->
  Rt Δ (tmPi k k' s t) (tyU (lmax k k')) (lsuc (lmax k k')).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hw Hw' Hs Ht IHs IHt Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. pose proof (sc_ctx_tm HCD Ht) as HΔLs. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  destruct (scr_tm Hs ltac:(eassumption) ltac:(eassumption)) as [Hs' Hss].
  destruct (scr_tm Ht ltac:(eassumption) ltac:(eassumption)) as [Ht' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  refine (rec_t_pi HΔL HΔ HkL HkR Hw Hw' _ _ _ _ HTL HTR Hs Hs' _ Ht Ht' _ _ _); try eassumption.
  - refine (IHs Hs _ _ _ _ _ _ HΔ (lequiv_refl L' (lsuc k) Hw) (lequiv_lsuc' _ _ _ Q) _ _ _ _); try eassumption.
    + apply eqty_refl, wft_U; [discriminate | exact HΔL | rewrite EL; exact Hw].
    + apply eqty_U; [discriminate | exact HΔL | rewrite EL; exact Q].
  - assert (HEl : [ G' ; Δ ⊢[ lD ] tyEl k s @ k ]) by (apply wft_El; [discriminate | rewrite EL; exact Hw | exact (lift_tm Hs HCD)]).
    refine (IHt Ht _ _ _ _ _ _ (ceq_ext HΔ HEl _ Q) (lequiv_refl L' (lsuc k') Hw') (lequiv_lsuc' _ _ _ Q') _ _ _ _);
      try eassumption.
    + apply eqty_El; [discriminate | rewrite EL; exact Q | exact Hss].
    + apply eqty_refl, wft_U; [discriminate | exact HΔLs | rewrite EL; exact Hw'].
    + apply eqty_U; [discriminate | exact HΔLs | rewrite EL; exact Q'].
Qed.

Lemma Rt_lam {Δ k k' A B b} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ,, A @ k ⊢[ lC ] b : B @ k' ] ->
  RT Δ A k -> Rt (Δ ,, A @ k) b B k' -> Rt Δ (lam k k' A b) (tyPi k k' A B) (lmax k k').
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros Hw Hw' HA Hb IHA IHb Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_tm Hb ltac:(eassumption) ltac:(eassumption)) as [Hb' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  refine (rec_t_lam HΔL HΔ HkL HkR Hw Hw' _ _ _ _ HTL HTR HA HA' _ Hb Hb' _ _ _); try eassumption.
  - exact (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - intros BL BR HBL HBR.
    exact (IHb Hb _ _ _ _ _ _ (ceq_ext HΔ (lift_ty HA HCD) HAA Q) (lequiv_refl _ _ Hw') Q' HBL HBR
             ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma Rt_app {Δ k k' A B f a} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ,, A @ k ⊢[ lC ] B @ k' ] ->
  [ G' ; Δ ⊢[ lC ] f : tyPi k k' A B @ lmax k k' ] -> [ G' ; Δ ⊢[ lC ] a : A @ k ] ->
  RT Δ A k -> RT (Δ ,, A @ k) B k' -> Rt Δ f (tyPi k k' A B) (lmax k k') -> Rt Δ a A k ->
  Rt Δ (app f k k' A B a) (B[lsingle a]) k'.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros Hw Hw' HA HB Hf Ha IHA IHB IHf IHa Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  match goal with H : ty_leq A ?x |- _ => rename x into A' end.
  match goal with H : ty_leq B ?x |- _ => rename x into B' end.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_ty HB ltac:(eassumption) ltac:(eassumption)) as [HB' HBB].
  destruct (scr_tm Hf ltac:(eassumption) ltac:(eassumption)) as [Hf' _].
  destruct (scr_tm Ha ltac:(eassumption) ltac:(eassumption)) as [Ha' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  assert (X : [ G' ; Δ ⊢[ lD ] tyPi k k' A B ≅ tyPi k1 k1' A' B' @ lmax k k' ]).
  { apply eqty_pi; [discriminate | rewrite EL; exact Q | rewrite EL; exact Q' | exact (lift_ty HA HCD) | exact HAA | exact HBB]. }
  refine (rec_t_app HΔL HΔ HkL HkR Hw Hw' _ _ _ _ HTL HTR HA HA' _ HB HB' _ Hf Hf' _ Ha Ha' _ _ _ _ _);
    try eassumption.
  - exact (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - exact (IHB HB _ _ _ _ (ceq_ext HΔ (lift_ty HA HCD) HAA Q) (lequiv_refl _ _ Hw') Q'
             ltac:(eassumption) ltac:(eassumption)).
  - exact (IHf Hf _ _ _ _ _ _ HΔ (lequiv_refl L' (lmax k k') (conj Hw Hw')) (lequiv_lmax' _ _ _ _ _ Q Q')
             (eq_self_l X) X ltac:(eassumption) ltac:(eassumption)).
  - exact (IHa Ha _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HAA) HAA ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma Rt_natrec {Δ k M s z t} : lwf (gL G') k ->
  [ G' ; Δ ,, tyNat @ lzero ⊢[ lC ] M @ k ] -> [ G' ; Δ ⊢[ lC ] s : M[lsingle zero] @ k ] ->
  [ G' ; Δ ,, tyNat @ lzero ,, M @ k ⊢[ lC ] z : M[lsucc] @ k ] -> [ G' ; Δ ⊢[ lC ] t : tyNat @ lzero ] ->
  RT (Δ ,, tyNat @ lzero) M k -> Rt Δ s (M[lsingle zero]) k ->
  Rt (Δ ,, tyNat @ lzero ,, M @ k) z (M[lsucc]) k -> Rt Δ t tyNat lzero ->
  Rt Δ (natrec k M s z t) (M[lsingle t]) k.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros Hw HM Hs Hz Ht IHM IHs IHz IHt Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : ty_leq M ?x |- _ => rename x into M' end.
  destruct (scr_ty HM ltac:(eassumption) ltac:(eassumption)) as [HM' HMM].
  destruct (scr_tm Hs ltac:(eassumption) ltac:(eassumption)) as [Hs' _].
  destruct (scr_tm Hz ltac:(eassumption) ltac:(eassumption)) as [Hz' _].
  destruct (scr_tm Ht ltac:(eassumption) ltac:(eassumption)) as [Ht' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  assert (HN0 : [ G' ; Δ ⊢[ lD ] tyNat @ lzero ]) by (apply wft_nat; [discriminate | exact HΔL]).
  assert (CN : [ G' ⊢[ lD ] Δ ,, tyNat @ lzero ≅ ΔR ,, tyNat @ lzero ])
    by (apply ceq_ext; [exact HΔ | exact HN0 | apply eqty_refl, HN0 | apply lequiv_refl; exact I]).
  pose proof (lift_ty HM HCD) as HMD.
  assert (CNM : [ G' ⊢[ lD ] Δ ,, tyNat @ lzero ,, M @ k ≅ ΔR ,, tyNat @ lzero ,, M' @ k1 ])
    by (apply ceq_ext; [exact CN | exact HMD | exact HMM | exact Q]).
  pose proof (sc_ctx_tm HCD Hz) as HΔLNM.
  assert (HM0 : [ G' ; Δ ⊢[ lD ] M[lsingle zero] ≅ M'[lsingle zero] @ k ])
    by exact (eqty_single (i := lD) eq_refl HMM (wf_zero _ lD _ ltac:(discriminate) HΔL)).
  assert (HMs : [ G' ; Δ ,, tyNat @ lzero ,, M @ k ⊢[ lD ] M[lsucc] ≅ M'[lsucc] @ k ])
    by exact (eqty_subst (i := lD) eq_refl HMM (lsub_wf_lsucc (i := lD) eq_refl ltac:(discriminate) HΔLNM)).
  assert (HNN : [ G' ; Δ ⊢[ lD ] tyNat ≅ tyNat @ lzero ]) by (apply eqty_refl, HN0).
  refine (rec_t_natrec HΔL HΔ HkL HkR Hw _ _ HTL HTR HM HM' _ Hs Hs' _ Hz Hz' _ Ht Ht' _ _ _ _ _); try eassumption.
  - exact (IHM HM _ _ _ _ CN (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - exact (IHs Hs _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HM0) HM0 ltac:(eassumption) ltac:(eassumption)).
  - exact (IHz Hz _ _ _ _ _ _ CNM (lequiv_refl _ _ Hw) Q (eq_self_l HMs) HMs ltac:(eassumption) ltac:(eassumption)).
  - exact (IHt Ht _ _ _ _ _ _ HΔ (lequiv_refl L' lzero I) (lequiv_refl L' lzero I) HNN HNN
             ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma RT_sig {Δ k1 k2 A B} : lwf (gL G') k1 -> lwf (gL G') k2 ->
  [ G' ; Δ ⊢[ lC ] A @ k1 ] -> [ G' ; Δ ,, A @ k1 ⊢[ lC ] B @ k2 ] ->
  RT Δ A k1 -> RT (Δ ,, A @ k1) B k2 -> RT Δ (tySig k1 k2 A B) (lmax k1 k2).
Proof using EL ELM ELP EMl HMT HMT' Hbs Hbs' He Hl1 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VΓ.
  intros Hw1 Hw2 HA HB IHA IHB Hc ΔR kL kR c' HΔ HkL HkR E W. rewrite EL in Hw1, Hw2.
  pose proof (sc_ctx HCD Hc) as HΔL. leq_inv.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_ty HB ltac:(eassumption) ltac:(eassumption)) as [HB' HBB].
  refine (rec_T_sig HΔL HΔ HkL HkR Hw1 Hw2 _ _ _ _ HA HB HA' HB' _ _ _ _); try eassumption.
  - refine (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw1) (lq Hw1 _ _) _ _); eassumption.
  - refine (IHB HB _ _ _ _ (ceq_ext HΔ (lift_ty HA HCD) HAA (lq Hw1 _ _)) (lequiv_refl _ _ Hw2) (lq Hw2 _ _) _ _);
      eassumption.
Qed.

Lemma RT_W {Δ k1 k2 A B} : lwf (gL G') k1 -> lwf (gL G') k2 ->
  [ G' ; Δ ⊢[ lC ] A @ k1 ] -> [ G' ; Δ ,, A @ k1 ⊢[ lC ] B @ k2 ] ->
  RT Δ A k1 -> RT (Δ ,, A @ k1) B k2 -> RT Δ (tyW k1 k2 A B) (lmax k1 k2).
Proof using EL ELM ELP EMl HMT HMT' Hbs Hbs' He Hl1 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VΓ.
  intros Hw1 Hw2 HA HB IHA IHB Hc ΔR kL kR c' HΔ HkL HkR E W. rewrite EL in Hw1, Hw2.
  pose proof (sc_ctx HCD Hc) as HΔL. leq_inv.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_ty HB ltac:(eassumption) ltac:(eassumption)) as [HB' HBB].
  refine (rec_T_W HΔL HΔ HkL HkR Hw1 Hw2 _ _ _ _ HA HB HA' HB' _ _ _ _); try eassumption.
  - refine (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw1) (lq Hw1 _ _) _ _); eassumption.
  - refine (IHB HB _ _ _ _ (ceq_ext HΔ (lift_ty HA HCD) HAA (lq Hw1 _ _)) (lequiv_refl _ _ Hw2) (lq Hw2 _ _) _ _);
      eassumption.
Qed.

Lemma RT_unit {Δ k} : RT Δ (tyUnit k) k.
Proof using EL ELM ELP EMl HMT HMT' Hbs Hbs' He Hl1 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VΓ.
  intros Hc ΔR kL kR c' HΔ HkL HkR E W. pose proof (sc_ctx HCD Hc) as HΔL.
  pose proof (lequiv_wf_l _ _ _ HkL) as Hw. leq_inv.
  exact (rec_T_unit HΔL HΔ HkL HkR Hw W E).
Qed.

Lemma Rt_codesig {Δ k k' s t} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] -> [ G' ; Δ ,, tyEl k s @ k ⊢[ lC ] t : tyU k' @ lsuc k' ] ->
  Rt Δ s (tyU k) (lsuc k) -> Rt (Δ ,, tyEl k s @ k) t (tyU k') (lsuc k') ->
  Rt Δ (tmSig k k' s t) (tyU (lmax k k')) (lsuc (lmax k k')).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hw Hw' Hs Ht IHs IHt Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. pose proof (sc_ctx_tm HCD Ht) as HΔLs. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  destruct (scr_tm Hs ltac:(eassumption) ltac:(eassumption)) as [Hs' Hss].
  destruct (scr_tm Ht ltac:(eassumption) ltac:(eassumption)) as [Ht' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  refine (rec_t_codesig HΔL HΔ HkL HkR Hw Hw' _ _ _ _ HTL HTR Hs Hs' _ Ht Ht' _ _ _); try eassumption.
  - refine (IHs Hs _ _ _ _ _ _ HΔ (lequiv_refl L' (lsuc k) Hw) (lequiv_lsuc' _ _ _ Q) _ _ _ _); try eassumption.
    + apply eqty_refl, wft_U; [discriminate | exact HΔL | rewrite EL; exact Hw].
    + apply eqty_U; [discriminate | exact HΔL | rewrite EL; exact Q].
  - assert (HEl : [ G' ; Δ ⊢[ lD ] tyEl k s @ k ]) by (apply wft_El; [discriminate | rewrite EL; exact Hw | exact (lift_tm Hs HCD)]).
    refine (IHt Ht _ _ _ _ _ _ (ceq_ext HΔ HEl _ Q) (lequiv_refl L' (lsuc k') Hw') (lequiv_lsuc' _ _ _ Q') _ _ _ _);
      try eassumption.
    + apply eqty_El; [discriminate | rewrite EL; exact Q | exact Hss].
    + apply eqty_refl, wft_U; [discriminate | exact HΔLs | rewrite EL; exact Hw'].
    + apply eqty_U; [discriminate | exact HΔLs | rewrite EL; exact Q'].
Qed.

Lemma Rt_codeW {Δ k k' s t} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] -> [ G' ; Δ ,, tyEl k s @ k ⊢[ lC ] t : tyU k' @ lsuc k' ] ->
  Rt Δ s (tyU k) (lsuc k) -> Rt (Δ ,, tyEl k s @ k) t (tyU k') (lsuc k') ->
  Rt Δ (tmW k k' s t) (tyU (lmax k k')) (lsuc (lmax k k')).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hw Hw' Hs Ht IHs IHt Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. pose proof (sc_ctx_tm HCD Ht) as HΔLs. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  destruct (scr_tm Hs ltac:(eassumption) ltac:(eassumption)) as [Hs' Hss].
  destruct (scr_tm Ht ltac:(eassumption) ltac:(eassumption)) as [Ht' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  refine (rec_t_codeW HΔL HΔ HkL HkR Hw Hw' _ _ _ _ HTL HTR Hs Hs' _ Ht Ht' _ _ _); try eassumption.
  - refine (IHs Hs _ _ _ _ _ _ HΔ (lequiv_refl L' (lsuc k) Hw) (lequiv_lsuc' _ _ _ Q) _ _ _ _); try eassumption.
    + apply eqty_refl, wft_U; [discriminate | exact HΔL | rewrite EL; exact Hw].
    + apply eqty_U; [discriminate | exact HΔL | rewrite EL; exact Q].
  - assert (HEl : [ G' ; Δ ⊢[ lD ] tyEl k s @ k ]) by (apply wft_El; [discriminate | rewrite EL; exact Hw | exact (lift_tm Hs HCD)]).
    refine (IHt Ht _ _ _ _ _ _ (ceq_ext HΔ HEl _ Q) (lequiv_refl L' (lsuc k') Hw') (lequiv_lsuc' _ _ _ Q') _ _ _ _);
      try eassumption.
    + apply eqty_El; [discriminate | rewrite EL; exact Q | exact Hss].
    + apply eqty_refl, wft_U; [discriminate | exact HΔLs | rewrite EL; exact Hw'].
    + apply eqty_U; [discriminate | exact HΔLs | rewrite EL; exact Q'].
Qed.

Lemma Rt_codeunit {Δ j} : Rt Δ (tmUnit j) (tyU j) (lsuc j).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. pose proof (sc_ctx_tm HCD Hc) as HΔL.
  pose proof (lequiv_wf_l _ _ _ HkL) as Hw; cbn in Hw. leq_inv.
  exact (rec_t_codeunit HΔL HΔ HkL HkR Hw W E HTL HTR).
Qed.

Lemma Rt_triv {Δ j} : Rt Δ (tmTriv j) (tyUnit j) j.
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. pose proof (sc_ctx_tm HCD Hc) as HΔL.
  pose proof (lequiv_wf_l _ _ _ HkL) as Hw. leq_inv.
  exact (rec_t_triv HΔL HΔ HkL HkR Hw W E HTL HTR).
Qed.

Lemma Rt_pair {Δ k k' A B a b} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ,, A @ k ⊢[ lC ] B @ k' ] ->
  [ G' ; Δ ⊢[ lC ] a : A @ k ] -> [ G' ; Δ ⊢[ lC ] b : B[lsingle a] @ k' ] ->
  RT Δ A k -> RT (Δ ,, A @ k) B k' -> Rt Δ a A k -> Rt Δ b (B[lsingle a]) k' ->
  Rt Δ (tmPair k k' A B a b) (tySig k k' A B) (lmax k k').
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros Hw Hw' HA HB Ha Hb IHA IHB IHa IHb Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  match goal with H : ty_leq A ?x |- _ => rename x into A' end.
  match goal with H : ty_leq B ?x |- _ => rename x into B' end.
  match goal with H : tm_leq a ?x |- _ => rename x into a' end.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_ty HB ltac:(eassumption) ltac:(eassumption)) as [HB' HBB].
  destruct (scr_tm Ha ltac:(eassumption) ltac:(eassumption)) as [Ha' Haa].
  destruct (scr_tm Hb ltac:(eassumption) ltac:(eassumption)) as [Hb' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  assert (X : [ G' ; Δ ⊢[ lD ] B[lsingle a] ≅ B'[lsingle a'] @ k' ])
    by exact (eqty_subst_single_D HBB (lift_ty HB' HCD) Haa (lift_tm Ha HCD) (lift_tm Ha' HCD)).
  refine (rec_t_pair HΔL HΔ HkL HkR Hw Hw' _ _ _ _ HTL HTR HA HA' _ HB HB' _ Ha Ha' _ Hb Hb' _ _ _ _ _);
    try eassumption.
  - exact (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - exact (IHB HB _ _ _ _ (ceq_ext HΔ (lift_ty HA HCD) HAA Q) (lequiv_refl _ _ Hw') Q'
             ltac:(eassumption) ltac:(eassumption)).
  - exact (IHa Ha _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HAA) HAA ltac:(eassumption) ltac:(eassumption)).
  - exact (IHb Hb _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw') Q' (eq_self_l X) X ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma Rt_fst {Δ k k' A B p} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ,, A @ k ⊢[ lC ] B @ k' ] ->
  [ G' ; Δ ⊢[ lC ] p : tySig k k' A B @ lmax k k' ] ->
  RT Δ A k -> RT (Δ ,, A @ k) B k' -> Rt Δ p (tySig k k' A B) (lmax k k') ->
  Rt Δ (tmFst k k' A B p) A k.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros Hw Hw' HA HB Hp IHA IHB IHp Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  match goal with H : ty_leq A ?x |- _ => rename x into A' end.
  match goal with H : ty_leq B ?x |- _ => rename x into B' end.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_ty HB ltac:(eassumption) ltac:(eassumption)) as [HB' HBB].
  destruct (scr_tm Hp ltac:(eassumption) ltac:(eassumption)) as [Hp' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  assert (X : [ G' ; Δ ⊢[ lD ] tySig k k' A B ≅ tySig k1 k1' A' B' @ lmax k k' ]).
  { apply eqty_sig; [discriminate | rewrite EL; exact Q | rewrite EL; exact Q' | exact (lift_ty HA HCD) | exact HAA | exact HBB]. }
  refine (rec_t_fst HΔL HΔ HkL HkR Hw Hw' _ _ _ _ HTL HTR HA HA' _ HB HB' _ Hp Hp' _ _ _ _);
    try eassumption.
  - exact (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - exact (IHB HB _ _ _ _ (ceq_ext HΔ (lift_ty HA HCD) HAA Q) (lequiv_refl _ _ Hw') Q'
             ltac:(eassumption) ltac:(eassumption)).
  - exact (IHp Hp _ _ _ _ _ _ HΔ (lequiv_refl L' (lmax k k') (conj Hw Hw')) (lequiv_lmax' _ _ _ _ _ Q Q')
             (eq_self_l X) X ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma Rt_snd {Δ k k' A B p} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ,, A @ k ⊢[ lC ] B @ k' ] ->
  [ G' ; Δ ⊢[ lC ] p : tySig k k' A B @ lmax k k' ] ->
  RT Δ A k -> RT (Δ ,, A @ k) B k' -> Rt Δ p (tySig k k' A B) (lmax k k') ->
  Rt Δ (tmSnd k k' A B p) (B[lsingle (tmFst k k' A B p)]) k'.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros Hw Hw' HA HB Hp IHA IHB IHp Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  match goal with H : ty_leq A ?x |- _ => rename x into A' end.
  match goal with H : ty_leq B ?x |- _ => rename x into B' end.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_ty HB ltac:(eassumption) ltac:(eassumption)) as [HB' HBB].
  destruct (scr_tm Hp ltac:(eassumption) ltac:(eassumption)) as [Hp' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  assert (X : [ G' ; Δ ⊢[ lD ] tySig k k' A B ≅ tySig k1 k1' A' B' @ lmax k k' ]).
  { apply eqty_sig; [discriminate | rewrite EL; exact Q | rewrite EL; exact Q' | exact (lift_ty HA HCD) | exact HAA | exact HBB]. }
  refine (rec_t_snd HΔL HΔ HkL HkR Hw Hw' _ _ _ _ HTL HTR HA HA' _ HB HB' _ Hp Hp' _ _ _ _);
    try eassumption.
  - exact (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - exact (IHB HB _ _ _ _ (ceq_ext HΔ (lift_ty HA HCD) HAA Q) (lequiv_refl _ _ Hw') Q'
             ltac:(eassumption) ltac:(eassumption)).
  - exact (IHp Hp _ _ _ _ _ _ HΔ (lequiv_refl L' (lmax k k') (conj Hw Hw')) (lequiv_lmax' _ _ _ _ _ Q Q')
             (eq_self_l X) X ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma RT_id {Δ k A a b} : lwf (gL G') k ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ⊢[ lC ] a : A @ k ] -> [ G' ; Δ ⊢[ lC ] b : A @ k ] ->
  RT Δ A k -> Rt Δ a A k -> Rt Δ b A k -> RT Δ (tyId k A a b) k.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros Hw HA Ha Hb IHA IHa IHb Hc ΔR kL kR c' HΔ HkL HkR E W. rewrite EL in Hw.
  pose proof (sc_ctx HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : ty_leq A ?x |- _ => rename x into A' end.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_tm Ha ltac:(eassumption) ltac:(eassumption)) as [Ha' _].
  destruct (scr_tm Hb ltac:(eassumption) ltac:(eassumption)) as [Hb' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  refine (rec_T_id HΔL HΔ HkL HkR Hw _ _ HA HA' _ Ha Ha' _ Hb Hb' _ _ _ _); try eassumption.
  - exact (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - exact (IHa Ha _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HAA) HAA ltac:(eassumption) ltac:(eassumption)).
  - exact (IHb Hb _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HAA) HAA ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma Rt_codeid {Δ k s t u} : lwf (gL G') k ->
  [ G' ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] ->
  [ G' ; Δ ⊢[ lC ] t : tyEl k s @ k ] -> [ G' ; Δ ⊢[ lC ] u : tyEl k s @ k ] ->
  Rt Δ s (tyU k) (lsuc k) -> Rt Δ t (tyEl k s) k -> Rt Δ u (tyEl k s) k ->
  Rt Δ (tmId k s t u) (tyU k) (lsuc k).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros Hw Hs Ht Hu IHs IHt IHu Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : tm_leq s ?x |- _ => rename x into s' end.
  destruct (scr_tm Hs ltac:(eassumption) ltac:(eassumption)) as [Hs' Hss].
  destruct (scr_tm Ht ltac:(eassumption) ltac:(eassumption)) as [Ht' _].
  destruct (scr_tm Hu ltac:(eassumption) ltac:(eassumption)) as [Hu' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  assert (HUU : [ G' ; Δ ⊢[ lD ] tyU k ≅ tyU k1 @ lsuc k ])
    by (apply eqty_U; [discriminate | exact HΔL | rewrite EL; exact Q]).
  assert (HEl : [ G' ; Δ ⊢[ lD ] tyEl k s ≅ tyEl k1 s' @ k ])
    by (apply eqty_El; [discriminate | rewrite EL; exact Q | exact Hss]).
  refine (rec_t_codeid HΔL HΔ HkL HkR Hw _ _ HTL HTR Hs Hs' _ Ht Ht' _ Hu Hu' _ _ _ _); try eassumption.
  - exact (IHs Hs _ _ _ _ _ _ HΔ (lequiv_refl L' (lsuc k) Hw) (lequiv_suc _ _ _ Q) (eq_self_l HUU) HUU
             ltac:(eassumption) ltac:(eassumption)).
  - exact (IHt Ht _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HEl) HEl ltac:(eassumption) ltac:(eassumption)).
  - exact (IHu Hu _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HEl) HEl ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma Rt_refl {Δ k A a} : lwf (gL G') k ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ⊢[ lC ] a : A @ k ] ->
  RT Δ A k -> Rt Δ a A k -> Rt Δ (tmRefl k A a) (tyId k A a a) k.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros Hw HA Ha IHA IHa Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : ty_leq A ?x |- _ => rename x into A' end.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_tm Ha ltac:(eassumption) ltac:(eassumption)) as [Ha' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  refine (rec_t_refl HΔL HΔ HkL HkR Hw _ _ HTL HTR HA HA' _ Ha Ha' _ _ _); try eassumption.
  - exact (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - exact (IHa Ha _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HAA) HAA ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma Rt_J {Δ k k' A a M c u e0} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ⊢[ lC ] a : A @ k ] ->
  [ G' ; Δ ,, A @ k ⊢[ lC ] tyId k A⟨↑⟩ a⟨↑⟩ (var 0) @ k ] ->
  [ G' ; Δ ,, A @ k ,, tyId k A⟨↑⟩ a⟨↑⟩ (var 0) @ k ⊢[ lC ] M @ k' ] ->
  [ G' ; Δ ⊢[ lC ] c : M[lsingle2 a (tmRefl k A a)] @ k' ] ->
  [ G' ; Δ ⊢[ lC ] u : A @ k ] -> [ G' ; Δ ⊢[ lC ] e0 : tyId k A a u @ k ] ->
  RT Δ A k -> Rt Δ a A k -> RT (Δ ,, A @ k ,, tyId k A⟨↑⟩ a⟨↑⟩ (var 0) @ k) M k' ->
  Rt Δ c (M[lsingle2 a (tmRefl k A a)]) k' -> Rt Δ u A k -> Rt Δ e0 (tyId k A a u) k ->
  Rt Δ (tmJ k k' A a M c u e0) (M[lsingle2 u e0]) k'.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros Hw Hw' HA Ha HI HM Hc Hu He0 IHA IHa IHM IHc IHu IHe Hc0 ΔR kL kR TL TR c0' HΔ HkL HkR HTL HTR E W.
  rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc0) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  match goal with H : ty_leq A ?x |- _ => rename x into A' end.
  match goal with H : tm_leq a ?x |- _ => rename x into a' end.
  match goal with H : ty_leq M ?x |- _ => rename x into M' end.
  match goal with H : tm_leq u ?x |- _ => rename x into u' end.
  match goal with H : tm_leq e0 ?x |- _ => rename x into e0' end.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_tm Ha ltac:(eassumption) ltac:(eassumption)) as [Ha' Haa].
  destruct (scr_ty HM ltac:(eassumption) ltac:(eassumption)) as [HM' HMM].
  destruct (scr_tm Hc ltac:(eassumption) ltac:(eassumption)) as [Hc' _].
  destruct (scr_tm Hu ltac:(eassumption) ltac:(eassumption)) as [Hu' Huu].
  destruct (scr_tm He0 ltac:(eassumption) ltac:(eassumption)) as [He0' Hee].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q).
  pose proof (J_ctx_eq' (i := lD) eq_refl ltac:(discriminate) Qg HΔ (lift_ty HA HCD) HAA Haa) as CM1.
  destruct (J_facts_D (l3 := k1) Qg (lift_ty HA HCD) HAA (lift_ty HA' HCD) (lift_tm Ha HCD) Haa (lift_tm Ha' HCD)
              HMM (lift_ty HM' HCD) (lift_tm Hu HCD) Huu (lift_tm Hu' HCD) (lift_tm He0 HCD) Hee (lift_tm He0' HCD))
    as (_ & Hc1 & _ & HId1).
  refine (rec_t_J HΔL HΔ HkL HkR Hw Hw' _ _ _ _ HTL HTR HA HA' _ Ha Ha' _ HI HM HM' _ Hc Hc' _ Hu Hu' _ He0 He0' _
            _ _ _ _ _ _); try eassumption.
  - exact (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - exact (IHa Ha _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HAA) HAA ltac:(eassumption) ltac:(eassumption)).
  - exact (IHM HM _ _ _ _ CM1 (lequiv_refl _ _ Hw') Q' ltac:(eassumption) ltac:(eassumption)).
  - exact (IHc Hc _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw') Q' (eq_self_l Hc1) Hc1 ltac:(eassumption) ltac:(eassumption)).
  - exact (IHu Hu _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HAA) HAA ltac:(eassumption) ltac:(eassumption)).
  - exact (IHe He0 _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HId1) HId1 ltac:(eassumption) ltac:(eassumption)).
Qed.

(** Strict equality (M10c). *)
Lemma RT_seq {Δ k A a b} : lwf (gL G') k ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ⊢[ lC ] a : A @ k ] -> [ G' ; Δ ⊢[ lC ] b : A @ k ] ->
  RT Δ A k -> Rt Δ a A k -> Rt Δ b A k -> RT Δ (tySEq k A a b) k.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros Hw HA Ha Hb IHA IHa IHb Hc ΔR kL kR c' HΔ HkL HkR E W. rewrite EL in Hw.
  pose proof (sc_ctx HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : ty_leq A ?x |- _ => rename x into A' end.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_tm Ha ltac:(eassumption) ltac:(eassumption)) as [Ha' _].
  destruct (scr_tm Hb ltac:(eassumption) ltac:(eassumption)) as [Hb' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  refine (rec_T_seq HΔL HΔ HkL HkR Hw _ _ HA HA' _ Ha Ha' _ Hb Hb' _ _ _ _); try eassumption.
  - exact (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - exact (IHa Ha _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HAA) HAA ltac:(eassumption) ltac:(eassumption)).
  - exact (IHb Hb _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HAA) HAA ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma Rt_codeseq {Δ k s t u} : lwf (gL G') k ->
  [ G' ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] ->
  [ G' ; Δ ⊢[ lC ] t : tyEl k s @ k ] -> [ G' ; Δ ⊢[ lC ] u : tyEl k s @ k ] ->
  Rt Δ s (tyU k) (lsuc k) -> Rt Δ t (tyEl k s) k -> Rt Δ u (tyEl k s) k ->
  Rt Δ (tmSEq k s t u) (tyU k) (lsuc k).
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros Hw Hs Ht Hu IHs IHt IHu Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : tm_leq s ?x |- _ => rename x into s' end.
  destruct (scr_tm Hs ltac:(eassumption) ltac:(eassumption)) as [Hs' Hss].
  destruct (scr_tm Ht ltac:(eassumption) ltac:(eassumption)) as [Ht' _].
  destruct (scr_tm Hu ltac:(eassumption) ltac:(eassumption)) as [Hu' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  assert (HUU : [ G' ; Δ ⊢[ lD ] tyU k ≅ tyU k1 @ lsuc k ])
    by (apply eqty_U; [discriminate | exact HΔL | rewrite EL; exact Q]).
  assert (HEl : [ G' ; Δ ⊢[ lD ] tyEl k s ≅ tyEl k1 s' @ k ])
    by (apply eqty_El; [discriminate | rewrite EL; exact Q | exact Hss]).
  refine (rec_t_codeseq HΔL HΔ HkL HkR Hw _ _ HTL HTR Hs Hs' _ Ht Ht' _ Hu Hu' _ _ _ _); try eassumption.
  - exact (IHs Hs _ _ _ _ _ _ HΔ (lequiv_refl L' (lsuc k) Hw) (lequiv_suc _ _ _ Q) (eq_self_l HUU) HUU
             ltac:(eassumption) ltac:(eassumption)).
  - exact (IHt Ht _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HEl) HEl ltac:(eassumption) ltac:(eassumption)).
  - exact (IHu Hu _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HEl) HEl ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma Rt_srefl {Δ k A a} : lwf (gL G') k ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ⊢[ lC ] a : A @ k ] ->
  RT Δ A k -> Rt Δ a A k -> Rt Δ (srefl k A a) (tySEq k A a a) k.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros Hw HA Ha IHA IHa Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : ty_leq A ?x |- _ => rename x into A' end.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_tm Ha ltac:(eassumption) ltac:(eassumption)) as [Ha' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  refine (rec_t_srefl HΔL HΔ HkL HkR Hw _ _ HTL HTR HA HA' _ Ha Ha' _ _ _); try eassumption.
  - exact (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - exact (IHa Ha _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HAA) HAA ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma RT_sempty {Δ k} : RT Δ (tySEmpty k) k.
Proof using EL ELM ELP EMl HMT HMT' Hbs Hbs' He Hl1 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VΓ.
  intros Hc ΔR kL kR c' HΔ HkL HkR E W. pose proof (sc_ctx HCD Hc) as HΔL.
  pose proof (lequiv_wf_l _ _ _ HkL) as Hw. leq_inv.
  exact (rec_T_sempty HΔL HΔ HkL HkR Hw W E).
Qed.

Lemma Rt_codesempty {Δ j} : Rt Δ (tmSEmpty j) (tyU j) (lsuc j).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. pose proof (sc_ctx_tm HCD Hc) as HΔL.
  pose proof (lequiv_wf_l _ _ _ HkL) as Hw; cbn in Hw. leq_inv.
  exact (rec_t_codesempty HΔL HΔ HkL HkR Hw W E HTL HTR).
Qed.

Lemma Rt_elimSEmpty {Δ k k' M e0} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] M @ k' ] -> [ G' ; Δ ⊢[ lC ] e0 : tySEmpty k @ k ] ->
  RT Δ M k' -> Rt Δ e0 (tySEmpty k) k -> Rt Δ (elimSEmpty k k' M e0) M k'.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros Hw Hw' HM He0 IHM IHe Hc0 ΔR kL kR TL TR c0' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc0) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  match goal with H : ty_leq M ?x |- _ => rename x into M' end.
  match goal with H : tm_leq e0 ?x |- _ => rename x into e0' end.
  destruct (scr_ty HM ltac:(eassumption) ltac:(eassumption)) as [HM' _].
  destruct (scr_tm He0 ltac:(eassumption) ltac:(eassumption)) as [He0' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  assert (HSE : [ G' ; Δ ⊢[ lD ] tySEmpty k ≅ tySEmpty k1 @ k ])
    by (apply eqty_sempty; [discriminate | exact HΔL | rewrite EL; exact Q]).
  refine (rec_t_elimSEmpty HΔL HΔ HkL HkR Hw Hw' _ _ _ _ HTL HTR HM HM' _ He0 He0' _ _ _); try eassumption.
  - exact (IHM HM _ _ _ _ HΔ (lequiv_refl _ _ Hw') Q' ltac:(eassumption) ltac:(eassumption)).
  - exact (IHe He0 _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HSE) HSE ltac:(eassumption) ltac:(eassumption)).
Qed.

(** The empty type and binary sums (M12c). *)
Lemma RT_empty {Δ k} : RT Δ (tyEmpty k) k.
Proof using EL ELM ELP EMl HMT HMT' Hbs Hbs' He Hl1 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VΓ.
  intros Hc ΔR kL kR c' HΔ HkL HkR E W. pose proof (sc_ctx HCD Hc) as HΔL.
  pose proof (lequiv_wf_l _ _ _ HkL) as Hw. leq_inv.
  exact (rec_T_empty HΔL HΔ HkL HkR Hw W E).
Qed.

Lemma Rt_codeempty {Δ j} : Rt Δ (tmEmpty j) (tyU j) (lsuc j).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. pose proof (sc_ctx_tm HCD Hc) as HΔL.
  pose proof (lequiv_wf_l _ _ _ HkL) as Hw; cbn in Hw. leq_inv.
  exact (rec_t_codeempty HΔL HΔ HkL HkR Hw W E HTL HTR).
Qed.

Lemma Rt_elimEmpty {Δ k k' M t} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ,, tyEmpty k' @ k' ⊢[ lC ] M @ k ] -> [ G' ; Δ ⊢[ lC ] t : tyEmpty k' @ k' ] ->
  RT (Δ ,, tyEmpty k' @ k') M k -> Rt Δ t (tyEmpty k') k' -> Rt Δ (elimEmpty k k' M t) (M[lsingle t]) k.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros Hw Hw' HM Ht IHM IHt Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  destruct (scr_ty HM ltac:(eassumption) ltac:(eassumption)) as [HM' _].
  destruct (scr_tm Ht ltac:(eassumption) ltac:(eassumption)) as [Ht' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  assert (HED : [ G' ; Δ ⊢[ lD ] tyEmpty k' @ k' ])
    by (apply wft_empty; [discriminate | exact HΔL | rewrite EL; exact Hw']).
  assert (HEE : [ G' ; Δ ⊢[ lD ] tyEmpty k' ≅ tyEmpty k1' @ k' ])
    by (apply eqty_empty; [discriminate | exact HΔL | rewrite EL; exact Q']).
  refine (rec_t_elimEmpty HΔL HΔ HkL HkR Hw Hw' _ _ _ _ HTL HTR HM HM' _ Ht Ht' _ _ _); try eassumption.
  - exact (IHM HM _ _ _ _ (ceq_ext HΔ HED HEE Q') (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - exact (IHt Ht _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw') Q' (eq_self_l HEE) HEE ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma RT_sum {Δ k k' A B} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ⊢[ lC ] B @ k' ] ->
  RT Δ A k -> RT Δ B k' -> RT Δ (tySum k k' A B) (lmax k k').
Proof using EL ELM ELP EMl HMT HMT' Hbs Hbs' He Hl1 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VΓ.
  intros Hw Hw' HA HB IHA IHB Hc ΔR kL kR c' HΔ HkL HkR E W. rewrite EL in Hw, Hw'.
  pose proof (sc_ctx HCD Hc) as HΔL. leq_inv.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' _].
  destruct (scr_ty HB ltac:(eassumption) ltac:(eassumption)) as [HB' _].
  refine (rec_T_sum HΔL HΔ HkL HkR Hw Hw' _ _ _ _ HA HB HA' HB' _ _ _ _); try eassumption.
  - refine (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) (lq Hw _ _) _ _); eassumption.
  - refine (IHB HB _ _ _ _ HΔ (lequiv_refl _ _ Hw') (lq Hw' _ _) _ _); eassumption.
Qed.

Lemma Rt_codesum {Δ k k' s t} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] -> [ G' ; Δ ⊢[ lC ] t : tyU k' @ lsuc k' ] ->
  Rt Δ s (tyU k) (lsuc k) -> Rt Δ t (tyU k') (lsuc k') ->
  Rt Δ (tmSum k k' s t) (tyU (lmax k k')) (lsuc (lmax k k')).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hw Hw' Hs Ht IHs IHt Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  destruct (scr_tm Hs ltac:(eassumption) ltac:(eassumption)) as [Hs' _].
  destruct (scr_tm Ht ltac:(eassumption) ltac:(eassumption)) as [Ht' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  refine (rec_t_codesum HΔL HΔ HkL HkR Hw Hw' _ _ _ _ HTL HTR Hs Hs' _ Ht Ht' _ _ _); try eassumption.
  - refine (IHs Hs _ _ _ _ _ _ HΔ (lequiv_refl L' (lsuc k) Hw) (lequiv_lsuc' _ _ _ Q) _ _ _ _); try eassumption.
    + apply eqty_refl, wft_U; [discriminate | exact HΔL | rewrite EL; exact Hw].
    + apply eqty_U; [discriminate | exact HΔL | rewrite EL; exact Q].
  - refine (IHt Ht _ _ _ _ _ _ HΔ (lequiv_refl L' (lsuc k') Hw') (lequiv_lsuc' _ _ _ Q') _ _ _ _); try eassumption.
    + apply eqty_refl, wft_U; [discriminate | exact HΔL | rewrite EL; exact Hw'].
    + apply eqty_U; [discriminate | exact HΔL | rewrite EL; exact Q'].
Qed.

Lemma Rt_inl {Δ k k' A B a} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ⊢[ lC ] B @ k' ] -> [ G' ; Δ ⊢[ lC ] a : A @ k ] ->
  RT Δ A k -> RT Δ B k' -> Rt Δ a A k -> Rt Δ (tmInl k k' A B a) (tySum k k' A B) (lmax k k').
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros Hw Hw' HA HB Ha IHA IHB IHa Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_ty HB ltac:(eassumption) ltac:(eassumption)) as [HB' _].
  destruct (scr_tm Ha ltac:(eassumption) ltac:(eassumption)) as [Ha' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  refine (rec_t_inl HΔL HΔ HkL HkR Hw Hw' _ _ _ _ HTL HTR HA HA' _ HB HB' _ Ha Ha' _ _ _ _); try eassumption.
  - exact (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - exact (IHB HB _ _ _ _ HΔ (lequiv_refl _ _ Hw') Q' ltac:(eassumption) ltac:(eassumption)).
  - exact (IHa Ha _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HAA) HAA ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma Rt_inr {Δ k k' A B b} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ⊢[ lC ] B @ k' ] -> [ G' ; Δ ⊢[ lC ] b : B @ k' ] ->
  RT Δ A k -> RT Δ B k' -> Rt Δ b B k' -> Rt Δ (tmInr k k' A B b) (tySum k k' A B) (lmax k k').
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros Hw Hw' HA HB Hb IHA IHB IHb Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' _].
  destruct (scr_ty HB ltac:(eassumption) ltac:(eassumption)) as [HB' HBB].
  destruct (scr_tm Hb ltac:(eassumption) ltac:(eassumption)) as [Hb' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  refine (rec_t_inr HΔL HΔ HkL HkR Hw Hw' _ _ _ _ HTL HTR HA HA' _ HB HB' _ Hb Hb' _ _ _ _); try eassumption.
  - exact (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - exact (IHB HB _ _ _ _ HΔ (lequiv_refl _ _ Hw') Q' ltac:(eassumption) ltac:(eassumption)).
  - exact (IHb Hb _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw') Q' (eq_self_l HBB) HBB ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma Rt_case {Δ k k' k'' A B M c1 c2 t} : lwf (gL G') k -> lwf (gL G') k' -> lwf (gL G') k'' ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ⊢[ lC ] B @ k' ] ->
  [ G' ; Δ ,, tySum k k' A B @ lmax k k' ⊢[ lC ] M @ k'' ] ->
  [ G' ; Δ ,, A @ k ⊢[ lC ] c1 : M⟨rlift ↑⟩[lsingle (tmInl k k' A⟨↑⟩ B⟨↑⟩ (var 0))] @ k'' ] ->
  [ G' ; Δ ,, B @ k' ⊢[ lC ] c2 : M⟨rlift ↑⟩[lsingle (tmInr k k' A⟨↑⟩ B⟨↑⟩ (var 0))] @ k'' ] ->
  [ G' ; Δ ⊢[ lC ] t : tySum k k' A B @ lmax k k' ] ->
  RT Δ A k -> RT Δ B k' -> RT (Δ ,, tySum k k' A B @ lmax k k') M k'' ->
  Rt (Δ ,, A @ k) c1 (M⟨rlift ↑⟩[lsingle (tmInl k k' A⟨↑⟩ B⟨↑⟩ (var 0))]) k'' ->
  Rt (Δ ,, B @ k') c2 (M⟨rlift ↑⟩[lsingle (tmInr k k' A⟨↑⟩ B⟨↑⟩ (var 0))]) k'' ->
  Rt Δ t (tySum k k' A B) (lmax k k') ->
  Rt Δ (tmCase k k' k'' A B M c1 c2 t) (M[lsingle t]) k''.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros Hw Hw' Hw'' HA HB HM Hc1 Hc2 Ht IHA IHB IHM IHc1 IHc2 IHt Hc0 ΔR kL kR TL TR c0' HΔ HkL HkR HTL HTR E W.
  rewrite EL in Hw, Hw', Hw''.
  pose proof (sc_ctx_tm HCD Hc0) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  match goal with H : leqv k'' ?x |- _ => rename x into k1'' end.
  match goal with H : ty_leq A ?x |- _ => rename x into A' end.
  match goal with H : ty_leq B ?x |- _ => rename x into B' end.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_ty HB ltac:(eassumption) ltac:(eassumption)) as [HB' HBB].
  destruct (scr_ty HM ltac:(eassumption) ltac:(eassumption)) as [HM' HMM].
  destruct (scr_tm Hc1 ltac:(eassumption) ltac:(eassumption)) as [Hc1' _].
  destruct (scr_tm Hc2 ltac:(eassumption) ltac:(eassumption)) as [Hc2' _].
  destruct (scr_tm Ht ltac:(eassumption) ltac:(eassumption)) as [Ht' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  assert (Q'' : lequiv L' k'' k1'') by (apply lq; assumption).
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q). assert (Qg' : lequiv (gL G') k' k1') by (rewrite EL; exact Q').
  assert (Qm : lequiv L' (lmax k k') (lmax k1 k1')) by (apply lequiv_max; assumption).
  assert (Hwm : lwf L' (lmax k k')) by (cbn; auto).
  pose proof (lift_ty HA HCD) as HAD. pose proof (lift_ty HB HCD) as HBD.
  assert (HSD : [ G' ; Δ ⊢[ lD ] tySum k k' A B @ lmax k k' ])
    by (apply wft_sum; [discriminate | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HAD | exact HBD]).
  assert (HSS : [ G' ; Δ ⊢[ lD ] tySum k k' A B ≅ tySum k1 k1' A' B' @ lmax k k' ])
    by (apply eqty_sum; [discriminate | exact Qg | exact Qg' | exact HAA | exact HBB]).
  destruct (case_facts_D Qg Qg' HAD HAA (lift_ty HA' HCD) HBD HBB (lift_ty HB' HCD) (lift_ty HM HCD) HMM (lift_ty HM' HCD))
    as (_ & CAf & CBf & EC1 & EC2).
  pose proof (ctxconv_eqty (eqctx_sym_D CAf) (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ EC1)) as HC1.
  pose proof (ctxconv_eqty (eqctx_sym_D CBf) (i := lD) eq_refl (eqty_sym _ _ _ _ _ _ EC2)) as HC2.
  refine (rec_t_case HΔL HΔ HkL HkR Hw Hw' Hw'' _ _ _ _ _ _ HTL HTR HA HA' _ HB HB' _ HM HM' _ Hc1 Hc1' _
            Hc2 Hc2' _ Ht Ht' _ _ _ _ _ _ _); try eassumption.
  - exact (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - exact (IHB HB _ _ _ _ HΔ (lequiv_refl _ _ Hw') Q' ltac:(eassumption) ltac:(eassumption)).
  - exact (IHM HM _ _ _ _ (ceq_ext HΔ HSD HSS Qm) (lequiv_refl _ _ Hw'') Q'' ltac:(eassumption) ltac:(eassumption)).
  - exact (IHc1 Hc1 _ _ _ _ _ _ (ceq_ext HΔ HAD HAA Q) (lequiv_refl _ _ Hw'') Q'' (eq_self_l HC1) HC1
             ltac:(eassumption) ltac:(eassumption)).
  - exact (IHc2 Hc2 _ _ _ _ _ _ (ceq_ext HΔ HBD HBB Q') (lequiv_refl _ _ Hw'') Q'' (eq_self_l HC2) HC2
             ltac:(eassumption) ltac:(eassumption)).
  - exact (IHt Ht _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hwm) Qm (eq_self_l HSS) HSS
             ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma Rt_sup {Δ k k' A B a f} : lwf (gL G') k -> lwf (gL G') k' ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ,, A @ k ⊢[ lC ] B @ k' ] -> [ G' ; Δ ⊢[ lC ] a : A @ k ] ->
  [ G' ; Δ ⊢[ lC ] f : tyPi k' (lmax k k') B[lsingle a] (tyW k k' A B)⟨↑⟩ @ lmax k' (lmax k k') ] ->
  RT Δ A k -> RT (Δ ,, A @ k) B k' -> Rt Δ a A k ->
  Rt Δ f (tyPi k' (lmax k k') B[lsingle a] (tyW k k' A B)⟨↑⟩) (lmax k' (lmax k k')) ->
  Rt Δ (tmSup k k' A B a f) (tyW k k' A B) (lmax k k').
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTr VMt VMtl VMtr VΓ.
  intros Hw Hw' HA HB Ha Hf IHA IHB IHa IHf Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw, Hw'.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  match goal with H : ty_leq A ?x |- _ => rename x into A' end.
  match goal with H : ty_leq B ?x |- _ => rename x into B' end.
  match goal with H : tm_leq a ?x |- _ => rename x into a' end.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_ty HB ltac:(eassumption) ltac:(eassumption)) as [HB' HBB].
  destruct (scr_tm Ha ltac:(eassumption) ltac:(eassumption)) as [Ha' Haa].
  destruct (scr_tm Hf ltac:(eassumption) ltac:(eassumption)) as [Hf' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q). assert (Qg' : lequiv (gL G') k' k1') by (rewrite EL; exact Q').
  assert (Qf : lequiv L' (lmax k' (lmax k k')) (lmax k1' (lmax k1 k1'))) by (repeat apply lequiv_max; assumption).
  assert (Hwf : lwf L' (lmax k' (lmax k k'))) by (cbn; auto).
  pose proof (@W_sup_feq G' lD eq_refl ltac:(discriminate) _ _ _ _ _ _ _ _ _ _ _ Qg Qg' (lift_ty HA HCD) HAA
                (lift_ty HB HCD) HBB Haa (lift_tm Ha HCD) (lift_tm Ha' HCD)) as X.
  refine (rec_t_sup HΔL HΔ HkL HkR Hw Hw' _ _ _ _ HTL HTR HA HA' _ HB HB' _ Ha Ha' _ Hf Hf' _ _ _ _ _);
    try eassumption.
  - exact (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - exact (IHB HB _ _ _ _ (ceq_ext HΔ (lift_ty HA HCD) HAA Q) (lequiv_refl _ _ Hw') Q'
             ltac:(eassumption) ltac:(eassumption)).
  - exact (IHa Ha _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q (eq_self_l HAA) HAA ltac:(eassumption) ltac:(eassumption)).
  - exact (IHf Hf _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hwf) Qf (eq_self_l X) X ltac:(eassumption) ltac:(eassumption)).
Qed.

Lemma Rt_elimW {Δ k k' k'' A B M c t} : lwf (gL G') k -> lwf (gL G') k' -> lwf (gL G') k'' ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ,, A @ k ⊢[ lC ] B @ k' ] ->
  [ G' ; Δ ,, tyW k k' A B @ lmax k k' ⊢[ lC ] M @ k'' ] ->
  [ G' ; Δ ,, A @ k ⊢[ lC ] wfty k k' A B @ lmax k' (lmax k k') ] ->
  [ G' ; Δ ,, A @ k ,, wfty k k' A B @ lmax k' (lmax k k') ⊢[ lC ] wihty k k' k'' A B M @ lmax k' k'' ] ->
  [ G' ; Δ ,, A @ k ,, wfty k k' A B @ lmax k' (lmax k k') ,, wihty k k' k'' A B M @ lmax k' k''
      ⊢[ lC ] c : wstepty k k' A B M @ k'' ] ->
  [ G' ; Δ ⊢[ lC ] t : tyW k k' A B @ lmax k k' ] ->
  RT Δ A k -> RT (Δ ,, A @ k) B k' -> RT (Δ ,, tyW k k' A B @ lmax k k') M k'' ->
  Rt (Δ ,, A @ k ,, wfty k k' A B @ lmax k' (lmax k k') ,, wihty k k' k'' A B M @ lmax k' k'')
    c (wstepty k k' A B M) k'' ->
  Rt Δ t (tyW k k' A B) (lmax k k') ->
  Rt Δ (tmElimW k k' k'' A B M c t) (M[lsingle t]) k''.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros Hw Hw' Hw'' HA HB HM HF HI Hc Ht IHA IHB IHM IHc IHt Hc0 ΔR kL kR TL TR c0' HΔ HkL HkR HTL HTR E W.
  rewrite EL in Hw, Hw', Hw''.
  pose proof (sc_ctx_tm HCD Hc0) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  match goal with H : leqv k' ?x |- _ => rename x into k1' end.
  match goal with H : leqv k'' ?x |- _ => rename x into k1'' end.
  match goal with H : ty_leq A ?x |- _ => rename x into A' end.
  match goal with H : ty_leq B ?x |- _ => rename x into B' end.
  match goal with H : ty_leq M ?x |- _ => rename x into M' end.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' HAA].
  destruct (scr_ty HB ltac:(eassumption) ltac:(eassumption)) as [HB' HBB].
  destruct (scr_ty HM ltac:(eassumption) ltac:(eassumption)) as [HM' HMM].
  destruct (scr_tm Hc ltac:(eassumption) ltac:(eassumption)) as [Hc' _].
  destruct (scr_tm Ht ltac:(eassumption) ltac:(eassumption)) as [Ht' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption). assert (Q' : lequiv L' k' k1') by (apply lq; assumption).
  assert (Q'' : lequiv L' k'' k1'') by (apply lq; assumption).
  assert (Qg : lequiv (gL G') k k1) by (rewrite EL; exact Q). assert (Qg' : lequiv (gL G') k' k1') by (rewrite EL; exact Q').
  assert (Qg'' : lequiv (gL G') k'' k1'') by (rewrite EL; exact Q'').
  assert (Qm : lequiv L' (lmax k k') (lmax k1 k1')) by (apply lequiv_max; assumption).
  assert (Hwm : lwf L' (lmax k k')) by (cbn; auto).
  pose proof (lift_ty HA HCD) as HAD. pose proof (lift_ty HB HCD) as HBD.
  assert (HWD : [ G' ; Δ ⊢[ lD ] tyW k k' A B @ lmax k k' ])
    by (apply wft_W; [discriminate | rewrite EL; exact Hw | rewrite EL; exact Hw' | exact HAD | exact HBD]).
  assert (HWW : [ G' ; Δ ⊢[ lD ] tyW k k' A B ≅ tyW k1 k1' A' B' @ lmax k k' ])
    by (apply eqty_W; [discriminate | exact Qg | exact Qg' | exact HAD | exact HAA | exact HBB]).
  destruct (@W_facts G' lD eq_refl ltac:(discriminate) _ _ _ _ _ _ _ _ _ _ _ _ _ Qg Qg' Qg''
              HAA HAD (lift_ty HA' HCD) HBB HBD (lift_ty HB' HCD) HMM (lift_ty HM HCD) (lift_ty HM' HCD)
              (lift_ty HF HCD) (lift_ty HI HCD)) as (_ & _ & CS1L & ES1).
  destruct (eqc_ext_inv CS1L) as (CS1a & _ & EI1 & QI1). destruct (eqc_ext_inv CS1a) as (_ & _ & EF1 & QF1).
  assert (CS1 : [ G' ⊢[ lD ] Δ ,, A @ k ,, wfty k k' A B @ lmax k' (lmax k k') ,, wihty k k' k'' A B M @ lmax k' k''
                  ≅ ΔR ,, A' @ k1 ,, wfty k1 k1' A' B' @ lmax k1' (lmax k1 k1') ,, wihty k1 k1' k1'' A' B' M' @ lmax k1' k1'' ])
    by (apply eqc_ext; [apply eqc_ext; [exact (ceq_ext HΔ HAD HAA Q) | exact (lift_ty HF HCD) | exact EF1 | exact QF1]
                       | exact (lift_ty HI HCD) | exact EI1 | exact QI1]).
  refine (rec_t_elimW HΔL HΔ HkL HkR Hw Hw' Hw'' _ _ _ _ _ _ HTL HTR HA HA' _ HB HB' _ HM HM' _ HF HI Hc Hc' _
            Ht Ht' _ _ _ _ _ _); try eassumption.
  - exact (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) Q ltac:(eassumption) ltac:(eassumption)).
  - exact (IHB HB _ _ _ _ (ceq_ext HΔ HAD HAA Q) (lequiv_refl _ _ Hw') Q' ltac:(eassumption) ltac:(eassumption)).
  - exact (IHM HM _ _ _ _ (ceq_ext HΔ HWD HWW Qm) (lequiv_refl _ _ Hw'') Q'' ltac:(eassumption) ltac:(eassumption)).
  - exact (IHc Hc _ _ _ _ _ _ CS1 (lequiv_refl _ _ Hw'') Q'' (eq_self_l ES1) ES1 ltac:(eassumption) ltac:(eassumption)).
  - exact (IHt Ht _ _ _ _ _ _ HΔ (lequiv_refl _ _ Hwm) Qm (eq_self_l HWW) HWW ltac:(eassumption) ltac:(eassumption)).
Qed.

(** Length-indexed tuples and finite indices, with their codes (M14b). *)
Lemma RT_vec {Δ k A n} : lwf (gL G') k ->
  [ G' ; Δ ⊢[ lC ] A @ k ] -> [ G' ; Δ ⊢[ lC ] n : tyNat @ lzero ] ->
  RT Δ A k -> Rt Δ n tyNat lzero -> RT Δ (tyVec k A n) k.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros Hw HA Hn IHA IHn Hc ΔR kL kR c' HΔ HkL HkR E W. rewrite EL in Hw.
  pose proof (sc_ctx HCD Hc) as HΔL. leq_inv.
  destruct (scr_ty HA ltac:(eassumption) ltac:(eassumption)) as [HA' _].
  destruct (scr_tm Hn ltac:(eassumption) ltac:(eassumption)) as [Hn' _].
  assert (HN : [ G' ; Δ ⊢[ lD ] tyNat ≅ tyNat @ lzero ]) by (apply eqty_refl, wft_nat; [discriminate | exact HΔL]).
  refine (rec_T_vec HΔL HΔ HkL HkR Hw _ _ HA HA' _ Hn Hn' _ _ _); try eassumption.
  - refine (IHA HA _ _ _ _ HΔ (lequiv_refl _ _ Hw) (lq Hw _ _) _ _); eassumption.
  - refine (IHn Hn _ _ _ _ _ _ HΔ (lequiv_refl L' lzero I) (lequiv_refl L' lzero I) HN HN _ _); eassumption.
Qed.

Lemma Rt_codevec {Δ k s n} : lwf (gL G') k ->
  [ G' ; Δ ⊢[ lC ] s : tyU k @ lsuc k ] -> [ G' ; Δ ⊢[ lC ] n : tyNat @ lzero ] ->
  Rt Δ s (tyU k) (lsuc k) -> Rt Δ n tyNat lzero -> Rt Δ (tmVec k s n) (tyU k) (lsuc k).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hw Hs Hn IHs IHn Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. rewrite EL in Hw.
  pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  match goal with H : leqv k ?x |- _ => rename x into k1 end.
  destruct (scr_tm Hs ltac:(eassumption) ltac:(eassumption)) as [Hs' _].
  destruct (scr_tm Hn ltac:(eassumption) ltac:(eassumption)) as [Hn' _].
  assert (Q : lequiv L' k k1) by (apply lq; assumption).
  assert (HN : [ G' ; Δ ⊢[ lD ] tyNat ≅ tyNat @ lzero ]) by (apply eqty_refl, wft_nat; [discriminate | exact HΔL]).
  refine (rec_t_codevec HΔL HΔ HkL HkR Hw _ _ HTL HTR Hs Hs' _ Hn Hn' _ _ _); try eassumption.
  - refine (IHs Hs _ _ _ _ _ _ HΔ (lequiv_refl L' (lsuc k) Hw) (lequiv_lsuc' _ _ _ Q) _ _ _ _); try eassumption.
    + apply eqty_refl, wft_U; [discriminate | exact HΔL | rewrite EL; exact Hw].
    + apply eqty_U; [discriminate | exact HΔL | rewrite EL; exact Q].
  - refine (IHn Hn _ _ _ _ _ _ HΔ (lequiv_refl L' lzero I) (lequiv_refl L' lzero I) HN HN _ _); eassumption.
Qed.

Lemma RT_fin {Δ n} : [ G' ; Δ ⊢[ lC ] n : tyNat @ lzero ] -> Rt Δ n tyNat lzero -> RT Δ (tyFin n) lzero.
Proof using EL ELM ELP EMl HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ.
  intros Hn IHn Hc ΔR kL kR c' HΔ HkL HkR E W. pose proof (sc_ctx HCD Hc) as HΔL. leq_inv.
  destruct (scr_tm Hn E W) as [Hn' _].
  refine (rec_T_fin HΔL HΔ HkL HkR Hn Hn' E _).
  assert (HN : [ G' ; Δ ⊢[ lD ] tyNat ≅ tyNat @ lzero ]) by (apply eqty_refl, wft_nat; [discriminate | exact HΔL]).
  exact (IHn Hn _ _ _ _ _ _ HΔ (lequiv_refl L' lzero I) (lequiv_refl L' lzero I) HN HN E W).
Qed.

Lemma Rt_codefin {Δ n} : [ G' ; Δ ⊢[ lC ] n : tyNat @ lzero ] -> Rt Δ n tyNat lzero ->
  Rt Δ (tmFin n) (tyU lzero) (lsuc lzero).
Proof using EL ELM ELP EMl HMt HMt' Hbs Hbs' He Hl2 HrbL HrbR Hσ Hφ VBr VBr' VMt VMtl VMtr VΓ.
  intros Hn IHn Hc ΔR kL kR TL TR c' HΔ HkL HkR HTL HTR E W. pose proof (sc_ctx_tm HCD Hc) as HΔL. leq_inv.
  destruct (scr_tm Hn E W) as [Hn' _].
  refine (rec_t_codefin HΔL HΔ HkL HkR HTL HTR Hn Hn' E _).
  assert (HN : [ G' ; Δ ⊢[ lD ] tyNat ≅ tyNat @ lzero ]) by (apply eqty_refl, wft_nat; [discriminate | exact HΔL]).
  exact (IHn Hn _ _ _ _ _ _ HΔ (lequiv_refl L' lzero I) (lequiv_refl L' lzero I) HN HN E W).
Qed.

Theorem rec_code :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> True) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> i = lC -> G = G' -> RT Γ T l) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> i = lC -> G = G' -> Rt Γ t T l) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> True) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> True) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> True).
Proof using EL ELM ELP EMl HG0 HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR HΓ0 Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ VΓT VΓbr VΓt.
  apply typing_mut; intros.
  par: (
    (try exact I;
    (* the rules at M do not type code *)
    match goal with Ei : ?i = lC, EG : ?G = G' |- _ => first [discriminate Ei | subst i G] end;
    repeat match goal with IH : lC = lC -> G' = G' -> _ |- _ => specialize (IH eq_refl eq_refl) end;
    cbn [typeof] in *;
    (* the rules of the computing layers do not type code (M8_DESIGN.md I1) *)
    try match goal with c : compt lC |- _ => destruct c; discriminate end);
    (first
    [ solve [apply RT_nat | apply RT_U | apply RT_gvar | apply Rt_nat | apply Rt_zero | apply Rt_U | apply Rt_gvar | apply Rt_gdef]
    | solve [eapply Rt_var; eassumption]
    | solve [eapply RT_pi; eassumption] | solve [eapply RT_El; eassumption] | solve [eapply RT_lconv; eassumption]
    | solve [eapply Rt_succ; eassumption] | solve [eapply Rt_pi; eassumption] | solve [eapply Rt_natrec; eassumption]
    | solve [eapply Rt_lam; eassumption] | solve [eapply Rt_app; eassumption]
    | solve [eapply Rt_conv; eassumption] | solve [eapply Rt_lconv; eassumption]
    | solve [apply RT_unit | apply Rt_codeunit | apply Rt_triv]
    | solve [eapply RT_sig; eassumption] | solve [eapply Rt_codesig; eassumption] | solve [eapply Rt_pair; eassumption]
    | solve [eapply Rt_fst; eassumption] | solve [eapply Rt_snd; eassumption]
    | solve [eapply RT_id; eassumption] | solve [eapply Rt_codeid; eassumption]
    | solve [eapply Rt_refl; eassumption] | solve [eapply Rt_J; eassumption]
    (* strict equality (M10c) *)
    | solve [eapply RT_seq; eassumption] | solve [eapply Rt_codeseq; eassumption]
    | solve [eapply Rt_srefl; eassumption] | solve [apply RT_sempty | apply Rt_codesempty]
    | solve [eapply Rt_elimSEmpty; eassumption]
    (* the empty type and binary sums (M12c) *)
    | solve [apply RT_empty | apply Rt_codeempty] | solve [eapply Rt_elimEmpty; eassumption]
    | solve [eapply RT_sum; eassumption] | solve [eapply Rt_codesum; eassumption]
    | solve [eapply Rt_inl; eassumption] | solve [eapply Rt_inr; eassumption]
    | solve [eapply Rt_case; eassumption]
    (* well-founded trees (M13b) *)
    | solve [eapply RT_W; eassumption] | solve [eapply Rt_codeW; eassumption]
    | solve [eapply Rt_sup; eassumption] | solve [eapply Rt_elimW; eassumption]
    (* length-indexed tuples and finite indices (M14b) *)
    | solve [eapply RT_vec; eassumption] | solve [eapply Rt_codevec; eassumption]
    | solve [eapply RT_fin; eassumption] | solve [eapply Rt_codefin; eassumption]
    (* finitary well-founded trees (M15b) *)
    | solve [eapply RT_wf; eassumption] | solve [eapply Rt_codewf; eassumption]
    | solve [eapply Rt_supf; eassumption] | solve [eapply Rt_elimWf; eassumption]
    (* propositional truncation (M16b) *)
    | solve [eapply RT_sq; eassumption] | solve [eapply Rt_codesq; eassumption]
    | solve [eapply Rt_sq; eassumption] | solve [eapply Rt_elimSq; eassumption]
    (* dependent tuples and indexed trees (M17c) *)
    | solve [eapply RT_dvec; eassumption] | solve [eapply Rt_codedvec; eassumption]
    | solve [eapply RT_iwf; eassumption] | solve [eapply Rt_codeiwf; eassumption]
    | solve [eapply Rt_supi; eassumption] | solve [eapply Rt_elimIWf; eassumption]
    (* indexed infinitary trees (M19c) *)
    | solve [eapply RT_iwi; eassumption] | solve [eapply Rt_codeiwi; eassumption]
    | solve [eapply Rt_supii; eassumption] | solve [eapply Rt_elimIWi; eassumption] ])).
Qed.

(** The recursion lemmas, for a code typed at C in the left context. *)
Lemma rec_T {ΔL ΔR kL kR k c c'} : [ G' ; ΔL ⊢[ lC ] c @ k ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k kL -> lequiv L' k kR -> ty_leq c c' -> ty_lwf L' c' ->
  LRtmM (lvsubst l1 φ) G' Θ (motT (wrapMT MTL) kL ΔL (boxT c)) (motT (wrapMT MTR) kR ΔR (boxT c'))
    (recTL kL ΔL c) (recTR kR ΔR c').
Proof using EL ELM ELP EMl HG0 HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR HΓ0 Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ VΓT VΓbr VΓt. intros Hc. exact (proj1 (proj2 (proj2 rec_code)) _ _ _ _ _ Hc eq_refl eq_refl Hc ΔR kL kR c'). Qed.

Lemma rec_t {ΔL ΔR kL kR k T TL TR c c'} : [ G' ; ΔL ⊢[ lC ] c : T @ k ] -> [ G' ⊢[ lD ] ΔL ≅ ΔR ] ->
  lequiv L' k kL -> lequiv L' k kR -> [ G' ; ΔL ⊢[ lD ] T ≅ TL @ k ] -> [ G' ; ΔL ⊢[ lD ] T ≅ TR @ k ] ->
  tm_leq c c' -> tm_lwf L' c' ->
  LRtmM (lvsubst l2 φ) G' Θ (mott (wrapMt MtL) kL ΔL TL (boxt c)) (mott (wrapMt MtR) kR ΔR TR (boxt c'))
    (rectL kL ΔL TL c) (rectR kR ΔR TR c').
Proof using EL ELM ELP EMl HG0 HMT HMT' HMt HMt' Hbs Hbs' He Hl1 Hl2 HrbL HrbR HΓ0 Hσ Hφ VBr VBr' VMT VMTl VMTr VMt VMtl VMtr VΓ VΓT VΓbr VΓt. intros Hc. exact (proj1 (proj2 (proj2 (proj2 rec_code))) _ _ _ _ _ _ Hc eq_refl eq_refl Hc ΔR kL kR TL TR c'). Qed.

End Rec.
