(** * The head of [elim_IWi]'s recursor branch (M19c)

    As [WfScopeIWf] for [IWf]: [br64_scope] (WfScope) types the branch's
    step scope; the eliminator itself, at the scope's global context, is
    typed here, from the generic typings of [IWiIHG], for the proofs
    walking the branches ([brRes_wf] in RecAdm, [brΓ_conv] in AlgPrereq). *)
From DeLaM.Typing Require Export WfScope IWiIHG.

Lemma wf_elimIWi_eq G i Γ l lp li l' X A N D Ot C M c m t T : M[lsingle2 m t] = T -> i <> lV ->
  lwf (gL G) l -> lwf (gL G) lp -> lwf (gL G) li -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ i ] X @ li ] -> [ G ; Γ ⊢[ i ] A @ l ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] D @ lp ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] Ot : X⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp ⊢[ i ] C : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] ->
  [ G ; Γ ,, X @ li ⊢[ i ] iwimotty l lp li X A N D Ot C @ iwiL l lp li ] ->
  [ G ; Γ ,, X @ li ,, iwimotty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] iwicsty l lp li X A N D Ot C @ iwiL l lp li ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ⊢[ i ] iwiihty l lp li l' X A N D Ot C M @ lmax lzero (lmax lp l') ] ->
  [ G ; Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li ,, iwiihty l lp li l' X A N D Ot C M @ lmax lzero (lmax lp l') ⊢[ i ] c : iwistepty l lp li X A N D Ot C M @ l' ] ->
  [ G ; Γ ⊢[ i ] m : X @ li ] -> [ G ; Γ ⊢[ i ] t : tyIWi l lp li X A N D Ot C m @ iwiL l lp li ] ->
  [ G ; Γ ⊢[ i ] tmElimIWi l lp li l' X A N D Ot C M c m t : T @ l' ].
Proof. intros <-; apply wf_elimIWi. Qed.

(** The head of [elim_IWi]'s branch, typed at C, as [br60_head]. *)
Lemma br64_head G0 : [ ⊢ brG 64 G0 ] ->
  [ brG 64 G0 ; cvar 10 ⊢[ lC ] tmElimIWi (lvar 3) (lvar 2) (lvar 1) (lvar 0) (gv 9) (gv 8) (gu 7) (gv 6)
      (gu 5) (gu 4) (gv 3) (gu 2) (gu 1) (gu 0) : tyGvar 3 (lsingle2 (gu 1) (gu 0)) @ lvar 0 ].
Proof.
  intros HG0. destruct (br64_scope G0 HG0) as (_ & _ & Hc).
  w_lookups 64 (gΨ (brG 64 G0)).
  assert (HS : @IWiSig (brG 64 G0) lC (cvar 10) (lvar 3) (lvar 2) (lvar 1) (gv 9) (gv 8) (gu 7) (gv 6) (gu 5) (gu 4))
    by (unfold IWiSig; repeat split; [lvl_ok | lvl_ok | lvl_ok | ..]; unfold gv, gu; wnorm; wtop).
  pose proof HS as (Wl & Wlp & Wli & HX & HA & HN & HD & HO & HC).
  assert (Wl' : lwf (gL (brG 64 G0)) (lvar 0)) by lvl_ok.
  assert (HM : [ brG 64 G0 ; cvar 10 ,, gv 9 @ lvar 1
                 ,, iwimotty (lvar 3) (lvar 2) (lvar 1) (gv 9) (gv 8) (gu 7) (gv 6) (gu 5) (gu 4)
                    @ iwiL (lvar 3) (lvar 2) (lvar 1)
                 ⊢[ lC ] gv 3 @ lvar 0 ])
    by (unfold gv, gu; wnorm; wtop).
  eapply wf_elimIWi_eq;
    [ unfold gv, gu; wnorm; reflexivity | discriminate | exact Wl | exact Wlp | exact Wli | exact Wl'
    | exact HX | exact HA | exact HN | exact HD | exact HO | exact HC
    | exact (IWi_mot_wf_g (i := lC) ltac:(discriminate) Wl Wlp Wli HX HA HN HD HO HC) | exact HM
    | exact (IWi_cs_wf_g (i := lC) ltac:(discriminate) Wl Wlp Wli HX HA HN HD HO HC)
    | exact (IWi_ihty_wf_g (i := lC) ltac:(discriminate) HS Wl' HM) | exact Hc | | ].
  all: unfold gv, gu; wnorm; wtop.
Qed.
