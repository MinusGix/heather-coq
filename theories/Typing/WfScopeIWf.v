(** * The head of [elim_IWf]'s recursor branch (M17c)

    [br60_scope] (WfScope) types the branch's step scope; the eliminator
    itself, at the scope's global context, is typed here, from the
    generic typings of [IWfIHG], for the proofs walking the branches
    ([brRes_wf] in RecAdm, [brΓ_conv] in AlgPrereq). *)
From DeLaM.Typing Require Export WfScope IWfIHG.

(** The head of [elim_IWf]'s branch, typed at C: by the generic typings of
    the motive, the children's tuple and the induction hypothesis
    (IWfIHG), which [RecWf]'s automation does not find on its own. *)
Lemma br60_head G0 : [ ⊢ brG 60 G0 ] ->
  [ brG 60 G0 ; cvar 9 ⊢[ lC ] tmElimIWf (lvar 2) (lvar 1) (lvar 0) (gv 8) (gv 7) (gu 6) (gu 5) (gu 4) (gv 3)
      (gu 2) (gu 1) (gu 0) : tyGvar 3 (lsingle2 (gu 1) (gu 0)) @ lvar 0 ].
Proof.
  intros HG0. destruct (br60_scope G0 HG0) as (_ & _ & Hc).
  w_lookups 60 (gΨ (brG 60 G0)).
  assert (HS : @IWfSig (brG 60 G0) lC (cvar 9) (lvar 2) (lvar 1) (gv 8) (gv 7) (gu 6) (gu 5) (gu 4))
    by (unfold IWfSig; repeat split; [lvl_ok | lvl_ok | ..]; unfold gv, gu; wnorm; wtop).
  pose proof HS as (Wl & Wli & HX & HA & HN & HO & HC).
  assert (Wl' : lwf (gL (brG 60 G0)) (lvar 0)) by lvl_ok.
  assert (HM : [ brG 60 G0 ; cvar 9 ,, gv 8 @ lvar 1
                 ,, iwfmotty (lvar 2) (lvar 1) (gv 8) (gv 7) (gu 6) (gu 5) (gu 4) @ lmax (lvar 2) (lvar 1)
                 ⊢[ lC ] gv 3 @ lvar 0 ])
    by (unfold gv, gu; wnorm; wtop).
  eapply wf_elimIWf_eq;
    [ unfold gv, gu; wnorm; reflexivity | discriminate | exact Wl | exact Wli | exact Wl'
    | exact HX | exact HA | exact HN | exact HO | exact HC
    | exact (IWf_mot_wf_g (i := lC) ltac:(discriminate) Wl Wli HX HA HN HO HC) | exact HM
    | exact (IWf_cs_wf_g (i := lC) ltac:(discriminate) Wl Wli HX HA HN HO HC)
    | exact (IWf_ihty_wf_g (i := lC) ltac:(discriminate) HS Wl' HM) | exact Hc | | ].
  all: unfold gv, gu; wnorm; wtop.
Qed.

