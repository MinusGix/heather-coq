(** * The typed step scope of [elim_Wf]'s recursor branch (M15b)

    Branch 50's scope ([Γ, a, cs, ih] with the step type) is typed by
    [RecWf]'s automation; each typing retypes the [ih] entry, [nth]
    included. Proved here once, for any global context of the branch's
    shape, rather than in each proof that walks the branches
    ([brΓ_conv] in AlgPrereq paid 22 s for it on the build's critical
    path). *)
From DeLaM.Typing Require Export Inversion.

Lemma br50_scope G0 : [ ⊢ brG 50 G0 ] ->
  [ brG 50 G0 ; cvar 5 ,, gv 4 @ lvar 1 ,, wfcsty (lvar 1) (gv 4) (gu 3) @ lvar 1
      ,, wfihty (lvar 1) (lvar 0) (gv 4) (gu 3) (gv 2) @ lmax lzero (lvar 0) ⊢[ lD ] ] /\
  [ brG 50 G0 ; cvar 5 ,, gv 4 @ lvar 1 ,, wfcsty (lvar 1) (gv 4) (gu 3) @ lvar 1
      ,, wfihty (lvar 1) (lvar 0) (gv 4) (gu 3) (gv 2) @ lmax lzero (lvar 0)
      ⊢[ lD ] wfstepty (lvar 1) (gv 4) (gu 3) (gv 2) @ lvar 0 ] /\
  [ brG 50 G0 ; cvar 5 ,, gv 4 @ lvar 1 ,, wfcsty (lvar 1) (gv 4) (gu 3) @ lvar 1
      ,, wfihty (lvar 1) (lvar 0) (gv 4) (gu 3) (gv 2) @ lmax lzero (lvar 0)
      ⊢[ lC ] gu 1 : wfstepty (lvar 1) (gv 4) (gu 3) (gv 2) @ lvar 0 ] /\
  [ brG 50 G0 ; cvar 5 ⊢[ lC ] tmElimWf (lvar 1) (lvar 0) (gv 4) (gu 3) (gv 2) (gu 1) (gu 0)
      : tyGvar 2 (lsingle (gu 0)) @ lvar 0 ].
Proof.
  intros HG0. w_lookups 50 (gΨ (brG 50 G0)).
  repeat split; unfold gv, gu; wnorm; wtop.
Qed.
