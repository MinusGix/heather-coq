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

(** [elim_IWf]'s branch (M17c), as [elim_Wf]'s: its step scope
    ([Γ, a, cs, ih] with the step type) carries [dnth] in the induction
    hypothesis's type, whose typing by [RecWf]'s automation is the
    costliest of the branches'. Here it is not redone: the step's
    declaration is well-formed in the branch's global context
    ([gctx_decl_ok]), which gives the scope at once (at D; its C typings,
    and the head's, are [AlgPrereq.br60_head]'s, from [IWfIHG]). *)
Lemma wfc_ext_inv {G i Γ A l} : [ G ; Γ ,, A @ l ⊢[ i ] ] ->
  [ G ; Γ ⊢[ i ] ] /\ [ G ; Γ ⊢[ i ] A @ l ] /\ lwf (gL G) l.
Proof. intros H; inversion H; subst; auto. Qed.

Lemma wf_elimIWf_eq G i Γ l li l' X A N Ot C M c m t T : M[lsingle2 m t] = T -> i <> lV ->
  lwf (gL G) l -> lwf (gL G) li -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ i ] X @ li ] -> [ G ; Γ ⊢[ i ] A @ l ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] -> [ G ; Γ ,, A @ l ⊢[ i ] Ot : X⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ i ] C : X⟨↑⟩⟨↑⟩ @ li ] ->
  [ G ; Γ ,, X @ li ⊢[ i ] iwfmotty l li X A N Ot C @ lmax l li ] ->
  [ G ; Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li ⊢[ i ] M @ l' ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] iwfcsty l li X A N Ot C @ lmax l li ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ⊢[ i ] iwfihty l li l' X A N Ot C M @ lmax lzero l' ] ->
  [ G ; Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ,, iwfihty l li l' X A N Ot C M @ lmax lzero l'
      ⊢[ i ] c : iwfstepty l li X A N Ot C M @ l' ] ->
  [ G ; Γ ⊢[ i ] m : X @ li ] -> [ G ; Γ ⊢[ i ] t : tyIWf l li X A N Ot C m @ lmax l li ] ->
  [ G ; Γ ⊢[ i ] tmElimIWf l li l' X A N Ot C M c m t : T @ l' ].
Proof. intros <-; apply wf_elimIWf. Qed.

Lemma br60_scope G0 : [ ⊢ brG 60 G0 ] ->
  [ brG 60 G0 ; cvar 9 ,, gv 7 @ lvar 2
      ,, iwfcsty (lvar 2) (lvar 1) (gv 8) (gv 7) (gu 6) (gu 5) (gu 4) @ lmax (lvar 2) (lvar 1)
      ,, iwfihty (lvar 2) (lvar 1) (lvar 0) (gv 8) (gv 7) (gu 6) (gu 5) (gu 4) (gv 3) @ lmax lzero (lvar 0)
      ⊢[ lD ] ] /\
  [ brG 60 G0 ; cvar 9 ,, gv 7 @ lvar 2
      ,, iwfcsty (lvar 2) (lvar 1) (gv 8) (gv 7) (gu 6) (gu 5) (gu 4) @ lmax (lvar 2) (lvar 1)
      ,, iwfihty (lvar 2) (lvar 1) (lvar 0) (gv 8) (gv 7) (gu 6) (gu 5) (gu 4) (gv 3) @ lmax lzero (lvar 0)
      ⊢[ lD ] iwfstepty (lvar 2) (lvar 1) (gv 8) (gv 7) (gu 6) (gu 5) (gu 4) (gv 3) @ lvar 0 ] /\
  [ brG 60 G0 ; cvar 9 ,, gv 7 @ lvar 2
      ,, iwfcsty (lvar 2) (lvar 1) (gv 8) (gv 7) (gu 6) (gu 5) (gu 4) @ lmax (lvar 2) (lvar 1)
      ,, iwfihty (lvar 2) (lvar 1) (lvar 0) (gv 8) (gv 7) (gu 6) (gu 5) (gu 4) (gv 3) @ lmax lzero (lvar 0)
      ⊢[ lC ] gu 2 : iwfstepty (lvar 2) (lvar 1) (gv 8) (gv 7) (gu 6) (gu 5) (gu 4) (gv 3) @ lvar 0 ].
Proof.
  intros HG0.
  pose proof (gctx_decl_ok _ _ _ HG0 (in_gctx_nth (gΨ (brG 60 G0)) 2 _ eq_refl)) as Hok.
  destruct Hok as (HC & HS & _).
  match type of HS with [ _ ; ?D ⊢[ _ ] ?T @ _ ] =>
    change D with (cvar 9 ,, gv 7 @ lvar 2
      ,, iwfcsty (lvar 2) (lvar 1) (gv 8) (gv 7) (gu 6) (gu 5) (gu 4) @ lmax (lvar 2) (lvar 1)
      ,, iwfihty (lvar 2) (lvar 1) (lvar 0) (gv 8) (gv 7) (gu 6) (gu 5) (gu 4) (gv 3) @ lmax lzero (lvar 0)) in HC, HS;
    change T with (iwfstepty (lvar 2) (lvar 1) (gv 8) (gv 7) (gu 6) (gu 5) (gu 4) (gv 3)) in HS end.
  refine (conj HC (conj HS _)).
  w_lookups 60 (gΨ (brG 60 G0)). unfold gu.
  eapply wf_gu; [ exact HC | glookup | unfold lle; cbn; lia | cbn; intuition congruence ].
Qed.
