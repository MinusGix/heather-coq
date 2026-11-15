(** * [RulesS]: [IWi]'s eliminator (M19b). Each lifting pushes the
    substitution through [IWi]'s premises, so they build beside the other
    rules, as [IWf]'s do ([RulesSIWf]). *)
From DeLaM.Validity Require Export RulesSBase.

#[local] Existing Instance LR_P.

Section RulesS.
Context (EP EM : GenericEq) {ELP : @GenericEqLaws EP} {ELM : @GenericEqLaws EM}.

Local Notation GSubRel := (GSubRel EP EM).
Local Notation GValid := (GValid EP EM).

Section Rules.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

Local Notation VCtxS := (@VCtxS EP EM E LP).
Local Notation VTyS := (@VTyS EP EM E LP).
Local Notation VTmS := (@VTmS EP EM E LP).

Lemma VS_elimIWi {ly G Γ l lp li l' l3 lp3 li3 l4 X X' A A' N N' D D' Ot Ot' C C' M M' c c' m m' t t'} :
  lwf (gL G) l -> lwf (gL G) lp -> lwf (gL G) li -> lwf (gL G) l' ->
  lequiv (gL G) l l3 -> lequiv (gL G) lp lp3 -> lequiv (gL G) li li3 -> lequiv (gL G) l' l4 ->
  [ G ; Γ ⊢[ ly ] X @ li ] -> [ G ; Γ ⊢[ ly ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ ly ] N : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ ly ] D @ lp ] -> [ G ; Γ ,, A @ l ⊢[ ly ] Ot : X⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp ⊢[ ly ] C : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ X X' li -> VTyS G Γ A A' l -> VTmS G (Γ ,, A @ l) N N' tyNat lzero ->
  VTyS G (Γ ,, A @ l ,, tyFin N @ lzero) D D' lp ->
  VTmS G (Γ ,, A @ l) Ot Ot' X⟨↑⟩ li -> VTmS G (Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp) C C' X⟨↑⟩⟨↑⟩⟨↑⟩ li ->
  VTyS G (Γ ,, X @ li) (iwimotty l lp li X A N D Ot C) (iwimotty l lp li X A N D Ot C) (iwiL l lp li) ->
  VTyS G (Γ ,, X @ li ,, iwimotty l lp li X A N D Ot C @ (iwiL l lp li)) M M' l' ->
  VTyS G (Γ ,, A @ l) (iwicsty l lp li X A N D Ot C) (iwicsty l lp li X A N D Ot C) (iwiL l lp li) ->
  VTyS G (Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ (iwiL l lp li))
    (iwiihty l lp li l' X A N D Ot C M) (iwiihty l3 lp3 li3 l4 X' A' N' D' Ot' C' M') (lmax lzero (lmax lp l')) ->
  VTmS G (Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ (iwiL l lp li)
            ,, iwiihty l lp li l' X A N D Ot C M @ lmax lzero (lmax lp l'))
    c c' (iwistepty l lp li X A N D Ot C M) l' ->
  VTmS G Γ m m' X li -> VTmS G Γ t t' (tyIWi l lp li X A N D Ot C m) (iwiL l lp li) ->
  VTmS G Γ (tmElimIWi l lp li l' X A N D Ot C M c m t) (tmElimIWi l3 lp3 li3 l4 X' A' N' D' Ot' C' M' c' m' t')
    M[lsingle2 m t] l'.
Proof using EL VL VN. intros; s_lift. Qed.
End Rules.

End RulesS.
