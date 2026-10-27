(** * [RulesS]: [IWf]'s eliminator and its type (M17b). Each lifting
    pushes the substitution through [IWf]'s premises, a third of
    [RulesS]'s time, so they build beside the other rules. *)
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

Lemma VS_elimIWf {ly G Γ l li l' l3 li3 l4 X X' A A' N N' Ot Ot' C C' M M' c c' m m' t t'} :
  lwf (gL G) l -> lwf (gL G) li -> lwf (gL G) l' ->
  lequiv (gL G) l l3 -> lequiv (gL G) li li3 -> lequiv (gL G) l' l4 ->
  [ G ; Γ ⊢[ ly ] X @ li ] -> [ G ; Γ ⊢[ ly ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ ly ] N : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ⊢[ ly ] Ot : X⟨↑⟩ @ li ] -> [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ ly ] C : X⟨↑⟩⟨↑⟩ @ li ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ X X' li -> VTyS G Γ A A' l -> VTmS G (Γ ,, A @ l) N N' tyNat lzero ->
  VTmS G (Γ ,, A @ l) Ot Ot' X⟨↑⟩ li -> VTmS G (Γ ,, A @ l ,, tyFin N @ lzero) C C' X⟨↑⟩⟨↑⟩ li ->
  VTyS G (Γ ,, X @ li) (iwfmotty l li X A N Ot C) (iwfmotty l li X A N Ot C) (lmax l li) ->
  VTyS G (Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li) M M' l' ->
  VTyS G (Γ ,, A @ l) (iwfcsty l li X A N Ot C) (iwfcsty l li X A N Ot C) (lmax l li) ->
  VTyS G (Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li)
    (iwfihty l li l' X A N Ot C M) (iwfihty l3 li3 l4 X' A' N' Ot' C' M') (lmax lzero l') ->
  VTmS G (Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ,, iwfihty l li l' X A N Ot C M @ lmax lzero l')
    c c' (iwfstepty l li X A N Ot C M) l' ->
  VTmS G Γ m m' X li -> VTmS G Γ t t' (tyIWf l li X A N Ot C m) (lmax l li) ->
  VTmS G Γ (tmElimIWf l li l' X A N Ot C M c m t) (tmElimIWf l3 li3 l4 X' A' N' Ot' C' M' c' m' t')
    M[lsingle2 m t] l'.
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_elimIWf_ty {ly G Γ l li l' X A N Ot C M c m t} :
  VTmS G Γ t t (tyIWf l li X A N Ot C m) (lmax l li) ->
  VTyS G (Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li) M M l' ->
  lwf (gL G) l -> lwf (gL G) li -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ ly ] X @ li ] -> [ G ; Γ ⊢[ ly ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ ly ] N : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ⊢[ ly ] Ot : X⟨↑⟩ @ li ] -> [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ ly ] C : X⟨↑⟩⟨↑⟩ @ li ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ X X li -> VTyS G Γ A A l -> VTmS G (Γ ,, A @ l) N N tyNat lzero ->
  VTmS G (Γ ,, A @ l) Ot Ot X⟨↑⟩ li -> VTmS G (Γ ,, A @ l ,, tyFin N @ lzero) C C X⟨↑⟩⟨↑⟩ li ->
  VTyS G (Γ ,, X @ li) (iwfmotty l li X A N Ot C) (iwfmotty l li X A N Ot C) (lmax l li) ->
  VTyS G (Γ ,, A @ l) (iwfcsty l li X A N Ot C) (iwfcsty l li X A N Ot C) (lmax l li) ->
  VTyS G (Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li)
    (iwfihty l li l' X A N Ot C M) (iwfihty l li l' X A N Ot C M) (lmax lzero l') ->
  VTmS G (Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ,, iwfihty l li l' X A N Ot C M @ lmax lzero l')
    c c (iwfstepty l li X A N Ot C M) l' ->
  VTmS G Γ m m X li ->
  VTyS G Γ M[lsingle2 m t] M[lsingle2 m t] l'.
Proof using EL VL VN. intros; s_lift. Qed.

End Rules.

End RulesS.
