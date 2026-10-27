(** * [RulesS]: [IWf]'s computation rule and its type (M17b), beside
    [RulesSIWf]. *)
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

Lemma VS_elimIWf_supi {ly G Γ l li l' X A N Ot C M c a cs} :
  lwf (gL G) l -> lwf (gL G) li -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ ly ] X @ li ] -> [ G ; Γ ⊢[ ly ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ ly ] N : tyNat @ lzero ] ->
  [ G ; Γ ,, A @ l ⊢[ ly ] Ot : X⟨↑⟩ @ li ] -> [ G ; Γ ,, A @ l ,, tyFin N @ lzero ⊢[ ly ] C : X⟨↑⟩⟨↑⟩ @ li ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ X X li -> VTyS G Γ A A l -> VTmS G (Γ ,, A @ l) N N tyNat lzero ->
  VTmS G (Γ ,, A @ l) Ot Ot X⟨↑⟩ li -> VTmS G (Γ ,, A @ l ,, tyFin N @ lzero) C C X⟨↑⟩⟨↑⟩ li ->
  VTyS G (Γ ,, X @ li) (iwfmotty l li X A N Ot C) (iwfmotty l li X A N Ot C) (lmax l li) ->
  VTyS G (Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li) M M l' ->
  VTyS G (Γ ,, A @ l) (iwfcsty l li X A N Ot C) (iwfcsty l li X A N Ot C) (lmax l li) ->
  VTyS G (Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li)
    (iwfihty l li l' X A N Ot C M) (iwfihty l li l' X A N Ot C M) (lmax lzero l') ->
  VTmS G (Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ,, iwfihty l li l' X A N Ot C M @ lmax lzero l')
    c c (iwfstepty l li X A N Ot C M) l' ->
  VTmS G Γ a a A l -> VTmS G Γ cs cs (tyDVec (lmax l li) N[lsingle a] (iwfFam l li X A N Ot C a)) (lmax l li) ->
  VTmS G Γ (tmElimIWf l li l' X A N Ot C M c Ot[lsingle a] (tmSupi l li X A N Ot C a cs))
    c[lsingle3 a cs (iwfIH l li l' X A N Ot C M c a cs)]
    M[lsingle2 Ot[lsingle a] (tmSupi l li X A N Ot C a cs)] l'.
Proof using EL VL VN. intros; s_lift. Qed.
End Rules.

End RulesS.
