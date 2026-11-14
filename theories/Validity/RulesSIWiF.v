(** * [RulesS]: [IWi]'s formation and constructor (M19b), beside the other
    rules. *)
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

Lemma VS_iwi {G Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' m m'} :
  lwf (gL G) l -> lwf (gL G) lp -> lwf (gL G) li ->
  lequiv (gL G) k l -> lequiv (gL G) kp lp -> lequiv (gL G) ki li ->
  VTyS G Γ X X' li -> VTyS G Γ A A' l -> VTmS G (Γ ,, A @ l) N N' tyNat lzero ->
  VTyS G (Γ ,, A @ l ,, tyFin N @ lzero) D D' lp ->
  VTmS G (Γ ,, A @ l) Ot Ot' X⟨↑⟩ li -> VTmS G (Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp) C C' X⟨↑⟩⟨↑⟩⟨↑⟩ li ->
  VTmS G Γ m m' X li ->
  VTyS G Γ (tyIWi l lp li X A N D Ot C m) (tyIWi k kp ki X' A' N' D' Ot' C' m') (iwiL l lp li).
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_supii {G Γ l lp li k kp ki X X' A A' N N' D D' Ot Ot' C C' a a' cs cs'} :
  lwf (gL G) l -> lwf (gL G) lp -> lwf (gL G) li ->
  lequiv (gL G) k l -> lequiv (gL G) kp lp -> lequiv (gL G) ki li ->
  VTyS G Γ X X' li -> VTyS G Γ A A' l -> VTmS G (Γ ,, A @ l) N N' tyNat lzero ->
  VTyS G (Γ ,, A @ l ,, tyFin N @ lzero) D D' lp ->
  VTmS G (Γ ,, A @ l) Ot Ot' X⟨↑⟩ li -> VTmS G (Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp) C C' X⟨↑⟩⟨↑⟩⟨↑⟩ li ->
  VTmS G Γ a a' A l -> VTmS G Γ cs cs' (tyDVec (iwiL l lp li) N[lsingle a] (iwiFam l lp li X A N D Ot C a)) (iwiL l lp li) ->
  VTmS G Γ (tmSupii l lp li X A N D Ot C a cs) (tmSupii k kp ki X' A' N' D' Ot' C' a' cs')
    (tyIWi l lp li X A N D Ot C Ot[lsingle a]) (iwiL l lp li).
Proof using EL VL VN. intros; s_lift. Qed.
(* the constructor's type, at its output index *)
Lemma VS_supii_ty {G Γ l lp li X A N D Ot C a cs} :
  lwf (gL G) l -> lwf (gL G) lp -> lwf (gL G) li ->
  VTyS G Γ X X li -> VTyS G Γ A A l -> VTmS G (Γ ,, A @ l) N N tyNat lzero ->
  VTyS G (Γ ,, A @ l ,, tyFin N @ lzero) D D lp ->
  VTmS G (Γ ,, A @ l) Ot Ot X⟨↑⟩ li -> VTmS G (Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp) C C X⟨↑⟩⟨↑⟩⟨↑⟩ li ->
  VTmS G Γ a a A l -> VTmS G Γ cs cs (tyDVec (iwiL l lp li) N[lsingle a] (iwiFam l lp li X A N D Ot C a)) (iwiL l lp li) ->
  VTyS G Γ (tyIWi l lp li X A N D Ot C Ot[lsingle a]) (tyIWi l lp li X A N D Ot C Ot[lsingle a]) (iwiL l lp li).
Proof using EL VL VN. intros; s_lift. Qed.
End Rules.

End RulesS.
