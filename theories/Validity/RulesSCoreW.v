(** * [RulesS]: the rules from [W] on but the eliminator of [IWf], beside
    [RulesSCore]. *)
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

(** [RulesSCore]'s [VS_El], for the codes' [El] rules below. *)
Local Lemma VS_El_w {G Γ l l' t t'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTmS G Γ t t' (tyU l) (lsuc l) -> VTyS G Γ (tyEl l t) (tyEl l' t') l.
Proof using EL VL. intros; s_lift. Qed.

(** Well-founded trees (M13a). *)
Lemma VS_W {ly G Γ l l' l3 l4 A A' B B'} : lwf (gL G) l -> lwf (gL G) l' ->
  lequiv (gL G) l3 l -> lequiv (gL G) l4 l' -> [ G ; Γ ,, A @ l ⊢[ ly ] B @ l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A' l -> VTyS G (Γ ,, A @ l) B B' l' ->
  VTyS G Γ (tyW l l' A B) (tyW l3 l4 A' B') (lmax l l').
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_sup {ly G Γ l l' l3 l4 A A' B B' a a' f f'} : lwf (gL G) l -> lwf (gL G) l' ->
  lequiv (gL G) l3 l -> lequiv (gL G) l4 l' -> [ G ; Γ ,, A @ l ⊢[ ly ] B @ l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A' l -> VTyS G (Γ ,, A @ l) B B' l' -> VTmS G Γ a a' A l ->
  VTmS G Γ f f' (tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩) (lmax l' (lmax l l')) ->
  VTmS G Γ (tmSup l l' A B a f) (tmSup l3 l4 A' B' a' f') (tyW l l' A B) (lmax l l').
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_elimW {ly G Γ l l' l'' l4 l5 l6 A A' B B' M M' c c' t t'} :
  lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) l'' ->
  lequiv (gL G) l l4 -> lequiv (gL G) l' l5 -> lequiv (gL G) l'' l6 ->
  [ G ; Γ ,, A @ l ⊢[ ly ] B @ l' ] -> lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A' l -> VTyS G (Γ ,, A @ l) B B' l' -> VTyS G (Γ ,, tyW l l' A B @ lmax l l') M M' l'' ->
  VTyS G (Γ ,, A @ l) (wfty l l' A B) (wfty l l' A B) (lmax l' (lmax l l')) ->
  VTyS G (Γ ,, A @ l ,, wfty l l' A B @ lmax l' (lmax l l')) (wihty l l' l'' A B M) (wihty l l' l'' A B M)
    (lmax l' l'') ->
  VTmS G (Γ ,, A @ l ,, wfty l l' A B @ lmax l' (lmax l l') ,, wihty l l' l'' A B M @ lmax l' l'')
    c c' (wstepty l l' A B M) l'' ->
  VTmS G Γ t t' (tyW l l' A B) (lmax l l') ->
  VTmS G Γ (tmElimW l l' l'' A B M c t) (tmElimW l4 l5 l6 A' B' M' c' t') M[lsingle t] l''.
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_elimW_sup {ly G Γ l l' l'' A B M c a f} :
  lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) l'' ->
  [ G ; Γ ,, A @ l ⊢[ ly ] B @ l' ] -> lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A l -> VTyS G (Γ ,, A @ l) B B l' -> VTyS G (Γ ,, tyW l l' A B @ lmax l l') M M l'' ->
  VTyS G (Γ ,, A @ l) (wfty l l' A B) (wfty l l' A B) (lmax l' (lmax l l')) ->
  VTyS G (Γ ,, A @ l ,, wfty l l' A B @ lmax l' (lmax l l')) (wihty l l' l'' A B M) (wihty l l' l'' A B M)
    (lmax l' l'') ->
  VTmS G (Γ ,, A @ l ,, wfty l l' A B @ lmax l' (lmax l l') ,, wihty l l' l'' A B M @ lmax l' l'')
    c c (wstepty l l' A B M) l'' ->
  VTmS G Γ a a A l ->
  VTmS G Γ f f (tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩) (lmax l' (lmax l l')) ->
  VTmS G Γ (tmElimW l l' l'' A B M c (tmSup l l' A B a f)) c[lsingle3 a f (wIH l l' l'' A B M c a f)]
    M[lsingle (tmSup l l' A B a f)] l''.
Proof using EL VL VN. intros; s_lift. Qed.

(** The code of W (M13b), as Σ's. *)
Lemma VS_code_W {ly G Γ l1 l2 l3 l4 s s' t t'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ ly ] s : tyU l1 @ lsuc l1 ] -> [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ ly ] t : tyU l2 @ lsuc l2 ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTmS G Γ s s' (tyU l1) (lsuc l1) -> VTmS G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) (lsuc l2) ->
  VTmS G Γ (tmW l1 l2 s t) (tmW l3 l4 s' t') (tyU (lmax l1 l2)) (lsuc (lmax l1 l2)).
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_El_W {ly G Γ l l' s t} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ ly ] s : tyU l @ lsuc l ] -> [ G ; Γ ,, tyEl l s @ l ⊢[ ly ] t : tyU l' @ lsuc l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTmS G Γ s s (tyU l) (lsuc l) -> VTmS G (Γ ,, tyEl l s @ l) t t (tyU l') (lsuc l') ->
  VTyS G Γ (tyW l l' (tyEl l s) (tyEl l' t)) (tyEl (lmax l l') (tmW l l' s t)) (lmax l l').
Proof using EL VL VN.
  intros Hw Hw' Hs Ht Hly Hty Vs Vt. eapply (VTyS_trans_diag EP EM (T2 := tyEl (lmax l l') (tmW l l' s t))); [s_diag V_El_W|].
  apply VS_El_w; [exact (lwf_max Hw Hw') | apply lequiv_refl, lwf_max; assumption |].
  eapply VS_code_W; try eassumption; apply lequiv_refl; assumption.
Qed.

(** Vec and Fin (M14a). *)
Lemma VS_vec {G Γ l l' A A' n n'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTyS G Γ A A' l -> VTmS G Γ n n' tyNat lzero -> VTyS G Γ (tyVec l A n) (tyVec l' A' n') l.
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_fin {G Γ n n'} : VTmS G Γ n n' tyNat lzero -> VTyS G Γ (tyFin n) (tyFin n') lzero.
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_vec_zero {G Γ l l' A A'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTyS G Γ A A' l -> VTyS G Γ (tyVec l A zero) (tyUnit l') l.
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_vec_succ {G Γ l l' A A' n n'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTyS G Γ A A' l -> VTmS G Γ n n' tyNat lzero ->
  VTyS G Γ (tyVec l A (succ n)) (tySig l' l' A' (tyVec l' A'⟨↑⟩ n'⟨↑⟩)) l.
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_fin_zero {G Γ} : VTyS G Γ (tyFin zero) (tyEmpty lzero) lzero.
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_fin_succ {G Γ n n'} : VTmS G Γ n n' tyNat lzero ->
  VTyS G Γ (tyFin (succ n)) (tySum lzero lzero (tyUnit lzero) (tyFin n')) lzero.
Proof using EL VL VN. intros; s_lift. Qed.

(** The codes of Vec and Fin (M14b). *)
Lemma VS_code_vec {G Γ l l' s s' n n'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTmS G Γ s s' (tyU l) (lsuc l) -> VTmS G Γ n n' tyNat lzero ->
  VTmS G Γ (tmVec l s n) (tmVec l' s' n') (tyU l) (lsuc l).
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_El_vec {G Γ l s n} : lwf (gL G) l ->
  VTmS G Γ s s (tyU l) (lsuc l) -> VTmS G Γ n n tyNat lzero ->
  VTyS G Γ (tyVec l (tyEl l s) n) (tyEl l (tmVec l s n)) l.
Proof using EL VL VN.
  intros Hw Vs Vn. eapply (VTyS_trans_diag EP EM (T2 := tyEl l (tmVec l s n))); [s_diag V_El_vec|].
  apply VS_El_w; [exact Hw | apply lequiv_refl, Hw |].
  apply VS_code_vec; [exact Hw | apply lequiv_refl, Hw | exact Vs | exact Vn].
Qed.
Lemma VS_code_fin {G Γ n n'} : VTmS G Γ n n' tyNat lzero ->
  VTmS G Γ (tmFin n) (tmFin n') (tyU lzero) (lsuc lzero).
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_El_fin {G Γ n} : VTmS G Γ n n tyNat lzero -> VTyS G Γ (tyFin n) (tyEl lzero (tmFin n)) lzero.
Proof using EL VL VN.
  intros Vn. eapply (VTyS_trans_diag EP EM (T2 := tyEl lzero (tmFin n))); [s_diag V_El_fin|].
  apply VS_El_w; [exact I | exact (lequiv_refl _ lzero I) |].
  apply VS_code_fin; exact Vn.
Qed.

(** Dependent tuples (M17a). *)
Lemma VS_dvec {G Γ l l' n n' F F'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTmS G Γ n n' tyNat lzero -> VTyS G (Γ ,, tyFin n @ lzero) F F' l ->
  VTyS G Γ (tyDVec l n F) (tyDVec l' n' F') l.
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_dvec_zero {G Γ l l' F F'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTyS G (Γ ,, tyFin zero @ lzero) F F' l -> VTyS G Γ (tyDVec l zero F) (tyUnit l') l.
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_dvec_succ {G Γ l l' n n' F F'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTmS G Γ n n' tyNat lzero -> VTyS G (Γ ,, tyFin (succ n) @ lzero) F F' l ->
  VTyS G Γ (tyDVec l (succ n) F) (tySig l' l' (dvecHd n' F') (dvecTl l' n' F')) l.
Proof using EL VL VN. intros; s_lift. Qed.

(** Indexed well-founded trees (M17b). *)
Lemma VS_iwf {G Γ l li l' li' X X' A A' N N' Ot Ot' C C' m m'} :
  lwf (gL G) l -> lwf (gL G) li -> lequiv (gL G) l' l -> lequiv (gL G) li' li ->
  VTyS G Γ X X' li -> VTyS G Γ A A' l -> VTmS G (Γ ,, A @ l) N N' tyNat lzero ->
  VTmS G (Γ ,, A @ l) Ot Ot' X⟨↑⟩ li -> VTmS G (Γ ,, A @ l ,, tyFin N @ lzero) C C' X⟨↑⟩⟨↑⟩ li ->
  VTmS G Γ m m' X li ->
  VTyS G Γ (tyIWf l li X A N Ot C m) (tyIWf l' li' X' A' N' Ot' C' m') (lmax l li).
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_supi {G Γ l li l' li' X X' A A' N N' Ot Ot' C C' a a' cs cs'} :
  lwf (gL G) l -> lwf (gL G) li -> lequiv (gL G) l' l -> lequiv (gL G) li' li ->
  VTyS G Γ X X' li -> VTyS G Γ A A' l -> VTmS G (Γ ,, A @ l) N N' tyNat lzero ->
  VTmS G (Γ ,, A @ l) Ot Ot' X⟨↑⟩ li -> VTmS G (Γ ,, A @ l ,, tyFin N @ lzero) C C' X⟨↑⟩⟨↑⟩ li ->
  VTmS G Γ a a' A l -> VTmS G Γ cs cs' (tyDVec (lmax l li) N[lsingle a] (iwfFam l li X A N Ot C a)) (lmax l li) ->
  VTmS G Γ (tmSupi l li X A N Ot C a cs) (tmSupi l' li' X' A' N' Ot' C' a' cs')
    (tyIWf l li X A N Ot C Ot[lsingle a]) (lmax l li).
Proof using EL VL VN. intros; s_lift. Qed.
(* the constructor's type, at its output index *)
Lemma VS_supi_ty {G Γ l li X A N Ot C a cs} :
  lwf (gL G) l -> lwf (gL G) li ->
  VTyS G Γ X X li -> VTyS G Γ A A l -> VTmS G (Γ ,, A @ l) N N tyNat lzero ->
  VTmS G (Γ ,, A @ l) Ot Ot X⟨↑⟩ li -> VTmS G (Γ ,, A @ l ,, tyFin N @ lzero) C C X⟨↑⟩⟨↑⟩ li ->
  VTmS G Γ a a A l -> VTmS G Γ cs cs (tyDVec (lmax l li) N[lsingle a] (iwfFam l li X A N Ot C a)) (lmax l li) ->
  VTyS G Γ (tyIWf l li X A N Ot C Ot[lsingle a]) (tyIWf l li X A N Ot C Ot[lsingle a]) (lmax l li).
Proof using EL VL VN. intros; s_lift. Qed.


(** Finitary well-founded trees (M15a). *)
Lemma VS_wf {G Γ l l' A A' N N'} : lwf (gL G) l -> lequiv (gL G) l' l ->
  VTyS G Γ A A' l -> VTmS G (Γ ,, A @ l) N N' tyNat lzero -> VTyS G Γ (tyWf l A N) (tyWf l' A' N') l.
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_supf {G Γ l l' A A' N N' a a' cs cs'} : lwf (gL G) l -> lequiv (gL G) l' l ->
  VTyS G Γ A A' l -> VTmS G (Γ ,, A @ l) N N' tyNat lzero -> VTmS G Γ a a' A l ->
  VTmS G Γ cs cs' (tyVec l (tyWf l A N) N[lsingle a]) l ->
  VTmS G Γ (tmSupf l A N a cs) (tmSupf l' A' N' a' cs') (tyWf l A N) l.
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_elimWf {ly G Γ l l' l3 l4 A A' N N' M M' c c' t t'} :
  lwf (gL G) l -> lwf (gL G) l' -> lequiv (gL G) l l3 -> lequiv (gL G) l' l4 ->
  [ G ; Γ ,, A @ l ⊢[ ly ] N : tyNat @ lzero ] -> lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A' l -> VTmS G (Γ ,, A @ l) N N' tyNat lzero -> VTyS G (Γ ,, tyWf l A N @ l) M M' l' ->
  VTyS G (Γ ,, A @ l) (wfcsty l A N) (wfcsty l A N) l ->
  VTyS G (Γ ,, A @ l ,, wfcsty l A N @ l) (wfihty l l' A N M) (wfihty l l' A N M) (lmax lzero l') ->
  VTmS G (Γ ,, A @ l ,, wfcsty l A N @ l ,, wfihty l l' A N M @ lmax lzero l') c c' (wfstepty l A N M) l' ->
  VTmS G Γ t t' (tyWf l A N) l ->
  VTmS G Γ (tmElimWf l l' A N M c t) (tmElimWf l3 l4 A' N' M' c' t') M[lsingle t] l'.
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_elimWf_supf {ly G Γ l l' A N M c a cs} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ,, A @ l ⊢[ ly ] N : tyNat @ lzero ] -> lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A l -> VTmS G (Γ ,, A @ l) N N tyNat lzero -> VTyS G (Γ ,, tyWf l A N @ l) M M l' ->
  VTyS G (Γ ,, A @ l) (wfcsty l A N) (wfcsty l A N) l ->
  VTyS G (Γ ,, A @ l ,, wfcsty l A N @ l) (wfihty l l' A N M) (wfihty l l' A N M) (lmax lzero l') ->
  VTmS G (Γ ,, A @ l ,, wfcsty l A N @ l ,, wfihty l l' A N M @ lmax lzero l') c c (wfstepty l A N M) l' ->
  VTmS G Γ a a A l -> VTmS G Γ cs cs (tyVec l (tyWf l A N) N[lsingle a]) l ->
  VTmS G Γ (tmElimWf l l' A N M c (tmSupf l A N a cs)) c[lsingle3 a cs (wfIH l l' A N M c a cs)]
    M[lsingle (tmSupf l A N a cs)] l'.
Proof using EL VL VN. intros; s_lift. Qed.

(** The code of Wf (M15b). *)
Lemma VS_code_wf {ly G Γ l l' s s' n n'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  [ G ; Γ ⊢[ ly ] s : tyU l @ lsuc l ] -> [ G ; Γ ,, tyEl l s @ l ⊢[ ly ] n : tyNat @ lzero ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTmS G Γ s s' (tyU l) (lsuc l) -> VTmS G (Γ ,, tyEl l s @ l) n n' tyNat lzero ->
  VTmS G Γ (tmWf l s n) (tmWf l' s' n') (tyU l) (lsuc l).
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_El_wf {ly G Γ l s n} : lwf (gL G) l ->
  [ G ; Γ ⊢[ ly ] s : tyU l @ lsuc l ] -> [ G ; Γ ,, tyEl l s @ l ⊢[ ly ] n : tyNat @ lzero ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTmS G Γ s s (tyU l) (lsuc l) -> VTmS G (Γ ,, tyEl l s @ l) n n tyNat lzero ->
  VTyS G Γ (tyWf l (tyEl l s) n) (tyEl l (tmWf l s n)) l.
Proof using EL VL VN.
  intros Hw Hs Hn Hly Hty Vs Vn. eapply (VTyS_trans_diag EP EM (T2 := tyEl l (tmWf l s n))); [s_diag V_El_wf|].
  apply VS_El_w; [exact Hw | apply lequiv_refl, Hw |].
  eapply VS_code_wf; try eassumption; apply lequiv_refl; assumption.
Qed.

(** Propositional truncation (M16a). *)
Lemma VS_sq {G Γ l l' A A'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTyS G Γ A A' l -> VTyS G Γ (tySq l A) (tySq l' A') l.
Proof using EL VL. intros; s_lift. Qed.
(** The eliminator's type, the motive at a valid scrutinee. *)
Lemma VS_sq_single {G Γ l l' X M a} : lwf (gL G) l' ->
  VTyS G (Γ ,, X @ l) M M l' -> VTmS G Γ a a X l ->
  VTyS G Γ (tySq l' M[lsingle a]) (tySq l' M[lsingle a]) l'.
Proof using EL VL. intros Hw VM Va. apply VS_sq; [exact Hw | apply lequiv_refl, Hw | exact (VTyS_single EP EM VM Va)]. Qed.
Lemma VS_sq_intro {G Γ l l' A A' a a'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTyS G Γ A A' l -> VTmS G Γ a a' A l -> VTmS G Γ (tmSq l A a) (tmSq l' A' a') (tySq l A) l.
Proof using EL VL. intros; s_lift. Qed.
(** β's type, the motive at a [squash]. *)
Lemma VS_sq_single_sq {G Γ l l' A M a} : lwf (gL G) l -> lwf (gL G) l' ->
  VTyS G Γ A A l -> VTyS G (Γ ,, tySq l A @ l) M M l' -> VTmS G Γ a a A l ->
  VTyS G Γ (tySq l' M[lsingle (tmSq l A a)]) (tySq l' M[lsingle (tmSq l A a)]) l'.
Proof using EL VL.
  intros Hw Hw' VA VM Va. eapply VS_sq_single; [exact Hw' | exact VM |].
  apply VS_sq_intro; [exact Hw | apply lequiv_refl, Hw | exact VA | exact Va].
Qed.
Lemma VS_sq_irr {G Γ l A t t'} : lwf (gL G) l ->
  VTmS G Γ t t (tySq l A) l -> VTmS G Γ t' t' (tySq l A) l -> VTmS G Γ t t' (tySq l A) l.
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_elimSq {G Γ l1 l2 l3 l4 A A' M M' c c' t t'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  VTyS G Γ A A' l1 -> VTyS G (Γ ,, tySq l1 A @ l1) M M' l2 ->
  VTmS G (Γ ,, A @ l1) c c' (tySq l2 M⟨rlift ↑⟩[lsingle (tmSq l1 A⟨↑⟩ (var 0))]) l2 ->
  VTmS G Γ t t' (tySq l1 A) l1 ->
  VTmS G Γ (tmElimSq l1 l2 A M c t) (tmElimSq l3 l4 A' M' c' t') (tySq l2 M[lsingle t]) l2.
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_elimSq_sq {ly G Γ l l' A M c a} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ ly ] A @ l ] -> lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A l -> VTyS G (Γ ,, tySq l A @ l) M M l' ->
  VTmS G (Γ ,, A @ l) c c (tySq l' M⟨rlift ↑⟩[lsingle (tmSq l A⟨↑⟩ (var 0))]) l' ->
  VTmS G Γ a a A l ->
  VTmS G Γ (tmElimSq l l' A M c (tmSq l A a)) c[lsingle a] (tySq l' M[lsingle (tmSq l A a)]) l'.
Proof using EL VL VN.
  intros. eapply (VTmS_trans_diag EP EM (t2 := c[lsingle a])); [s_diag V_elimSq_sq|].
  rewrite <- (sq_single M l A a) by (eapply wf_ty_nf; eassumption).
  change (tySq l' (M⟨rlift ↑⟩[lsingle (tmSq l A⟨↑⟩ (var 0))])[lsingle a])
    with ((tySq l' M⟨rlift ↑⟩[lsingle (tmSq l A⟨↑⟩ (var 0))])[lsingle a]).
  eapply VTmS_single; eassumption.
Qed.

(** The release of a squashed absurdity (M16c). *)
Lemma VS_unsq {G Γ l l' t t'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTmS G Γ t t' (tySq l (tyEmpty l)) l -> VTmS G Γ (tmUnsq l t) (tmUnsq l' t') (tyEmpty l) l.
Proof using EL VL VN. intros; s_lift. Qed.

(** The code of ∥·∥ (M16b). *)
Lemma VS_code_sq {G Γ l l' s s'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTmS G Γ s s' (tyU l) (lsuc l) -> VTmS G Γ (tmSqCode l s) (tmSqCode l' s') (tyU l) (lsuc l).
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_El_sq {G Γ l s} : lwf (gL G) l ->
  VTmS G Γ s s (tyU l) (lsuc l) -> VTyS G Γ (tySq l (tyEl l s)) (tyEl l (tmSqCode l s)) l.
Proof using EL VL VN.
  intros Hw Vs. eapply (VTyS_trans_diag EP EM (T2 := tyEl l (tmSqCode l s))); [s_diag V_El_sq|].
  apply VS_El_w; [exact Hw | apply lequiv_refl, Hw |].
  apply VS_code_sq; [exact Hw | apply lequiv_refl, Hw | exact Vs].
Qed.

(** The codes of DVec and IWf (M17c). *)
Lemma VS_code_dvec {G Γ l l' n n' f f'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTmS G Γ n n' tyNat lzero -> VTmS G (Γ ,, tyFin n @ lzero) f f' (tyU l) (lsuc l) ->
  VTmS G Γ (tmDVec l n f) (tmDVec l' n' f') (tyU l) (lsuc l).
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_El_dvec {G Γ l n f} : lwf (gL G) l ->
  VTmS G Γ n n tyNat lzero -> VTmS G (Γ ,, tyFin n @ lzero) f f (tyU l) (lsuc l) ->
  VTyS G Γ (tyDVec l n (tyEl l f)) (tyEl l (tmDVec l n f)) l.
Proof using EL VL VN.
  intros Hw Vn Vf. eapply (VTyS_trans_diag EP EM (T2 := tyEl l (tmDVec l n f))); [s_diag V_El_dvec|].
  apply VS_El_w; [exact Hw | apply lequiv_refl, Hw |].
  apply VS_code_dvec; [exact Hw | apply lequiv_refl, Hw | exact Vn | exact Vf].
Qed.
Lemma VS_code_iwf {G Γ l li l' li' x x' s s' n n' o o' c c' m m'} :
  lwf (gL G) l -> lwf (gL G) li -> lequiv (gL G) l l' -> lequiv (gL G) li li' ->
  VTmS G Γ x x' (tyU li) (lsuc li) -> VTmS G Γ s s' (tyU l) (lsuc l) ->
  VTmS G (Γ ,, tyEl l s @ l) n n' tyNat lzero ->
  VTmS G (Γ ,, tyEl l s @ l) o o' (tyEl li x⟨↑⟩) li ->
  VTmS G (Γ ,, tyEl l s @ l ,, tyFin n @ lzero) c c' (tyEl li x⟨↑⟩⟨↑⟩) li ->
  VTmS G Γ m m' (tyEl li x) li ->
  VTmS G Γ (tmIWf l li x s n o c m) (tmIWf l' li' x' s' n' o' c' m')
    (tyU (lmax l li)) (lsuc (lmax l li)).
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_El_iwf {G Γ l li x s n o c m} : lwf (gL G) l -> lwf (gL G) li ->
  VTmS G Γ x x (tyU li) (lsuc li) -> VTmS G Γ s s (tyU l) (lsuc l) ->
  VTmS G (Γ ,, tyEl l s @ l) n n tyNat lzero ->
  VTmS G (Γ ,, tyEl l s @ l) o o (tyEl li x⟨↑⟩) li ->
  VTmS G (Γ ,, tyEl l s @ l ,, tyFin n @ lzero) c c (tyEl li x⟨↑⟩⟨↑⟩) li ->
  VTmS G Γ m m (tyEl li x) li ->
  VTyS G Γ (tyIWf l li (tyEl li x) (tyEl l s) n o c m) (tyEl (lmax l li) (tmIWf l li x s n o c m)) (lmax l li).
Proof using EL VL VN.
  intros Hw Hwi Vx Vs Vn Vo Vc Vm.
  eapply (VTyS_trans_diag EP EM (T2 := tyEl (lmax l li) (tmIWf l li x s n o c m))); [s_diag V_El_iwf|].
  assert (Hwm : lwf (gL G) (lmax l li)) by (cbn; split; assumption).
  apply VS_El_w; [exact Hwm | apply lequiv_refl, Hwm |].
  apply VS_code_iwf; try assumption; apply lequiv_refl; assumption.
Qed.

(** Indexed coinductive types (M18b). *)
Lemma VS_M {G Γ l l' li k k' ki X X' A A' B B' C C' m m'} :
  lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) li ->
  lequiv (gL G) k l -> lequiv (gL G) k' l' -> lequiv (gL G) ki li ->
  VTyS G Γ X X' li -> VTyS G (Γ ,, X @ li) A A' l -> VTyS G (Γ ,, X @ li ,, A @ l) B B' l' ->
  VTmS G (Γ ,, X @ li ,, A @ l ,, B @ l') C C' X⟨↑⟩⟨↑⟩⟨↑⟩ li -> VTmS G Γ m m' X li ->
  VTyS G Γ (tyM l l' li X A B C m) (tyM k k' ki X' A' B' C' m') (mlvl l l' li).
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_mOutTy {G Γ l l' li X A B C m} :
  lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) li ->
  VTyS G Γ X X li -> VTyS G (Γ ,, X @ li) A A l -> VTyS G (Γ ,, X @ li ,, A @ l) B B l' ->
  VTmS G (Γ ,, X @ li ,, A @ l ,, B @ l') C C X⟨↑⟩⟨↑⟩⟨↑⟩ li -> VTmS G Γ m m X li ->
  VTyS G Γ (mOutTy l l' li X A B C m) (mOutTy l l' li X A B C m) (lmax l (mlvl l l' li)).
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_out {G Γ l l' li k k' ki X X' A A' B B' C C' m m' t t'} :
  lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) li ->
  lequiv (gL G) k l -> lequiv (gL G) k' l' -> lequiv (gL G) ki li ->
  VTyS G Γ X X' li -> VTyS G (Γ ,, X @ li) A A' l -> VTyS G (Γ ,, X @ li ,, A @ l) B B' l' ->
  VTmS G (Γ ,, X @ li ,, A @ l ,, B @ l') C C' X⟨↑⟩⟨↑⟩⟨↑⟩ li -> VTmS G Γ m m' X li ->
  VTmS G Γ t t' (tyM l l' li X A B C m) (mlvl l l' li) ->
  VTmS G Γ (tmOut l l' li X A B C m t) (tmOut k k' ki X' A' B' C' m' t')
    (mOutTy l l' li X A B C m) (lmax l (mlvl l l' li)).
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_corec {ly G Γ l l' li k k' ki kc kc' X X' A A' B B' C C' Y Y' c c' m m' y y'} :
  lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) li -> lwf (gL G) kc ->
  lequiv (gL G) k l -> lequiv (gL G) k' l' -> lequiv (gL G) ki li -> lequiv (gL G) kc' kc ->
  [ G ; Γ ⊢[ ly ] X @ li ] -> [ G ; Γ ,, X @ li ⊢[ ly ] A @ l ] -> [ G ; Γ ,, X @ li ,, A @ l ⊢[ ly ] B @ l' ] ->
  [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ⊢[ ly ] C : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] -> [ G ; Γ ,, X @ li ⊢[ ly ] Y @ kc ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ X X' li -> VTyS G (Γ ,, X @ li) A A' l -> VTyS G (Γ ,, X @ li ,, A @ l) B B' l' ->
  VTmS G (Γ ,, X @ li ,, A @ l ,, B @ l') C C' X⟨↑⟩⟨↑⟩⟨↑⟩ li -> VTyS G (Γ ,, X @ li) Y Y' kc ->
  VTmS G (Γ ,, X @ li ,, Y @ kc) c c' (mStepTy l l' li X A B C kc Y)⟨↑⟩ (lmax l (lmax kc (mlvl l l' li))) ->
  VTmS G Γ m m' X li -> VTmS G Γ y y' Y[lsingle m] kc ->
  VTmS G Γ (tmCorec l l' li X A B C kc Y c m y) (tmCorec k k' ki X' A' B' C' kc' Y' c' m' y')
    (tyM l l' li X A B C m) (mlvl l l' li).
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_out_corec {ly G Γ l l' li X A B C kc Y c m y} :
  lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) li -> lwf (gL G) kc ->
  [ G ; Γ ⊢[ ly ] X @ li ] -> [ G ; Γ ,, X @ li ⊢[ ly ] A @ l ] -> [ G ; Γ ,, X @ li ,, A @ l ⊢[ ly ] B @ l' ] ->
  [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ⊢[ ly ] C : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] -> [ G ; Γ ,, X @ li ⊢[ ly ] Y @ kc ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ X X li -> VTyS G (Γ ,, X @ li) A A l -> VTyS G (Γ ,, X @ li ,, A @ l) B B l' ->
  VTmS G (Γ ,, X @ li ,, A @ l ,, B @ l') C C X⟨↑⟩⟨↑⟩⟨↑⟩ li -> VTyS G (Γ ,, X @ li) Y Y kc ->
  VTmS G (Γ ,, X @ li ,, Y @ kc) c c (mStepTy l l' li X A B C kc Y)⟨↑⟩ (lmax l (lmax kc (mlvl l l' li))) ->
  VTmS G Γ m m X li -> VTmS G Γ y y Y[lsingle m] kc ->
  VTmS G Γ (tmOut l l' li X A B C m (tmCorec l l' li X A B C kc Y c m y)) (mOutCorec l l' li X A B C kc Y c m y)
    (mOutTy l l' li X A B C m) (lmax l (mlvl l l' li)).
Proof using EL VL VN. intros; s_lift. Qed.


End Rules.

End RulesS.
