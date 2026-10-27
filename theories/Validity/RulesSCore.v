(** * [RulesS]: the rules up to [Id] and sums; [W] on, and the eliminator
    of [IWf] (M17b), build in [RulesSCoreW] and [RulesSIWf*] beside them. *)
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

Lemma VS_var {G Γ n T l} : in_ctx Γ n T l -> VTmS G Γ (var n) (var n) T l.
Proof using . intros; s_lift. Qed.
Lemma VS_nat {G Γ} : VTyS G Γ tyNat tyNat lzero.
Proof using . s_lift. Qed.
Lemma VS_zero {G Γ} : VTmS G Γ zero zero tyNat lzero.
Proof using EL VL. s_lift. Qed.
Lemma VS_succ {G Γ t t'} : VTmS G Γ t t' tyNat lzero -> VTmS G Γ (succ t) (succ t') tyNat lzero.
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_U {G Γ l l'} : lwf (gL G) l -> lequiv (gL G) l l' -> VTyS G Γ (tyU l) (tyU l') (lsuc l).
Proof using . intros; s_lift. Qed.
Lemma VS_El {G Γ l l' t t'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTmS G Γ t t' (tyU l) (lsuc l) -> VTyS G Γ (tyEl l t) (tyEl l' t') l.
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_code_nat {G Γ} : VTmS G Γ tmNat tmNat (tyU lzero) (lsuc lzero).
Proof using EL VL. s_lift. Qed.
Lemma VS_code_U {G Γ l l'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTmS G Γ (tmU l) (tmU l') (tyU (lsuc l)) (lsuc (lsuc l)).
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_El_nat {G Γ} : VTyS G Γ tyNat (tyEl lzero tmNat) lzero.
Proof using . s_lift. Qed.
Lemma VS_El_U {G Γ l} : lwf (gL G) l -> VTyS G Γ (tyU l) (tyEl (lsuc l) (tmU l)) (lsuc l).
Proof using . intros; s_lift. Qed.

Lemma VS_pi {ly G Γ l l' l3 l4 A A' B B'} : lwf (gL G) l -> lwf (gL G) l' ->
  lequiv (gL G) l3 l -> lequiv (gL G) l4 l' -> [ G ; Γ ,, A @ l ⊢[ ly ] B @ l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A' l -> VTyS G (Γ ,, A @ l) B B' l' ->
  VTyS G Γ (tyPi l l' A B) (tyPi l3 l4 A' B') (lmax l l').
Proof using EL VL VN. intros; s_lift. Qed.

Lemma VS_app {ly G Γ l l' l3 l4 A A' B B' t t' s s'} : lwf (gL G) l -> lwf (gL G) l' ->
  lequiv (gL G) l3 l -> lequiv (gL G) l4 l' -> [ G ; Γ ,, A @ l ⊢[ ly ] B @ l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A' l -> VTyS G (Γ ,, A @ l) B B' l' ->
  VTmS G Γ t t' (tyPi l l' A B) (lmax l l') -> VTmS G Γ s s' A l ->
  VTmS G Γ (app t l l' A B s) (app t' l3 l4 A' B' s') B[lsingle s] l'.
Proof using EL VL VN. intros; s_lift. Qed.

Lemma VS_lam {ly G Γ l l' l3 l4 A A' B t t'} : lwf (gL G) l -> lwf (gL G) l' ->
  lequiv (gL G) l3 l -> lequiv (gL G) l4 l' -> [ G ; Γ ,, A @ l ⊢[ ly ] B @ l' ] ->
  [ G ; Γ ,, A @ l ⊢[ ly ] t : B @ l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A' l -> VTyS G (Γ ,, A @ l) B B l' -> VTmS G (Γ ,, A @ l) t t' B l' ->
  VTmS G Γ (lam l l' A t) (lam l3 l4 A' t') (tyPi l l' A B) (lmax l l').
Proof using EL VL VN. intros; s_lift. Qed.

Lemma VS_natrec {ly G Γ l l' M M' s s' z z' t t'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  [ G ; Γ ,, tyNat @ lzero ⊢[ ly ] M @ l ] -> [ G ; Γ ⊢[ ly ] s : M[lsingle zero] @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ ly ] z : M[lsucc] @ l ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G (Γ ,, tyNat @ lzero) M M' l -> VTmS G Γ s s' M[lsingle zero] l ->
  VTmS G (Γ ,, tyNat @ lzero ,, M @ l) z z' M[lsucc] l -> VTmS G Γ t t' tyNat lzero ->
  VTmS G Γ (natrec l M s z t) (natrec l' M' s' z' t') M[lsingle t] l.
Proof using EL VL VN. intros; s_lift. Qed.

Lemma VS_code_pi {ly G Γ l1 l2 l3 l4 s s' t t'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ ly ] s : tyU l1 @ lsuc l1 ] -> [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ ly ] t : tyU l2 @ lsuc l2 ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTmS G Γ s s' (tyU l1) (lsuc l1) -> VTmS G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) (lsuc l2) ->
  VTmS G Γ (tmPi l1 l2 s t) (tmPi l3 l4 s' t') (tyU (lmax l1 l2)) (lsuc (lmax l1 l2)).
Proof using EL VL VN. intros; s_lift. Qed.

(** ** Computation rules *)

Lemma VS_beta {ly G Γ l l' A B t s} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ,, A @ l ⊢[ ly ] B @ l' ] -> [ G ; Γ ,, A @ l ⊢[ ly ] t : B @ l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A l -> VTmS G (Γ ,, A @ l) t t B l' -> VTmS G Γ s s A l ->
  VTmS G Γ (app (lam l l' A t) l l' A B s) t[lsingle s] B[lsingle s] l'.
Proof using EL VL.
  intros. eapply (VTmS_trans_diag EP EM (t2 := t[lsingle s])); [s_diag V_beta | eapply VTmS_single; eassumption].
Qed.

Lemma VS_eta {ly G Γ l l' A B t} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ ly ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ ly ] B @ l' ] ->
  [ G ; Γ ⊢[ ly ] t : tyPi l l' A B @ lmax l l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A l -> VTyS G (Γ ,, A @ l) B B l' -> VTmS G Γ t t (tyPi l l' A B) (lmax l l') ->
  VTmS G Γ (lam l l' A (app t⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0))) t (tyPi l l' A B) (lmax l l').
Proof using EL VL VN. intros. eapply (VTmS_trans_diag EP EM (t2 := t)); [s_diag V_eta | eassumption]. Qed.

Lemma VS_natrec_zero {ly G Γ l M s z} : lwf (gL G) l ->
  [ G ; Γ ,, tyNat @ lzero ⊢[ ly ] M @ l ] -> [ G ; Γ ⊢[ ly ] s : M[lsingle zero] @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ ly ] z : M[lsucc] @ l ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G (Γ ,, tyNat @ lzero) M M l -> VTmS G Γ s s M[lsingle zero] l ->
  VTmS G (Γ ,, tyNat @ lzero ,, M @ l) z z M[lsucc] l ->
  VTmS G Γ (natrec l M s z zero) s M[lsingle zero] l.
Proof using EL VL. intros. eapply (VTmS_trans_diag EP EM (t2 := s)); [s_diag V_natrec_zero | eassumption]. Qed.

Lemma VS_natrec_succ {ly G Γ l M s z t} : lwf (gL G) l ->
  [ G ; Γ ,, tyNat @ lzero ⊢[ ly ] M @ l ] -> [ G ; Γ ⊢[ ly ] s : M[lsingle zero] @ l ] ->
  [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ ly ] z : M[lsucc] @ l ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G (Γ ,, tyNat @ lzero) M M l -> VTmS G Γ s s M[lsingle zero] l ->
  VTmS G (Γ ,, tyNat @ lzero ,, M @ l) z z M[lsucc] l -> VTmS G Γ t t tyNat lzero ->
  VTmS G Γ (natrec l M s z (succ t)) z[lsingle2 t (natrec l M s z t)] M[lsingle (succ t)] l.
Proof using EL VL VN.
  intros. eapply (VTmS_trans_diag EP EM (t2 := z[lsingle2 t (natrec l M s z t)])); [s_diag V_natrec_succ|].
  eapply VTmS_single2; try eassumption.
  eapply VS_natrec; try eassumption. apply lequiv_refl; assumption.
Qed.

Lemma VS_El_pi {ly G Γ l l' s t} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ ly ] s : tyU l @ lsuc l ] -> [ G ; Γ ,, tyEl l s @ l ⊢[ ly ] t : tyU l' @ lsuc l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTmS G Γ s s (tyU l) (lsuc l) -> VTmS G (Γ ,, tyEl l s @ l) t t (tyU l') (lsuc l') ->
  VTyS G Γ (tyPi l l' (tyEl l s) (tyEl l' t)) (tyEl (lmax l l') (tmPi l l' s t)) (lmax l l').
Proof using EL VL VN.
  intros Hw Hw' Hs Ht Hly Hty Vs Vt. eapply (VTyS_trans_diag EP EM (T2 := tyEl (lmax l l') (tmPi l l' s t))); [s_diag V_El_pi|].
  apply VS_El; [exact (lwf_max Hw Hw') | apply lequiv_refl, lwf_max; assumption |].
  eapply VS_code_pi; try eassumption; apply lequiv_refl; assumption.
Qed.

(** ** Dependent pairs (M8) *)

Lemma VS_sig {ly G Γ l l' l3 l4 A A' B B'} : lwf (gL G) l -> lwf (gL G) l' ->
  lequiv (gL G) l3 l -> lequiv (gL G) l4 l' -> [ G ; Γ ,, A @ l ⊢[ ly ] B @ l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A' l -> VTyS G (Γ ,, A @ l) B B' l' ->
  VTyS G Γ (tySig l l' A B) (tySig l3 l4 A' B') (lmax l l').
Proof using EL VL VN. intros; s_lift. Qed.

Lemma VS_code_sig {ly G Γ l1 l2 l3 l4 s s' t t'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ⊢[ ly ] s : tyU l1 @ lsuc l1 ] -> [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ ly ] t : tyU l2 @ lsuc l2 ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTmS G Γ s s' (tyU l1) (lsuc l1) -> VTmS G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) (lsuc l2) ->
  VTmS G Γ (tmSig l1 l2 s t) (tmSig l3 l4 s' t') (tyU (lmax l1 l2)) (lsuc (lmax l1 l2)).
Proof using EL VL VN. intros; s_lift. Qed.

Lemma VS_pair {ly G Γ l l' l3 l4 A A' B B' a a' b b'} : lwf (gL G) l -> lwf (gL G) l' ->
  lequiv (gL G) l3 l -> lequiv (gL G) l4 l' -> [ G ; Γ ,, A @ l ⊢[ ly ] B @ l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A' l -> VTyS G (Γ ,, A @ l) B B' l' ->
  VTmS G Γ a a' A l -> VTmS G Γ b b' B[lsingle a] l' ->
  VTmS G Γ (tmPair l l' A B a b) (tmPair l3 l4 A' B' a' b') (tySig l l' A B) (lmax l l').
Proof using EL VL VN. intros; s_lift. Qed.

Lemma VS_fst {ly G Γ l l' l3 l4 A A' B B' p p'} : lwf (gL G) l -> lwf (gL G) l' ->
  lequiv (gL G) l3 l -> lequiv (gL G) l4 l' -> [ G ; Γ ,, A @ l ⊢[ ly ] B @ l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A' l -> VTyS G (Γ ,, A @ l) B B' l' ->
  VTmS G Γ p p' (tySig l l' A B) (lmax l l') ->
  VTmS G Γ (tmFst l l' A B p) (tmFst l3 l4 A' B' p') A l.
Proof using EL VL VN. intros; s_lift. Qed.

Lemma VS_snd {ly G Γ l l' l3 l4 A A' B B' p p'} : lwf (gL G) l -> lwf (gL G) l' ->
  lequiv (gL G) l3 l -> lequiv (gL G) l4 l' -> [ G ; Γ ,, A @ l ⊢[ ly ] B @ l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A' l -> VTyS G (Γ ,, A @ l) B B' l' ->
  VTmS G Γ p p' (tySig l l' A B) (lmax l l') ->
  VTmS G Γ (tmSnd l l' A B p) (tmSnd l3 l4 A' B' p') B[lsingle (tmFst l l' A B p)] l'.
Proof using EL VL VN. intros; s_lift. Qed.

Lemma VS_fst_beta {ly G Γ l l' A B a b} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ,, A @ l ⊢[ ly ] B @ l' ] -> [ G ; Γ ⊢[ ly ] a : A @ l ] ->
  [ G ; Γ ⊢[ ly ] b : B[lsingle a] @ l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A l -> VTyS G (Γ ,, A @ l) B B l' -> VTmS G Γ a a A l -> VTmS G Γ b b B[lsingle a] l' ->
  VTmS G Γ (tmFst l l' A B (tmPair l l' A B a b)) a A l.
Proof using EL VL. intros. eapply (VTmS_trans_diag EP EM (t2 := a)); [s_diag V_fst_beta | eassumption]. Qed.

Lemma VS_snd_beta {ly G Γ l l' A B a b} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ,, A @ l ⊢[ ly ] B @ l' ] -> [ G ; Γ ⊢[ ly ] a : A @ l ] ->
  [ G ; Γ ⊢[ ly ] b : B[lsingle a] @ l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A l -> VTyS G (Γ ,, A @ l) B B l' -> VTmS G Γ a a A l -> VTmS G Γ b b B[lsingle a] l' ->
  VTmS G Γ (tmSnd l l' A B (tmPair l l' A B a b)) b B[lsingle a] l'.
Proof using EL VL. intros. eapply (VTmS_trans_diag EP EM (t2 := b)); [s_diag V_snd_beta | eassumption]. Qed.

Lemma VS_sig_eta {ly G Γ l l' A B p} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ ly ] A @ l ] -> [ G ; Γ ,, A @ l ⊢[ ly ] B @ l' ] ->
  [ G ; Γ ⊢[ ly ] p : tySig l l' A B @ lmax l l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A l -> VTyS G (Γ ,, A @ l) B B l' -> VTmS G Γ p p (tySig l l' A B) (lmax l l') ->
  VTmS G Γ (tmPair l l' A B (tmFst l l' A B p) (tmSnd l l' A B p)) p (tySig l l' A B) (lmax l l').
Proof using EL VL VN. intros. eapply (VTmS_trans_diag EP EM (t2 := p)); [s_diag V_sig_eta | eassumption]. Qed.

Lemma VS_El_sig {ly G Γ l l' s t} : lwf (gL G) l -> lwf (gL G) l' ->
  [ G ; Γ ⊢[ ly ] s : tyU l @ lsuc l ] -> [ G ; Γ ,, tyEl l s @ l ⊢[ ly ] t : tyU l' @ lsuc l' ] ->
  lle ly ge_layer -> typeof ly = ly ->
  VTmS G Γ s s (tyU l) (lsuc l) -> VTmS G (Γ ,, tyEl l s @ l) t t (tyU l') (lsuc l') ->
  VTyS G Γ (tySig l l' (tyEl l s) (tyEl l' t)) (tyEl (lmax l l') (tmSig l l' s t)) (lmax l l').
Proof using EL VL VN.
  intros Hw Hw' Hs Ht Hly Hty Vs Vt. eapply (VTyS_trans_diag EP EM (T2 := tyEl (lmax l l') (tmSig l l' s t))); [s_diag V_El_sig|].
  apply VS_El; [exact (lwf_max Hw Hw') | apply lequiv_refl, lwf_max; assumption |].
  eapply VS_code_sig; try eassumption; apply lequiv_refl; assumption.
Qed.

(** The unit type (M8c). *)
Lemma VS_unit {G Γ l l'} : lwf (gL G) l -> lequiv (gL G) l l' -> VTyS G Γ (tyUnit l) (tyUnit l') l.
Proof using . intros; s_lift. Qed.
Lemma VS_code_unit {G Γ l l'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTmS G Γ (tmUnit l) (tmUnit l') (tyU l) (lsuc l).
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_triv {G Γ l l'} : lwf (gL G) l -> lequiv (gL G) l l' -> VTmS G Γ (tmTriv l) (tmTriv l') (tyUnit l) l.
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_El_unit {G Γ l} : lwf (gL G) l -> VTyS G Γ (tyUnit l) (tyEl l (tmUnit l)) l.
Proof using . intros; s_lift. Qed.
Lemma VS_unit_eta {G Γ l t t'} : lwf (gL G) l ->
  VTmS G Γ t t (tyUnit l) l -> VTmS G Γ t' t' (tyUnit l) l -> VTmS G Γ t t' (tyUnit l) l.
Proof using EL VL. intros; s_lift. Qed.

(** Strict equality (M10a). *)
Lemma VS_seq {G Γ l l' A A' a a' b b'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTyS G Γ A A' l -> VTmS G Γ a a' A l -> VTmS G Γ b b' A l ->
  VTyS G Γ (tySEq l A a b) (tySEq l' A' a' b') l.
Proof using EL. intros; s_lift. Qed.
Lemma VS_sempty {G Γ l l'} : lwf (gL G) l -> lequiv (gL G) l l' -> VTyS G Γ (tySEmpty l) (tySEmpty l') l.
Proof using . intros; s_lift. Qed.
Lemma VS_srefl {G Γ l l' A A' a a'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTyS G Γ A A' l -> VTmS G Γ a a' A l -> VTmS G Γ (srefl l A a) (srefl l' A' a') (tySEq l A a a) l.
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_elimSEmpty {G Γ l1 l2 l3 l4 M M' e e'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lequiv (gL G) l3 l1 -> lequiv (gL G) l4 l2 ->
  VTyS G Γ M M' l2 -> VTmS G Γ e e' (tySEmpty l1) l1 ->
  VTmS G Γ (elimSEmpty l1 l2 M e) (elimSEmpty l3 l4 M' e') M l2.
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_seq_irr {G Γ l A a b t t'} :
  VTmS G Γ t t (tySEq l A a b) l -> VTmS G Γ t' t' (tySEq l A a b) l -> VTmS G Γ t t' (tySEq l A a b) l.
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_sempty_irr {G Γ l t t'} : lwf (gL G) l ->
  VTmS G Γ t t (tySEmpty l) l -> VTmS G Γ t' t' (tySEmpty l) l -> VTmS G Γ t t' (tySEmpty l) l.
Proof using EL VL. intros; s_lift. Qed.

(** The identity type (M11a). *)
Lemma VS_id {G Γ l l' A A' a a' b b'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTyS G Γ A A' l -> VTmS G Γ a a' A l -> VTmS G Γ b b' A l ->
  VTyS G Γ (tyId l A a b) (tyId l' A' a' b') l.
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_idrefl {G Γ l l' A A' a a'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTyS G Γ A A' l -> VTmS G Γ a a' A l -> VTmS G Γ (tmRefl l A a) (tmRefl l' A' a') (tyId l A a a) l.
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_J {G Γ l1 l2 l3 l4 A A' a a' M M' c c' u u' e e'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  VTyS G Γ A A' l1 -> VTmS G Γ a a' A l1 ->
  VTyS G (Γ ,, A @ l1) (tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0)) (tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0)) l1 ->
  VTyS G (Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1) M M' l2 ->
  VTmS G Γ c c' M[lsingle2 a (tmRefl l1 A a)] l2 ->
  VTmS G Γ u u' A l1 -> VTmS G Γ e e' (tyId l1 A a u) l1 ->
  VTmS G Γ (tmJ l1 l2 A a M c u e) (tmJ l3 l4 A' a' M' c' u' e') M[lsingle2 u e] l2.
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_J_beta {G Γ l l' A a M c} : lwf (gL G) l -> lwf (gL G) l' ->
  VTyS G Γ A A l -> VTmS G Γ a a A l ->
  VTyS G (Γ ,, A @ l) (tyId l A⟨↑⟩ a⟨↑⟩ (var 0)) (tyId l A⟨↑⟩ a⟨↑⟩ (var 0)) l ->
  VTyS G (Γ ,, A @ l ,, tyId l A⟨↑⟩ a⟨↑⟩ (var 0) @ l) M M l' ->
  VTmS G Γ c c M[lsingle2 a (tmRefl l A a)] l' ->
  VTmS G Γ (tmJ l l' A a M c a (tmRefl l A a)) c M[lsingle2 a (tmRefl l A a)] l'.
Proof using EL VL VN. intros. eapply (VTmS_trans_diag EP EM (t2 := c)); [s_diag V_J_beta | eassumption]. Qed.

(** The identity type's code (M11b). *)
Lemma VS_code_id {G Γ l l' s s' t t' u u'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTmS G Γ s s' (tyU l) (lsuc l) -> VTmS G Γ t t' (tyEl l s) l -> VTmS G Γ u u' (tyEl l s) l ->
  VTmS G Γ (tmId l s t u) (tmId l' s' t' u') (tyU l) (lsuc l).
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_El_id {G Γ l s t u} : lwf (gL G) l ->
  VTmS G Γ s s (tyU l) (lsuc l) -> VTmS G Γ t t (tyEl l s) l -> VTmS G Γ u u (tyEl l s) l ->
  VTyS G Γ (tyId l (tyEl l s) t u) (tyEl l (tmId l s t u)) l.
Proof using EL VL VN.
  intros Hw Vs Vt Vu. eapply (VTyS_trans_diag EP EM (T2 := tyEl l (tmId l s t u))); [s_diag V_El_id|].
  apply VS_El; [exact Hw | apply lequiv_refl, Hw |].
  apply VS_code_id; [exact Hw | apply lequiv_refl, Hw | exact Vs | exact Vt | exact Vu].
Qed.

(** Strict equality's codes (M10c). *)
Lemma VS_code_seq {G Γ l l' s s' t t' u u'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTmS G Γ s s' (tyU l) (lsuc l) -> VTmS G Γ t t' (tyEl l s) l -> VTmS G Γ u u' (tyEl l s) l ->
  VTmS G Γ (tmSEq l s t u) (tmSEq l' s' t' u') (tyU l) (lsuc l).
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_El_seq {G Γ l s t u} : lwf (gL G) l ->
  VTmS G Γ s s (tyU l) (lsuc l) -> VTmS G Γ t t (tyEl l s) l -> VTmS G Γ u u (tyEl l s) l ->
  VTyS G Γ (tySEq l (tyEl l s) t u) (tyEl l (tmSEq l s t u)) l.
Proof using EL VL VN.
  intros Hw Vs Vt Vu. eapply (VTyS_trans_diag EP EM (T2 := tyEl l (tmSEq l s t u))); [s_diag V_El_seq|].
  apply VS_El; [exact Hw | apply lequiv_refl, Hw |].
  apply VS_code_seq; [exact Hw | apply lequiv_refl, Hw | exact Vs | exact Vt | exact Vu].
Qed.
Lemma VS_code_sempty {G Γ l l'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTmS G Γ (tmSEmpty l) (tmSEmpty l') (tyU l) (lsuc l).
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_El_sempty {G Γ l} : lwf (gL G) l -> VTyS G Γ (tySEmpty l) (tyEl l (tmSEmpty l)) l.
Proof using . intros; s_lift. Qed.

(** The empty type (M12a). *)
Lemma VS_empty {G Γ l l'} : lwf (gL G) l -> lequiv (gL G) l l' -> VTyS G Γ (tyEmpty l) (tyEmpty l') l.
Proof using . intros; s_lift. Qed.
Lemma VS_elimEmpty {ly G Γ l1 l2 l3 l4 M M' t t'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  [ G ; Γ ,, tyEmpty l2 @ l2 ⊢[ ly ] M @ l1 ] -> lle ly ge_layer -> typeof ly = ly ->
  VTyS G (Γ ,, tyEmpty l2 @ l2) M M' l1 -> VTmS G Γ t t' (tyEmpty l2) l2 ->
  VTmS G Γ (elimEmpty l1 l2 M t) (elimEmpty l3 l4 M' t') M[lsingle t] l1.
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_empty_irr {G Γ l t t'} : lwf (gL G) l ->
  VTmS G Γ t t (tyEmpty l) l -> VTmS G Γ t' t' (tyEmpty l) l -> VTmS G Γ t t' (tyEmpty l) l.
Proof using EL VL. intros; s_lift. Qed.

(** Binary sums (M12b). *)
Lemma VS_sum {G Γ l1 l2 l3 l4 A A' B B'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  VTyS G Γ A A' l1 -> VTyS G Γ B B' l2 -> VTyS G Γ (tySum l1 l2 A B) (tySum l3 l4 A' B') (lmax l1 l2).
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_inl {G Γ l1 l2 l3 l4 A A' B B' a a'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  VTyS G Γ A A' l1 -> VTyS G Γ B B' l2 -> VTmS G Γ a a' A l1 ->
  VTmS G Γ (tmInl l1 l2 A B a) (tmInl l3 l4 A' B' a') (tySum l1 l2 A B) (lmax l1 l2).
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_inr {G Γ l1 l2 l3 l4 A A' B B' b b'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  VTyS G Γ A A' l1 -> VTyS G Γ B B' l2 -> VTmS G Γ b b' B l2 ->
  VTmS G Γ (tmInr l1 l2 A B b) (tmInr l3 l4 A' B' b') (tySum l1 l2 A B) (lmax l1 l2).
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_case {G Γ l1 l2 l3 l4 l5 l6 A A' B B' M M' c1 c1' c2 c2' t t'} :
  lwf (gL G) l1 -> lwf (gL G) l2 -> lwf (gL G) l3 ->
  lequiv (gL G) l1 l4 -> lequiv (gL G) l2 l5 -> lequiv (gL G) l3 l6 ->
  VTyS G Γ A A' l1 -> VTyS G Γ B B' l2 -> VTyS G (Γ ,, tySum l1 l2 A B @ lmax l1 l2) M M' l3 ->
  VTmS G (Γ ,, A @ l1) c1 c1' M⟨rlift ↑⟩[lsingle (tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] l3 ->
  VTmS G (Γ ,, B @ l2) c2 c2' M⟨rlift ↑⟩[lsingle (tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] l3 ->
  VTmS G Γ t t' (tySum l1 l2 A B) (lmax l1 l2) ->
  VTmS G Γ (tmCase l1 l2 l3 A B M c1 c2 t) (tmCase l4 l5 l6 A' B' M' c1' c2' t') M[lsingle t] l3.
Proof using EL VL VN. intros; s_lift. Qed.
Lemma VS_case_inl {ly G Γ l l' l'' A B M c1 c2 a} : lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) l'' ->
  [ G ; Γ ⊢[ ly ] A @ l ] -> [ G ; Γ ⊢[ ly ] B @ l' ] -> lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A l -> VTyS G Γ B B l' -> VTyS G (Γ ,, tySum l l' A B @ lmax l l') M M l'' ->
  VTmS G (Γ ,, A @ l) c1 c1 M⟨rlift ↑⟩[lsingle (tmInl l l' A⟨↑⟩ B⟨↑⟩ (var 0))] l'' ->
  VTmS G (Γ ,, B @ l') c2 c2 M⟨rlift ↑⟩[lsingle (tmInr l l' A⟨↑⟩ B⟨↑⟩ (var 0))] l'' ->
  VTmS G Γ a a A l ->
  VTmS G Γ (tmCase l l' l'' A B M c1 c2 (tmInl l l' A B a)) c1[lsingle a] M[lsingle (tmInl l l' A B a)] l''.
Proof using EL VL VN.
  intros. eapply (VTmS_trans_diag EP EM (t2 := c1[lsingle a])); [s_diag V_case_inl|].
  rewrite <- (case_inl_single M l l' A B a) by (eapply wf_ty_nf; eassumption).
  eapply VTmS_single; eassumption.
Qed.
Lemma VS_case_inr {ly G Γ l l' l'' A B M c1 c2 b} : lwf (gL G) l -> lwf (gL G) l' -> lwf (gL G) l'' ->
  [ G ; Γ ⊢[ ly ] A @ l ] -> [ G ; Γ ⊢[ ly ] B @ l' ] -> lle ly ge_layer -> typeof ly = ly ->
  VTyS G Γ A A l -> VTyS G Γ B B l' -> VTyS G (Γ ,, tySum l l' A B @ lmax l l') M M l'' ->
  VTmS G (Γ ,, A @ l) c1 c1 M⟨rlift ↑⟩[lsingle (tmInl l l' A⟨↑⟩ B⟨↑⟩ (var 0))] l'' ->
  VTmS G (Γ ,, B @ l') c2 c2 M⟨rlift ↑⟩[lsingle (tmInr l l' A⟨↑⟩ B⟨↑⟩ (var 0))] l'' ->
  VTmS G Γ b b B l' ->
  VTmS G Γ (tmCase l l' l'' A B M c1 c2 (tmInr l l' A B b)) c2[lsingle b] M[lsingle (tmInr l l' A B b)] l''.
Proof using EL VL VN.
  intros. eapply (VTmS_trans_diag EP EM (t2 := c2[lsingle b])); [s_diag V_case_inr|].
  rewrite <- (case_inr_single M l l' A B b) by (eapply wf_ty_nf; eassumption).
  eapply VTmS_single; eassumption.
Qed.

(** The codes of Empty and + (M12c). *)
Lemma VS_code_empty {G Γ l l'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTmS G Γ (tmEmpty l) (tmEmpty l') (tyU l) (lsuc l).
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_El_empty {G Γ l} : lwf (gL G) l -> VTyS G Γ (tyEmpty l) (tyEl l (tmEmpty l)) l.
Proof using . intros; s_lift. Qed.
Lemma VS_code_sum {G Γ l1 l2 l3 l4 s s' t t'} : lwf (gL G) l1 -> lwf (gL G) l2 ->
  lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  VTmS G Γ s s' (tyU l1) (lsuc l1) -> VTmS G Γ t t' (tyU l2) (lsuc l2) ->
  VTmS G Γ (tmSum l1 l2 s t) (tmSum l3 l4 s' t') (tyU (lmax l1 l2)) (lsuc (lmax l1 l2)).
Proof using EL VL. intros; s_lift. Qed.
Lemma VS_El_sum {G Γ l l' s t} : lwf (gL G) l -> lwf (gL G) l' ->
  VTmS G Γ s s (tyU l) (lsuc l) -> VTmS G Γ t t (tyU l') (lsuc l') ->
  VTyS G Γ (tySum l l' (tyEl l s) (tyEl l' t)) (tyEl (lmax l l') (tmSum l l' s t)) (lmax l l').
Proof using EL VL VN.
  intros Hw Hw' Vs Vt. eapply (VTyS_trans_diag EP EM (T2 := tyEl (lmax l l') (tmSum l l' s t))); [s_diag V_El_sum|].
  apply VS_El; [exact (lwf_max Hw Hw') | apply lequiv_refl, lwf_max; assumption |].
  apply VS_code_sum; [exact Hw | exact Hw' | apply lequiv_refl, Hw | apply lequiv_refl, Hw' | exact Vs | exact Vt].
Qed.

End Rules.

End RulesS.
