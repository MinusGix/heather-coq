(** * Level permutations of syntax and judgments (M3_DESIGN.md E14)

    A permutation [π] of the level variables with inverse [πi], fixing
    every variable from [gL G] up ([uperm]), acts as the universe
    substitution [pφ π]. On deep-normal syntax [πi] undoes [π]; the
    action commutes with local and global renaming, so Kripke worlds can
    be pushed forward along [π] and pulled back along [πi]. *)
From DeLaM.Typing Require Export GWeakening.

Definition pφ (π : nat -> nat) : nat -> lvl := fun n => lvar (π n).

Lemma uperm_usub_ok {π πi L} : uperm π πi L -> usub_ok (pφ π) L L.
Proof. intros H; apply usub_ok_ren, (uperm_ok _ _ _ H). Qed.
Lemma uperm_usub_ok_inv {π πi L} : uperm π πi L -> usub_ok (pφ πi) L L.
Proof. intros H; exact (uperm_usub_ok (uperm_inv _ _ _ H)). Qed.

(** ** Round trips *)

Section RT.
Context {π πi : nat -> nat} (Hinv : forall n, πi (π n) = n).

Lemma rt_comp n : lvsubst (pφ π n) (pφ πi) = lvar n.
Proof. unfold pφ; cbn. now rewrite Hinv. Qed.

Lemma rt_lvl l : lvsubst (lvsubst l (pφ π)) (pφ πi) = l.
Proof. rewrite (lvsubst_lvsubst l _ _ lvar) by (intros; symmetry; apply rt_comp). apply lvsubst_id; auto. Qed.
Lemma rt_ty (T : ty) : dnfty T -> T[pφ π]ᵤ[pφ πi]ᵤ = T.
Proof.
  intros H. rewrite (usubst_usubst_ty T _ _ lvar) by (intros; symmetry; apply rt_comp).
  apply usubst_id_ty; auto.
Qed.
Lemma rt_tm (t : tm) : dnftm t -> t[pφ π]ᵤ[pφ πi]ᵤ = t.
Proof.
  intros H. rewrite (usubst_usubst t _ _ lvar) by (intros; symmetry; apply rt_comp).
  apply usubst_id; auto.
Qed.
Lemma rt_ctx (Γ : ctx) : dnfctx Γ -> Γ[pφ π]ᵤ[pφ πi]ᵤ = Γ.
Proof.
  intros H. rewrite (usubst_usubst_ctx Γ _ _ lvar) by (intros; symmetry; apply rt_comp).
  apply usubst_id_ctx; auto.
Qed.

Lemma rt_gdecl D : dnf_decl D -> gdecl_usubst (gdecl_usubst D (pφ π)) (pφ πi) = D.
Proof.
  destruct D; cbn; intros H; f_equal; rewrite ?rt_lvl; try reflexivity;
    first [apply rt_ctx | apply rt_ty]; tauto.
Qed.

Lemma rt_gdecls Ψ : Forall dnf_decl Ψ ->
  map (fun D => gdecl_usubst D (pφ πi)) (map (fun D => gdecl_usubst D (pφ π)) Ψ) = Ψ.
Proof. induction 1; cbn; f_equal; auto using rt_gdecl. Qed.

End RT.

(** Declarations of a well-formed global context are deep-normal. *)
Lemma wfg_dnf G : [ ⊢ G ] -> Forall dnf_decl (gΨ G).
Proof.
  induction 1; cbn; constructor; auto; cbn;
    first [ exact I | eapply wf_ctx_dnf; eassumption
          | split; [eapply wf_ty_dnf_ctx; eassumption | eapply wf_ty_dnf; eassumption] ].
Qed.

Lemma rt_gctx {π πi} (Hinv : forall n, πi (π n) = n) G : [ ⊢ G ] ->
  G_us (G_us G (gL G) (pφ π)) (gL G) (pφ πi) = G.
Proof.
  intros HG. destruct G as [L Ψ]. unfold G_us, gctx_usubst; cbn. f_equal.
  exact (rt_gdecls Hinv Ψ (wfg_dnf _ HG)).
Qed.

(** ** Commutations *)

Lemma usubst_gwa_ty (T : ty) γ φ : T⟦γ⟧[φ]ᵤ = T[φ]ᵤ⟦γ⟧.
Proof. destruct γ; cbn [gwa]; [reflexivity | apply usubst_gren_ty ..]. Qed.
Lemma usubst_gwa_tm (t : tm) γ φ : t⟦γ⟧[φ]ᵤ = t[φ]ᵤ⟦γ⟧.
Proof. destruct γ; cbn [gwa]; [reflexivity | apply usubst_gren ..]. Qed.
Lemma usubst_gwa_ctx (Γ : ctx) γ φ : Γ⟦γ⟧[φ]ᵤ = Γ[φ]ᵤ⟦γ⟧.
Proof. destruct γ; cbn [gwa]; [reflexivity | apply usubst_gren_ctx ..]. Qed.

Lemma gwk_wf_usubst γ Ψ' Ψ φ : gwk_wf γ Ψ' Ψ ->
  gwk_wf γ (map (fun D => gdecl_usubst D φ) Ψ') (map (fun D => gdecl_usubst D φ) Ψ).
Proof. induction 1; cbn; rewrite ?gdecl_ren_usubst; now constructor. Qed.

Lemma wk_wf_usubst (r : wk) Δ Γ φ : r : Δ ≤ Γ -> r : Δ[φ]ᵤ ≤ Γ[φ]ᵤ.
Proof.
  induction 1; cbn [usubst USubst_ctx ucsubst]; change (usubst_ty ?A ?φ) with A[φ]ᵤ;
    change (ucsubst ?A ?φ) with A[φ]ᵤ; try rewrite usubst_ren_ty; now constructor.
Qed.

(** ** Judgments along a permutation *)

Section Along.
Context {π πi : nat -> nat} {G : gctx} (Hp : uperm π πi (gL G)).
Let Hφ := uperm_usub_ok Hp.

Lemma p_ctx {i Γ} : [ G ; Γ ⊢[ i ] ] -> [ G_us G (gL G) (pφ π) ; Γ[pφ π]ᵤ ⊢[ i ] ].
Proof. intros H; exact (proj1 (proj2 usubstitution) _ _ _ H _ _ Hφ). Qed.
Lemma p_ty {i Γ T l} : [ G ; Γ ⊢[ i ] T @ l ] ->
  [ G_us G (gL G) (pφ π) ; Γ[pφ π]ᵤ ⊢[ i ] T[pφ π]ᵤ @ lvsubst l (pφ π) ].
Proof. intros H; exact (proj1 (proj2 (proj2 usubstitution)) _ _ _ _ _ H _ _ Hφ). Qed.
Lemma p_tm {i Γ t T l} : [ G ; Γ ⊢[ i ] t : T @ l ] ->
  [ G_us G (gL G) (pφ π) ; Γ[pφ π]ᵤ ⊢[ i ] t[pφ π]ᵤ : T[pφ π]ᵤ @ lvsubst l (pφ π) ].
Proof. intros H; exact (proj1 (proj2 (proj2 (proj2 usubstitution))) _ _ _ _ _ _ H _ _ Hφ). Qed.
Lemma p_eqty {i Γ T T' l} : [ G ; Γ ⊢[ i ] T ≅ T' @ l ] ->
  [ G_us G (gL G) (pφ π) ; Γ[pφ π]ᵤ ⊢[ i ] T[pφ π]ᵤ ≅ T'[pφ π]ᵤ @ lvsubst l (pφ π) ].
Proof. intros H; exact (proj1 (proj2 (proj2 (proj2 (proj2 usubstitution)))) _ _ _ _ _ _ H _ _ Hφ). Qed.
Lemma p_eqtm {i Γ t t' T l} : [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] ->
  [ G_us G (gL G) (pφ π) ; Γ[pφ π]ᵤ ⊢[ i ] t[pφ π]ᵤ ≅ t'[pφ π]ᵤ : T[pφ π]ᵤ @ lvsubst l (pφ π) ].
Proof.
  intros H; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 usubstitution))))) _ _ _ _ _ _ _ H _ _ Hφ).
Qed.
Lemma p_lwf {l} : lwf (gL G) l -> lwf (gL (G_us G (gL G) (pφ π))) (lvsubst l (pφ π)).
Proof. intros H; exact (lwf_lvsubst _ _ _ _ Hφ H). Qed.
Lemma p_lequiv {l l'} : lequiv (gL G) l l' ->
  lequiv (gL (G_us G (gL G) (pφ π))) (lvsubst l (pφ π)) (lvsubst l' (pφ π)).
Proof. intros H; exact (lequiv_lvsubst _ _ _ _ _ Hφ H). Qed.
Lemma p_glob : [ ⊢ G ] -> [ ⊢ G_us G (gL G) (pφ π) ].
Proof. intros H; exact (proj1 usubstitution _ H _ _ Hφ). Qed.

End Along.

(** The permutation's level count only needs to bound its support. *)
Lemma p_gL G L φ : gL (G_us G L φ) = L.
Proof. reflexivity. Qed.

(** ** Scoped syntax only sees its levels (M3_DESIGN.md E14) *)

Lemma lvsubst_ext_lwf L l φ φ' : lwf L l -> (forall n, n < L -> φ n = φ' n) -> lvsubst l φ = lvsubst l φ'.
Proof. intros Hl H; induction l; cbn in *; f_equal; intuition. Qed.

Lemma uup_agree L φ φ' : (forall n, n < L -> φ n = φ' n) -> forall n, n < S L -> uup φ n = uup φ' n.
Proof. intros H [|n] Hn; cbn; [reflexivity | f_equal; apply H; lia]. Qed.

Lemma lwf_us_ext_all :
  (forall T L φ φ', ty_lwf L T -> (forall n, n < L -> φ n = φ' n) -> usubst_ty T φ = usubst_ty T φ') /\
  (forall t L φ φ', tm_lwf L t -> (forall n, n < L -> φ n = φ' n) -> usubst_tm t φ = usubst_tm t φ') /\
  (forall Γ L φ φ', ctx_lwf L Γ -> (forall n, n < L -> φ n = φ' n) -> ucsubst Γ φ = ucsubst Γ φ') /\
  (forall d L φ φ', lsub_lwf L d -> (forall n, n < L -> φ n = φ' n) -> ulsubst d φ = ulsubst d φ').
Proof.
  apply syn_ind; intros; cbn in *; try reflexivity;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    f_equal; eauto using lvsubst_ext_lwf.
  eapply H; [eassumption | apply uup_agree; assumption].
Qed.

Lemma lwf_us_ext_ty {L φ φ' T} : ty_lwf L T -> (forall n, n < L -> φ n = φ' n) -> T[φ]ᵤ = T[φ']ᵤ.
Proof. apply lwf_us_ext_all. Qed.
Lemma lwf_us_ext_tm {L φ φ' t} : tm_lwf L t -> (forall n, n < L -> φ n = φ' n) -> t[φ]ᵤ = t[φ']ᵤ.
Proof. apply lwf_us_ext_all. Qed.
Lemma lwf_us_ext_ctx {L φ φ' Γ} : ctx_lwf L Γ -> (forall n, n < L -> φ n = φ' n) -> Γ[φ]ᵤ = Γ[φ']ᵤ.
Proof. apply lwf_us_ext_all. Qed.
