(** * Instances of [UΠ]'s body (M4_DESIGN.md F2)

    A judgment under [n] fresh levels ([gctx_uwk n G], [Γ⟨ush n⟩ᵤ])
    instantiated at [n] well-formed levels [ls] holds in the original
    scope, by the universe substitution lemma at [uext ls lvar]. The η
    rule's body is the instance at the bound variables [ubvars n] of the
    function weakened by [n] levels. Presuppositions of the new rules. *)
From DeLaM.Syntax Require Export LevelRed.
From DeLaM.Typing Require Export RecPeel.

(** ** The scope at instantiated levels *)

Lemma gdecl_usubst_id D : dnf_decl D -> gdecl_usubst D lvar = D.
Proof.
  intros HD; destruct D; cbn [gdecl_usubst dnf_decl] in *; f_equal.
  all: first [ reflexivity | apply lvsubst_id; reflexivity
             | apply usubst_id_ctx; [tauto | auto] | apply usubst_id_ty; [tauto | auto] ].
Qed.

Lemma G_us_uwk_uext G ls : [ ⊢ G ] -> G_us (gctx_uwk (length ls) G) (gL G) (uext ls lvar) = G.
Proof.
  destruct G as [L Ψ]; intros HG. unfold G_us, gctx_usubst, gctx_uwk; cbn [gL gΨ]. f_equal.
  rewrite map_uren_uext. transitivity (map (fun D => D) Ψ); [| apply map_id].
  apply map_ext_in; intros D HD. apply gdecl_usubst_id, (glob_dnf _ _ HG _ HD).
Qed.

Lemma ctx_uwk_uext (Γ : ctx) ls : dnfctx Γ -> ucsubst Γ⟨ush (length ls)⟩ᵤ (uext ls lvar) = Γ.
Proof.
  intros HΓ. rewrite (proj1 (proj2 (proj2 uren_usubst_all)) _ _ _ lvar) by (intros; symmetry; apply uext_ush).
  apply usubst_id_ctx; auto.
Qed.

Section Inst.
Context {G : gctx} {Γ : ctx} {ls : list lvl} (HG : [ ⊢ G ]) (HΓ : dnfctx Γ)
  (Hls : Forall (lwf (gL G)) ls).
Let Hφ : usub_ok (uext ls lvar) (gL G) (length ls + gL G) := usub_ok_uext _ _ _ _ Hls (usub_ok_id _).

Lemma uinst_ty {i T l} : [ gctx_uwk (length ls) G ; Γ⟨ush (length ls)⟩ᵤ ⊢[ i ] T @ l ] ->
  [ G ; Γ ⊢[ i ] T[uext ls lvar]ᵤ @ lvsubst l (uext ls lvar) ].
Proof.
  intros H. pose proof (proj1 (proj2 (proj2 usubstitution)) _ _ _ _ _ H _ _ Hφ) as X.
  rewrite G_us_uwk_uext, ctx_uwk_uext in X by assumption. exact X.
Qed.
Lemma uinst_tm {i t T l} : [ gctx_uwk (length ls) G ; Γ⟨ush (length ls)⟩ᵤ ⊢[ i ] t : T @ l ] ->
  [ G ; Γ ⊢[ i ] t[uext ls lvar]ᵤ : T[uext ls lvar]ᵤ @ lvsubst l (uext ls lvar) ].
Proof.
  intros H. pose proof (proj1 (proj2 (proj2 (proj2 usubstitution))) _ _ _ _ _ _ H _ _ Hφ) as X.
  rewrite G_us_uwk_uext, ctx_uwk_uext in X by assumption. exact X.
Qed.
Lemma uinst_eqty {i T T' l} : [ gctx_uwk (length ls) G ; Γ⟨ush (length ls)⟩ᵤ ⊢[ i ] T ≅ T' @ l ] ->
  [ G ; Γ ⊢[ i ] T[uext ls lvar]ᵤ ≅ T'[uext ls lvar]ᵤ @ lvsubst l (uext ls lvar) ].
Proof.
  intros H. pose proof (proj1 (proj2 (proj2 (proj2 (proj2 usubstitution)))) _ _ _ _ _ _ H _ _ Hφ) as X.
  rewrite G_us_uwk_uext, ctx_uwk_uext in X by assumption. exact X.
Qed.
Lemma uinst_eqtm {i t t' T l} : [ gctx_uwk (length ls) G ; Γ⟨ush (length ls)⟩ᵤ ⊢[ i ] t ≅ t' : T @ l ] ->
  [ G ; Γ ⊢[ i ] t[uext ls lvar]ᵤ ≅ t'[uext ls lvar]ᵤ : T[uext ls lvar]ᵤ @ lvsubst l (uext ls lvar) ].
Proof.
  intros H.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 usubstitution))))) _ _ _ _ _ _ _ H _ _ Hφ) as X.
  rewrite G_us_uwk_uext, ctx_uwk_uext in X by assumption. exact X.
Qed.
End Inst.

(** Equivalent level lists give equivalent instances. *)
Lemma lequivs_lwf_r L ls ls' : Forall2 (lequiv L) ls ls' -> Forall (lwf L) ls'.
Proof. induction 1; constructor; eauto using lequiv_wf_r. Qed.
Lemma lequivs_lwf_l L ls ls' : Forall2 (lequiv L) ls ls' -> Forall (lwf L) ls.
Proof. induction 1; constructor; eauto using lequiv_wf_l. Qed.
Lemma lequivs_leqv L ls ls' : Forall2 (lequiv L) ls ls' -> Forall2 leqv ls ls'.
Proof. induction 1; constructor; eauto using lequiv_leqv. Qed.

Lemma lequiv_uinst L l ls ls' : lwf (length ls + L) l -> Forall2 (lequiv L) ls ls' ->
  lequiv L (lvsubst l (uext ls lvar)) (lvsubst l (uext ls' lvar)).
Proof.
  intros Hl H. apply leqv_lequiv.
  - eapply lwf_lvsubst; [exact (usub_ok_uext _ _ _ _ (lequivs_lwf_l _ _ _ H) (usub_ok_id _)) | exact Hl].
  - rewrite (Forall2_length H) in Hl.
    eapply lwf_lvsubst; [exact (usub_ok_uext _ _ _ _ (lequivs_lwf_r _ _ _ H) (usub_ok_id _)) | exact Hl].
  - apply leqv_lvsubst; [apply leqv_refl | apply leqv_uext, (lequivs_leqv _ _ _ H)].
Qed.

(** ** η: the bound variables *)

Lemma uext_ubvars n φ i : i < n -> uext (ubvars n) φ i = lvar i.
Proof.
  intros Hi. unfold uext. rewrite ubvars_length. destruct (Nat.ltb_spec i n); [|lia].
  unfold ubvars. rewrite (nth_indep _ _ (lvar 0)) by (rewrite length_map, length_rev, length_seq; lia).
  rewrite map_nth, rev_nth by (rewrite length_seq; lia). rewrite length_seq, seq_nth by lia.
  f_equal; lia.
Qed.

Lemma lwfs_ubvars n L : Forall (lwf (n + L)) (ubvars n).
Proof.
  unfold ubvars. apply Forall_map, Forall_forall. intros i Hi. apply in_rev, in_seq in Hi. cbn; lia.
Qed.

Lemma uuprn_lt n ρ i : i < n -> uuprn n ρ i = i.
Proof.
  revert i; induction n; intros i Hi; [lia|]. unfold uuprn in *; rewrite Nat.iter_succ.
  destruct i; cbn [uupr]; [reflexivity|]. f_equal; apply IHn; lia.
Qed.
Lemma uuprn_ge n ρ i : uuprn n ρ (n + i) = n + ρ i.
Proof. induction n; [reflexivity|]. unfold uuprn in *; rewrite Nat.iter_succ. cbn [Nat.add uupr]. now rewrite IHn. Qed.

Lemma ueta_var n i : uext (ubvars n) lvar (uuprn n (ush n) i) = lvar i.
Proof.
  destruct (Nat.ltb_spec i n) as [Hi | Hi].
  - rewrite uuprn_lt by exact Hi. apply uext_ubvars, Hi.
  - replace i with (n + (i - n)) by lia. rewrite uuprn_ge. unfold ush.
    pose proof (uext_ush (ubvars n) lvar (n + (i - n))) as E. rewrite ubvars_length in E. exact E.
Qed.

Lemma ueta_ty n (T : ty) : dnfty T -> T⟨uuprn n (ush n)⟩ᵤ[uext (ubvars n) lvar]ᵤ = T.
Proof.
  intros HT. rewrite (proj1 uren_usubst_all _ _ _ lvar) by (intros; symmetry; apply ueta_var).
  apply usubst_id_ty; auto.
Qed.
Lemma ueta_lvl n l : lvsubst (lvren l (uuprn n (ush n))) (uext (ubvars n) lvar) = l.
Proof. rewrite (lvren_lvsubst _ _ _ lvar) by (intros; symmetry; apply ueta_var). apply lvsubst_id; auto. Qed.

(** ** Universe weakening under the binder *)

Lemma uwk_under_ok n L : uren_ok (uuprn n (ush n)) (n + (n + L)) (n + L).
Proof.
  intros i Hi. destruct (Nat.ltb_spec i n).
  - rewrite uuprn_lt; lia.
  - replace i with (n + (i - n)) by lia. rewrite uuprn_ge. unfold ush; lia.
Qed.

Lemma uwk_under_scope n G (Γ : ctx) :
  G_us (gctx_uwk n G) (n + (n + gL G)) (uupn n (fun j => lvar (ush n j))) = gctx_uwk n (gctx_uwk n G) /\
  ucsubst Γ⟨ush n⟩ᵤ (uupn n (fun j => lvar (ush n j))) = Γ⟨ush n⟩ᵤ⟨ush n⟩ᵤ.
Proof.
  split.
  - unfold G_us. rewrite gctx_uwk_usubst, <- gctx_uwk_as. reflexivity.
  - rewrite ucren_ush_usubst, <- uren_ush_ctx. reflexivity.
Qed.

Lemma uwk_under_ty n {G i Γ T l} : [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ i ] T @ l ] ->
  [ gctx_uwk n (gctx_uwk n G) ; Γ⟨ush n⟩ᵤ⟨ush n⟩ᵤ ⊢[ i ] T⟨uuprn n (ush n)⟩ᵤ @ lvren l (uuprn n (ush n)) ].
Proof.
  intros H.
  pose proof (proj1 (proj2 (proj2 usubstitution)) _ _ _ _ _ H (n + (n + gL G))
                (uupn n (fun j => lvar (ush n j))) (usub_ok_uupn _ _ _ _ (usub_ok_ush n (gL G)))) as X.
  destruct (uwk_under_scope n G Γ) as [E1 E2]. rewrite E1, E2 in X.
  rewrite <- (proj1 uren_as_usubst_all T (uuprn n (ush n)) (uupn n (fun j => lvar (ush n j)))) in X
    by (intros; apply uupn_as; reflexivity).
  rewrite <- (lvren_as_lvsubst l (uuprn n (ush n)) (uupn n (fun j => lvar (ush n j)))) in X
    by (intros; apply uupn_as; reflexivity).
  exact X.
Qed.

Lemma uwk_under_tm n {G i Γ t T l} : [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ i ] t : T @ l ] ->
  [ gctx_uwk n (gctx_uwk n G) ; Γ⟨ush n⟩ᵤ⟨ush n⟩ᵤ ⊢[ i ] t⟨uuprn n (ush n)⟩ᵤ : T⟨uuprn n (ush n)⟩ᵤ
    @ lvren l (uuprn n (ush n)) ].
Proof.
  intros H.
  pose proof (proj1 (proj2 (proj2 (proj2 usubstitution))) _ _ _ _ _ _ H (n + (n + gL G))
                (uupn n (fun j => lvar (ush n j))) (usub_ok_uupn _ _ _ _ (usub_ok_ush n (gL G)))) as X.
  destruct (uwk_under_scope n G Γ) as [E1 E2]. rewrite E1, E2 in X.
  rewrite <- (proj1 (proj2 uren_as_usubst_all) t (uuprn n (ush n)) (uupn n (fun j => lvar (ush n j)))) in X
    by (intros; apply uupn_as; reflexivity).
  rewrite <- (proj1 uren_as_usubst_all T (uuprn n (ush n)) (uupn n (fun j => lvar (ush n j)))) in X
    by (intros; apply uupn_as; reflexivity).
  rewrite <- (lvren_as_lvsubst l (uuprn n (ush n)) (uupn n (fun j => lvar (ush n j)))) in X
    by (intros; apply uupn_as; reflexivity).
  exact X.
Qed.

Lemma ueta_tm n (t : tm) : dnftm t -> t⟨uuprn n (ush n)⟩ᵤ[uext (ubvars n) lvar]ᵤ = t.
Proof.
  intros Ht. rewrite (proj1 (proj2 uren_usubst_all) _ _ _ lvar) by (intros; symmetry; apply ueta_var).
  apply usubst_id; auto.
Qed.

(** The bound variables, instantiated. *)
Lemma map_ubvars_uext n ls φ : length ls = n -> map (fun l => lvsubst l (uext ls φ)) (ubvars n) = ls.
Proof.
  intros Hn. apply (nth_ext _ _ lzero lzero).
  - rewrite length_map, ubvars_length; auto.
  - intros k Hk. rewrite length_map, ubvars_length in Hk.
    rewrite (nth_indep _ _ (lvsubst (lvar 0) (uext ls φ))) by (rewrite length_map, ubvars_length; lia).
    pose proof (map_nth (fun l => lvsubst l (uext ls φ)) (ubvars n) (lvar 0) k) as E. cbn beta in E.
    rewrite E. unfold ubvars.
    rewrite map_nth, rev_nth by (rewrite length_seq; lia). rewrite length_seq, seq_nth by lia.
    cbn [lvsubst]. unfold uext. rewrite Hn. destruct (Nat.ltb_spec (0 + (n - S k)) n); [|lia].
    f_equal; lia.
Qed.

(** Levels of context entries and of instances are never ω. *)
Lemma in_ctx_lwf {G i Γ n A k} : [ G ; Γ ⊢[ i ] ] -> in_ctx Γ n A k -> lwf (gL G) k.
Proof.
  intros HΓ H; revert HΓ; induction H as [Γ A l | Γ A l B l' n H IH]; intros HΓ;
    inversion HΓ; subst; auto.
Qed.

Lemma ilv_not_omega L n l ls : lwf (n + L) l -> length ls = n -> Forall (lwf L) ls ->
  lvsubst l (uext ls lvar) <> lomega.
Proof.
  intros Hl Hn Hls. subst n. apply (lwf_not_omega L).
  exact (lwf_lvsubst _ _ _ _ (usub_ok_uext _ _ _ _ Hls (usub_ok_id _)) Hl).
Qed.

(** ** Presuppositions of the new rules *)

Section Presup.
Context {G : gctx} {Γ : ctx}.

Lemma pre_upi_r {n l l' T'} : [ G ; Γ ⊢[ lM ] ] -> 0 < n -> lequiv (n + gL G) l l' ->
  [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] T' @ l ] -> [ G ; Γ ⊢[ lM ] tyUPi n l' T' @ lomega ].
Proof.
  intros HΓ Hn Hl HT. apply wft_upi; [exact HΓ | exact Hn | exact (lequiv_wf_r _ _ _ Hl) |].
  eapply wft_lconv; [exact HT | apply lequiv_sym, Hl].
Qed.

Lemma pre_ulam_r {n l l' T T' t'} : [ G ; Γ ⊢[ lM ] ] -> 0 < n -> lequiv (n + gL G) l l' ->
  [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] T @ l ] -> [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] T' @ l ] ->
  [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] T ≅ T' @ l ] ->
  [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] t' : T @ l ] ->
  [ G ; Γ ⊢[ lM ] ulam n l' T' t' : tyUPi n l T @ lomega ].
Proof.
  intros HΓ Hn Hl HT HT' HTT Ht. eapply wf_conv.
  - apply wf_ulam; [exact HΓ | exact Hn | exact (lequiv_wf_r _ _ _ Hl) | |].
    + eapply wft_lconv; [exact HT' | apply lequiv_sym, Hl].
    + eapply wf_lconv; [| apply lequiv_sym, Hl]. eapply wf_conv; [exact Ht | apply eqty_sym, HTT].
  - apply eqty_upi; [exact HΓ | exact Hn | exact Hl | exact HT | exact HTT].
Qed.

Lemma pre_uapp_l {n l T t ls} : lwf (n + gL G) l -> [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] T @ l ] ->
  length ls = n -> Forall (lwf (gL G)) ls -> [ G ; Γ ⊢[ lM ] t : tyUPi n l T @ lomega ] ->
  [ G ; Γ ⊢[ lM ] T[uext ls lvar]ᵤ @ lvsubst l (uext ls lvar) ].
Proof.
  intros Hl HT Hn Hls Ht. subst n. pose proof (ctx_of_wf_tm (i := lM) eq_refl Ht) as HΓ.
  exact (uinst_ty (ctx_glob _ _ _ HΓ) (wf_ctx_dnf HΓ) Hls HT).
Qed.

Lemma pre_uapp_r {n l T t' ls ls'} : lwf (n + gL G) l -> [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] T @ l ] ->
  length ls = n -> Forall2 (lequiv (gL G)) ls ls' -> [ G ; Γ ⊢[ lM ] t' : tyUPi n l T @ lomega ] ->
  [ G ; Γ ⊢[ lM ] uapp t' ls' : T[uext ls lvar]ᵤ @ lvsubst l (uext ls lvar) ].
Proof.
  intros Hl HT Hn Hls Ht. pose proof (ctx_of_wf_tm (i := lM) eq_refl Ht) as HΓ.
  pose proof (ctx_glob _ _ _ HΓ) as HG. pose proof (wf_ctx_dnf HΓ) as HΓd.
  pose proof (Forall2_length Hls) as Hn'. subst n.
  pose proof (lequivs_lwf_l _ _ _ Hls) as Hw. pose proof (lequivs_lwf_r _ _ _ Hls) as Hw'.
  assert (HT' : [ gctx_uwk (length ls') G ; Γ⟨ush (length ls')⟩ᵤ ⊢[ lM ] T @ l ]) by now rewrite <- Hn'.
  pose proof (lequiv_uinst _ _ _ _ Hl Hls) as E.
  eapply wf_conv.
  - eapply wf_lconv; [| exact E]. apply wf_uapp with (n := length ls'); [rewrite <- Hn'; exact Hl | exact HT' | reflexivity | exact Hw' |].
    rewrite <- Hn'; exact Ht.
  - cbn [typeof]. apply eqty_leq.
    + exact (uinst_ty HG HΓd Hw HT).
    + eapply wft_lconv; [exact (uinst_ty HG HΓd Hw' HT') | exact E].
    + apply (proj1 leq_usubst_all); [apply leqv_uext, (lequivs_leqv _ _ _ Hls) | apply ty_leq_refl].
Qed.

Lemma pre_ubeta_l {n l T t ls} : [ G ; Γ ⊢[ lM ] ] -> 0 < n -> lwf (n + gL G) l ->
  [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] T @ l ] -> [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] t : T @ l ] ->
  length ls = n -> Forall (lwf (gL G)) ls ->
  [ G ; Γ ⊢[ lM ] uapp (ulam n l T t) ls : T[uext ls lvar]ᵤ @ lvsubst l (uext ls lvar) ].
Proof. intros; apply wf_uapp with (n := n); auto. apply wf_ulam; auto. Qed.

Lemma pre_ubeta_r {n l T t ls} : [ G ; Γ ⊢[ lM ] ] ->
  [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] t : T @ l ] -> length ls = n -> Forall (lwf (gL G)) ls ->
  [ G ; Γ ⊢[ lM ] t[uext ls lvar]ᵤ : T[uext ls lvar]ᵤ @ lvsubst l (uext ls lvar) ].
Proof. intros HΓ Ht Hn Hls. subst n. exact (uinst_tm (ctx_glob _ _ _ HΓ) (wf_ctx_dnf HΓ) Hls Ht). Qed.

Lemma pre_ueta_l {n l T t} : 0 < n -> lwf (n + gL G) l ->
  [ gctx_uwk n G ; Γ⟨ush n⟩ᵤ ⊢[ lM ] T @ l ] -> [ G ; Γ ⊢[ lM ] t : tyUPi n l T @ lomega ] ->
  [ G ; Γ ⊢[ lM ] ulam n l T (uapp t⟨ush n⟩ᵤ (ubvars n)) : tyUPi n l T @ lomega ].
Proof.
  intros Hn Hl HT Ht. pose proof (ctx_of_wf_tm (i := lM) eq_refl Ht) as HΓ.
  pose proof (wf_ty_dnf HT) as HTd.
  apply wf_ulam; [exact HΓ | exact Hn | exact Hl | exact HT |].
  pose proof (uwk_tm n Ht) as X. cbn [uren_ty lvren] in X.
  pose proof (uwk_under_ty n HT) as HT2.
  assert (Hl2 : lwf (n + gL (gctx_uwk n G)) (lvren l (uuprn n (ush n))))
    by (eapply lwf_lvren; [apply uwk_under_ok | exact Hl]).
  pose proof (wf_uapp (gctx_uwk n G) (Γ⟨ush n⟩ᵤ) n _ _ _ (ubvars n) Hl2 HT2 (ubvars_length n)
                (lwfs_ubvars n _) X) as Y.
  rewrite ueta_ty, ueta_lvl in Y by exact HTd. exact Y.
Qed.

End Presup.

(** ** Judgment levels

    Every judgment's level is well formed, or ω at layer M (the [UΠ]
    rules, M4_DESIGN.md F2). *)
Theorem judg_lvl :
  (forall G, [ ⊢ G ] -> True) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> True) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> lwf (gL G) l \/ (i = lM /\ l = lomega)) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] -> lwf (gL G) l \/ (i = lM /\ l = lomega)) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] -> lwf (gL G) l \/ (i = lM /\ l = lomega)) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> lwf (gL G) l \/ (i = lM /\ l = lomega)) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> True).
Proof.
  apply typing_mut; intros; auto; try (left; assumption); try (right; split; reflexivity);
    try (left; cbn [lwf]; auto; fail).
  all: try (left; cbn [lwf]; repeat split; first [assumption | eapply lequiv_wf_l; eassumption
                                                  | eapply lequiv_wf_r; eassumption]; fail).
  all: try (left; eapply in_ctx_lwf; eassumption).
  all: try (left; match goal with Hin : in_gctx (gΨ ?G) _ _, Hc : wf_ctx ?G _ _ |- _ =>
              let HD := fresh "HD" in pose proof (gctx_decl_ok _ _ _ (ctx_glob _ _ _ Hc) Hin) as HD;
              cbn [decl_ok] in HD; tauto end).
  all: try (left; eapply lwf_lvsubst;
            [ apply usub_ok_uext; [first [eassumption | eapply lequivs_lwf_l; eassumption] | apply usub_ok_id]
            | try match goal with Hn : length ?ls = ?n |- _ => rewrite Hn end; assumption ]).
  all: try (match goal with IH : lwf _ ?k \/ _, E : lequiv _ _ ?k |- _ => left; eapply lequiv_wf_l; eassumption
                           | IH : lwf _ ?k \/ _, E : lequiv _ ?k _ |- _ => left; eapply lequiv_wf_r; eassumption end).
Qed.
