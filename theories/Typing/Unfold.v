(** * Unfolding every definition preserves every judgment (M9 follow-up)

    [unf] ([Syntax/Unfold.v]) inlines every defined global at every
    occurrence, code included. It sends each judgment under [G] to the same
    judgment, unfolded, under [unf_G G], the global context whose bindings
    are unfolded ([unfolding]). An occurrence [u^δ] carrying the body [t]
    becomes [t[δ]] unfolded: typed by the substitution lemma from the
    carried body's own premise (typed at the use's layer, M9_DESIGN.md N1),
    and its δ-rule becomes reflexivity. Every output is definition-free
    ([unf_gfree]), which is what consistency at M with definitions uses
    ([Validity/ConsistencyDef.v]). *)
From DeLaM.Syntax Require Export Unfold.
From DeLaM.Typing Require Export PresupC.

(** ** Global contexts *)

Definition unf_decl (D : gdecl) : gdecl :=
  match D with
  | gdCtx => gdCtx
  | gdTy Δ i l => gdTy (unf_ctx Δ) i l
  | gdTm Δ i T l => gdTm (unf_ctx Δ) i (unf_ty T) l
  | gdDef Δ T l t => gdDef (unf_ctx Δ) (unf_ty T) l (unf_tm t)
  end.
Definition unf_G (G : gctx) : gctx := mkG (gL G) (map unf_decl (gΨ G)).

Lemma unf_decl_ren D ξ : unf_decl (gdecl_ren D ξ) = gdecl_ren (unf_decl D) ξ.
Proof. destruct D; cbn; f_equal; auto using unf_gren_ctx, unf_gren_ty, unf_gren. Qed.
Lemma unf_decl_uren D ρ : unf_decl (gdecl_uren D ρ) = gdecl_uren (unf_decl D) ρ.
Proof. destruct D; cbn; f_equal; auto using unf_uren_ctx, unf_uren_ty, unf_uren. Qed.

Lemma in_gctx_unf Ψ n D : in_gctx Ψ n D -> in_gctx (map unf_decl Ψ) n (unf_decl D).
Proof. induction 1; cbn; rewrite unf_decl_ren; now constructor. Qed.
Lemma in_gctx_unf_inv Ψ n D : in_gctx (map unf_decl Ψ) n D -> exists D0, in_gctx Ψ n D0 /\ D = unf_decl D0.
Proof.
  revert n D; induction Ψ as [| D1 Ψ IH]; intros n D H; cbn [map] in H; inversion H; subst.
  - exists (gdecl_ren D1 S); split; [constructor | symmetry; apply unf_decl_ren].
  - match goal with Hm : in_gctx (map _ _) _ _ |- _ => destruct (IH _ _ Hm) as (E & HE & ->) end.
    exists (gdecl_ren E S); split; [now constructor | symmetry; apply unf_decl_ren].
Qed.

Lemma gctx_var_unf G g : gctx_var G g -> gctx_var (unf_G G) g.
Proof. unfold gctx_var, unf_G; cbn. intros H. now rewrite nth_error_map, H. Qed.

Lemma unf_G_uwk n G : unf_G (gctx_uwk n G) = gctx_uwk n (unf_G G).
Proof.
  unfold unf_G, gctx_uwk; cbn [gL gΨ]. f_equal.
  rewrite !map_map. apply map_ext; intros; apply unf_decl_uren.
Qed.

(** ** Local contexts *)

Lemma in_ctx_unf Γ n T l : in_ctx Γ n T l -> in_ctx (unf_ctx Γ) n (unf_ty T) l.
Proof. induction 1; cbn [unf_ctx]; rewrite unf_ren_ty; now constructor. Qed.
Lemma in_ctx_unf_inv Γ n T l : in_ctx (unf_ctx Γ) n T l -> exists T0, in_ctx Γ n T0 l /\ T = unf_ty T0.
Proof.
  revert n T l; induction Γ as [| g | Γ IH A k]; intros n T l H; inversion H; subst.
  - exists A⟨↑⟩; split; [apply in_here | symmetry; apply unf_ren_ty].
  - match goal with Hm : in_ctx _ _ _ _ |- _ => destruct (IH _ _ _ Hm) as (T0 & HT0 & ->) end.
    exists T0⟨↑⟩; split; [now apply in_there | symmetry; apply unf_ren_ty].
Qed.

Lemma clen_unf Γ : clen (unf_ctx Γ) = clen Γ.
Proof. induction Γ; cbn; auto. Qed.
Lemma ctx_tail_unf Γ : ctx_tail (unf_ctx Γ) = unf_ctx (ctx_tail Γ).
Proof. induction Γ; cbn; auto. Qed.

Lemma lsub_tail_unf d Δ Γ : lsub_tail d Δ Γ -> lsub_tail (unf_l d) (unf_ctx Δ) (unf_ctx Γ).
Proof.
  intros [Ht Hl]; split.
  - rewrite !ctx_tail_unf; now f_equal.
  - intros n; rewrite !clen_unf, llk_unf, Hl; reflexivity.
Qed.

Lemma cexts_unf Γ As :
  unf_ctx (cexts Γ As) = cexts (unf_ctx Γ) (map (fun '(A, l) => (unf_ty A, l)) As).
Proof. revert Γ; induction As as [|[A l] As IH]; intros Γ; cbn; auto. Qed.

(** ** The recursor specification

    [unf] commutes with peeling a binder, but not with peeling a defined
    global's occurrence (which unfolds into anything): as for local
    substitution ([Substitution.v]), the peels are taken of heads that are
    binders ([hd_ok]), which the bundles' wrappers are by computation. *)

Fixpoint tup_nd (t : tm) : Prop := match t with tmTup _ r => tup_nd r | gdef _ _ _ => False | _ => True end.
Lemma tup_nth_unf t k : tup_nd t -> tup_nth (unf_tm t) k = unf_tm (tup_nth t k).
Proof. revert t; induction k; intros [] H; cbn in *; try contradiction; auto. Qed.

Lemma peelU_unf b l : hd_ok b -> peelU (unf_tm b) l = unf_tm (peelU b l).
Proof. destruct b; cbn [unf_tm peelU]; try contradiction; auto. intros _; symmetry; apply unf_usubst. Qed.
Lemma peelG_unf b o : hd_ok b -> peelG (unf_tm b) (unf_o o) = unf_tm (peelG b o).
Proof. destruct b; cbn [unf_tm peelG]; try contradiction; auto. intros _; symmetry; apply unf_gsingle. Qed.
Lemma unf_lsingle a : unf_l (lsingle a) = lsingle (unf_tm a).
Proof. reflexivity. Qed.
Lemma peelL_unf b a : hd_ok b -> peelL (unf_tm b) (unf_tm a) = unf_tm (peelL b a).
Proof.
  destruct b; cbn [unf_tm peelL]; try contradiction; auto. intros _. rewrite unf_subst, unf_lsingle. reflexivity.
Qed.

Lemma getTy_unf t : hd_ok t -> unf_ty (getTy t) = getTy (unf_tm t).
Proof. destruct t; cbn; try contradiction; reflexivity. Qed.

Lemma motT_unf w lv g c : hd_ok w -> hd_ok (peelU w lv) -> hd_ok (peelG (peelU w lv) (GCtx g)) ->
  hd_ok (peelL (peelG (peelU w lv) (GCtx g)) c) ->
  unf_ty (motT w lv g c) = motT (unf_tm w) lv (unf_ctx g) (unf_tm c).
Proof.
  intros H1 H2 H3 H4. unfold motT. rewrite getTy_unf, <- peelL_unf by assumption.
  change (GCtx (unf_ctx g)) with (unf_o (GCtx g)). rewrite <- peelG_unf, <- peelU_unf by assumption.
  reflexivity.
Qed.
Lemma mott_unf w lv g U c : hd_ok w -> hd_ok (peelU w lv) -> hd_ok (peelG (peelU w lv) (GCtx g)) ->
  hd_ok (peelG (peelG (peelU w lv) (GCtx g)) (GTy U)) ->
  hd_ok (peelL (peelG (peelG (peelU w lv) (GCtx g)) (GTy U)) c) ->
  unf_ty (mott w lv g U c) = mott (unf_tm w) lv (unf_ctx g) (unf_ty U) (unf_tm c).
Proof.
  intros H1 H2 H3 H4 H5. unfold mott. rewrite getTy_unf, <- peelL_unf by assumption.
  change (GTy (unf_ty U)) with (unf_o (GTy U)). change (GCtx (unf_ctx g)) with (unf_o (GCtx g)).
  rewrite <- !peelG_unf, <- peelU_unf by assumption. reflexivity.
Qed.

Lemma wkb_unf nu ng nl w : unf_tm (wkb nu ng nl w) = wkb nu ng nl (unf_tm w).
Proof. unfold wkb. now rewrite unf_ren, unf_gren, unf_uren. Qed.
Lemma wkc_unf nu ng Γ : unf_ctx (wkc nu ng Γ) = wkc nu ng (unf_ctx Γ).
Proof. unfold wkc. now rewrite unf_gren_ctx, unf_uren_ctx. Qed.

Lemma wrapU_unf n b : unf_tm (wrapU n b) = wrapU n (unf_tm b).
Proof. induction n; cbn; congruence. Qed.
Lemma wrapG_unf n b : unf_tm (wrapG n b) = wrapG n (unf_tm b).
Proof. induction n; cbn; congruence. Qed.
Lemma wrapL_unf n b : unf_tm (wrapL n b) = wrapL n (unf_tm b).
Proof. induction n; cbn; congruence. Qed.
Lemma wrap_unf nu ng nl b : unf_tm (wrap nu ng nl b) = wrap nu ng nl (unf_tm b).
Proof. unfold wrap. now rewrite wrapU_unf, wrapG_unf, wrapL_unf. Qed.

Lemma mkrb_unf MT Mt bs :
  unf_tm (mkrb MT Mt bs) = mkrb (unf_ty MT) (unf_ty Mt) (fun k => unf_tm (bs k)).
Proof. unfold mkrb. cbn [tup_from unf_tm br_ar]. rewrite !wrap_unf. reflexivity. Qed.
Lemma wrapMT_unf MT : unf_tm (wrapMT MT) = wrapMT (unf_ty MT).
Proof. reflexivity. Qed.
Lemma wrapMt_unf Mt : unf_tm (wrapMt Mt) = wrapMt (unf_ty Mt).
Proof. reflexivity. Qed.

Ltac unf_rec_rw :=
  rewrite ?motT_unf, ?mott_unf by hd_tac; rewrite ?wkb_unf.

(** The motive instances at a wrapped motive. *)
Lemma motT_wrap_unf MT lv g c : unf_ty (motT (wrapMT MT) lv g c) = motT (wrapMT (unf_ty MT)) lv (unf_ctx g) (unf_tm c).
Proof. unf_rec_rw. reflexivity. Qed.
Lemma mott_wrap_unf Mt lv g U c :
  unf_ty (mott (wrapMt Mt) lv g U c) = mott (wrapMt (unf_ty Mt)) lv (unf_ctx g) (unf_ty U) (unf_tm c).
Proof. unf_rec_rw. reflexivity. Qed.

(** The branch scopes: the branch declarations and the recursive calls'
    code mention no definition, so [unf] fixes them by computation. *)
Lemma brDecls_unf k : k < nbr -> map unf_decl (brDecls k) = brDecls k.
Proof. intros Hk. br_all ltac:(destruct k; [reflexivity|]); lia. Qed.

Lemma brG_unf k G : k < nbr -> unf_G (brG k G) = brG k (unf_G G).
Proof.
  intros Hk. unfold brG, unf_G, gctx_uwk; cbn [gL gΨ]. f_equal.
  rewrite map_app, brDecls_unf by auto. f_equal.
  rewrite !map_map. apply map_ext; intros; apply unf_decl_uren.
Qed.

Lemma brLocs_unf k MT Mt a1 a2 : k < nbr ->
  map (fun '(A, l) => (unf_ty A, l)) (brLocs k (wrapMT MT) (wrapMt Mt) a1 a2) =
  brLocs k (wrapMT (unf_ty MT)) (wrapMt (unf_ty Mt)) a1 a2.
Proof.
  intros Hk. br_all ltac:(destruct k;
    [cbn [brLocs map br_nu br_ar mkLocs call_ty call_lv br_calls br_ng]; unf_rec_rw; reflexivity|]).
  lia.
Qed.

Lemma brΓ_unf k Γ MT Mt l1 l2 : k < nbr ->
  unf_ctx (brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2) =
  brΓ k (unf_ctx Γ) (wrapMT (unf_ty MT)) (wrapMt (unf_ty Mt)) l1 l2.
Proof. intros Hk. unfold brΓ. now rewrite cexts_unf, wkc_unf, brLocs_unf. Qed.

Lemma brRes_unf k MT Mt : k < nbr ->
  unf_ty (brRes k (wrapMT MT) (wrapMt Mt)) = brRes k (wrapMT (unf_ty MT)) (wrapMt (unf_ty Mt)).
Proof.
  intros Hk. br_all ltac:(destruct k;
    [cbn [brRes br_nu br_ar call_ty br_head br_ng br_nl]; unf_rec_rw; reflexivity|]).
  lia.
Qed.

Lemma recGT_unf G : unf_G (recGT G) = recGT (unf_G G).
Proof.
  unfold recGT, unf_G, gctx_uwk; cbn [gL gΨ map unf_decl]. f_equal. f_equal.
  rewrite !map_map. apply map_ext; intros; apply unf_decl_uren.
Qed.
Lemma recGt_unf G : unf_G (recGt G) = recGt (unf_G G).
Proof.
  unfold recGt, unf_G, gctx_uwk; cbn [gL gΨ map unf_decl]. f_equal. f_equal. f_equal.
  rewrite !map_map. apply map_ext; intros; apply unf_decl_uren.
Qed.
Lemma recΓT_unf Γ : unf_ctx (recΓT Γ) = recΓT (unf_ctx Γ).
Proof. unfold recΓT; cbn [unf_ctx]. now rewrite wkc_unf. Qed.
Lemma recΓt_unf Γ : unf_ctx (recΓt Γ) = recΓt (unf_ctx Γ).
Proof. unfold recΓt; cbn [unf_ctx]. now rewrite wkc_unf. Qed.

(** The single local substitutions of the rules. *)
Lemma unf_lsingle2 a b : unf_l (lsingle2 a b) = lsingle2 (unf_tm a) (unf_tm b).
Proof. reflexivity. Qed.
Lemma unf_lsingle3 a b c : unf_l (lsingle3 a b c) = lsingle3 (unf_tm a) (unf_tm b) (unf_tm c).
Proof. reflexivity. Qed.
Lemma unf_lsucc : unf_l lsucc = lsucc.
Proof. reflexivity. Qed.
Lemma unf_lsingle_ty M a : unf_ty (subst_ty M (lsingle a)) = subst_ty (unf_ty M) (lsingle (unf_tm a)).
Proof. now rewrite unf_subst_ty, unf_lsingle. Qed.
Lemma unf_lsingle2_ty M a b :
  unf_ty (subst_ty M (lsingle2 a b)) = subst_ty (unf_ty M) (lsingle2 (unf_tm a) (unf_tm b)).
Proof. now rewrite unf_subst_ty, unf_lsingle2. Qed.
Lemma unf_lsucc_ty M : unf_ty (subst_ty M lsucc) = subst_ty (unf_ty M) lsucc.
Proof. now rewrite unf_subst_ty, unf_lsucc. Qed.
Lemma unf_lsingle_tm b a : unf_tm (subst_tm b (lsingle a)) = subst_tm (unf_tm b) (lsingle (unf_tm a)).
Proof. now rewrite unf_subst, unf_lsingle. Qed.
Lemma unf_lsingle2_tm b a c :
  unf_tm (subst_tm b (lsingle2 a c)) = subst_tm (unf_tm b) (lsingle2 (unf_tm a) (unf_tm c)).
Proof. now rewrite unf_subst, unf_lsingle2. Qed.
Lemma unf_lsingle3_tm b a c e :
  unf_tm (subst_tm b (lsingle3 a c e)) = subst_tm (unf_tm b) (lsingle3 (unf_tm a) (unf_tm c) (unf_tm e)).
Proof. now rewrite unf_subst, unf_lsingle3. Qed.

Lemma unf_wIH l l' l'' A B M c a f :
  unf_tm (wIH l l' l'' A B M c a f) =
  wIH l l' l'' (unf_ty A) (unf_ty B) (unf_ty M) (unf_tm c) (unf_tm a) (unf_tm f).
Proof.
  unfold wIH; cbn [unf_tm unf_ty].
  rewrite ?unf_ren_ty, ?unf_ren, ?unf_lsingle_ty. cbn [unf_ty]. reflexivity.
Qed.

Lemma unf_tmNth l T k cs j :
  unf_tm (tmNth l T k cs j) = tmNth l (unf_ty T) (unf_tm k) (unf_tm cs) (unf_tm j).
Proof.
  unfold tmNth, nthMot, nthBase, nthStep; cbn [unf_tm unf_ty].
  rewrite ?unf_ren_ty, ?unf_ren. reflexivity.
Qed.
Lemma unf_wfIH l l' A N M c a cs :
  unf_tm (wfIH l l' A N M c a cs) =
  wfIH l l' (unf_ty A) (unf_tm N) (unf_ty M) (unf_tm c) (unf_tm a) (unf_tm cs).
Proof.
  unfold wfIH; cbn [unf_tm unf_ty].
  rewrite ?unf_ren_ty, ?unf_ren, ?unf_lsingle, ?unf_subst, unf_tmNth. cbn [unf_ty].
  rewrite ?unf_ren_ty, ?unf_ren, ?unf_lsingle, ?unf_subst. reflexivity.
Qed.

(** [dnth] and [elim_IWf]'s induction hypothesis (M17b). *)
Lemma unf_tmDNth l n F cs j :
  unf_tm (tmDNth l n F cs j) = tmDNth l (unf_tm n) (unf_ty F) (unf_tm cs) (unf_tm j).
Proof.
  unfold tmDNth, dnthMot, dnthBase, dnthStep, dnthEmb, dnthFam, dnthRes, dnthFamS; cbn [unf_tm unf_ty].
  repeat progress (rewrite ?unf_ren_ty, ?unf_ren, ?unf_subst_ty, ?unf_lsingle; cbn [unf_tm unf_ty]).
  reflexivity.
Qed.
Lemma unf_iwfFam l li X A N Ot C a :
  unf_ty (iwfFam l li X A N Ot C a) =
  iwfFam l li (unf_ty X) (unf_ty A) (unf_tm N) (unf_tm Ot) (unf_tm C) (unf_tm a).
Proof.
  unfold iwfFam; cbn [unf_ty]. rewrite ?unf_ren_ty, ?unf_ren, ?unf_subst, ?unf_llift, ?unf_lsingle. reflexivity.
Qed.
Lemma unf_iwfIH l li l' X A N Ot C M c a cs :
  unf_tm (iwfIH l li l' X A N Ot C M c a cs) =
  iwfIH l li l' (unf_ty X) (unf_ty A) (unf_tm N) (unf_tm Ot) (unf_tm C) (unf_ty M) (unf_tm c) (unf_tm a) (unf_tm cs).
Proof.
  unfold iwfIH; cbn [unf_tm unf_ty].
  rewrite ?unf_ren_ty, ?unf_ren, ?unf_lsingle, ?unf_subst, ?unf_llift, unf_tmDNth. cbn [unf_ty].
  rewrite ?unf_ren_ty, ?unf_ren, ?unf_lsingle, ?unf_subst, unf_iwfFam. reflexivity.
Qed.

(** [elim_IWi]'s (M19a). *)
Lemma unf_iwiFamCod l lp li X A N D Ot C a :
  unf_ty (iwiFamCod l lp li X A N D Ot C a) =
  iwiFamCod l lp li (unf_ty X) (unf_ty A) (unf_tm N) (unf_ty D) (unf_tm Ot) (unf_tm C) (unf_tm a).
Proof.
  unfold iwiFamCod; cbn [unf_ty]. rewrite ?unf_ren_ty, ?unf_ren, ?unf_subst, ?unf_llift, ?unf_lsingle. reflexivity.
Qed.
Lemma unf_iwiFam l lp li X A N D Ot C a :
  unf_ty (iwiFam l lp li X A N D Ot C a) =
  iwiFam l lp li (unf_ty X) (unf_ty A) (unf_tm N) (unf_ty D) (unf_tm Ot) (unf_tm C) (unf_tm a).
Proof.
  unfold iwiFam; cbn [unf_ty]. rewrite ?unf_subst_ty, ?unf_llift, ?unf_lsingle, unf_iwiFamCod. reflexivity.
Qed.
Lemma unf_iwiIH l lp li l' X A N D Ot C M c a cs :
  unf_tm (iwiIH l lp li l' X A N D Ot C M c a cs) =
  iwiIH l lp li l' (unf_ty X) (unf_ty A) (unf_tm N) (unf_ty D) (unf_tm Ot) (unf_tm C) (unf_ty M) (unf_tm c)
    (unf_tm a) (unf_tm cs).
Proof.
  unfold iwiIH; cbn [unf_tm unf_ty].
  repeat progress (rewrite ?unf_ren_ty, ?unf_ren, ?unf_lsingle, ?unf_subst, ?unf_subst_ty, ?unf_llift, ?unf_tmDNth,
                     ?unf_iwiFam, ?unf_iwiFamCod; cbn [unf_ty unf_tm]).
  reflexivity.
Qed.

(** [M]'s [out]-of-[corec] reduct (M18b). *)
Lemma unf_mOutCorec l l' li X A B C k Y c j y :
  unf_tm (mOutCorec l l' li X A B C k Y c j y) =
  mOutCorec l l' li (unf_ty X) (unf_ty A) (unf_ty B) (unf_tm C) k (unf_ty Y) (unf_tm c) (unf_tm j) (unf_tm y).
Proof.
  unfold mOutCorec.
  repeat progress (cbn [unf_tm unf_ty];
    rewrite ?unf_ren_ty, ?unf_ren, ?unf_subst_ty, ?unf_subst, ?unf_llift, ?unf_lsingle, ?unf_lsingle2).
  reflexivity.
Qed.

Ltac unf_peel_push :=
  repeat first [ rewrite <- peelL_unf by hd_tac
               | rewrite <- peelG_unf by hd_tac
               | rewrite <- peelU_unf by hd_tac ];
  unfold rb_br; rewrite tup_nth_unf by hd_tac;
  do 3 (cbn [unf_o unf_tm unf_ctx unf_ty recT rect];
    rewrite ?unf_lsingle_ty, ?unf_lsucc_ty, ?unf_lsingle2_ty, ?unf_ren_ty, ?unf_ren);
  (* [sup_f]'s children's length and [elim_Wf]'s step telescope (M15b) *)
  repeat progress (rewrite ?unf_subst, ?unf_lsingle, ?unf_tmNth, ?unf_lsingle_ty, ?unf_ren_ty, ?unf_ren;
          cbn [unf_o unf_tm unf_ctx unf_ty]);
  (* [sup_i]'s children's family and [elim_IWf]'s step telescope (M17c) *)
  repeat progress (rewrite ?unf_iwfFam, ?unf_iwiFam, ?unf_iwiFamCod, ?unf_tmDNth, ?unf_subst, ?unf_lsingle, ?unf_lsingle_ty, ?unf_lsingle2_ty,
                           ?unf_ren_ty, ?unf_ren;
          cbn [unf_o unf_tm unf_ctx unf_ty]);
  reflexivity.

Lemma redT_unf_map l1 l2 MT Mt bs l Δ c :
  redT l1 l2 (unf_tm (mkrb MT Mt bs)) l (unf_ctx Δ) (unf_ty c) =
  option_map unf_tm (redT l1 l2 (mkrb MT Mt bs) l Δ c).
Proof. destruct c; cbn [redT unf_ty option_map]; try reflexivity; f_equal; unf_peel_push. Qed.
Lemma redt_unf_map l1 l2 MT Mt bs l Δ T c : (forall u b d, c <> gdef u b d) ->
  redt l1 l2 (unf_tm (mkrb MT Mt bs)) l (unf_ctx Δ) (unf_ty T) (unf_tm c) =
  option_map unf_tm (redt l1 l2 (mkrb MT Mt bs) l Δ T c).
Proof.
  intros Hc; destruct c; cbn [redt unf_tm option_map]; redt_case T; cbn [unf_ty redt option_map];
    try reflexivity; try (f_equal; unf_peel_push).
  all: exfalso; eapply Hc; reflexivity.
Qed.
Lemma redT_unf l1 l2 MT Mt bs l Δ c v : redT l1 l2 (mkrb MT Mt bs) l Δ c = Some v ->
  redT l1 l2 (unf_tm (mkrb MT Mt bs)) l (unf_ctx Δ) (unf_ty c) = Some (unf_tm v).
Proof. intros E. now rewrite redT_unf_map, E. Qed.
Lemma redt_unf l1 l2 MT Mt bs l Δ T c v : redt l1 l2 (mkrb MT Mt bs) l Δ T c = Some v ->
  redt l1 l2 (unf_tm (mkrb MT Mt bs)) l (unf_ctx Δ) (unf_ty T) (unf_tm c) = Some (unf_tm v).
Proof.
  intros E. rewrite redt_unf_map, E; [reflexivity|].
  intros u b d ->. discriminate E.
Qed.

(** ** Presupposition at the layers of a definition's use *)

Lemma eqtm_wf_r_C {G i Γ t t' T l} : lle lC i -> [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] -> [ G ; Γ ⊢[ i ] t' : T @ l ].
Proof.
  intros Hi H. destruct i; cbn in Hi; unfold lle in Hi; cbn in Hi; try lia.
  - exact (proj2 (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 presupposition_C))))) _ _ _ _ _ _ _ H (le_n _))).
  - exact (eqtm_wf_r eq_refl H).
  - exact (eqtm_wf_r eq_refl H).
Qed.

(** ** The theorem *)

Ltac unf_push :=
  cbn [unf_ty unf_tm unf_ctx unf_l unf_o unf_G unf_decl map gL gΨ gext typeof lcons'] in *.

Ltac unf_rw_all :=
  rewrite ?unf_subst_ty, ?unf_subst, ?unf_lsingle, ?unf_lsingle2, ?unf_lsingle3, ?unf_lsucc, ?unf_llift,
    ?unf_ren_ty, ?unf_ren, ?unf_gren_ty, ?unf_gren, ?unf_gren_ctx,
    ?unf_uren_ty, ?unf_uren, ?unf_uren_ctx, ?unf_usubst_ty, ?unf_usubst, ?unf_usubst_ctx,
    ?unf_gsingle_ty, ?unf_gsingle, ?motT_wrap_unf, ?mott_wrap_unf, ?mkrb_unf, ?wrapMT_unf, ?wrapMt_unf,
    ?unf_wIH, ?unf_wfIH, ?unf_tmNth, ?unf_iwfIH, ?unf_tmDNth, ?unf_iwfFam, ?unf_iwiIH, ?unf_iwiFam, ?unf_iwiFamCod, ?unf_mOutCorec, ?recGT_unf, ?recGt_unf, ?recΓT_unf, ?recΓt_unf, ?unf_G_uwk in *.

Ltac unf_norm := unf_push; do 2 (unf_rw_all; unf_push).

#[local] Hint Resolve in_ctx_unf gctx_var_unf lsub_tail_unf unf_dnfl unf_ty_leq unf_tm_leq : unf.
#[local] Hint Extern 1 (in_gctx _ _ _) =>
  match goal with Hin : in_gctx _ _ _ |- _ => exact (in_gctx_unf _ _ _ Hin) end : unf.

(** The lookup-typed local substitution of [u^δ]/[U^δ]: the induction
    hypotheses, at the unfolded lookups. *)
Ltac unf_entries :=
  let n := fresh "n" in let A := fresh "A" in let k := fresh "k" in let Hin := fresh "Hin" in
  intros n A k Hin;
  let A0 := fresh "A0" in let HA0 := fresh "HA0" in
  destruct (in_ctx_unf_inv _ _ _ _ Hin) as (A0 & HA0 & ->);
  rewrite ?llk_unf, <- ?unf_subst_ty;
  match goal with IH : forall n A k (_ : in_ctx _ n A k), _ |- _ => exact (IH n A0 k HA0) end.

Ltac unf_Δ tac :=
  match goal with
  | Hin : in_gctx _ _ (gdTy ?Δ _ _) |- _ => tac (unf_ctx Δ)
  | Hin : in_gctx _ _ (gdTm ?Δ _ _ _) |- _ => tac (unf_ctx Δ)
  | Hin : in_gctx _ _ (gdDef ?Δ _ _ _) |- _ => tac (unf_ctx Δ)
  end.

(** The branch premises. *)
Ltac unf_branches :=
  let k := fresh "k" in let Hk := fresh "Hk" in intros k Hk; cbn beta;
  match goal with
  | IH : forall k, k < nbr -> _ |- _ =>
      let X := fresh "X" in pose proof (IH k Hk) as X;
      rewrite ?brG_unf, ?brΓ_unf, ?brRes_unf in X by exact Hk; exact X
  end.

(** The typed substitution [unf δ : unf Γ ⇒ unf Δ] of an occurrence, and
    two of them equal. *)
Lemma unf_lsub_wf G i Γ Δ d :
  [ G ; unf_ctx Γ ⊢[ typeof i ] ] -> lsub_tail d Δ Γ -> dnfl d ->
  (forall n A k, in_ctx Δ n A k -> [ G ; unf_ctx Γ ⊢[ i ] unf_tm (llk d n) : unf_ty (A[d]) @ k ]) ->
  [ G ; unf_ctx Γ ⊢[ i ] unf_l d : unf_ctx Δ ].
Proof.
  intros HΓ Ht Hd Hv. constructor; auto.
  - intros n. apply dnfl_llk, unf_dnfl, Hd.
  - now apply lsub_tail_unf.
  - intros n A k Hin. destruct (in_ctx_unf_inv _ _ _ _ Hin) as (A0 & HA0 & ->).
    rewrite llk_unf, <- unf_subst_ty. exact (Hv _ _ _ HA0).
Qed.

Lemma unf_lsub_eq G i Γ Δ d d' :
  [ G ; unf_ctx Γ ⊢[ typeof i ] ] -> lsub_tail d Δ Γ -> dnfl d -> lsub_tail d' Δ Γ -> dnfl d' ->
  (forall n A k, in_ctx Δ n A k -> [ G ; unf_ctx Γ ⊢[ i ] unf_tm (llk d n) : unf_ty (A[d]) @ k ]) ->
  (forall n A k, in_ctx Δ n A k -> [ G ; unf_ctx Γ ⊢[ i ] unf_tm (llk d' n) : unf_ty (A[d']) @ k ]) ->
  (forall n A k, in_ctx Δ n A k ->
     [ G ; unf_ctx Γ ⊢[ i ] unf_tm (llk d n) ≅ unf_tm (llk d' n) : unf_ty (A[d]) @ k ]) ->
  [ G ; unf_ctx Γ ⊢[ i ] unf_l d ≅ unf_l d' : unf_ctx Δ ].
Proof.
  intros HΓ Ht Hd Ht' Hd' Hv Hv' He. split; [|split]; auto using unf_lsub_wf.
  intros n A k Hin. destruct (in_ctx_unf_inv _ _ _ _ Hin) as (A0 & HA0 & ->).
  rewrite !llk_unf, <- unf_subst_ty. exact (He _ _ _ HA0).
Qed.

Ltac unf_sub_wf := eapply unf_lsub_wf; eassumption.
Ltac unf_sub_eq := eapply unf_lsub_eq; eassumption.

Ltac unf_manual :=
  match goal with
  (* [elim_IWf]'s β (M17b): its induction hypothesis's typing has renamings
     nested deeper than [unf_norm]'s rounds reach *)
  | |- eq_tm _ _ _ (tmElimIWf _ _ _ _ _ _ _ _ _ _ _ (tmSupi _ _ _ _ _ _ _ _ _)) _ _ _ =>
      repeat progress (rewrite ?unf_ren_ty, ?unf_ren in * );
      eapply eqtm_elimIWf_supi; eauto with unf
  (* [elim_IWi]'s (M19a): its induction hypothesis's type nests one
     binder deeper, so one more round of pushing *)
  | |- eq_tm _ _ _ (tmElimIWi _ _ _ _ _ _ _ _ _ _ _ _ _ (tmSupii _ _ _ _ _ _ _ _ _ _ _)) _ _ _ =>
      do 2 (unf_rw_all; unf_push); repeat progress (rewrite ?unf_ren_ty, ?unf_ren in * );
      eapply eqtm_elimIWi_supii; eauto with unf
  | |- wf_tm _ _ _ (tmElimIWi _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ =>
      do 2 (unf_rw_all; unf_push); eapply wf_elimIWi; eauto with unf
  | |- eq_tm _ _ _ (tmElimIWi _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ =>
      do 2 (unf_rw_all; unf_push); eapply eqtm_elimIWi; eauto with unf
  | |- wf_ty _ _ _ (tyGvar _ _) _ =>
      unf_Δ ltac:(fun D => eapply wft_gvar with (Δ := D)); [ .. | unf_entries]; eauto with unf
  | |- eq_ty _ _ _ (tyGvar _ _) _ _ =>
      unf_Δ ltac:(fun D => eapply eqty_gvar with (Δ := D));
      [ .. | unf_entries | unf_entries | unf_entries]; eauto with unf
  | |- wf_tm _ _ _ (gvar _ _) _ _ =>
      unf_Δ ltac:(fun D => eapply wf_gvar with (Δ := D)); [ .. | unf_entries]; eauto with unf
  | |- eq_tm _ _ _ (gvar _ _) _ _ _ =>
      unf_Δ ltac:(fun D => eapply eqtm_gvar with (Δ := D));
      [ .. | unf_entries | unf_entries | unf_entries]; eauto with unf
  (* a defined global: the instance of its unfolded body *)
  | |- eq_tm _ _ _ ?x ?x _ _ =>
      apply eqtm_refl; eapply (proj1 (proj2 (proj2 (proj2 substitution_all)))); [eassumption | unf_sub_wf]
  | |- wf_tm _ _ _ (subst_tm _ _) _ _ =>
      eapply (proj1 (proj2 (proj2 (proj2 substitution_all)))); [eassumption | unf_sub_wf]
  | |- eq_tm _ _ _ (subst_tm _ _) (subst_tm ?t' _) _ _ =>
      eapply eqtm_trans;
      [ eapply (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 substitution_all)))))); [eassumption | unf_sub_wf]
      | eapply (proj1 (proj2 (proj2 (proj2 functionality_all))));
        [ eapply eqtm_wf_r_C; eassumption | unf_sub_eq ] ]
  (* the recursors *)
  | |- wf_tm _ _ _ (elimT _ _ _ _ _ _) _ _ =>
      eapply wf_elimT; [ .. | unf_branches | unf_branches | ]; eauto with unf
  | |- wf_tm _ _ _ (elimt _ _ _ _ _ _ _) _ _ =>
      eapply wf_elimt; [ .. | unf_branches | unf_branches | | ]; eauto with unf
  | |- eq_tm _ _ _ (elimT _ _ (unf_tm ?rb) _ _ (boxT _)) _ _ _ =>
      match goal with Hw : wf_tm _ _ _ (elimT _ _ rb _ _ _) _ _ |- _ =>
        let MT := fresh "MT" in let Mt := fresh "Mt" in let bs := fresh "bs" in
        destruct (inv_elimT (i := lM) eq_refl Hw) as (MT & Mt & bs & ((-> & _) & _)) end;
      eapply eqtm_elimT_beta; [eassumption | apply redT_unf; eassumption | eassumption]
  | |- eq_tm _ _ _ (elimt _ _ (unf_tm ?rb) _ _ _ (boxt _)) _ _ _ =>
      match goal with Hw : wf_tm _ _ _ (elimt _ _ rb _ _ _ _) _ _ |- _ =>
        let MT := fresh "MT" in let Mt := fresh "Mt" in let bs := fresh "bs" in
        destruct (inv_elimt (i := lM) eq_refl Hw) as (MT & Mt & bs & ((-> & _) & _)) end;
      eapply eqtm_elimt_beta; [eassumption | apply redt_unf; eassumption | eassumption]
  | |- eq_tm _ _ _ (elimT _ _ _ _ _ _) _ _ _ =>
      eapply eqtm_elimT; [ .. | unf_branches | unf_branches | unf_branches | unf_branches | ];
      eauto with unf
  | |- eq_tm _ _ _ (elimt _ _ _ _ _ _ _) _ _ _ =>
      eapply eqtm_elimt; [ .. | unf_branches | unf_branches | unf_branches | unf_branches | ];
      eauto with unf
  end.

Theorem unfolding :
  (forall G, [ ⊢ G ] -> [ ⊢ unf_G G ]) /\
  (forall G i Γ, [ G ; Γ ⊢[ i ] ] -> [ unf_G G ; unf_ctx Γ ⊢[ i ] ]) /\
  (forall G i Γ T l, [ G ; Γ ⊢[ i ] T @ l ] -> [ unf_G G ; unf_ctx Γ ⊢[ i ] unf_ty T @ l ]) /\
  (forall G i Γ t T l, [ G ; Γ ⊢[ i ] t : T @ l ] ->
     [ unf_G G ; unf_ctx Γ ⊢[ i ] unf_tm t : unf_ty T @ l ]) /\
  (forall G i Γ T T' l, [ G ; Γ ⊢[ i ] T ≅ T' @ l ] ->
     [ unf_G G ; unf_ctx Γ ⊢[ i ] unf_ty T ≅ unf_ty T' @ l ]) /\
  (forall G i Γ t t' T l, [ G ; Γ ⊢[ i ] t ≅ t' : T @ l ] ->
     [ unf_G G ; unf_ctx Γ ⊢[ i ] unf_tm t ≅ unf_tm t' : unf_ty T @ l ]) /\
  (forall G i Γ Γ', [ G ⊢[ i ] Γ ≅ Γ' ] -> [ unf_G G ⊢[ i ] unf_ctx Γ ≅ unf_ctx Γ' ]).
Proof.
  apply typing_mut; intros.
  par: (
    (unf_norm);
    (try any_rule ltac:(eauto with unf));
    (try unf_manual)).
Qed.
