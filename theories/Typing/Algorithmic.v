(** * Algorithmic convertibility (ch. 6 §"Convertibility Checking")

    Reduce to weak-head normal form, then compare heads and recurse
    (06:351–700). The judgments carry neither a layer nor a level
    (M6_DESIGN.md H2): the instances bundle declarative typing, which
    supplies both. Level annotations are compared by [leqv], boxed code by
    [≡ₗ] (H3). Neutral terms infer their type ([ac_tmne]); where the paper
    checks the inferred type against a fixed shape, the rules ignore it, and
    [uapp]/[capp]/[tapp] read their result type from it.

    - [ac_ty G Γ T T']: types;
    - [ac_tynf G Γ W W']: weak-head normal types;
    - [ac_tyne G Γ V V']: neutral types;
    - [ac_ctx G Γ Δ]: local contexts, pairwise;
    - [ac_tm G Γ t t' T]: terms at a type;
    - [ac_tmnf G Γ w w' W]: weak-head normal terms at a weak-head normal type;
    - [ac_tmne G Γ ν ν' T]: neutral terms, [T] inferred;
    - [ac_tmnee G Γ ν ν' W]: neutral terms, the inferred type reduced;
    - [ac_sub G Γ d d' Δ]: local substitutions, pointwise over [Δ]. *)
From DeLaM.Syntax Require Export LevelDec.
From DeLaM.Typing Require Export RecSpec.

(** The whnf types at which neutral terms are compared as such: the
    others are function types, compared by η. *)
Inductive posty : ty -> Prop :=
| posty_nat : posty tyNat
| posty_U l : posty (tyU l)
| posty_ne V : whne_ty V -> posty V
| posty_CTyp Δ l : posty (tyCTyp Δ l)
| posty_CTrm Δ T l : posty (tyCTrm Δ T l).

Inductive ac_ty : gctx -> ctx -> ty -> ty -> Prop :=
| act_red G Γ T T' W W' : reds_ty T W -> reds_ty T' W' -> whnf_ty W -> whnf_ty W' ->
    ac_tynf G Γ W W' -> ac_ty G Γ T T'

with ac_tynf : gctx -> ctx -> ty -> ty -> Prop :=
| actnf_nat G Γ : ac_tynf G Γ tyNat tyNat
| actnf_U G Γ l l' : leqv l l' -> ac_tynf G Γ (tyU l) (tyU l')
| actnf_pi G Γ l1 l2 l3 l4 A A' B B' : leqv l1 l3 -> leqv l2 l4 ->
    ac_ty G Γ A A' -> ac_ty G (Γ ,, A @ l1) B B' ->
    ac_tynf G Γ (tyPi l1 l2 A B) (tyPi l3 l4 A' B')
| actnf_ne G Γ V V' : ac_tyne G Γ V V' -> ac_tynf G Γ V V'
| actnf_CTyp G Γ Δ Δ' l l' : ac_ctx G Δ Δ' -> leqv l l' ->
    ac_tynf G Γ (tyCTyp Δ l) (tyCTyp Δ' l')
| actnf_CTrm G Γ Δ Δ' T T' l l' : ac_ctx G Δ Δ' -> ac_ty G Δ T T' -> leqv l l' ->
    ac_tynf G Γ (tyCTrm Δ T l) (tyCTrm Δ' T' l')
| actnf_upi G Γ n l l' T T' : leqv l l' -> ac_ty (gctx_uwk n G) Γ⟨ush n⟩ᵤ T T' ->
    ac_tynf G Γ (tyUPi n l T) (tyUPi n l' T')
| actnf_cpi G Γ l l' T T' : leqv l l' -> ac_ty (gext G gdCtx) Γ⟪S⟫ T T' ->
    ac_tynf G Γ (tyCPi l T) (tyCPi l' T')
| actnf_tpi G Γ Δ Δ' l1 l2 l3 l4 T T' : ac_ctx G Δ Δ' -> leqv l1 l3 -> leqv l2 l4 ->
    ac_ty (gext G (gdTy Δ lD l1)) Γ⟪S⟫ T T' ->
    ac_tynf G Γ (tyTPi Δ l1 l2 T) (tyTPi Δ' l3 l4 T')
(* dependent pairs (M8) *)
| actnf_sig G Γ l1 l2 l3 l4 A A' B B' : leqv l1 l3 -> leqv l2 l4 ->
    ac_ty G Γ A A' -> ac_ty G (Γ ,, A @ l1) B B' ->
    ac_tynf G Γ (tySig l1 l2 A B) (tySig l3 l4 A' B')

with ac_tyne : gctx -> ctx -> ty -> ty -> Prop :=
| actne_gvar G Γ U Δ i' l d d' : in_gctx (gΨ G) U (gdTy Δ i' l) -> ac_sub G Γ d d' Δ ->
    ac_tyne G Γ (tyGvar U d) (tyGvar U d')
| actne_El G Γ l l' ν ν' W : leqv l l' -> ac_tmnee G Γ ν ν' W ->
    ac_tyne G Γ (tyEl l ν) (tyEl l' ν')

with ac_ctx : gctx -> ctx -> ctx -> Prop :=
| acc_nil G : ac_ctx G cnil cnil
| acc_var G g : ac_ctx G (cvar g) (cvar g)
| acc_ext G Γ Γ' A A' l l' : ac_ctx G Γ Γ' -> ac_ty G Γ A A' -> leqv l l' ->
    ac_ctx G (Γ ,, A @ l) (Γ' ,, A' @ l')

with ac_tm : gctx -> ctx -> tm -> tm -> ty -> Prop :=
| actm_red G Γ t t' T w w' W : reds_ty T W -> whnf_ty W ->
    reds t w -> reds t' w' -> whnf w -> whnf w' ->
    ac_tmnf G Γ w w' W -> ac_tm G Γ t t' T

with ac_tmnf : gctx -> ctx -> tm -> tm -> ty -> Prop :=
| actmnf_code_nat G Γ l : ac_tmnf G Γ tmNat tmNat (tyU l)
| actmnf_code_U G Γ l k k' : leqv k k' -> ac_tmnf G Γ (tmU k) (tmU k') (tyU l)
| actmnf_code_pi G Γ l l1 l2 l3 l4 s s' t t' : leqv l1 l3 -> leqv l2 l4 ->
    ac_tm G Γ s s' (tyU l1) -> ac_tm G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) ->
    ac_tmnf G Γ (tmPi l1 l2 s t) (tmPi l3 l4 s' t') (tyU l)
| actmnf_zero G Γ : ac_tmnf G Γ zero zero tyNat
| actmnf_succ G Γ t t' : ac_tm G Γ t t' tyNat -> ac_tmnf G Γ (succ t) (succ t') tyNat
| actmnf_ne G Γ ν ν' W W' : posty W -> ac_tmnee G Γ ν ν' W' -> ac_tmnf G Γ ν ν' W
| actmnf_eta G Γ l l' A B w w' :
    ac_tm G (Γ ,, A @ l) (app w⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0))
                         (app w'⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0)) B ->
    ac_tmnf G Γ w w' (tyPi l l' A B)
| actmnf_ueta G Γ n l T w w' :
    ac_tm (gctx_uwk n G) Γ⟨ush n⟩ᵤ (uapp w⟨ush n⟩ᵤ (ubvars n)) (uapp w'⟨ush n⟩ᵤ (ubvars n)) T ->
    ac_tmnf G Γ w w' (tyUPi n l T)
| actmnf_ceta G Γ l T w w' :
    ac_tm (gext G gdCtx) Γ⟪S⟫ (capp w⟪S⟫ (cvar 0)) (capp w'⟪S⟫ (cvar 0)) T ->
    ac_tmnf G Γ w w' (tyCPi l T)
| actmnf_teta G Γ Δ l l' T w w' :
    ac_tm (gext G (gdTy Δ lD l)) Γ⟪S⟫ (tapp w⟪S⟫ (tyGvar 0 (lshift 0)))
                                     (tapp w'⟪S⟫ (tyGvar 0 (lshift 0))) T ->
    ac_tmnf G Γ w w' (tyTPi Δ l l' T)
| actmnf_boxT G Γ Δ l T T' : ty_leq T T' -> ac_tmnf G Γ (boxT T) (boxT T') (tyCTyp Δ l)
| actmnf_boxt G Γ Δ A l t t' : tm_leq t t' -> ac_tmnf G Γ (boxt t) (boxt t') (tyCTrm Δ A l)
(* dependent pairs (M8): the code, and η by the projections *)
| actmnf_code_sig G Γ l l1 l2 l3 l4 s s' t t' : leqv l1 l3 -> leqv l2 l4 ->
    ac_tm G Γ s s' (tyU l1) -> ac_tm G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) ->
    ac_tmnf G Γ (tmSig l1 l2 s t) (tmSig l3 l4 s' t') (tyU l)
| actmnf_sig_eta G Γ l l' A B w w' :
    ac_tm G Γ (tmFst l l' A B w) (tmFst l l' A B w') A ->
    ac_tm G Γ (tmSnd l l' A B w) (tmSnd l l' A B w') B[lsingle (tmFst l l' A B w)] ->
    ac_tmnf G Γ w w' (tySig l l' A B)

with ac_tmne : gctx -> ctx -> tm -> tm -> ty -> Prop :=
| actmne_var G Γ n T l : in_ctx Γ n T l -> ac_tmne G Γ (var n) (var n) T
| actmne_gvar G Γ u Δ i' T l d d' : in_gctx (gΨ G) u (gdTm Δ i' T l) -> ac_sub G Γ d d' Δ ->
    ac_tmne G Γ (gvar u d) (gvar u d') T[d]
| actmne_natrec G Γ l l' M M' s s' z z' ν ν' W : leqv l l' ->
    ac_ty G (Γ ,, tyNat @ lzero) M M' ->
    ac_tm G Γ s s' M[lsingle zero] ->
    ac_tm G (Γ ,, tyNat @ lzero ,, M @ l) z z' M[lsucc] ->
    ac_tmnee G Γ ν ν' W ->
    ac_tmne G Γ (natrec l M s z ν) (natrec l' M' s' z' ν') M[lsingle ν]
(* the annotations are the function's type up to equality: they are not
   inspected, the argument is compared at the domain of the function's
   inferred type (06:589; M6_DESIGN.md H9) *)
| actmne_app G Γ l1 l2 l3 l4 A A' B B' ν ν' s s' m m' A0 B0 :
    ac_tmnee G Γ ν ν' (tyPi m m' A0 B0) -> ac_tm G Γ s s' A0 ->
    ac_tmne G Γ (app ν l1 l2 A B s) (app ν' l3 l4 A' B' s') B0[lsingle s]
| actmne_letboxT G Γ l1 l2 l3 l4 Δ Δ' M M' t1 t2 ν ν' W : leqv l1 l3 -> leqv l2 l4 ->
    ac_ctx G Δ Δ' -> ac_ty G (Γ ,, tyCTyp Δ l2 @ lzero) M M' ->
    ac_tm (gext G (gdTy Δ lC l2)) Γ⟪S⟫ t1 t2 (M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))]) ->
    ac_tmnee G Γ ν ν' W ->
    ac_tmne G Γ (letboxT l1 l2 Δ M t1 ν) (letboxT l3 l4 Δ' M' t2 ν') M[lsingle ν]
| actmne_letboxt G Γ l1 l2 l3 l4 Δ Δ' T T' M M' t1 t2 ν ν' W : leqv l1 l3 -> leqv l2 l4 ->
    ac_ctx G Δ Δ' -> ac_ty G Δ T T' -> ac_ty G (Γ ,, tyCTrm Δ T l2 @ lzero) M M' ->
    ac_tm (gext G (gdTm Δ lC T l2)) Γ⟪S⟫ t1 t2 (M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))]) ->
    ac_tmnee G Γ ν ν' W ->
    ac_tmne G Γ (letboxt l1 l2 Δ T M t1 ν) (letboxt l3 l4 Δ' T' M' t2 ν') M[lsingle ν]
| actmne_elimT G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' ν ν' W :
    leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> ac_ctx G Δ Δ' ->
    ac_ty (recGT G) (recΓT Γ) MT MT' -> ac_ty (recGt G) (recΓt Γ) Mt Mt' ->
    (forall k, k < 13 -> ac_tm (brG k G) (brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                           (bs k) (bs' k) (brRes k (wrapMT MT) (wrapMt Mt))) ->
    ac_tmnee G Γ ν ν' W ->
    ac_tmne G Γ (elimT l1 l2 (mkrb MT Mt bs) l Δ ν) (elimT l1' l2' (mkrb MT' Mt' bs') l' Δ' ν')
      (motT (wrapMT MT) l Δ ν)
| actmne_elimT_gvar G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' U d d' :
    leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> ac_ctx G Δ Δ' ->
    ac_ty (recGT G) (recΓT Γ) MT MT' -> ac_ty (recGt G) (recΓt Γ) Mt Mt' ->
    (forall k, k < 13 -> ac_tm (brG k G) (brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                           (bs k) (bs' k) (brRes k (wrapMT MT) (wrapMt Mt))) ->
    lsub_leq d d' ->
    ac_tmne G Γ (elimT l1 l2 (mkrb MT Mt bs) l Δ (boxT (tyGvar U d)))
      (elimT l1' l2' (mkrb MT' Mt' bs') l' Δ' (boxT (tyGvar U d')))
      (motT (wrapMT MT) l Δ (boxT (tyGvar U d)))
| actmne_elimt G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' T T' ν ν' W :
    leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> ac_ctx G Δ Δ' -> ac_ty G Δ T T' ->
    ac_ty (recGT G) (recΓT Γ) MT MT' -> ac_ty (recGt G) (recΓt Γ) Mt Mt' ->
    (forall k, k < 13 -> ac_tm (brG k G) (brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                           (bs k) (bs' k) (brRes k (wrapMT MT) (wrapMt Mt))) ->
    ac_tmnee G Γ ν ν' W ->
    ac_tmne G Γ (elimt l1 l2 (mkrb MT Mt bs) l Δ T ν) (elimt l1' l2' (mkrb MT' Mt' bs') l' Δ' T' ν')
      (mott (wrapMt Mt) l Δ T ν)
| actmne_elimt_gvar G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' T T' u d d' :
    leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> ac_ctx G Δ Δ' -> ac_ty G Δ T T' ->
    ac_ty (recGT G) (recΓT Γ) MT MT' -> ac_ty (recGt G) (recΓt Γ) Mt Mt' ->
    (forall k, k < 13 -> ac_tm (brG k G) (brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                           (bs k) (bs' k) (brRes k (wrapMT MT) (wrapMt Mt))) ->
    lsub_leq d d' ->
    ac_tmne G Γ (elimt l1 l2 (mkrb MT Mt bs) l Δ T (boxt (gvar u d)))
      (elimt l1' l2' (mkrb MT' Mt' bs') l' Δ' T' (boxt (gvar u d')))
      (mott (wrapMt Mt) l Δ T (boxt (gvar u d)))
| actmne_uapp G Γ n l T ν ν' ls ls' : ac_tmnee G Γ ν ν' (tyUPi n l T) -> length ls = n ->
    Forall2 leqv ls ls' ->
    ac_tmne G Γ (uapp ν ls) (uapp ν' ls') T[uext ls lvar]ᵤ
| actmne_capp G Γ l T ν ν' Δ Δ' : ac_tmnee G Γ ν ν' (tyCPi l T) -> ac_ctx G Δ Δ' ->
    ac_tmne G Γ (capp ν Δ) (capp ν' Δ') T⦃gsingle (GCtx Δ)⦄
| actmne_tapp G Γ Δ l l' T ν ν' A A' : ac_tmnee G Γ ν ν' (tyTPi Δ l l' T) -> ac_ty G Δ A A' ->
    ac_tmne G Γ (tapp ν A) (tapp ν' A') T⦃gsingle (GTy A)⦄
(* dependent pairs (M8): as for [app], the annotations are the pair's type
   up to equality and are not inspected; the result type is read off the
   inferred type, the first projection included, so that it does not
   depend on the annotations either *)
| actmne_fst G Γ l1 l2 l3 l4 A A' B B' ν ν' m m' A0 B0 :
    ac_tmnee G Γ ν ν' (tySig m m' A0 B0) ->
    ac_tmne G Γ (tmFst l1 l2 A B ν) (tmFst l3 l4 A' B' ν') A0
| actmne_snd G Γ l1 l2 l3 l4 A A' B B' ν ν' m m' A0 B0 :
    ac_tmnee G Γ ν ν' (tySig m m' A0 B0) ->
    ac_tmne G Γ (tmSnd l1 l2 A B ν) (tmSnd l3 l4 A' B' ν') B0[lsingle (tmFst m m' A0 B0 ν)]

with ac_tmnee : gctx -> ctx -> tm -> tm -> ty -> Prop :=
| actmnee_red G Γ ν ν' T W : ac_tmne G Γ ν ν' T -> reds_ty T W -> whnf_ty W ->
    ac_tmnee G Γ ν ν' W

with ac_sub : gctx -> ctx -> lsub -> lsub -> ctx -> Prop :=
| acs_pt G Γ d d' Δ :
    (forall n A k, in_ctx Δ n A k -> ac_tm G Γ (llk d n) (llk d' n) A[d]) ->
    ac_sub G Γ d d' Δ.

Scheme ac_ty_mut := Induction for ac_ty Sort Prop
  with ac_tynf_mut := Induction for ac_tynf Sort Prop
  with ac_tyne_mut := Induction for ac_tyne Sort Prop
  with ac_ctx_mut := Induction for ac_ctx Sort Prop
  with ac_tm_mut := Induction for ac_tm Sort Prop
  with ac_tmnf_mut := Induction for ac_tmnf Sort Prop
  with ac_tmne_mut := Induction for ac_tmne Sort Prop
  with ac_tmnee_mut := Induction for ac_tmnee Sort Prop
  with ac_sub_mut := Induction for ac_sub Sort Prop.
Combined Scheme ac_mut from ac_ty_mut, ac_tynf_mut, ac_tyne_mut, ac_ctx_mut, ac_tm_mut,
  ac_tmnf_mut, ac_tmne_mut, ac_tmnee_mut, ac_sub_mut.

(** ** Shapes *)

Lemma ac_tynf_whnf_l_all :
  (forall G Γ T T', ac_ty G Γ T T' -> True) /\
  (forall G Γ W W', ac_tynf G Γ W W' -> whnf_ty W /\ whnf_ty W') /\
  (forall G Γ V V', ac_tyne G Γ V V' -> whne_ty V /\ whne_ty V') /\
  (forall G Δ Δ', ac_ctx G Δ Δ' -> True) /\
  (forall G Γ t t' T, ac_tm G Γ t t' T -> True) /\
  (forall G Γ w w' W, ac_tmnf G Γ w w' W -> True) /\
  (forall G Γ ν ν' T, ac_tmne G Γ ν ν' T -> whne ν /\ whne ν') /\
  (forall G Γ ν ν' W, ac_tmnee G Γ ν ν' W -> whne ν /\ whne ν') /\
  (forall G Γ d d' Δ, ac_sub G Γ d d' Δ -> True).
Proof.
  apply ac_mut; intros; try exact I;
    repeat match goal with H : _ /\ _ |- _ => destruct H end;
    split; auto using whne_elimT_gvar, whne_elimt_gvar with whnf.
Qed.

Lemma ac_tynf_whnf {G Γ W W'} : ac_tynf G Γ W W' -> whnf_ty W /\ whnf_ty W'.
Proof. apply ac_tynf_whnf_l_all. Qed.
Lemma ac_tyne_whne {G Γ V V'} : ac_tyne G Γ V V' -> whne_ty V /\ whne_ty V'.
Proof. apply ac_tynf_whnf_l_all. Qed.
Lemma ac_tmne_whne {G Γ ν ν' T} : ac_tmne G Γ ν ν' T -> whne ν /\ whne ν'.
Proof. apply ac_tynf_whnf_l_all. Qed.
Lemma ac_tmnee_whne {G Γ ν ν' W} : ac_tmnee G Γ ν ν' W -> whne ν /\ whne ν'.
Proof. apply ac_tynf_whnf_l_all. Qed.
