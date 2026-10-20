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
| posty_CTrm Δ T l : posty (tyCTrm Δ T l)
| posty_id l A a b : posty (tyId l A a b)
(* binary sums (M12b): no η *)
| posty_sum l l' A B : posty (tySum l l' A B)
(* well-founded trees (M13a): no η *)
| posty_W l l' A B : posty (tyW l l' A B)
(* finitary well-founded trees (M15a): no η *)
| posty_wf l A N : posty (tyWf l A N)
(* indexed W-types (M17b): no η *)
| posty_iwf l li X A N Ot C m : posty (tyIWf l li X A N Ot C m).

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
(* the unit type (M8c) *)
| actnf_unit G Γ l l' : leqv l l' -> ac_tynf G Γ (tyUnit l) (tyUnit l')
(* strict equality (M10a): endpoints compared at the left carrier *)
| actnf_seq G Γ l l' A A' a a' b b' : leqv l l' -> ac_ty G Γ A A' ->
    ac_tm G Γ a a' A -> ac_tm G Γ b b' A ->
    ac_tynf G Γ (tySEq l A a b) (tySEq l' A' a' b')
| actnf_sempty G Γ l l' : leqv l l' -> ac_tynf G Γ (tySEmpty l) (tySEmpty l')
(* the empty type (M12a) *)
| actnf_empty G Γ l l' : leqv l l' -> ac_tynf G Γ (tyEmpty l) (tyEmpty l')
(* binary sums (M12b) *)
| actnf_sum G Γ l1 l2 l3 l4 A A' B B' : leqv l1 l3 -> leqv l2 l4 -> ac_ty G Γ A A' -> ac_ty G Γ B B' ->
    ac_tynf G Γ (tySum l1 l2 A B) (tySum l3 l4 A' B')
(* well-founded trees (M13a): the positions under the shape, as Π's codomain *)
| actnf_W G Γ l1 l2 l3 l4 A A' B B' : leqv l1 l3 -> leqv l2 l4 -> ac_ty G Γ A A' -> ac_ty G (Γ ,, A @ l1) B B' ->
    ac_tynf G Γ (tyW l1 l2 A B) (tyW l3 l4 A' B')
(* finitary well-founded trees (M15a): the arities at Nat under the shape *)
| actnf_wf G Γ l l' A A' N N' : leqv l l' -> ac_ty G Γ A A' -> ac_tm G (Γ ,, A @ l) N N' tyNat ->
    ac_tynf G Γ (tyWf l A N) (tyWf l' A' N')
(* indexed W-types (M17b): the signature as [Wf]'s, the output and child
   indices at the index type under their binders, and the indices *)
| actnf_iwf G Γ l li k ki X X' A A' N N' Ot Ot' C C' m m' : leqv l k -> leqv li ki ->
    ac_ty G Γ X X' -> ac_ty G Γ A A' -> ac_tm G (Γ ,, A @ l) N N' tyNat ->
    ac_tm G (Γ ,, A @ l) Ot Ot' X⟨↑⟩ -> ac_tm G (Γ ,, A @ l ,, tyFin N @ lzero) C C' X⟨↑⟩⟨↑⟩ ->
    ac_tm G Γ m m' X ->
    ac_tynf G Γ (tyIWf l li X A N Ot C m) (tyIWf k ki X' A' N' Ot' C' m')
(* propositional truncation (M16a) *)
| actnf_sq G Γ l l' A A' : leqv l l' -> ac_ty G Γ A A' -> ac_tynf G Γ (tySq l A) (tySq l' A')
(* the identity type (M11a): endpoints compared at the left carrier *)
| actnf_id G Γ l l' A A' a a' b b' : leqv l l' -> ac_ty G Γ A A' ->
    ac_tm G Γ a a' A -> ac_tm G Γ b b' A ->
    ac_tynf G Γ (tyId l A a b) (tyId l' A' a' b')

with ac_tyne : gctx -> ctx -> ty -> ty -> Prop :=
| actne_gvar G Γ U Δ i' l d d' : in_gctx (gΨ G) U (gdTy Δ i' l) -> ac_sub G Γ d d' Δ ->
    ac_tyne G Γ (tyGvar U d) (tyGvar U d')
| actne_El G Γ l l' ν ν' W : leqv l l' -> ac_tmnee G Γ ν ν' W ->
    ac_tyne G Γ (tyEl l ν) (tyEl l' ν')
(* length-indexed tuples and finite indices at neutral lengths (M14a): the
   element types as types, the lengths as neutrals *)
| actne_vec G Γ l l' A A' ν ν' W : leqv l l' -> ac_ty G Γ A A' -> ac_tmnee G Γ ν ν' W ->
    ac_tyne G Γ (tyVec l A ν) (tyVec l' A' ν')
| actne_fin G Γ ν ν' W : ac_tmnee G Γ ν ν' W -> ac_tyne G Γ (tyFin ν) (tyFin ν')
(* dependent tuples at a neutral length (M17a): the families under the
   left length's index type *)
| actne_dvec G Γ l l' ν ν' F F' W : leqv l l' -> ac_tmnee G Γ ν ν' W ->
    ac_ty G (Γ ,, tyFin ν @ lzero) F F' -> ac_tyne G Γ (tyDVec l ν F) (tyDVec l' ν' F')

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
(* the unit type (M8c): the code, and η as proof irrelevance (any two
   weak-head normal forms, neutral or not; [Unit] is not [posty]) *)
| actmnf_code_unit G Γ l k k' : leqv k k' -> ac_tmnf G Γ (tmUnit k) (tmUnit k') (tyU l)
| actmnf_unit_eta G Γ l w w' : ac_tmnf G Γ w w' (tyUnit l)
(* strict equality (M10a): proof irrelevance at [sEq] and [sEmpty], as at
   [Unit] (neither is [posty]) *)
| actmnf_seq_irr G Γ l A a b w w' : ac_tmnf G Γ w w' (tySEq l A a b)
| actmnf_sempty_irr G Γ l w w' : ac_tmnf G Γ w w' (tySEmpty l)
(* the empty type: proof irrelevance, as at [sEmpty] ([Empty] is not
   [posty], so its neutrals are not compared either) *)
| actmnf_empty_irr G Γ l w w' : ac_tmnf G Γ w w' (tyEmpty l)
(* the identity type (M11a): two [refl]s at an [Id] type are equal (both
   points are its endpoints, by the typings the instances bundle); a [refl]
   and a neutral are not ([Id] is [posty]) *)
| actmnf_refl G Γ l A a b k k' C C' c c' :
    ac_tmnf G Γ (tmRefl k C c) (tmRefl k' C' c') (tyId l A a b)
(* its code (M11b) *)
| actmnf_code_id G Γ l k k' s s' t t' u u' : leqv k k' ->
    ac_tm G Γ s s' (tyU k) -> ac_tm G Γ t t' (tyEl k s) -> ac_tm G Γ u u' (tyEl k s) ->
    ac_tmnf G Γ (tmId k s t u) (tmId k' s' t' u') (tyU l)
(* strict equality's codes (M10c) *)
| actmnf_code_seq G Γ l k k' s s' t t' u u' : leqv k k' ->
    ac_tm G Γ s s' (tyU k) -> ac_tm G Γ t t' (tyEl k s) -> ac_tm G Γ u u' (tyEl k s) ->
    ac_tmnf G Γ (tmSEq k s t u) (tmSEq k' s' t' u') (tyU l)
| actmnf_code_sempty G Γ l k k' : leqv k k' -> ac_tmnf G Γ (tmSEmpty k) (tmSEmpty k') (tyU l)
(* the injections (M12b): the payloads at the summand; the annotations are
   the sum type's up to equality, as [refl]'s are the [Id] type's *)
| actmnf_inl G Γ l l' A B k1 k2 k3 k4 C D C' D' a a' : ac_tm G Γ a a' A ->
    ac_tmnf G Γ (tmInl k1 k2 C D a) (tmInl k3 k4 C' D' a') (tySum l l' A B)
| actmnf_inr G Γ l l' A B k1 k2 k3 k4 C D C' D' b b' : ac_tm G Γ b b' B ->
    ac_tmnf G Γ (tmInr k1 k2 C D b) (tmInr k3 k4 C' D' b') (tySum l l' A B)
(* [sup] (M13a): the shapes at the shape type and the child functions at
   their type; the annotations are the [W] type's up to equality *)
| actmnf_sup G Γ l l' A B k1 k2 k3 k4 C D C' D' a a' f f' : ac_tm G Γ a a' A ->
    ac_tm G Γ f f' (tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩) ->
    ac_tmnf G Γ (tmSup k1 k2 C D a f) (tmSup k3 k4 C' D' a' f') (tyW l l' A B)
(* [sup_f] (M15a): the shapes at the shape type and the children at their
   tuple type, which reduces to Σ's and Unit; no Wf-specific η *)
| actmnf_supf G Γ l A N k k' C D C' D' a a' cs cs' : ac_tm G Γ a a' A ->
    ac_tm G Γ cs cs' (tyVec l (tyWf l A N) N[lsingle a]) ->
    ac_tmnf G Γ (tmSupf k C D a cs) (tmSupf k' C' D' a' cs') (tyWf l A N)
(* [sup_i] (M17b): as [sup_f]'s, the children at their [DVec] type; the
   annotations are the type's up to equality, at any index *)
| actmnf_supi G Γ l li X A N Ot C m k ki X1 A1 N1 O1 C1 k' ki' X1' A1' N1' O1' C1' a a' cs cs' :
    ac_tm G Γ a a' A ->
    ac_tm G Γ cs cs' (tyDVec (lmax l li) N[lsingle a] (iwfFam l li X A N Ot C a)) ->
    ac_tmnf G Γ (tmSupi k ki X1 A1 N1 O1 C1 a cs) (tmSupi k' ki' X1' A1' N1' O1' C1' a' cs')
      (tyIWf l li X A N Ot C m)
(* the codes of Empty and + (M12c) *)
| actmnf_code_empty G Γ l k k' : leqv k k' -> ac_tmnf G Γ (tmEmpty k) (tmEmpty k') (tyU l)
| actmnf_code_sum G Γ l l1 l2 l3 l4 s s' t t' : leqv l1 l3 -> leqv l2 l4 ->
    ac_tm G Γ s s' (tyU l1) -> ac_tm G Γ t t' (tyU l2) ->
    ac_tmnf G Γ (tmSum l1 l2 s t) (tmSum l3 l4 s' t') (tyU l)
(* the code of W (M13b), as Σ's *)
| actmnf_code_W G Γ l l1 l2 l3 l4 s s' t t' : leqv l1 l3 -> leqv l2 l4 ->
    ac_tm G Γ s s' (tyU l1) -> ac_tm G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) ->
    ac_tmnf G Γ (tmW l1 l2 s t) (tmW l3 l4 s' t') (tyU l)
(* the codes of Vec and Fin (M14b): lengths at Nat *)
| actmnf_code_vec G Γ l k k' s s' n n' : leqv k k' ->
    ac_tm G Γ s s' (tyU k) -> ac_tm G Γ n n' tyNat ->
    ac_tmnf G Γ (tmVec k s n) (tmVec k' s' n') (tyU l)
| actmnf_code_fin G Γ l n n' : ac_tm G Γ n n' tyNat -> ac_tmnf G Γ (tmFin n) (tmFin n') (tyU l)
(* the code of Wf (M15b): the arity at Nat under the shape's binder *)
| actmnf_code_wf G Γ l k k' s s' n n' : leqv k k' ->
    ac_tm G Γ s s' (tyU k) -> ac_tm G (Γ ,, tyEl k s @ k) n n' tyNat ->
    ac_tmnf G Γ (tmWf k s n) (tmWf k' s' n') (tyU l)
(* propositional truncation (M16a): proof irrelevance, as at [Empty] (a
   squash type is not [posty]); both sides are already weak-head normal,
   which is Heather's normalizing-total conversion *)
| actmnf_sq_irr G Γ l A w w' : ac_tmnf G Γ w w' (tySq l A)
(* the code of ∥·∥ (M16b) *)
| actmnf_code_sq G Γ l k k' s s' : leqv k k' -> ac_tm G Γ s s' (tyU k) ->
    ac_tmnf G Γ (tmSqCode k s) (tmSqCode k' s') (tyU l)
(* the codes of [DVec] and [IWf] (M17c), structurally, the binders'
   contexts at the left components as [IWf]'s *)
| actmnf_code_dvec G Γ l k k' n n' f f' : leqv k k' ->
    ac_tm G Γ n n' tyNat -> ac_tm G (Γ ,, tyFin n @ lzero) f f' (tyU k) ->
    ac_tmnf G Γ (tmDVec k n f) (tmDVec k' n' f') (tyU l)
| actmnf_code_iwf G Γ l k k' ki ki' x x' s s' n n' o o' c c' m m' : leqv k k' -> leqv ki ki' ->
    ac_tm G Γ x x' (tyU ki) -> ac_tm G Γ s s' (tyU k) ->
    ac_tm G (Γ ,, tyEl k s @ k) n n' tyNat -> ac_tm G (Γ ,, tyEl k s @ k) o o' (tyEl ki x⟨↑⟩) ->
    ac_tm G (Γ ,, tyEl k s @ k ,, tyFin n @ lzero) c c' (tyEl ki x⟨↑⟩⟨↑⟩) ->
    ac_tm G Γ m m' (tyEl ki x) ->
    ac_tmnf G Γ (tmIWf k ki x s n o c m) (tmIWf k' ki' x' s' n' o' c' m') (tyU l)

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
    (forall k, k < nbr -> ac_tm (brG k G) (brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                           (bs k) (bs' k) (brRes k (wrapMT MT) (wrapMt Mt))) ->
    ac_tmnee G Γ ν ν' W ->
    ac_tmne G Γ (elimT l1 l2 (mkrb MT Mt bs) l Δ ν) (elimT l1' l2' (mkrb MT' Mt' bs') l' Δ' ν')
      (motT (wrapMT MT) l Δ ν)
| actmne_elimT_gvar G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' U d d' :
    leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> ac_ctx G Δ Δ' ->
    ac_ty (recGT G) (recΓT Γ) MT MT' -> ac_ty (recGt G) (recΓt Γ) Mt Mt' ->
    (forall k, k < nbr -> ac_tm (brG k G) (brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                           (bs k) (bs' k) (brRes k (wrapMT MT) (wrapMt Mt))) ->
    lsub_leq d d' ->
    ac_tmne G Γ (elimT l1 l2 (mkrb MT Mt bs) l Δ (boxT (tyGvar U d)))
      (elimT l1' l2' (mkrb MT' Mt' bs') l' Δ' (boxT (tyGvar U d')))
      (motT (wrapMT MT) l Δ (boxT (tyGvar U d)))
| actmne_elimt G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' T T' ν ν' W :
    leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> ac_ctx G Δ Δ' -> ac_ty G Δ T T' ->
    ac_ty (recGT G) (recΓT Γ) MT MT' -> ac_ty (recGt G) (recΓt Γ) Mt Mt' ->
    (forall k, k < nbr -> ac_tm (brG k G) (brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                           (bs k) (bs' k) (brRes k (wrapMT MT) (wrapMt Mt))) ->
    ac_tmnee G Γ ν ν' W ->
    ac_tmne G Γ (elimt l1 l2 (mkrb MT Mt bs) l Δ T ν) (elimt l1' l2' (mkrb MT' Mt' bs') l' Δ' T' ν')
      (mott (wrapMt Mt) l Δ T ν)
(* a boxed global (a global variable, or a definition, M9): its code compared as code *)
| actmne_elimt_glob G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' T T' c c' :
    leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> ac_ctx G Δ Δ' -> ac_ty G Δ T T' ->
    ac_ty (recGT G) (recΓT Γ) MT MT' -> ac_ty (recGt G) (recΓt Γ) Mt Mt' ->
    (forall k, k < nbr -> ac_tm (brG k G) (brΓ k Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                           (bs k) (bs' k) (brRes k (wrapMT MT) (wrapMt Mt))) ->
    boxed_global c -> tm_leq c c' ->
    ac_tmne G Γ (elimt l1 l2 (mkrb MT Mt bs) l Δ T (boxt c))
      (elimt l1' l2' (mkrb MT' Mt' bs') l' Δ' T' (boxt c'))
      (mott (wrapMt Mt) l Δ T (boxt c))
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
(* the irrelevant empty type's eliminator (M10a): the scrutinees are
   neutral and never compared (their typing, which the instances bundle,
   makes them equal by irrelevance) *)
| actmne_elimSEmpty G Γ l1 l2 l3 l4 M M' ν ν' : leqv l1 l3 -> leqv l2 l4 ->
    ac_ty G Γ M M' -> whne ν -> whne ν' ->
    ac_tmne G Γ (elimSEmpty l1 l2 M ν) (elimSEmpty l3 l4 M' ν') M
(* [J] (M11a): the scrutinees as neutrals, then the motives and the base
   cases in the left [J]'s telescope.  The scrutinee's type [Id A a u] and
   its level are not compared: equal scrutinees have equal types, so
   [Id]'s injectivity makes them equal (typed eliminator congruence,
   ELIM_CONGRUENCE.md) *)
| actmne_J G Γ l1 l2 l3 l4 A A' a a' M M' c c' u u' ν ν' W : leqv l2 l4 ->
    ac_ty G (Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1) M M' ->
    ac_tm G Γ c c' M[lsingle2 a (tmRefl l1 A a)] ->
    ac_tmnee G Γ ν ν' W ->
    ac_tmne G Γ (tmJ l1 l2 A a M c u ν) (tmJ l3 l4 A' a' M' c' u' ν') M[lsingle2 u ν]
(* [Empty]'s eliminator (M12a): the motives at the left scrutinee's type;
   the scrutinees are neutral and, as [elimSEmpty]'s, never compared
   (irrelevance at [Empty]) *)
| actmne_elimEmpty G Γ l1 l2 l3 l4 M M' ν ν' : leqv l1 l3 -> leqv l2 l4 ->
    ac_ty G (Γ ,, tyEmpty l2 @ l2) M M' -> whne ν -> whne ν' ->
    ac_tmne G Γ (elimEmpty l1 l2 M ν) (elimEmpty l3 l4 M' ν') M[lsingle ν]
(* [case] (M12b): the scrutinees as neutrals, then the motives and the
   branches in the left [case]'s telescope; the summands and their levels
   are the scrutinee's type's, as [J]'s *)
| actmne_case G Γ l1 l2 l3 l4 l5 l6 A A' B B' M M' c1 c1' c2 c2' ν ν' W :
    leqv l3 l6 ->
    ac_ty G (Γ ,, tySum l1 l2 A B @ lmax l1 l2) M M' ->
    ac_tm G (Γ ,, A @ l1) c1 c1' M⟨rlift ↑⟩[lsingle (tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] ->
    ac_tm G (Γ ,, B @ l2) c2 c2' M⟨rlift ↑⟩[lsingle (tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] ->
    ac_tmnee G Γ ν ν' W ->
    ac_tmne G Γ (tmCase l1 l2 l3 A B M c1 c2 ν) (tmCase l4 l5 l6 A' B' M' c1' c2' ν') M[lsingle ν]
(* [elim_W] (M13a): the scrutinees as neutrals, then the motives, and the
   steps under the left telescope; the shapes, the positions and their
   levels are the scrutinee's type's, as [J]'s *)
| actmne_elimW G Γ l1 l2 l3 l4 l5 l6 A A' B B' M M' c c' ν ν' W :
    leqv l3 l6 ->
    ac_ty G (Γ ,, tyW l1 l2 A B @ lmax l1 l2) M M' ->
    ac_tm G (Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, wihty l1 l2 l3 A B M @ lmax l2 l3)
      c c' (wstepty l1 l2 A B M) ->
    ac_tmnee G Γ ν ν' W ->
    ac_tmne G Γ (tmElimW l1 l2 l3 A B M c ν) (tmElimW l4 l5 l6 A' B' M' c' ν') M[lsingle ν]
(* [elim_Wf] (M15a): as [elim_W]; the shapes and the arities are the
   scrutinee's type's *)
| actmne_elimWf G Γ l1 l2 l3 l4 A A' N N' M M' c c' ν ν' W :
    leqv l2 l4 ->
    ac_ty G (Γ ,, tyWf l1 A N @ l1) M M' ->
    ac_tm G (Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ,, wfihty l1 l2 A N M @ lmax lzero l2)
      c c' (wfstepty l1 A N M) ->
    ac_tmnee G Γ ν ν' W ->
    ac_tmne G Γ (tmElimWf l1 l2 A N M c ν) (tmElimWf l3 l4 A' N' M' c' ν') M[lsingle ν]
(* [elim_IWf] (M17b): as [elim_Wf]; the signature, the index and their
   levels are the scrutinee's type's, and so are the induction hypothesis's
   types once the motives are equal ([IWf_ihty_eq], ELIM_CONGRUENCE.md) *)
| actmne_elimIWf G Γ l li l' k ki k' X X' A A' N N' Ot Ot' C C' M M' c c' m m' ν ν' W :
    leqv l' k' ->
    ac_ty G (Γ ,, X @ li ,, iwfmotty l li X A N Ot C @ lmax l li) M M' ->
    ac_tm G (Γ ,, A @ l ,, iwfcsty l li X A N Ot C @ lmax l li ,, iwfihty l li l' X A N Ot C M @ lmax lzero l')
      c c' (iwfstepty l li X A N Ot C M) ->
    ac_tmnee G Γ ν ν' W ->
    ac_tmne G Γ (tmElimIWf l li l' X A N Ot C M c m ν) (tmElimIWf k ki k' X' A' N' Ot' C' M' c' m' ν')
      M[lsingle2 m ν]
(* [ind_∥∥] (M16a): the carriers, and the motives at the left carrier's
   squash; the scrutinees are neutral and, as [elim_Empty]'s, never compared,
   and neither are the steps (irrelevance at the step's squash type) *)
| actmne_elimSq G Γ l1 l2 l3 l4 A A' M M' c c' ν ν' : leqv l1 l3 -> leqv l2 l4 ->
    ac_ty G Γ A A' -> ac_ty G (Γ ,, tySq l1 A @ l1) M M' -> whne ν -> whne ν' ->
    ac_tmne G Γ (tmElimSq l1 l2 A M c ν) (tmElimSq l3 l4 A' M' c' ν') (tySq l2 M[lsingle ν])

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
    split; eauto using whne_elimT_gvar, whne_elimt_glob, boxed_global_leq with whnf.
Qed.

Lemma ac_tynf_whnf {G Γ W W'} : ac_tynf G Γ W W' -> whnf_ty W /\ whnf_ty W'.
Proof. apply ac_tynf_whnf_l_all. Qed.
Lemma ac_tyne_whne {G Γ V V'} : ac_tyne G Γ V V' -> whne_ty V /\ whne_ty V'.
Proof. apply ac_tynf_whnf_l_all. Qed.
Lemma ac_tmne_whne {G Γ ν ν' T} : ac_tmne G Γ ν ν' T -> whne ν /\ whne ν'.
Proof. apply ac_tynf_whnf_l_all. Qed.
Lemma ac_tmnee_whne {G Γ ν ν' W} : ac_tmnee G Γ ν ν' W -> whne ν /\ whne ν'.
Proof. apply ac_tynf_whnf_l_all. Qed.

(** ** Irrelevance at [Empty], after type reduction

    The algorithm reduces the type before it compares terms, so [Empty]-η
    reaches types that only become [Empty] by reduction: two distinct
    variables at [Fin 0], and two [elim_Empty]s whose scrutinees differ. *)
Example ac_fin_zero_irr G Γ : ac_tm G Γ (var 1) (var 0) (tyFin zero).
Proof.
  eapply actm_red; [econstructor; [apply red_fin_zero | constructor] | apply whnf_tyEmpty
                   | constructor | constructor | apply whnf_ne, whne_var | apply whnf_ne, whne_var
                   | apply actmnf_empty_irr].
Qed.

Example ac_elimEmpty_irr G Γ l :
  ac_tmne G Γ (elimEmpty lzero l tyNat (var 1)) (elimEmpty lzero l tyNat (var 0)) tyNat[lsingle (var 1)].
Proof.
  apply actmne_elimEmpty; [apply leqv_refl | apply leqv_refl | | apply whne_var | apply whne_var].
  eapply act_red; [constructor | constructor | apply whnf_tyNat | apply whnf_tyNat | apply actnf_nat].
Qed.
