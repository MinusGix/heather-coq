(** * Substitution equations by computation on a template

    An equation between two instances of the same opaque type [F] and
    term [n] under concrete renamings and local substitutions, such as
    [F⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (… n⟨↑⟩ …)] = F⟨rlift (rshift 2)⟩[…]],
    is decided by rewriting the lookups pointwise ([meq] in [DNthCore],
    thousands of [rewrite]s on a wide former). [geq] decides it by
    computation instead: it replaces [F] and [n] by the global variables
    [tyGvar 0 id] and [gvar 1 id] (the template), on which renaming and
    substitution compute to normal forms, so [vm_compute] proves the
    template's equation; the global substitution [gθ F n] then turns the
    template back into the goal, by the laws that global substitution
    commutes with the local operations ([GSubst]) and [F[id] = F] for
    normal [F]. The template's normal forms are canonical (an operation's
    output lsub is normal, and normal lsubs with equal lookups are equal:
    [l_canon]), so the computation proves such an equation when it
    holds of all [F] and [n]. One that holds only by [F]'s scope, or
    whose shape [gpush] does not rebuild, is left to the pointwise
    tactics. *)
From Coq Require Import Lia.
From DeLaM.Syntax Require Export GSubst.

(** The template's atoms back to the goal's: [F] at global 0, [n] at 1. *)
Definition gθ (F : ty) (n : tm) : gsub :=
  fun j => match j with 0 => GTy F | 1 => GTm n | j => GId j end.

(** The commutations, on the raw operations (as [graw] leaves them). *)
Lemma gr_ty T r σ : gsubst_ty (ren_ty T r) σ = ren_ty (gsubst_ty T σ) r.
Proof using . exact (gsubst_ren_ty T r σ). Qed.
Lemma gr_tm t r σ : gsubst_tm (ren_tm t r) σ = ren_tm (gsubst_tm t σ) r.
Proof using . exact (gsubst_ren t r σ). Qed.
Lemma gs_ty T d σ : gsubst_ty (subst_ty T d) σ = subst_ty (gsubst_ty T σ) (glsubst d σ).
Proof using . exact (gsubst_subst_ty T d σ). Qed.
Lemma gs_tm t d σ : gsubst_tm (subst_tm t d) σ = subst_tm (gsubst_tm t σ) (glsubst d σ).
Proof using . exact (gsubst_subst t d σ). Qed.
Lemma gk d k σ : gsubst_tm (llk d k) σ = llk (glsubst d σ) k.
Proof using . symmetry; apply llk_glsubst. Qed.
Lemma gll d σ : glsubst (llift d) σ = llift (glsubst d σ).
Proof using .
  apply l_canon; [apply nf_glsubst | apply nf_llift |]. intros [|m];
    rewrite llk_glsubst, !llk_llift; [reflexivity|].
  rewrite llk_glsubst. apply gsubst_ren_tm.
Qed.
Lemma gid_ty T : nfty T -> subst_ty T (lshift 0) = T.
Proof using . intros N; apply (subst_id_ty T); [exact N|]; intros m; cbn; f_equal; lia. Qed.
Lemma gid_tm t : nftm t -> subst_tm t (lshift 0) = t.
Proof using . intros N; apply (subst_id t); [exact N|]; intros m; cbn; f_equal; lia. Qed.

(** The goal in raw operations, with [dnth]'s families unfolded. *)
Ltac graw := cbv beta delta [dnthFamS dnthFam dnthRes dnthEmb lsingle
  ren subst gsubst Ren_ty Ren_tm Ren_lsub Subst_ty Subst_tm Subst_lsub GSubst_ty GSubst_tm GSubst_lsub].
(** [gθ] pushed from the template's root to its atoms. *)
Ltac gpush H := repeat progress (rewrite ?gr_ty, ?gr_tm, ?gs_ty, ?gs_tm, ?gk, ?gll in H;
  cbn [gsubst_ty gsubst_tm glsubst pty ptm gθ lsingle lcons'] in H).

(** [t] has no type or term variable: computing on a template with one
    would get stuck on [lcons']'s match, and [vm_compute] reads a stuck
    match back with all its branches normalized (minutes). *)
Ltac gclosed t :=
  match t with
  | context [?x] => is_var x; let T := type of x in
      lazymatch T with ty => fail 2 "atom" x | tm => fail 2 "atom" x | _ => fail end
  | _ => idtac
  end.

(** [L = R] with atoms [F] (normal by [NF]) and [n] (by [Nn]). The
    result is compared syntactically before [exact]: a failing [exact]
    would leave the comparison to conversion, which unfolds the
    operations on the atoms and can take minutes. *)
Ltac geq_with F n NF Nn :=
  graw;
  lazymatch goal with |- ?L = ?R =>
    lazymatch eval pattern F, n in L with ?f F n =>
    lazymatch eval pattern F, n in R with ?g F n =>
    let L0 := eval cbv beta in (f (tyGvar 0 (lshift 0)) (gvar 1 (lshift 0))) in
    let R0 := eval cbv beta in (g (tyGvar 0 (lshift 0)) (gvar 1 (lshift 0))) in
    gclosed L0; gclosed R0;
    let E := fresh "E" in
    assert (E : L0 = R0) by (vm_compute; reflexivity);
    lazymatch type of L with
    | ty => apply (f_equal (fun T => gsubst_ty T (gθ F n))) in E
    | tm => apply (f_equal (fun t => gsubst_tm t (gθ F n))) in E
    end; cbv beta in E;
    gpush E; rewrite ?(gid_ty F NF), ?(gid_tm n Nn) in E;
    lazymatch type of E with ?a = ?b => constr_eq a L; constr_eq b R; exact E end
    end end
  end.
(** The atoms are the context's normal type and term. *)
Ltac geq := match goal with NF : nfty ?F, Nn : nftm ?n |- _ => geq_with F n NF Nn end.
