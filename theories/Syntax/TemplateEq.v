(** * Substitution equations by computation on a template

    An equation between two instances of the same opaque type [F] and
    term [n] under concrete renamings and local substitutions, such as
    [F⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (… n⟨↑⟩ …)] = F⟨rlift (rshift 2)⟩[…]],
    is decided by rewriting the lookups pointwise ([meq] in [DNthCore],
    thousands of [rewrite]s on a wide former). [geq] decides it by
    computation instead: it replaces [F] and [n] by the global variables
    [tyGvar 0 id] and [gvar 1 id] (the template), on which renaming and
    substitution compute to normal forms, so [vm_compute] proves the
    template's equation; the global substitution [gθ [GTy F; GTm n]] turns the
    template back into the goal, by the laws that global substitution
    commutes with the local operations ([GSubst]) and [F[id] = F] for
    normal [F]. The template's normal forms are canonical (an operation's
    output lsub is normal, and normal lsubs with equal lookups are equal:
    [l_canon]), so the computation proves such an equation when it
    holds of all [F] and [n]. One that holds only by [F]'s scope, or
    whose shape [gpush] does not rebuild, is left to the pointwise
    tactics. Any variable with an [nfty]/[nftm] hypothesis is an atom.
    [gnorm t] uses the same round trip to rewrite a term [t] of the goal
    to its normal form (a reduction's next state). *)
From Coq Require Import Lia.
From DeLaM.Syntax Require Export GSubst.

(** The template's atoms back to the goal's: the [j]th atom at global [j]. *)
Definition gθ (os : list gobj) : gsub := fun j => nth j os (GId j).

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
Ltac graw := cbv beta delta [dnthFamS dnthFam dnthRes dnthEmb dnthMot dnthBase dnthStep lsingle lsingle2 lsingle3 lsucc
  ren subst gsubst Ren_ty Ren_tm Ren_lsub Subst_ty Subst_tm Subst_lsub GSubst_ty GSubst_tm GSubst_lsub].
(** [gθ] pushed from the template's root to its atoms. *)
Ltac gpush H := repeat progress (rewrite ?gr_ty, ?gr_tm, ?gs_ty, ?gs_tm, ?gk, ?gll in H;
  cbn [gsubst_ty gsubst_tm glsubst pty ptm gθ nth lsingle lsingle2 lsingle3 lsucc lcons' Nat.eqb] in H).
(** The atoms' leaves [x[id]] back to [x]. *)
Ltac gids H := repeat match type of H with
  | context [subst_ty ?x (lshift 0)] => is_var x;
      match goal with N : nfty x |- _ => rewrite (gid_ty x N) in H end
  | context [subst_tm ?x (lshift 0)] => is_var x;
      match goal with N : nftm x |- _ => rewrite (gid_tm x N) in H end
  end.

(** [t] has no type or term variable: computing on a template with one
    would get stuck on [lcons']'s match, and [vm_compute] reads a stuck
    match back with all its branches normalized (minutes). *)
Ltac gclosed t :=
  match t with
  | context [?x] => is_var x; let T := type of x in
      lazymatch T with ty => fail 2 "atom" x | tm => fail 2 "atom" x | _ => fail end
  | _ => idtac
  end.

(** An atom: a variable whose normality is a hypothesis. *)
Ltac gnf x := lazymatch type of x with
  | ty => match goal with _ : nfty x |- _ => idtac end
  | tm => match goal with _ : nftm x |- _ => idtac end
  end.
(** [t]'s template: each atom replaced by the next global, then [k] on
    the template and the atoms' list. A failure of [k] is not retried
    at another atom ([fail 1] leaves the [match]). *)
Ltac gtempl t os n k :=
  match t with
  | context [?x] => is_var x; gnf x; first [ gtempl_at x t os n k | fail 1 ]
  | _ => k t os
  end
with gtempl_at x t os n k :=
  let T := type of x in
  lazymatch eval pattern x in t with ?g x =>
    lazymatch T with
    | ty => let t' := eval cbv beta in (g (tyGvar n (lshift 0))) in
            gtempl t' constr:(List.app os (cons (GTy x) nil)) constr:(S n) k
    | tm => let t' := eval cbv beta in (g (gvar n (lshift 0))) in
            gtempl t' constr:(List.app os (cons (GTm x) nil)) constr:(S n) k
    end
  end.

(** [E : L0 = R0] on the template, as [L = R] on the atoms [os]. Its
    callers take it [once]: a later failure retrying its [rewrite]s and
    [match]es at other occurrences costs minutes. *)
Ltac gback E os :=
  let os := eval cbv [List.app] in os in
  lazymatch type of E with
  | @eq ty _ _ => apply (f_equal (fun T => gsubst_ty T (gθ os))) in E
  | @eq tm _ _ => apply (f_equal (fun t => gsubst_tm t (gθ os))) in E
  end; cbv beta in E; gpush E; gids E.

(** [L = R] by computation. The result is compared syntactically before
    [exact]: a failing [exact] would leave the comparison to conversion,
    which unfolds the operations on the atoms and can take minutes. *)
Ltac geq :=
  graw;
  lazymatch goal with |- ?L = ?R =>
    gtempl constr:(L = R) constr:(@nil gobj) constr:(0) ltac:(fun P os =>
      lazymatch P with ?L0 = ?R0 =>
        gclosed L0; gclosed R0;
        let E := fresh "E" in
        assert (E : L0 = R0) by (vm_compute; reflexivity);
        once (gback E os);
        lazymatch type of E with ?a = ?b => constr_eq a L; constr_eq b R; exact E end
      end)
  end.

(** The term [t] of the goal to its normal form, by computation. *)
Ltac gnorm t :=
  gtempl t constr:(@nil gobj) constr:(0) ltac:(fun t0 os =>
    gclosed t0;
    let N0 := eval vm_compute in t0 in
    let E := fresh "E" in
    assert (E : t0 = N0) by (vm_compute; reflexivity);
    once (gback E os);
    lazymatch type of E with ?a = _ => constr_eq a t end;
    rewrite E; clear E).
