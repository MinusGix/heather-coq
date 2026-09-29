(** * The typing specification of the recursors' motives and branches (M3)

    The recursor rules (04:1127–1310) type each motive and branch in an
    extended scope: [nu] fresh levels, [ng] fresh global bindings, and [nl]
    fresh locals (the recursive calls). This file computes those scopes
    from the ambient [G], [Γ] and the wrapped motives [wT = wrapMT MT],
    [wt = wrapMt Mt] (M3_DESIGN.md E3):
    - [brG k G]: [L + nu] and [Ψ] universe-shifted, extended by the
      branch's own declarations [brDecls k] (which mention only
      branch-bound variables);
    - [brΓ k Γ …]: [Γ] universe- and globally shifted, extended by the
      types of the recursive calls;
    - [brRes k …] and [brLv k …]: the branch's type and level.

    Motive instances are computed by peeling the wrapped motive, weakened
    into the branch scope ([wkb]), with the paper's instantiations. *)
From DeLaM.Typing Require Export Context.
Import ListNotations.

(** ** Universe operations on declarations and global contexts *)

Definition gdecl_uren (D : gdecl) (ρ : nat -> nat) : gdecl :=
  match D with
  | gdCtx => gdCtx
  | gdTy Δ i l => gdTy (ucren Δ ρ) i (lvren l ρ)
  | gdTm Δ i T l => gdTm (ucren Δ ρ) i (uren_ty T ρ) (lvren l ρ)
  end.
Definition gdecl_usubst (D : gdecl) (φ : nat -> lvl) : gdecl :=
  match D with
  | gdCtx => gdCtx
  | gdTy Δ i l => gdTy (ucsubst Δ φ) i (lvsubst l φ)
  | gdTm Δ i T l => gdTm (ucsubst Δ φ) i (usubst_ty T φ) (lvsubst l φ)
  end.

(** [G[φ]] with [φ : L' ⇒ gL G], and weakening by [n] fresh levels. *)
Definition gctx_usubst (G : gctx) (L' : nat) (φ : nat -> lvl) : gctx :=
  mkG L' (map (fun D => gdecl_usubst D φ) (gΨ G)).
Definition ush (n : nat) : nat -> nat := fun i => n + i.
Definition gctx_uwk (n : nat) (G : gctx) : gctx :=
  mkG (n + gL G) (map (fun D => gdecl_uren D (ush n)) (gΨ G)).

(** ** Branch-scope helpers *)

Definition gv (j : nat) : ty := tyGvar j (lshift 0).            (* U_j^id *)
Definition gu (j : nat) : tm := gvar j (lshift 0).              (* u_j^id *)

(** Weakening an ambient term past [nu] levels, [ng] globals, [nl] locals. *)
Definition wkb (nu ng nl : nat) (w : tm) : tm :=
  ren_tm (gren_tm (uren_tm w (ush nu)) (ush ng)) (rshift nl).
Definition wkc (nu ng : nat) (Γ : ctx) : ctx := gcren (ucren Γ (ush nu)) (ush ng).

Definition getTy (t : tm) : ty := match t with tmTy T => T | _ => tyErr end.

(** Instances of the motives: [M_Typ[lv/ℓ, g/g, c/x_T]] and
    [M_Trm[lv/ℓ, g/g, U/U_T, c/x_t]]. *)
Definition motT (w : tm) (lv : lvl) (g : ctx) (c : tm) : ty :=
  getTy (peelL (peelG (peelU w lv) (GCtx g)) c).
Definition mott (w : tm) (lv : lvl) (g : ctx) (U : ty) (c : tm) : ty :=
  getTy (peelL (peelG (peelG (peelU w lv) (GCtx g)) (GTy U)) c).

(** ** The motive scopes (04:1141) *)

Definition recGT (G : gctx) : gctx := let G1 := gctx_uwk 1 G in mkG (gL G1) (gdCtx :: gΨ G1).
Definition recΓT (Γ : ctx) : ctx := wkc 1 1 Γ ,, tyCTyp (cvar 0) (lvar 0) @ lzero.
Definition recGt (G : gctx) : gctx :=
  let G1 := gctx_uwk 1 G in mkG (gL G1) (gdTy (cvar 0) lD (lvar 0) :: gdCtx :: gΨ G1).
Definition recΓt (Γ : ctx) : ctx := wkc 1 2 Γ ,, tyCTrm (cvar 1) (gv 0) (lvar 0) @ lzero.

(** ** The branch scopes (04:1150–1300)

    Declarations are listed most recent first (as in [gΨ]). Inside a
    branch with [nu = 2], [ℓ = lvar 1] and [ℓ' = lvar 0]. *)

Definition brDecls (k : nat) : list gdecl :=
  match k with
  (* g. t_Nat *)
  | 0 => [gdCtx]
  (* ℓ ℓ'; g, U_S : (g ⊢C @ℓ), U_T : (g, x : U_S^id @ℓ ⊢C @ℓ') *)
  | 1 => [gdTy (cvar 1 ,, gv 0 @ lvar 1) lC (lvar 0); gdTy (cvar 0) lC (lvar 1); gdCtx]
  (* ℓ; g *)
  | 2 => [gdCtx]
  (* ℓ; g, u_t : (g ⊢C Ty ℓ @ 1+ℓ) *)
  | 3 => [gdTm (cvar 0) lC (tyU (lvar 0)) (lsuc (lvar 0)); gdCtx]
  (* ℓ; g, U_T : (g ⊢P @ℓ), u_x : (g ⊢V U_T^id @ℓ) *)
  | 4 => [gdTm (cvar 1) lV (gv 0) (lvar 0); gdTy (cvar 0) lD (lvar 0); gdCtx]
  (* g *)
  | 5 => [gdCtx]
  (* ℓ ℓ'; g, u_s : (g ⊢C Ty ℓ @ 1+ℓ), u_t : (g, x : El ℓ u_s^id @ℓ ⊢C Ty ℓ' @ 1+ℓ') *)
  | 6 => [gdTm (cvar 1 ,, tyEl (lvar 1) (gu 0) @ lvar 1) lC (tyU (lvar 0)) (lsuc (lvar 0));
          gdTm (cvar 0) lC (tyU (lvar 1)) (lsuc (lvar 1)); gdCtx]
  (* ℓ; g *)
  | 7 => [gdCtx]
  (* g *)
  | 8 => [gdCtx]
  (* g, u_t : (g ⊢C Nat @0) *)
  | 9 => [gdTm (cvar 0) lC tyNat lzero; gdCtx]
  (* ℓ; g, U_M : (g, x : Nat ⊢C @ℓ), u_s : (g ⊢C U_M^{id,0/x} @ℓ),
     u_s' : (g, x : Nat, y : U_M^id @ℓ ⊢C U_M^{id,succ x/x} @ℓ), u_t : (g ⊢C Nat @0) *)
  | 10 => [gdTm (cvar 3) lC tyNat lzero;
           gdTm (cvar 2 ,, tyNat @ lzero ,, gv 1 @ lvar 0) lC (tyGvar 1 lsucc) (lvar 0);
           gdTm (cvar 1) lC (tyGvar 0 (lsingle zero)) (lvar 0);
           gdTy (cvar 0 ,, tyNat @ lzero) lC (lvar 0); gdCtx]
  (* ℓ ℓ'; g, U_S : (g ⊢C @ℓ), U_T : (g, x : U_S^id ⊢P @ℓ'),
     u_t : (g, x : U_S^id ⊢C U_T^id @ℓ') *)
  | 11 => [gdTm (cvar 2 ,, gv 1 @ lvar 1) lC (gv 0) (lvar 0);
           gdTy (cvar 1 ,, gv 0 @ lvar 1) lD (lvar 0);
           gdTy (cvar 0) lC (lvar 1); gdCtx]
  (* ℓ ℓ'; g, U_S, U_T (both C), u_t : (g ⊢C Π U_S^id U_T^id @ℓ⊔ℓ'), u_s : (g ⊢C U_S^id @ℓ) *)
  | 12 => [gdTm (cvar 3) lC (gv 2) (lvar 1);
           gdTm (cvar 2) lC (tyPi (lvar 1) (lvar 0) (gv 1) (gv 0)) (lmax (lvar 1) (lvar 0));
           gdTy (cvar 1 ,, gv 0 @ lvar 1) lC (lvar 0);
           gdTy (cvar 0) lC (lvar 1); gdCtx]
  | _ => []
  end.

Definition br_nu (k : nat) : nat := let '(nu, _, _) := br_ar k in nu.
Definition br_ng (k : nat) : nat := let '(_, ng, _) := br_ar k in ng.
Definition br_nl (k : nat) : nat := let '(_, _, nl) := br_ar k in nl.

(** ** Recursive calls and results as data (M8_DESIGN.md J2, S1)

    A recursive call (and a branch's result) is described by branch-scope
    syntax only: the motive it instantiates ([rcT] for [M_Typ], [rct] for
    [M_Trm]), the level, the index context, for a term call the index type,
    and the boxed code. The motive itself is supplied when the descriptor
    is read ([call_ty]): at call [j] of a branch with [nu] levels and [ng]
    globals, it is weakened past the [j] earlier calls ([wkb nu ng j]). *)
Inductive rcall : Type :=
| rcT (lv : lvl) (g : ctx) (c : tm)
| rct (lv : lvl) (g : ctx) (U : ty) (c : tm).

Definition call_ty (nu ng j : nat) (wT wt : tm) (x : rcall) : ty :=
  match x with
  | rcT lv g c => motT (wkb nu ng j wT) lv g c
  | rct lv g U c => mott (wkb nu ng j wt) lv g U c
  end.
Definition call_lv (a1 a2 : lvl) (x : rcall) : lvl :=
  match x with rcT _ _ _ => a1 | rct _ _ _ _ => a2 end.

Fixpoint mkLocs (nu ng j : nat) (wT wt : tm) (a1 a2 : lvl) (xs : list rcall) : list (ty * lvl) :=
  match xs with
  | [] => []
  | x :: xs => (call_ty nu ng j wT wt x, call_lv a1 a2 x) :: mkLocs nu ng (S j) wT wt a1 a2 xs
  end.

(** The recursive calls, in binding order. *)
Definition br_calls (k : nat) : list rcall :=
  match k with
  | 1 => [ rcT (lvar 1) (cvar 2) (boxT (gv 1));
           rcT (lvar 0) (cvar 2 ,, gv 1 @ lvar 1) (boxT (gv 0)) ]
  | 3 => [ rct (lsuc (lvar 0)) (cvar 1) (tyU (lvar 0)) (boxt (gu 0)) ]
  | 6 => [ rct (lsuc (lvar 1)) (cvar 2) (tyU (lvar 1)) (boxt (gu 1));
           rct (lsuc (lvar 0)) (cvar 2 ,, tyEl (lvar 1) (gu 1) @ lvar 1) (tyU (lvar 0)) (boxt (gu 0)) ]
  | 9 => [ rct lzero (cvar 1) tyNat (boxt (gu 0)) ]
  | 10 => [ rcT (lvar 0) (cvar 4 ,, tyNat @ lzero) (boxT (gv 3));
            rct (lvar 0) (cvar 4) (tyGvar 3 (lsingle zero)) (boxt (gu 2));
            rct (lvar 0) (cvar 4 ,, tyNat @ lzero ,, gv 3 @ lvar 0) (tyGvar 3 lsucc) (boxt (gu 1));
            rct lzero (cvar 4) tyNat (boxt (gu 0)) ]
  | 11 => [ rcT (lvar 1) (cvar 3) (boxT (gv 2));
            rct (lvar 0) (cvar 3 ,, gv 2 @ lvar 1) (gv 1) (boxt (gu 0)) ]
  | 12 => [ rcT (lvar 1) (cvar 4) (boxT (gv 3));
            rcT (lvar 0) (cvar 4 ,, gv 3 @ lvar 1) (boxT (gv 2));
            rct (lmax (lvar 1) (lvar 0)) (cvar 4) (tyPi (lvar 1) (lvar 0) (gv 3) (gv 2)) (boxt (gu 1));
            rct (lvar 1) (cvar 4) (gv 3) (boxt (gu 0)) ]
  | _ => []
  end.

(** The branch's result: the motive at the branch's code. *)
Definition br_head (k : nat) : rcall :=
  match k with
  | 0 => rcT lzero (cvar 0) (boxT tyNat)
  | 1 => rcT (lmax (lvar 1) (lvar 0)) (cvar 2) (boxT (tyPi (lvar 1) (lvar 0) (gv 1) (gv 0)))
  | 2 => rcT (lsuc (lvar 0)) (cvar 0) (boxT (tyU (lvar 0)))
  | 3 => rcT (lvar 0) (cvar 1) (boxT (tyEl (lvar 0) (gu 0)))
  | 4 => rct (lvar 0) (cvar 2) (gv 1) (boxt (gu 0))
  | 5 => rct (lsuc lzero) (cvar 0) (tyU lzero) (boxt tmNat)
  | 6 => rct (lsuc (lmax (lvar 1) (lvar 0))) (cvar 2) (tyU (lmax (lvar 1) (lvar 0)))
           (boxt (tmPi (lvar 1) (lvar 0) (gu 1) (gu 0)))
  | 7 => rct (lsuc (lsuc (lvar 0))) (cvar 0) (tyU (lsuc (lvar 0))) (boxt (tmU (lvar 0)))
  | 8 => rct lzero (cvar 0) tyNat (boxt zero)
  | 9 => rct lzero (cvar 1) tyNat (boxt (succ (gu 0)))
  | 10 => rct (lvar 0) (cvar 4) (tyGvar 3 (lsingle (gu 0)))
            (boxt (natrec (lvar 0) (gv 3) (gu 2) (gu 1) (gu 0)))
  | 11 => rct (lmax (lvar 1) (lvar 0)) (cvar 3) (tyPi (lvar 1) (lvar 0) (gv 2) (gv 1))
            (boxt (lam (lvar 1) (lvar 0) (gv 2) (gu 0)))
  | 12 => rct (lvar 0) (cvar 4) (tyGvar 2 (lsingle (gu 0)))
            (boxt (app (gu 1) (lvar 1) (lvar 0) (gv 3) (gv 2) (gu 0)))
  | _ => rcT lzero cnil (boxT tyErr)
  end.

(** The recursive calls' types, in binding order; [wT]/[wt] are the
    ambient wrapped motives, [a1]/[a2] the levels [l₁]/[l₂] already shifted
    past the branch's levels. *)
Definition brLocs (k : nat) (wT wt : tm) (a1 a2 : lvl) : list (ty * lvl) :=
  mkLocs (br_nu k) (br_ng k) 0 wT wt a1 a2 (br_calls k).

(** The branch's type. *)
Definition brRes (k : nat) (wT wt : tm) : ty := call_ty (br_nu k) (br_ng k) (br_nl k) wT wt (br_head k).

(** The branch's level: [l₁] for the type branches, [l₂] for the others. *)
Definition brLv (k : nat) (l1 l2 : lvl) : lvl :=
  lvren (if br_isT k then l1 else l2) (ush (br_nu k)).

Fixpoint cexts (Γ : ctx) (As : list (ty * lvl)) : ctx :=
  match As with [] => Γ | (A, l) :: As => cexts (Γ ,, A @ l) As end.

Definition brG (k : nat) (G : gctx) : gctx :=
  let G1 := gctx_uwk (br_nu k) G in mkG (gL G1) (brDecls k ++ gΨ G1).
Definition brΓ (k : nat) (Γ : ctx) (wT wt : tm) (l1 l2 : lvl) : ctx :=
  cexts (wkc (br_nu k) (br_ng k) Γ)
    (brLocs k wT wt (lvren l1 (ush (br_nu k))) (lvren l2 (ush (br_nu k)))).

(** Sanity: the declared scopes agree with the arity table. *)
Lemma brDecls_len k : k < nbr -> length (brDecls k) = br_ng k.
Proof. intros H; br_all ltac:(destruct k; [reflexivity|]); lia. Qed.
Lemma brLocs_len k wT wt a1 a2 : k < nbr -> length (brLocs k wT wt a1 a2) = br_nl k.
Proof. intros H; br_all ltac:(destruct k; [reflexivity|]); lia. Qed.
