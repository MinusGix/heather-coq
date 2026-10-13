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
  | gdDef Δ T l t => gdDef (ucren Δ ρ) (uren_ty T ρ) (lvren l ρ) (uren_tm t ρ)
  end.
Definition gdecl_usubst (D : gdecl) (φ : nat -> lvl) : gdecl :=
  match D with
  | gdCtx => gdCtx
  | gdTy Δ i l => gdTy (ucsubst Δ φ) i (lvsubst l φ)
  | gdTm Δ i T l => gdTm (ucsubst Δ φ) i (usubst_ty T φ) (lvsubst l φ)
  | gdDef Δ T l t => gdDef (ucsubst Δ φ) (usubst_ty T φ) (lvsubst l φ) (usubst_tm t φ)
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
  (* Heather's extension branches (M8_DESIGN.md L2) *)
  (* ℓ ℓ'; g, U_S, U_T: as t_Π *)
  | 13 => [gdTy (cvar 1 ,, gv 0 @ lvar 1) lC (lvar 0); gdTy (cvar 0) lC (lvar 1); gdCtx]
  (* ℓ; g *)
  | 14 => [gdCtx]
  (* ℓ ℓ'; g, u_s, u_t: as t'_Π *)
  | 15 => [gdTm (cvar 1 ,, tyEl (lvar 1) (gu 0) @ lvar 1) lC (tyU (lvar 0)) (lsuc (lvar 0));
           gdTm (cvar 0) lC (tyU (lvar 1)) (lsuc (lvar 1)); gdCtx]
  (* ℓ ℓ'; g, U_S, U_T, u_a : (g ⊢C U_S^id @ℓ), u_b : (g ⊢C U_T^{id,u_a^id/x} @ℓ') *)
  | 16 => [gdTm (cvar 3) lC (tyGvar 1 (lsingle (gu 0))) (lvar 0);
           gdTm (cvar 2) lC (gv 1) (lvar 1);
           gdTy (cvar 1 ,, gv 0 @ lvar 1) lC (lvar 0);
           gdTy (cvar 0) lC (lvar 1); gdCtx]
  (* ℓ ℓ'; g, U_S, U_T, u_p : (g ⊢C Σ U_S^id U_T^id @ℓ⊔ℓ') *)
  | 17 | 18 => [gdTm (cvar 2) lC (tySig (lvar 1) (lvar 0) (gv 1) (gv 0)) (lmax (lvar 1) (lvar 0));
                gdTy (cvar 1 ,, gv 0 @ lvar 1) lC (lvar 0);
                gdTy (cvar 0) lC (lvar 1); gdCtx]
  (* ℓ; g *)
  | 19 | 20 => [gdCtx]
  (* the identity type (M11b) *)
  (* ℓ; g, U_S : (g ⊢C @ℓ), u_t, u_u : (g ⊢C U_S^id @ℓ) *)
  | 21 => [gdTm (cvar 2) lC (gv 1) (lvar 0); gdTm (cvar 1) lC (gv 0) (lvar 0);
           gdTy (cvar 0) lC (lvar 0); gdCtx]
  (* ℓ; g, u_S : (g ⊢C Ty ℓ @1+ℓ), u_t, u_u : (g ⊢C El ℓ u_S^id @ℓ) *)
  | 22 => [gdTm (cvar 2) lC (tyEl (lvar 0) (gu 1)) (lvar 0); gdTm (cvar 1) lC (tyEl (lvar 0) (gu 0)) (lvar 0);
           gdTm (cvar 0) lC (tyU (lvar 0)) (lsuc (lvar 0)); gdCtx]
  (* ℓ; g, U_S, u_t : (g ⊢C U_S^id @ℓ) *)
  | 23 => [gdTm (cvar 1) lC (gv 0) (lvar 0); gdTy (cvar 0) lC (lvar 0); gdCtx]
  (* ℓ ℓ'; g, U_S, u_a : (g ⊢C U_S^id @ℓ), U_M : (g, y : U_S^id, p : Id(U_S^id↑; u_a^id↑; y) ⊢C @ℓ'),
     u_c : (g ⊢C U_M^{id, u_a^id/y, refl(U_S^id; u_a^id)/p} @ℓ'), u_r : (g ⊢C U_S^id @ℓ),
     u_e : (g ⊢C Id(U_S^id; u_a^id; u_r^id) @ℓ) *)
  | 24 => [gdTm (cvar 5) lC (tyId (lvar 1) (gv 4) (gu 3) (gu 0)) (lvar 1);
           gdTm (cvar 4) lC (gv 3) (lvar 1);
           gdTm (cvar 3) lC (tyGvar 0 (lsingle2 (gu 1) (tmRefl (lvar 1) (gv 2) (gu 1)))) (lvar 0);
           gdTy (cvar 2 ,, gv 1 @ lvar 1 ,, tyId (lvar 1) (gv 1)⟨↑⟩ (gu 0)⟨↑⟩ (var 0) @ lvar 1) lC (lvar 0);
           gdTm (cvar 1) lC (gv 0) (lvar 1);
           gdTy (cvar 0) lC (lvar 1); gdCtx]
  (* strict equality (M10c), as the identity type *)
  | 25 => [gdTm (cvar 2) lC (gv 1) (lvar 0); gdTm (cvar 1) lC (gv 0) (lvar 0);
           gdTy (cvar 0) lC (lvar 0); gdCtx]
  | 26 => [gdTm (cvar 2) lC (tyEl (lvar 0) (gu 1)) (lvar 0); gdTm (cvar 1) lC (tyEl (lvar 0) (gu 0)) (lvar 0);
           gdTm (cvar 0) lC (tyU (lvar 0)) (lsuc (lvar 0)); gdCtx]
  | 27 | 28 => [gdCtx]
  | 29 => [gdTm (cvar 1) lC (gv 0) (lvar 0); gdTy (cvar 0) lC (lvar 0); gdCtx]
  (* ℓ ℓ'; g, U_M : (g ⊢C @ℓ), u_t : (g ⊢C sEmpty^ℓ' @ℓ'): the motive is not
     dependent, as [elimSEmpty]'s (M10a) *)
  | 30 => [gdTm (cvar 1) lC (tySEmpty (lvar 0)) (lvar 0); gdTy (cvar 0) lC (lvar 1); gdCtx]
  (* the empty type and binary sums (M12c), Heather's order *)
  (* ℓ; g *)
  | 31 | 32 => [gdCtx]
  (* ℓ ℓ'; g, U_M : (g, x : Empty^ℓ' ⊢C @ℓ), u_t : (g ⊢C Empty^ℓ' @ℓ') *)
  | 33 => [gdTm (cvar 1) lC (tyEmpty (lvar 0)) (lvar 0);
           gdTy (cvar 0 ,, tyEmpty (lvar 0) @ lvar 0) lC (lvar 1); gdCtx]
  (* ℓ ℓ'; g, U_A : (g ⊢C @ℓ), U_B : (g ⊢C @ℓ') *)
  | 34 => [gdTy (cvar 1) lC (lvar 0); gdTy (cvar 0) lC (lvar 1); gdCtx]
  (* ℓ ℓ'; g, u_a : (g ⊢C Ty ℓ @1+ℓ), u_b : (g ⊢C Ty ℓ' @1+ℓ') *)
  | 35 => [gdTm (cvar 1) lC (tyU (lvar 0)) (lsuc (lvar 0));
           gdTm (cvar 0) lC (tyU (lvar 1)) (lsuc (lvar 1)); gdCtx]
  (* ℓ ℓ'; g, U_A, U_B, u_a : (g ⊢C U_A^id @ℓ) *)
  | 36 => [gdTm (cvar 2) lC (gv 1) (lvar 1); gdTy (cvar 1) lC (lvar 0); gdTy (cvar 0) lC (lvar 1); gdCtx]
  (* ℓ ℓ'; g, U_A, U_B, u_b : (g ⊢C U_B^id @ℓ') *)
  | 37 => [gdTm (cvar 2) lC (gv 0) (lvar 0); gdTy (cvar 1) lC (lvar 0); gdTy (cvar 0) lC (lvar 1); gdCtx]
  (* ℓ ℓ' ℓ''; g, U_A, U_B, U_M : (g, z : U_A^id + U_B^id ⊢C @ℓ''),
     u_l : (g, x : U_A^id ⊢C U_M^{↑, inl x/z} @ℓ''), u_r : (g, y : U_B^id ⊢C U_M^{↑, inr y/z} @ℓ''),
     u_t : (g ⊢C U_A^id + U_B^id @ℓ⊔ℓ') *)
  | 38 => [gdTm (cvar 5) lC (tySum (lvar 2) (lvar 1) (gv 4) (gv 3)) (lmax (lvar 2) (lvar 1));
           gdTm (cvar 4 ,, gv 2 @ lvar 1) lC
             (tyGvar 1 (lcons (lshift 1) (tmInr (lvar 2) (lvar 1) (gv 3)⟨↑⟩ (gv 2)⟨↑⟩ (var 0)))) (lvar 0);
           gdTm (cvar 3 ,, gv 2 @ lvar 2) lC
             (tyGvar 0 (lcons (lshift 1) (tmInl (lvar 2) (lvar 1) (gv 2)⟨↑⟩ (gv 1)⟨↑⟩ (var 0)))) (lvar 0);
           gdTy (cvar 2 ,, tySum (lvar 2) (lvar 1) (gv 1) (gv 0) @ lmax (lvar 2) (lvar 1)) lC (lvar 0);
           gdTy (cvar 1) lC (lvar 1); gdTy (cvar 0) lC (lvar 2); gdCtx]
  (* W-types (M13b). ℓ ℓ'; g, U_S, U_T: as t_Σ *)
  | 39 => [gdTy (cvar 1 ,, gv 0 @ lvar 1) lC (lvar 0); gdTy (cvar 0) lC (lvar 1); gdCtx]
  (* ℓ ℓ'; g, u_s, u_t: as t'_Σ *)
  | 40 => [gdTm (cvar 1 ,, tyEl (lvar 1) (gu 0) @ lvar 1) lC (tyU (lvar 0)) (lsuc (lvar 0));
           gdTm (cvar 0) lC (tyU (lvar 1)) (lsuc (lvar 1)); gdCtx]
  (* ℓ ℓ'; g, U_S, U_T, u_a : (g ⊢C U_S^id @ℓ),
     u_f : (g ⊢C Π(y : U_T^{id,u_a^id/x}). (W U_S^id U_T^id)^↑ @ℓ'⊔ℓ⊔ℓ') *)
  | 41 => [gdTm (cvar 3) lC (tyPi (lvar 0) (lmax (lvar 1) (lvar 0)) (tyGvar 1 (lsingle (gu 0)))
                                (tyW (lvar 1) (lvar 0) (gv 2) (gv 1))⟨↑⟩)
             (lmax (lvar 0) (lmax (lvar 1) (lvar 0)));
           gdTm (cvar 2) lC (gv 1) (lvar 1);
           gdTy (cvar 1 ,, gv 0 @ lvar 1) lC (lvar 0);
           gdTy (cvar 0) lC (lvar 1); gdCtx]
  (* ℓ ℓ' ℓ''; g, U_S, U_T, U_M : (g, w : W U_S^id U_T^id ⊢C @ℓ''),
     u_s : (g, x : U_S^id, f : wfty, h : wihty ⊢C wstepty @ℓ''),
     u_t : (g ⊢C W U_S^id U_T^id @ℓ⊔ℓ') *)
  | 42 => [gdTm (cvar 4) lC (tyW (lvar 2) (lvar 1) (gv 3) (gv 2)) (lmax (lvar 2) (lvar 1));
           gdTm (cvar 3 ,, gv 2 @ lvar 2
                        ,, wfty (lvar 2) (lvar 1) (gv 2) (gv 1) @ lmax (lvar 1) (lmax (lvar 2) (lvar 1))
                        ,, wihty (lvar 2) (lvar 1) (lvar 0) (gv 2) (gv 1) (gv 0) @ lmax (lvar 1) (lvar 0)) lC
             (wstepty (lvar 2) (lvar 1) (gv 2) (gv 1) (gv 0)) (lvar 0);
           gdTy (cvar 2 ,, tyW (lvar 2) (lvar 1) (gv 1) (gv 0) @ lmax (lvar 2) (lvar 1)) lC (lvar 0);
           gdTy (cvar 1 ,, gv 0 @ lvar 2) lC (lvar 1); gdTy (cvar 0) lC (lvar 2); gdCtx]
  (* length-indexed tuples and finite indices (M14b), Heather's telescopes *)
  (* ℓ; g, U_T : (g ⊢C @ℓ), u_k : (g ⊢C Nat @0) *)
  | 43 => [gdTm (cvar 1) lC tyNat lzero; gdTy (cvar 0) lC (lvar 0); gdCtx]
  (* ℓ; g, u_t : (g ⊢C Ty ℓ @1+ℓ), u_k : (g ⊢C Nat @0) *)
  | 44 => [gdTm (cvar 1) lC tyNat lzero; gdTm (cvar 0) lC (tyU (lvar 0)) (lsuc (lvar 0)); gdCtx]
  (* g, u_k : (g ⊢C Nat @0): no level binder, [Fin] lives at 0 *)
  | 45 | 46 => [gdTm (cvar 0) lC tyNat lzero; gdCtx]
  (* finitary well-founded trees (M15b), M15_DESIGN.md's derivation *)
  (* ℓ; g, U_S : (g ⊢C @ℓ), u_n : (g, x : U_S^id @ℓ ⊢C Nat @0) *)
  | 47 => [gdTm (cvar 1 ,, gv 0 @ lvar 0) lC tyNat lzero; gdTy (cvar 0) lC (lvar 0); gdCtx]
  (* ℓ; g, u_s : (g ⊢C Ty ℓ @1+ℓ), u_n : (g, x : El ℓ u_s^id @ℓ ⊢C Nat @0) *)
  | 48 => [gdTm (cvar 1 ,, tyEl (lvar 0) (gu 0) @ lvar 0) lC tyNat lzero;
           gdTm (cvar 0) lC (tyU (lvar 0)) (lsuc (lvar 0)); gdCtx]
  (* ℓ; g, U_S, u_n, u_a : (g ⊢C U_S^id @ℓ),
     u_cs : (g ⊢C Vec^ℓ(Wf^ℓ(x : U_S^id). u_n^id; u_n^{id,u_a/x}) @ℓ) *)
  | 49 => [gdTm (cvar 3) lC (tyVec (lvar 0) (tyWf (lvar 0) (gv 2) (gu 1)) (gvar 1 (lsingle (gu 0)))) (lvar 0);
           gdTm (cvar 2) lC (gv 1) (lvar 0);
           gdTm (cvar 1 ,, gv 0 @ lvar 0) lC tyNat lzero; gdTy (cvar 0) lC (lvar 0); gdCtx]
  (* ℓ ℓ'; g, U_S, u_n, U_M : (g, z : Wf @ℓ ⊢C @ℓ'),
     u_s : (g, a : U_S^id, cs : wfcsty, ih : wfihty ⊢C wfstepty @ℓ'), u_t : (g ⊢C Wf @ℓ) *)
  | 50 => [gdTm (cvar 4) lC (tyWf (lvar 1) (gv 3) (gu 2)) (lvar 1);
           gdTm (cvar 3 ,, gv 2 @ lvar 1 ,, wfcsty (lvar 1) (gv 2) (gu 1) @ lvar 1
                        ,, wfihty (lvar 1) (lvar 0) (gv 2) (gu 1) (gv 0) @ lmax lzero (lvar 0)) lC
             (wfstepty (lvar 1) (gv 2) (gu 1) (gv 0)) (lvar 0);
           gdTy (cvar 2 ,, tyWf (lvar 1) (gv 1) (gu 0) @ lvar 1) lC (lvar 0);
           gdTm (cvar 1 ,, gv 0 @ lvar 1) lC tyNat lzero; gdTy (cvar 0) lC (lvar 1); gdCtx]
  (* propositional truncation (M16b), Heather's telescopes *)
  (* ℓ; g, U_A : (g ⊢C @ℓ) *)
  | 51 => [gdTy (cvar 0) lC (lvar 0); gdCtx]
  (* ℓ; g, u_s : (g ⊢C Ty ℓ @1+ℓ) *)
  | 52 => [gdTm (cvar 0) lC (tyU (lvar 0)) (lsuc (lvar 0)); gdCtx]
  (* ℓ; g, U_A, u_a : (g ⊢C U_A^id @ℓ) *)
  | 53 => [gdTm (cvar 1) lC (gv 0) (lvar 0); gdTy (cvar 0) lC (lvar 0); gdCtx]
  (* ℓ ℓ'; g, U_A, U_M : (g, z : ∥U_A^id∥ @ℓ ⊢C @ℓ'),
     u_c : (g, x : U_A^id ⊢C ∥U_M^{↑, squash x/z}∥ @ℓ'), u_t : (g ⊢C ∥U_A^id∥ @ℓ) *)
  | 54 => [gdTm (cvar 3) lC (tySq (lvar 1) (gv 2)) (lvar 1);
           gdTm (cvar 2 ,, gv 1 @ lvar 1) lC
             (tySq (lvar 0) (tyGvar 0 (lcons (lshift 1) (tmSq (lvar 1) (gv 1)⟨↑⟩ (var 0))))) (lvar 0);
           gdTy (cvar 1 ,, tySq (lvar 1) (gv 0) @ lvar 1) lC (lvar 0);
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

(** The recursive calls, derived from the scope (M15b step 0; HEATHER.md,
    direction 1): one call per layer-C global, oldest first. The global at
    position [p] of [brDecls] (0 is the most recent) is read in the branch
    scope weakened past itself and the [p] later ones ([ush (S p)]); a type
    global gives a call at [M_Typ], a term global one at [M_Trm]. A layer-D
    or V global (the [λ] branch's codomain, [var]'s payload) gives none.
    [br_calls] below stays a written table, in the notation forms the
    branch proofs rewrite with (a computed table would normalize [elim_Wf]'s
    step telescope past its notations); [br_calls_derived] checks every
    entry against this function, and [br_nl] against its length. *)
Definition call_of (p : nat) (D : gdecl) : list rcall :=
  match D with
  | gdTy Δ lC l => [rcT l (gcren Δ (ush (S p))) (boxT (gv p))]
  | gdTm Δ lC T l => [rct l (gcren Δ (ush (S p))) (gren_ty T (ush (S p))) (boxt (gu p))]
  | _ => []
  end.
Fixpoint calls_from (p : nat) (ds : list gdecl) : list rcall :=
  match ds with [] => [] | D :: ds => calls_from (S p) ds ++ call_of p D end.
Definition derived_calls (k : nat) : list rcall := calls_from 0 (brDecls k).

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
  | 13 => [ rcT (lvar 1) (cvar 2) (boxT (gv 1));
            rcT (lvar 0) (cvar 2 ,, gv 1 @ lvar 1) (boxT (gv 0)) ]
  | 15 => [ rct (lsuc (lvar 1)) (cvar 2) (tyU (lvar 1)) (boxt (gu 1));
            rct (lsuc (lvar 0)) (cvar 2 ,, tyEl (lvar 1) (gu 1) @ lvar 1) (tyU (lvar 0)) (boxt (gu 0)) ]
  | 16 => [ rcT (lvar 1) (cvar 4) (boxT (gv 3));
            rcT (lvar 0) (cvar 4 ,, gv 3 @ lvar 1) (boxT (gv 2));
            rct (lvar 1) (cvar 4) (gv 3) (boxt (gu 1));
            rct (lvar 0) (cvar 4) (tyGvar 2 (lsingle (gu 1))) (boxt (gu 0)) ]
  | 17 | 18 => [ rcT (lvar 1) (cvar 3) (boxT (gv 2));
                 rcT (lvar 0) (cvar 3 ,, gv 2 @ lvar 1) (boxT (gv 1));
                 rct (lmax (lvar 1) (lvar 0)) (cvar 3) (tySig (lvar 1) (lvar 0) (gv 2) (gv 1)) (boxt (gu 0)) ]
  | 21 => [ rcT (lvar 0) (cvar 3) (boxT (gv 2));
            rct (lvar 0) (cvar 3) (gv 2) (boxt (gu 1));
            rct (lvar 0) (cvar 3) (gv 2) (boxt (gu 0)) ]
  | 22 => [ rct (lsuc (lvar 0)) (cvar 3) (tyU (lvar 0)) (boxt (gu 2));
            rct (lvar 0) (cvar 3) (tyEl (lvar 0) (gu 2)) (boxt (gu 1));
            rct (lvar 0) (cvar 3) (tyEl (lvar 0) (gu 2)) (boxt (gu 0)) ]
  | 23 => [ rcT (lvar 0) (cvar 2) (boxT (gv 1));
            rct (lvar 0) (cvar 2) (gv 1) (boxt (gu 0)) ]
  | 24 => [ rcT (lvar 1) (cvar 6) (boxT (gv 5));
            rct (lvar 1) (cvar 6) (gv 5) (boxt (gu 4));
            rcT (lvar 0) (cvar 6 ,, gv 5 @ lvar 1 ,, tyId (lvar 1) (gv 5)⟨↑⟩ (gu 4)⟨↑⟩ (var 0) @ lvar 1) (boxT (gv 3));
            rct (lvar 0) (cvar 6) (tyGvar 3 (lsingle2 (gu 4) (tmRefl (lvar 1) (gv 5) (gu 4)))) (boxt (gu 2));
            rct (lvar 1) (cvar 6) (gv 5) (boxt (gu 1));
            rct (lvar 1) (cvar 6) (tyId (lvar 1) (gv 5) (gu 4) (gu 1)) (boxt (gu 0)) ]
  | 25 => [ rcT (lvar 0) (cvar 3) (boxT (gv 2));
            rct (lvar 0) (cvar 3) (gv 2) (boxt (gu 1));
            rct (lvar 0) (cvar 3) (gv 2) (boxt (gu 0)) ]
  | 26 => [ rct (lsuc (lvar 0)) (cvar 3) (tyU (lvar 0)) (boxt (gu 2));
            rct (lvar 0) (cvar 3) (tyEl (lvar 0) (gu 2)) (boxt (gu 1));
            rct (lvar 0) (cvar 3) (tyEl (lvar 0) (gu 2)) (boxt (gu 0)) ]
  | 29 => [ rcT (lvar 0) (cvar 2) (boxT (gv 1));
            rct (lvar 0) (cvar 2) (gv 1) (boxt (gu 0)) ]
  | 30 => [ rcT (lvar 1) (cvar 2) (boxT (gv 1));
            rct (lvar 0) (cvar 2) (tySEmpty (lvar 0)) (boxt (gu 0)) ]
  | 33 => [ rcT (lvar 1) (cvar 2 ,, tyEmpty (lvar 0) @ lvar 0) (boxT (gv 1));
            rct (lvar 0) (cvar 2) (tyEmpty (lvar 0)) (boxt (gu 0)) ]
  | 34 => [ rcT (lvar 1) (cvar 2) (boxT (gv 1)); rcT (lvar 0) (cvar 2) (boxT (gv 0)) ]
  | 35 => [ rct (lsuc (lvar 1)) (cvar 2) (tyU (lvar 1)) (boxt (gu 1));
            rct (lsuc (lvar 0)) (cvar 2) (tyU (lvar 0)) (boxt (gu 0)) ]
  | 36 => [ rcT (lvar 1) (cvar 3) (boxT (gv 2)); rcT (lvar 0) (cvar 3) (boxT (gv 1));
            rct (lvar 1) (cvar 3) (gv 2) (boxt (gu 0)) ]
  | 37 => [ rcT (lvar 1) (cvar 3) (boxT (gv 2)); rcT (lvar 0) (cvar 3) (boxT (gv 1));
            rct (lvar 0) (cvar 3) (gv 1) (boxt (gu 0)) ]
  | 38 => [ rcT (lvar 2) (cvar 6) (boxT (gv 5)); rcT (lvar 1) (cvar 6) (boxT (gv 4));
            rcT (lvar 0) (cvar 6 ,, tySum (lvar 2) (lvar 1) (gv 5) (gv 4) @ lmax (lvar 2) (lvar 1)) (boxT (gv 3));
            rct (lvar 0) (cvar 6 ,, gv 5 @ lvar 2)
              (tyGvar 3 (lcons (lshift 1) (tmInl (lvar 2) (lvar 1) (gv 5)⟨↑⟩ (gv 4)⟨↑⟩ (var 0)))) (boxt (gu 2));
            rct (lvar 0) (cvar 6 ,, gv 4 @ lvar 1)
              (tyGvar 3 (lcons (lshift 1) (tmInr (lvar 2) (lvar 1) (gv 5)⟨↑⟩ (gv 4)⟨↑⟩ (var 0)))) (boxt (gu 1));
            rct (lmax (lvar 2) (lvar 1)) (cvar 6) (tySum (lvar 2) (lvar 1) (gv 5) (gv 4)) (boxt (gu 0)) ]
  | 39 => [ rcT (lvar 1) (cvar 2) (boxT (gv 1));
            rcT (lvar 0) (cvar 2 ,, gv 1 @ lvar 1) (boxT (gv 0)) ]
  | 40 => [ rct (lsuc (lvar 1)) (cvar 2) (tyU (lvar 1)) (boxt (gu 1));
            rct (lsuc (lvar 0)) (cvar 2 ,, tyEl (lvar 1) (gu 1) @ lvar 1) (tyU (lvar 0)) (boxt (gu 0)) ]
  | 41 => [ rcT (lvar 1) (cvar 4) (boxT (gv 3));
            rcT (lvar 0) (cvar 4 ,, gv 3 @ lvar 1) (boxT (gv 2));
            rct (lvar 1) (cvar 4) (gv 3) (boxt (gu 1));
            rct (lmax (lvar 0) (lmax (lvar 1) (lvar 0))) (cvar 4)
              (tyPi (lvar 0) (lmax (lvar 1) (lvar 0)) (tyGvar 2 (lsingle (gu 1)))
                 (tyW (lvar 1) (lvar 0) (gv 3) (gv 2))⟨↑⟩) (boxt (gu 0)) ]
  | 42 => [ rcT (lvar 2) (cvar 5) (boxT (gv 4));
            rcT (lvar 1) (cvar 5 ,, gv 4 @ lvar 2) (boxT (gv 3));
            rcT (lvar 0) (cvar 5 ,, tyW (lvar 2) (lvar 1) (gv 4) (gv 3) @ lmax (lvar 2) (lvar 1)) (boxT (gv 2));
            rct (lvar 0) (cvar 5 ,, gv 4 @ lvar 2
                                ,, wfty (lvar 2) (lvar 1) (gv 4) (gv 3) @ lmax (lvar 1) (lmax (lvar 2) (lvar 1))
                                ,, wihty (lvar 2) (lvar 1) (lvar 0) (gv 4) (gv 3) (gv 2) @ lmax (lvar 1) (lvar 0))
              (wstepty (lvar 2) (lvar 1) (gv 4) (gv 3) (gv 2)) (boxt (gu 1));
            rct (lmax (lvar 2) (lvar 1)) (cvar 5) (tyW (lvar 2) (lvar 1) (gv 4) (gv 3)) (boxt (gu 0)) ]
  | 43 => [ rcT (lvar 0) (cvar 2) (boxT (gv 1)); rct lzero (cvar 2) tyNat (boxt (gu 0)) ]
  | 44 => [ rct (lsuc (lvar 0)) (cvar 2) (tyU (lvar 0)) (boxt (gu 1)); rct lzero (cvar 2) tyNat (boxt (gu 0)) ]
  | 45 | 46 => [ rct lzero (cvar 1) tyNat (boxt (gu 0)) ]
  (* finitary well-founded trees (M15b); [br_calls_derived] checks them *)
  | 47 => [ rcT (lvar 0) (cvar 2) (boxT (gv 1)); rct lzero (cvar 2 ,, gv 1 @ lvar 0) tyNat (boxt (gu 0)) ]
  | 48 => [ rct (lsuc (lvar 0)) (cvar 2) (tyU (lvar 0)) (boxt (gu 1));
            rct lzero (cvar 2 ,, tyEl (lvar 0) (gu 1) @ lvar 0) tyNat (boxt (gu 0)) ]
  | 49 => [ rcT (lvar 0) (cvar 4) (boxT (gv 3)); rct lzero (cvar 4 ,, gv 3 @ lvar 0) tyNat (boxt (gu 2));
            rct (lvar 0) (cvar 4) (gv 3) (boxt (gu 1));
            rct (lvar 0) (cvar 4) (tyVec (lvar 0) (tyWf (lvar 0) (gv 3) (gu 2)) (gvar 2 (lsingle (gu 1)))) (boxt (gu 0)) ]
  | 50 => [ rcT (lvar 1) (cvar 5) (boxT (gv 4)); rct lzero (cvar 5 ,, gv 4 @ lvar 1) tyNat (boxt (gu 3));
            rcT (lvar 0) (cvar 5 ,, tyWf (lvar 1) (gv 4) (gu 3) @ lvar 1) (boxT (gv 2));
            rct (lvar 0) (cvar 5 ,, gv 4 @ lvar 1 ,, wfcsty (lvar 1) (gv 4) (gu 3) @ lvar 1
                         ,, wfihty (lvar 1) (lvar 0) (gv 4) (gu 3) (gv 2) @ lmax lzero (lvar 0))
              (wfstepty (lvar 1) (gv 4) (gu 3) (gv 2)) (boxt (gu 1));
            rct (lvar 1) (cvar 5) (tyWf (lvar 1) (gv 4) (gu 3)) (boxt (gu 0)) ]
  (* propositional truncation (M16b); [br_calls_derived] checks them *)
  | 51 => [ rcT (lvar 0) (cvar 1) (boxT (gv 0)) ]
  | 52 => [ rct (lsuc (lvar 0)) (cvar 1) (tyU (lvar 0)) (boxt (gu 0)) ]
  | 53 => [ rcT (lvar 0) (cvar 2) (boxT (gv 1)); rct (lvar 0) (cvar 2) (gv 1) (boxt (gu 0)) ]
  | 54 => [ rcT (lvar 1) (cvar 4) (boxT (gv 3));
            rcT (lvar 0) (cvar 4 ,, tySq (lvar 1) (gv 3) @ lvar 1) (boxT (gv 2));
            rct (lvar 0) (cvar 4 ,, gv 3 @ lvar 1)
              (tySq (lvar 0) (tyGvar 2 (lcons (lshift 1) (tmSq (lvar 1) (gv 3)⟨↑⟩ (var 0))))) (boxt (gu 1));
            rct (lvar 1) (cvar 4) (tySq (lvar 1) (gv 3)) (boxt (gu 0)) ]
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
  | 13 => rcT (lmax (lvar 1) (lvar 0)) (cvar 2) (boxT (tySig (lvar 1) (lvar 0) (gv 1) (gv 0)))
  | 14 => rcT (lvar 0) (cvar 0) (boxT (tyUnit (lvar 0)))
  | 15 => rct (lsuc (lmax (lvar 1) (lvar 0))) (cvar 2) (tyU (lmax (lvar 1) (lvar 0)))
            (boxt (tmSig (lvar 1) (lvar 0) (gu 1) (gu 0)))
  | 16 => rct (lmax (lvar 1) (lvar 0)) (cvar 4) (tySig (lvar 1) (lvar 0) (gv 3) (gv 2))
            (boxt (tmPair (lvar 1) (lvar 0) (gv 3) (gv 2) (gu 1) (gu 0)))
  | 17 => rct (lvar 1) (cvar 3) (gv 2) (boxt (tmFst (lvar 1) (lvar 0) (gv 2) (gv 1) (gu 0)))
  | 18 => rct (lvar 0) (cvar 3) (tyGvar 1 (lsingle (tmFst (lvar 1) (lvar 0) (gv 2) (gv 1) (gu 0))))
            (boxt (tmSnd (lvar 1) (lvar 0) (gv 2) (gv 1) (gu 0)))
  | 19 => rct (lsuc (lvar 0)) (cvar 0) (tyU (lvar 0)) (boxt (tmUnit (lvar 0)))
  | 20 => rct (lvar 0) (cvar 0) (tyUnit (lvar 0)) (boxt (tmTriv (lvar 0)))
  | 21 => rcT (lvar 0) (cvar 3) (boxT (tyId (lvar 0) (gv 2) (gu 1) (gu 0)))
  | 22 => rct (lsuc (lvar 0)) (cvar 3) (tyU (lvar 0)) (boxt (tmId (lvar 0) (gu 2) (gu 1) (gu 0)))
  | 23 => rct (lvar 0) (cvar 2) (tyId (lvar 0) (gv 1) (gu 0) (gu 0)) (boxt (tmRefl (lvar 0) (gv 1) (gu 0)))
  | 24 => rct (lvar 0) (cvar 6) (tyGvar 3 (lsingle2 (gu 1) (gu 0)))
            (boxt (tmJ (lvar 1) (lvar 0) (gv 5) (gu 4) (gv 3) (gu 2) (gu 1) (gu 0)))
  | 25 => rcT (lvar 0) (cvar 3) (boxT (tySEq (lvar 0) (gv 2) (gu 1) (gu 0)))
  | 26 => rct (lsuc (lvar 0)) (cvar 3) (tyU (lvar 0)) (boxt (tmSEq (lvar 0) (gu 2) (gu 1) (gu 0)))
  | 27 => rcT (lvar 0) (cvar 0) (boxT (tySEmpty (lvar 0)))
  | 28 => rct (lsuc (lvar 0)) (cvar 0) (tyU (lvar 0)) (boxt (tmSEmpty (lvar 0)))
  | 29 => rct (lvar 0) (cvar 2) (tySEq (lvar 0) (gv 1) (gu 0) (gu 0)) (boxt (srefl (lvar 0) (gv 1) (gu 0)))
  | 30 => rct (lvar 1) (cvar 2) (gv 1) (boxt (elimSEmpty (lvar 0) (lvar 1) (gv 1) (gu 0)))
  | 31 => rcT (lvar 0) (cvar 0) (boxT (tyEmpty (lvar 0)))
  | 32 => rct (lsuc (lvar 0)) (cvar 0) (tyU (lvar 0)) (boxt (tmEmpty (lvar 0)))
  | 33 => rct (lvar 1) (cvar 2) (tyGvar 1 (lsingle (gu 0))) (boxt (elimEmpty (lvar 1) (lvar 0) (gv 1) (gu 0)))
  | 34 => rcT (lmax (lvar 1) (lvar 0)) (cvar 2) (boxT (tySum (lvar 1) (lvar 0) (gv 1) (gv 0)))
  | 35 => rct (lsuc (lmax (lvar 1) (lvar 0))) (cvar 2) (tyU (lmax (lvar 1) (lvar 0)))
            (boxt (tmSum (lvar 1) (lvar 0) (gu 1) (gu 0)))
  | 36 => rct (lmax (lvar 1) (lvar 0)) (cvar 3) (tySum (lvar 1) (lvar 0) (gv 2) (gv 1))
            (boxt (tmInl (lvar 1) (lvar 0) (gv 2) (gv 1) (gu 0)))
  | 37 => rct (lmax (lvar 1) (lvar 0)) (cvar 3) (tySum (lvar 1) (lvar 0) (gv 2) (gv 1))
            (boxt (tmInr (lvar 1) (lvar 0) (gv 2) (gv 1) (gu 0)))
  | 38 => rct (lvar 0) (cvar 6) (tyGvar 3 (lsingle (gu 0)))
            (boxt (tmCase (lvar 2) (lvar 1) (lvar 0) (gv 5) (gv 4) (gv 3) (gu 2) (gu 1) (gu 0)))
  | 39 => rcT (lmax (lvar 1) (lvar 0)) (cvar 2) (boxT (tyW (lvar 1) (lvar 0) (gv 1) (gv 0)))
  | 40 => rct (lsuc (lmax (lvar 1) (lvar 0))) (cvar 2) (tyU (lmax (lvar 1) (lvar 0)))
            (boxt (tmW (lvar 1) (lvar 0) (gu 1) (gu 0)))
  | 41 => rct (lmax (lvar 1) (lvar 0)) (cvar 4) (tyW (lvar 1) (lvar 0) (gv 3) (gv 2))
            (boxt (tmSup (lvar 1) (lvar 0) (gv 3) (gv 2) (gu 1) (gu 0)))
  | 42 => rct (lvar 0) (cvar 5) (tyGvar 2 (lsingle (gu 0)))
            (boxt (tmElimW (lvar 2) (lvar 1) (lvar 0) (gv 4) (gv 3) (gv 2) (gu 1) (gu 0)))
  | 43 => rcT (lvar 0) (cvar 2) (boxT (tyVec (lvar 0) (gv 1) (gu 0)))
  | 44 => rct (lsuc (lvar 0)) (cvar 2) (tyU (lvar 0)) (boxt (tmVec (lvar 0) (gu 1) (gu 0)))
  | 45 => rcT lzero (cvar 1) (boxT (tyFin (gu 0)))
  | 46 => rct (lsuc lzero) (cvar 1) (tyU lzero) (boxt (tmFin (gu 0)))
  | 47 => rcT (lvar 0) (cvar 2) (boxT (tyWf (lvar 0) (gv 1) (gu 0)))
  | 48 => rct (lsuc (lvar 0)) (cvar 2) (tyU (lvar 0)) (boxt (tmWf (lvar 0) (gu 1) (gu 0)))
  | 49 => rct (lvar 0) (cvar 4) (tyWf (lvar 0) (gv 3) (gu 2)) (boxt (tmSupf (lvar 0) (gv 3) (gu 2) (gu 1) (gu 0)))
  | 50 => rct (lvar 0) (cvar 5) (tyGvar 2 (lsingle (gu 0)))
            (boxt (tmElimWf (lvar 1) (lvar 0) (gv 4) (gu 3) (gv 2) (gu 1) (gu 0)))
  | 51 => rcT (lvar 0) (cvar 1) (boxT (tySq (lvar 0) (gv 0)))
  | 52 => rct (lsuc (lvar 0)) (cvar 1) (tyU (lvar 0)) (boxt (tmSqCode (lvar 0) (gu 0)))
  | 53 => rct (lvar 0) (cvar 2) (tySq (lvar 0) (gv 1)) (boxt (tmSq (lvar 0) (gv 1) (gu 0)))
  | 54 => rct (lvar 0) (cvar 4) (tySq (lvar 0) (tyGvar 2 (lsingle (gu 0))))
            (boxt (tmElimSq (lvar 1) (lvar 0) (gv 3) (gv 2) (gu 1) (gu 0)))
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

(** The call table is the derived one, and the arity's local count is its
    length, for every branch (M15b step 0). *)
Lemma br_calls_derived k : k < nbr -> br_calls k = derived_calls k /\ br_nl k = length (derived_calls k).
Proof. intros H; br_all ltac:(destruct k; [split; vm_compute; reflexivity|]); lia. Qed.
