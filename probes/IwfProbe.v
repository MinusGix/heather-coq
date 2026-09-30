(* Probe for the IWf design (Heather route 4, with output indices).
   Fin and DVec as Heather's type-level reductions; dnth derived with a
   first-order family (Heather has no type-valued functions: the family is
   a fixed F over Fin n, reindexed by an embedding e). *)

Fixpoint Fin (k : nat) : Type := match k with 0 => Empty_set | S k => (unit + Fin k)%type end.

Fixpoint DVec (k : nat) : (Fin k -> Type) -> Type :=
  match k with
  | 0 => fun _ => unit
  | S k => fun F => (F (inl tt) * DVec k (fun j => F (inr j)))%type
  end.

(* dnth, in the shape Heather's elim_Nat schema can state: the family F
   over Fin n is fixed; the motive at stage k quantifies over an embedding
   e : Fin k -> Fin n, not over a family. *)
Section Dnth.
  Context (n : nat) (F : Fin n -> Type).
  Fixpoint go (k : nat) : forall (e : Fin k -> Fin n),
      DVec k (fun j => F (e j)) -> forall i : Fin k, F (e i) :=
    match k with
    | 0 => fun e cs i => match i with end
    | S k => fun e cs i =>
        match i as i0 return F (e i0) with
        | inl u => match u as u0 return F (e (inl u0)) with tt => fst cs end
        | inr j => go k (fun j => e (inr j)) (snd cs) j
        end
    end.
  Definition dnth (cs : DVec n F) (i : Fin n) : F i := go n (fun i => i) cs i.
End Dnth.

(* At a literal arity and a neutral tuple, dnth reduces to the projections. *)
Goal forall (F : Fin 3 -> Type) (cs : DVec 3 F),
  dnth 3 F cs (inl tt) = fst cs /\
  dnth 3 F cs (inr (inl tt)) = fst (snd cs) /\
  dnth 3 F cs (inr (inr (inl tt))) = fst (snd (snd cs)).
Proof. intros; repeat split; reflexivity. Qed.

(* IW with an output-index function.  Children are a function here only
   because Coq's positivity checker rejects DVec-nested occurrences; the
   Heather former stores them in DVec (value equality by Sigma/Unit eta, as
   Wf).  Nothing below depends on the children's representation. *)
Section IW.
  Context (I S : Type) (ar : S -> nat) (o : S -> I) (c : forall a, Fin (ar a) -> I).
  Inductive IW : I -> Type :=
    sup (a : S) (cs : forall i : Fin (ar a), IW (c a i)) : IW (o a).
End IW.
Arguments sup {I S ar o c} a cs.

(* 1. A computed result index (fording's motivating class):
      Lit : Tm 1,  App(n, m, f : Tm n, a : Tm m) : Tm (S (n + m)).
      Child indices are stored in the shape, so nothing is recomputed. *)
Definition TmS := (unit + nat * nat)%type.
Definition tm_ar (a : TmS) : nat := match a with inl _ => 0 | inr _ => 2 end.
Definition tm_o (a : TmS) : nat := match a with inl _ => 1 | inr (n, m) => S (n + m) end.
Definition tm_c (a : TmS) : Fin (tm_ar a) -> nat :=
  match a as a0 return Fin (tm_ar a0) -> nat with
  | inl _ => fun i => match i with end
  | inr (n, m) => fun i => match i with inl _ => n | inr _ => m end
  end.
Definition Tm := IW nat TmS tm_ar tm_o tm_c.
Definition lit : Tm 1 := @sup _ _ tm_ar tm_o tm_c (inl tt) (fun i : Empty_set => match i with end).
Definition app (n m : nat) (f : Tm n) (a : Tm m) : Tm (S (n + m)) :=
  @sup _ _ tm_ar tm_o tm_c (inr (n, m)) (fun i => match i as i0 return Tm (tm_c (inr (n, m)) i0) with
                             | inl _ => f
                             | inr (inl _) => a
                             | inr (inr e) => match e with end end).

(* The eliminator's beta fires on every constructor, open fields included:
   no stored proof, no form B. *)
Fixpoint size {k} (t : Tm k) : nat :=
  match t with
  | sup (inl _) _ => 1
  | sup (inr _) cs => S (size (cs (inl tt)) + size (cs (inr (inl tt))))
  end.
Goal forall n m (f : Tm n) (a : Tm m), size (app n m f a) = S (size f + size a).
Proof. reflexivity. Qed.

(* 2. The fording restrictions do not arise.
   F1 (child at a non-variable index): Node(l : T 0, r : T n) : T (S n).
   F2 (two children at one index):     Node(n, l : T n, r : T n) : T (n + n).
   F3 (payload mentions a child index): Cons(n, x : Fin n, xs : V n) : V (S n). *)
Definition F2S := (unit + nat)%type.
Definition f2_ar (a : F2S) := match a with inl _ => 0 | inr _ => 2 end.
Definition f2_o (a : F2S) := match a with inl _ => 0 | inr n => n + n end.
Definition f2_c (a : F2S) : Fin (f2_ar a) -> nat :=
  match a as a0 return Fin (f2_ar a0) -> nat with
  | inl _ => fun i => match i with end
  | inr n => fun _ => n end.
Definition T2 := IW nat F2S f2_ar f2_o f2_c.
Definition node2 (n : nat) (l r : T2 n) : T2 (n + n) :=
  @sup _ _ f2_ar f2_o f2_c (inr n) (fun i => match i as i0 return T2 (f2_c (inr n) i0) with
                        | inl _ => l | inr (inl _) => r | inr (inr e) => match e with end end).

Definition VS (A : Type) := (unit + {n : nat & (Fin n * A)%type})%type.
Definition v_ar {A} (a : VS A) := match a with inl _ => 0 | inr _ => 1 end.
Definition v_o {A} (a : VS A) := match a with inl _ => 0 | inr (existT _ n _) => S n end.
Definition v_c {A} (a : VS A) : Fin (v_ar a) -> nat :=
  match a as a0 return Fin (v_ar a0) -> nat with
  | inl _ => fun i => match i with end
  | inr (existT _ n _) => fun _ => n end.
Definition V (A : Type) := IW nat (VS A) v_ar v_o v_c.
Definition vnil {A} : V A 0 := @sup _ (VS A) v_ar v_o v_c (inl tt) (fun i : Empty_set => match i with end).
Definition vcons {A} (n : nat) (x : Fin n) (y : A) (xs : V A n) : V A (S n) :=
  @sup _ (VS A) v_ar v_o v_c (inr (existT _ n (x, y)))
      (fun i => match i as i0 return V A (v_c (inr (existT _ n (x, y))) i0) with
                | inl _ => xs | inr e => match e with end end).

(* 3. Inversion at a constructor-headed index needs no equation: the motive
   cases on the index (fording's form A, and route 1's device). *)
Definition vhead {A n} (v : V A (S n)) : A :=
  match v in IW _ _ _ _ _ j return match j with 0 => unit | S _ => A end with
  | sup (inl _) _ => tt
  | sup (inr (existT _ _ (_, y))) _ => y
  end.
Goal forall A n x y (xs : V A n), vhead (vcons n x y xs) = y.
Proof. reflexivity. Qed.

Print Assumptions vhead.
