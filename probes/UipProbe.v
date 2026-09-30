(* Heather's sEq modelled as a strict proposition, with transp computing
   only on srefl (beta), no strip: Coq's SProp equality eliminated into Type
   by hand-rolled beta via a Box. We avoid Definitional UIP; transp is an
   axiom with beta as a propositional-free rewrite rule is not available,
   so instead: define sEq as an SProp inductive and give transp by
   eliminating a *relevant* copy. *)
Set Universe Polymorphism.

(* Abstract interface: exactly what Heather provides. *)
Module Type HeatherSEq.
  Parameter sEq : forall {A : Type}, A -> A -> SProp.
  Parameter srefl : forall {A : Type} (a : A), sEq a a.
  Parameter transp : forall {A : Type} (P : A -> Type) {a b : A}, sEq a b -> P a -> P b.
  (* beta, as a propositional equation (weaker than Heather's definitional one) *)
  Parameter transp_beta : forall {A : Type} (P : A -> Type) (a : A) (t : P a),
    transp P (srefl a) t = t.
End HeatherSEq.

Module UIP (H : HeatherSEq).
  Import H.
  Definition toS {A} {u v : A} (p : u = v) : sEq u v :=
    match p in _ = v return sEq u v with eq_refl => srefl u end.
  Definition fromS {A} {u v : A} (e : sEq u v) : u = v :=
    transp (fun z => u = z) e eq_refl.
  Lemma round {A} {u v : A} (p : u = v) : fromS (toS p) = p.
  Proof. destruct p. apply transp_beta. Qed.
  (* definitional irrelevance of SProp does the rest *)
  Theorem uip {A} {u v : A} (p q : u = v) : p = q.
  Proof.
    rewrite <- (round p), <- (round q).
    reflexivity.  (* toS p and toS q are convertible: both inhabit an SProp *)
  Qed.
  Print Assumptions uip.
End UIP.
