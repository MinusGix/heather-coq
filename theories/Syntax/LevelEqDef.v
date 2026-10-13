(** * Level equivalence of syntax (M3_DESIGN.md E11)

    [x ≡ₗ x']: the same syntax up to level annotations that are equal
    under every valuation. Boxed code is compared by this relation (the
    Static Code Lemma, 05:1055). Its laws (an equivalence that every
    syntactic operation respects) are in [LevelEq].

    The definitions are a file of their own so that the files that only
    mention the relation ([NormalForms], and through it [Reduction] and
    the typing rules) do not wait for its laws, which take over a minute
    to check: it keeps [LevelEq] off the build's critical path. *)
From DeLaM.Syntax Require Export Term.

Definition leqv (l l' : lvl) : Prop := forall v, leval v l = leval v l'.

Fixpoint ty_leq (T T' : ty) {struct T} : Prop :=
  match T, T' with
  | tyErr, tyErr | tyNat, tyNat => True
  | tyPi l1 l2 A B, tyPi l1' l2' A' B' => leqv l1 l1' /\ leqv l2 l2' /\ ty_leq A A' /\ ty_leq B B'
  | tyU l, tyU l' => leqv l l'
  | tyEl l t, tyEl l' t' => leqv l l' /\ tm_leq t t'
  | tyGvar U d, tyGvar U' d' => U = U' /\ lsub_leq d d'
  | tyCTyp Δ l, tyCTyp Δ' l' => ctx_leq Δ Δ' /\ leqv l l'
  | tyCTrm Δ A l, tyCTrm Δ' A' l' => ctx_leq Δ Δ' /\ ty_leq A A' /\ leqv l l'
  | tyUPi n l A, tyUPi n' l' A' => n = n' /\ leqv l l' /\ ty_leq A A'
  | tyCPi l A, tyCPi l' A' => leqv l l' /\ ty_leq A A'
  | tyTPi Δ l1 l2 A, tyTPi Δ' l1' l2' A' => ctx_leq Δ Δ' /\ leqv l1 l1' /\ leqv l2 l2' /\ ty_leq A A'
  | tySig l1 l2 A B, tySig l1' l2' A' B' => leqv l1 l1' /\ leqv l2 l2' /\ ty_leq A A' /\ ty_leq B B'
  | tySum l1 l2 A B, tySum l1' l2' A' B' => leqv l1 l1' /\ leqv l2 l2' /\ ty_leq A A' /\ ty_leq B B'
  | tyW l1 l2 A B, tyW l1' l2' A' B' => leqv l1 l1' /\ leqv l2 l2' /\ ty_leq A A' /\ ty_leq B B'
  | tyVec l A n, tyVec l' A' n' => leqv l l' /\ ty_leq A A' /\ tm_leq n n'
  | tyFin n, tyFin n' => tm_leq n n'
  | tyWf l A N, tyWf l' A' N' => leqv l l' /\ ty_leq A A' /\ tm_leq N N'
  | tySq l A, tySq l' A' => leqv l l' /\ ty_leq A A'
  | tyDVec l n F, tyDVec l' n' F' => leqv l l' /\ tm_leq n n' /\ ty_leq F F'
  | tyUnit l, tyUnit l' | tySEmpty l, tySEmpty l' | tyEmpty l, tyEmpty l' => leqv l l'
  | tySEq l A a b, tySEq l' A' a' b' => leqv l l' /\ ty_leq A A' /\ tm_leq a a' /\ tm_leq b b'
  | tyId l A a b, tyId l' A' a' b' => leqv l l' /\ ty_leq A A' /\ tm_leq a a' /\ tm_leq b b'
  | _, _ => False
  end
with tm_leq (t t' : tm) {struct t} : Prop :=
  match t, t' with
  | var n, var n' => n = n'
  | tmErr, tmErr | tmNat, tmNat | zero, zero => True
  | tmPi l1 l2 s t, tmPi l1' l2' s' t' => leqv l1 l1' /\ leqv l2 l2' /\ tm_leq s s' /\ tm_leq t t'
  | tmU l, tmU l' => leqv l l'
  | succ t, succ t' => tm_leq t t'
  | natrec l M s z t, natrec l' M' s' z' t' =>
      leqv l l' /\ ty_leq M M' /\ tm_leq s s' /\ tm_leq z z' /\ tm_leq t t'
  | lam l1 l2 A t, lam l1' l2' A' t' => leqv l1 l1' /\ leqv l2 l2' /\ ty_leq A A' /\ tm_leq t t'
  | app t l1 l2 A B s, app t' l1' l2' A' B' s' =>
      tm_leq t t' /\ leqv l1 l1' /\ leqv l2 l2' /\ ty_leq A A' /\ ty_leq B B' /\ tm_leq s s'
  | gvar u d, gvar u' d' => u = u' /\ lsub_leq d d'
  | gdef u b d, gdef u' b' d' => u = u' /\ tm_leq b b' /\ lsub_leq d d'
  | boxT T, boxT T' => ty_leq T T'
  | boxt t, boxt t' => tm_leq t t'
  | letboxT l1 l2 Δ M t1 t, letboxT l1' l2' Δ' M' t1' t' =>
      leqv l1 l1' /\ leqv l2 l2' /\ ctx_leq Δ Δ' /\ ty_leq M M' /\ tm_leq t1 t1' /\ tm_leq t t'
  | letboxt l1 l2 Δ A M t1 t, letboxt l1' l2' Δ' A' M' t1' t' =>
      leqv l1 l1' /\ leqv l2 l2' /\ ctx_leq Δ Δ' /\ ty_leq A A' /\ ty_leq M M' /\
      tm_leq t1 t1' /\ tm_leq t t'
  | tmTy T, tmTy T' => ty_leq T T'
  | tmTup s t, tmTup s' t' => tm_leq s s' /\ tm_leq t t'
  | bindU b, bindU b' | bindG b, bindG b' | bindL b, bindL b' => tm_leq b b'
  | elimT l1 l2 rb l Δ t, elimT l1' l2' rb' l' Δ' t' =>
      leqv l1 l1' /\ leqv l2 l2' /\ tm_leq rb rb' /\ leqv l l' /\ ctx_leq Δ Δ' /\ tm_leq t t'
  | elimt l1 l2 rb l Δ A t, elimt l1' l2' rb' l' Δ' A' t' =>
      leqv l1 l1' /\ leqv l2 l2' /\ tm_leq rb rb' /\ leqv l l' /\ ctx_leq Δ Δ' /\ ty_leq A A' /\
      tm_leq t t'
  | ulam n l T t, ulam n' l' T' t' => n = n' /\ leqv l l' /\ ty_leq T T' /\ tm_leq t t'
  | uapp t ls, uapp t' ls' => tm_leq t t' /\ Forall2 leqv ls ls'
  | clam l T t, clam l' T' t' => leqv l l' /\ ty_leq T T' /\ tm_leq t t'
  | capp t Δ, capp t' Δ' => tm_leq t t' /\ ctx_leq Δ Δ'
  | tlam Δ l1 l2 T t, tlam Δ' l1' l2' T' t' => ctx_leq Δ Δ' /\ leqv l1 l1' /\ leqv l2 l2' /\ ty_leq T T' /\ tm_leq t t'
  | tapp t A, tapp t' A' => tm_leq t t' /\ ty_leq A A'
  | tmSig l1 l2 s t, tmSig l1' l2' s' t' | tmSum l1 l2 s t, tmSum l1' l2' s' t'
  | tmW l1 l2 s t, tmW l1' l2' s' t' =>
      leqv l1 l1' /\ leqv l2 l2' /\ tm_leq s s' /\ tm_leq t t'
  | tmVec l s n, tmVec l' s' n' => leqv l l' /\ tm_leq s s' /\ tm_leq n n'
  | tmFin n, tmFin n' => tm_leq n n'
  | tmWf l s n, tmWf l' s' n' => leqv l l' /\ tm_leq s s' /\ tm_leq n n'
  | tmPair l1 l2 A B a b, tmPair l1' l2' A' B' a' b' =>
      leqv l1 l1' /\ leqv l2 l2' /\ ty_leq A A' /\ ty_leq B B' /\ tm_leq a a' /\ tm_leq b b'
  | tmFst l1 l2 A B p, tmFst l1' l2' A' B' p' =>
      leqv l1 l1' /\ leqv l2 l2' /\ ty_leq A A' /\ ty_leq B B' /\ tm_leq p p'
  | tmSnd l1 l2 A B p, tmSnd l1' l2' A' B' p' =>
      leqv l1 l1' /\ leqv l2 l2' /\ ty_leq A A' /\ ty_leq B B' /\ tm_leq p p'
  | tmUnit l, tmUnit l' | tmTriv l, tmTriv l' | tmSEmpty l, tmSEmpty l' | tmEmpty l, tmEmpty l' => leqv l l'
  | srefl l A a, srefl l' A' a' => leqv l l' /\ ty_leq A A' /\ tm_leq a a'
  | tmRefl l A a, tmRefl l' A' a' => leqv l l' /\ ty_leq A A' /\ tm_leq a a'
  | tmId l s t u, tmId l' s' t' u' => leqv l l' /\ tm_leq s s' /\ tm_leq t t' /\ tm_leq u u'
  | tmSEq l s t u, tmSEq l' s' t' u' => leqv l l' /\ tm_leq s s' /\ tm_leq t t' /\ tm_leq u u'
  | tmJ l1 l2 A a M c u e, tmJ l1' l2' A' a' M' c' u' e' =>
      leqv l1 l1' /\ leqv l2 l2' /\ ty_leq A A' /\ tm_leq a a' /\ ty_leq M M' /\
      tm_leq c c' /\ tm_leq u u' /\ tm_leq e e'
  | elimSEmpty l1 l2 M e, elimSEmpty l1' l2' M' e' =>
      leqv l1 l1' /\ leqv l2 l2' /\ ty_leq M M' /\ tm_leq e e'
  | elimEmpty l1 l2 M e, elimEmpty l1' l2' M' e' =>
      leqv l1 l1' /\ leqv l2 l2' /\ ty_leq M M' /\ tm_leq e e'
  | tmInl l1 l2 A B a, tmInl l1' l2' A' B' a' | tmInr l1 l2 A B a, tmInr l1' l2' A' B' a' =>
      leqv l1 l1' /\ leqv l2 l2' /\ ty_leq A A' /\ ty_leq B B' /\ tm_leq a a'
  | tmCase l1 l2 l3 A B M c1 c2 t, tmCase l1' l2' l3' A' B' M' c1' c2' t' =>
      leqv l1 l1' /\ leqv l2 l2' /\ leqv l3 l3' /\ ty_leq A A' /\ ty_leq B B' /\ ty_leq M M' /\
      tm_leq c1 c1' /\ tm_leq c2 c2' /\ tm_leq t t'
  | tmSup l1 l2 A B a f, tmSup l1' l2' A' B' a' f' =>
      leqv l1 l1' /\ leqv l2 l2' /\ ty_leq A A' /\ ty_leq B B' /\ tm_leq a a' /\ tm_leq f f'
  | tmElimW l1 l2 l3 A B M c t, tmElimW l1' l2' l3' A' B' M' c' t' =>
      leqv l1 l1' /\ leqv l2 l2' /\ leqv l3 l3' /\ ty_leq A A' /\ ty_leq B B' /\ ty_leq M M' /\
      tm_leq c c' /\ tm_leq t t'
  | tmSupf l A N a cs, tmSupf l' A' N' a' cs' =>
      leqv l l' /\ ty_leq A A' /\ tm_leq N N' /\ tm_leq a a' /\ tm_leq cs cs'
  | tmElimWf l1 l2 A N M c t, tmElimWf l1' l2' A' N' M' c' t' =>
      leqv l1 l1' /\ leqv l2 l2' /\ ty_leq A A' /\ tm_leq N N' /\ ty_leq M M' /\
      tm_leq c c' /\ tm_leq t t'
  | tmSq l A a, tmSq l' A' a' => leqv l l' /\ ty_leq A A' /\ tm_leq a a'
  | tmElimSq l1 l2 A M c t, tmElimSq l1' l2' A' M' c' t' =>
      leqv l1 l1' /\ leqv l2 l2' /\ ty_leq A A' /\ ty_leq M M' /\ tm_leq c c' /\ tm_leq t t'
  | tmSqCode l s, tmSqCode l' s' => leqv l l' /\ tm_leq s s'
  | _, _ => False
  end
with ctx_leq (Γ Γ' : ctx) {struct Γ} : Prop :=
  match Γ, Γ' with
  | cnil, cnil => True
  | cvar g, cvar g' => g = g'
  | cext Γ A l, cext Γ' A' l' => ctx_leq Γ Γ' /\ ty_leq A A' /\ leqv l l'
  | _, _ => False
  end
with lsub_leq (d d' : lsub) {struct d} : Prop :=
  match d, d' with
  | lshift k, lshift k' => k = k'
  | lcons d t, lcons d' t' => lsub_leq d d' /\ tm_leq t t'
  | _, _ => False
  end.

Definition gobj_leq (o o' : gobj) : Prop :=
  match o, o' with
  | GId j, GId j' => j = j'
  | GCtx Γ, GCtx Γ' => ctx_leq Γ Γ'
  | GTy T, GTy T' => ty_leq T T'
  | GTm t, GTm t' => tm_leq t t'
  | _, _ => False
  end.

