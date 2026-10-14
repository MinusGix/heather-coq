(** * [dnth] on a neutral tuple, untyped (M17_DESIGN.md, M17a)

    Heather's design (its §3) says [dnth(3; F; cs; inr (inl ⟨⟩))]
    reduces to [fst (snd cs)] for a neutral [cs]: the projection never
    looks at the tuple. Checked here on that instance, for any [cs] in
    normal form, by stepping the reduction. It needs only the syntax
    ([WfNthReds]' [teq]), so it builds beside the metatheory; [DNthReds]
    reuses its [rstep] and [tpush] for [dnth]'s states in general. *)
From DeLaM.Validity Require Import WfNthReds.

(** One reduction step, at the redex the congruences reach. *)
Ltac rstep := eapply Relation_Operators.rt1n_trans;
  [repeat first [apply red_natrec_succ | apply red_beta | apply red_case_inl | apply red_case_inr
                | apply red_app | apply red_fst | apply red_snd | apply red_case] |].

(** Substitutions pushed through terms only: the annotations' types stay
    as they are, since reduction never looks at them. *)
Ltac tpush := repeat (match goal with
  | |- context [@subst tm _ ?t _] => let h := head_of t in push_subst_at h ltac:(fun L => rewrite L)
  end); pw.

Section DNthReds.
Context (l : lvl) (F : ty) (NF : nfty F) (cs : tm) (Ncs : nftm cs).

Lemma dnth_reds_example : exists A B A' B',
  reds (tmDNth l (succ (succ (succ zero))) F cs
          (tmInr lzero lzero (tyUnit lzero) (tyFin (succ (succ zero)))
             (tmInl lzero lzero (tyUnit lzero) (tyFin (succ zero)) (tmTriv lzero))))
       (tmFst l l A B (tmSnd l l A' B' cs)).
Proof.
  do 4 eexists. unfold tmDNth.
  rstep. unfold dnthStep at 1. tpush.
  rstep. tpush.
  rstep. tpush.
  rstep. tpush.
  rstep. tpush.
  rstep. unfold dnthStep at 1. tpush.
  rstep. tpush.
  rstep. tpush.
  rstep. tpush.
  rstep. tpush.
  apply reds_eq. lazymatch goal with |- tmFst _ _ _ _ (tmSnd _ _ _ _ ?z) = _ =>
    assert (Ez : z = cs) by (repeat change (ren_tm ?x ?r) with x⟨r⟩; teq); rewrite Ez end.
  reflexivity.
Qed.
End DNthReds.
