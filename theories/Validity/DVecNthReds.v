(** * [dnth] on a neutral tuple, untyped (M17_DESIGN.md, M17a)

    Heather's design (its §3) says [dnth(3; F; cs; inr (inl ⟨⟩))]
    reduces to [fst (snd cs)] for a neutral [cs]: the projection never
    looks at the tuple. Checked here on that instance, for any [cs] in
    normal form, by stepping the reduction and computing each state's
    normal form ([tnorm]). It needs only the syntax, so it builds beside
    the metatheory; [DNthReds] reuses its [rstep] and [tpush] for
    [dnth]'s states in general. *)
From DeLaM.Syntax Require Import TemplateEq.
From DeLaM.Validity Require Import WfNthReds.

(** One reduction step, at the redex the congruences reach. *)
Ltac rstep := eapply Relation_Operators.rt1n_trans;
  [repeat first [apply red_natrec_succ | apply red_beta | apply red_case_inl | apply red_case_inr
                | apply red_app | apply red_fst | apply red_snd | apply red_case] |].

(** Substitutions pushed through terms only: the annotations' types stay
    as they are, since reduction never looks at them. *)
Ltac tpush := repeat (match goal with
  | |- context [@subst tm _ ?t _] => let h := head_of t in push_subst_at h ltac:(fun L => rewrite !L)
  end); pw.

(** The next state to its normal form, by computation ([TemplateEq]):
    [F] and [cs] are its atoms. *)
Ltac tnorm := graw; lazymatch goal with |- Relation_Operators.clos_refl_trans_1n _ _ ?S _ => gnorm S end.

Section DNthReds.
Context (l : lvl) (F : ty) (NF : nfty F) (cs : tm) (Ncs : nftm cs).

Lemma dnth_reds_example : exists A B A' B',
  reds (tmDNth l (succ (succ (succ zero))) F cs
          (tmInr lzero lzero (tyUnit lzero) (tyFin (succ (succ zero)))
             (tmInl lzero lzero (tyUnit lzero) (tyFin (succ zero)) (tmTriv lzero))))
       (tmFst l l A B (tmSnd l l A' B' cs)).
Proof using NF Ncs.
  do 4 eexists. unfold tmDNth.
  do 10 (rstep; tnorm).
  apply reds_eq. reflexivity.
Qed.
End DNthReds.
