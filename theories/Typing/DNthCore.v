(** * Typing of [dnth] from its family's instances

    [dnth^l(n; i. F; cs; i)]'s derivation ([Typing/DNth.v], M17a) as a
    lemma that needs no metatheory: where [DNth] weakens [n] and
    substitutes into [F] (weakening and substitution of judgements, which
    come after [RecWf]), this file takes the instances it uses as
    premises ([NW], [FW], [FV], [FE], [FE0]): [n] and [F] in [Γ] extended by [m]
    locals, at any [m] up to the derivation's depth, [F] at any index
    there. [DNth] discharges them by weakening and substitution;
    [RecWf]'s scope automation by typing the concrete [n] and [F] under
    [m] abstract locals, which is what lets [elim_IWf]'s scope type its
    [dnth] without unfolding it (110 s of the critical path before). *)
From DeLaM.Syntax Require Import SubstCommute TemplateEq.
From DeLaM.Typing Require Export Declarative.

(** ** Iterated weakenings *)

Lemma shift2_tm (t : tm) : t⟨↑⟩⟨↑⟩ = t⟨rshift 2⟩.
Proof using . rewrite ren_ren_comp. apply ren_ext_tm; intros m; rlk_simpl; cbn; lia. Qed.
Lemma shiftS_tm (t : tm) k : t⟨rshift k⟩⟨↑⟩ = t⟨rshift (S k)⟩.
Proof using . rewrite ren_ren_comp. apply ren_ext_tm; intros m; rlk_simpl; cbn; lia. Qed.
Lemma lift2_ty (T : ty) : T⟨rlift ↑⟩⟨rlift ↑⟩ = T⟨rlift (rshift 2)⟩.
Proof using . rewrite ren_ren_comp_ty. apply ren_ext_ty; intros [|m]; rlk_simpl; cbn; lia. Qed.
Lemma liftS_ty (T : ty) k : T⟨rlift (rshift k)⟩⟨rlift ↑⟩ = T⟨rlift (rshift (S k))⟩.
Proof using . rewrite ren_ren_comp_ty. apply ren_ext_ty; intros [|m]; rlk_simpl; cbn; lia. Qed.

Lemma shift_add_tm (t : tm) a b : t⟨rshift a⟩⟨rshift b⟩ = t⟨rshift (a + b)⟩.
Proof using . rewrite ren_ren_comp. apply ren_ext_tm; intros m; rlk_simpl; cbn; lia. Qed.
Lemma lift_add_ty (T : ty) a b : T⟨rlift (rshift a)⟩⟨rlift (rshift b)⟩ = T⟨rlift (rshift (a + b))⟩.
Proof using . rewrite ren_ren_comp_ty. apply ren_ext_ty; intros [|m]; rlk_simpl; cbn; lia. Qed.

Lemma shift_lift_tm (t : tm) k a : t⟨rshift (S k)⟩⟨rlift (rshift a)⟩ = t⟨rshift (S k + a)⟩.
Proof using . rewrite ren_ren_comp. apply ren_ext_tm; intros m; rlk_simpl; cbn; rewrite ?Nat.add_succ_r; cbn; rlk_simpl; cbn; lia. Qed.

(** Iterated weakenings to one [rshift k] (and [rlift (rshift k)]). *)
Ltac nshift_go := unfold rshift1; repeat first [ rewrite shift_add_tm | rewrite shift_lift_tm | rewrite lift_add_ty
  | match goal with |- context [rshift (?a + ?b)] =>
      let c := eval compute in (a + b) in change (a + b) with c end ].
(** In a judgement, the context is left alone. *)
Ltac nshift := lazymatch goal with
  | |- [ _ ; ?D ⊢[ _ ] _ @ _ ] => let DD := fresh "DD" in set (DD := D); nshift_go; subst DD
  | |- [ _ ; ?D ⊢[ _ ] _ : _ @ _ ] => let DD := fresh "DD" in set (DD := D); nshift_go; subst DD
  | |- _ => nshift_go
  end.


Lemma dnc_subst_comp_ty (T : ty) d1 d2 : T[d1][d2] = T[lcomp d1 d2].
Proof using . apply subst_subst_ty; intros; apply llk_lcomp. Qed.
Lemma dnc_subst_comp (t : tm) d1 d2 : t[d1][d2] = t[lcomp d1 d2].
Proof using . apply subst_subst; intros; apply llk_lcomp. Qed.

(** Pointwise comparison of substitutions ([PresupAux.pw]). *)
Ltac dpw := repeat first
  [ progress (rewrite ?llk_lcomp, ?llk_r2l, ?llk_llift, ?llk_lren)
  | progress rlk_simpl
  | progress cbn [llk lsingle lsingle2 lsingle3 ren_tm subst_tm rlk Nat.add]
  | progress push_ren | progress push_subst ];
  try reflexivity; try (f_equal; lia).

(** ** Syntactic equations of the motive's instances *)

(** [PresupAux]'s [teq_core] (local to its section): two substitution
    instances agree pointwise. *)
Ltac tcong := repeat match goal with
  | |- tyPi _ _ _ _ = tyPi _ _ _ _ => f_equal
  | |- tySig _ _ _ _ = tySig _ _ _ _ => f_equal
  | |- tyDVec _ _ _ = tyDVec _ _ _ => f_equal
  | |- tyFin _ = tyFin _ => f_equal
  end.
Ltac fin_sub := repeat match goal with
  | |- context [subst_ty (tyFin ?a) ?d] => change (subst_ty (tyFin a) d) with (tyFin (a[d]))
  | |- context [(tyFin ?a)[?d]] => change ((tyFin a)[d]) with (tyFin (a[d]))
  end;
  f_equal; repeat rewrite dnc_subst_comp; apply subst_ext; intros ?m; dpw;
  rewrite Nat.add_comm; cbn [Nat.add llk]; push_ren; rlk_simpl; cbn; f_equal; lia.
Ltac teq_core := repeat first [ rewrite ren_as_r2l_ty | rewrite ren_as_r2l ];
  repeat first [ rewrite dnc_subst_comp_ty | rewrite dnc_subst_comp ];
  first [ apply subst_ext_ty | apply subst_ext
        | apply subst_id_ty; [assumption|] | apply subst_id; [assumption|]
        | symmetry; apply subst_id_ty; [assumption|] | symmetry; apply subst_id; [assumption|] ];
  intros [|[|[|[|[|[|[|[|?n]]]]]]]]; unfold lsucc; dpw;
  try solve [apply ren_as_r2l | symmetry; apply ren_as_r2l].
(** Raw [ren_ty] (and the like) left by [cbn], back to the classes'
    notation, which [push_ren] and [push_subst] read. *)
Ltac refold := try change ren_ty with (@ren ty Ren_ty); try change ren_tm with (@ren tm Ren_tm);
  try change subst_ty with (@subst ty Subst_ty); try change subst_tm with (@subst tm Subst_tm).
(** A pointwise term equation: congruence down to [n]'s instances, which
    are compared as substitutions. *)
Ltac n_eq := repeat first [ rewrite ren_as_r2l | rewrite ren_as_r2l_ty ];
  repeat first [ rewrite dnc_subst_comp | rewrite dnc_subst_comp_ty ];
  first [ apply subst_ext | apply subst_ext_ty ]; intros ?m; dpw;
  rewrite Nat.add_comm; cbn [Nat.add llk]; push_ren; rlk_simpl; cbn; f_equal; lia.
Ltac tq := refold; push_ren; push_subst; dpw;
  repeat match goal with
  | |- ?x = ?x => reflexivity
  | |- app _ _ _ _ _ _ = app _ _ _ _ _ _ => f_equal
  | |- lam _ _ _ _ = lam _ _ _ _ => f_equal
  | |- tmInr _ _ _ _ _ = tmInr _ _ _ _ _ => f_equal
  | |- tmInl _ _ _ _ _ = tmInl _ _ _ _ _ => f_equal
  | |- succ _ = succ _ => f_equal
  | |- tyFin _ = tyFin _ => f_equal
  | |- var _ = var _ => f_equal; lia
  | |- _ = _ => progress (refold; push_ren; push_subst; dpw)
  end; n_eq.
(** The motive's equations: by computation on a template ([geq],
    [TemplateEq]), else congruence, then pointwise. *)
Ltac meq_pw := push_subst; tcong; try solve [dpw]; try teq_core; try solve [f_equal; try reflexivity; fin_sub]; try solve [tq].
Ltac meq := first [ geq | meq_pw ].
(** A local substitution's term that the equation discards (it lands
    on no variable of the type), generalized so that [meq] does not
    push the renamings through it. *)
Ltac gen_big := repeat match goal with |- context [llift (lsingle ?b)] =>
  lazymatch b with var _ => fail | _ => tryif is_var b then fail else
    let x := fresh "b" in generalize b; intros x end end.
(** [gen_big] only for the pointwise tactics: [geq] computes through [b]. *)
Ltac meq_big := first [ geq | gen_big; meq_pw ].


(** [Δ] is [Γ] extended by [m] locals. *)
Fixpoint ctx_extn (m : nat) (Δ Γ : ctx) : Prop :=
  match m with
  | 0 => Δ = Γ
  | S m => match Δ with cext Δ' _ _ => ctx_extn m Δ' Γ | _ => False end
  end.

Lemma ctx_extn_trans j m Δ' Δ Γ : ctx_extn j Δ' Δ -> ctx_extn m Δ Γ -> ctx_extn (j + m) Δ' Γ.
Proof using .
  revert Δ'; induction j as [|j IH]; intros Δ' H1 H2; cbn in *; [now subst|].
  destruct Δ'; try contradiction. exact (IH _ H1 H2).
Qed.

Ltac ext_n := first [ exact eq_refl | cbn; reflexivity ].

Lemma dnc_notV i : compt i -> i <> lV.
Proof using . now intros [-> | ->]. Qed.

Lemma dnc_retype G i Δ x T T' l : [ G ; Δ ⊢[ i ] x : T' @ l ] -> T' = T -> [ G ; Δ ⊢[ i ] x : T @ l ].
Proof using . now intros ? ->. Qed.

Lemma shiftS_single (t : tm) k s : nftm t -> t⟨rshift (S k)⟩[lsingle s] = t⟨rshift k⟩.
Proof using .
  intros _. rewrite (ren_subst _ _ _ (lshift k)).
  - symmetry; apply ren_as_subst. intros m; cbn; rlk_simpl; cbn; f_equal; lia.
  - intros m; rlk_simpl; cbn. rewrite Nat.add_succ_r; cbn. f_equal; lia.
Qed.

Lemma eqty_rw {G i Δ T1 T2 T1' T2' k} : T1 = T1' -> T2 = T2' ->
  [ G ; Δ ⊢[ i ] T1' ≅ T2' @ k ] -> [ G ; Δ ⊢[ i ] T1 ≅ T2 @ k ].
Proof using . now intros -> ->. Qed.

Lemma lq_00 {G} : lequiv (gL G) lzero (lmax lzero lzero).
Proof using . apply lequiv_sym, lmax_idem; exact I. Qed.
Lemma dnc_lq_0l {G l} : lwf (gL G) l -> lequiv (gL G) (lmax lzero l) l.
Proof using . intros Hl. eapply lequiv_trans; [apply lmax_comm; cbn; auto | apply lmax_zero; auto]. Qed.
Lemma dnc_lq_ll {G l} : lwf (gL G) l -> lequiv (gL G) (lmax l l) l.
Proof using . apply lmax_idem. Qed.

(** ** The motive's instances *)

Lemma dnth_E0 l (n : tm) (F : ty) : nftm n -> nfty F ->
  (dnthMot l n F)[lsingle zero] =
  tyPi lzero l (tyPi lzero lzero (tyFin zero) (tyFin n⟨↑⟩))
    (tyPi l l (tyDVec l zero F⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin zero) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))])
       (tyPi lzero l (tyFin zero) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 2) lzero lzero (tyFin zero) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))])).
Proof using .
  intros Nn NF. unfold dnthMot, dnthEmb, dnthFam, dnthRes. push_subst.
  meq.
Qed.

Lemma dnth_ES l (n : tm) (F : ty) : nftm n -> nfty F ->
  (dnthMot l n F)[lsucc] =
  tyPi lzero l (tyPi lzero lzero (tyFin (succ (var 1))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩))
    (tyPi l l (tyDVec l (succ (var 2)) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin (succ (var 3))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))])
       (tyPi lzero l (tyFin (succ (var 3))) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 2) lzero lzero (tyFin (succ (var 4))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))])).
Proof using .
  intros Nn NF. unfold dnthMot, dnthEmb, dnthFam, dnthRes. push_subst. meq.
Qed.

Section DNthCore.
Context {G : gctx} {i : layer} (Hc : compt i).

Let Hi : typeof i = i := compt_typeof_self _ Hc.
Let Hv : i <> lV := dnc_notV _ Hc.

Ltac wvar := eapply dnc_retype; [eapply wf_var; [rewrite Hi; eassumption | repeat constructor] |
  try (unfold dnthMot, dnthEmb, dnthFam, dnthRes, dnthFamS; push_ren; rlk_simpl; nshift; reflexivity)].
Ltac cext := apply wfc_ext; [assumption | | ].

(** [Fin (succ k)] against [Unit + Fin k], both ways. *)
Lemma fin_of_sum {Δ t K} : [ G ; Δ ⊢[ i ] K : tyNat @ lzero ] ->
  [ G ; Δ ⊢[ i ] t : tySum lzero lzero (tyUnit lzero) (tyFin K) @ lmax lzero lzero ] ->
  [ G ; Δ ⊢[ i ] t : tyFin (succ K) @ lzero ].
Proof using Hc.
  intros HK Ht. eapply wf_conv; [eapply wf_lconv; [exact Ht | exact lq_00] |].
  rewrite Hi. exact (eqty_fin_succ _ _ _ _ Hc HK).
Qed.

Lemma sum_of_fin {Δ t K} : [ G ; Δ ⊢[ i ] K : tyNat @ lzero ] -> [ G ; Δ ⊢[ i ] t : tyFin (succ K) @ lzero ] ->
  [ G ; Δ ⊢[ i ] t : tySum lzero lzero (tyUnit lzero) (tyFin K) @ lmax lzero lzero ].
Proof using Hc.
  intros HK Ht. eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]. eapply wf_conv; [exact Ht |].
  rewrite Hi. apply eqty_sym. exact (eqty_fin_succ _ _ _ _ Hc HK).
Qed.

Lemma fin_of_sum_eq {Δ t t' K} : [ G ; Δ ⊢[ i ] K : tyNat @ lzero ] ->
  [ G ; Δ ⊢[ i ] t ≅ t' : tySum lzero lzero (tyUnit lzero) (tyFin K) @ lmax lzero lzero ] ->
  [ G ; Δ ⊢[ i ] t ≅ t' : tyFin (succ K) @ lzero ].
Proof using Hc.
  intros HK Ht. eapply eqtm_conv; [eapply eqtm_lconv; [exact Ht | exact lq_00] |].
  rewrite Hi. exact (eqty_fin_succ _ _ _ _ Hc HK).
Qed.

Section Schema.
Context {Γ : ctx} {n : tm} {F : ty} {l : lvl} (Hl : lwf (gL G) l) (HΓ : [ G ; Γ ⊢[ i ] ])
  (Nn : nftm n) (NF : nfty F)
  (Hn : [ G ; Γ ⊢[ i ] n : tyNat @ lzero ]) (HF : [ G ; Γ ,, tyFin n @ lzero ⊢[ i ] F @ l ])
  (NW : forall m Δ, m <= 10 -> ctx_extn m Δ Γ -> [ G ; Δ ⊢[ i ] ] ->
     [ G ; Δ ⊢[ i ] n⟨rshift m⟩ : tyNat @ lzero ])
  (FW : forall m Δ e K x, 2 <= m <= 9 -> ctx_extn m Δ Γ -> [ G ; Δ ⊢[ i ] ] ->
     [ G ; Δ ⊢[ i ] app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x : tyFin n⟨rshift m⟩ @ lzero ] ->
     [ G ; Δ ⊢[ i ] F⟨rlift (rshift m)⟩[lsingle (app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x)] @ l ])
  (FV : forall m Δ, 2 <= m <= 2 -> ctx_extn m Δ Γ -> [ G ; Δ ⊢[ i ] ] ->
     [ G ; Δ ⊢[ i ] var 0 : tyFin n⟨rshift m⟩ @ lzero ] -> [ G ; Δ ⊢[ i ] F⟨rlift (rshift m)⟩[lsingle (var 0)] @ l ])
  (FE : forall m Δ e K x e' K' x', 6 <= m <= 8 -> ctx_extn m Δ Γ -> [ G ; Δ ⊢[ i ] ] ->
     [ G ; Δ ⊢[ i ] app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x : tyFin n⟨rshift m⟩ @ lzero ] ->
     [ G ; Δ ⊢[ i ] app e' lzero lzero (tyFin K') (tyFin n⟨rshift (S m)⟩) x' : tyFin n⟨rshift m⟩ @ lzero ] ->
     [ G ; Δ ⊢[ i ] app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x
                  ≅ app e' lzero lzero (tyFin K') (tyFin n⟨rshift (S m)⟩) x' : tyFin n⟨rshift m⟩ @ lzero ] ->
     [ G ; Δ ⊢[ i ] F⟨rlift (rshift m)⟩[lsingle (app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x)]
                  ≅ F⟨rlift (rshift m)⟩[lsingle (app e' lzero lzero (tyFin K') (tyFin n⟨rshift (S m)⟩) x')] @ l ])
  (FE0 : forall m Δ e K x, m <= 2 -> ctx_extn m Δ Γ -> [ G ; Δ ⊢[ i ] ] ->
     [ G ; Δ ⊢[ i ] app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x : tyFin n⟨rshift m⟩ @ lzero ] ->
     [ G ; Δ ⊢[ i ] var 0 : tyFin n⟨rshift m⟩ @ lzero ] ->
     [ G ; Δ ⊢[ i ] app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x ≅ var 0 : tyFin n⟨rshift m⟩ @ lzero ] ->
     [ G ; Δ ⊢[ i ] F⟨rlift (rshift m)⟩[lsingle (app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x)]
                  ≅ F⟨rlift (rshift m)⟩[lsingle (var 0)] @ l ]).

(** An embedding applied at an index of [Fin k], in a context [Δ] where
    the embedding is [ev], [k] is [K], and [Δ] extends [Γ] by [m] locals. *)
Lemma emb_app_wf {Δ m ev K t} : m <= 9 -> ctx_extn m Δ Γ -> [ G ; Δ ⊢[ i ] ] ->
  [ G ; Δ ⊢[ i ] K : tyNat @ lzero ] ->
  [ G ; Δ ⊢[ i ] ev : tyPi lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) @ lmax lzero lzero ] ->
  [ G ; Δ ⊢[ i ] t : tyFin K @ lzero ] ->
  [ G ; Δ ⊢[ i ] app ev lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) t : tyFin n⟨rshift m⟩ @ lzero ].
Proof using Hc NW Nn.
  intros Hm Hr HΔ HK He Ht.
  assert (HFK : [ G ; Δ ⊢[ i ] tyFin K @ lzero ]) by (apply wft_fin; [exact Hv | exact HK]).
  assert (HΔK : [ G ; Δ ,, tyFin K @ lzero ⊢[ i ] ]) by (cext; [exact HFK | exact I]).
  eapply dnc_retype; [apply wf_app; [exact Hv | exact I | exact I | exact HFK | | exact He | exact Ht] |].
  - apply wft_fin; [exact Hv|]. apply (NW (S m)); [lia | exact Hr | exact HΔK].
  - change ((tyFin n⟨rshift (S m)⟩)[lsingle t]) with (tyFin (n⟨rshift (S m)⟩[lsingle t])).
    now rewrite shiftS_single.
Qed.

Lemma emb_app_eq {Δ m ev K t t'} : m <= 9 -> ctx_extn m Δ Γ -> [ G ; Δ ⊢[ i ] ] ->
  [ G ; Δ ⊢[ i ] K : tyNat @ lzero ] ->
  [ G ; Δ ⊢[ i ] ev : tyPi lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) @ lmax lzero lzero ] ->
  [ G ; Δ ⊢[ i ] t ≅ t' : tyFin K @ lzero ] ->
  [ G ; Δ ⊢[ i ] app ev lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) t
      ≅ app ev lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) t' : tyFin n⟨rshift m⟩ @ lzero ].
Proof using Hc NW Nn.
  intros Hm Hr HΔ HK He Ht.
  assert (HFK : [ G ; Δ ⊢[ i ] tyFin K @ lzero ]) by (apply wft_fin; [exact Hv | exact HK]).
  assert (HΔK : [ G ; Δ ,, tyFin K @ lzero ⊢[ i ] ]) by (cext; [exact HFK | exact I]).
  assert (HC : [ G ; Δ ,, tyFin K @ lzero ⊢[ i ] tyFin n⟨rshift (S m)⟩ @ lzero ])
    by (apply wft_fin; [exact Hv|]; apply (NW (S m)); [lia | exact Hr | exact HΔK]).
  assert (E : (tyFin n⟨rshift (S m)⟩)[lsingle t] = tyFin n⟨rshift m⟩)
    by (change ((tyFin n⟨rshift (S m)⟩)[lsingle t]) with (tyFin (n⟨rshift (S m)⟩[lsingle t])); now rewrite shiftS_single).
  rewrite <- E. eapply eqtm_app; [exact Hv | exact (lequiv_refl (gL G) lzero I) | exact (lequiv_refl (gL G) lzero I) | exact HFK
    | exact (eqty_refl _ _ _ _ _ HFK) | exact (eqty_refl _ _ _ _ _ HC) | exact (eqtm_refl _ _ _ _ _ _ He) | exact Ht].
Qed.

(** β at an embedding's instance: the family at [(λy. b) s] against [b[s/y]]. *)
Lemma fam_beta {Δ m K b s e' K' x'} : 6 <= m <= 8 -> ctx_extn m Δ Γ -> [ G ; Δ ⊢[ i ] ] -> [ G ; Δ ⊢[ i ] K : tyNat @ lzero ] ->
  [ G ; Δ ,, tyFin K @ lzero ⊢[ i ] b : tyFin n⟨rshift (S m)⟩ @ lzero ] -> [ G ; Δ ⊢[ i ] s : tyFin K @ lzero ] ->
  b[lsingle s] = app e' lzero lzero (tyFin K') (tyFin n⟨rshift (S m)⟩) x' ->
  [ G ; Δ ⊢[ i ] app e' lzero lzero (tyFin K') (tyFin n⟨rshift (S m)⟩) x' : tyFin n⟨rshift m⟩ @ lzero ] ->
  [ G ; Δ ⊢[ i ] F⟨rlift (rshift m)⟩[lsingle (app (lam lzero lzero (tyFin K) b) lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) s)]
      ≅ F⟨rlift (rshift m)⟩[lsingle (app e' lzero lzero (tyFin K') (tyFin n⟨rshift (S m)⟩) x')] @ l ].
Proof using Hc NW Nn FE.
  intros Hm Hr HΔ HK Hb Hs Eb Hbs. rewrite <- Eb in Hbs.
  assert (HFK : [ G ; Δ ⊢[ i ] tyFin K @ lzero ]) by (apply wft_fin; [exact Hv | exact HK]).
  assert (HΔK : [ G ; Δ ,, tyFin K @ lzero ⊢[ i ] ]) by (cext; [exact HFK | exact I]).
  assert (HC : [ G ; Δ ,, tyFin K @ lzero ⊢[ i ] tyFin n⟨rshift (S m)⟩ @ lzero ])
    by (apply wft_fin; [exact Hv|]; apply (NW (S m)); [lia | exact Hr | exact HΔK]).
  assert (E : (tyFin n⟨rshift (S m)⟩)[lsingle s] = tyFin n⟨rshift m⟩)
    by (change ((tyFin n⟨rshift (S m)⟩)[lsingle s]) with (tyFin (n⟨rshift (S m)⟩[lsingle s])); now rewrite shiftS_single).
  assert (Hlam : [ G ; Δ ⊢[ i ] lam lzero lzero (tyFin K) b : tyPi lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) @ lmax lzero lzero ])
    by (apply wf_lam; [exact Hv | exact I | exact I | exact HFK | exact Hb]).
  assert (Hβ : [ G ; Δ ⊢[ i ] app (lam lzero lzero (tyFin K) b) lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) s ≅ b[lsingle s] : tyFin n⟨rshift m⟩ @ lzero ])
    by (rewrite <- E; exact (eqtm_beta _ _ _ lzero lzero _ _ _ _ Hc I I HFK HC Hb Hs)).
  rewrite Eb in Hβ.
  exact (FE m Δ _ _ _ _ _ _ ltac:(lia) Hr HΔ (emb_app_wf (m := m) ltac:(lia) Hr HΔ HK Hlam Hs) ltac:(rewrite <- Eb; exact Hbs) Hβ).
Qed.

(** β at an embedding's instance: the family at [(λy. b) s] against [b[s/y]]. *)
Lemma fam_beta0 {Δ m K b s} : m <= 2 -> ctx_extn m Δ Γ -> [ G ; Δ ⊢[ i ] ] -> [ G ; Δ ⊢[ i ] K : tyNat @ lzero ] ->
  [ G ; Δ ,, tyFin K @ lzero ⊢[ i ] b : tyFin n⟨rshift (S m)⟩ @ lzero ] -> [ G ; Δ ⊢[ i ] s : tyFin K @ lzero ] ->
  b[lsingle s] = var 0 -> [ G ; Δ ⊢[ i ] var 0 : tyFin n⟨rshift m⟩ @ lzero ] ->
  [ G ; Δ ⊢[ i ] F⟨rlift (rshift m)⟩[lsingle (app (lam lzero lzero (tyFin K) b) lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) s)]
      ≅ F⟨rlift (rshift m)⟩[lsingle (var 0)] @ l ].
Proof using Hc NW Nn FE0.
  intros Hm Hr HΔ HK Hb Hs Eb Hbs. rewrite <- Eb in Hbs.
  assert (HFK : [ G ; Δ ⊢[ i ] tyFin K @ lzero ]) by (apply wft_fin; [exact Hv | exact HK]).
  assert (HΔK : [ G ; Δ ,, tyFin K @ lzero ⊢[ i ] ]) by (cext; [exact HFK | exact I]).
  assert (HC : [ G ; Δ ,, tyFin K @ lzero ⊢[ i ] tyFin n⟨rshift (S m)⟩ @ lzero ])
    by (apply wft_fin; [exact Hv|]; apply (NW (S m)); [lia | exact Hr | exact HΔK]).
  assert (E : (tyFin n⟨rshift (S m)⟩)[lsingle s] = tyFin n⟨rshift m⟩)
    by (change ((tyFin n⟨rshift (S m)⟩)[lsingle s]) with (tyFin (n⟨rshift (S m)⟩[lsingle s])); now rewrite shiftS_single).
  assert (Hlam : [ G ; Δ ⊢[ i ] lam lzero lzero (tyFin K) b : tyPi lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) @ lmax lzero lzero ])
    by (apply wf_lam; [exact Hv | exact I | exact I | exact HFK | exact Hb]).
  assert (Hβ : [ G ; Δ ⊢[ i ] app (lam lzero lzero (tyFin K) b) lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) s ≅ b[lsingle s] : tyFin n⟨rshift m⟩ @ lzero ])
    by (rewrite <- E; exact (eqtm_beta _ _ _ lzero lzero _ _ _ _ Hc I I HFK HC Hb Hs)).
  rewrite Eb in Hβ.
  exact (FE0 m Δ _ _ _ ltac:(lia) Hr HΔ (emb_app_wf (m := m) ltac:(lia) Hr HΔ HK Hlam Hs) ltac:(rewrite <- Eb; exact Hbs) Hβ).
Qed.

Lemma dnth_emb_wf {Δ m K} : m <= 9 -> ctx_extn m Δ Γ -> [ G ; Δ ⊢[ i ] ] -> [ G ; Δ ⊢[ i ] K : tyNat @ lzero ] ->
  [ G ; Δ ⊢[ i ] tyPi lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) @ lzero ].
Proof using Hc NW Nn.
  intros Hm Hr HΔ HK.
  assert (HFK : [ G ; Δ ⊢[ i ] tyFin K @ lzero ]) by (apply wft_fin; [exact Hv | exact HK]).
  assert (HΔK : [ G ; Δ ,, tyFin K @ lzero ⊢[ i ] ]) by (cext; [exact HFK | exact I]).
  eapply wft_lconv; [| exact lq_00]. apply wft_pi; [exact Hv | exact I | exact I | exact HFK |].
  apply wft_fin; [exact Hv|]. apply (NW (S m)); [lia | exact Hr | exact HΔK].
Qed.

Lemma dnth_mot_wf : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] dnthMot l n F @ l ].
Proof using Hc Hl HΓ Nn NF Hn HF NW FW FV FE FE0.
  assert (H1 : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] ]) by (cext; [apply wft_nat; [exact Hv | rewrite Hi; exact HΓ] | exact I]).
  assert (Hk1 : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] var 0 : tyNat @ lzero ]) by wvar.
  assert (HE : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] dnthEmb n @ lzero ]).
  { unfold dnthEmb. nshift. exact (dnth_emb_wf (m := 1) (Δ := Γ ,, tyNat @ lzero) ltac:(lia) eq_refl H1 Hk1). }
  set (Δ2 := Γ ,, tyNat @ lzero ,, dnthEmb n @ lzero).
  assert (H2 : [ G ; Δ2 ⊢[ i ] ]) by (cext; [exact HE | exact I]).
  assert (Hk2 : [ G ; Δ2 ⊢[ i ] var 1 : tyNat @ lzero ]) by wvar.
  assert (HF2 : [ G ; Δ2 ⊢[ i ] tyFin (var 1) @ lzero ]) by (apply wft_fin; [exact Hv | exact Hk2]).
  assert (H3 : [ G ; Δ2 ,, tyFin (var 1) @ lzero ⊢[ i ] ]) by (cext; [exact HF2 | exact I]).
  assert (HFam : [ G ; Δ2 ,, tyFin (var 1) @ lzero ⊢[ i ] dnthFam n F @ l ]).
  { unfold dnthFam. nshift. apply (FW 3); [lia | ext_n | exact H3 |].
    apply (emb_app_wf (m := 3)); [lia | ext_n | exact H3 | wvar | | wvar].
    eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]. wvar. }
  assert (HD : [ G ; Δ2 ⊢[ i ] tyDVec l (var 1) (dnthFam n F) @ l ])
    by (apply wft_dvec; [exact Hv | exact Hl | exact Hk2 | exact HFam]).
  assert (H3' : [ G ; Δ2 ,, tyDVec l (var 1) (dnthFam n F) @ l ⊢[ i ] ]) by (cext; [exact HD | exact Hl]).
  assert (HF3 : [ G ; Δ2 ,, tyDVec l (var 1) (dnthFam n F) @ l ⊢[ i ] tyFin (var 2) @ lzero ])
    by (apply wft_fin; [exact Hv | wvar]).
  assert (H4 : [ G ; Δ2 ,, tyDVec l (var 1) (dnthFam n F) @ l ,, tyFin (var 2) @ lzero ⊢[ i ] ])
    by (cext; [exact HF3 | exact I]).
  unfold dnthMot. eapply wft_lconv; [| apply lequiv_sym, dnc_lq_0l, Hl].
  apply wft_pi; [exact Hv | exact I | exact Hl | exact HE |].
  eapply wft_lconv; [| apply lequiv_sym, dnc_lq_ll, Hl].
  apply wft_pi; [exact Hv | exact Hl | exact Hl | exact HD |].
  eapply wft_lconv; [| apply lequiv_sym, dnc_lq_0l, Hl].
  apply wft_pi; [exact Hv | exact I | exact Hl | exact HF3 |].
  unfold dnthRes. nshift. apply (FW 4); [lia | ext_n | exact H4 |].
  apply (emb_app_wf (m := 4)); [lia | ext_n | exact H4 | wvar | | wvar].
  eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]. wvar.
Qed.

Lemma dnth_base_wf : [ G ; Γ ⊢[ i ] dnthBase l n F : (dnthMot l n F)[lsingle zero] @ l ].
Proof using Hc Hl HΓ Nn NF Hn HF NW FW FV FE FE0.
  rewrite (dnth_E0 l n F Nn NF). unfold dnthBase.
  assert (Hz : forall Δ, [ G ; Δ ⊢[ i ] ] -> [ G ; Δ ⊢[ i ] zero : tyNat @ lzero ])
    by (intros Δ HΔ; apply wf_zero; [exact Hv | rewrite Hi; exact HΔ]).
  assert (HE0 : [ G ; Γ ⊢[ i ] tyPi lzero lzero (tyFin zero) (tyFin n⟨↑⟩) @ lzero ])
    by exact (dnth_emb_wf (m := 0) (Δ := Γ) ltac:(lia) eq_refl HΓ (Hz _ HΓ)).
  set (Γ1 := Γ ,, tyPi lzero lzero (tyFin zero) (tyFin n⟨↑⟩) @ lzero).
  assert (H1 : [ G ; Γ1 ⊢[ i ] ]) by (cext; [exact HE0 | exact I]).
  assert (HF1 : [ G ; Γ1 ⊢[ i ] tyFin zero @ lzero ]) by (apply wft_fin; [exact Hv | exact (Hz _ H1)]).
  assert (H1' : [ G ; Γ1 ,, tyFin zero @ lzero ⊢[ i ] ]) by (cext; [exact HF1 | exact I]).
  assert (HD0 : [ G ; Γ1 ⊢[ i ] tyDVec l zero F⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin zero) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))] @ l ]).
  { apply wft_dvec; [exact Hv | exact Hl | exact (Hz _ H1) |]. nshift.
    apply (FW 2); [lia | ext_n | exact H1' |].
    apply (emb_app_wf (m := 2)); [lia | ext_n | exact H1' | exact (Hz _ H1') | | wvar].
    eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]. wvar. }
  set (Γ2 := Γ1 ,, tyDVec l zero F⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin zero) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))] @ l).
  assert (H2 : [ G ; Γ2 ⊢[ i ] ]) by (cext; [exact HD0 | exact Hl]).
  assert (HF2 : [ G ; Γ2 ⊢[ i ] tyFin zero @ lzero ]) by (apply wft_fin; [exact Hv | exact (Hz _ H2)]).
  assert (H3 : [ G ; Γ2 ,, tyFin zero @ lzero ⊢[ i ] ]) by (cext; [exact HF2 | exact I]).
  assert (EZ : forall Δ, [ G ; Δ ⊢[ i ] ] -> [ G ; Δ ⊢[ typeof i ] tyFin zero ≅ tyEmpty lzero @ lzero ])
    by (intros Δ HΔ; rewrite Hi; apply eqty_fin_zero; [exact Hc | rewrite Hi; exact HΔ]).
  assert (HEm : [ G ; Γ2 ,, tyFin zero @ lzero ⊢[ i ] tyEmpty lzero @ lzero ])
    by (apply wft_empty; [exact Hv | rewrite Hi; exact H3 | exact I]).
  assert (H4 : [ G ; Γ2 ,, tyFin zero @ lzero ,, tyEmpty lzero @ lzero ⊢[ i ] ]) by (cext; [exact HEm | exact I]).
  eapply wf_lconv; [| apply lequiv_sym, dnc_lq_0l, Hl].
  apply wf_lam; [exact Hv | exact I | exact Hl | exact HE0 |].
  eapply wf_lconv; [| apply lequiv_sym, dnc_lq_ll, Hl].
  apply wf_lam; [exact Hv | exact Hl | exact Hl | exact HD0 |].
  eapply wf_lconv; [| apply lequiv_sym, dnc_lq_0l, Hl].
  apply wf_lam; [exact Hv | exact I | exact Hl | exact HF2 |].
  eapply dnc_retype; [apply wf_elimEmpty; [exact Hv | exact Hl | exact I | |] |].
  - nshift. apply (FW 4); [lia | ext_n | exact H4 |].
    apply (emb_app_wf (m := 4)); [lia | ext_n | exact H4 | exact (Hz _ H4) | |].
    + eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]. wvar.
    + eapply wf_conv; [wvar | exact (EZ _ H4)].
  - eapply wf_conv; [wvar | apply eqty_sym, (EZ _ H3)].
  - meq.
Qed.

Lemma dnc_retm G' i' Δ x x' T k : [ G' ; Δ ⊢[ i' ] x' : T @ k ] -> x = x' -> [ G' ; Δ ⊢[ i' ] x : T @ k ].
Proof using . now intros ? ->. Qed.

(** The head and the tail of [DVec(S k̂; dnthFamS)] in the step's [case]
    branches (what [inv_ty_sig] read off [eqty_dvec_succ] in [DNth]). *)
Ltac sig_hd Hr HΔ Hk He Hx :=
  replace (dvecHd (var 5) (dnthFamS n F))
    with (F⟨rlift (rshift 6)⟩[lsingle (app (var 3) lzero lzero (tyFin (succ (var 5))) (tyFin n⟨rshift 7⟩)
            (tmInl lzero lzero (tyUnit lzero) (tyFin (var 5)) (tmTriv lzero)))]) by (unfold dnthFamS; meq);
  apply (FW 6); [lia | exact Hr | exact HΔ | exact (emb_app_wf (m := 6) ltac:(lia) Hr HΔ (wf_succ _ _ _ _ Hv Hk) He Hx)].
Ltac sig_tl HA :=
  lazymatch goal with |- [ _ ; ?D ⊢[ _ ] _ @ _ ] =>
    let HD := fresh "HD" in assert (HD : [ G ; D ⊢[ i ] ]) by (cext; [exact HA | exact Hl]);
    replace (dvecTl l (var 5) (dnthFamS n F))
      with (tyDVec l (var 6) F⟨rlift (rshift 8)⟩[lsingle (app (var 5) lzero lzero (tyFin (succ (var 7))) (tyFin n⟨rshift 9⟩)
              (tmInr lzero lzero (tyUnit lzero) (tyFin (var 7)) (var 0)))]) by (unfold dnthFamS; meq);
    let Hk := fresh "Hk" in assert (Hk : [ G ; D ⊢[ i ] var 6 : tyNat @ lzero ]) by wvar;
    let HD1 := fresh "HD1" in
    assert (HD1 : [ G ; D ,, tyFin (var 6) @ lzero ⊢[ i ] ]) by (cext; [apply wft_fin; [exact Hv | exact Hk] | exact I]);
    apply wft_dvec; [exact Hv | exact Hl | exact Hk |];
    apply (FW 8); [lia | ext_n | exact HD1 |];
    apply (emb_app_wf (m := 8)); [lia | ext_n | exact HD1 | apply wf_succ; [exact Hv | wvar]
                                 | eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]; wvar |];
    apply fin_of_sum; [wvar | apply wf_inr; [exact Hv | exact I | exact I | apply wft_unit; [exact Hv | rewrite Hi; exact HD1 | exact I]
                                            | apply wft_fin; [exact Hv | wvar] | wvar]]
  end.

Lemma dnth_step_wf :
  [ G ; Γ ,, tyNat @ lzero ,, dnthMot l n F @ l ⊢[ i ] dnthStep l n F : (dnthMot l n F)[lsucc] @ l ].
Proof using Hc Hl HΓ Nn NF Hn HF NW FW FV FE FE0.
  rewrite (dnth_ES l n F Nn NF). unfold dnthStep.
  assert (Hsucc : forall Δ t, [ G ; Δ ⊢[ i ] t : tyNat @ lzero ] -> [ G ; Δ ⊢[ i ] succ t : tyNat @ lzero ])
    by (intros; apply wf_succ; [exact Hv | assumption]).
  assert (H0 : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] ]) by (cext; [apply wft_nat; [exact Hv | rewrite Hi; exact HΓ] | exact I]).
  set (Δr := Γ ,, tyNat @ lzero ,, dnthMot l n F @ l).
  assert (Hr : [ G ; Δr ⊢[ i ] ]) by (cext; [exact dnth_mot_wf | exact Hl]).
  assert (HE1 : [ G ; Δr ⊢[ i ] tyPi lzero lzero (tyFin (succ (var 1))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) @ lzero ])
    by (nshift; apply (dnth_emb_wf (m := 2)); [lia | ext_n | exact Hr | apply Hsucc; wvar]).
  set (Δe := Δr ,, tyPi lzero lzero (tyFin (succ (var 1))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) @ lzero).
  assert (He : [ G ; Δe ⊢[ i ] ]) by (cext; [exact HE1 | exact I]).
  assert (HFe : [ G ; Δe ⊢[ i ] tyFin (succ (var 2)) @ lzero ]) by (apply wft_fin; [exact Hv | apply Hsucc; wvar]).
  assert (He' : [ G ; Δe ,, tyFin (succ (var 2)) @ lzero ⊢[ i ] ]) by (cext; [exact HFe | exact I]).
  assert (HD1 : [ G ; Δe ⊢[ i ] tyDVec l (succ (var 2)) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin (succ (var 3))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))] @ l ]).
  { apply wft_dvec; [exact Hv | exact Hl | apply Hsucc; wvar |]. nshift.
    apply (FW 4); [lia | ext_n | exact He' |].
    apply (emb_app_wf (m := 4)); [lia | ext_n | exact He' | apply Hsucc; wvar | | wvar].
    eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]. wvar. }
  set (Δc := Δe ,, tyDVec l (succ (var 2)) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin (succ (var 3))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))] @ l).
  assert (Hcs : [ G ; Δc ⊢[ i ] ]) by (cext; [exact HD1 | exact Hl]).
  assert (HFc : [ G ; Δc ⊢[ i ] tyFin (succ (var 3)) @ lzero ]) by (apply wft_fin; [exact Hv | apply Hsucc; wvar]).
  set (Δi := Δc ,, tyFin (succ (var 3)) @ lzero).
  assert (Hii : [ G ; Δi ⊢[ i ] ]) by (cext; [exact HFc | exact I]).
  eapply wf_lconv; [| apply lequiv_sym, dnc_lq_0l, Hl].
  apply wf_lam; [exact Hv | exact I | exact Hl | exact HE1 |].
  eapply wf_lconv; [| apply lequiv_sym, dnc_lq_ll, Hl].
  apply wf_lam; [exact Hv | exact Hl | exact Hl | exact HD1 |].
  eapply wf_lconv; [| apply lequiv_sym, dnc_lq_0l, Hl].
  apply wf_lam; [exact Hv | exact I | exact Hl | exact HFc |].
  assert (HU : forall Δ, [ G ; Δ ⊢[ i ] ] -> [ G ; Δ ⊢[ i ] tyUnit lzero @ lzero ])
    by (intros Δ HΔ; apply wft_unit; [exact Hv | rewrite Hi; exact HΔ | exact I]).
  assert (HB : [ G ; Δi ⊢[ i ] tyFin (var 4) @ lzero ]) by (apply wft_fin; [exact Hv | wvar]).
  assert (HS : [ G ; Δi ⊢[ i ] tySum lzero lzero (tyUnit lzero) (tyFin (var 4)) @ lmax lzero lzero ])
    by (apply wft_sum; [exact Hv | exact I | exact I | exact (HU _ Hii) | exact HB]).
  assert (HiS : [ G ; Δi ,, tySum lzero lzero (tyUnit lzero) (tyFin (var 4)) @ lmax lzero lzero ⊢[ i ] ])
    by (cext; [exact HS | cbn; auto]).
  eapply dnc_retype; [apply wf_case; [exact Hv | exact I | exact I | exact Hl | exact (HU _ Hii) | exact HB | | | | ] | meq].
  - (* the motive *) nshift. apply (FW 6); [lia | ext_n | exact HiS |].
    apply (emb_app_wf (m := 6)); [lia | ext_n | exact HiS | apply Hsucc; wvar | |].
    + eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]. wvar.
    + apply fin_of_sum; [wvar | wvar].
  - (* inl: the head, at the family's [inl ⟨⟩] instance (Unit-η) *)
    set (Δu := Δi ,, tyUnit lzero @ lzero).
    assert (Hu : [ G ; Δu ⊢[ i ] ]) by (cext; [exact (HU _ Hii) | exact I]).
    assert (Hk5 : [ G ; Δu ⊢[ i ] var 5 : tyNat @ lzero ]) by wvar.
    assert (HF5 : [ G ; Δu ⊢[ i ] tyFin (var 5) @ lzero ]) by (apply wft_fin; [exact Hv | exact Hk5]).
    assert (HFS1 : [ G ; Δu ⊢[ i ] tyFin (succ (var 5)) @ lzero ]) by (apply wft_fin; [exact Hv | apply Hsucc, Hk5]).
    assert (Hu' : [ G ; Δu ,, tyFin (succ (var 5)) @ lzero ⊢[ i ] ]) by (cext; [exact HFS1 | exact I]).
    assert (HFS : [ G ; Δu ,, tyFin (succ (var 5)) @ lzero ⊢[ i ] dnthFamS n F @ l ]).
    { unfold dnthFamS. nshift. apply (FW 7); [lia | ext_n | exact Hu' |].
      apply (emb_app_wf (m := 7)); [lia | ext_n | exact Hu' | apply Hsucc; wvar | | wvar].
      eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]. wvar. }
    pose proof (eqty_dvec_succ _ _ _ _ _ _ Hc Hl Hk5 HFS) as EQ.
    assert (He3 : [ G ; Δu ⊢[ i ] var 3 : tyPi lzero lzero (tyFin (succ (var 5))) (tyFin n⟨rshift 7⟩) @ lmax lzero lzero ])
      by (eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]; wvar).
    assert (Ht : [ G ; Δu ⊢[ i ] tmTriv lzero : tyUnit lzero @ lzero ]) by (apply wf_triv; [exact Hv | rewrite Hi; exact Hu | exact I]).
    assert (Hx' : [ G ; Δu ⊢[ i ] tmInl lzero lzero (tyUnit lzero) (tyFin (var 5)) (tmTriv lzero) : tyFin (succ (var 5)) @ lzero ])
      by (apply fin_of_sum; [exact Hk5 | apply wf_inl; [exact Hv | exact I | exact I | exact (HU _ Hu) | exact HF5 | exact Ht]]).
    assert (Hr6 : ctx_extn 6 Δu Γ) by ext_n.
    assert (HA : [ G ; Δu ⊢[ i ] dvecHd (var 5) (dnthFamS n F) @ l ]) by (sig_hd Hr6 Hu Hk5 He3 Hx').
    assert (HB2 : [ G ; Δu ,, dvecHd (var 5) (dnthFamS n F) @ l ⊢[ i ] dvecTl l (var 5) (dnthFamS n F) @ l ])
      by (sig_tl HA).
    eapply wf_conv; [apply wf_fst; [exact Hv | exact Hl | exact Hl | exact HA | exact HB2 |] |].
    + eapply wf_lconv; [| apply dnc_lq_ll, Hl]. eapply wf_conv; [| rewrite Hi; exact (eqty_sym _ _ _ _ _ _ EQ)].
      wvar. push_ren. unfold dnthFamS. meq.
    + rewrite Hi.
      assert (Hx : [ G ; Δu ⊢[ i ] tmInl lzero lzero (tyUnit lzero) (tyFin (var 5)) (var 0) : tyFin (succ (var 5)) @ lzero ])
        by (apply fin_of_sum; [exact Hk5 | apply wf_inl; [exact Hv | exact I | exact I | exact (HU _ Hu) | exact HF5 | wvar]]).
      assert (Exx : [ G ; Δu ⊢[ i ] tmInl lzero lzero (tyUnit lzero) (tyFin (var 5)) (var 0) ≅ tmInl lzero lzero (tyUnit lzero) (tyFin (var 5)) (tmTriv lzero) : tyFin (succ (var 5)) @ lzero ]).
      { apply fin_of_sum_eq; [exact Hk5 |]. apply eqtm_inl; [exact Hv | exact (lequiv_refl (gL G) lzero I) | exact (lequiv_refl (gL G) lzero I)
          | exact (eqty_refl _ _ _ _ _ (HU _ Hu)) | exact (eqty_refl _ _ _ _ _ HF5) |].
        apply eqtm_unit_eta; [exact Hc | exact I | wvar | exact Ht]. }
      refine (eqty_rw _ _ (FE 6 _ _ _ _ _ _ _ ltac:(lia) Hr6 Hu (emb_app_wf (m := 6) ltac:(lia) Hr6 Hu (Hsucc _ _ Hk5) He3 Hx)
        (emb_app_wf (m := 6) ltac:(lia) Hr6 Hu (Hsucc _ _ Hk5) He3 Hx') (emb_app_eq (m := 6) ltac:(lia) Hr6 Hu (Hsucc _ _ Hk5) He3 Exx)));
        unfold dnthFamS; meq.
  - (* inr: the recursive call at [λy. e (inr y)], the tail and the index (β) *)
    set (Δj := Δi ,, tyFin (var 4) @ lzero).
    assert (Hj : [ G ; Δj ⊢[ i ] ]) by (cext; [exact HB | exact I]).
    assert (Hk5 : [ G ; Δj ⊢[ i ] var 5 : tyNat @ lzero ]) by wvar.
    assert (HF5 : [ G ; Δj ⊢[ i ] tyFin (var 5) @ lzero ]) by (apply wft_fin; [exact Hv | exact Hk5]).
    assert (Hj5 : [ G ; Δj ,, tyFin (var 5) @ lzero ⊢[ i ] ]) by (cext; [exact HF5 | exact I]).
    assert (Hk6 : [ G ; Δj ,, tyFin (var 5) @ lzero ⊢[ i ] var 6 : tyNat @ lzero ]) by wvar.
    assert (HF6 : [ G ; Δj ,, tyFin (var 5) @ lzero ⊢[ i ] tyFin (var 6) @ lzero ]) by (apply wft_fin; [exact Hv | exact Hk6]).
    assert (Hj56 : [ G ; Δj ,, tyFin (var 5) @ lzero ,, tyFin (var 6) @ lzero ⊢[ i ] ]) by (cext; [exact HF6 | exact I]).
    assert (Hr6 : ctx_extn 6 Δj Γ) by ext_n.
    assert (Hr7 : ctx_extn 7 (Δj ,, tyFin (var 5) @ lzero) Γ) by ext_n.
    assert (Hr8 : ctx_extn 8 (Δj ,, tyFin (var 5) @ lzero ,, tyFin (var 6) @ lzero) Γ) by ext_n.
    assert (HbE : [ G ; Δj ,, tyFin (var 5) @ lzero ⊢[ i ] app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨rshift 8⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)) : tyFin n⟨rshift 7⟩ @ lzero ]).
    { apply (emb_app_wf (m := 7) ltac:(lia) Hr7 Hj5 (Hsucc _ _ Hk6)); [eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]; wvar |].
      apply fin_of_sum; [exact Hk6 | apply wf_inr; [exact Hv | exact I | exact I | exact (HU _ Hj5) | exact HF6 | wvar]]. }
    assert (HFres : [ G ; Δj ,, tyFin (var 5) @ lzero ⊢[ i ] F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))] @ l ])
      by (nshift; exact (FW 7 _ _ _ _ ltac:(lia) Hr7 Hj5 HbE)).
    assert (HDV : [ G ; Δj ⊢[ i ] tyDVec l (var 5) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))] @ l ]) by (apply wft_dvec; [exact Hv | exact Hl | exact Hk5 | exact HFres]).
    assert (HjD : [ G ; Δj ,, tyDVec l (var 5) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))] @ l ⊢[ i ] ]) by (cext; [exact HDV | exact Hl]).
    assert (Hk6' : [ G ; Δj ,, tyDVec l (var 5) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))] @ l ⊢[ i ] var 6 : tyNat @ lzero ]) by wvar.
    assert (HF6' : [ G ; Δj ,, tyDVec l (var 5) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))] @ l ⊢[ i ] tyFin (var 6) @ lzero ]) by (apply wft_fin; [exact Hv | exact Hk6']).
    assert (HjD6 : [ G ; Δj ,, tyDVec l (var 5) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))] @ l ,, tyFin (var 6) @ lzero ⊢[ i ] ]) by (cext; [exact HF6' | exact I]).
    assert (Hk7 : [ G ; Δj ,, tyDVec l (var 5) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))] @ l ,, tyFin (var 6) @ lzero ⊢[ i ] var 7 : tyNat @ lzero ]) by wvar.
    assert (Hr8' : ctx_extn 8 (Δj ,, tyDVec l (var 5) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))] @ l ,, tyFin (var 6) @ lzero) Γ) by ext_n.
    assert (HbE' : [ G ; Δj ,, tyDVec l (var 5) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))] @ l ,, tyFin (var 6) @ lzero ⊢[ i ] app (var 5) lzero lzero (tyFin (succ (var 7))) (tyFin n⟨rshift 9⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 7)) (var 0)) : tyFin n⟨rshift 8⟩ @ lzero ]).
    { apply (emb_app_wf (m := 8) ltac:(lia) Hr8' HjD6 (Hsucc _ _ Hk7)); [eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]; wvar |].
      apply fin_of_sum; [exact Hk7 | apply wf_inr; [exact Hv | exact I | exact I | exact (HU _ HjD6) | apply wft_fin; [exact Hv | exact Hk7] | wvar]]. }
    assert (HPi : [ G ; Δj ,, tyDVec l (var 5) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))] @ l ⊢[ i ] tyPi lzero l (tyFin (var 6)) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 5) lzero lzero (tyFin (succ (var 7))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 7)) (var 0)))] @ l ]).
    { eapply wft_lconv; [| apply lequiv_sym, dnc_lq_0l, Hl]. apply wft_pi; [exact Hv | exact I | exact Hl | exact HF6' |].
      nshift. exact (FW 8 _ _ _ _ ltac:(lia) Hr8' HjD6 HbE'). }
    eapply dnc_retype; [eapply wf_app; [exact Hv | exact I | exact Hl | exact HF5 | exact HFres | | wvar] | meq].
    eapply wf_lconv; [| apply dnc_lq_0l, Hl].
    eapply dnc_retype; [eapply wf_app; [exact Hv | exact Hl | exact Hl | exact HDV | exact HPi | | ] | meq_big].
    + (* the recursive call at the shifted embedding *)
      assert (Hr4 : [ G ; Δj ⊢[ i ] var 4 : tyPi lzero l (dnthEmb n)⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩
          (tyPi l l (tyDVec l (var 1) (dnthFam n F)) (tyPi lzero l (tyFin (var 2)) (dnthRes n F)))⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ @ l ])
        by wvar.
      assert (HEm : [ G ; Δj ⊢[ i ] (dnthEmb n)⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ @ lzero ]).
      { replace ((dnthEmb n)⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) with (tyPi lzero lzero (tyFin (var 5)) (tyFin n⟨rshift 7⟩))
          by (unfold dnthEmb; push_ren; rlk_simpl; nshift; reflexivity).
        apply (dnth_emb_wf (m := 6)); [lia | ext_n | exact Hj | exact Hk5]. }
      set (ΔE := Δj ,, (dnthEmb n)⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩ @ lzero).
      assert (HE : [ G ; ΔE ⊢[ i ] ]) by (cext; [exact HEm | exact I]).
      assert (HRest : [ G ; ΔE ⊢[ i ] (tyPi l l (tyDVec l (var 1) (dnthFam n F)) (tyPi lzero l (tyFin (var 2)) (dnthRes n F)))⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩ @ l ]).
      { replace ((tyPi l l (tyDVec l (var 1) (dnthFam n F)) (tyPi lzero l (tyFin (var 2)) (dnthRes n F)))⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩)
          with (tyPi l l (tyDVec l (var 6) F⟨rlift (rshift 8)⟩[lsingle (app (var 1) lzero lzero (tyFin (var 7)) (tyFin n⟨rshift 9⟩) (var 0))])
                  (tyPi lzero l (tyFin (var 7)) F⟨rlift (rshift 9)⟩[lsingle (app (var 2) lzero lzero (tyFin (var 8)) (tyFin n⟨rshift 10⟩) (var 0))]))
          by (unfold dnthFam, dnthRes; push_ren; meq).
        assert (Hk6E : [ G ; ΔE ⊢[ i ] var 6 : tyNat @ lzero ]) by wvar.
        assert (HEa : [ G ; ΔE ,, tyFin (var 6) @ lzero ⊢[ i ] ]) by (cext; [apply wft_fin; [exact Hv | exact Hk6E] | exact I]).
        assert (HDd : [ G ; ΔE ⊢[ i ] tyDVec l (var 6) F⟨rlift (rshift 8)⟩[lsingle (app (var 1) lzero lzero (tyFin (var 7)) (tyFin n⟨rshift 9⟩) (var 0))] @ l ]).
        { apply wft_dvec; [exact Hv | exact Hl | exact Hk6E |].
          apply (FW 8); [lia | ext_n | exact HEa |].
          apply (emb_app_wf (m := 8)); [lia | ext_n | exact HEa | wvar | eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]; wvar | wvar]. }
        assert (HEb : [ G ; ΔE ,, tyDVec l (var 6) F⟨rlift (rshift 8)⟩[lsingle (app (var 1) lzero lzero (tyFin (var 7)) (tyFin n⟨rshift 9⟩) (var 0))] @ l ⊢[ i ] ])
          by (cext; [exact HDd | exact Hl]).
        assert (HFg : [ G ; ΔE ,, tyDVec l (var 6) F⟨rlift (rshift 8)⟩[lsingle (app (var 1) lzero lzero (tyFin (var 7)) (tyFin n⟨rshift 9⟩) (var 0))] @ l ⊢[ i ] tyFin (var 7) @ lzero ])
          by (apply wft_fin; [exact Hv | wvar]).
        assert (HEc : [ G ; ΔE ,, tyDVec l (var 6) F⟨rlift (rshift 8)⟩[lsingle (app (var 1) lzero lzero (tyFin (var 7)) (tyFin n⟨rshift 9⟩) (var 0))] @ l ,, tyFin (var 7) @ lzero ⊢[ i ] ])
          by (cext; [exact HFg | exact I]).
        eapply wft_lconv; [| apply lequiv_sym, dnc_lq_ll, Hl].
        apply wft_pi; [exact Hv | exact Hl | exact Hl | exact HDd |].
        eapply wft_lconv; [| apply lequiv_sym, dnc_lq_0l, Hl].
        apply wft_pi; [exact Hv | exact I | exact Hl | exact HFg |].
        apply (FW 9); [lia | ext_n | exact HEc |].
        apply (emb_app_wf (m := 9)); [lia | ext_n | exact HEc | wvar | eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]; wvar | wvar]. }
      eapply wf_lconv; [| apply dnc_lq_ll, Hl].
      eapply wf_conv; [eapply wf_app; [exact Hv | exact I | exact Hl | exact HEm | exact HRest | eapply wf_lconv; [exact Hr4 | apply dnc_lq_0l, Hl] |] |].
      * eapply dnc_retype; [eapply wf_lconv; [apply wf_lam; [exact Hv | exact I | exact I | exact HF5 | nshift; exact HbE] | exact lq_00] |].
        unfold dnthEmb; push_ren; rlk_simpl; nshift; reflexivity.
      * rewrite Hi.
        assert (EF : [ G ; Δj ,, tyFin (var 5) @ lzero ⊢[ i ] F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))] ≅ F⟨rlift (rshift 7)⟩[lsingle (app (lam lzero lzero (tyFin (var 6)) (app (var 5) lzero lzero (tyFin (succ (var 7))) (tyFin n⟨rshift 9⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 7)) (var 0)))) lzero lzero (tyFin (var 6)) (tyFin n⟨rshift 8⟩) (var 0))] @ l ]).
        { apply eqty_sym. refine (eqty_rw eq_refl _ (fam_beta (m := 7) ltac:(lia) Hr7 Hj5 Hk6 _ _ _ HbE)); [meq | | | meq].
          - assert (Hk7a : [ G ; Δj ,, tyFin (var 5) @ lzero ,, tyFin (var 6) @ lzero ⊢[ i ] var 7 : tyNat @ lzero ]) by wvar.
            apply (emb_app_wf (m := 8) ltac:(lia) Hr8 Hj56 (Hsucc _ _ Hk7a)); [eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]; wvar |].
            apply fin_of_sum; [wvar | apply wf_inr; [exact Hv | exact I | exact I | exact (HU _ Hj56) | apply wft_fin; [exact Hv | wvar] | wvar]].
          - wvar. }
        assert (HF7 : [ G ; Δj ,, tyDVec l (var 5) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))] @ l ,, tyFin (var 6) @ lzero ⊢[ i ] tyFin (var 7) @ lzero ]) by (apply wft_fin; [exact Hv | exact Hk7]).
        assert (Hj7 : [ G ; Δj ,, tyDVec l (var 5) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))] @ l ,, tyFin (var 6) @ lzero ,, tyFin (var 7) @ lzero ⊢[ i ] ]) by (cext; [exact HF7 | exact I]).
        assert (Hk8 : [ G ; Δj ,, tyDVec l (var 5) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))] @ l ,, tyFin (var 6) @ lzero ,, tyFin (var 7) @ lzero ⊢[ i ] var 8 : tyNat @ lzero ]) by wvar.
        assert (Hr9 : ctx_extn 9 (Δj ,, tyDVec l (var 5) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))] @ l ,, tyFin (var 6) @ lzero ,, tyFin (var 7) @ lzero) Γ) by ext_n.
        assert (EF8 : [ G ; Δj ,, tyDVec l (var 5) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))] @ l ,, tyFin (var 6) @ lzero ⊢[ i ] F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 5) lzero lzero (tyFin (succ (var 7))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 7)) (var 0)))] ≅ F⟨rlift (rshift 8)⟩[lsingle (app (lam lzero lzero (tyFin (var 7)) (app (var 6) lzero lzero (tyFin (succ (var 8))) (tyFin n⟨rshift 10⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 8)) (var 0)))) lzero lzero (tyFin (var 7)) (tyFin n⟨rshift 9⟩) (var 0))] @ l ]).
        { apply eqty_sym. refine (eqty_rw eq_refl _ (fam_beta (m := 8) ltac:(lia) Hr8' HjD6 Hk7 _ _ _ HbE')); [meq | | | meq].
          - apply (emb_app_wf (m := 9) ltac:(lia) Hr9 Hj7 (Hsucc _ _ Hk8)); [eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]; wvar |].
            apply fin_of_sum; [exact Hk8 | apply wf_inr; [exact Hv | exact I | exact I | exact (HU _ Hj7) | apply wft_fin; [exact Hv | exact Hk8] | wvar]].
          - wvar. }
        assert (EPi : [ G ; Δj ⊢[ i ] tyPi l l (tyDVec l (var 5) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 4) lzero lzero (tyFin (succ (var 6))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 6)) (var 0)))]) (tyPi lzero l (tyFin (var 6)) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 5) lzero lzero (tyFin (succ (var 7))) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 7)) (var 0)))]) ≅ tyPi l l (tyDVec l (var 5) F⟨rlift (rshift 7)⟩[lsingle (app (lam lzero lzero (tyFin (var 6)) (app (var 5) lzero lzero (tyFin (succ (var 7))) (tyFin n⟨rshift 9⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 7)) (var 0)))) lzero lzero (tyFin (var 6)) (tyFin n⟨rshift 8⟩) (var 0))]) (tyPi lzero l (tyFin (var 6)) F⟨rlift (rshift 8)⟩[lsingle (app (lam lzero lzero (tyFin (var 7)) (app (var 6) lzero lzero (tyFin (succ (var 8))) (tyFin n⟨rshift 10⟩) (tmInr lzero lzero (tyUnit lzero) (tyFin (var 8)) (var 0)))) lzero lzero (tyFin (var 7)) (tyFin n⟨rshift 9⟩) (var 0))]) @ lmax l l ]).
        { apply eqty_pi; [exact Hv | exact (lequiv_refl _ _ Hl) | exact (lequiv_refl _ _ Hl) | exact HDV | |].
          - apply eqty_dvec; [exact Hv | exact (lequiv_refl _ _ Hl) | exact Hk5 | exact (eqtm_refl _ _ _ _ _ _ Hk5) | exact HFres | exact EF].
          - eapply eqty_lconv; [| apply lequiv_sym, dnc_lq_0l, Hl].
            apply eqty_pi; [exact Hv | exact (lequiv_refl (gL G) lzero I) | exact (lequiv_refl _ _ Hl) | exact HF6' | exact (eqty_refl _ _ _ _ _ HF6') | exact EF8]. }
        refine (eqty_rw eq_refl _ (eqty_lconv _ _ _ _ _ _ _ EPi (lequiv_sym _ _ _ (dnc_lq_ll Hl)))).
        unfold dnthFam, dnthRes. push_ren. push_subst. meq.
    + (* the tail *)
      assert (HFS1 : [ G ; Δj ⊢[ i ] tyFin (succ (var 5)) @ lzero ]) by (apply wft_fin; [exact Hv | apply Hsucc, Hk5]).
      assert (Hj' : [ G ; Δj ,, tyFin (succ (var 5)) @ lzero ⊢[ i ] ]) by (cext; [exact HFS1 | exact I]).
      assert (HFS : [ G ; Δj ,, tyFin (succ (var 5)) @ lzero ⊢[ i ] dnthFamS n F @ l ]).
      { unfold dnthFamS. nshift. apply (FW 7); [lia | ext_n | exact Hj' |].
        apply (emb_app_wf (m := 7)); [lia | ext_n | exact Hj' | apply Hsucc; wvar | | wvar].
        eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]. wvar. }
      pose proof (eqty_dvec_succ _ _ _ _ _ _ Hc Hl Hk5 HFS) as EQ.
      assert (He3 : [ G ; Δj ⊢[ i ] var 3 : tyPi lzero lzero (tyFin (succ (var 5))) (tyFin n⟨rshift 7⟩) @ lmax lzero lzero ])
        by (eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]; wvar).
      assert (Ht : [ G ; Δj ⊢[ i ] tmTriv lzero : tyUnit lzero @ lzero ]) by (apply wf_triv; [exact Hv | rewrite Hi; exact Hj | exact I]).
      assert (Hx' : [ G ; Δj ⊢[ i ] tmInl lzero lzero (tyUnit lzero) (tyFin (var 5)) (tmTriv lzero) : tyFin (succ (var 5)) @ lzero ])
        by (apply fin_of_sum; [exact Hk5 | apply wf_inl; [exact Hv | exact I | exact I | exact (HU _ Hj) | exact HF5 | exact Ht]]).
      assert (HA : [ G ; Δj ⊢[ i ] dvecHd (var 5) (dnthFamS n F) @ l ]) by (sig_hd Hr6 Hj Hk5 He3 Hx').
      assert (HB2 : [ G ; Δj ,, dvecHd (var 5) (dnthFamS n F) @ l ⊢[ i ] dvecTl l (var 5) (dnthFamS n F) @ l ])
        by (sig_tl HA).
      eapply dnc_retype; [apply wf_snd; [exact Hv | exact Hl | exact Hl | exact HA | exact HB2 |] | unfold dnthFamS; push_subst; meq_big].
      eapply wf_lconv; [| apply dnc_lq_ll, Hl]. eapply wf_conv; [| rewrite Hi; exact (eqty_sym _ _ _ _ _ _ EQ)].
      wvar. push_ren. unfold dnthFamS. meq.
  - (* the scrutinee *) apply sum_of_fin; [wvar | wvar].
Qed.

(** [dnth]'s typing: the [natrec] at the length, applied to the identity
    embedding (β in the family, both of the tuple and of the result), the
    tuple and the index. *)
Lemma dnth_wf_core {cs t} : [ G ; Γ ⊢[ i ] cs : tyDVec l n F @ l ] -> [ G ; Γ ⊢[ i ] t : tyFin n @ lzero ] ->
  [ G ; Γ ⊢[ i ] tmDNth l n F cs t : F[lsingle t] @ l ].
Proof using Hc Hl HΓ Nn NF Hn HF NW FW FV FE FE0.
  intros Hcs Ht. unfold tmDNth.
  assert (HFn : [ G ; Γ ⊢[ i ] tyFin n @ lzero ]) by (apply wft_fin; [exact Hv | exact Hn]).
  assert (HΓn : [ G ; Γ ,, tyFin n @ lzero ⊢[ i ] ]) by (cext; [exact HFn | exact I]).
  assert (HDV : [ G ; Γ ⊢[ i ] tyDVec l n F @ l ]) by (apply wft_dvec; [exact Hv | exact Hl | exact Hn | exact HF]).
  assert (HΓD : [ G ; Γ ,, tyDVec l n F @ l ⊢[ i ] ]) by (cext; [exact HDV | exact Hl]).
  assert (HFn1 : [ G ; Γ ,, tyDVec l n F @ l ⊢[ i ] tyFin n⟨↑⟩ @ lzero ])
    by (apply wft_fin; [exact Hv | exact (NW 1 (Γ ,, tyDVec l n F @ l) ltac:(lia) eq_refl HΓD)]).
  assert (HΓD1 : [ G ; Γ ,, tyDVec l n F @ l ,, tyFin n⟨↑⟩ @ lzero ⊢[ i ] ]) by (cext; [exact HFn1 | exact I]).
  apply wf_app; [exact Hv | exact I | exact Hl | exact HFn | exact HF | | exact Ht].
  eapply wf_lconv; [| apply dnc_lq_0l, Hl].
  eapply dnc_retype; [eapply wf_app; [exact Hv | exact Hl | exact Hl | exact HDV | | | exact Hcs] |].
  - eapply wft_lconv; [| apply lequiv_sym, dnc_lq_0l, Hl]. apply wft_pi; [exact Hv | exact I | exact Hl | exact HFn1 |].
    replace (F⟨rlift ↑⟩) with (F⟨rlift (rshift 2)⟩[lsingle (var 0)]) by meq.
    apply (FV 2); [lia | ext_n | exact HΓD1 | wvar].
  - assert (HN : [ G ; Γ ⊢[ i ] natrec l (dnthMot l n F) (dnthBase l n F) (dnthStep l n F) n : tyPi lzero l (tyPi lzero lzero (tyFin n) (tyFin n⟨↑⟩)) (tyPi l l (tyDVec l n⟨↑⟩ F⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin n⟨↑⟩⟨↑⟩) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))]) (tyPi lzero l (tyFin n⟨↑⟩⟨↑⟩) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 2) lzero lzero (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))])) @ l ]).
    { eapply dnc_retype; [apply wf_natrec; [exact Hv | exact Hl | exact dnth_mot_wf | exact dnth_base_wf | exact dnth_step_wf | exact Hn] |].
      unfold dnthMot, dnthEmb, dnthFam, dnthRes. meq. }
    assert (HEm : [ G ; Γ ⊢[ i ] tyPi lzero lzero (tyFin n) (tyFin n⟨↑⟩) @ lzero ])
      by exact (dnth_emb_wf (m := 0) (Δ := Γ) ltac:(lia) eq_refl HΓ Hn).
    assert (HE : [ G ; Γ ,, tyPi lzero lzero (tyFin n) (tyFin n⟨↑⟩) @ lzero ⊢[ i ] ]) by (cext; [exact HEm | exact I]).
    set (ΓE := Γ ,, tyPi lzero lzero (tyFin n) (tyFin n⟨↑⟩) @ lzero) in *.
    assert (Hn1E : [ G ; ΓE ⊢[ i ] n⟨↑⟩ : tyNat @ lzero ]) by exact (NW 1 ΓE ltac:(lia) eq_refl HE).
    assert (HE1 : [ G ; ΓE ,, tyFin n⟨↑⟩ @ lzero ⊢[ i ] ]) by (cext; [apply wft_fin; [exact Hv | exact Hn1E] | exact I]).
    assert (HDE : [ G ; ΓE ⊢[ i ] tyDVec l n⟨↑⟩ F⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin n⟨↑⟩⟨↑⟩) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))] @ l ]).
    { apply wft_dvec; [exact Hv | exact Hl | exact Hn1E |]. nshift.
      apply (FW 2); [lia | ext_n | exact HE1 |].
      apply (emb_app_wf (m := 2)); [lia | ext_n | exact HE1 | apply (NW 2); [lia | ext_n | exact HE1] | | wvar].
      eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]. wvar. }
    assert (HD : [ G ; ΓE ,, tyDVec l n⟨↑⟩ F⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin n⟨↑⟩⟨↑⟩) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))] @ l ⊢[ i ] ])
      by (cext; [exact HDE | exact Hl]).
    assert (Hn2D : [ G ; ΓE ,, tyDVec l n⟨↑⟩ F⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin n⟨↑⟩⟨↑⟩) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))] @ l ⊢[ i ] n⟨↑⟩⟨↑⟩ : tyNat @ lzero ])
      by (nshift; apply (NW 2); [lia | ext_n | exact HD]).
    assert (HD1 : [ G ; ΓE ,, tyDVec l n⟨↑⟩ F⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin n⟨↑⟩⟨↑⟩) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))] @ l ,, tyFin n⟨↑⟩⟨↑⟩ @ lzero ⊢[ i ] ])
      by (cext; [apply wft_fin; [exact Hv | exact Hn2D] | exact I]).
    assert (HRest : [ G ; ΓE ⊢[ i ] tyPi l l (tyDVec l n⟨↑⟩ F⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 1) lzero lzero (tyFin n⟨↑⟩⟨↑⟩) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))])
        (tyPi lzero l (tyFin n⟨↑⟩⟨↑⟩) F⟨rlift ↑⟩⟨rlift ↑⟩⟨rlift ↑⟩[lsingle (app (var 2) lzero lzero (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩) (tyFin n⟨↑⟩⟨↑⟩⟨↑⟩⟨↑⟩) (var 0))]) @ l ]).
    { eapply wft_lconv; [| apply lequiv_sym, dnc_lq_ll, Hl].
      apply wft_pi; [exact Hv | exact Hl | exact Hl | exact HDE |].
      eapply wft_lconv; [| apply lequiv_sym, dnc_lq_0l, Hl].
      apply wft_pi; [exact Hv | exact I | exact Hl | apply wft_fin; [exact Hv | exact Hn2D] |].
      nshift. apply (FW 3); [lia | ext_n | exact HD1 |].
      apply (emb_app_wf (m := 3)); [lia | ext_n | exact HD1 | apply (NW 3); [lia | ext_n | exact HD1] | | wvar].
      eapply wf_lconv; [| exact (lequiv_sym _ _ _ lq_00)]. wvar. }
    eapply wf_lconv; [| apply dnc_lq_ll, Hl].
    eapply wf_conv; [eapply wf_app; [exact Hv | exact I | exact Hl | exact HEm | exact HRest | eapply wf_lconv; [exact HN | apply dnc_lq_0l, Hl] |] |].
    + eapply wf_lconv; [| exact lq_00]. apply wf_lam; [exact Hv | exact I | exact I | exact HFn | wvar].
    + rewrite Hi.
      assert (Hr1 : ctx_extn 1 (Γ ,, tyFin n @ lzero) Γ) by ext_n.
      assert (Hr2 : ctx_extn 2 (Γ ,, tyDVec l n F @ l ,, tyFin n⟨↑⟩ @ lzero) Γ) by ext_n.
      assert (Hn1 : [ G ; Γ ,, tyFin n @ lzero ⊢[ i ] n⟨rshift 1⟩ : tyNat @ lzero ]) by exact (NW 1 _ ltac:(lia) Hr1 HΓn).
      assert (Hn2 : [ G ; Γ ,, tyDVec l n F @ l ,, tyFin n⟨↑⟩ @ lzero ⊢[ i ] n⟨rshift 2⟩ : tyNat @ lzero ]) by exact (NW 2 _ ltac:(lia) Hr2 HΓD1).
      assert (E1 : [ G ; Γ ,, tyFin n @ lzero ⊢[ i ] F ≅ F⟨rlift (rshift 1)⟩[lsingle (app (lam lzero lzero (tyFin n⟨rshift 1⟩) (var 0)) lzero lzero (tyFin n⟨rshift 1⟩) (tyFin n⟨rshift 2⟩) (var 0))] @ l ]).
      { apply eqty_sym. refine (eqty_rw eq_refl _ (fam_beta0 (m := 1) ltac:(lia) Hr1 HΓn Hn1 _ _ _ _)); [meq | | wvar | reflexivity | wvar].
        assert (HX : [ G ; Γ ,, tyFin n @ lzero ,, tyFin n⟨rshift 1⟩ @ lzero ⊢[ i ] ]) by (cext; [apply wft_fin; [exact Hv | exact Hn1] | exact I]).
        wvar. }
      assert (E2 : [ G ; Γ ,, tyDVec l n F @ l ,, tyFin n⟨↑⟩ @ lzero ⊢[ i ] F⟨rlift ↑⟩ ≅ F⟨rlift (rshift 2)⟩[lsingle (app (lam lzero lzero (tyFin n⟨rshift 2⟩) (var 0)) lzero lzero (tyFin n⟨rshift 2⟩) (tyFin n⟨rshift 3⟩) (var 0))] @ l ]).
      { apply eqty_sym. refine (eqty_rw eq_refl _ (fam_beta0 (m := 2) ltac:(lia) Hr2 HΓD1 Hn2 _ _ _ _)); [meq | | wvar | reflexivity | wvar].
        assert (HX : [ G ; Γ ,, tyDVec l n F @ l ,, tyFin n⟨↑⟩ @ lzero ,, tyFin n⟨rshift 2⟩ @ lzero ⊢[ i ] ]) by (cext; [apply wft_fin; [exact Hv | exact Hn2] | exact I]).
        wvar. }
      assert (EPi : [ G ; Γ ⊢[ i ] tyPi l l (tyDVec l n F) (tyPi lzero l (tyFin n⟨↑⟩) F⟨rlift ↑⟩)
          ≅ tyPi l l (tyDVec l n F⟨rlift (rshift 1)⟩[lsingle (app (lam lzero lzero (tyFin n⟨rshift 1⟩) (var 0)) lzero lzero (tyFin n⟨rshift 1⟩) (tyFin n⟨rshift 2⟩) (var 0))]) (tyPi lzero l (tyFin n⟨↑⟩) F⟨rlift (rshift 2)⟩[lsingle (app (lam lzero lzero (tyFin n⟨rshift 2⟩) (var 0)) lzero lzero (tyFin n⟨rshift 2⟩) (tyFin n⟨rshift 3⟩) (var 0))]) @ lmax l l ]).
      { apply eqty_pi; [exact Hv | exact (lequiv_refl _ _ Hl) | exact (lequiv_refl _ _ Hl) | exact HDV | |].
        - apply eqty_dvec; [exact Hv | exact (lequiv_refl _ _ Hl) | exact Hn | exact (eqtm_refl _ _ _ _ _ _ Hn) | exact HF | exact E1].
        - eapply eqty_lconv; [| apply lequiv_sym, dnc_lq_0l, Hl].
          apply eqty_pi; [exact Hv | exact (lequiv_refl (gL G) lzero I) | exact (lequiv_refl _ _ Hl) | exact HFn1 | exact (eqty_refl _ _ _ _ _ HFn1) | exact E2]. }
      refine (eqty_rw eq_refl _ (eqty_lconv _ _ _ _ _ _ _ EPi (lequiv_sym _ _ _ (dnc_lq_ll Hl)))). meq.
  - meq.
Qed.

End Schema.

End DNthCore.

