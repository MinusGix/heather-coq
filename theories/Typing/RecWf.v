(** * The recursors' scopes are well formed (M3)

    If [G] is well formed, so are the global contexts of the motives
    ([recGT], [recGt]) and of the branches ([brG k]): their declarations
    (04:1150–1300) are well formed in the universe-weakened [G]. The
    automation and every branch but [elim_IWf]'s are [RecWfBase]'s; this
    file adds [dnth]'s typing to it ([wdnth], from [DNthCore]), so that
    only [elim_IWf]'s branch waits for that derivation. *)
From DeLaM.Typing Require Export RecWfBase.
From DeLaM.Typing Require Import TypedDnf DNthCore.

(** [dnth]'s typing at the expected type ([DNthCore.dnth_wf_core]): the
    length's and the family's instances under [m] locals are premises,
    each typed under abstract locals by [dnth_ext] below. *)
Lemma wf_dnth_eq G i Γ l n F cs t T : compt i -> lwf (gL G) l -> [ G ; Γ ⊢[ i ] ] ->
  [ G ; Γ ⊢[ i ] n : tyNat @ lzero ] -> [ G ; Γ ,, tyFin n @ lzero ⊢[ i ] F @ l ] ->
  (forall m Δ, m <= 11 -> ctx_extn m Δ Γ -> [ G ; Δ ⊢[ i ] ] ->
     [ G ; Δ ⊢[ i ] n⟨rshift m⟩ : tyNat @ lzero ]) ->
  (forall m Δ e K x, 2 <= m <= 9 -> ctx_extn m Δ Γ -> [ G ; Δ ⊢[ i ] ] ->
     [ G ; Δ ⊢[ i ] app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x : tyFin n⟨rshift m⟩ @ lzero ] -> wk_tm G i Δ (app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x) (tyFin n⟨rshift m⟩) ->
     [ G ; Δ ⊢[ i ] F⟨rlift (rshift m)⟩[lsingle (app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x)] @ l ]) ->
  (forall m Δ, 2 <= m <= 2 -> ctx_extn m Δ Γ -> [ G ; Δ ⊢[ i ] ] ->
     [ G ; Δ ⊢[ i ] var 0 : tyFin n⟨rshift m⟩ @ lzero ] -> wk_tm G i Δ (var 0) (tyFin n⟨rshift m⟩) ->
     [ G ; Δ ⊢[ i ] F⟨rlift (rshift m)⟩[lsingle (var 0)] @ l ]) ->
  (forall m Δ e K x e' K' x', 6 <= m <= 8 -> ctx_extn m Δ Γ -> [ G ; Δ ⊢[ i ] ] ->
     [ G ; Δ ⊢[ i ] app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x : tyFin n⟨rshift m⟩ @ lzero ] ->
     [ G ; Δ ⊢[ i ] app e' lzero lzero (tyFin K') (tyFin n⟨rshift (S m)⟩) x' : tyFin n⟨rshift m⟩ @ lzero ] ->
     [ G ; Δ ⊢[ i ] app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x ≅ app e' lzero lzero (tyFin K') (tyFin n⟨rshift (S m)⟩) x' : tyFin n⟨rshift m⟩ @ lzero ] ->
     wk_tm G i Δ (app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x) (tyFin n⟨rshift m⟩) -> wk_tm G i Δ (app e' lzero lzero (tyFin K') (tyFin n⟨rshift (S m)⟩) x') (tyFin n⟨rshift m⟩) -> wk_eq G i Δ (app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x) (app e' lzero lzero (tyFin K') (tyFin n⟨rshift (S m)⟩) x') (tyFin n⟨rshift m⟩) ->
     [ G ; Δ ⊢[ i ] F⟨rlift (rshift m)⟩[lsingle (app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x)]
                  ≅ F⟨rlift (rshift m)⟩[lsingle (app e' lzero lzero (tyFin K') (tyFin n⟨rshift (S m)⟩) x')] @ l ]) ->
  (forall m Δ e K x, m <= 2 -> ctx_extn m Δ Γ -> [ G ; Δ ⊢[ i ] ] ->
     [ G ; Δ ⊢[ i ] app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x : tyFin n⟨rshift m⟩ @ lzero ] ->
     [ G ; Δ ⊢[ i ] var 0 : tyFin n⟨rshift m⟩ @ lzero ] ->
     [ G ; Δ ⊢[ i ] app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x ≅ var 0 : tyFin n⟨rshift m⟩ @ lzero ] ->
     wk_tm G i Δ (app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x) (tyFin n⟨rshift m⟩) -> wk_tm G i Δ (var 0) (tyFin n⟨rshift m⟩) -> wk_eq G i Δ (app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x) (var 0) (tyFin n⟨rshift m⟩) ->
     [ G ; Δ ⊢[ i ] F⟨rlift (rshift m)⟩[lsingle (app e lzero lzero (tyFin K) (tyFin n⟨rshift (S m)⟩) x)]
                  ≅ F⟨rlift (rshift m)⟩[lsingle (var 0)] @ l ]) ->
  [ G ; Γ ⊢[ i ] cs : tyDVec l n F @ l ] -> [ G ; Γ ⊢[ i ] t : tyFin n @ lzero ] -> F[lsingle t] = T ->
  [ G ; Γ ⊢[ i ] tmDNth l n F cs t : T @ l ].
Proof.
  intros Hc Hl HΓ Hn HF NW FW FV FE FE0 Hcs Ht <-.
  exact (dnth_wf_core Hc Hl HΓ (wf_tm_nf Hn) (wf_ty_nf HF) Hn HF NW FW FV FE FE0 Hcs Ht).
Qed.

(** [Δ] extending [Γ] by a concrete number of locals, as [Γ] and as many
    abstract locals. *)
Lemma ctx_extn_S m Δ Γ : ctx_extn (S m) Δ Γ ->
  exists Δ' T l, Δ = (Δ' ,, T @ l) /\ ctx_extn m Δ' Γ.
Proof. destruct Δ; cbn; try contradiction; eauto. Qed.
Ltac ext_inv H :=
  lazymatch type of H with
  | ctx_extn 0 _ _ => cbn in H; subst
  | ctx_extn (S _) _ _ =>
      let D := fresh "D" in let T := fresh "T" in let l := fresh "l" in
      let E := fresh "E" in let H' := fresh "Hx" in
      destruct (ctx_extn_S _ _ _ H) as (D & T & l & E & H'); clear H; subst;
      ext_inv H'
  end.

Lemma dnf_of_wf G i Γ t T l : [ G ; Γ ⊢[ i ] t : T @ l ] -> dnftm t.
Proof. intros H. exact (proj1 (proj1 (proj2 (proj2 (proj2 typed_dnf))) _ _ _ _ _ _ H)). Qed.

(** The index's abstract parts are in deep normal form, by its typing
    ([wdnf] needs them, for the global instances it reaches). *)
Ltac dnf_hyps :=
  repeat match goal with
  | H : [ _ ; _ ⊢[ _ ] app ?e _ _ _ _ _ : _ @ _ ] |- _ =>
      is_var e; lazymatch goal with
      | _ : dnftm e |- _ => fail
      | _ => let Hd := fresh "Hd" in pose proof (dnf_of_wf _ _ _ _ _ _ H) as Hd; cbn [dnftm dnfty] in Hd;
             repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end
      end
  end.
(** A premise of [wf_dnth_eq]: one goal per number of locals in its
    range, under abstract locals. *)
Ltac dnth_ext tac :=
  let m := fresh "m" in let D := fresh "D" in let Hm := fresh "Hm" in let Hx := fresh "Hx" in
  intros m D; repeat lazymatch goal with |- forall _ : tm, _ => intro | |- forall _ : ty, _ => intro end; intros Hm Hx; intros;
  dnf_hyps;
  repeat (destruct m as [|m]; [first [exfalso; lia | ext_inv Hx; wnorm_hyps; tac] | try (exfalso; lia)]); fail "dnth_ext: an instance is left".

(** [RecWfBase]'s [wty] at [dnth]: its lemma, with its premises. *)
Ltac wdnth ::= eapply wf_dnth_eq;
  [ first [exact compt_D | exact compt_M] | lvl_ok | wctx | wty | wty
  | dnth_ext ltac:(wty) | dnth_ext ltac:(wnorm; wty) | dnth_ext ltac:(wnorm; wty) | dnth_ext ltac:(wnorm; weq) | dnth_ext ltac:(wnorm; weq)
  | wty | wty | wnorm; reflexivity ].

Section Scopes.
Context {G : gctx} (HG : [ ⊢ G ]).

(** [elim_IWf]'s branch (M17c): its step's context carries [dnth] in the
    induction hypothesis's type, typed by [DNthCore]'s lemma ([wdnth]). *)
Lemma wf_brG_60 : [ ⊢ brG 60 G ].
Proof using HG.
  pose proof (uwk_glob (br_nu 60) G HG) as Hu.
  unfold brG, gctx_uwk in *; cbn [gL gΨ] in *.
  cbn [brDecls List.app br_nu br_ar] in *; unfold gv, gu; wnorm; wglob.
Qed.

(** [elim_IWi]'s branch (M19c), as [elim_IWf]'s: its induction
    hypothesis's type applies a [dnth] to the field's argument. *)
Lemma wf_brG_64 : [ ⊢ brG 64 G ].
Proof using HG.
  pose proof (uwk_glob (br_nu 64) G HG) as Hu.
  unfold brG, gctx_uwk in *; cbn [gL gΨ] in *.
  cbn [brDecls List.app br_nu br_ar] in *; unfold gv, gu; wnorm; wglob.
Qed.

Lemma wf_brG k : k < nbr -> [ ⊢ brG k G ].
Proof using HG.
  intros Hk. assert (HW : 39 <= k < 43 \/ ~ 39 <= k < 43) by lia.
  destruct HW as [HW|HW]; [now apply (wf_brG_W HG)|].
  assert (HF : 47 <= k < 51 \/ ~ 47 <= k < 51) by lia.
  destruct HF as [HF|HF]; [now apply (wf_brG_Wf HG)|].
  assert (HI : 55 <= k < 60 \/ ~ 55 <= k < 60) by lia.
  destruct HI as [HI|HI]; [now apply (wf_brG_IWf HG)|].
  assert (H60 : k = 60 \/ k <> 60) by lia.
  destruct H60 as [->|H60]; [exact wf_brG_60|].
  assert (HJ : 61 <= k < 64 \/ ~ 61 <= k < 64) by lia.
  destruct HJ as [HJ|HJ]; [now apply (wf_brG_IWi HG)|].
  assert (H64 : k = 64 \/ k <> 64) by lia.
  destruct H64 as [->|H64]; [exact wf_brG_64|].
  pose proof (uwk_glob (br_nu k) G HG) as Hu.
  unfold brG, gctx_uwk in *; cbn [gL gΨ] in *.
  br_all ltac:(destruct k; [first [exfalso; lia | cbn [brDecls List.app br_nu br_ar] in *; unfold gv, gu;
    cbn [ren Ren_ty Ren_tm ren_ty ren_tm lren r2l rdrop rshift1]; wfd_all]|]). lia.
Qed.

End Scopes.
