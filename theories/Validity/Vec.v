(** * Validity of [Vec] and [Fin] (M14_DESIGN.md, M14a)

    Neither former has a case of its own in the relation: at a length that
    reduces to [0] or [S k], a [Vec] or [Fin] type is related by the case of
    its reduct ([Unit], [Σ], [Empty] or [+]), through the relation's
    closure under typed weak-head expansion; at a neutral length, it is a
    neutral type. The relation is built by induction on the length's
    [NatRel] ([LR_vec_nat], [LR_fin_nat]). [Σ]'s codomain is [Vec] at the
    predecessor in every Kripke world, which the induction hypothesis gives
    through the relation's Kripke weakening; [+]'s summands are at [Γ]. *)
From DeLaM.Validity Require Export WElim.

Section Vec.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

(** ** Syntax *)

Section KwSyntax.
Context {G : gctx} {Γ : ctx} (ρ : kwk G Γ).

Lemma kty_tyVec l A n : kty ρ (tyVec l A n) = tyVec l (kty ρ A) (ktm ρ n).
Proof. unfold kty, ktm; now rewrite gwa_tyVec. Qed.
Lemma kty_tyFin n : kty ρ (tyFin n) = tyFin (ktm ρ n).
Proof. unfold kty, ktm; now rewrite gwa_tyFin. Qed.

Lemma ktml_shift (t : tm) : ktml ρ t⟨↑⟩ = (ktm ρ t)⟨↑⟩.
Proof. unfold ktm, ktml. now rewrite gwa_ren, shift_lift. Qed.

(** [Σ]'s codomain at the successor does not depend on the first
    component. *)
Lemma vec_cod_single l A k a :
  (ktyl ρ (tyVec l A⟨↑⟩ k⟨↑⟩))[lsingle a] = tyVec l (kty ρ A) (ktm ρ k).
Proof.
  transitivity (tyVec l (ktyl ρ A⟨↑⟩)[lsingle a] (ktml ρ k⟨↑⟩)[lsingle a]).
  { unfold ktyl, ktml. now rewrite gwa_tyVec, ren_tyVec, subst_tyVec. }
  rewrite ktyl_shift, ktml_shift, shift_single_ty, shift_single; [reflexivity | ..];
    unfold kty, ktm; first [apply ren_nf | apply ren_nf_ty].
Qed.

End KwSyntax.

(** ** Typed reductions *)

Lemma tyred_vec {G Δ l A m w} : lwf (gL G) l -> [ G ; Δ ⊢g A @ l ] ->
  [ G ; Δ ⊢g m ⤳* w : tyNat @ lzero ] -> [ G ; Δ ⊢g tyVec l A m ⤳* tyVec l A w @ l ].
Proof.
  intros Hw HA [Hm Hr He]. split.
  - apply wft_vec; [exact ge_notV | exact Hw | exact HA | exact Hm].
  - now apply reds_vec.
  - apply eqty_vec; [exact ge_notV | now apply lequiv_refl | exact HA | now apply eqty_refl | exact He].
Qed.

Lemma tyred_fin {G Δ m w} :
  [ G ; Δ ⊢g m ⤳* w : tyNat @ lzero ] -> [ G ; Δ ⊢g tyFin m ⤳* tyFin w @ lzero ].
Proof.
  intros [Hm Hr He]. split.
  - apply wft_fin; [exact ge_notV | exact Hm].
  - now apply reds_fin.
  - apply eqty_fin; [exact ge_notV | exact He].
Qed.

Lemma wf_zero_g {G Δ} : [ G ; Δ ⊢g ] -> [ G ; Δ ⊢g zero : tyNat @ lzero ].
Proof. intros HΔ. apply wf_zero; [exact ge_notV | now rewrite ge_typeof]. Qed.

(** The reducts of the computation rules, as typed reductions. *)
Lemma tyred_vec_zero {G Δ l A} : lwf (gL G) l -> [ G ; Δ ⊢g A @ l ] ->
  [ G ; Δ ⊢g tyVec l A zero ⤳* tyUnit l @ l ].
Proof.
  intros Hw HA. pose proof (wf_zero_g (ctx_of_ty HA)) as Hz.
  apply tyred_step; [apply wft_vec; [exact ge_notV | exact Hw | exact HA | exact Hz] | constructor |].
  apply eqty_vec_zero; [exact ge_compt | exact Hw | exact HA].
Qed.

Lemma tyred_vec_succ {G Δ l A k} : lwf (gL G) l -> [ G ; Δ ⊢g A @ l ] ->
  [ G ; Δ ⊢g k : tyNat @ lzero ] ->
  [ G ; Δ ⊢g tyVec l A (succ k) ⤳* tySig l l A (tyVec l A⟨↑⟩ k⟨↑⟩) @ l ].
Proof.
  intros Hw HA Hk. assert (Hs : [ G ; Δ ⊢g succ k : tyNat @ lzero ]) by (apply wf_succ; [exact ge_notV | exact Hk]).
  apply tyred_step; [apply wft_vec; [exact ge_notV | exact Hw | exact HA | exact Hs] | constructor |].
  apply eqty_vec_succ; [exact ge_compt | exact Hw | exact HA | exact Hk].
Qed.

Lemma tyred_fin_zero {G Δ} : [ G ; Δ ⊢g ] -> [ G ; Δ ⊢g tyFin zero ⤳* tyEmpty lzero @ lzero ].
Proof.
  intros HΔ. apply tyred_step; [apply wft_fin; [exact ge_notV | exact (wf_zero_g HΔ)] | constructor |].
  apply eqty_fin_zero; [exact ge_compt | now rewrite ge_typeof].
Qed.

Lemma tyred_fin_succ {G Δ k} : [ G ; Δ ⊢g k : tyNat @ lzero ] ->
  [ G ; Δ ⊢g tyFin (succ k) ⤳* tySum lzero lzero (tyUnit lzero) (tyFin k) @ lzero ].
Proof.
  intros Hk. assert (Hs : [ G ; Δ ⊢g succ k : tyNat @ lzero ]) by (apply wf_succ; [exact ge_notV | exact Hk]).
  apply tyred_step; [apply wft_fin; [exact ge_notV | exact Hs] | constructor |].
  apply eqty_fin_succ; [exact ge_compt | exact Hk].
Qed.

(** ** The reducts' relations, up to typed weak-head expansion *)

Lemma LR_unit_red {G Δ l l' T T'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  [ G ; Δ ⊢g T ⤳* tyUnit l @ l ] -> [ G ; Δ ⊢g T' ⤳* tyUnit l' @ l ] -> LRty l G Δ T T'.
Proof.
  intros Hw Hl HT HT'. exists (UnitRel G Δ l).
  eapply LRunit with (l1 := l) (l2 := l');
    [now apply lequiv_refl | now apply lequiv_sym | exact Hw | exact HT | exact HT' | apply releq_refl].
Qed.

Lemma LR_empty_red {G Δ l l' T T'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  [ G ; Δ ⊢g T ⤳* tyEmpty l @ l ] -> [ G ; Δ ⊢g T' ⤳* tyEmpty l' @ l ] -> LRty l G Δ T T'.
Proof.
  intros Hw Hl HT HT'. exists (EmptyRel G Δ l).
  eapply LRempty with (l1 := l) (l2 := l');
    [now apply lequiv_refl | now apply lequiv_sym | exact Hw | exact HT | exact HT' | apply releq_refl].
Qed.

(** ** [Vec] *)

Section VecLR.
Context {G : gctx} {Δ : ctx} {l l' : lvl} {A A' : ty}
  (Hw : lwf (gL G) l) (Hl : lequiv (gL G) l l') (HRA : LRty l G Δ A A').

(** At a successor: [Σ] over the element type, with [Vec] at the
    predecessor (related at [Δ]) in every world. *)
Lemma LR_vec_sig {k k' T T'} : LRty l G Δ (tyVec l A k) (tyVec l' A' k') ->
  [ G ; Δ ⊢g T ⤳* tySig l l A (tyVec l A⟨↑⟩ k⟨↑⟩) @ l ] ->
  [ G ; Δ ⊢g T' ⤳* tySig l' l' A' (tyVec l' A'⟨↑⟩ k'⟨↑⟩) @ l ] -> LRty l G Δ T T'.
Proof.
  intros [RV HRV] HT HT'. destruct HRA as [RA HRA0].
  destruct (escape_ty _ _ _ _ _ _ _ _ HRA0) as (HA & HA' & HAA).
  destruct (escape_ty _ _ _ _ _ _ _ _ HRV) as (HV & HV' & HVV).
  assert (HΔA : [ G ; Δ ,, A @ l ⊢g ]) by now apply ext_wf_g.
  assert (HΔA' : [ G ; Δ ,, A' @ l ⊢g ]) by now apply ext_wf_g.
  set (domR := fun ρ : kwk G Δ => LRrel (lmeasure l) (kw_G ρ) (kw_Δ ρ) (kty ρ A) (kty ρ A') l).
  set (codR := fun (ρ : kwk G Δ) a a' (_ : domR ρ a a') =>
         LRrel (lmeasure l) (kw_G ρ) (kw_Δ ρ) (ktyl ρ (tyVec l A⟨↑⟩ k⟨↑⟩))[lsingle a]
           (ktyl ρ (tyVec l' A'⟨↑⟩ k'⟨↑⟩))[lsingle a'] l).
  eexists. eapply (LRsig _ _ _ _ _ _ _ l l l' l' A (tyVec l A⟨↑⟩ k⟨↑⟩) A' (tyVec l' A'⟨↑⟩ k'⟨↑⟩) domR codR);
    [split | | | apply releq_refl].
  - apply lequiv_sym, lmax_idem, Hw.
  - now apply lequiv_sym.
  - now apply lequiv_sym.
  - exact Hw.
  - exact Hw.
  - exact HT.
  - exact HT'.
  - exact HA.
  - exact HA'.
  - change (tyVec l A⟨↑⟩ k⟨↑⟩) with (tyVec l A k)⟨↑⟩.
    eapply wk1_ty_g; [rewrite ge_typeof; exact HΔA | exact HV].
  - change (tyVec l' A'⟨↑⟩ k'⟨↑⟩) with (tyVec l' A' k')⟨↑⟩.
    eapply wk1_ty_g; [rewrite ge_typeof; exact HΔA' | exact HV'].
  - exact HAA.
  - exact (geq_ty_wk (wkr_shift1 _ _ _) HΔA HVV).
  - intros ρ. destruct (LR_kwk _ _ _ _ _ _ _ HRA0 ρ) as (R' & HR' & _).
    exact (LR_canon _ _ _ _ _ _ _ HR').
  - intros ρ a a' ha. unfold codR. rewrite !vec_cod_single.
    destruct (LR_kwk _ _ _ _ _ _ _ HRV ρ) as (R' & HR' & _). rewrite !kty_tyVec in HR'.
    exact (LR_canon _ _ _ _ _ _ _ HR').
Qed.

Lemma LR_vec_nat {m m'} : NatRel G Δ m m' -> LRty l G Δ (tyVec l A m) (tyVec l' A' m').
Proof.
  pose proof HRA as [RA HRA0].
  destruct (escape_ty _ _ _ _ _ _ _ _ HRA0) as (HA & HA'0 & HAA).
  pose proof (lequiv_wf_r _ _ _ Hl) as Hw'.
  assert (HA' : [ G ; Δ ⊢g A' @ l' ]) by (eapply wft_lconv; [exact HA'0 | now apply lequiv_sym]).
  revert m m'.
  apply (NatRel_mut G Δ (fun m m' _ => LRty l G Δ (tyVec l A m) (tyVec l' A' m'))
                        (fun w w' _ => LRty l G Δ (tyVec l A w) (tyVec l' A' w'))).
  - intros t t' w w' Ht Ht' _ _ [R HR]. exists R.
    eapply LR_red_ty; [exact HR | exact (tyred_vec Hw HA Ht) |].
    exact (tyred_lconv _ _ _ _ (tyred_vec Hw' HA' Ht') Hl).
  - apply (LR_unit_red (l' := l')); [exact Hw | exact Hl | exact (tyred_vec_zero Hw HA) |].
    exact (tyred_lconv _ _ _ _ (tyred_vec_zero Hw' HA') Hl).
  - intros t t' Ht IH. destruct (NatRel_escape Ht) as (Hk & Hk' & _).
    apply (LR_vec_sig IH); [exact (tyred_vec_succ Hw HA Hk) |].
    exact (tyred_lconv _ _ _ _ (tyred_vec_succ Hw' HA' Hk') Hl).
  - intros ν ν' Hνν.
    pose proof (geq_tm_sound (gne_tm_geq Hνν)) as Hν.
    exists (NeRel G Δ (tyVec l A ν) (tyVec l' A' ν') l).
    eapply LRne.
    + apply tyred_refl, wft_vec; [exact ge_notV | exact Hw | exact HA | exact (eqtm_wf_l ge_typeof Hν)].
    + eapply tyred_lconv; [|exact Hl].
      apply tyred_refl, wft_vec; [exact ge_notV | exact Hw' | exact HA' | exact (eqtm_wf_r ge_typeof Hν)].
    + exact (gne_ty_vec Hl HA HAA Hνν).
    + apply releq_refl.
Qed.

End VecLR.

(** ** [Fin] *)

Section FinLR.
Context {G : gctx} {Δ : ctx} (HΔ : [ G ; Δ ⊢g ]).

(** At a successor: [Unit + Fin k], with [Fin k] related at [Δ]. *)
Lemma LR_fin_sum {k k' T T'} : LRty lzero G Δ (tyFin k) (tyFin k') ->
  [ G ; Δ ⊢g T ⤳* tySum lzero lzero (tyUnit lzero) (tyFin k) @ lzero ] ->
  [ G ; Δ ⊢g T' ⤳* tySum lzero lzero (tyUnit lzero) (tyFin k') @ lzero ] -> LRty lzero G Δ T T'.
Proof.
  intros [RB HRB] HT HT'.
  assert (Hz : lwf (gL G) lzero) by exact I. pose proof (lequiv_refl _ _ Hz) as Hzz.
  destruct (escape_ty _ _ _ _ _ _ _ _ HRB) as (HB & _ & HBB).
  pose proof (LR_unit_here HΔ Hz Hzz) as HRA.
  destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HA & _ & HAA).
  pose proof (LR_sum_here Hz Hz Hzz Hzz HA HAA HB HBB HRA HRB) as HS.
  destruct (LRty_lconv (ex_intro _ _ HS) (lequiv_sym _ _ _ (lmax_idem _ _ Hz))) as [R HR].
  exists R. eapply LR_red_ty; [exact HR | exact HT | exact HT'].
Qed.

Lemma LR_fin_nat {m m'} : NatRel G Δ m m' -> LRty lzero G Δ (tyFin m) (tyFin m').
Proof.
  revert m m'.
  apply (NatRel_mut G Δ (fun m m' _ => LRty lzero G Δ (tyFin m) (tyFin m'))
                        (fun w w' _ => LRty lzero G Δ (tyFin w) (tyFin w'))).
  - intros t t' w w' Ht Ht' _ _ [R HR]. exists R.
    eapply LR_red_ty; [exact HR | exact (tyred_fin Ht) | exact (tyred_fin Ht')].
  - apply (LR_empty_red (l' := lzero)); [exact I | exact (lequiv_refl (gL G) lzero I) | exact (tyred_fin_zero HΔ) | exact (tyred_fin_zero HΔ)].
  - intros t t' Ht IH. destruct (NatRel_escape Ht) as (Hk & Hk' & _).
    exact (LR_fin_sum IH (tyred_fin_succ Hk) (tyred_fin_succ Hk')).
  - intros ν ν' Hνν.
    pose proof (geq_tm_sound (gne_tm_geq Hνν)) as Hν.
    exists (NeRel G Δ (tyFin ν) (tyFin ν') lzero).
    eapply LRne.
    + apply tyred_refl, wft_fin; [exact ge_notV | exact (eqtm_wf_l ge_typeof Hν)].
    + apply tyred_refl, wft_fin; [exact ge_notV | exact (eqtm_wf_r ge_typeof Hν)].
    + exact (gne_ty_fin Hνν).
    + apply releq_refl.
Qed.

End FinLR.

(** ** The rules *)

Lemma V_vec {G Γ l l' A A' n n'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTy G Γ A A' l -> VTm G Γ n n' tyNat lzero -> VTy G Γ (tyVec l A n) (tyVec l' A' n') l.
Proof.
  intros Hw Hl VA Vn Δ d d' Hd. rewrite !subst_tyVec.
  pose proof (Vn _ _ _ Hd) as Hn. rewrite subst_tyNat in Hn.
  exact (LR_vec_nat Hw Hl (VA _ _ _ Hd) (proj1 LRtm_nat Hn)).
Qed.

Lemma V_fin {G Γ n n'} : VTm G Γ n n' tyNat lzero -> VTy G Γ (tyFin n) (tyFin n') lzero.
Proof.
  intros Vn Δ d d' Hd. rewrite !subst_tyFin.
  pose proof (Vn _ _ _ Hd) as Hn. rewrite subst_tyNat in Hn.
  exact (LR_fin_nat (SubRel_ctx Hd) (proj1 LRtm_nat Hn)).
Qed.

Lemma V_vec_zero {G Γ l l' A A'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTy G Γ A A' l -> VTy G Γ (tyVec l A zero) (tyUnit l') l.
Proof.
  intros Hw Hl VA Δ d d' Hd. rewrite subst_tyVec, subst_zero, subst_tyUnit.
  destruct (VA _ _ _ Hd) as [RA HRA]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HA & _ & _).
  apply (LR_unit_red (l' := l')); [exact Hw | exact Hl | exact (tyred_vec_zero Hw HA) |].
  apply tyred_refl, wft_unit_g; [exact (SubRel_ctx Hd) | exact Hl].
Qed.

Lemma V_vec_succ {G Γ l l' A A' n n'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTy G Γ A A' l -> VTm G Γ n n' tyNat lzero ->
  VTy G Γ (tyVec l A (succ n)) (tySig l' l' A' (tyVec l' A'⟨↑⟩ n'⟨↑⟩)) l.
Proof.
  intros Hw Hl VA Vn Δ d d' Hd.
  rewrite subst_tyVec, subst_succ, subst_tySig, subst_tyVec, shift_llift_ty, shift_llift.
  pose proof (VA _ _ _ Hd) as HRA. destruct HRA as [RA HRA0].
  destruct (escape_ty _ _ _ _ _ _ _ _ HRA0) as (HA & HA'0 & _).
  pose proof (Vn _ _ _ Hd) as Hn. rewrite subst_tyNat in Hn. apply LRtm_nat in Hn.
  destruct (NatRel_escape Hn) as (Hk & Hk' & _).
  pose proof (lequiv_wf_r _ _ _ Hl) as Hw'.
  assert (HA' : [ G ; Δ ⊢g A'[d'] @ l' ]) by (eapply wft_lconv; [exact HA'0 | now apply lequiv_sym]).
  apply (LR_vec_sig Hw Hl (ex_intro _ _ HRA0) (LR_vec_nat Hw Hl (ex_intro _ _ HRA0) Hn));
    [exact (tyred_vec_succ Hw HA Hk) |].
  eapply tyred_lconv; [|exact Hl].
  apply tyred_refl. exact (eqty_wf_r ge_typeof (tyred_eq _ _ _ _ _ _ (tyred_vec_succ Hw' HA' Hk'))).
Qed.

Lemma V_fin_zero {G Γ} : VTy G Γ (tyFin zero) (tyEmpty lzero) lzero.
Proof.
  intros Δ d d' Hd. rewrite subst_tyFin, subst_zero, subst_tyEmpty.
  pose proof (SubRel_ctx Hd) as HΔ.
  apply (LR_empty_red (l' := lzero)); [exact I | exact (lequiv_refl (gL G) lzero I) | exact (tyred_fin_zero HΔ) |].
  apply tyred_refl, wft_empty_g; [exact HΔ | exact (lequiv_refl (gL G) lzero I)].
Qed.

Lemma V_fin_succ {G Γ n n'} : VTm G Γ n n' tyNat lzero ->
  VTy G Γ (tyFin (succ n)) (tySum lzero lzero (tyUnit lzero) (tyFin n')) lzero.
Proof.
  intros Vn Δ d d' Hd. rewrite subst_tyFin, subst_succ, subst_tySum, subst_tyUnit, subst_tyFin.
  pose proof (SubRel_ctx Hd) as HΔ.
  pose proof (Vn _ _ _ Hd) as Hn. rewrite subst_tyNat in Hn. apply LRtm_nat in Hn.
  destruct (NatRel_escape Hn) as (Hk & Hk' & _).
  apply (LR_fin_sum HΔ (LR_fin_nat HΔ Hn)); [exact (tyred_fin_succ Hk) |].
  apply tyred_refl. exact (eqty_wf_r ge_typeof (tyred_eq _ _ _ _ _ _ (tyred_fin_succ Hk'))).
Qed.

(** ** The codes (M14b) and their decoding *)

(** Decoding a [Vec] code whose annotation [k] is equivalent to the level
    at which its element code is typed; the length rides across. *)
Lemma tyred_El_vec {G Δ la l k s n} : lequiv (gL G) la l -> lequiv (gL G) k l ->
  [ G ; Δ ⊢g s : tyU l @ lsuc l ] -> [ G ; Δ ⊢g n : tyNat @ lzero ] ->
  [ G ; Δ ⊢g tyEl la (tmVec k s n) ⤳* tyVec k (tyEl k s) n @ l ].
Proof.
  intros Hla Hk Hs Hn.
  pose proof (lequiv_wf_l _ _ _ Hk) as Wk.
  pose proof (conv_U' Hs (lequiv_sym _ _ _ Hk)) as Hsk.
  assert (Hc0 : [ G ; Δ ⊢g tmVec k s n : tyU k @ lsuc k ])
    by (apply wf_code_vec; [exact ge_notV | exact Wk | exact Hsk | exact Hn]).
  pose proof (conv_U' Hc0 Hk) as Hc.
  destruct (El_annot Hc Hla) as [HEl HEq].
  apply tyred_step; [exact HEl | constructor |].
  eapply eqty_trans; [exact HEq|].
  eapply (eqty_trans _ _ _ _ (tyEl k (tmVec k s n))).
  - apply eqty_El; [exact ge_notV | now apply lequiv_sym | apply eqtm_refl, Hc].
  - apply (eqty_lconv _ _ _ _ _ l k); [|now apply lequiv_sym].
    apply eqty_sym, eqty_El_vec; [exact ge_compt | exact Wk | exact Hsk | exact Hn].
Qed.

Lemma tyred_El_fin {G Δ la n} : lequiv (gL G) la lzero -> [ G ; Δ ⊢g n : tyNat @ lzero ] ->
  [ G ; Δ ⊢g tyEl la (tmFin n) ⤳* tyFin n @ lzero ].
Proof.
  intros Hla Hn.
  assert (Hc : [ G ; Δ ⊢g tmFin n : tyU lzero @ lsuc lzero ]) by (apply wf_code_fin; [exact ge_notV | exact Hn]).
  destruct (El_annot Hc Hla) as [HEl HEq].
  apply tyred_step; [exact HEl | constructor |].
  eapply eqty_trans; [exact HEq|].
  apply eqty_sym, eqty_El_fin; [exact ge_compt | exact Hn].
Qed.

Lemma V_El_vec {G Γ l s n} : lwf (gL G) l ->
  VTm G Γ s s (tyU l) (lsuc l) -> VTm G Γ n n tyNat lzero ->
  VTy G Γ (tyVec l (tyEl l s) n) (tyEl l (tmVec l s n)) l.
Proof.
  intros Hw Vs Vn Δ d d' Hd.
  pose proof (V_El Hw (lequiv_refl _ _ Hw) Vs) as VA.
  destruct (V_vec Hw (lequiv_refl _ _ Hw) VA Vn _ _ _ Hd) as [R HR].
  destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (HP & _ & _).
  pose proof (Vs _ _ _ (SubRel_refl_r Hd)) as Xs. pose proof (Vn _ _ _ (SubRel_refl_r Hd)) as Xn.
  rewrite !subst_tyU in Xs. rewrite subst_tyNat in Xn.
  exists R. eapply LR_red_ty; [exact HR | apply tyred_refl, HP |]. push_subst.
  apply tyred_El_vec; [now apply lequiv_refl | now apply lequiv_refl
                      | exact (proj1 (LRtm_escape Xs)) | exact (proj1 (LRtm_escape Xn))].
Qed.

Lemma V_code_vec {G Γ l l' s s' n n'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTm G Γ s s' (tyU l) (lsuc l) -> VTm G Γ n n' tyNat lzero ->
  VTm G Γ (tmVec l s n) (tmVec l' s' n') (tyU l) (lsuc l).
Proof.
  intros Hw Hl Vs Vn Δ d d' Hd.
  pose proof (V_El Hw Hl Vs) as VA.
  destruct (V_vec Hw Hl VA Vn _ _ _ Hd) as [R HR].
  pose proof (Vs _ _ _ Hd) as Xs. pose proof (Vn _ _ _ Hd) as Xn.
  rewrite !subst_tyU in Xs. rewrite subst_tyNat in Xn.
  destruct (LRtm_escape Xs) as [Hsd Hs'd']. destruct (LRtm_escape Xn) as [Hnd Hn'd'].
  pose proof (geq_tm_code_vec Hl (LRtm_geq Xs) (LRtm_geq Xn)) as Hgeq.
  pose proof (geq_tm_sound Hgeq) as Hgeq'.
  push_subst. apply (LRtm_U Hw).
  exists (tmVec l s[d] n[d]), (tmVec l' s'[d'] n'[d']).
  refine (conj (tmred_refl _ _ _ (eqtm_wf_l ge_typeof Hgeq'))
           (conj (tmred_refl _ _ _ (eqtm_wf_r ge_typeof Hgeq'))
           (conj (whnf_tmVec _ _ _) (conj (whnf_tmVec _ _ _) (conj Hgeq _))))).
  intros la lb Hla Hlb. rewrite LRbelow_spec by (rewrite ?lmeasure_suc; lia).
  exists R. eapply LR_red_ty; [exact HR | |]; push_subst.
  - apply tyred_El_vec; [exact Hla | now apply lequiv_refl | exact Hsd | exact Hnd].
  - apply tyred_El_vec; [exact Hlb | now apply lequiv_sym | exact Hs'd' | exact Hn'd'].
Qed.

Lemma V_El_fin {G Γ n} : VTm G Γ n n tyNat lzero -> VTy G Γ (tyFin n) (tyEl lzero (tmFin n)) lzero.
Proof.
  intros Vn Δ d d' Hd.
  destruct (V_fin Vn _ _ _ Hd) as [R HR].
  destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (HP & _ & _).
  pose proof (Vn _ _ _ (SubRel_refl_r Hd)) as Xn. rewrite subst_tyNat in Xn.
  exists R. eapply LR_red_ty; [exact HR | apply tyred_refl, HP |]. push_subst.
  apply tyred_El_fin; [exact (lequiv_refl (gL G) lzero I) | exact (proj1 (LRtm_escape Xn))].
Qed.

Lemma V_code_fin {G Γ n n'} : VTm G Γ n n' tyNat lzero ->
  VTm G Γ (tmFin n) (tmFin n') (tyU lzero) (lsuc lzero).
Proof.
  intros Vn Δ d d' Hd.
  destruct (V_fin Vn _ _ _ Hd) as [R HR].
  pose proof (Vn _ _ _ Hd) as Xn. rewrite subst_tyNat in Xn.
  destruct (LRtm_escape Xn) as [Hnd Hn'd'].
  pose proof (geq_tm_code_fin (LRtm_geq Xn)) as Hgeq.
  pose proof (geq_tm_sound Hgeq) as Hgeq'.
  push_subst. apply (LRtm_U (l := lzero) I).
  exists (tmFin n[d]), (tmFin n'[d']).
  refine (conj (tmred_refl _ _ _ (eqtm_wf_l ge_typeof Hgeq'))
           (conj (tmred_refl _ _ _ (eqtm_wf_r ge_typeof Hgeq'))
           (conj (whnf_tmFin _) (conj (whnf_tmFin _) (conj Hgeq _))))).
  intros la lb Hla Hlb. rewrite LRbelow_spec by (rewrite ?lmeasure_suc; lia).
  exists R. eapply LR_red_ty; [exact HR | |]; push_subst.
  - exact (tyred_El_fin Hla Hnd).
  - exact (tyred_El_fin Hlb Hn'd').
Qed.

End Vec.
