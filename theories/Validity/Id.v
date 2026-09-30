(** * Validity of the identity type (M11_DESIGN.md, M11a)

    Formation of [Id], [refl], [J] and its β rule. [J]'s scrutinee
    reduces to a [refl] or to a neutral ([IdNf]): at a [refl], [J] steps to
    its base case, whose motive instance is converted along the [refl]'s
    point (related to both endpoints); at a neutral, [J] is neutral. *)
From DeLaM.Validity Require Export SEq.

(** ** Syntax: the motive context's [Id] entry *)

Lemma Jmot_llift l A a d : (tyId l A⟨↑⟩ a⟨↑⟩ (var 0))[llift d] = tyId l A[d]⟨↑⟩ a[d]⟨↑⟩ (var 0).
Proof. rewrite subst_tyId, shift_llift_ty, shift_llift, subst_var, llk_llift. reflexivity. Qed.

Lemma Jmot_cons l A a d x : (tyId l A⟨↑⟩ a⟨↑⟩ (var 0))[lcons d x] = tyId l A[d] a[d] x.
Proof.
  rewrite subst_tyId. f_equal; [apply ren_subst_ty | apply ren_subst];
    intros n; rewrite rlk_shift1; reflexivity.
Qed.

Lemma lift2_single2_ty (M : ty) d n r :
  LK nftm d -> M[llift (llift d)][lsingle2 n r] = M[lcons (lcons d n) r].
Proof.
  intros Hd. apply subst_subst_ty. intros [|[|m]].
  - rewrite !llk_llift. reflexivity.
  - rewrite !llk_llift. change (ren_tm ?x ?r) with x⟨r⟩. reflexivity.
  - rewrite !llk_llift. change (ren_tm (ren_tm ?x ?r) ?r') with x⟨r⟩⟨r'⟩.
    cbn [llk]. rewrite shift2_single2 by apply Hd. reflexivity.
Qed.

Section Id.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

Local Lemma convg {G Δ t t' T T' l} :
  [ G ; Δ ⊢g t ≅ t' : T' @ l ] -> [ G ; Δ ⊢g T ≅ T' @ l ] -> [ G ; Δ ⊢g t ≅ t' : T @ l ].
Proof. intros H HT. apply eqtm_conv with (T' := T'); [exact H | now rewrite ge_typeof]. Qed.

(** ** [J]'s reductions, typed *)

Section JRed.
Context {G : gctx} {Δ : ctx} {l1 l2 : lvl} {A : ty} {a : tm} {M : ty} {c u : tm}
  (Hw1 : lwf (gL G) l1) (Hw2 : lwf (gL G) l2)
  (HA : [ G ; Δ ⊢g A @ l1 ]) (Ha : [ G ; Δ ⊢g a : A @ l1 ])
  (HI : [ G ; Δ ,, A @ l1 ⊢g tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ])
  (HM : [ G ; Δ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ⊢g M @ l2 ])
  (Hc : [ G ; Δ ⊢g c : M[lsingle2 a (tmRefl l1 A a)] @ l2 ])
  (Hu : [ G ; Δ ⊢g u : A @ l1 ]).

(** The motive, along equal proofs. *)
Lemma J_motive_conv {e e'} : [ G ; Δ ⊢g e ≅ e' : tyId l1 A a u @ l1 ] ->
  [ G ; Δ ⊢g M[lsingle2 u e] ≅ M[lsingle2 u e'] @ l2 ].
Proof.
  intros Hee. apply (wf_ty_func ge_typeof HM).
  apply (lsub_eq_J ge_typeof ge_notV Hw1 HA Ha Hu Hu (eqtm_refl _ _ _ _ _ _ Hu)
           (eqtm_wf_l ge_typeof Hee) (eqtm_wf_r ge_typeof Hee) Hee).
Qed.

(** A proof equal to a [refl] at a point equal to both endpoints: [J] is
    its base case. *)
Lemma J_refl_eq {e k C w} : [ G ; Δ ⊢g e ≅ tmRefl k C w : tyId l1 A a u @ l1 ] ->
  lequiv (gL G) k l1 -> [ G ; Δ ⊢g A ≅ C @ l1 ] ->
  [ G ; Δ ⊢g a ≅ w : A @ l1 ] -> [ G ; Δ ⊢g u ≅ w : A @ l1 ] ->
  [ G ; Δ ⊢g tmJ l1 l2 A a M c u e ≅ c : M[lsingle2 u e] @ l2 ] /\
  [ G ; Δ ⊢g M[lsingle2 a (tmRefl l1 A a)] ≅ M[lsingle2 u e] @ l2 ].
Proof.
  intros Hee Hk HAC Haw Huw.
  assert (Hau : [ G ; Δ ⊢g a ≅ u : A @ l1 ]) by (eapply eqtm_trans; [exact Haw | now apply eqtm_sym]).
  assert (HId : [ G ; Δ ⊢g tyId l1 A a a ≅ tyId l1 A a u @ l1 ]).
  { apply eqty_id; [exact ge_compt | now apply lequiv_refl | exact HA | now apply eqty_refl
                   | now apply eqtm_refl | exact Hau]. }
  assert (Hrr : [ G ; Δ ⊢g tmRefl l1 A a ≅ tmRefl k C w : tyId l1 A a a @ l1 ])
    by (apply eqtm_idrefl; [exact ge_compt | now apply lequiv_sym | exact HA | exact HAC | exact Haw]).
  assert (Her : [ G ; Δ ⊢g e ≅ tmRefl l1 A a : tyId l1 A a u @ l1 ]).
  { eapply eqtm_trans; [exact Hee|]. apply eqtm_sym. eapply convg; [exact Hrr | now apply eqty_sym]. }
  pose proof (J_motive_conv Her) as HMe.
  assert (Hcong : [ G ; Δ ⊢g tmJ l1 l2 A a M c u e ≅ tmJ l1 l2 A a M c a (tmRefl l1 A a)
                     : M[lsingle2 u e] @ l2 ]).
  { apply eqtm_J; first [exact ge_compt | now apply lequiv_refl | assumption | now apply eqty_refl
                         | now apply eqtm_refl | now apply eqtm_sym]. }
  pose proof (eqtm_J_beta _ _ _ _ _ _ _ _ _ ge_compt Hw1 Hw2 HA Ha HI HM Hc) as Hb.
  (* the motive at [(a, refl)] is the one at [(u, e)] *)
  assert (HMs : [ G ; Δ ⊢g M[lsingle2 a (tmRefl l1 A a)] ≅ M[lsingle2 u e] @ l2 ]).
  { apply eqty_sym. eapply eqty_trans; [exact HMe|].
    apply (wf_ty_func ge_typeof HM).
    apply (lsub_eq_J ge_typeof ge_notV Hw1 HA Ha Hu Ha (eqtm_sym _ _ _ _ _ _ _ Hau)); [| |].
    - eapply conv_tm'; [exact ge_typeof | exact (wf_idrefl _ _ _ _ _ _ ge_compt Hw1 HA Ha) | now apply eqty_sym].
    - eapply conv_tm'; [exact ge_typeof | exact (wf_idrefl _ _ _ _ _ _ ge_compt Hw1 HA Ha) | now apply eqty_sym].
    - apply eqtm_refl. eapply conv_tm'; [exact ge_typeof | exact (wf_idrefl _ _ _ _ _ _ ge_compt Hw1 HA Ha)
                                         | now apply eqty_sym]. }
  split; [|exact HMs].
  eapply eqtm_trans; [exact Hcong|]. eapply convg; [exact Hb | now apply eqty_sym].
Qed.

End JRed.

(** ** Formation and [refl] *)

Lemma LR_id_here {G Δ l l' A A' a a' b b' RA} : lwf (gL G) l -> lequiv (gL G) l l' ->
  [ G ; Δ ⊢g A @ l ] -> [ G ; Δ ⊢ A ≈ A' @ l ] ->
  [ G ; Δ ⊢ a ≈ a' : A @ l ] -> [ G ; Δ ⊢ b ≈ b' : A @ l ] ->
  LogRel l G Δ A A' l RA -> RA a a' -> RA b b' ->
  LogRel l G Δ (tyId l A a b) (tyId l' A' a' b') l (IdRel G Δ l A a b RA).
Proof.
  intros Hw Hl HA HAA Haa Hbb HRA Ra Rb.
  pose proof (geq_ty_sound (geq_ty_id Hl HA HAA Haa Hbb)) as EV.
  destruct (LR_tm_per _ _ _ _ _ _ _ HRA) as [Sy Tr].
  eapply LRid with (l1 := l) (l2 := l').
  - now apply lequiv_refl.
  - now apply lequiv_sym.
  - exact Hw.
  - apply tyred_refl, (eqty_wf_l ge_typeof EV).
  - apply tyred_refl, (eqty_wf_r ge_typeof EV).
  - exact HA.
  - exact HAA.
  - exact Haa.
  - exact Hbb.
  - exact HRA.
  - exact Ra.
  - exact Rb.
  - exact Sy.
  - exact Tr.
  - apply releq_refl.
Qed.

Lemma V_id {G Γ l l' A A' a a' b b'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTy G Γ A A' l -> VTm G Γ a a' A l -> VTm G Γ b b' A l ->
  VTy G Γ (tyId l A a b) (tyId l' A' a' b') l.
Proof.
  intros Hw Hl VA Va Vb Δ d d' Hd. push_subst.
  destruct (seq_at VA Va Hd) as (HA & EA & Ea). destruct (seq_at VA Vb Hd) as (_ & _ & Eb).
  destruct (VA _ _ _ Hd) as [RA HRA].
  eexists; apply (LR_id_here Hw Hl HA EA Ea Eb HRA).
  - exact (LRtm_inv HRA (LRtm_irrel_r (Va _ _ _ Hd) (ex_intro _ RA HRA))).
  - exact (LRtm_inv HRA (LRtm_irrel_r (Vb _ _ _ Hd) (ex_intro _ RA HRA))).
Qed.

Lemma V_idrefl {G Γ l l' A A' a a'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTy G Γ A A' l -> VTm G Γ a a' A l -> VTm G Γ (tmRefl l A a) (tmRefl l' A' a') (tyId l A a a) l.
Proof.
  intros Hw Hl VA Va Δ d d' Hd. push_subst.
  pose proof (VTy_refl_l VA) as VAA. pose proof (VTm_trans Va (VTm_sym Va)) as Vaa.
  destruct (seq_at VAA Vaa Hd) as (HA & EAA & Eaa).
  destruct (seq_at VA Va Hd) as (_ & EA & Ea).
  destruct (VAA _ _ _ Hd) as [RA HRA].
  destruct (LR_tm_per _ _ _ _ _ _ _ HRA) as [Sy Tr].
  assert (Raa : RA a[d] a[d']) by exact (LRtm_inv HRA (Vaa _ _ _ Hd)).
  assert (Ra : RA a[d] a'[d']) by exact (LRtm_inv HRA (Va _ _ _ Hd)).
  assert (Ra0 : RA a[d] a[d]) by exact (Tr _ _ _ Raa (Sy _ _ Raa)).
  pose proof (geq_ty_sound EA) as DA. pose proof (geq_tm_sound Ea) as Da.
  eapply LRtm_of; [exact (LR_id_here Hw (lequiv_refl _ _ Hw) HA EAA Eaa Eaa HRA Raa Raa)|].
  exists (tmRefl l A[d] a[d]), (tmRefl l' A'[d'] a'[d']).
  refine (conj (tmred_refl _ _ _ _) (conj (tmred_refl _ _ _ _) (conj _ _))).
  - apply wf_idrefl; [exact ge_compt | exact Hw | exact HA | exact (eqtm_wf_l ge_typeof Da)].
  - exact (pre_idrefl_r ge_typeof ge_notV Hl HA DA (eqty_wf_r ge_typeof DA) Da (eqtm_wf_r ge_typeof Da)).
  - exact (geq_tm_idrefl Hl HA EA Ea).
  - apply idnf_refl; auto using lequiv_refl, lequiv_sym.
    exact (geq_ty_trans EA (geq_ty_sym EA)).
Qed.

(** ** The code (M11b) and its decoding *)

(** Decoding a code whose annotation [k] is equivalent to the level [l]
    at which its pieces are typed. *)
Lemma tyred_El_id {G Δ la l k s t u} : lequiv (gL G) la l -> lequiv (gL G) k l ->
  [ G ; Δ ⊢g s : tyU l @ lsuc l ] -> [ G ; Δ ⊢g t : tyEl l s @ l ] -> [ G ; Δ ⊢g u : tyEl l s @ l ] ->
  [ G ; Δ ⊢g tyEl la (tmId k s t u) ⤳* tyId k (tyEl k s) t u @ l ].
Proof.
  intros Hla Hk Hs Ht Hu.
  assert (Hkl : lequiv (gL G) l k) by now apply lequiv_sym.
  pose proof (lequiv_wf_l _ _ _ Hk) as Hwk.
  pose proof (conv_U' Hs Hkl) as Hsk.
  assert (EEl : [ G ; Δ ⊢g tyEl k s ≅ tyEl l s @ k ])
    by (apply eqty_El; [exact ge_notV | exact Hk | apply eqtm_refl, Hsk]).
  assert (F : forall x, [ G ; Δ ⊢g x : tyEl l s @ l ] -> [ G ; Δ ⊢g x : tyEl k s @ k ]).
  { intros x Hx. eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hx Hk) | rewrite ge_typeof; exact EEl]. }
  assert (Hc : [ G ; Δ ⊢g tmId k s t u : tyU k @ lsuc k ])
    by (apply wf_code_id; [exact ge_compt | exact Hwk | exact Hsk | apply F, Ht | apply F, Hu]).
  pose proof (conv_U' Hc Hk) as Hcl.
  destruct (El_annot Hcl Hla) as [HEl HEq].
  apply tyred_step; [exact HEl | constructor |].
  eapply eqty_trans; [exact HEq|].
  eapply (eqty_trans _ _ _ _ (tyEl k (tmId k s t u))).
  - apply eqty_El; [exact ge_notV | exact Hkl | apply eqtm_refl, Hcl].
  - apply (eqty_lconv _ _ _ _ _ l k); [|exact Hkl].
    apply eqty_sym, eqty_El_id; [exact ge_compt | exact Hwk | exact Hsk | apply F, Ht | apply F, Hu].
Qed.

Lemma V_El_id {G Γ l s t u} : lwf (gL G) l ->
  VTm G Γ s s (tyU l) (lsuc l) -> VTm G Γ t t (tyEl l s) l -> VTm G Γ u u (tyEl l s) l ->
  VTy G Γ (tyId l (tyEl l s) t u) (tyEl l (tmId l s t u)) l.
Proof.
  intros Hw Vs Vt Vu Δ d d' Hd.
  pose proof (V_El Hw (lequiv_refl _ _ Hw) Vs) as VA.
  destruct (V_id Hw (lequiv_refl _ _ Hw) VA Vt Vu _ _ _ Hd) as [R HR].
  destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (HP & _ & _).
  pose proof (Vs _ _ _ (SubRel_refl_r Hd)) as Xs. pose proof (Vt _ _ _ (SubRel_refl_r Hd)) as Xt.
  pose proof (Vu _ _ _ (SubRel_refl_r Hd)) as Xu.
  rewrite !subst_tyU in Xs. rewrite !subst_tyEl in Xt, Xu.
  exists R. eapply LR_red_ty; [exact HR | apply tyred_refl, HP |]. push_subst.
  apply tyred_El_id; [now apply lequiv_refl | now apply lequiv_refl | exact (proj1 (LRtm_escape Xs))
                     | exact (proj1 (LRtm_escape Xt)) | exact (proj1 (LRtm_escape Xu))].
Qed.

Lemma V_code_id {G Γ l l' s s' t t' u u'} : lwf (gL G) l -> lequiv (gL G) l l' ->
  VTm G Γ s s' (tyU l) (lsuc l) -> VTm G Γ t t' (tyEl l s) l -> VTm G Γ u u' (tyEl l s) l ->
  VTm G Γ (tmId l s t u) (tmId l' s' t' u') (tyU l) (lsuc l).
Proof.
  intros Hw Hl Vs Vt Vu Δ d d' Hd.
  pose proof (V_El Hw Hl Vs) as VA.
  destruct (V_id Hw Hl VA Vt Vu _ _ _ Hd) as [R HR].
  pose proof (Vs _ _ _ Hd) as Xs. pose proof (Vt _ _ _ Hd) as Xt. pose proof (Vu _ _ _ Hd) as Xu.
  rewrite !subst_tyU in Xs. rewrite !subst_tyEl in Xt, Xu.
  destruct (LRtm_escape Xs) as [Hsd Hs'd'].
  pose proof (geq_tm_code_id Hl Hsd (LRtm_geq Xs) (LRtm_geq Xt) (LRtm_geq Xu)) as Hgeq.
  pose proof (geq_tm_sound Hgeq) as Hgeq'.
  assert (EEl : [ G ; Δ ⊢g tyEl l s'[d'] ≅ tyEl l s[d] @ l ]).
  { apply eqty_sym, eqty_El; [exact ge_notV | now apply lequiv_refl | exact (geq_tm_sound (LRtm_geq Xs))]. }
  assert (F : forall x, [ G ; Δ ⊢g x : tyEl l s[d] @ l ] -> [ G ; Δ ⊢g x : tyEl l s'[d'] @ l ]).
  { intros x Hx. eapply wf_conv; [exact Hx | rewrite ge_typeof; exact EEl]. }
  push_subst. apply (LRtm_U Hw).
  exists (tmId l s[d] t[d] u[d]), (tmId l' s'[d'] t'[d'] u'[d']).
  refine (conj (tmred_refl _ _ _ (eqtm_wf_l ge_typeof Hgeq'))
           (conj (tmred_refl _ _ _ (eqtm_wf_r ge_typeof Hgeq'))
           (conj (whnf_tmId _ _ _ _) (conj (whnf_tmId _ _ _ _) (conj Hgeq _))))).
  intros la lb Hla Hlb. rewrite LRbelow_spec by (rewrite ?lmeasure_suc; lia).
  exists R. eapply LR_red_ty; [exact HR | |]; push_subst.
  - apply tyred_El_id; [exact Hla | now apply lequiv_refl | exact Hsd
                       | exact (proj1 (LRtm_escape Xt)) | exact (proj1 (LRtm_escape Xu))].
  - apply tyred_El_id; [exact Hlb | now apply lequiv_sym | exact Hs'd'
                       | exact (F _ (proj2 (LRtm_escape Xt))) | exact (F _ (proj2 (LRtm_escape Xu)))].
Qed.

(** ** [J] *)

Section JAt.
Context {G : gctx} {Γ : ctx} {l1 l2 : lvl} {A A' : ty} {a a' : tm} {M M' : ty} {c c' : tm}
  (Hw1 : lwf (gL G) l1)
  (VA : VTy G Γ A A' l1) (Va : VTm G Γ a a' A l1)
  (VI : VTy G (Γ ,, A @ l1) (tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0)) (tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0)) l1)
  (VM : VTy G (Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1) M M' l2)
  (Vc : VTm G Γ c c' M[lsingle2 a (tmRefl l1 A a)] l2).

(** The premises of [J], at related substitutions. *)
Lemma J_at {Δ d d'} : SubRel G Γ Δ d d' ->
  [ G ; Δ ⊢g A[d] @ l1 ] /\ [ G ; Δ ⊢ A[d] ≈ A'[d'] @ l1 ] /\ [ G ; Δ ⊢ a[d] ≈ a'[d'] : A[d] @ l1 ] /\
  [ G ; Δ ,, A[d] @ l1 ⊢g tyId l1 A[d]⟨↑⟩ a[d]⟨↑⟩ (var 0) @ l1 ] /\
  [ G ; Δ ,, A[d] @ l1 ,, tyId l1 A[d]⟨↑⟩ a[d]⟨↑⟩ (var 0) @ l1 ⊢g M[llift (llift d)] @ l2 ] /\
  [ G ; Δ ,, A[d] @ l1 ,, tyId l1 A[d]⟨↑⟩ a[d]⟨↑⟩ (var 0) @ l1 ⊢ M[llift (llift d)] ≈ M'[llift (llift d')] @ l2 ] /\
  [ G ; Δ ⊢ c[d] ≈ c'[d'] : M[llift (llift d)][lsingle2 a[d] (tmRefl l1 A[d] a[d])] @ l2 ].
Proof.
  intros Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  destruct (seq_at VA Va Hd) as (HA & EA & Ea).
  pose proof (SubRel_lift Hd (VTy_refl_l VA) HA Hw1) as Hd1.
  destruct (VI _ _ _ Hd1) as [RI HRI]. destruct (escape_ty _ _ _ _ _ _ _ _ HRI) as (HI & _ & _).
  pose proof (SubRel_lift Hd1 VI HI Hw1) as Hd2.
  destruct (VM _ _ _ Hd2) as [RM HRM]. destruct (escape_ty _ _ _ _ _ _ _ _ HRM) as (HM & _ & EM).
  pose proof (LRtm_geq (Vc _ _ _ Hd)) as Ec.
  rewrite single2_subst_ty, subst_refl in Ec by exact Nd.
  rewrite Jmot_llift in HI, HM, EM.
  repeat split; assumption.
Qed.

Lemma V_J {l3 l4 u u' e e'} : lwf (gL G) l2 -> lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 ->
  VTm G Γ u u' A l1 -> VTm G Γ e e' (tyId l1 A a u) l1 ->
  VTm G Γ (tmJ l1 l2 A a M c u e) (tmJ l3 l4 A' a' M' c' u' e') M[lsingle2 u e] l2.
Proof.
  intros Hw2 H13 H24 Vu Ve Δ d d' Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  rewrite !single2_subst_ty by assumption. push_subst.
  pose proof (SubRel_refl_l Hd) as Hdd.
  destruct (J_at Hd) as (HA & EA & Ea & HI & HM & EM & Ec).
  pose proof (VTy_refl_l VA) as VAA. pose proof (VTm_trans Va (VTm_sym Va)) as Vaa.
  pose proof (VTm_trans Vu (VTm_sym Vu)) as Vuu. pose proof (VTm_trans Ve (VTm_sym Ve)) as Vee.
  (* the carrier's relation at [A[d]] *)
  destruct (VAA _ _ _ Hdd) as [RA HRA]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (_ & _ & EAd).
  destruct (LR_tm_per _ _ _ _ _ _ _ HRA) as [Sy Tr].
  pose proof (Vaa _ _ _ Hdd) as Xa. pose proof (Vuu _ _ _ Hdd) as Xu.
  assert (Raa : RA a[d] a[d]) by exact (LRtm_inv HRA Xa).
  assert (Ruu : RA u[d] u[d]) by exact (LRtm_inv HRA Xu).
  pose proof (LRtm_geq Xa) as Eaa. pose proof (LRtm_geq Xu) as Euu.
  pose proof (LRtm_geq (Vu _ _ _ Hd)) as Eu.
  (* the proof's relation is [IdRel] *)
  pose proof (Ve _ _ _ Hd) as Xe. rewrite !subst_tyId in Xe. pose proof (LRtm_geq Xe) as Ee.
  pose proof (LR_id_here Hw1 (lequiv_refl _ _ Hw1) HA EAd Eaa Euu HRA Raa Ruu) as HIdd.
  assert (Re : IdRel G Δ l1 A[d] a[d] u[d] RA e[d] e'[d'])
    by exact (LRtm_inv HIdd (LRtm_irrel_r Xe (ex_intro _ _ HIdd))).
  (* the motive at [(u, e)], on both sides *)
  assert (Hs0 : SubRel G (Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1) Δ
                  (lcons (lcons d u[d]) e[d]) (lcons (lcons d u[d]) e[d])).
  { apply SubRel_cons; [exact (SubRel_cons Hdd Xu)|].
    rewrite !Jmot_cons. pose proof (Vee _ _ _ Hdd) as X. rewrite !subst_tyId in X. exact X. }
  destruct (VTy_refl_l VM _ _ _ Hs0) as [RL HRL]. rewrite <- !lift2_single2_ty in HRL by exact Nd.
  assert (Hs1 : SubRel G (Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1) Δ
                  (lcons (lcons d u[d]) e[d]) (lcons (lcons d' u[d']) e[d'])).
  { apply SubRel_cons; [exact (SubRel_cons Hd (Vuu _ _ _ Hd))|].
    rewrite !Jmot_cons. pose proof (Vee _ _ _ Hd) as X. rewrite !subst_tyId in X. exact X. }
  pose proof (VTy_refl_l VM _ _ _ Hs1) as XT. rewrite <- !lift2_single2_ty in XT by assumption.
  eapply LRtm_irrel_r; [|exact XT].
  (* declarative forms *)
  pose proof (geq_ty_sound EA) as DA. pose proof (geq_tm_sound Ea) as Da.
  pose proof (geq_ty_sound EM) as DM. pose proof (geq_tm_sound Ec) as Dc.
  pose proof (geq_tm_sound Eu) as Du. pose proof (geq_tm_sound Ee) as De.
  pose proof (eqtm_wf_l ge_typeof Da) as Ha. pose proof (eqtm_wf_l ge_typeof Du) as Hu.
  pose proof (eqtm_wf_l ge_typeof Dc) as Hc.
  assert (HJJ : [ G ; Δ ⊢g tmJ l1 l2 A[d] a[d] M[llift (llift d)] c[d] u[d] e[d]
                   ≅ tmJ l3 l4 A'[d'] a'[d'] M'[llift (llift d')] c'[d'] u'[d'] e'[d']
                   : M[llift (llift d)][lsingle2 u[d] e[d]] @ l2 ])
    by exact (eqtm_J _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ge_compt H13 H24 HA DA Da HI HM DM Dc Du De).
  destruct Re as (w & w' & Hrw & Hrw' & Eww & Nww).
  destruct Nww as [k k' C C' w0 w0' Hk Hk' HC HC' Raw Raw' Ruw Ruw' | ν ν' Hν].
  - (* [refl]: both sides step to the base case *)
    pose proof (proj2 (proj2 (escape_tm _ _ _ _ _ _ _ _ HRA _ _ Raw))) as Eaw.
    pose proof (proj2 (proj2 (escape_tm _ _ _ _ _ _ _ _ HRA _ _ Ruw))) as Euw.
    destruct (J_refl_eq Hw1 Hw2 HA Ha HI HM Hc Hu (tmred_eq _ _ _ _ _ _ _ Hrw) Hk (geq_ty_sound HC)
                (geq_tm_sound Eaw) (geq_tm_sound Euw)) as [HJc HMs].
    assert (Lred : [ G ; Δ ⊢g tmJ l1 l2 A[d] a[d] M[llift (llift d)] c[d] u[d] e[d] ⤳* c[d]
                     : M[llift (llift d)][lsingle2 u[d] e[d]] @ l2 ]).
    { split; [exact (eqtm_wf_l ge_typeof HJc) | | exact HJc].
      eapply reds_trans; [apply reds_J, (tmred_red _ _ _ _ _ _ _ Hrw)|].
      econstructor; [apply red_J_refl | constructor]. }
    assert (Rred : [ G ; Δ ⊢g tmJ l3 l4 A'[d'] a'[d'] M'[llift (llift d')] c'[d'] u'[d'] e'[d'] ⤳* c'[d']
                     : M[llift (llift d)][lsingle2 u[d] e[d]] @ l2 ]).
    { split; [exact (eqtm_wf_r ge_typeof HJJ) | |].
      - eapply reds_trans; [apply reds_J, (tmred_red _ _ _ _ _ _ _ Hrw')|].
        econstructor; [apply red_J_refl | constructor].
      - eapply eqtm_trans; [apply eqtm_sym, HJJ|]. eapply eqtm_trans; [exact HJc|].
        eapply convg; [exact Dc | now apply eqty_sym]. }
    (* the base cases, at the motive instance of [(u, e)] *)
    assert (Rua : RA u[d] a[d]) by exact (Tr _ _ _ Ruw (Sy _ _ Raw)).
    pose proof (proj2 (proj2 (escape_tm _ _ _ _ _ _ _ _ HRA _ _ Rua))) as Eua.
    assert (DId : [ G ; Δ ⊢g tyId l1 A[d] a[d] a[d] ≅ tyId l1 A[d] a[d] u[d] @ l1 ]).
    { apply eqty_id; [exact ge_compt | now apply lequiv_refl | exact HA | now apply eqty_refl
                     | now apply eqtm_refl | exact (geq_tm_sound (geq_tm_sym Eua))]. }
    pose proof (LR_id_here Hw1 (lequiv_refl _ _ Hw1) HA EAd Eaa Eua HRA Raa Rua) as HIdua.
    assert (Xr : LRtm l1 G Δ (tyId l1 A[d] a[d] u[d]) (tyId l1 A[d] a[d] a[d]) e[d] (tmRefl l1 A[d] a[d])).
    { eapply LRtm_of; [exact HIdua|].
      exists (tmRefl k C w0), (tmRefl l1 A[d] a[d]).
      refine (conj Hrw (conj (tmred_refl _ _ _ _) (conj _ _))).
      - eapply conv_tm'; [exact ge_typeof | exact (wf_idrefl _ _ _ _ _ _ ge_compt Hw1 HA Ha)
                         | now apply eqty_sym].
      - eapply geq_tm_conv; [apply geq_tm_sym, (geq_tm_idrefl (lequiv_sym _ _ _ Hk) HA HC Eaw) | exact DId].
      - apply idnf_refl; auto using lequiv_refl. }
    assert (Hs2 : SubRel G (Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1) Δ
                    (lcons (lcons d u[d]) e[d]) (lcons (lcons d a[d]) (tmRefl l1 A[d] a[d]))).
    { apply SubRel_cons; [exact (SubRel_cons Hdd (LRtm_of HRA Rua))|].
      rewrite !Jmot_cons. exact Xr. }
    pose proof (VTy_refl_l VM _ _ _ Hs2) as XT2. rewrite <- !lift2_single2_ty in XT2 by exact Nd.
    pose proof (Vc _ _ _ Hd) as Xc. rewrite !single2_subst_ty, !subst_refl in Xc by assumption.
    eapply LRtm_red; [|exact Lred | exact Rred].
    eapply LRtm_irrel_r; [exact (LRtm_conv_l Xc XT2) | exact (ex_intro _ _ HRL)].
  - (* a neutral: [J] is neutral *)
    pose proof (tmred_eq _ _ _ _ _ _ _ Hrw) as Deν.
    assert (HJν : [ G ; Δ ⊢g tmJ l1 l2 A[d] a[d] M[llift (llift d)] c[d] u[d] e[d]
                     ≅ tmJ l1 l2 A[d] a[d] M[llift (llift d)] c[d] u[d] ν
                     : M[llift (llift d)][lsingle2 u[d] e[d]] @ l2 ]).
    { apply eqtm_J; first [exact ge_compt | now apply lequiv_refl | assumption | now apply eqty_refl
                           | now apply eqtm_refl]. }
    pose proof (J_motive_conv Hw1 HA Ha HM Hu Deν) as HMν.
    assert (HJνν : [ G ; Δ ⊢g tmJ l1 l2 A[d] a[d] M[llift (llift d)] c[d] u[d] ν
                      ≅ tmJ l3 l4 A'[d'] a'[d'] M'[llift (llift d')] c'[d'] u'[d'] ν'
                      : M[llift (llift d)][lsingle2 u[d] e[d]] @ l2 ]).
    { eapply convg; [|exact HMν].
      apply eqtm_J; first [exact ge_compt | assumption | exact (geq_tm_sound Eww)]. }
    assert (Lred : [ G ; Δ ⊢g tmJ l1 l2 A[d] a[d] M[llift (llift d)] c[d] u[d] e[d]
                     ⤳* tmJ l1 l2 A[d] a[d] M[llift (llift d)] c[d] u[d] ν
                     : M[llift (llift d)][lsingle2 u[d] e[d]] @ l2 ]).
    { split; [exact (eqtm_wf_l ge_typeof HJν) | apply reds_J, (tmred_red _ _ _ _ _ _ _ Hrw) | exact HJν]. }
    assert (Rred : [ G ; Δ ⊢g tmJ l3 l4 A'[d'] a'[d'] M'[llift (llift d')] c'[d'] u'[d'] e'[d']
                     ⤳* tmJ l3 l4 A'[d'] a'[d'] M'[llift (llift d')] c'[d'] u'[d'] ν'
                     : M[llift (llift d)][lsingle2 u[d] e[d]] @ l2 ]).
    { split; [exact (eqtm_wf_r ge_typeof HJJ) | apply reds_J, (tmred_red _ _ _ _ _ _ _ Hrw') |].
      eapply eqtm_trans; [apply eqtm_sym, HJJ|]. eapply eqtm_trans; [exact HJν | exact HJνν]. }
    pose proof (gne_tm_J H13 H24 HA EA Ea HI HM EM Ec Eu Hν) as Hne.
    apply (fun H => gne_tm_conv H (eqty_sym _ _ _ _ _ _ HMν)) in Hne.
    eapply LRtm_red; [|exact Lred | exact Rred].
    exact (LRtm_of HRL (LR_neutral _ _ _ _ _ _ _ HRL _ _ Hne Hne)).
Qed.

Lemma V_J_beta : lwf (gL G) l2 -> VTm G Γ c c M[lsingle2 a (tmRefl l1 A a)] l2 ->
  VTm G Γ (tmJ l1 l2 A a M c a (tmRefl l1 A a)) c M[lsingle2 a (tmRefl l1 A a)] l2.
Proof.
  intros Hw2 Vcc Δ d d' Hd. destruct (SubRel_nf _ _ _ _ _ Hd) as [Nd Nd'].
  destruct (J_at Hd) as (HA & _ & Ea & HI & HM & _ & Ec).
  pose proof (eqtm_wf_l ge_typeof (geq_tm_sound Ea)) as Ha.
  pose proof (eqtm_wf_l ge_typeof (geq_tm_sound Ec)) as Hc.
  pose proof (Vcc _ _ _ Hd) as X. rewrite !single2_subst_ty, !subst_refl in X |- * by assumption.
  push_subst. eapply LRtm_red_l; [exact X|].
  pose proof (eqtm_J_beta _ _ _ _ _ _ _ _ _ ge_compt Hw1 Hw2 HA Ha HI HM Hc) as Hb.
  split; [exact (eqtm_wf_l ge_typeof Hb) | | exact Hb].
  econstructor; [apply red_J_refl | constructor].
Qed.

End JAt.

End Id.
