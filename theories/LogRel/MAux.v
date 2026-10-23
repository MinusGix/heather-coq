(** * The relation at [M]: syntax in Kripke worlds, equivalent worlds,
      and the facts one side of [LRm] gives (M18b)

    What the laws of [MR] (irrelevance, symmetry, transitivity,
    weakening) share: [M]'s syntax commutes with a world, worlds that act
    alike on syntax ([kw_eqv]: the two associations of a composite, a
    world after the identity) relate alike, and [MSide] bundles what one
    [LRm] gives about its two signatures and its relations in every
    world, closed under moving to a world ([MSide_kw]). *)
From DeLaM.LogRel Require Export Escape.

Lemma gwa_tyM γ l l' li X A B C j :
  (tyM l l' li X A B C j)⟦γ⟧ = tyM l l' li X⟦γ⟧ A⟦γ⟧ B⟦γ⟧ C⟦γ⟧ j⟦γ⟧.
Proof. now destruct γ. Qed.
Lemma gwa_out γ l l' li X A B C j t :
  (tmOut l l' li X A B C j t)⟦γ⟧ = tmOut l l' li X⟦γ⟧ A⟦γ⟧ B⟦γ⟧ C⟦γ⟧ j⟦γ⟧ t⟦γ⟧.
Proof. now destruct γ. Qed.
Lemma gwa_corec γ l l' li X A B C k Y c j y :
  (tmCorec l l' li X A B C k Y c j y)⟦γ⟧ = tmCorec l l' li X⟦γ⟧ A⟦γ⟧ B⟦γ⟧ C⟦γ⟧ k Y⟦γ⟧ c⟦γ⟧ j⟦γ⟧ y⟦γ⟧.
Proof. now destruct γ. Qed.

Lemma gwa_mOutCorec γ l l' li X A B C k Y c j y :
  (mOutCorec l l' li X A B C k Y c j y)⟦γ⟧ = mOutCorec l l' li X⟦γ⟧ A⟦γ⟧ B⟦γ⟧ C⟦γ⟧ k Y⟦γ⟧ c⟦γ⟧ j⟦γ⟧ y⟦γ⟧.
Proof. destruct γ; cbn [gwa]; [reflexivity | apply gren_mOutCorec ..]. Qed.

Lemma gwa_lsingle3' (a b c : tm) γ : (lsingle3 a b c)⟦γ⟧ = lsingle3 a⟦γ⟧ b⟦γ⟧ c⟦γ⟧.
Proof. now destruct γ. Qed.

Lemma llk_llift_ext (d d' : lsub) : (forall n, llk d n = llk d' n) -> forall n, llk (llift d) n = llk (llift d') n.
Proof. intros H [|n]; rewrite !llk_llift; [reflexivity | now rewrite H]. Qed.

Lemma gwa_llift2 (d : lsub) γ n : llk (llift (llift d))⟦γ⟧ n = llk (llift (llift d⟦γ⟧)) n.
Proof. rewrite llk_llift_gwa. apply llk_llift_ext, llk_llift_gwa. Qed.

(** [out]'s type's substitutions, for [gl_push] *)
Lemma gwa_llift_single_ty (B : ty) a γ : B[llift (lsingle a)]⟦γ⟧ = B⟦γ⟧[llift (lsingle a⟦γ⟧)].
Proof. rewrite gwa_subst_ty. apply subst_ext_ty. intros n. now rewrite llk_llift_gwa, gwa_lsingle. Qed.
Lemma gwa_llift2_single (t : tm) a γ : t[llift (llift (lsingle a))]⟦γ⟧ = t⟦γ⟧[llift (llift (lsingle a⟦γ⟧))].
Proof. rewrite gwa_subst. apply subst_ext. intros n. now rewrite gwa_llift2, gwa_lsingle. Qed.

(** ** Renamings composed under binders *)

Lemma ren_wk_comp_lift2_ty (T : ty) (ρ ρ' : wk) :
  T⟨rlift (rlift ρ)⟩⟨rlift (rlift ρ')⟩ = T⟨rlift (rlift (wk_comp ρ' ρ))⟩.
Proof.
  apply ren_ren_ty; intros [|[|n]]; rewrite ?rlk_rlift; cbn; rewrite ?rlk_rlift; auto. now rewrite rlk_wk_comp.
Qed.
Lemma ren_wk_comp_lift3 (t : tm) (ρ ρ' : wk) :
  t⟨rlift (rlift (rlift ρ))⟩⟨rlift (rlift (rlift ρ'))⟩ = t⟨rlift (rlift (rlift (wk_comp ρ' ρ)))⟩.
Proof.
  apply ren_ren; intros [|[|[|n]]]; rewrite ?rlk_rlift; cbn; rewrite ?rlk_rlift; cbn; rewrite ?rlk_rlift; auto.
  now rewrite rlk_wk_comp.
Qed.
Lemma ren_wk_comp_lift2' (t : tm) (ρ ρ' : wk) :
  t⟨rlift (rlift ρ)⟩⟨rlift (rlift ρ')⟩ = t⟨rlift (rlift (wk_comp ρ' ρ))⟩.
Proof.
  apply ren_ren; intros [|[|n]]; rewrite ?rlk_rlift; cbn; rewrite ?rlk_rlift; auto. now rewrite rlk_wk_comp.
Qed.

(** ** Declaratively equal signatures (at any layer of [M]'s)

    [PresupM]'s [MEq] is symmetric and transitive; [out]'s annotations
    ([MAnn]) move along it. *)
Section MDecl.
Context {G : gctx} {i : layer} (Hi : typeof i = i) (Hv : i <> lV).

Lemma MEq_sym {Γ l l' li k k' ki X X' A A' B B' C C'} :
  MEq (G := G) (i := i) Γ l l' li k k' ki X X' A A' B B' C C' ->
  MEq (G := G) (i := i) Γ k k' ki l l' li X' X A' A B' B C' C.
Proof using Hi Hv.
  intros HE. pose proof (MEq_ids Hi Hv HE) as (Hid1 & Hid2 & Hid3).
  pose proof (MEq_sig_r Hi Hv HE) as (Hk & Hk' & Hki & HX' & HA' & HB' & HC').
  destruct HE as (Hlk & Hlk' & Hlik & (Hl & Hl' & Hli & HX & HA & HB & HC) & HXX & HAA & HBB & HCC & _).
  pose proof (lequiv_sym _ _ _ Hlk) as Hkl. pose proof (lequiv_sym _ _ _ Hlk') as Hkl'.
  pose proof (lequiv_sym _ _ _ Hlik) as Hkil.
  assert (EX3 : [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ⊢[ i ] X'⟨↑⟩⟨↑⟩⟨↑⟩ ≅ X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ])
    by (eapply wk3_eqty; [exact Hi | exact (ctx_of_wf_tm Hi HC) | exact (eqty_sym _ _ _ _ _ _ HXX)]).
  apply MEq_intro; try assumption.
  - eapply eqty_lconv; [apply eqty_sym, HXX | exact Hkil].
  - eapply eqty_lconv; [apply (M_mv_eqty Hi Hid1), eqty_sym, HAA | exact Hkl].
  - eapply eqty_lconv; [apply (M_mv_eqty Hi Hid2), eqty_sym, HBB | exact Hkl'].
  - eapply eqtm_lconv; [| exact Hkil]. apply (M_mv_eqtm Hi Hid3).
    eapply eqtm_conv; [apply eqtm_sym, HCC | rewrite Hi; exact EX3].
  - eapply wft_lconv; [exact HX | exact Hkil].
  - eapply wft_lconv; [exact (M_mv_ty Hi Hid1 HA) | exact Hkl].
  - eapply wft_lconv; [exact (M_mv_ty Hi Hid2 HB) | exact Hkl'].
  - eapply wf_lconv; [| exact Hkil]. apply (M_mv_tm Hi Hid3).
    eapply wf_conv; [exact HC | rewrite Hi; exact EX3].
Qed.

Lemma MEq_trans {Γ l l' li k k' ki m m' mi X1 X2 X3 A1 A2 A3 B1 B2 B3 C1 C2 C3} :
  MEq (G := G) (i := i) Γ l l' li k k' ki X1 X2 A1 A2 B1 B2 C1 C2 ->
  MEq (G := G) (i := i) Γ k k' ki m m' mi X2 X3 A2 A3 B2 B3 C2 C3 ->
  MEq (G := G) (i := i) Γ l l' li m m' mi X1 X3 A1 A3 B1 B3 C1 C3.
Proof using Hi Hv.
  intros H12 H23. pose proof (MEq_ids Hi Hv (MEq_sym H12)) as (Jid1 & Jid2 & Jid3).
  destruct H12 as (Hlk & Hlk' & Hlik & (Hl & Hl' & Hli & HX & HA & HB & HC) & HXX & HAA & HBB & HCC & _).
  destruct H23 as (Hkm & Hkm' & Hkim & _ & HXX' & HAA' & HBB' & HCC' & HX3 & HA3 & HB3 & HC3).
  pose proof (lequiv_sym _ _ _ Hlk) as Hkl. pose proof (lequiv_sym _ _ _ Hlk') as Hkl'.
  pose proof (lequiv_sym _ _ _ Hlik) as Hkil.
  assert (EX3 : [ G ; Γ ,, X1 @ li ,, A1 @ l ,, B1 @ l' ⊢[ i ] X1⟨↑⟩⟨↑⟩⟨↑⟩ ≅ X2⟨↑⟩⟨↑⟩⟨↑⟩ @ li ])
    by (eapply wk3_eqty; [exact Hi | exact (ctx_of_wf_tm Hi HC) | exact HXX]).
  apply MEq_intro; try assumption.
  - eapply lequiv_trans; eassumption.
  - eapply lequiv_trans; eassumption.
  - eapply lequiv_trans; eassumption.
  - eapply eqty_trans; [exact HXX | eapply eqty_lconv; [exact HXX' | exact Hlik]].
  - eapply eqty_trans; [exact HAA | eapply eqty_lconv; [exact (M_mv_eqty Hi Jid1 HAA') | exact Hlk]].
  - eapply eqty_trans; [exact HBB | eapply eqty_lconv; [exact (M_mv_eqty Hi Jid2 HBB') | exact Hlk']].
  - eapply eqtm_trans; [exact HCC |]. eapply eqtm_lconv; [| exact Hlik].
    eapply eqtm_conv; [exact (M_mv_eqtm Hi Jid3 HCC') | rewrite Hi; eapply eqty_lconv; [exact EX3 | exact Hkil]].
  - eapply wft_lconv; [exact HX3 | exact Hlik].
  - eapply wft_lconv; [exact (M_mv_ty Hi Jid1 HA3) | exact Hlk].
  - eapply wft_lconv; [exact (M_mv_ty Hi Jid2 HB3) | exact Hlk'].
  - eapply wf_lconv; [| exact Hlik].
    eapply wf_conv; [exact (M_mv_tm Hi Jid3 HC3) | rewrite Hi; eapply eqty_lconv; [exact EX3 | exact Hkil]].
Qed.

(** A signature at equivalent levels. *)
Lemma MSig_lconv {Γ l l' li k k' ki X A B C} :
  MSig (G := G) (i := i) Γ l l' li X A B C ->
  lequiv (gL G) l k -> lequiv (gL G) l' k' -> lequiv (gL G) li ki ->
  MSig (G := G) (i := i) Γ k k' ki X A B C.
Proof using Hi Hv.
  intros HS H1 H2 H3. pose proof HS as (Hl & Hl' & Hli & HX & HA & HB & HC).
  apply (MEq_sig_r Hi Hv (l := l) (l' := l') (li := li) (X := X) (A := A) (B := B) (C := C)).
  apply MEq_intro; first [assumption | now apply eqty_refl | now apply eqtm_refl].
Qed.

(** The contexts of two equal signatures are equivalent. *)
Lemma MEq_ctxeq {Γ l l' li k k' ki X X' A A' B B' C C'} :
  MEq (G := G) (i := i) Γ l l' li k k' ki X X' A A' B B' C C' ->
  [ G ⊢[ i ] Γ ,, X @ li ≅ Γ ,, X' @ ki ] /\
  [ G ⊢[ i ] Γ ,, X @ li ,, A @ l ≅ Γ ,, X' @ ki ,, A' @ k ] /\
  [ G ⊢[ i ] Γ ,, X @ li ,, A @ l ,, B @ l' ≅ Γ ,, X' @ ki ,, A' @ k ,, B' @ k' ].
Proof using Hi.
  intros (Hlk & Hlk' & Hlik & (Hl & Hl' & Hli & HX & HA & HB & HC) & HXX & HAA & HBB & _).
  pose proof (eqc_ext _ _ _ _ _ _ _ _ (eqc_refl _ _ _ (ctx_of_wf_ty Hi HX)) HX HXX Hlik) as H1.
  pose proof (eqc_ext _ _ _ _ _ _ _ _ H1 HA HAA Hlk) as H2.
  pose proof (eqc_ext _ _ _ _ _ _ _ _ H2 HB HBB Hlk') as H3.
  tauto.
Qed.

(** Two converted entries: the contexts are equivalent. *)
Lemma ctx2_conv {Γ A A' la la' B B' lb lb'} :
  [ G ; Γ ⊢[ i ] A ≅ A' @ la ] -> lequiv (gL G) la la' ->
  [ G ; Γ ,, A @ la ⊢[ i ] B ≅ B' @ lb ] -> lequiv (gL G) lb lb' ->
  [ G ⊢[ i ] Γ ,, A @ la ,, B @ lb ≅ Γ ,, A' @ la' ,, B' @ lb' ].
Proof using Hi.
  intros EA Hla EB Hlb.
  pose proof (eqty_wf_l Hi EA) as HA. pose proof (eqty_wf_l Hi EB) as HB.
  apply eqc_ext; [apply eqc_ext; [exact (eqc_refl _ _ _ (ctx_of_wf_ty Hi HA)) | exact HA | exact EA | exact Hla]
                 | exact HB | exact EB | exact Hlb].
Qed.

End MDecl.

Section MAux.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

Lemma ktyll_comp {G Γ} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) T :
  ktyll (kw_comp ρ ρ') T = ktyll ρ' (ktyll ρ T).
Proof. unfold ktyll; cbn. now rewrite gwa_ren_ty, gwa_comp_ty, ren_wk_comp_lift2_ty. Qed.
Lemma ktmll_comp' {G Γ} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) t :
  ktmll (kw_comp ρ ρ') t = ktmll ρ' (ktmll ρ t).
Proof. unfold ktmll; cbn. now rewrite gwa_ren, gwa_comp_tm, ren_wk_comp_lift2'. Qed.
Lemma ktmlll_comp {G Γ} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) t :
  ktmlll (kw_comp ρ ρ') t = ktmlll ρ' (ktmlll ρ t).
Proof. unfold ktmlll; cbn. now rewrite gwa_ren, gwa_comp_tm, ren_wk_comp_lift3. Qed.

(** ** [M]'s syntax in a world *)

Section KwM.
Context {G : gctx} {Γ : ctx} (ρ : kwk G Γ).

Lemma kty_tyM l l' li X A B C j :
  kty ρ (tyM l l' li X A B C j) = tyM l l' li (kty ρ X) (ktyl ρ A) (ktyll ρ B) (ktmlll ρ C) (ktm ρ j).
Proof. unfold kty, ktm, ktyl, ktyll, ktmlll; now rewrite gwa_tyM. Qed.
Lemma ktm_out l l' li X A B C j t :
  ktm ρ (tmOut l l' li X A B C j t) =
  tmOut l l' li (kty ρ X) (ktyl ρ A) (ktyll ρ B) (ktmlll ρ C) (ktm ρ j) (ktm ρ t).
Proof. unfold kty, ktm, ktyl, ktyll, ktmlll; now rewrite gwa_out. Qed.
Lemma ktm_corec l l' li X A B C k Y c j y :
  ktm ρ (tmCorec l l' li X A B C k Y c j y) =
  tmCorec l l' li (kty ρ X) (ktyl ρ A) (ktyll ρ B) (ktmlll ρ C) k (ktyl ρ Y) (ktmll ρ c) (ktm ρ j) (ktm ρ y).
Proof. unfold kty, ktm, ktyl, ktyll, ktmll, ktmlll; now rewrite gwa_corec. Qed.

(** Instances at an index, a shape and a position. *)
Lemma kty_lsingle (T : ty) a : kty ρ T[lsingle a] = (ktyl ρ T)[lsingle (ktm ρ a)].
Proof. unfold kty, ktyl, ktm. now rewrite gwa_subst_ty, gwa_lsingle, lsingle_ren_ty. Qed.

Lemma kty_lsingle2 (T : ty) a b : kty ρ T[lsingle2 a b] = (ktyll ρ T)[lsingle2 (ktm ρ a) (ktm ρ b)].
Proof. unfold kty, ktyll, ktm. now rewrite gwa_subst_ty, gwa_lsingle2, lsingle2_ren_ty. Qed.

Lemma ktm_lsingle3 (t : tm) a b c :
  ktm ρ t[lsingle3 a b c] = (ktmlll ρ t)[lsingle3 (ktm ρ a) (ktm ρ b) (ktm ρ c)].
Proof.
  unfold ktm, ktmlll. rewrite gwa_subst, gwa_lsingle3'. apply lsingle3_ren.
Qed.

Lemma ktyl_llift_single (T : ty) a : ktyl ρ T[llift (lsingle a)] = (ktyll ρ T)[llift (lsingle (ktm ρ a))].
Proof.
  unfold ktyl, ktyll, ktm. rewrite gwa_subst_ty.
  rewrite (subst_ext_ty _ (llift (lsingle a))⟦kw_γ ρ⟧ (llift (lsingle a)⟦kw_γ ρ⟧)) by apply llk_llift_gwa.
  rewrite gwa_lsingle, llift_lsingle_ren_ty. reflexivity.
Qed.

Lemma ktml_llift_single2 (t : tm) a b :
  ktml ρ t[llift (lsingle2 a b)] = (ktmlll ρ t)[llift (lsingle2 (ktm ρ a) (ktm ρ b))].
Proof.
  unfold ktml, ktmlll, ktm. rewrite gwa_subst.
  rewrite (subst_ext _ (llift (lsingle2 a b))⟦kw_γ ρ⟧ (llift (lsingle2 a b)⟦kw_γ ρ⟧)) by apply llk_llift_gwa.
  rewrite gwa_lsingle2, llift_lsingle2_ren. reflexivity.
Qed.

Lemma ktmll_llift2_single (t : tm) a :
  ktmll ρ t[llift (llift (lsingle a))] = (ktmlll ρ t)[llift (llift (lsingle (ktm ρ a)))].
Proof.
  unfold ktmll, ktmlll, ktm. rewrite gwa_subst.
  rewrite (subst_ext _ (llift (llift (lsingle a)))⟦kw_γ ρ⟧ (llift (llift (lsingle a⟦kw_γ ρ⟧))))
    by (intros n; rewrite gwa_llift2, gwa_lsingle; reflexivity).
  meq. all: now rewrite ?Nat.add_0_r.
Qed.

Lemma kw_mKid l l' li X A B C j :
  ktyll ρ (mKidTy l l' li X A B C j) =
  mKidTy l l' li (kty ρ X) (ktyl ρ A) (ktyll ρ B) (ktmlll ρ C) (ktm ρ j).
Proof.
  unfold ktyll, kty, ktyl, ktmlll, ktm. rewrite gwa_tyM, !gwa_ren_ty, !gwa_ren, gwa_subst.
  rewrite (subst_ext _ (llift (llift (lsingle j)))⟦kw_γ ρ⟧ (llift (llift (lsingle j⟦kw_γ ρ⟧))))
    by (intros n; rewrite gwa_llift2, gwa_lsingle; reflexivity).
  meq. all: now rewrite ?Nat.add_0_r.
Qed.

Lemma kw_B_single (T : ty) m a : (ktyl ρ T[llift (lsingle m)])[lsingle a] = (ktyll ρ T)[lsingle2 (ktm ρ m) a].
Proof.
  rewrite ktyl_llift_single. assert (N : nftm (ktm ρ m)) by (unfold ktm; apply ren_nf).
  revert N. generalize (ktm ρ m) (ktyll ρ T). intros x U N. meq.
Qed.

End KwM.

(** [out]'s child type at a shape. *)
Lemma mKid_single l l' li (X A B : ty) (C j a : tm) : nfty X -> nfty A -> nfty B -> nftm C -> nftm j ->
  (mKidTy l l' li X A B C j)[llift (lsingle a)] =
  tyM l l' li X⟨↑⟩ A⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩ C⟨rlift (rlift (rlift ↑))⟩ C[llift (lsingle2 j a)].
Proof. intros. meq. Qed.



(** ** Generically equal signatures *)

Definition MGeq G Γ l l' li (X A B : ty) (C : tm) k k' ki (X' A' B' : ty) (C' : tm) : Prop :=
  lequiv (gL G) l k /\ lequiv (gL G) l' k' /\ lequiv (gL G) li ki /\
  MSig (G := G) (i := ge_layer) Γ l l' li X A B C /\
  [ G ; Γ ⊢ X ≈ X' @ li ] /\ [ G ; Γ ,, X @ li ⊢ A ≈ A' @ l ] /\
  [ G ; Γ ,, X @ li ,, A @ l ⊢ B ≈ B' @ l' ] /\
  [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ⊢ C ≈ C' : X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ].

Lemma MEq_of_MGeq {G Γ l l' li X A B C k k' ki X' A' B' C'} :
  MGeq G Γ l l' li X A B C k k' ki X' A' B' C' ->
  MEq (G := G) (i := ge_layer) Γ l l' li k k' ki X X' A A' B B' C C'.
Proof using EL.
  intros (Hlk & Hlk' & Hlik & (Hl & Hl' & Hli & HX & HA & HB & HC) & HXX & HAA & HBB & HCC).
  apply geq_ty_sound in HXX, HAA, HBB. apply geq_tm_sound in HCC.
  apply MEq_intro; auto.
  - exact (eqty_wf_r ge_typeof HXX).
  - exact (eqty_wf_r ge_typeof HAA).
  - exact (eqty_wf_r ge_typeof HBB).
  - exact (eqtm_wf_r ge_typeof HCC).
Qed.

Lemma MGeq_M {G Γ l l' li X A B C k k' ki X' A' B' C' j j'} :
  MGeq G Γ l l' li X A B C k k' ki X' A' B' C' -> [ G ; Γ ⊢ j ≈ j' : X @ li ] ->
  [ G ; Γ ⊢ tyM l l' li X A B C j ≈ tyM k k' ki X' A' B' C' j' @ mlvl l l' li ].
Proof using EL.
  intros (Hlk & Hlk' & Hlik & (Hl & Hl' & Hli & HX & HA & HB & HC) & HXX & HAA & HBB & HCC) Hjj.
  now apply geq_ty_M.
Qed.

Lemma MGeq_wk1 {G Γ Y ly l l' li X A B C k k' ki X' A' B' C'} :
  MGeq G Γ l l' li X A B C k k' ki X' A' B' C' -> [ G ; Γ ,, Y @ ly ⊢g ] ->
  MGeq G (Γ ,, Y @ ly) l l' li X⟨↑⟩ A⟨rlift ↑⟩ B⟨rlift (rlift ↑)⟩ C⟨rlift (rlift (rlift ↑))⟩
    k k' ki X'⟨↑⟩ A'⟨rlift ↑⟩ B'⟨rlift (rlift ↑)⟩ C'⟨rlift (rlift (rlift ↑))⟩.
Proof using EL.
  intros (Hlk & Hlk' & Hlik & HS & HXX & HAA & HBB & HCC) HΓY.
  pose proof (MSig_wk1 ge_typeof ge_notV HS HΓY) as HS1.
  pose proof HS1 as (Hl & Hl' & Hli & HX1 & HA1 & HB1 & _).
  refine (conj Hlk (conj Hlk' (conj Hlik (conj HS1 _)))).
  assert (H1 : [ G ; Γ ,, Y @ ly ,, X⟨↑⟩ @ li ⊢g ]) by exact (ext_wf_g HX1 Hli).
  assert (H2 : [ G ; Γ ,, Y @ ly ,, X⟨↑⟩ @ li ,, A⟨rlift ↑⟩ @ l ⊢g ]) by exact (ext_wf_g HA1 Hl).
  assert (H3 : [ G ; Γ ,, Y @ ly ,, X⟨↑⟩ @ li ,, A⟨rlift ↑⟩ @ l ,, B⟨rlift (rlift ↑)⟩ @ l' ⊢g ])
    by exact (ext_wf_g HB1 Hl').
  repeat split.
  - exact (geq_ty_wk (wkr_shift1 _ _ _) HΓY HXX).
  - refine (geq_ty_wk _ H1 HAA). eapply wkr_up'; [apply wkr_shift1 | reflexivity].
  - refine (geq_ty_wk _ H2 HBB). eapply wkr_up'; [eapply wkr_up'; [apply wkr_shift1 | reflexivity] | reflexivity].
  - pose proof (geq_tm_wk (r := rlift (rlift (rlift ↑))) ltac:(eapply wkr_up'; [eapply wkr_up'; [eapply wkr_up';
        [apply wkr_shift1 | reflexivity] | reflexivity] | reflexivity]) H3 HCC) as X0.
    rewrite M_E_X3 in X0. exact X0.
Qed.

(** The other side's view: its signature first. *)
Lemma MGeq_flip {G Γ l l' li X A B C k k' ki X' A' B' C'} :
  MGeq G Γ l l' li X A B C k k' ki X' A' B' C' -> MGeq G Γ k k' ki X' A' B' C' l l' li X A B C.
Proof using EL.
  intros HG. pose proof (MEq_of_MGeq HG) as HE.
  pose proof (MEq_sig_r ge_typeof ge_notV HE) as HS'.
  destruct (MEq_ctxeq ge_typeof HE) as (Q1 & Q2 & Q3).
  destruct HG as (H1 & H2 & H3 & (W1 & W2 & Wi & HX & HA & HB & HC) & HXX & HAA & HBB & HCC).
  pose proof (lequiv_sym _ _ _ H1) as H1'. pose proof (lequiv_sym _ _ _ H2) as H2'.
  pose proof (lequiv_sym _ _ _ H3) as H3'.
  assert (EX3 : [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ⊢g X⟨↑⟩⟨↑⟩⟨↑⟩ ≅ X'⟨↑⟩⟨↑⟩⟨↑⟩ @ li ])
    by (eapply wk3_eqty; [exact ge_typeof | exact (ctx_of_wf_tm ge_typeof HC) | exact (geq_ty_sound HXX)]).
  refine (conj H1' (conj H2' (conj H3' (conj HS' (conj _ (conj _ (conj _ _))))))).
  - exact (geq_ty_lconv (geq_ty_sym HXX) H3').
  - exact (geq_ty_ctxeq Q1 (geq_ty_lconv (geq_ty_sym HAA) H1')).
  - exact (geq_ty_ctxeq Q2 (geq_ty_lconv (geq_ty_sym HBB) H2')).
  - exact (geq_tm_ctxeq Q3 (geq_tm_lconv (geq_tm_conv (geq_tm_sym HCC) EX3) H3')).
Qed.

(** Composed: the second's equalities moved to the first's contexts and
    levels. *)
Lemma MGeq_trans {G Γ l l' li X A B C k k' ki X' A' B' C' r r' ri X'' A'' B'' C''} :
  MGeq G Γ l l' li X A B C k k' ki X' A' B' C' -> MGeq G Γ k k' ki X' A' B' C' r r' ri X'' A'' B'' C'' ->
  MGeq G Γ l l' li X A B C r r' ri X'' A'' B'' C''.
Proof using EL.
  intros H12 H23. pose proof (MEq_sym ge_typeof ge_notV (MEq_of_MGeq H12)) as HE.
  destruct (MEq_ctxeq ge_typeof HE) as (Q1 & Q2 & Q3).
  destruct H12 as (H1 & H2 & H3 & HS & HXX & HAA & HBB & HCC).
  pose proof HS as (W1 & W2 & Wi & HX & HA & HB & HC).
  destruct H23 as (K1 & K2 & K3 & _ & GXX & GAA & GBB & GCC).
  assert (EX3 : [ G ; Γ ,, X @ li ,, A @ l ,, B @ l' ⊢g X'⟨↑⟩⟨↑⟩⟨↑⟩ ≅ X⟨↑⟩⟨↑⟩⟨↑⟩ @ li ])
    by (eapply wk3_eqty; [exact ge_typeof | exact (ctx_of_wf_tm ge_typeof HC)
                         | exact (eqty_sym _ _ _ _ _ _ (geq_ty_sound HXX))]).
  refine (conj (lequiv_trans _ _ _ _ H1 K1) (conj (lequiv_trans _ _ _ _ H2 K2)
            (conj (lequiv_trans _ _ _ _ H3 K3) (conj HS (conj _ (conj _ (conj _ _))))))).
  - exact (geq_ty_trans HXX (geq_ty_lconv GXX H3)).
  - exact (geq_ty_trans HAA (geq_ty_ctxeq Q1 (geq_ty_lconv GAA H1))).
  - exact (geq_ty_trans HBB (geq_ty_ctxeq Q2 (geq_ty_lconv GBB H2))).
  - exact (geq_tm_trans HCC (geq_tm_conv (geq_tm_ctxeq Q3 (geq_tm_lconv GCC H3)) EX3)).
Qed.

(** ** [out]'s annotations along equal signatures *)

Lemma MEq_of_MAnn {G Γ l l' li X A B C j k k' ki X1 A1 B1 C1 j1} :
  MSig (G := G) (i := ge_layer) Γ l l' li X A B C ->
  MAnn G Γ l l' li X A B C j k k' ki X1 A1 B1 C1 j1 ->
  MEq (G := G) (i := ge_layer) Γ l l' li k k' ki X X1 A A1 B B1 C C1.
Proof using.
  intros (Hl & Hl' & Hli & HX & HA & HB & HC) (Hk & Hk' & Hki & HXX & HAA & HBB & HCC & _).
  apply MEq_intro; auto using lequiv_sym.
  - exact (eqty_wf_r ge_typeof HXX).
  - exact (eqty_wf_r ge_typeof HAA).
  - exact (eqty_wf_r ge_typeof HBB).
  - exact (eqtm_wf_r ge_typeof HCC).
Qed.

Lemma MAnn_conv {G Γ l l' li X A B C j r r' ri X' A' B' C' j' k k' ki X1 A1 B1 C1 j1} :
  MEq (G := G) (i := ge_layer) Γ l l' li r r' ri X X' A A' B B' C C' ->
  [ G ; Γ ⊢g j ≅ j' : X @ li ] ->
  MAnn G Γ r r' ri X' A' B' C' j' k k' ki X1 A1 B1 C1 j1 ->
  MAnn G Γ l l' li X A B C j k k' ki X1 A1 B1 C1 j1.
Proof using.
  intros HE Hjj HA. pose proof (MEq_sig_r ge_typeof ge_notV HE) as HS'.
  pose proof (MEq_trans ge_typeof ge_notV HE (MEq_of_MAnn HS' HA)) as (Hk & Hk' & Hki & _ & E1 & E2 & E3 & E4 & _).
  destruct HE as (Hlr & Hlr' & Hlri & _ & HXX & _).
  destruct HA as (_ & _ & _ & _ & _ & _ & _ & Hj1).
  refine (conj (lequiv_sym _ _ _ Hk) (conj (lequiv_sym _ _ _ Hk') (conj (lequiv_sym _ _ _ Hki)
            (conj E1 (conj E2 (conj E3 (conj E4 _))))))).
  eapply eqtm_trans; [exact Hjj |]. eapply eqtm_lconv; [| exact Hlri].
  eapply eqtm_conv; [exact Hj1 | rewrite ge_typeof; eapply eqty_lconv; [exact HXX | apply lequiv_sym, Hlri]].
Qed.

(** ** Typing under the signature's binders, in a world *)

Section KwBinders.
Context {G : gctx} {Γ : ctx} (ρ : kwk G Γ).
Local Notation Hγ := (kw_gok ρ).
Local Notation HG' := (kw_glob ρ).

Lemma kw_wkr_l2 {A B l l'} :
  wkr (rlift (rlift (kw_r ρ))) (kw_Δ ρ ,, kty ρ A @ l ,, ktyl ρ B @ l') ((Γ ,, A @ l ,, B @ l')⟦kw_γ ρ⟧).
Proof.
  pose proof (kw_wkr_l ρ (A := A) (l := l)) as W. rewrite gwa_cext in W.
  rewrite !gwa_cext. eapply wkr_up'; [exact W | reflexivity].
Qed.
Lemma kw_wkr_l3 {A B C l l' l''} :
  wkr (rlift (rlift (rlift (kw_r ρ))))
    (kw_Δ ρ ,, kty ρ A @ l ,, ktyl ρ B @ l' ,, ktyll ρ C @ l'') ((Γ ,, A @ l ,, B @ l' ,, C @ l'')⟦kw_γ ρ⟧).
Proof.
  pose proof (kw_wkr_l2 (A := A) (B := B) (l := l) (l' := l')) as W. rewrite !gwa_cext in W.
  rewrite !gwa_cext. eapply wkr_up'; [exact W | reflexivity].
Qed.

Lemma kw_ext_l2 {A B l l'} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l -> [ G ; Γ ,, A @ l ⊢g B @ l' ] -> lwf (gL G) l' ->
  [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ,, ktyl ρ B @ l' ⊢g ].
Proof. intros HA Hl HB Hl'. apply ext_wf_g; [exact (kw_ty_l ρ HA Hl HB) | exact (kw_lwf ρ Hl')]. Qed.

Lemma kw_ty_l2 {A B l l' T l''} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l -> [ G ; Γ ,, A @ l ⊢g B @ l' ] -> lwf (gL G) l' ->
  [ G ; Γ ,, A @ l ,, B @ l' ⊢g T @ l'' ] -> [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ,, ktyl ρ B @ l' ⊢g ktyll ρ T @ l'' ].
Proof. intros HA Hl HB Hl' H. exact (wf_ty_wkr kw_wkr_l2 (kw_ext_l2 HA Hl HB Hl') (gwa_ty Hγ HG' H)). Qed.
Lemma kw_geq_ty_l2 {A B l l' T T' l''} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l -> [ G ; Γ ,, A @ l ⊢g B @ l' ] ->
  lwf (gL G) l' -> [ G ; Γ ,, A @ l ,, B @ l' ⊢ T ≈ T' @ l'' ] ->
  [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ,, ktyl ρ B @ l' ⊢ ktyll ρ T ≈ ktyll ρ T' @ l'' ].
Proof. intros HA Hl HB Hl' H. exact (geq_ty_wk kw_wkr_l2 (kw_ext_l2 HA Hl HB Hl') (geq_ty_gwa Hγ HG' H)). Qed.

Lemma kw_ext_l3 {A B C l l' l''} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l -> [ G ; Γ ,, A @ l ⊢g B @ l' ] -> lwf (gL G) l' ->
  [ G ; Γ ,, A @ l ,, B @ l' ⊢g C @ l'' ] -> lwf (gL G) l'' ->
  [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ,, ktyl ρ B @ l' ,, ktyll ρ C @ l'' ⊢g ].
Proof. intros HA Hl HB Hl' HC Hl''. apply ext_wf_g; [exact (kw_ty_l2 HA Hl HB Hl' HC) | exact (kw_lwf ρ Hl'')]. Qed.

Lemma kty_shift3 (T : ty) : T⟨↑⟩⟨↑⟩⟨↑⟩⟦kw_γ ρ⟧⟨rlift (rlift (rlift (kw_r ρ)))⟩ = (kty ρ T)⟨↑⟩⟨↑⟩⟨↑⟩.
Proof. unfold kty. rewrite !gwa_ren_ty, !shift_lift_ty. reflexivity. Qed.
Lemma kty_shift2 (T : ty) : T⟨↑⟩⟨↑⟩⟦kw_γ ρ⟧⟨rlift (rlift (kw_r ρ))⟩ = (kty ρ T)⟨↑⟩⟨↑⟩.
Proof. unfold kty. now rewrite !gwa_ren_ty, !shift_lift_ty. Qed.

Lemma kw_tm_l3 {A B C l l' l'' t T} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l -> [ G ; Γ ,, A @ l ⊢g B @ l' ] ->
  lwf (gL G) l' -> [ G ; Γ ,, A @ l ,, B @ l' ⊢g C @ l'' ] -> lwf (gL G) l'' ->
  [ G ; Γ ,, A @ l ,, B @ l' ,, C @ l'' ⊢g t : T⟨↑⟩⟨↑⟩⟨↑⟩ @ l ] ->
  [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ,, ktyl ρ B @ l' ,, ktyll ρ C @ l'' ⊢g ktmlll ρ t : (kty ρ T)⟨↑⟩⟨↑⟩⟨↑⟩ @ l ].
Proof.
  intros HA Hl HB Hl' HC Hl'' H. rewrite <- kty_shift3.
  exact (wf_tm_wkr kw_wkr_l3 (kw_ext_l3 HA Hl HB Hl' HC Hl'') (gwa_tm Hγ HG' H)).
Qed.
Lemma kw_geq_tm_l3 {A B C l l' l'' t t' T} : [ G ; Γ ⊢g A @ l ] -> lwf (gL G) l -> [ G ; Γ ,, A @ l ⊢g B @ l' ] ->
  lwf (gL G) l' -> [ G ; Γ ,, A @ l ,, B @ l' ⊢g C @ l'' ] -> lwf (gL G) l'' ->
  [ G ; Γ ,, A @ l ,, B @ l' ,, C @ l'' ⊢ t ≈ t' : T⟨↑⟩⟨↑⟩⟨↑⟩ @ l ] ->
  [ kw_G ρ ; kw_Δ ρ ,, kty ρ A @ l ,, ktyl ρ B @ l' ,, ktyll ρ C @ l''
      ⊢ ktmlll ρ t ≈ ktmlll ρ t' : (kty ρ T)⟨↑⟩⟨↑⟩⟨↑⟩ @ l ].
Proof.
  intros HA Hl HB Hl' HC Hl'' H. rewrite <- kty_shift3.
  exact (geq_tm_wk kw_wkr_l3 (kw_ext_l3 HA Hl HB Hl' HC Hl'') (geq_tm_gwa Hγ HG' H)).
Qed.

End KwBinders.

(** ** Worlds acting alike on syntax

    The two associations of a composite world, and a world after the
    identity, are not equal ([kw_comp] composes proofs), but act alike;
    the relations of [LRm] at such worlds agree by irrelevance. *)
Definition kw_eqv {G Γ} (ρ1 ρ2 : kwk G Γ) : Prop :=
  kw_G ρ1 = kw_G ρ2 /\ kw_Δ ρ1 = kw_Δ ρ2 /\
  (forall T : ty, T⟦kw_γ ρ1⟧ = T⟦kw_γ ρ2⟧) /\ (forall t : tm, t⟦kw_γ ρ1⟧ = t⟦kw_γ ρ2⟧) /\
  (forall k, rlk (kw_r ρ1) k = rlk (kw_r ρ2) k).

Lemma kw_eqv_sym {G Γ} {ρ1 ρ2 : kwk G Γ} : kw_eqv ρ1 ρ2 -> kw_eqv ρ2 ρ1.
Proof. intros (E1 & E2 & E3 & E4 & E5). repeat split; intros; symmetry; auto. Qed.

Lemma kw_eqv_assoc {G Γ} (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) (ρ'' : kwk (kw_G ρ') (kw_Δ ρ')) :
  kw_eqv (kw_comp (kw_comp ρ ρ') ρ'') (kw_comp ρ (kw_comp ρ' ρ'')).
Proof.
  repeat split; cbn [kw_γ kw_r kw_comp]; intros.
  - now rewrite <- !gwa_comp_ty.
  - now rewrite <- !gwa_comp_tm.
  - now rewrite !rlk_wk_comp.
Qed.

Lemma kw_eqv_comp_l {G Γ} (ρ : kwk G Γ) {ρ1 ρ2 : kwk (kw_G ρ) (kw_Δ ρ)} :
  kw_eqv ρ1 ρ2 -> kw_eqv (kw_comp ρ ρ1) (kw_comp ρ ρ2).
Proof.
  intros (E1 & E2 & E3 & E4 & E5). refine (conj E1 (conj E2 _)). cbn [kw_γ kw_r kw_comp].
  repeat split; intros.
  - now rewrite <- !gwa_comp_ty.
  - now rewrite <- !gwa_comp_tm.
  - now rewrite !rlk_wk_comp, E5.
Qed.

Lemma kw_eqv_self {G Γ} (HΓ : [ G ; Γ ⊢g ]) (ρ : kwk G Γ) : kw_eqv (kw_comp (kw_self HΓ) ρ) ρ.
Proof.
  repeat split; cbn [kw_γ kw_r kw_comp kw_self kw_loc]; intros.
  - now rewrite gwk_comp_id_r.
  - now rewrite gwk_comp_id_r.
  - rewrite rlk_wk_comp. cbn [wk_ren]. now rewrite rlk_shift0.
Qed.

Section KwEqv.
Context {G Γ} {ρ1 ρ2 : kwk G Γ} (Hρ : kw_eqv ρ1 ρ2).

Lemma rlk_lift_eqv r r' : (forall k, rlk r k = rlk r' k) -> forall k, rlk (rlift r) k = rlk (rlift r') k.
Proof. intros H [|k]; rewrite !rlk_rlift; [reflexivity | now rewrite H]. Qed.

Lemma kty_eqv T : kty ρ1 T = kty ρ2 T.
Proof. destruct Hρ as (_ & _ & E3 & _ & E5). unfold kty. rewrite E3. now apply ren_ext_ty. Qed.
Lemma ktm_eqv t : ktm ρ1 t = ktm ρ2 t.
Proof. destruct Hρ as (_ & _ & _ & E4 & E5). unfold ktm. rewrite E4. now apply ren_ext_tm. Qed.
Lemma ktyl_eqv T : ktyl ρ1 T = ktyl ρ2 T.
Proof. destruct Hρ as (_ & _ & E3 & _ & E5). unfold ktyl. rewrite E3. now apply ren_ext_ty, rlk_lift_eqv. Qed.
Lemma ktml_eqv t : ktml ρ1 t = ktml ρ2 t.
Proof. destruct Hρ as (_ & _ & _ & E4 & E5). unfold ktml. rewrite E4. now apply ren_ext_tm, rlk_lift_eqv. Qed.
Lemma ktyll_eqv T : ktyll ρ1 T = ktyll ρ2 T.
Proof.
  destruct Hρ as (_ & _ & E3 & _ & E5). unfold ktyll. rewrite E3. now apply ren_ext_ty, rlk_lift_eqv, rlk_lift_eqv.
Qed.
Lemma ktmll_eqv t : ktmll ρ1 t = ktmll ρ2 t.
Proof.
  destruct Hρ as (_ & _ & _ & E4 & E5). unfold ktmll. rewrite E4. now apply ren_ext_tm, rlk_lift_eqv, rlk_lift_eqv.
Qed.
Lemma ktmlll_eqv t : ktmlll ρ1 t = ktmlll ρ2 t.
Proof.
  destruct Hρ as (_ & _ & _ & E4 & E5). unfold ktmlll. rewrite E4.
  now apply ren_ext_tm, rlk_lift_eqv, rlk_lift_eqv, rlk_lift_eqv.
Qed.

End KwEqv.

(** The identity world on the signature's components. *)
Lemma ktyl_self {G Γ} (HΓ : [ G ; Γ ⊢g ]) T : nfty T -> ktyl (kw_self HΓ) T = T.
Proof.
  intros H. unfold ktyl, kw_self, kw_loc; cbn [kw_γ kw_r gwa wk_ren].
  rewrite <- (ren_id_ty T H) at 2. apply ren_ext_ty. intros [|n]; rlk_simpl; cbn; lia.
Qed.
Lemma ktyll_self {G Γ} (HΓ : [ G ; Γ ⊢g ]) T : nfty T -> ktyll (kw_self HΓ) T = T.
Proof.
  intros H. unfold ktyll, kw_self, kw_loc; cbn [kw_γ kw_r gwa wk_ren].
  rewrite <- (ren_id_ty T H) at 2. apply ren_ext_ty. intros [|[|n]]; rlk_simpl; cbn; lia.
Qed.
Lemma ktmlll_self {G Γ} (HΓ : [ G ; Γ ⊢g ]) t : nftm t -> ktmlll (kw_self HΓ) t = t.
Proof.
  intros H. unfold ktmlll, kw_self, kw_loc; cbn [kw_γ kw_r gwa wk_ren].
  rewrite <- (ren_id_tm t H) at 2. apply ren_ext_tm. intros [|[|[|n]]]; rlk_simpl; cbn; lia.
Qed.

(** ** One side of [LRm]

    What an [LRm] derivation gives about its two signatures and its three
    relations, with the [LR] premises replaced by their escapes and the
    relations' agreement at worlds acting alike ([kw_eqv]) added, which
    irrelevance provides. *)
End MAux.

Record MSide `{E : GenericEq} (G : gctx) (Γ : ctx) (l1 l2 li : lvl) (X A B : ty) (C : tm)
    (r1 r2 ri : lvl) (X' A' B' : ty) (C' : tm)
    (idxR : DomRel G Γ) (shR : MShRel G Γ) (posR : MPosRel G Γ) : Prop := {
  ms_geq : MGeq G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' ;
  ms_eI : forall (ρ : kwk G Γ) x x', idxR ρ x x' -> [ kw_G ρ ; kw_Δ ρ ⊢ x ≈ x' : kty ρ X @ li ] ;
  ms_gA : forall (ρ : kwk G Γ) x x', idxR ρ x x' ->
    [ kw_G ρ ; kw_Δ ρ ⊢ (ktyl ρ A)[lsingle x] ≈ (ktyl ρ A')[lsingle x'] @ l1 ] ;
  ms_eS : forall (ρ : kwk G Γ) x x' a a', idxR ρ x x' -> shR ρ x x' a a' ->
    [ kw_G ρ ; kw_Δ ρ ⊢ a ≈ a' : (ktyl ρ A)[lsingle x] @ l1 ] ;
  ms_gBa : forall (ρ : kwk G Γ) x x' a a', idxR ρ x x' -> shR ρ x x' a a' ->
    [ kw_G ρ ; kw_Δ ρ ⊢ (ktyll ρ B)[lsingle2 x a] ≈ (ktyll ρ B')[lsingle2 x' a'] @ l2 ] ;
  ms_eP : forall (ρ : kwk G Γ) x x' a a' p p', idxR ρ x x' -> shR ρ x x' a a' -> posR ρ x x' a a' p p' ->
    [ kw_G ρ ; kw_Δ ρ ⊢ p ≈ p' : (ktyll ρ B)[lsingle2 x a] @ l2 ] ;
  ms_ch : forall (ρ : kwk G Γ) x x' a a' p p', idxR ρ x x' -> shR ρ x x' a a' -> posR ρ x x' a a' p p' ->
    idxR ρ (ktmlll ρ C)[lsingle3 x a p] (ktmlll ρ C')[lsingle3 x' a' p'] ;
  ms_gB : forall (ρ : kwk G Γ) x x', idxR ρ x x' ->
    [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ A)[lsingle x] @ l1
        ⊢ (ktyll ρ B)[llift (lsingle x)] ≈ (ktyll ρ B')[llift (lsingle x')] @ l2 ] ;
  ms_gC : forall (ρ : kwk G Γ) x x', idxR ρ x x' ->
    [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ A)[lsingle x] @ l1 ,, (ktyll ρ B)[llift (lsingle x)] @ l2
        ⊢ (ktmlll ρ C)[llift (llift (lsingle x))] ≈ (ktmlll ρ C')[llift (llift (lsingle x'))]
        : (kty ρ X)⟨↑⟩⟨↑⟩ @ li ] ;
  ms_gCa : forall (ρ : kwk G Γ) x x' a a', idxR ρ x x' -> shR ρ x x' a a' ->
    [ kw_G ρ ; kw_Δ ρ ,, (ktyll ρ B)[lsingle2 x a] @ l2
        ⊢ (ktmlll ρ C)[llift (lsingle2 x a)] ≈ (ktmlll ρ C')[llift (lsingle2 x' a')] : (kty ρ X)⟨↑⟩ @ li ] ;
  ms_imon : forall (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) x x', idxR ρ x x' ->
    idxR (kw_comp ρ ρ') (ktm ρ' x) (ktm ρ' x') ;
  ms_shmon : forall (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) x x' a a', idxR ρ x x' -> shR ρ x x' a a' ->
    shR (kw_comp ρ ρ') (ktm ρ' x) (ktm ρ' x') (ktm ρ' a) (ktm ρ' a') ;
  ms_posmon : forall (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) x x' a a' p p', idxR ρ x x' -> shR ρ x x' a a' ->
    posR ρ x x' a a' p p' ->
    posR (kw_comp ρ ρ') (ktm ρ' x) (ktm ρ' x') (ktm ρ' a) (ktm ρ' a') (ktm ρ' p) (ktm ρ' p') ;
  ms_iinv : forall ρ1 ρ2 : kwk G Γ, kw_eqv ρ1 ρ2 -> forall x x', idxR ρ1 x x' -> idxR ρ2 x x' ;
  ms_shinv : forall ρ1 ρ2 : kwk G Γ, kw_eqv ρ1 ρ2 -> forall x x' a a', idxR ρ1 x x' ->
    shR ρ1 x x' a a' -> shR ρ2 x x' a a' ;
  ms_posinv : forall ρ1 ρ2 : kwk G Γ, kw_eqv ρ1 ρ2 -> forall x x' a a' p p', idxR ρ1 x x' ->
    shR ρ1 x x' a a' -> posR ρ1 x x' a a' p p' -> posR ρ2 x x' a a' p p'
}.

Arguments ms_geq {E G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR}.
Arguments ms_eI {E G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR}.
Arguments ms_gA {E G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR}.
Arguments ms_eS {E G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR}.
Arguments ms_gBa {E G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR}.
Arguments ms_eP {E G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR}.
Arguments ms_ch {E G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR}.
Arguments ms_gB {E G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR}.
Arguments ms_gC {E G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR}.
Arguments ms_gCa {E G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR}.
Arguments ms_imon {E G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR}.
Arguments ms_shmon {E G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR}.
Arguments ms_posmon {E G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR}.
Arguments ms_iinv {E G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR}.
Arguments ms_shinv {E G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR}.
Arguments ms_posinv {E G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR}.

Section MAuxSide.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

(** In a world, along the relations at the composite worlds. *)
Lemma MGeq_kw {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C'} (ρ : kwk G Γ) :
  MGeq G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' ->
  MGeq (kw_G ρ) (kw_Δ ρ) l1 l2 li (kty ρ X) (ktyl ρ A) (ktyll ρ B) (ktmlll ρ C)
    r1 r2 ri (kty ρ X') (ktyl ρ A') (ktyll ρ B') (ktmlll ρ C').
Proof using EL.
  intros (Hl1 & Hl2 & Hli & (W1 & W2 & Wi & HX & HA & HB & HC) & HXX & HAA & HBB & HCC).
  refine (conj (kw_lequiv ρ Hl1) (conj (kw_lequiv ρ Hl2) (conj (kw_lequiv ρ Hli) _))).
  refine (conj (conj (kw_lwf ρ W1) (conj (kw_lwf ρ W2) (conj (kw_lwf ρ Wi)
            (conj (kw_ty ρ HX) (conj (kw_ty_l ρ HX Wi HA) (conj (kw_ty_l2 ρ HX Wi HA W1 HB)
               (kw_tm_l3 ρ HX Wi HA W1 HB W2 HC)))))))
            (conj (kw_geq_ty ρ HXX) (conj (kw_geq_ty_l ρ HX Wi HAA)
              (conj (kw_geq_ty_l2 ρ HX Wi HA W1 HBB) (kw_geq_tm_l3 ρ HX Wi HA W1 HB W2 HCC))))).
Qed.

Lemma MSide_kw {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR} (ρ : kwk G Γ) :
  MSide G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR ->
  MSide (kw_G ρ) (kw_Δ ρ) l1 l2 li (kty ρ X) (ktyl ρ A) (ktyll ρ B) (ktmlll ρ C)
    r1 r2 ri (kty ρ X') (ktyl ρ A') (ktyll ρ B') (ktmlll ρ C')
    (fun ρ' => idxR (kw_comp ρ ρ')) (fun ρ' => shR (kw_comp ρ ρ')) (fun ρ' => posR (kw_comp ρ ρ')).
Proof using EL.
  intros [HG eI gA eS gBa eP ch gB gC gCa imon shmon posmon iinv shinv posinv].
  split; cbn beta.
  - exact (MGeq_kw ρ HG).
  - intros ρ' x x' h. rewrite <- kty_comp. exact (eI _ x x' h).
  - intros ρ' x x' h. rewrite <- !ktyl_comp. exact (gA _ x x' h).
  - intros ρ' x x' a a' h ha. rewrite <- ktyl_comp. exact (eS _ x x' a a' h ha).
  - intros ρ' x x' a a' h ha. rewrite <- !ktyll_comp. exact (gBa _ x x' a a' h ha).
  - intros ρ' x x' a a' p p' h ha hp. rewrite <- ktyll_comp. exact (eP _ x x' a a' p p' h ha hp).
  - intros ρ' x x' a a' p p' h ha hp. rewrite <- !ktmlll_comp. exact (ch _ x x' a a' p p' h ha hp).
  - intros ρ' x x' h. rewrite <- ktyl_comp, <- !ktyll_comp. exact (gB _ x x' h).
  - intros ρ' x x' h. rewrite <- ktyl_comp, <- ktyll_comp, <- !ktmlll_comp, <- kty_comp. exact (gC _ x x' h).
  - intros ρ' x x' a a' h ha. rewrite <- ktyll_comp, <- !ktmlll_comp, <- kty_comp. exact (gCa _ x x' a a' h ha).
  - intros ρ' ρ'' x x' h. exact (iinv _ _ (kw_eqv_assoc ρ ρ' ρ'') _ _ (imon (kw_comp ρ ρ') ρ'' x x' h)).
  - intros ρ' ρ'' x x' a a' h ha.
    exact (shinv _ _ (kw_eqv_assoc ρ ρ' ρ'') _ _ _ _ (imon (kw_comp ρ ρ') ρ'' x x' h) (shmon (kw_comp ρ ρ') ρ'' x x' a a' h ha)).
  - intros ρ' ρ'' x x' a a' p p' h ha hp.
    exact (posinv _ _ (kw_eqv_assoc ρ ρ' ρ'') _ _ _ _ _ _ (imon (kw_comp ρ ρ') ρ'' x x' h) (shmon (kw_comp ρ ρ') ρ'' x x' a a' h ha)
             (posmon (kw_comp ρ ρ') ρ'' x x' a a' p p' h ha hp)).
  - intros ρ1 ρ2 Eρ. exact (iinv _ _ (kw_eqv_comp_l ρ Eρ)).
  - intros ρ1 ρ2 Eρ. exact (shinv _ _ (kw_eqv_comp_l ρ Eρ)).
  - intros ρ1 ρ2 Eρ. exact (posinv _ _ (kw_eqv_comp_l ρ Eρ)).
Qed.

(** ** At the context itself: the index, the shapes' type, the positions'
    type and the child index, at the index *)

Lemma MGeq_nf {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C'} :
  MGeq G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' ->
  nfty X /\ nfty A /\ nfty B /\ nftm C /\ nfty X' /\ nfty A' /\ nfty B' /\ nftm C'.
Proof using EL.
  intros HG. pose proof (MEq_of_MGeq HG) as (_ & _ & _ & HS & _ & _ & _ & _ & HX' & HA' & HB' & HC').
  destruct (MSig_nf HS) as (N1 & N2 & N3 & N4).
  repeat split; auto; first [exact (wf_ty_nf HX') | exact (wf_ty_nf HA') | exact (wf_ty_nf HB') | exact (wf_tm_nf HC')].
Qed.

Lemma MGeq_ctx {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C'} :
  MGeq G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' -> [ G ; Γ ⊢g ].
Proof using. intros (_ & _ & _ & (_ & _ & _ & HX & _) & _). exact (ctx_of_ty HX). Qed.

Lemma MSide_root {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR m m'} :
  MSide G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR -> nftm m -> nftm m' ->
  (forall ρ : kwk G Γ, idxR ρ (ktm ρ m) (ktm ρ m')) ->
  [ G ; Γ ⊢ m ≈ m' : X @ li ] /\
  [ G ; Γ ⊢ A[lsingle m] ≈ A'[lsingle m'] @ l1 ] /\
  [ G ; Γ ,, A[lsingle m] @ l1 ⊢ B[llift (lsingle m)] ≈ B'[llift (lsingle m')] @ l2 ] /\
  [ G ; Γ ,, A[lsingle m] @ l1 ,, B[llift (lsingle m)] @ l2
      ⊢ C[llift (llift (lsingle m))] ≈ C'[llift (llift (lsingle m'))] : X⟨↑⟩⟨↑⟩ @ li ].
Proof using EL.
  intros HM Nm Nm' Hix. pose proof (MGeq_ctx (ms_geq HM)) as HΓ.
  destruct (MGeq_nf (ms_geq HM)) as (NX & NA & NB & NC & NX' & NA' & NB' & NC').
  pose proof (Hix (kw_self HΓ)) as h. rewrite !ktm_self in h by assumption.
  pose proof (ms_eI HM _ _ _ h) as E1. pose proof (ms_gA HM _ _ _ h) as E2.
  pose proof (ms_gB HM _ _ _ h) as E3. pose proof (ms_gC HM _ _ _ h) as E4.
  rewrite (kty_self HΓ X NX) in E1, E4.
  rewrite (ktyl_self HΓ A NA) in E2, E3, E4. rewrite (ktyl_self HΓ A' NA') in E2.
  rewrite (ktyll_self HΓ B NB) in E3, E4. rewrite (ktyll_self HΓ B' NB') in E3.
  rewrite (ktmlll_self HΓ C NC), (ktmlll_self HΓ C' NC') in E4.
  exact (conj E1 (conj E2 (conj E3 E4))).
Qed.

(** [out]'s type's second component, along generically equal signatures
    and their instances at the index. *)
Lemma M_outB_geq {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' m m'} :
  MGeq G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' ->
  [ G ; Γ ,, A[lsingle m] @ l1 ⊢ B[llift (lsingle m)] ≈ B'[llift (lsingle m')] @ l2 ] ->
  [ G ; Γ ,, A[lsingle m] @ l1 ,, B[llift (lsingle m)] @ l2
      ⊢ C[llift (llift (lsingle m))] ≈ C'[llift (llift (lsingle m'))] : X⟨↑⟩⟨↑⟩ @ li ] ->
  [ G ; Γ ,, A[lsingle m] @ l1 ⊢ tyPi l2 (mlvl l1 l2 li) B[llift (lsingle m)] (mKidTy l1 l2 li X A B C m)
      ≈ tyPi r2 (mlvl r1 r2 ri) B'[llift (lsingle m')] (mKidTy r1 r2 ri X' A' B' C' m') @ mlvl l1 l2 li ].
Proof using EL.
  intros HG HBB HCC. pose proof HG as (Hl1 & Hl2 & Hli & (W1 & W2 & Wi & _) & _).
  pose proof (eqty_wf_l ge_typeof (geq_ty_sound HBB)) as HB.
  pose proof (ctx_of_ty HB) as H1. pose proof (ext_wf_g HB W2) as H2.
  pose proof (MGeq_M (MGeq_wk1 (MGeq_wk1 HG H1) H2) HCC) as K.
  eapply geq_ty_lconv; [| apply lequiv_sym, M_lv_f; assumption].
  apply geq_ty_pi; [exact Hl2 | exact (lequiv_max _ _ _ _ _ (lequiv_max _ _ _ _ _ Hl1 Hl2) Hli) | exact HB | exact HBB | exact K].
Qed.

(** An index related in every world, seen from a world. *)
Lemma MIdx_kw {G Γ} {idxR : DomRel G Γ} {m m'} (ρ : kwk G Γ) :
  (forall ρ, idxR ρ (ktm ρ m) (ktm ρ m')) ->
  forall ρ' : kwk (kw_G ρ) (kw_Δ ρ), idxR (kw_comp ρ ρ') (ktm ρ' (ktm ρ m)) (ktm ρ' (ktm ρ m')).
Proof using. intros I ρ'. rewrite <- !ktm_comp. exact (I (kw_comp ρ ρ')). Qed.

(** ** The other side's view

    The relations with both sides' arguments swapped. *)
Definition mflipI {G Γ} (idxR : DomRel G Γ) : DomRel G Γ := fun ρ x x' => idxR ρ x' x.
Definition mflipS {G Γ} (shR : MShRel G Γ) : MShRel G Γ := fun ρ x x' a a' => shR ρ x' x a' a.
Definition mflipP {G Γ} (posR : MPosRel G Γ) : MPosRel G Γ :=
  fun ρ x x' a a' p p' => posR ρ x' x a' a p' p.

Lemma MSide_flip {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR} :
  MSide G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR ->
  MSide G Γ r1 r2 ri X' A' B' C' l1 l2 li X A B C (mflipI idxR) (mflipS shR) (mflipP posR).
Proof using EL.
  intros HM. pose proof (ms_geq HM) as HG.
  pose proof HG as (H1 & H2 & H3 & (W1 & W2 & Wi & HX & HA & HB & HC) & HXX & _).
  pose proof (lequiv_sym _ _ _ H1) as H1'. pose proof (lequiv_sym _ _ _ H2) as H2'.
  pose proof (lequiv_sym _ _ _ H3) as H3'.
  pose proof (lequiv_wf_r _ _ _ H1) as W1'. pose proof (lequiv_wf_r _ _ _ H2) as W2'.
  assert (EXρ : forall ρ : kwk G Γ, [ kw_G ρ ; kw_Δ ρ ⊢g kty ρ X ≅ kty ρ X' @ li ])
    by (intros ρ; exact (kw_eqty ρ (geq_ty_sound HXX))).
  unfold mflipI, mflipS, mflipP. split.
  - exact (MGeq_flip HG).
  - intros ρ x x' h. eapply geq_tm_lconv; [| exact (kw_lequiv ρ H3')].
    exact (geq_tm_conv (geq_tm_sym (ms_eI HM ρ x' x h)) (EXρ ρ)).
  - intros ρ x x' h. exact (geq_ty_lconv (geq_ty_sym (ms_gA HM ρ x' x h)) (kw_lequiv ρ H1')).
  - intros ρ x x' a a' h ha. eapply geq_tm_lconv; [| exact (kw_lequiv ρ H1')].
    exact (geq_tm_conv (geq_tm_sym (ms_eS HM ρ x' x a' a h ha)) (geq_ty_sound (ms_gA HM ρ x' x h))).
  - intros ρ x x' a a' h ha. exact (geq_ty_lconv (geq_ty_sym (ms_gBa HM ρ x' x a' a h ha)) (kw_lequiv ρ H2')).
  - intros ρ x x' a a' p p' h ha hp. eapply geq_tm_lconv; [| exact (kw_lequiv ρ H2')].
    exact (geq_tm_conv (geq_tm_sym (ms_eP HM ρ x' x a' a p' p h ha hp)) (geq_ty_sound (ms_gBa HM ρ x' x a' a h ha))).
  - intros ρ x x' a a' p p' h ha hp. exact (ms_ch HM ρ x' x a' a p' p h ha hp).
  - intros ρ x x' h. pose proof (geq_ty_sound (ms_gA HM ρ x' x h)) as EA.
    eapply geq_ty_ctxconv; [exact EA | exact (kw_lequiv ρ H1) | apply ext_wf_g; [| exact (kw_lwf ρ W1')] |].
    + eapply wft_lconv; [exact (eqty_wf_r ge_typeof EA) | exact (kw_lequiv ρ H1')].
    + exact (geq_ty_lconv (geq_ty_sym (ms_gB HM ρ x' x h)) (kw_lequiv ρ H2')).
  - intros ρ x x' h. pose proof (geq_ty_sound (ms_gA HM ρ x' x h)) as EA.
    pose proof (geq_ty_sound (ms_gB HM ρ x' x h)) as EB.
    pose proof (ms_gC HM ρ x' x h) as GC.
    pose proof (ctx_of_eqtm ge_typeof (geq_tm_sound GC)) as HΓ2.
    pose proof (ctx_pre HΓ2) as HΓ1.
    assert (EX2 : [ kw_G ρ ; kw_Δ ρ ,, (ktyl ρ A)[lsingle x'] @ l1 ,, (ktyll ρ B)[llift (lsingle x')] @ l2
                    ⊢g (kty ρ X)⟨↑⟩⟨↑⟩ ≅ (kty ρ X')⟨↑⟩⟨↑⟩ @ li ])
      by exact (wk1_eqty _ ge_layer ge_typeof _ _ _ _ _ _ HΓ2 (wk1_eqty _ ge_layer ge_typeof _ _ _ _ _ _ HΓ1 (EXρ ρ))).
    pose proof (ctx2_conv ge_typeof EA (kw_lequiv ρ H1) EB (kw_lequiv ρ H2)) as Q.
    exact (geq_tm_ctxeq Q (geq_tm_lconv (geq_tm_conv (geq_tm_sym GC) EX2) (kw_lequiv ρ H3'))).
  - intros ρ x x' a a' h ha. pose proof (geq_ty_sound (ms_gBa HM ρ x' x a' a h ha)) as EB.
    pose proof (ms_gCa HM ρ x' x a' a h ha) as GC.
    pose proof (ctx_of_eqtm ge_typeof (geq_tm_sound GC)) as HΓ1.
    assert (EX1 : [ kw_G ρ ; kw_Δ ρ ,, (ktyll ρ B)[lsingle2 x' a'] @ l2 ⊢g (kty ρ X)⟨↑⟩ ≅ (kty ρ X')⟨↑⟩ @ li ])
      by exact (wk1_eqty _ ge_layer ge_typeof _ _ _ _ _ _ HΓ1 (EXρ ρ)).
    eapply geq_tm_ctxconv; [exact EB | exact (kw_lequiv ρ H2) | apply ext_wf_g; [| exact (kw_lwf ρ W2')] |].
    + eapply wft_lconv; [exact (eqty_wf_r ge_typeof EB) | exact (kw_lequiv ρ H2')].
    + exact (geq_tm_lconv (geq_tm_conv (geq_tm_sym GC) EX1) (kw_lequiv ρ H3')).
  - intros ρ ρ' x x' h. exact (ms_imon HM ρ ρ' x' x h).
  - intros ρ ρ' x x' a a' h ha. exact (ms_shmon HM ρ ρ' x' x a' a h ha).
  - intros ρ ρ' x x' a a' p p' h ha hp. exact (ms_posmon HM ρ ρ' x' x a' a p' p h ha hp).
  - intros ρ1 ρ2 Eρ x x' h. exact (ms_iinv HM ρ1 ρ2 Eρ x' x h).
  - intros ρ1 ρ2 Eρ x x' a a' h ha. exact (ms_shinv HM ρ1 ρ2 Eρ x' x a' a h ha).
  - intros ρ1 ρ2 Eρ x x' a a' p p' h ha hp. exact (ms_posinv HM ρ1 ρ2 Eρ x' x a' a p' p h ha hp).
Qed.

(** ** A child of related indices, shapes and positions *)

Lemma LK_lsingle3 a b c : nftm a -> nftm b -> nftm c -> LK nftm (lsingle3 a b c).
Proof using. intros Ha Hb Hc [|[|[|n]]]; cbn; auto. Qed.

Lemma MSide_child {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR m m'}
    (ρ : kwk G Γ) (ρ' : kwk (kw_G ρ) (kw_Δ ρ)) a a' p p' :
  MSide G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR -> nftm m -> nftm m' ->
  (forall ρ, idxR ρ (ktm ρ m) (ktm ρ m')) ->
  shR ρ (ktm ρ m) (ktm ρ m') a a' ->
  posR (kw_comp ρ ρ') (ktm (kw_comp ρ ρ') m) (ktm (kw_comp ρ ρ') m') (ktm ρ' a) (ktm ρ' a') p p' ->
  nftm (ktmlll (kw_comp ρ ρ') C)[lsingle3 (ktm (kw_comp ρ ρ') m) (ktm ρ' a) p] /\
  nftm (ktmlll (kw_comp ρ ρ') C')[lsingle3 (ktm (kw_comp ρ ρ') m') (ktm ρ' a') p'] /\
  (forall ρ'' : kwk (kw_G ρ') (kw_Δ ρ'), idxR (kw_comp (kw_comp ρ ρ') ρ'')
      (ktm ρ'' (ktmlll (kw_comp ρ ρ') C)[lsingle3 (ktm (kw_comp ρ ρ') m) (ktm ρ' a) p])
      (ktm ρ'' (ktmlll (kw_comp ρ ρ') C')[lsingle3 (ktm (kw_comp ρ ρ') m') (ktm ρ' a') p'])).
Proof using EL.
  intros HM Nm Nm' I ha hp.
  set (ρ1 := kw_comp ρ ρ').
  assert (Sa : shR ρ1 (ktm ρ1 m) (ktm ρ1 m') (ktm ρ' a) (ktm ρ' a')).
  { subst ρ1. rewrite !ktm_comp. exact (ms_shmon HM ρ ρ' _ _ _ _ (I ρ) ha). }
  pose proof (geq_tm_sound (ms_eP HM ρ1 _ _ _ _ _ _ (I ρ1) Sa hp)) as Ep.
  pose proof (wf_tm_nf (eqtm_wf_l ge_typeof Ep)) as Np.
  pose proof (wf_tm_nf (eqtm_wf_r ge_typeof Ep)) as Np'.
  assert (Nr : forall t : tm, nftm (ktm ρ1 t)) by (intros; unfold ktm; apply ren_nf).
  assert (Nr' : forall t : tm, nftm (ktm ρ' t)) by (intros; unfold ktm; apply ren_nf).
  assert (Nl : forall t : tm, nftm (ktmlll ρ1 t)) by (intros; unfold ktmlll; apply ren_nf).
  refine (conj _ (conj _ _)).
  - apply subst_nf; [apply Nl | apply LK_lsingle3; auto].
  - apply subst_nf; [apply Nl | apply LK_lsingle3; auto].
  - intros ρ''.
    pose proof (ms_shmon HM ρ1 ρ'' _ _ _ _ (I ρ1) Sa) as Sa'.
    pose proof (ms_posmon HM ρ1 ρ'' _ _ _ _ _ _ (I ρ1) Sa hp) as hp'.
    rewrite <- !(ktm_comp ρ1 ρ'') in Sa', hp'.
    pose proof (ms_ch HM _ _ _ _ _ _ _ (I (kw_comp ρ1 ρ'')) Sa' hp') as Y.
    rewrite !ktm_lsingle3, <- !(ktmlll_comp ρ1 ρ''), <- !(ktm_comp ρ1 ρ''). exact Y.
Qed.

End MAuxSide.

(** Normality of syntax in a world. *)
Ltac kw_nf := unfold kty, ktyl, ktyll, ktmlll, ktm; first [apply ren_nf_ty | apply ren_nf].
