(** * Validity of [elim_IWi] (M19_DESIGN.md, M19b)

    As [elim_IWf]'s ([IWfElim]), by induction on [IWiRel] at every global
    weakening and related substitution, with the motive index-agnostic and
    the spine's motive at [dnth]'s states. The children are functions:

    - The motive at the spine is also at an application of [dnth]'s state
      to an argument, at the annotations of the induction hypothesis's
      body; the argument is related by the spine's argument relation at
      every canonical position the index of [Fin] is related to
      ([PosCan], [fin_pos_hd], [fin_pos_tl]), with the annotations
      equivalent to the field's at that position.
    - The relation's domains' relation is canonical where the relation
      reads it ([LR_iwi_rel]), against the left family at the right
      substitution ([elimIWi_kd]).
    - The induction hypothesis is two λs, related at its [Π]s by
      [LRtm_lam_K] twice. *)
From DeLaM.Validity Require Export IWiElimBase.
From DeLaM.Typing Require Import IWiIH.
From DeLaM.LogRel Require Import IWfAux IWiAux.
From DeLaM.Validity Require Import DNthReds MCorec IWfSp IWiSp IWiElimDnth.

Section IWiElimV.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp} `{VN : !VPNe}.

(** The motive's scrutinee type at an index. *)
Lemma iwimotty_cons l lp li (X A : ty) (N : tm) (D : ty) (Ot C : tm) e x : LK nftm e ->
  nfty X[e] -> nfty A[e] -> nftm N[llift e] -> nfty D[llift (llift e)] -> nftm Ot[llift e] ->
  nftm C[llift (llift (llift e))] ->
  (iwimotty l lp li X A N D Ot C)[lcons e x] =
  tyIWi l lp li X[e] A[e] N[llift e] D[llift (llift e)] Ot[llift e] C[llift (llift (llift e))] x.
Proof using .
  intros Ne NX NA NN ND NO NC. rewrite <- lift_single_ty by exact Ne. rewrite iwimotty_llift by exact Ne.
  apply IWi_E_mot; assumption.
Qed.

(** The induction hypothesis in a world, and its body at an index and an
    argument. *)
Lemma ktm_iwiIH {G Δ} (ρ : kwk G Δ) l lp li l' X A N D Ot C M c a cs :
  ktm ρ (iwiIH l lp li l' X A N D Ot C M c a cs) =
  iwiIH l lp li l' (kty ρ X) (kty ρ A) (ktml ρ N) (ktyll ρ D) (ktml ρ Ot) (ktmlll ρ C) (ktyll ρ M) (ktmlll ρ c)
    (ktm ρ a) (ktm ρ cs).
Proof using . unfold ktm, kty, ktml, ktyll, ktmlll. now rewrite gwa_iwiIH, ren_iwiIH. Qed.

Lemma ktmll_iwibody {G Δ} (ρ : kwk G Δ) l lp li l' X A N D Ot C M c a cs :
  ktmll ρ (iwibody l lp li l' X A N D Ot C M c a cs) =
  iwibody l lp li l' (kty ρ X) (kty ρ A) (ktml ρ N) (ktyll ρ D) (ktml ρ Ot) (ktmlll ρ C) (ktyll ρ M) (ktmlll ρ c)
    (ktm ρ a) (ktm ρ cs).
Proof using .
  pose proof (ktm_iwiIH ρ l lp li l' X A N D Ot C M c a cs) as H. rewrite !iwiIH_body in H.
  rewrite ktm_lam, ktml_lam in H.
  (* the body, by projection: [injection] states every component's equation *)
  exact (f_equal (fun t => match t with lam _ _ _ (lam _ _ _ b) => b | _ => t end) H).
Qed.

Lemma ktmll_iwiapp {G Δ} (ρ : kwk G Δ) l lp li X A N D Ot C a cs :
  ktmll ρ (iwiapp l lp li X A N D Ot C a cs) =
  iwiapp l lp li (kty ρ X) (kty ρ A) (ktml ρ N) (ktyll ρ D) (ktml ρ Ot) (ktmlll ρ C) (ktm ρ a) (ktm ρ cs).
Proof using .
  pose proof (ktmll_iwibody ρ l lp li lzero X A N D Ot C tyNat (var 0) a cs) as H.
  unfold ktmll in H. rewrite gwa_elimIWi in H. cbn [ren_tm] in H.
  exact (f_equal (fun t => match t with tmElimIWi _ _ _ _ _ _ _ _ _ _ _ _ _ s => s | _ => t end) H).
Qed.

Lemma ktyll_iwicod {G Δ} (ρ : kwk G Δ) l lp li X A N D Ot C (M : ty) a cs :
  ktyll ρ (iwicod l lp li X A N D Ot C M a cs) =
  iwicod l lp li (kty ρ X) (kty ρ A) (ktml ρ N) (ktyll ρ D) (ktml ρ Ot) (ktmlll ρ C) (ktyll ρ M) (ktm ρ a) (ktm ρ cs).
Proof using .
  rewrite <- ktmll_iwiapp, <- ktmll_llift2_single.
  unfold ktyll, ktmll. rewrite gwa_subst_ty, gwa_lsingle2, !gwa_ren_ty, lsingle2_ren_ty. f_equal.
  rewrite !ren_ren_comp_ty. apply ren_ext_ty. intros [|[|n]]; rlk_simpl; reflexivity.
Qed.

Lemma iwiapp_single2 l lp li (X A : ty) (N : tm) (D : ty) (Ot C a cs i y : tm) :
  nfty X -> nfty A -> nftm N -> nfty D -> nftm Ot -> nftm C -> nftm a -> nftm cs -> nftm i -> nftm y ->
  (iwiapp l lp li X A N D Ot C a cs)[lsingle2 i y] =
  app (tmDNth (iwiL l lp li) N[lsingle a] (iwiFam l lp li X A N D Ot C a) cs i) lp (iwiL l lp li)
    D[lsingle2 a i] (iwiFamCod l lp li X A N D Ot C a)[llift (lsingle i)] y.
Proof using .
  intros NX NA NN ND NO NC Na Ncs Ni Ny.
  meq. rewrite subst_tmDNth by (apply lk_lsingle2; assumption). unfold iwiFam, iwiFamCod. meq.
Qed.

Lemma iwibody_single2 l lp li l' (X A : ty) (N : tm) (D : ty) (Ot C : tm) (M : ty) (c a cs i y : tm) :
  nfty X -> nfty A -> nftm N -> nfty D -> nftm Ot -> nftm C -> nfty M -> nftm c -> nftm a -> nftm cs ->
  nftm i -> nftm y ->
  (iwibody l lp li l' X A N D Ot C M c a cs)[lsingle2 i y] =
  tmElimIWi l lp li l' X A N D Ot C M c C[lsingle3 a i y]
    (app (tmDNth (iwiL l lp li) N[lsingle a] (iwiFam l lp li X A N D Ot C a) cs i) lp (iwiL l lp li)
       D[lsingle2 a i] (iwiFamCod l lp li X A N D Ot C a)[llift (lsingle i)] y).
Proof using .
  intros NX NA NN ND NO NC NM Nc Na Ncs Ni Ny.
  rewrite subst_elimIWi, iwiapp_single2, llift2_single_single2 by assumption. f_equal; meq.
Qed.

Lemma iwicod_single2 l lp li (X A : ty) (N : tm) (D : ty) (Ot C : tm) (M : ty) (a cs i y : tm) :
  nfty X -> nfty A -> nftm N -> nfty D -> nftm Ot -> nftm C -> nfty M -> nftm a -> nftm cs ->
  nftm i -> nftm y ->
  (iwicod l lp li X A N D Ot C M a cs)[lsingle2 i y] =
  M[lsingle2 C[lsingle3 a i y]
      (app (tmDNth (iwiL l lp li) N[lsingle a] (iwiFam l lp li X A N D Ot C a) cs i) lp (iwiL l lp li)
         D[lsingle2 a i] (iwiFamCod l lp li X A N D Ot C a)[llift (lsingle i)] y)].
Proof using .
  intros NX NA NN ND NO NC NM Na Ncs Ni Ny.
  rewrite (single2_subst_ty (lsingle2 i y)) by (apply lk_lsingle2; assumption).
  rewrite iwiapp_single2, llift2_single_single2 by assumption. f_equal. meq.
Qed.

(** [IWiRel] is closed under expansion. *)
Lemma IWiRel_red_bwd {G Δ l lp li X A N D Ot C ix dm pd m t t' u u'} :
  [ G ; Δ ⊢g t ⤳* u : tyIWi l lp li X A N D Ot C m @ iwiL l lp li ] ->
  [ G ; Δ ⊢g t' ⤳* u' : tyIWi l lp li X A N D Ot C m @ iwiL l lp li ] ->
  IWiRel G Δ l lp li X A N D Ot C ix dm pd m u u' -> IWiRel G Δ l lp li X A N D Ot C ix dm pd m t t'.
Proof using .
  intros Ht Ht' H. destruct (IWiRel_inv H) as (w & w' & Hw & Hw' & Ew & Nw).
  econstructor; [eapply tmred_trans; [exact Ht | exact Hw] | eapply tmred_trans; [exact Ht' | exact Hw']
                | exact Ew | exact Nw].
Qed.

(** ** The eliminator at related premises *)

Section ElimAt.
Context {G : gctx} {Γ : ctx} {l lp li l' l3 lp3 li3 l4 : lvl} {X X' A A' D D' : ty} {N N' Ot Ot' C C' : tm}
  {M M' : ty} {c c' : tm}
  (Hwl : lwf (gL G) l) (Hwlp : lwf (gL G) lp) (Hwli : lwf (gL G) li) (Hwl' : lwf (gL G) l')
  (H13 : lequiv (gL G) l l3) (Hp3 : lequiv (gL G) lp lp3) (Hi3 : lequiv (gL G) li li3)
  (H24 : lequiv (gL G) l' l4)
  (HS : IWiSig (G := G) (i := ge_layer) Γ l lp li X A N D Ot C)
  (VX : VTyG G Γ X X' li) (VA : VTyG G Γ A A' l)
  (VNt : VTmG G (Γ ,, A @ l) N N' tyNat lzero)
  (VD : VTyG G (Γ ,, A @ l ,, tyFin N @ lzero) D D' lp)
  (VO : VTmG G (Γ ,, A @ l) Ot Ot' X⟨↑⟩ li)
  (VC : VTmG G (Γ ,, A @ l ,, tyFin N @ lzero ,, D @ lp) C C' X⟨↑⟩⟨↑⟩⟨↑⟩ li)
  (Vmot : VTyG G (Γ ,, X @ li) (iwimotty l lp li X A N D Ot C) (iwimotty l lp li X A N D Ot C) (iwiL l lp li))
  (VM : VTyG G (Γ ,, X @ li ,, iwimotty l lp li X A N D Ot C @ iwiL l lp li) M M' l')
  (Vcs : VTyG G (Γ ,, A @ l) (iwicsty l lp li X A N D Ot C) (iwicsty l lp li X A N D Ot C) (iwiL l lp li))
  (Vih : VTyG G (Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li)
           (iwiihty l lp li l' X A N D Ot C M) (iwiihty l3 lp3 li3 l4 X' A' N' D' Ot' C' M')
           (lmax lzero (lmax lp l')))
  (Vc : VTmG G (Γ ,, A @ l ,, iwicsty l lp li X A N D Ot C @ iwiL l lp li
                  ,, iwiihty l lp li l' X A N D Ot C M @ lmax lzero (lmax lp l'))
          c c' (iwistepty l lp li X A N D Ot C M) l').

Local Notation L := (iwiL l lp li).
Local Notation LI := (lmax lzero (lmax lp l')).

(** The premises at a global weakening, localized. *)
Lemma elimIWi_loc {G0 γ} : gwk_ok γ G0 G ->
  VTyG G0 Γ⟦γ⟧ X⟦γ⟧ X'⟦γ⟧ li /\ VTyG G0 Γ⟦γ⟧ A⟦γ⟧ A'⟦γ⟧ l /\
  VTmG G0 (Γ⟦γ⟧ ,, A⟦γ⟧ @ l) N⟦γ⟧ N'⟦γ⟧ tyNat lzero /\
  VTyG G0 (Γ⟦γ⟧ ,, A⟦γ⟧ @ l ,, tyFin N⟦γ⟧ @ lzero) D⟦γ⟧ D'⟦γ⟧ lp /\
  VTmG G0 (Γ⟦γ⟧ ,, A⟦γ⟧ @ l) Ot⟦γ⟧ Ot'⟦γ⟧ X⟦γ⟧⟨↑⟩ li /\
  VTmG G0 (Γ⟦γ⟧ ,, A⟦γ⟧ @ l ,, tyFin N⟦γ⟧ @ lzero ,, D⟦γ⟧ @ lp) C⟦γ⟧ C'⟦γ⟧ X⟦γ⟧⟨↑⟩⟨↑⟩⟨↑⟩ li /\
  VTy G0 (Γ⟦γ⟧ ,, X⟦γ⟧ @ li) (iwimotty l lp li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ D⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧)
    (iwimotty l lp li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ D⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧) L /\
  VTy G0 (Γ⟦γ⟧ ,, X⟦γ⟧ @ li ,, iwimotty l lp li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ D⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧ @ L) M⟦γ⟧ M'⟦γ⟧ l' /\
  VTy G0 (Γ⟦γ⟧ ,, A⟦γ⟧ @ l) (iwicsty l lp li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ D⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧)
    (iwicsty l lp li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ D⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧) L /\
  VTy G0 (Γ⟦γ⟧ ,, A⟦γ⟧ @ l ,, iwicsty l lp li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ D⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧ @ L)
    (iwiihty l lp li l' X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ D⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧ M⟦γ⟧)
    (iwiihty l3 lp3 li3 l4 X'⟦γ⟧ A'⟦γ⟧ N'⟦γ⟧ D'⟦γ⟧ Ot'⟦γ⟧ C'⟦γ⟧ M'⟦γ⟧) LI /\
  VTm G0 (Γ⟦γ⟧ ,, A⟦γ⟧ @ l ,, iwicsty l lp li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ D⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧ @ L
            ,, iwiihty l lp li l' X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ D⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧ M⟦γ⟧ @ LI)
    c⟦γ⟧ c'⟦γ⟧ (iwistepty l lp li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ D⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧ M⟦γ⟧) l'.
Proof using VA VC VD VM VNt VO VX Vc Vcs Vih Vmot.
  intros Hγ.
  pose proof (VTyG_gwk VX Hγ) as VXγ. pose proof (VTyG_gwk VA Hγ) as VAγ.
  pose proof (VTmG_gwk VNt Hγ) as VNγ. rewrite gwa_cext, gwa_tyNat in VNγ.
  pose proof (VTyG_gwk VD Hγ) as VDγ. rewrite !gwa_cext, gwa_tyFin in VDγ.
  pose proof (VTmG_gwk VO Hγ) as VOγ. rewrite gwa_cext, gwa_ren_ty in VOγ.
  pose proof (VTmG_gwk VC Hγ) as VCγ. rewrite !gwa_cext, gwa_tyFin, !gwa_ren_ty in VCγ.
  pose proof (Vmot _ _ Hγ) as Vmotγ. rewrite gwa_cext, gwa_iwimotty in Vmotγ.
  pose proof (VM _ _ Hγ) as VMγ. rewrite !gwa_cext, gwa_iwimotty in VMγ.
  pose proof (Vcs _ _ Hγ) as Vcsγ. rewrite gwa_cext, gwa_iwicsty in Vcsγ.
  pose proof (Vih _ _ Hγ) as Vihγ. rewrite !gwa_cext, gwa_iwicsty, !gwa_iwiihty in Vihγ.
  pose proof (Vc _ _ Hγ) as Vcγ. rewrite !gwa_cext, gwa_iwicsty, gwa_iwiihty, gwa_iwistepty in Vcγ.
  repeat split; assumption.
Qed.

(** Abbreviations: the premises at a global weakening and a substitution. *)
Local Notation sX γ e := (X⟦γ⟧[e]).
Local Notation sX' γ e := (X'⟦γ⟧[e]).
Local Notation sA γ e := (A⟦γ⟧[e]).
Local Notation sA' γ e := (A'⟦γ⟧[e]).
Local Notation sN γ e := (N⟦γ⟧[llift e]).
Local Notation sN' γ e := (N'⟦γ⟧[llift e]).
Local Notation sD γ e := (D⟦γ⟧[llift (llift e)]).
Local Notation sD' γ e := (D'⟦γ⟧[llift (llift e)]).
Local Notation sO γ e := (Ot⟦γ⟧[llift e]).
Local Notation sO' γ e := (Ot'⟦γ⟧[llift e]).
Local Notation sC γ e := (C⟦γ⟧[llift (llift (llift e))]).
Local Notation sC' γ e := (C'⟦γ⟧[llift (llift (llift e))]).
Local Notation sM γ e := (M⟦γ⟧[llift (llift e)]).
Local Notation sM' γ e := (M'⟦γ⟧[llift (llift e)]).
Local Notation sc γ e := (c⟦γ⟧[llift (llift (llift e))]).
Local Notation sc' γ e := (c'⟦γ⟧[llift (llift (llift e))]).
Local Notation tyL γ e m := (tyIWi l lp li (sX γ e) (sA γ e) (sN γ e) (sD γ e) (sO γ e) (sC γ e) m).
Local Notation elL γ e m t :=
  (tmElimIWi l lp li l' (sX γ e) (sA γ e) (sN γ e) (sD γ e) (sO γ e) (sC γ e) (sM γ e) (sc γ e) m t).
Local Notation elR γ e m t :=
  (tmElimIWi l3 lp3 li3 l4 (sX' γ e) (sA' γ e) (sN' γ e) (sD' γ e) (sO' γ e) (sC' γ e) (sM' γ e) (sc' γ e) m t).

(** The premises at a related substitution after a global weakening. *)
Lemma elimIWi_at {G0 γ Δ0 e e'} : gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' ->
  [ G0 ; Δ0 ⊢g sX γ e @ li ] /\ [ G0 ; Δ0 ⊢ sX γ e ≈ sX' γ e' @ li ] /\
  [ G0 ; Δ0 ⊢g sA γ e @ l ] /\ [ G0 ; Δ0 ⊢ sA γ e ≈ sA' γ e' @ l ] /\
  [ G0 ; Δ0 ,, sA γ e @ l ⊢g sN γ e : tyNat @ lzero ] /\
  [ G0 ; Δ0 ,, sA γ e @ l ⊢ sN γ e ≈ sN' γ e' : tyNat @ lzero ] /\
  [ G0 ; Δ0 ,, sA γ e @ l ,, tyFin (sN γ e) @ lzero ⊢g sD γ e @ lp ] /\
  [ G0 ; Δ0 ,, sA γ e @ l ,, tyFin (sN γ e) @ lzero ⊢ sD γ e ≈ sD' γ e' @ lp ] /\
  [ G0 ; Δ0 ,, sA γ e @ l ⊢g sO γ e : (sX γ e)⟨↑⟩ @ li ] /\
  [ G0 ; Δ0 ,, sA γ e @ l ⊢ sO γ e ≈ sO' γ e' : (sX γ e)⟨↑⟩ @ li ] /\
  [ G0 ; Δ0 ,, sA γ e @ l ,, tyFin (sN γ e) @ lzero ,, sD γ e @ lp ⊢g sC γ e : (sX γ e)⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] /\
  [ G0 ; Δ0 ,, sA γ e @ l ,, tyFin (sN γ e) @ lzero ,, sD γ e @ lp
      ⊢ sC γ e ≈ sC' γ e' : (sX γ e)⟨↑⟩⟨↑⟩⟨↑⟩ @ li ] /\
  [ G0 ; Δ0 ,, sX γ e @ li ⊢g iwimotty l lp li (sX γ e) (sA γ e) (sN γ e) (sD γ e) (sO γ e) (sC γ e) @ L ] /\
  [ G0 ; Δ0 ,, sX γ e @ li ,, iwimotty l lp li (sX γ e) (sA γ e) (sN γ e) (sD γ e) (sO γ e) (sC γ e) @ L
      ⊢g sM γ e @ l' ] /\
  [ G0 ; Δ0 ,, sX γ e @ li ,, iwimotty l lp li (sX γ e) (sA γ e) (sN γ e) (sD γ e) (sO γ e) (sC γ e) @ L
      ⊢ sM γ e ≈ sM' γ e' @ l' ] /\
  [ G0 ; Δ0 ,, sA γ e @ l ⊢g iwicsty l lp li (sX γ e) (sA γ e) (sN γ e) (sD γ e) (sO γ e) (sC γ e) @ L ] /\
  [ G0 ; Δ0 ,, sA γ e @ l ,, iwicsty l lp li (sX γ e) (sA γ e) (sN γ e) (sD γ e) (sO γ e) (sC γ e) @ L
      ⊢g iwiihty l lp li l' (sX γ e) (sA γ e) (sN γ e) (sD γ e) (sO γ e) (sC γ e) (sM γ e) @ LI ] /\
  [ G0 ; Δ0 ,, sA γ e @ l ,, iwicsty l lp li (sX γ e) (sA γ e) (sN γ e) (sD γ e) (sO γ e) (sC γ e) @ L
      ⊢ iwiihty l lp li l' (sX γ e) (sA γ e) (sN γ e) (sD γ e) (sO γ e) (sC γ e) (sM γ e)
        ≈ iwiihty l3 lp3 li3 l4 (sX' γ e') (sA' γ e') (sN' γ e') (sD' γ e') (sO' γ e') (sC' γ e') (sM' γ e')
        @ LI ] /\
  [ G0 ; Δ0 ,, sA γ e @ l ,, iwicsty l lp li (sX γ e) (sA γ e) (sN γ e) (sD γ e) (sO γ e) (sC γ e) @ L
      ,, iwiihty l lp li l' (sX γ e) (sA γ e) (sN γ e) (sD γ e) (sO γ e) (sC γ e) (sM γ e) @ LI
      ⊢ sc γ e ≈ sc' γ e'
        : iwistepty l lp li (sX γ e) (sA γ e) (sN γ e) (sD γ e) (sO γ e) (sC γ e) (sM γ e) @ l' ].
Proof using EL Hwl Hwl' Hwli Hwlp VA VC VD VL VM VN VNt VO VX Vc Vcs Vih Vmot.
  intros Hγ He. destruct (SubRel_nf _ _ _ _ _ He) as [Ne Ne'].
  destruct (elimIWi_loc Hγ) as (VXγ & VAγ & VNγ & VDγ & VOγ & VCγ & Vmotγ & VMγ & Vcsγ & Vihγ & Vcγ).
  pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwl) as Hwl0. pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwli) as Hwli0.
  pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwlp) as Hwlp0. pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwl') as Hwl'0.
  assert (HwL : lwf (gL G0) L) by (split; [split|]; assumption).
  assert (HwI : lwf (gL G0) LI) by (split; [exact I | split; assumption]).
  destruct (VTyG_loc VXγ _ _ _ He) as [RX HRX]. destruct (escape_ty _ _ _ _ _ _ _ _ HRX) as (HX0 & _ & EX).
  destruct (VTyG_loc VAγ _ _ _ He) as [RA HRA]. destruct (escape_ty _ _ _ _ _ _ _ _ HRA) as (HA0 & _ & EA).
  pose proof (SubRel_lift He (VTy_refl_l (VTyG_loc VAγ)) HA0 Hwl0) as H1.
  pose proof (VTmG_loc VNγ _ _ _ H1) as XN. rewrite !subst_tyNat in XN.
  destruct (LRtm_escape XN) as [HN0 _]. pose proof (LRtm_geq XN) as EN.
  pose proof (VTmG_loc VOγ _ _ _ H1) as XO. rewrite !shift_llift_ty in XO.
  destruct (LRtm_escape XO) as [HO0 _]. pose proof (LRtm_geq XO) as EO.
  assert (HF0 : [ G0 ; Δ0 ,, sA γ e @ l ⊢g (tyFin N⟦γ⟧)[llift e] @ lzero ])
    by (rewrite subst_tyFin; apply wft_fin; [exact ge_notV | exact HN0]).
  pose proof (SubRel_lift H1 (V_fin (VTmG_loc (VTmG_refl_l VNγ))) HF0 I) as H1F.
  destruct (VTyG_loc VDγ _ _ _ H1F) as [RD HRD]. destruct (escape_ty _ _ _ _ _ _ _ _ HRD) as (HD0 & _ & ED).
  pose proof (SubRel_lift H1F (VTy_refl_l (VTyG_loc VDγ)) HD0 Hwlp0) as H1D.
  rewrite subst_tyFin in HD0, ED, H1D.
  pose proof (VTmG_loc VCγ _ _ _ H1D) as XC. rewrite !shift_llift_ty in XC.
  destruct (LRtm_escape XC) as [HC0 _]. pose proof (LRtm_geq XC) as EC.
  (* the motive *)
  pose proof (SubRel_lift He (VTy_refl_l (VTyG_loc VXγ)) HX0 Hwli0) as H1X.
  destruct (Vmotγ _ _ _ H1X) as [RMo HRMo]. destruct (escape_ty _ _ _ _ _ _ _ _ HRMo) as (HMot0 & _ & _).
  pose proof (SubRel_lift H1X Vmotγ HMot0 HwL) as H2X.
  destruct (VMγ _ _ _ H2X) as [RM HRM]. destruct (escape_ty _ _ _ _ _ _ _ _ HRM) as (HM0 & _ & EM).
  rewrite iwimotty_llift in HMot0, HM0, EM by exact Ne.
  (* the step's telescope *)
  destruct (Vcsγ _ _ _ H1) as [RC HRC]. destruct (escape_ty _ _ _ _ _ _ _ _ HRC) as (Hcs0 & _ & _).
  pose proof (SubRel_lift H1 Vcsγ Hcs0 HwL) as H2.
  destruct (Vihγ _ _ _ H2) as [RI HRI]. destruct (escape_ty _ _ _ _ _ _ _ _ HRI) as (HI0 & _ & EI).
  pose proof (SubRel_lift H2 (VTy_refl_l Vihγ) HI0 HwI) as H3.
  pose proof (LRtm_geq (Vcγ _ _ _ H3)) as Ec.
  rewrite iwicsty_llift in Hcs0, HI0, EI, Ec by exact Ne.
  rewrite !iwiihty_llift2 in HI0, EI, Ec by assumption.
  rewrite iwistepty_llift3 in Ec by exact Ne.
  rewrite (iwiihty_llift2 e' Ne') in EI.
  repeat split; assumption.
Qed.

Lemma elimIWi_nf {G0 γ Δ0 e e'} : gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' ->
  nfty (sX γ e) /\ nfty (sA γ e) /\ nftm (sN γ e) /\ nfty (sD γ e) /\ nftm (sO γ e) /\ nftm (sC γ e) /\
  nfty (sM γ e) /\ nftm (sc γ e).
Proof using EL Hwl Hwl' Hwli Hwlp VA VC VD VL VM VN VNt VO VX Vc Vcs Vih Vmot.
  intros Hγ He.
  destruct (elimIWi_at Hγ He)
    as (HX0 & _ & HA0 & _ & HN0 & _ & HD0 & _ & HO0 & _ & HC0 & _ & _ & HM0 & _ & _ & _ & _ & Ec).
  repeat split; first [exact (wf_ty_nf HX0) | exact (wf_ty_nf HA0) | exact (wf_tm_nf HN0) | exact (wf_ty_nf HD0)
                      | exact (wf_tm_nf HO0) | exact (wf_tm_nf HC0) | exact (wf_ty_nf HM0)
                      | exact (wf_tm_nf (eqtm_wf_l ge_typeof (geq_tm_sound Ec)))].
Qed.

(** [elim_IWi]'s congruence and typed reductions in the scrutinee. *)
Section Cong.
Context {G0 γ Δ0 e e'} (Hγ : gwk_ok γ G0 G) (He : SubRel G0 Γ⟦γ⟧ Δ0 e e').

Lemma elimIWi_cong {m m' t t'} :
  [ G0 ; Δ0 ⊢g m ≅ m' : sX γ e @ li ] -> [ G0 ; Δ0 ⊢g t ≅ t' : tyL γ e m @ L ] ->
  [ G0 ; Δ0 ⊢g elL γ e m t ≅ elR γ e' m' t' : (sM γ e)[lsingle2 m t] @ l' ].
Proof using EL H13 H24 He Hi3 Hp3 Hwl Hwl' Hwli Hwlp Hγ VA VC VD VL VM VN VNt VO VX Vc Vcs Vih Vmot.
  intros Hm Ht.
  destruct (elimIWi_at Hγ He) as (HX0 & EX & HA0 & EA & HN0 & EN & HD0 & ED & HO0 & EO & HC0 & EC & HMot0 & HM0
                                  & EM & Hcs0 & HI0 & EI & Ec).
  apply eqtm_elimIWi; first [exact (compt_notV _ ge_compt) | apply (lequiv_weaken _ _ _ _ (proj1 Hγ)); assumption
                            | apply geq_ty_sound; assumption | apply geq_tm_sound; assumption | assumption].
Qed.

Lemma elimIWi_cong_l {m m' t t'} :
  [ G0 ; Δ0 ⊢g m ≅ m' : sX γ e @ li ] -> [ G0 ; Δ0 ⊢g t ≅ t' : tyL γ e m @ L ] ->
  [ G0 ; Δ0 ⊢g elL γ e m t ≅ elL γ e m' t' : (sM γ e)[lsingle2 m t] @ l' ].
Proof using EL He Hwl Hwl' Hwli Hwlp Hγ VA VC VD VL VM VN VNt VO VX Vc Vcs Vih Vmot.
  intros Hm Ht.
  destruct (elimIWi_at Hγ He) as (HX0 & EX & HA0 & EA & HN0 & EN & HD0 & ED & HO0 & EO & HC0 & EC & HMot0 & HM0
                                  & EM & Hcs0 & HI0 & EI & Ec).
  pose proof (eqtm_wf_l ge_typeof (geq_tm_sound Ec)) as Hc0.
  apply eqtm_elimIWi; first [exact (compt_notV _ ge_compt)
                            | apply lequiv_refl, (lwf_weaken _ _ _ (proj1 Hγ)); assumption
                            | apply eqty_refl; assumption | apply eqtm_refl; assumption | assumption].
Qed.

Lemma elimIWi_red_l {m t w} : [ G0 ; Δ0 ⊢g m : sX γ e @ li ] ->
  [ G0 ; Δ0 ⊢g t ⤳* w : tyL γ e m @ L ] ->
  [ G0 ; Δ0 ⊢g elL γ e m t ⤳* elL γ e m w : (sM γ e)[lsingle2 m t] @ l' ].
Proof using EL He Hwl Hwl' Hwli Hwlp Hγ VA VC VD VL VM VN VNt VO VX Vc Vcs Vih Vmot.
  intros Hm Hr. pose proof (elimIWi_cong_l (eqtm_refl _ _ _ _ _ _ Hm) (tmred_eq _ _ _ _ _ _ _ Hr)) as Y.
  split; [exact (eqtm_wf_l ge_typeof Y) | apply reds_elimIWi, (tmred_red _ _ _ _ _ _ _ Hr) | exact Y].
Qed.

Lemma elimIWi_red_r {m m' t t' w'} :
  [ G0 ; Δ0 ⊢g m ≅ m' : sX γ e @ li ] -> [ G0 ; Δ0 ⊢g t ≅ t' : tyL γ e m @ L ] ->
  [ G0 ; Δ0 ⊢g t' ⤳* w' : tyL γ e m @ L ] ->
  [ G0 ; Δ0 ⊢g elR γ e' m' t' ⤳* elR γ e' m' w' : (sM γ e)[lsingle2 m t] @ l' ].
Proof using EL H13 H24 He Hi3 Hp3 Hwl Hwl' Hwli Hwlp Hγ VA VC VD VL VM VN VNt VO VX Vc Vcs Vih Vmot.
  intros Hm Htt Hr. pose proof (elimIWi_cong Hm Htt) as Y1.
  pose proof (elimIWi_cong Hm (eqtm_trans _ _ _ _ _ _ _ _ Htt (tmred_eq _ _ _ _ _ _ _ Hr))) as Y2.
  split; [exact (eqtm_wf_r ge_typeof Y1) | apply reds_elimIWi, (tmred_red _ _ _ _ _ _ _ Hr) |].
  eapply eqtm_trans; [apply eqtm_sym, Y1 | exact Y2].
Qed.

End Cong.

(** The index, shape and domain relations of the relation at [IWi]:
    canonical at the index and shape types, and at the domains where the
    relation reads them, against the left family at the right
    substitution (what [LR_iwi_rel] takes). *)
Definition elimIWi_kd G0 Δ0 (ix dm : DomRel G0 Δ0) (pd : IPosDomRel G0 Δ0) γ e e' : Prop :=
  KDom G0 Δ0 (lmeasure L) li (sX γ e) ix /\ KDom G0 Δ0 (lmeasure L) l (sA γ e) dm /\
  (forall (ρ : kwk G0 Δ0) a a', dm ρ a a' ->
     NatRel (kw_G ρ) (kw_Δ ρ) (ktml ρ (sN γ e))[lsingle a] (ktml ρ (sN γ e'))[lsingle a']) /\
  (forall (ρ : kwk G0 Δ0) a a', dm ρ a a' -> forall p p',
     PosRel (kw_G ρ) (kw_Δ ρ) (ktml ρ (sN γ e))[lsingle a] (ktml ρ (sN γ e'))[lsingle a'] p p' ->
     exists D1, LR (lmeasure L) (LRbelow (lmeasure L)) (kw_G ρ) (kw_Δ ρ) (ktyll ρ (sD γ e))[lsingle2 a p] D1 lp
       (pd ρ a a' p p')) /\
  (forall (ρ : kwk G0 Δ0) a a' p p' y y', pd ρ a a' p p' y y' ->
     PosRel (kw_G ρ) (kw_Δ ρ) (ktml ρ (sN γ e))[lsingle a] (ktml ρ (sN γ e'))[lsingle a'] p p').

(** The relation at [IWi] at an index, its relations canonical. *)
Lemma elimIWi_WLR {G0 γ Δ0 e e' x x'} : gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' ->
  LRtm li G0 Δ0 (sX γ e) (sX γ e') x x' ->
  exists (ix dm : DomRel G0 Δ0) (pd : IPosDomRel G0 Δ0),
    LogRel L G0 Δ0 (tyL γ e x)
      (tyIWi l lp li (sX γ e') (sA γ e') (sN γ e') (sD γ e') (sO γ e') (sC γ e') x') L
      (IWiRel G0 Δ0 l lp li (sX γ e) (sA γ e) (sN γ e) (sD γ e) (sO γ e) (sC γ e) ix dm pd x) /\
    elimIWi_kd G0 Δ0 ix dm pd γ e e'.
Proof using EL Hwl Hwli Hwlp VA VC VD VL VM VN VNt VO VX Vc Vcs Vih Vmot.
  intros Hγ He Hx. destruct (elimIWi_loc Hγ) as (VXγ & VAγ & VNγ & VDγ & VOγ & VCγ & _).
  pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwl) as Hwl0. pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwli) as Hwli0.
  pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwlp) as Hwlp0.
  pose proof (VTyG_refl_l VXγ) as VXX. pose proof (VTyG_refl_l VAγ) as VAA. pose proof (VTmG_refl_l VNγ) as VNN.
  pose proof (VTyG_refl_l VDγ) as VDD. pose proof (VTmG_refl_l VOγ) as VOO. pose proof (VTmG_refl_l VCγ) as VCC.
  eexists _, _, _. split.
  - exact (LR_IWi_at Hwl0 Hwlp0 Hwli0 (lequiv_refl _ _ Hwl0) (lequiv_refl _ _ Hwlp0) (lequiv_refl _ _ Hwli0)
             VXX VAA VNN VDD VOO VCC _ _ _ _ _ He Hx).
  - refine (conj _ (conj _ (conj _ (conj _ _)))).
    + intros ρ. eexists. exact (iwiIdx_canon (l := l) (lp := lp) VXX He ρ).
    + intros ρ. eexists. exact (iwiDom_canon (lp := lp) (li := li) VAA He ρ).
    + intros ρ a a' h. exact (iwi_arity VAA VNN He ρ a a' h).
    + intros ρ a a' h p p' Hp. eexists. exact (iwiPd_canon VAA VNN VDD He ρ a a' h p p' Hp).
    + intros ρ a a' p p' y y' [Hp _]. exact Hp.
Qed.

Lemma elimIWi_mot {G0 γ Δ0 e e' x x' s s'} : gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' ->
  LRtm li G0 Δ0 (sX γ e) (sX γ e') x x' ->
  LRtm L G0 Δ0 (tyL γ e x) (tyIWi l lp li (sX γ e') (sA γ e') (sN γ e') (sD γ e') (sO γ e') (sC γ e') x') s s' ->
  LRty l' G0 Δ0 (sM γ e)[lsingle2 x s] (sM γ e')[lsingle2 x' s'].
Proof using EL Hwl Hwl' Hwli Hwlp VA VC VD VL VM VN VNt VO VX Vc Vcs Vih Vmot.
  intros Hγ He Hx Hs. destruct (SubRel_nf _ _ _ _ _ He) as [Ne Ne'].
  destruct (elimIWi_loc Hγ) as (_ & _ & _ & _ & _ & _ & _ & VMγ & _).
  destruct (elimIWi_nf Hγ He) as (NX & NA & NN & ND & NO & NC & _).
  destruct (elimIWi_nf Hγ (SubRel_refl_r He)) as (NX' & NA' & NN' & ND' & NO' & NC' & _).
  rewrite <- (iwimotty_cons l lp li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ D⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧ e x Ne NX NA NN ND NO NC),
    <- (iwimotty_cons l lp li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ D⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧ e' x' Ne' NX' NA' NN' ND' NO' NC') in Hs.
  pose proof (VTy_refl_l VMγ _ _ _ (SubRel_cons (SubRel_cons He Hx) Hs)) as Y.
  now rewrite <- (lift_single2_ty e Ne), <- (lift_single2_ty e' Ne') in Y.
Qed.

(** [IWiRel] at canonical relations is the relation at [IWi]. *)
Lemma elimIWi_rel {G0 γ Δ0 e e'} {ix dm : DomRel G0 Δ0} {pd : IPosDomRel G0 Δ0} {x s s'} :
  gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' ->
  LRtm li G0 Δ0 (sX γ e) (sX γ e) x x -> elimIWi_kd G0 Δ0 ix dm pd γ e e' ->
  IWiRel G0 Δ0 l lp li (sX γ e) (sA γ e) (sN γ e) (sD γ e) (sO γ e) (sC γ e) ix dm pd x s s' ->
  LRtm L G0 Δ0 (tyL γ e x) (tyL γ e x) s s'.
Proof using EL Hwl Hwli Hwlp VA VC VD VL VM VN VNt VO VX Vc Vcs Vih Vmot.
  intros Hγ He Hx (HX & HA & Har & Hpd & HpdE) Hs. destruct (elimIWi_loc Hγ) as (VXγ & _).
  pose proof (LRtm_irrel_r Hx (VTy_refl_l (VTyG_loc VXγ) _ _ _ He)) as Hx'.
  destruct (elimIWi_WLR Hγ He Hx') as (ix0 & dm0 & pd0 & HW & _).
  pose proof (proj2 (LR_iwi_rel HW HX HA Har Hpd HpdE s s') Hs) as Y.
  destruct (elimIWi_WLR Hγ (SubRel_refl_l He) Hx) as (ix1 & dm1 & pd1 & HW1 & _).
  exact (LRtm_irrel_r (LRtm_of HW Y) (ex_intro _ _ HW1)).
Qed.

(** The elimination at related terms, from the elimination at their whnfs. *)
Lemma elimIWi_back {G0 γ Δ0 e e'} {ix dm : DomRel G0 Δ0} {pd : IPosDomRel G0 Δ0} {x x' s s' w w'} :
  gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' -> LRtm li G0 Δ0 (sX γ e) (sX γ e) x x' ->
  elimIWi_kd G0 Δ0 ix dm pd γ e e' ->
  IWiRel G0 Δ0 l lp li (sX γ e) (sA γ e) (sN γ e) (sD γ e) (sO γ e) (sC γ e) ix dm pd x s s' ->
  [ G0 ; Δ0 ⊢g s ⤳* w : tyL γ e x @ L ] -> [ G0 ; Δ0 ⊢g s' ⤳* w' : tyL γ e x @ L ] ->
  whnf w -> whnf w' ->
  LRtm l' G0 Δ0 (sM γ e)[lsingle2 x w] (sM γ e)[lsingle2 x w] (elL γ e x w) (elR γ e' x' w') ->
  LRtm l' G0 Δ0 (sM γ e)[lsingle2 x s] (sM γ e)[lsingle2 x s] (elL γ e x s) (elR γ e' x' s').
Proof using EL H13 H24 Hi3 Hp3 Hwl Hwl' Hwli Hwlp VA VC VD VL VM VN VNt VO VX Vc Vcs Vih Vmot.
  intros Hγ He Hxx HK Hss Hs Hs' Nw Nw' Y.
  pose proof (LRtm_trans Hxx (LRtm_sym Hxx)) as Hx.
  destruct (IWiRel_inv Hss) as (w0 & w0' & Hw0 & Hw0' & Ew & Nn).
  assert (w0 = w) as -> by (eapply tmred_whnf_det; [exact Hw0 | exact Hs | exact (IWiNf_whnf_l Nn) | exact Nw]).
  assert (w0' = w') as -> by (eapply tmred_whnf_det; [exact Hw0' | exact Hs' | exact (IWiNf_whnf_r Nn) | exact Nw']).
  pose proof (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hs)) as Hwt.
  pose proof (eqtm_wf_r ge_typeof (tmred_eq _ _ _ _ _ _ _ Hs')) as Hw't.
  assert (Rsw' : IWiRel G0 Δ0 l lp li (sX γ e) (sA γ e) (sN γ e) (sD γ e) (sO γ e) (sC γ e) ix dm pd x s w')
    by (eapply iwirel; [exact Hs | exact (tmred_refl _ _ _ Hw't) | exact Ew | exact Nn]).
  assert (Rww' : IWiRel G0 Δ0 l lp li (sX γ e) (sA γ e) (sN γ e) (sD γ e) (sO γ e) (sC γ e) ix dm pd x w w')
    by (eapply iwirel; [exact (tmred_refl _ _ _ Hwt) | exact (tmred_refl _ _ _ Hw't) | exact Ew | exact Nn]).
  pose proof (elimIWi_rel Hγ He Hx HK Rsw') as Xsw'. pose proof (elimIWi_rel Hγ He Hx HK Rww') as Xww'.
  pose proof (LRtm_trans Xsw' (LRtm_sym Xww')) as Xsw. pose proof (LRtm_trans Xsw (LRtm_sym Xsw)) as Xss.
  pose proof (elimIWi_mot Hγ (SubRel_refl_l He) Hx Xsw) as XT.
  pose proof (elimIWi_mot Hγ (SubRel_refl_l He) Hx Xss) as XTT.
  pose proof (LRtm_irrel_r (LRtm_conv_l Y XT) XTT) as Y2.
  pose proof (geq_tm_sound (LRtm_geq (elimIWi_rel Hγ He Hx HK Hss))) as Hss'.
  destruct (LRtm_escape Hxx) as [Hxt _]. pose proof (geq_tm_sound (LRtm_geq Hxx)) as Exx.
  exact (LRtm_red Y2 (elimIWi_red_l Hγ He Hxt Hs) (elimIWi_red_r Hγ He Exx Hss' Hs')).
Qed.

(** At a term reducing to a neutral, the elimination is neutral. *)
Lemma elimIWi_ne {G0 γ Δ0 e e'} {ix dm : DomRel G0 Δ0} {pd : IPosDomRel G0 Δ0} {x x' s s' ν} :
  gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' -> LRtm li G0 Δ0 (sX γ e) (sX γ e) x x' ->
  elimIWi_kd G0 Δ0 ix dm pd γ e e' ->
  IWiRel G0 Δ0 l lp li (sX γ e) (sA γ e) (sN γ e) (sD γ e) (sO γ e) (sC γ e) ix dm pd x s s' ->
  reds s ν -> whne ν ->
  LRtm l' G0 Δ0 (sM γ e)[lsingle2 x s] (sM γ e)[lsingle2 x s] (elL γ e x s) (elR γ e' x' s').
Proof using EL H13 H24 Hi3 Hp3 Hwl Hwl' Hwli Hwlp VA VC VD VL VM VN VNt VO VX Vc Vcs Vih Vmot.
  intros Hγ He Hxx HK Hss Hsν Nν.
  pose proof (LRtm_trans Hxx (LRtm_sym Hxx)) as Hx.
  destruct (IWiRel_inv Hss) as (w & w' & Hw & Hw' & Ew & Nn).
  assert (w = ν) as ->.
  { eapply reds_whnf_det; [exact (tmred_red _ _ _ _ _ _ _ Hw) | exact Hsν | exact (IWiNf_whnf_l Nn)
                          | now apply whnf_ne]. }
  pose proof (IWiNf_ne_inv Nν Nn) as Hne.
  destruct (elimIWi_at Hγ He) as (HX0 & EX & HA0 & EA & HN0 & EN & HD0 & ED & HO0 & EO & HC0 & EC & HMot0 & HM0
                                  & EM & Hcs0 & HI0 & EI & Ec).
  pose proof (gne_tm_elimIWi (lequiv_weaken _ _ _ _ (proj1 Hγ) H13) (lequiv_weaken _ _ _ _ (proj1 Hγ) Hp3)
                (lequiv_weaken _ _ _ _ (proj1 Hγ) Hi3) (lequiv_weaken _ _ _ _ (proj1 Hγ) H24)
                HX0 EX HA0 EA HN0 EN HD0 ED HO0 EO HC0 EC HM0 EM EI Ec (LRtm_geq Hxx) Hne) as HE.
  pose proof (gne_tm_refl_l Hne) as Hνν.
  pose proof (eqtm_wf_l ge_typeof (geq_tm_sound (gne_tm_geq Hνν))) as Hνt.
  assert (Rνν : IWiRel G0 Δ0 l lp li (sX γ e) (sA γ e) (sN γ e) (sD γ e) (sO γ e) (sC γ e) ix dm pd x ν ν).
  { eapply iwirel; [exact (tmred_refl _ _ _ Hνt) | exact (tmred_refl _ _ _ Hνt) | exact (gne_tm_geq Hνν) |].
    apply iwinf_ne, Hνν. }
  destruct (elimIWi_mot Hγ (SubRel_refl_l He) Hx (elimIWi_rel Hγ He Hx HK Rνν)) as [RL HRL].
  eapply elimIWi_back; [exact Hγ | exact He | exact Hxx | exact HK | exact Hss | exact Hw | exact Hw'
                       | now apply whnf_ne | exact (IWiNf_whnf_r Nn) |].
  exact (LRtm_of HRL (LR_neutral _ _ _ _ _ _ _ HRL _ _ HE HE)).
Qed.

(** The signature at a related substitution, with its generic reflexivity. *)
Lemma elimIWi_sig {G0 γ Δ0 e e'} : gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' ->
  IWiEq (G := G0) (i := ge_layer) Δ0 l lp li l lp li (sX γ e) (sX γ e) (sA γ e) (sA γ e) (sN γ e) (sN γ e)
    (sD γ e) (sD γ e) (sO γ e) (sO γ e) (sC γ e) (sC γ e) /\
  IWiGeq G0 Δ0 l lp li (sX γ e) (sX γ e) (sA γ e) (sA γ e) (sN γ e) (sN γ e) (sD γ e) (sD γ e)
    (sO γ e) (sO γ e) (sC γ e) (sC γ e).
Proof using EL Hwl Hwl' Hwli Hwlp VA VC VD VL VM VN VNt VO VX Vc Vcs Vih Vmot.
  intros Hγ He.
  destruct (elimIWi_at Hγ He) as (HX0 & EX & HA0 & EA & HN0 & EN & HD0 & ED & HO0 & EO & HC0 & EC & _).
  pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwl) as Hwl0. pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwli) as Hwli0.
  pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwlp) as Hwlp0.
  split.
  - apply IWiEq_intro; first [apply lequiv_refl; assumption | apply eqty_refl; assumption
                             | apply eqtm_refl; assumption | assumption].
  - refine (conj (geq_ty_trans EX (geq_ty_sym EX)) (conj (geq_ty_trans EA (geq_ty_sym EA))
              (conj (geq_tm_trans EN (geq_tm_sym EN)) (conj (geq_ty_trans ED (geq_ty_sym ED))
                (conj (geq_tm_trans EO (geq_tm_sym EO)) (geq_tm_trans EC (geq_tm_sym EC))))))).
Qed.

(** ** The core: related eliminations at related trees *)

(** The eliminations at two indices and terms, after a global weakening
    and at a related substitution, related at the motive. *)
Definition elimIWi_goal G0 Δ0 γ e e' x x' s s' : Prop :=
  LRtm l' G0 Δ0 (sM γ e)[lsingle2 x s] (sM γ e)[lsingle2 x s] (elL γ e x s) (elR γ e' x' s').

(** The relation's indices are the premises' at a global weakening and a
    related substitution, and its relations are canonical. *)
Definition elimIWi_hyp G0 Δ0 k1 kp1 ki1 X0 A0 N0 D0 O0 C0 (ix dm : DomRel G0 Δ0) (pd : IPosDomRel G0 Δ0)
    γ e e' : Prop :=
  gwk_ok γ G0 G /\ SubRel G0 Γ⟦γ⟧ Δ0 e e' /\ k1 = l /\ kp1 = lp /\ ki1 = li /\ X0 = sX γ e /\ A0 = sA γ e /\
  N0 = sN γ e /\ D0 = sD γ e /\ O0 = sO γ e /\ C0 = sC γ e /\ elimIWi_kd G0 Δ0 ix dm pd γ e e'.

(** The motive at a tree, whatever its index. *)
Definition elimIWi_mrel G0 Δ0 k1 kp1 ki1 X0 A0 N0 D0 O0 C0 (ix dm : DomRel G0 Δ0) (pd : IPosDomRel G0 Δ0)
    (t t' : tm) : Prop :=
  forall γ e e', elimIWi_hyp G0 Δ0 k1 kp1 ki1 X0 A0 N0 D0 O0 C0 ix dm pd γ e e' ->
  forall x x', LRtm li G0 Δ0 X0 X0 x x' ->
  forall s s', IWiRel G0 Δ0 l lp li X0 A0 N0 D0 O0 C0 ix dm pd x s s' -> Join s t -> Join s' t' ->
  elimIWi_goal G0 Δ0 γ e e' x x' s s'.

(** The motive at a spine, at a domain family and a family of child
    indices well formed and generically reflexive at related positions:
    at tuples joinable with it, related indices of [Fin] and arguments
    related by [yR] at every canonical position the index is related to,
    with annotations equivalent to the field's there, any two terms
    related at [IWi] reducing to the applications of [dnth]'s states to
    the arguments have related eliminations. *)
Definition elimIWi_mspine G0 Δ0 k1 kp1 ki1 X0 A0 N0 D0 O0 C0 (ix dm : DomRel G0 Δ0) (pd : IPosDomRel G0 Δ0)
    (yR : tm -> tm -> tm -> Prop) (d : ty) (cf k cs cs' : tm) : Prop :=
  forall γ e e', elimIWi_hyp G0 Δ0 k1 kp1 ki1 X0 A0 N0 D0 O0 C0 ix dm pd γ e e' ->
  [ G0 ; Δ0 ,, tyFin k @ lzero ⊢g iwiFamT l lp li X0 A0 N0 D0 O0 C0 d cf @ L ] ->
  IWiPosGeq G0 Δ0 lp li X0 k k d d cf cf ->
  forall c0 c0', nftm c0 -> nftm c0' -> TC c0 cs -> TC c0' cs' ->
  forall k' i i', NatRel G0 Δ0 k k' -> LRtm lzero G0 Δ0 (tyFin k) (tyFin k') i i' ->
  forall e1 e1' u u', nftm e1 -> nftm e1' -> DNat k e1 c0 i u -> DNat k' e1' c0' i' u' ->
  forall y y' la2 lb2 A3 B3 la2' lb2' A3' B3',
  lequiv (gL G0) la2 lp -> lequiv (gL G0) lb2 L -> lequiv (gL G0) la2' lp -> lequiv (gL G0) lb2' L ->
  (forall p p', PosCan G0 Δ0 k k' p p' -> LRtm lzero G0 Δ0 (tyFin k) (tyFin k') i p ->
     yR p y y' /\ [ G0 ; Δ0 ⊢ d[lsingle p] ≈ A3 @ lp ] /\
     [ G0 ; Δ0 ,, d[lsingle p] @ lp ⊢ (iwiFamCodT l lp li X0 A0 N0 D0 O0 C0 cf)[llift (lsingle p)] ≈ B3 @ L ] /\
     [ G0 ; Δ0 ⊢ d[lsingle p] ≈ A3' @ lp ] /\
     [ G0 ; Δ0 ,, d[lsingle p] @ lp ⊢ (iwiFamCodT l lp li X0 A0 N0 D0 O0 C0 cf)[llift (lsingle p)] ≈ B3' @ L ]) ->
  forall x x' s s', LRtm li G0 Δ0 X0 X0 x x' -> IWiRel G0 Δ0 l lp li X0 A0 N0 D0 O0 C0 ix dm pd x s s' ->
  reds s (app u la2 lb2 A3 B3 y) -> reds s' (app u' la2' lb2' A3' B3' y') -> elimIWi_goal G0 Δ0 γ e e' x x' s s'.

Lemma elimIWi_c_rel {G0 Δ0 k1 kp1 ki1 X0 A0 N0 D0 O0 C0} {ix dm : DomRel G0 Δ0} {pd : IPosDomRel G0 Δ0}
    {m t t' w w'} :
  [ G0 ; Δ0 ⊢g t ⤳* w : tyIWi k1 kp1 ki1 X0 A0 N0 D0 O0 C0 m @ iwiL k1 kp1 ki1 ] ->
  [ G0 ; Δ0 ⊢g t' ⤳* w' : tyIWi k1 kp1 ki1 X0 A0 N0 D0 O0 C0 m @ iwiL k1 kp1 ki1 ] ->
  IWiNf G0 Δ0 k1 kp1 ki1 X0 A0 N0 D0 O0 C0 ix dm pd m w w' ->
  elimIWi_mrel G0 Δ0 k1 kp1 ki1 X0 A0 N0 D0 O0 C0 ix dm pd w w' ->
  elimIWi_mrel G0 Δ0 k1 kp1 ki1 X0 A0 N0 D0 O0 C0 ix dm pd t t'.
Proof using EL.
  intros Hw Hw' Nn IH γ e e' Hh x x' Hx s s' Hss Js Js'. apply (IH γ e e' Hh x x' Hx s s' Hss).
  - exact (join_red _ _ _ Js (tmred_red _ _ _ _ _ _ _ Hw) (IWiNf_whnf_l Nn)).
  - exact (join_red _ _ _ Js' (tmred_red _ _ _ _ _ _ _ Hw') (IWiNf_whnf_r Nn)).
Qed.

Lemma elimIWi_c_ne {G0 Δ0 k1 kp1 ki1 X0 A0 N0 D0 O0 C0} {ix dm : DomRel G0 Δ0} {pd : IPosDomRel G0 Δ0} {m ν ν'} :
  [ G0 ; Δ0 ⊢ ν ~ ν' : tyIWi k1 kp1 ki1 X0 A0 N0 D0 O0 C0 m @ iwiL k1 kp1 ki1 ] ->
  elimIWi_mrel G0 Δ0 k1 kp1 ki1 X0 A0 N0 D0 O0 C0 ix dm pd ν ν'.
Proof using EL H13 H24 Hi3 Hp3 Hwl Hwl' Hwli Hwlp VA VC VD VL VM VN VNt VO VX Vc Vcs Vih Vmot.
  intros Hν γ e e' (Hγ & He & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & HK) x x' Hx s s' Hss Js _.
  subst k1 kp1 ki1 X0 A0 N0 D0 O0 C0.
  destruct (join_ne _ _ Js (gne_tm_whne_l Hν)) as (X1 & HX1 & NX1).
  exact (elimIWi_ne Hγ He Hx HK Hss HX1 NX1).
Qed.

(** At a neutral state of [dnth], the application is neutral. *)
Lemma elimIWi_app_ne {G0 Δ0 k1 kp1 ki1 X0 A0 N0 D0 O0 C0} {ix dm : DomRel G0 Δ0} {pd : IPosDomRel G0 Δ0}
    {γ e e' x x' s s' u la2 lb2 A3 B3 y ν} :
  elimIWi_hyp G0 Δ0 k1 kp1 ki1 X0 A0 N0 D0 O0 C0 ix dm pd γ e e' -> LRtm li G0 Δ0 X0 X0 x x' ->
  IWiRel G0 Δ0 l lp li X0 A0 N0 D0 O0 C0 ix dm pd x s s' ->
  reds s (app u la2 lb2 A3 B3 y) -> reds u ν -> whne ν -> elimIWi_goal G0 Δ0 γ e e' x x' s s'.
Proof using EL H13 H24 Hi3 Hp3 Hwl Hwl' Hwli Hwlp VA VC VD VL VM VN VNt VO VX Vc Vcs Vih Vmot.
  intros (Hγ & He & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & HK) Hx Hss Hs Hu Nν.
  subst k1 kp1 ki1 X0 A0 N0 D0 O0 C0.
  exact (elimIWi_ne Hγ He Hx HK Hss (reds_trans _ _ _ Hs (reds_app _ _ _ _ _ _ _ Hu)) (whne_app _ _ _ _ _ _ Nν)).
Qed.

Lemma elimIWi_c_zero {G0 Δ0 k1 kp1 ki1 X0 A0 N0 D0 O0 C0} {ix dm : DomRel G0 Δ0} {pd : IPosDomRel G0 Δ0}
    {yR d cf k cs cs'} :
  [ G0 ; Δ0 ⊢g k ⤳* zero : tyNat @ lzero ] ->
  elimIWi_mspine G0 Δ0 k1 kp1 ki1 X0 A0 N0 D0 O0 C0 ix dm pd yR d cf k cs cs'.
Proof using EL H13 H24 Hi3 Hp3 Hwl Hwl' Hwli Hwlp VA VC VD VL VM VN VNt VO VX Vc Vcs Vih Vmot.
  intros Hk γ e e' Hh _ _ c0 c0' _ _ _ _ k' i i' _ Hi e1 e1' u u' _ _ Du _ y y' la2 lb2 A3 B3 la2' lb2' A3' B3'
    _ _ _ _ _ x x' s s' Hx Hss Hs _.
  destruct (fin_idx_zero Hi Hk) as (ν & Hiν & Nν).
  destruct (dn_zero (tmred_red _ _ _ _ _ _ _ Hk) Hiν Nν Du) as (X1 & HX1 & NX1).
  exact (elimIWi_app_ne Hh Hx Hss Hs HX1 NX1).
Qed.

Lemma elimIWi_c_vne {G0 Δ0 k1 kp1 ki1 X0 A0 N0 D0 O0 C0} {ix dm : DomRel G0 Δ0} {pd : IPosDomRel G0 Δ0}
    {yR d cf k ν cs cs'} :
  [ G0 ; Δ0 ⊢g k ⤳* ν : tyNat @ lzero ] -> [ G0 ; Δ0 ⊢ ν ~ ν : tyNat @ lzero ] ->
  elimIWi_mspine G0 Δ0 k1 kp1 ki1 X0 A0 N0 D0 O0 C0 ix dm pd yR d cf k cs cs'.
Proof using EL H13 H24 Hi3 Hp3 Hwl Hwl' Hwli Hwlp VA VC VD VL VM VN VNt VO VX Vc Vcs Vih Vmot.
  intros Hk Hν γ e e' Hh _ _ c0 c0' _ _ _ _ k' i i' _ _ e1 e1' u u' _ _ Du _ y y' la2 lb2 A3 B3 la2' lb2' A3' B3'
    _ _ _ _ _ x x' s s' Hx Hss Hs _.
  destruct (dn_ne (tmred_red _ _ _ _ _ _ _ Hk) (gne_tm_whne_l Hν) Du) as (X1 & HX1 & NX1).
  exact (elimIWi_app_ne Hh Hx Hss Hs HX1 NX1).
Qed.

Lemma elimIWi_c_succ {G0 Δ0 k1 kp1 ki1 X0 A0 N0 D0 O0 C0} {ix dm : DomRel G0 Δ0} {pd : IPosDomRel G0 Δ0}
    {yR d cf k m cs cs' w w'} :
  [ G0 ; Δ0 ⊢g k ⤳* succ m : tyNat @ lzero ] ->
  [ G0 ; Δ0 ⊢g cs ⤳* w : tySig (iwiL k1 kp1 ki1) (iwiL k1 kp1 ki1)
                          (dvecHd m (iwiFamT k1 kp1 ki1 X0 A0 N0 D0 O0 C0 d cf))
                          (dvecTl (iwiL k1 kp1 ki1) m (iwiFamT k1 kp1 ki1 X0 A0 N0 D0 O0 C0 d cf))
                          @ lmax (iwiL k1 kp1 ki1) (iwiL k1 kp1 ki1) ] ->
  [ G0 ; Δ0 ⊢g cs' ⤳* w' : tySig (iwiL k1 kp1 ki1) (iwiL k1 kp1 ki1)
                          (dvecHd m (iwiFamT k1 kp1 ki1 X0 A0 N0 D0 O0 C0 d cf))
                          (dvecTl (iwiL k1 kp1 ki1) m (iwiFamT k1 kp1 ki1 X0 A0 N0 D0 O0 C0 d cf))
                          @ lmax (iwiL k1 kp1 ki1) (iwiL k1 kp1 ki1) ] ->
  whnf w -> whnf w' ->
  (forall la lb A2 B2 la' lb' A2' B2',
     lequiv (gL G0) la (iwiL k1 kp1 ki1) -> lequiv (gL G0) lb (iwiL k1 kp1 ki1) ->
     lequiv (gL G0) la' (iwiL k1 kp1 ki1) -> lequiv (gL G0) lb' (iwiL k1 kp1 ki1) ->
     [ G0 ; Δ0 ⊢ dvecHd m (iwiFamT k1 kp1 ki1 X0 A0 N0 D0 O0 C0 d cf) ≈ A2 @ iwiL k1 kp1 ki1 ] ->
     [ G0 ; Δ0 ,, dvecHd m (iwiFamT k1 kp1 ki1 X0 A0 N0 D0 O0 C0 d cf) @ iwiL k1 kp1 ki1
         ⊢ dvecTl (iwiL k1 kp1 ki1) m (iwiFamT k1 kp1 ki1 X0 A0 N0 D0 O0 C0 d cf) ≈ B2 @ iwiL k1 kp1 ki1 ] ->
     [ G0 ; Δ0 ⊢ dvecHd m (iwiFamT k1 kp1 ki1 X0 A0 N0 D0 O0 C0 d cf) ≈ A2' @ iwiL k1 kp1 ki1 ] ->
     [ G0 ; Δ0 ,, dvecHd m (iwiFamT k1 kp1 ki1 X0 A0 N0 D0 O0 C0 d cf) @ iwiL k1 kp1 ki1
         ⊢ dvecTl (iwiL k1 kp1 ki1) m (iwiFamT k1 kp1 ki1 X0 A0 N0 D0 O0 C0 d cf) ≈ B2' @ iwiL k1 kp1 ki1 ] ->
     WhRel G0 Δ0 (dvecHd m (iwiFamT k1 kp1 ki1 X0 A0 N0 D0 O0 C0 d cf)) (iwiL k1 kp1 ki1)
       (tmFst la lb A2 B2 w) (tmFst la' lb' A2' B2' w')) ->
  (forall la lb A2 B2 la' lb' A2' B2',
     lequiv (gL G0) la (iwiL k1 kp1 ki1) -> lequiv (gL G0) lb (iwiL k1 kp1 ki1) ->
     lequiv (gL G0) la' (iwiL k1 kp1 ki1) -> lequiv (gL G0) lb' (iwiL k1 kp1 ki1) ->
     [ G0 ; Δ0 ⊢ dvecHd m (iwiFamT k1 kp1 ki1 X0 A0 N0 D0 O0 C0 d cf) ≈ A2 @ iwiL k1 kp1 ki1 ] ->
     [ G0 ; Δ0 ,, dvecHd m (iwiFamT k1 kp1 ki1 X0 A0 N0 D0 O0 C0 d cf) @ iwiL k1 kp1 ki1
         ⊢ dvecTl (iwiL k1 kp1 ki1) m (iwiFamT k1 kp1 ki1 X0 A0 N0 D0 O0 C0 d cf) ≈ B2 @ iwiL k1 kp1 ki1 ] ->
     [ G0 ; Δ0 ⊢ dvecHd m (iwiFamT k1 kp1 ki1 X0 A0 N0 D0 O0 C0 d cf) ≈ A2' @ iwiL k1 kp1 ki1 ] ->
     [ G0 ; Δ0 ,, dvecHd m (iwiFamT k1 kp1 ki1 X0 A0 N0 D0 O0 C0 d cf) @ iwiL k1 kp1 ki1
         ⊢ dvecTl (iwiL k1 kp1 ki1) m (iwiFamT k1 kp1 ki1 X0 A0 N0 D0 O0 C0 d cf) ≈ B2' @ iwiL k1 kp1 ki1 ] ->
     forall y y', yR (posHd m) y y' ->
     forall la2 lb2 A3 B3 la2' lb2' A3' B3',
     lequiv (gL G0) la2 kp1 -> lequiv (gL G0) lb2 (iwiL k1 kp1 ki1) ->
     lequiv (gL G0) la2' kp1 -> lequiv (gL G0) lb2' (iwiL k1 kp1 ki1) ->
     [ G0 ; Δ0 ⊢ d[lsingle (posHd m)] ≈ A3 @ kp1 ] ->
     [ G0 ; Δ0 ,, d[lsingle (posHd m)] @ kp1
         ⊢ (iwiFamCodT k1 kp1 ki1 X0 A0 N0 D0 O0 C0 cf)[llift (lsingle (posHd m))] ≈ B3 @ iwiL k1 kp1 ki1 ] ->
     [ G0 ; Δ0 ⊢ d[lsingle (posHd m)] ≈ A3' @ kp1 ] ->
     [ G0 ; Δ0 ,, d[lsingle (posHd m)] @ kp1
         ⊢ (iwiFamCodT k1 kp1 ki1 X0 A0 N0 D0 O0 C0 cf)[llift (lsingle (posHd m))] ≈ B3' @ iwiL k1 kp1 ki1 ] ->
     elimIWi_mrel G0 Δ0 k1 kp1 ki1 X0 A0 N0 D0 O0 C0 ix dm pd
       (app (tmFst la lb A2 B2 w) la2 lb2 A3 B3 y) (app (tmFst la' lb' A2' B2' w') la2' lb2' A3' B3' y')) ->
  (forall la lb A2 B2 la' lb' A2' B2',
     lequiv (gL G0) la (iwiL k1 kp1 ki1) -> lequiv (gL G0) lb (iwiL k1 kp1 ki1) ->
     lequiv (gL G0) la' (iwiL k1 kp1 ki1) -> lequiv (gL G0) lb' (iwiL k1 kp1 ki1) ->
     [ G0 ; Δ0 ⊢ dvecHd m (iwiFamT k1 kp1 ki1 X0 A0 N0 D0 O0 C0 d cf) ≈ A2 @ iwiL k1 kp1 ki1 ] ->
     [ G0 ; Δ0 ,, dvecHd m (iwiFamT k1 kp1 ki1 X0 A0 N0 D0 O0 C0 d cf) @ iwiL k1 kp1 ki1
         ⊢ dvecTl (iwiL k1 kp1 ki1) m (iwiFamT k1 kp1 ki1 X0 A0 N0 D0 O0 C0 d cf) ≈ B2 @ iwiL k1 kp1 ki1 ] ->
     [ G0 ; Δ0 ⊢ dvecHd m (iwiFamT k1 kp1 ki1 X0 A0 N0 D0 O0 C0 d cf) ≈ A2' @ iwiL k1 kp1 ki1 ] ->
     [ G0 ; Δ0 ,, dvecHd m (iwiFamT k1 kp1 ki1 X0 A0 N0 D0 O0 C0 d cf) @ iwiL k1 kp1 ki1
         ⊢ dvecTl (iwiL k1 kp1 ki1) m (iwiFamT k1 kp1 ki1 X0 A0 N0 D0 O0 C0 d cf) ≈ B2' @ iwiL k1 kp1 ki1 ] ->
     elimIWi_mspine G0 Δ0 k1 kp1 ki1 X0 A0 N0 D0 O0 C0 ix dm pd (fun p => yR (posTl m p)) (posMvT m d)
       (posMv2 m cf) m (tmSnd la lb A2 B2 w) (tmSnd la' lb' A2' B2' w')) ->
  elimIWi_mspine G0 Δ0 k1 kp1 ki1 X0 A0 N0 D0 O0 C0 ix dm pd yR d cf k cs cs'.
Proof using EL H13 H24 Hi3 Hp3 Hwl Hwl' Hwli Hwlp VA VC VD VL VM VN VNt VO VX Vc Vcs Vih Vmot.
  intros Hk Hcs Hcs' Nw Nw' Hwh IHf IHs γ e e' Hh HF HP c0 c0' Nc0 Nc0' Tc Tc' k' i i' Hkk Hi
    e1 e1' u u' Ne1 Ne1' Du Du' y y' la2 lb2 A3 B3 la2' lb2' A3' B3' H3 H4 H3' H4' HY x x' s s' Hx Hss Hs Hs'.
  pose proof Hh as (Hγ & He & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & HK).
  subst k1 kp1 ki1 X0 A0 N0 D0 O0 C0.
  destruct (elimIWi_nf Hγ He) as (NX & NA & NN & ND & NO & NC & _).
  pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwl) as Hwl0. pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwli) as Hwli0.
  pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwlp) as Hwlp0.
  assert (HwL : lwf (gL G0) L) by (split; [split|]; assumption).
  pose proof (lequiv_refl _ _ HwL) as HLL.
  destruct (NatRel_inv_succ Hkk Hk) as (m' & Hk' & Hmm).
  destruct (NatRel_escape Hmm) as (Hm & Hm' & _). pose proof (wf_tm_nf Hm) as Nm. pose proof (wf_tm_nf Hm') as Nm'.
  destruct (LRtm_escape Hi) as [Hit Hi't]. pose proof (wf_tm_nf Hit) as Ni. pose proof (wf_tm_nf Hi't) as Ni'.
  pose proof (ctx_of_tm Hm) as HΔ0.
  (* the canonical annotations *)
  destruct (elimIWi_sig Hγ He) as [HE HG].
  pose proof (fin_stab_ty' (tmred_eq _ _ _ _ _ _ _ Hk) HF) as HF1.
  destruct (iwi_succ_geq HE HG Hk Hk (NatRel_refl_l _ _ _ _ Hmm) (eqty_refl _ _ _ _ _ HF) HP) as [Ghd Gtl].
  pose proof (tyred_dvec_succ HwL HF1 Hm) as HDs.
  destruct (inv_ty_sig (eqty_wf_r ge_typeof (tyred_eq _ _ _ _ _ _ HDs))) as ((_ & _ & _ & Hhd & _) & _).
  pose proof (Gtl _ _ (ext_wf_g Hhd HwL)) as Gtl'.
  (* the tuples are pairs or neutral: their heads reach whnfs *)
  destruct (Hwh _ _ _ _ _ _ _ _ HLL HLL HLL HLL Ghd Gtl' Ghd Gtl') as (v & v' & Hv & Hv' & Nv & Nv' & _).
  assert (Pw : PairOrNe w) by exact (fst_cases _ _ _ _ _ _ Nw (tmred_red _ _ _ _ _ _ _ Hv) Nv).
  assert (Pw' : PairOrNe w') by exact (fst_cases _ _ _ _ _ _ Nw' (tmred_red _ _ _ _ _ _ _ Hv') Nv').
  destruct (fin_idx_succ Hi Hk Hmm)
    as [(k2 & k3 & C1 & D1 & u0 & k2' & k3' & C1' & D1' & u0' & Hi1 & Hi1')
       |[(k2 & k3 & C1 & D1 & j & k2' & k3' & C1' & D1' & j' & Hi1 & Hi1' & Hjj) | (ν & Hiν & Nν)]].
  - (* [inl]: the head, applied *)
    destruct (dn_inl Nm Ne1 Nc0 Ni (tmred_red _ _ _ _ _ _ _ Hk) Hi1 Du) as (L1 & A1 & B1 & Hu).
    destruct (dn_inl Nm' Ne1' Nc0' Ni' (tmred_red _ _ _ _ _ _ _ Hk') Hi1' Du') as (L1' & A1' & B1' & Hu').
    pose proof (fin_pos_hd Hi Hk Hkk Hi1) as Xih.
    destruct (HY _ _ (pc_hd _ _ _ _ _ _ Hk Hk' Hmm) Xih) as (Hy & HA3 & HB3 & HA3' & HB3').
    apply (IHf _ _ _ _ _ _ _ _ HLL HLL HLL HLL Ghd Gtl' Ghd Gtl' y y' Hy _ _ _ _ _ _ _ _ H3 H4 H3' H4'
             HA3 HB3 HA3' HB3' γ e e' Hh x x' Hx s s' Hss).
    + eapply join_reds_l; [exact (reds_trans _ _ _ Hs (reds_app _ _ _ _ _ _ _ Hu))|].
      apply join_app. exact (join_fst _ _ _ _ _ _ _ _ _ _ _ Tc (tmred_red _ _ _ _ _ _ _ Hcs) Nw Pw).
    + eapply join_reds_l; [exact (reds_trans _ _ _ Hs' (reds_app _ _ _ _ _ _ _ Hu'))|].
      apply join_app. exact (join_fst _ _ _ _ _ _ _ _ _ _ _ Tc' (tmred_red _ _ _ _ _ _ _ Hcs') Nw' Pw').
  - (* [inr]: [dnth] at the tails, along the moved families *)
    pose proof (wf_tm_nf (proj1 (LRtm_escape Hjj))) as Nj. pose proof (wf_tm_nf (proj2 (LRtm_escape Hjj))) as Nj'.
    destruct (dn_inr Nm Ne1 Nc0 Ni Nj (tmred_red _ _ _ _ _ _ _ Hk) Hi1 Du)
      as (e2 & L1 & A1 & B1 & u2 & Ne2 & Nsnd & Du2 & Hu2).
    destruct (dn_inr Nm' Ne1' Nc0' Ni' Nj' (tmred_red _ _ _ _ _ _ _ Hk') Hi1' Du')
      as (e2' & L1' & A1' & B1' & u2' & Ne2' & Nsnd' & Du2' & Hu2').
    assert (HFmv : [ G0 ; Δ0 ,, tyFin m @ lzero
                     ⊢g iwiFamT l lp li (sX γ e) (sA γ e) (sN γ e) (sD γ e) (sO γ e) (sC γ e)
                          (posMvT m d) (posMv2 m cf) @ L ]).
    { rewrite <- iwiFamT_mv. exact (dvecMv_wf ge_typeof ge_notV ge_compt Hm HF1). }
    pose proof (LR_fin_nat HΔ0 (NatRel_refl_l _ _ _ _ Hmm)) as LFm.
    assert (HY' : forall p p', PosCan G0 Δ0 m m' p p' -> LRtm lzero G0 Δ0 (tyFin m) (tyFin m') j p ->
              yR (posTl m p) y y' /\ [ G0 ; Δ0 ⊢ (posMvT m d)[lsingle p] ≈ A3 @ lp ] /\
              [ G0 ; Δ0 ,, (posMvT m d)[lsingle p] @ lp
                  ⊢ (iwiFamCodT l lp li (sX γ e) (sA γ e) (sN γ e) (sD γ e) (sO γ e) (sC γ e) (posMv2 m cf))
                      [llift (lsingle p)] ≈ B3 @ L ] /\
              [ G0 ; Δ0 ⊢ (posMvT m d)[lsingle p] ≈ A3' @ lp ] /\
              [ G0 ; Δ0 ,, (posMvT m d)[lsingle p] @ lp
                  ⊢ (iwiFamCodT l lp li (sX γ e) (sA γ e) (sN γ e) (sD γ e) (sO γ e) (sC γ e) (posMv2 m cf))
                      [llift (lsingle p)] ≈ B3' @ L ]).
    { intros p p' Hpc Xjp.
      rewrite posMvT_single, !iwiFamCodT_single, posMv2_single, <- iwiFamCodT_single by assumption.
      apply (HY _ (posTl m' p')); [exact (pc_tl _ _ _ _ _ _ _ _ Hk Hk' Hpc)|].
      exact (fin_pos_tl Hi Hk Hkk Hi1 (LRtm_irrel_r Xjp LFm)). }
    apply (IHs _ _ _ _ _ _ _ _ HLL HLL HLL HLL Ghd Gtl' Ghd Gtl' γ e e' Hh HFmv (IWiPosGeq_tl HP Hk Hk) _ _
             Nsnd Nsnd'
             (tc_snd _ _ _ _ _ _ _ _ _ _ _ Tc (tmred_red _ _ _ _ _ _ _ Hcs) Nw Pw)
             (tc_snd _ _ _ _ _ _ _ _ _ _ _ Tc' (tmred_red _ _ _ _ _ _ _ Hcs') Nw' Pw')
             m' j j' Hmm Hjj _ _ _ _ Ne2 Ne2' Du2 Du2' y y' _ _ _ _ _ _ _ _ H3 H4 H3' H4' HY' x x' s s' Hx Hss).
    + exact (reds_trans _ _ _ Hs (reds_app _ _ _ _ _ _ _ Hu2)).
    + exact (reds_trans _ _ _ Hs' (reds_app _ _ _ _ _ _ _ Hu2')).
  - (* a neutral index *)
    destruct (dn_case_ne Nm Ne1 Nc0 Ni (tmred_red _ _ _ _ _ _ _ Hk) Hiν Nν Du) as (X1 & HX1 & NX1).
    exact (elimIWi_app_ne Hh Hx Hss Hs HX1 NX1).
Qed.

(** ** The step at a [sup_ii] *)

(** A child index in a world, at related shapes, positions and domain
    elements. *)
Lemma elimIWi_ci_kw {G0 γ Δ0 e e2 Cr} (ρ : kwk G0 Δ0) {b b' i i' y y'} :
  gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e2 ->
  VTmG G0 (Γ⟦γ⟧ ,, A⟦γ⟧ @ l ,, tyFin N⟦γ⟧ @ lzero ,, D⟦γ⟧ @ lp) C⟦γ⟧ Cr X⟦γ⟧⟨↑⟩⟨↑⟩⟨↑⟩ li ->
  LRtm l (kw_G ρ) (kw_Δ ρ) (kty ρ (sA γ e)) (kty ρ (sA γ e2)) b b' ->
  LRtm lzero (kw_G ρ) (kw_Δ ρ) (tyFin (ktml ρ (sN γ e))[lsingle b]) (tyFin (ktml ρ (sN γ e2))[lsingle b']) i i' ->
  LRtm lp (kw_G ρ) (kw_Δ ρ) (ktyll ρ (sD γ e))[lsingle2 b i] (ktyll ρ (sD γ e2))[lsingle2 b' i'] y y' ->
  LRtm li (kw_G ρ) (kw_Δ ρ) (kty ρ (sX γ e)) (kty ρ (sX γ e))
    (ktmlll ρ (sC γ e))[lsingle3 b i y] (ktmlll ρ Cr[llift (llift (llift e2))])[lsingle3 b' i' y'].
Proof using EL VA VC VD VL VM VN VNt VO VX Vc Vcs Vih Vmot.
  intros Hγ He VCr Hb Hi Hy.
  destruct (elimIWi_loc Hγ) as (VXγ & _).
  destruct (SubRel_nf _ _ _ _ _ He) as [Ne Ne2].
  pose proof (SubRel_kw _ _ _ ρ _ _ He) as Heρ.
  rewrite !kty_subst in Hb. rewrite !ktml_subst_single in Hi.
  rewrite (ktyll_subst_single2 ρ e Ne), (ktyll_subst_single2 ρ e2 Ne2) in Hy.
  assert (Hi' : LRtm lzero (kw_G ρ) (kw_Δ ρ) (tyFin N⟦γ⟧⟦kw_γ ρ⟧)[lcons (kwsub ρ e) b]
                  (tyFin N⟦γ⟧⟦kw_γ ρ⟧)[lcons (kwsub ρ e2) b'] i i') by (rewrite !subst_tyFin; exact Hi).
  pose proof (VCr _ _ (kw_gok ρ)) as VCρ. rewrite !gwa_cext, gwa_tyFin, !gwa_ren_ty in VCρ.
  pose proof (VCρ _ _ _ (SubRel_cons (SubRel_cons (SubRel_cons Heρ Hb) Hi') Hy)) as Y.
  rewrite (ktmlll_subst_single3 ρ e Ne), (ktmlll_subst_single3 ρ e2 Ne2).
  rewrite !shift_cons_ty, <- !kty_subst in Y.
  eapply LRtm_irrel_r; [exact Y | exact (VTyG_kw ρ (VTyG_refl_l VXγ) (SubRel_refl_l He))].
Qed.

(** The signatures at the two sides of a related substitution, with
    their generic equality. *)
Lemma elimIWi_sig2 {G0 γ Δ0 e e'} : gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' ->
  IWiEq (G := G0) (i := ge_layer) Δ0 l lp li l3 lp3 li3 (sX γ e) (sX' γ e') (sA γ e) (sA' γ e') (sN γ e) (sN' γ e')
    (sD γ e) (sD' γ e') (sO γ e) (sO' γ e') (sC γ e) (sC' γ e') /\
  IWiGeq G0 Δ0 l lp li (sX γ e) (sX' γ e') (sA γ e) (sA' γ e') (sN γ e) (sN' γ e') (sD γ e) (sD' γ e')
    (sO γ e) (sO' γ e') (sC γ e) (sC' γ e').
Proof using EL H13 Hi3 Hp3 Hwl Hwl' Hwli Hwlp VA VC VD VL VM VN VNt VO VX Vc Vcs Vih Vmot.
  intros Hγ He.
  destruct (elimIWi_at Hγ He) as (HX0 & EX & HA0 & EA & HN0 & EN & HD0 & ED & HO0 & EO & HC0 & EC & _).
  pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwl) as Hwl0. pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwli) as Hwli0.
  pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwlp) as Hwlp0.
  split; [| exact (conj EX (conj EA (conj EN (conj ED (conj EO EC)))))].
  apply IWiEq_intro;
    first [ exact (lequiv_weaken _ _ _ _ (proj1 Hγ) H13) | exact (lequiv_weaken _ _ _ _ (proj1 Hγ) Hp3)
          | exact (lequiv_weaken _ _ _ _ (proj1 Hγ) Hi3)
          | apply geq_ty_sound; assumption | apply geq_tm_sound; assumption | assumption
          | exact (eqty_wf_r ge_typeof (geq_ty_sound EX)) | exact (eqty_wf_r ge_typeof (geq_ty_sound EA))
          | exact (eqtm_wf_r ge_typeof (geq_tm_sound EN)) | exact (eqty_wf_r ge_typeof (geq_ty_sound ED))
          | exact (eqtm_wf_r ge_typeof (geq_tm_sound EO)) | exact (eqtm_wf_r ge_typeof (geq_tm_sound EC)) ].
Qed.

(** A field's domain and codomain at related shapes and positions in a
    world, generically equal to another signature's at another
    substitution. *)
Lemma elimIWi_ann {G0 γ Δ0 e e2 kl klp kli Xr Ar Nr Or Dg Cg} (ρ : kwk G0 Δ0) {b b' i q} :
  gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e2 ->
  VTyG G0 (Γ⟦γ⟧ ,, A⟦γ⟧ @ l ,, tyFin N⟦γ⟧ @ lzero) D⟦γ⟧ Dg lp ->
  VTmG G0 (Γ⟦γ⟧ ,, A⟦γ⟧ @ l ,, tyFin N⟦γ⟧ @ lzero ,, D⟦γ⟧ @ lp) C⟦γ⟧ Cg X⟦γ⟧⟨↑⟩⟨↑⟩⟨↑⟩ li ->
  IWiEq (G := G0) (i := ge_layer) Δ0 l lp li kl klp kli (sX γ e) Xr (sA γ e) Ar (sN γ e) Nr
    (sD γ e) Dg[llift (llift e2)] (sO γ e) Or (sC γ e) Cg[llift (llift (llift e2))] ->
  IWiGeq G0 Δ0 l lp li (sX γ e) Xr (sA γ e) Ar (sN γ e) Nr
    (sD γ e) Dg[llift (llift e2)] (sO γ e) Or (sC γ e) Cg[llift (llift (llift e2))] ->
  LRtm l (kw_G ρ) (kw_Δ ρ) (kty ρ (sA γ e)) (kty ρ (sA γ e2)) b b' ->
  LRtm lzero (kw_G ρ) (kw_Δ ρ) (tyFin (ktml ρ (sN γ e))[lsingle b]) (tyFin (ktml ρ (sN γ e2))[lsingle b']) i q ->
  LRty lp (kw_G ρ) (kw_Δ ρ) (ktyll ρ (sD γ e))[lsingle2 b i] (ktyll ρ Dg[llift (llift e2)])[lsingle2 b' q] /\
  [ kw_G ρ ; kw_Δ ρ ,, (ktyll ρ (sD γ e))[lsingle2 b i] @ lp
      ⊢ (ktmlll ρ (sC γ e))[llift (lsingle2 b i)] ≈ (ktmlll ρ Cg[llift (llift (llift e2))])[llift (lsingle2 b' q)]
      : (kty ρ (sX γ e))⟨↑⟩ @ li ] /\
  [ kw_G ρ ; kw_Δ ρ ,, (ktyll ρ (sD γ e))[lsingle2 b i] @ lp
      ⊢ tyIWi l lp li (kty ρ (sX γ e))⟨↑⟩ (kty ρ (sA γ e))⟨↑⟩ (ktml ρ (sN γ e))⟨rlift ↑⟩
          (ktyll ρ (sD γ e))⟨rlift (rlift ↑)⟩ (ktml ρ (sO γ e))⟨rlift ↑⟩
          (ktmlll ρ (sC γ e))⟨rlift (rlift (rlift ↑))⟩ (ktmlll ρ (sC γ e))[llift (lsingle2 b i)]
        ≈ tyIWi kl klp kli (kty ρ Xr)⟨↑⟩ (kty ρ Ar)⟨↑⟩ (ktml ρ Nr)⟨rlift ↑⟩
          (ktyll ρ Dg[llift (llift e2)])⟨rlift (rlift ↑)⟩ (ktml ρ Or)⟨rlift ↑⟩
          (ktmlll ρ Cg[llift (llift (llift e2))])⟨rlift (rlift (rlift ↑))⟩
          (ktmlll ρ Cg[llift (llift (llift e2))])[llift (lsingle2 b' q)] @ L ].
Proof using EL Hwlp VL VN.
  intros Hγ He VDg VCg HE HG Hb Hi.
  destruct (SubRel_nf _ _ _ _ _ He) as [Ne Ne2].
  pose proof (SubRel_kw _ _ _ ρ _ _ He) as Heρ.
  rewrite !kty_subst in Hb. rewrite !ktml_subst_single in Hi.
  assert (Hi' : LRtm lzero (kw_G ρ) (kw_Δ ρ) (tyFin N⟦γ⟧⟦kw_γ ρ⟧)[lcons (kwsub ρ e) b]
                  (tyFin N⟦γ⟧⟦kw_γ ρ⟧)[lcons (kwsub ρ e2) b'] i q) by (rewrite !subst_tyFin; exact Hi).
  pose proof (SubRel_cons (SubRel_cons Heρ Hb) Hi') as Hs.
  pose proof (VDg _ _ (kw_gok ρ)) as VDρ. rewrite !gwa_cext, gwa_tyFin in VDρ.
  destruct (VDρ _ _ _ Hs) as [R HR]. destruct (escape_ty _ _ _ _ _ _ _ _ HR) as (HDd & _ & ED).
  pose proof (kw_lwf ρ (lwf_weaken _ _ _ (proj1 Hγ) Hwlp)) as Hwlpρ.
  pose proof (SubRel_lift Hs (VTy_refl_l VDρ) HDd Hwlpρ) as Hs2.
  pose proof (VCg _ _ (kw_gok ρ)) as VCρ. rewrite !gwa_cext, gwa_tyFin, !gwa_ren_ty in VCρ.
  pose proof (LRtm_geq (VCρ _ _ _ Hs2)) as EC.
  rewrite !shift_llift_ty, !shift_cons_ty', <- kty_subst in EC.
  rewrite <- (ktyll_subst_single2 ρ e Ne) in HDd, HR, EC. rewrite <- (ktyll_subst_single2 ρ e2 Ne2) in HR.
  rewrite <- (ktmlll_subst_lift_single2 ρ e Ne), <- (ktmlll_subst_lift_single2 ρ e2 Ne2) in EC.
  refine (conj (ex_intro _ _ HR) (conj EC _)).
  pose proof (IWiEq_kw ρ HE) as HEρ. pose proof (IWiGeq_kw ρ HE HG) as HGρ.
  pose proof (ext_wf_g HDd Hwlpρ) as HΓd.
  exact (iwi_geq_at (IWiEq_wk1 ge_typeof ge_notV HEρ HΓd) (IWiGeq_wk1 HEρ HGρ HΓd) EC).
Qed.

(** The induction hypothesis's body in a world, at an index and an
    argument: the motive at the children's spine, at the application of
    [dnth]'s state to the argument. *)
Local Notation kF ρ γ e a :=
  (iwiFam l lp li (kty ρ (sX γ e)) (kty ρ (sA γ e)) (ktml ρ (sN γ e)) (ktyll ρ (sD γ e)) (ktml ρ (sO γ e))
     (ktmlll ρ (sC γ e)) (ktm ρ a)).
Local Notation kF' ρ γ e' a' :=
  (iwiFam l3 lp3 li3 (kty ρ (sX' γ e')) (kty ρ (sA' γ e')) (ktml ρ (sN' γ e')) (ktyll ρ (sD' γ e'))
     (ktml ρ (sO' γ e')) (ktmlll ρ (sC' γ e')) (ktm ρ a')).
Local Notation kCod ρ γ e a :=
  (iwiFamCod l lp li (kty ρ (sX γ e)) (kty ρ (sA γ e)) (ktml ρ (sN γ e)) (ktyll ρ (sD γ e)) (ktml ρ (sO γ e))
     (ktmlll ρ (sC γ e)) (ktm ρ a)).
Local Notation kCod' ρ γ e' a' :=
  (iwiFamCod l3 lp3 li3 (kty ρ (sX' γ e')) (kty ρ (sA' γ e')) (ktml ρ (sN' γ e')) (ktyll ρ (sD' γ e'))
     (ktml ρ (sO' γ e')) (ktmlll ρ (sC' γ e')) (ktm ρ a')).
Local Notation kscr ρ γ e a cs i y :=
  (app (tmDNth L (ktml ρ (sN γ e))[lsingle (ktm ρ a)] (kF ρ γ e a) (ktm ρ cs) i) lp L
     (ktyll ρ (sD γ e))[lsingle2 (ktm ρ a) i] (kCod ρ γ e a)[llift (lsingle i)] y).
Local Notation kscr' ρ γ e' a' cs' i' y' :=
  (app (tmDNth (iwiL l3 lp3 li3) (ktml ρ (sN' γ e'))[lsingle (ktm ρ a')] (kF' ρ γ e' a') (ktm ρ cs') i') lp3
     (iwiL l3 lp3 li3) (ktyll ρ (sD' γ e'))[lsingle2 (ktm ρ a') i'] (kCod' ρ γ e' a')[llift (lsingle i')] y').

Lemma elimIWi_kgoal {G0 Δ0} {ix dm : DomRel G0 Δ0} {pd : IPosDomRel G0 Δ0} {a a' cs cs' γ e e'} (ρ : kwk G0 Δ0)
    {i i' y y' T1 T2} :
  gwk_ok γ G0 G -> SubRel G0 Γ⟦γ⟧ Δ0 e e' -> elimIWi_kd G0 Δ0 ix dm pd γ e e' ->
  LRtm l G0 Δ0 (sA γ e) (sA γ e') a a' -> (forall ρ : kwk G0 Δ0, dm ρ (ktm ρ a) (ktm ρ a')) ->
  LRtm L G0 Δ0 (iwicsty l lp li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ D⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧)[lcons e a]
    (iwicsty l lp li X⟦γ⟧ A⟦γ⟧ N⟦γ⟧ D⟦γ⟧ Ot⟦γ⟧ C⟦γ⟧)[lcons e' a'] cs cs' ->
  (forall ρ : kwk G0 Δ0,
     elimIWi_mspine (kw_G ρ) (kw_Δ ρ) l lp li (kty ρ (sX γ e)) (kty ρ (sA γ e)) (ktml ρ (sN γ e))
       (ktyll ρ (sD γ e)) (ktml ρ (sO γ e)) (ktmlll ρ (sC γ e))
       (fun ρ' => ix (kw_comp ρ ρ')) (fun ρ' => dm (kw_comp ρ ρ')) (fun ρ' => pd (kw_comp ρ ρ'))
       (fun p y y' => exists p', pd ρ (ktm ρ a) (ktm ρ a') p p' y y')
       (ktyll ρ (sD γ e))[llift (lsingle (ktm ρ a))] (ktmlll ρ (sC γ e))[llift (llift (lsingle (ktm ρ a)))]
       (ktml ρ (sN γ e))[lsingle (ktm ρ a)] (ktm ρ cs) (ktm ρ cs')) ->
  LRtm lzero (kw_G ρ) (kw_Δ ρ) (tyFin (ktml ρ (sN γ e))[lsingle (ktm ρ a)]) T1 i i' ->
  LRtm lp (kw_G ρ) (kw_Δ ρ) (ktyll ρ (sD γ e))[lsingle2 (ktm ρ a) i] T2 y y' ->
  LRtm l' (kw_G ρ) (kw_Δ ρ)
    (ktyll ρ (sM γ e))[lsingle2 (ktmlll ρ (sC γ e))[lsingle3 (ktm ρ a) i y] (kscr ρ γ e a cs i y)]
    (ktyll ρ (sM γ e))[lsingle2 (ktmlll ρ (sC γ e))[lsingle3 (ktm ρ a) i y] (kscr ρ γ e a cs i y)]
    (tmElimIWi l lp li l' (kty ρ (sX γ e)) (kty ρ (sA γ e)) (ktml ρ (sN γ e)) (ktyll ρ (sD γ e)) (ktml ρ (sO γ e))
       (ktmlll ρ (sC γ e)) (ktyll ρ (sM γ e)) (ktmlll ρ (sc γ e)) (ktmlll ρ (sC γ e))[lsingle3 (ktm ρ a) i y]
       (kscr ρ γ e a cs i y))
    (tmElimIWi l3 lp3 li3 l4 (kty ρ (sX' γ e')) (kty ρ (sA' γ e')) (ktml ρ (sN' γ e')) (ktyll ρ (sD' γ e'))
       (ktml ρ (sO' γ e')) (ktmlll ρ (sC' γ e')) (ktyll ρ (sM' γ e')) (ktmlll ρ (sc' γ e'))
       (ktmlll ρ (sC' γ e'))[lsingle3 (ktm ρ a') i' y'] (kscr' ρ γ e' a' cs' i' y')).
Proof using EL H13 H24 HS Hi3 Hp3 Hwl Hwl' Hwli Hwlp VA VC VD VL VM VN VNt VO VX Vc Vcs Vih Vmot.
  intros Hγ He HK Xa Ha Xcs IH Hi Hy.
  pose proof HK as (HX & HA & Har & Hpd & HpdE).
  pose proof (SubRel_ctx He) as HΔ0. destruct (SubRel_nf _ _ _ _ _ He) as [Ne Ne'].
  destruct (elimIWi_loc Hγ) as (VXγ & VAγ & VNγ & VDγ & VOγ & VCγ & _).
  destruct (elimIWi_nf Hγ He) as (NX & NA & NN & ND & NO & NC & NM & Nc).
  pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwl) as Hwl0. pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwli) as Hwli0.
  pose proof (lwf_weaken _ _ _ (proj1 Hγ) Hwlp) as Hwlp0.
  assert (HwL : lwf (gL G0) L) by (repeat split; assumption).
  destruct (LRtm_escape Xa) as [Hat Ha't]. pose proof (wf_tm_nf Hat) as Na. pose proof (wf_tm_nf Ha't) as Na'.
  destruct (LRtm_escape Xcs) as [Hcst Hcs't]. pose proof (wf_tm_nf Hcst) as Ncs. pose proof (wf_tm_nf Hcs't) as Ncs'.
  pose proof (SubRel_cons He Xa) as HS1. pose proof (SubRel_cons HS1 Xcs) as HS2.
  (* the arities *)
  pose proof (VTmG_loc (VTmG_refl_l VNγ) _ _ _ HS1) as XN. rewrite !subst_tyNat in XN.
  apply LRtm_nat in XN. rewrite <- !lift_single_tm in XN by assumption.
  pose proof (NatRel_kw ρ _ _ XN) as Hkkl. rewrite !ktm_single in Hkkl.
  pose proof (LRtm_trans Xa (LRtm_sym Xa)) as Xaa.
  pose proof (VTmG_loc (VTmG_refl_l VNγ) _ _ _ (SubRel_cons (SubRel_refl_l He) Xaa)) as XN0.
  rewrite !subst_tyNat in XN0. apply LRtm_nat in XN0. rewrite <- !lift_single_tm in XN0 by assumption.
  pose proof (LRtm_irrel_r Hi (LR_fin_nat (kw_ctx ρ) Hkkl)) as Yl.
  pose proof (LRtm_kw ρ Xa) as Xaρ.
  destruct (elimIWi_sig2 Hγ He) as [HE2 HG2].
  destruct (elimIWi_ann ρ Hγ He VDγ VCγ HE2 HG2 Xaρ Yl) as (LD & GC & GCod).
  pose proof (LRtm_irrel_r Hy LD) as Yy.
  pose proof (elimIWi_dnth_kw Hwl Hwlp Hwli H13 Hp3 Hi3 HS VX VA VNt VD VO VC ρ Hγ HS2 Yl) as Xdn.
  unfold iwiFieldT in Xdn.
  destruct (LRtm_pi_K Xdn) as (w & w' & Hw & Hw' & Nw & Nw' & Eww & HLv & _ & _ & Hd0 & HCd0 & Happ).
  assert (Nk : nfty (kty ρ (sX γ e)) /\ nfty (kty ρ (sA γ e)) /\ nftm (ktml ρ (sN γ e)) /\ nfty (ktyll ρ (sD γ e))
               /\ nftm (ktml ρ (sO γ e)) /\ nftm (ktmlll ρ (sC γ e)) /\ nftm (ktm ρ a)
               /\ nfty (kty ρ (sX' γ e')) /\ nfty (kty ρ (sA' γ e')) /\ nftm (ktml ρ (sN' γ e'))
               /\ nfty (ktyll ρ (sD' γ e')) /\ nftm (ktml ρ (sO' γ e')) /\ nftm (ktmlll ρ (sC' γ e'))
               /\ nftm (ktm ρ a') /\ nftm (ktm ρ cs) /\ nftm (ktm ρ cs') /\ nfty (ktyll ρ (sM γ e)))
    by (unfold kty, ktml, ktyll, ktmlll, ktm; repeat split; first [apply ren_nf_ty | apply ren_nf]).
  destruct Nk as (NkX & NkA & NkN & NkD & NkO & NkC & Nka & NkX' & NkA' & NkN' & NkD' & NkO' & NkC' & Nka'
                  & Nkcs & Nkcs' & NkM).
  destruct (LRtm_escape Yl) as [Hit Hi't]. pose proof (wf_tm_nf Hit) as Ni. pose proof (wf_tm_nf Hi't) as Ni'.
  assert (EB : (kCod ρ γ e a)[llift (lsingle i)] =
               tyIWi l lp li (kty ρ (sX γ e))⟨↑⟩ (kty ρ (sA γ e))⟨↑⟩ (ktml ρ (sN γ e))⟨rlift ↑⟩
                 (ktyll ρ (sD γ e))⟨rlift (rlift ↑)⟩ (ktml ρ (sO γ e))⟨rlift ↑⟩
                 (ktmlll ρ (sC γ e))⟨rlift (rlift (rlift ↑))⟩ (ktmlll ρ (sC γ e))[llift (lsingle2 (ktm ρ a) i)]).
  { change (kCod ρ γ e a) with (iwiFamCodT l lp li (kty ρ (sX γ e)) (kty ρ (sA γ e)) (ktml ρ (sN γ e))
             (ktyll ρ (sD γ e)) (ktml ρ (sO γ e)) (ktmlll ρ (sC γ e))
             (ktmlll ρ (sC γ e))[llift (llift (lsingle (ktm ρ a)))]).
    rewrite iwiFamCodT_single, llift2_single_llift_single by assumption. reflexivity. }
  assert (EB' : (kCod' ρ γ e' a')[llift (lsingle i')] =
               tyIWi l3 lp3 li3 (kty ρ (sX' γ e'))⟨↑⟩ (kty ρ (sA' γ e'))⟨↑⟩ (ktml ρ (sN' γ e'))⟨rlift ↑⟩
                 (ktyll ρ (sD' γ e'))⟨rlift (rlift ↑)⟩ (ktml ρ (sO' γ e'))⟨rlift ↑⟩
                 (ktmlll ρ (sC' γ e'))⟨rlift (rlift (rlift ↑))⟩ (ktmlll ρ (sC' γ e'))[llift (lsingle2 (ktm ρ a') i')]).
  { change (kCod' ρ γ e' a') with (iwiFamCodT l3 lp3 li3 (kty ρ (sX' γ e')) (kty ρ (sA' γ e')) (ktml ρ (sN' γ e'))
             (ktyll ρ (sD' γ e')) (ktml ρ (sO' γ e')) (ktmlll ρ (sC' γ e'))
             (ktmlll ρ (sC' γ e'))[llift (llift (lsingle (ktm ρ a')))]).
    rewrite iwiFamCodT_single, llift2_single_llift_single by assumption. reflexivity. }
  pose proof (lequiv_weaken _ _ _ _ (proj1 Hγ) H13) as H13'. pose proof (lequiv_weaken _ _ _ _ (proj1 Hγ) Hp3) as Hp3'.
  pose proof (lequiv_weaken _ _ _ _ (proj1 Hγ) Hi3) as Hi3'.
  assert (HLL : lequiv (gL G0) L (iwiL l3 lp3 li3)) by (repeat apply lequiv_max; assumption).
  pose proof (kw_lwf ρ Hwlp0) as Hwlpρ. pose proof (kw_lwf ρ HwL) as HwLρ.
  destruct LD as [RD HRD]. destruct (escape_ty _ _ _ _ _ _ _ _ HRD) as (_ & HD't & ED).
  destruct (Happ y y' _ Yy lp L lp3 (iwiL l3 lp3 li3) (ktyll ρ (sD γ e))[lsingle2 (ktm ρ a) i] (kCod ρ γ e a)[llift (lsingle i)]
              (ktyll ρ (sD' γ e'))[lsingle2 (ktm ρ a') i'] (kCod' ρ γ e' a')[llift (lsingle i')]
              (lequiv_refl _ _ Hwlpρ) (lequiv_refl _ _ HwLρ) (kw_lequiv ρ (lequiv_sym _ _ _ Hp3'))
              (kw_lequiv ρ (lequiv_sym _ _ _ HLL)) (geq_ty_trans ED (geq_ty_sym ED)))
    as (T3 & Xap).
  { rewrite EB. exact (geq_ty_trans GCod (geq_ty_sym GCod)). }
  { exact ED. }
  { rewrite EB'. exact GCod. }
  assert (LDl : LRty lp (kw_G ρ) (kw_Δ ρ) (ktyll ρ (sD γ e))[lsingle2 (ktm ρ a) i]
                  (ktyll ρ (sD γ e'))[lsingle2 (ktm ρ a') i']).
  { pose proof (SubRel_kw _ _ _ ρ _ _ He) as Heρ.
    pose proof Xaρ as Hb. pose proof Yl as Hi0.
    rewrite !kty_subst in Hb. rewrite !ktml_subst_single in Hi0.
    assert (Hi1 : LRtm lzero (kw_G ρ) (kw_Δ ρ) (tyFin N⟦γ⟧⟦kw_γ ρ⟧)[lcons (kwsub ρ e) (ktm ρ a)]
                    (tyFin N⟦γ⟧⟦kw_γ ρ⟧)[lcons (kwsub ρ e') (ktm ρ a')] i i') by (rewrite !subst_tyFin; exact Hi0).
    pose proof (VTyG_refl_l VDγ _ _ (kw_gok ρ)) as VDρ. rewrite !gwa_cext, gwa_tyFin in VDρ.
    destruct (VDρ _ _ _ (SubRel_cons (SubRel_cons Heρ Hb) Hi1)) as [R HR].
    rewrite <- (ktyll_subst_single2 ρ e Ne), <- (ktyll_subst_single2 ρ e' Ne') in HR. exists R; exact HR. }
  pose proof (LRtm_irrel_r Yy LDl) as Yy2.
  assert (Ec : forall t : tm, t[llift (lsingle2 (ktm ρ a) i)][lsingle y] = t[lsingle3 (ktm ρ a) i y]).
  { intros t. clear -Nka Ni. revert Nka Ni. generalize (ktm ρ a) i y. intros x q z N1 N2. meq. }
  rewrite iwiCod_single, Ec in Xap by assumption.
  destruct (IWiCan_comp ρ HK) as (HXρ & HAρ & Harρ & Hpdρ & HpdEρ).
  destruct Xap as (R0 & HR0 & Hn0).
  pose proof (proj1 (LR_iwi_rel HR0 HXρ HAρ Harρ Hpdρ HpdEρ _ _) Hn0) as Z.
  destruct (LRtm_escape Yy) as [Hyt Hyt']. pose proof (LRtm_geq Yy) as Eyy.
  pose proof (tmred_app_annot Hwlpρ HwLρ (lequiv_refl _ _ Hwlpρ) (lequiv_refl _ _ HwLρ) Hd0 HCd0 Hyt
                (geq_ty_sound (geq_ty_trans ED (geq_ty_sym ED)))
                (geq_ty_sound (eq_rect_r (fun B => [ _ ; _ ⊢ _ ≈ B @ _ ]) (geq_ty_trans GCod (geq_ty_sym GCod)) EB))
                Hw) as Ra.
  assert (Ec' : forall t : tm, t[llift (lsingle2 (ktm ρ a) i)][lsingle y'] = t[lsingle3 (ktm ρ a) i y']).
  { intros t. clear -Nka Ni. revert Nka Ni. generalize (ktm ρ a) i y'. intros x q z N1 N2. meq. }
  pose proof (tmred_app_annot Hwlpρ HwLρ (kw_lequiv ρ (lequiv_sym _ _ _ Hp3')) (kw_lequiv ρ (lequiv_sym _ _ _ HLL))
                Hd0 HCd0 Hyt' (geq_ty_sound ED)
                (geq_ty_sound (eq_rect_r (fun B => [ _ ; _ ⊢ _ ≈ B @ _ ]) GCod EB')) Hw') as Ra'.
  pose proof (wf_ty_func ge_typeof HCd0 (lsub_eq_single ge_typeof Hyt' Hyt (eqtm_sym _ _ _ _ _ _ _ (geq_tm_sound Eyy))))
    as EB0.
  rewrite iwiCod_single in Ra by assumption. rewrite iwiCod_single in Ra' by assumption.
  rewrite !iwiCod_single in EB0 by assumption. rewrite Ec in Ra, EB0. rewrite Ec' in Ra', EB0.
  pose proof (IWiRel_red_bwd Ra (tmred_conv _ _ _ _ _ ge_typeof Ra' EB0) Z) as Hn.
  clear Z Ra Ra' EB0 Hn0.
  (* the child indices *)
  pose proof (elimIWi_ci_kw ρ Hγ He VCγ Xaρ Yl Yy2) as Xx.
  (* the induction hypothesis's premises in the world *)
  assert (He1 : SubRel (kw_G ρ) Γ⟦gwk_comp (kw_γ ρ) γ⟧ (kw_Δ ρ) (kwsub ρ e) (kwsub ρ e')).
  { pose proof (SubRel_kw _ _ _ ρ _ _ He) as Z. now rewrite gwa_comp_ctx in Z. }
  assert (Hh : elimIWi_hyp (kw_G ρ) (kw_Δ ρ) l lp li (kty ρ (sX γ e)) (kty ρ (sA γ e)) (ktml ρ (sN γ e))
                 (ktyll ρ (sD γ e)) (ktml ρ (sO γ e)) (ktmlll ρ (sC γ e))
                 (fun ρ' => ix (kw_comp ρ ρ')) (fun ρ' => dm (kw_comp ρ ρ')) (fun ρ' => pd (kw_comp ρ ρ'))
                 (gwk_comp (kw_γ ρ) γ) (kwsub ρ e) (kwsub ρ e')).
  { pose proof (gwk_ok_comp (kw_gok ρ) Hγ) as Hγ1.
    unfold elimIWi_hyp, elimIWi_kd.
    rewrite <- (kγ_ty ρ X γ e), <- (kγ_ty ρ A γ e), <- (kγ_tml ρ N γ e), <- (kγ_tyll ρ D γ e),
      <- (kγ_tml ρ Ot γ e), <- (kγ_tmlll ρ C γ e), <- (kγ_tml ρ N γ e').
    refine (conj Hγ1 (conj He1 _)). repeat split; first [reflexivity | assumption]. }
  pose proof (IWiEq_kw ρ (proj1 (elimIWi_sig Hγ He))) as (_ & _ & _ & HSρ & _).
  destruct (LRtm_escape Xaρ) as [Haρ _].
  pose proof (IWi_fam_wf ge_typeof ge_notV HSρ Haρ) as HFam. rewrite iwiFam_T in HFam.
  pose proof (VTmG_loc (VTmG_refl_l VNγ) _ _ _ (SubRel_cons (SubRel_refl_l He) Xaa)) as XN1.
  rewrite !subst_tyNat in XN1. apply LRtm_nat in XN1. rewrite <- !lift_single_tm in XN1 by assumption.
  assert (HPG : IWiPosGeq (kw_G ρ) (kw_Δ ρ) lp li (kty ρ (sX γ e)) (ktml ρ (sN γ e))[lsingle (ktm ρ a)]
                  (ktml ρ (sN γ e))[lsingle (ktm ρ a)] (ktyll ρ (sD γ e))[llift (lsingle (ktm ρ a))]
                  (ktyll ρ (sD γ e))[llift (lsingle (ktm ρ a))] (ktmlll ρ (sC γ e))[llift (llift (lsingle (ktm ρ a)))]
                  (ktmlll ρ (sC γ e))[llift (llift (lsingle (ktm ρ a)))]).
  { intros ρ' p p' Hp. rewrite !ktyl_iwiD_single, !ktmll_iwiC_single, <- kty_comp. rewrite !ktm_comp_single in Hp.
    pose proof (NatRel_kw (kw_comp ρ ρ') _ _ XN1) as Hk2. rewrite !ktm_single in Hk2.
    destruct (elimIWi_sig Hγ He) as [HE0 HG0].
    destruct (elimIWi_ann (kw_comp ρ ρ') Hγ (SubRel_refl_l He) (VTyG_refl_l VDγ) (VTmG_refl_l VCγ) HE0 HG0
                (LRtm_kw (kw_comp ρ ρ') Xaa) (PosRel_LRtm Hp Hk2)) as ([R1 HR1] & GC1 & _).
    destruct (escape_ty _ _ _ _ _ _ _ _ HR1) as (HDp & _ & EDp).
    exact (conj HDp (conj EDp GC1)). }
  (* the arities, against the other side's *)
  pose proof (VTmG_loc VNγ _ _ _ HS1) as XNp. rewrite !subst_tyNat in XNp.
  apply LRtm_nat in XNp. rewrite <- !lift_single_tm in XNp by assumption.
  pose proof (NatRel_kw ρ _ _ XNp) as Hkkp. rewrite !ktm_single in Hkkp.
  pose proof (LRtm_irrel_r Hi (LR_fin_nat (kw_ctx ρ) Hkkp)) as Yp.
  destruct (NatRel_escape Hkkp) as (Hk & Hk' & _). pose proof (wf_tm_nf Hk) as Nk. pose proof (wf_tm_nf Hk') as Nk'.
  pose proof (wf_ty_nf HFam) as NF.
  assert (NF' : nfty (kF' ρ γ e' a')).
  { unfold iwiFam, iwiFamCod. cbn. repeat split.
    all: repeat first [assumption | apply ren_nf_ty | apply ren_nf | apply subst_nf_ty | apply subst_nf
                      | apply lk_llift | apply lk_lsingle]. }
  assert (Ne1 : nftm (lam lzero lzero (tyFin (ktml ρ (sN γ e))[lsingle (ktm ρ a)]) (var 0))) by (cbn; auto).
  assert (Ne1' : nftm (lam lzero lzero (tyFin (ktml ρ (sN' γ e'))[lsingle (ktm ρ a')]) (var 0))) by (cbn; auto).
  pose proof (IH ρ _ _ _ Hh HFam HPG (ktm ρ cs) (ktm ρ cs') Nkcs Nkcs' (tc_refl _) (tc_refl _) _ _ _ Hkkp Yp
                _ _ _ _ Ne1 Ne1' (dn_top (L := L) Nk NF) (dn_top (L := iwiL l3 lp3 li3) Nk' NF') y y' lp L (ktyll ρ (sD γ e))[lsingle2 (ktm ρ a) i] (kCod ρ γ e a)[llift (lsingle i)]
                lp3 (iwiL l3 lp3 li3) (ktyll ρ (sD' γ e'))[lsingle2 (ktm ρ a') i'] (kCod' ρ γ e' a')[llift (lsingle i')]
                (lequiv_refl _ _ Hwlpρ) (lequiv_refl _ _ HwLρ) (kw_lequiv ρ (lequiv_sym _ _ _ Hp3'))
                (kw_lequiv ρ (lequiv_sym _ _ _ HLL))) as X0.
  match type of X0 with ?P -> _ => assert (HY : P) end.
  2: { pose proof (X0 HY _ _ _ _ Xx Hn (reds_refl _) (reds_refl _)) as X1.
    unfold elimIWi_goal in X1.
    rewrite <- (kγ_ty ρ X γ e), <- (kγ_ty ρ A γ e), <- (kγ_tml ρ N γ e), <- (kγ_tyll ρ D γ e), <- (kγ_tml ρ Ot γ e),
      <- (kγ_tmlll ρ C γ e), <- (kγ_tyll ρ M γ e), <- (kγ_tmlll ρ c γ e), <- (kγ_ty ρ X' γ e'), <- (kγ_ty ρ A' γ e'),
      <- (kγ_tml ρ N' γ e'), <- (kγ_tyll ρ D' γ e'), <- (kγ_tml ρ Ot' γ e'), <- (kγ_tmlll ρ C' γ e'),
      <- (kγ_tyll ρ M' γ e'), <- (kγ_tmlll ρ c' γ e') in X1.
    exact X1. }
  intros p p' Hpc Hip.
  pose proof (NatRel_kw ρ _ _ XN1) as Hk0. rewrite !ktm_single in Hk0.
  pose proof (LRtm_irrel_l (LRtm_sym Hip) (LR_fin_nat (kw_ctx ρ) Hk0)) as Hpi.
  destruct (LRtm_escape Hpi) as [Hpt _]. pose proof (wf_tm_nf Hpt) as Np.
  destruct (elimIWi_sig Hγ He) as [HE0 HG0].
  destruct (elimIWi_ann ρ Hγ (SubRel_refl_l He) (VTyG_refl_l VDγ) (VTmG_refl_l VCγ) HE0 HG0
              (LRtm_kw ρ Xaa) Hpi) as (LDpi & _ & GCodpi).
  pose proof (LRtm_trans Hpi Yl) as Hpi'.
  destruct (elimIWi_ann ρ Hγ He VDγ VCγ HE2 HG2 Xaρ Hpi') as (LDpi' & _ & GCodpi').
  pose proof LDpi as [R3 HR3]. destruct (escape_ty _ _ _ _ _ _ _ _ HR3) as (_ & _ & EDpi).
  pose proof LDpi' as [R4 HR4]. destruct (escape_ty _ _ _ _ _ _ _ _ HR4) as (_ & _ & EDpi').
  rewrite llift_single_single_ty by assumption.
  rewrite iwiFamCodT_single, llift2_single_llift_single by assumption. rewrite EB, EB'.
  refine (conj _ (conj EDpi (conj GCodpi (conj EDpi' GCodpi')))).
  (* the argument, at the position's domain *)
  destruct (PosRel_retarget (PosCan_rel Hpc) _ Hkkl) as (p2 & Hp2).
  destruct (Hpd ρ _ _ (Ha ρ) p p2 Hp2) as [D1 YD].
  pose proof (LRtm_irrel_l Yy2 (LRty_trans LDpi LDl)) as Yp2.
  assert (Hle : lmeasure lp <= lmeasure L) by (rewrite !lmeasure_max; lia).
  destruct (proj1 (LRtm_stage Hle) Yp2) as (R2 & H2r & Hr2).
  exists p2. exact (proj1 (LR_irrel _ _ _ _ _ _ _ _ _ _ H2r YD y y') Hr2).
Qed.

End ElimAt.

End IWiElimV.
