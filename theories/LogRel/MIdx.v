(** * [M]'s relation at related indices (M18_DESIGN.md, M18b)

    At one depth, [MRn] at indices [m], [m'] is [MRn] at any [m1], [m1']
    related to them, given the side's relations' irrelevance in both
    indices: [MRn_dir] on the right index, and under [MRn_flip] on the
    left one. [corec]'s validity proves its relation at the [corec]'s own
    index only and moves it to the claimed one with this. *)
From DeLaM.LogRel Require Export Transitivity.
From DeLaM.LogRel Require Import MAux.

Section MIdx.
Context `{E : GenericEq} `{EL : !GenericEqLaws} `{LP : LRParams} `{VL : VPLaws lr_vp}.

Lemma MRn_idx n {G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR m m' m1 m1' t t'} :
  MSide G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' idxR shR posR ->
  MShIrr idxR shR -> MPosIrr idxR shR posR ->
  MShIrr (mflipI idxR) (mflipS shR) -> MPosIrr (mflipI idxR) (mflipS shR) (mflipP posR) ->
  nftm m -> nftm m' -> nftm m1 -> nftm m1' ->
  (forall ρ, idxR ρ (ktm ρ m) (ktm ρ m')) -> (forall ρ, idxR ρ (ktm ρ m) (ktm ρ m1')) ->
  (forall ρ, idxR ρ (ktm ρ m1) (ktm ρ m1')) ->
  MRn n G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' shR posR m m' t t' ->
  MRn n G Γ l1 l2 li X A B C r1 r2 ri X' A' B' C' shR posR m1 m1' t t'.
Proof using EL.
  intros HM Si Pi Si' Pi' N N' N1 N1' I1 I2 I3 Ht.
  assert (H1 := MRn_dir n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 (MIrrHyps_self HM Si Pi N N' N1' I1 I2) t t' Ht).
  assert (H2 := MRn_flip n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HM N N1' I2 t' t H1).
  pose proof (MSide_flip HM) as HMf.
  assert (H3 := MRn_dir n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
                 (MIrrHyps_self HMf Si' Pi' N1' N N1 I2 I3) t' t H2).
  exact (MRn_flip n _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HMf N1' N1 I3 t t' H3).
Qed.

End MIdx.
