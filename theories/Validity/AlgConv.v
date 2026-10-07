(** * The conversion lemma for algorithmic conversion (08:94; M6_DESIGN.md H10)

    An algorithmic derivation over [(G, Γ)] at a type [T] also holds over a
    related [(G2, Γ2)] at an equal type [T2]: [GEq G G2] for the global
    context, [Γ ≅ Γ2] in [G2], and [T2 ≅ T] in [(G2, Γ)]. Neutral terms
    infer an equal type. The source syntax is typed in [(G, Γ)], as for
    soundness. All declarative facts about the target live over the source
    local context [Γ]; [Γ2] only appears in the algorithmic conclusion
    (untyped reduction does not look at contexts).

    This file: the plumbing. *)
From DeLaM.Validity Require Export AlgSound.
From DeLaM.Typing Require Export GConv AlgStruct.

(** ** Lookups along an equivalence of contexts *)

Lemma eqctx_lookup {G i Γ Γ2} : typeof i = i -> [ G ⊢[ i ] Γ ≅ Γ2 ] ->
  forall n T l, in_ctx Γ n T l ->
  exists T2 l2, in_ctx Γ2 n T2 l2 /\ lequiv (gL G) l l2 /\ [ G ; Γ ⊢[ i ] T ≅ T2 @ l ].
Proof.
  intros Hi H. induction H as [G i0 HG | G i0 g HG Hg | G i0 Γ Γ' A A' l l' Hc IH HA HAA Hl];
    intros n T l0 Hin; inversion Hin; subst.
  - pose proof (wfc_ext _ _ _ _ _ (ctx_of_wf_ty Hi HA) HA (lequiv_wf_l _ _ _ Hl)) as HΓA.
    exists A'⟨↑⟩, l'. split; [constructor | split; [exact Hl | eapply wk1_eqty; eassumption]].
  - match goal with Hm : in_ctx Γ _ _ _ |- _ => destruct (IH Hi _ _ _ Hm) as (T2 & l2 & Hin2 & El & ET) end.
    pose proof (wfc_ext _ _ _ _ _ (ctx_of_wf_ty Hi HA) HA (lequiv_wf_l _ _ _ Hl)) as HΓA.
    exists T2⟨↑⟩, l2. split; [now constructor | split; [exact El | eapply wk1_eqty; eassumption]].
Qed.

Lemma eqctx_lookup_r {G i Γ Γ2} : typeof i = i -> [ G ⊢[ i ] Γ ≅ Γ2 ] ->
  forall n T2 l2, in_ctx Γ2 n T2 l2 ->
  exists T l, in_ctx Γ n T l /\ lequiv (gL G) l l2 /\ [ G ; Γ ⊢[ i ] T ≅ T2 @ l ].
Proof.
  intros Hi H. induction H as [G i0 HG | G i0 g HG Hg | G i0 Γ Γ' A A' l l' Hc IH HA HAA Hl];
    intros n T2 l2 Hin; inversion Hin; subst.
  - pose proof (wfc_ext _ _ _ _ _ (ctx_of_wf_ty Hi HA) HA (lequiv_wf_l _ _ _ Hl)) as HΓA.
    exists A⟨↑⟩, l. split; [constructor | split; [exact Hl | eapply wk1_eqty; eassumption]].
  - match goal with Hm : in_ctx Γ' _ _ _ |- _ => destruct (IH Hi _ _ _ Hm) as (T & l1 & Hin1 & El & ET) end.
    pose proof (wfc_ext _ _ _ _ _ (ctx_of_wf_ty Hi HA) HA (lequiv_wf_l _ _ _ Hl)) as HΓA.
    exists T⟨↑⟩, l1. split; [now constructor | split; [exact El | eapply wk1_eqty; eassumption]].
Qed.

(** ** Equivalent contexts under the rules' binders *)

(** Extension by the same entries. *)
Lemma eqctx_ext_refl {G i Γ Γ2 A l} : [ G ⊢[ i ] Γ ≅ Γ2 ] -> [ G ; Γ ⊢[ i ] A @ l ] -> lwf (gL G) l ->
  [ G ⊢[ i ] Γ ,, A @ l ≅ Γ2 ,, A @ l ].
Proof. intros Hc HA Hl. apply eqc_ext; [exact Hc | exact HA | apply eqty_refl, HA | exact (lequiv_refl _ _ Hl)]. Qed.

(** Under a new global binding. *)
Lemma eqctx_gext {G i Γ Γ2 D} : [ ⊢ gext G D ] -> [ G ⊢[ i ] Γ ≅ Γ2 ] -> [ gext G D ⊢[ i ] Γ⟪S⟫ ≅ Γ2⟪S⟫ ].
Proof.
  intros Hg H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 gweakening))))) _ _ _ _ H _ (D :: gΨ G)
                        (gwk_step gwk_id) (le_n _) (gwkwf_step _ _ _ _ (gwkwf_id _)) Hg).
Qed.

(** Under fresh levels and fresh global bindings ([wf_wkc]). *)
Lemma eqctx_wkc G i Γ Γ2 nu Ds : [ G ⊢[ i ] Γ ≅ Γ2 ] ->
  [ ⊢ mkG (nu + gL G) (Ds ++ map (fun D => gdecl_uren D (ush nu)) (gΨ G)) ] ->
  [ mkG (nu + gL G) (Ds ++ map (fun D => gdecl_uren D (ush nu)) (gΨ G)) ⊢[ i ]
      wkc nu (length Ds) Γ ≅ wkc nu (length Ds) Γ2 ].
Proof.
  intros H HG. pose proof (uwk_eqctx nu H) as X. unfold gctx_uwk in X; cbn [gL gΨ] in X.
  pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 gweakening))))) _ _ _ _ X _ _ _ (le_n _)
                (gwk_stepn_wf Ds _) HG) as Y.
  unfold wkc. rewrite !(proj1 (proj2 (proj2 gren_ext_all)) _ (ush (length Ds)) (gwk_fn (gwk_stepn (length Ds))))
    by (intros; now rewrite gwk_stepn_fn).
  exact Y.
Qed.

(** Extension by the same entries. *)
Lemma eqctx_cexts {G i Γ Γ2} As : [ G ⊢[ i ] Γ ≅ Γ2 ] -> [ G ; cexts Γ As ⊢[ i ] ] ->
  [ G ⊢[ i ] cexts Γ As ≅ cexts Γ2 As ].
Proof.
  revert Γ Γ2; induction As as [| [A l] As IH]; intros Γ Γ2 H HΓ; cbn [cexts] in *; [exact H|].
  apply IH; [| exact HΓ].
  destruct (wfc_ext_inv (wf_cexts_prefix _ _ _ _ HΓ)) as (_ & HA & Hl).
  exact (eqctx_ext_refl H HA Hl).
Qed.

(** The recursors' scopes. *)
Lemma eqctx_recΓT {G Γ Γ2} : [ G ⊢[ lM ] Γ ≅ Γ2 ] -> [ recGT G ⊢[ lM ] recΓT Γ ≅ recΓT Γ2 ].
Proof.
  intros H. pose proof (eqctx_wf_l (i := lM) eq_refl H) as HΓ.
  pose proof (wf_recΓT _ _ HΓ) as HT. unfold recΓT in *.
  destruct (wfc_ext_inv HT) as (_ & HA & Hl). apply eqctx_ext_refl; [| exact HA | exact Hl].
  exact (eqctx_wkc _ _ _ _ 1 (gdCtx :: nil) H (wf_recGT (ctx_glob _ _ _ HΓ))).
Qed.

Lemma eqctx_recΓt {G Γ Γ2} : [ G ⊢[ lM ] Γ ≅ Γ2 ] -> [ recGt G ⊢[ lM ] recΓt Γ ≅ recΓt Γ2 ].
Proof.
  intros H. pose proof (eqctx_wf_l (i := lM) eq_refl H) as HΓ.
  pose proof (wf_recΓt _ _ HΓ) as HT. unfold recΓt in *.
  destruct (wfc_ext_inv HT) as (_ & HA & Hl). apply eqctx_ext_refl; [| exact HA | exact Hl].
  exact (eqctx_wkc _ _ _ _ 1 (_ :: gdCtx :: nil) H (wf_recGt (ctx_glob _ _ _ HΓ))).
Qed.

Lemma eqctx_brΓ {G Γ Γ2 wT wt l1 l2} k : k < nbr -> [ G ⊢[ lM ] Γ ≅ Γ2 ] ->
  [ brG k G ; brΓ k Γ wT wt l1 l2 ⊢[ lM ] ] ->
  [ brG k G ⊢[ lM ] brΓ k Γ wT wt l1 l2 ≅ brΓ k Γ2 wT wt l1 l2 ].
Proof.
  intros Hk H HB. unfold brΓ in *. apply eqctx_cexts; [| exact HB].
  pose proof (eqctx_wf_l (i := lM) eq_refl H) as HΓ.
  pose proof (wf_brG (ctx_glob _ _ _ HΓ) k Hk) as HG.
  rewrite <- (brDecls_len k Hk). exact (eqctx_wkc _ _ _ _ _ (brDecls k) H HG).
Qed.

(** ** Small facts about the relation *)

Lemma GEq_L {G G2} : GEq G G2 -> gL G2 = gL G.
Proof. intros (_ & _ & HL & _); exact HL. Qed.
Lemma GEq_wf2 {G G2} : GEq G G2 -> [ ⊢ G2 ].
Proof. intros (_ & HG2 & _); exact HG2. Qed.
Lemma GEq_lwf {G G2 l} : GEq G G2 -> lwf (gL G) l -> lwf (gL G2) l.
Proof. intros HE; now rewrite (GEq_L HE). Qed.
Lemma GEq_lequiv {G G2 l l'} : GEq G G2 -> lequiv (gL G) l l' -> lequiv (gL G2) l l'.
Proof. intros HE; now rewrite (GEq_L HE). Qed.

Lemma ac_ctx_sound' {G Δ Δ'} : ac_ctx G Δ Δ' -> [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ' ⊢[ lD ] ] -> [ G ⊢[ lD ] Δ ≅ Δ' ].
Proof. intros H; exact (proj1 (proj2 (proj2 (proj2 ac_sound_all))) _ _ _ H). Qed.

(** ** Annotations along the head spine (M6_DESIGN.md H10, M8_DESIGN.md)

    [spa G i Γ t x]: [x] is [t] with the annotations of the [app],
    [tmFst] and [tmSnd] nodes on its head spine (through [app], [uapp],
    [capp], [tapp], [tmFst], [tmSnd]) replaced by equal ones. Reduction
    and the neutral rules never read them. The η rules take their
    annotations from the type, so converting the type changes them; the
    conversion lemma carries [spa] on its terms. The equations are kept
    because the type of a second projection mentions its (changed)
    scrutinee: the change is absorbed up to declarative equality
    ([spa_eq]), not syntactically. *)

Inductive spa (G : gctx) (i : layer) (Γ : ctx) : tm -> tm -> Prop :=
| spa_refl t : spa G i Γ t t
| spa_app f f' l1 l2 A B l3 l4 A' B' s : spa G i Γ f f' ->
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
    [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
    spa G i Γ (app f l1 l2 A B s) (app f' l3 l4 A' B' s)
| spa_uapp f f' ls : spa G i Γ f f' -> spa G i Γ (uapp f ls) (uapp f' ls)
| spa_capp f f' Δ : spa G i Γ f f' -> spa G i Γ (capp f Δ) (capp f' Δ)
| spa_tapp f f' T : spa G i Γ f f' -> spa G i Γ (tapp f T) (tapp f' T)
| spa_fst f f' l1 l2 A B l3 l4 A' B' : spa G i Γ f f' ->
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
    [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
    spa G i Γ (tmFst l1 l2 A B f) (tmFst l3 l4 A' B' f')
| spa_snd f f' l1 l2 A B l3 l4 A' B' : spa G i Γ f f' ->
    lequiv (gL G) l1 l3 -> lequiv (gL G) l2 l4 -> [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ] ->
    [ G ; Γ ,, A @ l1 ⊢[ i ] B ≅ B' @ l2 ] ->
    spa G i Γ (tmSnd l1 l2 A B f) (tmSnd l3 l4 A' B' f').

Arguments spa_refl {G i Γ t}.

(** A non-spine head is only related to itself. *)
Ltac spa_triv :=
  repeat match goal with Hs : spa _ _ _ ?t ?x |- _ =>
    is_var x; tryif is_var t then fail else (inversion Hs; subst; clear Hs) end.

Lemma spa_whne {G i Γ t t'} : spa G i Γ t t' -> whne t -> whne t'.
Proof. induction 1; intros Hw; [exact Hw | ..]; inversion Hw; subst; constructor; auto. Qed.

Lemma spa_whnf {G i Γ t t'} : spa G i Γ t t' -> whnf t -> whnf t'.
Proof.
  intros H Hw. destruct H; [exact Hw | ..];
    inversion Hw; subst; apply whnf_ne; (eapply spa_whne; [econstructor; eassumption | eassumption]).
Qed.

Lemma spa_red {G i Γ t t'} : spa G i Γ t t' -> forall u, red t u -> exists u', red t' u' /\ spa G i Γ u u'.
Proof.
  induction 1; intros u Hr;
    first [ solve [exists u; split; [exact Hr | apply spa_refl]] | inversion Hr; subst ].
  (* β: the head is an abstraction or a pair, which only relates to itself *)
  all: try solve
    [ spa_triv; eexists; split; [econstructor; try first [eassumption | reflexivity] | apply spa_refl] ].
  (* congruence *)
  all: match goal with IH : forall u, red ?f u -> _, Hr' : red ?f ?f1 |- _ =>
         destruct (IH _ Hr') as (f3 & Hr3 & Hs3) end;
       eexists; split; [econstructor; exact Hr3 | econstructor; eassumption].
Qed.

Lemma spa_reds {G i Γ t t' u} : reds t u -> spa G i Γ t t' -> exists u', reds t' u' /\ spa G i Γ u u'.
Proof.
  intros H; revert t'; induction H as [t | t v u Htv Hvu IH]; intros t' Hs.
  - exists t'; split; [constructor | exact Hs].
  - destruct (spa_red Hs _ Htv) as (v' & Hv' & Hsv).
    destruct (IH _ Hsv) as (u' & Hu' & Hsu). exists u'; split; [econstructor; eassumption | exact Hsu].
Qed.

Lemma spa_app_inv {G i Γ f l1 l2 A B s x} : spa G i Γ (app f l1 l2 A B s) x ->
  exists f' l3 l4 A' B', x = app f' l3 l4 A' B' s /\ spa G i Γ f f'.
Proof. intros H; inversion H; subst; do 5 eexists; split; first [reflexivity | eassumption | apply spa_refl]. Qed.
Lemma spa_uapp_inv {G i Γ f ls x} : spa G i Γ (uapp f ls) x -> exists f', x = uapp f' ls /\ spa G i Γ f f'.
Proof. intros H; inversion H; subst; eexists; split; first [reflexivity | eassumption | apply spa_refl]. Qed.
Lemma spa_capp_inv {G i Γ f Δ x} : spa G i Γ (capp f Δ) x -> exists f', x = capp f' Δ /\ spa G i Γ f f'.
Proof. intros H; inversion H; subst; eexists; split; first [reflexivity | eassumption | apply spa_refl]. Qed.
Lemma spa_tapp_inv {G i Γ f T x} : spa G i Γ (tapp f T) x -> exists f', x = tapp f' T /\ spa G i Γ f f'.
Proof. intros H; inversion H; subst; eexists; split; first [reflexivity | eassumption | apply spa_refl]. Qed.
Lemma spa_fst_inv {G i Γ f l1 l2 A B x} : spa G i Γ (tmFst l1 l2 A B f) x ->
  exists f' l3 l4 A' B', x = tmFst l3 l4 A' B' f' /\ spa G i Γ f f'.
Proof. intros H; inversion H; subst; do 5 eexists; split; first [reflexivity | eassumption | apply spa_refl]. Qed.
Lemma spa_snd_inv {G i Γ f l1 l2 A B x} : spa G i Γ (tmSnd l1 l2 A B f) x ->
  exists f' l3 l4 A' B', x = tmSnd l3 l4 A' B' f' /\ spa G i Γ f f'.
Proof. intros H; inversion H; subst; do 5 eexists; split; first [reflexivity | eassumption | apply spa_refl]. Qed.

Lemma lequivs_refl {L ls} : Forall (lwf L) ls -> Forall2 (lequiv L) ls ls.
Proof. induction 1; constructor; [exact (lequiv_refl _ _ H) | exact IHForall]. Qed.

(** Related terms are equal. *)
Lemma spa_eq {G i Γ t x} : spa G i Γ t x -> typeof i = i ->
  forall T k, [ G ; Γ ⊢[ i ] t : T @ k ] -> [ G ; Γ ⊢[ i ] t ≅ x : T @ k ].
Proof.
  intros H Hi; induction H as [t | f f' l1 l2 A B l3 l4 A' B' s Hf IH E13 E24 EA EB | f f' ls Hf IH
    | f f' Δ Hf IH | f f' T0 Hf IH | f f' l1 l2 A B l3 l4 A' B' Hf IH E13 E24 EA EB
    | f f' l1 l2 A B l3 l4 A' B' Hf IH E13 E24 EA EB]; intros T k Hx.
  - exact (eqtm_refl _ _ _ _ _ _ Hx).
  - destruct (inv_app Hi Hx) as ((Hv & W1 & W2 & HA & HB & Hν & Hs) & Hk & HX).
    pose proof (eqtm_app _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hv E13 E24 HA EA EB (IH _ _ Hν)
                  (eqtm_refl _ _ _ _ _ _ Hs)) as Econg.
    eapply eqtm_conv; [exact (lvl_eq_eqtm Hk Econg) | rewrite Hi; exact HX].
  - destruct (inv_uapp Hi Hx) as (n0 & l0 & T1 & (-> & W0 & HT0 & Hlen & Hw & Hν) & Hk & HX).
    pose proof (eqtm_uapp _ _ _ _ _ _ _ _ _ W0 HT0 Hlen (lequivs_refl Hw) (IH _ _ Hν)) as Econg.
    eapply eqtm_conv; [exact (lvl_eq_eqtm Hk Econg) | exact HX].
  - destruct (inv_capp Hi Hx) as (l0 & T1 & (-> & W0 & HT0 & HΔ & Hν & HTΔ) & Hk & HX).
    pose proof (eqtm_capp _ _ _ _ _ _ _ _ W0 HT0 HΔ HΔ (eqc_refl _ _ _ HΔ) (eqty_refl _ _ _ _ _ HTΔ)
                  (IH _ _ Hν)) as Econg.
    eapply eqtm_conv; [exact (lvl_eq_eqtm Hk Econg) | exact HX].
  - destruct (inv_tapp Hi Hx) as (Δ0 & l0 & l0' & T1 & (-> & Hν & HΔ0 & W0 & W0' & HT0 & HA & HTA) & Hk & HX).
    pose proof (eqtm_tapp _ _ _ _ _ _ _ _ _ _ (IH _ _ Hν) HΔ0 W0 W0' HT0 HA (eqty_refl _ _ _ _ _ HA)
                  (eqty_refl _ _ _ _ _ HTA)) as Econg.
    eapply eqtm_conv; [exact (lvl_eq_eqtm Hk Econg) | exact HX].
  - destruct (inv_fst Hi Hx) as ((Hv & W1 & W2 & HA & HB & Hν) & Hk & HX).
    pose proof (eqtm_fst _ _ _ _ _ _ _ _ _ _ _ _ _ Hv E13 E24 HA EA EB (IH _ _ Hν)) as Econg.
    eapply eqtm_conv; [exact (lvl_eq_eqtm Hk Econg) | rewrite Hi; exact HX].
  - destruct (inv_snd Hi Hx) as ((Hv & W1 & W2 & HA & HB & Hν) & Hk & HX).
    pose proof (eqtm_snd _ _ _ _ _ _ _ _ _ _ _ _ _ Hv E13 E24 HA EA EB (IH _ _ Hν)) as Econg.
    eapply eqtm_conv; [exact (lvl_eq_eqtm Hk Econg) | rewrite Hi; exact HX].
Qed.

(** Weakenings, for the η rules. *)
Lemma spa_wk {G i Γ t x} : spa G i Γ t x -> typeof i = i ->
  forall Δ r, wkr r Δ Γ -> [ G ; Δ ⊢[ i ] ] -> spa G i Δ t⟨r⟩ x⟨r⟩.
Proof.
  destruct weakening_r as (_ & _ & Wty & _).
  intros H Hi; induction H; intros Δ1 r Hr HΔ; push_ren; try solve [constructor; auto].
  all: match goal with EA : [ _ ; _ ⊢[ _ ] ?A ≅ _ @ ?l1 ], E13 : lequiv _ ?l1 _ |- _ =>
         pose proof (Wty _ _ _ _ _ _ EA Hi _ _ Hr HΔ) as EA';
         assert (HΔA : [ G ; Δ1 ,, A⟨r⟩ @ l1 ⊢[ i ] ])
           by (apply wfc_ext; [exact HΔ | exact (eqty_wf_l Hi EA') | exact (lequiv_wf_l _ _ _ E13)]) end.
  all: econstructor; [auto | eassumption | eassumption | exact EA' |].
  all: eapply Wty; [eassumption | exact Hi | apply wkr_up'; [exact Hr | reflexivity] | exact HΔA].
Qed.

Lemma spa_uwk {G i Γ t x} n : spa G i Γ t x ->
  spa (gctx_uwk n G) i Γ⟨ush n⟩ᵤ t⟨ush n⟩ᵤ x⟨ush n⟩ᵤ.
Proof.
  unfold uren, URen_tm, URen_ctx; induction 1; cbn [uren_tm ucren]; try solve [constructor; auto].
  all: econstructor; [exact IHspa | exact (lequiv_ush n H0) | exact (lequiv_ush n H1)
                     | exact (uwk_eqty n H2) | exact (uwk_eqty n H3)].
Qed.

Lemma spa_gext {G i Γ t x} D : spa G i Γ t x -> [ ⊢ gext G D ] -> spa (gext G D) i Γ⟪S⟫ t⟪S⟫ x⟪S⟫.
Proof.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 gweakening))))) as Wty.
  intros H Hg; induction H; push_gren; try solve [constructor; auto].
  all: econstructor; [exact IHspa | exact H0 | exact H1 | |].
  all: match goal with |- [ _ ; _ ⊢[ _ ] ?A ≅ _ @ _ ] =>
         first [ exact (Wty _ _ _ _ _ _ H2 _ (D :: gΨ G) (gwk_step gwk_id) (le_n _)
                          (gwkwf_step _ _ _ _ (gwkwf_id _)) Hg)
               | exact (Wty _ _ _ _ _ _ H3 _ (D :: gΨ G) (gwk_step gwk_id) (le_n _)
                          (gwkwf_step _ _ _ _ (gwkwf_id _)) Hg) ] end.
Qed.

(** The [Π] η-expansions of related terms, at equal annotations. *)
Lemma spa_eta_pi {G i Γ l l' m m' A A2 B B2 y y'} : typeof i = i -> [ G ; Γ ,, A @ l ⊢[ i ] ] ->
  lequiv (gL G) l m -> lequiv (gL G) l' m' -> [ G ; Γ ⊢[ i ] A ≅ A2 @ l ] ->
  [ G ; Γ ,, A @ l ⊢[ i ] B ≅ B2 @ l' ] -> spa G i Γ y y' ->
  spa G i (Γ ,, A @ l) (app y⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0)) (app y'⟨↑⟩ m m' A2⟨↑⟩ B2⟨rlift ↑⟩ (var 0)).
Proof.
  destruct weakening_r as (Wt & _ & Wty & _).
  intros Hi HΓA E1 E2 EA EB Hy.
  assert (HΓAA : [ G ; Γ ,, A @ l ,, A⟨↑⟩ @ l ⊢[ i ] ]).
  { apply wfc_ext; [exact HΓA | exact (Wt _ _ _ _ _ (eqty_wf_l Hi EA) Hi _ _ (wkr_shift1 _ _ _) HΓA)
                   | exact (lequiv_wf_l _ _ _ E1)]. }
  apply spa_app; [exact (spa_wk Hy Hi _ _ (wkr_shift1 _ _ _) HΓA) | exact E1 | exact E2 | |].
  - exact (Wty _ _ _ _ _ _ EA Hi _ _ (wkr_shift1 _ _ _) HΓA).
  - exact (Wty _ _ _ _ _ _ EB Hi _ _ (wkr_up' _ _ _ _ _ _ (wkr_shift1 _ _ _) eq_refl) HΓAA).
Qed.


(** ** The statements *)

Definition C_ty G Γ T T' : Prop := forall i G2 Γ2 k k', compt i -> GEq G G2 -> [ G2 ⊢[ i ] Γ ≅ Γ2 ] ->
  [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T' @ k' ] -> ac_ty G2 Γ2 T T'.
Definition C_tynf G Γ T T' : Prop := forall i G2 Γ2 k k', compt i -> GEq G G2 -> [ G2 ⊢[ i ] Γ ≅ Γ2 ] ->
  [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T' @ k' ] -> ac_tynf G2 Γ2 T T'.
Definition C_tyne G Γ T T' : Prop := forall i G2 Γ2 k k', compt i -> GEq G G2 -> [ G2 ⊢[ i ] Γ ≅ Γ2 ] ->
  [ G ; Γ ⊢[ i ] T @ k ] -> [ G ; Γ ⊢[ i ] T' @ k' ] -> ac_tyne G2 Γ2 T T'.
Definition C_ctx G Δ Δ' : Prop := forall G2, GEq G G2 ->
  [ G ; Δ ⊢[ lD ] ] -> [ G ; Δ' ⊢[ lD ] ] -> ac_ctx G2 Δ Δ'.
Definition C_tm G Γ t t' T : Prop := forall i G2 Γ2 T2 k, compt i -> GEq G G2 -> [ G2 ⊢[ i ] Γ ≅ Γ2 ] ->
  [ G ; Γ ⊢[ i ] t : T @ k ] -> [ G ; Γ ⊢[ i ] t' : T @ k ] -> [ G2 ; Γ ⊢[ i ] T2 ≅ T @ k ] ->
  forall x x', spa G2 i Γ t x -> spa G2 i Γ t' x' -> ac_tm G2 Γ2 x x' T2.
Definition C_tmnf G Γ w w' W : Prop := forall i G2 Γ2 W2 k, compt i -> GEq G G2 -> [ G2 ⊢[ i ] Γ ≅ Γ2 ] ->
  [ G ; Γ ⊢[ i ] w : W @ k ] -> [ G ; Γ ⊢[ i ] w' : W @ k ] -> [ G2 ; Γ ⊢[ i ] W2 ≅ W @ k ] -> whnf_ty W2 ->
  forall x x', spa G2 i Γ w x -> spa G2 i Γ w' x' -> ac_tmnf G2 Γ2 x x' W2.
Definition C_ne G Γ ν ν' T : Prop := forall i G2 Γ2 k k' A A', compt i -> GEq G G2 -> [ G2 ⊢[ i ] Γ ≅ Γ2 ] ->
  [ G ; Γ ⊢[ i ] ν : A @ k ] -> [ G ; Γ ⊢[ i ] ν' : A' @ k' ] ->
  forall x x', spa G2 i Γ ν x -> spa G2 i Γ ν' x' ->
  exists T2, ac_tmne G2 Γ2 x x' T2 /\ [ G2 ; Γ ⊢[ i ] T2 ≅ T @ k ].
Definition C_nee G Γ ν ν' W : Prop := forall i G2 Γ2 k k' A A', compt i -> GEq G G2 -> [ G2 ⊢[ i ] Γ ≅ Γ2 ] ->
  [ G ; Γ ⊢[ i ] ν : A @ k ] -> [ G ; Γ ⊢[ i ] ν' : A' @ k' ] ->
  forall x x', spa G2 i Γ ν x -> spa G2 i Γ ν' x' ->
  exists W2, ac_tmnee G2 Γ2 x x' W2 /\ [ G2 ; Γ ⊢[ i ] W2 ≅ W @ k ].
Definition C_sub G Γ d d' Θ : Prop := forall i G2 Γ2 Θ2, compt i -> GEq G G2 -> [ G2 ⊢[ i ] Γ ≅ Γ2 ] ->
  [ G ; Θ ⊢[ i ] ] -> [ G ; Γ ⊢[ i ] d : Θ ] -> [ G ; Γ ⊢[ i ] d' : Θ ] -> [ G2 ⊢[ lD ] Θ ≅ Θ2 ] ->
  ac_sub G2 Γ2 d d' Θ2.

(** ** Types *)

Lemma C_act_red {G Γ T T' W W'} : reds_ty T W -> reds_ty T' W' -> whnf_ty W -> whnf_ty W' ->
  C_tynf G Γ W W' -> C_ty G Γ T T'.
Proof.
  intros Hr Hr' Hw Hw' IH i G2 Γ2 k k' Hc HE Hctx HT HT'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  pose proof (eqty_wf_r Hi (red_ty_sound Hc HT Hr Hw)) as HW.
  pose proof (eqty_wf_r Hi (red_ty_sound Hc HT' Hr' Hw')) as HW'.
  eapply act_red; [exact Hr | exact Hr' | exact Hw | exact Hw' | exact (IH i G2 Γ2 k k' Hc HE Hctx HW HW')].
Qed.

Lemma C_actnf_nat {G Γ} : C_tynf G Γ tyNat tyNat.
Proof. red; intros; apply actnf_nat. Qed.
Lemma C_actnf_U {G Γ l l'} : leqv l l' -> C_tynf G Γ (tyU l) (tyU l').
Proof. intros Hl; red; intros; now apply actnf_U. Qed.

Lemma C_actnf_pi {G Γ l1 l2 l3 l4 A A' B B'} : leqv l1 l3 -> leqv l2 l4 ->
  ac_ty G Γ A A' -> C_ty G Γ A A' -> C_ty G (Γ ,, A @ l1) B B' ->
  C_tynf G Γ (tyPi l1 l2 A B) (tyPi l3 l4 A' B').
Proof.
  intros H13 H24 DA IHA IHB i G2 Γ2 k k' Hc HE Hctx HT HT'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_pi HT) as ((Hv & W1 & W2 & HA & HB) & _).
  destruct (inv_ty_pi HT') as ((_ & W3 & W4 & HA' & HB') & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E13)) as EA.
  assert (HΓA : [ G ; Γ ,, A @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact (ctx_of_wf_ty Hi HA) | exact HA | exact W1]).
  assert (EA' : [ G ; Γ ⊢[ i ] A' ≅ A @ l3 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E13)]).
  pose proof (stab_ty Hi EA' (lequiv_sym _ _ _ E13) HΓA HB') as HB1.
  apply actnf_pi; [exact H13 | exact H24 | exact (IHA i G2 Γ2 l1 l3 Hc HE Hctx HA HA') |].
  apply (IHB i G2 (Γ2 ,, A @ l1) l2 l4 Hc HE); [| exact HB | exact HB1].
  exact (eqctx_ext_refl Hctx (gconv_ty HE HA) (GEq_lwf HE W1)).
Qed.

Lemma C_actnf_ne {G Γ V V'} : C_tyne G Γ V V' -> C_tynf G Γ V V'.
Proof. intros IH i G2 Γ2 k k' Hc HE Hctx HT HT'. apply actnf_ne. exact (IH i G2 Γ2 k k' Hc HE Hctx HT HT'). Qed.

Lemma C_actnf_CTyp {G Γ Δ Δ' l l'} : C_ctx G Δ Δ' -> leqv l l' -> C_tynf G Γ (tyCTyp Δ l) (tyCTyp Δ' l').
Proof.
  intros IH Hl i G2 Γ2 k k' Hc HE Hctx HT HT'.
  destruct (inv_ty_CTyp HT) as ((_ & _ & HΔ & _) & _). destruct (inv_ty_CTyp HT') as ((_ & _ & HΔ' & _) & _).
  apply actnf_CTyp; [exact (IH G2 HE HΔ HΔ') | exact Hl].
Qed.

Lemma C_actnf_CTrm {G Γ Δ Δ' T T' l l'} : ac_ctx G Δ Δ' -> C_ctx G Δ Δ' -> C_ty G Δ T T' -> leqv l l' ->
  C_tynf G Γ (tyCTrm Δ T l) (tyCTrm Δ' T' l').
Proof.
  intros Dc IHc IHT Hl i G2 Γ2 k k' Hc HE Hctx HX HX'.
  destruct (inv_ty_CTrm HX) as ((_ & _ & HΔ & HT & W) & _).
  destruct (inv_ty_CTrm HX') as ((_ & _ & HΔ' & HT' & W') & _).
  pose proof (leqv_lequiv _ _ _ W W' Hl) as E.
  pose proof (ac_ctx_sound' Dc HΔ HΔ') as Ec.
  pose proof (decl_ty_ctxconv_D (eqctx_sym_D Ec) HT' (lequiv_sym _ _ _ E)) as HT1.
  apply actnf_CTrm; [exact (IHc G2 HE HΔ HΔ') | | exact Hl].
  exact (IHT lD G2 Δ l l compt_D HE (eqc_refl _ _ _ (gconv_ctx HE compt_D HΔ)) HT HT1).
Qed.

Lemma C_actnf_upi {G Γ n l l' T T'} : leqv l l' -> C_ty (gctx_uwk n G) Γ⟨ush n⟩ᵤ T T' ->
  C_tynf G Γ (tyUPi n l T) (tyUPi n l' T').
Proof.
  intros Hl IH i G2 Γ2 k k' Hc HE Hctx HX HX'.
  destruct (inv_ty_upi HX) as ((-> & _ & _ & _ & HT) & _). destruct (inv_ty_upi HX') as ((_ & _ & _ & _ & HT') & _).
  apply actnf_upi; [exact Hl |].
  exact (IH lM (gctx_uwk n G2) Γ2⟨ush n⟩ᵤ l l' compt_M (GEq_uwk n HE) (uwk_eqctx n Hctx) HT HT').
Qed.

Lemma C_actnf_cpi {G Γ l l' T T'} : leqv l l' -> C_ty (gext G gdCtx) Γ⟪S⟫ T T' ->
  C_tynf G Γ (tyCPi l T) (tyCPi l' T').
Proof.
  intros Hl IH i G2 Γ2 k k' Hc HE Hctx HX HX'.
  destruct (inv_ty_cpi HX) as ((-> & _ & _ & HT) & _). destruct (inv_ty_cpi HX') as ((_ & _ & _ & HT') & _).
  pose proof (GEq_ext_same HE (ctx_glob _ _ _ (ctx_of_wf_ty (i := lM) eq_refl HT))) as HE1.
  apply actnf_cpi; [exact Hl |].
  exact (IH lM _ Γ2⟪S⟫ l l' compt_M HE1 (eqctx_gext (GEq_wf2 HE1) Hctx) HT HT').
Qed.

Lemma C_actnf_tpi {G Γ Δ Δ' l1 l2 l3 l4 T T'} : ac_ctx G Δ Δ' -> C_ctx G Δ Δ' -> leqv l1 l3 -> leqv l2 l4 ->
  C_ty (gext G (gdTy Δ lD l1)) Γ⟪S⟫ T T' -> C_tynf G Γ (tyTPi Δ l1 l2 T) (tyTPi Δ' l3 l4 T').
Proof.
  intros Dc IHc H13 H24 IH i G2 Γ2 k k' Hc HE Hctx HX HX'.
  destruct (inv_ty_tpi HX) as ((-> & HΓ & HΔ & W1 & W2 & HT) & _).
  destruct (inv_ty_tpi HX') as ((_ & _ & HΔ' & W3 & W4 & HT') & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (ac_ctx_sound' Dc HΔ HΔ') as Ec.
  pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (HGD : [ ⊢ gext G (gdTy Δ lD l1) ]) by (apply wfg_ty; auto).
  pose proof (gbind_obj_ty (lle_refl lD) ltac:(discriminate) HGD Ec E13) as Ho.
  pose proof (gbind_ty HG HGD Ho HT') as HT1.
  pose proof (GEq_ext_same HE HGD) as HE1.
  apply actnf_tpi; [exact (IHc G2 HE HΔ HΔ') | exact H13 | exact H24 |].
  exact (IH lM _ Γ2⟪S⟫ l2 l4 compt_M HE1 (eqctx_gext (GEq_wf2 HE1) Hctx) HT HT1).
Qed.

Lemma C_actne_gvar {G Γ U Δ i' l d d'} : in_gctx (gΨ G) U (gdTy Δ i' l) -> C_sub G Γ d d' Δ ->
  C_tyne G Γ (tyGvar U d) (tyGvar U d').
Proof.
  intros Hin IH i G2 Γ2 k k' Hc HE Hctx HX HX'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_gvar HX) as (Δ0 & i0 & l0 & (Hv & HΓ & Hin0 & Hle & Ht & Hn & He) & _).
  destruct (inv_ty_gvar HX') as (Δ1 & i1 & l1 & (_ & _ & Hin1 & _ & Ht' & Hn' & He') & _).
  pose proof (in_gctx_det Hin Hin0) as E0. injection E0 as <- <- <-.
  pose proof (in_gctx_det Hin Hin1) as E1. injection E1 as <- <- <-.
  rewrite Hi in HΓ.
  destruct (gctx_decl_ok _ _ _ (ctx_glob _ _ _ HΓ) Hin) as (HΔ & _).
  pose proof (lift_ctx HΔ (lle_D_compt _ Hc)) as HΔi.
  destruct HE as (HG & HG2 & HL & Hl). destruct (Hl _ _ Hin) as (D2 & Hin2 & HD2).
  destruct D2 as [| Δ2 i2 l2 | |]; cbn in HD2; try contradiction. destruct HD2 as (-> & _ & _ & HΔΔ).
  eapply actne_gvar; [exact Hin2 |].
  exact (IH i G2 Γ2 Δ2 Hc (conj HG (conj HG2 (conj HL Hl))) Hctx HΔi
           (lsub_wf_prem Hi HΓ Ht Hn He) (lsub_wf_prem Hi HΓ Ht' Hn' He') HΔΔ).
Qed.

Lemma C_actne_El {G Γ l l' ν ν' W} : leqv l l' -> C_nee G Γ ν ν' W -> C_tyne G Γ (tyEl l ν) (tyEl l' ν').
Proof.
  intros Hl IH i G2 Γ2 k k' Hc HE Hctx HX HX'.
  destruct (inv_ty_El HX) as ((_ & _ & Hν) & _). destruct (inv_ty_El HX') as ((_ & _ & Hν') & _).
  destruct (IH i G2 Γ2 _ _ _ _ Hc HE Hctx Hν Hν' _ _ spa_refl spa_refl) as (W2 & X & _).
  eapply actne_El; [exact Hl | exact X].
Qed.

(** [Vec] and [Fin] at a neutral length (M14a). *)
Lemma C_actne_vec {G Γ l l' A A' ν ν' W} : leqv l l' -> C_ty G Γ A A' -> C_nee G Γ ν ν' W ->
  C_tyne G Γ (tyVec l A ν) (tyVec l' A' ν').
Proof.
  intros Hl IHA IH i G2 Γ2 k k' Hc HE Hctx HX HX'.
  destruct (inv_ty_vec HX) as ((_ & _ & HA & Hν) & _). destruct (inv_ty_vec HX') as ((_ & _ & HA' & Hν') & _).
  destruct (IH i G2 Γ2 _ _ _ _ Hc HE Hctx Hν Hν' _ _ spa_refl spa_refl) as (W2 & X & _).
  eapply actne_vec; [exact Hl | exact (IHA i G2 Γ2 _ _ Hc HE Hctx HA HA') | exact X].
Qed.

Lemma C_actne_fin {G Γ ν ν' W} : C_nee G Γ ν ν' W -> C_tyne G Γ (tyFin ν) (tyFin ν').
Proof.
  intros IH i G2 Γ2 k k' Hc HE Hctx HX HX'.
  destruct (inv_ty_fin HX) as ((_ & Hν) & _). destruct (inv_ty_fin HX') as ((_ & Hν') & _).
  destruct (IH i G2 Γ2 _ _ _ _ Hc HE Hctx Hν Hν' _ _ spa_refl spa_refl) as (W2 & X & _).
  eapply actne_fin; exact X.
Qed.

(** ** Local contexts (at D) *)

Lemma C_acc_nil {G} : C_ctx G cnil cnil.
Proof. red; intros; apply acc_nil. Qed.
Lemma C_acc_var {G g} : C_ctx G (cvar g) (cvar g).
Proof. red; intros; apply acc_var. Qed.

Lemma C_acc_ext {G Γ Γ' A A' l l'} : ac_ctx G Γ Γ' -> C_ctx G Γ Γ' -> C_ty G Γ A A' -> leqv l l' ->
  C_ctx G (Γ ,, A @ l) (Γ' ,, A' @ l').
Proof.
  intros Dc IHc IHA Hl G2 HE H H'.
  destruct (wfc_ext_inv H) as (HΓ & HA & W). destruct (wfc_ext_inv H') as (HΓ' & HA' & W').
  pose proof (leqv_lequiv _ _ _ W W' Hl) as E.
  pose proof (ac_ctx_sound' Dc HΓ HΓ') as Ec.
  pose proof (decl_ty_ctxconv_D (eqctx_sym_D Ec) HA' (lequiv_sym _ _ _ E)) as HA1.
  apply acc_ext; [exact (IHc G2 HE HΓ HΓ') | | exact Hl].
  exact (IHA lD G2 Γ l l compt_D HE (eqc_refl _ _ _ (gconv_ctx HE compt_D HΓ)) HA HA1).
Qed.

(** ** Terms *)

(** Normalization of a typed type, with its equation. *)
Lemma tgt_whnf {G i Γ T k} : compt i -> [ G ; Γ ⊢[ i ] T @ k ] ->
  exists W, reds_ty T W /\ whnf_ty W /\ [ G ; Γ ⊢[ i ] T ≅ W @ k ].
Proof.
  intros Hc HT. destruct Hc as [-> | ->].
  - destruct (decl_whnf_tyred HT) as (W & HW & Hw).
    exists W; exact (conj (tyred_red _ _ _ _ _ _ HW) (conj Hw (tyred_eq _ _ _ _ _ _ HW))).
  - destruct (declM_whnf_tyred HT) as (W & HW & Hw).
    exists W; exact (conj (tyred_red _ _ _ _ _ _ HW) (conj Hw (tyred_eq _ _ _ _ _ _ HW))).
Qed.

(** A whnf type equal to a positive one is positive. *)
Lemma posty_head W W2 : posty W -> whnf_ty W2 -> ty_head W2 = ty_head W -> posty W2.
Proof.
  intros Hp Hw2 E. destruct Hp;
    try match goal with Hn : whne_ty ?V |- _ => rewrite (whne_ty_head V Hn) in E end;
    destruct W2; cbn in E; try discriminate;
    first [ apply posty_nat | apply posty_U | apply posty_CTyp | apply posty_CTrm | apply posty_id | apply posty_sum
          | apply posty_W | apply posty_wf | apply posty_ne; inversion Hw2; subst; first [assumption | constructor] ].
Qed.

Lemma head_pi W : ty_head W = 3 -> exists m m' A B, W = tyPi m m' A B.
Proof. destruct W; cbn; intros E; try discriminate; eauto. Qed.
Lemma head_sum W : ty_head W = 16 -> exists m m' A B, W = tySum m m' A B.
Proof. destruct W; cbn; intros E; try discriminate; eauto. Qed.
Lemma head_W W : ty_head W = 17 -> exists m m' A B, W = tyW m m' A B.
Proof. destruct W; cbn; intros E; try discriminate; eauto. Qed.
Lemma head_wf W : ty_head W = 18 -> exists m A N, W = tyWf m A N.
Proof. destruct W; cbn; intros E; try discriminate; eauto. Qed.
Lemma head_upi W : ty_head W = 6 -> exists n m T, W = tyUPi n m T.
Proof. destruct W; cbn; intros E; try discriminate; eauto. Qed.
Lemma head_cpi W : ty_head W = 7 -> exists m T, W = tyCPi m T.
Proof. destruct W; cbn; intros E; try discriminate; eauto. Qed.
Lemma head_tpi W : ty_head W = 8 -> exists Δ m m' T, W = tyTPi Δ m m' T.
Proof. destruct W; cbn; intros E; try discriminate; eauto. Qed.
Lemma head_sig W : ty_head W = 10 -> exists m m' A B, W = tySig m m' A B.
Proof. destruct W; cbn; intros E; try discriminate; eauto. Qed.

(** The head of the new type, from its equation with the old. *)
Ltac new_head Hc EW Hw2 W :=
  let E := fresh "Eh" in
  pose proof (decl_head_c Hc EW Hw2 ltac:(auto with whnf)) as E; cbn [ty_head] in E;
  destruct W; cbn [ty_head] in E; try discriminate; clear E.

Lemma C_actm_red {G Γ t t' T w w' W} : reds_ty T W -> whnf_ty W -> reds t w -> reds t' w' ->
  whnf w -> whnf w' -> C_tmnf G Γ w w' W -> C_tm G Γ t t' T.
Proof.
  intros HrT HwT Hr Hr' Hw Hw' IH i G2 Γ2 T2 k Hc HE Hctx Ht Ht' ET2 x x' Hsx Hsx'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  pose proof (red_ty_sound Hc (wf_tm_ty Hi Ht) HrT HwT) as ET.
  pose proof (red_tm_sound Hc Ht Hr Hw) as Et. pose proof (red_tm_sound Hc Ht' Hr' Hw') as Et'.
  assert (EW : [ G ; Γ ⊢[ typeof i ] W ≅ T @ k ]) by (rewrite Hi; exact (eqty_sym _ _ _ _ _ _ ET)).
  destruct (tgt_whnf Hc (eqty_wf_l Hi ET2)) as (W2 & HrT2 & HwT2 & ET2W).
  assert (EW2 : [ G2 ; Γ ⊢[ i ] W2 ≅ W @ k ]).
  { eapply eqty_trans; [exact (eqty_sym _ _ _ _ _ _ ET2W) |].
    eapply eqty_trans; [exact ET2 | exact (gconv_eqty HE Hi ET)]. }
  destruct (spa_reds Hr Hsx) as (u & Hu & Hsu). destruct (spa_reds Hr' Hsx') as (u' & Hu' & Hsu').
  eapply actm_red; [exact HrT2 | exact HwT2 | exact Hu | exact Hu' | exact (spa_whnf Hsu Hw)
                   | exact (spa_whnf Hsu' Hw') |].
  exact (IH i G2 Γ2 W2 k Hc HE Hctx (wf_conv _ _ _ _ _ _ _ (eqtm_wf_r Hi Et) EW)
           (wf_conv _ _ _ _ _ _ _ (eqtm_wf_r Hi Et') EW) EW2 HwT2 _ _ Hsu Hsu').
Qed.

Lemma C_actmnf_code_nat {G Γ l} : C_tmnf G Γ tmNat tmNat (tyU l).
Proof. red; intros i G2 Γ2 W2 k Hc HE Hctx Ht Ht' EW Hw2 x x' Hsx Hsx'. spa_triv. new_head Hc EW Hw2 W2. apply actmnf_code_nat. Qed.

Lemma C_actmnf_code_U {G Γ l k k'} : leqv k k' -> C_tmnf G Γ (tmU k) (tmU k') (tyU l).
Proof.
  intros Hl; red; intros i G2 Γ2 W2 kk Hc HE Hctx Ht Ht' EW Hw2 x x' Hsx Hsx'. spa_triv. new_head Hc EW Hw2 W2.
  apply actmnf_code_U; exact Hl.
Qed.

Lemma C_actmnf_code_pi {G Γ l l1 l2 l3 l4 s s' t t'} : leqv l1 l3 -> leqv l2 l4 ->
  ac_tm G Γ s s' (tyU l1) -> C_tm G Γ s s' (tyU l1) -> C_tm G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) ->
  C_tmnf G Γ (tmPi l1 l2 s t) (tmPi l3 l4 s' t') (tyU l).
Proof.
  intros H13 H24 Ds IHs IHt i G2 Γ2 W2 k Hc HE Hctx Hx Hx' EW Hw2 x x' Hsx Hsx'. spa_triv. pose proof (compt_typeof_self _ Hc) as Hi.
  new_head Hc EW Hw2 W2.
  destruct (inv_code_pi Hi Hx) as ((Hv & W1 & W2 & Hs & Ht) & _).
  destruct (inv_code_pi Hi Hx') as ((_ & W3 & W4 & Hs' & Ht') & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (ctx_of_wf_tm Hi Hs) as HΓ.
  assert (HΓt : [ G ; Γ ⊢[ typeof i ] ]) by (rewrite Hi; exact HΓ).
  assert (EU1 : [ G ; Γ ⊢[ i ] tyU l1 ≅ tyU l3 @ lsuc l1 ]) by (apply eqty_U; assumption).
  assert (Hs1 : [ G ; Γ ⊢[ i ] s' : tyU l1 @ lsuc l1 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Hs' | exact (lequiv_suc _ _ _ E13)] | rewrite Hi; exact EU1]. }
  pose proof (ac_tm_sound Hc Ds Hs Hs1) as Es.
  assert (Es' : [ G ; Γ ⊢[ i ] s' ≅ s : tyU l3 @ lsuc l3 ]).
  { eapply eqtm_lconv; [| exact (lequiv_suc _ _ _ (lequiv_sym _ _ _ E13))].
    eapply eqtm_conv; [exact (eqtm_sym _ _ _ _ _ _ _ Es) | rewrite Hi; exact (eqty_sym _ _ _ _ _ _ EU1)]. }
  assert (EEl : [ G ; Γ ⊢[ i ] tyEl l3 s' ≅ tyEl l1 s @ l3 ])
    by (apply eqty_El; [exact Hv | exact (lequiv_sym _ _ _ E13) | exact Es']).
  assert (HEl : [ G ; Γ ⊢[ i ] tyEl l1 s @ l1 ]) by (apply wft_El; assumption).
  assert (HΓ1 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HEl | exact W1]).
  pose proof (stab_tm Hi EEl (lequiv_sym _ _ _ E13) HΓ1 Ht') as Ht1.
  assert (EU2 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] tyU l2 ≅ tyU l4 @ lsuc l2 ])
    by (apply eqty_U; [exact Hv | rewrite Hi; exact HΓ1 | exact E24]).
  assert (Ht2 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t' : tyU l2 @ lsuc l2 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Ht1 | exact (lequiv_suc _ _ _ E24)] | rewrite Hi; exact EU2]. }
  apply actmnf_code_pi; [exact H13 | exact H24 | |].
  - exact (IHs i G2 Γ2 (tyU l1) (lsuc l1) Hc HE Hctx Hs Hs1 (eqty_refl _ _ _ _ _ (gconv_ty HE (wf_tm_ty Hi Hs))) _ _ spa_refl spa_refl).
  - apply (IHt i G2 (Γ2 ,, tyEl l1 s @ l1) (tyU l2) (lsuc l2) Hc HE); [| exact Ht | exact Ht2 | | exact spa_refl | exact spa_refl].
    + exact (eqctx_ext_refl Hctx (gconv_ty HE HEl) (GEq_lwf HE W1)).
    + exact (eqty_refl _ _ _ _ _ (gconv_ty HE (wf_tm_ty Hi Ht))).
Qed.

Lemma C_actmnf_zero {G Γ} : C_tmnf G Γ zero zero tyNat.
Proof. red; intros i G2 Γ2 W2 k Hc HE Hctx Ht Ht' EW Hw2 x x' Hsx Hsx'. spa_triv. new_head Hc EW Hw2 W2. apply actmnf_zero. Qed.

Lemma C_actmnf_succ {G Γ t t'} : C_tm G Γ t t' tyNat -> C_tmnf G Γ (succ t) (succ t') tyNat.
Proof.
  intros IH i G2 Γ2 W2 k Hc HE Hctx Hx Hx' EW Hw2 x x' Hsx Hsx'. spa_triv. pose proof (compt_typeof_self _ Hc) as Hi.
  new_head Hc EW Hw2 W2.
  destruct (inv_succ Hi Hx) as ((Hv & Ht) & _). destruct (inv_succ Hi Hx') as ((_ & Ht') & _).
  apply actmnf_succ.
  exact (IH i G2 Γ2 tyNat lzero Hc HE Hctx Ht Ht' (eqty_refl _ _ _ _ _ (gconv_ty HE (wf_tm_ty Hi Ht))) _ _ spa_refl spa_refl).
Qed.

Lemma C_actmnf_ne {G Γ ν ν' W W'} : posty W -> C_nee G Γ ν ν' W' -> C_tmnf G Γ ν ν' W.
Proof.
  intros Hp IH i G2 Γ2 W2 k Hc HE Hctx Hν Hν' EW Hw2 x x' Hsx Hsx'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  assert (HwW : whnf_ty W) by (destruct Hp; auto with whnf).
  pose proof (decl_head_c Hc EW Hw2 HwW) as Eh.
  destruct (IH i G2 Γ2 _ _ _ _ Hc HE Hctx Hν Hν' x x' Hsx Hsx') as (W3 & X & _).
  eapply actmnf_ne; [exact (posty_head _ _ Hp Hw2 Eh) | exact X].
Qed.

Lemma C_actmnf_eta {G Γ l l' A B w w'} :
  C_tm G (Γ ,, A @ l) (app w⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0)) (app w'⟨↑⟩ l l' A⟨↑⟩ B⟨rlift ↑⟩ (var 0)) B ->
  C_tmnf G Γ w w' (tyPi l l' A B).
Proof.
  intros IH i G2 Γ2 W2 k Hc HE Hctx Hw Hw' EW Hw2 x x' Hsx Hsx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (head_pi W2 (decl_head_c Hc EW Hw2 (whnf_tyPi _ _ _ _))) as (m & m' & A2 & B2 & ->).
  destruct (inv_ty_pi (wf_tm_ty Hi Hw)) as ((Hv & W1 & W3 & HA & HB) & Hk).
  pose proof (lvl_eq_tm' Hk Hw) as Hw1. pose proof (lvl_eq_tm' Hk Hw') as Hw1'.
  destruct (pi_inj_c Hc (eqty_sym _ _ _ _ _ _ EW)) as (Em & Em' & EA & EB).
  assert (Hctx' : [ G2 ⊢[ i ] Γ ,, A @ l ≅ Γ2 ,, A2 @ m ])
    by (apply eqc_ext; [exact Hctx | exact (gconv_ty HE HA) | exact EA | exact (lequiv_sym _ _ _ Em)]).
  pose proof (IH i G2 (Γ2 ,, A2 @ m) B2 l' Hc HE Hctx' (pre_eta_body Hi Hv W1 W3 HA HB Hw1)
                (pre_eta_body Hi Hv W1 W3 HA HB Hw1') (eqty_sym _ _ _ _ _ _ EB)) as X.
  pose proof (gconv_ty HE HA) as HA2.
  assert (HΓA : [ G2 ; Γ ,, A @ l ⊢[ i ] ])
    by (apply wfc_ext; [exact (ctx_of_wf_ty Hi HA2) | exact HA2 | exact (GEq_lwf HE W1)]).
  apply actmnf_eta.
  exact (X _ _ (spa_eta_pi Hi HΓA (lequiv_sym _ _ _ Em) (lequiv_sym _ _ _ Em') EA EB Hsx)
               (spa_eta_pi Hi HΓA (lequiv_sym _ _ _ Em) (lequiv_sym _ _ _ Em') EA EB Hsx')).
Qed.

Lemma wfg_gext {G D} : [ ⊢ G ] -> decl_ok G D -> decl_layer D -> [ ⊢ gext G D ].
Proof. destruct G; apply wfg_cons. Qed.

Lemma C_actmnf_ueta {G Γ n l T w w'} :
  C_tm (gctx_uwk n G) Γ⟨ush n⟩ᵤ (uapp w⟨ush n⟩ᵤ (ubvars n)) (uapp w'⟨ush n⟩ᵤ (ubvars n)) T ->
  C_tmnf G Γ w w' (tyUPi n l T).
Proof.
  intros IH i G2 Γ2 W2 k Hc HE Hctx Hw Hw' EW Hw2 x x' Hsx Hsx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_upi (wf_tm_ty Hi Hw)) as ((-> & HΓ & Hn & W & HT) & Hk).
  destruct (head_upi W2 (decl_head_c Hc EW Hw2 (whnf_tyUPi _ _ _))) as (n2 & m & T2 & ->).
  destruct (declM_upi_inj (eqty_sym _ _ _ _ _ _ EW)) as (-> & _ & ET).
  pose proof (lvl_eq_tm' Hk Hw) as Hw1. pose proof (lvl_eq_tm' Hk Hw') as Hw1'.
  apply actmnf_ueta.
  exact (IH lM (gctx_uwk n G2) Γ2⟨ush n⟩ᵤ T2 l compt_M (GEq_uwk n HE) (uwk_eqctx n Hctx)
           (wf_ueta_body W HT Hw1) (wf_ueta_body W HT Hw1') (eqty_sym _ _ _ _ _ _ ET)
           _ _ (spa_uapp _ _ _ _ _ _ (spa_uwk n Hsx)) (spa_uapp _ _ _ _ _ _ (spa_uwk n Hsx'))).
Qed.

Lemma C_actmnf_ceta {G Γ l T w w'} :
  C_tm (gext G gdCtx) Γ⟪S⟫ (capp w⟪S⟫ (cvar 0)) (capp w'⟪S⟫ (cvar 0)) T -> C_tmnf G Γ w w' (tyCPi l T).
Proof.
  intros IH i G2 Γ2 W2 k Hc HE Hctx Hw Hw' EW Hw2 x x' Hsx Hsx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_cpi (wf_tm_ty Hi Hw)) as ((-> & HΓ & W & HT) & Hk).
  destruct (head_cpi W2 (decl_head_c Hc EW Hw2 (whnf_tyCPi _ _))) as (m & T2 & ->).
  destruct (declM_cpi_inj (eqty_sym _ _ _ _ _ _ EW)) as (_ & ET).
  pose proof (lvl_eq_tm' Hk Hw) as Hw1. pose proof (lvl_eq_tm' Hk Hw') as Hw1'.
  pose proof (GEq_ext_same HE (ctx_glob _ _ _ (ctx_of_wf_ty (i := lM) eq_refl HT))) as HE1.
  apply actmnf_ceta.
  exact (IH lM _ Γ2⟪S⟫ T2 l compt_M HE1 (eqctx_gext (GEq_wf2 HE1) Hctx)
           (wf_ceta_body W HT Hw1) (wf_ceta_body W HT Hw1') (eqty_sym _ _ _ _ _ _ ET)
           _ _ (spa_capp _ _ _ _ _ _ (spa_gext _ Hsx (GEq_wf2 HE1)))
           (spa_capp _ _ _ _ _ _ (spa_gext _ Hsx' (GEq_wf2 HE1)))).
Qed.

Lemma C_actmnf_teta {G Γ Δ l l' T w w'} :
  C_tm (gext G (gdTy Δ lD l)) Γ⟪S⟫ (tapp w⟪S⟫ (tyGvar 0 (lshift 0))) (tapp w'⟪S⟫ (tyGvar 0 (lshift 0))) T ->
  C_tmnf G Γ w w' (tyTPi Δ l l' T).
Proof.
  intros IH i G2 Γ2 W2 k Hc HE Hctx Hw Hw' EW Hw2 x x' Hsx Hsx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_tpi (wf_tm_ty Hi Hw)) as ((-> & HΓ & HΔ & W1 & W3 & HT) & Hk).
  destruct (head_tpi W2 (decl_head_c Hc EW Hw2 (whnf_tyTPi _ _ _ _))) as (Δ2 & m & m' & T2 & ->).
  destruct (declM_tpi_inj (eqty_sym _ _ _ _ _ _ EW)) as (HΔΔ & Em & _ & ET).
  pose proof (lvl_eq_tm' Hk Hw) as Hw1. pose proof (lvl_eq_tm' Hk Hw') as Hw1'.
  pose proof (ctx_glob _ _ _ (ctx_of_wf_ty (i := lM) eq_refl HT)) as HGD.
  pose proof (GEq_ext_same HE HGD) as HE0.
  pose proof (GEq_wf2 HE) as HG2.
  assert (HGD2 : [ ⊢ gext G2 (gdTy Δ2 lD m) ]).
  { apply (wfg_gext HG2); [split; [exact (eqctx_wf_r (i := lD) eq_refl HΔΔ) | exact (lequiv_wf_l _ _ _ Em)]
                         | right; reflexivity]. }
  assert (Hd : gdecl_eq G2 (gdTy Δ lD l) (gdTy Δ2 lD m))
    by exact (conj eq_refl (conj (or_intror eq_refl) (conj (lequiv_sym _ _ _ Em) HΔΔ))).
  pose proof (GEq_ext HE HGD HGD2 Hd) as HE1.
  pose proof (GEq_ext (GEq_refl _ HG2) (GEq_wf2 HE0) HGD2 Hd) as HE2.
  apply actmnf_teta.
  exact (IH lM _ Γ2⟪S⟫ T2 l' compt_M HE1 (eqctx_gext HGD2 Hctx)
           (wf_teta_body HΔ W1 W3 HT Hw1) (wf_teta_body HΔ W1 W3 HT Hw1')
           (eqty_sym _ _ _ _ _ _ (gconv_eqty HE2 eq_refl ET))
           _ _ (spa_tapp _ _ _ _ _ _ (spa_gext _ Hsx HGD2)) (spa_tapp _ _ _ _ _ _ (spa_gext _ Hsx' HGD2))).
Qed.

Lemma C_actmnf_boxT {G Γ Δ l T T'} : ty_leq T T' -> C_tmnf G Γ (boxT T) (boxT T') (tyCTyp Δ l).
Proof.
  intros H; red; intros i G2 Γ2 W2 k Hc HE Hctx Ht Ht' EW Hw2 x x' Hsx Hsx'. spa_triv. new_head Hc EW Hw2 W2.
  apply actmnf_boxT; exact H.
Qed.

Lemma C_actmnf_boxt {G Γ Δ A l t t'} : tm_leq t t' -> C_tmnf G Γ (boxt t) (boxt t') (tyCTrm Δ A l).
Proof.
  intros H; red; intros i G2 Γ2 W2 k Hc HE Hctx Ht Ht' EW Hw2 x x' Hsx Hsx'. spa_triv. new_head Hc EW Hw2 W2.
  apply actmnf_boxt; exact H.
Qed.

(** ** Neutral terms *)

Lemma lvl_eq_G2 {G G2 k l} : GEq G G2 -> lvl_eq (gL G) k l -> lvl_eq (gL G2) k l.
Proof. intros HE; now rewrite (GEq_L HE). Qed.

Lemma gconv_lsub {G G2 i Γ d Θ} : GEq G G2 -> compt i -> [ G ; Γ ⊢[ i ] d : Θ ] -> [ G2 ; Γ ⊢[ i ] d : Θ ].
Proof.
  intros HE Hc [Hx Hn Ht Hv]. pose proof (compt_typeof_self _ Hc) as Hi.
  constructor; [rewrite Hi in Hx |- *; exact (gconv_ctx HE Hc Hx) | exact Hn | exact Ht |].
  intros n T l Hin. exact (gconv_tm HE Hi (Hv _ _ _ Hin)).
Qed.

Lemma ac_ne_sound' {G Γ ν ν' T i k k' A A'} : ac_tmne G Γ ν ν' T -> compt i ->
  [ G ; Γ ⊢[ i ] ν : A @ k ] -> [ G ; Γ ⊢[ i ] ν' : A' @ k' ] ->
  [ G ; Γ ⊢[ i ] A ≅ T @ k ] /\ [ G ; Γ ⊢[ i ] A' ≅ T @ k' ] /\ [ G ; Γ ⊢[ i ] ν ≅ ν' : A @ k ].
Proof. intros D; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ac_sound_all)))))) _ _ _ _ _ D _ _ _ _ _). Qed.

(** An unchanged inferred type is related to itself in the target. *)
Lemma ne_refl {G Γ ν ν' T i G2 k k' A A'} : ac_tmne G Γ ν ν' T -> compt i -> GEq G G2 ->
  [ G ; Γ ⊢[ i ] ν : A @ k ] -> [ G ; Γ ⊢[ i ] ν' : A' @ k' ] -> [ G2 ; Γ ⊢[ i ] T ≅ T @ k ].
Proof.
  intros D Hc HE Hν Hν'. destruct (ac_ne_sound' D Hc Hν Hν') as (EA & _ & _).
  exact (eqty_refl _ _ _ _ _ (gconv_ty HE (eqty_wf_r (compt_typeof_self _ Hc) EA))).
Qed.

Lemma ac_tmnee_whnf {G Γ ν ν' W} : ac_tmnee G Γ ν ν' W -> whnf_ty W.
Proof. intros H; inversion H; assumption. Qed.

Lemma C_actmnee_red {G Γ ν ν' T W} : ac_tmne G Γ ν ν' T -> C_ne G Γ ν ν' T -> reds_ty T W -> whnf_ty W ->
  C_nee G Γ ν ν' W.
Proof.
  intros D IH Hr Hw i G2 Γ2 k k' A A' Hc HE Hctx Hν Hν' x x' Hsx Hsx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (IH i G2 Γ2 k k' A A' Hc HE Hctx Hν Hν' x x' Hsx Hsx') as (T2 & X & ET2).
  destruct (ac_ne_sound' D Hc Hν Hν') as (EA & _ & _).
  pose proof (red_ty_sound Hc (eqty_wf_r Hi EA) Hr Hw) as ET.
  destruct (tgt_whnf Hc (eqty_wf_l Hi ET2)) as (W2 & Hr2 & Hw2 & EW2).
  exists W2. split; [exact (actmnee_red _ _ _ _ _ _ X Hr2 Hw2) |].
  eapply eqty_trans; [exact (eqty_sym _ _ _ _ _ _ EW2) |].
  eapply eqty_trans; [exact ET2 | exact (gconv_eqty HE Hi ET)].
Qed.

Lemma C_acs_pt {G Γ d d' Θ} :
  (forall n A k, in_ctx Θ n A k -> ac_tm G Γ (llk d n) (llk d' n) A[d]) ->
  (forall n A k, in_ctx Θ n A k -> C_tm G Γ (llk d n) (llk d' n) A[d]) -> C_sub G Γ d d' Θ.
Proof.
  intros D IH i G2 Γ2 Θ2 Hc HE Hctx HΘ Hd Hd' HΘΘ. pose proof (compt_typeof_self _ Hc) as Hi.
  pose proof (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ac_sound_all))))))) _ _ _ _ _
                (acs_pt _ _ _ _ _ D) i Hc HΘ Hd Hd') as (_ & _ & Edd).
  apply acs_pt. intros n A2 k2 Hin2.
  destruct (eqctx_lookup_r (i := lD) eq_refl HΘΘ _ _ _ Hin2) as (A & k & Hin & _ & EA).
  apply (IH n A k Hin i G2 Γ2 A2[d] k Hc HE Hctx (lsw_var _ _ _ _ _ Hd _ _ _ Hin)
           (eqtm_wf_r Hi (Edd _ _ _ Hin))); [| exact spa_refl | exact spa_refl].
  exact (eqty_subst Hi (lift_eqty (eqty_sym _ _ _ _ _ _ EA) (lle_D_compt _ Hc)) (gconv_lsub HE Hc Hd)).
Qed.

Lemma C_actmne_var {G Γ n T l} : in_ctx Γ n T l -> C_ne G Γ (var n) (var n) T.
Proof.
  intros Hin i G2 Γ2 k k' X X' Hc HE Hctx Hν Hν' x x' Hsx Hsx'. spa_triv. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_var Hi Hν) as (T0 & l0 & (_ & Hin0) & Hk & _).
  destruct (in_ctx_det Hin Hin0) as [<- <-].
  destruct (eqctx_lookup Hi Hctx _ _ _ Hin) as (T2 & l2 & Hin2 & _ & ET).
  exists T2. split; [exact (actmne_var _ _ _ _ _ Hin2) |].
  exact (eqty_sym _ _ _ _ _ _ (lvl_eq_eqty (lvl_eq_G2 HE Hk) ET)).
Qed.

Lemma C_actmne_gvar {G Γ u Δ i' T l d d'} : in_gctx (gΨ G) u (gdTm Δ i' T l) -> C_sub G Γ d d' Δ ->
  C_ne G Γ (gvar u d) (gvar u d') T[d].
Proof.
  intros Hin IH i G2 Γ2 k k' X X' Hc HE Hctx Hν Hν' x x' Hsx Hsx'. spa_triv. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_gvar Hi Hν) as (Δ0 & i0 & T0 & l0 & (HΓ & Hin0 & Hle & Ht & Hn & He) & Hk & _).
  destruct (inv_gvar Hi Hν') as (Δ1 & i1 & T1 & l1 & (_ & Hin1 & _ & Ht' & Hn' & He') & _ & _).
  pose proof (in_gctx_det Hin Hin0) as E0. injection E0 as <- <- <- <-.
  pose proof (in_gctx_det Hin Hin1) as E1. injection E1 as <- <- <- <-.
  pose proof HΓ as HΓi. rewrite Hi in HΓi.
  destruct (gctx_decl_ok _ _ _ (ctx_glob _ _ _ HΓi) Hin) as (HΔ & _).
  pose proof (lift_ctx HΔ (lle_D_compt _ Hc)) as HΔi.
  pose proof (lsub_wf_prem Hi HΓi Ht Hn He) as Hd.
  pose proof HE as (_ & _ & _ & Hl). destruct (Hl _ _ Hin) as (D2 & Hin2 & HD2).
  destruct D2 as [| | Δ2 i2 T2 l2 |]; cbn in HD2; try contradiction.
  destruct HD2 as (-> & _ & _ & HΔΔ & ET).
  exists T2[d]. split.
  - eapply actmne_gvar; [exact Hin2 |].
    exact (IH i G2 Γ2 Δ2 Hc HE Hctx HΔi Hd (lsub_wf_prem Hi HΓi Ht' Hn' He') HΔΔ).
  - apply (lvl_eq_eqty (lvl_eq_G2 HE Hk)).
    exact (eqty_subst Hi (lift_eqty (eqty_sym _ _ _ _ _ _ ET) (lle_D_compt _ Hc)) (gconv_lsub HE Hc Hd)).
Qed.

Lemma C_actmne_natrec {G Γ l l' M M' s s' z z' ν ν' W} : leqv l l' ->
  ac_ty G (Γ ,, tyNat @ lzero) M M' -> C_ty G (Γ ,, tyNat @ lzero) M M' ->
  ac_tm G Γ s s' M[lsingle zero] -> C_tm G Γ s s' M[lsingle zero] ->
  ac_tm G (Γ ,, tyNat @ lzero ,, M @ l) z z' M[lsucc] -> C_tm G (Γ ,, tyNat @ lzero ,, M @ l) z z' M[lsucc] ->
  ac_tmnee G Γ ν ν' W -> C_nee G Γ ν ν' W ->
  C_ne G Γ (natrec l M s z ν) (natrec l' M' s' z' ν') M[lsingle ν].
Proof.
  intros Hl DM IHM Ds IHs Dz IHz Dν IHν i G2 Γ2 k k' X X' Hc HE Hctx Hx Hx' x x' Hsx Hsx'. spa_triv.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_natrec Hi Hx) as ((Hv & Wl & HM & Hs & Hz & Hν) & Hk & HX).
  destruct (inv_natrec Hi Hx') as ((_ & Wl' & HM' & Hs' & Hz' & Hν') & Hk' & HX').
  pose proof (leqv_lequiv _ _ _ Wl Wl' Hl) as E.
  pose proof (ac_ty_sound Hc DM HM (wft_lconv _ _ _ _ _ _ HM' E)) as EM.
  pose proof (ctx_of_wf_tm Hi Hν) as HΓ.
  assert (HN : [ G ; Γ ⊢[ i ] tyNat @ lzero ]) by (apply wft_nat; [exact Hv | rewrite Hi; exact HΓ]).
  assert (HΓN : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HN | exact I]).
  assert (H0 : [ G ; Γ ⊢[ i ] zero : tyNat @ lzero ]) by (apply wf_zero; [exact Hv | rewrite Hi; exact HΓ]).
  pose proof (eqty_single Hi EM H0) as EM0.
  assert (Hs1 : [ G ; Γ ⊢[ i ] s' : M[lsingle zero] @ l ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Hs' | exact E] | rewrite Hi; exact EM0]).
  assert (HΓM : [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ i ] ]) by (apply wfc_ext; assumption).
  assert (EM' : [ G ; Γ ,, tyNat @ lzero ⊢[ i ] M' ≅ M @ l' ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EM) | exact (lequiv_sym _ _ _ E)]).
  pose proof (stab_tm Hi EM' (lequiv_sym _ _ _ E) HΓM Hz') as Hz1.
  pose proof (eqty_subst Hi EM (lsub_wf_lsucc Hi Hv HΓM)) as EMs.
  assert (Hz2 : [ G ; Γ ,, tyNat @ lzero ,, M @ l ⊢[ i ] z' : M[lsucc] @ l ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Hz1 | exact E] | rewrite Hi; exact EMs]).
  assert (HctxN : [ G2 ⊢[ i ] Γ ,, tyNat @ lzero ≅ Γ2 ,, tyNat @ lzero ])
    by exact (eqctx_ext_refl Hctx (gconv_ty HE HN) I).
  destruct (IHν i G2 Γ2 _ _ _ _ Hc HE Hctx Hν Hν' _ _ spa_refl spa_refl) as (W2 & Xν & _).
  exists M[lsingle ν]. split.
  - apply (actmne_natrec _ _ _ _ _ _ _ _ _ _ _ _ W2 Hl).
    + exact (IHM i G2 _ l l Hc HE HctxN HM (wft_lconv _ _ _ _ _ _ HM' E)).
    + exact (IHs i G2 Γ2 _ l Hc HE Hctx Hs Hs1 (eqty_refl _ _ _ _ _ (gconv_ty HE (wf_tm_ty Hi Hs))) _ _ spa_refl spa_refl).
    + apply (IHz i G2 _ _ l Hc HE (eqctx_ext_refl HctxN (gconv_ty HE HM) (GEq_lwf HE Wl)) Hz Hz2);
        [exact (eqty_refl _ _ _ _ _ (gconv_ty HE (wf_tm_ty Hi Hz))) | exact spa_refl | exact spa_refl].
    + exact Xν.
  - exact (ne_refl (actmne_natrec _ _ _ _ _ _ _ _ _ _ _ _ _ Hl DM Ds Dz Dν) Hc HE Hx Hx').
Qed.

Lemma ac_nee_sound' {G Γ ν ν' W i k k' A A'} : ac_tmnee G Γ ν ν' W -> compt i ->
  [ G ; Γ ⊢[ i ] ν : A @ k ] -> [ G ; Γ ⊢[ i ] ν' : A' @ k' ] ->
  [ G ; Γ ⊢[ i ] A ≅ W @ k ] /\ [ G ; Γ ⊢[ i ] A' ≅ W @ k' ] /\ [ G ; Γ ⊢[ i ] ν ≅ ν' : A @ k ].
Proof.
  intros D; exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ac_sound_all))))))) _ _ _ _ _ D _ _ _ _ _).
Qed.

Lemma C_actmne_app {G Γ l1 l2 l3 l4 A A' B B' ν ν' s s' m m' A0 B0} :
  ac_tmnee G Γ ν ν' (tyPi m m' A0 B0) -> C_nee G Γ ν ν' (tyPi m m' A0 B0) ->
  ac_tm G Γ s s' A0 -> C_tm G Γ s s' A0 ->
  C_ne G Γ (app ν l1 l2 A B s) (app ν' l3 l4 A' B' s') B0[lsingle s].
Proof.
  intros Dν IHν Ds IHs i G2 Γ2 k k' X X' Hc HE Hctx Hx Hx' x x' Hsx Hsx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (spa_app_inv Hsx) as (hd & ? & ? & ? & ? & -> & Hf).
  destruct (spa_app_inv Hsx') as (hd' & ? & ? & ? & ? & -> & Hf').
  destruct (inv_app Hi Hx) as ((Hv & W1 & W2 & HA & HB & Hν & Hs) & Hk & HX).
  destruct (inv_app Hi Hx') as ((_ & W3 & W4 & HA' & HB' & Hν' & Hs') & Hk' & HX').
  destruct (ac_nee_sound' Dν Hc Hν Hν') as (E0 & E1 & _).
  destruct (pi_inj_c Hc E0) as (Em1 & Em2 & EA0 & EB0).
  destruct (pi_inj_c Hc E1) as (Em3 & Em4 & EA1 & EB1).
  pose proof (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ Em1) Em3) as E13.
  assert (EA : [ G ; Γ ⊢[ i ] A ≅ A' @ l1 ]).
  { eapply eqty_trans; [exact EA0 |]. apply eqty_sym.
    eapply eqty_lconv; [exact EA1 | exact E13]. }
  assert (Hs0 : [ G ; Γ ⊢[ i ] s : A0 @ l1 ])
    by (eapply wf_conv; [exact Hs | rewrite Hi; exact (eqty_sym _ _ _ _ _ _ EA0)]).
  assert (Hs1 : [ G ; Γ ⊢[ i ] s' : A @ l1 ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Hs' | exact E13] | rewrite Hi; exact EA]).
  assert (Hs1' : [ G ; Γ ⊢[ i ] s' : A0 @ l1 ])
    by (eapply wf_conv; [exact Hs1 | rewrite Hi; exact (eqty_sym _ _ _ _ _ _ EA0)]).
  destruct (IHν i G2 Γ2 _ _ _ _ Hc HE Hctx Hν Hν' _ _ Hf Hf') as (W & Xν & EW).
  destruct (head_pi W (decl_head_c Hc EW (ac_tmnee_whnf Xν) (whnf_tyPi _ _ _ _))) as (n1 & n2 & A2 & B2 & ->).
  destruct (pi_inj_c Hc (eqty_sym _ _ _ _ _ _ EW)) as (_ & En2 & EA2 & EB2).
  pose proof (GEq_lequiv HE Em1) as Em1'. pose proof (GEq_lequiv HE Em2) as Em2'.
  assert (ET : [ G2 ; Γ ⊢[ i ] A2 ≅ A0 @ l1 ])
    by exact (eqty_sym _ _ _ _ _ _ (eqty_lconv _ _ _ _ _ _ _ EA2 (lequiv_sym _ _ _ Em1'))).
  pose proof (IHs i G2 Γ2 A2 l1 Hc HE Hctx Hs0 Hs1' ET _ _ spa_refl spa_refl) as Xs.
  exists B2[lsingle s]. split; [eapply actmne_app; [exact Xν | exact Xs] |].
  assert (Hs0m : [ G2 ; Γ ⊢[ i ] s : A0 @ m ]) by exact (gconv_tm HE Hi (wf_lconv _ _ _ _ _ _ _ Hs0 Em1)).
  pose proof (eqty_sym _ _ _ _ _ _ (eqty_single Hi EB2 Hs0m)) as EBs.
  apply (lvl_eq_eqty (lvl_eq_G2 HE Hk)).
  exact (eqty_lconv _ _ _ _ _ _ _ EBs (lequiv_sym _ _ _ Em2')).
Qed.

Lemma C_actmne_uapp {G Γ n l T ν ν' ls ls'} :
  ac_tmnee G Γ ν ν' (tyUPi n l T) -> C_nee G Γ ν ν' (tyUPi n l T) -> length ls = n ->
  Forall2 leqv ls ls' -> C_ne G Γ (uapp ν ls) (uapp ν' ls') T[uext ls lvar]ᵤ.
Proof.
  intros Dν IHν Hn Hls i G2 Γ2 k k' X X' Hc HE Hctx Hx Hx' x x' Hsx Hsx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (spa_uapp_inv Hsx) as (hd & -> & Hf). destruct (spa_uapp_inv Hsx') as (hd' & -> & Hf').
  destruct (inv_uapp Hi Hx) as (n0 & l0 & T0 & (-> & W0 & HT0 & Hlen & Hw & Hν) & Hk & HX).
  destruct (inv_uapp Hi Hx') as (n1 & l1 & T1 & (_ & _ & _ & _ & _ & Hν') & _ & _).
  destruct (ac_nee_sound' Dν compt_M Hν Hν') as (E0 & _ & _).
  destruct (declM_upi_inj E0) as (-> & El0 & _).
  destruct (IHν lM G2 Γ2 _ _ _ _ compt_M HE Hctx Hν Hν' _ _ Hf Hf') as (W & Xν & EW).
  destruct (head_upi W (decl_head_c compt_M EW (ac_tmnee_whnf Xν) (whnf_tyUPi _ _ _))) as (n2 & m & T2 & ->).
  destruct (declM_upi_inj (eqty_sym _ _ _ _ _ _ EW)) as (-> & _ & ET).
  exists T2[uext ls lvar]ᵤ. split; [eapply actmne_uapp; [exact Xν | exact Hn | exact Hls] |].
  subst n0.
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Hν) as HΓ.
  assert (Hw2 : Forall (lwf (gL G2)) ls) by (rewrite (GEq_L HE); exact Hw).
  pose proof (uinst_eqty (GEq_wf2 HE) (wf_ctx_dnf HΓ) Hw2 (eqty_sym _ _ _ _ _ _ ET)) as I.
  assert (Hok : usub_ok (uext ls lvar) (gL G) (length ls + gL G))
    by (apply usub_ok_uext; [exact Hw | apply usub_ok_id]).
  pose proof (lequiv_lvsubst _ _ _ _ _ Hok El0) as E.
  apply (lvl_eq_eqty (lvl_eq_G2 HE Hk)). exact (eqty_lconv _ _ _ _ _ _ _ I (GEq_lequiv HE E)).
Qed.

Lemma C_actmne_capp {G Γ l T ν ν' Δ Δ'} :
  ac_tmnee G Γ ν ν' (tyCPi l T) -> C_nee G Γ ν ν' (tyCPi l T) -> C_ctx G Δ Δ' ->
  C_ne G Γ (capp ν Δ) (capp ν' Δ') T⦃gsingle (GCtx Δ)⦄.
Proof.
  intros Dν IHν IHc i G2 Γ2 k k' X X' Hc HE Hctx Hx Hx' x x' Hsx Hsx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (spa_capp_inv Hsx) as (hd & -> & Hf). destruct (spa_capp_inv Hsx') as (hd' & -> & Hf').
  destruct (inv_capp Hi Hx) as (l0 & T0 & (-> & W0 & HT0 & HΔ & Hν & _) & Hk & HX).
  destruct (inv_capp Hi Hx') as (l1 & T1 & (_ & W1 & HT1 & HΔ' & Hν' & _) & _ & _).
  destruct (ac_nee_sound' Dν compt_M Hν Hν') as (E0 & _ & _).
  destruct (declM_cpi_inj E0) as (El0 & _).
  destruct (IHν lM G2 Γ2 _ _ _ _ compt_M HE Hctx Hν Hν' _ _ Hf Hf') as (W & Xν & EW).
  destruct (head_cpi W (decl_head_c compt_M EW (ac_tmnee_whnf Xν) (whnf_tyCPi _ _))) as (m & T2 & ->).
  destruct (declM_cpi_inj (eqty_sym _ _ _ _ _ _ EW)) as (_ & ET).
  exists T2⦃gsingle (GCtx Δ)⦄. split; [eapply actmne_capp; [exact Xν | exact (IHc G2 HE HΔ HΔ')] |].
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Hν) as HΓ.
  pose proof (inst_c_eqty (gconv_ctx HE compt_M HΓ) (gconv_ctx HE compt_D HΔ) (eqty_sym _ _ _ _ _ _ ET)) as I.
  apply (lvl_eq_eqty (lvl_eq_G2 HE Hk)).
  exact (eqty_lconv _ _ _ _ _ _ _ I (lequiv_sym _ _ _ (GEq_lequiv HE El0))).
Qed.

Lemma C_actmne_tapp {G Γ Δ l l' T ν ν' A A'} :
  ac_tmnee G Γ ν ν' (tyTPi Δ l l' T) -> C_nee G Γ ν ν' (tyTPi Δ l l' T) -> C_ty G Δ A A' ->
  C_ne G Γ (tapp ν A) (tapp ν' A') T⦃gsingle (GTy A)⦄.
Proof.
  intros Dν IHν IHA i G2 Γ2 k k' X X' Hc HE Hctx Hx Hx' x x' Hsx Hsx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (spa_tapp_inv Hsx) as (hd & -> & Hf). destruct (spa_tapp_inv Hsx') as (hd' & -> & Hf').
  destruct (inv_tapp Hi Hx) as (Δ0 & l0 & l0' & T0 & (-> & Hν & HΔ0 & W0 & W0' & HT0 & HA & _) & Hk & HX).
  destruct (inv_tapp Hi Hx') as (Δ1 & l1 & l1' & T1 & (_ & Hν' & HΔ1 & W1 & W1' & HT1 & HA' & _) & _ & _).
  destruct (ac_nee_sound' Dν compt_M Hν Hν') as (E0 & E1 & _).
  destruct (declM_tpi_inj E0) as (Ec0 & El0 & El0' & _).
  destruct (declM_tpi_inj E1) as (Ec1 & El1 & _ & _).
  pose proof (decl_ty_ctxconv_D Ec0 HA (lequiv_refl _ _ W0)) as HAΔ.
  pose proof (decl_ty_ctxconv_D Ec1 HA' (lequiv_trans _ _ _ _ (lequiv_sym _ _ _ El1) El0)) as HA'Δ.
  destruct (IHν lM G2 Γ2 _ _ _ _ compt_M HE Hctx Hν Hν' _ _ Hf Hf') as (W & Xν & EW).
  destruct (head_tpi W (decl_head_c compt_M EW (ac_tmnee_whnf Xν) (whnf_tyTPi _ _ _ _))) as (Δ2 & m & m' & T2 & ->).
  destruct (declM_tpi_inj (eqty_sym _ _ _ _ _ _ EW)) as (HΔΔ2 & _ & _ & ET).
  exists T2⦃gsingle (GTy A)⦄. split.
  { eapply actmne_tapp; [exact Xν | exact (IHA lD G2 Δ2 l0 l0 compt_D HE HΔΔ2 HAΔ HA'Δ)]. }
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Hν) as HΓ.
  pose proof (gconv_ty HE (wft_lconv _ _ _ _ _ _ HAΔ El0)) as HAl.
  pose proof (inst_t_eqty (gconv_ctx HE compt_M HΓ) HAl (eqty_sym _ _ _ _ _ _ ET)) as I.
  apply (lvl_eq_eqty (lvl_eq_G2 HE Hk)).
  exact (eqty_lconv _ _ _ _ _ _ _ I (lequiv_sym _ _ _ (GEq_lequiv HE El0'))).
Qed.

(** ** letbox *)

Lemma C_actmne_letboxT {G Γ l1 l2 l3 l4 Δ Δ' M M' t1 t2 ν ν' W} : leqv l1 l3 -> leqv l2 l4 ->
  ac_ctx G Δ Δ' -> C_ctx G Δ Δ' ->
  ac_ty G (Γ ,, tyCTyp Δ l2 @ lzero) M M' -> C_ty G (Γ ,, tyCTyp Δ l2 @ lzero) M M' ->
  ac_tm (gext G (gdTy Δ lC l2)) Γ⟪S⟫ t1 t2 (M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))]) ->
  C_tm (gext G (gdTy Δ lC l2)) Γ⟪S⟫ t1 t2 (M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))]) ->
  ac_tmnee G Γ ν ν' W -> C_nee G Γ ν ν' W ->
  C_ne G Γ (letboxT l1 l2 Δ M t1 ν) (letboxT l3 l4 Δ' M' t2 ν') M[lsingle ν].
Proof.
  intros H13 H24 Dc IHc DM IHM Dt IHt Dν IHν i G2 Γ2 k k' X X' Hc HE Hctx Hx Hx' x x' Hsx Hsx'. spa_triv.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_letboxT Hi Hx) as ((-> & W1 & W2 & HΔ & HM & Ht1 & Hν) & Hk & HX).
  destruct (inv_letboxT Hi Hx') as ((_ & W3 & W4 & HΔ' & HM' & Ht2 & Hν') & _ & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (ac_ctx_sound' Dc HΔ HΔ') as Ec.
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Hν) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (HCC : [ G ; Γ ⊢[ lM ] tyCTyp Δ l2 ≅ tyCTyp Δ' l4 @ lzero ]) by (apply eqty_CTyp; assumption).
  assert (HC : [ G ; Γ ⊢[ lM ] tyCTyp Δ l2 @ lzero ]) by (apply wft_CTyp; assumption).
  assert (HΓ1 : [ G ; Γ ,, tyCTyp Δ l2 @ lzero ⊢[ lM ] ]) by (apply wfc_ext; [exact HΓ | exact HC | exact I]).
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty (i := lM) eq_refl (eqty_sym _ _ _ _ _ _ HCC)
                                        (lequiv_refl (gL G) lzero I) HΓ1 HM') E13) as HM1.
  pose proof (ac_ty_sound compt_M DM HM HM1) as EM.
  assert (HGD : [ ⊢ gext G (gdTy Δ lC l2) ]) by (apply wfg_ty; [exact HG | exact HΔ | left; reflexivity | exact W2]).
  pose proof (gbind_obj_ty (i := lC) ltac:(unfold lle; cbn; lia) ltac:(discriminate) HGD Ec E24) as Ho.
  pose proof (gbind_tm HG HGD Ho eq_refl Ht2) as Ht2a.
  pose proof (letboxT_body_eq HGD HΔ W2 EM) as EMb.
  assert (Ht2b : [ gext G (gdTy Δ lC l2) ; Γ⟪S⟫ ⊢[ lM ] t2 : M⟪S⟫[lsingle (boxT (tyGvar 0 (lshift 0)))] @ l1 ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Ht2a | exact E13] | exact EMb]).
  pose proof (GEq_ext_same HE HGD) as HE1.
  destruct (IHν lM G2 Γ2 _ _ _ _ compt_M HE Hctx Hν Hν' _ _ spa_refl spa_refl) as (Wν & Xν & _).
  exists M[lsingle ν]. split.
  - eapply actmne_letboxT; [exact H13 | exact H24 | exact (IHc G2 HE HΔ HΔ') | | | exact Xν].
    + exact (IHM lM G2 _ l1 l1 compt_M HE (eqctx_ext_refl Hctx (gconv_ty HE HC) I) HM HM1).
    + exact (IHt lM _ Γ2⟪S⟫ _ l1 compt_M HE1 (eqctx_gext (GEq_wf2 HE1) Hctx) Ht1 Ht2b
               (eqty_refl _ _ _ _ _ (gconv_ty HE1 (wf_tm_ty (i := lM) eq_refl Ht1))) _ _ spa_refl spa_refl).
  - exact (ne_refl (actmne_letboxT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H13 H24 Dc DM Dt Dν) compt_M HE Hx Hx').
Qed.

Lemma C_actmne_letboxt {G Γ l1 l2 l3 l4 Δ Δ' T T' M M' t1 t2 ν ν' W} : leqv l1 l3 -> leqv l2 l4 ->
  ac_ctx G Δ Δ' -> C_ctx G Δ Δ' -> ac_ty G Δ T T' -> C_ty G Δ T T' ->
  ac_ty G (Γ ,, tyCTrm Δ T l2 @ lzero) M M' -> C_ty G (Γ ,, tyCTrm Δ T l2 @ lzero) M M' ->
  ac_tm (gext G (gdTm Δ lC T l2)) Γ⟪S⟫ t1 t2 (M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))]) ->
  C_tm (gext G (gdTm Δ lC T l2)) Γ⟪S⟫ t1 t2 (M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))]) ->
  ac_tmnee G Γ ν ν' W -> C_nee G Γ ν ν' W ->
  C_ne G Γ (letboxt l1 l2 Δ T M t1 ν) (letboxt l3 l4 Δ' T' M' t2 ν') M[lsingle ν].
Proof.
  intros H13 H24 Dc IHc DT IHT DM IHM Dt IHt Dν IHν i G2 Γ2 k k' X X' Hc HE Hctx Hx Hx' x x' Hsx Hsx'. spa_triv.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_letboxt Hi Hx) as ((-> & W1 & W2 & HΔ & HT & HM & Ht1 & Hν) & Hk & HX).
  destruct (inv_letboxt Hi Hx') as ((_ & W3 & W4 & HΔ' & HT' & HM' & Ht2 & Hν') & _ & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (ac_ctx_sound' Dc HΔ HΔ') as Ec.
  pose proof (decl_ty_ctxconv_D (eqctx_sym_D Ec) HT' (lequiv_sym _ _ _ E24)) as HT1.
  pose proof (ac_ty_sound compt_D DT HT HT1) as ET.
  pose proof (ctx_of_wf_tm (i := lM) eq_refl Hν) as HΓ. pose proof (ctx_glob _ _ _ HΓ) as HG.
  assert (HCC : [ G ; Γ ⊢[ lM ] tyCTrm Δ T l2 ≅ tyCTrm Δ' T' l4 @ lzero ]) by (apply eqty_CTrm; assumption).
  assert (HC : [ G ; Γ ⊢[ lM ] tyCTrm Δ T l2 @ lzero ]) by (apply wft_CTrm; assumption).
  assert (HΓ1 : [ G ; Γ ,, tyCTrm Δ T l2 @ lzero ⊢[ lM ] ]) by (apply wfc_ext; [exact HΓ | exact HC | exact I]).
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty (i := lM) eq_refl (eqty_sym _ _ _ _ _ _ HCC)
                                        (lequiv_refl (gL G) lzero I) HΓ1 HM') E13) as HM1.
  pose proof (ac_ty_sound compt_M DM HM HM1) as EM.
  assert (HGD : [ ⊢ gext G (gdTm Δ lC T l2) ]) by (apply wfg_tm; [exact HG | exact HT | right; reflexivity | exact W2]).
  pose proof (gbind_obj_tm HGD Ec ET E24) as Ho.
  pose proof (gbind_tm HG HGD Ho eq_refl Ht2) as Ht2a.
  pose proof (letboxt_body_eq HGD HΔ HT W2 EM) as EMb.
  assert (Ht2b : [ gext G (gdTm Δ lC T l2) ; Γ⟪S⟫ ⊢[ lM ] t2 : M⟪S⟫[lsingle (boxt (gvar 0 (lshift 0)))] @ l1 ])
    by (eapply wf_conv; [eapply wf_lconv; [exact Ht2a | exact E13] | exact EMb]).
  pose proof (GEq_ext_same HE HGD) as HE1.
  destruct (IHν lM G2 Γ2 _ _ _ _ compt_M HE Hctx Hν Hν' _ _ spa_refl spa_refl) as (Wν & Xν & _).
  exists M[lsingle ν]. split.
  - eapply actmne_letboxt; [exact H13 | exact H24 | exact (IHc G2 HE HΔ HΔ') | | | | exact Xν].
    + exact (IHT lD G2 Δ l2 l2 compt_D HE (eqc_refl _ _ _ (gconv_ctx HE compt_D HΔ)) HT HT1).
    + exact (IHM lM G2 _ l1 l1 compt_M HE (eqctx_ext_refl Hctx (gconv_ty HE HC) I) HM HM1).
    + exact (IHt lM _ Γ2⟪S⟫ _ l1 compt_M HE1 (eqctx_gext (GEq_wf2 HE1) Hctx) Ht1 Ht2b
               (eqty_refl _ _ _ _ _ (gconv_ty HE1 (wf_tm_ty (i := lM) eq_refl Ht1))) _ _ spa_refl spa_refl).
  - exact (ne_refl (actmne_letboxt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H13 H24 Dc DT DM Dt Dν) compt_M HE Hx Hx').
Qed.

(** ** The recursors *)

(** The motives and branches, moved to the target. *)
Lemma C_rec_core {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' G2 Γ2} :
  ac_ty (recGT G) (recΓT Γ) MT MT' -> C_ty (recGT G) (recΓT Γ) MT MT' ->
  ac_ty (recGt G) (recΓt Γ) Mt Mt' -> C_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < nbr -> C_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  GEq G G2 -> [ G2 ⊢[ lM ] Γ ≅ Γ2 ] -> [ G ; Γ ⊢[ lM ] ] ->
  lequiv (gL G) l1 l1' -> lequiv (gL G) l2 l2' ->
  [ recGT G ; recΓT Γ ⊢[ lM ] MT @ lvren l1 (ush 1) ] -> [ recGT G ; recΓT Γ ⊢[ lM ] MT' @ lvren l1' (ush 1) ] ->
  [ recGt G ; recΓt Γ ⊢[ lM ] Mt @ lvren l2 (ush 1) ] -> [ recGt G ; recΓt Γ ⊢[ lM ] Mt' @ lvren l2' (ush 1) ] ->
  (forall j, j < nbr -> [ brG j G ; brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ] ]) ->
  (forall j, j < nbr -> [ brG j G ; brΓ j Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ] ]) ->
  (forall j, j < nbr -> [ brG j G ; brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2 ⊢[ lM ]
                         bs j : brRes j (wrapMT MT) (wrapMt Mt) @ brLv j l1 l2 ]) ->
  (forall j, j < nbr -> [ brG j G ; brΓ j Γ (wrapMT MT') (wrapMt Mt') l1' l2' ⊢[ lM ]
                         bs' j : brRes j (wrapMT MT') (wrapMt Mt') @ brLv j l1' l2' ]) ->
  ac_ty (recGT G2) (recΓT Γ2) MT MT' /\ ac_ty (recGt G2) (recΓt Γ2) Mt Mt' /\
  (forall j, j < nbr -> ac_tm (brG j G2) (brΓ j Γ2 (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))).
Proof.
  intros DMT IHT DMt IHt IHb HE Hctx HΓ E1 E2 HMT HMT' HMt HMt' Hbc Hbc' Hbs Hbs'.
  pose proof (wft_lconv _ _ _ _ _ _ HMT' (lequiv_ush 1 E1)) as HMT1.
  pose proof (wft_lconv _ _ _ _ _ _ HMt' (lequiv_ush 1 E2)) as HMt1.
  pose proof (ac_ty_sound compt_M DMT HMT HMT1) as EMT.
  pose proof (ac_ty_sound compt_M DMt HMt HMt1) as EMt.
  refine (conj _ (conj _ _)).
  - exact (IHT lM _ _ _ _ compt_M (GEq_recGT HE (ctx_glob _ _ _ (ctx_of_wf_ty (i := lM) eq_refl HMT)))
             (eqctx_recΓT Hctx) HMT HMT1).
  - exact (IHt lM _ _ _ _ compt_M (GEq_recGt HE (ctx_glob _ _ _ (ctx_of_wf_ty (i := lM) eq_refl HMt)))
             (eqctx_recΓt Hctx) HMt HMt1).
  - intros j Hj.
    pose proof (GEq_brG j HE (ctx_glob _ _ _ (Hbc j Hj))) as HEj.
    apply (IHb j Hj lM _ _ _ _ compt_M HEj
             (eqctx_brΓ j Hj Hctx (gconv_ctx HEj compt_M (Hbc j Hj))) (Hbs j Hj)
             (branch_conv j Hj EMT EMt E1 E2 HΓ (Hbc j Hj) (Hbc' j Hj) (Hbs' j Hj)));
      [exact (eqty_refl _ _ _ _ _ (gconv_ty HEj (wf_tm_ty (i := lM) eq_refl (Hbs j Hj)))) | exact spa_refl | exact spa_refl].
Qed.

Ltac rec_inv Hi Hx Hx' :=
  let MT0 := fresh "MT0" in let Mt0 := fresh "Mt0" in let bs0 := fresh "bs0" in
  let MT1 := fresh "MT1" in let Mt1 := fresh "Mt1" in let bs1 := fresh "bs1" in
  let Erb := fresh "Erb" in let Erb' := fresh "Erb'" in
  first
  [ destruct (inv_elimT Hi Hx) as (MT0 & Mt0 & bs0 & (Erb & -> & _ & W1 & W2 & Wl & HΔ & HMT & HMt & Hbc & Hbs & Hν)
                                   & Hk & HX);
    destruct (inv_elimT Hi Hx') as (MT1 & Mt1 & bs1 & (Erb' & _ & _ & W1' & W2' & Wl' & HΔ' & HMT' & HMt' & Hbc'
                                                       & Hbs' & Hν') & _ & _)
  | destruct (inv_elimt Hi Hx) as (MT0 & Mt0 & bs0 & (Erb & -> & _ & W1 & W2 & Wl & HΔ & HMT & HMt & Hbc & Hbs
                                   & HT & Hν) & Hk & HX);
    destruct (inv_elimt Hi Hx') as (MT1 & Mt1 & bs1 & (Erb' & _ & _ & W1' & W2' & Wl' & HΔ' & HMT' & HMt' & Hbc'
                                                       & Hbs' & HT' & Hν') & _ & _) ];
  destruct (mkrb_inj_MT Erb) as [<- <-]; destruct (mkrb_inj_MT Erb') as [<- <-];
  pose proof (mkrb_inj_br Erb) as Eb; pose proof (mkrb_inj_br Erb') as Eb'.

Ltac rec_core IHT IHt IHb DMT DMt HE Hctx :=
  let HΓ := fresh "HΓ" in
  match goal with Hν : [ _ ; ?Γ ⊢[ lM ] _ : _ @ _ ] |- _ =>
    pose proof (ctx_of_wf_tm (i := lM) eq_refl Hν) as HΓ end;
  match goal with
  | W1 : lwf _ ?l1, W1' : lwf _ ?l1', H1 : leqv ?l1 ?l1', W2 : lwf _ ?l2, W2' : lwf _ ?l2', H2 : leqv ?l2 ?l2',
    HMT : [ recGT _ ; _ ⊢[ lM ] ?MT @ _ ], HMT' : [ recGT _ ; _ ⊢[ lM ] ?MT' @ _ ],
    HMt : [ recGt _ ; _ ⊢[ lM ] ?Mt @ _ ], HMt' : [ recGt _ ; _ ⊢[ lM ] ?Mt' @ _ ],
    Hbc : forall j, j < nbr -> [ _ ; brΓ j _ (wrapMT ?MT) _ _ _ ⊢[ lM ] ],
    Hbc' : forall j, j < nbr -> [ _ ; brΓ j _ (wrapMT ?MT') _ _ _ ⊢[ lM ] ],
    Hbs : forall j, j < nbr -> [ _ ; brΓ j _ (wrapMT ?MT) _ _ _ ⊢[ lM ] _ : _ @ _ ],
    Hbs' : forall j, j < nbr -> [ _ ; brΓ j _ (wrapMT ?MT') _ _ _ ⊢[ lM ] _ : _ @ _ ],
    Eb : forall k, k < nbr -> ?bs k = _, Eb' : forall k, k < nbr -> ?bs' k = _ |- _ =>
    let Hbs0 := fresh "Hbs0" in let Hbs1 := fresh "Hbs1" in
    assert (Hbs0 : forall j, j < nbr -> [ _ ; brΓ j _ (wrapMT MT) _ _ _ ⊢[ lM ]
                                        bs j : brRes j (wrapMT MT) (wrapMt Mt) @ brLv j l1 l2 ])
      by (intros j Hj; rewrite (Eb j Hj); exact (Hbs j Hj));
    assert (Hbs1 : forall j, j < nbr -> [ _ ; brΓ j _ (wrapMT MT') _ _ _ ⊢[ lM ]
                                        bs' j : brRes j (wrapMT MT') (wrapMt Mt') @ brLv j l1' l2' ])
      by (intros j Hj; rewrite (Eb' j Hj); exact (Hbs' j Hj));
    destruct (C_rec_core DMT IHT DMt IHt IHb HE Hctx HΓ (leqv_lequiv _ _ _ W1 W1' H1)
                (leqv_lequiv _ _ _ W2 W2' H2) HMT HMT' HMt HMt' Hbc Hbc' Hbs0 Hbs1) as (XMT & XMt & Xb)
  end.

Lemma C_actmne_elimT {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' ν ν' W} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> ac_ctx G Δ Δ' -> C_ctx G Δ Δ' ->
  ac_ty (recGT G) (recΓT Γ) MT MT' -> C_ty (recGT G) (recΓT Γ) MT MT' ->
  ac_ty (recGt G) (recΓt Γ) Mt Mt' -> C_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < nbr -> ac_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  (forall j, j < nbr -> C_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  ac_tmnee G Γ ν ν' W -> C_nee G Γ ν ν' W ->
  C_ne G Γ (elimT l1 l2 (mkrb MT Mt bs) l Δ ν) (elimT l1' l2' (mkrb MT' Mt' bs') l' Δ' ν')
    (motT (wrapMT MT) l Δ ν).
Proof.
  intros H1 H2 Hl Dc IHc DMT IHT DMt IHt Db IHb Dν IHν i G2 Γ2 k k' X X' Hc HE Hctx Hx Hx' x x' Hsx Hsx'. spa_triv.
  pose proof (compt_typeof_self _ Hc) as Hi. rec_inv Hi Hx Hx'. rec_core IHT IHt IHb DMT DMt HE Hctx.
  destruct (IHν lM G2 Γ2 _ _ _ _ compt_M HE Hctx Hν Hν' _ _ spa_refl spa_refl) as (Wν & Xν & _).
  exists (motT (wrapMT MT) l Δ ν). split.
  - eapply actmne_elimT; [exact H1 | exact H2 | exact Hl | exact (IHc G2 HE HΔ HΔ') | exact XMT | exact XMt
                         | exact Xb | exact Xν].
  - exact (ne_refl (actmne_elimT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H2 Hl Dc DMT DMt Db Dν) compt_M HE Hx Hx').
Qed.

Lemma C_actmne_elimT_gvar {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' U d d'} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> ac_ctx G Δ Δ' -> C_ctx G Δ Δ' ->
  ac_ty (recGT G) (recΓT Γ) MT MT' -> C_ty (recGT G) (recΓT Γ) MT MT' ->
  ac_ty (recGt G) (recΓt Γ) Mt Mt' -> C_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < nbr -> ac_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  (forall j, j < nbr -> C_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  lsub_leq d d' ->
  C_ne G Γ (elimT l1 l2 (mkrb MT Mt bs) l Δ (boxT (tyGvar U d)))
    (elimT l1' l2' (mkrb MT' Mt' bs') l' Δ' (boxT (tyGvar U d')))
    (motT (wrapMT MT) l Δ (boxT (tyGvar U d))).
Proof.
  intros H1 H2 Hl Dc IHc DMT IHT DMt IHt Db IHb Hd i G2 Γ2 k k' X X' Hc HE Hctx Hx Hx' x x' Hsx Hsx'. spa_triv.
  pose proof (compt_typeof_self _ Hc) as Hi. rec_inv Hi Hx Hx'. rec_core IHT IHt IHb DMT DMt HE Hctx.
  exists (motT (wrapMT MT) l Δ (boxT (tyGvar U d))). split.
  - eapply actmne_elimT_gvar; [exact H1 | exact H2 | exact Hl | exact (IHc G2 HE HΔ HΔ') | exact XMT | exact XMt
                              | exact Xb | exact Hd].
  - exact (ne_refl (actmne_elimT_gvar _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H2 Hl Dc DMT DMt Db Hd)
             compt_M HE Hx Hx').
Qed.

Lemma C_actmne_elimt {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' T T' ν ν' W} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> ac_ctx G Δ Δ' -> C_ctx G Δ Δ' -> ac_ty G Δ T T' -> C_ty G Δ T T' ->
  ac_ty (recGT G) (recΓT Γ) MT MT' -> C_ty (recGT G) (recΓT Γ) MT MT' ->
  ac_ty (recGt G) (recΓt Γ) Mt Mt' -> C_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < nbr -> ac_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  (forall j, j < nbr -> C_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  ac_tmnee G Γ ν ν' W -> C_nee G Γ ν ν' W ->
  C_ne G Γ (elimt l1 l2 (mkrb MT Mt bs) l Δ T ν) (elimt l1' l2' (mkrb MT' Mt' bs') l' Δ' T' ν')
    (mott (wrapMt Mt) l Δ T ν).
Proof.
  intros H1 H2 Hl Dc IHc DT IHi DMT IHT DMt IHt Db IHb Dν IHν i G2 Γ2 k k' X X' Hc HE Hctx Hx Hx' x x' Hsx Hsx'. spa_triv.
  pose proof (compt_typeof_self _ Hc) as Hi. rec_inv Hi Hx Hx'. rec_core IHT IHt IHb DMT DMt HE Hctx.
  pose proof (leqv_lequiv _ _ _ Wl Wl' Hl) as El.
  pose proof (ac_ctx_sound' Dc HΔ HΔ') as Ec.
  pose proof (decl_ty_ctxconv_D (eqctx_sym_D Ec) HT' (lequiv_sym _ _ _ El)) as HT1.
  destruct (IHν lM G2 Γ2 _ _ _ _ compt_M HE Hctx Hν Hν' _ _ spa_refl spa_refl) as (Wν & Xν & _).
  exists (mott (wrapMt Mt) l Δ T ν). split.
  - eapply actmne_elimt; [exact H1 | exact H2 | exact Hl | exact (IHc G2 HE HΔ HΔ')
                         | exact (IHi lD G2 Δ l l compt_D HE (eqc_refl _ _ _ (gconv_ctx HE compt_D HΔ)) HT HT1)
                         | exact XMT | exact XMt | exact Xb | exact Xν].
  - exact (ne_refl (actmne_elimt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H2 Hl Dc DT DMT DMt Db Dν)
             compt_M HE Hx Hx').
Qed.

Lemma C_actmne_elimt_glob {G Γ l1 l2 l1' l2' MT MT' Mt Mt' bs bs' l l' Δ Δ' T T' c c'} :
  leqv l1 l1' -> leqv l2 l2' -> leqv l l' -> ac_ctx G Δ Δ' -> C_ctx G Δ Δ' -> ac_ty G Δ T T' -> C_ty G Δ T T' ->
  ac_ty (recGT G) (recΓT Γ) MT MT' -> C_ty (recGT G) (recΓT Γ) MT MT' ->
  ac_ty (recGt G) (recΓt Γ) Mt Mt' -> C_ty (recGt G) (recΓt Γ) Mt Mt' ->
  (forall j, j < nbr -> ac_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  (forall j, j < nbr -> C_tm (brG j G) (brΓ j Γ (wrapMT MT) (wrapMt Mt) l1 l2)
                         (bs j) (bs' j) (brRes j (wrapMT MT) (wrapMt Mt))) ->
  boxed_global c -> tm_leq c c' ->
  C_ne G Γ (elimt l1 l2 (mkrb MT Mt bs) l Δ T (boxt c))
    (elimt l1' l2' (mkrb MT' Mt' bs') l' Δ' T' (boxt c'))
    (mott (wrapMt Mt) l Δ T (boxt c)).
Proof.
  intros H1 H2 Hl Dc IHc DT IHi DMT IHT DMt IHt Db IHb Hg Hd i G2 Γ2 k k' X X' Hc HE Hctx Hx Hx' x x' Hsx Hsx'. spa_triv.
  pose proof (compt_typeof_self _ Hc) as Hi. rec_inv Hi Hx Hx'. rec_core IHT IHt IHb DMT DMt HE Hctx.
  pose proof (leqv_lequiv _ _ _ Wl Wl' Hl) as El.
  pose proof (ac_ctx_sound' Dc HΔ HΔ') as Ec.
  pose proof (decl_ty_ctxconv_D (eqctx_sym_D Ec) HT' (lequiv_sym _ _ _ El)) as HT1.
  exists (mott (wrapMt Mt) l Δ T (boxt c)). split.
  - eapply actmne_elimt_glob; [exact H1 | exact H2 | exact Hl | exact (IHc G2 HE HΔ HΔ')
                              | exact (IHi lD G2 Δ l l compt_D HE (eqc_refl _ _ _ (gconv_ctx HE compt_D HΔ)) HT HT1)
                              | exact XMT | exact XMt | exact Xb | exact Hg | exact Hd].
  - exact (ne_refl (actmne_elimt_glob _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H1 H2 Hl Dc DT DMT DMt Db Hg Hd)
             compt_M HE Hx Hx').
Qed.

(** ** Dependent pairs (M8) *)

Lemma C_actnf_sig {G Γ l1 l2 l3 l4 A A' B B'} : leqv l1 l3 -> leqv l2 l4 ->
  ac_ty G Γ A A' -> C_ty G Γ A A' -> C_ty G (Γ ,, A @ l1) B B' ->
  C_tynf G Γ (tySig l1 l2 A B) (tySig l3 l4 A' B').
Proof.
  intros H13 H24 DA IHA IHB i G2 Γ2 k k' Hc HE Hctx HT HT'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_sig HT) as ((Hv & W1 & W2 & HA & HB) & _).
  destruct (inv_ty_sig HT') as ((_ & W3 & W4 & HA' & HB') & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E13)) as EA.
  assert (HΓA : [ G ; Γ ,, A @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact (ctx_of_wf_ty Hi HA) | exact HA | exact W1]).
  assert (EA' : [ G ; Γ ⊢[ i ] A' ≅ A @ l3 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E13)]).
  pose proof (stab_ty Hi EA' (lequiv_sym _ _ _ E13) HΓA HB') as HB1.
  apply actnf_sig; [exact H13 | exact H24 | exact (IHA i G2 Γ2 l1 l3 Hc HE Hctx HA HA') |].
  apply (IHB i G2 (Γ2 ,, A @ l1) l2 l4 Hc HE); [| exact HB | exact HB1].
  exact (eqctx_ext_refl Hctx (gconv_ty HE HA) (GEq_lwf HE W1)).
Qed.

Lemma C_actmnf_code_sig {G Γ l l1 l2 l3 l4 s s' t t'} : leqv l1 l3 -> leqv l2 l4 ->
  ac_tm G Γ s s' (tyU l1) -> C_tm G Γ s s' (tyU l1) -> C_tm G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) ->
  C_tmnf G Γ (tmSig l1 l2 s t) (tmSig l3 l4 s' t') (tyU l).
Proof.
  intros H13 H24 Ds IHs IHt i G2 Γ2 W2 k Hc HE Hctx Hx Hx' EW Hw2 x x' Hsx Hsx'. spa_triv. pose proof (compt_typeof_self _ Hc) as Hi.
  new_head Hc EW Hw2 W2.
  destruct (inv_code_sig Hi Hx) as ((Hc0 & W1 & W2 & Hs & Ht) & _).
  destruct (inv_code_sig Hi Hx') as ((_ & W3 & W4 & Hs' & Ht') & _).
  pose proof Hc0 as Hv.
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (ctx_of_wf_tm Hi Hs) as HΓ.
  assert (HΓt : [ G ; Γ ⊢[ typeof i ] ]) by (rewrite Hi; exact HΓ).
  assert (EU1 : [ G ; Γ ⊢[ i ] tyU l1 ≅ tyU l3 @ lsuc l1 ]) by (apply eqty_U; assumption).
  assert (Hs1 : [ G ; Γ ⊢[ i ] s' : tyU l1 @ lsuc l1 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Hs' | exact (lequiv_suc _ _ _ E13)] | rewrite Hi; exact EU1]. }
  pose proof (ac_tm_sound Hc Ds Hs Hs1) as Es.
  assert (Es' : [ G ; Γ ⊢[ i ] s' ≅ s : tyU l3 @ lsuc l3 ]).
  { eapply eqtm_lconv; [| exact (lequiv_suc _ _ _ (lequiv_sym _ _ _ E13))].
    eapply eqtm_conv; [exact (eqtm_sym _ _ _ _ _ _ _ Es) | rewrite Hi; exact (eqty_sym _ _ _ _ _ _ EU1)]. }
  assert (EEl : [ G ; Γ ⊢[ i ] tyEl l3 s' ≅ tyEl l1 s @ l3 ])
    by (apply eqty_El; [exact Hv | exact (lequiv_sym _ _ _ E13) | exact Es']).
  assert (HEl : [ G ; Γ ⊢[ i ] tyEl l1 s @ l1 ]) by (apply wft_El; assumption).
  assert (HΓ1 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HEl | exact W1]).
  pose proof (stab_tm Hi EEl (lequiv_sym _ _ _ E13) HΓ1 Ht') as Ht1.
  assert (EU2 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] tyU l2 ≅ tyU l4 @ lsuc l2 ])
    by (apply eqty_U; [exact Hv | rewrite Hi; exact HΓ1 | exact E24]).
  assert (Ht2 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t' : tyU l2 @ lsuc l2 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Ht1 | exact (lequiv_suc _ _ _ E24)] | rewrite Hi; exact EU2]. }
  apply actmnf_code_sig; [exact H13 | exact H24 | |].
  - exact (IHs i G2 Γ2 (tyU l1) (lsuc l1) Hc HE Hctx Hs Hs1 (eqty_refl _ _ _ _ _ (gconv_ty HE (wf_tm_ty Hi Hs))) _ _ spa_refl spa_refl).
  - apply (IHt i G2 (Γ2 ,, tyEl l1 s @ l1) (tyU l2) (lsuc l2) Hc HE); [| exact Ht | exact Ht2 | | exact spa_refl | exact spa_refl].
    + exact (eqctx_ext_refl Hctx (gconv_ty HE HEl) (GEq_lwf HE W1)).
    + exact (eqty_refl _ _ _ _ _ (gconv_ty HE (wf_tm_ty Hi Ht))).
Qed.
Lemma C_actmnf_code_W {G Γ l l1 l2 l3 l4 s s' t t'} : leqv l1 l3 -> leqv l2 l4 ->
  ac_tm G Γ s s' (tyU l1) -> C_tm G Γ s s' (tyU l1) -> C_tm G (Γ ,, tyEl l1 s @ l1) t t' (tyU l2) ->
  C_tmnf G Γ (tmW l1 l2 s t) (tmW l3 l4 s' t') (tyU l).
Proof.
  intros H13 H24 Ds IHs IHt i G2 Γ2 W2 k Hc HE Hctx Hx Hx' EW Hw2 x x' Hsx Hsx'. spa_triv. pose proof (compt_typeof_self _ Hc) as Hi.
  new_head Hc EW Hw2 W2.
  destruct (inv_code_W Hi Hx) as ((_ & W1 & W2 & Hs & Ht) & _).
  destruct (inv_code_W Hi Hx') as ((_ & W3 & W4 & Hs' & Ht') & _).
  assert (Hv : i <> lV) by (destruct Hc as [-> | ->]; discriminate).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (ctx_of_wf_tm Hi Hs) as HΓ.
  assert (HΓt : [ G ; Γ ⊢[ typeof i ] ]) by (rewrite Hi; exact HΓ).
  assert (EU1 : [ G ; Γ ⊢[ i ] tyU l1 ≅ tyU l3 @ lsuc l1 ]) by (apply eqty_U; assumption).
  assert (Hs1 : [ G ; Γ ⊢[ i ] s' : tyU l1 @ lsuc l1 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Hs' | exact (lequiv_suc _ _ _ E13)] | rewrite Hi; exact EU1]. }
  pose proof (ac_tm_sound Hc Ds Hs Hs1) as Es.
  assert (Es' : [ G ; Γ ⊢[ i ] s' ≅ s : tyU l3 @ lsuc l3 ]).
  { eapply eqtm_lconv; [| exact (lequiv_suc _ _ _ (lequiv_sym _ _ _ E13))].
    eapply eqtm_conv; [exact (eqtm_sym _ _ _ _ _ _ _ Es) | rewrite Hi; exact (eqty_sym _ _ _ _ _ _ EU1)]. }
  assert (EEl : [ G ; Γ ⊢[ i ] tyEl l3 s' ≅ tyEl l1 s @ l3 ])
    by (apply eqty_El; [exact Hv | exact (lequiv_sym _ _ _ E13) | exact Es']).
  assert (HEl : [ G ; Γ ⊢[ i ] tyEl l1 s @ l1 ]) by (apply wft_El; assumption).
  assert (HΓ1 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HEl | exact W1]).
  pose proof (stab_tm Hi EEl (lequiv_sym _ _ _ E13) HΓ1 Ht') as Ht1.
  assert (EU2 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] tyU l2 ≅ tyU l4 @ lsuc l2 ])
    by (apply eqty_U; [exact Hv | rewrite Hi; exact HΓ1 | exact E24]).
  assert (Ht2 : [ G ; Γ ,, tyEl l1 s @ l1 ⊢[ i ] t' : tyU l2 @ lsuc l2 ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Ht1 | exact (lequiv_suc _ _ _ E24)] | rewrite Hi; exact EU2]. }
  apply actmnf_code_W; [exact H13 | exact H24 | |].
  - exact (IHs i G2 Γ2 (tyU l1) (lsuc l1) Hc HE Hctx Hs Hs1 (eqty_refl _ _ _ _ _ (gconv_ty HE (wf_tm_ty Hi Hs))) _ _ spa_refl spa_refl).
  - apply (IHt i G2 (Γ2 ,, tyEl l1 s @ l1) (tyU l2) (lsuc l2) Hc HE); [| exact Ht | exact Ht2 | | exact spa_refl | exact spa_refl].
    + exact (eqctx_ext_refl Hctx (gconv_ty HE HEl) (GEq_lwf HE W1)).
    + exact (eqty_refl _ _ _ _ _ (gconv_ty HE (wf_tm_ty Hi Ht))).
Qed.

Lemma C_actmnf_sig_eta {G Γ l l' A B w w'} :
  ac_tm G Γ (tmFst l l' A B w) (tmFst l l' A B w') A ->
  C_tm G Γ (tmFst l l' A B w) (tmFst l l' A B w') A ->
  C_tm G Γ (tmSnd l l' A B w) (tmSnd l l' A B w') B[lsingle (tmFst l l' A B w)] ->
  C_tmnf G Γ w w' (tySig l l' A B).
Proof.
  intros D1 IH1 IH2 i G2 Γ2 W2 k Hc HE Hctx Hw Hw' EW Hw2 x x' Hsx Hsx'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (head_sig W2 (decl_head_c Hc EW Hw2 (whnf_tySig _ _ _ _))) as (m & m' & A2 & B2 & ->).
  destruct (inv_ty_sig (wf_tm_ty Hi Hw)) as ((Hv & W1 & W3 & HA & HB) & Hk).
  pose proof (lvl_eq_tm' Hk Hw) as Hw1. pose proof (lvl_eq_tm' Hk Hw') as Hw1'.
  destruct (sig_inj_c Hc (eqty_sym _ _ _ _ _ _ EW)) as (Em & Em' & EA & EB).
  (* the source projections *)
  pose proof (wf_fst _ _ _ _ _ _ _ _ Hv W1 W3 HA HB Hw1) as Hf.
  pose proof (wf_fst _ _ _ _ _ _ _ _ Hv W1 W3 HA HB Hw1') as Hf'.
  pose proof (wf_snd _ _ _ _ _ _ _ _ Hv W1 W3 HA HB Hw1) as Hs.
  pose proof (wf_snd _ _ _ _ _ _ _ _ Hv W1 W3 HA HB Hw1') as Hs'.
  pose proof (ac_tm_sound Hc D1 Hf Hf') as E1.
  pose proof (sig_fam_eq Hi HB (eqty_refl _ _ _ _ _ HB) (eqtm_sym _ _ _ _ _ _ _ E1) Hf' Hf) as EBs.
  assert (Hs1 : [ G ; Γ ⊢[ i ] tmSnd l l' A B w' : B[lsingle (tmFst l l' A B w)] @ l' ])
    by (eapply wf_conv; [exact Hs' | rewrite Hi; exact (eqty_sym _ _ _ _ _ _ EBs)]).
  (* the targets' projections, at the target's annotations *)
  assert (Hsf : forall y y', spa G2 i Γ y y' -> spa G2 i Γ (tmFst l l' A B y) (tmFst m m' A2 B2 y'))
    by (intros y y' Hy; apply spa_fst; [exact Hy | exact (lequiv_sym _ _ _ Em) | exact (lequiv_sym _ _ _ Em')
                                       | exact EA | exact EB]).
  assert (Hss : forall y y', spa G2 i Γ y y' -> spa G2 i Γ (tmSnd l l' A B y) (tmSnd m m' A2 B2 y'))
    by (intros y y' Hy; apply spa_snd; [exact Hy | exact (lequiv_sym _ _ _ Em) | exact (lequiv_sym _ _ _ Em')
                                       | exact EA | exact EB]).
  (* the type of the second projection moves with the scrutinee *)
  pose proof (spa_eq Hsx Hi _ _ (gconv_tm HE Hi Hw1)) as Ex.
  pose proof (eqtm_fst _ _ _ _ _ _ _ _ _ _ _ _ _ Hv (lequiv_sym _ _ _ Em) (lequiv_sym _ _ _ Em')
                (gconv_ty HE HA) EA EB Ex) as Efx.
  pose proof (sig_fam_eq Hi (gconv_ty HE HB) EB Efx (gconv_tm HE Hi Hf) (eqtm_wf_r Hi Efx)) as EBx.
  apply actmnf_sig_eta.
  - exact (IH1 i G2 Γ2 A2 l Hc HE Hctx Hf Hf' (eqty_sym _ _ _ _ _ _ EA) _ _ (Hsf _ _ Hsx) (Hsf _ _ Hsx')).
  - exact (IH2 i G2 Γ2 _ l' Hc HE Hctx Hs Hs1 (eqty_sym _ _ _ _ _ _ EBx) _ _ (Hss _ _ Hsx) (Hss _ _ Hsx')).
Qed.

(** The projections' annotations are the pair type's up to equality, and are
    not inspected; the result type is read off the inferred type. *)
Lemma C_actmne_fst {G Γ l1 l2 l3 l4 A A' B B' ν ν' m m' A0 B0} :
  ac_tmnee G Γ ν ν' (tySig m m' A0 B0) -> C_nee G Γ ν ν' (tySig m m' A0 B0) ->
  C_ne G Γ (tmFst l1 l2 A B ν) (tmFst l3 l4 A' B' ν') A0.
Proof.
  intros Dν IHν i G2 Γ2 k k' X X' Hc HE Hctx Hx Hx' x x' Hsx Hsx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (spa_fst_inv Hsx) as (hd & ? & ? & ? & ? & -> & Hf).
  destruct (spa_fst_inv Hsx') as (hd' & ? & ? & ? & ? & -> & Hf').
  destruct (inv_fst Hi Hx) as ((Hv & W1 & W2 & HA & HB & Hν) & Hk & HX).
  destruct (inv_fst Hi Hx') as ((_ & W3 & W4 & HA' & HB' & Hν') & _ & _).
  destruct (ac_nee_sound' Dν Hc Hν Hν') as (E0 & _ & _).
  destruct (sig_inj_c Hc E0) as (_ & _ & EA0 & _).
  destruct (IHν i G2 Γ2 _ _ _ _ Hc HE Hctx Hν Hν' _ _ Hf Hf') as (W & Xν & EW).
  destruct (head_sig W (decl_head_c Hc EW (ac_tmnee_whnf Xν) (whnf_tySig _ _ _ _))) as (n1 & n2 & A2 & B2 & ->).
  pose proof (eqty_trans _ _ _ _ _ _ _ (gconv_eqty HE Hi E0) (eqty_sym _ _ _ _ _ _ EW)) as ES.
  destruct (sig_inj_c Hc ES) as (_ & _ & FA & _).
  exists A2. split; [eapply actmne_fst; exact Xν |].
  apply (lvl_eq_eqty (lvl_eq_G2 HE Hk)).
  eapply eqty_trans; [exact (eqty_sym _ _ _ _ _ _ FA) | exact (gconv_eqty HE Hi EA0)].
Qed.

Lemma C_actmne_snd {G Γ l1 l2 l3 l4 A A' B B' ν ν' m m' A0 B0} :
  ac_tmnee G Γ ν ν' (tySig m m' A0 B0) -> C_nee G Γ ν ν' (tySig m m' A0 B0) ->
  C_ne G Γ (tmSnd l1 l2 A B ν) (tmSnd l3 l4 A' B' ν') B0[lsingle (tmFst m m' A0 B0 ν)].
Proof.
  intros Dν IHν i G2 Γ2 k k' X X' Hc HE Hctx Hx Hx' x x' Hsx Hsx'. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (spa_snd_inv Hsx) as (hd & ? & ? & ? & ? & -> & Hf).
  destruct (spa_snd_inv Hsx') as (hd' & ? & ? & ? & ? & -> & Hf').
  destruct (inv_snd Hi Hx) as ((Hv & W1 & W2 & HA & HB & Hν) & Hk & HX).
  destruct (inv_snd Hi Hx') as ((_ & W3 & W4 & HA' & HB' & Hν') & _ & _).
  destruct (ac_nee_sound' Dν Hc Hν Hν') as (E0 & _ & _).
  destruct (sig_inj_c Hc E0) as (Em1 & Em2 & EA0 & EB0).
  destruct (IHν i G2 Γ2 _ _ _ _ Hc HE Hctx Hν Hν' _ _ Hf Hf') as (W & Xν & EW).
  destruct (head_sig W (decl_head_c Hc EW (ac_tmnee_whnf Xν) (whnf_tySig _ _ _ _))) as (n1 & n2 & A2 & B2 & ->).
  pose proof (eqty_trans _ _ _ _ _ _ _ (gconv_eqty HE Hi E0) (eqty_sym _ _ _ _ _ _ EW)) as ES.
  destruct (sig_inj_c Hc ES) as (F1 & F2 & FA & FB).
  exists B2[lsingle (tmFst n1 n2 A2 B2 hd)]. split; [eapply actmne_snd; exact Xν |].
  (* source: the annotations against the inferred type *)
  pose proof (wf_fst _ _ _ _ _ _ _ _ Hv W1 W2 HA HB Hν) as Hf0.
  pose proof (eqtm_fst _ _ _ _ _ _ _ _ _ _ _ _ _ Hv (lequiv_sym _ _ _ Em1) (lequiv_sym _ _ _ Em2) HA EA0 EB0
                (eqtm_refl _ _ _ _ _ _ Hν)) as Ef0.
  pose proof (sig_fam_eq Hi HB EB0 Ef0 Hf0 (eqtm_wf_r Hi Ef0)) as EBB0.
  (* target: the scrutinee moved along [spa] *)
  pose proof (spa_eq Hf Hi _ _ (gconv_tm HE Hi Hν)) as Eh.
  pose proof (eqtm_fst _ _ _ _ _ _ _ _ _ _ _ _ _ Hv (lequiv_sym _ _ _ F1) (lequiv_sym _ _ _ F2)
                (gconv_ty HE HA) FA FB Eh) as Efh.
  pose proof (sig_fam_eq Hi (gconv_ty HE HB) FB Efh (gconv_tm HE Hi Hf0) (eqtm_wf_r Hi Efh)) as EBh.
  apply (lvl_eq_eqty (lvl_eq_G2 HE Hk)).
  eapply eqty_trans; [exact (eqty_sym _ _ _ _ _ _ EBh) | exact (gconv_eqty HE Hi EBB0)].
Qed.

(** ** The unit type (M8c) *)

Lemma C_actnf_unit {G Γ l l'} : leqv l l' -> C_tynf G Γ (tyUnit l) (tyUnit l').
Proof. intros Hl; red; intros; now apply actnf_unit. Qed.

Lemma C_actmnf_code_unit {G Γ l k k'} : leqv k k' -> C_tmnf G Γ (tmUnit k) (tmUnit k') (tyU l).
Proof.
  intros Hl; red; intros i G2 Γ2 W2 kk Hc HE Hctx Ht Ht' EW Hw2 x x' Hsx Hsx'. spa_triv. new_head Hc EW Hw2 W2.
  apply actmnf_code_unit; exact Hl.
Qed.
(** The codes of [Empty] and [+] (M12c). *)
Lemma C_actmnf_code_empty {G Γ l k k'} : leqv k k' -> C_tmnf G Γ (tmEmpty k) (tmEmpty k') (tyU l).
Proof.
  intros Hl; red; intros i G2 Γ2 W2 kk Hc HE Hctx Ht Ht' EW Hw2 x x' Hsx Hsx'. spa_triv. new_head Hc EW Hw2 W2.
  apply actmnf_code_empty; exact Hl.
Qed.

Lemma C_actmnf_code_sum {G Γ l l1 l2 l3 l4 s s' t t'} : leqv l1 l3 -> leqv l2 l4 ->
  C_tm G Γ s s' (tyU l1) -> C_tm G Γ t t' (tyU l2) -> C_tmnf G Γ (tmSum l1 l2 s t) (tmSum l3 l4 s' t') (tyU l).
Proof.
  intros H13 H24 IHs IHt i G2 Γ2 W2 m Hc HE Hctx Hx Hx' EW Hw2 x x' Hsx Hsx'. spa_triv.
  pose proof (compt_typeof_self _ Hc) as Hi. new_head Hc EW Hw2 W2.
  destruct (code_sum_prem Hc Hx) as (W1 & W2 & Hs & Ht). destruct (code_sum_prem Hc Hx') as (W3 & W4 & Hs' & Ht').
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  apply actmnf_code_sum; [exact H13 | exact H24 | |].
  - exact (IHs i G2 Γ2 (tyU l1) (lsuc l1) Hc HE Hctx Hs (code_U_conv Hc E13 Hs')
             (eqty_refl _ _ _ _ _ (gconv_ty HE (wf_tm_ty Hi Hs))) _ _ spa_refl spa_refl).
  - exact (IHt i G2 Γ2 (tyU l2) (lsuc l2) Hc HE Hctx Ht (code_U_conv Hc E24 Ht')
             (eqty_refl _ _ _ _ _ (gconv_ty HE (wf_tm_ty Hi Ht))) _ _ spa_refl spa_refl).
Qed.

(** The codes of [Vec] and [Fin] (M14b). *)
Lemma C_actmnf_code_vec {G Γ l k k' s s' n n'} : leqv k k' ->
  C_tm G Γ s s' (tyU k) -> C_tm G Γ n n' tyNat -> C_tmnf G Γ (tmVec k s n) (tmVec k' s' n') (tyU l).
Proof.
  intros Hk0 IHs IHn i G2 Γ2 W2 m Hc HE Hctx Hx Hx' EW Hw2 x x' Hsx Hsx'. spa_triv.
  pose proof (compt_typeof_self _ Hc) as Hi. new_head Hc EW Hw2 W2.
  destruct (code_vec_prem Hc Hx) as (Wk & Hs & Hn). destruct (code_vec_prem Hc Hx') as (Wk' & Hs' & Hn').
  pose proof (leqv_lequiv _ _ _ Wk Wk' Hk0) as E.
  apply actmnf_code_vec; [exact Hk0 | |].
  - exact (IHs i G2 Γ2 (tyU k) (lsuc k) Hc HE Hctx Hs (code_U_conv Hc E Hs')
             (eqty_refl _ _ _ _ _ (gconv_ty HE (wf_tm_ty Hi Hs))) _ _ spa_refl spa_refl).
  - exact (IHn i G2 Γ2 tyNat lzero Hc HE Hctx Hn Hn'
             (eqty_refl _ _ _ _ _ (gconv_ty HE (wf_tm_ty Hi Hn))) _ _ spa_refl spa_refl).
Qed.

Lemma C_actmnf_code_fin {G Γ l n n'} : C_tm G Γ n n' tyNat -> C_tmnf G Γ (tmFin n) (tmFin n') (tyU l).
Proof.
  intros IHn i G2 Γ2 W2 m Hc HE Hctx Hx Hx' EW Hw2 x x' Hsx Hsx'. spa_triv.
  pose proof (compt_typeof_self _ Hc) as Hi. new_head Hc EW Hw2 W2.
  pose proof (code_fin_prem Hc Hx) as Hn. pose proof (code_fin_prem Hc Hx') as Hn'.
  apply actmnf_code_fin.
  exact (IHn i G2 Γ2 tyNat lzero Hc HE Hctx Hn Hn'
           (eqty_refl _ _ _ _ _ (gconv_ty HE (wf_tm_ty Hi Hn))) _ _ spa_refl spa_refl).
Qed.

Lemma C_actmnf_code_sempty {G Γ l k k'} : leqv k k' -> C_tmnf G Γ (tmSEmpty k) (tmSEmpty k') (tyU l).
Proof.
  intros Hl; red; intros i G2 Γ2 W2 kk Hc HE Hctx Ht Ht' EW Hw2 x x' Hsx Hsx'. spa_triv. new_head Hc EW Hw2 W2.
  apply actmnf_code_sempty; exact Hl.
Qed.

(** η: any targets, once the new type is [Unit] too. *)
Lemma C_actmnf_unit_eta {G Γ l w w'} : C_tmnf G Γ w w' (tyUnit l).
Proof.
  red; intros i G2 Γ2 W2 k Hc HE Hctx Ht Ht' EW Hw2 x x' Hsx Hsx'. new_head Hc EW Hw2 W2.
  apply actmnf_unit_eta.
Qed.

(** ** Strict equality (M10a) *)

Lemma C_actnf_seq {G Γ l l' A A' a a' b b'} : leqv l l' ->
  ac_ty G Γ A A' -> C_ty G Γ A A' -> ac_tm G Γ a a' A -> C_tm G Γ a a' A ->
  ac_tm G Γ b b' A -> C_tm G Γ b b' A -> C_tynf G Γ (tySEq l A a b) (tySEq l' A' a' b').
Proof.
  intros Hl DA IHA Da IHa Db IHb i G2 Γ2 k k' Hc HE Hctx HT HT'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_seq HT) as ((_ & W & HA & Ha & Hb) & _).
  destruct (inv_ty_seq HT') as ((_ & W' & HA' & Ha' & Hb') & _).
  pose proof (leqv_lequiv _ _ _ W W' Hl) as E.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E)) as EA.
  assert (F : forall x, [ G ; Γ ⊢[ i ] x : A' @ l' ] -> [ G ; Γ ⊢[ i ] x : A @ l ]).
  { intros x Hx. eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hx E) | rewrite Hi; exact EA]. }
  pose proof (eqty_refl _ _ _ _ _ (gconv_ty HE HA)) as HAr.
  apply actnf_seq; [exact Hl | exact (IHA i G2 Γ2 l l' Hc HE Hctx HA HA') |
                    exact (IHa i G2 Γ2 A l Hc HE Hctx Ha (F _ Ha') HAr _ _ spa_refl spa_refl) |
                    exact (IHb i G2 Γ2 A l Hc HE Hctx Hb (F _ Hb') HAr _ _ spa_refl spa_refl)].
Qed.

Lemma C_actnf_sempty {G Γ l l'} : leqv l l' -> C_tynf G Γ (tySEmpty l) (tySEmpty l').
Proof. intros Hl; red; intros; now apply actnf_sempty. Qed.

(** The empty type (M12a). *)
Lemma C_actnf_empty {G Γ l l'} : leqv l l' -> C_tynf G Γ (tyEmpty l) (tyEmpty l').
Proof. intros Hl; red; intros; now apply actnf_empty. Qed.

Lemma C_actmnf_empty_irr {G Γ l w w'} : C_tmnf G Γ w w' (tyEmpty l).
Proof.
  red; intros i G2 Γ2 W2 k Hc HE Hctx Ht Ht' EW Hw2 x x' Hsx Hsx'. new_head Hc EW Hw2 W2.
  apply actmnf_empty_irr.
Qed.

Lemma C_actmne_elimEmpty {G Γ l1 l2 l3 l4 M M' ν ν'} : leqv l1 l3 -> leqv l2 l4 ->
  ac_ty G (Γ ,, tyEmpty l2 @ l2) M M' -> C_ty G (Γ ,, tyEmpty l2 @ l2) M M' ->
  whne ν -> whne ν' ->
  C_ne G Γ (elimEmpty l1 l2 M ν) (elimEmpty l3 l4 M' ν') M[lsingle ν].
Proof.
  intros H13 H24 DM IHM Hn Hn' i G2 Γ2 k k' X X' Hc HE Hctx Hx Hx' x x' Hsx Hsx'. spa_triv.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_elimEmpty Hi Hx) as ((_ & W1 & W2 & HM & Hν) & _ & _).
  destruct (inv_elimEmpty Hi Hx') as ((_ & W3 & W4 & HM' & Hν') & _ & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (ctx_of_wf_tm Hi Hν) as HΓ.
  assert (HE2 : [ G ; Γ ⊢[ i ] tyEmpty l2 @ l2 ]) by (apply wft_empty; [exact (compt_notV _ Hc) | rewrite Hi; exact HΓ | exact W2]).
  assert (HEE : [ G ; Γ ⊢[ i ] tyEmpty l4 ≅ tyEmpty l2 @ l4 ])
    by (apply eqty_empty; [exact (compt_notV _ Hc) | rewrite Hi; exact HΓ | exact (lequiv_sym _ _ _ E24)]).
  assert (HΓE : [ G ; Γ ,, tyEmpty l2 @ l2 ⊢[ i ] ]) by (apply wfc_ext; [exact HΓ | exact HE2 | exact W2]).
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty Hi HEE (lequiv_sym _ _ _ E24) HΓE HM') E13) as HM'1.
  assert (HctxE : [ G2 ⊢[ i ] Γ ,, tyEmpty l2 @ l2 ≅ Γ2 ,, tyEmpty l2 @ l2 ])
    by exact (eqctx_ext_refl Hctx (gconv_ty HE HE2) (GEq_lwf HE W2)).
  exists M[lsingle ν]. split.
  - apply actmne_elimEmpty; [exact H13 | exact H24 | exact (IHM i G2 _ l1 l1 Hc HE HctxE HM HM'1)
                            | exact Hn | exact Hn'].
  - exact (ne_refl (actmne_elimEmpty _ _ _ _ _ _ _ _ _ _ H13 H24 DM Hn Hn') Hc HE Hx Hx').
Qed.

(** Binary sums (M12b). *)
Lemma C_actnf_sum {G Γ l1 l2 l3 l4 A A' B B'} : leqv l1 l3 -> leqv l2 l4 ->
  C_ty G Γ A A' -> C_ty G Γ B B' -> C_tynf G Γ (tySum l1 l2 A B) (tySum l3 l4 A' B').
Proof.
  intros H13 H24 IHA IHB i G2 Γ2 k k' Hc HE Hctx HT HT'.
  destruct (inv_ty_sum HT) as ((_ & W1 & W2 & HA & HB) & _).
  destruct (inv_ty_sum HT') as ((_ & W3 & W4 & HA' & HB') & _).
  apply actnf_sum; [exact H13 | exact H24 | exact (IHA i G2 Γ2 l1 l3 Hc HE Hctx HA HA')
                   | exact (IHB i G2 Γ2 l2 l4 Hc HE Hctx HB HB')].
Qed.

Lemma C_actmnf_inl {G Γ l l' A B k1 k2 k3 k4 C D C' D' a a'} : C_tm G Γ a a' A ->
  C_tmnf G Γ (tmInl k1 k2 C D a) (tmInl k3 k4 C' D' a') (tySum l l' A B).
Proof.
  intros IHa i G2 Γ2 W2 m Hc HE Hctx Ht Ht' EW Hw2 x x' Hsx Hsx'. spa_triv.
  destruct (head_sum W2 (decl_head_c Hc EW Hw2 (whnf_tySum _ _ _ _))) as (m1 & m2 & A2 & B2 & ->).
  destruct (sum_inj_c Hc (eqty_sym _ _ _ _ _ _ EW)) as (E1 & _ & EA & _).
  apply actmnf_inl.
  exact (IHa i G2 Γ2 A2 l Hc HE Hctx (inl_payload Hc Ht) (inl_payload Hc Ht')
           (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EA) (lequiv_refl _ _ (lequiv_wf_r _ _ _ E1)))
           _ _ spa_refl spa_refl).
Qed.

Lemma C_actmnf_inr {G Γ l l' A B k1 k2 k3 k4 C D C' D' b b'} : C_tm G Γ b b' B ->
  C_tmnf G Γ (tmInr k1 k2 C D b) (tmInr k3 k4 C' D' b') (tySum l l' A B).
Proof.
  intros IHb i G2 Γ2 W2 m Hc HE Hctx Ht Ht' EW Hw2 x x' Hsx Hsx'. spa_triv.
  destruct (head_sum W2 (decl_head_c Hc EW Hw2 (whnf_tySum _ _ _ _))) as (m1 & m2 & A2 & B2 & ->).
  destruct (sum_inj_c Hc (eqty_sym _ _ _ _ _ _ EW)) as (_ & E2 & _ & EB).
  apply actmnf_inr.
  exact (IHb i G2 Γ2 B2 l' Hc HE Hctx (inr_payload Hc Ht) (inr_payload Hc Ht')
           (eqty_lconv _ _ _ _ _ _ _ (eqty_sym _ _ _ _ _ _ EB) (lequiv_refl _ _ (lequiv_wf_r _ _ _ E2)))
           _ _ spa_refl spa_refl).
Qed.

Lemma C_actmne_case {G Γ l1 l2 l3 l4 l5 l6 A A' B B' M M' c1 c1' c2 c2' ν ν' W} :
  leqv l1 l4 -> leqv l2 l5 -> leqv l3 l6 ->
  ac_ty G Γ A A' -> C_ty G Γ A A' -> ac_ty G Γ B B' -> C_ty G Γ B B' ->
  ac_ty G (Γ ,, tySum l1 l2 A B @ lmax l1 l2) M M' -> C_ty G (Γ ,, tySum l1 l2 A B @ lmax l1 l2) M M' ->
  ac_tm G (Γ ,, A @ l1) c1 c1' M⟨rlift ↑⟩[lsingle (tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] ->
  C_tm G (Γ ,, A @ l1) c1 c1' M⟨rlift ↑⟩[lsingle (tmInl l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] ->
  ac_tm G (Γ ,, B @ l2) c2 c2' M⟨rlift ↑⟩[lsingle (tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] ->
  C_tm G (Γ ,, B @ l2) c2 c2' M⟨rlift ↑⟩[lsingle (tmInr l1 l2 A⟨↑⟩ B⟨↑⟩ (var 0))] ->
  ac_tmnee G Γ ν ν' W -> C_nee G Γ ν ν' W ->
  C_ne G Γ (tmCase l1 l2 l3 A B M c1 c2 ν) (tmCase l4 l5 l6 A' B' M' c1' c2' ν') M[lsingle ν].
Proof.
  intros H14 H25 H36 DA IHA DB IHB DM IHM Dc1 IHc1 Dc2 IHc2 Dν IHν i G2 Γ2 k k' X X' Hc HE Hctx Hx Hx' x x' Hsx Hsx'.
  spa_triv. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_case Hi Hx) as ((_ & W1 & W2 & W3 & HA & HB & HM & Hc1 & Hc2 & Hν) & _ & _).
  destruct (inv_case Hi Hx') as ((_ & W4 & W5 & W6 & HA' & HB' & HM' & Hc1' & Hc2' & Hν') & _ & _).
  pose proof (leqv_lequiv _ _ _ W1 W4 H14) as E14. pose proof (leqv_lequiv _ _ _ W2 W5 H25) as E25.
  pose proof (leqv_lequiv _ _ _ W3 W6 H36) as E36.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E14)) as EA.
  pose proof (ac_ty_sound Hc DB HB (wft_lconv _ _ _ _ _ _ HB' E25)) as EB.
  destruct (case_right_left (M := M) (c1' := c1') (c2' := c2') (ν' := ν') Hc E14 E25 E36 HA HB HA' HB' EA EB HM')
    as [HM'3 Hbr].
  pose proof (ac_ty_sound Hc DM HM HM'3) as EM.
  destruct (Hbr HM EM Hc1' Hc2' Hν') as (_ & _ & Hc1'2 & Hc2'2 & _).
  assert (HS : [ G ; Γ ⊢[ i ] tySum l1 l2 A B @ lmax l1 l2 ]) by (apply wft_sum; [exact (compt_notV _ Hc) | ..]; assumption).
  assert (HctxS : [ G2 ⊢[ i ] Γ ,, tySum l1 l2 A B @ lmax l1 l2 ≅ Γ2 ,, tySum l1 l2 A B @ lmax l1 l2 ])
    by exact (eqctx_ext_refl Hctx (gconv_ty HE HS) (GEq_lwf HE (l := lmax l1 l2) (conj W1 W2))).
  assert (HctxA : [ G2 ⊢[ i ] Γ ,, A @ l1 ≅ Γ2 ,, A @ l1 ])
    by exact (eqctx_ext_refl Hctx (gconv_ty HE HA) (GEq_lwf HE W1)).
  assert (HctxB : [ G2 ⊢[ i ] Γ ,, B @ l2 ≅ Γ2 ,, B @ l2 ])
    by exact (eqctx_ext_refl Hctx (gconv_ty HE HB) (GEq_lwf HE W2)).
  destruct (IHν i G2 Γ2 _ _ _ _ Hc HE Hctx Hν Hν' _ _ spa_refl spa_refl) as (Wν & Xν & _).
  exists M[lsingle ν]. split.
  - eapply actmne_case; [exact H14 | exact H25 | exact H36 | | | | | | exact Xν].
    + exact (IHA i G2 Γ2 l1 l4 Hc HE Hctx HA HA').
    + exact (IHB i G2 Γ2 l2 l5 Hc HE Hctx HB HB').
    + exact (IHM i G2 _ l3 l3 Hc HE HctxS HM HM'3).
    + exact (IHc1 i G2 _ _ l3 Hc HE HctxA Hc1 Hc1'2 (eqty_refl _ _ _ _ _ (gconv_ty HE (wf_tm_ty Hi Hc1)))
               _ _ spa_refl spa_refl).
    + exact (IHc2 i G2 _ _ l3 Hc HE HctxB Hc2 Hc2'2 (eqty_refl _ _ _ _ _ (gconv_ty HE (wf_tm_ty Hi Hc2)))
               _ _ spa_refl spa_refl).
  - exact (ne_refl (actmne_case _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H14 H25 H36 DA DB DM Dc1 Dc2 Dν)
             Hc HE Hx Hx').
Qed.

(** Well-founded trees (M13a). *)
Lemma C_actnf_W {G Γ l1 l2 l3 l4 A A' B B'} : leqv l1 l3 -> leqv l2 l4 ->
  ac_ty G Γ A A' -> C_ty G Γ A A' -> C_ty G (Γ ,, A @ l1) B B' ->
  C_tynf G Γ (tyW l1 l2 A B) (tyW l3 l4 A' B').
Proof.
  intros H13 H24 DA IHA IHB i G2 Γ2 k k' Hc HE Hctx HT HT'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_W HT) as ((_ & W1 & W2 & HA & HB) & _).
  destruct (inv_ty_W HT') as ((_ & W3 & W4 & HA' & HB') & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E13)) as EA.
  assert (HΓA : [ G ; Γ ,, A @ l1 ⊢[ i ] ]) by (apply wfc_ext; [exact (ctx_of_wf_ty Hi HA) | exact HA | exact W1]).
  assert (EA' : [ G ; Γ ⊢[ i ] A' ≅ A @ l3 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E13)]).
  pose proof (stab_ty Hi EA' (lequiv_sym _ _ _ E13) HΓA HB') as HB1.
  apply actnf_W; [exact H13 | exact H24 | exact (IHA i G2 Γ2 l1 l3 Hc HE Hctx HA HA') |].
  apply (IHB i G2 (Γ2 ,, A @ l1) l2 l4 Hc HE); [| exact HB | exact HB1].
  exact (eqctx_ext_refl Hctx (gconv_ty HE HA) (GEq_lwf HE W1)).
Qed.

Lemma C_actmnf_sup {G Γ l l' A B k1 k2 k3 k4 C D C' D' a a' f f'} : ac_tm G Γ a a' A -> C_tm G Γ a a' A ->
  C_tm G Γ f f' (tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩) ->
  C_tmnf G Γ (tmSup k1 k2 C D a f) (tmSup k3 k4 C' D' a' f') (tyW l l' A B).
Proof.
  intros Da IHa IHf i G2 Γ2 W2 m Hc HE Hctx Ht Ht' EW Hw2 x x' Hsx Hsx'. spa_triv.
  pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  destruct (head_W W2 (decl_head_c Hc EW Hw2 (whnf_tyW _ _ _ _))) as (m1 & m2 & A2 & B2 & ->).
  destruct (W_inj_c Hc (eqty_sym _ _ _ _ _ _ EW)) as (E1 & E2 & EA & EB).
  destruct (sup_parts Hc Ht) as (Wl0 & Wl0' & HA & HB & Ha & Hf).
  destruct (sup_parts Hc Ht') as (_ & _ & _ & _ & Ha' & Hf'0).
  pose proof (ac_tm_sound Hc Da Ha Ha') as Ea.
  assert (Hf' : [ G ; Γ ⊢[ i ] f' : tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩ @ lmax l' (lmax l l') ]).
  { eapply wf_conv; [exact Hf'0 | rewrite Hi]. apply eqty_sym. exact (fty_conv Hc Wl0 Wl0' HA HB Ha Ha' (eqtm_sym _ _ _ _ _ _ _ Ea)). }
  pose proof (lequiv_wf_r _ _ _ E1) as Wl. pose proof (lequiv_wf_r _ _ _ E2) as Wl'.
  pose proof (gconv_ty HE HA) as HA2. pose proof (gconv_tm HE Hi Ha) as Ha2.
  pose proof (gconv_ty HE HB) as HB2.
  assert (EW2 : [ G2 ; Γ ⊢[ i ] tyW l l' A B ≅ tyW m1 m2 A2 B2 @ lmax l l' ])
    by (apply eqty_W; first [(apply compt_notV; exact Hc) | exact Hc | now apply lequiv_sym | assumption]).
  assert (HBa : [ G2 ; Γ ⊢[ i ] B[lsingle a] @ l' ]) by exact (wf_ty_single Hi HB2 Ha2).
  pose proof (ext_wf Hi HBa Wl') as HΓB.
  assert (EF : [ G2 ; Γ ⊢[ i ] tyPi l' (lmax l l') B[lsingle a] (tyW l l' A B)⟨↑⟩
                 ≅ tyPi m2 (lmax m1 m2) B2[lsingle a] (tyW m1 m2 A2 B2)⟨↑⟩ @ lmax l' (lmax l l') ]).
  { apply eqty_pi; first [exact Hv | now apply lequiv_sym | apply lequiv_max; now apply lequiv_sym | exact HBa
                         | idtac].
    - exact (eqty_single Hi EB Ha2).
    - exact (wk1_eqty _ _ Hi _ _ _ _ _ _ HΓB EW2). }
  apply actmnf_sup.
  - exact (IHa i G2 Γ2 A2 l Hc HE Hctx Ha Ha' (eqty_sym _ _ _ _ _ _ EA) _ _ spa_refl spa_refl).
  - exact (IHf i G2 Γ2 _ _ Hc HE Hctx Hf Hf' (eqty_sym _ _ _ _ _ _ EF) _ _ spa_refl spa_refl).
Qed.

Lemma C_actmne_elimW {G Γ l1 l2 l3 l4 l5 l6 A A' B B' M M' c c' ν ν' W} :
  leqv l1 l4 -> leqv l2 l5 -> leqv l3 l6 ->
  ac_ty G Γ A A' -> C_ty G Γ A A' -> ac_ty G (Γ ,, A @ l1) B B' -> C_ty G (Γ ,, A @ l1) B B' ->
  ac_ty G (Γ ,, tyW l1 l2 A B @ lmax l1 l2) M M' -> C_ty G (Γ ,, tyW l1 l2 A B @ lmax l1 l2) M M' ->
  ac_tm G (Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, wihty l1 l2 l3 A B M @ lmax l2 l3)
    c c' (wstepty l1 l2 A B M) ->
  C_tm G (Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, wihty l1 l2 l3 A B M @ lmax l2 l3)
    c c' (wstepty l1 l2 A B M) ->
  ac_tmnee G Γ ν ν' W -> C_nee G Γ ν ν' W ->
  C_ne G Γ (tmElimW l1 l2 l3 A B M c ν) (tmElimW l4 l5 l6 A' B' M' c' ν') M[lsingle ν].
Proof.
  intros H14 H25 H36 DA IHA DB IHB DM IHM Dc IHc Dν IHν i G2 Γ2 k k' X X' Hc HE Hctx Hx Hx' x x' Hsx Hsx'.
  spa_triv. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_elimW Hi Hx) as ((_ & W1 & W2 & W3 & HA & HB & HM & HF & HI & Hc0 & Hν) & _ & _).
  destruct (inv_elimW Hi Hx') as ((_ & W4 & W5 & W6 & HA' & HB' & HM' & HF' & HI' & Hc0' & Hν') & _ & _).
  pose proof (leqv_lequiv _ _ _ W1 W4 H14) as E14. pose proof (leqv_lequiv _ _ _ W2 W5 H25) as E25.
  pose proof (leqv_lequiv _ _ _ W3 W6 H36) as E36.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E14)) as EA.
  pose proof (ext_wf Hi HA W1) as HΓA.
  assert (EA4 : [ G ; Γ ⊢[ i ] A' ≅ A @ l4 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E14)]).
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty Hi EA4 (lequiv_sym _ _ _ E14) HΓA HB') E25) as HB'A.
  pose proof (ac_ty_sound Hc DB HB HB'A) as EB.
  assert (WL : lwf (gL G) (lmax l1 l2)) by (cbn; split; assumption).
  assert (HL : lequiv (gL G) (lmax l4 l5) (lmax l1 l2)) by (apply lequiv_max; now apply lequiv_sym).
  assert (HW : [ G ; Γ ⊢[ i ] tyW l1 l2 A B @ lmax l1 l2 ]) by (apply wft_W; first [assumption | (apply compt_notV; eassumption)]).
  assert (EW' : [ G ; Γ ⊢[ i ] tyW l4 l5 A' B' ≅ tyW l1 l2 A B @ lmax l4 l5 ]).
  { eapply eqty_lconv; [apply eqty_sym, eqty_W; first [assumption | (apply compt_notV; eassumption)] | exact HL]. }
  pose proof (ext_wf Hi HW WL) as HΓW.
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty Hi EW' HL HΓW HM') E36) as HM'3.
  pose proof (ac_ty_sound Hc DM HM HM'3) as EM.
  pose proof (elimW_step_left Hc E14 E25 E36 HA HA' EA HB HB' EB HM HM' EM HF HI Hc0') as Hc0'2.
  assert (HctxA : [ G2 ⊢[ i ] Γ ,, A @ l1 ≅ Γ2 ,, A @ l1 ])
    by exact (eqctx_ext_refl Hctx (gconv_ty HE HA) (GEq_lwf HE W1)).
  assert (HctxW : [ G2 ⊢[ i ] Γ ,, tyW l1 l2 A B @ lmax l1 l2 ≅ Γ2 ,, tyW l1 l2 A B @ lmax l1 l2 ])
    by exact (eqctx_ext_refl Hctx (gconv_ty HE HW) (GEq_lwf HE WL)).
  assert (HctxT : [ G2 ⊢[ i ] Γ ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, wihty l1 l2 l3 A B M @ lmax l2 l3
                    ≅ Γ2 ,, A @ l1 ,, wfty l1 l2 A B @ lmax l2 (lmax l1 l2) ,, wihty l1 l2 l3 A B M @ lmax l2 l3 ]).
  { apply (eqctx_ext_refl (eqctx_ext_refl HctxA (gconv_ty HE HF) (GEq_lwf HE (lwf_max W2 WL))) (gconv_ty HE HI)).
    exact (GEq_lwf HE (lwf_max W2 W3)). }
  destruct (IHν i G2 Γ2 _ _ _ _ Hc HE Hctx Hν Hν' _ _ spa_refl spa_refl) as (Wν & Xν & _).
  exists M[lsingle ν]. split.
  - eapply actmne_elimW; [exact H14 | exact H25 | exact H36 | | | | | exact Xν].
    + exact (IHA i G2 Γ2 l1 l4 Hc HE Hctx HA HA').
    + exact (IHB i G2 _ l2 l2 Hc HE HctxA HB HB'A).
    + exact (IHM i G2 _ l3 l3 Hc HE HctxW HM HM'3).
    + exact (IHc i G2 _ _ l3 Hc HE HctxT Hc0 Hc0'2 (eqty_refl _ _ _ _ _ (gconv_ty HE (wf_tm_ty Hi Hc0)))
               _ _ spa_refl spa_refl).
  - exact (ne_refl (actmne_elimW _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H14 H25 H36 DA DB DM Dc Dν) Hc HE Hx Hx').
Qed.

(** Finitary well-founded trees (M15a). *)
Lemma C_actnf_wf {G Γ l l' A A' N N'} : leqv l l' ->
  ac_ty G Γ A A' -> C_ty G Γ A A' -> ac_tm G (Γ ,, A @ l) N N' tyNat -> C_tm G (Γ ,, A @ l) N N' tyNat ->
  C_tynf G Γ (tyWf l A N) (tyWf l' A' N').
Proof.
  intros Hl DA IHA DN IHN i G2 Γ2 k k' Hc HE Hctx HT HT'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_wf HT) as ((_ & W1 & HA & HN) & _).
  destruct (inv_ty_wf HT') as ((_ & W2 & HA' & HN') & _).
  pose proof (leqv_lequiv _ _ _ W1 W2 Hl) as E.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E)) as EA.
  assert (HΓA : [ G ; Γ ,, A @ l ⊢[ i ] ]) by (apply wfc_ext; [exact (ctx_of_wf_ty Hi HA) | exact HA | exact W1]).
  assert (EA' : [ G ; Γ ⊢[ i ] A' ≅ A @ l' ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E)]).
  pose proof (stab_tm Hi EA' (lequiv_sym _ _ _ E) HΓA HN') as HN1.
  apply actnf_wf; [exact Hl | exact (IHA i G2 Γ2 l l' Hc HE Hctx HA HA') |].
  apply (IHN i G2 (Γ2 ,, A @ l) tyNat lzero Hc HE); [| exact HN | exact HN1 | | apply spa_refl | apply spa_refl].
  - exact (eqctx_ext_refl Hctx (gconv_ty HE HA) (GEq_lwf HE W1)).
  - exact (eqty_refl _ _ _ _ _ (gconv_ty HE (wf_tm_ty Hi HN))).
Qed.

(** A [sup_f] at a [Wf] type: its pieces at the type's. *)
Lemma supf_parts {G i Γ l A N k C D a cs m} : compt i ->
  [ G ; Γ ⊢[ i ] tmSupf k C D a cs : tyWf l A N @ m ] ->
  lwf (gL G) l /\ [ G ; Γ ⊢[ i ] A @ l ] /\ [ G ; Γ ,, A @ l ⊢[ i ] N : tyNat @ lzero ] /\
  [ G ; Γ ⊢[ i ] a : A @ l ] /\ [ G ; Γ ⊢[ i ] cs : tyVec l (tyWf l A N) N[lsingle a] @ l ].
Proof.
  intros Hc Ht. pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  destruct (inv_supf Hi Ht) as ((_ & Wk & HC & HD & Ha & Hcs) & _ & ET).
  destruct (Wf_inj_c Hc ET) as (E1 & EAC & END).
  pose proof (lequiv_wf_r _ _ _ E1) as Wl.
  pose proof (eqty_wf_l Hi EAC) as HA. pose proof (eqtm_wf_l Hi END) as HN.
  assert (Ha1 : [ G ; Γ ⊢[ i ] a : A @ l ]).
  { eapply wf_conv; [eapply wf_lconv; [exact Ha | now apply lequiv_sym] | rewrite Hi; exact EAC]. }
  assert (HW : [ G ; Γ ⊢[ i ] tyWf l A N @ l ]) by (apply wft_wf; assumption).
  assert (EW : [ G ; Γ ⊢[ i ] tyWf l A N ≅ tyWf k C D @ l ])
    by (apply eqty_wf; first [assumption | now apply lequiv_sym]).
  assert (ECs : [ G ; Γ ⊢[ i ] tyVec l (tyWf l A N) N[lsingle a] ≅ tyVec k (tyWf k C D) D[lsingle a] @ l ]).
  { apply eqty_vec; first [exact Hv | now apply lequiv_sym | exact HW | exact EW | idtac].
    exact (Wf_Na_eq Hi HN END Ha1 Ha1 (eqtm_refl _ _ _ _ _ _ Ha1)). }
  refine (conj Wl (conj HA (conj HN (conj Ha1 _)))).
  eapply wf_conv; [eapply wf_lconv; [exact Hcs | now apply lequiv_sym] | rewrite Hi; exact ECs].
Qed.

Lemma C_actmnf_supf {G Γ l A N k k' C D C' D' a a' cs cs'} : ac_tm G Γ a a' A -> C_tm G Γ a a' A ->
  ac_tm G Γ cs cs' (tyVec l (tyWf l A N) N[lsingle a]) -> C_tm G Γ cs cs' (tyVec l (tyWf l A N) N[lsingle a]) ->
  C_tmnf G Γ (tmSupf k C D a cs) (tmSupf k' C' D' a' cs') (tyWf l A N).
Proof.
  intros Da IHa Dcs IHcs i G2 Γ2 W2 m Hc HE Hctx Ht Ht' EW Hw2 x x' Hsx Hsx'. spa_triv.
  pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  destruct (head_wf W2 (decl_head_c Hc EW Hw2 (whnf_tyWf _ _ _))) as (m1 & A2 & N2 & ->).
  destruct (Wf_inj_c Hc (eqty_sym _ _ _ _ _ _ EW)) as (E1 & EA & EN).
  destruct (supf_parts Hc Ht) as (Wl & HA & HN & Ha & Hcs).
  destruct (supf_parts Hc Ht') as (_ & _ & _ & Ha' & Hcs'0).
  pose proof (ac_tm_sound Hc Da Ha Ha') as Ea.
  assert (HW : [ G ; Γ ⊢[ i ] tyWf l A N @ l ]) by (apply wft_wf; assumption).
  assert (Hcs' : [ G ; Γ ⊢[ i ] cs' : tyVec l (tyWf l A N) N[lsingle a] @ l ]).
  { eapply wf_conv; [exact Hcs'0 | rewrite Hi].
    apply eqty_vec; first [exact Hv | apply lequiv_refl, Wl | exact HW | apply eqty_refl, HW | idtac].
    exact (Wf_Na_eq Hi HN (eqtm_refl _ _ _ _ _ _ HN) Ha Ha' Ea). }
  pose proof (gconv_ty HE HA) as HA2. pose proof (gconv_tm HE Hi Ha) as Ha2.
  pose proof (gconv_tm HE Hi HN) as HN2.
  assert (EW2 : [ G2 ; Γ ⊢[ i ] tyWf l A N ≅ tyWf m1 A2 N2 @ l ])
    by (apply eqty_wf; first [exact Hc | now apply lequiv_sym | assumption]).
  assert (ECs : [ G2 ; Γ ⊢[ i ] tyVec l (tyWf l A N) N[lsingle a] ≅ tyVec m1 (tyWf m1 A2 N2) N2[lsingle a] @ l ]).
  { apply eqty_vec; first [exact Hv | now apply lequiv_sym | exact (eqty_wf_l Hi EW2) | exact EW2 | idtac].
    exact (Wf_Na_eq Hi HN2 EN Ha2 Ha2 (eqtm_refl _ _ _ _ _ _ Ha2)). }
  apply actmnf_supf.
  - exact (IHa i G2 Γ2 A2 l Hc HE Hctx Ha Ha' (eqty_sym _ _ _ _ _ _ EA) _ _ spa_refl spa_refl).
  - exact (IHcs i G2 Γ2 _ l Hc HE Hctx Hcs Hcs' (eqty_sym _ _ _ _ _ _ ECs) _ _ spa_refl spa_refl).
Qed.

Lemma C_actmne_elimWf {G Γ l1 l2 l3 l4 A A' N N' M M' c c' ν ν' W} :
  leqv l1 l3 -> leqv l2 l4 ->
  ac_ty G Γ A A' -> C_ty G Γ A A' -> ac_tm G (Γ ,, A @ l1) N N' tyNat -> C_tm G (Γ ,, A @ l1) N N' tyNat ->
  ac_ty G (Γ ,, tyWf l1 A N @ l1) M M' -> C_ty G (Γ ,, tyWf l1 A N @ l1) M M' ->
  ac_tm G (Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ,, wfihty l1 l2 A N M @ lmax lzero l2)
    c c' (wfstepty l1 A N M) ->
  C_tm G (Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ,, wfihty l1 l2 A N M @ lmax lzero l2)
    c c' (wfstepty l1 A N M) ->
  ac_tmnee G Γ ν ν' W -> C_nee G Γ ν ν' W ->
  C_ne G Γ (tmElimWf l1 l2 A N M c ν) (tmElimWf l3 l4 A' N' M' c' ν') M[lsingle ν].
Proof.
  intros H13 H24 DA IHA DN IHN DM IHM Dc IHc Dν IHν i G2 Γ2 k k' X X' Hc HE Hctx Hx Hx' x x' Hsx Hsx'.
  spa_triv. pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_elimWf Hi Hx) as ((_ & W1 & W2 & HA & HN & HM & HC & HI & Hc0 & Hν) & _ & _).
  destruct (inv_elimWf Hi Hx') as ((_ & W3 & W4 & HA' & HN' & HM' & HC' & HI' & Hc0' & Hν') & _ & _).
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E13)) as EA.
  pose proof (ext_wf Hi HA W1) as HΓA.
  assert (EA3 : [ G ; Γ ⊢[ i ] A' ≅ A @ l3 ])
    by (eapply eqty_lconv; [exact (eqty_sym _ _ _ _ _ _ EA) | exact (lequiv_sym _ _ _ E13)]).
  pose proof (stab_tm Hi EA3 (lequiv_sym _ _ _ E13) HΓA HN') as HN'A.
  pose proof (ac_tm_sound Hc DN HN HN'A) as EN.
  assert (HW : [ G ; Γ ⊢[ i ] tyWf l1 A N @ l1 ]) by (apply wft_wf; assumption).
  assert (EW : [ G ; Γ ⊢[ i ] tyWf l1 A N ≅ tyWf l3 A' N' @ l1 ]) by (apply eqty_wf; assumption).
  assert (EW' : [ G ; Γ ⊢[ i ] tyWf l3 A' N' ≅ tyWf l1 A N @ l3 ])
    by (eapply eqty_lconv; [apply eqty_sym, EW | exact (lequiv_sym _ _ _ E13)]).
  pose proof (ext_wf Hi HW W1) as HΓW.
  pose proof (wft_lconv _ _ _ _ _ _ (stab_ty Hi EW' (lequiv_sym _ _ _ E13) HΓW HM') E24) as HM'3.
  pose proof (ac_ty_sound Hc DM HM HM'3) as EM.
  pose proof (elimWf_step_left Hc E13 E24 HA HA' EA HN HN' EN HM HM' EM HI Hc0') as Hc0'2.
  assert (HctxA : [ G2 ⊢[ i ] Γ ,, A @ l1 ≅ Γ2 ,, A @ l1 ])
    by exact (eqctx_ext_refl Hctx (gconv_ty HE HA) (GEq_lwf HE W1)).
  assert (HctxW : [ G2 ⊢[ i ] Γ ,, tyWf l1 A N @ l1 ≅ Γ2 ,, tyWf l1 A N @ l1 ])
    by exact (eqctx_ext_refl Hctx (gconv_ty HE HW) (GEq_lwf HE W1)).
  assert (WL : lwf (gL G) (lmax lzero l2)) by (cbn; split; auto).
  assert (HctxT : [ G2 ⊢[ i ] Γ ,, A @ l1 ,, wfcsty l1 A N @ l1 ,, wfihty l1 l2 A N M @ lmax lzero l2
                    ≅ Γ2 ,, A @ l1 ,, wfcsty l1 A N @ l1 ,, wfihty l1 l2 A N M @ lmax lzero l2 ]).
  { apply (eqctx_ext_refl (eqctx_ext_refl HctxA (gconv_ty HE HC) (GEq_lwf HE W1)) (gconv_ty HE HI)).
    exact (GEq_lwf HE WL). }
  destruct (IHν i G2 Γ2 _ _ _ _ Hc HE Hctx Hν Hν' _ _ spa_refl spa_refl) as (Wν & Xν & _).
  exists M[lsingle ν]. split.
  - eapply actmne_elimWf; [exact H13 | exact H24 | | | | | exact Xν].
    + exact (IHA i G2 Γ2 l1 l3 Hc HE Hctx HA HA').
    + exact (IHN i G2 _ _ lzero Hc HE HctxA HN HN'A (eqty_refl _ _ _ _ _ (gconv_ty HE (wf_tm_ty Hi HN)))
               _ _ spa_refl spa_refl).
    + exact (IHM i G2 _ l2 l2 Hc HE HctxW HM HM'3).
    + exact (IHc i G2 _ _ l2 Hc HE HctxT Hc0 Hc0'2 (eqty_refl _ _ _ _ _ (gconv_ty HE (wf_tm_ty Hi Hc0)))
               _ _ spa_refl spa_refl).
  - exact (ne_refl (actmne_elimWf _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H13 H24 DA DN DM Dc Dν) Hc HE Hx Hx').
Qed.

Lemma C_actmnf_seq_irr {G Γ l A a b w w'} : C_tmnf G Γ w w' (tySEq l A a b).
Proof.
  red; intros i G2 Γ2 W2 k Hc HE Hctx Ht Ht' EW Hw2 x x' Hsx Hsx'. new_head Hc EW Hw2 W2.
  apply actmnf_seq_irr.
Qed.

Lemma C_actmnf_sempty_irr {G Γ l w w'} : C_tmnf G Γ w w' (tySEmpty l).
Proof.
  red; intros i G2 Γ2 W2 k Hc HE Hctx Ht Ht' EW Hw2 x x' Hsx Hsx'. new_head Hc EW Hw2 W2.
  apply actmnf_sempty_irr.
Qed.

Lemma C_actmne_elimSEmpty {G Γ l1 l2 l3 l4 M M' ν ν'} : leqv l1 l3 -> leqv l2 l4 ->
  ac_ty G Γ M M' -> C_ty G Γ M M' -> whne ν -> whne ν' ->
  C_ne G Γ (elimSEmpty l1 l2 M ν) (elimSEmpty l3 l4 M' ν') M.
Proof.
  intros H13 H24 DM IHM Hn Hn' i G2 Γ2 k k' X X' Hc HE Hctx Hx Hx' x x' Hsx Hsx'. spa_triv.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_elimSEmpty Hi Hx) as ((_ & W1 & W2 & HM & _) & Hk & _).
  destruct (inv_elimSEmpty Hi Hx') as ((_ & W3 & W4 & HM' & _) & _ & _).
  exists M. split.
  - apply actmne_elimSEmpty; [exact H13 | exact H24 | exact (IHM i G2 Γ2 l2 l4 Hc HE Hctx HM HM')
                             | exact Hn | exact Hn'].
  - apply (lvl_eq_eqty (lvl_eq_G2 HE Hk)), eqty_refl, (gconv_ty HE HM).
Qed.

(** ** The identity type (M11a) *)

Lemma C_actnf_id {G Γ l l' A A' a a' b b'} : leqv l l' ->
  ac_ty G Γ A A' -> C_ty G Γ A A' -> ac_tm G Γ a a' A -> C_tm G Γ a a' A ->
  ac_tm G Γ b b' A -> C_tm G Γ b b' A -> C_tynf G Γ (tyId l A a b) (tyId l' A' a' b').
Proof.
  intros Hl DA IHA Da IHa Db IHb i G2 Γ2 k k' Hc HE Hctx HT HT'.
  pose proof (compt_typeof_self _ Hc) as Hi.
  destruct (inv_ty_id HT) as ((_ & W & HA & Ha & Hb) & _).
  destruct (inv_ty_id HT') as ((_ & W' & HA' & Ha' & Hb') & _).
  pose proof (leqv_lequiv _ _ _ W W' Hl) as E.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E)) as EA.
  assert (F : forall x, [ G ; Γ ⊢[ i ] x : A' @ l' ] -> [ G ; Γ ⊢[ i ] x : A @ l ]).
  { intros x Hx. eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hx E) | rewrite Hi; exact EA]. }
  pose proof (eqty_refl _ _ _ _ _ (gconv_ty HE HA)) as HAr.
  apply actnf_id; [exact Hl | exact (IHA i G2 Γ2 l l' Hc HE Hctx HA HA') |
                   exact (IHa i G2 Γ2 A l Hc HE Hctx Ha (F _ Ha') HAr _ _ spa_refl spa_refl) |
                   exact (IHb i G2 Γ2 A l Hc HE Hctx Hb (F _ Hb') HAr _ _ spa_refl spa_refl)].
Qed.

Lemma C_actmnf_refl {G Γ l A a b k k' C C' c c'} :
  C_tmnf G Γ (tmRefl k C c) (tmRefl k' C' c') (tyId l A a b).
Proof.
  red; intros i G2 Γ2 W2 m Hc HE Hctx Ht Ht' EW Hw2 x x' Hsx Hsx'. spa_triv. new_head Hc EW Hw2 W2.
  apply actmnf_refl.
Qed.

Lemma C_actmne_J {G Γ l1 l2 l3 l4 A A' a a' M M' c c' u u' ν ν' W} : leqv l1 l3 -> leqv l2 l4 ->
  ac_ty G Γ A A' -> C_ty G Γ A A' -> ac_tm G Γ a a' A -> C_tm G Γ a a' A ->
  ac_ty G (Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1) M M' ->
  C_ty G (Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1) M M' ->
  ac_tm G Γ c c' M[lsingle2 a (tmRefl l1 A a)] -> C_tm G Γ c c' M[lsingle2 a (tmRefl l1 A a)] ->
  ac_tm G Γ u u' A -> C_tm G Γ u u' A ->
  ac_tmnee G Γ ν ν' W -> C_nee G Γ ν ν' W ->
  C_ne G Γ (tmJ l1 l2 A a M c u ν) (tmJ l3 l4 A' a' M' c' u' ν') M[lsingle2 u ν].
Proof.
  intros H13 H24 DA IHA Da IHa DM IHM Dc IHc Du IHu Dν IHν i G2 Γ2 k k' X X' Hc HE Hctx Hx Hx' x x' Hsx Hsx'.
  spa_triv. pose proof (compt_typeof_self _ Hc) as Hi. pose proof (compt_notV _ Hc) as Hv.
  destruct (inv_J Hi Hx) as ((_ & W1 & W2 & HA & Ha & HI & HM & Hcc & Hu & He) & Hk & HX).
  destruct (inv_J Hi Hx') as ((_ & W3 & W4 & HA' & Ha' & HI' & HM' & Hc' & Hu' & He') & Hk' & HX').
  pose proof (leqv_lequiv _ _ _ W1 W3 H13) as E13. pose proof (leqv_lequiv _ _ _ W2 W4 H24) as E24.
  pose proof (ac_ty_sound Hc DA HA (wft_lconv _ _ _ _ _ _ HA' E13)) as EA.
  assert (F : forall y, [ G ; Γ ⊢[ i ] y : A' @ l3 ] -> [ G ; Γ ⊢[ i ] y : A @ l1 ]).
  { intros y Hy. eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hy E13) | rewrite Hi; exact EA]. }
  pose proof (F _ Ha') as Ha'1. pose proof (F _ Hu') as Hu'1.
  pose proof (ac_tm_sound Hc Da Ha Ha'1) as Ea.
  (* the other motive, in this context *)
  pose proof (J_ctx_conv Hi Hc E13 HA HA' EA Ea) as Hid.
  pose proof (wf_ty_subst Hi HM' Hid) as HM'1. rewrite nf_id_ty in HM'1 by exact (wf_ty_nf HM').
  assert (HM'2 : [ G ; Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ⊢[ i ] M' @ l2 ])
    by exact (wft_lconv _ _ _ _ _ _ HM'1 E24).
  pose proof (ac_ty_sound Hc DM HM HM'2) as EM.
  (* the other base case, at this instance *)
  assert (Hr : [ G ; Γ ⊢[ i ] tmRefl l1 A a : tyId l1 A a a @ l1 ]) by (apply wf_idrefl; auto).
  pose proof (pre_idrefl_r Hi Hv E13 HA EA (eqty_wf_r Hi EA) Ea Ha'1) as Hr'.
  assert (Hrr : [ G ; Γ ⊢[ i ] tmRefl l1 A a ≅ tmRefl l3 A' a' : tyId l1 A a a @ l1 ])
    by (apply eqtm_idrefl; auto).
  pose proof (lsub_eq_J Hi Hv W1 HA Ha Ha Ha'1 Ea Hr Hr' Hrr) as Hs.
  assert (HMs : [ G ; Γ ⊢[ i ] M[lsingle2 a (tmRefl l1 A a)] ≅ M'[lsingle2 a' (tmRefl l3 A' a')] @ l2 ]).
  { eapply eqty_trans; [exact (eqty_subst Hi EM (lsub_eq_l Hs)) | exact (wf_ty_func Hi HM'2 Hs)]. }
  assert (Hc'1 : [ G ; Γ ⊢[ i ] c' : M[lsingle2 a (tmRefl l1 A a)] @ l2 ]).
  { eapply wf_conv; [exact (wf_lconv _ _ _ _ _ _ _ Hc' E24) | rewrite Hi; exact HMs]. }
  assert (HctxA : [ G2 ⊢[ i ] Γ ,, A @ l1 ≅ Γ2 ,, A @ l1 ])
    by exact (eqctx_ext_refl Hctx (gconv_ty HE HA) (GEq_lwf HE W1)).
  assert (HctxI : [ G2 ⊢[ i ] Γ ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1
                              ≅ Γ2 ,, A @ l1 ,, tyId l1 A⟨↑⟩ a⟨↑⟩ (var 0) @ l1 ])
    by exact (eqctx_ext_refl HctxA (gconv_ty HE HI) (GEq_lwf HE W1)).
  destruct (IHν i G2 Γ2 _ _ _ _ Hc HE Hctx He He' _ _ spa_refl spa_refl) as (W5 & Xν & _).
  exists M[lsingle2 u ν]. split.
  - eapply actmne_J; [exact H13 | exact H24 | | | | | | exact Xν].
    + exact (IHA i G2 Γ2 l1 l3 Hc HE Hctx HA HA').
    + exact (IHa i G2 Γ2 A l1 Hc HE Hctx Ha Ha'1 (eqty_refl _ _ _ _ _ (gconv_ty HE HA)) _ _ spa_refl spa_refl).
    + exact (IHM i G2 _ l2 l2 Hc HE HctxI HM HM'2).
    + exact (IHc i G2 Γ2 _ l2 Hc HE Hctx Hcc Hc'1 (eqty_refl _ _ _ _ _ (gconv_ty HE (wf_tm_ty Hi Hcc)))
               _ _ spa_refl spa_refl).
    + exact (IHu i G2 Γ2 A l1 Hc HE Hctx Hu Hu'1 (eqty_refl _ _ _ _ _ (gconv_ty HE HA)) _ _ spa_refl spa_refl).
  - exact (ne_refl (actmne_J _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H13 H24 DA Da DM Dc Du Dν) Hc HE Hx Hx').
Qed.

Lemma C_actmnf_code_id {G Γ l k k' s s' t t' u u'} : leqv k k' ->
  ac_tm G Γ s s' (tyU k) -> C_tm G Γ s s' (tyU k) -> C_tm G Γ t t' (tyEl k s) -> C_tm G Γ u u' (tyEl k s) ->
  C_tmnf G Γ (tmId k s t u) (tmId k' s' t' u') (tyU l).
Proof.
  intros Hk0 Ds IHs IHt IHu i G2 Γ2 W2 m Hc HE Hctx Hx Hx' EW Hw2 x x' Hsx Hsx'. spa_triv.
  pose proof (compt_typeof_self _ Hc) as Hi. new_head Hc EW Hw2 W2.
  destruct (code_id_prem Hc Hx) as (W & Hs & Ht & Hu). destruct (code_id_prem Hc Hx') as (W' & Hs' & Ht' & Hu').
  pose proof (leqv_lequiv _ _ _ W W' Hk0) as E.
  pose proof (code_U_conv Hc E Hs') as Hs1.
  pose proof (ac_tm_sound Hc Ds Hs Hs1) as Es.
  destruct (code_El_conv Hc E Es) as (F & _).
  pose proof (eqty_refl _ _ _ _ _ (gconv_ty HE (wf_tm_ty Hi Ht))) as HEr.
  apply actmnf_code_id; [exact Hk0 | | |].
  - exact (IHs i G2 Γ2 (tyU k) (lsuc k) Hc HE Hctx Hs Hs1 (eqty_refl _ _ _ _ _ (gconv_ty HE (wf_tm_ty Hi Hs)))
             _ _ spa_refl spa_refl).
  - exact (IHt i G2 Γ2 _ k Hc HE Hctx Ht (F _ Ht') HEr _ _ spa_refl spa_refl).
  - exact (IHu i G2 Γ2 _ k Hc HE Hctx Hu (F _ Hu') HEr _ _ spa_refl spa_refl).
Qed.
Lemma C_actmnf_code_seq {G Γ l k k' s s' t t' u u'} : leqv k k' ->
  ac_tm G Γ s s' (tyU k) -> C_tm G Γ s s' (tyU k) -> C_tm G Γ t t' (tyEl k s) -> C_tm G Γ u u' (tyEl k s) ->
  C_tmnf G Γ (tmSEq k s t u) (tmSEq k' s' t' u') (tyU l).
Proof.
  intros Hk0 Ds IHs IHt IHu i G2 Γ2 W2 m Hc HE Hctx Hx Hx' EW Hw2 x x' Hsx Hsx'. spa_triv.
  pose proof (compt_typeof_self _ Hc) as Hi. new_head Hc EW Hw2 W2.
  destruct (code_seq_prem Hc Hx) as (W & Hs & Ht & Hu). destruct (code_seq_prem Hc Hx') as (W' & Hs' & Ht' & Hu').
  pose proof (leqv_lequiv _ _ _ W W' Hk0) as E.
  pose proof (code_U_conv Hc E Hs') as Hs1.
  pose proof (ac_tm_sound Hc Ds Hs Hs1) as Es.
  destruct (code_El_conv Hc E Es) as (F & _).
  pose proof (eqty_refl _ _ _ _ _ (gconv_ty HE (wf_tm_ty Hi Ht))) as HEr.
  apply actmnf_code_seq; [exact Hk0 | | |].
  - exact (IHs i G2 Γ2 (tyU k) (lsuc k) Hc HE Hctx Hs Hs1 (eqty_refl _ _ _ _ _ (gconv_ty HE (wf_tm_ty Hi Hs)))
             _ _ spa_refl spa_refl).
  - exact (IHt i G2 Γ2 _ k Hc HE Hctx Ht (F _ Ht') HEr _ _ spa_refl spa_refl).
  - exact (IHu i G2 Γ2 _ k Hc HE Hctx Hu (F _ Hu') HEr _ _ spa_refl spa_refl).
Qed.

(** ** The conversion lemma *)

Theorem ac_conv_spa :
  (forall G Γ T T', ac_ty G Γ T T' -> C_ty G Γ T T') /\
  (forall G Γ W W', ac_tynf G Γ W W' -> C_tynf G Γ W W') /\
  (forall G Γ V V', ac_tyne G Γ V V' -> C_tyne G Γ V V') /\
  (forall G Δ Δ', ac_ctx G Δ Δ' -> C_ctx G Δ Δ') /\
  (forall G Γ t t' T, ac_tm G Γ t t' T -> C_tm G Γ t t' T) /\
  (forall G Γ w w' W, ac_tmnf G Γ w w' W -> C_tmnf G Γ w w' W) /\
  (forall G Γ ν ν' T, ac_tmne G Γ ν ν' T -> C_ne G Γ ν ν' T) /\
  (forall G Γ ν ν' W, ac_tmnee G Γ ν ν' W -> C_nee G Γ ν ν' W) /\
  (forall G Γ d d' Δ, ac_sub G Γ d d' Δ -> C_sub G Γ d d' Δ).
Proof.
  apply ac_mut; intros;
    first
    [ solve [eapply C_act_red; eassumption] | solve [eapply C_actnf_nat] | solve [eapply C_actnf_U; eassumption]
    | solve [eapply C_actnf_pi; eassumption] | solve [eapply C_actnf_ne; eassumption]
    | solve [eapply C_actnf_CTyp; eassumption] | solve [eapply C_actnf_CTrm; eassumption]
    | solve [eapply C_actnf_upi; eassumption] | solve [eapply C_actnf_cpi; eassumption]
    | solve [eapply C_actnf_tpi; eassumption]
    | solve [eapply C_actne_gvar; eassumption] | solve [eapply C_actne_El; eassumption]
    | solve [eapply C_acc_nil] | solve [eapply C_acc_var] | solve [eapply C_acc_ext; eassumption]
    | solve [eapply C_actm_red; eassumption]
    | solve [eapply C_actmnf_code_nat] | solve [eapply C_actmnf_code_U; eassumption]
    | solve [eapply C_actmnf_code_pi; eassumption] | solve [eapply C_actmnf_zero]
    | solve [eapply C_actmnf_succ; eassumption] | solve [eapply C_actmnf_ne; eassumption]
    | solve [eapply C_actmnf_eta; eassumption] | solve [eapply C_actmnf_ueta; eassumption]
    | solve [eapply C_actmnf_ceta; eassumption] | solve [eapply C_actmnf_teta; eassumption]
    | solve [eapply C_actmnf_boxT; eassumption] | solve [eapply C_actmnf_boxt; eassumption]
    | solve [eapply C_actmne_var; eassumption] | solve [eapply C_actmne_gvar; eassumption]
    | solve [eapply C_actmne_natrec; eassumption] | solve [eapply C_actmne_app; eassumption]
    | solve [eapply C_actmne_letboxT; eassumption] | solve [eapply C_actmne_letboxt; eassumption]
    | solve [eapply C_actmne_elimT; eassumption] | solve [eapply C_actmne_elimT_gvar; eassumption]
    | solve [eapply C_actmne_elimt; eassumption] | solve [eapply C_actmne_elimt_glob; eassumption]
    | solve [eapply C_actmne_uapp; eassumption] | solve [eapply C_actmne_capp; eassumption]
    | solve [eapply C_actmne_tapp; eassumption] | solve [eapply C_actmnee_red; eassumption]
    | solve [eapply C_acs_pt; eassumption]
    | solve [eapply C_actnf_sig; eassumption] | solve [eapply C_actmnf_code_sig; eassumption]
    | solve [eapply C_actmnf_sig_eta; eassumption] | solve [eapply C_actmne_fst; eassumption]
    | solve [eapply C_actmne_snd; eassumption]
    | solve [eapply C_actnf_unit; eassumption] | solve [eapply C_actmnf_code_unit; eassumption]
    | solve [eapply C_actmnf_unit_eta]
    | solve [eapply C_actnf_seq; eassumption] | solve [eapply C_actnf_sempty; eassumption]
    | solve [eapply C_actmnf_seq_irr] | solve [eapply C_actmnf_sempty_irr] | solve [eapply C_actmnf_empty_irr]
    | solve [eapply C_actmne_elimSEmpty; eassumption]
    | solve [eapply C_actnf_id; eassumption] | solve [eapply C_actmnf_refl]
    | solve [eapply C_actmne_J; eassumption] | solve [eapply C_actmnf_code_id; eassumption]
    | solve [eapply C_actmnf_code_seq; eassumption] | solve [eapply C_actmnf_code_sempty; eassumption]
    | solve [eapply C_actnf_empty; eassumption] | solve [eapply C_actmne_elimEmpty; eassumption]
    | solve [eapply C_actnf_sum; eassumption] | solve [eapply C_actmnf_inl; eassumption]
    | solve [eapply C_actmnf_inr; eassumption] | solve [eapply C_actmne_case; eassumption]
    | solve [eapply C_actmnf_code_empty; eassumption] | solve [eapply C_actmnf_code_sum; eassumption]
    | solve [eapply C_actmnf_code_vec; eassumption] | solve [eapply C_actmnf_code_fin; eassumption]
    | solve [eapply C_actnf_W; eassumption] | solve [eapply C_actmnf_sup; eassumption]
    | solve [eapply C_actmne_elimW; eassumption]
    | solve [eapply C_actmnf_code_W; eassumption]
    | solve [eapply C_actnf_wf; eassumption] | solve [eapply C_actmnf_supf; eassumption]
    | solve [eapply C_actmne_elimWf; eassumption]
    | solve [eapply C_actne_vec; eassumption] | solve [eapply C_actne_fin; eassumption] ].
Qed.

(** The statement without annotation changes. *)
Definition C0_tm G Γ t t' T : Prop := forall i G2 Γ2 T2 k, compt i -> GEq G G2 -> [ G2 ⊢[ i ] Γ ≅ Γ2 ] ->
  [ G ; Γ ⊢[ i ] t : T @ k ] -> [ G ; Γ ⊢[ i ] t' : T @ k ] -> [ G2 ; Γ ⊢[ i ] T2 ≅ T @ k ] ->
  ac_tm G2 Γ2 t t' T2.
Definition C0_tmnf G Γ w w' W : Prop := forall i G2 Γ2 W2 k, compt i -> GEq G G2 -> [ G2 ⊢[ i ] Γ ≅ Γ2 ] ->
  [ G ; Γ ⊢[ i ] w : W @ k ] -> [ G ; Γ ⊢[ i ] w' : W @ k ] -> [ G2 ; Γ ⊢[ i ] W2 ≅ W @ k ] -> whnf_ty W2 ->
  ac_tmnf G2 Γ2 w w' W2.
Definition C0_ne G Γ ν ν' T : Prop := forall i G2 Γ2 k k' A A', compt i -> GEq G G2 -> [ G2 ⊢[ i ] Γ ≅ Γ2 ] ->
  [ G ; Γ ⊢[ i ] ν : A @ k ] -> [ G ; Γ ⊢[ i ] ν' : A' @ k' ] ->
  exists T2, ac_tmne G2 Γ2 ν ν' T2 /\ [ G2 ; Γ ⊢[ i ] T2 ≅ T @ k ].
Definition C0_nee G Γ ν ν' W : Prop := forall i G2 Γ2 k k' A A', compt i -> GEq G G2 -> [ G2 ⊢[ i ] Γ ≅ Γ2 ] ->
  [ G ; Γ ⊢[ i ] ν : A @ k ] -> [ G ; Γ ⊢[ i ] ν' : A' @ k' ] ->
  exists W2, ac_tmnee G2 Γ2 ν ν' W2 /\ [ G2 ; Γ ⊢[ i ] W2 ≅ W @ k ].

Theorem ac_conv_all :
  (forall G Γ T T', ac_ty G Γ T T' -> C_ty G Γ T T') /\
  (forall G Γ W W', ac_tynf G Γ W W' -> C_tynf G Γ W W') /\
  (forall G Γ V V', ac_tyne G Γ V V' -> C_tyne G Γ V V') /\
  (forall G Δ Δ', ac_ctx G Δ Δ' -> C_ctx G Δ Δ') /\
  (forall G Γ t t' T, ac_tm G Γ t t' T -> C0_tm G Γ t t' T) /\
  (forall G Γ w w' W, ac_tmnf G Γ w w' W -> C0_tmnf G Γ w w' W) /\
  (forall G Γ ν ν' T, ac_tmne G Γ ν ν' T -> C0_ne G Γ ν ν' T) /\
  (forall G Γ ν ν' W, ac_tmnee G Γ ν ν' W -> C0_nee G Γ ν ν' W) /\
  (forall G Γ d d' Δ, ac_sub G Γ d d' Δ -> C_sub G Γ d d' Δ).
Proof.
  destruct ac_conv_spa as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
  refine (conj H1 (conj H2 (conj H3 (conj H4 (conj _ (conj _ (conj _ (conj _ H9)))))))); intros; red; intros.
  all: first [eapply H5 | eapply H6 | eapply H7 | eapply H8]; first [eassumption | exact spa_refl].
Qed.
