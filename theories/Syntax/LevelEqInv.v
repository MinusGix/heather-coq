(** * Inversion of [≡ₗ] at a constructor

    Purely syntactic: split off [LevelInv] (the relation's level
    invariance), which waits for the logical relation's metatheory. *)
From DeLaM.Syntax Require Export LevelEq.

Lemma ty_leq_pi_inv {l3 l4 A2 B2 W} : ty_leq (tyPi l3 l4 A2 B2) W ->
  exists k3 k4 A3 B3, W = tyPi k3 k4 A3 B3 /\ leqv l3 k3 /\ leqv l4 k4 /\ ty_leq A2 A3 /\ ty_leq B2 B3.
Proof. intros H; destruct W; try exact (False_ind _ H); revert H; cbn; intros; do 4 eexists; intuition eauto. Qed.
Lemma ty_leq_sig_inv {l3 l4 A2 B2 W} : ty_leq (tySig l3 l4 A2 B2) W ->
  exists k3 k4 A3 B3, W = tySig k3 k4 A3 B3 /\ leqv l3 k3 /\ leqv l4 k4 /\ ty_leq A2 A3 /\ ty_leq B2 B3.
Proof. intros H; destruct W; try exact (False_ind _ H); revert H; cbn; intros; do 4 eexists; intuition eauto. Qed.
Lemma ty_leq_U_inv {l2 W} : ty_leq (tyU l2) W -> exists l3, W = tyU l3 /\ leqv l2 l3.
Proof. intros H; destruct W; try exact (False_ind _ H); revert H; cbn; eauto. Qed.
Lemma ty_leq_unit_inv {l2 W} : ty_leq (tyUnit l2) W -> exists l3, W = tyUnit l3 /\ leqv l2 l3.
Proof. intros H; destruct W; try exact (False_ind _ H); revert H; cbn; eauto. Qed.
Lemma ty_leq_seq_inv {l2 A2 a2 b2 W} : ty_leq (tySEq l2 A2 a2 b2) W ->
  exists l3 A3 a3 b3, W = tySEq l3 A3 a3 b3 /\ leqv l2 l3 /\ ty_leq A2 A3 /\ tm_leq a2 a3 /\ tm_leq b2 b3.
Proof. intros H; destruct W; try exact (False_ind _ H); revert H; cbn; intros; do 4 eexists; intuition eauto. Qed.
Lemma ty_leq_id_inv {l2 A2 a2 b2 W} : ty_leq (tyId l2 A2 a2 b2) W ->
  exists l3 A3 a3 b3, W = tyId l3 A3 a3 b3 /\ leqv l2 l3 /\ ty_leq A2 A3 /\ tm_leq a2 a3 /\ tm_leq b2 b3.
Proof. intros H; destruct W; try exact (False_ind _ H); revert H; cbn; intros; do 4 eexists; intuition eauto. Qed.
Lemma tm_leq_refl_inv {l C c w} : tm_leq (tmRefl l C c) w ->
  exists l' C' c', w = tmRefl l' C' c' /\ leqv l l' /\ ty_leq C C' /\ tm_leq c c'.
Proof. intros H; destruct w; try exact (False_ind _ H); revert H; cbn; intros; do 3 eexists; intuition eauto. Qed.
Lemma ty_leq_sempty_inv {l2 W} : ty_leq (tySEmpty l2) W -> exists l3, W = tySEmpty l3 /\ leqv l2 l3.
Proof. intros H; destruct W; try exact (False_ind _ H); revert H; cbn; eauto. Qed.
Lemma ty_leq_empty_inv {l2 W} : ty_leq (tyEmpty l2) W -> exists l3, W = tyEmpty l3 /\ leqv l2 l3.
Proof. intros H; destruct W; try exact (False_ind _ H); revert H; cbn; eauto. Qed.
Lemma ty_leq_sum_inv {l3 l4 A2 B2 W} : ty_leq (tySum l3 l4 A2 B2) W ->
  exists k3 k4 A3 B3, W = tySum k3 k4 A3 B3 /\ leqv l3 k3 /\ leqv l4 k4 /\ ty_leq A2 A3 /\ ty_leq B2 B3.
Proof. intros H; destruct W; try exact (False_ind _ H); revert H; cbn; intros; do 4 eexists; intuition eauto. Qed.
Lemma tm_leq_inl_inv {l l' C D c w} : tm_leq (tmInl l l' C D c) w ->
  exists k k' C' D' c', w = tmInl k k' C' D' c' /\ leqv l k /\ leqv l' k' /\ ty_leq C C' /\ ty_leq D D' /\ tm_leq c c'.
Proof. intros H; destruct w; try exact (False_ind _ H); revert H; cbn; intros; do 5 eexists; intuition eauto. Qed.
Lemma tm_leq_inr_inv {l l' C D c w} : tm_leq (tmInr l l' C D c) w ->
  exists k k' C' D' c', w = tmInr k k' C' D' c' /\ leqv l k /\ leqv l' k' /\ ty_leq C C' /\ ty_leq D D' /\ tm_leq c c'.
Proof. intros H; destruct w; try exact (False_ind _ H); revert H; cbn; intros; do 5 eexists; intuition eauto. Qed.
Lemma ty_leq_nat_inv {W} : ty_leq tyNat W -> W = tyNat.
Proof. intros H; destruct W; try exact (False_ind _ H); revert H; cbn; auto. Qed.
Lemma ty_leq_cpi_inv {l2 U2 W} : ty_leq (tyCPi l2 U2) W ->
  exists k U3, W = tyCPi k U3 /\ leqv l2 k /\ ty_leq U2 U3.
Proof. intros H; destruct W; try exact (False_ind _ H); revert H; cbn; intros; do 2 eexists; intuition eauto. Qed.
Lemma ty_leq_tpi_inv {Δ2 l3 l4 U2 W} : ty_leq (tyTPi Δ2 l3 l4 U2) W ->
  exists Δ3 k3 k4 U3, W = tyTPi Δ3 k3 k4 U3 /\ ctx_leq Δ2 Δ3 /\ leqv l3 k3 /\ leqv l4 k4 /\ ty_leq U2 U3.
Proof. intros H; destruct W; try exact (False_ind _ H); revert H; cbn; intros; do 4 eexists; intuition eauto. Qed.

Lemma ty_leq_W_inv {l3 l4 A2 B2 W} : ty_leq (tyW l3 l4 A2 B2) W ->
  exists k3 k4 A3 B3, W = tyW k3 k4 A3 B3 /\ leqv l3 k3 /\ leqv l4 k4 /\ ty_leq A2 A3 /\ ty_leq B2 B3.
Proof. intros H; destruct W; try exact (False_ind _ H); revert H; cbn; intros; do 4 eexists; intuition eauto. Qed.
Lemma tm_leq_sup_inv {l l' C D a f w} : tm_leq (tmSup l l' C D a f) w ->
  exists k k' C' D' a' f', w = tmSup k k' C' D' a' f' /\ leqv l k /\ leqv l' k' /\ ty_leq C C' /\
    ty_leq D D' /\ tm_leq a a' /\ tm_leq f f'.
Proof. intros H; destruct w; try exact (False_ind _ H); revert H; cbn; intros; do 6 eexists; intuition eauto. Qed.

Lemma ty_leq_wf_inv {l A N W} : ty_leq (tyWf l A N) W ->
  exists l' A' N', W = tyWf l' A' N' /\ leqv l l' /\ ty_leq A A' /\ tm_leq N N'.
Proof. intros H; destruct W; try exact (False_ind _ H); revert H; cbn; intros; do 3 eexists; intuition eauto. Qed.
Lemma ty_leq_sq_inv {l2 A2 W} : ty_leq (tySq l2 A2) W ->
  exists l3 A3, W = tySq l3 A3 /\ leqv l2 l3 /\ ty_leq A2 A3.
Proof. intros H; destruct W; try exact (False_ind _ H); revert H; cbn; intros; do 2 eexists; intuition eauto. Qed.
Lemma tm_leq_supf_inv {l A N a cs w} : tm_leq (tmSupf l A N a cs) w ->
  exists l' A' N' a' cs', w = tmSupf l' A' N' a' cs' /\ leqv l l' /\ ty_leq A A' /\ tm_leq N N' /\
    tm_leq a a' /\ tm_leq cs cs'.
Proof. intros H; destruct w; try exact (False_ind _ H); revert H; cbn; intros; do 5 eexists; intuition eauto. Qed.
Lemma ty_leq_iwf_inv {l li X A N Ot C m W} : ty_leq (tyIWf l li X A N Ot C m) W ->
  exists l' li' X' A' N' Ot' C' m', W = tyIWf l' li' X' A' N' Ot' C' m' /\ leqv l l' /\ leqv li li' /\
    ty_leq X X' /\ ty_leq A A' /\ tm_leq N N' /\ tm_leq Ot Ot' /\ tm_leq C C' /\ tm_leq m m'.
Proof. intros H; destruct W; try exact (False_ind _ H); revert H; cbn; intros; do 8 eexists; intuition eauto. Qed.
Lemma tm_leq_supi_inv {l li X A N Ot C a cs w} : tm_leq (tmSupi l li X A N Ot C a cs) w ->
  exists l' li' X' A' N' Ot' C' a' cs', w = tmSupi l' li' X' A' N' Ot' C' a' cs' /\ leqv l l' /\ leqv li li' /\
    ty_leq X X' /\ ty_leq A A' /\ tm_leq N N' /\ tm_leq Ot Ot' /\ tm_leq C C' /\ tm_leq a a' /\ tm_leq cs cs'.
Proof. intros H; destruct w; try exact (False_ind _ H); revert H; cbn; intros; do 9 eexists; intuition eauto. Qed.

Lemma ty_leq_M_inv {l l' li X A B C m W} : ty_leq (tyM l l' li X A B C m) W ->
  exists k k' ki X' A' B' C' m', W = tyM k k' ki X' A' B' C' m' /\ leqv l k /\ leqv l' k' /\ leqv li ki /\
    ty_leq X X' /\ ty_leq A A' /\ ty_leq B B' /\ tm_leq C C' /\ tm_leq m m'.
Proof. intros H; destruct W; try exact (False_ind _ H); revert H; cbn; intros; do 8 eexists; intuition eauto. Qed.
