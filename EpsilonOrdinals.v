Module EpsilonOrdinals.

Inductive ord :=
| Zero : ord
| Stroke : forall r f : ord, ord
.

  
Notation "0" := (Zero).
Notation "f $ r" := (Stroke r f) (at level 80).

Section chain.
  Variable A : Type.
  Variable f : A -> A.
  Variable start : A.
  
Fixpoint chain (n : nat) : A :=
  match n with
    | O => start
    | S n' => f (chain n')
  end
.
End chain.

Arguments chain {A} f start n.

Inductive LT : forall (n m : ord), Prop :=
| succLE : forall r f, r < (f $ r)
| succTransLE : forall q r f : ord, q < r -> q < (f $ r)
| limitLE : forall g f r : ord, f < g -> forall n, (chain (fun o => f $ o) r n) < (g $ r)
where "a < b" := (LT a b).

Arguments succLE {r} {f}.
Arguments succTransLE {q} {r} {f} p.
Arguments limitLE {g} {f} {r} p {n}.

Notation "\$ f" := (fun o => f $ o) (at level 50).

Theorem chain_0 : forall f n r, chain (\$ f) r n = 0 -> r = 0 /\ n = O.
Proof.
  induction n; simpl; intros; [split ; auto | idtac].
  contradict H; discriminate.
Qed.

Lemma succ_neq : forall r f, r <> (f $ r).
Proof.
  intros r f; induction r; [discriminate | intro p]; inversion p.
  apply IHr1.
  rewrite H0.
  exact p.
Qed.

Fixpoint r_hight o : nat :=
  match o with
    | 0 => O
    | (_f $ r) => S (r_hight r)
  end
.

Lemma nat_plus_S n m : n + S m = S (n + m).
Proof.
  induction n.
  simpl.
  reflexivity.
  simpl.
  rewrite IHn.
  auto.
Qed.


Lemma nat_plus_comm n m : n + m = m + n.
Proof.
  induction n.
  induction m.
  reflexivity.  
  simpl; rewrite <- IHm; simpl; reflexivity.
  rewrite nat_plus_S; simpl; rewrite IHn; reflexivity.
Qed.


Section chain_f_inj.

Let nat_nk_ind :
  forall (P : nat -> nat -> Prop),
    (forall k n, P n (k + n) -> k = O) ->
    forall m n, (P n m -> P m n -> n = m).
Proof.
  intros.
  assert (exists k, n = k + m \/ m = k + n).
  clear.
  induction m.
  exists n; left; induction n; simpl; try rewrite <- IHn; reflexivity.
  destruct IHm as [ k [ IH | IH ] ]; rewrite IH; clear IH; destruct k; simpl;
  try (exists 1; right; simpl; reflexivity).
  exists k; left; rewrite nat_plus_S; reflexivity.
  exists (2 + k); right; simpl; reflexivity.

  destruct H2 as [k H2]; destruct H2;
  [ (rewrite H2 in H1; apply H in H1; rewrite H1 in H2)
  | (rewrite H2 in H0; apply H in H0; rewrite H0 in H2)
  ] ; rewrite H2; simpl; auto.
Qed.
  
  Variable f r : ord.
  Let F n := chain (\$ f) r n.
  Let P n m := F n = F m.

  Require Import Coq.Arith.Lt.

Theorem chain_f_inj : forall n m, P n m -> n = m.
Proof.
 intros.
 apply (nat_nk_ind P); auto; unfold P; unfold F.
 clear H F P n.
 destruct k; simpl; intros; auto.
 assert ((r_hight (chain (\$ f) r n) < r_hight (f $ chain (\$ f) r (k + n)))%nat).
 clear; induction k; simpl.
 unfold lt; eauto.
 apply lt_trans with (m := r_hight (f $ chain (\$ f) r (k + n))).
 apply IHk.
 eauto.
 rewrite H in H0.
 contradict H0.
 apply lt_irrefl.
 symmetry.
 apply H.
Qed.

End chain_f_inj. 

Theorem transfinite_induction :
  forall P,
    (P 0) ->
    (forall q, (forall r, r < q -> P r) -> P q) ->
    forall q, P q.
Proof.
  intros.
  induction q.
  assumption.
     
  Qed.
  
 
  
Theorem LE_antirefl : forall p q, p < q -> p <> q.
Proof.
  Check LT_ind.
  intros p q H.
  induction p.
  destruct q; inversion H; try discriminate.
  absurd ((g $ r) = 0).
  discriminate.
  rewrite H1.
  exact H0.
  clear g H3.
  rewrite H1 in H0.
  clear r H1.
  rewrite H0.
  discriminate.
Qed.

Theorem LE_antisymm : forall p q, p < q -> ~ (q 
  