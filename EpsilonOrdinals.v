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
| succLT : forall r f, r < (f $ r)
| succTransLT : forall q r f : ord, q < r -> q < (f $ r)
| limitLT : forall g f r : ord, f < g -> forall n, (chain (fun o => f $ o) r n) < (g $ r)
where "a < b" := (LT a b).

Notation "a <= b" := (a = b \/ LT a b).

Arguments succLT {r} {f}.
Arguments succTransLT {q} {r} {f} p.
Arguments limitLT {g} {f} {r} p {n}.

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


Section ind.

  Lemma Z_le : forall r, 0 <= r.
    induction r.
    left; reflexivity.
    right; destruct IHr1.
    rewrite <- H; apply succLT.
    apply succTransLT; assumption.
  Qed.
  
  Lemma rising : forall f g, f < (f $ g).
  Proof.
    induction f; intro g.
    assert (0 <= (0 $ g)) by apply Z_le.
    destruct H;
      [ contradict H; discriminate
      | assumption
      ].
    assert(H : chain (\$ f) 
  Qed.

  Lemma no_smaller_step : forall r m, m < (0 $ r) <-> m <= r.
  Proof.
    intros.
    split; intro H.

    inversion_clear H.
    left; auto.
    right; auto.

    inversion H0.

    destruct H.
    rewrite H; apply succLT.
    
    apply succTransLT; assumption.
  Qed.

  Require Import Coq.Setoids.Setoid. 
  

  Lemma chain_induction : forall f start (P : ord -> Prop),
                            (forall r, r <= start -> P r)
                            -> (forall x, (forall r, r < x -> P r) -> P x)
                            -> forall n, (forall r, r <= (chain (\$ f) start n) -> P r).
  Proof.
    intros f start P H_start H_next.
    induction f; induction n; simpl; try assumption.
    intro.

    assert (H_next_ : forall x, (forall r, r < x -> P r) -> (forall r, r <= x -> P r)) by
        (clear n IHn r; intros x r_lt_x r r_le_x; destruct r_le_x; [rewrite H; apply H_next | apply r_lt_x]; assumption).

    clear H_next.
    apply H_next_.
    clear r.
    intros r r_lt_0Chain.
    apply IHn.
    
    clear H0; apply H1; clear H1 r.
    intros r r_lt_x.
    apply IHn.
    rewrite <- no_smaller_step.
    assumption.

    
  Qed.
  
Let Ind x := forall P : ord -> Prop, (forall q, (forall r, r < q -> P r) -> P q) -> P x.
  
Theorem transfinite_induction :
  forall P,
    (forall q, (forall r, r < q -> P r) -> P q) ->
    forall q, P q.
Proof.
  assert (forall q,  Ind q).
  unfold Ind; clear.  
  intros.
  apply H.
  induction q; intros r H_lt; inversion H_lt.
  rewrite H2 in H_lt; clear r H0 H2 f H3.
  apply H.
  assumption.
  apply IHq1; assumption.
  rewrite H0 in H1;  clear g H3 r0 H0.
  rewrite <- H1 in H_lt; clear r H1.
  induction n; simpl; simpl in H_lt.
  clear f H2; apply H; apply IHq1.
  
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
  