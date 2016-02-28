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

Require Import Omega.
Require Import Coq.Arith.Lt Coq.Arith.Plus Coq.Arith.Le.

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
  exists k; left; omega.
  exists (2 + k); right; omega.

  destruct H2 as [k H2]; destruct H2;
  [ (rewrite H2 in H1; apply H in H1; rewrite H1 in H2)
  | (rewrite H2 in H0; apply H in H0; rewrite H0 in H2)
  ] ; rewrite H2; simpl; auto.
Qed.
  
  Variable f r : ord.
  Let F n := chain (\$ f) r n.
  Let P n m := F n = F m.

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

Section Linear.

Definition nudge direction raw :=
  match raw with
  | Eq => direction
  | _  => raw
  end
.

Require Import Coq.Program.Wf.

Fixpoint hight o : nat :=
  match o with
  | 0 => 0%nat
  | f $ r => S (max (hight f) (hight r))
  end
.

Require Import Arith.Le Arith.Plus Arith.Lt.

Lemma max_le_l : (forall n m, n <= max n m )%nat.
Proof.
induction n.
apply le_0_n.
destruct m; simpl; apply le_n_S; [apply le_refl | apply IHn].
Qed.

Lemma max_comm : (forall n m, max m n = max n m)%nat.
Proof.
induction n; destruct m; simpl; auto.
Qed.

Lemma max_le_r : forall n m, (m <= max n m)%nat.
Proof.
intros n m.
rewrite max_comm.
apply max_le_l.
Qed.

Lemma hight_lt_r : forall f r, (hight r < hight (f $ r))%nat.
Proof.
intros; simpl.
assert (forall n m : nat, (n < S (max m n) )%nat).
clear; intros.
apply le_lt_n_Sm.
apply max_le_r.
apply H.
Qed.

Lemma hight_comm : forall p q, hight (p $ q) = hight (q $ p).
simpl.
intros.
rewrite max_comm.
reflexivity.
Qed.

Lemma hight_lt_f : forall f r, (hight f < hight (f $ r))%nat.
Proof.
intros.
rewrite hight_comm.
apply hight_lt_r.
Qed.

Program Fixpoint compOrd (q p : ord) {measure (hight q + hight p)} 
 : {c : comparison | CompSpec eq LT q p c} :=
    match q, p with
    | 0, 0 => Eq
    | 0, _ => Lt
    | _, 0 => Gt
    | fq $ rq, fp $ rp =>
      match compOrd fq fp with
      | Eq => compOrd rq rp
      | Lt => nudge Gt (compOrd rq p)
      | Gt => nudge Lt (compOrd q rp)
      end
    end
.

Lemma ord_lt_0_o : forall o, o <> 0 -> 0 < o.
Proof.
intros; induction o.
destruct H; reflexivity.
destruct o1.
apply succLT.
apply succTransLT.
apply IHo1.
discriminate.
Qed.

Next Obligation.
Proof.
unfold CompSpec; apply CompLt.
apply ord_lt_0_o.
destruct p.
contradict H.
split; auto.
discriminate.
Qed.

Next Obligation.
Proof.
apply CompGt.
apply ord_lt_0_o.
contradict H0.
split; auto.
Qed.

Next Obligation.
Proof.
clear.
apply plus_lt_compat; apply hight_lt_f.
Qed.

Next Obligation.
Proof.
clear.
apply plus_lt_compat; apply hight_lt_r.
Qed.

Next Obligation.
Proof.
assert (fq = fp).
set (C :=
    (compOrd fq fp
      (compOrd_func_obligation_4 (fq $ rq) (fp $ rp) compOrd
        _ _ _ _ eq_refl eq_refl
      )
    )
  ).
fold C in Heq_anonymous.
induction C.
destruct p; try assumption; simpl in Heq_anonymous; discriminate Heq_anonymous.
set (obligation_5 := 
  compOrd_func_obligation_5 
    (fq $ rq) 
    (fp $ rp) 
    compOrd _ _ _ _ eq_refl eq_refl Heq_anonymous
).
set (C := compOrd rq rp obligation_5).
rewrite <- H.
induction C.
clear obligation_5 Heq_anonymous.
rewrite <- H in compOrd.
clear fp H.
induction p; constructor; try (rewrite H; reflexivity).
apply succMonoLT.
Qed.

Next Obligation.
Proof.
clear.
apply plus_le_lt_compat; [apply le_refl | apply hight_lt_r].
Qed.

Next Obligation.
Proof.
split; intros; clear; intro H; destruct H as [H _]; discriminate H.
Qed.

Next Obligation.
Proof.
apply measure_wf.
induction a; apply Acc_intro; intros.
contradict H.
apply lt_n_0.
inversion_clear H.
apply IHa.
apply (Acc_inv IHa).
unfold lt.
exact H0.
Defined.
Check CompSpec.

Functional Scheme compOrdScheme := Induction for compOrd Sort Prop.

Lemma compOrd_spec : forall p q, CompSpec eq LT p q (compOrd p q).
intros; functional induction (compOrd p q) using compOrdScheme; intros.
unfold compOrd_func.

Theorem LinearOrder : forall r q, r < q \/ r = q \/ q < r. 
Proof.
Qed.

End Linear.

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
  