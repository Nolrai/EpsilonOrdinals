Module EpsilonOrdinals.

Inductive ord :=
| Zero : ord
| Stroke : forall r f : ord, ord
.

  
Notation "0" := (Zero).
Notation "f $ r" := (Stroke r f) (at level 80).

Inductive LT : forall (r q : ord), Prop :=
| succLT  : forall r q f  , r <= q                   -> r  < (f $ q)
| monoLT  : forall r q f  , r <  q                   -> (f $ r) < (f $ q) 
| limitLT : forall r q f g, f <  g  ->  r < (g $ q)  -> (f $ r) < (g $ q)

where "r < q"  := (LT r q) 
and   "r <= q" := ((r = q) \/ (r < q)).

Arguments succLT  {r} {q} {f} p.
Arguments monoLT  {r} {q} {f} p.
Arguments limitLT {r} {q} {f} {g} f_lt_g r_lt_gq.

Lemma succ_neq : forall r f, r <> (f $ r).
Proof.
  intros r f; induction r; [discriminate | intro p]; inversion p.
  apply IHr1.
  rewrite H0.
  exact p.
Qed.

Require Import Omega.
Require Import Coq.Arith.Lt Coq.Arith.Plus Coq.Arith.Le.

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
destruct m; simpl; apply le_n_S; [app0ly le_refl | apply IHn].
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

Lemma le_0_ord : forall r, 0 <= r.
Proof.
intros; induction r; [left | right ; apply succLT]; auto.
Qed.

Lemma lt_0_ord : forall r : ord, (0 <> r) -> 0 < r.
Proof.
intros.
assert (le_r : 0 <= r) by apply le_0_ord; destruct le_r; [contradict H | idtac]; auto.
Qed.

Next Obligation.
Proof.
unfold CompSpec; apply CompLt; apply lt_0_ord; contradict H; split; auto.
Qed.

Next Obligation.
Proof.
apply CompGt.
apply lt_0_ord.
contradict H0; split; auto.
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
induction p; constructor; try rewrite H; try apply succMonoLT; auto;
constructor 2; auto.
Qed.

Next Obligation.
Proof.
clear.
apply plus_lt_le_compat. 
apply hight_lt_r.
constructor 1; auto.
Qed.

Next Obligation.
Proof.
assert (fq < fp).
set (obl := compOrd_func_obligation_4 (fq $ rq) (fp $ rp) compOrd _ _ _ _ eq_refl eq_refl)
 in *.
set (C := compOrd fq fp obl) in *.
destruct C; simpl in *; induction c; try discriminate; auto.

set (obl := compOrd_func_obligation_7 _ _ compOrd rq fq rp fp eq_refl eq_refl Heq_anonymous).
set (C := compOrd rq (fp $ rp) obl).
induction C.
clear obl Heq_anonymous.
simpl.
induction p; simpl; constructor.
rewrite <- H0; apply succLT; left; auto.
apply limitLT; assumption.
apply succLT; right; assumption.
Qed.

Next Obligation.
Proof.
apply plus_lt_compat_l.
apply hight_lt_r.
Qed.

Next Obligation.
Proof.
set (obl := compOrd_func_obligation_4 _ _ compOrd rq fq rp fp eq_refl eq_refl) in *.
set (C := compOrd fq fp obl) in *.
set (obl2 := compOrd_func_obligation_9 _ _ compOrd rq fq rp fp eq_refl eq_refl Heq_anonymous).
set (C2 := compOrd (fq $ rq) rp obl2) in *.
induction C2. clear obl2.
induction C; simpl in *. clear compOrd obl.
induction p0; inversion_clear Heq_anonymous.
induction p; simpl; constructor.
rewrite H0; apply succLT; auto.
apply succLT; auto.
apply limitLT; auto.
Qed.

Next Obligation.
Proof.
split; intros; clear; intro H; destruct H as [H _]; discriminate H.
Qed.

Functional Scheme compOrdScheme := Induction for compOrd Sort Prop.

Theorem LinearOrder : forall r q, r < q \/ r = q \/ q < r. 
Proof.
intros.
induction (compOrd r q).
induction p; intuition.
Qed.

End Linear.

Section ind.

CoInductive Stream A := 
| cons : A -> Stream A -> Stream A
.

Arguments cons {A} a s.

CoInductive Decending : Stream ord -> Prop :=
| decCons : forall a b s, b < a -> Decending (cons a s) -> Decending (cons b (cons a s))
.  

Lemma no_infinite_decent : forall s, ~ Decending s.
assert (forall p q s, q < p -> ~ Decending (cons p s)).
induction p; intros; inversion H.
clear r q0 f H1 H0 H3.
destruct H2.
rewrite H0 in *.
clear H.

Qed.

Inductive Proper : ord -> Prop :=
 MkProper : forall q, (forall r, r < q -> Proper r) -> Proper q
.

Lemma all_proper : forall q, Proper q.
Proof.
induction q.
apply MkProper; intros.
inversion H.

apply MkProper; intros; inversion H.
clear r0 H1 q f H0 H3.
destruct H2.
rewrite H0 in *; clear r H0; assumption.
inversion_clear IHq1; apply H1; assumption.
Qed.
  
Theorem transfinite_induction :
  forall (P : ord -> Prop),
    (forall q, (forall r, r < q -> P r) -> P q) ->
    forall q, P q.
Proof.

Qed.
  
 
  
Theorem LT_antirefl : forall p q, p < q -> p <> q.
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
  