inductive ord : Type :=
| Zero : ord
| Stroke : ord -> ord -> ord

open ord

infix `∥`:50 := Stroke

definition ord.has_zero [instance] : has_zero ord :=
  {| has_zero, zero := Zero |}
  
attribute Stroke [coercion] --this seems to act flaky?

definition ord.has_one [instance] : has_one ord :=
  has_one.mk (0 ∥ 0)

inductive ord.le : ord -> ord -> Prop :=
| refl  {} : ∀ r        : ord,                                              ord.le r r
| app   {} : ∀ r q f    : ord,           ord.le q r                     ->  ord.le q (f r)
| mono  {} : ∀ r q g f  : ord,           ord.le q r     -> ord.le g f   ->  ord.le (g q) (f r)
| limit {} : ∀ r q g f  : ord,  q ≠ f -> ord.le q (f r) -> ord.le g f   ->  ord.le (g q) (f r)

local infix ≤ := ord.le

definition ord.has_le [instance] : has_le ord :=
  has_le.mk ord.le

open ord.le

lemma zero_le : ∀ r : ord, 0 ≤ r :=
begin
 intro r,
 induction r,
    {exact (ord.le.refl _)},
    {
        apply app,
        { assumption },
    }
end

lemma le_zero : ∀ r : ord, r ≤ 0 -> r = 0 :=
begin
  intros r H,
  cases H,
  esimp,
end

open nat

definition nat.max : nat -> nat -> nat
    | 0        m          := m
    | n        0          := n
    | (succ n) (succ m)   := succ (nat.max n m)

definition hight : ∀ o : ord, nat
  | 0 := 0
  | (f ∥ r) := 1 + nat.max (hight f) (hight r)


record has_swap [class] (A : Type) : Type := (swap : A -> A)

record has_involution [class] (A : Type) extends (has_swap A) := 
    (is_involution : ∀ x, swap (swap x) = x)

abbreviation σ {{A}} [H : has_swap A] x := @has_swap.swap A H x

print σ

inductive ineq : Type :=
  | LessThan
  | GreaterThan

inductive comp : Type :=
  | Ineq : ineq -> comp
  | EqualTo

namespace ineq

abbreviation LT := LessThan
abbreviation GT := GreaterThan

definition inversion : ineq -> ineq
  | LT := GT
  | GT := LT

definition ineq_swap [instance] : has_swap ineq 
    := {| has_swap ineq, swap := inversion |}

lemma inversion_is_involution :
  ∀ (x : ineq), σ(σ x) = x := 
    ineq.rec rfl rfl

definition ineq_involution [instance] :
    has_involution ineq := 
     {| has_involution ineq, ineq_swap, is_involution := inversion_is_involution |} 

end ineq

namespace comp

export ineq

abbreviation EQ := EqualTo
attribute comp.Ineq [coercion]

definition nudge : ineq -> comp -> comp
  | tie_breaker EQ      := Ineq tie_breaker
  | _           non_tie := non_tie

end comp

section comp_spec
open comp

parameter {A : Type}
parameter f : A -> A -> comp

local infix `≤` := le

variables x y : A

definition comp_spec' [H : has_le A] : Prop :=
    match f x y with
    | LT := x ≤ y
    | EQ := x = y
    | GT := y ≤ x
    end
    
definition comp_spec [H : has_le A] : Prop := 
    ∀ x y, comp_spec' x y
    
end comp_spec

namespace ord

open comp
open ineq

definition compOrd' : ((ord×ord)->comp)->(ord×ord)->comp
    | f (p, q) := 
      match (p,q) with
      | (0,0) := EQ
      | (0,_) := Ineq LT
      | (_,0) := Ineq GT
      | ((fp∥rp),(fq∥rq)) := 
        match f (fp,fq) with
        | EQ := f (rp,rq)
        | LT := nudge GT (f (rp,q))
        | GT := nudge LT (f (p,rq))
        end
      end

inductive is_child : ord -> ord -> Prop :=
  | through_f : forall {f r}, is_child f (f∥r)
  | through_r : forall {f r}, is_child f (f∥r)

inductive trans_completion' {A : Type} (R : A -> A -> Prop) : A -> A -> Type :=
  | single : forall {a b}, 
    R a b -> trans_completion' R a b
  | next : forall {a b} c, 
    R a b -> trans_completion' R b c -> trans_completion' R a c

abbreviation TR' {A} R := @trans_completion' A R

infix `~>`:50 := is_child

structure to_prop : Type -> Prop :=
  | inhabited : ∀ {A} (x : A), to_prop A

abbreviation TR {A} R := λ a b : A, to_prop (TR' R a b)

open eq.ops well_founded decidable prod

namespace trans_completion'
section One
  parameter A : Type
  parameter R : A -> A -> Prop

lemma trans_valid' : forall {a b}, TR' R a b -> ∃ c, R c b
  | a b (single p) := exists.intro a p
  | a b (next _ p pp) := trans_valid' pp

lemma trans_valid : forall {a b}, TR R a b -> ∃ c, R c b
  | a b {|to_prop, inhabited := tr |} := trans_valid' tr 

end One
end trans_completion'

open trans_completion'

lemma zero_has_no_children : ∀ x, ¬ (x ~> 0) :=
  begin
    intros x H,
    cases H,
    now
  end

lemma Zero_is_zero : Zero = 0 := rfl
open ord

theorem all_reached : well_founded TR :=
  well_founded.intro
    proof
      begin
        intro,
        constructor,
        intros,
        induction a,
        cases a_1,
        exfalso,
        assert H : ∃ z, z ~> 0,
        apply (trans_valid ord  x),
        now
      end
    qed
  
end

end ord

