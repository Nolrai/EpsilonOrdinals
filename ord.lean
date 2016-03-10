inductive ord : Type :=
| Zero : ord
| Stroke : ord -> ord -> ord

open ord

infix `∥`:50 := Stroke

definition ord.has_zero [instance] : has_zero ord :=
  has_zero.mk Zero
  
attribute Stroke [coercion] --this seems to act flaky?

definition ord.has_one [instance] : has_one ord :=
  has_one.mk (0 ∥ 0)

inductive ord.le : ord -> ord -> Prop :=
| refl  {} : ∀ r        : ord,                                              ord.le r r
| app   {} : ∀ r q f    : ord,           ord.le q r                     ->  ord.le q (f r)
| mono  {} : ∀ r q g f  : ord,           ord.le q r     -> ord.le g f   ->  ord.le (g q) (f r)
| limit {} : ∀ r q g f  : ord,  q ≠ f -> ord.le q (f r) -> ord.le g f   ->  ord.le (g q) (f r)

local infix ≤ := ord.le

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
  
inductive comparison : Type :=
| LessThan
| EqualTo
| GreaterThan

section comp_spec

parameter A : Type
parameter f : A -> A -> comparison

local infix `≤` := le

variables x y : A

definition comp_spec' [H : has_le A] : Prop :=
    match f x y with
    | LessThan := x ≤ y
    | EqualTo  := x = y
    | GreaterThan := y ≤ x
    end
    
definition comp_spec [H : has_le A] : Prop := 
    ∀ x y, comp_spec' x y
    
end comp_spec

print comp_spec
