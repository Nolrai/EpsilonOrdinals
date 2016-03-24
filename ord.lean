
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

inductive is_child : ord -> ord -> Prop :=
  | through_f : forall {f r}, is_child f (f∥r)
  | through_r : forall {f r}, is_child r (f∥r)

inductive kleen_star {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
  | refl : forall {a},
    kleen_star R a a
  | next : forall {a b} c, 
    R a b -> kleen_star R b c -> kleen_star R a c

attribute kleen_star.refl [refl]

notation R `⋆` := kleen_star R

infix `~>`:50 := is_child

open eq.ops well_founded decidable prod

namespace trans_completion
section One
  parameter A : Type
  parameter R : A -> A -> Prop

end One
end trans_completion

open trans_completion

lemma zero_has_no_children : ∀ x, ¬ (x ~> 0) :=
  begin
    intros x H,
    cases H,
    now
  end

lemma Zero_is_zero : Zero = 0 := rfl
reveal Zero_is_zero
open ord

infix `~~>`:50 := is_child⋆

lemma is_desc_split' : forall y x, 
    y ~~> x
    -> exists f r,
        (   y = x 
            ∨ (x = (f∥r) ∧ ((y ~~> f) ∨ (y ~~> r)))
        )
  :=
    begin
        intros y x H,
        induction H,
        {existsi 0, existsi 0, left, reflexivity},
        {
            induction v_0 with f v_1, induction v_1 with r v_2,
            cases v_2,
            {
                clear f r, 
                induction a_1 with f r, 
                    all_goals existsi f, 
                    all_goals existsi r,
                    all_goals right,
                    all_goals split,
                    all_goals try (symmetry; assumption),
                    {left, reflexivity},
                    {right, reflexivity}
            },
            {
                existsi f, existsi r, 
                right, 
                cases a_3 with H HH,
                split, {assumption}, 
                cases HH with HH, 
                {left, apply kleen_star.next, repeat assumption},
                {right, apply kleen_star.next, repeat assumption},
            },
        },
    end
    
definition is_desc_split {y} {f} {r} 
    : y ~~> (f∥r) -> y = (f∥r) ∨ ((y ~~> f) ∨ (y ~~> r)) :=
    begin
        intros y f r H,
        assert (∃ f' r', (f∥r) = (f'\||r') ∧ (f∥r) ∨ ((y ~~> f) ∨ (y ~~> r))
    end

check is_desc_split

theorem all_reached : well_founded (TR is_child) :=
  well_founded.intro
    proof
      begin
        intro a,
        induction a with f r,
        all_goals split,
        {
            intros y H,
            cases H,
            {
                exfalso,
                assert H : ∃ z, z ~> 0,
                {existsi y, rewrite Zero_is_zero at a_1, assumption},
                cases H, apply zero_has_no_children, assumption
            },
            {
                exfalso,
                assert H : ∃ z, z ~> 0,
                {apply trans_valid, apply a_2},
                cases H,
                apply zero_has_no_children,
                apply a_3
            },
        },
        {
            intro y YH,
            assert H : (y = f ∨ y = r) ∨ y ~~> f ∨ y ~~> r,
            {apply is_desc_split, assumption},
            cases H with H H,
            {all_goals cases H with H H, all_goals (subst y; assumption) },
            {
                all_goals cases H with H H,
                {cases v_0 with _ HH, apply HH, assumption},
                {cases v_1 with _ HH, apply HH, assumption},
            },
        }
      end
    qed
    
    protected definition R := rprod (TR is_child) (TR is_child)
    
    theorem wfR : well_founded ord.R := rprod.wf all_reached all_reached
    
    local infix `⟪`:50 := ord.R
    
    private lemma lemma1
        : Π fp rp fq rq, (rp, rq)⟪(fp∥rp, fq∥rq) :=
        take fp rp fq rq : ord, 
        have Hp : rp ⟪ (fp∥rp), from
            TR.single is_child.through_r,
        qed
    
    definition compOrd' : 
    Π x : (ord×ord), 
    (Π p : (ord×ord), p ⟪ x ->comp) ->
    comp
    | (0,0) _ := EQ
    | (0,_) _ := Ineq LT
    | (_,0) _ := Ineq GT
    | ((fp∥rp),(fq∥rq)) f := 
        match f (fp,fq) lemma1 with
        | EQ := f (rp,rq) _
        | LT := nudge GT (f (rp,(fq∥rq)) _)
        | GT := nudge LT (f ((fp∥rp),rq) _)
        end
    end
      
    
    definition compOrd x y := fix compOrd' (x,y)

end ord

end

