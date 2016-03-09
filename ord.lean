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

section ord_le

inductive ord.le : ord -> ord -> Prop :=
| refl  {} : ∀ r        : ord,                                              ord.le r r
| app   {} : ∀ r q f    : ord,           ord.le q r                     ->  ord.le q (f r)
| mono  {} : ∀ r q g f  : ord,           ord.le q r     -> ord.le g f   ->  ord.le (g q) (f r)
| limit {} : ∀ r q g f  : ord,  q ≠ f -> ord.le q (f r) -> ord.le g f   ->  ord.le (g q) (f r)

local infix ≤ := ord.le

print ord.le

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

reveal zero_le
print zero_le

end ord_le
