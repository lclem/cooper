import .reify' .main

open tactic 
/- Theorems (Easy) -/

example : ∀ (x y : rat), ∃ (z : rat), (z > x ∧ z > y) := by dlo
example : ∃ (z : rat), (z > (5 : rat)) := by dlo
example : ∃ (x y : rat), x < 1.348 ∧ y > (324 / 23) := by dlo

example : forall x y : rat, exists z : rat, z < x ∧ z < y := by dlo
example : forall x : rat, exists y : rat, x < y := by dlo
example : forall x y : rat, x < y ∨ (x = y) ∨ y < x := by dlo
example : forall x y : rat, exists z : rat, z < x ∧ z < y := by dlo
example : forall x y : rat, x < y → exists z : rat, x < z ∧ z < y := by dlo
example : exists x : rat, x = x := by dlo
example : forall x y z : rat, exists u, u < x ∧ u < y ∧ u < z := by dlo
example : forall a b : rat, exists x : rat, ¬(x = a) ∨ ¬(x = b) ∨ (a = b) := by dlo

/- Theorems (Hard) -/

-- example : ∀ (x y z w v : rat), (x < y ∧ y < z ∧ z < w ∧ w < v) → x < v := by dlo

-- example : forall x y z : rat, x < y ∧ y < z → x < z := by dlo
-- example : forall x y : rat, ¬(x = y) → exists u, u < x ∧ (y < u ∨ x < y) := by dlo
-- example : forall a b : rat, (forall x : rat, x < a → x < b) ↔ a ≤ b := by dlo_rat.vm_decide
-- example : forall a b : rat, (forall x : rat, x < a ↔ x < b) ↔ a = b := by dlo_rat.vm_decide
-- example : forall a b, (forall x : rat, x < a → x < b) ↔ a ≤ b := by dlo_rat.vm_decide
-- example : forall x y : rat, x ≤ y ∨ x > y := by dlo_rat.vm_decide




/- Nontheorems -/

-- example : exists x y z : rat, forall u,
--                  x < x ∨ ¬x < u ∨ (x < y ∧ y < z ∧ ¬x < z) := by dlo_rat.vm_decide
-- example : exists x y : rat, x < y ∧ y < x := by dlo_rat.vm_decide
-- example : forall x y : rat, exists z : rat, z < x ∧ x < y := by dlo_rat.vm_decide
-- example : forall x y : rat, x ≤ y ∨ x < y := by dlo_rat.vm_decide



/- Open goals -/

-- example : exists x : rat, x = x ∧ x = y := by dlo_rat.vm_decide
-- example : forall x : rat, x < a → x < b := by dlo_rat.vm_decide
-- example : exists z : rat, z < x ∧ x < y := by dlo_rat.vm_decide
-- example : exists z : rat, x < z ∧ z < y := by dlo_rat.vm_decide
-- example : exists z : rat, x ≤ z ∧ z ≤ y := by dlo_rat.vm_decide
-- example : forall x y : rat, x < y := by dlo_rat.vm_decide
-- example : exists z : rat, x < z ∧ z ≤ y := by dlo_rat.vm_decide
-- example : forall y : rat, x < y ∧ y < z → w < z := by dlo_rat.vm_decide
-- example : exists z : rat, z < x ∧ x < y := by dlo_rat.vm_decide
-- example : forall x : rat, x < a → x < b := by dlo_rat.vm_decide
-- example : forall x : rat, x < a → x ≤ b := by dlo_rat.vm_decide