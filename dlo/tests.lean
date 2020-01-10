import .reify .main

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
