#exit

example : ∀ (x y : rat), ∃ (z : rat), (z > x ∧ z > y) := by dlo_rat.decide
example : ∃ (z : rat), (z > 5) := by dlo_rat.decide
example : ∀ (x y z w v : rat), (x < y ∧ y < z ∧ z < w ∧ w < v) → x < v := by dlo_rat.decide
example : ∃ (x y : rat), x < 1.348 ∧ y > (324 / 23) := by dlo_rat.decide

example : forall a b : rat, (forall x : rat, x < a → x < b) ↔ a ≤ b := by dlo_rat.vm_decide
example : forall a b : rat, (forall x : rat, x < a ↔ x < b) ↔ a = b := by dlo_rat.vm_decide
example : forall a b, (forall x : rat, x < a → x < b) ↔ a ≤ b := by dlo_rat.vm_decide
example : forall x y : rat, x ≤ y ∨ x > y := by dlo_rat.vm_decide