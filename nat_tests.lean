#exit

example : ∀ x : nat, 31 * x > 0 → x > 0 := by lna_int.decide
example : ∀ x y : nat, (x ≤ 5 ∧ y ≤ 3) → x + y ≤ 8 := by lna_int.decide
example : ∀ x y : nat, ¬(2 * x + 1 = 2 * y) := by lna_int.decide
example : ∀ x y : nat, x + 2 = y → ∃ z : nat, z + 1 = y := by lna_int.decide
example : ∀ x y : nat, x > 0 → x + y > 0 := by lna_int.decide

example : ∃ x y : nat, 7 * x = 5 * y := by lna.decide
example : ∃ x y : nat, 5 * x + 3 * y = 11 := by lna.decide
example : ∀ x : nat, x < 349 ∨ x > 123 := by lna.decide
example : ∀ x : nat, ∃ y : nat, x = 2 * y ∨ x = (2 * y) + 1 := by lna.decide
example : ∀ x y : nat, ∃ z : nat, (x < z ∧ y < z) := by lna.decide

example : ∀ x : nat, x > 5000 → ∃ y : nat, y ≥ 1000 ∧ 5 * y < x := by lna.vm_decide
example : ∀ x y z w : nat, x ≤ y → y ≤ z → z ≤ w → x ≤ w := by lna.vm_decide
example : ∀ x y : nat, x ≤ 3 * y → 3 * x ≤ 9 * y := by lna.vm_decide
example : ∀ x y : nat, x + 2 < y → ∃ z w : nat, (x < z ∧ z < w ∧ w < y) := by lna.vm_decide
example : ∀ x y : nat, 6 * x = 5 * y → ∃ z : nat, y = 2 * z := by lna.vm_decide
