import .lia.main

example : ∃ (z : int), z + 5 = 1223 := by lia
example : ∃ (x : int), 3 ∣ (x + 5)  := by lia

example : ∀ x : int, 31 * x > 0 → x > 0 := by lia
example : ∀ x y : int, (x ≤ 5 ∧ y ≤ 3) → x + y ≤ 8 := by lia
example : ∀ x y : int, ¬(2 * x + 1 = 2 * y) := by lia
example : ∀ x y : int, x + 2 = y → ∃ z : int, z + 1 = y := by lia

example : ∃ x y : int, 7 * x = 5 * y := by lia
example : ∃ x y : int, 5 * x + 3 * y = 11 := by lia
example : ∀ x : int, x < 349 ∨ x > 123 := by lia
example : ∀ x : int, ∃ y : int, x = 2 * y ∨ x = (2 * y) + 1 := by lia
example : ∀ x y : int, ∃ z : int, (x < z ∧ y < z) := by lia

example : ∀ x y z w : int, x ≤ y → y ≤ z → z ≤ w → x ≤ w := by lia
example : ∀ x y : int, x ≤ 3 * y → 3 * x ≤ 9 * y := by lia
example : ∀ x y : int, x + 2 < y → ∃ z w : int, (x < z ∧ z < w ∧ w < y) := by lia
example : ∀ x y : int, 6 * x = 5 * y → ∃ z : int, y = 2 * z := by lia

-- Large numbers can be handled with lia_vm, but requires you to trust VM evaluation
example : ∀ x : int, x > 5000 → ∃ y : int, y ≥ 1000 ∧ 5 * y < x := by lia_vm
