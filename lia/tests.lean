import .main 

set_option profiler true 

open tactic


lemma ex06 : ∀ x : int, x ≤ -x → x ≤ 0 :=
begin
  reify, 
  normalize, 
  quant_elim,
  exact_dec_trivial,
  exact_dec_trivial,
end



#exit

/- Acknowledgement : The examples marked with a commented plus sign (--+) 
   are my own. The rest are from John Harrison's Handbook of Practical 
   Logic and Automated Reasoning. -/

/- Theorems (Easy) -/
lemma ex01 : ∀ x : int, x ≤ -x → x ≤ 0 := by lia --+
lemma ex02 : ∀ x y : int, (x ≤ 5 ∧ y ≤ 3) → x + y ≤ 8 := by lia --+
lemma ex03 : ∀ x y z : int, x < y → y < z → x < z := by lia --+
lemma ex04 : ∀ x y z : int, x - y ≤ x - z → z ≤ y := by lia --+
lemma ex05 : ∀ x : int, (x = 5 ∨ x = 7) → 2 < x := by lia --+
lemma ex06 : ∀ x : int, (x = -5 ∨ x = 7) → ¬x = 0 := by lia --+
-- lemma ex07 : ∀ x : int, 31 * x > 0 → x > 0 := by lia --+
-- lemma ex08 : ∀ x y : int, (-x - y < x - y) → (x - y < x + y) → (x > 0 ∧ y > 0) := by lia --+
-- lemma ex09 : ∀ x : int, (x ≥ -1 ∧ x ≤ 1) → (x = -1 ∨ x = 0 ∨ x = 1):= by lia --+
-- lemma ex10 : ∀ x : int, ∃ y : int, x = 2 * y ∨ x = (2 * y) + 1 := by lia_vm' --+
-- lemma ex11 : ∀ x : int, 5 * x = 5 → x = 1 := by lia --+
-- lemma ex12 : ∀ x y : int, ¬(2 * x + 1 = 2 * y) := by lia 
-- lemma ex13 : ∀ x y z : int, (2 * x + 1 = 2 * y) → x + y + z > 129 := by lia 
-- lemma ex14 : ∃ x y : int, 5 * x + 3 * y = 1 := by lia 
-- lemma ex15 : ∀ x y : int, x + 2 < y → ∃ z w : int, (x < z ∧ z < w ∧ w < y) := by lia 

/- Theorems (Medium) -/
-- lemma ex16 : ∀ x : int, (∃ y : int, 2 * y + 1 = x) → ¬ ∃ y : int, 4 * y = x := by lia  --+
-- lemma ex17 : ∀ x y z : int, x = y → y = z → x = z := by lia --+
-- lemma ex18 : ∀ x : int, x < 349 ∨ x > 123 := by lia --+
-- lemma ex19 : ∀ x y : int, x ≤ 3 * y → 3 * x ≤ 9 * y := by lia --+
-- lemma ex20 : ∃ x : int, 5 * x = 1335 := by lia --+
-- lemma ex21 : ∃ x y : int, x + y = 231 ∧ x - y = -487 := by lia --+
-- lemma ex22 : ∃ x y : int, 32 * x = 2023 + y := by lia --+
-- lemma ex23 : ∀ x : int, (x < 43 ∧ x > 513) → ¬x = x := by lia --+
-- lemma ex24 : ∀ x : int, ∃ y : int, x = 3 * y - 1 ∨ x = 3 * y ∨ x = 3 * y + 1 := by lia --+
-- lemma ex25 : ∀ a : int, ∃ b : int, a < 4 * b + 3 * a ∨ (¬(a < b) ∧ a > b + 1) := by lia
-- lemma ex26 : ∃ x y : int, x > 0 ∧ y ≥ 0 ∧ 3 * x - 5 * y = 1 := by lia
-- lemma ex27 : ∃ x y : int, x ≥ 0 ∧ y ≥ 0 ∧ 5 * x - 6 * y = 1 := by lia
-- lemma ex28 : ∃ x y : int, x ≥ 0 ∧ y ≥ 0 ∧ 5 * x - 3 * y = 1 := by lia
-- lemma ex29 : ∃ x y : int, x ≥ 0 ∧ y ≥ 0 ∧ 3 * x - 5 * y = 1 := by lia
-- lemma ex30 : ∃ a b : int, ¬(a = 1) ∧ ((2 * b = a) ∨ (2 * b = 3 * a + 1)) ∧ (a = b) := by lia
-- lemma ex31 : ∀ x : int, ∃ y : int, 
--   x = 5 * y - 2 ∨ 
--   x = 5 * y - 1 ∨ 
--   x = 5 * y     ∨ 
--   x = 5 * y + 1 ∨ 
--   x = 5 * y + 2 := by lia
-- lemma ex32 : ∀ x y : int, 6 * x = 5 * y 
--   → ∃ d : int, y = 3 * d := by lia
-- lemma ex33 : ∀ x : int, ¬(∃ m : int, x = 2 * m) 
--   ∧ (∃ m : int, x = 3 * m + 1) 
--   ↔ (∃ m : int, x = 12 * m + 1) 
--   ∨ (∃ m : int, x = 12 * m + 7) := by lia
-- lemma ex34 : ∀ x y : int, (∃ d : int, x + y = 2 * d) 
--   ↔ ((∃ d : int, x = 2 * d) ↔ (∃ d : int, y = 2 * d)) := by lia



/- Theorems (Hard) -/
lemma ex35 : ∀ x : int, x > 5000 → ∃ y : int, y ≥ 1000 ∧ 5 * y < x := by lia_vm --+
lemma ex36 : ∀ x : int, (∃ y : int, 3 * y = x) → (∃ y : int, 7 * y = x) → (∃ y : int, 21 * y = x) := by lia_vm
lemma ex37 : ∀ y : int, (∃ d : int, y = 65 * d) → (∃ d : int, y = 5 * d) := by lia_vm
lemma ex38 : ∀ n : int,
    0 < n ∧ n < 2400
      → n ≤ 2 ∧ 2 ≤ 2 * n ∨
          n ≤ 3 ∧ 3 ≤ 2 * n ∨
          n ≤ 5 ∧ 5 ≤ 2 * n ∨
          n ≤ 7 ∧ 7 ≤ 2 * n ∨
          n ≤ 13 ∧ 13 ≤ 2 * n ∨
          n ≤ 23 ∧ 23 ≤ 2 * n ∨
          n ≤ 43 ∧ 43 ≤ 2 * n ∨
          n ≤ 83 ∧ 83 ≤ 2 * n ∨
          n ≤ 163 ∧ 163 ≤ 2 * n ∨
          n ≤ 317 ∧ 317 ≤ 2 * n ∨
          n ≤ 631 ∧ 631 ≤ 2 * n ∨
          n ≤ 1259 ∧ 1259 ≤ 2 * n ∨
          n ≤ 2503 ∧ 2503 ≤ 2 * n := by lia_vm
lemma ex39 : ∀ z : int, z > 7 → ∃ x y : int, x ≥ 0 ∧ y ≥ 0 ∧ 3 * x + 5 * y = z := by lia_vm
lemma ex40 : ∃ w x y z : int, 2 * w + 3 * x + 4 * y + 5 * z = 1 := by lia_vm
lemma ex41 : ∀ x : int, x ≥ 8 → ∃ u v : int, u ≥ 0 ∧ v ≥ 0 ∧ x = 3 * u + 5 * v := by lia_vm



/- Timeouts & deep recursions : these cannot be decided the current version of the tactic. -/
-------------------------------------------------------------

-- example : ∃ l : int,
--       ∀ x : int, x ≥ l
--                 → ∃ u v : int, u ≥ 0 ∧ v ≥ 0 ∧ x = 3 * u + 8 * v := by lia_vm
-- example : ∃ l : int,
--       ∀ x : int, x ≥ l
--                 → ∃ u v : int, u ≥ 0 ∧ v ≥ 0 ∧ x = 7 * u + 8 * v := by lia_vm
-- example : ∀ x q1 q2 r1 r2 : int,
--       x < 4699 ∧
--       2622 * x = 65536 * q1 + r1 ∧ 0 ≤ q1 ∧ 0 ≤ r1 ∧ r1 < 65536 ∧
--       x = 100 * q2 + r2 ∧ 0 ≤ q2 ∧ 0 ≤ r2 ∧ r2 < 100
--       → q1 = q2 := by lia_vm


-- example : ∀ z : int, z ≤ 7
--   → ((∃ x y : int, x ≥ 0 ∧ y ≥ 0 ∧ 3 * x + 5 * y = z) ↔
--        ¬(∃ x y : int, x ≥ 0 ∧ y ≥ 0 ∧ 3 * x + 5 * y = 7 - z)) := by lia_vm
-- example : ∃ a b : int, a > 1 ∧ b > 1 ∧
--                ((2 * b = a) ∨ (2 * b = 3 * a + 1)) ∧
--                ((2 * a = b) ∨ (2 * a = 3 * b + 1)) := by lia_vm
-- example : ∃ l : int,
--       ∀ x : int, x ≥ l
--                 → ∃ u v : int, u ≥ 0 ∧ v ≥ 0 ∧ x = 3 * u + 5 * v := by lia_vm
-- example : ∃ l : int,
--       ∀ x : int, x ≥ l
--                 → ∃ u v : int, u ≥ 0 ∧ v ≥ 0 ∧ x = 3 * u + 7 * v := by lia_vm


#exit

/- Nontheorems : Useful for testing the soundness of vm-based tactics. -/
-- example : ∃ x : int, x * 0 = 11 := by lia --+
-- example : ∀ x : int, ∃ y : int, x = 3 * y ∨ x = 3 * y + 1 := by lia --+
-- example : ∃ x y z : int, 4 * x - 6 * y = 1 := by lia
-- lemma ex42 : ∀ x y : int, x ≤ y → 2 * x + 1 < 2 * y := by lia
-- lemma ex43 : ∀ a b : int, ∃ x : int, a < 20 * x ∧ 20 * x < b := by lia
-- lemma ex44 : ∃ y : int, ∀ x : int, x + 5 * y > 1 ∧ 13 * x - y > 1 ∧ x + 2 < 0 := by lia
-- lemma ex45 : ∃ x y : int, 5 * x + 10 * y = 1 := by lia
-- lemma ex46 : ∀ x y : int, x ≥ 0 ∧ y ≥ 0           → 12 * x - 8 * y < 0 ∨ 12 * x - 8 * y > 2 := by lia
-- lemma ex47 : ∃ x y : int, x ≥ 0 ∧ y ≥ 0 ∧ 6 * x - 3 * y = 1 := by lia
-- lemma ex48 : ∀ x y : int, ¬(x = 0) → 5 * y < 6 * x ∨ 5 * y > 6 * x := by lia
-- lemma ex49 : ∀ x y : int, ¬(6 * x = 5 * y) := by lia
-- lemma ex50 : ∃ a b : int, a > 1 ∧ b > 1 ∧
--                ((2 * b = a) ∨ (2 * b = 3 * a + 1)) ∧
--                (a = b) := by lia
-- example : ∀ z : int, z > 2 → ∃ x y : int, x ≥ 0 ∧ y ≥ 0 ∧ 3 * x + 5 * y = z := by lia_vm




/- Open formulas : The tactic only supports closed formulas at the moment. -/

-- example : ∀ x : int, a < x → b < x := by lia
-- example : ∀ x : int, a < 3 * x → b < 3 * x := by lia
-- example : (∃ d : int, y = 65 * d) → (∃ d : int, y = 5 * d) := by lia
-- example : ∀ x : int, a ≤ x → b < x := by lia
-- example : ∃ x : int, a < 20 * x ∧ 20 * x < b := by lia
-- example : ∀ b : int, ∃ x : int, a < 20 * x ∧ 20 * x < b := by lia
-- example : 6 * x = 5 * y → ∃ d : int, y = 3 * d := by lia
-- example : a + 2 = b ∧ v_3 = b - a + 1 ∧ v_2 = b - 2 ∧ v_1 = 3 → false := by lia
-- example : ((2 * b = a) ∨ (2 * b = 3 * a + 1)) ∧
--    ((2 * c = b) ∨ (2 * c = 3 * b + 1)) ∧
--    ((2 * d = c) ∨ (2 * d = 3 * c + 1)) ∧
--    ((2 * e = d) ∨ (2 * e = 3 * d + 1)) ∧
--    ((2 * f = e) ∨ (2 * f = 3 * e + 1)) ∧
--    (f = a) := by lia



/- Goals with divisibility-by-constant predicates : 
   It is possible to extend the tactic to handle such goals, 
   but this functionality is not supported at the moment. -/

-- example : ∀ x y : int, ¬(5 ∣ x) ∧ ¬(6 ∣ y) → ¬(6 * x = 5 * y) := by lia
-- example : ∀ x y : int, ¬(5 ∣ x) → ¬(6 * x = 5 * y) := by lia
-- example : ∀ x : int, ¬(2 ∣ x) ∧ (3 ∣ x-1) ↔
--             (12 ∣ x-1) ∨ (12 ∣ x-7) := by lia
-- example : ∀ x : int,
--        ¬((2 ∣ x))
--        → (4 ∣ x-1) ∨
--            (8 ∣ x-1) ∨
--            (8 ∣ x-3) ∨
--            (6 ∣ x-1) ∨
--            (14 ∣ x-1) ∨
--            (14 ∣ x-9) ∨
--            (14 ∣ x-11) ∨
--            (24 ∣ x-5) ∨
--            (24 ∣ x-11) := by lia