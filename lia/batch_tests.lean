import .main 

open tactic


#exit
meta def ex01 : expr := `(∀ x : int, x ≤ -x → x ≤ 0)
meta def ex02 : expr := `(∀ x y : int, (x ≤ 5 ∧ y ≤ 3) → x + y ≤ 8)
meta def ex03 : expr := `(∀ x y z : int, x < y → y < z → x < z)
meta def ex04 : expr := `(∀ x y z : int, x - y ≤ x - z → z ≤ y)
meta def ex05 : expr := `(∀ x : int, (x = 5 ∨ x = 7) → 2 < x)
meta def ex06 : expr := `(∀ x : int, (x = -5 ∨ x = 7) → x ≠ 0)
meta def ex07 : expr := `(∀ x : int, 31 * x > 0 → x > 0)
meta def ex08 : expr := `(∀ x y : int, (-x - y < x - y) → (x - y < x + y) → (x > 0 ∧ y > 0))
meta def ex09 : expr := `(∀ x y : int, ¬(2 * x + 1 = 2 * y))
meta def ex10 : expr := `(∀ x y z : int, (2 * x + 1 = 2 * y) → x + y + z > 1)
meta def ex11 : expr := `(∃ x y : int, 5 * x + 3 * y = 1)
meta def ex12 : expr := `(∀ x y : int, x + 2 < y → ∃ z w : int, (x < z ∧ z < w ∧ w < y))
meta def ex13 : expr := `(∀ x : int, (x ≥ -1 ∧ x ≤ 1) → (x = -1 ∨ x = 0 ∨ x = 1))
meta def ex14 : expr := `(∀ x : int, ∃ y : int, x = 2 * y ∨ x = (2 * y) + 1)
meta def ex15 : expr := `(∀ x : int, 5 * x = 5 → x = 1)

meta def ex16 : expr := `(∀ x : int, (∃ y : int, 2 * y + 1 = x) → ¬ ∃ y : int, 4 * y = x)
meta def ex17 : expr := `(∃ x : int, 5 * x = 1335)
meta def ex18 : expr := `(∃ x y : int, x + y = 231 ∧ x - y = -487)
meta def ex19 : expr := `(∀ a : int, ∃ b : int, a < 4 * b + 3 * a ∨ (¬(a < b) ∧ a > b + 1))
meta def ex20 : expr := `(∃ x y : int, x > 0 ∧ y ≥ 0 ∧ 3 * x - 5 * y = 1)
meta def ex21 : expr := `(∃ x y : int, x ≥ 0 ∧ y ≥ 0 ∧ 5 * x - 6 * y = 1)
meta def ex22 : expr := `(∃ x y : int, x ≥ 0 ∧ y ≥ 0 ∧ 5 * x - 3 * y = 1)
meta def ex23 : expr := `(∃ x y : int, x ≥ 0 ∧ y ≥ 0 ∧ 3 * x - 5 * y = 1)
meta def ex24 : expr := `(∃ a b : int, ¬(a = 1) ∧ ((2 * b = a) ∨ (2 * b = 3 * a + 1)) ∧ (a = b))
meta def ex25 : expr := `(∀ x y z : int, x = y → y = z → x = z)
meta def ex26 : expr := `(∀ x : int, x < 349 ∨ x > 123)
meta def ex27 : expr := `(∀ x y : int, x ≤ 3 * y → 3 * x ≤ 9 * y)
meta def ex28 : expr := `(∃ x y : int, 32 * x = 2023 + y)
meta def ex29 : expr := `(∀ x : int, (x < 43 ∧ x > 513) → x ≠ x)
meta def ex30 : expr := `(∀ x : int, ∃ y : int, x = 3 * y - 1 ∨ x = 3 * y ∨ x = 3 * y + 1)
meta def ex31 : expr := `(forall x : int, exists y : int, x = 5 * y - 2 \/ x = 5 * y - 1 \/ x = 5 * y \/ x = 5 * y + 1 \/ x = 5 * y + 2) 
meta def ex32 : expr := `(forall x y : int, 6 * x = 5 * y -> exists d : int, y = 3 * d) 
meta def ex33 : expr := `(forall x : int, ¬(exists m : int, x = 2 * m) /\ (exists m : int, x = 3 * m + 1) ↔ (exists m : int, x = 12 * m + 1) \/ (exists m : int, x = 12 * m + 7)) 
meta def ex34 : expr := `(forall x y : int, (exists d : int, x + y = 2 * d) ↔ ((exists d : int, x = 2 * d) ↔ (exists d : int, y = 2 * d))) 

meta def ex35 : expr := `(∀ x : int, x > 5000 → ∃ y : int, y ≥ 1000 ∧ 5 * y < x)
meta def ex36 : expr := `(forall x : int, (exists y : int, 3 * y = x) -> (exists y : int, 7 * y = x) -> (exists y : int, 21 * y = x)) 
meta def ex37 : expr := `(forall y : int, (exists d : int, y = 65 * d) -> (exists d : int, y = 5 * d)) 
meta def ex38 : expr :=
  `(forall n : int, 0 < n /\ n < 2400
    -> n <= 2 /\ 2 <= 2 * n \/
       n <= 3 /\ 3 <= 2 * n \/
       n <= 5 /\ 5 <= 2 * n \/
       n <= 7 /\ 7 <= 2 * n \/
       n <= 13 /\ 13 <= 2 * n \/
       n <= 23 /\ 23 <= 2 * n \/
       n <= 43 /\ 43 <= 2 * n \/
       n <= 83 /\ 83 <= 2 * n \/
       n <= 163 /\ 163 <= 2 * n \/
       n <= 317 /\ 317 <= 2 * n \/
       n <= 631 /\ 631 <= 2 * n \/
       n <= 1259 /\ 1259 <= 2 * n \/
       n <= 2503 /\ 2503 <= 2 * n) 
meta def ex39 : expr := `(forall z : int, z > 7 -> exists x y : int, x >= 0 /\ y >= 0 /\ 3 * x + 5 * y = z) 
meta def ex40 : expr := `(exists w x y z : int, 2 * w + 3 * x + 4 * y + 5 * z = 1) 
meta def ex41 : expr := `(forall x : int, x >= 8 -> exists u v : int, u >= 0 /\ v >= 0 /\ x = 3 * u + 5 * v) 
meta def ex42 : expr :=  `(forall x y : int, x <= y -> 2 * x + 1 < 2 * y)
meta def ex43 : expr :=  `(forall a b : int, exists x : int, a < 20 * x /\ 20 * x < b)
meta def ex44 : expr :=  `(exists y : int, forall x : int, x + 5 * y > 1 /\ 13 * x - y > 1 /\ x + 2 < 0)
meta def ex45 : expr :=  `(exists x y : int, 5 * x + 10 * y = 1)
meta def ex46 : expr :=  `(forall x y : int, x >= 0 /\ y >= 0           -> 12 * x - 8 * y < 0 \/ 12 * x - 8 * y > 2)
meta def ex47 : expr :=  `(exists x y : int, x >= 0 /\ y >= 0 /\ 6 * x - 3 * y = 1)
meta def ex48 : expr :=  `(forall x y : int, ¬(x = 0) -> 5 * y < 6 * x \/ 5 * y > 6 * x)
meta def ex49 : expr :=  `(forall x y : int, ¬(6 * x = 5 * y))
meta def ex50 : expr :=  `(exists a b : int, a > 1 /\ b > 1 /\ ((2 * b = a) \/ (2 * b = 3 * a + 1)) /\ (a = b))

meta def batch_test (solver : tactic unit) : nat → list expr → tactic unit 
| _ [] := tactic.triv
| idx (exp::exps) :=
  ((do gs ← tactic.get_goals,
       g ← tactic.mk_meta_var exp,
       tactic.set_goals (g::gs),
       solver) <|> (trace (("Failed ex " : format) ++ format.of_nat idx) >> skip))
       >> batch_test (idx+1) exps

meta def examples_easy : list expr := 
[ex01,ex02,ex03,ex04,ex05,ex06,ex07,ex08,ex09,ex10,
 ex11,ex12,ex13,ex14,ex15,ex16,ex17,ex18,ex19,ex20,
 ex21,ex22,ex23,ex24,ex25,ex26,ex27,ex28,ex29,ex30,
 ex31,ex32,ex33,ex34]

meta def examples_hard : list expr := 
[ex35,ex36,ex37,ex38,ex39,ex40,ex41]

meta def nontheorems : list expr := 
[ex42,ex43,ex44,ex45,ex46,ex47,ex48,ex49,ex50]

set_option profiler true

lemma test : true := 
by do batch_test lia_vm 0 nontheorems



-- lemma test_lia_vm : true := 
-- by do batch_test lia_vm 0 examples_easy
