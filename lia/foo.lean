#exit
ex01 : forall x : int, x <= -x -> x <= 0 
ex02 : forall x y : int, (x <= 5 /\ y <= 3) -> x + y <= 8 
ex03 : forall x y z : int, x < y -> y < z -> x < z 
ex04 : forall x y z : int, x - y <= x - z -> z <= y 
ex05 : forall x : int, (x = 5 \/ x = 7) -> 2 < x 
ex06 : forall x : int, (x = -5 \/ x = 7) -> ¬x = 0 
ex07 : forall x : int, 31 * x > 0 -> x > 0 
ex08 : forall x y : int, (-x - y < x - y) -> (x - y < x + y) -> (x > 0 /\ y > 0) 
ex09 : forall x : int, (x >= -1 /\ x <= 1) -> (x = -1 \/ x = 0 \/ x = 1)
ex10 : forall x : int, exists y : int, x = 2 * y \/ x = (2 * y) + 1 
ex11 : forall x : int, 5 * x = 5 -> x = 1 
ex12 : forall x y : int, ¬(2 * x + 1 = 2 * y) 
ex13 : forall x y z : int, (2 * x + 1 = 2 * y) -> x + y + z > 129 
ex14 : exists x y : int, 5 * x + 3 * y = 1 
ex15 : forall x y : int, x + 2 < y -> exists z w : int, (x < z /\ z < w /\ w < y) 
ex16 : forall x : int, (exists y : int, 2 * y + 1 = x) -> ¬ exists y : int, 4 * y = x 
ex17 : forall x y z : int, x = y -> y = z -> x = z 
ex18 : forall x : int, x < 349 \/ x > 123 
ex19 : forall x y : int, x <= 3 * y -> 3 * x <= 9 * y 
ex20 : exists x : int, 5 * x = 1335 
ex21 : exists x y : int, x + y = 231 /\ x - y = -487 
ex22 : exists x y : int, 32 * x = 2023 + y 
ex23 : forall x : int, (x < 43 /\ x > 513) -> ¬x = x 
ex24 : forall x : int, exists y : int, x = 3 * y - 1 \/ x = 3 * y \/ x = 3 * y + 1 
ex25 : forall a : int, exists b : int, a < 4 * b + 3 * a \/ (¬(a < b) /\ a > b + 1) 
ex26 : exists x y : int, x > 0 /\ y ≥ 0 /\ 3 * x - 5 * y = 1 
ex27 : exists x y : int, x ≥ 0 /\ y ≥ 0 /\ 5 * x - 6 * y = 1 
ex28 : exists x y : int, x ≥ 0 /\ y ≥ 0 /\ 5 * x - 3 * y = 1 
ex29 : exists x y : int, x ≥ 0 /\ y ≥ 0 /\ 3 * x - 5 * y = 1 
ex30 : exists a b : int, ¬(a = 1) /\ ((2 * b = a) \/ (2 * b = 3 * a + 1)) /\ (a = b) 
ex31 : forall x : int, x > 5000 -> exists y : int, y ≥ 1000 /\ 5 * y < x 
ex32 : forall x : int, exists y : int, 
  x = 5 * y - 2 \/ 
  x = 5 * y - 1 \/ 
  x = 5 * y     \/ 
  x = 5 * y + 1 \/ 
  x = 5 * y + 2 
ex33 : forall x : int, (exists y : int, 3 * y = x) 
  -> (exists y : int, 7 * y = x) -> (exists y : int, 21 * y = x) 
ex34 : forall y : int, (exists d : int, y = 65 * d) 
  -> (exists d : int, y = 5 * d) 
ex35 : forall x y : int, 6 * x = 5 * y -> exists d : int, y = 3 * d 
ex36 : forall x : int, ¬(exists m : int, x = 2 * m) 
  /\ (exists m : int, x = 3 * m + 1) 
  ↔ (exists m : int, x = 12 * m + 1) 
  \/ (exists m : int, x = 12 * m + 7) 
ex37 : forall x y : int, (exists d : int, x + y = 2 * d) 
  ↔ ((exists d : int, x = 2 * d) ↔ (exists d : int, y = 2 * d)) 
ex38 : forall n : int,
    0 < n /\ n < 2400
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
          n <= 2503 /\ 2503 <= 2 * n 
ex39 : exists x : int, x * 0 = 11 
ex40 : forall x : int, exists y : int, x = 3 * y ∨ x = 3 * y + 1 
ex41 : exists x y z : int, 4 * x - 6 * y = 1 
ex42 : forall x y : int, x <= y -> 2 * x + 1 < 2 * y 
ex43 : forall a b : int, exists x : int, a < 20 * x /\ 20 * x < b 
ex44 : exists y : int, forall x : int, x + 5 * y > 1 
  /\ 13 * x - y > 1 /\ x + 2 < 0 
ex45 : exists x y : int, 5 * x + 10 * y = 1 
ex46 : forall x y : int, x ≥ 0 /\ y ≥ 0 
  -> 12 * x - 8 * y < 0 \/ 12 * x - 8 * y > 2 
ex47 : exists x y : int, x ≥ 0 /\ y ≥ 0 /\ 6 * x - 3 * y = 1 
ex48 : forall x y : int, ¬(x = 0) -> 5 * y < 6 * x \/ 5 * y > 6 * x 
ex49 : forall x y : int, ¬(6 * x = 5 * y) 
ex50 : exists a b : int, a > 1 /\ b > 1 /\
         ((2 * b = a) \/ (2 * b = 3 * a + 1)) /\
         (a = b) 
