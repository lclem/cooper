import data.num.lemmas data.list.basic .tactics .int

open tactic

def nat.to_num (n : nat) : num := n
def int.to_znum (z : int) : znum := z
def nat.to_znum : nat → znum := int.to_znum ∘ nat.to_int
def num.to_nat (n : num) : nat := n
def znum.to_int (z : znum) : int := z
def znum.to_nat : znum → nat := int.to_nat ∘ znum.to_int

lemma int.bijective_to_znum : function.bijective int.to_znum := 
begin
  rw [function.bijective_iff_has_inverse],
  existsi (λ (z : znum), (z : int)), constructor,
  { simp [function.left_inverse, int.to_znum] },
  { simp [function.left_inverse, 
    function.right_inverse, int.to_znum] }
end

lemma int.to_znum_to_int {z : int} : z.to_znum.to_int = z := 
begin simp [int.to_znum, znum.to_int] end

lemma int.map_to_znum_to_int {zs : list int} : 
list.map znum.to_int (list.map int.to_znum zs) = zs := 
begin
  simp [list.map, int.to_znum, znum.to_int, function.comp], 
  have h : (λ (x : ℤ), x) = id, refl, rw h, apply list.map_id
end

lemma nat.to_znum_to_nat {n : nat} : n.to_znum.to_nat = n := 
begin
  simp [znum.to_nat, nat.to_znum],
  rw int.to_znum_to_int, rw nat.to_int_to_nat
end

lemma nat.to_int_nonneg {n : nat} : 0 ≤ n.to_int :=
begin exact_dec_trivial end



namespace num

open list

instance inhabited : inhabited num := ⟨0⟩ 

lemma le_of_nat {m n : nat} : m.to_num ≤ n.to_num ↔ m ≤ n :=
begin rw ← le_to_nat, simp [nat.to_num] end

lemma add_of_nat' {m n : nat} : (m + n).to_num = m.to_num + n.to_num :=
begin simp [nat.to_num] end

lemma mul_of_nat' {m n : nat} : (m * n).to_num = m.to_num * n.to_num :=
begin simp [nat.to_num] end

lemma mul_to_znum' : ∀ {m n : num}, (m * n).to_znum = m.to_znum * n.to_znum
| 0       0       := rfl
| 0       (pos q) := (zero_mul _).symm
| (pos p) 0       := rfl
| (pos p) (pos q) := 
  begin simp [has_mul.mul, num.mul, to_znum, znum.mul] end


meta instance has_to_format : has_to_format num := 
⟨λ z, to_fmt (z : nat)⟩  

def range (n : num) : list num :=
list.map nat.to_num (list.range (n : nat))

def lcm (m n : num) : num := m * n / (gcd m n)

lemma gcd_one_right (m : num) : gcd m 1 = 1 := 
begin
  rw [cast_inj.symm, gcd_to_nat],
  apply nat.gcd_one_right
end

lemma div_one (n : num) : n / 1 = n :=
begin
  rw [cast_inj.symm, div_to_nat],
  apply nat.div_one
end

lemma cast_inj' {α : Type} [linear_ordered_semiring α] {m n : num} : 
(m : α) ≠ (n : α) ↔ m ≠ n :=
begin
  constructor; intros h hc; 
  [ {rw cast_inj.symm at hc}, {rw cast_inj at hc} ];
  apply h hc,
end

lemma lcm_to_nat {m n : num} :
 ((lcm m n).to_nat) = nat.lcm m.to_nat n.to_nat := 
begin simp [lcm, nat.lcm, to_nat] end

lemma to_znum_nonneg : ∀ (n : num), 0 ≤ n.to_znum := 
begin intro n, cases n; exact_dec_trivial end

lemma lt_to_znum : ∀ {m n : num}, m.to_znum < n.to_znum ↔ m < n 
| 0 0 := begin simp [to_znum], refl end 
| 0 (pos n) := begin constructor; intro h; exact_dec_trivial end
| (pos m) 0 := begin constructor; intro h; cases h end
| (pos m) (pos n) := 
  begin simp [to_znum, has_lt.lt, znum.cmp, cmp] end

lemma mem_range {m n : num} : m ∈ range n ↔ m < n :=
begin
  constructor; intro h,
  { simp [range, mem_map] at h, 
    cases h with k hk, cases hk with h1 h2, subst h2,
    rw [← lt_to_nat, nat.to_num, to_of_nat], apply h1 },
  { simp [range], existsi (m : nat),
    constructor, simp [le_to_nat], apply h, 
    apply of_to_nat } 
end

lemma pos_iff_nonzero :
∀ {m : num}, m > 0 ↔ m ≠ 0 
| 0 := begin simp, exact_dec_trivial end
| (pos m) := begin simp, exact_dec_trivial end

lemma to_znum_pos_iff {m : num} :
  m.to_znum > 0 ↔ m > 0 := 
begin simp [gt], rw ← lt_to_znum, refl end

def comp_sub' : ∀ (as1 as2 : list num), list znum 
| [] [] := [] 
| [] (n::ns) := (to_znum_neg n)::(comp_sub' [] ns) 
| (n::ns) [] := (to_znum n)::(comp_sub' ns []) 
| (n1::ns1) (n2::ns2) := (sub' n1 n2)::(comp_sub' ns1 ns2)

lemma to_znum_to_int_eq' :
∀ {m : num}, m.to_znum.to_int = m.to_nat.to_int :=
  begin
    intro n, have h1 := (@num.cast_to_znum int _ _ _ _ n),
    simp [znum.to_int, num.to_nat, nat.to_int], 
  end

lemma to_znum_to_int_eq :
∀ {m : num}, ((m.to_znum) : int) = m.to_nat.to_int := 
begin
  intro m, rw ← to_znum_to_int_eq', 
  dsimp [znum.to_int], refl,
end

def lcms : list num → num
| [] := 1 
| (z::zs) := lcm z (lcms zs)

end num


namespace znum

open list

meta instance has_to_format : has_to_format znum := 
⟨λ z, to_fmt (z : int)⟩ 

instance inhabited : inhabited znum := ⟨0⟩ 

lemma to_int_to_znum {z : znum} : z.to_int.to_znum = z :=
begin rw ← @cast_inj int _, apply int.to_znum_to_int end

lemma to_nat_to_znum {z : znum} :
0 ≤ z → z.to_nat.to_znum = z :=
begin
  intro h, cases z, refl, simp [to_nat, nat.to_znum],
  rw int.to_nat_to_int, apply to_int_to_znum,
  rw ← le_to_int at h, apply h, exfalso, apply h, exact_dec_trivial
end

lemma mod_def : ∀ (a b : znum), a % b = a - b * (a / b) := 
begin
  intros a b, rw to_int_inj.symm,
  simp [mod_to_int, mul_to_int, int.mod_def]
end

lemma add_le_iff_le_sub {a b c : znum} : a + b ≤ c ↔ a ≤ c - b := 
iff.intro (le_sub_right_of_add_le) (add_le_of_le_sub_right)

lemma lt_of_le_sub_one {a b : znum} (h : a ≤ b - 1) : a < b := 
begin
  rw lt_to_int.symm, simp [le_to_int.symm] at h,
  apply int.lt_of_le_sub_one h,
end

lemma le_sub_one_of_lt : ∀ {a b : znum}, a < b → a ≤ b - 1 :=
begin
  intros a b h, simp [le_to_int.symm],
  rw lt_to_int.symm at h, apply int.le_sub_one_of_lt h,
end

def sign : znum → znum
| (pos _) := 1
| zero    := 0
| (neg _) := -1

def lcm (x y : znum) : znum :=
  (num.lcm (abs x) (abs y)).to_znum

def lcms : list znum → znum
| [] := 1 
| (z::zs) := lcm z (lcms zs)

lemma lcm_to_int {x y} : to_int (lcm x y) = int.lcm (to_int x) (to_int y) := 
begin
  simp [lcm, int.lcm], repeat {rw ← abs_to_nat},
  have heq1 : int.nat_abs (to_int x) = (abs x).to_nat, 
  { simp [to_int], rw (abs_to_nat x).symm, 
    simp [num.to_nat] },
  have heq2 : int.nat_abs (to_int y) = (abs y).to_nat, 
  { simp [to_int], rw (abs_to_nat y).symm, 
    simp [num.to_nat] },
  rw [heq1, heq2], rw (num.lcm_to_nat).symm, 
  apply num.to_znum_to_int_eq',
end

lemma lcm_to_int' {x y} : ↑(lcm x y) = int.lcm (to_int x) (to_int y) := lcm_to_int

lemma lcms_to_int :
  ∀ {zs}, (to_int (lcms zs)) = int.lcms (map to_int zs) 
| [] := begin refl end
| (z::zs) := begin simp [lcms, int.lcms, lcm_to_int, lcms_to_int] end

lemma lcms_to_int' :
  ∀ {zs}, ↑(lcms zs) = int.lcms (map to_int zs) := @lcms_to_int

def range (z : znum) : list znum :=
list.map num.to_znum (num.range (abs z))

lemma neg_one_mul_eq_neg {z : znum} : (-1) * z = -z :=
begin cases z; simp end

lemma mul_le_mul_iff_le_of_neg_left (x y z : znum) :
z < 0 → (z * x ≤ z * y ↔ y ≤ x) := 
begin
  rw [← le_to_int, ← le_to_int, ← lt_to_int, mul_to_int, mul_to_int],
  apply int.mul_le_mul_iff_le_of_neg_left,
end

lemma le_of_lt_add_one {a b : znum} : a < b + 1 → a ≤ b :=
begin
  rw [← lt_to_int, ← le_to_int, cast_add],
  apply int.le_of_lt_add_one 
end

lemma add_one_le_of_lt {a b : znum} : a < b → a + 1 ≤ b :=
begin rw [← lt_to_int, ← le_to_int, cast_add], apply int.add_one_le_of_lt end

lemma nonneg_iff_exists (z : znum) :
  0 ≤ z ↔ ∃ (n : num), z = n.to_znum :=
begin
  cases z with m m; constructor; intro h, 
  { existsi (0 : num), refl },
  exact_dec_trivial,
  { existsi (num.pos m), refl}, 
  exact_dec_trivial,
  { exfalso, apply h, exact_dec_trivial }, 
  { cases h with n hn, cases n; cases hn }
end

lemma to_znum_abs : ∀ {a : znum}, a ≥ 0 → (abs a).to_znum = a
| (neg n) h := begin exfalso, apply h, exact_dec_trivial end
| 0       h := rfl
| (pos n) h := rfl

lemma mul_nonzero {z y : znum} : z ≠ 0 → y ≠ 0 → z * y ≠ 0 := 
begin
  intros h1 h2 hc, 
  apply @int.mul_nonzero (z : int) (y : int),
  { intro hc, apply h1, rw cast_inj.symm, apply hc },
  { intro hc, apply h2, rw cast_inj.symm, apply hc },
  { rw [cast_inj.symm, mul_to_int] at hc, apply hc,}
end 

lemma div_one (a : znum) : a / 1 = a :=
begin rw [← @cast_inj int, div_to_int], apply int.div_one end

lemma div_nonzero (z y : znum) : z ≠ 0 → has_dvd.dvd y z → (z / y) ≠ 0 := 
begin
  intros hz hy hc, apply @int.div_nonzero (z : int) (y : int),
  { intro hc, apply hz, rw cast_inj.symm, apply hc },
  { rw dvd_to_int, apply hy },
  { rw [cast_inj.symm, div_to_int] at hc, apply hc }
end

lemma nonzero_of_pos {z : znum} : z > 0 → z ≠ 0 :=
begin
  intro h, cases z, cases h, 
  intro hc, cases hc, intro hc, cases hc,
end

lemma abs_pos_of_nonzero {z : znum} : 
z ≠ 0 → abs z > 0 := 
begin
  intro h, cases z, exfalso, 
  { apply h, refl },
  exact_dec_trivial, exact_dec_trivial
end

lemma lcms_pos {zs : list znum} : (∀ (z : znum), z ∈ zs → z ≠ 0) → lcms zs > 0 :=
begin
  intro h, simp [gt, lt_to_int.symm],
  have hrw := @lcms_to_int zs, simp [to_int] at hrw,
  rw hrw, apply int.lcms_pos, intros z hz hc,
  rw mem_map at hz, cases hz with x hx, cases hx with hx1 hx2,
  subst hx2, apply h _ hx1 _, --simp [to_int] at hc,
  rw cast_inj.symm, apply hc
end

lemma dvd_lcms : ∀ {x : znum} {zs : list znum}, x ∈ zs → x ∣ lcms zs :=
begin
  intros z zs h, rw (dvd_to_int _ _).symm,
  have hrw := @lcms_to_int zs, simp [to_int] at hrw, rw hrw,
  apply int.dvd_lcms, rw mem_map, existsi z,
  apply and.intro h rfl

end

lemma eq_zero_of_abs_eq_zero {z : znum} : abs z = 0 → z = 0 :=
begin intro h, cases z, refl, cases h, cases h end

lemma abs_one : abs 1 = 1 := rfl

lemma exists_lt_and_lt (x y : znum) : ∃ (z : znum), z < x ∧ z < y :=
begin
  cases (int.exists_lt_and_lt x y) with z hz,
  rw [← to_of_int z, lt_to_int, lt_to_int] at hz, 
  existsi z.to_znum, apply hz,
end

lemma neg_to_int {z : znum} :
(-z).to_int = -(z.to_int) :=
begin cases z; simp [to_int] end

lemma neg_to_int' {z : znum} :
↑(-z) = -(z.to_int) := neg_to_int

lemma abs_to_int {z : znum} :
(_root_.abs z).to_int = _root_.abs z.to_int := 
begin
  simp [_root_.abs, abs, to_int, max], 
  by_cases (z ≤ -z),
  { rw [if_pos h], rw (if_pos _), apply neg_to_int,
    have hrw := @neg_to_int z, dsimp [to_int] at hrw, rw ← hrw,
    rw le_to_int, assumption },
  { rw [if_neg h], rw (if_neg _), intro hc, apply h,
    have hrw := @neg_to_int z, dsimp [to_int] at hrw, 
    rw ← le_to_int, rw hrw, assumption }
end

lemma abs_to_int' {z : znum} : ↑(_root_.abs z) = _root_.abs z.to_int := abs_to_int

lemma abs_eq_abs_to_znum (z : znum) :
_root_.abs z = (abs z).to_znum :=
begin
  rw [← (@znum.cast_inj int _)], have hrw := @abs_to_int z, 
  simp [to_int] at hrw, rw hrw, 
  have hrw2 := @num.to_znum_to_int_eq' (abs z),
  dsimp [to_int] at hrw2, rw hrw2,
  rw (int.abs_eq_nat_abs), simp [nat.to_int],
  rw int.coe_nat_eq_coe_nat_iff, simp [num.to_nat],
end

lemma lcms_distrib (xs ys zs : list znum) :
  (zs ≃ xs ∪ ys) → lcms zs = lcm (lcms xs) (lcms ys) :=
begin
  intro h1, rw ← (@cast_inj int _),
  simp [lcms_to_int, lcms_to_int', lcm_to_int'],
  apply int.lcms_distrib, apply equiv.trans,
  { apply list.map_equiv_map_of_equiv h1, },
  { apply list.map_union_equiv }
end

lemma abs_dvd (x y : znum) : _root_.abs x ∣ y ↔ x ∣ y :=
begin rw [← dvd_to_int, ← dvd_to_int, abs_to_int'], apply int.abs_dvd end

-- lemma dvd_lcm_left (x y : znum) : x | lcm x y :=  sorry
-- -- begin rw [← dvd_to_int, lcm_to_int'], apply int.dvd_lcm_left end

lemma dvd_lcm_left (x y : znum) : x ∣ lcm x y := 
begin rw [← dvd_to_int, lcm_to_int'], apply int.dvd_lcm_left end

lemma dvd_lcm_right (x y : znum) : y ∣ lcm x y :=
begin rw [← dvd_to_int, lcm_to_int'], apply int.dvd_lcm_right end

lemma le_mul_of_pos_left {x y : znum} : y ≥ 0 → x > 0 → y ≤ x * y :=
begin
  simp [ge, gt], rw [← le_to_int, ← le_to_int, ← lt_to_int, mul_to_int],
  apply int.le_mul_of_pos_left
end

lemma add_mul_mod_self {a b c : znum} : (a + b * c) % c = a % c :=
begin rw ← @cast_inj int _, simp [mod_to_int] end

lemma exists_min_of_exists_lb {P : znum → Prop} {w : znum} {lb : znum} :
P w → (∀ (x : znum), x < lb → ¬P x) → ∃ (y : znum), P y ∧ ∀ (x : znum), x < y → ¬P x := 
begin
  intros hw hlb,
  have h := @int.exists_min_of_exists_lb 
    (λ (z : int), P z.to_znum) w.to_int lb.to_int _ _,
  { cases h with k hk, cases hk with hk1 hk2, existsi k.to_znum,
    constructor, apply hk1, intros m hm1 hm2, apply (hk2 m.to_int _ _), 
    { rw ← lt_to_int at hm1, simp [int.to_znum] at hm1, apply hm1 },
    { simp [int.to_znum, to_int], apply hm2 } },
    { simp [int.to_znum, to_int], apply hw } ,
  { intros k hk1 hk2, apply hlb k.to_znum _ hk2,
    rw ← lt_to_int, simp [int.to_znum], apply hk1 }
end

lemma mod_nonneg (a : znum) {b : znum} : b ≠ 0 → a % b ≥ 0 :=
begin
  simp [ne, ge], rw [← @cast_inj int _, ← le_to_int, mod_to_int], 
  apply int.mod_nonneg,
end

lemma mod_lt (a : znum) {b : znum} : b ≠ 0 → a % b < _root_.abs b :=
begin
  simp [ne], rw [← @cast_inj int _, ← lt_to_int, 
    mod_to_int, abs_to_int'], apply int.mod_lt, 
end

lemma lt_irrefl (a : znum) : ¬ a < a :=
begin rw ← lt_to_int, apply int.lt_irrefl end

lemma div_mul_cancel {a b : znum} (h : b ∣ a) : a / b * b = a :=
begin
  rw [← (@cast_inj int _), mul_to_int, div_to_int],
  apply int.div_mul_cancel, rw dvd_to_int, apply h
end

lemma div_mul_comm (x y z : znum) : 
has_dvd.dvd y x → (x / y) * z = x * z / y := 
begin
  rw [ ← dvd_to_int, ← @cast_inj int _, mul_to_int, div_to_int,
       div_to_int, mul_to_int], apply int.div_mul_comm
end

lemma sign_to_int' {z : znum} :
to_int (sign z) = int.sign z.to_int := 
begin
  cases z, refl,
  { rw (int.sign_eq_one_of_pos _), refl,
    have hgt : 0 < pos z, exact_dec_trivial,
    rw ← lt_to_int at hgt, apply hgt },
  { rw (int.sign_eq_neg_one_of_neg _), refl,
    have hlt : neg z < 0, exact_dec_trivial,
    rw ← lt_to_int at hlt, apply hlt }
end

lemma sign_to_int {z : znum} :
↑(sign z) = int.sign z.to_int := sign_to_int'

theorem sign_eq_one_of_pos {a : znum} (h : 0 < a) : sign a = 1 :=
begin
  rw [ ← @cast_inj int _, sign_to_int], 
  apply int.sign_eq_one_of_pos, rw ← lt_to_int at h, apply h
end

theorem sign_eq_zero_iff_zero (a : znum) : sign a = 0 ↔ a = 0 :=
begin
  rw [ ← @cast_inj int _, ← @cast_inj int _, sign_to_int], 
  apply int.sign_eq_zero_iff_zero
end

lemma sign_eq_neg_one_of_neg {a : znum} (h : a < 0) : sign a = -1 :=
begin
  rw [ ← @cast_inj int _, neg_to_int', sign_to_int], 
  apply int.sign_eq_neg_one_of_neg, rw ← lt_to_int at h, apply h
end

lemma sign_eq_div_abs (a : znum) : sign a = a / (_root_.abs a) :=
begin
  rw [ ← @cast_inj int _, sign_to_int, div_to_int, abs_to_int'], 
  apply int.sign_eq_div_abs
end

lemma mul_div_assoc (a b c : znum) : c ∣ b → (a * b) / c = a * (b / c) :=
begin
  rw [← dvd_to_int, ← @cast_inj int, mul_to_int],
  rw [div_to_int, div_to_int, mul_to_int], apply int.mul_div_assoc
end


lemma mul_le_mul_iff_le_of_pos_left (x y z : znum) :
  z > 0 → (z * x ≤ z * y ↔ x ≤ y) := 
begin
  simp [gt], rw [← lt_to_int, ← le_to_int, ← le_to_int,
    mul_to_int, mul_to_int], apply int.mul_le_mul_iff_le_of_pos_left,
end

lemma div_pos_of_pos_of_dvd {a b : znum} : 
a > 0 → b ≥ 0 → b ∣ a → a / b > 0 :=
begin
  simp [ge, gt], 
  rw [← lt_to_int, ← lt_to_int, ← le_to_int, ← dvd_to_int, div_to_int],
  apply int.div_pos_of_pos_of_dvd,
end

lemma eq_to_int {x y : znum} : 
x.to_int = y.to_int ↔ x = y :=
begin rw ← @cast_inj int, refl end

lemma mul_to_int' {x y : znum} : 
(x * y).to_int = x.to_int * y.to_int :=
begin simp [to_int] end

lemma add_to_int {x y : znum} : 
(x + y).to_int = x.to_int + y.to_int :=
begin simp [to_int] end

lemma div_to_int' {x y : znum} : 
(x / y).to_int = x.to_int / y.to_int :=
begin simp [to_int] end

lemma ne_to_int {x y : znum} : 
x.to_int ≠ y.to_int ↔ x ≠ y :=
begin simp [to_int] end

lemma mul_div_cancel_left {a : znum} (b : znum) (h : a ≠ 0) : a * b / a = b :=
begin
  rw [← eq_to_int, div_to_int', mul_to_int'],
  apply int.mul_div_cancel_left, rw ← ne_to_int at h, apply h
end

lemma dvd_to_int' {m n : znum} : 
has_dvd.dvd m.to_int n.to_int ↔ has_dvd.dvd m n :=
begin simp [to_int] end

lemma dvd_iff_exists (x y) :
  has_dvd.dvd x y ↔ ∃ (z : znum), z * x = y := 
begin
  constructor; intro h,
  { rw [← dvd_to_int, int.dvd_iff_exists] at h,
    cases h with z hz, existsi z.to_znum,
    rw [← eq_to_int, mul_to_int', int.to_znum_to_int], 
    apply hz },
  { cases h with z hz, 
    rw [← eq_to_int, mul_to_int'] at hz,
    rw [← dvd_to_int', int.dvd_iff_exists],
    existsi z.to_int, apply hz }
end

lemma sign_trichotomy (z : znum) : 
  sign z = -1 ∨ sign z = 0 ∨ sign z = 1 :=
begin
  repeat {rw [← eq_to_int]},
  repeat {rw [sign_to_int']},
  apply int.sign_trichotomy
end

lemma le_to_int' {m n : znum} : m.to_int ≤ n.to_int ↔ m ≤ n :=
begin simp [to_int] end

lemma lt_to_int' {m n : znum} : m.to_int < n.to_int ↔ m < n :=
begin simp [to_int] end

lemma add_one_le_iff {a b : znum} : a + 1 ≤ b ↔ a < b := 
begin
  rw [← le_to_int, ← lt_to_int, cast_add],
  apply int.add_one_le_iff, 
end

lemma eq_one_or_eq_neg_one_of_mul_eq_one_left {a b : znum} (h : a * b = 1) : b = 1 ∨ b = -1 :=
begin
  rw [← @cast_inj int, ← @cast_inj int, neg_to_int'],
  simp [to_int], rw [← @cast_inj int, mul_to_int] at h,
  apply int.eq_one_or_eq_neg_one_of_mul_eq_one_left h
end

lemma eq_one_or_eq_neg_one_of_mul_eq_neg_one_left {a b : znum} (h : a * b = -1) : b = 1 ∨ b = -1 :=
begin
  rw [← @cast_inj int, ← @cast_inj int, neg_to_int'],
  simp [to_int], rw [← @cast_inj int, mul_to_int, neg_to_int'] at h,
  simp [to_int] at h, apply int.eq_one_or_eq_neg_one_of_mul_eq_neg_one_left h
end

end znum

lemma int.le_to_znum {x y : int} :
x.to_znum ≤ y.to_znum ↔ x ≤ y := 
begin rw [← znum.le_to_int', int.to_znum_to_int, int.to_znum_to_int] end

lemma nat.to_znum_nonneg {n : nat} : 0 ≤ n.to_znum :=
begin 
  simp [nat.to_znum], rw [← znum.le_to_int', int.to_znum_to_int],
  apply nat.to_int_nonneg
end

namespace num

lemma le_to_nat' {m n : num} : m.to_nat ≤ n.to_nat ↔ m ≤ n :=
begin simp [to_nat] end

lemma le_to_znum' {m n : num} : m.to_znum ≤ n.to_znum ↔ m ≤ n :=
begin
  rw [← znum.le_to_int', to_znum_to_int_eq', 
    to_znum_to_int_eq', ← le_to_nat'], apply nat.le_to_int',
end

lemma add_to_nat' : ∀ {m n : num}, (m + n).to_nat = m.to_nat + n.to_nat :=
begin simp [to_nat] end

lemma add_to_znum' : ∀ {m n : num}, (m + n).to_znum = m.to_znum + n.to_znum :=
begin
  intros m n, rw [← @znum.cast_inj int _, znum.cast_add],
  repeat {rw to_znum_to_int_eq}, rw [add_to_nat', nat.add_to_int']
end

end num