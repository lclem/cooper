import  data.nat.gcd data.int.basic

namespace nat

lemma gt_zero_of_ne_zero (n) : n ≠ 0 → n > 0 :=
begin
  intro h, cases n, exfalso, apply h, refl,
  apply nat.zero_lt_succ
end

lemma mul_nonzero {m n : nat} : m ≠ 0 → n ≠ 0 → m * n ≠ 0 :=
begin
  intros hm hn hc, apply hm,
  apply eq.trans, apply eq.symm,
  apply nat.mul_div_cancel,
  apply gt_zero_of_ne_zero, apply hn,
  rewrite hc, apply nat.zero_div
end

lemma lcm_nonzero (m n : nat) : m ≠ 0 → n ≠ 0 → (nat.lcm m n) ≠ 0 :=
begin
  intros hm hn hc,
  have h := nat.gcd_mul_lcm m n,
  rewrite hc at h, rewrite mul_zero at h,
  apply nat.mul_nonzero hm hn,
  apply eq.symm h
end

def to_int (n : nat) : int := n

lemma le_to_int' {m n : ℕ} : m.to_int ≤ n.to_int ↔ m ≤ n :=
by simp [to_int]

lemma add_to_int' {m n : ℕ} : (m + n).to_int = m.to_int + n.to_int :=
begin simp [to_int] end

lemma to_int_to_nat {n : nat} : n.to_int.to_nat = n :=
begin simp [to_int] end

end nat
