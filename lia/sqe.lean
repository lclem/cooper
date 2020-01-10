import .formula .asubst 

variables {α β : Type}

open list atom tactic

def formula.atoms : formula → list atom
| ⊤' := [] 
| ⊥' := [] 
| (A' a) := [a]
| (¬' p) := p.atoms
| (p ∨' q) := p.atoms ++ q.atoms
| (p ∧' q) := p.atoms ++ q.atoms
| (∃' p) := p.atoms

def head_coeff : atom → znum 
| (le i [])         := 0
| (le i (k::_))     := k
| (dvd d i [])      := 0
| (dvd d i (k::_))  := k
| (ndvd d i [])     := 0
| (ndvd d i (k::_)) := k

def dep_0 (a : atom) := head_coeff a ≠ 0

instance dec_dep_0 : decidable_pred dep_0 :=
begin intro a, cases a; simp [dep_0, head_coeff]; apply_instance end

def formula.atoms_dep_0 (p : formula) : list atom := 
p.atoms.filter dep_0

def atom.unify : znum → atom → atom 
| m (atom.le i (k::ks)) := 
  if k = 0 
  then (atom.le i (0::ks))  
  else let m' := (m / (abs k)) in 
       atom.le (m' * i) (znum.sign k :: map_mul m' ks)
| m (atom.dvd d i (k::ks)) :=
  if k = 0 
  then (atom.dvd d i (0::ks)) 
  else let m' := (m / k) in 
       atom.dvd (m' * d) (m' * i) (1 :: map_mul m' ks)
| m (atom.ndvd d i (k::ks)) := 
  if k = 0 
  then (atom.ndvd d i (0::ks)) 
  else let m' := (m / k) in 
       atom.ndvd (m' * d) (m' * i) (1 :: map_mul m' ks)
| m (atom.le i []) := (atom.le i [])
| m (atom.dvd d i []) := (atom.dvd d i []) 
| m (atom.ndvd d i []) := (atom.ndvd d i []) 

def coeffs_lcm (p : formula) := 
  znum.lcms (map head_coeff p.atoms_dep_0)

def divisor : atom → znum 
| (atom.le i ks)     := 1
| (atom.dvd d i ks)  := d 
| (atom.ndvd d i ks) := d 


def divisors_lcm (p : formula) := 
  znum.lcms (map divisor (p.atoms_dep_0))

def formula.unify (p : formula) : formula := 
A' (atom.dvd (coeffs_lcm p) 0 [1]) ∧' (p.map (atom.unify (coeffs_lcm p)))

def inf_minus : formula → formula 
| ⊤' := ⊤' 
| ⊥' := ⊥' 
| (A' (atom.le i (k::ks))) := 
  if k < 0 
  then ⊤' 
  else if k > 0
       then ⊥' 
       else A' (atom.le i (0::ks))
| (A' a) := A' a
| (p ∧' q) := and_o (inf_minus p) (inf_minus q)
| (p ∨' q) := or_o (inf_minus p) (inf_minus q)
| (¬' p) := ¬' p
| (∃' p) := ∃' p

lemma inf_minus_le_eq_of_lt {i k ks} : 
  k < 0 → inf_minus (A' (atom.le i (k::ks))) = ⊤' := 
begin intro h, simp [inf_minus], rw if_pos h end

lemma inf_minus_le_eq_of_eq {i ks} : 
  inf_minus (A' (atom.le i (0::ks))) = (A' (atom.le i (0::ks))) := 
begin
  simp [inf_minus], rw if_neg,
  rw if_neg, exact_dec_trivial, exact_dec_trivial
end

lemma inf_minus_le_eq_of_gt {i k ks} : 
  k > 0 → inf_minus (A' (atom.le i (k::ks))) = ⊥' := 
begin 
  intro h, simp [inf_minus], rw if_neg,
  rw if_pos, apply h, rw not_lt, apply le_of_lt h,
end

def inf_minus_le_eq {i k ks} : 
  inf_minus (A' (atom.le i (k::ks))) = 
  if k < 0 
  then ⊤' 
  else if k > 0
       then ⊥' 
       else A' (atom.le i (0::ks)) := rfl

def subst (i ks) (p : formula) := p.map (asubst i ks) 

def get_lb : atom → option (znum × list znum) 
| (atom.le i (k::ks)) :=
  if k > 0 then (i,ks) else none
| (atom.le _ []) := none
| (atom.dvd _ _ _) := none
| (atom.ndvd _ _ _) := none

def bnd_points (p : formula) := 
  filter_map get_lb (p.atoms_dep_0)

lemma bnd_points_le_eq {i k ks} : 
  k > 0 → bnd_points (A' (atom.le i (k::ks))) = [(i,ks)] :=
begin
  intro h, simp [formula.atoms, bnd_points, 
    formula.atoms_dep_0, dep_0, filter, head_coeff],
  rw if_pos, simp [filter_map, get_lb],
  rw if_pos, refl, assumption, intro hc,
  subst hc, cases h
end

lemma znum.range_neg_eq_range : 
  ∀ {z}, znum.range (-z) = znum.range z :=
begin intro z, cases z; simp [znum.range, znum.abs]; refl end

lemma znum.mem_range {z y : znum} : 
  0 ≤ z → z < y → z ∈ znum.range y := 
begin
  intros hz hzy, have hy : 0 ≤ y := le_of_lt (lt_of_le_of_lt hz hzy), 
  unfold znum.range, rewrite mem_map, rewrite znum.nonneg_iff_exists at hz,
  cases hz with n hn, subst hn, existsi n, apply and.intro _ rfl, 
  rewrite num.mem_range, rewrite iff.symm num.lt_to_znum,
  rw znum.to_znum_abs hy, assumption,
end

lemma znum.mem_range' {z y : znum} : 
  0 ≤ z → z < (abs y) → z ∈ znum.range y := 
begin
  by_cases hy : (0 ≤ y),
  { rw abs_of_nonneg hy, apply znum.mem_range },
  { simp [not_le] at hy, rw abs_of_nonpos (le_of_lt hy),
    rw znum.range_neg_eq_range.symm, apply znum.mem_range }
end

lemma znum.mem_range_iff {x y : znum} : 
   0 ≤ y → (x ∈ znum.range y ↔ (0 ≤ x ∧ x < y)) := 
begin
  intro h1, constructor; intro h2,
  { simp [znum.range] at h2, cases h2 with n hn,
    cases hn with hn1 hn2, subst hn2, constructor,
    apply num.to_znum_nonneg, simp [num.mem_range] at hn1,
    rw num.lt_to_znum.symm at hn1,
    rw znum.to_znum_abs h1 at hn1, assumption },
  { apply znum.mem_range h2.left h2.right } 
end

def sqe_inf (p : formula) : formula := 
  disj_map (znum.range (divisors_lcm p)) (λ n, subst n [] (inf_minus p)) 

def sqe_bnd  (p : formula) : formula := 
  disj_map (bnd_points p) 
   (λ iks, disj_map (znum.range (divisors_lcm p)) 
     (λ n, subst (iks^.fst + n) (map_neg iks^.snd) p))

def sqe_core (p : formula) : formula := 
  or_o (sqe_inf p) (sqe_bnd p)

def sqe (p : formula) : formula := sqe_core p.unify
