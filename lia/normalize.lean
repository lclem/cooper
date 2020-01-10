import ..logic ..list .preformula .formula -- .has_ptm .has_atom

open list

def preterm_lia.const : preterm_lia → int
| (preterm_lia.var k)     := 0
| (preterm_lia.cst c)     := c
| (preterm_lia.lmul c k)  := 0
| (preterm_lia.rmul k c)  := 0
| (preterm_lia.neg t)     := -t.const
| (preterm_lia.add t1 t2) := t1.const + t2.const
| (preterm_lia.sub t1 t2) := t1.const - t2.const

def preterm_lia.coeffs : preterm_lia → list int
| (preterm_lia.var k)     := update_nth_force [] k 1 0
| (preterm_lia.cst c)     := []
| (preterm_lia.lmul c k)  := update_nth_force [] k c 0
| (preterm_lia.rmul k c)  := update_nth_force [] k c 0
| (preterm_lia.neg t)     := map_neg t.coeffs
| (preterm_lia.add t1 t2) := comp_add t1.coeffs t2.coeffs
| (preterm_lia.sub t1 t2) := comp_sub t1.coeffs t2.coeffs.

def preatom_lia.normalize : preatom_lia → atom
| (preatom_lia.le t1 t2) :=
  atom.le (t1.const - t2.const).to_znum
    (map int.to_znum (comp_sub t2.coeffs t1.coeffs))
| (preatom_lia.dvd d t) :=
  atom.dvd d.to_znum t.const.to_znum (map int.to_znum t.coeffs)
| (preatom_lia.ndvd d t) :=
  atom.ndvd d.to_znum t.const.to_znum (map int.to_znum t.coeffs)

def preformula_lia.normalize : preformula_lia → formula
| preformula_lia.true      := formula.true
| preformula_lia.false     := formula.false
| (preformula_lia.atom a)  := formula.atom a.normalize
| (preformula_lia.not p)   := p.normalize.not
| (preformula_lia.or  p q) := formula.or  p.normalize q.normalize
| (preformula_lia.and p q) := formula.and p.normalize q.normalize
| (preformula_lia.imp p q) := formula.or p.normalize.not q.normalize
| (preformula_lia.iff p q) :=
  formula.or (formula.and p.normalize q.normalize)
    (formula.and p.normalize.not q.normalize.not)
| (preformula_lia.fa p)    := p.normalize.not.ex.not
| (preformula_lia.ex p)    := p.normalize.ex

lemma preterm_lia.eval_eq_aux {z} : ∀ {k zs},
  z * option.iget (nth zs k) = int.dot_prod (update_nth_force nil k z 0) zs
| 0 [] :=
  by simp [int.dot_prod, update_nth_force]
| 0 (z::zs) :=
  begin
    simp [nth, update_nth_force,
    int.dot_prod, int.nil_dot_prod]
  end
| (k+1) [] :=
  by simp [int.dot_prod, update_nth_force]
| (k+1) (z::zs) :=
  begin simp [nth, update_nth_force, int.dot_prod], apply preterm_lia.eval_eq_aux end

lemma preterm_lia.eval_eq {zs} :
  ∀ (t), preterm_lia.eval zs t = t.const + (int.dot_prod t.coeffs zs)
| (preterm_lia.var k) :=
  begin
    simp [preterm_lia.const, preterm_lia.coeffs, preterm_lia.eval],
          rw preterm_lia.eval_eq_aux.symm, simp [one_mul]
  end
| (preterm_lia.cst c) :=
  begin
    simp [preterm_lia.const, preterm_lia.coeffs,
          preterm_lia.eval, int.nil_dot_prod]
  end
| (preterm_lia.lmul k z) :=
  begin
    simp [preterm_lia.const, preterm_lia.coeffs, preterm_lia.eval],
    apply preterm_lia.eval_eq_aux
  end
| (preterm_lia.rmul z k) :=
  begin
    simp [preterm_lia.const, preterm_lia.coeffs, preterm_lia.eval, mul_comm _ k],
    apply preterm_lia.eval_eq_aux
  end
| (preterm_lia.neg t) :=
  begin
    simp [preterm_lia.eval, preterm_lia.const, preterm_lia.coeffs,
    preterm_lia.eval_eq t, neg_add, int.map_neg_dot_prod.symm]
  end
| (preterm_lia.add t1 t2) :=
  begin
    simp [preterm_lia.eval, preterm_lia.const, preterm_lia.coeffs,
    preterm_lia.eval_eq t1, preterm_lia.eval_eq t2, int.comp_add_dot_prod]
  end
| (preterm_lia.sub t1 t2) :=
  begin
    simp [preterm_lia.eval, preterm_lia.const, preterm_lia.coeffs,
    preterm_lia.eval_eq t1, preterm_lia.eval_eq t2, int.comp_sub_dot_prod]
  end

lemma preatom_lia.eval_normalize (zs : list int) :
∀ (p : preatom_lia), p.normalize.eval (map int.to_znum zs) ↔ p.eval zs
| (t1 ≤* t2):=
begin
  simp [preatom_lia.normalize, formula.eval, atom.eval,
    preterm_lia.const, preterm_lia.coeffs, preatom_lia.eval],
  rw [preterm_lia.eval_eq, preterm_lia.eval_eq, ← znum.le_to_int',
    int.to_znum_to_int, znum.dot_prod_to_int'], simp [map],
  have hf : (znum.to_int ∘ int.to_znum) = id,
  { rw function.funext_iff, intro x, simp [znum.to_int, int.to_znum] },
  rw [hf, map_id, map_id, int.comp_sub_dot_prod,
    ← add_sub_assoc, ← int.add_le_iff_le_sub],
end
| (d ∣* t):=
  begin
    simp [preatom_lia.normalize, formula.eval, atom.eval,
      preterm_lia.const, preterm_lia.coeffs, preatom_lia.eval],
    rw [preterm_lia.eval_eq, ← znum.dvd_to_int',
      int.to_znum_to_int, znum.add_to_int,
      int.to_znum_to_int, znum.dot_prod_to_int',
      int.map_to_znum_to_int, int.map_to_znum_to_int]
  end
| (d ∤* t):=
  begin
    simp [preatom_lia.normalize, formula.eval, atom.eval,
      preterm_lia.const, preterm_lia.coeffs, preatom_lia.eval],
    rw [preterm_lia.eval_eq, ← znum.dvd_to_int',
      int.to_znum_to_int, znum.add_to_int,
      int.to_znum_to_int, znum.dot_prod_to_int',
      int.map_to_znum_to_int, int.map_to_znum_to_int]
  end

meta def preformula_lia.eval_normalize_simp :=
`[simp [formula.eval, preformula_lia.eval,
  preformula_lia.normalize, preformula_lia.eval_normalize]] --, preatom_lia.eval_normalize_iff]]

lemma preformula_lia.eval_normalize :
forall {p : preformula_lia} {zs : list int},
  p.normalize.eval (map int.to_znum zs) ↔ p.eval zs
| ⊤* ds := by preformula_lia.eval_normalize_simp
| ⊥* ds := by preformula_lia.eval_normalize_simp
| (A* a) ds :=
  begin
    preformula_lia.eval_normalize_simp,
    apply preatom_lia.eval_normalize
  end
| (¬* φ) ds := begin preformula_lia.eval_normalize_simp end
| (φ ∨* ψ) ds :=
begin preformula_lia.eval_normalize_simp end
| (φ ∧* ψ) ds :=
begin preformula_lia.eval_normalize_simp end
| (φ →* ψ) ds :=
begin
  preformula_lia.eval_normalize_simp,
  simp [@imp_iff_not_or _ _ (classical.dec _)]
end
| (φ ↔* ψ) ds :=
  begin
    preformula_lia.eval_normalize_simp,
    apply iff_iff_and_or_not_and_not.symm,
    apply classical.dec
  end
| (∀* φ) ds :=
  begin
    preformula_lia.eval_normalize_simp, simp [not_not_iff],
    constructor; intros h x,
    { apply preformula_lia.eval_normalize.elim_left, apply h },
    { cases ((int.bijective_to_znum).right x) with a ha,
      subst ha, have h := preformula_lia.eval_normalize.elim_right (h a), apply h }
  end
| (∃* φ) ds :=
  begin
    preformula_lia.eval_normalize_simp,
    constructor; intro h; cases h with x hx,
    { cases ((int.bijective_to_znum).right x) with a ha,
      subst ha, existsi a, apply preformula_lia.eval_normalize.elim_left, apply hx },
    { existsi (x.to_znum),
      have h := preformula_lia.eval_normalize.elim_right hx, apply h }
  end

meta def normalize : tactic unit :=
pexact ``(preformula_lia.eval_normalize.elim_left _)
