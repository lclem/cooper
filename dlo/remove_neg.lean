import .formula

open list 

def remove_neg : atom_dlo → formula_dlo
| (t <' s) := (A' (t =' s) ∨' A' (s <' t))
| (t =' s)  := (A' (t <' s) ∨' A' (s <' t))

lemma eval_remove_neg : 
  ∀ (a : atom_dlo) (xs : list rat), 
    (remove_neg a).eval xs ↔ (¬ (a.eval xs)) 
| (t <' s) xs := 
  begin 
    simp [formula_dlo.eval, atom_dlo.eval, remove_neg, 
      le_iff_lt_or_eq, or.comm, eq.symm']
  end
| (t =' s) xs := 
  begin 
    simp [formula_dlo.eval, atom_dlo.eval, remove_neg, le_antisymm_iff], 
    rw [imp_iff_not_or, not_le, or.comm],
  end

  #exit
    simp only [remove_neg, atom_dlo.eval], 
    apply calc 
          (1 - i ≤ znum.dot_prod (map_neg ks) xs) 
        ↔ (-(znum.dot_prod (map_neg ks) xs) ≤ -(1 - i)) : 
          begin apply iff.intro, apply (@neg_le_neg znum _), apply (@le_of_neg_le_neg znum _) end
    ... ↔ (znum.dot_prod ks xs ≤ -(1 - i)) : 
          begin rw [znum.map_neg_dot_prod], simp, end
    ... ↔ (znum.dot_prod ks xs ≤ i - 1) : 
           by rewrite neg_sub
    ... ↔ (znum.dot_prod ks xs < i) : 
          begin
            apply iff.intro,
            apply znum.lt_of_le_sub_one,
            apply znum.le_sub_one_of_lt 
          end
    ... ↔ ¬i ≤ znum.dot_prod ks xs : 
          begin
            apply iff.intro,
            apply not_le_of_gt,
            apply lt_of_not_ge
          end 
  end
| (atom_dlo.dvd d i ks)  xs := by refl
| (atom_dlo.ndvd d i ks) xs := by apply not_not_iff.symm

