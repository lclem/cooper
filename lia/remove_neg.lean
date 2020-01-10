import .wf

open list 

def remove_neg : atom → atom
| (atom.le i ks) := atom.le (1 - i) (map_neg ks)
| (atom.dvd d i ks)  := atom.ndvd d i ks
| (atom.ndvd d i ks) := atom.dvd d i ks

meta def neg_prsv_normal_aux :=
  `[unfold remove_neg at hb, 
    rewrite (eq_of_mem_singleton hb), trivial]

lemma wf_remove_neg : ∀ {a : atom}, a.wf → (remove_neg a).wf
| (atom.le i ks)     h := begin simp [remove_neg] end
| (atom.dvd d i ks)  h := begin simp [remove_neg], apply h end
| (atom.ndvd d i ks) h := begin simp [remove_neg], apply h end

lemma eval_remove_neg : 
  ∀ (a : atom) (xs : list znum), 
    (remove_neg a).eval xs ↔ (¬ (a.eval xs)) 
| (atom.le i ks) xs := 
  begin 
    simp only [remove_neg, atom.eval], 
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
| (atom.dvd d i ks)  xs := by refl
| (atom.ndvd d i ks) xs := by apply not_not_iff.symm

