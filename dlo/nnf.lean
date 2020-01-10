import ..logic .qfree .remove_neg 

-- Requires : nqfree arg
-- Ensures : nqfree ret
def push_neg : formula_dlo → formula_dlo
| ⊤' := ⊥'  
| ⊥' := ⊤' 
| (A' a) := remove_neg a
| (¬' p) := ⊥'
| (p ∨' q) := push_neg p ∧' push_neg q
| (p ∧' q) := push_neg p ∨' push_neg q
| (∃' p) := ⊥' 

lemma nqfree_push_neg : 
  ∀ {p : formula_dlo}, nqfree p → nqfree (push_neg p) 
| ⊤' h := trivial
| ⊥' h := trivial
| (A' a) h := 
  begin cases a; simp [push_neg, remove_neg, nqfree] end
| (¬' p) h := by cases h
| (p ∨' q) h := begin cases h, constructor; apply nqfree_push_neg; assumption end
| (p ∧' q) h := begin cases h, constructor; apply nqfree_push_neg; assumption end
| (∃' p) h := by cases h

-- Requires : qfree arg
-- Ensures : nqfree ret
def nnf : formula_dlo → formula_dlo
| (formula_dlo.true) := ⊤'  
| (formula_dlo.false) := ⊥' 
| (formula_dlo.atom a) := A' a
| (formula_dlo.not p) := push_neg (nnf p)
| (formula_dlo.or p q) := formula_dlo.or (nnf p) (nnf q)
| (formula_dlo.and p q) := formula_dlo.and (nnf p) (nnf q)
| (formula_dlo.ex p) := ⊥'

lemma nqfree_nnf : 
  ∀ {p : formula_dlo}, qfree p → nqfree (nnf p) 
| ⊤' _ := trivial
| ⊥' _ := trivial
| (A' _) _ := trivial
| (¬' p) h := 
  begin apply nqfree_push_neg (nqfree_nnf _), apply h end
| (p ∧' q) h := 
  begin 
    cases h, simp [nnf], constructor; 
    apply nqfree_nnf; assumption 
  end
| (p ∨' q) h := 
  begin 
    cases h, simp [nnf], constructor; 
    apply nqfree_nnf; assumption 
  end

lemma eval_push_neg  : 
  ∀ {p : formula_dlo}, nqfree p → 
    ∀ {xs : list rat}, (push_neg p).eval xs ↔ ¬ (p.eval xs) 
| ⊤' h xs := begin simp [push_neg, formula_dlo.eval] end
| ⊥' h xs := begin simp [push_neg, formula_dlo.eval] end
| (A' a) h xs := 
  begin 
    simp [push_neg, formula_dlo.eval],
    apply eval_remove_neg,
  end
| (p ∧' q) h xs := 
  begin
    cases h, simp only [push_neg, formula_dlo.eval, eval_not_and], 
    rw (@not_and_distrib _ _ (classical.dec _)),
    apply or_iff_or; apply eval_push_neg; assumption
  end
| (p ∨' q) h xs := 
  begin
    cases h, simp only [push_neg, formula_dlo.eval, not_or_distrib], 
    apply and_iff_and; apply eval_push_neg; assumption
  end

lemma eval_nnf  : 
  ∀ {p : formula_dlo}, qfree p → 
    ∀ {xs : list rat}, ((nnf p).eval xs ↔ p.eval xs) 
| ⊤' hf xs := iff.refl _
| ⊥' hf xs := iff.refl _
| (A' a) h xs := iff.refl _
| (¬' p) h xs := 
  begin
    simp [nnf, formula_dlo.eval],
    rw eval_push_neg (nqfree_nnf _),
    rw eval_nnf, apply h, apply h
  end
| (p ∧' q) hf xs := 
  begin
    cases hf, simp [nnf, formula_dlo.eval],
    apply and_iff_and; apply eval_nnf; assumption
  end
| (p ∨' q) hf xs := 
  begin
    cases hf, simp [nnf, formula_dlo.eval],
    apply or_iff_or; apply eval_nnf; assumption
  end