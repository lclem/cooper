import ..logic .qfree .wf .remove_neg 

-- Requires : nqfree arg
-- Ensures : nqfree ret
def push_neg : formula → formula
| ⊤' := ⊥'  
| ⊥' := ⊤' 
| (A' a) := A' (remove_neg a)
| (¬' p) := ⊥'
| (p ∨' q) := push_neg p ∧' push_neg q
| (p ∧' q) := push_neg p ∨' push_neg q
| (∃' p) := ⊥' 

lemma nqfree_push_neg : 
  ∀ {p : formula}, nqfree p → nqfree (push_neg p) 
| ⊤' h := trivial
| ⊥' h := trivial
| (A' a) h := trivial
| (¬' p) h := by cases h
| (p ∨' q) h := begin cases h, constructor; apply nqfree_push_neg; assumption end
| (p ∧' q) h := begin cases h, constructor; apply nqfree_push_neg; assumption end
| (∃' p) h := by cases h

-- Requires : qfree arg
-- Ensures : nqfree ret
def nnf : formula → formula
| (formula.true) := ⊤'  
| (formula.false) := ⊥' 
| (formula.atom a) := A' a
| (formula.not p) := push_neg (nnf p)
| (formula.or p q) := formula.or (nnf p) (nnf q)
| (formula.and p q) := formula.and (nnf p) (nnf q)
| (formula.ex p) := ⊥'

lemma nqfree_nnf : 
  ∀ {p : formula}, qfree p → nqfree (nnf p) 
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

lemma wf_push_neg : ∀ {p : formula}, nqfree p → p.wf → (push_neg p).wf 
| ⊤' h1 h2 := trivial
| ⊥' h1 h2 := trivial
| (A' a) h1 h2 := begin apply wf_remove_neg, apply h2 end
| (¬' p) h1 h2 := by cases h1
| (p ∨' q) h1 h2 := 
  begin
    cases h1, cases h2, constructor; 
    apply wf_push_neg; assumption
  end
| (p ∧' q) h1 h2 := 
  begin
    cases h1, cases h2, constructor; 
    apply wf_push_neg; assumption
  end
| (∃' p) h1 h2 := by cases h1

lemma wf_nnf : ∀ {p : formula}, qfree p → p.wf → (nnf p).wf 
| ⊤' h1 h2 := trivial
| ⊥' h1 h2 := trivial
| (A' a) h1 h2 := h2
| (¬' p) h1 h2 := 
  begin 
    apply wf_push_neg (nqfree_nnf _), 
    apply wf_nnf, apply h1, apply h2, apply h1
  end
| (p ∨' q) h1 h2 := 
  begin 
    cases h1, cases h2, constructor; 
    apply wf_nnf; assumption
  end
| (p ∧' q) h1 h2 := 
  begin 
    cases h1, cases h2, constructor; 
    apply wf_nnf; assumption
  end
| (∃' p) h1 h2 := by cases h1

lemma eval_push_neg  : 
  ∀ {p : formula}, nqfree p → 
    ∀ {xs : list znum}, (push_neg p).eval xs ↔ ¬ (p.eval xs) 
| ⊤' h xs := begin simp [push_neg, formula.eval] end
| ⊥' h xs := begin simp [push_neg, formula.eval] end
| (A' a) h xs := 
  begin 
    simp [push_neg, formula.eval],
    apply eval_remove_neg,
  end
| (p ∧' q) h xs := 
  begin
    cases h, simp only [push_neg, formula.eval, eval_not_and], 
    rw (@not_and_distrib _ _ (classical.dec _)),
    apply or_iff_or; apply eval_push_neg; assumption
  end
| (p ∨' q) h xs := 
  begin
    cases h, simp only [push_neg, formula.eval, not_or_distrib], 
    apply and_iff_and; apply eval_push_neg; assumption
  end

lemma eval_nnf  : 
  ∀ {p : formula}, qfree p → 
    ∀ {xs : list znum}, ((nnf p).eval xs ↔ p.eval xs) 
| ⊤' hf xs := iff.refl _
| ⊥' hf xs := iff.refl _
| (A' a) h xs := iff.refl _
| (¬' p) h xs := 
  begin
    simp [nnf, formula.eval],
    rw eval_push_neg (nqfree_nnf _),
    rw eval_nnf, apply h, apply h
  end
| (p ∧' q) hf xs := 
  begin
    cases hf, simp [nnf, formula.eval],
    apply and_iff_and; apply eval_nnf; assumption
  end
| (p ∨' q) hf xs := 
  begin
    cases hf, simp [nnf, formula.eval],
    apply or_iff_or; apply eval_nnf; assumption
  end

#exit
def nnf : formula → formula
| (formula.true) := formula.true  
| (formula.false) := formula.false
| (formula.atom a) := formula.atom a
| (formula.not (formula.true)) := formula.false
| (formula.not (formula.false)) := formula.true 
| (formula.not (formula.atom a)) := formula.atom (remove_neg a)
| (formula.not (formula.not p)) := nnf p
| (formula.not (formula.or p q)) := formula.and (nnf p.not) (nnf q.not)
| (formula.not (formula.and p q)) := formula.or (nnf p.not) (nnf q.not)
| (formula.not (formula.ex p)) := formula.false
| (formula.or p q) := formula.or (nnf p) (nnf q)
| (formula.and p q) := formula.and (nnf p) (nnf q)
| (formula.ex p) := formula.false

| (formula.true) _ _ := and.intro trivial trivial 
| (formula.false) _ _ := and.intro trivial trivial 
| (formula.atom a) _ h := 
  begin
    simp [nnf, formula.wf] at *, apply and.intro h, 
    apply wf_remove_neg h,
  end
| (¬' p) hf hn := 
  begin
    cases (@wf_nnf_core p hf hn),
    simp [nnf], constructor; assumption
  end
| (formula.and p q) hf hn := by wf_nnf_core_tac
| (formula.or  p q) hf hn := by wf_nnf_core_tac

#exit
-- Requires : nqfree arg
-- Ensures : nqfree ret

meta def nqfree_nnf_core_aux := 
`[ cases h with hp hq, simp [nnf, nqfree], 
    cases (nqfree_nnf_core hp),
    cases (nqfree_nnf_core hq),
    constructor; constructor; assumption ]

lemma nqfree_nnf_core : 
  ∀ {p : formula}, qfree p → (nqfree (nnf p) ∧ nqfree (nnf ¬' p))
| ⊤' _ := and.intro trivial trivial
| ⊥' _ := and.intro trivial trivial
| (A' _) _ := begin constructor; simp [nnf] end
| (¬' p) h := 
  begin
    cases (@nqfree_nnf_core p h),
    simp [nnf], constructor; assumption,
  end
| (p ∧' q) h := by nqfree_nnf_core_aux
| (p ∨' q) h := by nqfree_nnf_core_aux

lemma nqfree_nnf  : 
  ∀ {p : formula}, qfree p → nqfree (nnf p) := 
λ p h, (nqfree_nnf_core h).left

meta def wf_nnf_core_tac := 
`[ cases hf with hfp hfq, cases hn with hnp hnq, 
   simp [formula.wf, nnf],
   cases (@wf_nnf_core p hfp hnp), 
   cases (@wf_nnf_core q hfq hnq), 
   constructor; constructor; assumption ]

lemma wf_nnf_core  : 
  ∀ {p : formula}, qfree p → p.wf 
    → (nnf p).wf ∧ (nnf ¬' p).wf 
| (formula.true) _ _ := and.intro trivial trivial 
| (formula.false) _ _ := and.intro trivial trivial 
| (formula.atom a) _ h := 
  begin
    simp [nnf, formula.wf] at *, apply and.intro h, 
    apply wf_remove_neg h,
  end
| (¬' p) hf hn := 
  begin
    cases (@wf_nnf_core p hf hn),
    simp [nnf], constructor; assumption
  end
| (formula.and p q) hf hn := by wf_nnf_core_tac
| (formula.or  p q) hf hn := by wf_nnf_core_tac

lemma wf_nnf  {p : formula} 
(hf : qfree p) (hn : p.wf) : (nnf p).wf :=
(wf_nnf_core hf hn)^.elim_left

open formula

lemma eval_nnf_core  : 
  ∀ {p : formula}, qfree p → 
    ∀ {xs : list znum}, 
      (eval xs (nnf p) ↔ eval xs p) 
    ∧ (eval xs (nnf (¬' p)) ↔ eval xs (¬' p))   
| ⊤' hf xs := and.intro (by refl) (by {simp [nnf, formula.eval]})
| ⊥' hf xs := and.intro (by refl) (by {simp [nnf, formula.eval]})
| (A' a) hf xs := 
  begin 
    apply and.intro; simp [nnf, formula.eval], 
    apply eval_remove_neg,
  end
| (¬' p) hf xs := 
  begin
    cases (@eval_nnf_core p hf xs),
    constructor, assumption,
    simp [nnf, eval_not, left, not_not_iff],
  end
| (p ∧' q) hf xs := 
  begin
    cases (@eval_nnf_core _ hf.left  xs),
    cases (@eval_nnf_core _ hf.right  xs),
    simp [nnf, eval_and], constructor;
    [
      {apply and_iff_and; assumption},
      {
        rw [eval_not, eval_and, @not_and_distrib _ _ (classical.dec _)], 
        simp [eval_or], apply or_iff_or; assumption
      }
    ]
  end
| (p ∨' q) hf xs := 
  begin
    cases (@eval_nnf_core _ hf.left xs),
    cases (@eval_nnf_core _ hf.right xs),
    simp [nnf, eval_and], constructor;
    [
      {apply or_iff_or; assumption},
      {
        rw [eval_not, eval_or, not_or_distrib], 
        apply and_iff_and; assumption
      }
    ]
  end

lemma eval_nnf {p : formula} (h : qfree p) {xs : list znum} : 
  (nnf p).eval xs ↔ p.eval xs := 
(eval_nnf_core h)^.elim_left
