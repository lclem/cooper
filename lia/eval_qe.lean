import .nnf .qfree_sqe .wf_sqe .eval_sqe

def qe : formula → formula
| (p ∧' q) := and_o (qe p) (qe q)
| (p ∨' q) := or_o  (qe p) (qe q)
| (¬' p) := not_o (qe p)
| (∃' p) := sqe (nnf (qe p))
| p := p

lemma qfree_qe :
  ∀ {f : formula}, qfree (qe f) :=
λ f, formula.rec_on f trivial trivial
  (λ a, trivial)
  (λ f1 f2 h1 h2, qfree_and_o h1 h2)
  (λ f1 f2 h1 h2, qfree_or_o  h1 h2)
  (λ f1 h, qfree_not_o h)
  (λ f1 h, begin simp [qe], apply qfree_sqe (nqfree_nnf h) end)

lemma wf_qe :
  ∀ {φ : formula}, formula.wf φ → formula.wf (qe φ) 
| ⊤' h := by trivial
| ⊥' h := by trivial
| (A' a) h := by apply h
| (p ∧' q) h := 
  begin 
    cases h with hp hq, simp [qe], 
    apply wf_and_o; apply wf_qe; assumption  
  end
| (p ∨' q) h := 
  begin 
    cases h with hp hq, simp [qe], 
    apply wf_or_o; apply wf_qe; assumption  
  end
| (¬' p) h := 
  begin 
    simp [qe], apply cases_not_o;
    try {trivial}, simp [formula.wf], apply @wf_qe p h
  end
| (∃' p) h := 
  begin
    simp [qe], apply wf_sqe,
    apply wf_nnf qfree_qe (wf_qe _), apply h,
  end

lemma eval_qe : 
  ∀ {φ : formula}, φ.wf → ∀ {xs}, (qe φ).eval xs ↔ φ.eval xs 
| ⊤' _ xs := begin simp [formula.eval] end
| ⊥' _ xs := begin simp [formula.eval], intro hc, cases hc end
| (A' a) _ xs := begin simp [formula.eval, qe] end
| (¬' φ) h xs := 
  begin simp [qe, eval_not_o, eval_not, @eval_qe φ h] end
| (φ ∨' ψ) h xs := 
  by simp [qe, eval_or_o, eval_or,
           @eval_qe φ h.left, @eval_qe ψ h.right] 
| (φ ∧' ψ) h xs := 
  by simp [qe, eval_and_o, eval_and,
           @eval_qe φ h.left, @eval_qe ψ h.right] 
| (∃' p) h xs := 
  begin
    simp [qe, eval_ex],
    apply iff.trans (eval_sqe _ _),
    { apply exists_iff_exists, intro x,
      apply iff.trans (eval_nnf _),
      apply @eval_qe p h, apply qfree_qe },
    { apply nqfree_nnf, apply qfree_qe },
    { apply wf_nnf qfree_qe (wf_qe _), apply h}
  end

def dec_eval_of_qfree :
  ∀ (φ : formula), qfree φ → ∀ (ds), decidable (φ.eval ds) 
| ⊤' h _ := decidable.true 
| ⊥' h _ := decidable.false 
| (A' a) h _ := begin simp [formula.eval], apply_instance end
| (¬' p) h _ := 
  begin apply @not.decidable _ (dec_eval_of_qfree _ _ _), apply h end
| (p ∧' q) h _ := 
  @and.decidable _ _ 
  (dec_eval_of_qfree _ h.left _) 
  (dec_eval_of_qfree _ h.right _) 
| (p ∨' q) h _ := 
  @or.decidable _ _ 
  (dec_eval_of_qfree _ h.left _) 
  (dec_eval_of_qfree _ h.right _) 
| (∃' p) h _ := by cases h

instance dec_eval_qe (φ : formula) (zs : list znum) : decidable ((qe φ).eval zs) :=
dec_eval_of_qfree _ qfree_qe _

meta def quant_elim : tactic unit :=
pexact ``((eval_qe _).elim_left _)