import .formula

def qfree : formula_dlo → Prop
| formula_dlo.true := true
| formula_dlo.false := true
| (formula_dlo.atom _) := true
| (formula_dlo.not p) := qfree p
| (formula_dlo.or  p q) := qfree p /\ qfree q
| (formula_dlo.and p q) := qfree p /\ qfree q
| (formula_dlo.ex p) := false

def nqfree : formula_dlo → Prop
| ⊤' := true
| ⊥' := true
| A' a := true
| (¬' p) := false
| (p ∨' q) := nqfree p ∧ nqfree q
| (p ∧' q) := nqfree p ∧ nqfree q
| (∃' p) := false

lemma qfree_not_o {p : formula_dlo} : qfree p → qfree (not_o p) :=
begin intro h, cases p; try {trivial <|> assumption} end

lemma qfree_and_o {p q : formula_dlo} : qfree p → qfree q → qfree (and_o p q) := 
begin
  intros hp hq, apply cases_and_o; 
  try { trivial <|> assumption }, apply and.intro hp hq
end

lemma qfree_or_o {p q : formula_dlo} : qfree p → qfree q → qfree (or_o p q) := 
begin
  intros hp hq, apply cases_or_o; 
  try { trivial <|> assumption }, apply and.intro hp hq
end

lemma qfree_disj : 
  ∀ {ps : list (formula_dlo)}, (∀ p ∈ ps, qfree p) → qfree (disj ps)  
| [] _ := trivial
| (p::ps) h := 
  have hp : qfree p := h _ (or.inl rfl),
  have hps : qfree (disj ps) := 
    qfree_disj (list.forall_mem_of_forall_mem_cons h),
  begin
    simp [disj], apply cases_or_o; 
    try {simp [qfree], constructor};
    {trivial <|> assumption}
  end

lemma qfree_conj : 
∀ {ps : list (formula_dlo)}, (∀ p ∈ ps, qfree p) → qfree (conj ps)  
| [] _ := trivial
| (p::ps) h := 
  have hp : qfree p := h _ (or.inl rfl),
  have hps : qfree (conj ps) := 
    qfree_conj (list.forall_mem_of_forall_mem_cons h),
  begin 
    simp [conj], apply cases_and_o;
    try {simp [qfree], constructor};
    try {trivial <|> assumption},
  end

lemma qfree_conj_atom :
∀ {as : list atom_dlo}, qfree (conj_atom as) 
| [] := trivial
| (a::as) := qfree_and_o trivial qfree_conj_atom

lemma qfree_of_nqfree : ∀ {p : formula_dlo}, nqfree p → qfree p 
| ⊤' h := trivial
| ⊥' h := trivial
| (A' a) h := trivial
| (¬' p) h := by cases h
| (p ∨' q) h := 
  begin
    cases h with hp hq, apply and.intro; 
    apply qfree_of_nqfree; assumption
  end
| (p ∧' q) h := 
  begin
    cases h with hp hq, apply and.intro; 
    apply qfree_of_nqfree; assumption
  end
| (∃' p) h := by cases h
