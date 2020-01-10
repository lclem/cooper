import data.list.basic .sqe

def atom.wf : atom → Prop 
| (atom.le i ks)     := true
| (atom.dvd d i ks)  := d ≠ 0
| (atom.ndvd d i ks) := d ≠ 0 

instance atom.dec_wf : decidable_pred atom.wf 
| (atom.le i ks)     := decidable.is_true trivial
| (atom.dvd d i ks)  := begin simp [atom.wf], apply_instance end
| (atom.ndvd d i ks) := begin simp [atom.wf], apply_instance end

lemma normal_iff_divisor_nonzero :
  ∀ {a : atom}, a.wf ↔ divisor a ≠ 0 :=
begin intro a, cases a; simp [atom.wf, divisor] end

def formula.wf : formula → Prop 
| ⊤' := true
| ⊥' := true
| (A' a) := atom.wf a 
| (p ∧' q) := formula.wf p ∧ formula.wf q
| (p ∨' q) := formula.wf p ∧ formula.wf q
| (¬' p) := formula.wf p
| (∃' p) := formula.wf p

lemma wf_and_o  {p q : formula} : 
  formula.wf p → formula.wf q → formula.wf (and_o p q) := 
begin
  intros hp hq, apply cases_and_o; try {assumption},
  trivial, constructor; assumption
end

lemma wf_or_o  {p q : formula} : 
  formula.wf p → formula.wf q → formula.wf (or_o p q) := 
begin
  intros hp hq, apply cases_or_o; try {assumption},
  trivial, constructor; assumption
end

def formula.wf_alt (p : formula) := ∀ a ∈ p.atoms, atom.wf a

lemma wf_iff_wf_alt  : 
  ∀ {p : formula}, formula.wf p ↔ formula.wf_alt p 
| ⊤' := begin constructor; intro h, intros a ha, cases ha, trivial end
| ⊥' := begin constructor; intro h, intros a ha, cases ha, trivial end
| (A' a) := 
  begin 
    unfold formula.wf, 
    unfold formula.wf_alt, unfold formula.atoms,
    apply iff.intro; intro h, 
    intros a' ha', cases ha' with he he,
    subst he, apply h, cases he, 
    apply h, apply or.inl rfl
  end
| (p ∧' q) := 
  begin 
    unfold formula.wf, 
    repeat {rewrite wf_iff_wf_alt}, 
    apply iff.symm, apply list.forall_mem_append
  end
| (p ∨' q) := 
  begin 
    unfold formula.wf, 
    repeat {rewrite wf_iff_wf_alt}, 
    apply iff.symm, apply list.forall_mem_append
  end
| (¬' p) := 
  begin 
    unfold formula.wf, 
    rewrite wf_iff_wf_alt, refl
  end
| (∃' p) := by {simp [formula.wf, wf_iff_wf_alt], refl}

lemma wf_disj  : 
  ∀ {ps : list (formula)}, (∀ p ∈ ps, formula.wf p) → formula.wf (disj ps)  
| [] _ := trivial
| (p::ps) h := 
  have hp : formula.wf p := h _ (or.inl rfl),
  have hps : formula.wf (disj ps) := 
    wf_disj (list.forall_mem_of_forall_mem_cons h),
  begin
    simp [disj], apply cases_or_o; 
    try {simp [formula.wf], constructor};
    {trivial <|> assumption}
  end

lemma wf_conj  : 
  ∀ {ps : list (formula)}, (∀ p ∈ ps, formula.wf p) → formula.wf (conj ps)  
| [] _ := trivial
| (p::ps) h := 
  have hp : formula.wf p := h _ (or.inl rfl),
  have hps : formula.wf (conj ps) := 
    wf_conj (list.forall_mem_of_forall_mem_cons h),
  begin
    simp [conj], apply cases_and_o; 
    try {simp [formula.wf], constructor};
    {trivial <|> assumption}
  end

lemma wf_conj_atom  : 
  ∀ {ps : list atom}, (∀ p ∈ ps, atom.wf p) → formula.wf (conj_atom ps)
| [] h := trivial
| (a::as) h := 
  begin
    simp [conj_atom], apply wf_and_o,
    apply (h _ (or.inl rfl)), apply wf_conj_atom, 
    apply list.forall_mem_of_forall_mem_cons h
  end

instance formula.dec_wf  : decidable_pred formula.wf 
| ⊤' := decidable.is_true trivial 
| ⊥' := decidable.is_true trivial 
| (A' a) := begin unfold formula.wf, apply_instance end
| (p ∧' q) := 
  begin
    unfold formula.wf, 
    apply @and.decidable _ _ _ _;
    apply formula.dec_wf
  end
| (p ∨' q) :=
  begin
    unfold formula.wf, 
    apply @and.decidable _ _ _ _;
    apply formula.dec_wf
  end
| (¬' p) := begin unfold formula.wf, apply formula.dec_wf end
| (∃' p) := begin unfold formula.wf, apply formula.dec_wf end