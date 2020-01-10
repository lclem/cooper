import .sqe .qfree

open list

lemma nqfree_map_unify {z} : 
  ∀ {p : formula}, nqfree p → nqfree (p.map (atom.unify z)) 
| ⊤' h       := by unfold formula.map
| ⊥' h       := by unfold formula.map
| (A' _) h   := by unfold formula.map
| (p ∧' q) h := 
  begin
    unfold formula.map, cases h, constructor; 
    apply nqfree_map_unify; assumption
  end
| (p ∨' q) h := 
  begin
    unfold formula.map, cases h, constructor; 
    apply nqfree_map_unify; assumption
  end
| (¬' _) h   := by cases h
| (∃' _) h   := by unfold formula.map


lemma nqfree_unify : 
  ∀ {p}, nqfree p → nqfree p.unify :=
begin
  intros p h, unfold formula.unify, 
  apply and.intro, trivial, 
  apply nqfree_map_unify h
end

lemma qfree_subst_of_qfree (i ks) : 
  ∀ p, qfree p → qfree (subst i ks p) 
| ⊤' h := by unfold subst
| ⊥' h := by unfold subst
| (A' a) h := by unfold subst
| (p ∧' q) h := 
  begin
    cases h with hp hq, apply and.intro,
    apply qfree_subst_of_qfree p hp,
    apply qfree_subst_of_qfree q hq
  end
| (p ∨' q) h := 
  begin
    cases h with hp hq, apply and.intro,
    apply qfree_subst_of_qfree p hp,
    apply qfree_subst_of_qfree q hq
  end
| (¬' p) h := qfree_subst_of_qfree p h
| (∃' p) h := by unfold subst

lemma qfree_inf_minus_of_qfree : 
  ∀ p, qfree p → qfree (inf_minus p) 
| ⊤' h := by trivial
| ⊥' h := by trivial
| (A' a) h := 
  begin 
    cases a with k ks; try {trivial}, 
    cases ks with k' ks, trivial, simp [inf_minus], 
    apply ite.rec; intro h, trivial,
    apply ite.rec; intro h; trivial 
  end
| (p ∧' q) h := 
  begin
    cases h with h1 h2, apply cases_and_o; try {trivial};
    try {apply qfree_inf_minus_of_qfree, assumption},
    constructor; {apply qfree_inf_minus_of_qfree, assumption}
  end
| (p ∨' q) h := 
  begin
    cases h with h1 h2, apply cases_or_o; try {trivial};
    try {apply qfree_inf_minus_of_qfree, assumption},
    constructor; {apply qfree_inf_minus_of_qfree, assumption}
  end
| (¬' p) h := by assumption
| (∃' p) h := by assumption

lemma qfree_sqe_core : ∀ {φ}, nqfree φ → qfree (sqe_core φ) := 
begin
  intros p hp, simp [sqe_core, sqe_inf, sqe_bnd], 
  apply qfree_or_o; apply qfree_disj,
 { intros q hq, rw mem_map at hq,
   cases hq with z hz, cases hz with hz1 hz2,
   subst hz2, apply qfree_subst_of_qfree,
   apply qfree_inf_minus_of_qfree,
   apply qfree_of_nqfree hp },
 { intros q hq, rw mem_map at hq,
   cases hq with z hz, cases hz with hz1 hz2,
   subst hz2, apply qfree_disj,
   intros a ha, rw mem_map at ha,
   cases ha with k hk, cases hk with hk1 hk2, 
   subst hk2, apply qfree_subst_of_qfree,
   apply qfree_of_nqfree hp }
end

lemma qfree_sqe : ∀ {φ}, nqfree φ → qfree (sqe φ) :=
begin
  unfold sqe, intros p h, apply qfree_sqe_core,
  apply nqfree_unify, apply h
end
