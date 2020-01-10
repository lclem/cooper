import ..list .sqe .dnf

variable {α : Type}
-- import .axms_eq ..dnf.basic ..has_dec_aval

-- namespace dnf
-- 
-- open list has_atom_dlo axms axms_eq dnf

-- class has_sqe_eq (α : Type) extends axms_eq α  :=
-- 
-- -- Requires : all args are normal 
-- -- Requires : all args are unified 
-- -- Requires : all args are nontrivial 
-- -- Requires : all args are nonsolutions 
-- (sqe : list atom_dlo → list atom_dlo)   
-- -- (qfree_sqe : ∀ {as : list atom_dlo}, --(∀ a ∈ as, dep_0 a) → qfree (sqe as))
-- (forall_mem_sqe_normal : ∀ {as : list atom_dlo}, (∀ a ∈ as, normal a) → (∀ a ∈ (sqe as), normal a))
-- (eval_sqe_iff : ∀ {as : list atom_dlo}, 
--   (∀ a ∈ as, normal a) → 
--   (∀ a ∈ as, dep_0 a) → 
--   (∀ a ∈ as, ¬ trv a) → 
--   (∀ a ∈ as, ¬ solv_0 a) → 
--   ∀ {bs : list α}, (avals bs (sqe as) ↔ ∃ (x : α), avals (x::bs) as))
-- 
open list


def sqe_eq (as : list atom_dlo) : list (atom_dlo) := 
  match find (solv_0) as with 
  | none := sqe as
  | some eq := map (atom_dlo.subst_0 eq) as
  end

-- lemma forall_mem_sqe_eq_normal {as : list (atom_dlo)} : 
-- (∀ a ∈ as, normal a) → -- (∀ a ∈ as, dep_0 a) → 
--   ∀ a ∈ (sqe_eq as), normal a := 
-- begin
--   intros h1 a ha, simp [sqe_eq] at ha,
--   cases (find (solv_0) as); simp [sqe_eq] at ha,
--   { apply forall_mem_sqe_normal h1 _ ha },
--   { cases ha with x hx, cases hx, subst hx_right,
--     apply normal_subst, apply h1 _ hx_left }
-- end

lemma option.dest :
 ∀ (x : option α), x = none ∨ ∃ a, x = (some a) 
| none := or.inl rfl
| (some a) := or.inr (begin existsi a, refl end)

lemma forall_mem_filter_nontrv_eval {as : list (atom_dlo)} {bs : list rat} :
  (∀ a ∈ (as.filter (λ x, ¬ trv x)), a.eval bs) ↔ (∀ a ∈ as, atom_dlo.eval bs a) := 
begin
  constructor; intros h a ha,
  { by_cases ht : (trv a), apply of_trv ht,
    apply h a _, rw mem_filter, constructor; assumption },
  { apply h _ (mem_of_mem_filter ha) }
end

lemma eval_sqe_eq_iff :
∀ {as : list (atom_dlo)}, 
  -- (∀ a ∈ as, normal a) → 
  (∀ a ∈ as, dep_0 a) → (∀ a ∈ as, ¬ trv a) 
  → ∀ {bs : list rat}, ((avals bs (sqe_eq as)) ↔ (∃ x, avals (x::bs) as)) :=
begin
  intros as has2 has3 bs, simp [sqe_eq],
  cases 
    (option.dest (list.find (solv_0) as)) with heq heq,
    { rw heq, simp [sqe_eq], 
      apply eval_sqe has2,
      rw list.find_eq_none at heq, apply heq },
    {
      cases heq with eq heq, rw heq, simp [sqe_eq], 
      have heq1 : solv_0 eq := list.find_some heq,
      have heq2 : eq ∈ as := list.find_mem heq,
      have heq3 : ¬ trv eq := has3 _ heq2, 
      constructor; intro h,
      { cases (of_solv_0 heq1) with b hb,
        existsi b, intros a ha,
        apply (eval_subst_0_iff heq1 heq3 hb).elim_left,
        apply h, apply mem_map_of_mem _ ha },
      { cases h with b hb, intros a ha, rw mem_map at ha,
        cases ha with a' ha', cases ha' with ha1' ha2', subst ha2', 
        rw (eval_subst_0_iff heq1 heq3 (hb _ heq2)), apply hb _ ha1' }
    }
end 

def sqe_opt (as : list (atom_dlo)) : list (atom_dlo) :=
let as1 := as.filter (λ a, dep_0 a ∧ ¬ trv a) in 
let as2 := as.filter (λ a, ¬ dep_0 a ∧ ¬ trv a) in 
(sqe_eq as1) ++ (map atom_dlo.decr_idx as2)

lemma avals_append {bs} {as1 as2 : list atom_dlo} :
avals bs (as1 ++ as2) ↔ (avals bs as1 ∧ avals bs as2) :=
begin
  simp [avals, forall_mem_append], constructor; intros h, 
  { constructor; intros a ha; apply h, apply or.inl ha,
    apply or.inr ha },
  { intros a ha, cases ha, apply h.left, assumption,
    apply h.right, assumption }
end

lemma eval_sqe_opt_iff {as : list atom_dlo} {bs : list rat} : 
  (avals bs (sqe_opt as)) ↔ (∃ b, avals (b::bs) as) := 
begin
  simp [sqe_opt, avals_append],
  rw ( @eval_sqe_eq_iff (filter (λ a, dep_0 a ∧ ¬trv a) as)
       -- (forall_mem_filter_of_forall_mem hr) 
       (begin intros a ha, rw mem_filter at ha, apply ha.right.left end) 
       (begin intros a ha, rw mem_filter at ha, apply ha.right.right end) bs),
  apply iff.trans 
    exists_and_distrib_right.symm 
    (exists_iff_exists _),
  intro b, constructor; intro h,
  { cases h with h1 h2, intros a ha, 
    by_cases htrv : trv a, 
    { apply of_trv htrv },
    { by_cases (dep_0 a),
      { apply h1, apply mem_filter_of_mem ha, 
        constructor; assumption },
      { rw (atom_dlo.eval_decr_idx_iff h).symm, 
        apply h2, rw mem_map, existsi a, 
        apply and.intro _ rfl,
        apply mem_filter_of_mem ha,
        constructor; assumption, } } },
  { constructor, 
    { intros a ha, apply h _ (mem_of_mem_filter ha) },
    { apply forall_mem_map, intros a ha, rw mem_filter at ha, 
      rw atom_dlo.eval_decr_idx_iff ha.right.left, apply h _ ha.left } }
end

-- lemma qfree_sqe_eq : 
--   ∀ {as : list (atom_dlo)}, (∀ a ∈ as, dep_0 a) → qfree (sqe_eq as) :=
-- begin
--   intros as has, simp [sqe_eq], --simp,
--   cases (list.find (solv_0) as) with pr,
--   { apply qfree_sqe  },
--   { simp [sqe_eq], apply qfree_conj,
--     apply forall_mem_map, intros a ha, trivial }
-- end

--lemma qfree_sqe_opt (as : list (atom_dlo)) : 
--  qfree (sqe_opt as) := 
--begin
--  simp [sqe_opt], apply qfree_and_o,
--  { apply qfree_sqe_eq, simp [of_mem_filter],
--    intros, assumption },
--  { apply qfree_conj, intros p hp,
--    rw mem_map at hp, cases hp with a ha, 
--    cases ha with ha1 ha2, subst ha2, trivial }
--end

def qe : formula_dlo → formula_dlo 
| (formula_dlo.true) := ⊤'
| (formula_dlo.false) := ⊥'
| (formula_dlo.atom a) := A' a
| (formula_dlo.and p q) := (qe p) ∧' (qe q)
| (formula_dlo.or p q) := (qe p) ∨' (qe q)
| (formula_dlo.not p) := ¬'(qe p) 
| (formula_dlo.ex p) := to_frm $ map sqe_opt $ dnf $ qe p 




lemma qfree_qe : ∀ {p : formula_dlo}, qfree (qe p) 
| ⊤' := trivial
| ⊥' := trivial
| (A' _) := trivial
| (¬' p) := begin apply (@qfree_qe p) end
| (p ∧' q) := begin constructor; apply qfree_qe end
| (p ∨' q) := begin constructor; apply qfree_qe end
| (∃' p) := 
  begin
    simp [qe], apply qfree_disj,
    intros q hq, rw mem_map at hq, cases hq with as has,
    cases has with has1 has2, subst has2, apply qfree_conj_atom
  end

-- lemma forall_mem_sqe_opt_normal :
--   ∀ {as : list (atom_dlo)}, (∀ a ∈ as, normal a) → (∀ a ∈ (sqe_opt as), normal a) := 
-- begin
--   intros as has a ha1, 
--   
--   simp [sqe_opt] at ha1, cases ha1, 
--   { apply forall_mem_sqe_eq_normal _ _ ha1, 
--     intros a ha2, apply has,
--     apply mem_of_mem_filter ha2 },
--   { cases ha1 with x hx, cases hx, subst hx_right,
--     apply normal_decr_idx, apply has _ hx_left.left }
-- end
-- 
-- lemma fnormal_qe : ∀ {p : formula_dlo}, fnormal p → fnormal (qe p) 
-- | (frm.true α) hnm := trivial
-- | (frm.false α) hnm := trivial
-- | (frm.atom_dlo a) hnm := hnm 
-- | (frm.and p q) hnm := 
--   begin cases hnm, constructor; apply fnormal_qe; assumption end
-- | (frm.or p q) hnm := 
--   begin cases hnm, constructor; apply fnormal_qe; assumption end
-- | (frm.not p) hnm := 
--   begin apply @fnormal_qe p, assumption end
-- | (frm.ex p) hnm := 
--   begin
--    simp [fnormal, to_frm, qe],
--    apply fnormal_disj, apply forall_mem_map,
--    intros as has, apply fnormal_conj_atom_dlo,
--    apply forall_mem_sqe_opt_normal,
--    apply forall_mem_dnf_core_forall_mem_normal _ has,
--    apply nnf.fnormal_dnf _ (fnormal_qe _),
--    apply qfree_qe, apply hnm,
--  end

lemma eval_qe :
  ∀ {p : formula_dlo} {bs : list rat}, (qe p).eval bs ↔ p.eval bs 
| ⊤' bs := iff.refl _
| ⊥' bs := iff.refl _
| (A' a) bs := iff.refl _
| (p ∧' q) bs := 
  begin
    simp [qe, eval_and],
    repeat {rw eval_qe}; assumption,
  end
| (p ∨' q) bs := 
  begin
    simp [qe, eval_or],
    repeat {rw eval_qe}; assumption,
  end
| (¬' p) bs := 
  begin simp [qe, eval_not], repeat {rw eval_qe} end
| (∃' p) bs := 
  begin
    simp [qe, eval_to_frm, eval_ex],
    apply calc
      (∃ (l : list (atom_dlo)), (∃ (a : list (atom_dlo)), a ∈ dnf (qe p) ∧ sqe_opt a = l) ∧ avals bs l) 
    ↔ (∃ (as : list (atom_dlo)), as ∈ dnf (qe p) ∧ avals bs (sqe_opt as)) : 
      begin
        constructor; intro h,
        { cases h with as1 h2, cases h2 with h2 h3,
          cases h2 with as2 h2, cases h2, subst h2_right,
          existsi as2, constructor; assumption },
        { cases h with as has, existsi (sqe_opt as), constructor,
          { existsi as, constructor, apply has.left, refl },
          { apply has.right} }
      end
... ↔ (∃ (x : rat) (as : list (atom_dlo)), as ∈ dnf (qe p) ∧ ∀ a ∈ as, atom_dlo.eval (x::bs) a) : 
      begin
        constructor; intro h; 
        [ 
          {
            cases h with as has, cases has with has1 has2,
            rw [eval_sqe_opt_iff] at has2;
            [ 
              { cases has2 with b hb, existsi b, existsi as, constructor; assumption }
              --{ apply forall_mem_dnf_forall_mem_normal _ _ has1,
              --  apply qfree_qe, apply fnormal_qe, apply hp }
            ]
          },
          {
            cases h with b hb, cases hb with as has,
            cases has with has1 has2, existsi as, apply and.intro has1, 
            apply (eval_sqe_opt_iff).elim_right,
              { existsi b, apply has2 },
              -- { apply forall_mem_dnf_forall_mem_normal _ _ has1,
              --   apply qfree_qe, apply fnormal_qe, apply hp }
          }
        ]
      end
... ↔ ∃ (x : rat), (qe p).eval (x :: bs) :
      begin
        apply exists_iff_exists, intro b,
        apply some_disjunct_true_iff, 
        apply qfree_qe 
      end
... ↔ ∃ (x : rat), p.eval (x :: bs) : 
      begin
        apply exists_iff_exists, intro b,
        apply eval_qe, 
      end
end

def dec_eval_of_qfree :
  ∀ {φ : formula_dlo}, qfree φ → ∀ {ds}, decidable (φ.eval ds) 
| ⊤' h _ := decidable.true 
| ⊥' h _ := decidable.false 
| (A' a) h _ := begin simp [formula_dlo.eval], apply_instance end
| (¬' p) h _ := 
  begin apply @not.decidable _ (dec_eval_of_qfree _), apply h end
| (p ∧' q) h _ := 
  @and.decidable _ _ 
  (dec_eval_of_qfree h.left) 
  (dec_eval_of_qfree h.right) 
| (p ∨' q) h _ := 
  @or.decidable _ _ 
  (dec_eval_of_qfree h.left) 
  (dec_eval_of_qfree h.right) 
| (∃' p) h _ := by cases h

instance dec_eval_qe 
  {φ : formula_dlo} : decidable ((qe φ).eval []) :=
begin apply dec_eval_of_qfree, apply qfree_qe end 
