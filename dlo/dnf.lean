import .nnf

open list

-- Requires : nqfree arg-0
def dnf_core : formula_dlo → list (list atom_dlo) 
| (formula_dlo.true) := [[]]
| (formula_dlo.false) := []
| (formula_dlo.atom a) := [[a]]
| (formula_dlo.and p q) := map append_pair $ product (dnf_core p) (dnf_core q)
| (formula_dlo.or p q) := dnf_core p ++ dnf_core q 
| (formula_dlo.ex _) := []
| (formula_dlo.not _) := []

def dnf : formula_dlo → list (list atom_dlo) := 
dnf_core ∘ nnf

def to_frm (ls : list (list atom_dlo)) := disj (map conj_atom ls)

lemma eval_to_frm (bs) (ls : list (list atom_dlo)) :
(to_frm ls).eval bs ↔ ∃ l ∈ ls, avals bs l :=
begin
  simp [to_frm, eval_disj], constructor; intro h,
  { cases h with p hp, cases hp with hp1 hp2,
    cases hp1 with l hl, cases hl with h1 h2, subst h2,
    simp [eval_conj_atom] at hp2, existsi l,
    apply and.intro h1 hp2 }, 
  { cases h with l hl, existsi (conj_atom l), constructor,
    { existsi l, constructor, apply hl.left, refl },
    { simp [eval_conj_atom], apply hl.right } }
end


lemma some_core_disjunct_true_iff :
  ∀ {p : formula_dlo}, nqfree p → ∀ {bs : list rat},
    (∃ (as : list atom_dlo), as ∈ dnf_core p 
      ∧ ∀ (a : atom_dlo), a ∈ as → atom_dlo.eval bs a) ↔ p.eval bs 
| ⊤' h1 bs := begin simp [dnf_core] end
| ⊥' h1 bs := begin simp [dnf_core, formula_dlo.eval] end
| (A' a) h1 bs := begin simp [dnf_core, formula_dlo.eval] end
| (p ∨' q) h1 bs := 
  begin
    cases h1 with hp hq,
    simp [dnf_core, eval_or],
    apply iff.trans (exists_iff_exists _) _;  
    [
      {}, 
      { intro as, apply or_and_distrib_right}, 
      { rw exists_or_distrib, apply or_iff_or;
        apply some_core_disjunct_true_iff; assumption }
    ]
  end
| (p ∧' q) h1 bs := 
  begin
    simp [dnf_core, eval_and],
    constructor; intro h2; 
    [
      {
        cases h1 with hp hq, cases h2 with as h2, 
        cases h2 with h2 h3, cases h2 with as2 h2, 
        cases h2 with as3 h2, cases h2 with h2 h4, 
        cases h2 with h2p h2q, subst h4,
        simp only [append_pair] at h3,
        rw [forall_mem_append] at h3, cases h3 with h3 h4,
        constructor; 
        [ 
          { rw (some_core_disjunct_true_iff _).symm, 
            existsi as2, constructor; assumption, assumption }, 
          { rw (some_core_disjunct_true_iff _).symm, 
            existsi as3, constructor; assumption, assumption } 
        ]
      },
      {
        cases h1 with h1p h1q,
        cases h2 with h2p h2q,
        rw (some_core_disjunct_true_iff h1p).symm at h2p,
        rw (some_core_disjunct_true_iff h1q).symm at h2q,
        cases h2p with as1 hp, cases hp with hp1 hp2,
        cases h2q with as2 hq, cases hq with hq1 hq2,
        existsi (as1 ++ as2), constructor;
        [
          { existsi as1, existsi as2, apply and.intro _ rfl,
            constructor; assumption },
          { intros a ha, rw mem_append at ha, cases ha; 
            [{apply hp2},{apply hq2}]; assumption }
        ]
      }
    ]
  end

lemma some_disjunct_true_iff {p : formula_dlo} (h : qfree p) {bs : list rat} :
(∃ (as : list atom_dlo), as ∈ dnf p ∧ ∀ (a : atom_dlo), a ∈ as → atom_dlo.eval bs a) ↔ p.eval bs :=
begin
  simp [dnf, dnf_core],
  rw some_core_disjunct_true_iff,
   apply eval_nnf h,
   apply nqfree_nnf h,
end



#exit
lemma join_dnf_core_subset_atms :
  ∀ {φ : formula_dlo}, join (dnf_core φ) ⊆ atom_dlos φ 
| (A' a') a h := begin simp [dnf_core, atms] at *, assumption end
| (p ∧' q) a h := 
  begin 
     simp [dnf_core, atms] at *, 
     cases h with as1 h, cases h with h h1, 
     cases h with as2 h, cases h with as3 h,
     cases h with h2 h4, cases h2 with h2 h3,
     subst h4, rw mem_append at h1, cases h1;
     [
       {apply or.inl, apply join_dnf_core_subset_atms,
        rw mem_join, existsi as2, constructor; assumption},
       {apply or.inr, apply join_dnf_core_subset_atms,
        rw mem_join, existsi as3, constructor; assumption}
     ]
  end
| (p ∨' q) a h := 
  begin 
     simp [dnf_core, atms] at *, 
     cases h; cases h with as h; cases h with h1 h2;
     [
       {apply or.inl, apply join_dnf_core_subset_atms,
        rw mem_join, existsi as, constructor; assumption},
       {apply or.inr, apply join_dnf_core_subset_atms,
        rw mem_join, existsi as, constructor; assumption}
     ]
  end

lemma forall_mem_dnf_core_forall_mem [axms α] (p : atom_dlo → Prop) : 
  ∀ (φ : formula_dlo), (∀ a ∈ (atms φ), p a) 
    → ∀ as ∈ (dnf_core φ), ∀ a ∈ as, p a := 
begin
  intros φ h1 as h2 a h3, 
  apply h1, apply join_dnf_core_subset_atms,
  rw mem_join, existsi as, constructor; assumption
end

lemma forall_mem_dnf_core_forall_mem_normal [axms α] : ∀ {p : formula_dlo}, 
  @fnormal α _ p → ∀ {as : list atom_dlo}, as ∈ (dnf_core p) → ∀ a ∈ as, normal a :=
begin
  intros p hp, rewrite fnormal_iff_fnormal_alt at hp,
  apply forall_mem_dnf_core_forall_mem (normal) _ hp, 
end

lemma forall_mem_dnf_forall_mem_normal [axms α]  
  {p : formula_dlo} (hp1 : qfree p) (hp2 : fnormal p) :
  ∀ {as : list atom_dlo}, (as ∈ (dnf p)) → ∀ a ∈ as, normal a :=
begin
  intros as has, simp [dnf] at has,
  apply forall_mem_dnf_core_forall_mem_normal _ has,
  apply nnf.fnormal_dnf hp1 hp2
end