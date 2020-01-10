import data.list.basic

variables {α β : Type}

namespace list

def equiv (l1 l2 : list α) := l1 ⊆ l2 ∧ l2 ⊆ l1

notation l1 `≃` l2 := equiv l1 l2

def equiv.refl {l : list α} : l ≃ l := 
and.intro (subset.refl _) (subset.refl _)

def equiv.symm {as1 as2 : list α} : (as1 ≃ as2) → (as2 ≃ as1) :=
begin
  intro h, cases h with h1 h2, 
  apply and.intro; assumption
end 

lemma equiv.trans {l1 l2 l3 : list α} : (l1 ≃ l2) → (l2 ≃ l3) → (l1 ≃ l3) :=  
begin
  intros h1 h2, cases h1 with h1a h1b, cases h2 with h2a h2b, 
  apply and.intro (subset.trans h1a h2a) (subset.trans h2b h1b),
end 

lemma mem_iff_mem_of_equiv {as1 as2 : list α} :
  (as1 ≃ as2) → ∀ (a : α), a ∈ as1 ↔ a ∈ as2 := 
begin
  intros heqv a, cases heqv with hss1 hss2, 
  apply iff.intro; intro hm,
  apply hss1; assumption,
  apply hss2; assumption
end

lemma map_subset_map_of_subset 
  {f : α → β} {as1 as2 : list α} :
  (as1 ⊆ as2) → (map f as1 ⊆ map f as2) :=
begin
  intros hss b hb, rewrite mem_map at *, cases hb with a ha,
  cases ha with ha1 ha2, subst ha2, existsi a, 
  apply and.intro _ rfl, apply hss ha1
end 

lemma map_equiv_map_of_equiv 
  {f : α → β} {as1 as2 : list α} :
  (as1 ≃ as2) → (map f as1 ≃ map f as2) :=
begin
  intro heqv, cases heqv with hss1 hss2, apply and.intro; 
  apply map_subset_map_of_subset; assumption
end 

lemma union_equiv_append [decidable_eq α] {as1 as2 : list α} :
  (as1 ∪ as2) ≃ (as1 ++ as2) :=
begin
  constructor, apply subset_of_sublist,
  apply union_sublist_append, intros a ha,
  rw mem_append at ha, cases ha,
  apply mem_union_left ha, 
  apply mem_union_right _ ha, 
end

lemma map_union_equiv [decidable_eq α] [decidable_eq β] 
  {f : α → β} {as1 as2 : list α} :
  map f (as1 ∪ as2) ≃ (map f as1) ∪ (map f as2) := 
begin
  apply and.intro; intros x hx,
  rewrite mem_map at hx, cases hx with y hy,
  cases hy with hy1 hy2, subst hy2, 
  rewrite mem_union at hy1,
  cases hy1 with hym hym, 
  apply mem_union_left, rewrite mem_map,
  existsi y, apply and.intro, assumption, refl,
  apply mem_union_right, rewrite mem_map,
  existsi y, apply and.intro, assumption, refl,
  rewrite mem_union at hx, cases hx with hx hx;
  rewrite mem_map at hx; cases hx with y hy;
  rewrite mem_map; existsi y; cases hy with hy1 hy2;
  apply and.intro _ hy2,
  apply mem_union_left hy1, 
  apply mem_union_right _ hy1
end

end list