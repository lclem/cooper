import data.list.basic .tactics

variables {α β : Type}

namespace list

open tactic

def append_pair : (list α × list α) → list α  
| (l1,l2) := l1 ++ l2 

lemma forsome_mem_cons {p : α → Prop} {a : α} {as : list α} :
  (∃ x, x ∈ (a::as) ∧ p x) ↔ p a ∨ ∃ x, x ∈ as ∧ p x := 
begin
  constructor; intro h;
  [
    {
      cases h with a2 ha2, cases ha2 with ha2l ha2r,
      cases (eq_or_mem_of_mem_cons ha2l) with ha2l,
      subst ha2l, apply or.inl, assumption,
      apply or.inr, existsi a2, constructor; assumption
    },
    {
      cases h with h h;
      [ 
        { existsi a, constructor, apply or.inl rfl, assumption },
        {
          cases h with a ha, cases ha with ha1 ha2,
          existsi a, apply and.intro (or.inr ha1) ha2
        }
      ]
    }
  ]
end

def forall_mem (P : α → Prop) (as : list α) := ∀ a ∈ as, P a

lemma forall_mem_map_iff {f : α → β} {Q : β → Prop} {as} : 
(∀ b ∈ (map f as), Q b) ↔ (∀ a ∈ as, Q (f a)) := 
begin
  constructor; intro h,
  { intros a ha, 
    apply h, apply mem_map_of_mem _ ha },
  { intros b hb, rw mem_map at hb,
    cases hb with a ha, cases ha with ha1 ha2, 
    subst ha2, apply h _ ha1 }
end

lemma forall_mem_map {f : α → β} {p : β → Prop} {as} : 
(∀ a ∈ as, p (f a)) → (∀ b ∈ (map f as), p b) :=
forall_mem_map_iff.elim_right

-- lemma forall_mem_map {f : α → β} {p : α → Prop} 
--   {q : β → Prop} (h1 : ∀ a, p a → q (f a)) :
--   ∀ {as}, (∀ a ∈ as, p a) → (∀ b ∈ (map f as), q b) 
-- | [] _ := by {apply forall_mem_nil}
-- | (a::as) h2 := 
--   begin
--     intros b h3, simp [map] at h3, cases h3,
--     rw h3, apply h1, apply h2, apply or.inl rfl,
--     cases h3 with a' ha', cases ha' with h3 h4,
--     subst h4, apply h1, apply h2, apply or.inr h3 
--   end

lemma forall_mem_filter_of_forall_mem {P Q : α → Prop} [H : decidable_pred Q] 
  {as : list α} (h : ∀ a ∈ as, P a) : ∀ a ∈ (list.filter Q as), P a := 
begin intros a ha, apply h, apply mem_of_mem_filter ha end

lemma forall_mem_filter {P Q : α → Prop} [H : decidable_pred P] {as} : 
(∀ a ∈ (filter P as), Q a) ↔ (∀ a ∈ as, P a → Q a) := 
begin
  constructor; intro h,
  { intros a ha1 ha2, apply h, rw mem_filter, 
    constructor; assumption },
  { intros a ha, rw mem_filter at ha,
    apply h _ ha.left ha.right }
end

def some_true (ps : list Prop) : Prop := ∃ p, p ∈ ps ∧ p

def forsome_mem (P : α → Prop) (as : list α) := ∃ a, a ∈ as ∧ P a

instance forsome_mem.decidable {P : α → Prop} [hd : decidable_pred P] :
  ∀ {as : list α}, decidable (∃ a, a ∈ as ∧ P a) 
| [] := decidable.is_false (by simp)
| (a::as) :=
  begin
    cases (hd a),
      { cases forsome_mem.decidable,
          { apply decidable.is_false, intro hc,
            cases hc with a' hc, cases hc with hc1 hc2,
            cases hc1, subst hc1, apply h hc2, apply h_1, 
            existsi a', constructor; assumption },
          { apply decidable.is_true, 
            rw forsome_mem_cons, apply or.inr h_1 } },
      { apply decidable.is_true, 
        rw forsome_mem_cons, apply or.inl h } 
  end

instance dec_eq_nil : ∀ {as : list α}, decidable (as = []) 
| [] := decidable.is_true rfl 
| (a::as) := decidable.is_false (begin intro h, cases h end)

lemma map_ne_nil_of_ne_nil : 
  ∀ {f : α → β} {as : list α}, as ≠ [] → map f as ≠ [] :=
λ f as, not_imp_not.elim_right eq_nil_of_map_eq_nil

lemma exists_maximum [linear_order β] : 
∀ {bs : list β} (hi : bs ≠ []), ∃ b, b ∈ bs ∧ ∀ b' ∈ bs, b' ≤ b 
| [] hi := begin exfalso, apply hi rfl end
| [b] hi := 
  begin
    existsi b, apply and.intro (or.inl rfl), 
    intros b' hb', cases hb' with hb' hb', 
    subst hb', cases hb',
  end
| (b::b'::bs') hi := 
  begin
    cases (@exists_maximum (b'::bs') _) with x hx;
    [{}, { exact_dec_trivial }], cases hx with hx1 hx2,
    apply @classical.by_cases (b ≤ x); intro hle,
    { existsi x, apply and.intro (or.inr hx1), 
      intros bl hbl, rewrite mem_cons_iff at hbl, 
      cases hbl with hbl hbl, subst hbl, apply hle, 
      apply hx2 _ hbl },
    { existsi b, apply and.intro (or.inl rfl),
      intros bl hbl, rewrite mem_cons_iff at hbl, 
      cases hbl with hbl hbl, subst hbl, 
      apply le_trans, apply hx2 _ hbl, 
      apply le_of_not_le hle }
  end

def converse_linear_order (h : linear_order α) : linear_order α := 
{
  le := ge,
  le_refl := le_refl,
  le_trans := @ge_trans _ _,
  le_antisymm := λ a b h1 h2, le_antisymm h2 h1,
  le_total := λ a b, or.symm (le_total a b)
}

lemma exists_minimum [h : linear_order β] : 
∀ {bs : list β} (hi : bs ≠ []), ∃ b, b ∈ bs ∧ ∀ b' ∈ bs, b' ≥ b :=  
@exists_maximum _ (converse_linear_order h)

def map_neg [has_neg α] (as : list α) : list α :=
list.map (λ x, -x) as

def map_mul [has_mul α] (a) (as : list α) : list α :=
list.map (λ x, a * x) as

lemma of_mem_repeat {k m : nat} :
∀ {n}, k ∈ repeat m n → k = m 
| 0 h := by cases h
| (n+1) h :=
  begin
    simp [repeat] at h, cases h, assumption,
    apply eq_of_mem_repeat h
  end

lemma one_map_mul [monoid α] :
∀ (as : list α), map_mul 1 as = as 
| [] := rfl
| (a::as) := begin simp [map_mul], apply map_id end

def update_nth_force : list α → ℕ → α → α → list α
| (x::xs) 0     a a' := a :: xs
| (x::xs) (i+1) a a' := x :: update_nth_force xs i a a'
| []      0     a a' := [a] 
| []      (i+1) a a' := a' :: update_nth_force [] i a a'

-- def zip_pad (da : α) (db : β) : list α → list β → list (α × β)
-- | [] [] := []
-- | [] (b::bs) := (da, b)::(zip_pad [] bs)
-- | (a::as) [] := (a, db)::(zip_pad as [])
-- | (a::as) (b::bs) := (a,b)::(zip_pad as bs)
-- 
-- lemma cons_zip_pad_cons {a b a' b'} {as : list α} {bs : list β} : 
--   zip_pad a' b' (a::as) (b::bs) = (a,b)::(zip_pad a' b' as bs) :=
-- begin unfold zip_pad end

def comp_add [has_add α] : list α → list α → list α 
| (a1::as1) (a2::as2) := (a1+a2)::(comp_add as1 as2) 
| [] as2 := as2
| as1 [] := as1

def comp_sub [has_neg α] [has_add α] [has_sub α] : list α → list α → list α 
| (a1::as1) (a2::as2) := (a1-a2)::(comp_sub as1 as2) 
| as1 [] := as1
| [] as2 := map_neg as2

-- def comp_add [has_zero α] [has_add α] (as1 as2 : list α) : list α := 
-- list.map (λ xy, prod.fst xy + prod.snd xy) (list.zip_pad 0 0 as1 as2)
-- 
-- def comp_sub [has_zero α] [has_neg α] [has_add α] (as1 as2 : list α) : list α := 
-- comp_add as1 (map_neg as2)

lemma nil_comp_add [semiring α] (as : list α) :
comp_add [] as = as := 
begin cases as; refl end

lemma comp_add_nil [semiring α] (as : list α) :
comp_add as [] = as := 
begin cases as; refl end

lemma nil_comp_sub [has_neg α] [has_add α] [has_sub α] (as : list α) :
comp_sub [] as = map_neg as := 
begin cases as; refl end

lemma comp_sub_nil [has_neg α] [has_add α] [has_sub α] (as : list α) :
comp_sub as [] = as := 
begin cases as; refl end

-- | (a::as) := 
--   begin
--     unfold comp_add, unfold list.zip_pad,
--     unfold list.map, simp, 
--     have h := nil_comp_add as,
--     unfold comp_add at h, rewrite h
--   end
-- 
-- lemma comp_add_nil [semiring α] :
--   ∀ (as : list α), comp_add as [] = as 
-- | [] := rfl
-- | (a::as) := 
--   begin
--     unfold comp_add, unfold list.zip_pad, 
--     simp, have h := comp_add_nil as, 
--     unfold comp_add at h, rewrite h 
--   end
-- 
-- lemma cons_comp_add_cons [semiring α] (a1 a2 : α) (as1 as2) :
-- comp_add (a1::as1) (a2::as2) = (a1 + a2)::(comp_add as1 as2) := 
-- begin unfold comp_add, unfold list.zip_pad, simp end
-- 
-- def map_comp_add_eq [semiring α] [semiring β] 
--   {f : α → β} (hf : ∀ a1 a2, f (a1 + a2) = f a1 + f a2) :
-- ∀ (as1 as2 : list α), map f (comp_add as1 as2) = comp_add (map f as1) (map f as2) 
-- | [] [] := rfl
-- | [] (a2::as2) := begin simp [nil_comp_add, map] end
-- | (a1::as1) [] := begin simp [comp_add_nil, map] end
-- | (a1::as1) (a2::as2) := 
--   begin
--     simp [cons_comp_add_cons], constructor,
--     apply hf, apply map_comp_add_eq
--   end

-- def map_comp_sub_eq [semiring α] [has_neg α] [semiring β] [has_neg β]
--   {f : α → β} (hf1 : ∀ a1 a2, f (a1 + a2) = f a1 + f a2) (hf2 : ∀ a, f (-a) = - f a):
-- ∀ (as1 as2 : list α), map f (comp_sub as1 as2) = comp_sub (map f as1) (map f as2) :=
-- begin
--   intros as1 as2, simp [comp_sub], rw (map_comp_add_eq hf1), simp [map_neg],
--   have hrw : (f ∘ has_neg.neg) = (has_neg.neg ∘ f) := funext hf2, rw hrw 
-- end

lemma filter_map_append_eq {f : α → option β} : 
∀ {as1 as2 : list α}, filter_map f (as1 ++ as2) = (filter_map f as1 ++ filter_map f as2) 
| [] as2 := begin simp [filter_map] end
| (a::as1) as2 :=
  begin 
    simp [filter_map], cases (f a), 
    apply filter_map_append_eq,
    rw (@filter_map_append_eq as1 as2), refl,
  end

lemma forall_mem_iff_forall_mem {P Q : α → Prop} {as : list α} : 
(∀ a, P a ↔ Q a) → ((∀ a ∈ as, P a) ↔ (∀ a ∈ as, Q a)) := 
begin
  intro heq, constructor; intros h a ha,
  rw ← heq, apply h _ ha, rw heq, apply h _ ha
end

end list
