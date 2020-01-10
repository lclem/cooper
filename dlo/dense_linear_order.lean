import ..list data.rat

universe u

variables {α β: Type}

class dense_linear_order (α : Type) extends decidable_linear_order α :=
(inh : inhabited α)
(dense : ∀ {x z : α}, x < z → ∃ (y : α), x < y ∧ y < z)
(exists_lt : ∀ (y : α), ∃ (x : α), x < y)
(exists_gt : ∀ (x : α), ∃ (y : α), x < y)

open dense_linear_order 

lemma dense_of_lof [linear_ordered_field α] : 
  ∀ {x z : α}, x < z → ∃ (y : α), x < y ∧ y < z := 
begin
  intros x z h, existsi ((x + z) / 2), constructor,
  { have h2 : (x + x) / 2 < (x + z) / 2, 
    { apply div_lt_div_of_lt_of_pos, apply add_lt_add_left h,
      apply lt.trans zero_lt_one, apply two_gt_one },
    rw add_self_div_two at h2, apply h2 },
  { have h2 : (x + z) / 2 < (z + z) / 2, 
    { apply div_lt_div_of_lt_of_pos, apply add_lt_add_right h,
      apply lt.trans zero_lt_one, apply two_gt_one },
    rw add_self_div_two at h2, apply h2 },
end

lemma exists_lt_of_lof [linear_ordered_field α] :  ∀ (y : α), ∃ (x : α), x < y :=
begin intro y, existsi (y - 1), apply sub_lt_self, apply zero_lt_one end

lemma exists_gt_of_lof [linear_ordered_field α] :  ∀ (x : α), ∃ (y : α), x < y :=
begin intro y, existsi (y + 1), apply lt_add_of_pos_right, apply zero_lt_one, end

instance inh_dom [dense_linear_order β] : inhabited β := dense_linear_order.inh β 

lemma exists_upper_bound [dense_linear_order β] : 
∀ (bs : list β), ∃ x, ∀ b ∈ bs, b < x 
| [] := begin existsi (default β), intros b hb, cases hb end
| (b::bs) :=
  begin
    cases (exists_upper_bound bs) with x hx, by_cases (b < x),
    { existsi x, intros b' hb', cases hb', 
      {subst hb', apply h}, {apply hx _ hb'} },
    {
      cases (exists_gt b) with y hy, existsi y, intros b' hb', cases hb',
      {subst hb', apply hy}, 
      {apply lt.trans (hx _ hb'), apply lt_of_le_of_lt (le_of_not_lt h) hy}
    }
  end

lemma exists_lower_bound [dense_linear_order β] : 
∀ (bs : list β), ∃ x, ∀ b ∈ bs, x < b
| [] := begin existsi (default β), intros b hb, cases hb end
| (b::bs) :=
  begin
    cases (exists_lower_bound bs) with x hx, by_cases (x < b),
    { existsi x, intros b' hb', cases hb', 
      {subst hb', apply h}, {apply hx _ hb'} },
    {
      cases (exists_lt b) with y hy, existsi y, intros b' hb', cases hb',
      {subst hb', apply hy}, 
      {apply lt.trans _ (hx _ hb'), apply lt_of_lt_of_le hy (le_of_not_lt h)}
    }
  end

instance rat.dense_linear_order : dense_linear_order rat := 
{ inh := ⟨0⟩, 
  dense := @dense_of_lof _ _,
  exists_lt := @exists_lt_of_lof _ _,
  exists_gt := @exists_gt_of_lof _ _ }