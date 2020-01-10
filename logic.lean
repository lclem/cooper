import logic.basic

lemma or_iff_or {p p' q q' : Prop} :
  (p ↔ p') → (q ↔ q') → ((p ∨ q) ↔ (p' ∨ q')) := 
begin
  intros hp hq, rewrite hp, rewrite hq
end

lemma and_iff_and {p p' q q' : Prop} :
  (p ↔ p') → (q ↔ q') → ((p ∧ q) ↔ (p' ∧ q')) := 
begin intros hp hq, rewrite hp, rewrite hq end

lemma iff_of_left_of_right {p q : Prop} :
  p → q → (p ↔ q) := 
begin intros hp hq, constructor; intro h; assumption end

lemma iff_iff_and_or_not_and_not {p q : Prop} :
  (p ↔ q) ↔ ((p ∧ q) ∨ (¬p ∧ ¬q)) := 
begin
  constructor; intro h1,
  { apply @classical.by_cases p; intro h2,
    { left, rw ← h1, constructor; assumption }, 
    { right, rw ← h1, constructor; assumption } }, 
  { cases h1; cases h1 with hp hq, 
    { constructor; intro _; assumption }, 
    { constructor; intro _; contradiction } }
end

lemma exists_iff_exists {α : Type} {p q : α → Prop} :
  (∀ a, p a ↔ q a) → ((∃ a, p a) ↔ ∃ a, q a) :=
begin
  intro h, constructor; intro h; 
  cases h with a ha; existsi a; 
  [{rw (h a).symm}, {rw h}]; assumption
end

lemma forall_iff_not_exists_not {α : Type} {p : α → Prop} :
  (∀ a, p a) ↔ (¬ ∃ a, ¬ p a) :=
begin
  rw [@not_exists_not α p (λ x, _)], 
  apply classical.dec
end

lemma forall_iff_forall {α : Type} {p q : α → Prop} :
  (∀ a, p a ↔ q a) → ((∀ a, p a) ↔ ∀ a, q a) :=
begin
  intro h1, constructor; intros h2 a;
  [{rw (h1 a).symm}, {rw h1}]; apply h2
end 

lemma not_not_iff {φ : Prop} : ¬¬φ ↔ φ :=
iff.intro (classical.by_contradiction) (not_not_intro)

lemma or_of_not_imp_right {p q} : (¬ q → p) → p ∨ q :=
begin
  intro h, cases (classical.em q) with hq hq,
  apply or.inr hq, apply or.inl (h hq)
end

variable {α : Type}

lemma exists_eq_and_iff {p : α → Prop} {a : α} :
  (∃ x, (x = a ∧ p x)) ↔ p a :=
begin
  constructor; intro h, cases h with a' ha',
  cases ha' with ha1' ha2', subst ha1', assumption,
  existsi a, constructor, refl, assumption
end

lemma exists_and_comm {p q : α → Prop} :
  (∃ x, p x ∧ q x) ↔ (∃ x, q x ∧ p x) :=
begin apply exists_iff_exists, intro a, apply and.comm end

lemma ite.rec {p} [hd : decidable p] {q : α → Prop} {f g : α} 
  (hf : p → q f) (hg : ¬ p → q g) : q (@ite p hd α f g) := 
begin
  unfold ite, tactic.unfreeze_local_instances, 
  cases hd with h h, simp, apply hg h, simp, apply hf h
end

def as_true' (c : Prop) (h : decidable c) : Prop :=
@ite _ h Prop true false

def of_as_true' {c : Prop} (h₁ : decidable c) (h₂ : as_true' c h₁) : c :=
match h₁, h₂ with
| (is_true h_c),  h₂ := h_c
| (is_false h_c), h₂ := false.elim h₂
end

lemma eq.symm' {a1 a2 : α} :
  a1 = a2 ↔ a2 = a1 :=
iff.intro eq.symm eq.symm
  

lemma eq_iff_eq_of_eq_of_eq {a1 a2 a3 a4 : α} :
  a1 = a3 → a2 = a4 → (a1 = a2 ↔ a3 = a4) :=
begin intros h1 h2, rw [h1, h2] end

lemma lt_iff_lt_of_eq_of_eq [has_lt α] {a1 a2 a3 a4 : α} :
  a1 = a3 → a2 = a4 → (a1 < a2 ↔ a3 < a4) :=
begin intros h1 h2, rw [h1, h2] end