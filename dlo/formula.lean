import ..list ..logic data.rat

instance rat.inhabited : inhabited rat := ⟨0⟩ 

inductive term_dlo : Type
| var : nat → term_dlo 
| cst : rat → term_dlo

notation `V'` := term_dlo.var 
notation `C'` r  := term_dlo.cst r

instance term_dlo.decidable_eq : decidable_eq term_dlo := by tactic.mk_dec_eq_instance

-- def term_dlo.decr_idx : term_dlo rat → term_dlo rat 
-- | (term_dlo.var rat m) := term_dlo.var rat (m-1)
-- | (term_dlo.cst b) := term_dlo.cst b
-- 
def term_dlo.incr_idx : term_dlo → term_dlo 
| (term_dlo.var m) := term_dlo.var (m+1)
| (term_dlo.cst b) := term_dlo.cst b

def term_dlo.eval (bs : list rat) : term_dlo → rat 
| (term_dlo.var n) := list.inth bs n 
| (term_dlo.cst r) := r

-- meta def term_dlo.to_format : term_dlo → format 
-- | (term_dlo.var m) := "#" ++ to_fmt m 
-- | (term_dlo.cst b) := "@" ++ to_fmt b

-- meta instance term_dlo.has_to_format : has_to_format term_dlo := 
-- ⟨term_dlo.to_format⟩

lemma term_dlo.eval_incr_idx_eq {t : term_dlo} {b : rat} {bs} :
t.incr_idx.eval (b::bs) = t.eval bs := 
begin cases t with n b; simp [term_dlo.incr_idx, term_dlo.eval] end

instance dec_eq_term_dlo : decidable_eq term_dlo := 
by tactic.mk_dec_eq_instance

inductive atom_dlo : Type 
| lt : term_dlo → term_dlo → atom_dlo 
| eq : term_dlo → term_dlo → atom_dlo 

def atom_dlo.eval (bs : list rat) : atom_dlo → Prop 
| (atom_dlo.lt t1 t2) := term_dlo.eval bs t1 < term_dlo.eval bs t2
| (atom_dlo.eq t1 t2) := term_dlo.eval bs t1 = term_dlo.eval bs t2
-- | (x <' y) := sorry
-- | (x =' y) := sorry

-- meta def atom_dlo.to_format : atom_dlo → format 
-- | (atom_dlo.lt t s) := to_fmt t ++ " < " ++ to_fmt s
-- | (atom_dlo.eq t s) := to_fmt t ++ " = " ++ to_fmt s

inductive formula_dlo : Type 
| true  : formula_dlo
| false : formula_dlo
| atom : atom_dlo → formula_dlo 
| and : formula_dlo → formula_dlo → formula_dlo  
| or  : formula_dlo → formula_dlo → formula_dlo  
| not : formula_dlo → formula_dlo 
| ex  : formula_dlo → formula_dlo 
-- | formula_dlo.true := sorry
-- | formula_dlo.false := sorry
-- | (formula_dlo.atom a) := sorry
-- | (formula_dlo.and p q) := sorry
-- | (p ∨' q) := sorry
-- | (¬' p) := sorry
-- | (formula_dlo.ex p) := sorry

notation `⊤'`     := formula_dlo.true
notation `⊥'`     := formula_dlo.false
notation `A'` a   := formula_dlo.atom a
notation `¬'` p   := formula_dlo.not p
notation p `∧'` q := formula_dlo.and p q 
notation p `∨'` q := formula_dlo.or p q 
notation `∃'` p   := formula_dlo.ex p
notation x `<'` y := atom_dlo.lt x y
notation x `='` y := atom_dlo.eq x y

def formula_dlo.eval : list rat → formula_dlo → Prop 
| as formula_dlo.true := _root_.true
| as formula_dlo.false := _root_.false 
| as (formula_dlo.atom a) := a.eval as   
| as (formula_dlo.not φ)   := ¬ (formula_dlo.eval as φ)
| as (formula_dlo.or φ ψ)  := (formula_dlo.eval as φ) ∨ (formula_dlo.eval as ψ)
| as (formula_dlo.and φ ψ) := (formula_dlo.eval as φ) ∧ (formula_dlo.eval as ψ)
| as (formula_dlo.ex φ) := ∃ d, formula_dlo.eval (d::as) φ 

lemma eval_true  {xs : list rat} : formula_dlo.true.eval xs ↔ _root_.true := 
by simp [formula_dlo.eval]

lemma eval_not {p : formula_dlo} (xs : list rat) :
(p.not).eval xs ↔ ¬ (p.eval xs) := iff.refl _

lemma eval_not_false {p : formula_dlo} (xs : list rat) :
(formula_dlo.false.not).eval xs ↔ _root_.true := 
begin simp [formula_dlo.eval] end

lemma eval_not_or {p q : formula_dlo} {xs : list rat} :
((formula_dlo.or p q).not).eval xs ↔ ((p.not).eval xs ∧ (q.not).eval xs) :=
begin simp [formula_dlo.eval, eval_not, not_or_distrib] end

lemma eval_not_and {p q : formula_dlo} {xs : list rat} :
((formula_dlo.and p q).not).eval xs ↔ ((p.not).eval xs ∨ (q.not).eval xs) :=
begin 
  simp only [formula_dlo.eval, eval_not ], 
  rw (@not_and_distrib _ _ (classical.dec _)) 
end

lemma eval_or {p q : formula_dlo} (xs : list rat) : 
(formula_dlo.or p q).eval xs = (p.eval xs ∨ q.eval xs) := eq.refl _

lemma eval_and {p q : formula_dlo} {xs : list rat} : 
(formula_dlo.and p q).eval xs = (p.eval xs ∧ q.eval xs) := eq.refl _

lemma eval_le {t s : term_dlo} {rs : list rat} : 
(atom_dlo.lt t s).eval rs ↔ (t.eval rs < s.eval rs) := iff.refl _

lemma eval_false {xs : list rat} : formula_dlo.false.eval xs ↔ _root_.false := 
by simp [formula_dlo.eval]

lemma eval_ex {p : formula_dlo} (xs) : p.ex.eval xs = ∃ x, (p.eval (x::xs)) := 
begin simp [formula_dlo.eval] end

open rat

def not_o : formula_dlo → formula_dlo  
| formula_dlo.true := formula_dlo.false 
| formula_dlo.false := formula_dlo.true
| p := p.not

def and_o : formula_dlo → formula_dlo → formula_dlo  
| (formula_dlo.true) q' := q'
| p' (formula_dlo.true) := p'
| (formula_dlo.false) q' := formula_dlo.false  
| p' (formula_dlo.false) := formula_dlo.false 
| p' q' := formula_dlo.and p' q'

def or_o : formula_dlo → formula_dlo → formula_dlo  
| (formula_dlo.true ) _ := formula_dlo.true
| _ (formula_dlo.true ) := formula_dlo.true
| (formula_dlo.false ) q := q
| p (formula_dlo.false ) := p
| p q := formula_dlo.or p q 

lemma eval_not_o {p : formula_dlo} (xs : list rat) : 
  (not_o p).eval xs ↔ ¬(p.eval xs) :=
begin cases p; simp [not_o, formula_dlo.eval] end

lemma eval_or_o {p q : formula_dlo} (xs : list rat) : 
(or_o p q).eval xs ↔ (p.eval xs ∨ q.eval xs) := 
begin cases p; cases q; simp [or_o, formula_dlo.eval] end

lemma eval_and_o {p q : formula_dlo} (xs : list rat) : 
(and_o p q).eval xs ↔ (p.eval xs ∧ q.eval xs) := 
begin cases p; cases q; simp [and_o, formula_dlo.eval] end

-- Requires : qfree arg-0
def formula_dlo.map (f : atom_dlo → atom_dlo) : formula_dlo → formula_dlo 
| formula_dlo.true := formula_dlo.true 
| formula_dlo.false := formula_dlo.false 
| (formula_dlo.atom a) := formula_dlo.atom (f a)
| (formula_dlo.not p) := p.map.not
| (formula_dlo.or p q) :=  formula_dlo.or p.map q.map
| (formula_dlo.and p q) :=  formula_dlo.and p.map q.map
| (formula_dlo.ex p) := formula_dlo.false 

def conj  : list (formula_dlo) → formula_dlo 
| [] := formula_dlo.true 
| (p::ps) := and_o p $ conj ps 

def conj_atom  : list (atom_dlo) → formula_dlo 
| [] := formula_dlo.true 
| (a::as) := and_o (formula_dlo.atom a) $ conj_atom as 

def disj : list (formula_dlo) → formula_dlo 
| [] := formula_dlo.false 
| (p::ps) := or_o p $ disj ps 

lemma eval_disj {xs : list rat} : 
  ∀ {ps : list (formula_dlo)}, (disj ps).eval xs ↔ (∃ p : formula_dlo, p ∈ ps ∧ p.eval xs) 
| [] := begin simp [disj, formula_dlo.eval] end
| (p::ps) := 
  begin
    rw [list.forsome_mem_cons], simp [disj, eval_or_o], 
    apply or_iff_or iff.rfl eval_disj
  end

def disj_map {β : Type} (bs : list β) (p : β → formula_dlo) := disj (list.map p bs) 

lemma eval_disj_map {β : Type} (as : list β) 
  (p : β → formula_dlo) {ds : list rat} :
  (disj_map as p).eval ds ↔ ∃ a, a ∈ as ∧ (p a).eval ds := 
begin
  simp [disj_map, eval_disj],
  constructor; intro h; cases h with x hx; cases hx with hx1 hx2,
  { cases hx1 with a ha, cases ha with ha1 ha2, subst ha2,
    existsi a, constructor; assumption },
  { existsi (p x), constructor, existsi x, 
    constructor, assumption, refl, assumption }
end

lemma cases_not_o (P : formula_dlo → Prop) (p : formula_dlo)  
  (HT : P formula_dlo.true) (Hp : P formula_dlo.false) (Hq : P (p.not)) : P (not_o p) :=  
begin cases p; try {simp [not_o], assumption} end

lemma cases_or_o (P : formula_dlo → Prop) (p q : formula_dlo)  
  (HT : P formula_dlo.true) (Hp : P p) (Hq : P q) (Hpq : P (formula_dlo.or p q)) : P (or_o p q) :=  
begin cases p; cases q; try {simp [or_o], assumption} end

lemma cases_and_o (P : formula_dlo → Prop) (p q : formula_dlo)  
  (HB : P formula_dlo.false) (Hp : P p) (Hq : P q) (Hpq : P (formula_dlo.and p q)) : P (and_o p q) :=  
begin cases p; cases q; try {simp [and_o], assumption} end

-- meta def formula_dlo.to_format  : formula_dlo → format 
-- | (formula_dlo.true)  := "⊤"
-- | (formula_dlo.false) := "⊥"
-- | (formula_dlo.atom a) := a.to_format
-- | (formula_dlo.and p q) := "(" ++ (formula_dlo.to_format p) ++ " ∧ " ++ (formula_dlo.to_format q) ++ ")"
-- | (formula_dlo.or p q)  := "(" ++ (formula_dlo.to_format p) ++ " ∨ " ++ (formula_dlo.to_format q) ++ ")"
-- | (formula_dlo.not p)  := "¬(" ++ (formula_dlo.to_format p) ++ ")" 
-- | (formula_dlo.ex p)   := "∃(" ++ (formula_dlo.to_format p) ++ ")"

-- meta instance formula_dlo.has_to_format : has_to_format (formula_dlo) := ⟨formula_dlo.to_format⟩ 
-- 
-- meta instance formula_dlo.has_to_tactic_format : has_to_tactic_format (formula_dlo) := 
-- has_to_format_to_has_to_tactic_format _

instance atom_dlo.decidable_eq : decidable_eq atom_dlo := by tactic.mk_dec_eq_instance

instance dec_aval {as a} : decidable (atom_dlo.eval as a) :=
begin cases a; {simp [atom_dlo.eval], apply_instance} end

def avals (bs : list rat) (as : list atom_dlo) : Prop :=  
∀ a ∈ as, atom_dlo.eval bs a

lemma eval_conj {xs : list rat} : 
  ∀ {ps : list formula_dlo}, formula_dlo.eval xs (conj ps) ↔ (∀ p ∈ ps, formula_dlo.eval xs p)
| [] := begin simp [conj, formula_dlo.eval] end
| (p::ps) :=
  begin
    simp [conj, eval_and_o], 
    apply and_iff_and iff.rfl eval_conj
  end

lemma eval_conj_atom {xs : list rat} : 
  ∀ {as : list atom_dlo}, (conj_atom as).eval xs ↔ (∀ a ∈ as, atom_dlo.eval xs a) 
| [] := begin simp [conj_atom] end
| (a::as) := 
  begin simp [conj_atom, eval_and_o, atom_dlo.eval,
   eval_conj_atom, formula_dlo.eval] end