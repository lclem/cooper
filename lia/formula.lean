import ..dot_prod ..logic .atom

inductive formula : Type 
| true  : formula
| false : formula
| atom : atom → formula 
| and : formula → formula → formula  
| or  : formula → formula → formula  
| not : formula → formula 
| ex  : formula → formula 
-- | ⊤' := sorry
-- | ⊥' := sorry
-- | (A' a) := sorry
-- | (p ∧' q) := sorry
-- | (p ∨' q) := sorry
-- | (¬' p) := sorry
-- | (∃' p) := sorry

notation `⊤'`     := formula.true
notation `⊥'`     := formula.false
notation `A'` a   := formula.atom a
notation `¬'` p   := formula.not p
notation p `∧'` q := formula.and p q 
notation p `∨'` q := formula.or p q 
notation `∃'` p   := formula.ex p

def formula.eval : list znum → formula → Prop 
| as ⊤' := _root_.true
| as ⊥' := _root_.false 
| as (A' a) := a.eval as   
| as (formula.not φ)   := ¬ (formula.eval as φ)
| as (formula.or φ ψ)  := (formula.eval as φ) ∨ (formula.eval as ψ)
| as (formula.and φ ψ) := (formula.eval as φ) ∧ (formula.eval as ψ)
| as (formula.ex φ) := ∃ d, formula.eval (d::as) φ 

lemma eval_true  {xs : list znum} : ⊤'.eval xs ↔ _root_.true := 
by simp [formula.eval]

lemma eval_not {p : formula} (xs : list znum) :
(¬' p).eval xs ↔ ¬ (p.eval xs) := iff.refl _

lemma eval_not_false {p : formula} (xs : list znum) :
(¬' ⊥').eval xs ↔ _root_.true := 
begin simp [formula.eval] end

lemma eval_not_or {p q : formula} {xs : list znum} :
(¬' (p ∨' q)).eval xs ↔ ((¬' p).eval xs ∧ (¬' q).eval xs) :=
begin simp [formula.eval, eval_not, not_or_distrib] end

lemma eval_not_and {p q : formula} {xs : list znum} :
(¬' (p ∧' q)).eval xs ↔ ((¬' p).eval xs ∨ (¬' q).eval xs) :=
begin 
  simp only [formula.eval, eval_not ], 
  rw (@not_and_distrib _ _ (classical.dec _)) 
end

lemma eval_or {p q : formula} (xs : list znum) : 
(p ∨' q).eval xs = (p.eval xs ∨ q.eval xs) := eq.refl _

lemma eval_and {p q : formula} {xs : list znum} : 
(p ∧' q).eval xs ↔ (p.eval xs ∧ q.eval xs) := iff.refl _

lemma eval_le {i : znum} {ks zs : list znum} : 
  (A' (i ≤' ks)).eval zs ↔ (i ≤ znum.dot_prod ks zs) := iff.refl _

lemma eval_false {xs : list znum} : ⊥'.eval xs ↔ _root_.false := 
by simp [formula.eval]

lemma eval_ex {p : formula} (xs) : (∃' p).eval xs = ∃ x, (p.eval (x::xs)) := 
begin simp [formula.eval] end

open znum

lemma eval_dvd {d i : znum} {ks zs : list znum} : 
  (A' (atom.dvd d i ks)).eval zs ↔ (has_dvd.dvd d (i + dot_prod ks zs)) := iff.refl _

lemma eval_ndvd {d i ks zs} : 
  (A' (atom.ndvd d i ks)).eval zs ↔ ¬ (has_dvd.dvd d (i + dot_prod ks zs)) := iff.refl _

lemma eval_ndvd' (d i : znum) (ks zs : list znum) :
  (A' (atom.ndvd d i ks)).eval zs ↔ ¬ (A' (atom.dvd d i ks)).eval zs :=
begin simp [formula.eval, atom.eval] end

def not_o : formula → formula  
| ⊤' := ⊥' 
| ⊥' := ⊤'
| p := ¬' p

def and_o : formula → formula → formula  
| (formula.true) q' := q'
| p' (formula.true) := p'
| (formula.false) q' := formula.false  
| p' (formula.false) := formula.false 
| p' q' := formula.and p' q'

def or_o : formula → formula → formula  
| (formula.true ) _ := ⊤'
| _ (formula.true ) := ⊤'
| (formula.false ) q := q
| p (formula.false ) := p
| p q := formula.or p q 

lemma eval_not_o {p : formula} (xs : list znum) : 
  (not_o p).eval xs ↔ ¬(p.eval xs) :=
begin cases p; simp [not_o, formula.eval] end

lemma eval_or_o {p q : formula} (xs : list znum) : 
(or_o p q).eval xs ↔ (p.eval xs ∨ q.eval xs) := 
begin cases p; cases q; simp [or_o, formula.eval] end

lemma eval_and_o {p q : formula} (xs : list znum) : 
(and_o p q).eval xs ↔ (p.eval xs ∧ q.eval xs) := 
begin cases p; cases q; simp [and_o, formula.eval] end

-- Requires : qfree arg-0
def formula.map (f : atom → atom) : formula → formula 
| ⊤' := ⊤' 
| ⊥' := ⊥' 
| A' a := A' (f a)
| (¬' p) := ¬' p.map
| (p ∨' q) :=  p.map ∨' q.map
| (p ∧' q) :=  p.map ∧' q.map
| (∃' p) := ⊥' 

def conj  : list (formula) → formula 
| [] := ⊤' 
| (p::ps) := and_o p $ conj ps 

def conj_atom  : list (atom) → formula 
| [] := ⊤' 
| (a::as) := and_o (A' a) $ conj_atom as 

def disj : list (formula) → formula 
| [] := ⊥' 
| (p::ps) := or_o p $ disj ps 

lemma eval_disj {xs : list znum} : 
  ∀ {ps : list (formula)}, (disj ps).eval xs ↔ (∃ p : formula, p ∈ ps ∧ p.eval xs) 
| [] := begin simp [disj, formula.eval] end
| (p::ps) := 
  begin
    rw [list.forsome_mem_cons], simp [disj, eval_or_o], 
    apply or_iff_or iff.rfl eval_disj
  end

def disj_map {β : Type} (bs : list β) (p : β → formula) := disj (list.map p bs) 

lemma eval_disj_map {β : Type} (as : list β) 
  (p : β → formula) {ds : list znum} :
  (disj_map as p).eval ds ↔ ∃ a, a ∈ as ∧ (p a).eval ds := 
begin
  simp [disj_map, eval_disj],
  constructor; intro h; cases h with x hx; cases hx with hx1 hx2,
  { cases hx1 with a ha, cases ha with ha1 ha2, subst ha2,
    existsi a, constructor; assumption },
  { existsi (p x), constructor, existsi x, 
    constructor, assumption, refl, assumption }
end

lemma cases_not_o (P : formula → Prop) (p : formula)  
  (HT : P ⊤') (Hp : P ⊥') (Hq : P (¬'p)) : P (not_o p) :=  
begin cases p; try {simp [not_o], assumption} end

lemma cases_or_o (P : formula → Prop) (p q : formula)  
  (HT : P ⊤') (Hp : P p) (Hq : P q) (Hpq : P (p ∨' q)) : P (or_o p q) :=  
begin cases p; cases q; try {simp [or_o], assumption} end

lemma cases_and_o (P : formula → Prop) (p q : formula)  
  (HB : P ⊥') (Hp : P p) (Hq : P q) (Hpq : P (p ∧' q)) : P (and_o p q) :=  
begin cases p; cases q; try {simp [and_o], assumption} end

lemma eval_mod_dvd {m d i ks z zs} :
  d ∣ m → 
  ((A' (atom.dvd d i ks)).eval (z % m :: zs) 
  ↔ (A' (atom.dvd d i ks)).eval (z :: zs))  := 
begin
  intro hdvd, cases ks with k ks; simp [eval_dvd],
  simp [dot_prod], have hrw1 : z = (z % m) + (z - (z % m)), 
  { rw [add_comm, sub_add_cancel] },
  have hrw2 : k * z = k * ((z % m) + (z - (z % m))) := by simp [hrw1.symm],
  rw [hrw2, mul_add],  repeat {rw [(add_assoc _ _ _).symm]},
  apply (dvd_add_iff_left _), 
  rw [znum.mod_def, sub_sub_cancel, mul_comm, mul_assoc],
  apply dvd_mul_of_dvd_left hdvd,
end

lemma eval_mod_ndvd {m d i ks z zs} : 
  d ∣ m → 
  ((A' (atom.ndvd d i ks)).eval (z % m :: zs) 
    ↔ (A' (atom.ndvd d i ks)).eval (z :: zs)) := 
begin intro hdvd, simp [eval_ndvd', eval_mod_dvd hdvd] end 

meta def formula.to_format  : formula → format 
| (formula.true)  := "⊤"
| (formula.false) := "⊥"
| (formula.atom a) := a.to_format
| (formula.and p q) := "(" ++ (formula.to_format p) ++ " ∧ " ++ (formula.to_format q) ++ ")"
| (formula.or p q)  := "(" ++ (formula.to_format p) ++ " ∨ " ++ (formula.to_format q) ++ ")"
| (formula.not p)  := "¬(" ++ (formula.to_format p) ++ ")" 
| (formula.ex p)   := "∃(" ++ (formula.to_format p) ++ ")"

meta instance formula.has_to_format : has_to_format (formula) := ⟨formula.to_format⟩ 

meta instance formula.has_to_tactic_format : has_to_tactic_format (formula) := 
has_to_format_to_has_to_tactic_format _
