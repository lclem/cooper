import ..list ..int

open list 

inductive preterm_lia : Type
| var : nat → preterm_lia 
| cst : int → preterm_lia 
| lmul : int → nat → preterm_lia
| rmul : nat → int → preterm_lia
| neg : preterm_lia → preterm_lia 
| add : preterm_lia → preterm_lia → preterm_lia 
| sub : preterm_lia → preterm_lia → preterm_lia 
open preterm_lia
-- | (var n) := sorry 
-- | (cst z) := sorry 
-- | (lmul z n) := sorry
-- | (rmul n z) := sorry
-- | (neg t) := sorry
-- | (add t1 t2) := sorry
-- | (sub t1 t2) := sorry

notation `V*` n := preterm_lia.var n
notation `C*` k := preterm_lia.cst k
notation t `×*` s := preterm_lia.lmul t s
notation t `*×` s := preterm_lia.rmul t s
notation `-*` t := preterm_lia.neg t
notation t `+*` s := preterm_lia.add t s
notation t `-**` s := preterm_lia.sub t s


meta def preterm_lia.to_format : preterm_lia → format
| (var n) := "#" ++ to_fmt n 
| (cst z) := to_fmt z
| (lmul z n) := to_fmt z ++ " * #" ++ to_fmt n 
| (rmul n z) := "#" ++ to_fmt n ++ " * " ++ to_fmt z 
| (neg t) := "-" ++ preterm_lia.to_format t
| (add t1 t2) := "(" ++ preterm_lia.to_format t1 ++ " + " ++ preterm_lia.to_format t2 ++ ")"
| (sub t1 t2) := "(" ++ preterm_lia.to_format t1 ++ " - " ++ preterm_lia.to_format t2 ++ ")"

meta instance preterm_lia.has_to_format : has_to_format preterm_lia := ⟨preterm_lia.to_format⟩  

meta instance preterm_lia.has_reflect : has_reflect preterm_lia := by tactic.mk_has_reflect_instance

inductive preatom_lia : Type 
| le : preterm_lia → preterm_lia → preatom_lia
| dvd : int → preterm_lia → preatom_lia
| ndvd : int → preterm_lia → preatom_lia

notation t1 `≤*` t2 := preatom_lia.le t1 t2
notation d `∣*` t := preatom_lia.dvd d t
notation d `∤*` t := preatom_lia.ndvd d t

meta def preatom_lia.to_format : preatom_lia → format
| (t1 ≤* t2) := to_fmt t1 ++ " ≤ " ++ to_fmt t2 
| (d ∣* t) := to_fmt d ++ " ∣ " ++ to_fmt t 
| (d ∤* t) := to_fmt d ++ " ∤ " ++ to_fmt t

meta instance preatom_lia.has_to_format : has_to_format preatom_lia := ⟨preatom_lia.to_format⟩  

meta instance preatom_lia.has_reflect : has_reflect preatom_lia := by tactic.mk_has_reflect_instance

def preterm_lia.eval (zs : list int) : preterm_lia → int 
| (preterm_lia.var k) := list.inth zs k
| (preterm_lia.cst z) := z
| (preterm_lia.lmul z k) := z * (list.inth zs k)
| (preterm_lia.rmul k z) := (list.inth zs k) * z
| (preterm_lia.neg t) := -(preterm_lia.eval t)
| (preterm_lia.add t1 t2) := preterm_lia.eval t1 + preterm_lia.eval t2
| (preterm_lia.sub t1 t2) := preterm_lia.eval t1 - preterm_lia.eval t2

def preatom_lia.eval : list int → preatom_lia → Prop 
| zs (preatom_lia.le t1 t2) := preterm_lia.eval zs t1 ≤ preterm_lia.eval zs t2
| zs (preatom_lia.dvd d t) := d ∣ preterm_lia.eval zs t
| zs (preatom_lia.ndvd d t) := ¬(d ∣ preterm_lia.eval zs t)

@[derive has_reflect] 
inductive preformula_lia : Type 
| true  : preformula_lia
| false : preformula_lia
| atom : preatom_lia → preformula_lia 
| not : preformula_lia → preformula_lia 
| or  : preformula_lia → preformula_lia → preformula_lia  
| and : preformula_lia → preformula_lia → preformula_lia  
| imp : preformula_lia → preformula_lia → preformula_lia  
| iff : preformula_lia → preformula_lia → preformula_lia  
| fa  : preformula_lia → preformula_lia 
| ex  : preformula_lia → preformula_lia 
-- | ⊤* := sorry
-- | ⊥* := sorry
-- | (A* a) := sorry
-- | (¬* p) := sorry
-- | (p ∨* q) := sorry
-- | (p ∧* q) := sorry
-- | (p →* q) := sorry
-- | (p ↔* q) := sorry
-- | (∀* p) := sorry
-- | (∃* p) := sorry
notation `⊤*` := preformula_lia.true 
notation `⊥*` := preformula_lia.false 
notation `A*` a   := preformula_lia.atom a
notation `¬*` p   := preformula_lia.not p
notation p `∨*` q := preformula_lia.or p q 
notation p `∧*` q := preformula_lia.and p q 
notation p `→*` q := preformula_lia.imp p q 
notation p `↔*` q := preformula_lia.iff p q 
notation `∀*` p   := preformula_lia.fa p
notation `∃*` p   := preformula_lia.ex p

def preformula_lia.eval : list int → preformula_lia → Prop 
| zs preformula_lia.true := _root_.true
| zs preformula_lia.false := _root_.false 
| zs (preformula_lia.atom a) := a.eval zs  
| zs (preformula_lia.not φ) := ¬ (preformula_lia.eval zs φ)
| zs (preformula_lia.or  φ ψ) := (preformula_lia.eval zs φ) ∨ (preformula_lia.eval zs ψ)
| zs (preformula_lia.and φ ψ) := (preformula_lia.eval zs φ) ∧ (preformula_lia.eval zs ψ)
| zs (preformula_lia.imp φ ψ) := (preformula_lia.eval zs φ) → (preformula_lia.eval zs ψ)
| zs (preformula_lia.iff φ ψ) := (preformula_lia.eval zs φ) ↔ (preformula_lia.eval zs ψ)
| zs (preformula_lia.fa φ) := ∀ z, preformula_lia.eval (z::zs) φ 
| zs (preformula_lia.ex φ) := ∃ z, preformula_lia.eval (z::zs) φ 

#exit
def preformula_lia.eval : list int → preformula_lia → Prop 
| zs ⊤* := _root_.true
| zs ⊥* := _root_.false 
| zs (A* a) := a.eval zs  
| zs (¬* φ)   := ¬ (preformula_lia.eval zs φ)
| zs (φ ∨* ψ)  := (preformula_lia.eval zs φ) ∨ (preformula_lia.eval zs ψ)
| zs (φ ∧* ψ) := (preformula_lia.eval zs φ) ∧ (preformula_lia.eval zs ψ)
| zs (φ →* ψ) := (preformula_lia.eval zs φ) → (preformula_lia.eval zs ψ)
| zs (φ ↔* ψ) := (preformula_lia.eval zs φ) ↔ (preformula_lia.eval zs ψ)
| zs (∀* φ) := ∀ b, preformula_lia.eval (b::zs) φ 
| zs (∃* φ) := ∃ b, preformula_lia.eval (b::zs) φ 
