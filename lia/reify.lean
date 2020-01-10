import ..tactics .preformula

variable (α : Type)

open tactic
 
meta def expr.to_preterm_lia : expr → tactic preterm_lia 
| (expr.var k) := return (preterm_lia.var k)
| `(%%zx * %%(expr.var k)) := 
  do z ← eval_expr int zx, return (preterm_lia.lmul z k)
| `(%%(expr.var k) * %%zx) := 
  do z ← eval_expr int zx, return (preterm_lia.rmul k z)
| `(- %%tx) := 
  do t ← expr.to_preterm_lia tx, return (preterm_lia.neg t)
| `(%%t1x + %%t2x) := 
  do t1 ← expr.to_preterm_lia t1x, 
     t2 ← expr.to_preterm_lia t2x, 
     return (preterm_lia.add t1 t2)
| `(%%t1x - %%t2x) := 
  do t1 ← expr.to_preterm_lia t1x,
     t2 ← expr.to_preterm_lia t2x,
     return (preterm_lia.sub t1 t2)
| zx := do z ← eval_expr int zx, return (preterm_lia.cst z)

meta def expr.to_preatom_lia : expr → tactic preatom_lia 
| `(%%t1x ≤ %%t2x) :=
  do t1 ← expr.to_preterm_lia t1x,
     t2 ← expr.to_preterm_lia t2x,
     return (t1 ≤* t2)
| `(%%dx ∣ %%tx) :=
  do d ← eval_expr int dx,
     t ← expr.to_preterm_lia tx,
     return (d ∣* t)
| _ := trace "Invalid input for expr.to_ptm" >> failed
 
meta def expr.to_preformula_lia : expr → tactic preformula_lia
| `(true)  := return ⊤* 
| `(false) := return ⊥* 
| `(¬ %%e) := 
  do p ← expr.to_preformula_lia e, 
  return (¬* p) 
| `(%%x1 ∨ %%x2) := 
  do p ← expr.to_preformula_lia x1,
     q ← expr.to_preformula_lia x2, 
     return (p ∨* q)
| `(%%x1 ∧ %%x2) := 
  do p ← expr.to_preformula_lia x1, 
     q ← expr.to_preformula_lia x2, 
     return (p ∧* q)
| `(%%x1 ↔ %%x2) := 
  do p ← expr.to_preformula_lia x1, 
     q ← expr.to_preformula_lia x2, 
     return (p ↔* q)
| `(%%(expr.pi _ _ x1 x2)) := 
  monad.cond 
   (if expr.has_var x1 then return true else is_prop x1)
   (do p ← (expr.to_preformula_lia x1), 
       q ← (expr.to_preformula_lia (x2.lower_vars 1 1)), 
       return $ p →* q) 
   (do q ← (expr.to_preformula_lia x2), return (∀* q))
| `(Exists %%(expr.lam _ _ _ px)) := do p ← expr.to_preformula_lia px, return (∃* p)
| `(Exists %%prx) := 
  do p ← expr.to_preformula_lia (expr.app (prx.lift_vars 0 1) (expr.var 0)), 
    return (∃* p)
| e := do a ← expr.to_preatom_lia e, return (A* a)

meta def reify : tactic unit :=
do `[try {simp only [ge, gt, int.lt_iff_add_one_le, le_antisymm_iff, mul_add, add_mul]}],
   g ← target,
   p ← expr.to_preformula_lia g, 
   to_expr ``(@iff.elim_left ((%%`(p)).eval []) %%g (iff.refl _) _) >>= apply >> skip