import .formula

open tactic expr

meta def expr.to_term_lia : expr → tactic expr
| (expr.var k) := return (app `(term_dlo.var) `(k))
| r            := return (app `(term_dlo.cst) r)

meta def expr.to_atom_dlo : expr → tactic expr
| `(%%rx1 < %%rx2) := 
  do tx1 ← rx1.to_term_lia,
     tx2 ← rx2.to_term_lia,
     return (app (app `(atom_dlo.lt) tx1) tx2)
| `(%%rx1 = %%rx2) := 
  do tx1 ← rx1.to_term_lia,
     tx2 ← rx2.to_term_lia,
     return (app (app `(atom_dlo.eq) tx1) tx2)
| _ := fail "expr.to_atom_lia : unexpected case"
 
meta def expr.to_formula_dlo : expr → tactic expr
| `(true)  := return `(formula_dlo.true) 
| `(false) := return `(formula_dlo.false) 
| `(¬ %%px) :=  
  do fx ← expr.to_formula_dlo px, 
     return (app `(formula_dlo.not) fx)
| `(%%px ∨ %%qx) :=  
  do fx ← expr.to_formula_dlo px, 
     gx ← expr.to_formula_dlo qx, 
     return (app (app `(formula_dlo.or) fx) gx)
| `(%%px ∧ %%qx) :=  
  do fx ← expr.to_formula_dlo px, 
     gx ← expr.to_formula_dlo qx, 
     return (app (app `(formula_dlo.and) fx) gx)
| `(Exists %%(expr.lam _ _ _ px)) := 
  do fx ← expr.to_formula_dlo px, 
     return (app `(formula_dlo.ex) fx)
| `(Exists %%prx) := 
  do fx ← expr.to_formula_dlo (expr.app (prx.lift_vars 0 1) (expr.var 0)), 
     return (app `(formula_dlo.ex) fx)
| px := 
  do ax ← expr.to_atom_dlo px,
     return (app `(formula_dlo.atom) ax)

meta def reify' : tactic unit :=
do try `[simp only [ge, gt, le_iff_lt_or_eq,
     imp_iff_not_or, forall_iff_not_exists_not]], 
   gx ← target,
   fx ← expr.to_formula_dlo gx, 
   to_expr ``(@iff.elim_left ((%%fx).eval []) %%gx (iff.refl _) _) >>= apply >> skip

#exit
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
