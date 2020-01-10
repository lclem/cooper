import ..tactics .reify .normalize .eval_qe .bval

open tactic

meta def lia : tactic unit := 
do reify, normalize, quant_elim,
   exact_dec_trivial, -- `[simp only [list.map]],
   exact_dec_trivial

axiom any : ∀ {p : Prop}, p

meta def vm_dec_eval : tactic unit :=
do `((qe %%fx).eval _) ← target,
   f ← eval_expr formula fx,
   match (dec_eval_qe f []) with
   | (is_true _) := admit --p`apply ``(any)
   | _ := failed
   end 

meta def vm_dec_eval' : tactic unit :=
do `((qe %%fx).eval _) ← target,
   monad.cond (eval_expr bool `(bval %%fx))
   admit failed
   -- match b with
   -- | tt := papply ``(any)
   -- | ff := failed
   -- end 

meta def lia_vm : tactic unit := 
do reify, normalize, quant_elim,
   exact_dec_trivial, -- `[simp only [list.map]],
   vm_dec_eval

meta def lia_vm' : tactic unit := 
do reify, normalize, quant_elim,
   exact_dec_trivial, -- `[simp only [list.map]],
   vm_dec_eval'