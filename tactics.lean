open tactic 

meta def papply (pe : pexpr) := to_expr pe >>= apply >> skip 
meta def pexact (pe : pexpr) := to_expr pe >>= exact

meta def intro_fresh : tactic expr :=
get_unused_name >>= intro

#exit



meta def exact_dec_trivial_1 (x : expr) : tactic unit :=
to_expr ``(@of_as_true %%x) >>= apply >> skip

meta def exact_dec_trivial_2 : tactic unit := tactic.triv

meta def exact_dec_trivial : tactic unit :=
do t ← target, 
   to_expr ``(@of_as_true %%t) >>= apply, 
   tactic.triv
