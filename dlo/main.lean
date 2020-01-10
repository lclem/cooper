import .reify .reify' .eval_qe

meta def quant_elim : tactic unit :=
pexact ``(eval_qe.elim_left _)

meta def dlo : tactic unit :=
reify' >> quant_elim >> tactic.exact_dec_trivial