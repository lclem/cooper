import .formula

open tactic


lemma term_dlo.eval_cst_eq {b1 b2 : rat} {bs : list rat} : 
b1 = b2 → term_dlo.eval bs (term_dlo.cst b1) = b2 :=
begin intro h, simp [term_dlo.eval, h] end

lemma term_dlo.eval_var_eq (k : nat) {b : rat} {bs} : 
list.inth bs k = b → (term_dlo.eval bs (term_dlo.var k) = b) := 
begin intro h, simp [term_dlo.eval, h] end

meta def reify_var (k : nat) : nat → tactic unit 
| n := 
  if n ≥ k then failed 
  else 
  (papply ``(term_dlo.eval_var_eq %%`(n)) >> papply ``(eq.refl _)) <|> reify_var (n+1) 

meta def reify_term_dlo : nat → tactic unit := 
λ k,
do ge ← target,
   match ge with
   --| `(_ = %%(expr.var _)) := reify_var k 0
   | `(_ = %%(expr.local_const _ _ _ _)) := reify_var k 0
   | `(_ = _) := papply ``(term_dlo.eval_cst_eq) >> reflexivity 
   | e := trace "Unexpected case for reify_term_dlo : " >> trace e >> failed
   end

lemma eval_lt_iff {t1 t2 : term_dlo} {d1 d2 : rat} {rs : list rat} : 
  t1.eval rs = d1 → t2.eval rs = d2 → 
  ((t1 <' t2).eval rs ↔ (d1 < d2)) := 
begin intros h1 h2, simp [formula_dlo.eval, atom_dlo.eval, h1, h2] end

lemma eval_eq_iff {t1 t2 : term_dlo} {d1 d2 : rat} {rs : list rat} : 
  term_dlo.eval rs t1 = d1 → term_dlo.eval rs t2 = d2 → 
  ((t1 =' t2).eval rs ↔ (d1 = d2)) := 
begin intros h1 h2, simp [formula_dlo.eval, atom_dlo.eval, h1, h2] end


meta def reify_atm (k : nat) : tactic unit :=
do ge ← target,
   match ge with
   | `(_ ↔ (_ < _)) := papply ``(eval_lt_iff); reify_term_dlo k
   | `(_ ↔ (_ = _)) := papply ``(eval_eq_iff); reify_term_dlo k
   | e := trace "Unexpected case for reify_atm : " >> trace e
   end

lemma eval_true_iff {rs : list rat} :
(⊤'.eval rs ↔ _root_.true) := iff.refl _

lemma eval_false_iff {rs : list rat} :
(⊥'.eval rs↔ _root_.false) := iff.refl _

lemma eval_atm_iff {a : atom_dlo} {φ : Prop} {rs : list rat} :
(a.eval rs ↔ φ) → ((A' a).eval rs ↔ φ) := 
begin intros h, simp [formula_dlo.eval, h] end

lemma eval_not_iff {π : formula_dlo} {φ} {rs : list rat} :
(π.eval rs ↔ φ) → ((¬' π).eval rs ↔ (¬ φ)) := 
begin intros h, simp [formula_dlo.eval, h] end

lemma eval_or_iff  {π ρ : formula_dlo} {φ ψ} {rs : list rat} :
(π.eval rs ↔ φ) → (ρ.eval rs ↔ ψ) → ((formula_dlo.or π ρ).eval rs ↔ (φ ∨ ψ)) := 
begin intros h1 h2, simp [formula_dlo.eval, h1, h2] end

lemma eval_and_iff  {p q : formula_dlo} {P Q} {rs : list rat} :
(p.eval rs ↔ P) → (q.eval rs ↔ Q) → ((formula_dlo.and p q).eval rs ↔ (P ∧ Q)) := 
begin intros h1 h2, simp [formula_dlo.eval, h1, h2] end

-- lemma eval_imp_iff  {π ρ : formula_dlo} {φ ψ} {rs : list rat} :
-- (π.eval rs ↔ φ) → (ρ.eval rs ↔ ψ) → ((formula_dlo.imp π ρ).eval rs ↔ (φ → ψ)) := 
-- begin intros h1 h2, simp [formula_dlo.eval, h1, h2] end
-- 
-- lemma eval_iff_iff {π ρ : formula_dlo} {φ ψ} {rs : list rat} :
-- (π.eval rs ↔ φ) → (ρ.eval rs ↔ ψ) → ((formula_dlo.iff π ρ).eval rs ↔ (φ ↔ ψ)) := 
-- begin intros h1 h2, simp [formula_dlo.eval, h1, h2] end

lemma eval_ex_iff {π : formula_dlo} {P : rat → Prop} {rs : list rat} :
(∀ r, π.eval (r::rs) ↔ P r) → ((formula_dlo.ex π).eval rs ↔ (∃ x, P x)) := 
begin intros h, simp [formula_dlo.eval, h] end

-- lemma eval_fa_iff {π} {P : rat → Prop} {rs : list rat} :
-- (∀ d, eval (d::ds) π ↔ P d) → ((formula_dlo.fa π).eval rs ↔ (∀ x, P x)) := 
-- begin intros h, simp [formula_dlo.eval, h] end



meta def reify_core : nat → tactic unit :=
λ k,
do ge ← target,
   match ge with
   | `(_ ↔ true) := 
     if k = 0 
     then papply ``(@eval_true_iff [])
     else papply ``(eval_true_iff) 
   | `(_ ↔ false) := 
     if k = 0 
     then papply ``(@eval_false_iff [])
     else papply ``(eval_false_iff) 
   | `(_ ↔ (¬ %%pe)) := 
     (if k = 0
      then papply ``(@eval_not_iff _ _ [])
      else papply ``(eval_not_iff)); reify_core k
   | `(_ ↔ (%%pe ∨ %%qe)) := 
     (if k = 0
      then papply ``(@eval_or_iff _ _ _ _ [])
      else papply ``(eval_or_iff)); reify_core k
   | `(_ ↔ (%%pe ∧ %%qe)) := 
     (if k = 0
      then papply ``(@eval_and_iff _ _ _ _ [])
      else papply ``(eval_and_iff)); reify_core k
   -- | `(_ ↔ (%%pe ↔ %%qe)) := 
   --   (if k = 0
   --    then papply ``(@eval_iff_iff _ _ _ _ _ [])
   --    else papply ``(eval_iff_iff)); reify_core k
   -- | `(_ ↔ %%(expr.pi _ _ pe qe)) := 
   --   if expr.has_var pe
   --   then (if k = 0
   --         then papply ``(@eval_imp_iff _ _ _ _ _ [])
   --         else papply ``(eval_imp_iff)); reify_core k
   --   else monad.cond (is_prop pe)
   --        ((if k = 0
   --          then papply ``(@eval_imp_iff _ _ _ _ _ [])
   --          else papply ``(eval_imp_iff)); reify_core k)
   --        ((if k = 0
   --          then papply ``(@eval_fa_iff _ _ _ _ [])
   --          else papply ``(eval_fa_iff))
   --          >> intro_fresh >> reify_core (k+1))
   | `(_ ↔ (Exists _)) := 
      (if k = 0 
       then papply ``(@eval_ex_iff _ _ [])
       else papply ``(eval_ex_iff)) >> intro_fresh >> reify_core (k+1)
   | `(_ ↔ _) := 
     (if k = 0
      then papply ``(@eval_atm_iff _ _ [])
      else papply ``(eval_atm_iff)) >> reify_atm k
   | _ := trace "Exception : reify_core" >> failed
   end

meta def reify : tactic unit :=
do try `[simp only [ge, gt, le_iff_lt_or_eq,
     imp_iff_not_or, forall_iff_not_exists_not]], 
   ge ← target,
   papply ``(@iff.elim_left _ %%ge _ _),
   rotate 1,
   reify_core 0
