import .formula ..logic

def dep_0 : atom_dlo → Prop 
| (t1 =' t2) := t1 = V' 0 ∨ t2 = V' 0
| (t1 <' t2) := t1 = V' 0 ∨ t2 = V' 0

instance dec_dep_0 : decidable_pred dep_0 
| (x <' y) := begin simp [dep_0], apply_instance end
| (x =' y) := begin simp [dep_0], apply_instance end

def solv_0 : atom_dlo → Prop 
| (t1 <' t2) := false
| (t1 =' t2) := t1 = V' 0 ∨ t2 = V' 0

instance dec_solv_0 : decidable_pred solv_0
| (t1 <' t2) := decidable.is_false (by simp [solv_0])
| (t1 =' t2) := or.decidable 

def term_dlo.decr_idx : term_dlo → term_dlo 
| (term_dlo.var m) := term_dlo.var (m-1)
| (term_dlo.cst b) := term_dlo.cst b

def atom_dlo.decr_idx : atom_dlo → atom_dlo 
| (atom_dlo.lt t1 t2) := atom_dlo.lt (term_dlo.decr_idx t1) (term_dlo.decr_idx t2)
| (atom_dlo.eq t1 t2) := atom_dlo.eq (term_dlo.decr_idx t1) (term_dlo.decr_idx t2)

def term_dlo.subst_0 : term_dlo → term_dlo → term_dlo 
| t (term_dlo.var 0) := term_dlo.decr_idx t
| t (term_dlo.var (k+1)) := term_dlo.var k
| t (term_dlo.cst b) := term_dlo.cst b

def term_dlo.subst_0' : atom_dlo → term_dlo → term_dlo 
| ((term_dlo.var 0) =' t) := term_dlo.subst_0 t
| (t =' (term_dlo.var 0)) := term_dlo.subst_0 t
| _ := id

lemma term_dlo.subst_0'_left {t : term_dlo} : 
  term_dlo.subst_0' (term_dlo.var 0 =' t) = term_dlo.subst_0 t := 
begin cases t, simp [term_dlo.subst_0'], refl end

lemma term_dlo.subst_0'_right {t : term_dlo} : 
  term_dlo.subst_0' (t =' term_dlo.var 0) = term_dlo.subst_0 t := 
begin cases t with k, cases k with k; refl, refl end

def atom_dlo.subst_0 : atom_dlo → atom_dlo → atom_dlo  
| a (t1 <' t2) := (term_dlo.subst_0' a t1) <' (term_dlo.subst_0' a t2)
| a (t1 =' t2) := (term_dlo.subst_0' a t1) =' (term_dlo.subst_0' a t2)


def trv : atom_dlo → Prop 
| (atom_dlo.lt t1 t2) := false
| (atom_dlo.eq t1 t2) := t1 = t2

instance dec_trv : decidable_pred trv
| (atom_dlo.lt t1 t2) := decidable.is_false (by simp [trv])
| (atom_dlo.eq t1 t2) := begin simp [trv], apply_instance end

lemma of_trv  :
  ∀ {a : atom_dlo}, trv a → ∀ {bs : list rat}, atom_dlo.eval bs a :=
begin 
  intros a ha, cases a, exfalso, apply ha, simp [trv] at ha, 
  rw ha, intro bs, simp [atom_dlo.eval]
end


lemma term_dlo.eval_decr_idx_eq :
  ∀ (t : term_dlo), ¬(t = term_dlo.var 0) → ∀ (b : rat) (bs : list rat), 
    term_dlo.eval bs (term_dlo.decr_idx t) = term_dlo.eval (b :: bs) t := 
begin
  intros t ht b bs, cases t with k b, cases k with k,
  exfalso, apply ht, repeat {simp [term_dlo.decr_idx, term_dlo.eval]}
end

lemma atom_dlo.eval_decr_idx_iff :
  ∀ {a : atom_dlo}, ¬(dep_0 a) → ∀ {b : rat} {bs : list rat}, 
    atom_dlo.eval bs (atom_dlo.decr_idx a) ↔ atom_dlo.eval (b :: bs) a := 
begin
  intros a ha b bs, cases a with t1 t2 t1 t2;
  {simp [dep_0, not_or_distrib] at ha,
  cases ha with ha1 ha2, simp [atom_dlo.eval, atom_dlo.decr_idx],
  repeat {rw [term_dlo.eval_decr_idx_eq _ _ b bs]}; assumption}
end

lemma of_solv_0 : 
  ∀ {a : atom_dlo}, solv_0 a → ∀ {bs : list rat}, ∃ (b : rat), atom_dlo.eval (b :: bs) a := 
begin
  intros a ha rs, cases a; cases ha; subst ha,
  { cases a_a_1 with k r, cases k with k, existsi (0 : rat), 
    simp [atom_dlo.eval], existsi (list.inth rs k), simp [atom_dlo.eval, 
    term_dlo.eval], existsi r, simp [atom_dlo.eval, term_dlo.eval] },
  { cases a_a with k r, cases k with k, existsi (0 : rat), 
    simp [atom_dlo.eval], existsi (list.inth rs k), simp [atom_dlo.eval, 
    term_dlo.eval], existsi r, simp [atom_dlo.eval, term_dlo.eval] },
end

lemma trv_subst_0_of_trv :
∀ {a : atom_dlo}, trv a → ∀ (eq : atom_dlo), trv (atom_dlo.subst_0 eq a) := 
begin
  intros a ha, cases a; cases ha, 
  intro eq, simp [atom_dlo.subst_0, trv] 
end

lemma eval_decr_idx_eq_of_ne_var_0 {t : term_dlo} :
  t ≠ term_dlo.var 0 → ∀ b bs, term_dlo.eval bs (term_dlo.decr_idx t) = term_dlo.eval (b::bs) t := 
begin
  intros h b bs, cases t with k b, 
  cases k with k, exfalso, apply h, refl, 
  repeat {simp [term_dlo.decr_idx, term_dlo.eval]}
end

lemma eval_subst_0_eq 
  {b : rat} {bs : list rat} {t1 t2 : term_dlo}
  (h2 : t2 ≠ term_dlo.var 0) (h3 : b = term_dlo.eval (b :: bs) t2) : 
  term_dlo.eval bs (term_dlo.subst_0 t2 t1) = term_dlo.eval (b :: bs) t1 :=
begin
  cases t1 with k b1; 
  [ 
    {
      cases k with k; 
      [
        {simp [term_dlo.subst_0, term_dlo.eval], rw h3, 
          apply eval_decr_idx_eq_of_ne_var_0 h2}, 
        {simp [term_dlo.subst_0, term_dlo.eval]}
      ]
    }, 
    {simp [term_dlo.subst_0, term_dlo.eval]}
  ] 
end

lemma eval_subst_0'_eq 
  {a1 : atom_dlo} {h1 : solv_0 a1} {h2 : ¬trv a1}
  {b : rat} {bs : list rat} {h3 : atom_dlo.eval (b :: bs) a1} {t1 t2 : term_dlo} :
  term_dlo.eval bs (term_dlo.subst_0' a1 t1) = term_dlo.eval (b :: bs) t1 :=
begin
  cases a1; cases h1; subst h1; 
  [
    {rw term_dlo.subst_0'_left,
     apply eval_subst_0_eq (ne.symm h2) h3}, 
    {rw term_dlo.subst_0'_right,
     apply eval_subst_0_eq h2 (eq.symm h3)} 
  ]
end

lemma eval_subst_0_iff :
 ∀ {a1 : atom_dlo}, solv_0 a1 → ¬ trv a1 → 
   ∀ {b} {bs : list rat}, atom_dlo.eval (b :: bs) a1 
   → ∀ {a2 : atom_dlo}, atom_dlo.eval bs (atom_dlo.subst_0 a1 a2) ↔ atom_dlo.eval (b :: bs) a2 := 
begin
  intros a1 h1 h2 b bs h3 a2,
  cases a2 with t1 t2 t1 t2;
  simp [atom_dlo.eval];
  [ 
    {apply lt_iff_lt_of_eq_of_eq, 
     repeat {apply eval_subst_0'_eq; assumption}}, 
    {apply eq_iff_eq_of_eq_of_eq, 
     repeat {apply eval_subst_0'_eq; assumption}} 
  ]
end

#exit

def atom_dlo.decr_idx : atom_dlo → atom_dlo 
| (atom_dlo.lt t1 t2) := atom_dlo.lt (term_dlo.decr_idx t1) (term_dlo.decr_idx t2)
| (atom_dlo.eq t1 t2) := atom_dlo.eq (term_dlo.decr_idx t1) (term_dlo.decr_idx t2)

def term_dlo.subst_0 : term_dlo → term_dlo → term_dlo 
| t (term_dlo.var 0) := term_dlo.decr_idx t
| t (term_dlo.var (k+1)) := term_dlo.var k
| t (term_dlo.cst b) := term_dlo.cst b

def term_dlo.subst_0' : atom_dlo → term_dlo → term_dlo 
| ((term_dlo.var 0) =' t) := term_dlo.subst_0 t
| (t =' (term_dlo.var 0)) := term_dlo.subst_0 t
| _ := id

lemma term_dlo.subst_0'_left {t : term_dlo} : 
  term_dlo.subst_0' (term_dlo.var 0 =' t) = term_dlo.subst_0 t := 
begin cases t, simp [term_dlo.subst_0'], refl end

lemma term_dlo.subst_0'_right {t : term_dlo} : 
  term_dlo.subst_0' (t =' term_dlo.var 0) = term_dlo.subst_0 t := 
begin cases t with k, cases k with k; refl, refl end

def atom_dlo.subst_0 : atom_dlo → atom_dlo → atom_dlo  
| a (t1 <' t2) := (term_dlo.subst_0' a t1) <' (term_dlo.subst_0' a t2)
| a (t1 =' t2) := (term_dlo.subst_0' a t1) =' (term_dlo.subst_0' a t2)