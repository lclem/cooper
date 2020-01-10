import .formula .basic .dense_linear_order

open list --dnf

def get_lb : atom_dlo → option term_dlo
| (_ =' _) := none 
| ((term_dlo.var 0) <' (term_dlo.var 0)) := none
| ((term_dlo.var (n+1)) <' (term_dlo.var 0)) := some (term_dlo.var n)
| ((term_dlo.cst b) <' (term_dlo.var 0)) := some (term_dlo.cst b)
| (_ <' (term_dlo.var (n+1))) := none 
| (_ <' (term_dlo.cst _)) := none 

lemma of_get_lb_eq_some : 
  ∀ {a : atom_dlo} {t}, get_lb a = some t → a = (t.incr_idx <' V' 0) :=
begin
  intros a t h, cases a with t1 t2 t1 t2;
  cases t1 with k1 b1; cases t2 with k2 b2; try {cases h},
  { cases k1; cases k2; try {cases h}, refl },
  { cases k1; cases h },
  { cases k2; cases h, refl }
end

def lbs : list atom_dlo → list (term_dlo) := filter_map get_lb

def get_ub : atom_dlo → option (term_dlo)
| (_ =' _) := none 
| ((term_dlo.var 0) <' (term_dlo.var 0)) := none
| ((term_dlo.var 0) <' (term_dlo.var (n+1))) := some (term_dlo.var n)
| ((term_dlo.var 0) <' (term_dlo.cst b)) := some (term_dlo.cst b)
| ((term_dlo.var (n+1)) <' _) := none 
| ((term_dlo.cst _) <' _) := none 

def ubs : list atom_dlo → list (term_dlo) := filter_map get_ub

lemma of_get_ub_eq_some : 
  ∀ {a : atom_dlo} {t}, get_ub a = some t → a = (V' 0 <' t.incr_idx) := 
begin
  intros a t h, cases a with t1 t2 t1 t2;
  cases t1 with k1 b1; cases t2 with k2 b2; try {cases h};
  { cases k1; try {cases k2}; try {cases h}, refl },
end

def is_false_gnd_lt_atom_dlo : atom_dlo → Prop
| (term_dlo.cst a1 <' term_dlo.cst a2) := a2 ≤ a1
| _ := false

lemma not_eval_of_is_false_gnd_lt_atom_dlo : 
  ∀ {a : atom_dlo}, is_false_gnd_lt_atom_dlo a → ∀ {bs}, ¬ a.eval bs := 
begin
  intros a ha bs, cases a with t1 t2; 
  [{cases t1; cases t2}, {}]; try {cases ha},
  simp [atom_dlo.eval, term_dlo.eval], apply ha
end

instance dec_is_false_gnd_lt_atom_dlo : 
  decidable_pred is_false_gnd_lt_atom_dlo := 
begin
  intro a, cases a with t1 t2; [{cases t1; cases t2}, {}]; 
  try {simp [is_false_gnd_lt_atom_dlo]}; apply_instance,
end

def is_not_gnd_lt_atom_dlo : atom_dlo → Prop
| (term_dlo.cst a1 <' term_dlo.cst a2) := false
| _ := true

lemma eval_of_not_false_gnd_of_gnd : 
  ∀ {a : atom_dlo}, ¬ is_not_gnd_lt_atom_dlo a 
    → ¬ is_false_gnd_lt_atom_dlo a → ∀ {bs}, a.eval bs := 
begin
  intros a ha1 ha2 bs, cases a with t1 t2;
  [{cases t1; cases t2}, {}];
  try {simp [is_not_gnd_lt_atom_dlo] at ha1, cases ha1},
  simp [is_false_gnd_lt_atom_dlo] at ha2, apply ha2
end

instance dec_is_not_gnd_lt_atom_dlo : ∀ (a : atom_dlo), decidable (is_not_gnd_lt_atom_dlo a) :=
begin
  intro a, cases a with t1 t2; 
  [ {cases t1; cases t2}, {} ]; simp [is_not_gnd_lt_atom_dlo]; 
  { apply decidable.true <|> apply decidable.false }
end

def new_lt_atom_dlos (as : list atom_dlo) : list atom_dlo := 
let prs := product (lbs as) (ubs as) in
map (λ (pr : term_dlo × term_dlo), pr.fst <' pr.snd) prs 

def sqe_aux (as : list atom_dlo) : list atom_dlo := 
let nas := new_lt_atom_dlos as in
if (∃ a, a ∈ nas ∧ is_false_gnd_lt_atom_dlo a) 
  then [C' 0 <' C' 0]  
  else (filter is_not_gnd_lt_atom_dlo nas)

def sqe (as : list atom_dlo) : list atom_dlo := 
if h : (V' 0 <' V' 0) ∈ as
  then [C' 0 <' C' 0]
  else sqe_aux as 

lemma forall_mem_new_lt_atom_dlos_eval {as : list atom_dlo} {b bs} :
  (∀ t ∈ lbs as, term_dlo.eval bs t < b) → (∀ t ∈ ubs as, b < term_dlo.eval bs t)
  → ∀ a ∈ new_lt_atom_dlos as, atom_dlo.eval bs a := 
begin
  intros hb1 hb2 a ha1, simp [new_lt_atom_dlos] at ha1,
  cases ha1 with t1 ha1, cases ha1 with t2 ha1, 
  cases ha1 with ha1 ha3, subst ha3, simp [atom_dlo.eval],
  apply @lt.trans _ _ _ b _ (hb1 _ ha1.left) (hb2 _ ha1.right) 
end

def is_lb : atom_dlo → Prop
| (t1 <' t2) := ¬ t1 = term_dlo.var 0 ∧ t2 = term_dlo.var 0
| (t1 =' t2) := false

def is_ub : atom_dlo → Prop
| (t1 <' t2) := t1 = V' 0 ∧ ¬ t2 = V' 0
| (t1 =' t2) := false


lemma is_lb_or_is_ub {a : atom_dlo} : 
  dep_0 a → ¬solv_0 a → a ≠ (V' 0<' V' 0) → is_lb a ∨ is_ub a := 
begin
  intros h1 h2 h3, cases a with t1 t2 t1 t2,
  { by_cases h1d : t1 = V' 0; by_cases h2d : t2 = V' 0,
    { subst h1d, subst h2d, exfalso, apply h3, refl },
    { apply or.inr, constructor; assumption },
    { apply or.inl, constructor; assumption },
    { cases h1; contradiction } },
  { simp [solv_0, not_or_distrib] at h2, cases h2, 
    cases h1; contradiction }
end

lemma is_midpoint_iff  : 
∀ {as : list atom_dlo}, 
  (∀ a ∈ as, is_lb a ∨ is_ub a) → 
  ∀ {b bs}, ((∀ t ∈ lbs as, term_dlo.eval bs t < b) ∧ (∀ t ∈ ubs as, b < term_dlo.eval bs t))
            ↔ ∀ a ∈ as, atom_dlo.eval (b :: bs) a :=
begin
  intros as has b bs, constructor; intro h,
  {
    intros a ha, cases has _ ha with hbnd hbnd;
    cases a with t1 t2 t1 t2; cases hbnd with h1 h2,
    { subst h2, cases t1 with k r, 
      { cases k, exfalso, apply h1 rfl, 
        apply h.left (V' k) _, simp [lbs, mem_filter_map], 
        constructor, apply and.intro ha, refl },
      { apply h.left (C' r) _, simp [lbs, mem_filter_map], 
        constructor, apply and.intro ha, refl } },
    { subst h1, cases t2 with k r, 
      { cases k, exfalso, apply h2 rfl, 
        apply h.right (V' k) _, simp [ubs, mem_filter_map], 
        constructor, apply and.intro ha, refl },
      { apply h.right (C' r) _, simp [ubs, mem_filter_map], 
        constructor, apply and.intro ha, refl } } },
  {
    constructor; intros t ht,
    { simp [lbs] at ht, cases ht with a ha,
      have hrw := (of_get_lb_eq_some ha.right), subst hrw,
      rw (term_dlo.eval_incr_idx_eq.symm), apply h _ ha.left },
    { simp [ubs] at ht, cases ht with a ha,
      have hrw := (of_get_ub_eq_some ha.right), subst hrw,
      rw (term_dlo.eval_incr_idx_eq.symm), apply h _ ha.left }
  }
end

lemma eval_sqe :
∀ {as : list atom_dlo}, 
 (∀ a ∈ as, dep_0 a) → (∀ a ∈ as, ¬solv_0 a) 
  → ∀ {bs : list rat}, avals bs (sqe as) ↔ ∃ x, avals (x :: bs) as := 
begin
  intros as has1 has2 bs, simp [sqe], 
  apply @ite.rec _ _ _ 
  (λ φ, avals bs φ ↔ ∃ x, avals (x::bs) as); intro h1,
  { constructor; intro h, 
    { exfalso, apply lt_irrefl _ (h _ (or.inl rfl)) },
    { cases h with r hr, exfalso, apply lt_irrefl _ (hr _ h1) } },
  { simp [sqe_aux],
    apply @ite.rec _ _ _
      (λ φ, avals bs φ ↔ ∃ x, avals (x :: bs) as); intro h2,
    { 
      constructor; intro h; exfalso,
      { apply lt_irrefl _ (h _ (or.inl rfl)) },
      { 
        cases h2 with a ha, cases h with b hb,
        apply @not_eval_of_is_false_gnd_lt_atom_dlo a ha.right bs, 
        apply @forall_mem_new_lt_atom_dlos_eval as b _ _ _ _ ha.left;
        intros t ht; simp [lbs, ubs] at ht; cases ht with a' ha';
        cases ha' with ha1' ha2';
        [ { have hrw := (of_get_lb_eq_some ha2') },  
          { have hrw := (of_get_ub_eq_some ha2') } ]; 
        { subst hrw, have h := hb _ ha1', 
          simp [atom_dlo.eval, term_dlo.eval_incr_idx_eq] at h, apply h }
      } 
    },
    { simp [avals], 
       -- have hrw := (@forall_mem_filter _ is_not_gnd_lt_atom_dlo 
       --   _ _ (new_lt_atom_dlos as)), rw hrw, 
      apply calc 
        (∀ a ∈ new_lt_atom_dlos as, is_not_gnd_lt_atom_dlo a → a.eval bs)  
      ↔ ∃ b, (∀ t ∈ lbs as, term_dlo.eval bs t < b) ∧ (∀ t ∈ ubs as, b < term_dlo.eval bs t) : 
        begin
          constructor; intro h3,
          { 
            by_cases hl : lbs as = [], 
            { rw hl, simp, cases exists_lower_bound (map (term_dlo.eval bs) (ubs as)) 
              with b hb, existsi b, intros t ht, apply hb _ (mem_map_of_mem _ ht) },
            {
              by_cases hu : ubs as = [], 
              { rw hu, simp, cases exists_upper_bound (map (term_dlo.eval bs) (lbs as)) 
                with b hb, existsi b, intros t ht, apply hb _ (mem_map_of_mem _ ht) },
              { 
                cases @exists_maximum _ _ (map (term_dlo.eval bs) (lbs as)) _ with x hx;
                [{}, {apply map_ne_nil_of_ne_nil hl}], cases hx with hx1 hx2,
                cases @exists_minimum _ _ (map (term_dlo.eval bs) (ubs as)) _ with y hy;
                [{}, {apply map_ne_nil_of_ne_nil hu}], cases hy with hy1 hy2,
                have hlt : x < y, 
                  { 
                    rw mem_map at hx1, cases hx1 with tx htx,
                    cases htx with htx hrw, subst hrw,
                    rw mem_map at hy1, cases hy1 with ty hty,
                    cases hty with hty hrw, subst hrw,
                    have hmem : (tx <' ty) ∈ new_lt_atom_dlos as, 
                      { simp [new_lt_atom_dlos], existsi tx, existsi ty,
                        constructor; constructor; {assumption <|> refl} },
                    by_cases hgnd : is_not_gnd_lt_atom_dlo (tx <' ty),
                    { apply h3 _ hmem hgnd },
                    { apply eval_of_not_false_gnd_of_gnd hgnd _, intro hc, 
                      apply h2, constructor, apply and.intro hmem hc }
                  },
                cases dense hlt with b hb, existsi b,
                constructor; intros t ht,
                { apply lt_of_le_of_lt (hx2 _ _) hb.left, 
                  apply mem_map_of_mem _ ht },
                { apply lt_of_lt_of_le hb.right (hy2 _ _), 
                  apply mem_map_of_mem _ ht }
              }
            }
          },
          { cases h3 with b hb, intros a ha1 _,
            apply forall_mem_new_lt_atom_dlos_eval hb.left hb.right _ ha1 }
        end
  ... ↔ ∃ b, ∀ a ∈ as, atom_dlo.eval (b::bs) a : 
        begin
          apply exists_iff_exists, intro b, apply is_midpoint_iff, 
          intros a ha, apply is_lb_or_is_ub (has1 _ ha) (has2 _ ha), 
          intro hc, subst hc, apply h1 ha,
        end
    }
  }


end

#exit


instance dlo_rat.has_sqe_eq : has_sqe_eq rat :=
{
  sqe := dlo_rat.sqe,
  forall_mem_sqe_normal := λ _ _ _ _, trivial,
  eval_sqe_iff := λ as _ h _, @dlo_rat.eval_sqe_iff as h,
}

instance dlo_rat.dec_eval_qe := @dnf.dec_eval_qe rat _ @dlo_rat.dec_aval

meta def dlo_rat.qelim : tactic unit :=
papply ``((@dnf.eval_qe_iff rat dlo_rat.has_sqe_eq _ _ []).elim_left _)