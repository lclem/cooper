import .sqe .wf

open list

lemma atom.unify_dvd (m d i k ks) : 
  k ≠ 0 → atom.unify m (atom.dvd d i (k::ks)) = 
 (let m' := has_div.div m k in 
  atom.dvd (m' * d) (m' * i) (1 :: list.map (λ x, m' * x) ks)) := 
begin intro hne, cases k, exfalso, apply hne, repeat {refl} end

lemma atom.unify_ndvd (m d i k ks) : 
  k ≠ 0 → atom.unify m (atom.ndvd d i (k::ks)) = 
 (let m' := has_div.div m k in 
  atom.ndvd (m' * d) (m' * i) (1 :: list.map (λ x, m' * x) ks)) := 
begin intro hne, cases k, exfalso, apply hne, repeat {refl} end

lemma wf_inf_minus : 
  ∀ {p : formula}, formula.wf p → formula.wf (inf_minus p) 
| ⊤' h := by trivial
| ⊥' h := by trivial
| (A' a) h := 
  begin 
    cases a; try {trivial}, cases a_a_1 with z zs, 
    simp [inf_minus], rw inf_minus_le_eq,
    apply ite.rec; intro h, trivial,
    apply ite.rec; intro h; trivial 
  end
| (p ∧' q) h := 
  begin
    cases h with h1 h2, apply cases_and_o; try {trivial};
    try {apply wf_inf_minus, assumption},
    constructor; {apply wf_inf_minus, assumption}
  end
| (p ∨' q) h := 
  begin
    cases h with h1 h2, apply cases_or_o; try {trivial};
    try {apply wf_inf_minus, assumption},
    constructor; {apply wf_inf_minus, assumption}
  end
| (¬' p) h := by assumption
| (∃' p) h := by assumption

lemma wf_asubst :
  ∀ a : atom, atom.wf a → ∀ i ks, atom.wf (asubst i ks a) := 
begin
  intro a, cases a with i ks d i ks d i ks; 
  intros h i' ks'; cases ks with k ks; trivial
end

lemma wf_subst (i ks) : 
  ∀ p, formula.wf p → formula.wf (subst i ks p) 
| ⊤' h := by unfold subst
| ⊥' h := by unfold subst
| (A' a) h :=
  begin
    unfold subst, unfold formula.map,
    unfold formula.wf, apply wf_asubst _ h
  end
| (p ∧' q) h := 
  begin
    cases h with hp hq, apply and.intro; 
    apply wf_subst; assumption
  end
| (p ∨' q) h := 
  begin
    cases h with hp hq, apply and.intro; 
    apply wf_subst; assumption
  end
| (¬' p) h := wf_subst p h
| (∃' p) h := by unfold subst

lemma atom.wf_unify (z : znum) (hne : z ≠ 0) :
  ∀ (a : atom), atom.wf a → (head_coeff a ∣ z ∨ head_coeff a = 0)
  → atom.wf (atom.unify z a) 
| (atom.le i ks) ha1 ha2 := 
  begin cases ks with k ks, trivial, cases k with m m; trivial end
| (atom.dvd d i ks) ha1 ha2 := 
  begin
    cases ks with k ks, trivial, 
    cases (classical.em (k = 0)) with hk hk, 
    subst hk, trivial, cases ha2 with ha2 ha2,
    rewrite atom.unify_dvd, simp,
    apply znum.mul_nonzero, unfold head_coeff at ha2,
    apply znum.div_nonzero, apply hne, apply ha2, 
    apply ha1, apply hk, exfalso, apply hk ha2
  end
| (atom.ndvd d i ks) ha1 ha2 := 
  begin
    cases ks with k ks, trivial, 
    cases (classical.em (k = 0)) with hk hk, 
    subst hk, trivial, cases ha2 with ha2 ha2,
    rewrite atom.unify_ndvd, simp,
    apply znum.mul_nonzero, unfold head_coeff at ha2,
    apply znum.div_nonzero, apply hne, apply ha2, 
    apply ha1, apply hk, exfalso, apply hk ha2 
  end

meta def formula.wf_map_hco_of_formula.wf_tac :=
 `[unfold formula.map, unfold formula.wf,
   cases hn with hnp hnq, unfold formula.atoms at hnz, 
   rewrite list.forall_mem_append at hnz,
   cases hnz with hnzp hnzq, apply and.intro; 
   apply formula.wf_map_hco_of_formula.wf; assumption]

lemma formula.wf_map_hco_of_formula.wf {z : znum} (hz : z ≠ 0) :
  ∀ {p : formula}, (formula.wf p) 
  → (∀ a ∈ p.atoms, has_dvd.dvd (head_coeff a) z ∨ head_coeff a = 0) 
  → formula.wf (p.map (atom.unify z))  
| ⊤' hn hnz := by unfold formula.map 
| ⊥' hn hnz := by unfold formula.map 
| (A' a) hn hnz := 
  begin
    unfold formula.map, unfold formula.wf, unfold formula.wf at hn,
    apply atom.wf_unify z hz _ hn, apply hnz, 
    unfold formula.atoms, simp,
  end
| (p ∧' q) hn hnz := by formula.wf_map_hco_of_formula.wf_tac
| (p ∨' q) hn hnz := by formula.wf_map_hco_of_formula.wf_tac
| (¬' p) hp hpz :=
  begin
    unfold formula.map, unfold formula.wf, 
    apply @formula.wf_map_hco_of_formula.wf p hp hpz,
  end
| (∃' p) hn hnz := by unfold formula.map

lemma formula.wf_hcso : 
  ∀ {φ : formula}, formula.wf φ → formula.wf (φ.unify) := 
begin
  intros p hp, unfold formula.unify, unfold formula.wf, 
  have hne : znum.lcms (list.map head_coeff (p.atoms_dep_0)) ≠ 0, 
  { apply znum.nonzero_of_pos, apply znum.lcms_pos, 
    apply @forall_mem_map _ _ head_coeff (λ (z : znum), z ≠ 0), 
    unfold formula.atoms_dep_0, intros a ha, apply list.of_mem_filter ha },
  { apply and.intro, 
    { intro hc, apply hne hc },
    { apply formula.wf_map_hco_of_formula.wf hne hp, 
     intros a ha, apply or_of_not_imp_right,
     intro haz, apply znum.dvd_lcms,
     rewrite list.mem_map, existsi a, apply and.intro,
     unfold formula.atoms_dep_0, apply list.mem_filter_of_mem,
     apply ha, apply haz, refl } }
end

lemma wf_sqe_core : 
  ∀ {φ : formula}, formula.wf φ → formula.wf (sqe_core φ) := 
begin
  intros p hp, simp [sqe_core],
  apply wf_or_o, apply wf_disj,
  { apply forall_mem_map, 
    intros z hz, apply wf_subst,
    apply wf_inf_minus, apply hp },
  { apply wf_disj, apply forall_mem_map,
    intros zzs hzzs, apply wf_disj, 
    apply forall_mem_map, intros z hz,
    apply wf_subst, apply hp }
end

lemma wf_sqe : 
  ∀ (φ : formula), formula.wf φ → formula.wf (sqe φ) :=
begin
  intros p hp, apply wf_sqe_core,
  apply formula.wf_hcso hp
end
