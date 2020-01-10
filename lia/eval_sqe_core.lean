import .sqe .qfree .wf --..equiv ..num .sqe

open list

def atom.unified (a : atom) : Prop :=
  head_coeff a = -1 ∨ head_coeff a = 0 ∨ head_coeff a = 1

def unified (p : formula) : Prop := ∀ a ∈ p.atoms, (atom.unified a)

lemma eval_subst_iff {i ks xs} :
  ∀ {p}, nqfree p →
    ((subst i ks p).eval xs ↔ p.eval ((i + znum.dot_prod ks xs)::xs))
| ⊤' _ := by refl
| ⊥' _ := by refl
| (A' (atom.le i ks')) _ :=
  begin
    simp [subst, formula.map], cases ks' with k' ks';
    simp [asubst, eval_le],
    simp [znum.comp_add_dot_prod, znum.dot_prod, mul_add,
    znum.map_mul_dot_prod],
  end
| (A' (atom.ndvd d i ks')) _ :=
  begin
    simp [subst, formula.map], cases ks' with k' ks';
    simp [asubst, eval_ndvd],
    simp [znum.comp_add_dot_prod, znum.dot_prod, mul_add,
    znum.map_mul_dot_prod],
  end
| (A' (atom.dvd d i ks')) _ :=
  begin
    simp [subst, formula.map], cases ks' with k' ks';
    simp [asubst, eval_dvd],
    simp [znum.comp_add_dot_prod, znum.dot_prod, mul_add,
    znum.map_mul_dot_prod]
  end
| (p ∧' q) hf :=
  begin
    cases hf with hfp hfq,
    unfold subst, unfold formula.map,
    repeat {rewrite eval_and},
    let ihp := @eval_subst_iff p hfp,
    unfold subst at ihp, rewrite ihp,
    let ihq := @eval_subst_iff q hfq,
    unfold subst at ihq, rewrite ihq
  end
| (p ∨' q) hf :=
  begin
    cases hf with hfp hfq,
    unfold subst, unfold formula.map,
    repeat {rewrite eval_or},
    let ihp := @eval_subst_iff p hfp,
    unfold subst at ihp, rewrite ihp,
    let ihq := @eval_subst_iff q hfq,
    unfold subst at ihq, rewrite ihq
  end
| (¬' p) hf := by cases hf
| (∃' p) hf := by cases hf

lemma inf_minus_prsv (zs) : ∀ (p : formula),
  ∃ (y : znum), ∀ z, z < y →
    ((inf_minus p).eval (z::zs) ↔ p.eval (z::zs))
| ⊤' := begin existsi (0 : znum), intros z hz, constructor; intro hc; trivial end
| ⊥' := begin existsi (0 : znum), intros z hz, constructor; intro hc; cases hc end
| (A' (atom.le i ks)) :=
  begin
    cases ks with k ks,
    { existsi (0 : znum), intros z hz, refl },
    cases (lt_trichotomy k 0) with hlt heqgt;
    [ {}, { cases heqgt with heq hgt } ],
    {
      existsi (- abs (i - znum.dot_prod ks zs)), intros z hz,
      simp [inf_minus_le_eq_of_lt hlt],
      constructor; intro h,
      {
        simp [formula.eval,  atom.eval, znum.dot_prod],
        rw sub_le_iff_le_add'.symm,
        apply calc
              i - znum.dot_prod ks zs
            ≤ abs (i - znum.dot_prod ks zs) : le_abs_self _
        ... ≤ -z : begin rw lt_neg at hz, apply le_of_lt hz end
        ... ≤ k * z :
            begin
              rw (znum.neg_one_mul_eq_neg).symm, repeat {rw mul_comm _ z},
              rw znum.mul_le_mul_iff_le_of_neg_left,
              apply znum.le_of_lt_add_one, apply hlt,
              apply lt_of_lt_of_le hz (neg_le_of_neg_le _),
              have h := abs_nonneg (i - znum.dot_prod ks zs), apply h
            end
      },
      { trivial }
    },
    { subst heq, simp [inf_minus_le_eq_of_eq] },
    {
      existsi (- abs (i - znum.dot_prod ks zs)), intros z hz,
      simp [inf_minus_le_eq_of_gt hgt], constructor; intro h,
      { cases h },
      { apply absurd h,
        simp [formula.eval,  atom.eval, znum.dot_prod],
        rw lt_sub_iff_add_lt'.symm,
        apply calc
              k * z
            ≤ 1 * z :
              begin
                repeat {rw (mul_comm _ z)},
                rw znum.mul_le_mul_iff_le_of_neg_left,
                apply znum.add_one_le_of_lt hgt,
                apply lt_of_lt_of_le hz (neg_le_of_neg_le _),
                apply abs_nonneg (i - znum.dot_prod ks zs)
              end
        ... = z : one_mul _
        ... < - abs (i - znum.dot_prod ks zs) : hz
        ... ≤ i - znum.dot_prod ks zs :
              begin
                rw neg_le,
                apply neg_le_abs_self (i - znum.dot_prod ks zs),
              end
      }
    }
  end
| (A' (atom.dvd d i ks)) := begin simp [inf_minus] end
| (A' (atom.ndvd d i ks)) := begin simp [inf_minus] end
| (p ∧' q) :=
  begin
    cases (inf_minus_prsv p) with x hx,
    cases (inf_minus_prsv q) with y hy,
    cases (znum.exists_lt_and_lt x y) with z hz,
    cases hz with hz1 hz2, existsi z, intros w hw,
    simp [inf_minus, eval_and_o, eval_and,
      hx w (lt.trans hw hz1), hy w (lt.trans hw hz2)]
  end
| (p ∨' q) :=
  begin
    cases (inf_minus_prsv p) with x hx,
    cases (inf_minus_prsv q) with y hy,
    cases (znum.exists_lt_and_lt x y) with z hz,
    cases hz with hz1 hz2, existsi z, intros w hw,
    simp [inf_minus, eval_or_o, eval_or,
      hx w (lt.trans hw hz1), hy w (lt.trans hw hz2)]
  end
| (¬' p) := begin simp [inf_minus] end
| (∃' p) := begin simp [inf_minus] end

lemma divisors_lcm_pos {p : formula} :
  formula.wf p → 0 < divisors_lcm p :=
begin
  intro hn, apply znum.lcms_pos,
  intros z hz, rewrite list.mem_map at hz,
  cases hz with a ha, cases ha with ha1 ha2,
  subst ha2, unfold formula.atoms_dep_0 at ha1,
  rw (@mem_filter _ dep_0 _ a (p.atoms)) at ha1,
  rewrite wf_iff_wf_alt at hn,
  rewrite iff.symm normal_iff_divisor_nonzero,
  apply hn, apply ha1^.elim_left
end

lemma divisors_lcm_dvd_eq {d i k : znum} {ks : list znum} :
  k ≠ 0 → divisors_lcm (A' (atom.dvd d i (k::ks))) = abs d :=
begin
  intro h, simp [divisors_lcm, formula.atoms_dep_0, formula.atoms,
    dep_0, filter, head_coeff], rw if_pos,
  simp [map, divisor, znum.lcms, znum.lcm, num.lcm, znum.abs_eq_abs_to_znum,
    num.to_znum, znum.abs_one, num.gcd_one_right, num.div_one],
  apply h
end

lemma divisors_lcm_ndvd_eq {d i k : znum} {ks : list znum} :
  k ≠ 0 → divisors_lcm (A' (atom.ndvd d i (k::ks))) = abs d :=
begin
  intro h, simp [divisors_lcm, formula.atoms_dep_0,
    formula.atoms, dep_0, filter, head_coeff], rw if_pos,
  simp [map, divisor, znum.lcms, znum.lcm, num.lcm, znum.abs_eq_abs_to_znum,
    num.to_znum, znum.abs_one, num.gcd_one_right, num.div_one],
  apply h
end

lemma divisors_lcm_and_eq (p q) :
  divisors_lcm (p ∧' q) = znum.lcm (divisors_lcm p) (divisors_lcm q) :=
begin
  apply znum.lcms_distrib, apply list.equiv.trans,
  apply list.map_equiv_map_of_equiv,
  simp [formula.atoms_dep_0, formula.atoms], apply equiv.refl,
  simp [map_append, formula.atoms_dep_0],
  apply equiv.symm union_equiv_append,
end

lemma divisors_lcm_or_eq (p q) :
  divisors_lcm (p ∨' q) = znum.lcm (divisors_lcm p) (divisors_lcm q) :=
begin
  apply znum.lcms_distrib, apply list.equiv.trans,
  apply list.map_equiv_map_of_equiv,
  simp [formula.atoms_dep_0, formula.atoms], apply equiv.refl,
  simp [map_append, formula.atoms_dep_0],
  apply equiv.symm union_equiv_append,
end

lemma inf_minus_mod {k z zs} :
  ∀ {p}, nqfree p → (has_dvd.dvd (divisors_lcm p) k)
    → ( (inf_minus p).eval (z % k :: zs)
         ↔ (inf_minus p).eval (z :: zs) )
| ⊤' _ _ := begin constructor; intro h; trivial end
| ⊥' _ _ := begin constructor; intro hc; cases hc end
| (A' (atom.le i [])) hf hdvd :=
  begin simp [inf_minus, eval_le] end
| (A' (atom.le i (k'::ks'))) hf hdvd :=
  begin
    cases (lt_trichotomy k' 0) with hlt heqgt;
    [ {}, { cases heqgt with heq hgt } ],
    { simp [inf_minus_le_eq_of_lt hlt], trivial },
    { subst heq, simp [inf_minus_le_eq_of_eq, eval_le, znum.dot_prod] },
    { simp [inf_minus_le_eq_of_gt hgt], trivial },
  end
| (A' (atom.dvd d i [])) hf hdvd :=
  begin simp [inf_minus, eval_dvd] end
| (A' (atom.dvd d i (k::ks))) hf hdvd :=
  begin
    simp [inf_minus], by_cases hkz : k = 0,
    { subst hkz, simp [eval_dvd, znum.dot_prod] },
    { apply eval_mod_dvd,
      simp [divisors_lcm_dvd_eq hkz] at hdvd,
      rw znum.abs_dvd at hdvd, assumption }
  end
| (A' (atom.ndvd d i [])) hf hdvd :=
  begin simp [inf_minus, eval_ndvd] end
| (A' (atom.ndvd d i (k::ks))) hf hdvd :=
  begin
    simp [inf_minus], by_cases hkz : k = 0,
    { subst hkz, simp [eval_ndvd, znum.dot_prod] },
    { apply eval_mod_ndvd,
      simp [divisors_lcm_ndvd_eq hkz] at hdvd,
      rw znum.abs_dvd at hdvd, assumption }
  end
| (p ∧' q) hf hdvd :=
  begin
    cases hf with hfp hfq, simp [inf_minus, eval_and_o],
    rw [@inf_minus_mod p, @inf_minus_mod q]; try {assumption};
    apply dvd.trans _ hdvd; rw [divisors_lcm_and_eq],
    apply znum.dvd_lcm_right, apply znum.dvd_lcm_left,
  end
| (p ∨' q) hf hdvd :=
  begin
    cases hf with hfp hfq, simp [inf_minus, eval_or_o],
    rw [@inf_minus_mod p, @inf_minus_mod q]; try {assumption};
    apply dvd.trans _ hdvd; rw [divisors_lcm_or_eq],
    apply znum.dvd_lcm_right, apply znum.dvd_lcm_left,
  end
| (¬' p) hf _ := by cases hf
| (∃' p) hf _ := by cases hf

lemma no_lb_inf_minus {p : formula} (hf : nqfree p) (hn : formula.wf p) (z : znum) (zs) :
  (inf_minus p).eval (z::zs) → ∀ y, ∃ x, (x < y ∧ (inf_minus p).eval (x::zs)) :=
begin
  intros h y,
  have hlt : z - ((abs z + abs y + 1) * divisors_lcm p) < y,
  { simp [add_mul],
    repeat {rw (add_assoc _ _ _).symm}, rw (add_comm z),
    apply calc
          -divisors_lcm p + z + -(abs z * divisors_lcm p)
          + -(abs y * divisors_lcm p)
        < -(abs y * divisors_lcm p) :
          begin
            apply add_lt_of_neg_of_le,
            { rw add_assoc, apply add_neg_of_neg_of_nonpos,
              { rw neg_lt, apply divisors_lcm_pos hn },
              { rw le_sub_iff_add_le.symm, rw [zero_sub, neg_neg],
                apply le_trans (le_abs_self z), rw mul_comm,
                apply znum.le_mul_of_pos_left (abs_nonneg _),
                apply divisors_lcm_pos hn } },
            { apply le_refl (-(abs y * divisors_lcm p)) }
          end
    ... ≤ -(abs y) * 1:
          begin
            rw [neg_mul_eq_neg_mul],
            apply @mul_le_mul_of_nonpos_left _ _ _ _ (-abs y),
            apply @znum.add_one_le_of_lt 0 (divisors_lcm p),
            apply divisors_lcm_pos hn, rw neg_le, apply abs_nonneg y
          end
    ... = -(abs y): mul_one _
    ... ≤ y : begin rw neg_le, apply neg_le_abs_self y end
  },
  existsi (z - (abs z + abs y + 1) * divisors_lcm p),
  constructor, assumption,
  rw (inf_minus_mod hf (dvd_refl _)).symm,
  rw (inf_minus_mod hf (dvd_refl _)).symm at h,
  have heq : (z - (abs z + abs y + 1) * divisors_lcm p) % divisors_lcm p = z % divisors_lcm p,
  { rw [sub_eq_add_neg, neg_mul_eq_neg_mul],
    apply znum.add_mul_mod_self },
  rw heq, assumption,
end

lemma nqfree_inf_minus_of_nqfree :
  ∀ {p}, nqfree p → nqfree (inf_minus p)
| ⊤' h := h
| ⊥' h := h
| (A' a) h :=
  begin
    cases a with i ks d i ks di ks;
    cases ks with k ks;
    unfold inf_minus,
    apply ite.rec; intro _, trivial,
    apply ite.rec; intro _; trivial
  end
| (p ∧' q) h :=
  begin
    cases h with h1 h2, unfold inf_minus,
    apply cases_and_o, trivial,
    repeat {apply nqfree_inf_minus_of_nqfree, assumption},
    apply and.intro; apply nqfree_inf_minus_of_nqfree;
    assumption
  end
| (p ∨' q) h :=
  begin
    cases h with h1 h2, unfold inf_minus,
    apply cases_or_o, trivial,
    repeat {apply nqfree_inf_minus_of_nqfree, assumption},
    apply and.intro; apply nqfree_inf_minus_of_nqfree;
    assumption
  end
| (¬' p) h := by cases h
| (∃' p) h := by cases h

lemma ex_iff_inf_or_bnd (P : znum → Prop) :
  (∃ z, P z) ↔ ((∀ y, ∃ x, x < y ∧ P x) ∨ (∃ y, (P y ∧ ∀ x, x < y → ¬ P x))) :=
begin
  apply iff.intro; intro h1,
  { rw @or_iff_not_imp_left _ _ (classical.dec _), intro h2,
    rw (@not_forall _ _ (classical.dec _) (classical.dec_pred _)) at h2,
    cases h1 with w hw, cases h2 with lb hlb, simp at hlb,
    apply znum.exists_min_of_exists_lb hw hlb },
  { cases h1 with hinf hbnd, cases (hinf 0) with z hz,
    existsi z, apply hz^.elim_right, cases hbnd with z hz,
    existsi z, apply hz^.elim_left }
end

lemma mod_znum.mem_range :
  ∀ {x y}, (0 ≠ y) → x % y ∈ znum.range y :=
begin
  intros x y hy, apply znum.mem_range',
  apply znum.mod_nonneg _ hy.symm,
  apply znum.mod_lt _ hy.symm,
end

lemma unified_and_iff (p q : formula) : unified (p ∧' q) ↔ (unified p ∧ unified q) :=
begin unfold unified, unfold formula.atoms, apply list.forall_mem_append end

lemma unified_or_iff (p q : formula) : unified (p ∨' q) ↔ (unified p ∧ unified q) :=
begin unfold unified, unfold formula.atoms, apply list.forall_mem_append end

lemma bnd_points_and_equiv {p q} :
  bnd_points (p ∧' q) ≃ (bnd_points p ∪ bnd_points q) :=
begin
  simp [bnd_points, formula.atoms_dep_0,
    dep_0, formula.atoms, filter_map_append_eq],
  apply equiv.symm union_equiv_append,
end

lemma bnd_points_or_equiv {p q} :
  bnd_points (p ∨' q) ≃ (bnd_points p ∪ bnd_points q) :=
begin
  simp [bnd_points, formula.atoms_dep_0,
    dep_0, formula.atoms, filter_map_append_eq],
  apply equiv.symm union_equiv_append,
end

lemma eval_sqe_core_iff_aux {z : znum} {zs : list znum} :
∀ {p : formula}, nqfree p → formula.wf p → unified p
  → ∀ {k}, 0 < k → (has_dvd.dvd (divisors_lcm p) k)
    → ¬ p.eval (z :: zs) → p.eval ((z + k)::zs)
    →  ∃ iks, iks ∈ bnd_points p ∧
        ∃ (d : znum), (0 ≤ d ∧ d < k
          ∧ z + k = (d + (prod.fst iks) - znum.dot_prod ((iks.snd)) zs))
| ⊤' hf hn hu k _ hk h1 h2 := by trivial
| ⊥' hf hn hu k _ hk h1 h2 := by trivial
| (A' (atom.le i ks)) hf hn hu k hkp hk h1 h2 :=
  begin
    have hex : ∃ ks', ks = (1::ks'),
    {
      simp [formula.eval,  atom.eval, znum.dot_prod] at *,
      have hlt := lt_of_lt_of_le h1 h2,
      cases ks with k' ks',
      { exfalso, cases hlt },
      {
        cases (hu _ (or.inl rfl)) with hk' hk' hk';
        simp [head_coeff] at hk',
        { exfalso, subst hk', simp [znum.dot_prod, lt_neg, neg_zero] at hlt,
          apply znum.lt_irrefl _ (lt.trans hlt hkp) },
        { cases hk',
          { exfalso, subst hk', simp [znum.dot_prod] at hlt,
            apply znum.lt_irrefl _ hlt },
          { subst hk', constructor, refl }
        }
      }
    },
    cases hex with xs hxs, subst hxs,
    existsi (i,xs), constructor,
    { rw bnd_points_le_eq, apply or.inl rfl, apply zero_lt_one },
    {
      simp, existsi (z + k - (i - (znum.dot_prod xs zs))), constructor,
      { simp [formula.eval,  atom.eval, znum.dot_prod] at h2,
        rw [le_sub_iff_add_le, add_sub, sub_le_iff_le_add,
            zero_add, add_assoc], assumption, },
      { constructor,
        { simp [formula.eval,  atom.eval, znum.dot_prod] at h1,
          rw [sub_lt_iff_lt_add', add_lt_add_iff_right, lt_sub_iff_add_lt],
          assumption },
        { simp } }
    }
  end
| (A' (atom.ndvd d i ks)) hf hn hu k hkp hk h1 h2 :=
  begin
    exfalso, simp [formula.eval,  atom.eval, znum.dot_prod] at h1 h2,
    have h3 : (d ∣ i + znum.dot_prod ks (z :: zs))
      ↔ (d ∣ i + znum.dot_prod ks ((z + k) :: zs)),
    {
      cases ks with x ks; simp [znum.dot_prod],
      by_cases hx : x = 0,
      { subst hx, simp },
      { simp [mul_add], rw (add_assoc _ (x*z) _).symm,
        rw (add_assoc i _ (x*k)).symm, apply dvd_add_iff_left,
        apply dvd_mul_of_dvd_right, rw [divisors_lcm_ndvd_eq hx] at hk,
        rw znum.abs_dvd at hk, assumption }
    },
    rw h3 at h1, apply h2 h1
 end
| (A' (atom.dvd d i ks)) hf hn hu k hkp hk h1 h2 :=
begin
  exfalso, simp [formula.eval,  atom.eval, znum.dot_prod] at h1 h2,
  have h3 : (d ∣ i + znum.dot_prod ks (z :: zs))
    ↔ (d ∣ i + znum.dot_prod ks ((z + k) :: zs)),
  {
    cases ks with x ks; simp [znum.dot_prod],
    by_cases hx : x = 0,
    { subst hx, simp },
    { simp [mul_add], rw (add_assoc _ (x*z) _).symm,
      rw (add_assoc i _ (x*k)).symm, apply dvd_add_iff_left,
      apply dvd_mul_of_dvd_right, rw [divisors_lcm_dvd_eq hx] at hk,
      rw znum.abs_dvd at hk, assumption }
  },
  rw h3 at h1, apply h1 h2
end
| (p ∨' q) hf hn hu k hkp hk h1 h2 :=
  begin
    simp [eval_or, not_or_distrib] at h1,
    simp [eval_or] at h2, cases h1 with hp hq,
    cases hn with hnp hnq, cases hf with hfp hfq,
    rw unified_or_iff at hu, cases hu with hup huq,
    rw divisors_lcm_or_eq at hk,
    have hdp := dvd.trans (znum.dvd_lcm_left _ _) hk,
    have hdq := dvd.trans (znum.dvd_lcm_right _ _) hk,
    cases h2 with h2 h2;
    [ {cases (@eval_sqe_core_iff_aux p _ _ _ _ hkp _ _ _) with iks hiks},
      {cases (@eval_sqe_core_iff_aux q _ _ _ _ hkp _ _ _) with iks hiks} ];
    try {assumption};
    `[cases hiks with hm h, existsi iks, apply and.intro,
    rw mem_iff_mem_of_equiv (bnd_points_or_equiv) ],
    apply mem_union_left hm, assumption,
    apply mem_union_right _ hm, assumption
  end
| (p ∧' q) hf hn hu k hkp hk h1 h2 :=
  begin
    rw [eval_and] at h1, rw [@not_and_distrib' _ _ (classical.dec _)] at h1,
    simp [eval_and] at h2, cases h2 with hp hq,
    cases hn with hnp hnq, cases hf with hfp hfq,
    rw unified_and_iff at hu, cases hu with hup huq,
    rw divisors_lcm_and_eq at hk,
    have hdp := dvd.trans (znum.dvd_lcm_left _ _) hk,
    have hdq := dvd.trans (znum.dvd_lcm_right _ _) hk,
    cases h1 with h1 h1;
    [ {cases (@eval_sqe_core_iff_aux p _ _ _ _ hkp _ _ _) with iks hiks},
      {cases (@eval_sqe_core_iff_aux q _ _ _ _ hkp _ _ _) with iks hiks} ];
    try {assumption};
    `[ cases hiks with hm h, existsi iks, apply and.intro,
       rw mem_iff_mem_of_equiv (bnd_points_and_equiv) ],
    apply mem_union_left hm, assumption,
    apply mem_union_right _ hm, assumption
  end
| (¬' p) hf hn hu k _ hk h1 h2 := by cases hf
| (∃' p) hf hn hu k _ hk h1 h2 := by cases hf


lemma eval_sqe_core_iff :
  ∀ (p : formula), nqfree p → formula.wf p → unified p
  → ∀ (bs : list znum), (sqe_core p).eval bs ↔ ∃ (b : znum), p.eval (b :: bs) :=
begin
  intros p hf hn hu zs, constructor; intro h,
  {
    simp [sqe_core, sqe_inf, sqe_bnd, eval_or_o, eval_disj_map] at h,
    cases h with h h; cases h with z hz,
    {
      cases hz with hz1 hz2, rw eval_subst_iff at hz2,
      { simp [znum.nil_dot_prod, @add_zero znum] at hz2,
        cases (inf_minus_prsv zs p) with lb hlb,
        cases (no_lb_inf_minus hf hn z zs hz2 lb) with x hx,
        cases hx with hx1 hx2, rw hlb _ hx1 at hx2,
        existsi x, assumption },
      { apply nqfree_inf_minus_of_nqfree hf }
    },
    {
      cases hz with zs hzs,
      cases hzs with hzs1 hzs2, cases hzs2 with k hk,
      cases hk with hk1 hk2, rw (eval_subst_iff hf) at hk2,
      constructor, apply hk2,
    }
  },
  {
    simp [sqe_core, eval_or_o],
    rewrite ex_iff_inf_or_bnd at h, cases h with h h,
    {
      apply or.inl, simp [sqe_inf], rw eval_disj_map,
      have hw : ∃ w, formula.eval (w :: zs) (inf_minus p),
      { cases (inf_minus_prsv zs p) with lb hlb,
        cases h lb with w h, cases h with h1 h2,
        existsi w, rw (hlb _ h1), assumption },
      cases hw with w hw,
      have hwm : formula.eval ((w % divisors_lcm p)::zs) (inf_minus p),
      { rw inf_minus_mod; try {assumption}, apply dvd_refl },
      existsi (w % divisors_lcm p), constructor,
      { apply mod_znum.mem_range, apply ne.symm,
        apply znum.nonzero_of_pos, apply divisors_lcm_pos hn },
      { rw eval_subst_iff, simp [znum.dot_prod_nil, @zero_add znum],
        apply hwm, apply nqfree_inf_minus_of_nqfree hf }
    },
    {
      cases h with lb hlb, cases hlb with hlb1 hlb2, apply or.inr,

      have h :=
        @eval_sqe_core_iff_aux
          (lb - (divisors_lcm p)) zs p hf hn hu
          (divisors_lcm p) (divisors_lcm_pos hn)
          (dvd_refl _)
          (begin
            apply hlb2, rewrite sub_lt_self_iff,
            apply divisors_lcm_pos hn,
           end)
          (begin simp, apply hlb1 end),

      cases h with iks h, cases h with hiks h, cases h with k' h,
      cases h with h1 h, cases h with h2 h3, simp at h3, subst h3,

      simp [sqe_bnd, eval_disj_map],
      existsi iks.fst, existsi iks.snd, apply and.intro,
      { cases iks, simp, apply hiks },
      { existsi k', constructor,
        { apply znum.mem_range h1 h2 },
        { rw [eval_subst_iff, znum.map_neg_dot_prod],
          rw (add_comm iks.fst), rw add_assoc,
          apply hlb1, apply hf }
      }
     }
  }
end
