import .eval_sqe_core .qfree_sqe .wf_sqe

open list

lemma hco_le_eq_of_ne_zero {m i k ks} :
k ≠ 0 → atom.unify m (atom.le i (k::ks)) = 
  let m' := (m / (abs k)) in 
  atom.le (m' * i) (znum.sign k :: map_mul m' ks) := 
begin intro h, simp [atom.unify], rw if_neg, apply h end

lemma hco_dvd_eq_of_ne_zero {m d i k ks} :
k ≠ 0 → atom.unify m (atom.dvd d i (k::ks)) =
  let m' := (m / k) in 
  atom.dvd (m' * d) (m' * i) (1 :: map_mul m' ks) := 
begin intro h, simp [atom.unify], rw if_neg, apply h end

lemma hco_ndvd_eq_of_ne_zero {m d i k ks} :
k ≠ 0 → atom.unify m (atom.ndvd d i (k::ks)) =
  let m' := (m / k) in 
  atom.ndvd (m' * d) (m' * i) (1 :: map_mul m' ks) := 
begin intro h, simp [atom.unify], rw if_neg, apply h end

lemma clcm_le_eq_of_ne_zero {i k : znum} {ks : list znum} :
  k ≠ 0 → coeffs_lcm (A' (atom.le i (k::ks))) = abs k := 
begin
  intro h, simp [coeffs_lcm, formula.atoms_dep_0, 
     dep_0, formula.atoms, filter, head_coeff ],
  rw if_pos, simp [head_coeff, znum.lcms, znum.lcm, num.lcm,
    znum.abs_eq_abs_to_znum, znum.abs_one,
    num.gcd_one_right, num.div_one], apply h
end

lemma clcm_dvd_eq_of_ne_zero {d i k : znum} {ks : list znum} :
  k ≠ 0 → coeffs_lcm (A' (atom.dvd d i (k::ks))) = abs k := 
begin
  intro h, simp [coeffs_lcm, formula.atoms_dep_0, 
     dep_0, formula.atoms, filter, head_coeff ],
  rw if_pos, simp [head_coeff, znum.lcms, znum.lcm, num.lcm,
    znum.abs_eq_abs_to_znum, znum.abs_one,
    num.gcd_one_right, num.div_one], apply h
end

lemma clcm_ndvd_eq {d i : znum} {ks : list znum} :
  coeffs_lcm (A' (atom.ndvd d i ks))
  = coeffs_lcm (A' (atom.dvd d i ks)) :=
begin
  cases ks with k ks; simp [coeffs_lcm, formula.atoms_dep_0, 
     dep_0, formula.atoms, filter, head_coeff ],
  by_cases hkz : k = 0,
  { subst hkz, repeat {rw if_neg}, simp, simp, },
  { repeat {rw if_pos}, simp [head_coeff], assumption, assumption }
end

lemma eval_hco_le_iff {lcm z i : znum} {zs ks : list znum}
  (hpos : 0 < lcm) (hdvd : coeffs_lcm (A' atom.le i ks) ∣ lcm) :
  (A' (atom.unify lcm (atom.le i ks))).eval (lcm * z :: zs) 
  ↔ (A' (atom.le i ks)).eval (z :: zs) :=
begin
  cases ks with k ks,
  { simp [atom.unify, eval_le] },
  {
    by_cases hkz : k = 0, 
    { subst hkz, simp [atom.unify, eval_le, znum.dot_prod] },
    { 
      rw clcm_le_eq_of_ne_zero hkz at hdvd, 
      rw (hco_le_eq_of_ne_zero hkz), simp [eval_le, znum.dot_prod],
      apply calc
            lcm / abs k * i ≤ znum.sign k * (lcm * z) + znum.dot_prod (map_mul (lcm / abs k) ks) zs 
          ↔ (lcm / abs k) * i ≤ (lcm / abs k) * (znum.dot_prod ks zs + k * z) : 
            begin
              rw [mul_add, add_comm, znum.map_mul_dot_prod],
              have heq : znum.sign k * (lcm * z) = lcm / abs k * (k * z),
              { rw [(mul_assoc _ k _).symm, (znum.div_mul_comm _ _ _ hdvd),
                    (mul_comm lcm k), (znum.div_mul_comm _ _ _ _).symm,
                    znum.sign_eq_div_abs, mul_assoc], rw znum.abs_dvd,
                apply dvd_refl }, 
              rw heq,
            end
      ... ↔ i ≤ znum.dot_prod ks zs + k * z : 
            begin 
              apply znum.mul_le_mul_iff_le_of_pos_left,
              apply znum.div_pos_of_pos_of_dvd hpos (abs_nonneg _) hdvd
            end
    }
  }
end 

lemma eval_hco_dvd_iff {lcm z d i : znum} {zs ks}
  (hpos : lcm > 0) (hdvd : coeffs_lcm (A' atom.dvd d i ks) ∣ lcm) :
  (A' (atom.unify lcm (atom.dvd d i ks))).eval (lcm * z :: zs) 
  ↔ (A' (atom.dvd d i ks)).eval (z :: zs) :=
begin
  cases ks with k ks,
  { simp [atom.unify, eval_dvd] },
  {
    by_cases hkz : k = 0, 
    { subst hkz, simp [atom.unify, eval_dvd, znum.dot_prod] },
    {
      rw clcm_dvd_eq_of_ne_zero hkz at hdvd, 
      rw (hco_dvd_eq_of_ne_zero hkz), simp [eval_dvd, znum.dot_prod], 
      apply calc 
            lcm / k * d ∣ lcm * z + (lcm / k * i + znum.dot_prod (map_mul (lcm / k) ks) zs) 
          ↔ (lcm / k) * d ∣ (lcm / k) * (i + (znum.dot_prod ks zs + k * z)) : 
            begin
              rw [mul_add, znum.map_mul_dot_prod, 
                add_comm, mul_add, add_assoc],
              have heq : lcm / k * (k * z) = lcm * z, 
              { rw [(mul_assoc _ _ _).symm, znum.div_mul_cancel],
                rw znum.abs_dvd at hdvd, apply hdvd }, 
              rw heq
            end
      ... ↔ d ∣ i + (znum.dot_prod ks zs + k * z) : 
            begin
              apply mul_dvd_mul_iff_left, apply znum.div_nonzero,
              apply znum.nonzero_of_pos hpos, 
              rw znum.abs_dvd at hdvd, apply hdvd,
            end
    }
  }
end 

lemma eval_hco_ndvd_iff {m d i ks} {zs : list znum} :
 (A' (atom.unify m (atom.ndvd d i ks))).eval zs 
 ↔ ¬ (A' (atom.unify m (atom.dvd d i ks))).eval zs := 
begin
  cases ks with k ks;
  simp [atom.unify, eval_dvd, eval_ndvd],
  by_cases hkz : k = 0,
  { subst hkz, repeat {rw if_pos}, 
    simp [eval_dvd, eval_ndvd], refl },
  { repeat {rw if_neg}, 
    simp [eval_dvd, eval_ndvd], 
    assumption, assumption }
end

lemma coeffs_lcm_and (p q) :
  coeffs_lcm (p ∧' q) = znum.lcm (coeffs_lcm p) (coeffs_lcm q) := 
begin
  apply znum.lcms_distrib, apply list.equiv.trans, 
  apply list.map_equiv_map_of_equiv, 
  simp [formula.atoms_dep_0, formula.atoms], apply equiv.refl,
  simp [map_append, formula.atoms_dep_0],
  apply equiv.symm union_equiv_append,
end

lemma coeffs_lcm_or (p q) :
  coeffs_lcm (p ∨' q) = znum.lcm (coeffs_lcm p) (coeffs_lcm q) := 
begin
  apply znum.lcms_distrib, apply list.equiv.trans, 
  apply list.map_equiv_map_of_equiv, 
  simp [formula.atoms_dep_0, formula.atoms], apply equiv.refl,
  simp [map_append, formula.atoms_dep_0],
  apply equiv.symm union_equiv_append,
end

lemma hcso_prsv_1 (lcm z : znum) (zs) (hlcm1 : lcm > 0) (hdvd : lcm ∣ z) :
  ∀ (p : formula), nqfree p → formula.wf p → (has_dvd.dvd (coeffs_lcm p) lcm)
  → (formula.map (atom.unify lcm) p).eval (z::zs) → p.eval ((has_div.div z lcm)::zs) 
| ⊤' hf hn _ h := begin simp [eval_true] end
| ⊥' hf hn _ h := begin exfalso, apply h end
| (A' (atom.le i ks)) hf hn hlcm2 h := 
  begin
    simp [formula.map] at h, have heq : z = lcm * (z / lcm), 
    { rw [mul_comm, znum.div_mul_cancel hdvd] },
    rw heq at h, rw eval_hco_le_iff at h; try {assumption}, 
  end
| (A' (atom.dvd d i ks)) hf hn hlcm2 h := 
  begin
    simp [formula.map] at h, have heq : z = lcm * (z / lcm), 
    { rw [mul_comm, znum.div_mul_cancel hdvd] }, rw heq at h,
    rewrite eval_hco_dvd_iff at h; try {assumption}, 
  end
| (A' (atom.ndvd d i ks)) hf hn hlcm2 h := 
  begin
    simp [formula.map] at h, have heq : z = lcm * (z / lcm), 
    { rw [mul_comm, znum.div_mul_cancel hdvd] }, rw heq at h, 
    rewrite eval_hco_ndvd_iff at h, rewrite eval_hco_dvd_iff at h,
    rw eval_ndvd', assumption, assumption,
    rw clcm_ndvd_eq at hlcm2, assumption,
  end
| (p ∧' q) hf hn hlcm2 h := 
  begin
    rewrite eval_and, cases hf with hfp hfq, cases hn with hnp hnq,
    unfold formula.map at h, cases h with hp hq, rewrite coeffs_lcm_and at hlcm2, 
    apply and.intro; apply hcso_prsv_1; try {assumption},
    apply dvd.trans _ hlcm2, apply znum.dvd_lcm_left,
    apply dvd.trans _ hlcm2, apply znum.dvd_lcm_right,
  end
  | (p ∨' q) hf hn hlcm2 h := 
  begin
    rewrite coeffs_lcm_or at hlcm2, rewrite eval_or, 
    cases hf with hfp hfq, cases hn with hnp hnq,
    unfold formula.map at h, rewrite eval_or at h, cases h with hp hq,
    apply or.inl, apply hcso_prsv_1; try {assumption},
    apply dvd.trans _ hlcm2, apply znum.dvd_lcm_left,
    apply or.inr, apply hcso_prsv_1; try {assumption},
    apply dvd.trans _ hlcm2, apply znum.dvd_lcm_right
  end
| (¬' p) hf hn _ h := by cases hf
| (∃' p) hf hn _ h := by cases hf

lemma hcso_prsv_2 (lcm z : znum) (zs) (hpos : lcm > 0) :
  ∀ (p : formula), nqfree p → formula.wf p → has_dvd.dvd (coeffs_lcm p) lcm
  → p.eval (z::zs) → (formula.map (atom.unify lcm) p).eval ((lcm * z)::zs) 
| ⊤' hf hn hdvd h := trivial
| ⊥' hf hn hdvd h := by cases h
| (A' (atom.le i ks)) hf hn hdvd h := 
  begin
    unfold formula.map, rewrite eval_hco_le_iff, 
    apply h, apply hpos, apply hdvd
  end
| (A' (atom.dvd d i ks)) hf hn hdvd h := 
  begin
    unfold formula.map, rewrite eval_hco_dvd_iff, 
    apply h, apply hpos, apply hdvd
  end
| (A' (atom.ndvd d i ks)) hf hn hdvd h := 
  begin
    unfold formula.map, rw [eval_hco_ndvd_iff, eval_hco_dvd_iff],
    apply h, apply hpos, rw clcm_ndvd_eq at hdvd, apply hdvd
  end
| (p ∧' q) hf hn hdvd h := 
  begin
    unfold formula.map, rewrite eval_and, 
    rewrite eval_and at h, cases h with hp hq,
    cases hn with hnp hnq, cases hf with hfp hfq,
    rewrite coeffs_lcm_and at hdvd, apply and.intro; 
    apply hcso_prsv_2; try {assumption},
    apply dvd.trans _ hdvd, apply znum.dvd_lcm_left,
    apply dvd.trans _ hdvd, apply znum.dvd_lcm_right
  end
| (p ∨' q) hf hn hdvd h := 
  begin
    unfold formula.map, rewrite eval_or, rewrite eval_or at h, 
    cases hn with hnp hnq, cases hf with hfp hfq,
    rewrite coeffs_lcm_or at hdvd,
    cases h with hp hq, apply or.inl, 
    apply hcso_prsv_2; try {assumption},
    apply dvd.trans _ hdvd, apply znum.dvd_lcm_left,
    apply or.inr, apply hcso_prsv_2; try {assumption},
    apply dvd.trans _ hdvd, apply znum.dvd_lcm_right
  end
| (¬' p) hf hn hdvd h := by cases hf
| (∃' p) hf hn hdvd h := by cases hf

lemma coeffs_lcm_pos (p) :
  coeffs_lcm p > 0 := 
begin
  apply znum.lcms_pos,
  intros z hz, rewrite list.mem_map at hz,
  cases hz with a ha, cases ha with ha1 ha2,
  subst ha2, unfold formula.atoms_dep_0 at ha1,
  rw (@mem_filter _ dep_0 _ a (formula.atoms p)) at ha1,
  apply ha1^.elim_right
end

lemma hcso_prsv :  
∀ (p : formula) (hf : nqfree p) (hn : formula.wf p) (bs : list znum),
(∃ (b : znum), (p.unify).eval (b :: bs)) ↔ ∃ (b : znum), p.eval (b :: bs) :=
begin
  intros p hf hn bs, apply iff.intro; 
  intro h; cases h with z hz, 
  { unfold formula.unify at hz, rewrite eval_and at hz,
    existsi (has_div.div z (coeffs_lcm p)), 
    cases hz with hz1 hz2, apply hcso_prsv_1; 
    try {assumption}, rewrite eval_dvd at hz1, 
    rewrite zero_add at hz1, apply coeffs_lcm_pos,
    simp [eval_dvd, znum.dot_prod] at hz1, 
    apply hz1, apply dvd_refl },
  { existsi (coeffs_lcm p * z), unfold formula.unify,
    rewrite eval_and, apply and.intro,
    rewrite eval_dvd, rewrite zero_add,
    simp [znum.dot_prod], apply hcso_prsv_2;
    try {assumption}, apply coeffs_lcm_pos, 
    apply dvd_refl }
end

lemma unified_sign {k} : 
  znum.sign k = -1 ∨ znum.sign k = 0 ∨ znum.sign k = 1 := 
begin
  cases lt_trichotomy k 0 with h h,
  { rw znum.sign_eq_neg_one_of_neg h, apply or.inl rfl },
  cases h with h h,
  { rw znum.sign_eq_zero_iff_zero, apply or.inr (or.inl h) },
  { rw znum.sign_eq_one_of_pos h, apply or.inr (or.inr rfl) },
end

lemma unified_atom_hco {k} : 
  ∀ {a}, (atom.unify k a).unified
| (atom.le i []) := or.inr (or.inl rfl)
| (atom.ndvd d i []) := or.inr (or.inl rfl)
| (atom.le i (k::ks)) :=  
  begin
    by_cases hkz : k = 0,
    { subst hkz, apply or.inr (or.inl rfl) },
    { rw hco_le_eq_of_ne_zero hkz, apply unified_sign }
  end
| (atom.dvd d i []) := or.inr (or.inl rfl) 
| (atom.dvd d i (k::ks)) := 
  begin
    by_cases hkz : k = 0,
    { subst hkz, apply or.inr (or.inl rfl) },
    { rw hco_dvd_eq_of_ne_zero hkz, apply or.inr (or.inr rfl) }
  end
| (atom.ndvd d i (k::ks)) := 
  begin
    by_cases hkz : k = 0,
    { subst hkz, apply or.inr (or.inl rfl) },
    { rw hco_ndvd_eq_of_ne_zero hkz, apply or.inr (or.inr rfl) }
  end

lemma unified_formula.map_hco {k} :
  ∀ p, nqfree p → unified (formula.map (atom.unify k) p) 
| ⊤' hf a hm := by cases hm
| ⊥' hf a hm := by cases hm
| (A' a') hf a hm := 
  begin
   simp [formula.atoms, formula.map] at hm, subst hm,
   apply unified_atom_hco,
  end
| (p ∧' q) hf a hm := 
  begin
    cases hf with hfp hfq, simp [formula.atoms, formula.map] at hm, 
    cases hm, apply unified_formula.map_hco p hfp _ hm,
    apply unified_formula.map_hco q hfq _ hm,
  end
| (p ∨' q) hf a hm := 
  begin
    cases hf with hfp hfq, simp [formula.atoms, formula.map] at hm, 
    cases hm, apply unified_formula.map_hco p hfp _ hm,
    apply unified_formula.map_hco q hfq _ hm,
  end
| (¬' p) hf a hm := by cases hf
| (∃' p) hf a hm := by cases hf

lemma unified_hcso :
  ∀ p, nqfree p → unified p.unify := 
begin
  intros p hf, simp [unified, formula.atoms, formula.unify],
  constructor, apply (or.inr (or.inr rfl)),
  apply unified_formula.map_hco _ hf
end

lemma eval_sqe :  
  ∀ {p : formula}, nqfree p → formula.wf p 
  → ∀ {bs : list znum}, (sqe p).eval bs ↔ ∃ (b : znum), p.eval (b :: bs) := 
begin
  intros p hf hn bs, unfold sqe,
  rewrite eval_sqe_core_iff,
  apply hcso_prsv p hf hn bs, 
  apply nqfree_unify hf, 
  apply formula.wf_hcso hn,
  apply unified_hcso, apply hf
end