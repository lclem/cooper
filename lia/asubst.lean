import .atom

open list znum

def asubst (i') (ks') : atom → atom 
| (atom.le i (k::ks))     := atom.le (i - (k * i')) (comp_add (map_mul k ks') ks)
| (atom.dvd d i (k::ks))  := atom.dvd d (i + (k * i')) (comp_add (map_mul k ks') ks)
| (atom.ndvd d i (k::ks)) := atom.ndvd d (i + (k * i')) (comp_add (map_mul k ks') ks)
| a := a

meta def aval_subst_iff_tac := 
`[unfold asubst, unfold atom.eval, rewrite add_assoc,
  have he : (i' * k + dot_prod (comp_add (map_mul k ks') ks) xs) 
            = (dot_prod (k :: ks) ((i' + dot_prod ks' xs) :: xs)),
  rw cons_dot_prod_cons_eq,
  rewrite mul_add, rewrite mul_comm, simp, 
  rewrite comp_add_dot_prod, 
  simp [dot_prod], apply map_mul_dot_prod,
  rewrite mul_comm at he, rewrite he]

meta def aval_subst_iff_aux := 
`[unfold asubst, unfold atom.eval, 
  repeat {rewrite nil_dot_prod}]

lemma aval_subst_iff (i' ks' xs) : 
  ∀ a, (asubst i' ks' a).eval xs ↔ a.eval ((i' + dot_prod ks' xs)::xs)  
| (atom.le i (k::ks))     := 
  begin
    unfold asubst, simp, unfold atom.eval, 
    rewrite znum.add_le_iff_le_sub, simp, 
    have he : (i' * k + dot_prod (comp_add (map_mul k ks') ks) xs) 
               = (dot_prod (k :: ks) ((i' + dot_prod ks' xs) :: xs)),
    { rewrite cons_dot_prod_cons_eq,
      rewrite mul_add, rewrite mul_comm, simp, 
      rewrite comp_add_dot_prod, simp [dot_prod], 
     apply map_mul_dot_prod }, 
    rewrite mul_comm at he, simp at *, rewrite he
  end
| (atom.dvd d i (k::ks))  := by aval_subst_iff_tac
| (atom.ndvd d i (k::ks)) := by aval_subst_iff_tac
| (atom.le i [])     := by aval_subst_iff_aux
| (atom.dvd d i [])  := by aval_subst_iff_aux
| (atom.ndvd d i []) := by aval_subst_iff_aux
