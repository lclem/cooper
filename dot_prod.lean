import .list .num

namespace int

open list

def dot_prod : list int → list int → int 
| [] [] := 0 
| [] (_::_) := 0 
| (_::_) [] := 0 
| (a1::as1) (a2::as2) :=
  (a1 * a2) + dot_prod as1 as2

def map_neg_dot_prod : 
  ∀ {as1 as2 : list int}, dot_prod (map_neg as1) as2 = -(dot_prod as1 as2) 
| [] [] := begin simp [map_neg, dot_prod] end 
| [] (_::_) := begin simp [map_neg, dot_prod] end 
| (_::_) [] := begin simp [map_neg, dot_prod] end 
| (a1::as1) (a2::as2) :=
  begin
    simp [map_neg, dot_prod],
    rw (@map_neg_dot_prod as1 as2).symm, 
    simp [map_neg],
  end

lemma nil_dot_prod  :
  ∀ {as}, dot_prod [] as = 0  
| [] := rfl
| (a::as) := rfl

lemma dot_prod_nil  :
  ∀ {as}, dot_prod as [] = 0  
| [] := rfl
| (a::as) := rfl

lemma cons_dot_prod_cons_eq {a1 a2 as1 as2} : 
dot_prod (a1::as1) (a2::as2) = (a1 * a2) + dot_prod as1 as2 := rfl

lemma comp_add_dot_prod  :
  ∀ (as1 as2 as3 : list int),
    dot_prod (comp_add as1 as2) as3 = (dot_prod as1 as3) + (dot_prod as2 as3)
| [] as2 as3 := 
  begin simp [dot_prod, nil_comp_add, nil_dot_prod] end
| as1 [] as3 := 
  begin simp [dot_prod, comp_add_nil, nil_dot_prod] end
| as1 as2 [] := 
  begin repeat {rewrite dot_prod_nil}, simp end
| (a1::as1) (a2::as2) (a3::as3) := 
  begin simp [dot_prod, comp_add, comp_add_dot_prod, add_mul] end

lemma comp_sub_dot_prod :
  ∀ (as1 as2 as3 : list int),
    dot_prod (comp_sub as1 as2) as3 = (dot_prod as1 as3) - (dot_prod as2 as3) 
| [] as2 as3 := 
  begin simp [dot_prod, nil_comp_sub, map_neg_dot_prod, nil_dot_prod] end
| as1 [] as3 := 
  begin simp [dot_prod, comp_sub_nil, nil_dot_prod] end
| as1 as2 [] := 
  begin repeat {rewrite dot_prod_nil}, simp end
| (a1::as1) (a2::as2) (a3::as3) := 
  begin simp [dot_prod, comp_sub, comp_sub_dot_prod, add_mul] end

lemma map_mul_dot_prod {a : int} :
  ∀ {as1 as2}, dot_prod (map_mul a as1) as2 = a * (dot_prod as1 as2) 
| [] as2 := 
  begin simp [map_mul, nil_dot_prod] end
| as1 [] := 
  begin
    repeat {rewrite dot_prod_nil},
    rewrite _root_.mul_zero a,
  end
| (a1::as1) (a2::as2) := 
  begin
    unfold map_mul, simp, repeat {rewrite cons_dot_prod_cons_eq}, 
    have h := @map_mul_dot_prod as1 as2, unfold map_mul at h, 
    rewrite h, rewrite mul_add, simp, rewrite mul_assoc
  end

end int


namespace znum

open list

def dot_prod : list znum → list znum → znum 
| [] [] := 0 
| [] (_::_) := 0 
| (_::_) [] := 0 
| (a1::as1) (a2::as2) :=
  (a1 * a2) + dot_prod as1 as2

def map_neg_dot_prod : 
  ∀ {as1 as2 : list znum}, dot_prod (map_neg as1) as2 = -(dot_prod as1 as2) 
| [] [] := begin simp [map_neg, dot_prod] end 
| [] (_::_) := begin simp [map_neg, dot_prod] end 
| (_::_) [] := begin simp [map_neg, dot_prod] end 
| (a1::as1) (a2::as2) :=
  begin
    simp [map_neg, dot_prod],
    rw (@map_neg_dot_prod as1 as2).symm, 
    simp [map_neg],
  end

@[simp] lemma nil_dot_prod  :
  ∀ {as}, dot_prod [] as = 0  
| [] := rfl
| (a::as) := rfl

@[simp] lemma dot_prod_nil  :
  ∀ {as}, dot_prod as [] = 0  
| [] := rfl
| (a::as) := rfl

lemma cons_dot_prod_cons_eq {a1 a2 as1 as2} : 
dot_prod (a1::as1) (a2::as2) = (a1 * a2) + dot_prod as1 as2 := rfl

lemma comp_add_dot_prod  :
  ∀ (as1 as2 as3 : list znum),
    dot_prod (comp_add as1 as2) as3 = (dot_prod as1 as3) + (dot_prod as2 as3)
| [] as2 as3 := 
  begin
    rewrite nil_comp_add, 
    rewrite nil_dot_prod, simp
  end
| as1 [] as3 := 
  begin
    rewrite comp_add_nil, 
    rewrite nil_dot_prod, simp
  end
| as1 as2 [] := 
  begin repeat {rewrite dot_prod_nil}, simp end
| (a1::as1) (a2::as2) (a3::as3) := 
  begin simp [dot_prod, comp_add, comp_add_dot_prod, add_mul] end

lemma comp_sub_dot_prod :
  ∀ (as1 as2 as3 : list znum),
    dot_prod (comp_sub as1 as2) as3 = (dot_prod as1 as3) - (dot_prod as2 as3) 
| [] as2 as3 := 
  begin simp [dot_prod, nil_comp_sub, map_neg_dot_prod, nil_dot_prod] end
| as1 [] as3 := 
  begin simp [dot_prod, comp_sub_nil, nil_dot_prod] end
| as1 as2 [] := 
  begin repeat {rewrite dot_prod_nil}, simp end
| (a1::as1) (a2::as2) (a3::as3) := 
  begin simp [dot_prod, comp_sub, comp_sub_dot_prod, add_mul] end
lemma map_mul_dot_prod {a : znum} :
  ∀ {as1 as2}, dot_prod (map_mul a as1) as2 = a * (dot_prod as1 as2) 
| [] as2 := 
  begin
    unfold map_mul, simp,
    repeat {rewrite nil_dot_prod}
  end
| as1 [] := 
  begin
    repeat {rewrite dot_prod_nil},
    rewrite mul_zero
  end
| (a1::as1) (a2::as2) := 
  begin
    unfold map_mul, simp, repeat {rewrite cons_dot_prod_cons_eq}, 
    have h := @map_mul_dot_prod as1 as2, unfold map_mul at h, 
    rewrite h, rewrite mul_add, simp, rewrite mul_assoc
  end

lemma dot_prod_to_int' : 
∀ {zs1 zs2 : list znum}, 
  (dot_prod zs1 zs2).to_int = int.dot_prod (map to_int zs1) (map to_int zs2)
| [] [] := rfl
| [] (a2::as2) := begin simp [nil_dot_prod, map], refl end
| (a1::as1) [] := begin simp [dot_prod_nil, map], refl end
| (a1::as1) (a2::as2) := 
  begin 
    simp [int.cons_dot_prod_cons_eq, znum.cons_dot_prod_cons_eq, 
      dot_prod_to_int', to_int, int.to_znum], 
    have h := @dot_prod_to_int' as1 as2, simp [to_int] at h, rw h,
  end

lemma dot_prod_to_int : 
∀ {zs1 zs2 : list znum}, 
  ↑(dot_prod zs1 zs2) = int.dot_prod (map to_int zs1) (map to_int zs2) :=
  @dot_prod_to_int'

lemma dot_prod_eq_of_forall_mem_zero : 
  ∀ {zs1 zs2}, (∀ z ∈ zs1, z = (0 : znum)) → dot_prod zs1 zs2 = 0 
| [] zs2 _ := nil_dot_prod 
| (z1::zs1) zs2 h :=
  begin
    cases zs2, apply dot_prod_nil,
    simp [dot_prod], have hrw := (h z1 (or.inl rfl)),
    subst hrw, simp, apply dot_prod_eq_of_forall_mem_zero,
    apply forall_mem_of_forall_mem_cons h
  end
  
   

end znum

namespace num 

open list

def dot_prod : list num → list num → num 
| [] [] := 0 
| [] (_::_) := 0 
| (_::_) [] := 0 
| (a1::as1) (a2::as2) :=
  (a1 * a2) + dot_prod as1 as2

@[simp] lemma nil_dot_prod  :
  ∀ {as}, dot_prod [] as = 0  
| [] := rfl
| (a::as) := rfl

@[simp] lemma dot_prod_nil  :
  ∀ {as}, dot_prod as [] = 0  
| [] := rfl
| (a::as) := rfl

lemma comp_add_dot_prod  :
  ∀ (as1 as2 as3 : list num),
    dot_prod (comp_add as1 as2) as3 = (dot_prod as1 as3) + (dot_prod as2 as3)
| [] as2 as3 := 
  begin
    rewrite nil_comp_add, 
    rewrite nil_dot_prod, simp
  end
| as1 [] as3 := 
  begin
    rewrite comp_add_nil, 
    rewrite nil_dot_prod, simp
  end
| as1 as2 [] := 
  begin repeat {rewrite dot_prod_nil}, simp end
| (a1::as1) (a2::as2) (a3::as3) := 
  begin
    simp [dot_prod, comp_add, comp_add_dot_prod as1 as2 as3, add_mul] 
  end

lemma cons_dot_prod_cons_eq {a1 a2 as1 as2} : 
dot_prod (a1::as1) (a2::as2) = (a1 * a2) + dot_prod as1 as2 := rfl

lemma dot_prod_to_znum' : 
∀ {ns1 ns2 : list num}, 
  (dot_prod ns1 ns2).to_znum = znum.dot_prod (map to_znum ns1) (map to_znum ns2)
| [] [] := rfl
| [] (a2::as2) := begin simp [nil_dot_prod, map], refl end
| (a1::as1) [] := begin simp [dot_prod_nil, map], refl end
| (a1::as1) (a2::as2) := 
  begin 
    simp [num.cons_dot_prod_cons_eq, znum.cons_dot_prod_cons_eq, 
       dot_prod_to_znum', num.mul_to_znum'],
  end

lemma map_mul_dot_prod {a : num} :
  ∀ {as1 as2}, dot_prod (map_mul a as1) as2 = a * (dot_prod as1 as2) 
| [] as2 := begin simp [map_mul] end
| as1 [] :=  begin simp [map_mul] end
| (a1::as1) (a2::as2) := 
  begin
    unfold map_mul, simp, repeat {rewrite cons_dot_prod_cons_eq}, 
    have h := @map_mul_dot_prod as1 as2, unfold map_mul at h, 
    rewrite h, rewrite mul_add, simp, rewrite mul_assoc
  end

end num