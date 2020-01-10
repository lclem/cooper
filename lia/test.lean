import analysis.topology.topological_space data.real.basic

def real_line : set real := λ r, true

def left_ray (u : real) : set real := λ r, r < u
def right_ray (l : real) : set real := λ r, l < r 
def open_interval (l u : real) : set real := λ r, l < r ∧ l < u

-- def real.is_univ (rs : set real) : Prop := 
-- ∀ r : real, r ∈ rs 
-- 
-- def real.is_open_interval (rs : set real) : Prop := 
-- ∃ l u : real, ∀ r, (r ∈ rs ↔ l < r ∧ r < u)

def fooₖ : nat := 0

#exit

inductive real.is_open : set real → Prop 
| univ             : real.is_open real_line
| left (u : real)  : real.is_open (left_ray u) 
| right (l : real) : real.is_open (right_ray l) 
| interval (l u : real) : real.is_open ()
| union (s t : set real) :
  real.is_open s → real.is_open t → real.is_open (s ∪ t)

#exit
instance foo : topological_space real := 
{
  is_open := real.is_open,
  is_open_univ := real.is_open.univ,
  is_open_inter := real.is_open.inter,
  is_open_sUnion := 
  begin
    intros s hs, 
  end
}

#exit
example : ∀ x : int, 5 * x < x * 4 :=
begin
  simp [mul_comm],
end

#exit



def nat.foo : bool → bool → nat → int → bool := 
λ b1 b2 n z, b1 

def foobool : bool := (5 : nat).foo tt ff (-1 : int)

meta def expr_of_rat (r : rat) : expr := `(r)

#check has_reflect
example : true :=
begin
  apply (@iff.elim_left (¬false) true (by simp))

end