import ..num ..dot_prod

open list znum

inductive atom : Type 
| le : znum → list znum → atom
| dvd : znum → znum → list znum → atom
| ndvd : znum → znum → list znum → atom
open atom
-- | (i ≤' ks) := sorry
-- | (d ∣' i ks) := sorry
-- | (d ¬| i ks) := sorry

notation c `≤'` ks := atom.le c ks
notation d `|'` c := atom.dvd d c
notation d `¬|'` c := atom.ndvd d c

meta def coeffs_to_format : nat → list znum → format 
| n [] := "0"
| n [k] := to_fmt k ++ "x" ++ to_fmt n
| n (k1::k2::ks) := to_fmt k1 ++ "x" ++ to_fmt n ++ " + " ++ coeffs_to_format (n+1) (k2::ks)

meta def atom.to_format : atom → format 
| (atom.le i ks) := to_fmt i ++ " ≤ " ++ coeffs_to_format 0 ks
| (atom.dvd d i ks) := to_fmt d ++ " | " ++ to_fmt i ++ " + " ++ coeffs_to_format 0 ks
| (atom.ndvd d i ks) := "¬(" ++ atom.to_format (atom.dvd d i ks) ++ ")"

meta instance atom.has_to_format : has_to_format atom := ⟨atom.to_format⟩ 

meta instance : has_to_tactic_format atom := has_to_format_to_has_to_tactic_format _

def atom.eval : list znum → atom → Prop 
| xs (le i ks) := i ≤ dot_prod ks xs
| xs (dvd d i ks) := d ∣ (i + dot_prod ks xs)
| xs (ndvd d i ks) := ¬ (d ∣ i + dot_prod ks xs)

instance atom.dec_eval {zs : list znum} {a : atom} : decidable (a.eval zs) :=
begin cases a; {simp [atom.eval], apply_instance} end

open znum