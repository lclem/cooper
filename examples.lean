import .lia.main

/- This package includes two different tactics for linear integer arithmetic. 
   lia is the standard tactic you'd likely what you'd want to use 
   in most cases. The main difference between the two is that the shadow syntax 
   of reify is defined using int, whereas that of the the latter uses znum. -/ 

/- If performance is really critical and you're willing to trust the vm, 
   you might want to try out reify. This tactic uses the vm instead
   of the kernel to evaluate decidability proof terms, which allows it to 
   handle a much wider range of goals. -/

/- Since reify runs the risk of being unsound, we'd want to 
   test it with some nontheorems and make sure it fails every time,
   for a quick sanity check. -/


example : ∃ (z : int), z + 5 = 1223 := by lia

lemma fooquz : ∃ (x : int), 3 ∣ (x + 5)  := by lia

#print fooquz
