import Mathlib.Tactic -- Use always
import Mathlib.Util.Delaborators -- Use always

set_option warningAsError false -- Use always
open Set




#check subset_refl
#check subset_antisymm
#check subset_trans



section -- ????
  variables {α : Type*} (s t : Set α) -- ????

  #check s ≤ t -- ????
  #check instLE -- ????

end
