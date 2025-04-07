import Mathlib.Tactic -- Use always
import Mathlib.Util.Delaborators -- Use always

set_option warningAsError false -- Use always
open Set

#check univ
#check ∅


#check range
-- domain?
#check Set.restrict

#check union_def
#check inter_def
#check compl_def --  \^c
#check Set.diff_eq -- \\

#check sSup
#check sInf
/-
The are opened as "sUnion"
  and "sInter"

This terms are used, so they are here
-/
example {α : Type*} (s : Set (Set α))
  : sSup s = sSup (s ∪ ∅) := by
  dsimp [sSup]
  -- ⋃₀ s = ⋃₀ (s ∪ ∅)
  sorry


#check iSup
#check iInf
/-

/-- Indexed supremum -/
def iSup [SupSet α] (s : ι → α) : α :=
  sSup (range s)

/-- Indexed infimum -/
def iInf [InfSet α] (s : ι → α) : α :=
  sInf (range s)

- `⨆ i, f i`, `⨅ i, f i`: supremum and infimum of an indexed family, respectively;
-/


#check sUnion
#check sInter
/-
def sInter (S : Set (Set α)) : Set α :=
  sInf S

def sUnion (S : Set (Set α)) : Set α :=
  sSup S

- `⋃₀ s`, `⋂₀ s`: union and intersection of a set of sets;
-/
#check mem_sUnion -- Use this as def
#check mem_sInter -- Use this as def





#check iUnion
#check iInter
/-
/-- Indexed union of a family of sets -/
def iUnion (s : ι → Set α) : Set α :=
  iSup s

/-- Indexed intersection of a family of sets -/
def iInter (s : ι → Set α) : Set α :=
  iInf s

- `⋃ i, s i`, `⋂ i, s i`: union and intersection of an indexed family of sets.
-/
#check mem_iUnion -- Use this as def
#check mem_iInter -- Use this as def

#check subset_def

#check Set.insert
#check Set.Nonempty
