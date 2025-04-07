import Mathlib.Tactic -- Use always
import Mathlib.Util.Delaborators -- Use always

import Mathlib.Topology.Basic

open Topology

set_option warningAsError false -- Use always
set_option diagnostics true



#check Set.mem_of_subset_of_mem

#check interior_subset
theorem my_interior_subset
  {X : Type*} [TopologicalSpace X]
  {A : Set X}
  : interior A ⊆ A := by
  -- The interior is defined as the union of all open sets contained in A
  -- So any x ∈ interior A must be in one of these open subsets, which are all contained in A
  intro x hx
  -- By definition of interior, hx means there exists an open set t with x ∈ t and t ⊆ A
  rw [mem_interior] at hx
  -- Get the witness t from the existential
  rcases hx with ⟨t, ⟨t_subset_A, _, x_in_t⟩⟩
  -- Since x ∈ t and t ⊆ A, we have x ∈ A
  exact Set.mem_of_subset_of_mem t_subset_A x_in_t


#check Set.mem_setOf
#check subset_trans
#check interior_subset
theorem interior_subset_interior
  {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h : B ⊆ A)
    : interior B ⊆ interior A
  := by
  -- The interior of B is the largest open set contained in B
  -- Since B ⊆ A, any open set contained in B is also contained in A
  show interior B ⊆ interior A
  -- interior B is open and interior B ⊆ B ⊆ A
  have : interior B ⊆ A := subset_trans my_interior_subset h
  -- interior A is the largest open subset of A
  exact interior_maximal this isOpen_interior
