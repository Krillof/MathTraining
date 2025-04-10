import Mathlib.Tactic -- Use always
import Mathlib.Util.Delaborators -- Use always

import Mathlib.Topology.Basic

open Topology

set_option warningAsError false -- Use always
set_option diagnostics true


#check Filter
/-
/-- A filter `F` on a type `α` is a collection of sets of `α` which contains the whole `α`,
is upwards-closed, and is stable under intersection. We do not forbid this collection to be
all sets of `α`. -/
structure Filter (α : Type*) where
  /-- The set of sets that belong to the filter. -/
  sets : Set (Set α)
  /-- The set `Set.univ` belongs to any filter. -/
  univ_sets : Set.univ ∈ sets
  /-- If a set belongs to a filter, then its superset belongs to the filter as well. -/
  sets_of_superset {x y} : x ∈ sets → x ⊆ y → y ∈ sets
  /-- If two sets belong to a filter, then their intersection belongs to the filter as well. -/
  inter_sets {x y} : x ∈ sets → y ∈ sets → x ∩ y ∈ sets


/-- The principal filter of `s` is
  the collection of all supersets of `s`. -/
def principal (s : Set α) : Filter α where
  sets := { t | s ⊆ t }
  univ_sets := subset_univ s
  sets_of_superset hx := Subset.trans hx
  inter_sets := subset_inter

scoped notation "𝓟" => Filter.principal

-/

#check Filter.principal
#check Filter.mem_principal



#check 𝓝 -- same as 'nhds'
#check nhds
#check mem_nhds_iff -- better use this as def
/-


/-- A set is called a neighborhood of `x` if it contains an open set around `x`. The set of all
neighborhoods of `x` forms a filter, the neighborhood filter at `x`, is here defined as the
infimum over the principal filters of all open sets containing `x`. -/
irreducible_def nhds (x : X) : Filter X :=
  ⨅ s ∈ { s : Set X | x ∈ s ∧ IsOpen s }, 𝓟 s

-/






#check interior
#check closure
#check frontier
#check IsClosed
#check IsClopen
/-
/-- The interior of a set `s` is the largest open subset of `s`. -/
def interior (s : Set X) : Set X :=
  ⋃₀ { t | IsOpen t ∧ t ⊆ s }

/-- The closure of `s` is the smallest closed set containing `s`. -/
def closure (s : Set X) : Set X :=
  ⋂₀ { t | IsClosed t ∧ s ⊆ t }

/-- The frontier of a set is the set of points between the closure and interior. -/
def frontier (s : Set X) : Set X :=
  closure s \ interior s

 /-- A set is closed if its complement is open -/
class IsClosed (s : Set X) : Prop where
  /-- The complement of a closed set is an open set. -/
  isOpen_compl : IsOpen sᶜ

/-- A set is clopen if it is both closed and open. -/
def IsClopen (s : Set X) : Prop :=
  IsClosed s ∧ IsOpen s
-/





#check mem_interior
-- above is alternative definition of an interior

#check interior_eq_iff_isOpen

#check interior_interior

#check interior_inter

#check Set.mem_of_subset_of_mem
#check isOpen_interior
theorem my_isOpen_interior
  {X : Type*} [TopologicalSpace X]
  {A : Set X}
  : IsOpen (interior A):= by
  dsimp [interior]
  /-
  ⊢ IsOpen (⋃₀ {t | IsOpen t ∧ t ⊆ A})
  -/
  apply isOpen_sUnion
  /-
    ⊢ ∀ t ∈ {t | IsOpen t ∧ t ⊆ A}, IsOpen t
  -/
  intro t ⟨t_open, t_subset_A⟩
  /-
    A t : Set X
    t_open : IsOpen t
    t_subset_A : t ⊆ A
    ⊢ IsOpen t
  -/
  exact t_open



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


#check isOpen_iff_mem_nhds
-- above is alternative definition of an open set
theorem my_isOpen_iff_mem_nhds
  {X : Type*}
  {A : Set X}
  [TopologicalSpace X]
  : IsOpen A ↔ ∀ x ∈ A, A ∈ 𝓝 x
  := by
  constructor
  . intro A_is_open x x_in_A
    /-
    A_is_open : IsOpen A
    x : X
    x_in_A : x ∈ A
    ⊢ A ∈ 𝓝 x
    -/
    rw [mem_nhds_iff]
    /-
    ⊢ ∃ t ⊆ A, IsOpen t ∧ x ∈ t
    -/
    use A
    -- yes, that is an end of the proof
  . intro h
    /-
    h : ∀ x ∈ A, A ∈ 𝓝 x
    ⊢ IsOpen A
    -/

    sorry


#check interior_mono
theorem my_interior_mono
  {X : Type*} [TopologicalSpace X]
    {A B : Set X} (h : B ⊆ A)
    : interior B ⊆ interior A
  := by
  by_contra int_B_not_subset_int_A
  dsimp [Set.subset_def] at int_B_not_subset_int_A
  push_neg at int_B_not_subset_int_A
  /-
    A B : Set X
    h : B ⊆ A
    int_B_not_subset_int_A : ∃ x ∈ interior B, x ∉ interior A
    ⊢ False
  -/
  obtain ⟨x, ⟨x_in_int_B, x_not_in_int_A⟩⟩
    := int_B_not_subset_int_A
  /-
    x : X
    x_in_int_B : x ∈ interior B
    x_not_in_int_A : x ∉ interior A
  -/
  rw [mem_interior] at x_not_in_int_A
  push_neg at x_not_in_int_A
  /-
  x_not_in_int_A : ∀ t ⊆ A, IsOpen t → x ∉ t
  -/
  have h1 : interior B ⊆ A:= by
    exact Set.Subset.trans my_interior_subset h
  have h2 : x ∉ interior B := by
    specialize x_not_in_int_A (interior B) h1 my_isOpen_interior
    exact x_not_in_int_A
  contradiction



#check subset_closure
theorem my_subset_closure
  {X : Type*} [TopologicalSpace X]
  {A : Set X}
  : A ⊆ closure A := by
  sorry

#check closure_mono

#check closure_union

#check closure_closure

#check isClosed_closure

#check closure_eq_iff_isClosed
