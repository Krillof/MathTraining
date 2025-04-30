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
  intro x x_in_int_A
  dsimp [interior] at x_in_int_A
  /-
  A : Set X
  x : X
  x_in_int_A : x ∈ ⋃₀ {t | IsOpen t ∧ t ⊆ A}
  ⊢ x ∈ A
  -/
  rw [Set.mem_sUnion] at x_in_int_A
  -- x_in_int_A : ∃ t ∈ {t | IsOpen t ∧ t ⊆ A}, x ∈ t
  obtain ⟨t, t_in_set, x_in_t⟩ := x_in_int_A
  /-
  t : Set X
  t_in_set : t ∈ {t | IsOpen t ∧ t ⊆ A}
  x_in_t : x ∈ t
  -/
  dsimp at t_in_set
  -- t_in_set : IsOpen t ∧ t ⊆ A
  obtain ⟨is_open_t, t_subs_A⟩ := t_in_set
  /-
  is_open_t : IsOpen t
  t_subs_A : t ⊆ A
  -/
  apply Set.mem_of_subset_of_mem t_subs_A x_in_t


#check mem_interior
-- above is alternative definition of an interior
theorem my_mem_interior
  {X : Type*}
  {x : X}
  {A : Set X}
  [TopologicalSpace X]
  : x ∈ interior A ↔ ∃ B ⊆ A, IsOpen B ∧ x ∈ B
  := by
  constructor
  . intro x_in_int_A
    /-
    x_in_int_A : x ∈ interior A
    ⊢ ∃ B ⊆ A, IsOpen B ∧ x ∈ B
    -/
    use interior A
    -- ⊢ interior A ⊆ A
    --  ∧ IsOpen (interior A)
    --  ∧ x ∈ interior A
    constructor
    . exact my_interior_subset
    . constructor
      . exact my_isOpen_interior
      . exact x_in_int_A
  . intro h
    /-
    h : ∃ B ⊆ A, IsOpen B ∧ x ∈ B
    ⊢ x ∈ interior A
    -/
    obtain ⟨B, B_subs_A, is_open_B, x_in_B⟩ := h
    /-
    B : Set X
    B_subs_A : B ⊆ A
    is_open_B : IsOpen B
    x_in_B : x ∈ B
    -/
    dsimp [interior]
    -- ⊢ x ∈ ⋃₀ {t | IsOpen t ∧ t ⊆ A}
    rw [Set.mem_sUnion]
    use B
    -- ⊢ B ∈ {t | IsOpen t ∧ t ⊆ A} ∧ x ∈ B
    constructor
    . simp
      -- ⊢ IsOpen B ∧ B ⊆ A
      constructor
      . exact is_open_B
      . exact B_subs_A
    . exact x_in_B




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
  rw [my_mem_interior] at x_not_in_int_A
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





#check interior_eq_iff_isOpen
theorem my_interior_eq_iff_isOpen
  {X : Type*}
  {A : Set X}
  [TopologicalSpace X]
  : interior A = A ↔ IsOpen A
  := by
  constructor
  . intro int_A_eq_A
    /-
    int_A_eq_A : interior A = A
    ⊢ IsOpen A
    -/
    rw [← int_A_eq_A]
    apply my_isOpen_interior
  . intro is_open_A
    /-
    is_open_A : IsOpen A
    ⊢ interior A = A
    -/
    ext x
    /-
    x : X
    ⊢ x ∈ interior A ↔ x ∈ A
    -/
    constructor
    . intro x_in_int_A
      /-
      x_in_int_A : x ∈ interior A
      ⊢ x ∈ A
      -/
      apply my_interior_subset
      /-
      ⊢ x ∈ interior A
      -/
      exact x_in_int_A
    . intro x_in_A
      /-
      is_open_A : IsOpen A
      x : X
      x_in_A : x ∈ A
      ⊢ x ∈ interior A
      -/
      rw [my_mem_interior]
      -- ⊢ ∃ t ⊆ A, IsOpen t ∧ x ∈ t
      use A -- that is end

#check interior_interior
theorem my_interior_interior
  {X : Type*}
  {A : Set X}
  [TopologicalSpace X]
  : interior (interior A) = interior A
  := by
  ext x
  constructor
  . apply Set.mem_of_subset_of_mem my_interior_subset
  . intro x_in_int_A
    apply my_mem_interior.mpr
    use interior A
    /-
    ⊢ interior A ⊆ interior A
      ∧ IsOpen (interior A)
      ∧ x ∈ interior A
    -/
    constructor
    . -- ⊢ interior A ⊆ interior A
      exact Set.Subset.refl (interior A)
    . constructor
      . -- ⊢ IsOpen (interior A)
        exact my_isOpen_interior
      . -- ⊢ x ∈ interior A
        exact x_in_int_A




#check interior_inter

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
    apply my_interior_eq_iff_isOpen.mp
    /-
    h : ∀ x ∈ A, A ∈ 𝓝 x
    ⊢ interior A = A
    -/
    ext x
    specialize h x
    /-
    h : x ∈ A → A ∈ 𝓝 x
    ⊢ x ∈ interior A ↔ x ∈ A
    -/
    constructor
    . intro x_in_int_A
      apply Set.mem_of_subset_of_mem my_interior_subset
      exact x_in_int_A
    . intro x_in_A
      specialize h x_in_A
      /-
      x_in_A : x ∈ A
      h : A ∈ 𝓝 x
      ⊢ x ∈ interior A
      -/
      rw [mem_nhds_iff] at h
      -- h : ∃ t ⊆ A, IsOpen t ∧ x ∈ t
      obtain ⟨B, ⟨h1,h2,h3⟩⟩ := h
      /-
      B : Set X
      h1 : B ⊆ A
      h2 : IsOpen B
      h3 : x ∈ B
      ⊢ x ∈ interior A
      -/
      have h4 : interior B = B := by
        apply my_interior_eq_iff_isOpen.mpr h2
      rw [← h4] at h3
      -- h3 : x ∈ interior B
      have h5 : interior B ⊆ interior A := by
        apply my_interior_mono h1
      apply Set.mem_of_subset_of_mem h5 h3




-- Alternative definition for a frontier:
--#check ????
theorem whereis__mem_frontier
  {X : Type*}
  {x : X}
  {A : Set X}
  [TopologicalSpace X]
  : x ∈ frontier A
    ↔
    ∀ B ∈ 𝓝 x,
    (B ∩ A).Nonempty
    ∧ (B ∩ Aᶜ).Nonempty
  := by
    constructor
    . intro x_in_fr_A B B_in_nhds_x
      /-
      B : Set X
      B_in_nhds_x : B ∈ 𝓝 x
      ⊢ (B ∩ A).Nonempty ∧ (B ∩ Aᶜ).Nonempty
      -/
      constructor
      . -- ⊢ (B ∩ A).Nonempty
        sorry
      . sorry

    . intro h
      /-
      h : ∀ B ∈ 𝓝 x, (B ∩ A).Nonempty ∧ (B ∩ Aᶜ).Nonempty
      ⊢ x ∈ frontier A
      -/
      sorry





#check isClosed_closure
theorem my_isClosed_closure
  {X : Type*} [TopologicalSpace X]
  {A : Set X}
  : IsClosed (closure A) := by
  dsimp [closure]
  sorry

#check subset_closure
theorem my_subset_closure
  {X : Type*} [TopologicalSpace X]
  {A : Set X}
  : A ⊆ closure A := by
  sorry

#check closure_mono

#check closure_union

#check closure_closure



#check closure_eq_iff_isClosed
