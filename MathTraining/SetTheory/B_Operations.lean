import Mathlib.Tactic -- Use always
import Mathlib.Util.Delaborators -- Use always

set_option warningAsError false -- Use always
open Set


/-
###################################################
#############Unions and intersections##############
###################################################
-/

#check and_comm
#check mem_inter_iff

#check inter_comm
theorem my_inter_comm
  {α : Type*} (s t : Set α)
  : s ∩ t = t ∩ s := by
  ext x
  simp only [mem_inter_iff]
  constructor
  · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
  · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩


#check union_def
#check union_comm
theorem my_union_comm
  {α : Type*} (a b : Set α)
  : a ∪ b = b ∪ a := by
  ext x
  constructor
  . rintro xab
    cases xab with
    | inl xa =>
      right
      exact xa
    | inr xb =>
      left
      exact xb
  . rintro xba
    cases xba with
    | inl xb =>
      right
      exact xb
    | inr xa =>
      left
      exact xa


#check union_inter_distrib_left
example {α : Type*} (s t u : Set α)
  : s ∪ t ∩ u = (s ∪ t) ∩ (s ∪ u) := by
  ext x
  constructor
  . intro x_sutnu
    constructor
    . cases x_sutnu with
      | inl h =>
        left
        exact h
      | inr h =>
        right
        obtain ⟨xt, xu⟩ := h
        exact xt
    . cases x_sutnu with
      | inl h =>
        left
        exact h
      | inr h =>
        right
        obtain ⟨xt, xu⟩ := h
        exact xu
  . intro x_stsu
    obtain ⟨xst, xsu⟩ := x_stsu
    cases xst with
    | inl xs =>
      left
      exact xs
    | inr xt =>
      cases xsu with
      | inl xs =>
        left
        exact xs
      | inr xu =>
        right
        constructor
        . exact xt
        . exact xu



#check union_inter_distrib_right



#check inter_union_distrib_left
#check inter_union_distrib_right


#check compl_def
#check True.intro

#check compl_empty
example
  {α : Type*}
  : ∅ᶜ = (univ : Set α)
  := by
  dsimp [compl_def]
  -- ⊢ {x | x ∉ ∅} = univ
  ext x
  dsimp
  -- ⊢ x ∉ ∅ ↔ x ∈ univ
  constructor
  . rintro h
    apply True.intro
  . rintro x_in_univ
    by_contra x_in_empty
    exact x_in_empty


/-
###################################################
#############Infinite unions and intersections#####
###################################################
-/

#check mem_iUnion -- Use as def
#check mem_iInter -- Use as def

#check inter_iUnion
example
  {α I : Type*}
  (A : I → Set α)
  (s : Set α)
  : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
  ext x
  simp only [mem_inter_iff, mem_iUnion]
  constructor
  · rintro ⟨xs, ⟨i, xAi⟩⟩
    exact ⟨i, xAi, xs⟩
  rintro ⟨i, xAi, xs⟩
  exact ⟨xs, ⟨i, xAi⟩⟩

#check inter_iInter
example
  {α I : Type*}
  (A : I → Set α)
  (s : Set α)
  : (s ∩ ⋂ i, A i) = ⋂ i, A i ∩ s := by
  sorry



example
  {α I : Type*}
  (A B : I → Set α)
  : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
  ext x
  simp only [mem_inter_iff, mem_iInter]
  constructor
  · intro h
    constructor
    · intro i
      exact (h i).1
    intro i
    exact (h i).2
  rintro ⟨h1, h2⟩ i
  constructor
  · exact h1 i
  exact h2 i

#check sUnion_subset
#check subset_sInter

/-
###################################################
#############Subsets###############################
###################################################
-/

#check Subset.antisymm
#check Subset.trans
#check Subset.refl

theorem my_subset_antisymm
  {α : Type*}
  (A B : Set α)
  (hAB : A ⊆ B)
  (hBA : B ⊆ A)
  : A = B := by
  -- Uses set extensionality axiom
  ext x
  constructor
  · intro xA
    dsimp [subset_def] at hAB
    specialize hAB x xA
    exact hAB
  · intro xB
    dsimp [subset_def] at hBA
    specialize hBA x xB
    exact hBA

theorem my_subset_refl
  {α : Type*}
  (A : Set α)
  : A ⊆ A := by
  -- By definition of ⊆ (∀ x ∈ A, x ∈ A)
  intro x hx
  exact hx

theorem my_subset_trans
  {α : Type*}
  (A B C : Set α)
  (hAB : A ⊆ B)
  (hBC : B ⊆ C)
  : A ⊆ C := by
  intro x hx
  apply hBC
  apply hAB
  exact hx

#check empty_def

#check empty_subset
theorem my_empty_subset
  {α : Type*}
  (A : Set α) : ∅ ⊆ A := by
  intro x x_in_empty
  /-
    x : α
    x_in_empty : x ∈ ∅
    ⊢ x ∈ A
  -/
  exfalso
  rw [empty_def] at x_in_empty
  /-
    x_in_empty : x ∈ {_x | False}
    ⊢ False
  -/
  exact x_in_empty


#check compl_empty
#check compl_def

#check subset_univ
theorem my_subset_univ
  {α : Type*}
  (A : Set α)
  : A ⊆ univ := by
  intro x xA
  rw [
    ← compl_empty,
    -- ⊢ x ∈ ∅ᶜ
     compl_def
    -- ⊢ x ∈ {x | x ∉ ∅}
  ]
  dsimp
  -- ⊢ x ∉ ∅
  by_contra x_in_empty
  exact x_in_empty


#check mem_of_subset_of_mem


/-
###################################################
#############Nonempty##############################
###################################################
-/

#check Set.Nonempty
example
  {α : Type*} (s t : Set α)
  : ¬(s ⊆ t) ↔ Set.Nonempty (s \ t)
  := by
  constructor
  . intro not_s_subset_t
    contrapose! not_s_subset_t
    intro x x_in_s
    sorry
  . intro s_minus_t_ne_emptyset
    contrapose! s_minus_t_ne_emptyset
    sorry
