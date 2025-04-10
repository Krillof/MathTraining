import Mathlib.Tactic -- Use always
import Mathlib.Util.Delaborators -- Use always

set_option warningAsError false -- Use always
open Set

open Function


#check Function.comp
#check Function.comp_apply -- use as def
section
  variable  {α β γ: Type*} (f : α → β) (g : β → γ)
  #check g ∘ f
end




#check Function.Injective
/-
/-- A function `f : α → β` is called injective if `f x = f y` implies `x = y`. -/
def Injective (f : α → β) : Prop :=
  ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂

-/

#check Function.Injective.comp

example
  {α β φ : Type*}
  {f : α → β}
  {g : β → φ}
  (hg : Injective g)
  (hf : Injective f)
  : Injective (g ∘ f)
  := by
  intro a1 a2 h
  rw [
    Function.comp_apply,
    Function.comp_apply,
  ] at h
  dsimp [Injective] at hg hf
  /-
    f : α → β
    g : β → φ
    hg : ∀ ⦃a₁ a₂ : β⦄, g a₁ = g a₂ → a₁ = a₂
    hf : ∀ ⦃a₁ a₂ : α⦄, f a₁ = f a₂ → a₁ = a₂
    a1 a2 : α
    h : g (f a1) = g (f a2)
    ⊢ a1 = a2
  -/
  specialize hg h
  -- hg : f a1 = f a2
  specialize hf hg
  -- hf : a1 = a2
  exact hf






#check Function.Surjective
/-
/-- A function `f : α → β` is called surjective if every `b : β` is equal to `f a`
for some `a : α`. -/
def Surjective (f : α → β) : Prop :=
  ∀ b, ∃ a, f a = b
-/


#check Function.Bijective
/-
/-- A function is called bijective
  if it is both injective and surjective. -/
def Bijective (f : α → β) :=
  Injective f ∧ Surjective f
-/

/-
 f ⁻¹' is an inverse image
-/
example
  {α β : Type*} (f : α → β) (u  : Set β)
 : f ⁻¹' u = {x | f x ∈ u} := by
  rfl


example
  {α β : Type*} (f : α → β) (u v : Set β)
 : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext x
  rfl

/-
 f '' is an image
-/
example
  {α β : Type*} (f : α → β) (s : Set α)
  : f '' s = {y | ∃ x, x ∈ s ∧ f x = y} := by
  rfl

example
  {α β : Type*} (f : α → β) (s t : Set α)
 : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt, rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x, Or.inl xs
  use x, Or.inr xt

#check mem_image_of_mem
