import Mathlib.Tactic -- Use always
import Mathlib.Util.Delaborators -- Use always

set_option warningAsError false -- Use always

#check Group

#check mul_assoc -- a * b * c = a * (b * c)
#check one_mul --  1 * a = a
#check inv_mul_cancel --  a⁻¹ * a = 1


theorem my_mul_div
  {G : Type*}
  [Group G] (a b : G)
  : a = b⁻¹ * b * a
  := by
  nth_rw 1 [← one_mul a]
  -- 1 * a = b⁻¹ * b * a
  rw [← inv_mul_cancel b]
  -- b⁻¹ * b * a =  b⁻¹ * b * a

theorem my_mul_div_fixed_right
  {G : Type*}
  [Group G] (a b c : G)
  : a * c =  b⁻¹ * b * a * c
  := by
  nth_rw 1 [my_mul_div a b]

theorem my_inv_inv_fixed_right
  {G : Type*}
  [Group G] (a b : G)
  : a * b =  (a⁻¹)⁻¹ * b
  := by
  rw [
    my_mul_div_fixed_right a a⁻¹ b,
    -- a⁻¹⁻¹ * a⁻¹ * a * b = a⁻¹⁻¹ * b
    mul_assoc,
    -- a⁻¹⁻¹ * a⁻¹ * (a * b) = a⁻¹⁻¹ * b
    mul_assoc
    -- a⁻¹⁻¹ * (a⁻¹ * (a * b)) = a⁻¹⁻¹ * b
    ]
  nth_rw 2 [← mul_assoc]
  -- a⁻¹⁻¹ * (a⁻¹ * a * b) = a⁻¹⁻¹ * b
  rw [
    inv_mul_cancel,
    -- a⁻¹⁻¹ * (1 * b) = a⁻¹⁻¹ * b
    one_mul
    -- a⁻¹⁻¹ * b = a⁻¹⁻¹ * b
    ]

theorem my_mul_inv_cancel
  {G : Type*}
  [Group G] (a : G)
  : a * a⁻¹ = 1
  := by
  rw [
    my_inv_inv_fixed_right a a⁻¹,
    -- a⁻¹⁻¹ * a⁻¹ = 1
    inv_mul_cancel
    -- 1 = 1
    ]

theorem my_inv_mul_eq_mul_inv
  {G : Type*}
  [Group G] (a : G)
  : a * a⁻¹ = a⁻¹ * a
  := by
  rw [
    inv_mul_cancel,
    -- a * a⁻¹ = 1
    my_mul_inv_cancel
    -- 1 = 1
    ]

theorem my_mul_one
  {G : Type*}
  [Group G] (a : G)
  : a * 1 = a
  := by
  rw [
    ← inv_mul_cancel a,
    -- a * (a⁻¹ * a) = a
    ← mul_assoc,
    -- a * a⁻¹ * a = a
    my_mul_inv_cancel,
    -- 1 * a = a
    one_mul
    -- a = a
    ]
/--/
theorem my_inv_one
  {G : Type*}
  [Group G]
  : (1 : G)⁻¹ = 1
  := by
  rw [← one_mul 1⁻¹]
  -- 1 * 1⁻¹ = 1
  rw [mul_inv_cancel 1]
  -- 1 = 1



theorem my_mul_inv_rev
  {G : Type*}
  [Group G]
  (a b : G)
  : (a * b)⁻¹ = b⁻¹ * a⁻¹
  := by
  rw [← one_mul (a * b)⁻¹, ← one_mul (b⁻¹ * a⁻¹)]
  -- 1 * (a * b)⁻¹ = 1 * (b⁻¹ * a⁻¹)
  rw [← inv_mul_cancel (a * b), mul_assoc,  mul_inv_cancel (a * b)]
  -- (a * b)⁻¹ * 1 = (a * b)⁻¹ * (a * b) * (b⁻¹ * a⁻¹)
  rw [mul_one]
  -- (a * b)⁻¹ = (a * b)⁻¹ * (a * b) * (b⁻¹ * a⁻¹)
  rw [mul_assoc]
  -- (a * b)⁻¹ = (a * b)⁻¹ * (a * b * (b⁻¹ * a⁻¹))
  nth_rw 2 [← mul_assoc, mul_assoc]
  -- (a * b)⁻¹ = (a * b)⁻¹ * (a * (b * b⁻¹) * a⁻¹)
  rw [mul_inv_cancel b, mul_one a]
  -- (a * b)⁻¹ = (a * b)⁻¹ * (a * a⁻¹)
  rw [mul_inv_cancel, mul_one]


theorem my_inv_inv
  [Group G] (a : G)
  : a⁻¹⁻¹ = a
  := by
  rw [← one_mul a⁻¹⁻¹, ← mul_inv_cancel a]
  -- a * a⁻¹ * a⁻¹⁻¹ = a
  rw [mul_assoc, mul_inv_cancel a⁻¹, mul_one]


theorem my_self_eq_mul_right
  {G : Type*}
  [Group G]
  (a b : G)
  : a = a * b ↔ b = 1
  := by
  constructor
  . intro h
    rw [← one_mul b]
    -- 1 * b = 1
    nth_rw 1 [← inv_mul_cancel a]
    -- because just `rw` will apply
    --   theorem multiple times
    -- a⁻¹ * a * b = 1
    rw [mul_assoc, ← h]
    exact inv_mul_cancel a
  . intro h
    rw [h]
    -- a = a * 1
    rw [mul_one a]


theorem my_self_eq_mul_left
  {G : Type*}
  [Group G]
  (a b : G)
  : b = a * b ↔ a = 1
  := by
  constructor
  . intro h
    rw [← mul_one a]
    -- a * 1 = 1
    nth_rw 1 [← mul_inv_cancel b]
    -- because just `rw` will apply
    --   theorem multiple times
    -- a * (b * b⁻¹) = 1
    rw [← mul_assoc, ← h]
    exact mul_inv_cancel b
  . intro h
    rw [h]
    -- b = 1 * b
    rw [one_mul b]


theorem my_inv_mul_eq_of_eq_mul
  {G : Type*}
  [Group G] {a b c : G}
  (h : b = a * c)
  : a⁻¹ * b = c
  := by
  rw [h, ← mul_assoc]
  -- a⁻¹ * a * c = c
  rw [inv_mul_cancel, one_mul]


theorem my_mul_eq_of_eq_mul_inv
  {G : Type*}
  [Group G] {a b c : G}
  (h : a = c * b⁻¹)
  : a * b = c
  := by
  rw [h, mul_assoc]
  -- c * (b⁻¹ * b) = c
  rw [inv_mul_cancel, mul_one]
-/


-- TODO: add to card system
theorem my_one_uniqueness
  {G : Type*}
  [Group G]
  : ∃! a : G,
    ∀ b : G,
    a * b = b
    ∧ b * a = b
  := by
  dsimp [ExistsUnique]
  /-
  ⊢ ∃ x,
  (∀ (b : G), x * b = b ∧ b * x = b)
  ∧
  ∀ (y : G),
  (∀ (b : G), y * b = b ∧ b * y = b)
  → y = x
  -/
  use 1
  constructor
  . intro b
    /-
    b : G
    ⊢ 1 * b = b ∧ b * 1 = b
    -/
    constructor
    . apply one_mul
    . apply mul_one
  . intro y h
    /-
    y : G
    h : ∀ (b : G), y * b = b ∧ b * y = b
    ⊢ y = 1
    -/
    specialize h 1
    obtain ⟨h1, h2⟩ := h
    /-
    h1 : y * 1 = 1
    h2 : 1 * y = 1
    ⊢ y = 1
    -/
    rw [mul_one] at h1
    -- h1 : y = 1
    exact h1

theorem my_inv_uniqueness
  {G : Type*}
  [Group G]
  (a : G)
  : ∃! (b : G), b = a⁻¹
  := by
  dsimp [ExistsUnique]
  /-
  ⊢ ∃ x,
    x = a⁻¹
    ∧ ∀ (y : G),
    y = a⁻¹ → y = x
  -/
  use a⁻¹
  /-
  ⊢ a⁻¹ = a⁻¹
  ∧ ∀ (y : G),
  y = a⁻¹ → y = a⁻¹
  -/
  constructor
  . -- ⊢ a⁻¹ = a⁻¹
    rfl
  . intro y
    /-
    a y : G
    ⊢ y = a⁻¹ → y = a⁻¹
    -/
    intro h
    exact h
