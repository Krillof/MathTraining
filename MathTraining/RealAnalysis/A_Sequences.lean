import Mathlib.Tactic -- Use always
import Mathlib.Util.Delaborators -- Use always

set_option warningAsError false -- Use always
set_option diagnostics true

def ConvergentSeqTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0,
  ∃ N,
  ∀ n ≥ N,
  |s n - a| < ε

def
  CauchyConvergentSeq
  (s : ℕ → ℝ)
  :=
  ∀ ε > 0,
  ∃ N,
  ∀ n ≥ N,
  ∀ m ≥ N,
  |s n - s m| < ε

def
  InfinitelyLargeSeq
  (s : ℕ → ℝ) :=
  ∀ A > 0,
  ∃ N,
  ∀ n ≥ N,
  |s n| > A

def
  InfinitelySmallSeq
  (s : ℕ → ℝ) :=
  ∀ ε > 0,
  ∃ N,
  ∀ n ≥ N,
  |s n| < ε

def
  BoundedSeq
  (s : ℕ → ℝ) :=
  ∃ A > 0,
  ∀ n,
  |s n| < A

def
  Subsequence
  (s : ℕ → ℝ)
  (ss : ℕ → ℝ)
  :=
  ∃ r : ℕ → ℕ,
  ∀ n,
  s (r n) = ss n

#check sub_eq_add_neg
#check abs_sub
#check abs_add
#check add_le_add
#check add_lt_add
#check abs_sub_comm

#check abs_nonneg
#check abs_cases
#check abs_eq_zero

#check not_le.mpr

theorem
  conv_seq_to_unique
  {a b : ℝ}
  {s : ℕ → ℝ}
  (s_conv_a : ConvergentSeqTo s a)
  (s_conv_b : ConvergentSeqTo s b)
  : a = b
  :=
  by
  by_contra a_ne_b
  dsimp [ConvergentSeqTo] at s_conv_a s_conv_b
  have h0 : ∀ ε' > 0, |a - b| < ε' := by
    intros ε' ε'_pos
    have half_ε'_pos : ε' / 2 > 0 := by
      apply div_pos ε'_pos
      /- ⊢ 0 < 2-/
      linarith
    have s_conv_a' := (s_conv_a (ε' / 2) half_ε'_pos)
    have s_conv_b' := (s_conv_b (ε' / 2) half_ε'_pos)
    cases s_conv_a' with | intro N_a s_conv_a'' =>
      cases s_conv_b' with | intro N_b s_conv_b'' =>
        let N := max N_a N_b
        have N_ge_Na : N ≥ N_a := by simp [N]
        have N_ge_Nb : N ≥ N_b := by simp [N]
        have s_conv_a''' : |s N - a| < ε' / 2 := s_conv_a'' N N_ge_Na
        have s_conv_b''' : |s N - b| < ε' / 2 := s_conv_b'' N N_ge_Nb
        calc
          |a - b| = |a - s N + s N - b| := by simp
          _ = |a - s N - (b - s N)| := by simp
          _ ≤ |a - s N| + |b - s N| := by
            exact abs_sub (a - s N) (b - s N)
          _ = |s N - a| + |s N - b| := by
            conv =>
              rhs
              congr
              . apply abs_sub_comm
              . apply abs_sub_comm
          _ < ε'/2 + ε'/2 := by
            exact add_lt_add s_conv_a''' s_conv_b'''
          _ = ε' := by linarith
  have h1 : |a - b| = 0 := by
    cases lt_trichotomy |a - b| 0
      with
    | inl ab_lt =>
      exfalso
      have h11 : |a - b| ≥ 0 := abs_nonneg (a-b)
      have h12 : ¬|a - b| ≥ 0 := not_le.mpr ab_lt
      contradiction
    | inr ab_eq_gt =>
      cases ab_eq_gt with
        | inl ab_eq =>
          exact ab_eq
        | inr ab_gt =>
          exfalso
          have h11 : ¬ ∀ ε' > 0, |a - b| < ε' := by
            have h111 : |a - b|/2 ≤ |a - b| := by linarith
            have h112 : |a - b|/2 > 0 := by linarith
            push_neg
            use |a - b|/2, h112, h111
          contradiction
  have h2 : a = b := by
    have h21 : a - b = 0 := by
      apply abs_eq_zero.mp h1
    calc
      a = a - b + b := by ring
      _ = 0 + b := by rw [h21]
      _ = b := by ring
  contradiction


#check abs_add
#check abs_sub

theorem
  conv_iff_cauchy_conv
  {a b : ℝ}
  {s : ℕ → ℝ}
  : ConvergentSeqTo s a
    ↔
    CauchyConvergentSeq s
  := by
  constructor
  . intro s_conv
    dsimp [CauchyConvergentSeq]
    dsimp [ConvergentSeqTo] at s_conv
    /-
    s_conv : ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε
    ⊢ ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, |s n - s m| < ε
    -/
    intro ε ε_pos
    let ε_half := ε/2
    have ε_half_pos : ε_half > 0 := by
      sorry
    specialize s_conv ε_half ε_half_pos
    obtain ⟨N, s_conv⟩ := s_conv
    use N
    intro n n_ge_N m m_ge_N
    calc
      |s n - s m|
      = |(s n - a) - (s m - a)|
        := by sorry
      _ ≤ |s n - a| + |s m - a|
        := by
          apply abs_sub
      _ < ε_half + ε_half
        := by
          apply add_lt_add_of_lt_of_lt
          . exact s_conv n n_ge_N
          . exact s_conv m m_ge_N
      _ = ε
        := by
          dsimp [ε_half]
          linarith
  . intro cauchy_s_conv
    dsimp [CauchyConvergentSeq]at cauchy_s_conv
    dsimp [ConvergentSeqTo]
    /-
    cauchy_s_conv : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, |s n - s m| < ε
    ⊢ ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε
    -/
    sorry

theorem
  conv_of_subseq_iff
  {a b : ℝ}
  {s : ℕ → ℝ}
  : ConvergentSeqTo s a
    ↔
    ∀ ss : ℕ → ℝ, Subsequence s ss → ConvergentSeqTo ss a
  := by
  constructor
  . intro s_conv
    intro ss ss_subs_of_s
    /-
    s_conv : ConvergentSeqTo s a
    ss : ℕ → ℝ
    ss_subs_of_s : Subsequence s ss
    -/
    sorry
  . sorry




#check lt_of_le_of_ne
#check abs_eq_self
#check abs_eq_neg_self

theorem
  conv_seq_to_bounded
  {a : ℝ}
  {s : ℕ → ℝ}
  (h : ConvergentSeqTo s a)
  : BoundedSeq s
  := by
  have h1 : CauchyConvergentSeq s := by
    exact conv_iff_cauchy_conv.mp h
  dsimp [CauchyConvergentSeq] at h1
  dsimp [BoundedSeq]
  /-
  h1 : ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, |s n - s m| < ε
  ⊢ ∃ A > 0, ∀ (n : ℕ), |s n| < A
  -/
  sorry

  /-
  contrapose h
  dsimp [ConvergentSeqTo]
  push_neg
  dsimp [BoundedSeq] at h
  push_neg at h
  /-
    h : ∀ A > 0, ∃ n, A ≤ |s n|
    ⊢ ∃ ε > 0, ∀ (N : ℕ), ∃ n ≥ N, ε ≤ |s n - a|
  -/
  by_cases h1 : ∃ n, s n ≠ 0
  . /-
    h1 : ∃ n, s n ≠ 0
    -/
    obtain ⟨n, h1⟩ := h1
    let A := |s n|
    have h11 : A > 0 := by
      dsimp [A]
      /-
      h : ∀ A > 0, ∃ n, A ≤ |s n|
      n : ℕ
      h1 : s n ≠ 0
      A : ℝ := |s n|
      ⊢ |s n| > 0
      -/
      have h112 : |s n| ≥ 0 := abs_nonneg s n
      apply lt_of_le_of_ne
      . exact h112
      . by_contra abs_s_n_eq_zero
        /-
        h1 : s n ≠ 0
        A : ℝ := |s n|
        h112 : |s n| ≥ 0
        abs_s_n_eq_zero : 0 = |s n|
        ⊢ False
        -/
        have h113 : s n = 0 :=
           abs_eq_zero.mp (Eq.symm abs_s_n_eq_zero)
        contradiction
    specialize h A h11
    use A, h11
    intro N
    sorry
  . push_neg at h1
    /-
    h1 : ∀ (n : ℕ), s n = 0
    -/
    exfalso
    have h11 : (1 : ℝ) > 0 := by
      linarith
    specialize h 1 h11
    obtain ⟨n, h⟩ := h
    /-
    h1 : ∀ (n : ℕ), s n = 0
    h11 : 1 > 0
    n : ℕ
    h : 1 ≤ |s n|
    ⊢ False
    -/
    specialize h1 n
    rw [h1] at h
    simp at h
    /-
    h : 1 ≤ 0
    -/
    have h12 : ¬(1 : ℝ) ≤ 0 :=
      by linarith
    contradiction
  -/





theorem
  exists_conv_seq_to_with_const_mul
  (s : ℕ → ℝ)
  (a : ℝ)
  (a_ne_zero : a ≠ 0)
  : ∃ s' : ℕ → ℝ,
    ∀ n : ℕ,
    s n = a * s' n
  := by
  sorry
  /-
  by_contra goal
  push_neg at goal
  specialize goal (fun n ↦ a⁻¹ * s n)
  obtain ⟨n, goal⟩ := goal
  rw [ne_eq] at goal
  rw [← mul_assoc] at goal
  rw [mul_inv_cancel₀, a_ne_zero, one_mul] at goal
  have counter_goal : s n = s n := by
    rfl
  contradiction
  -/

theorem
  const_move_out
  (b : ℝ)
  : ConvergentSeqTo s a
    ↔ ConvergentSeqTo (fun n : ℕ ↦ b * s n ) (b * a)
  := by
  constructor
  . intro s_a_conv
    intro ε ε_gt_0
    dsimp
    use 1
    intro n n_ge_1
    sorry -- TODO: easy to continue
  . intro bs_ba_conv ε ε_gt_0
    specialize bs_ba_conv ε ε_gt_0
    obtain ⟨N,bs_ba_conv⟩ := bs_ba_conv
    use N
    intro n n_ge_N
    specialize bs_ba_conv n n_ge_N
    dsimp at bs_ba_conv
    sorry -- TODO: easy to continue




theorem
  conv_seq_to_const
  (a : ℝ)
  : ConvergentSeqTo (fun x : ℕ ↦ a) a
  := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

theorem
  conv_seq_to_add
  {s t : ℕ → ℝ}
  {a b : ℝ}
  (cs : ConvergentSeqTo s a)
  (ct : ConvergentSeqTo t b)
  : ConvergentSeqTo
      (fun n ↦ s n + t n)
      (a + b)
  := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n ngr
  rcases hs n (le_of_max_le_left ngr) with qs
  rcases ht n (le_of_max_le_right ngr) with qt
  have ε2sum : ε / 2 + ε / 2 = ε := by norm_num
  have g : |s n - a| + |t n - b| < ε := by
    rw [← ε2sum]
    apply add_lt_add qs qt
  apply lt_of_le_of_lt _ g
  have h : s n + t n - (a + b) = (s n - a) + (t n - b) := by linarith
  rw [h]
  apply abs_add


-- https://brandonrozek.com/blog/lean4-tutorial/
#check Exists.intro
#check Exists.elim



theorem
  conv_seq_to_minus
  {s t r : ℕ → ℝ}
  {a b : ℝ}
  (cs : ConvergentSeqTo s a)
  (ct : ConvergentSeqTo t b)
  (r_eq : ∀ n : ℕ, r n = s n - t n)
  : ConvergentSeqTo
      (fun n ↦ s n - t n)
      (a - b)
  := by
  have minus_one_ne_zero : (-1 : ℝ) ≠ 0 := by
    linarith
  have t'_eq : ∃ t' : ℕ → ℝ,
                ∀ n : ℕ,
                t n = (-1) * t' n
    := exists_conv_seq_to_with_const_mul (t) (-1) minus_one_ne_zero
  obtain ⟨t', t'_eq⟩ := t'_eq
  intro ε ε_gt_0
  dsimp
  use 1
  intro n n_gt_0
  specialize t'_eq n
  rw [t'_eq]
  simp




  sorry





theorem
  conv_seq_to_div
  {s t : ℕ → ℝ}
  {a b : ℝ}
  (h : b ≠ 0)
  (cs : ConvergentSeqTo s a)
  (ct : ConvergentSeqTo t b)
  : ConvergentSeqTo
      (fun n ↦ s n + t n)
      (a / b)
  := by
  sorry





theorem
  infinitely_large_seq_is_not_bounded
  (s : ℕ → ℝ)
  (h : InfinitelyLargeSeq s)
  : ¬ BoundedSeq s
  := by
  sorry

theorem
  not_bounded_seq_does_not_mean_infinitely_large_seq
  (s : ℕ → ℝ)
  (h : BoundedSeq s)
  : (InfinitelyLargeSeq s)
    ∨ (¬ InfinitelyLargeSeq s)
  := by
  sorry
