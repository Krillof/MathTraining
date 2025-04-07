import Mathlib.Tactic -- Use always
import Mathlib.Util.Delaborators -- Use always
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.Basic

set_option warningAsError false -- Use always
set_option diagnostics true


open Filter Metric

theorem convergent_sequence_is_bounded
    {α : Type*} [MetricSpace α]
    {u : ℕ → α} {l : α}
    (hu : Tendsto u atTop (𝓝 l)) :
    ∃ B, ∃ N, ∀ n ≥ N, dist (u n) l ≤ B := by
  -- Since u converges to l, for ε = 1 there exists N such that for all n ≥ N, dist (u n) l < 1
  rcases Metric.tendsto_atTop.1 hu 1 zero_lt_one with ⟨N, hN⟩
  -- Take B = max of distances for n < N and 1 for n ≥ N
  let B := max (Finset.sup (Finset.range N) fun n => dist (u n) l) 1
  use B, N
  intro n hn
  -- Case 1: n ≥ N
  have h_le : dist (u n) l ≤ 1 := le_of_lt (hN n hn)
  -- Case 2: n < N is handled by the Finset.sup
  exact le_trans h_le (le_max_right _ _)
