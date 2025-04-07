import Mathlib.Tactic -- Use always
import Mathlib.Util.Delaborators -- Use always


set_option warningAsError false -- Use always
set_option diagnostics true

-- https://hrmacbeth.github.io/math2001/01_Proofs_by_Calculation.html

/-
Don't be scared to use
"ring" tactic - it's very useful for rearrangement
-/

example
{a b : ℚ}
(h1 : a - b = 4)
(h2 : a * b = 1)
: (a + b) ^ 2 = 20 :=
  calc
    (a + b) ^ 2 = (a - b) ^ 2 + 4 * (a * b) := by ring
    _ = 4 ^ 2 + 4 * 1 := by rw [h1, h2]
    _ = 20 := by ring


example
{a b c d e f : ℤ}
(h1 : a * d = b * c)
(h2 : c * f = d * e) :
    d * (a * f - b * e) = 0 :=
  calc
    d * (a * f - b * e) = d * a * f - d * b * e := by ring
    _ = (d * a) * f - d * e * b := by ring
    _ = (a * d) * f - (d * e) * b := by ring
    _ = (b * c) * f - (c * f) * b := by rw [h1, ← h2]
    _ = 0 := by ring


/-
Trick:
If you want to solve an equation,
like x + 4 = 2
and you know how answer should look
(x = -2)
then you can solve it in Lean
-/
example {x : ℤ} (h1 : x + 4 = 2) : x = -2 :=
  calc
    x = x + 4 - 4 := by ring
    _ = 2 - 4 := by rw [h1]
    _ = -2 := by ring



/-
Here is more:
`norm_num` to not think about numbers

-/

example
{x y : ℤ}
(hx : x + 3 ≤ 2)
(hy : y + 2 * x ≥ 3)
: y > 3 :=
  calc
    y = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by rel [hy]
    _ = 9 - 2 * (x + 3) := by ring
    _ ≥ 9 - 2 * 2 := by rel [hx]
    _ > 3 := by norm_num
