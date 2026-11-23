
import Mathlib

namespace LNZGrant

/--
The six-harmonic trigonometric mode M3
from Grant, Section 15.4.

The coefficients remain independent.
No fitted values are assumed.
-/
def mode3
    (c1 c2 c3 c4 c5 c6 : ℝ)
    (n : ℕ) : ℝ :=
  let x := (n : ℝ) * Real.pi / 2
  c1 * Real.cos x
    + c2 * Real.sin x
    + c3 * Real.cos (2 * x)
    + c4 * Real.sin (2 * x)
    + c5 * Real.cos (3 * x)
    + c6 * Real.sin (3 * x)

/--
Initial exact identity at n = 0.
No expected numerical coefficient.
-/
theorem mode3_zero
    (c1 c2 c3 c4 c5 c6 : ℝ) :
    mode3 c1 c2 c3 c4 c5 c6 0 =
      c1 + c3 + c5 := by
  simp [mode3]

#print axioms LNZGrant.mode3_zero

end LNZGrant
