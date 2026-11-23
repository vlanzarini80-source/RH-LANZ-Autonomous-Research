
import Mathlib

namespace LNZGrant

/--
Six-harmonic M3 mode from Grant.
All coefficients remain independent.
-/
noncomputable def mode3
    (c1 c2 c3 c4 c5 c6 : ℝ)
    (n : ℕ) : ℝ :=
  let x := (n : ℝ) * Real.pi / 2
  c1 * Real.cos x
    + c2 * Real.sin x
    + c3 * Real.cos (2 * x)
    + c4 * Real.sin (2 * x)
    + c5 * Real.cos (3 * x)
    + c6 * Real.sin (3 * x)

/-- Previously verified initial identity. -/
theorem mode3_zero
    (c1 c2 c3 c4 c5 c6 : ℝ) :
    mode3 c1 c2 c3 c4 c5 c6 0 =
      c1 + c3 + c5 := by
  simp [mode3]

/--
Four steps in the discrete index shift
the fundamental angle by exactly 2*pi.
-/
theorem mode3_angle_shift (n : ℕ) :
    ((n + 4 : ℕ) : ℝ) * Real.pi / 2 =
      (n : ℝ) * Real.pi / 2 +
        2 * Real.pi := by
  push_cast
  ring

#print axioms LNZGrant.mode3_zero
#print axioms LNZGrant.mode3_angle_shift

end LNZGrant
