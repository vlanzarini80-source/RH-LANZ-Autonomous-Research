
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

/-- Previously verified four-step angular shift. -/
theorem mode3_angle_shift (n : ℕ) :
    ((n + 4 : ℕ) : ℝ) * Real.pi / 2 =
      (n : ℝ) * Real.pi / 2 +
        2 * Real.pi := by
  push_cast
  ring

/--
Sine is unchanged after an angular shift of 2*pi.
No periodicity hypothesis is assumed.
-/
theorem sin_two_pi_shift (x : ℝ) :
    Real.sin (x + 2 * Real.pi) =
      Real.sin x := by
  rw [Real.sin_add]
  simp [Real.sin_two_pi, Real.cos_two_pi]

/--
Cosine is unchanged after an angular shift of 2*pi.
No periodicity hypothesis is assumed.
-/
theorem cos_two_pi_shift (x : ℝ) :
    Real.cos (x + 2 * Real.pi) =
      Real.cos x := by
  rw [Real.cos_add]
  simp [Real.sin_two_pi, Real.cos_two_pi]

#print axioms LNZGrant.mode3_zero
#print axioms LNZGrant.mode3_angle_shift
#print axioms LNZGrant.sin_two_pi_shift
#print axioms LNZGrant.cos_two_pi_shift

end LNZGrant
