
import Mathlib

namespace LNZGrant

/--
Trigonometric M3 mode from Grant.
All six coefficients remain independent.
-/
noncomputable def mode3
    (c1 c2 c3 c4 c5 c6 : ℝ)
    (n : ℕ) : ℝ :=
  let x := (n : ℝ) * Real.pi / 2
  c1 * Real.cos x + c2 * Real.sin x
    + c3 * Real.cos (2 * x)
    + c4 * Real.sin (2 * x)
    + c5 * Real.cos (3 * x)
    + c6 * Real.sin (3 * x)

/-- P0.3: verified initial identity. -/
theorem mode3_zero
    (c1 c2 c3 c4 c5 c6 : ℝ) :
    mode3 c1 c2 c3 c4 c5 c6 0 =
      c1 + c3 + c5 := by
  simp [mode3]

/-- P1.1: verified angular shift. -/
theorem mode3_angle_shift (n : ℕ) :
    ((n + 4 : ℕ) : ℝ) * Real.pi / 2 =
      (n : ℝ) * Real.pi / 2 +
        2 * Real.pi := by
  push_cast
  ring

/-- P1.2: verified sine shift. -/
theorem sin_two_pi_shift (x : ℝ) :
    Real.sin (x + 2 * Real.pi) =
      Real.sin x := by
  rw [Real.sin_add]
  simp [Real.sin_two_pi, Real.cos_two_pi]

/-- P1.2: verified cosine shift. -/
theorem cos_two_pi_shift (x : ℝ) :
    Real.cos (x + 2 * Real.pi) =
      Real.cos x := by
  rw [Real.cos_add]
  simp [Real.sin_two_pi, Real.cos_two_pi]

/-- P1.3: second harmonic sine shift. -/
theorem sin_second_harmonic_shift (x : ℝ) :
    Real.sin (2 * (x + 2 * Real.pi)) =
      Real.sin (2 * x) := by
  calc
    Real.sin (2 * (x + 2 * Real.pi)) =
        Real.sin ((2 * x + 2 * Real.pi)
          + 2 * Real.pi) := by
            congr 1 <;> ring
    _ = Real.sin (2 * x + 2 * Real.pi) :=
      sin_two_pi_shift _
    _ = Real.sin (2 * x) :=
      sin_two_pi_shift _

/-- P1.3: second harmonic cosine shift. -/
theorem cos_second_harmonic_shift (x : ℝ) :
    Real.cos (2 * (x + 2 * Real.pi)) =
      Real.cos (2 * x) := by
  calc
    Real.cos (2 * (x + 2 * Real.pi)) =
        Real.cos ((2 * x + 2 * Real.pi)
          + 2 * Real.pi) := by
            congr 1 <;> ring
    _ = Real.cos (2 * x + 2 * Real.pi) :=
      cos_two_pi_shift _
    _ = Real.cos (2 * x) :=
      cos_two_pi_shift _

/-- P1.3: third harmonic sine shift. -/
theorem sin_third_harmonic_shift (x : ℝ) :
    Real.sin (3 * (x + 2 * Real.pi)) =
      Real.sin (3 * x) := by
  calc
    Real.sin (3 * (x + 2 * Real.pi)) =
        Real.sin (((3 * x + 2 * Real.pi)
          + 2 * Real.pi) + 2 * Real.pi) := by
            congr 1 <;> ring
    _ = Real.sin ((3 * x + 2 * Real.pi)
          + 2 * Real.pi) :=
      sin_two_pi_shift _
    _ = Real.sin (3 * x + 2 * Real.pi) :=
      sin_two_pi_shift _
    _ = Real.sin (3 * x) :=
      sin_two_pi_shift _

/-- P1.3: third harmonic cosine shift. -/
theorem cos_third_harmonic_shift (x : ℝ) :
    Real.cos (3 * (x + 2 * Real.pi)) =
      Real.cos (3 * x) := by
  calc
    Real.cos (3 * (x + 2 * Real.pi)) =
        Real.cos (((3 * x + 2 * Real.pi)
          + 2 * Real.pi) + 2 * Real.pi) := by
            congr 1 <;> ring
    _ = Real.cos ((3 * x + 2 * Real.pi)
          + 2 * Real.pi) :=
      cos_two_pi_shift _
    _ = Real.cos (3 * x + 2 * Real.pi) :=
      cos_two_pi_shift _
    _ = Real.cos (3 * x) :=
      cos_two_pi_shift _

/--
P1.3: exact four-step periodicity of M3.
No restrictions on the coefficients.
-/
theorem mode3_period_four
    (c1 c2 c3 c4 c5 c6 : ℝ)
    (n : ℕ) :
    mode3 c1 c2 c3 c4 c5 c6 (n + 4) =
      mode3 c1 c2 c3 c4 c5 c6 n := by
  unfold mode3
  dsimp only
  rw [mode3_angle_shift n]
  simp only [
    sin_two_pi_shift,
    cos_two_pi_shift,
    sin_second_harmonic_shift,
    cos_second_harmonic_shift,
    sin_third_harmonic_shift,
    cos_third_harmonic_shift
  ]

#print axioms LNZGrant.mode3_zero
#print axioms LNZGrant.mode3_angle_shift
#print axioms LNZGrant.sin_two_pi_shift
#print axioms LNZGrant.cos_two_pi_shift
#print axioms LNZGrant.sin_second_harmonic_shift
#print axioms LNZGrant.cos_second_harmonic_shift
#print axioms LNZGrant.sin_third_harmonic_shift
#print axioms LNZGrant.cos_third_harmonic_shift
#print axioms LNZGrant.mode3_period_four

end LNZGrant
