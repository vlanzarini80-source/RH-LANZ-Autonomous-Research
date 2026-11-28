import Mathlib

namespace LNZGrant

/-!
GRANT-P2.2
Exact residue evaluations, infinite subsequences
and symbolic odd-residue difference.
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

/- GRANT-P0.3 -/

theorem mode3_zero
    (c1 c2 c3 c4 c5 c6 : ℝ) :
    mode3 c1 c2 c3 c4 c5 c6 0 =
      c1 + c3 + c5 := by
  simp [mode3]

/- GRANT-P1.1 -/

theorem mode3_angle_shift (n : ℕ) :
    ((n + 4 : ℕ) : ℝ) * Real.pi / 2 =
      (n : ℝ) * Real.pi / 2 +
        2 * Real.pi := by
  push_cast
  ring

/- GRANT-P1.2 -/

theorem sin_two_pi_shift (x : ℝ) :
    Real.sin (x + 2 * Real.pi) =
      Real.sin x := by
  rw [Real.sin_add]
  simp [Real.sin_two_pi, Real.cos_two_pi]

theorem cos_two_pi_shift (x : ℝ) :
    Real.cos (x + 2 * Real.pi) =
      Real.cos x := by
  rw [Real.cos_add]
  simp [Real.sin_two_pi, Real.cos_two_pi]

/- GRANT-P1.3 -/

theorem mode3_period_four
    (c1 c2 c3 c4 c5 c6 : ℝ)
    (n : ℕ) :
    mode3 c1 c2 c3 c4 c5 c6 (n + 4) =
      mode3 c1 c2 c3 c4 c5 c6 n := by
  unfold mode3
  dsimp only
  rw [mode3_angle_shift]
  have h2 :
      2 * ((n : ℝ) * Real.pi / 2 +
        2 * Real.pi) =
      (2 * ((n : ℝ) * Real.pi / 2) +
        2 * Real.pi) + 2 * Real.pi := by
    ring
  have h3 :
      3 * ((n : ℝ) * Real.pi / 2 +
        2 * Real.pi) =
      ((3 * ((n : ℝ) * Real.pi / 2) +
        2 * Real.pi) + 2 * Real.pi) +
        2 * Real.pi := by
    ring
  rw [h2, h3]
  simp only [sin_two_pi_shift, cos_two_pi_shift]

/- GRANT-P2.1: residue 1 -/

theorem grant_p2_1_mode3_one
    (c1 c2 c3 c4 c5 c6 : ℝ) :
    mode3 c1 c2 c3 c4 c5 c6 1 =
      c2 - c3 - c6 := by
  unfold mode3
  dsimp only
  have h1 :
      ((1 : ℕ) : ℝ) * Real.pi / 2 =
        Real.pi / 2 := by
    norm_num
  rw [h1]
  have h2 :
      2 * (Real.pi / 2) =
        Real.pi := by
    ring
  have h3 :
      3 * (Real.pi / 2) =
        Real.pi + Real.pi / 2 := by
    ring
  rw [h2, h3]
  simp [Real.sin_add, Real.cos_add] <;> ring

/- GRANT-P2.1: residue 2 -/

theorem grant_p2_1_mode3_two
    (c1 c2 c3 c4 c5 c6 : ℝ) :
    mode3 c1 c2 c3 c4 c5 c6 2 =
      -c1 + c3 - c5 := by
  unfold mode3
  dsimp only
  have h1 :
      ((2 : ℕ) : ℝ) * Real.pi / 2 =
        Real.pi := by
    push_cast
    ring
  rw [h1]
  have h3 :
      3 * Real.pi =
        Real.pi + 2 * Real.pi := by
    ring
  rw [h3]
  simp [sin_two_pi_shift, cos_two_pi_shift,
    Real.sin_two_pi, Real.cos_two_pi] <;> ring

/- GRANT-P2.1: residue 3 -/

theorem grant_p2_1_mode3_three
    (c1 c2 c3 c4 c5 c6 : ℝ) :
    mode3 c1 c2 c3 c4 c5 c6 3 =
      -c2 - c3 + c6 := by
  unfold mode3
  dsimp only
  have h2 :
      2 * (((3 : ℕ) : ℝ) * Real.pi / 2) =
        Real.pi + 2 * Real.pi := by
    push_cast
    ring
  have h3 :
      3 * (((3 : ℕ) : ℝ) * Real.pi / 2) =
        (Real.pi / 2 + 2 * Real.pi) +
          2 * Real.pi := by
    push_cast
    ring
  have h1 :
      ((3 : ℕ) : ℝ) * Real.pi / 2 =
        Real.pi + Real.pi / 2 := by
    push_cast
    ring
  rw [h2, h3, h1]
  simp only [sin_two_pi_shift, cos_two_pi_shift]
  simp [Real.sin_add, Real.cos_add] <;> ring

/- GRANT-P2.2: periodicity by induction -/

theorem grant_p2_2_period_iter
    (c1 c2 c3 c4 c5 c6 : ℝ)
    (r k : ℕ) :
    mode3 c1 c2 c3 c4 c5 c6 (4 * k + r) =
      mode3 c1 c2 c3 c4 c5 c6 r := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have h :
          4 * (k + 1) + r =
            (4 * k + r) + 4 := by
        omega
      change
        mode3 c1 c2 c3 c4 c5 c6
          (4 * (k + 1) + r) =
        mode3 c1 c2 c3 c4 c5 c6 r
      calc
        mode3 c1 c2 c3 c4 c5 c6
            (4 * (k + 1) + r) =
          mode3 c1 c2 c3 c4 c5 c6
            ((4 * k + r) + 4) := by
              rw [h]
        _ = mode3 c1 c2 c3 c4 c5 c6
              (4 * k + r) :=
            mode3_period_four
              c1 c2 c3 c4 c5 c6
              (4 * k + r)
        _ = mode3 c1 c2 c3 c4 c5 c6 r :=
            ih

/- GRANT-P2.2: infinite residue zero -/

theorem grant_p2_2_residue_zero
    (c1 c2 c3 c4 c5 c6 : ℝ)
    (k : ℕ) :
    mode3 c1 c2 c3 c4 c5 c6 (4 * k) =
      c1 + c3 + c5 := by
  simpa only [Nat.add_zero, mode3_zero] using
    (grant_p2_2_period_iter
      c1 c2 c3 c4 c5 c6 0 k)

/- GRANT-P2.2: infinite residue one -/

theorem grant_p2_2_residue_one
    (c1 c2 c3 c4 c5 c6 : ℝ)
    (k : ℕ) :
    mode3 c1 c2 c3 c4 c5 c6 (4 * k + 1) =
      c2 - c3 - c6 := by
  rw [grant_p2_2_period_iter,
      grant_p2_1_mode3_one]

/- GRANT-P2.2: infinite residue two -/

theorem grant_p2_2_residue_two
    (c1 c2 c3 c4 c5 c6 : ℝ)
    (k : ℕ) :
    mode3 c1 c2 c3 c4 c5 c6 (4 * k + 2) =
      -c1 + c3 - c5 := by
  rw [grant_p2_2_period_iter,
      grant_p2_1_mode3_two]

/- GRANT-P2.2: infinite residue three -/

theorem grant_p2_2_residue_three
    (c1 c2 c3 c4 c5 c6 : ℝ)
    (k : ℕ) :
    mode3 c1 c2 c3 c4 c5 c6 (4 * k + 3) =
      -c2 - c3 + c6 := by
  rw [grant_p2_2_period_iter,
      grant_p2_1_mode3_three]

/- GRANT-P2.2: exact odd-residue difference -/

theorem grant_p2_2_odd_gap
    (c1 c2 c3 c4 c5 c6 : ℝ)
    (k : ℕ) :
    mode3 c1 c2 c3 c4 c5 c6 (4 * k + 1) -
      mode3 c1 c2 c3 c4 c5 c6 (4 * k + 3) =
        2 * (c2 - c6) := by
  rw [grant_p2_2_residue_one,
      grant_p2_2_residue_three]
  ring

/- Complete axiom audit -/

#print axioms LNZGrant.mode3_zero
#print axioms LNZGrant.mode3_angle_shift
#print axioms LNZGrant.sin_two_pi_shift
#print axioms LNZGrant.cos_two_pi_shift
#print axioms LNZGrant.mode3_period_four
#print axioms LNZGrant.grant_p2_1_mode3_one
#print axioms LNZGrant.grant_p2_1_mode3_two
#print axioms LNZGrant.grant_p2_1_mode3_three

#print axioms LNZGrant.grant_p2_2_period_iter
#print axioms LNZGrant.grant_p2_2_residue_zero
#print axioms LNZGrant.grant_p2_2_residue_one
#print axioms LNZGrant.grant_p2_2_residue_two
#print axioms LNZGrant.grant_p2_2_residue_three
#print axioms LNZGrant.grant_p2_2_odd_gap

end LNZGrant
