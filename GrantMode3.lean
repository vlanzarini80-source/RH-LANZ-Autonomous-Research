import Mathlib

namespace LNZGrant

set_option maxHeartbeats 400000

/-!
GRANT-P2.4a

Exact periodicity.
Infinite residue subsequences.
Exact geometric coefficients.
Strict subsequence separation.
Asymptotic incompatibility.
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

/- GRANT-P2.1 -/

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

/- GRANT-P2.2 -/

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

theorem grant_p2_2_residue_zero
    (c1 c2 c3 c4 c5 c6 : ℝ)
    (k : ℕ) :
    mode3 c1 c2 c3 c4 c5 c6 (4 * k) =
      c1 + c3 + c5 := by
  simpa only [Nat.add_zero, mode3_zero] using
    (grant_p2_2_period_iter
      c1 c2 c3 c4 c5 c6 0 k)

theorem grant_p2_2_residue_one
    (c1 c2 c3 c4 c5 c6 : ℝ)
    (k : ℕ) :
    mode3 c1 c2 c3 c4 c5 c6 (4 * k + 1) =
      c2 - c3 - c6 := by
  rw [grant_p2_2_period_iter,
      grant_p2_1_mode3_one]

theorem grant_p2_2_residue_two
    (c1 c2 c3 c4 c5 c6 : ℝ)
    (k : ℕ) :
    mode3 c1 c2 c3 c4 c5 c6 (4 * k + 2) =
      -c1 + c3 - c5 := by
  rw [grant_p2_2_period_iter,
      grant_p2_1_mode3_two]

theorem grant_p2_2_residue_three
    (c1 c2 c3 c4 c5 c6 : ℝ)
    (k : ℕ) :
    mode3 c1 c2 c3 c4 c5 c6 (4 * k + 3) =
      -c2 - c3 + c6 := by
  rw [grant_p2_2_period_iter,
      grant_p2_1_mode3_three]

theorem grant_p2_2_odd_gap
    (c1 c2 c3 c4 c5 c6 : ℝ)
    (k : ℕ) :
    mode3 c1 c2 c3 c4 c5 c6 (4 * k + 1) -
      mode3 c1 c2 c3 c4 c5 c6 (4 * k + 3) =
        2 * (c2 - c6) := by
  rw [grant_p2_2_residue_one,
      grant_p2_2_residue_three]
  ring

/- GRANT-P2.3a -/

noncomputable def grantQM
    (a b c : ℝ) : ℝ :=
  Real.sqrt ((a ^ 2 + b ^ 2 + c ^ 2) / 3)

noncomputable def grantCHM
    (a b c : ℝ) : ℝ :=
  (a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c)

noncomputable def grantLBM
    (a b : ℝ) : ℝ :=
  b ^ 2 / a

noncomputable def grantQM1 : ℝ :=
  grantQM 5 12 13

noncomputable def grantQM2 : ℝ :=
  grantQM 11 60 61

noncomputable def grantCHM1 : ℝ :=
  grantCHM 5 12 13

noncomputable def grantLBM3 : ℝ :=
  grantLBM 5 (4 * Real.sqrt 6)

noncomputable def grantC2 : ℝ :=
  (grantQM1 + grantQM2 + grantLBM3) / 468

noncomputable def grantC6 : ℝ :=
  (grantCHM1 - grantQM2) / 208

theorem grant_p2_3_sqrt6_sq :
    (Real.sqrt 6) ^ 2 = 6 := by
  exact Real.sq_sqrt (by norm_num)

theorem grant_p2_3_sqrt6_pos :
    0 < Real.sqrt 6 := by
  exact Real.sqrt_pos.2 (by norm_num)

theorem grant_p2_3_sqrt6_gt_one :
    1 < Real.sqrt 6 := by
  by_contra h
  have hle : Real.sqrt 6 ≤ 1 :=
    le_of_not_gt h
  have hn : 0 ≤ Real.sqrt 6 :=
    Real.sqrt_nonneg _
  have hm :
      0 ≤ (1 - Real.sqrt 6) *
        (1 + Real.sqrt 6) := by
    apply mul_nonneg <;> linarith
  nlinarith [grant_p2_3_sqrt6_sq]

theorem grant_p2_3_sqrt_unique
    (x y : ℝ)
    (hx : 0 ≤ x)
    (hy : 0 ≤ y)
    (hs : x ^ 2 = y ^ 2) :
    x = y := by
  have hf : (x - y) * (x + y) = 0 := by
    nlinarith [hs]
  rcases mul_eq_zero.mp hf with h | h
  · linarith
  · linarith

theorem grant_p2_3_QM1_exact :
    grantQM1 = 13 * Real.sqrt 6 / 3 := by
  unfold grantQM1 grantQM
  apply grant_p2_3_sqrt_unique
  · exact Real.sqrt_nonneg _
  · positivity
  · rw [Real.sq_sqrt (by norm_num)]
    nlinarith [grant_p2_3_sqrt6_sq]

theorem grant_p2_3_QM2_exact :
    grantQM2 = 61 * Real.sqrt 6 / 3 := by
  unfold grantQM2 grantQM
  apply grant_p2_3_sqrt_unique
  · exact Real.sqrt_nonneg _
  · positivity
  · rw [Real.sq_sqrt (by norm_num)]
    nlinarith [grant_p2_3_sqrt6_sq]

theorem grant_p2_3_CHM1_exact :
    grantCHM1 = 169 / 15 := by
  norm_num [grantCHM1, grantCHM]

theorem grant_p2_3_LBM3_exact :
    grantLBM3 = 96 / 5 := by
  unfold grantLBM3 grantLBM
  nlinarith [grant_p2_3_sqrt6_sq]

theorem grant_p2_3_C2_pos :
    0 < grantC2 := by
  unfold grantC2
  rw [grant_p2_3_QM1_exact,
      grant_p2_3_QM2_exact,
      grant_p2_3_LBM3_exact]
  linarith [grant_p2_3_sqrt6_pos]

theorem grant_p2_3_C6_neg :
    grantC6 < 0 := by
  unfold grantC6
  rw [grant_p2_3_CHM1_exact,
      grant_p2_3_QM2_exact]
  linarith [grant_p2_3_sqrt6_gt_one]

theorem grant_p2_3_coefficients_distinct :
    grantC2 ≠ grantC6 := by
  exact ne_of_gt
    (lt_trans grant_p2_3_C6_neg
      grant_p2_3_C2_pos)

theorem grant_p2_3_gap_positive :
    0 < 2 * (grantC2 - grantC6) := by
  linarith [grant_p2_3_C2_pos,
    grant_p2_3_C6_neg]

theorem grant_p2_3_gap_nonzero :
    2 * (grantC2 - grantC6) ≠ 0 := by
  exact ne_of_gt grant_p2_3_gap_positive

theorem grant_p2_3_physical_odd_gap
    (c1 c3 c4 c5 : ℝ)
    (k : ℕ) :
    0 <
      mode3 c1 grantC2 c3 c4 c5 grantC6
        (4 * k + 1) -
      mode3 c1 grantC2 c3 c4 c5 grantC6
        (4 * k + 3) := by
  rw [grant_p2_2_odd_gap]
  exact grant_p2_3_gap_positive

/- GRANT-P2.4a: asymptotic incompatibility -/

theorem grant_p2_4a_gap_limit
    (f g : ℕ → ℝ)
    (a b : ℝ)
    (hf : Filter.Tendsto f Filter.atTop
      (nhds a))
    (hg : Filter.Tendsto g Filter.atTop
      (nhds b)) :
    Filter.Tendsto
      (fun k => f k - g k)
      Filter.atTop
      (nhds (a - b)) := by
  exact hf.sub hg

theorem grant_p2_4a_noncompensation
    (f g : ℕ → ℝ)
    (d : ℝ)
    (hd : 0 < d)
    (hgap : ∀ k : ℕ, f k - g k = d) :
    ¬ ∃ L : ℝ,
      Filter.Tendsto f Filter.atTop
        (nhds L) ∧
      Filter.Tendsto g Filter.atTop
        (nhds L) := by
  rintro ⟨L, hf, hg⟩
  have hz :
      Filter.Tendsto
        (fun k => f k - g k)
        Filter.atTop (nhds 0) := by
    simpa only [sub_self] using hf.sub hg
  have he :
      (fun k => f k - g k) =
        (fun _ : ℕ => d) := by
    funext k
    exact hgap k
  rw [he] at hz
  have hc :
      Filter.Tendsto
        (fun _ : ℕ => d)
        Filter.atTop (nhds d) :=
    tendsto_const_nhds
  have hh : d = 0 :=
    tendsto_nhds_unique hc hz
  linarith

theorem grant_p2_4a_mode3_no_common_limit
    (c1 c3 c4 c5 : ℝ) :
    ¬ ∃ L : ℝ,
      Filter.Tendsto
        (fun k : ℕ =>
          mode3 c1 grantC2 c3 c4 c5 grantC6
            (4 * k + 1))
        Filter.atTop (nhds L) ∧
      Filter.Tendsto
        (fun k : ℕ =>
          mode3 c1 grantC2 c3 c4 c5 grantC6
            (4 * k + 3))
        Filter.atTop (nhds L) := by
  apply grant_p2_4a_noncompensation
    _ _ (2 * (grantC2 - grantC6))
    grant_p2_3_gap_positive
  intro k
  exact grant_p2_2_odd_gap
    c1 grantC2 c3 c4 c5 grantC6 k

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

#print axioms LNZGrant.grant_p2_3_sqrt6_sq
#print axioms LNZGrant.grant_p2_3_sqrt6_pos
#print axioms LNZGrant.grant_p2_3_sqrt6_gt_one
#print axioms LNZGrant.grant_p2_3_sqrt_unique
#print axioms LNZGrant.grant_p2_3_QM1_exact
#print axioms LNZGrant.grant_p2_3_QM2_exact
#print axioms LNZGrant.grant_p2_3_CHM1_exact
#print axioms LNZGrant.grant_p2_3_LBM3_exact
#print axioms LNZGrant.grant_p2_3_C2_pos
#print axioms LNZGrant.grant_p2_3_C6_neg
#print axioms LNZGrant.grant_p2_3_coefficients_distinct
#print axioms LNZGrant.grant_p2_3_gap_positive
#print axioms LNZGrant.grant_p2_3_gap_nonzero
#print axioms LNZGrant.grant_p2_3_physical_odd_gap

#print axioms LNZGrant.grant_p2_4a_gap_limit
#print axioms LNZGrant.grant_p2_4a_noncompensation
#print axioms LNZGrant.grant_p2_4a_mode3_no_common_limit

end LNZGrant
