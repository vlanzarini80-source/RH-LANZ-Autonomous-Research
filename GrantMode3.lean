
namespace LNZGrant

/-!
GRANT-P2.3
Exact geometric coefficient reconstruction.
Independent symbolic verification.
-/

set_option maxHeartbeats 400000

noncomputable def grantQM
    (a b c : ℝ) : ℝ :=
  Real.sqrt ((a ^ 2 + b ^ 2 + c ^ 2) / 3)

noncomputable def grantCHM
    (a b c : ℝ) : ℝ :=
  (a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c)

noncomputable def grantLBM
    (a b : ℝ) : ℝ :=
  b ^ 2 / a

/- Geometric inputs -/

noncomputable def grantQM1 : ℝ :=
  grantQM 5 12 13

noncomputable def grantQM2 : ℝ :=
  grantQM 11 60 61

noncomputable def grantCHM1 : ℝ :=
  grantCHM 5 12 13

noncomputable def grantLBM3 : ℝ :=
  grantLBM 5 (4 * Real.sqrt 6)

/- Coefficient definitions -/

noncomputable def grantC2 : ℝ :=
  (grantQM1 + grantQM2 + grantLBM3) / 468

noncomputable def grantC6 : ℝ :=
  (grantCHM1 - grantQM2) / 208

/- Radical identities -/

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

/- General square-root uniqueness -/

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

/- Exact reconstruction of geometric means -/

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

/- Derive signs from geometric definitions -/

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

/- Strict coefficient separation -/

theorem grant_p2_3_coefficients_distinct :
    grantC2 ≠ grantC6 := by
  exact ne_of_gt
    (lt_trans grant_p2_3_C6_neg
      grant_p2_3_C2_pos)

theorem grant_p2_3_gap_positive :
    0 < 2 * (grantC2 - grantC6) := by
  linarith [grant_p2_3_C2_pos,
    grant_p2_3_C6_neg]

/- Nonzero gap -/

theorem grant_p2_3_gap_nonzero :
    2 * (grantC2 - grantC6) ≠ 0 := by
  exact ne_of_gt grant_p2_3_gap_positive

/- Axiom audit -/

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

end LNZGrant
