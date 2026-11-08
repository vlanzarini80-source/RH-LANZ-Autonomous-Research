
import Mathlib

namespace RHLanz

theorem p11_exact_exponent_identity
    (k : ℕ) :
    (2 : ℝ) ^ (32 * k) =
      (2 : ℝ) ^ (31 * k) * (2 : ℝ) ^ k := by
  rw [← pow_add]
  congr 1
  omega

#print axioms p11_exact_exponent_identity

end RHLanz
