import Mathlib

/-! Algebra of the transported pole and its invariant quotients.
The kernel, source, boundary, and dual are transported together.
The source-specific physical assignments remain inputs to these identities.
-/
namespace Comparison.OneFormula

section Ring
variable {A : Type*} [Ring A]

theorem carried_sandwich (H V l J r : A) (hVH : V * H = 1) :
    (l * V) * (H * J * V) * (H * r) = l * J * r := by
  calc
    (l * V) * (H * J * V) * (H * r) =
        l * (V * H) * J * (V * H) * r := by simp only [mul_assoc]
    _ = l * J * r := by rw [hVH]; simp

theorem pole_commutator (l K r X : A) (hl : l * K = 0) (hr : K * r = 0) :
    l * (X * K - K * X) * r = 0 := by
  calc
    l * (X * K - K * X) * r = l * X * (K * r) - (l * K) * X * r := by
      noncomm_ring
    _ = 0 := by rw [hl, hr]; simp

theorem moving_frame_pole (l K r X J : A) (hl : l * K = 0) (hr : K * r = 0) :
    l * (J + (X * K - K * X)) * r = l * J * r := by
  rw [mul_add, add_mul, pole_commutator l K r X hl hr, add_zero]

end Ring

section Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {F : Type*} [Field F]

theorem trace_carried (H V A : Matrix n n F) (hVH : V * H = 1) :
    Matrix.trace (H * A * V) = Matrix.trace A := by
  rw [Matrix.trace_mul_comm, ← mul_assoc, hVH, one_mul]

theorem determinant_carried (H V A : Matrix n n F) (hVH : V * H = 1) :
    Matrix.det (H * A * V) = Matrix.det A := by
  have hd : Matrix.det V * Matrix.det H = 1 := by
    rw [← Matrix.det_mul, hVH, Matrix.det_one]
  rw [Matrix.det_mul, Matrix.det_mul]
  calc
    Matrix.det H * Matrix.det A * Matrix.det V =
        Matrix.det A * (Matrix.det V * Matrix.det H) := by ring
    _ = Matrix.det A := by rw [hd, mul_one]

end Matrix

theorem common_scale_ratio {F : Type*} [Field F] (x y a : F) (ha : a ≠ 0) :
    (a * x) / (a * y) = x / y := by
  exact mul_div_mul_left x y ha

theorem mixed_orthogonal : ((1 : ℚ) * 1 - 5 * 0) / 72 = 1 / 72 := by norm_num
theorem mixed_line_complement : ((1 : ℚ) * 4 - 5 * 0) / 72 = 1 / 18 := by norm_num
theorem mixed_plane_colour : ((2 : ℚ) * 3 - 5 * 0) / 72 = 1 / 12 := by norm_num
theorem return_odds_even : - (-(1 : ℚ) / 19) / (1 + (-(1 : ℚ) / 19)) = 1 / 18 := by norm_num
theorem return_odds_odd : - (-(1 : ℚ) / 13) / (1 + (-(1 : ℚ) / 13)) = 1 / 12 := by norm_num

end Comparison.OneFormula

#print axioms Comparison.OneFormula.carried_sandwich
#print axioms Comparison.OneFormula.pole_commutator
#print axioms Comparison.OneFormula.moving_frame_pole
#print axioms Comparison.OneFormula.trace_carried
#print axioms Comparison.OneFormula.determinant_carried
#print axioms Comparison.OneFormula.common_scale_ratio
#print axioms Comparison.OneFormula.mixed_orthogonal
#print axioms Comparison.OneFormula.mixed_line_complement
#print axioms Comparison.OneFormula.mixed_plane_colour
#print axioms Comparison.OneFormula.return_odds_even
#print axioms Comparison.OneFormula.return_odds_odd
