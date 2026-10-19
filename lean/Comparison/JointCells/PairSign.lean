import Mathlib

/-!
# What a pair and a triangle see of the overlap's sign

The one composition of a bound state (Proposition 189) reads the law on the spectrum of `R = D^{1/2} G D^{1/2}`,
`D = diag(S_i)`, `G_ii = 1`, `G_ij` the pair overlap with `G_ij² = c`. This file proves, for the seven many-body places:

* `pair_sign_blind`: for two lines the trace and the determinant of `R`, hence its spectrum, depend on the overlap `g`
  only through `g²`: a two-line bound state (the deuteron, K⁰, π±) cannot tell `+c^{1/2}` from `−c^{1/2}`;
* `triangle_reads_sign`: for three equal lines `Tr G³ = 3 + 18g² + 6g³`, so `G(g)` and `G(−g)` differ in their
  triangle by `12g³`: a totally antisymmetric state of three world lines reads the sign;
* `gram_minus_det`, `gram_minus_not_pos`: `det(I − g(J − I)) = (1 − 2g)(1 + g)²`, negative at `g² = 8/15`
  (Proposition 194's coupling): the meeting matrix with every overlap `−c^{1/2}` is not positive.
-/

open Matrix

namespace Comparison.JointCells

/-- The level operator of two lines with overlap `g`, written with `s = (S₁S₂)^{1/2}`. -/
def pairR (S₁ S₂ s g : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![S₁, g * s; g * s, S₂]

/-- **A pair cannot see the sign of its overlap:** the trace and the determinant of the two-line level operator are
the same for `g` and `−g`. -/
theorem pair_sign_blind (S₁ S₂ s g : ℝ) :
    (pairR S₁ S₂ s g).trace = (pairR S₁ S₂ s (-g)).trace ∧
      (pairR S₁ S₂ s g).det = (pairR S₁ S₂ s (-g)).det := by
  constructor
  · simp [pairR, Matrix.trace_fin_two]
  · simp [pairR, Matrix.det_fin_two]

/-- The meeting matrix of three equal lines with overlap `g`. -/
def tri (g : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := !![1, g, g; g, 1, g; g, g, 1]

/-- **A triangle reads the sign:** `Tr G³ = 3 + 18g² + 6g³`. -/
theorem triangle_reads_sign (g : ℝ) : (tri g * tri g * tri g).trace = 3 + 18 * g ^ 2 + 6 * g ^ 3 := by
  simp [tri, Matrix.trace_fin_three]
  ring

/-- The two signs differ in the triangle by `12g³`. -/
theorem triangle_sign_difference (g : ℝ) :
    (tri g * tri g * tri g).trace - (tri (-g) * tri (-g) * tri (-g)).trace = 12 * g ^ 3 := by
  rw [triangle_reads_sign, triangle_reads_sign]
  ring

/-- **`det(I − g(J − I)) = (1 − 2g)(1 + g)²`.** -/
theorem gram_minus_det (g : ℝ) : (tri (-g)).det = (1 - 2 * g) * (1 + g) ^ 2 := by
  simp [tri, Matrix.det_fin_three]
  ring

/-- **At Proposition 194's coupling the negative-overlap meeting matrix is not positive:** for `g > 0` with
`g² = 8/15`, `det(I − g(J − I)) < 0`. -/
theorem gram_minus_not_pos (g : ℝ) (hg : 0 < g) (hc : g ^ 2 = 8 / 15) : (tri (-g)).det < 0 := by
  rw [gram_minus_det]
  have h1 : 1 / 2 < g := by nlinarith
  have h2 : 1 - 2 * g < 0 := by linarith
  have h3 : 0 < (1 + g) ^ 2 := by positivity
  exact mul_neg_of_neg_of_pos h2 h3

/-- With every overlap `+c^{1/2}` the meeting matrix is positive: `det(I + g(J − I)) = (1 + 2g)(1 − g)² > 0` for
`0 < g < 1`. -/
theorem gram_plus_det (g : ℝ) : (tri g).det = (1 + 2 * g) * (1 - g) ^ 2 := by
  simp [tri, Matrix.det_fin_three]
  ring

theorem gram_plus_pos (g : ℝ) (hg : 0 < g) (hg1 : g < 1) : 0 < (tri g).det := by
  rw [gram_plus_det]
  have h1 : 0 < 1 + 2 * g := by linarith
  have h2 : 0 < (1 - g) ^ 2 := by
    have : 0 < 1 - g := by linarith
    positivity
  exact mul_pos h1 h2

end Comparison.JointCells

#print axioms Comparison.JointCells.pair_sign_blind
#print axioms Comparison.JointCells.triangle_reads_sign
#print axioms Comparison.JointCells.triangle_sign_difference
#print axioms Comparison.JointCells.gram_minus_det
#print axioms Comparison.JointCells.gram_minus_not_pos
#print axioms Comparison.JointCells.gram_plus_det
#print axioms Comparison.JointCells.gram_plus_pos
