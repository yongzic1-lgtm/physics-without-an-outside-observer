module

public import Mathlib

/-! The through-third frame required by Proposition 90. The magnitude of a
retained overlap is separate from its normalized transport. -/

@[expose] public section

namespace Comparison.JointCells

open scoped Matrix

section Frame
variable {G : Type*} [Group G]

/-- Once the first two comparisons are fixed, the third is their carried product. -/
theorem third_frame_unique (a b c : G) (h : a * c = b) : c = a⁻¹ * b := by
  rw [← h]
  simp only [← mul_assoc, inv_mul_cancel, one_mul]

/-- The composed comparison triangle has identity holonomy, also noncommutatively. -/
theorem through_third_flat (a b : G) : a * (a⁻¹ * b) * b⁻¹ = 1 := by
  simp [← mul_assoc]

/-- Three relative comparisons obtained from three frames close. -/
theorem vertex_frames_flat (a b c : G) :
    (a⁻¹ * b) * (b⁻¹ * c) * (c⁻¹ * a) = 1 := by
  simp [mul_assoc]

end Frame

theorem sign_triangle (a b : ℝ) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) :
    a * (a * b) * b = 1 := by
  calc
    a * (a * b) * b = a ^ 2 * b ^ 2 := by ring
    _ = 1 := by rw [ha, hb, one_mul]

/-- Two negative comparisons force a positive third, not three negative edges. -/
theorem two_negative_force_positive (c : ℝ) (h : (-1 : ℝ) * c = -1) : c = 1 := by
  linarith

/-- A flat normalized triangle cannot have all three overlaps negative. -/
theorem three_negative_not_flat : (-1 : ℝ) * (-1) * (-1) ≠ 1 := by norm_num

def planeFrame : Matrix (Fin 5) (Fin 5) ℝ := Matrix.diagonal ![-1, -1, 1, 1, 1]
def colourFrame : Matrix (Fin 5) (Fin 5) ℝ := Matrix.diagonal ![1, 1, -1, -1, -1]

/-- The full comparison through a third joins F and C by the singlet's counterpart `{n}`. -/
theorem plane_colour_third : planeFrameᵀ * colourFrame = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [planeFrame, colourFrame, Matrix.mul_apply, Fin.sum_univ_five,
      Matrix.diagonal, Matrix.one_apply]

/-- The orientation-reversing third two-spinor state is used twice around the triangle. -/
theorem plane_colour_triangle : planeFrame * (-1) * colourFrameᵀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [planeFrame, colourFrame, Matrix.mul_apply, Fin.sum_univ_five,
      Matrix.diagonal, Matrix.one_apply]

end Comparison.JointCells

#print axioms Comparison.JointCells.third_frame_unique
#print axioms Comparison.JointCells.through_third_flat
#print axioms Comparison.JointCells.vertex_frames_flat
#print axioms Comparison.JointCells.sign_triangle
#print axioms Comparison.JointCells.two_negative_force_positive
#print axioms Comparison.JointCells.three_negative_not_flat
#print axioms Comparison.JointCells.plane_colour_third
#print axioms Comparison.JointCells.plane_colour_triangle

end
