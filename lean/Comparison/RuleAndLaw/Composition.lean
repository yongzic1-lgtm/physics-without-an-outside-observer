import Comparison.Law.Composite

/-! Extensions at the composition step of the line.
The finite identities below do not assign a new physical source to a particle.
-/

namespace Comparison.RuleAndLaw
open Comparison.Law Matrix

/-- Fourth order of Proposition 189: the coherent spectral composition minus the
record mixture has the NEGATIVE cross coefficient. -/
theorem fourth_order_difference (x y c : ℝ) :
    (x^4 + y^4 + 4*c*(x^3*y+x*y^3) + (4*c+2*c^2)*x^2*y^2) -
      ((1-c)*(x^4+y^4)+c*(x+y)^4) = -2*c*(1-c)*x^2*y^2 := by
  ring

/-- The spectral fourth moment, linked to the existing eigen-levels. -/
theorem eigen_fourth (x y c : ℝ)
    (hd : 0 ≤ (x-y)^2 + 4*c*x*y) :
    eigenPlus x y c ^ 4 + eigenMinus x y c ^ 4 =
      x^4+y^4+4*c*(x^3*y+x*y^3)+(4*c+2*c^2)*x^2*y^2 := by
  have hs := eigen_sq x y c hd
  have hp := eigen_prod x y c hd
  calc
    _ = (eigenPlus x y c ^ 2 + eigenMinus x y c ^ 2)^2 -
        2*(eigenPlus x y c * eigenMinus x y c)^2 := by ring
    _ = _ := by rw [hs, hp]; ring

/-- The original's claimed single-level coefficient needs k >= 2: at k=1
the coefficient is 1, independently of c. -/
theorem first_moment_unit_coefficient (x y c : ℝ) :
    (eigenPlus x y c + eigenMinus x y c) -
      (eigenPlus x 0 c + eigenMinus x 0 c) = y := by
  rw [eigen_sum, eigen_sum]
  ring

noncomputable def rootPlus (s : ℝ) : ℝ :=
  (3 + Real.sqrt (9 + 16 * Real.exp (-s))) / 8

noncomputable def rootMinus (s : ℝ) : ℝ :=
  (3 - Real.sqrt (9 + 16 * Real.exp (-s))) / 8

theorem root_product (s : ℝ) : rootPlus s * rootMinus s = -Real.exp (-s)/4 := by
  have h := sqrt_level_sq s
  dsimp [rootPlus, rootMinus]
  nlinarith

theorem rootPlus_pos (s : ℝ) : 0 < rootPlus s := by
  unfold rootPlus
  positivity

theorem rootMinus_neg (s : ℝ) : rootMinus s < 0 := by
  have hsq := sqrt_level_sq s
  have hs := sqrt_level_pos s
  have he := Real.exp_pos (-s)
  dsimp [rootMinus]
  nlinarith

/-- The positive root stays strictly above 3/4 at every finite level. -/
theorem rootPlus_gt (s : ℝ) : 3/4 < rootPlus s := by
  have hm := rootMinus_neg s
  dsimp [rootMinus] at hm
  dsimp [rootPlus]
  linarith

theorem rootPlus_le_one (s : ℝ) (hs : 0 ≤ s) : rootPlus s ≤ 1 := by
  have he : Real.exp (-s) ≤ 1 := by
    simpa using Real.exp_le_exp.mpr (show -s ≤ 0 by linarith)
  have hsq := sqrt_level_sq s
  have hpos := sqrt_level_pos s
  dsimp [rootPlus]
  nlinarith

/-- The positive-root shift is bounded. More repetitions within this same
function cannot supply an arbitrarily heavy rest response. -/
theorem delta_bounds (s : ℝ) (hs : 0 ≤ s) :
    0 ≤ deltaLevel s ∧ deltaLevel s < Real.log (4/3) := by
  rw [level_value]
  change 0 ≤ -Real.log (rootPlus s) ∧ -Real.log (rootPlus s) < Real.log (4/3)
  constructor
  · have h := Real.log_le_log (rootPlus_pos s) (rootPlus_le_one s hs)
    simp only [Real.log_one] at h
    linarith
  · have h := Real.log_lt_log (by norm_num : (0:ℝ) < 3/4) (rootPlus_gt s)
    have hi : Real.log (4/3 : ℝ) = -Real.log (3/4) := by
      rw [← Real.log_inv]
      congr 1
      norm_num
    rw [hi]
    linarith

/-- Both attenuation roots retain the source exactly; the negative root's
phase is not discarded by pretending it is a positive probability. -/
theorem both_attenuations (s : ℝ) :
    -Real.log (rootPlus s) - Real.log (-rootMinus s) - Real.log 4 = s := by
  have hp := rootPlus_pos s
  have hm : 0 < -rootMinus s := neg_pos.mpr (rootMinus_neg s)
  have hprod : rootPlus s * (-rootMinus s) = Real.exp (-s)/4 := by
    have h := root_product s
    nlinarith
  have hl := Real.log_mul (ne_of_gt hp) (ne_of_gt hm)
  rw [hprod, Real.log_div (ne_of_gt (Real.exp_pos (-s))) (by norm_num), Real.log_exp] at hl
  linarith

/-- Finite rank version of the heavy-root obstruction. -/
theorem finite_mode_ceiling {n : ℕ} (hn : 0 < n) (s : Fin n → ℝ)
    (hs : ∀ i, 0 ≤ s i) :
    (∑ i, deltaLevel (s i)) < n * Real.log (4/3) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h := Finset.sum_lt_sum_of_nonempty
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty)
    (fun i _ => (delta_bounds (s i) (hs i)).2)
  simpa using h

/-- All joint occupation counts, using the existing sixteen two-spinor states.
Divide by fifteen to get 1, 8/15, 4/15, 2/15, 1/15, 0. -/
theorem all_joint_counts : ∀ held : Finset (Fin 5),
    (Finset.univ.filter (fun U : Fin 16 => U ≠ 0 ∧ held ⊆ disagreeSet U)).card =
      (match held.card with | 0 => 15 | 1 => 8 | 2 => 4 | 3 => 2 | 4 => 1 | _ => 0) := by
  decide +kernel

/-- Algebraic Gram determinant with q the real part of the triangle phase. -/
def gramDet (c r q : ℝ) : ℝ := 1 - 3*c + 2*c*r*q

/-- The actual three-line determinant before the phase is parameterized.
For a Hermitian meeting y is the conjugate of x. -/
theorem gram_determinant (r x y : ℂ) :
    Matrix.det !![1, r, y; r, 1, r; x, r, 1] =
      1 - 2*r^2 - x*y + r^2*(x+y) := by
  simp only [Matrix.det_fin_three]
  simp
  ring

/-- At equal overlap, x*y=c and x+y=2*r*q give the triangle formula. -/
theorem gram_equal_overlap (c r q x y : ℂ)
    (hr : r^2 = c) (hp : x*y = c) (hs : x+y = 2*r*q) :
    Matrix.det !![1, r, y; r, 1, r; x, r, 1] = 1-3*c+2*c*r*q := by
  rw [gram_determinant, hr, hp, hs]
  ring

/-- At c=8/15, every nonpositive cosine gives a negative determinant. -/
theorem nonflat_quarter_excluded (r q : ℝ) (hr : 0 ≤ r) (hq : q ≤ 0) :
    gramDet (8/15) r q < 0 := by
  have h : r*q ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr hq
  dsimp [gramDet]
  nlinarith

/-- A fourth-root triangle has real part 1, 0, or -1. Positive Gram
determinant therefore forces its real part to be 1. -/
theorem discrete_triangle_flat (r q : ℝ) (hr : 0 ≤ r)
    (hq : q = 1 ∨ q = 0 ∨ q = -1) (hdet : 0 ≤ gramDet (8/15) r q) : q = 1 := by
  rcases hq with h | h | h
  · exact h
  · have hn := nonflat_quarter_excluded r q hr (by linarith)
    linarith
  · have hn := nonflat_quarter_excluded r q hr (by linarith)
    linarith

#print axioms fourth_order_difference
#print axioms eigen_fourth
#print axioms first_moment_unit_coefficient
#print axioms root_product
#print axioms rootPlus_pos
#print axioms rootMinus_neg
#print axioms rootPlus_gt
#print axioms rootPlus_le_one
#print axioms delta_bounds
#print axioms both_attenuations
#print axioms finite_mode_ceiling
#print axioms all_joint_counts
#print axioms gram_determinant
#print axioms gram_equal_overlap
#print axioms nonflat_quarter_excluded
#print axioms discrete_triangle_flat

end Comparison.RuleAndLaw
