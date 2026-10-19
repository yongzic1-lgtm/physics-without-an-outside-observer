import Comparison.Elements.OneThing
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.LinearCombination

/-!
# Spacetime and the radar step (statement 30)

Statement 30: `X ↦ AXA†`, `SL(2,ℂ)/{±I} = SO⁺(1,3)`, `det X = t² − |x|²`, `σ₅ = (2/5)𝟏𝟏ᵀ − I`, `v = 3/5`,
`γ = 5/4`, `ξ = log 2`, `tanh(ξ/4) = tan²(π/8)`: one side of a plane carries Lorentz transformations, and its
symmetric step is a radar echo with echo times four and one.

* `det_conj_action`, `conj_action_hermitian`: for `det A = 1` the action `X ↦ AXA†` keeps the
  determinant `t² − |x|²` (`det_planeMat` in Geometry.lean) and keeps Hermitian matrices Hermitian.
* `sl2_kernel`: **an `A` with `det A = 1` that fixes `1`, `σ₁` and `σ₃` is `±1`**: the action has kernel `{±I}`.
  (That every proper orthochronous Lorentz transformation arises, the other half of
  `SL(2,ℂ)/{±I} = SO⁺(1,3)`, is not proved here.)
* `radar_velocity`, `radar_gamma`, `radar_echo`: with `ξ = log 2`, **`tanh ξ = 3/5 = v`**, **`cosh ξ = 5/4 = γ`**,
  `γ = 1/√(1 − v²)`, and the echo ratio **`e^(2ξ) = 4`**: echo times four and one.
* `tanh_quarter`, `tan_sq_pi_div_eight`, `radar_quarter`: **`tanh(ξ/4) = 3 − 2√2 = tan²(π/8)`**.
-/

open Matrix hiding J
open Complex

namespace Comparison.ArticleStatements.Radar

/-! ## One side of a plane carries Lorentz transformations -/

/-- **`det(AXA†) = det X`** for `det A = 1`. -/
theorem det_conj_action (A X : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.det = 1) :
    (A * X * Aᴴ).det = X.det := by
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hA]
  simp

/-- The action keeps Hermitian matrices Hermitian. -/
theorem conj_action_hermitian (A X : Matrix (Fin 2) (Fin 2) ℂ) (hX : Xᴴ = X) :
    (A * X * Aᴴ)ᴴ = A * X * Aᴴ := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hX,
    Matrix.mul_assoc]

/-- **The kernel is `{±1}`:** an `A` with `det A = 1` fixing `1`, `σ₁` and `σ₃` under `X ↦ AXA†` is `±1`. -/
theorem sl2_kernel (A : Matrix (Fin 2) (Fin 2) ℂ) (hdet : A.det = 1) (h1 : A * Aᴴ = 1)
    (hs1 : A * σ₁ * Aᴴ = σ₁) (hs3 : A * σ₃ * Aᴴ = σ₃) : A = 1 ∨ A = -1 := by
  have h1' : Aᴴ * A = 1 :=
    (Matrix.mul_eq_one_comm_of_card_eq (m := Fin 2) (n := Fin 2) (R := ℂ) rfl).mp h1
  have c1 : A * σ₁ = σ₁ * A := by
    calc A * σ₁ = A * σ₁ * (Aᴴ * A) := by rw [h1', Matrix.mul_one]
      _ = A * σ₁ * Aᴴ * A := by simp only [Matrix.mul_assoc]
      _ = σ₁ * A := by rw [hs1]
  have c3 : A * σ₃ = σ₃ * A := by
    calc A * σ₃ = A * σ₃ * (Aᴴ * A) := by rw [h1', Matrix.mul_one]
      _ = A * σ₃ * Aᴴ * A := by simp only [Matrix.mul_assoc]
      _ = σ₃ * A := by rw [hs3]
  have e01 := congrFun (congrFun c3 0) 1
  have e10 := congrFun (congrFun c3 1) 0
  have e00 := congrFun (congrFun c1 0) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, σ₁, σ₃] at e01 e10 e00
  have h01 : A 0 1 = 0 := by linear_combination -e01 / 2
  have h10 : A 1 0 = 0 := by linear_combination e10 / 2
  rw [Matrix.det_fin_two] at hdet
  have hsq : (A 0 0 - 1) * (A 0 0 + 1) = 0 := by
    linear_combination hdet + A 0 0 * e00 + A 1 0 * h01
  rcases mul_eq_zero.mp hsq with h | h
  · left
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10] <;>
      first | linear_combination h | linear_combination h - e00
  · right
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h01, h10] <;>
      first | linear_combination h | linear_combination h - e00

/-! ## The radar step -/

theorem two_pos_real : (0 : ℝ) < 2 := by norm_num

/-- **`tanh ξ = 3/5 = v`** with `ξ = log 2`. -/
theorem radar_velocity : Real.tanh (Real.log 2) = 3 / 5 := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_log two_pos_real, Real.cosh_log two_pos_real]
  norm_num

/-- **`cosh ξ = 5/4 = γ = 1/√(1 − v²)`.** -/
theorem radar_gamma : Real.cosh (Real.log 2) = 5 / 4 ∧ 1 / Real.sqrt (1 - (3 / 5 : ℝ) ^ 2) = 5 / 4 := by
  refine ⟨?_, ?_⟩
  · rw [Real.cosh_log two_pos_real]
    norm_num
  · have h : Real.sqrt (1 - (3 / 5 : ℝ) ^ 2) = 4 / 5 := by
      rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)]
      norm_num
    rw [h]
    norm_num

/-- **The echo ratio `e^(2ξ) = 4`**: an echo sent at one returns at four. -/
theorem radar_echo : Real.exp (2 * Real.log 2) = 4 := by
  have h : (2 : ℝ) * Real.log 2 = Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [h, Real.exp_log (by norm_num)]

theorem sqrt_two_mul_self : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)

/-- **`tanh(ξ/4) = 3 − 2√2`.** -/
theorem tanh_quarter : Real.tanh (Real.log 2 / 4) = 3 - 2 * Real.sqrt 2 := by
  set x := Real.exp (Real.log 2 / 4) with hx
  have hxpos : 0 < x := Real.exp_pos _
  have hs : Real.sqrt 2 = Real.exp (Real.log 2 / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos two_pos_real]
    congr 1
    ring
  have hx2 : x ^ 2 = Real.sqrt 2 := by
    rw [hs, hx, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hx21 : x ^ 2 + 1 ≠ 0 := by positivity
  have e1 : (x - x⁻¹) / 2 / ((x + x⁻¹) / 2) = (x ^ 2 - 1) / (x ^ 2 + 1) := by
    have hx0 : x ≠ 0 := hxpos.ne'
    field_simp
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq, Real.exp_neg, ← hx, e1, hx2,
    div_eq_iff (by positivity)]
  linear_combination 2 * sqrt_two_mul_self

/-- **`tan²(π/8) = 3 − 2√2`.** -/
theorem tan_sq_pi_div_eight : Real.tan (Real.pi / 8) ^ 2 = 3 - 2 * Real.sqrt 2 := by
  have hs2 : Real.sqrt 2 ≤ 2 := by nlinarith [Real.sqrt_nonneg 2, sqrt_two_mul_self]
  rw [Real.tan_eq_sin_div_cos, Real.sin_pi_div_eight, Real.cos_pi_div_eight, div_pow, div_pow, div_pow,
    Real.sq_sqrt (by linarith), Real.sq_sqrt (by positivity), div_div_div_cancel_right₀ (by norm_num),
    div_eq_iff (by positivity)]
  linear_combination 2 * sqrt_two_mul_self

/-- **`tanh(ξ/4) = tan²(π/8)`** for the radar step `ξ = log 2`. -/
theorem radar_quarter : Real.tanh (Real.log 2 / 4) = Real.tan (Real.pi / 8) ^ 2 := by
  rw [tanh_quarter, tan_sq_pi_div_eight]

end Comparison.ArticleStatements.Radar

#print axioms Comparison.ArticleStatements.Radar.det_conj_action
#print axioms Comparison.ArticleStatements.Radar.conj_action_hermitian
#print axioms Comparison.ArticleStatements.Radar.sl2_kernel
#print axioms Comparison.ArticleStatements.Radar.two_pos_real
#print axioms Comparison.ArticleStatements.Radar.radar_velocity
#print axioms Comparison.ArticleStatements.Radar.radar_gamma
#print axioms Comparison.ArticleStatements.Radar.radar_echo
#print axioms Comparison.ArticleStatements.Radar.sqrt_two_mul_self
#print axioms Comparison.ArticleStatements.Radar.tanh_quarter
#print axioms Comparison.ArticleStatements.Radar.tan_sq_pi_div_eight
#print axioms Comparison.ArticleStatements.Radar.radar_quarter
