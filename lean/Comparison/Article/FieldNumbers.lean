import Comparison.Article.QCouplings
import Comparison.WholePicture.SecondVariation

/-!
# The field in units of the charge, and the pencil of a mass (Eqs. (36) and (38))

* `flux_metric_numbers` (**Eq. (36)**): with the stiffness `κ = 1/200` at the plane and `1/98` at colour
  (`WholePicture/SecondVariation.lean`: `kappa_quarters`), **`8πκα = 9.170124·10⁻⁴`, `8πκα_s = 3.022369·10⁻²`,
  and `1/16πα = 2.726245`**, each to the digits the article prints.
* `pencil_det`, `pencil_zero`, `pencil_rescale`, `pencil_ratio` (**Eq. (38)**): the two-by-two pencil
  `K_X(ζ) = [[ζC_L, −A], [−B, ζC_R]]` has `det K_X(ζ) = ζ²C_LC_R − AB`, so **its zeros are `ζ = ±Ω_X`,
  `Ω_X² = AB/(C_LC_R)`**; a change of either end's description that multiplies `AB` and `C_LC_R` by one factor keeps
  `Ω_X`, and `m_X/m_e = Ω_X/Ω_e` is a ratio of two such zeros.
-/

namespace Comparison.Article

open Real

/-- **Eq. (36): the field in units of the charge, numerically.** -/
theorem flux_metric_numbers :
    ((9.1701235e-4 : ℝ) < 8 * π * (1 / 200) * qAlpha ∧ 8 * π * (1 / 200) * qAlpha < 9.1701245e-4) ∧
      ((3.0223685e-2 : ℝ) < 8 * π * (1 / 98) * qAlphaS ∧ 8 * π * (1 / 98) * qAlphaS < 3.0223695e-2) ∧
      ((2.7262445 : ℝ) < 1 / (16 * π * qAlpha) ∧ 1 / (16 * π * qAlpha) < 2.7262455) := by
  have h1 := Bnd.mul (Bnd.mul bnd_pi (Bnd.const (8 * (1 / 200) : ℝ)) (by norm_num) (by norm_num)) qAlpha_bnd
    (by norm_num) (by norm_num)
  have h2 := Bnd.mul (Bnd.mul bnd_pi (Bnd.const (8 * (1 / 98) : ℝ)) (by norm_num) (by norm_num)) qAlphaS_bnd
    (by norm_num) (by norm_num)
  have h3 := Bnd.mul (Bnd.mul bnd_pi (Bnd.const (16 : ℝ)) (by norm_num) (by norm_num)) qAlpha_bnd
    (by norm_num) (by norm_num)
  have h3' := Bnd.inv h3 (by norm_num)
  have e1 : 8 * π * (1 / 200) * qAlpha = π * (8 * (1 / 200)) * qAlpha := by ring
  have e2 : 8 * π * (1 / 98) * qAlphaS = π * (8 * (1 / 98)) * qAlphaS := by ring
  have e3 : 1 / (16 * π * qAlpha) = (π * 16 * qAlpha)⁻¹ := by rw [one_div]; ring_nf
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]; exact h1.strict (by norm_num) (by norm_num)
  · rw [e2]; exact h2.strict (by norm_num) (by norm_num)
  · rw [e3]; exact h3'.strict (by norm_num) (by norm_num)

/-- The two-by-two pencil of a mass at its zero. -/
def pencil (ζ CL CR A B : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![ζ * CL, -A; -B, ζ * CR]

theorem pencil_det (ζ CL CR A B : ℝ) : (pencil ζ CL CR A B).det = ζ ^ 2 * (CL * CR) - A * B := by
  rw [pencil, Matrix.det_fin_two_of]
  ring

/-- **The zeros of the pencil:** `det K_X(ζ) = 0` exactly when `ζ² = Ω_X² = AB/(C_LC_R)`. -/
theorem pencil_zero (ζ CL CR A B : ℝ) (hC : CL * CR ≠ 0) :
    (pencil ζ CL CR A B).det = 0 ↔ ζ ^ 2 = A * B / (CL * CR) := by
  rw [pencil_det, eq_div_iff hC, sub_eq_zero]

/-- **A change of either end's description** that multiplies `AB` and `C_LC_R` by one factor `c ≠ 0` keeps
`Ω_X² = AB/(C_LC_R)`. -/
theorem pencil_rescale (CL CR A B c : ℝ) (hc : c ≠ 0) (hC : CL * CR ≠ 0) :
    (c * (A * B)) / (c * (CL * CR)) = A * B / (CL * CR) := by
  rw [mul_div_mul_left _ _ hc]

/-- **`m_X/m_e = Ω_X/Ω_e`**: the ratio of two positive zeros is the root of the ratio of their `Ω²`. -/
theorem pencil_ratio (ΩX Ωe : ℝ) (hX : 0 < ΩX) (he : 0 < Ωe) : ΩX / Ωe = √(ΩX ^ 2 / Ωe ^ 2) := by
  rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq hX.le, Real.sqrt_sq he.le]

end Comparison.Article
