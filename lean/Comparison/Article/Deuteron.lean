import Comparison.Article.QCosmos

/-!
# The deuteron (Proposition 124; Eq. (41); Proposition S124 and Eq. (40) of
the public edition)

* `uB_composition`: **`u_B = B_d/m_p = χ_A^{1/2} a³ [1 − (1 − k₃) ε₂]`** with `1 − k₃ = 1 + t/Eℓ = 41/40`
  (`k₃ = k(3-cycle) = −1/40`, `Existence/Planes.lean`: `k_values`), `χ_A = 1/(1 + Φ(i)) = 13/12`,
  `a = (1 − Φ(1))/8 = 5/38`, `ε₂ = α²/(1 + α/N₂)`; the binding to its printed digits is row G10
  (`QNucleon.lean`: `rowG10_digits`), `m_d/m_p` row G12.
* `gD_eq`, `deutM_eigen`, `deutD_share`: **`g = α_s²/Ψ₁ = 7/18`; the pole matrix
  `[[0, g√8], [g√8, 6 − 2g]]` has the eigenvalues `49/9` and `−2/9`, and at the low pole `−2/9` the D share is
  `P_D = 2/51`** (row T07).
* `mud_forms`: **`μ_d = μ_S − (μ_S − g_l)[(3/2)P_D + |Φ(i)| w_B/(1 + w_B)]`, `w_B = χ_A(1 − t)u_B`, is
  `(16μ_S + g_l)/17 − u_B(μ_S − g_l)/(20 + 13u_B)`**; its value is row G13.
-/

namespace Comparison.Article

open Real Comparison.Law

/-- **`1 − k₃ = 1 + t/Eℓ = 41/40`** with `t = t_{}` the transmission at here. -/
theorem one_sub_k3 : 1 + tS sHere / 16 = 41 / 40 := by
  rw [table_here.2.2.2.2.2.2.1]
  norm_num

/-- `χ_A = 1/(1 + Φ(i)) = 13/12` at `C`. -/
theorem chiA_eq : 1 / (1 + (PhiS sC).re) = 13 / 12 := by
  rw [piece_PhiC]
  norm_num

/-- **The deuteron's binding per proton mass.** -/
theorem uB_composition :
    qBd / qMp = √(1 / (1 + (PhiS sC).re)) * (aS sHere).re ^ 3 * (1 - (1 + tS sHere / 16) * qEps2) := by
  have hm : qMp ≠ 0 := (lt_of_lt_of_le (by norm_num) qMp_bnd.1).ne'
  rw [chiA_eq, one_sub_k3, piece_a_here, qBd]
  field_simp
  norm_num
  ring

/-- `g = α_s²/Ψ₁`: the colour meeting over the association at a plane. -/
noncomputable def gD : ℝ := meetS sLine (NS sF) / (PsiS sPlane).re

theorem gD_eq : gD = 7 / 18 := by
  rw [gD, piece_alphas_sq, piece_Psi_plane]
  norm_num

/-- **The deuteron's pole matrix** `[[0, g√8], [g√8, 6 − 2g]]`. -/
noncomputable def deutM : Matrix (Fin 2) (Fin 2) ℝ := !![0, gD * √8; gD * √8, 6 - 2 * gD]

theorem sqrt8 : √8 = 2 * √2 := by
  rw [show (8 : ℝ) = 2 ^ 2 * 2 by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

/-- The low pole's eigenvector `(−7√2/2, 1)` and the high pole's `(1, 7√2/2)`. -/
noncomputable def vLow : Fin 2 → ℝ := ![-(7 * √2 / 2), 1]
noncomputable def vHigh : Fin 2 → ℝ := ![1, 7 * √2 / 2]

/-- **The two poles: `49/9` and `−2/9`.** -/
theorem deutM_eigen :
    deutM.mulVec vLow = (-2 / 9 : ℝ) • vLow ∧ deutM.mulVec vHigh = (49 / 9 : ℝ) • vHigh ∧
      deutM.trace = 47 / 9 ∧ deutM.det = -98 / 81 := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i
    fin_cases i <;> simp [deutM, vLow, Matrix.mulVec, dotProduct, Fin.sum_univ_two, gD_eq, sqrt8] <;>
      nlinarith [h2]
  · ext i
    fin_cases i <;> simp [deutM, vHigh, Matrix.mulVec, dotProduct, Fin.sum_univ_two, gD_eq, sqrt8] <;>
      nlinarith [h2]
  · simp [deutM, Matrix.trace, Fin.sum_univ_two, gD_eq]
    norm_num
  · rw [deutM, Matrix.det_fin_two_of, gD_eq, sqrt8]
    nlinarith [h2]

/-- **The D share at the low pole: `P_D = y²/(x² + y²) = 2/51`.** -/
noncomputable def deutD_share : ℝ := vLow 1 ^ 2 / (vLow 0 ^ 2 + vLow 1 ^ 2)

theorem deutD_share_eq : deutD_share = 2 / 51 := by
  have h2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [deutD_share]
  simp [vLow]
  rw [show (7 * √2 / 2) ^ 2 = 49 / 4 * √2 ^ 2 by ring, h2]
  norm_num

/-- **Row T07 is the D share.** -/
theorem rowT07_eq_share : rowT07 = deutD_share := by
  rw [deutD_share_eq, rowT07]

/-- **The deuteron's moment in its two forms:** with `(3/2)P_D = 1/17` and the bound current
`|Φ(i)| w_B/(1 + w_B) = u_B/(20 + 13u_B)` at `w_B = χ_A(1 − t)u_B = (13/20)u_B`. -/
theorem mud_forms (μS gl u : ℝ) (hu : 0 ≤ u) :
    μS - (μS - gl) * ((3 / 2) * deutD_share +
        (1 / 13) * ((13 / 12) * (1 - 2 / 5) * u) / (1 + (13 / 12) * (1 - 2 / 5) * u)) =
      (16 * μS + gl) / 17 - u * (μS - gl) / (20 + 13 * u) := by
  rw [deutD_share_eq]
  have h1 : (0 : ℝ) < 20 + 13 * u := by linarith
  have h2 : (0 : ℝ) < 1 + 13 / 12 * (1 - 2 / 5) * u := by nlinarith
  field_simp
  ring

/-- **The deuteron's moment is row G13's composition** `μ_d(μ_p + μ_n, B_d)`. -/
theorem mud_is_row : qMud = qMus - (qMus - qGl) * ((3 / 2) * deutD_share +
    (1 / 13) * ((13 / 12) * (1 - 2 / 5) * qUB) / (1 + (13 / 12) * (1 - 2 / 5) * qUB)) := by
  rw [mud_forms qMus qGl qUB (le_trans (by norm_num) qUB_bnd.1), qMud]

end Comparison.Article
