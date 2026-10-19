import Comparison.Elements.TwoThings
import Mathlib.Analysis.Normed.Algebra.MatrixExponential

/-!
# An excursion with opposite orientation
# (statement 35, time reversal)

Statement 35 writes `Θ² = −I` and `(Θ ⊗ Θ) e^(−itL) (Θ ⊗ Θ)⁻¹ = e^(itL)`: the quaternionic structure on both systems turns the
comparison's evolution backwards. With `Θv = J v̄` (Book I, `Θ`, `Θ_Θ`) and on two systems
`Θ₂v = (J ⊗ J) v̄`:

* `JJ_mul_JJ`, `Θ₂_Θ₂`: `(J ⊗ J)² = 1`, so **`Θ₂² = +1` on two systems** (while `Θ² = −1` on one).
* `JJ_mul_conjL`: **`(J ⊗ J) L̄ = L (J ⊗ J)`**, from `γ_s J = J γ̄_s` (`γ_mul_J`); `Θ₂_L`: `Θ₂(Lv) = L(Θ₂v)`.
* `exp_map_star`: the entrywise conjugate of `exp X` is `exp X̄`.
* `time_reversal`: **`Θ₂(e^(−itL) v) = e^(itL) Θ₂v`** for every real `t` and every two-spinor state `v`, which is
  `(Θ ⊗ Θ) e^(−itL) (Θ ⊗ Θ)⁻¹ = e^(itL)`.
-/

open Matrix hiding J
open Complex Kronecker NormedSpace

namespace Comparison.ArticleStatements.Reversal

/-- **The quaternionic structure on two systems:** `Θ₂v = (J ⊗ J) v̄`. -/
noncomputable def Θ₂ (v : Two → ℂ) : Two → ℂ := (J ⊗ₖ J) *ᵥ star v

theorem kron_map_star (A B : Matrix Four Four ℂ) : (A ⊗ₖ B).map star = A.map star ⊗ₖ B.map star := by
  ext p q
  simp [Matrix.kroneckerMap_apply]

theorem JJ_map_star : (J ⊗ₖ J).map star = J ⊗ₖ J := by
  rw [kron_map_star, J_map_star]

/-- `(J ⊗ J)² = 1`. -/
theorem JJ_mul_JJ : (J ⊗ₖ J) * (J ⊗ₖ J) = 1 := by
  rw [← mul_kronecker_mul, J_mul_J, ← neg_one_smul ℂ (1 : Matrix Four Four ℂ), Matrix.smul_kronecker,
    Matrix.kronecker_smul, smul_smul, one_kronecker_one]
  norm_num

theorem star_mulVec_two (M : Matrix Two Two ℂ) (v : Two → ℂ) : star (M *ᵥ v) = M.map star *ᵥ star v := by
  ext i
  simp [Matrix.mulVec, dotProduct, star_sum, star_mul']

/-- **`Θ₂² = +1`** on two systems. -/
theorem Θ₂_Θ₂ (v : Two → ℂ) : Θ₂ (Θ₂ v) = v := by
  rw [Θ₂, Θ₂, star_mulVec_two, JJ_map_star, star_star, Matrix.mulVec_mulVec, JJ_mul_JJ,
    Matrix.one_mulVec]

/-- **`(J ⊗ J) L̄ = L (J ⊗ J)`.** -/
theorem JJ_mul_conjL : (J ⊗ₖ J) * L.map star = L * (J ⊗ₖ J) := by
  have hγ : ∀ s : Fin 5, (J ⊗ₖ J) * ((γ s).map star ⊗ₖ (γ s).map star) = (γ s ⊗ₖ γ s) * (J ⊗ₖ J) := by
    intro s
    rw [← mul_kronecker_mul, ← mul_kronecker_mul, ← γ_mul_J]
  have hL : L.map star = 1 ⊗ₖ 1 + ∑ s, (γ s).map star ⊗ₖ (γ s).map star := by
    rw [L]
    ext p q
    simp [Matrix.kroneckerMap_apply, Matrix.sum_apply, Matrix.one_apply]
  rw [hL, L, Matrix.mul_add, Matrix.add_mul, Finset.mul_sum, Finset.sum_mul]
  simp only [hγ, one_kronecker_one, Matrix.mul_one, Matrix.one_mul]

/-- **The quaternionic structure commutes with the comparison:** `Θ₂(Lv) = L(Θ₂v)`. -/
theorem Θ₂_L (v : Two → ℂ) : Θ₂ (L *ᵥ v) = L *ᵥ Θ₂ v := by
  rw [Θ₂, Θ₂, star_mulVec_two, Matrix.mulVec_mulVec, JJ_mul_conjL, ← Matrix.mulVec_mulVec]

theorem map_star_eq (M : Matrix Two Two ℂ) : M.map star = (Mᴴ)ᵀ := by
  ext i j
  simp [Matrix.conjTranspose_apply]

/-- **The conjugate of `exp X` is `exp X̄`.** -/
theorem exp_map_star (X : Matrix Two Two ℂ) : exp (X.map star) = (exp X).map star := by
  rw [map_star_eq, map_star_eq, exp_transpose, exp_conjTranspose]

/-- **Time reversal:** `Θ₂(e^(−itL) v) = e^(itL) Θ₂v` for real `t`, i.e.
`(Θ ⊗ Θ) e^(−itL) (Θ ⊗ Θ)⁻¹ = e^(itL)`. -/
theorem time_reversal (t : ℝ) (v : Two → ℂ) :
    Θ₂ (exp ((-((t : ℂ) * I)) • L) *ᵥ v) = exp (((t : ℂ) * I) • L) *ᵥ Θ₂ v := by
  have hU : IsUnit (J ⊗ₖ J) := ⟨⟨J ⊗ₖ J, J ⊗ₖ J, JJ_mul_JJ, JJ_mul_JJ⟩, rfl⟩
  have hinv : (J ⊗ₖ J)⁻¹ = J ⊗ₖ J := Matrix.inv_eq_left_inv JJ_mul_JJ
  have hsm : ((-((t : ℂ) * I)) • L).map star = ((t : ℂ) * I) • L.map star := by
    ext p q
    simp [Matrix.smul_apply, Complex.conj_ofReal]
  have hconj : (J ⊗ₖ J) * (((t : ℂ) * I) • L.map star) * (J ⊗ₖ J)⁻¹ = ((t : ℂ) * I) • L := by
    rw [hinv, Matrix.mul_smul, Matrix.smul_mul, JJ_mul_conjL, Matrix.mul_assoc, JJ_mul_JJ, Matrix.mul_one]
  have hexp : (J ⊗ₖ J) * exp (((t : ℂ) * I) • L.map star) = exp (((t : ℂ) * I) • L) * (J ⊗ₖ J) := by
    rw [← hconj, exp_conj _ _ hU, hinv, Matrix.mul_assoc, Matrix.mul_assoc, JJ_mul_JJ, Matrix.mul_one]
  rw [Θ₂, Θ₂, star_mulVec_two, ← exp_map_star, hsm, Matrix.mulVec_mulVec, hexp, ← Matrix.mulVec_mulVec]

end Comparison.ArticleStatements.Reversal

#print axioms Comparison.ArticleStatements.Reversal.kron_map_star
#print axioms Comparison.ArticleStatements.Reversal.JJ_map_star
#print axioms Comparison.ArticleStatements.Reversal.JJ_mul_JJ
#print axioms Comparison.ArticleStatements.Reversal.star_mulVec_two
#print axioms Comparison.ArticleStatements.Reversal.Θ₂_Θ₂
#print axioms Comparison.ArticleStatements.Reversal.JJ_mul_conjL
#print axioms Comparison.ArticleStatements.Reversal.Θ₂_L
#print axioms Comparison.ArticleStatements.Reversal.map_star_eq
#print axioms Comparison.ArticleStatements.Reversal.exp_map_star
#print axioms Comparison.ArticleStatements.Reversal.time_reversal
