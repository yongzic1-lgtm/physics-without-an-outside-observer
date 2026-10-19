import Comparison.Existence.LastDirectionSplit
import Comparison.WholePicture.Curvature
import Comparison.GroupsContinuumLaw.Ward

/-!
# The double grading selects the complementary-plane wedge, and `Λℓ² = 3`

At the last-step direction `h = 0` take the four tangent lines `χ_μ = γ_{μ+1}`.

* `tangent_grade_is_lastDirection`: **`χ₀χ₁χ₂χ₃ = γ₁γ₂γ₃γ₄ = γ₀`**; `double_grade_is_agreement`: the double grading
  `χ₅ ⊗ γ₀` **is the last-step direction-agreement summand `γ₀ ⊗ γ₀` of the comparison `L`**;
  `lastDirection_agreement_singlet`, `marked_bass_singlet`: it fixes the singlet, and the marked Bass operator
  `(1 + u + 4u²) − uL − s γ₀⊗γ₀` has the singlet eigenvalue `1 − 5u + 4u² − s`.
* `external_oriented_trace`: `tr(χ₅χ_μχ_νχ_ρχ_σ) = 4ε_{μνρσ}`; `double_grade_trace_zero`:
  `tr(χ₅ ⊗ γ₀) = 0`.
* `double_grade_curvature_square`: **`tr((χ₅ ⊗ γ₀) E²) = ¼ Σ ε_{μνρσ} ε_{0abcd} F^{ab}_{μν} F^{cd}_{ρσ}`**
  for `E = ½ Σ χ_μχ_ν ⊗ 𝓕_{μν}`, `𝓕 = ¼ Σ F^{ab} γ_aγ_b`: the double-graded response is the
  complementary-plane wedge, for every curvature (moved directions included).
* `cubic_trace`: the coefficient of `st²` in `Σ_n tr((tE + sH)ⁿ)/n` is `tr(HE²)`.
* `square_versus_wedge`: for `E₀ = χ₀χ₁⊗γ₁γ₂ + χ₂χ₃⊗γ₃γ₄`, `tr((1 ⊗ γ₀)E₀²) = 0` while
  `tr((χ₅ ⊗ γ₀)E₀²) = 32`: the second grading is indispensable.
* `lambda_ell_sq`: with the wedge selected, `WholePicture.curvature_identity` gives
  `−(4/ℓ²)(R − 6/ℓ²)` and **`Λℓ² = 3`**.
-/

namespace Comparison.GroupsContinuumLaw

open Matrix hiding J
open Kronecker
open WholePicture (eps4)

/-- **The tangent grading is the last-step direction:** `γ₁γ₂γ₃γ₄ = γ₀`. -/
theorem tangent_grade_is_lastDirection : γ 1 * γ 2 * γ 3 * γ 4 = γ 0 := by
  have h : γ 0 * (γ 1 * γ 2 * γ 3 * γ 4) = 1 := by
    rw [← γ_prod]
    simp only [Matrix.mul_assoc]
  calc γ 1 * γ 2 * γ 3 * γ 4 = (γ 0 * γ 0) * (γ 1 * γ 2 * γ 3 * γ 4) := by
        rw [γ_mul_self, Matrix.one_mul]
    _ = γ 0 * (γ 0 * (γ 1 * γ 2 * γ 3 * γ 4)) := by rw [Matrix.mul_assoc]
    _ = γ 0 := by rw [h, Matrix.mul_one]

/-- The double grading `χ₅ ⊗ γ₀`. -/
noncomputable def doubleGrade : Matrix Two Two ℂ := (γ 1 * γ 2 * γ 3 * γ 4) ⊗ₖ γ 0

/-- The last-step direction-agreement summand of `L = 1 ⊗ 1 + Σ_t γ_t ⊗ γ_t`. -/
noncomputable def lastDirectionAgreement : Matrix Two Two ℂ := γ 0 ⊗ₖ γ 0

/-- **The double grading is the last-step direction-agreement operator.** -/
theorem double_grade_is_agreement : doubleGrade = lastDirectionAgreement := by
  rw [doubleGrade, tangent_grade_is_lastDirection, lastDirectionAgreement]

/-- **The last-step direction agreement fixes the singlet.** -/
theorem lastDirection_agreement_singlet : lastDirectionAgreement *ᵥ Ω = Ω := by
  have h := agreement 0 0
  rw [rel_zero] at h
  rw [lastDirectionAgreement, h]
  simp [disagreeSet]

/-- **The marked Bass operator on the singlet:** `(1 + u + 4u²) − uL − s γ₀⊗γ₀` has the eigenvalue
`1 − 5u + 4u² − s` on `Ω`. -/
theorem marked_bass_singlet (u s : ℂ) :
    ((1 + u + 4 * u ^ 2) • (1 : Matrix Two Two ℂ) - u • L - s • lastDirectionAgreement) *ᵥ Ω =
      (1 - 5 * u + 4 * u ^ 2 - s) • Ω := by
  rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, L_mulVec_singlet, lastDirection_agreement_singlet, smul_smul]
  module

theorem lc5_eps4 : ∀ μ ν ρ σ : Fin 4, lc5 0 μ.succ ν.succ ρ.succ σ.succ = eps4 μ ν ρ σ := by
  decide

/-- **The external oriented trace:** `tr(χ₅χ_μχ_νχ_ρχ_σ) = 4ε_{μνρσ}`. -/
theorem external_oriented_trace (μ ν ρ σ : Fin 4) :
    (γ 1 * γ 2 * γ 3 * γ 4 * γ μ.succ * γ ν.succ * γ ρ.succ * γ σ.succ).trace =
      4 * (eps4 μ ν ρ σ : ℂ) := by
  rw [tangent_grade_is_lastDirection, trace_five, lc5_eps4]

theorem gamma_trace_zero (a : Fin 5) : (γ a).trace = 0 := γ_trace a

theorem trace_one_four : (1 : Matrix Four Four ℂ).trace = 4 := by
  simp [Matrix.trace_one]

/-- **The double grading has trace zero.** -/
theorem double_grade_trace_zero : doubleGrade.trace = 0 := by
  rw [doubleGrade, Matrix.trace_kronecker, tangent_grade_is_lastDirection, γ_trace, zero_mul]

/-- The internal curvature `𝓕_{μν} = ¼ Σ_{ab} F^{ab}_{μν} γ_aγ_b`. -/
noncomputable def internalCurv (F : Fin 4 → Fin 4 → Fin 5 → Fin 5 → ℂ) (μ ν : Fin 4) :
    Matrix Four Four ℂ :=
  (1 / 4 : ℂ) • ∑ a, ∑ b, F μ ν a b • (γ a * γ b)

/-- The curvature term of the first-order operator: `E = ½ Σ_{μν} χ_μχ_ν ⊗ 𝓕_{μν}`. -/
noncomputable def pauliCurv (F : Fin 4 → Fin 4 → Fin 5 → Fin 5 → ℂ) : Matrix Two Two ℂ :=
  (1 / 2 : ℂ) • ∑ μ, ∑ ν, (γ μ.succ * γ ν.succ) ⊗ₖ internalCurv F μ ν

/-- The last-step direction-graded wedge `¼ Σ ε_{μνρσ} ε_{0abcd} F^{ab}_{μν} F^{cd}_{ρσ}`. -/
noncomputable def wedgeLastDirection (F : Fin 4 → Fin 4 → Fin 5 → Fin 5 → ℂ) : ℂ :=
  (1 / 4 : ℂ) * ∑ μ, ∑ ν, ∑ ρ, ∑ σ, ∑ a, ∑ b, ∑ c, ∑ d,
    (eps4 μ ν ρ σ : ℂ) * (lc5 0 a b c d : ℂ) * (F μ ν a b * F ρ σ c d)

theorem internalCurv_pairs (F : Fin 4 → Fin 4 → Fin 5 → Fin 5 → ℂ) (μ ν : Fin 4) :
    internalCurv F μ ν = (1 / 4 : ℂ) • ∑ p : Fin 5 × Fin 5, F μ ν p.1 p.2 • (γ p.1 * γ p.2) := by
  rw [internalCurv, Fintype.sum_prod_type]

theorem tr_internal (F : Fin 4 → Fin 4 → Fin 5 → Fin 5 → ℂ) (μ ν ρ σ : Fin 4) :
    (γ 0 * (internalCurv F μ ν * internalCurv F ρ σ)).trace =
      (1 / 4 : ℂ) * ∑ p : Fin 5 × Fin 5, ∑ q : Fin 5 × Fin 5,
        (lc5 0 p.1 p.2 q.1 q.2 : ℂ) * (F μ ν p.1 p.2 * F ρ σ q.1 q.2) := by
  rw [internalCurv_pairs, internalCurv_pairs]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul, smul_eq_mul]
  rw [Finset.sum_mul_sum]
  simp only [Finset.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul, smul_eq_mul]
  have e : γ 0 * (γ p.1 * γ p.2 * (γ q.1 * γ q.2)) = γ 0 * γ p.1 * γ p.2 * γ q.1 * γ q.2 := by
    simp only [Matrix.mul_assoc]
  rw [e, trace_five]
  ring

theorem tr_external (μ ν ρ σ : Fin 4) :
    (γ 0 * (γ μ.succ * γ ν.succ * (γ ρ.succ * γ σ.succ))).trace = 4 * (eps4 μ ν ρ σ : ℂ) := by
  have e : γ 0 * (γ μ.succ * γ ν.succ * (γ ρ.succ * γ σ.succ)) =
      γ 0 * γ μ.succ * γ ν.succ * γ ρ.succ * γ σ.succ := by
    simp only [Matrix.mul_assoc]
  rw [e, trace_five, lc5_eps4]

theorem pauliCurv_pairs (F : Fin 4 → Fin 4 → Fin 5 → Fin 5 → ℂ) :
    pauliCurv F = (1 / 2 : ℂ) • ∑ P : Fin 4 × Fin 4,
      (γ P.1.succ * γ P.2.succ) ⊗ₖ internalCurv F P.1 P.2 := by
  rw [pauliCurv, Fintype.sum_prod_type]

/-- **The double-graded curvature response is the complementary-plane wedge:**
`tr((χ₅ ⊗ γ₀) E E) = ¼ Σ ε_{μνρσ} ε_{0abcd} F^{ab}_{μν} F^{cd}_{ρσ}` for every curvature `F`. -/
theorem double_grade_curvature_square (F : Fin 4 → Fin 4 → Fin 5 → Fin 5 → ℂ) :
    (doubleGrade * (pauliCurv F * pauliCurv F)).trace =
      (1 / 4 : ℂ) * ∑ P : Fin 4 × Fin 4, ∑ Q : Fin 4 × Fin 4, ∑ p : Fin 5 × Fin 5,
        ∑ q : Fin 5 × Fin 5, (eps4 P.1 P.2 Q.1 Q.2 : ℂ) * (lc5 0 p.1 p.2 q.1 q.2 : ℂ) *
          (F P.1 P.2 p.1 p.2 * F Q.1 Q.2 q.1 q.2) := by
  rw [double_grade_is_agreement, lastDirectionAgreement, pauliCurv_pairs]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_smul, smul_eq_mul]
  rw [Finset.sum_mul_sum]
  simp only [Finset.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun Q _ => ?_
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker, tr_external,
    tr_internal]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  ring

/-- The last-step direction-graded wedge `¼ Σ ε_{μνρσ} ε_{0abcd} F^{ab}_{μν} F^{cd}_{ρσ}` as the response. -/
theorem double_grade_is_wedge (F : Fin 4 → Fin 4 → Fin 5 → Fin 5 → ℂ) :
    (doubleGrade * (pauliCurv F * pauliCurv F)).trace = wedgeLastDirection F := by
  rw [double_grade_curvature_square, wedgeLastDirection]
  congr 1
  simp only [Fintype.sum_prod_type]

/-- **The cubic term of the marked logarithm:** `tr((tE + sH)³) = t³tr E³ + 3t²s tr(HE²) +
3ts² tr(EH²) + s³ tr H³`; in `Σ_n tr((tE + sH)ⁿ)/n` the coefficient of `st²` is `tr(HE²)`. -/
theorem cubic_trace {n : Type*} [Fintype n] [DecidableEq n] (E H : Matrix n n ℂ) (s t : ℂ) :
    ((t • E + s • H) ^ 3).trace = t ^ 3 * (E * E * E).trace + 3 * t ^ 2 * s * (H * E * E).trace +
      3 * t * s ^ 2 * (E * H * H).trace + s ^ 3 * (H * H * H).trace := by
  have c1 : (E * E * H).trace = (H * E * E).trace := by
    rw [Matrix.trace_mul_cycle]
  have c2 : (E * H * E).trace = (H * E * E).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  have c3 : (H * E * H).trace = (E * H * H).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]
  have c4 : (H * H * E).trace = (E * H * H).trace := by
    rw [Matrix.trace_mul_cycle]
  simp only [pow_succ, pow_zero, Matrix.one_mul, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  rw [c1, c2, c3, c4]
  ring

theorem g12_sq : γ 1 * γ 2 * (γ 1 * γ 2) = -1 := by
  have h21 : γ 2 * γ 1 = -(γ 1 * γ 2) := γ_anticomm (by decide)
  calc γ 1 * γ 2 * (γ 1 * γ 2) = γ 1 * (γ 2 * γ 1) * γ 2 := by simp only [Matrix.mul_assoc]
    _ = -1 := by
      rw [h21, Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc, γ_mul_self, Matrix.one_mul, γ_mul_self]

theorem g34_sq : γ 3 * γ 4 * (γ 3 * γ 4) = -1 := by
  have h43 : γ 4 * γ 3 = -(γ 3 * γ 4) := γ_anticomm (by decide)
  calc γ 3 * γ 4 * (γ 3 * γ 4) = γ 3 * (γ 4 * γ 3) * γ 4 := by simp only [Matrix.mul_assoc]
    _ = -1 := by
      rw [h43, Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc, γ_mul_self, Matrix.one_mul, γ_mul_self]

theorem g34_g1 : γ 3 * γ 4 * γ 1 = γ 1 * (γ 3 * γ 4) := by
  have a13 : γ 3 * γ 1 = -(γ 1 * γ 3) := γ_anticomm (by decide)
  have a14 : γ 4 * γ 1 = -(γ 1 * γ 4) := γ_anticomm (by decide)
  rw [Matrix.mul_assoc, a14, Matrix.mul_neg, ← Matrix.mul_assoc, a13, Matrix.neg_mul, neg_neg,
    Matrix.mul_assoc]

theorem g34_g2 : γ 3 * γ 4 * γ 2 = γ 2 * (γ 3 * γ 4) := by
  have a23 : γ 3 * γ 2 = -(γ 2 * γ 3) := γ_anticomm (by decide)
  have a24 : γ 4 * γ 2 = -(γ 2 * γ 4) := γ_anticomm (by decide)
  rw [Matrix.mul_assoc, a24, Matrix.mul_neg, ← Matrix.mul_assoc, a23, Matrix.neg_mul, neg_neg,
    Matrix.mul_assoc]

theorem g12_g34_comm : γ 3 * γ 4 * (γ 1 * γ 2) = γ 1 * γ 2 * (γ 3 * γ 4) := by
  rw [← Matrix.mul_assoc, g34_g1, Matrix.mul_assoc, g34_g2, ← Matrix.mul_assoc]

theorem g12_g34 : γ 1 * γ 2 * (γ 3 * γ 4) = γ 0 := by
  rw [← tangent_grade_is_lastDirection]
  simp only [Matrix.mul_assoc]

/-- The counterexample's curvature `E₀ = χ₀χ₁⊗γ₁γ₂ + χ₂χ₃⊗γ₃γ₄` (`χ_μ = γ_{μ+1}`). -/
noncomputable def E0 : Matrix Two Two ℂ := (γ 1 * γ 2) ⊗ₖ (γ 1 * γ 2) + (γ 3 * γ 4) ⊗ₖ (γ 3 * γ 4)

theorem E0_sq : E0 * E0 = (2 : ℂ) • (1 : Matrix Two Two ℂ) + (2 : ℂ) • (γ 0 ⊗ₖ γ 0) := by
  rw [E0]
  simp only [Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_kronecker_mul, g12_sq, g34_sq,
    g12_g34_comm, g12_g34]
  have hn : ((-1 : Matrix Four Four ℂ) ⊗ₖ (-1 : Matrix Four Four ℂ)) = 1 := by
    rw [show (-1 : Matrix Four Four ℂ) = (-1 : ℂ) • (1 : Matrix Four Four ℂ) by simp,
      Matrix.smul_kronecker, Matrix.kronecker_smul, Matrix.one_kronecker_one, smul_smul]
    norm_num
  rw [hn]
  module

/-- **The square pairing and the wedge differ:** `tr((1 ⊗ γ₀)E₀²) = 0`, `tr((χ₅ ⊗ γ₀)E₀²) = 32`. -/
theorem square_versus_wedge :
    (((1 : Matrix Four Four ℂ) ⊗ₖ γ 0) * (E0 * E0)).trace = 0 ∧
      (doubleGrade * (E0 * E0)).trace = 32 := by
  have h00 : γ 0 * γ 0 = 1 := γ_mul_self 0
  rw [E0_sq]
  constructor
  · simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, ← Matrix.mul_kronecker_mul,
      Matrix.one_mul, h00, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_kronecker, γ_trace]
    simp
  · rw [double_grade_is_agreement, lastDirectionAgreement]
    simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, ← Matrix.mul_kronecker_mul, h00,
      Matrix.trace_add, Matrix.trace_smul, Matrix.trace_kronecker, γ_trace, trace_one_four]
    norm_num

/-- **`Λℓ² = 3`:** once the wedge is selected, the volume term `24/ℓ⁴` is `(4/ℓ²)·2Λ` exactly when
`Λℓ² = 3` (`WholePicture.lambda_three`; the cross coefficient is `WholePicture.curvature_identity`). -/
theorem lambda_ell_sq (ℓ : ℝ) (hℓ : ℓ ≠ 0) (Λ : ℝ) :
    (24 / ℓ ^ 4 = (4 / ℓ ^ 2) * (2 * Λ)) ↔ Λ * ℓ ^ 2 = 3 := by
  rw [WholePicture.lambda_three ℓ hℓ Λ]
  have h2 : ℓ ^ 2 ≠ 0 := pow_ne_zero 2 hℓ
  constructor
  · intro h
    rw [h]
    field_simp
  · intro h
    field_simp
    linarith

end Comparison.GroupsContinuumLaw
