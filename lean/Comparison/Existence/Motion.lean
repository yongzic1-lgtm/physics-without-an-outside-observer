module

public import Comparison.Existence.Table
public import Comparison.Existence.Coin
public import Comparison.Elements.Overlap

/-!
# Book XI. The local form: the critical step and one step in motion (Propositions 59, 60)

**Prop. 59.**
* `vline t = e_t − 𝟙/5`: `vline_sum` `Σ_t v_t = 0`; `vline_dot` `v_a·v_b = δ_ab − 1/5`;
  `vline_outer` `Σ_t v_t v_tᵀ = 1 − 𝟙𝟙ᵀ/5`; `coin_vline`: the coin reverses every `v_t`
  (it keeps `𝟙` and reverses `𝟙^⊥`).
* `critical_expansion`: at `u = 1/4 − δ`, `δ = ε²m²/24`, exactly
  `(1 + 4u²) − u(5 + (ε²/2)Δ) = (ε²/8)(m² − Δ) + 4δ² + (δε²/2)Δ`, the remainder of order `ε⁴`;
  `critical_vertex`: `(1 + 4u²) − 5u = (1 − u)(1 − 4u)`.

**Prop. 60.**
* `stepMotion k μ j h = e^{−ikγ_j} e^{−iμγ_h}`; `stepMotion_add_adjoint`: `U + U† = 2 cos k cos μ`
  for `j ≠ h`; `stepMotion_unitary`: `U U† = 1`; `eigen_phase`: every eigenvalue `λ` of `U` has
  `|λ| = 1` and `Re λ = cos k cos μ`: `cos ω = cos μ cos k`; `stepMotion_rest`: at `k = 0` the step
  is the clock's rotation `e^{−iμγ_h}`.
* `chart_square`: for five lines `Γ_μ = γ(O_μ)` from any orthogonal `O`,
  `(Σ_μ x_μ Γ_μ)² = (Σ_μ x_μ²)·1`; `dirac_square`: `(Σ_{μ<4} p_μ Γ_μ + iM Γ₄)² = (Σ p_μ² − M²)·1`.
-/

@[expose] public section

namespace Comparison

open Matrix hiding J
open Complex

/-! ## Prop. 59 -/

/-- The five steps less their mean: `v_t = e_t − 𝟙/5`. -/
def vline (t : Fin 5) : Fin 5 → ℚ := fun s => (if s = t then 1 else 0) - 1 / 5

theorem vline_sum : ∑ t, vline t = 0 := by
  funext s
  simp only [vline, Finset.sum_apply, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Pi.zero_apply]
  norm_num

theorem vline_dot (a b : Fin 5) :
    ∑ s, vline a s * vline b s = (if a = b then 1 else 0) - 1 / 5 := by
  fin_cases a <;> fin_cases b <;> simp [vline, Fin.sum_univ_five] <;> norm_num

theorem vline_outer :
    ∑ t, (Matrix.of fun i j => vline t i * vline t j) =
      (1 : Matrix (Fin 5) (Fin 5) ℚ) - (1 / 5 : ℚ) • ones5 := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.of_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.smul_apply, ones5, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [vline, Fin.sum_univ_five] <;> norm_num

/-- **The coin reverses every step less the mean:** `σ v_t = −v_t`. -/
theorem coin_vline (t : Fin 5) : coin *ᵥ vline t = -vline t := by
  funext s
  simp only [Matrix.mulVec, dotProduct, coin_apply, vline, Pi.neg_apply]
  fin_cases t <;> fin_cases s <;> simp [Fin.sum_univ_five] <;> norm_num

/-- `(1 + 4u²) − 5u = (1 − u)(1 − 4u)`. -/
theorem critical_vertex (u : ℝ) : (1 + 4 * u ^ 2) - 5 * u = (1 - u) * (1 - 4 * u) := by ring

/-- **The law near its critical step:** at `u = 1/4 − ε²m²/24`,
`(1 + 4u²) − u(5 + (ε²/2)Δ) = (ε²/8)(m² − Δ) + 4δ² + (δε²/2)Δ` with `δ = ε²m²/24`. -/
theorem critical_expansion (ε m Δ : ℝ) :
    let δ := ε ^ 2 * m ^ 2 / 24
    let u := 1 / 4 - δ
    (1 + 4 * u ^ 2) - u * (5 + ε ^ 2 / 2 * Δ) =
      ε ^ 2 / 8 * (m ^ 2 - Δ) + (4 * δ ^ 2 + δ * ε ^ 2 / 2 * Δ) := by
  intro δ u
  simp only [u, δ]
  ring

/-! ## Prop. 60 -/

/-- **One step in motion:** `U = e^{−ikγ_j} e^{−iμγ_h}`. -/
noncomputable def stepMotion (k μ : ℝ) (j h : Fin 5) : Matrix Four Four ℂ :=
  expIγ (-k) j * expIγ (-μ) h

theorem expIγ_conjTranspose (a : ℝ) (h : Fin 5) : (expIγ a h)ᴴ = expIγ (-a) h := by
  have h1 : star ((Real.cos a : ℝ) : ℂ) = ((Real.cos (-a) : ℝ) : ℂ) := by
    rw [Real.cos_neg]
    exact Complex.conj_ofReal _
  have h2 : star (I * ((Real.sin a : ℝ) : ℂ)) = I * ((Real.sin (-a) : ℝ) : ℂ) := by
    rw [Real.sin_neg, star_mul', Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  rw [expIγ, expIγ, Matrix.conjTranspose_add, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_smul, Matrix.conjTranspose_one, γ_conjTranspose, h1, h2]

theorem stepMotion_unitary (k μ : ℝ) (j h : Fin 5) :
    stepMotion k μ j h * (stepMotion k μ j h)ᴴ = 1 := by
  rw [stepMotion, Matrix.conjTranspose_mul, expIγ_conjTranspose, expIγ_conjTranspose,
    show expIγ (-k) j * expIγ (-μ) h * (expIγ (- -μ) h * expIγ (- -k) j) =
      expIγ (-k) j * (expIγ (-μ) h * expIγ (- -μ) h) * expIγ (- -k) j by
        simp only [Matrix.mul_assoc],
    expIγ_unitary, Matrix.mul_one, expIγ_unitary]

/-- **`U + U† = 2 cos k cos μ`** for a step along `j ≠ h`. -/
theorem stepMotion_add_adjoint (k μ : ℝ) {j h : Fin 5} (hjh : j ≠ h) :
    stepMotion k μ j h + (stepMotion k μ j h)ᴴ =
      ((2 * Real.cos k * Real.cos μ : ℝ) : ℂ) • (1 : Matrix Four Four ℂ) := by
  have hI : ∀ x y : ℂ, I * x * (I * y) = -(x * y) := by
    intro x y
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [stepMotion, Matrix.conjTranspose_mul, expIγ_conjTranspose, expIγ_conjTranspose]
  simp only [neg_neg, expIγ, Real.cos_neg, Real.sin_neg, add_mul, mul_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul, hI]
  have hanti : γ h * γ j = -(γ j * γ h) := γ_anticomm (Ne.symm hjh)
  rw [hanti]
  push_cast
  module

theorem stepMotion_rest (μ : ℝ) (j h : Fin 5) : stepMotion 0 μ j h = expIγ (-μ) h := by
  simp [stepMotion, expIγ]

open scoped ComplexOrder in
/-- **Every eigenphase obeys `cos ω = cos μ cos k`:** an eigenvalue `λ` of the step has
`|λ| = 1` and `Re λ = cos k cos μ`. -/
theorem eigen_phase (k μ : ℝ) {j h : Fin 5} (hjh : j ≠ h) (v : Four → ℂ) (hv : v ≠ 0) (lam : ℂ)
    (hlam : stepMotion k μ j h *ᵥ v = lam • v) :
    lam.re = Real.cos k * Real.cos μ ∧ Complex.normSq lam = 1 := by
  set U := stepMotion k μ j h
  have hvv : star v ⬝ᵥ v ≠ 0 := by
    intro h0
    exact hv (dotProduct_star_self_eq_zero.mp h0)
  -- ⟨v, U† v⟩ = conj λ ⟨v, v⟩
  have hadj : star v ⬝ᵥ (Uᴴ *ᵥ v) = star lam * (star v ⬝ᵥ v) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, hlam, star_smul, smul_dotProduct,
      smul_eq_mul]
  have hsum := congrArg (fun M => star v ⬝ᵥ (M *ᵥ v)) (stepMotion_add_adjoint k μ hjh)
  simp only [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, smul_eq_mul] at hsum
  rw [hlam, dotProduct_smul, smul_eq_mul, hadj] at hsum
  have hsum' : (lam + star lam) * (star v ⬝ᵥ v) =
      ((2 * Real.cos k * Real.cos μ : ℝ) : ℂ) * (star v ⬝ᵥ v) := by
    rw [add_mul]
    exact hsum
  have hre : lam + star lam = ((2 * Real.cos k * Real.cos μ : ℝ) : ℂ) :=
    (mul_left_inj' hvv).mp hsum'
  constructor
  · have := congrArg Complex.re hre
    simp only [Complex.add_re, Complex.star_def, Complex.conj_re, Complex.ofReal_re] at this
    linarith
  · -- unitarity: |λ|² ⟨v,v⟩ = ⟨Uv, Uv⟩ = ⟨v, v⟩
    have hU : Uᴴ * U = 1 := mul_eq_one_comm.mp (stepMotion_unitary k μ j h)
    have h1 : star (U *ᵥ v) ⬝ᵥ (U *ᵥ v) = star v ⬝ᵥ v := by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hU,
        Matrix.one_mulVec]
    rw [hlam, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
      ← mul_assoc] at h1
    have h1' : (star lam * lam) * (star v ⬝ᵥ v) = 1 * (star v ⬝ᵥ v) := by
      rw [one_mul]
      exact h1
    have h2 : star lam * lam = 1 := (mul_left_inj' hvv).mp h1'
    have h3 : ((Complex.normSq lam : ℝ) : ℂ) = 1 := by
      rw [Complex.normSq_eq_conj_mul_self]
      exact h2
    exact_mod_cast h3

/-- **Five lines in the chart:** for `Γ_μ = γ(O_μ)` with `O` orthogonal,
`(Σ_μ x_μ Γ_μ)² = (Σ_μ x_μ²)·1`. -/
theorem chart_square (O : Matrix (Fin 5) (Fin 5) ℝ) (hO : O * Oᵀ = 1) (x : Fin 5 → ℂ) :
    (∑ μ, x μ • γv (O μ)) * (∑ μ, x μ • γv (O μ)) = (∑ μ, x μ ^ 2) • (1 : Matrix Four Four ℂ) := by
  have e : ∑ μ, x μ • γv (O μ) = ∑ s, (∑ μ, x μ * (O μ s : ℂ)) • γ s := by
    simp only [γv, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_smul]
  rw [e, sq_sum]
  congr 1
  have hO' : ∀ μ ν, ∑ s, (O μ s : ℂ) * (O ν s : ℂ) = if μ = ν then 1 else 0 := by
    intro μ ν
    have := congrFun (congrFun hO μ) ν
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at this
    have h' : ((∑ s, O μ s * O ν s : ℝ) : ℂ) = ((if μ = ν then 1 else 0 : ℝ) : ℂ) := by
      rw [this]
    push_cast at h'
    rw [h']
    split_ifs <;> simp
  calc ∑ s, (∑ μ, x μ * (O μ s : ℂ)) ^ 2
      = ∑ s, ∑ μ, ∑ ν, x μ * x ν * ((O μ s : ℂ) * (O ν s : ℂ)) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [sq, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
        ring
    _ = ∑ μ, ∑ ν, x μ * x ν * ∑ s, (O μ s : ℂ) * (O ν s : ℂ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun μ _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ μ, x μ ^ 2 := by
        simp only [hO', mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
          ↓reduceIte]
        refine Finset.sum_congr rfl fun μ _ => ?_
        ring

/-- **Dirac's square in the chart:** `(Σ_{μ<4} p_μ Γ_μ + iM Γ₄)² = (Σ_{μ<4} p_μ² − M²)·1`. -/
theorem dirac_square (O : Matrix (Fin 5) (Fin 5) ℝ) (hO : O * Oᵀ = 1) (p : Fin 4 → ℝ) (M : ℝ) :
    (∑ μ : Fin 4, (p μ : ℂ) • γv (O μ.castSucc) + (I * M) • γv (O (Fin.last 4))) *
      (∑ μ : Fin 4, (p μ : ℂ) • γv (O μ.castSucc) + (I * M) • γv (O (Fin.last 4))) =
      ((∑ μ, p μ ^ 2 - M ^ 2 : ℝ) : ℂ) • (1 : Matrix Four Four ℂ) := by
  let x : Fin 5 → ℂ := Fin.snoc (α := fun _ => ℂ) (fun μ : Fin 4 => (p μ : ℂ)) (I * M)
  have hL : ∑ μ, x μ • γv (O μ) =
      ∑ μ : Fin 4, (p μ : ℂ) • γv (O μ.castSucc) + (I * M) • γv (O (Fin.last 4)) := by
    rw [Fin.sum_univ_castSucc]
    simp only [x, Fin.snoc_castSucc, Fin.snoc_last]
  have hR : ∑ μ, x μ ^ 2 = ((∑ μ, p μ ^ 2 - M ^ 2 : ℝ) : ℂ) := by
    rw [Fin.sum_univ_castSucc]
    simp only [x, Fin.snoc_castSucc, Fin.snoc_last]
    push_cast
    rw [mul_pow, Complex.I_sq]
    ring
  rw [← hL, chart_square O hO x, hR]

end Comparison

end
