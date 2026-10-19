module

public import Comparison.Mass.Simple

/-!
# The road to the masses: the shift of the law's zero under a source (Proposition 57)

With a source `J K_a` added to the law,
`K(J, u) = 1 − uB − J K_a` on the eighty states, any real matrix `K_a`:

* `zero_shift_law`: **the zero `ζ(J)` of `det K(J, ·)` through `ζ(0) = 1/4` exists near `J = 0` and
  `dζ/dJ = −(𝟏 · K_a 𝟏)/320 = −ℓ S_a r/(ℓ S_ζ r)`** with `r = ℓ = 𝟏`, `S_a = ∂_J K = −K_a` and
  `S_ζ = ∂_u K = −B` (`𝟏 · B𝟏 = 320`): Proposition 57's shift, from the determinant, with the
  simple zero a theorem (`law_deriv_quarter`, `adj_law_quarter`), by the implicit function theorem.
-/

@[expose] public section

namespace Comparison

open Matrix Filter Topology

/-- The law with a source. -/
noncomputable def lawSrc (Ka : Matrix State State ℝ) (J u : ℝ) : ℝ :=
  (1 - u • stepR - J • Ka).det

/-- Its `J`-derivative. -/
noncomputable def lawSrcJ (Ka : Matrix State State ℝ) (J u : ℝ) : ℝ :=
  ((1 - u • stepR - J • Ka).adjugate * (-Ka)).trace

/-- Its `u`-derivative. -/
noncomputable def lawSrcU (Ka : Matrix State State ℝ) (J u : ℝ) : ℝ :=
  ((1 - u • stepR - J • Ka).adjugate * (-stepR)).trace

theorem lawSrc_hasDerivAt_J (Ka : Matrix State State ℝ) (J u : ℝ) :
    HasDerivAt (fun J => lawSrc Ka J u) (lawSrcJ Ka J u) J := by
  apply hasDerivAt_det
  intro i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply]
  simpa using ((hasDerivAt_id J).mul_const (Ka i j)).const_sub
    ((1 : Matrix State State ℝ) i j - u * stepR i j)

theorem lawSrc_hasDerivAt_u (Ka : Matrix State State ℝ) (J u : ℝ) :
    HasDerivAt (fun u => lawSrc Ka J u) (lawSrcU Ka J u) u := by
  apply hasDerivAt_det
  intro i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply]
  exact ((hasDerivAt_mul_const (stepR i j)).const_sub
    ((1 : Matrix State State ℝ) i j)).sub_const (J * Ka i j)

theorem lawSrc_mat_continuous (Ka : Matrix State State ℝ) :
    Continuous (fun p : ℝ × ℝ => (1 - p.2 • stepR - p.1 • Ka).adjugate) := by
  apply Continuous.matrix_adjugate
  exact (continuous_const.sub (continuous_snd.smul continuous_const)).sub
    (continuous_fst.smul continuous_const)

/-- **Proposition 57, the shift of the zero under a source:** `dζ/dJ = −(𝟏 · K_a 𝟏)/320`. -/
theorem zero_shift_law (Ka : Matrix State State ℝ) :
    ∃ ζ : ℝ → ℝ, ζ 0 = 1 / 4 ∧ (∀ᶠ J in 𝓝 0, lawSrc Ka J (ζ J) = 0) ∧
      HasDerivAt ζ (-((1 : State → ℝ) ⬝ᵥ (Ka *ᵥ 1)) / 320) 0 := by
  have hadj : (1 - (1 / 4 : ℝ) • stepR - (0 : ℝ) • Ka).adjugate =
      kappaLaw • vecMulVec (1 : State → ℝ) 1 := by
    rw [zero_smul, sub_zero]
    exact adj_law_quarter
  have hU : lawSrcU Ka 0 (1 / 4) = -(320 * kappaLaw) := by
    rw [lawSrcU, hadj, trace_smul_vecMulVec_mul, Matrix.neg_mulVec, dotProduct_neg,
      one_dot_stepR_one]
    ring
  have hJ : lawSrcJ Ka 0 (1 / 4) = -(kappaLaw * ((1 : State → ℝ) ⬝ᵥ (Ka *ᵥ 1))) := by
    rw [lawSrcJ, hadj, trace_smul_vecMulVec_mul, Matrix.neg_mulVec, dotProduct_neg]
    ring
  have hκ : kappaLaw ≠ 0 := kappaLaw_pos.ne'
  have hU0 : lawSrcU Ka 0 (1 / 4) ≠ 0 := by
    rw [hU]
    exact neg_ne_zero.mpr (mul_ne_zero (by norm_num) hκ)
  have df₁ : ∀ᶠ w in 𝓝 ((0 : ℝ), (1 / 4 : ℝ)), HasFDerivAt (lawSrc Ka · w.2)
      ((fun J u => ContinuousLinearMap.toSpanSingleton ℝ (lawSrcJ Ka J u)) w.1 w.2) w.1 :=
    Filter.Eventually.of_forall fun w => (lawSrc_hasDerivAt_J Ka w.1 w.2).hasFDerivAt
  have df₂ : ∀ᶠ w in 𝓝 ((0 : ℝ), (1 / 4 : ℝ)), HasFDerivAt (lawSrc Ka w.1 ·)
      ((fun J u => ContinuousLinearMap.toSpanSingleton ℝ (lawSrcU Ka J u)) w.1 w.2) w.2 :=
    Filter.Eventually.of_forall fun w => (lawSrc_hasDerivAt_u Ka w.1 w.2).hasFDerivAt
  have cJ : Continuous (fun p : ℝ × ℝ => lawSrcJ Ka p.1 p.2) :=
    ((lawSrc_mat_continuous Ka).mul continuous_const).matrix_trace
  have cU : Continuous (fun p : ℝ × ℝ => lawSrcU Ka p.1 p.2) :=
    ((lawSrc_mat_continuous Ka).mul continuous_const).matrix_trace
  have cf₁ : ContinuousAt
      (Function.uncurry fun J u => ContinuousLinearMap.toSpanSingleton ℝ (lawSrcJ Ka J u))
      ((0 : ℝ), (1 / 4 : ℝ)) :=
    ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp cJ).continuousAt
  have cf₂ : ContinuousAt
      (Function.uncurry fun J u => ContinuousLinearMap.toSpanSingleton ℝ (lawSrcU Ka J u))
      ((0 : ℝ), (1 / 4 : ℝ)) :=
    ((ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).continuous.comp cU).continuousAt
  have if₂u : ((fun J u => ContinuousLinearMap.toSpanSingleton ℝ (lawSrcU Ka J u))
      ((0 : ℝ), (1 / 4 : ℝ)).1 ((0 : ℝ), (1 / 4 : ℝ)).2).IsInvertible := by
    have hU0' : lawSrcU Ka 0 4⁻¹ ≠ 0 := by rwa [one_div] at hU0
    refine ContinuousLinearMap.IsInvertible.of_inverse
      (g := ContinuousLinearMap.toSpanSingleton ℝ (lawSrcU Ka 0 (1 / 4))⁻¹) ?_ ?_
    · ext
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
        smul_eq_mul, one_mul, ContinuousLinearMap.id_apply, one_div]
      exact inv_mul_cancel₀ hU0'
    · ext
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
        smul_eq_mul, one_mul, ContinuousLinearMap.id_apply, one_div]
      exact mul_inv_cancel₀ hU0'

  set ζ := implicitFunctionOfBivariate (u := ((0 : ℝ), (1 / 4 : ℝ))) (f := lawSrc Ka)
    (f₁ := fun J u => ContinuousLinearMap.toSpanSingleton ℝ (lawSrcJ Ka J u))
    (f₂ := fun J u => ContinuousLinearMap.toSpanSingleton ℝ (lawSrcU Ka J u))
    df₁ df₂ cf₁ cf₂ if₂u with hζ
  have hζ0 : ζ 0 = 1 / 4 := by
    have := (eventually_apply_eq_iff_implicitFunctionOfBivariate (u := ((0 : ℝ), (1 / 4 : ℝ)))
      (f := lawSrc Ka)
      (f₁ := fun J u => ContinuousLinearMap.toSpanSingleton ℝ (lawSrcJ Ka J u))
      (f₂ := fun J u => ContinuousLinearMap.toSpanSingleton ℝ (lawSrcU Ka J u))
      df₁ df₂ cf₁ cf₂ if₂u).self_of_nhds
    exact this.mp rfl
  have hzero : ∀ᶠ J in 𝓝 (0 : ℝ), lawSrc Ka J (ζ J) = 0 := by
    have := eventually_apply_implicitFunctionOfBivariate (u := ((0 : ℝ), (1 / 4 : ℝ)))
      (f := lawSrc Ka)
      (f₁ := fun J u => ContinuousLinearMap.toSpanSingleton ℝ (lawSrcJ Ka J u))
      (f₂ := fun J u => ContinuousLinearMap.toSpanSingleton ℝ (lawSrcU Ka J u))
      df₁ df₂ cf₁ cf₂ if₂u
    have h0 : lawSrc Ka 0 (1 / 4) = 0 := by
      rw [lawSrc, zero_smul, sub_zero]
      exact det_law_quarter
    filter_upwards [this] with J hJ'
    rw [hJ']
    exact h0
  have hderiv := (hasStrictFDerivAt_implicitFunctionOfBivariate (u := ((0 : ℝ), (1 / 4 : ℝ)))
    (f := lawSrc Ka)
    (f₁ := fun J u => ContinuousLinearMap.toSpanSingleton ℝ (lawSrcJ Ka J u))
    (f₂ := fun J u => ContinuousLinearMap.toSpanSingleton ℝ (lawSrcU Ka J u))
    df₁ df₂ cf₁ cf₂ if₂u).hasFDerivAt
  refine ⟨ζ, hζ0, hzero, ?_⟩
  have h1 := hderiv.hasDerivAt
  convert h1 using 1
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, one_smul]
  have hinv : (ContinuousLinearMap.toSpanSingleton ℝ (lawSrcU Ka 0 (1 / 4))).inverse
      (lawSrcJ Ka 0 (1 / 4)) = lawSrcJ Ka 0 (1 / 4) / lawSrcU Ka 0 (1 / 4) := by
    rw [if₂u.inverse_apply_eq]
    simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
    field_simp
  rw [hinv, hJ, hU]
  field_simp

/-- The shift in the book's form: `−(𝟏 · K_a 𝟏)/320 = −ℓ S_a r/(ℓ S_ζ r)` with `S_a = −K_a`,
`S_ζ = −B`. -/
theorem zero_shift_form (Ka : Matrix State State ℝ) :
    -((1 : State → ℝ) ⬝ᵥ (Ka *ᵥ 1)) / 320 =
      -((1 : State → ℝ) ⬝ᵥ ((-Ka) *ᵥ 1)) / ((1 : State → ℝ) ⬝ᵥ ((-stepR) *ᵥ 1)) := by
  rw [Matrix.neg_mulVec, Matrix.neg_mulVec, dotProduct_neg, dotProduct_neg, one_dot_stepR_one]
  ring

end Comparison

end
