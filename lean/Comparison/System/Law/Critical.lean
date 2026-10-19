import Comparison.System.Postulates
import Comparison.Mass.Taylor

/-!
# The proof system, the law: Proposition 59, the law near its critical step

The chart `ℝ⁵ ⊇ 𝟏^⊥ = ℝ⁴`, the five steps less their
mean `v_t = e_t − 𝟏/5` (`vR`, `Mass/Taylor.lean`), `(A_εψ)(x) = Σ_t ψ(x + εv_t)`.

* `vR_dot`, `vR_outer`: `v_a·v_b = δ_ab − 1/5`, `Σ_t v_t v_tᵀ = 1 − 𝟏𝟏ᵀ/5`, the identity on `𝟏^⊥`
  (`vR_outer_perp`).
* `stepSecond_eq`: the second derivative of `ψ` along the step `v_t` is `D²ψ(x)(v_t, v_t)`.
* `stepLaplacian_eq_frame`: **`Σ_t (v_t·∇)²ψ(x) = Σ_{i=1}^4 D²ψ(x)(f_i, f_i)` for every orthonormal basis
  `f₁, …, f₄` of `𝟏^⊥`**: the step Laplacian is the Laplacian of `ℝ⁴`; `helmert`: such a basis exists.
* `prop_59`: Proposition 59 as one statement.
-/

open Matrix Filter Topology Asymptotics Comparison

namespace Comparison.System

namespace Law

/-- `v_a·v_b = δ_ab − 1/5`. -/
theorem vR_dot (a b : Fin 5) : vR a ⬝ᵥ vR b = (if a = b then 1 else 0) - 1 / 5 := by
  fin_cases a <;> fin_cases b <;> simp [vR, dotProduct, Fin.sum_univ_five] <;> norm_num

/-- `Σ_t v_t v_tᵀ = 1 − 𝟏𝟏ᵀ/5`. -/
theorem vR_outer :
    ∑ t, vecMulVec (vR t) (vR t) = (1 : Matrix (Fin 5) (Fin 5) ℝ) - (1 / 5 : ℝ) • Matrix.of fun _ _ => 1 := by
  ext i j
  simp only [Matrix.sum_apply, vecMulVec_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
    Matrix.of_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp [vR, Fin.sum_univ_five] <;> norm_num

/-- **`Σ_t v_t v_tᵀ` is the identity on `𝟏^⊥`.** -/
theorem vR_outer_perp (v : Fin 5 → ℝ) (hv : ∑ i, v i = 0) :
    (∑ t, vecMulVec (vR t) (vR t)) *ᵥ v = v := by
  rw [vR_outer, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  have hJ : (Matrix.of fun _ _ : Fin 5 => (1 : ℝ)) *ᵥ v = 0 := by
    funext i
    simp [Matrix.mulVec, dotProduct, hv]
  rw [hJ, smul_zero, sub_zero]

/-- **The second derivative along a step:** `(d/dε)² ψ(x + εv)|₀ = D²ψ(x)(v, v)` for `ψ ∈ C²`. -/
theorem iteratedDeriv_two_line (ψ : (Fin 5 → ℝ) → ℝ) (hψ : ContDiff ℝ 2 ψ) (x v : Fin 5 → ℝ) :
    iteratedDeriv 2 (fun e : ℝ => ψ (x + e • v)) 0 = fderiv ℝ (fderiv ℝ ψ) x v v := by
  have hd : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have hd2 : Differentiable ℝ (fderiv ℝ ψ) :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have h1 : deriv (fun e : ℝ => ψ (x + e • v)) = fun e => fderiv ℝ ψ (x + e • v) v := by
    funext e
    have := (hd (x + e • v)).hasFDerivAt.comp_hasDerivAt e (line_hasDerivAt x v e)
    exact this.deriv
  have h2 : HasDerivAt (fun e : ℝ => fderiv ℝ ψ (x + e • v) v) (fderiv ℝ (fderiv ℝ ψ) x v v) 0 := by
    have hc : HasFDerivAt (fun y => fderiv ℝ ψ y v) ((fderiv ℝ (fderiv ℝ ψ) x).flip v) x := by
      have := (hd2 x).hasFDerivAt.clm_apply (hasFDerivAt_const v x)
      simpa using this
    have := hc.comp_hasDerivAt_of_eq (0 : ℝ) (line_hasDerivAt x v 0) (by simp)
    exact this
  rw [iteratedDeriv_succ, iteratedDeriv_one, h1]
  exact h2.deriv

/-- The second derivative along the step `v_t` is `D²ψ(x)(v_t, v_t)`. -/
theorem stepSecond_eq (ψ : (Fin 5 → ℝ) → ℝ) (hψ : ContDiff ℝ 2 ψ) (x : Fin 5 → ℝ) (t : Fin 5) :
    stepSecond ψ x t = fderiv ℝ (fderiv ℝ ψ) x (vR t) (vR t) :=
  iteratedDeriv_two_line ψ hψ x (vR t)

/-- A bilinear form summed on a family of vectors is its matrix contracted with their outer product. -/
theorem bilin_sum {ι : Type*} [Fintype ι] (B : (Fin 5 → ℝ) →L[ℝ] (Fin 5 → ℝ) →L[ℝ] ℝ)
    (w : ι → Fin 5 → ℝ) :
    ∑ i, B (w i) (w i) =
      ∑ a, ∑ b, (∑ i, w i a * w i b) * B (Pi.single a 1) (Pi.single b 1) := by
  have hv : ∀ v : Fin 5 → ℝ, v = ∑ a, v a • (Pi.single a 1 : Fin 5 → ℝ) := by
    intro v
    funext k
    simp [Finset.sum_apply, Pi.single_apply]
  have hB : ∀ v u : Fin 5 → ℝ,
      B v u = ∑ a, ∑ b, v a * u b * B (Pi.single a 1) (Pi.single b 1) := by
    intro v u
    have e1 : B v u = ∑ a, v a * B (Pi.single a 1) u := by
      conv_lhs => rw [hv v]
      rw [map_sum, ContinuousLinearMap.sum_apply]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [e1]
    refine Finset.sum_congr rfl fun a _ => ?_
    conv_lhs => rw [hv u]
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smul, smul_eq_mul]
    ring
  calc ∑ i, B (w i) (w i)
      = ∑ i, ∑ a, ∑ b, w i a * w i b * B (Pi.single a 1) (Pi.single b 1) :=
        Finset.sum_congr rfl fun i _ => hB (w i) (w i)
    _ = ∑ a, ∑ b, ∑ i, w i a * w i b * B (Pi.single a 1) (Pi.single b 1) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ a, ∑ b, (∑ i, w i a * w i b) * B (Pi.single a 1) (Pi.single b 1) := by
        simp only [Finset.sum_mul]

/-- The frame matrix: the rows `f₁, …, f₄` and `𝟏/√5`. -/
noncomputable def frameMat (f : Fin 4 → Fin 5 → ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  Matrix.of (Fin.snoc (α := fun _ => Fin 5 → ℝ) f (fun _ => 1 / Real.sqrt 5))

/-- An orthonormal basis of `𝟏^⊥` has `Σ_i f_i f_iᵀ = 1 − 𝟏𝟏ᵀ/5`. -/
theorem frame_outer (f : Fin 4 → Fin 5 → ℝ) (hon : ∀ i j, f i ⬝ᵥ f j = if i = j then 1 else 0)
    (hperp : ∀ i, ∑ a, f i a = 0) (a b : Fin 5) :
    ∑ i, f i a * f i b = (if a = b then 1 else 0) - 1 / 5 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs : Real.sqrt 5 ≠ 0 := by positivity
  have hrow : frameMat f * (frameMat f)ᵀ = 1 := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, frameMat, Matrix.of_apply, Matrix.one_apply]
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [Fin.snoc_last, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        ↓reduceIte]
      field_simp
      rw [h5]
      norm_num
    · simp only [Fin.snoc_last, Fin.snoc_castSucc, Fin.castSucc_ne_last, ↓reduceIte]
      rw [← Finset.mul_sum, hperp j, mul_zero]
      exact (if_neg (Fin.castSucc_ne_last j).symm).symm
    · simp only [Fin.snoc_last, Fin.snoc_castSucc]
      rw [← Finset.sum_mul, hperp i, zero_mul]
      exact (if_neg (Fin.castSucc_ne_last i)).symm
    · simp only [Fin.snoc_castSucc]
      have := hon i j
      rw [dotProduct] at this
      rw [this]
      simp [Fin.castSucc_inj]
  have hcol : (frameMat f)ᵀ * frameMat f = 1 := mul_eq_one_comm.mp hrow
  have h := congrFun (congrFun hcol a) b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, frameMat, Matrix.of_apply,
    Matrix.one_apply] at h
  rw [Fin.sum_univ_castSucc] at h
  simp only [Fin.snoc_castSucc, Fin.snoc_last] at h
  have e : 1 / Real.sqrt 5 * (1 / Real.sqrt 5) = 1 / 5 := by
    rw [div_mul_div_comm, one_mul, ← sq, h5]
  rw [e] at h
  linarith

/-- **The step Laplacian is the Laplacian of `𝟏^⊥ = ℝ⁴`:** for `ψ ∈ C²` and every orthonormal basis
`f₁, …, f₄` of `𝟏^⊥`, `Σ_t (v_t·∇)²ψ(x) = Σ_i D²ψ(x)(f_i, f_i)`. -/
theorem stepLaplacian_eq_frame (ψ : (Fin 5 → ℝ) → ℝ) (hψ : ContDiff ℝ 2 ψ) (x : Fin 5 → ℝ)
    (f : Fin 4 → Fin 5 → ℝ) (hon : ∀ i j, f i ⬝ᵥ f j = if i = j then 1 else 0)
    (hperp : ∀ i, ∑ a, f i a = 0) :
    stepLaplacian ψ x = ∑ i, fderiv ℝ (fderiv ℝ ψ) x (f i) (f i) := by
  rw [stepLaplacian]
  simp only [stepSecond_eq ψ hψ x]
  rw [bilin_sum, bilin_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  rw [frame_outer f hon hperp a b]
  have := congrFun (congrFun vR_outer a) b
  simp only [Matrix.sum_apply, vecMulVec_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_one] at this
  rw [this]

/-- The Helmert vectors of `𝟏^⊥`, before normalization. -/
def hU : Fin 4 → Fin 5 → ℝ :=
  ![![1, -1, 0, 0, 0], ![1, 1, -2, 0, 0], ![1, 1, 1, -3, 0], ![1, 1, 1, 1, -4]]

/-- Their squared lengths. -/
def hN : Fin 4 → ℝ := ![2, 6, 12, 20]

/-- The Helmert basis of `𝟏^⊥`. -/
noncomputable def helmert (i : Fin 4) (a : Fin 5) : ℝ := hU i a / Real.sqrt (hN i)

theorem hU_dot (i j : Fin 4) : hU i ⬝ᵥ hU j = if i = j then hN i else 0 := by
  fin_cases i <;> fin_cases j <;> simp [hU, hN, dotProduct, Fin.sum_univ_five] <;> norm_num

theorem hN_pos (i : Fin 4) : 0 < hN i := by
  fin_cases i <;> simp [hN]

theorem hU_sum (i : Fin 4) : ∑ a, hU i a = 0 := by
  fin_cases i <;> simp [hU, Fin.sum_univ_five] <;> norm_num

/-- **`𝟏^⊥` has an orthonormal basis**, the Helmert basis. -/
theorem helmert_orthonormal :
    (∀ i j, helmert i ⬝ᵥ helmert j = if i = j then 1 else 0) ∧ ∀ i, ∑ a, helmert i a = 0 := by
  refine ⟨fun i j => ?_, fun i => ?_⟩
  · have e : helmert i ⬝ᵥ helmert j = (hU i ⬝ᵥ hU j) / (Real.sqrt (hN i) * Real.sqrt (hN j)) := by
      simp only [helmert, dotProduct, div_mul_div_comm, Finset.sum_div]
    rw [e, hU_dot]
    split_ifs with h
    · subst h
      rw [Real.mul_self_sqrt (hN_pos i).le, div_self (hN_pos i).ne']
    · simp
  · simp only [helmert, ← Finset.sum_div, hU_sum, zero_div]

end Law

open Comparison.System.Law

/-- **Proposition 59, the law near its critical step.** `v_t = e_t − 𝟏/5`: `Σ_t v_t = 0`,
`v_a·v_b = δ_ab − 1/5`, `Σ_t v_t ⊗ v_t = 1 − 𝟏𝟏ᵀ/5`, the identity on `𝟏^⊥ = ℝ⁴`; for every `ψ ∈ C³` and
every `x`, at `u = 1/4 − ε²m²/24`, `(1 + 4u²)ψ(x) − u Σ_t ψ(x + εv_t) = (ε²/8)(m²ψ(x) − Δψ(x)) + O(ε³)`;
and `Δψ(x) = Σ_t (v_t·∇)²ψ(x)` is the Laplacian of `𝟏^⊥ = ℝ⁴`: `Σ_i D²ψ(x)(f_i, f_i)` for every orthonormal
basis `f` of `𝟏^⊥` (one exists). -/
theorem prop_59 :
    ∑ t, vR t = 0 ∧
    (∀ a b, vR a ⬝ᵥ vR b = (if a = b then 1 else 0) - 1 / 5) ∧
    ∑ t, vecMulVec (vR t) (vR t) = (1 : Matrix (Fin 5) (Fin 5) ℝ) - (1 / 5 : ℝ) • (Matrix.of fun _ _ => 1) ∧
    (∀ v : Fin 5 → ℝ, ∑ i, v i = 0 → (∑ t, vecMulVec (vR t) (vR t)) *ᵥ v = v) ∧
    (∀ (ψ : (Fin 5 → ℝ) → ℝ), ContDiff ℝ 3 ψ → ∀ (x : Fin 5 → ℝ) (m : ℝ),
      (fun ε : ℝ => (1 + 4 * (1 / 4 - ε ^ 2 * m ^ 2 / 24) ^ 2) * ψ x -
        (1 / 4 - ε ^ 2 * m ^ 2 / 24) * ∑ t, ψ (x + ε • vR t) -
        ε ^ 2 / 8 * (m ^ 2 * ψ x - stepLaplacian ψ x)) =O[𝓝 0] (fun ε : ℝ => ε ^ 3)) ∧
    (∀ (ψ : (Fin 5 → ℝ) → ℝ), ContDiff ℝ 2 ψ → ∀ (x : Fin 5 → ℝ) (f : Fin 4 → Fin 5 → ℝ),
      (∀ i j, f i ⬝ᵥ f j = if i = j then 1 else 0) → (∀ i, ∑ a, f i a = 0) →
      stepLaplacian ψ x = ∑ i, fderiv ℝ (fderiv ℝ ψ) x (f i) (f i)) ∧
    ∃ f : Fin 4 → Fin 5 → ℝ, (∀ i j, f i ⬝ᵥ f j = if i = j then 1 else 0) ∧ ∀ i, ∑ a, f i a = 0 :=
  ⟨vR_sum, vR_dot, vR_outer, vR_outer_perp, fun ψ hψ x m => critical_operator ψ hψ x m,
    fun ψ hψ x f hon hperp => stepLaplacian_eq_frame ψ hψ x f hon hperp,
    ⟨helmert, helmert_orthonormal⟩⟩

end Comparison.System
