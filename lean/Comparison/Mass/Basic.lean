module

public import Mathlib

/-!
# The road to the masses: the finite tools (Jacobi, the rank-one adjugate, the positive eigenvector)

* `hasDerivAt_det`: **Jacobi's formula for a differentiable family of matrices** over any
  nontrivially normed field: `(det M)' = tr(adj M · M')`.
* `adjugate_rank_one`: at a matrix `K` with `det K = 0` whose right and left kernels are spanned by
  `r` and `ℓ`, the adjugate is `κ r ℓᵀ` for one number `κ`.
* `norm_le_of_pos_eigen`: if `A ≥ 0` has a positive eigenvector `x` with eigenvalue `ρ`, every
  complex eigenvalue `μ` of `A` has `‖μ‖ ≤ ρ` (the positive eigenvector bounds the spectrum).
* `left_eigen_defect`: with a left eigenvector `y` of `A` for `ρ`, every trial pair `(λ, x)` has
  `(ρ − λ)(y·x) = y·((A − λ)x)`.
-/

@[expose] public section

namespace Comparison

open Matrix

section Jacobi

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem prod_updateCol' (M : Matrix ι ι 𝕜) (i : ι) (v : ι → 𝕜) (σ : Equiv.Perm ι) :
    ∏ j, (M.updateCol i v) (σ j) j = (∏ j ∈ Finset.univ.erase i, M (σ j) j) * v (σ i) := by
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  congr 1
  · refine Finset.prod_congr rfl fun j hj => ?_
    simp [updateCol_apply, Finset.ne_of_mem_erase hj]
  · rw [updateCol_self]

theorem trace_adjugate_mul_eq (M M' : Matrix ι ι 𝕜) :
    (M.adjugate * M').trace = ∑ i, (M.updateCol i (fun k => M' k i)).det := by
  rw [Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← cramer_apply, cramer_eq_adjugate_mulVec]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.diag]

/-- **Jacobi's formula** for a family of matrices differentiable at `x`:
`d/dy det M(y) = tr(adj M(x) · M'(x))`. -/
theorem hasDerivAt_det {M : 𝕜 → Matrix ι ι 𝕜} {M' : Matrix ι ι 𝕜} {x : 𝕜}
    (h : ∀ i j, HasDerivAt (fun y => M y i j) (M' i j) x) :
    HasDerivAt (fun y => (M y).det) ((M x).adjugate * M').trace x := by
  have key : ∀ σ : Equiv.Perm ι, HasDerivAt (fun y => ((Equiv.Perm.sign σ : ℤ) : 𝕜) *
      ∏ i, M y (σ i) i)
      (((Equiv.Perm.sign σ : ℤ) : 𝕜) *
        ∑ i, (∏ j ∈ Finset.univ.erase i, M x (σ j) j) * M' (σ i) i) x := by
    intro σ
    refine HasDerivAt.const_mul _ ?_
    have := HasDerivAt.fun_finsetProd (u := Finset.univ) (f := fun i y => M y (σ i) i)
      (f' := fun i => M' (σ i) i) (x := x) (fun i _ => h (σ i) i)
    simpa [smul_eq_mul] using this
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun σ _ => key σ)
  have e1 : (fun y => (M y).det) = fun y => ∑ σ : Equiv.Perm ι,
      ((Equiv.Perm.sign σ : ℤ) : 𝕜) * ∏ i, M y (σ i) i := by
    funext y
    rw [det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Units.smul_def, zsmul_eq_mul]
  rw [e1]
  convert hsum using 1
  rw [trace_adjugate_mul_eq]
  simp only [det_apply, Units.smul_def, zsmul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [prod_updateCol']

end Jacobi

section RankOne

variable {𝕜 : Type*} [Field 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The adjugate at a zero with one-dimensional kernels is of rank one:** `adj K = κ r ℓᵀ`. -/
theorem adjugate_rank_one (K : Matrix ι ι 𝕜) (r ℓ : ι → 𝕜) (hr : r ≠ 0) (hdet : K.det = 0)
    (hkerR : ∀ v, K *ᵥ v = 0 → ∃ c : 𝕜, v = c • r)
    (hkerL : ∀ w, w ᵥ* K = 0 → ∃ c : 𝕜, w = c • ℓ) :
    ∃ κ : 𝕜, K.adjugate = κ • vecMulVec r ℓ := by
  have hKA : K * K.adjugate = 0 := by rw [mul_adjugate, hdet, zero_smul]
  have hAK : K.adjugate * K = 0 := by rw [adjugate_mul, hdet, zero_smul]
  have hcol : ∀ j, ∃ c : 𝕜, (fun i => K.adjugate i j) = c • r := by
    intro j
    apply hkerR
    funext i
    have := congrFun (congrFun hKA i) j
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
  choose c hc using hcol
  have hM : K.adjugate = vecMulVec r c := by
    ext i j
    have := congrFun (hc j) i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [vecMulVec_apply, this, mul_comm]
  obtain ⟨i₀, hi₀⟩ : ∃ i, r i ≠ 0 := by
    by_contra hh
    push Not at hh
    exact hr (funext hh)
  have hcK : c ᵥ* K = 0 := by
    have := congrArg (fun X => X i₀) hAK
    simp only [hM] at this
    funext j
    have hj := congrFun this j
    simp only [Matrix.mul_apply, vecMulVec_apply, Matrix.zero_apply] at hj
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
    have h2 : r i₀ * ∑ x, c x * K x j = 0 := by
      rw [Finset.mul_sum]
      simpa [mul_assoc] using hj
    exact (mul_eq_zero.mp h2).resolve_left hi₀
  obtain ⟨κ, hκ⟩ := hkerL c hcK
  refine ⟨κ, ?_⟩
  rw [hM, hκ]
  ext i j
  simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
  ring

/-- The trace of a rank-one adjugate: `tr(κ r ℓᵀ C) = κ (ℓ · C r)`. -/
theorem trace_smul_vecMulVec_mul (κ : 𝕜) (r ℓ : ι → 𝕜) (C : Matrix ι ι 𝕜) :
    ((κ • vecMulVec r ℓ) * C).trace = κ * (ℓ ⬝ᵥ (C *ᵥ r)) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, vecMulVec_apply, dotProduct, Matrix.mulVec]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

end RankOne

section Positive

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- **A positive eigenvector bounds the spectrum:** if `A ≥ 0` entrywise and `A x = ρ x` with
`x > 0`, then every complex eigenvalue `μ` of `A` has `‖μ‖ ≤ ρ`. -/
theorem norm_le_of_pos_eigen (A : Matrix ι ι ℝ) (hA : ∀ i j, 0 ≤ A i j) (x : ι → ℝ)
    (hx : ∀ i, 0 < x i) (ρ : ℝ) (hρ : A *ᵥ x = ρ • x) (μ : ℂ) (y : ι → ℂ) (hy : y ≠ 0)
    (hμ : (A.map (fun a : ℝ => (a : ℂ))) *ᵥ y = μ • y) : ‖μ‖ ≤ ρ := by
  have hne : (Finset.univ : Finset ι).Nonempty := by
    obtain ⟨i, hi⟩ : ∃ i, y i ≠ 0 := by
      by_contra hh
      push Not at hh
      exact hy (funext hh)
    exact ⟨i, Finset.mem_univ i⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ (fun i => ‖y i‖ / x i) hne
  set m := ‖y i‖ / x i with hm
  have hyj : ∀ j, ‖y j‖ ≤ m * x j := by
    intro j
    have := hi j (Finset.mem_univ j)
    rw [div_le_iff₀ (hx j)] at this
    exact this
  have hm_pos : 0 < m := by
    obtain ⟨k, hk⟩ : ∃ k, y k ≠ 0 := by
      by_contra hh
      push Not at hh
      exact hy (funext hh)
    have h1 : 0 < ‖y k‖ / x k := div_pos (norm_pos_iff.mpr hk) (hx k)
    exact lt_of_lt_of_le h1 (hi k (Finset.mem_univ k))
  have hyi : ‖y i‖ = m * x i := by
    rw [hm]
    field_simp [(hx i).ne']
  have hrow : μ * y i = ∑ j, (A i j : ℂ) * y j := by
    have := congrFun hμ i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply, smul_eq_mul] at this
    exact this.symm
  have hbound : ‖μ‖ * ‖y i‖ ≤ ρ * ‖y i‖ := by
    calc ‖μ‖ * ‖y i‖ = ‖μ * y i‖ := (norm_mul _ _).symm
      _ = ‖∑ j, (A i j : ℂ) * y j‖ := by rw [hrow]
      _ ≤ ∑ j, ‖(A i j : ℂ) * y j‖ := norm_sum_le _ _
      _ = ∑ j, A i j * ‖y j‖ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hA i j)]
      _ ≤ ∑ j, A i j * (m * x j) := by
          refine Finset.sum_le_sum fun j _ => ?_
          exact mul_le_mul_of_nonneg_left (hyj j) (hA i j)
      _ = m * (A *ᵥ x) i := by
          simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ = ρ * ‖y i‖ := by
          rw [hρ, hyi]
          simp only [Pi.smul_apply, smul_eq_mul]
          ring
  have hyi_pos : 0 < ‖y i‖ := by
    rw [hyi]
    exact mul_pos hm_pos (hx i)
  exact le_of_mul_le_mul_right hbound hyi_pos

omit [DecidableEq ι] in
/-- **The defect identity:** if `yᵀA = ρ yᵀ`, then for every trial `(λ, x)`,
`(ρ − λ)(y·x) = y·((A − λ)x)`. -/
theorem left_eigen_defect (A : Matrix ι ι ℝ) (y x : ι → ℝ) (ρ lam : ℝ) (hy : y ᵥ* A = ρ • y) :
    (ρ - lam) * (y ⬝ᵥ x) = y ⬝ᵥ (A *ᵥ x - lam • x) := by
  rw [dotProduct_sub, dotProduct_mulVec, hy, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    smul_eq_mul]
  ring

end Positive

end Comparison

end
