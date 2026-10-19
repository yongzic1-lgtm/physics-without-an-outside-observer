import Comparison.Article.Geometry3

/-!
# The operators of the last-step direction's side (Proposition 99's `1, K₁, K₂, K₃`; Proposition S99 of the public
edition; Proposition 164's side `Q(h)H`)

With the last-step direction `h = 0` and `Π = (1 + γ_h)/2` the projection on the side `Q(h)H`:

* `sideP_apply`, `side_entries`: an operator `X` of the side (`ΠXΠ = X`) has entries that depend only on the second
  factor, `X_{(i,j),(k,l)} = Z_{jl}`;
* `K_side`: `K_c Π = (−i/2)(𝟙𝟙ᵀ) ⊗ σ_{c−1}` for `K_c = γ_kγ_c`, `k = 1`, `c = 2, 3, 4`;
* `side_span` (**Proposition 99**): **every operator of the side is `aΠ + b₁K₁Π + b₂K₂Π + b₃K₃Π`**, so `1, K₁, K₂,
  K₃` span the operators of `Q(h)H`; `K_on_side`: each `K_c` keeps the side.
-/

namespace Comparison.Article

open Matrix hiding J
open Complex Kronecker

/-- The projection on the last-step direction's side, `Π = (1 + γ_h)/2`, `h = 0`. -/
noncomputable def sideP : Matrix Four Four ℂ := (1 / 2 : ℂ) • (1 + γ 0)

theorem sideP_apply (i j m n : Fin 2) : sideP (i, j) (m, n) = if j = n then 1 / 2 else 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases m <;> fin_cases n <;>
    simp [sideP, γ, σ₁, Matrix.one_apply, Matrix.kroneckerMap_apply]

/-- **An operator of the side depends only on the second factor.** -/
theorem side_entries (X : Matrix Four Four ℂ) (hX : sideP * X * sideP = X) (i j k l : Fin 2) :
    X (i, j) (k, l) = X (0, j) (0, l) := by
  have h1 := congrFun (congrFun hX (i, j)) (k, l)
  have h2 := congrFun (congrFun hX (0, j)) (0, l)
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, sideP_apply] at h1 h2
  rw [← h1, ← h2]

/-- `𝟙𝟙ᵀ/2` on the first factor. -/
noncomputable def halfOnes : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 2, 1 / 2; 1 / 2, 1 / 2]

theorem sideP_kron : sideP = halfOnes ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  four_ext <;> simp [sideP, halfOnes, γ, σ₁, Matrix.one_apply, Matrix.kroneckerMap_apply]

/-- **`K_c Π = (−i)(𝟙𝟙ᵀ/2) ⊗ σ_{c−1}`.** -/
theorem K_side :
    Kturn 2 * sideP = (-I) • (halfOnes ⊗ₖ σ₁) ∧ Kturn 3 * sideP = (-I) • (halfOnes ⊗ₖ σ₂) ∧
      Kturn 4 * sideP = (-I) • (halfOnes ⊗ₖ σ₃) := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · rw [sideP_kron]
    four_ext <;>
      simp [Kturn, γ, σ₁, σ₂, σ₃, halfOnes, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        Matrix.kroneckerMap_apply, Matrix.one_apply] <;> ring_nf <;> simp [Complex.ext_iff] <;> norm_num

/-- **Proposition 99: `1, K₁, K₂, K₃` span the operators of the side.** -/
theorem side_span (X : Matrix Four Four ℂ) (hX : sideP * X * sideP = X) :
    X = (X (0, 0) (0, 0) + X (0, 1) (0, 1)) • sideP +
      (I * (X (0, 0) (0, 1) + X (0, 1) (0, 0))) • (Kturn 2 * sideP) +
      (X (0, 1) (0, 0) - X (0, 0) (0, 1)) • (Kturn 3 * sideP) +
      (I * (X (0, 0) (0, 0) - X (0, 1) (0, 1))) • (Kturn 4 * sideP) := by
  obtain ⟨k2, k3, k4⟩ := K_side
  rw [k2, k3, k4, sideP_kron]
  ext ⟨i, j⟩ ⟨k, l⟩
  rw [side_entries X hX i j k l]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [halfOnes, σ₁, σ₂, σ₃, Matrix.kroneckerMap_apply, Matrix.one_apply] <;> ring_nf <;>
    simp [Complex.ext_iff] <;> ring_nf <;> simp

/-- Each `K_c` keeps the side: `Π K_c Π = K_c Π`. -/
theorem K_on_side {c : Fin 5} (h0 : c ≠ 0) : sideP * (Kturn c * sideP) = Kturn c * sideP := by
  have hc : Kturn c * γ 0 = γ 0 * Kturn c := K_comm_lastDirection h0
  have hP : sideP * sideP = sideP := by
    rw [sideP, smul_mul_smul_comm, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, Matrix.one_mul, γ_mul_self]
    module
  have hKP : Kturn c * sideP = sideP * Kturn c := by
    rw [sideP, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, hc, Matrix.mul_one,
      Matrix.one_mul]
  rw [hKP, ← Matrix.mul_assoc, hP]

end Comparison.Article
