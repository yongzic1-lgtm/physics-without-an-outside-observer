module

public import Mathlib

/-!
# Pauli matrices, Dirac matrices and quaternions in Mathlib

Small facts the project builds on:

* Pauli matrices over `ℂ`: each squares to `1`, two different ones anticommute,
  and `σ₁ σ₂ = i σ₃`.
* Dirac-representation gamma matrices in `Matrix (Fin 4) (Fin 4) ℂ`:
  the Clifford relations `γ₀² = 1`, `γₖ² = -1`, `{γ_μ, γ_ν} = 0` for `μ ≠ ν`.
* A Kronecker product of Pauli matrices: two anticommuting factors give a commuting product.
* Quaternions `ℍ[ℝ]`: Hamilton's rules and the multiplicativity of the norm.

Build with `lake build Comparison.PauliDirac`.
-/

@[expose] public section

namespace PauliDirac

open Complex Matrix Kronecker
open scoped Quaternion

/-! ## Pauli matrices over `ℂ` -/

/-- Pauli matrix `σ₁`. -/
def σ₁ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- Pauli matrix `σ₂`. -/
def σ₂ : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]

/-- Pauli matrix `σ₃`. -/
def σ₃ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

theorem σ₁_sq : σ₁ * σ₁ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [σ₁, Matrix.mul_apply, Fin.sum_univ_two]

theorem σ₂_sq : σ₂ * σ₂ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [σ₂, Matrix.mul_apply, Fin.sum_univ_two]

theorem σ₃_sq : σ₃ * σ₃ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [σ₃, Matrix.mul_apply, Fin.sum_univ_two]

/-- Two different Pauli matrices anticommute: `σ₁ σ₂ + σ₂ σ₁ = 0`. -/
theorem σ₁_σ₂_anticomm : σ₁ * σ₂ + σ₂ * σ₁ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [σ₁, σ₂]

theorem σ₂_σ₃_anticomm : σ₂ * σ₃ + σ₃ * σ₂ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [σ₂, σ₃]

theorem σ₁_σ₃_anticomm : σ₁ * σ₃ + σ₃ * σ₁ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [σ₁, σ₃]

/-- `σ₁ σ₂ = i σ₃`. -/
theorem σ₁_mul_σ₂ : σ₁ * σ₂ = I • σ₃ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [σ₁, σ₂, σ₃, Matrix.mul_apply, Fin.sum_univ_two]

/-! ## Dirac-representation gamma matrices in `Matrix (Fin 4) (Fin 4) ℂ` -/

/-- `γ₀ = diag(1, 1, -1, -1)`. -/
def γ₀ : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, -1, 0;
     0, 0, 0, -1]

/-- `γ₁ = [[0, σ₁], [-σ₁, 0]]`. -/
def γ₁ : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, 1;
     0, 0, 1, 0;
     0, -1, 0, 0;
     -1, 0, 0, 0]

/-- `γ₂ = [[0, σ₂], [-σ₂, 0]]`. -/
def γ₂ : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, 0, -I;
     0, 0, I, 0;
     0, I, 0, 0;
     -I, 0, 0, 0]

theorem γ₀_sq : γ₀ * γ₀ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [γ₀, Matrix.mul_apply, Fin.sum_univ_four]

theorem γ₁_sq : γ₁ * γ₁ = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [γ₁, Matrix.mul_apply, Fin.sum_univ_four]

theorem γ₂_sq : γ₂ * γ₂ = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [γ₂, Matrix.mul_apply, Fin.sum_univ_four]

theorem γ₀_γ₁_anticomm : γ₀ * γ₁ + γ₁ * γ₀ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [γ₀, γ₁]

theorem γ₀_γ₂_anticomm : γ₀ * γ₂ + γ₂ * γ₀ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [γ₀, γ₂]

theorem γ₁_γ₂_anticomm : γ₁ * γ₂ + γ₂ * γ₁ = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [γ₁, γ₂]

theorem trace_γ₀ : Matrix.trace γ₀ = 0 := by
  norm_num [Matrix.trace, γ₀, Fin.sum_univ_four]

/-! ## A Kronecker product of Pauli matrices -/

/-- `σ₃ σ₁ = -(σ₁ σ₃)`, from the anticommutator. -/
theorem σ₃_mul_σ₁ : σ₃ * σ₁ = -(σ₁ * σ₃) := by
  rw [eq_neg_iff_add_eq_zero, add_comm]
  exact σ₁_σ₃_anticomm

/-- Two anticommuting factors give a commuting Kronecker product:
`(σ₁ ⊗ σ₁)(σ₃ ⊗ σ₃) = (σ₃ ⊗ σ₃)(σ₁ ⊗ σ₁)` on `ℂ² ⊗ ℂ²`. -/
theorem kron_commute :
    (σ₁ ⊗ₖ σ₁) * (σ₃ ⊗ₖ σ₃) = (σ₃ ⊗ₖ σ₃) * (σ₁ ⊗ₖ σ₁) := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, σ₃_mul_σ₁]
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [Matrix.kroneckerMap_apply]

/-! ## Quaternions `ℍ[ℝ]` -/

/-- The quaternion unit `i`. -/
def qi : ℍ[ℝ] := ⟨0, 1, 0, 0⟩

/-- The quaternion unit `j`. -/
def qj : ℍ[ℝ] := ⟨0, 0, 1, 0⟩

/-- The quaternion unit `k`. -/
def qk : ℍ[ℝ] := ⟨0, 0, 0, 1⟩

theorem qi_sq : qi * qi = -1 := by
  ext <;> simp [qi]

theorem qi_mul_qj : qi * qj = qk := by
  ext <;> simp [qi, qj, qk]

/-- Hamilton's units anticommute, like the Pauli matrices: `j i = -k`. -/
theorem qj_mul_qi : qj * qi = -qk := by
  ext <;> simp [qi, qj, qk]

/-- The quaternion norm is multiplicative. -/
theorem normSq_mul (p q : ℍ[ℝ]) :
    Quaternion.normSq (p * q) = Quaternion.normSq p * Quaternion.normSq q :=
  map_mul Quaternion.normSq p q

/-- `ℍ[ℝ]` is a division ring: every nonzero quaternion is invertible. -/
theorem mul_inv_of_ne_zero (q : ℍ[ℝ]) (h : q ≠ 0) : q * q⁻¹ = 1 :=
  mul_inv_cancel₀ h

end PauliDirac

end

-- Axiom check: only the standard axioms may appear (no `sorryAx`).
#print axioms PauliDirac.σ₁_σ₂_anticomm
#print axioms PauliDirac.γ₁_γ₂_anticomm
#print axioms PauliDirac.kron_commute
#print axioms PauliDirac.qj_mul_qi
