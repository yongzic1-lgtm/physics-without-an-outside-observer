module

public import Mathlib

/-!
# The Elements of Comparison in Lean. Book I: one system

One system has four amplitudes. We index them by `Four = Fin 2 × Fin 2`, so `ℂ⁴ = Four → ℂ`.

* `J = 1 ⊗ ε`, `ε = !![0, 1; -1, 0]`, is the alternating join. In the order
  (0,0), (0,1), (1,0), (1,1) it is `diag(ε, ε)`.
* `Θ v = J v̄` is the quaternionic structure map (`Θ = J K`, `K` the complex conjugation).
* A distinction is a Hermitian matrix of trace zero that commutes with `Θ`
  (`IsDistinction`; `commutes_Θ_iff` turns the commuting into `a J = J ā`).
* The five directions are the explicit matrices `γ 0, …, γ 4`:
  `σ₁ ⊗ 1, σ₃ ⊗ 1, σ₂ ⊗ σ₁, σ₂ ⊗ σ₂, σ₂ ⊗ σ₃` (Pauli matrices `σ₁, σ₂, σ₃`).

Proved here: `Θ² = -1`, every state is orthogonal to its conjugate and as long, the Clifford
two-spinor state `γ_s γ_t + γ_t γ_s = 2 δ_st`, and `γ₀ γ₁ γ₂ γ₃ γ₄ = 1`.
-/

@[expose] public section

namespace Comparison

open Matrix hiding J
open Complex Kronecker

/-- One system: four amplitudes, indexed as two pairs. -/
abbrev Four := Fin 2 × Fin 2

/-- Split an identity of matrices on `Four` into its sixteen entries. -/
macro "four_ext" : tactic =>
  `(tactic| (ext ⟨a, b⟩ ⟨c, d⟩; fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d))

/-- Pauli matrix `σ₁`. -/
def σ₁ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
/-- Pauli matrix `σ₂`. -/
def σ₂ : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]
/-- Pauli matrix `σ₃`. -/
def σ₃ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]
/-- The alternating `2 × 2` block. -/
def ε : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; -1, 0]

/-- The join `J = 1 ⊗ ε = diag(ε, ε)`. -/
def J : Matrix Four Four ℂ := (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ ε

/-- The quaternionic structure map `Θ v = J v̄`. -/
def Θ (v : Four → ℂ) : Four → ℂ := J *ᵥ star v

/-! ## The quaternionic structure (Proposition 1) -/

/-- The join is alternating: `Jᵀ = -J`. -/
theorem J_transpose : Jᵀ = -J := by
  four_ext <;> simp [J, ε]

/-- The join is real. -/
theorem J_map_star : J.map star = J := by
  four_ext <;> simp [J, ε]

theorem J_conjTranspose : Jᴴ = -J := by
  four_ext <;> simp [J, ε]

theorem J_mul_J : J * J = -1 := by
  four_ext <;> simp [J, ε, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.one_apply]

/-- The join is unitary. -/
theorem J_mul_conjTranspose : J * Jᴴ = 1 := by
  rw [J_conjTranspose, Matrix.mul_neg, J_mul_J, neg_neg]

/-- The conjugate of the conjugate is `-v`: `Θ² = -1`. -/
theorem Θ_Θ (v : Four → ℂ) : Θ (Θ v) = -v := by
  ext ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [Θ, J, ε, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- Every state is orthogonal to its conjugate: `⟨v, Θ v⟩ = 0`. -/
theorem Θ_orth (v : Four → ℂ) : star v ⬝ᵥ Θ v = 0 := by
  simp [Θ, J, ε, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

/-- The conjugate is as long as the state: `⟨Θ v, Θ v⟩ = ⟨v, v⟩`. -/
theorem Θ_norm (v : Four → ℂ) : star (Θ v) ⬝ᵥ Θ v = star v ⬝ᵥ v := by
  simp [Θ, J, ε, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]
  ring

theorem Θ_add (v w : Four → ℂ) : Θ (v + w) = Θ v + Θ w := by
  simp [Θ, Matrix.mulVec_add]

/-- The quaternionic structure map is antilinear. -/
theorem Θ_smul (c : ℂ) (v : Four → ℂ) : Θ (c • v) = star c • Θ v := by
  simp [Θ, Matrix.mulVec_smul]

/-! ## Distinctions and the five directions (Propositions 2 to 4) -/

/-- A distinction: Hermitian, of trace zero, and commuting with the quaternionic structure (`a J = J ā`). -/
def IsDistinction (a : Matrix Four Four ℂ) : Prop :=
  aᴴ = a ∧ a.trace = 0 ∧ a * J = J * a.map star

theorem star_mulVec' (a : Matrix Four Four ℂ) (v : Four → ℂ) :
    star (a *ᵥ v) = a.map star *ᵥ star v := by
  ext i
  simp [Matrix.mulVec, dotProduct, star_sum]

/-- Commuting with the quaternionic structure map is the matrix identity `a J = J ā`. -/
theorem commutes_Θ_iff (a : Matrix Four Four ℂ) :
    (∀ v, a *ᵥ Θ v = Θ (a *ᵥ v)) ↔ a * J = J * a.map star := by
  constructor
  · intro h
    rw [Matrix.ext_iff_mulVec]
    intro w
    have := h (star w)
    simp only [Θ, star_mulVec', star_star, Matrix.mulVec_mulVec] at this
    exact this
  · intro h v
    simp only [Θ, star_mulVec', Matrix.mulVec_mulVec, h]

/-- The five directions: `σ₁ ⊗ 1, σ₃ ⊗ 1, σ₂ ⊗ σ₁, σ₂ ⊗ σ₂, σ₂ ⊗ σ₃`. -/
def γ : Fin 5 → Matrix Four Four ℂ :=
  ![σ₁ ⊗ₖ 1, σ₃ ⊗ₖ 1, σ₂ ⊗ₖ σ₁, σ₂ ⊗ₖ σ₂, σ₂ ⊗ₖ σ₃]

theorem γ_conjTranspose (s : Fin 5) : (γ s)ᴴ = γ s := by
  fin_cases s <;> (four_ext <;> simp [γ, σ₁, σ₂, σ₃])

theorem γ_trace (s : Fin 5) : (γ s).trace = 0 := by
  fin_cases s <;> simp [γ, σ₁, σ₂, σ₃, Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem γ_mul_J (s : Fin 5) : γ s * J = J * (γ s).map star := by
  fin_cases s <;>
  (four_ext <;> simp [γ, σ₁, σ₂, σ₃, J, ε, Matrix.mul_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two])

/-- Each of the five directions is a distinction. -/
theorem γ_isDistinction (s : Fin 5) : IsDistinction (γ s) :=
  ⟨γ_conjTranspose s, γ_trace s, γ_mul_J s⟩

set_option maxHeartbeats 4000000 in
-- 25 pairs of lines, each checked on all sixteen entries
/-- The Clifford relation: `γ_s γ_t + γ_t γ_s = 2 δ_st`. -/
theorem clifford (s t : Fin 5) :
    γ s * γ t + γ t * γ s = (if s = t then (2 : ℂ) else 0) • (1 : Matrix Four Four ℂ) := by
  fin_cases s <;> fin_cases t <;>
  · four_ext <;>
      simp [γ, σ₁, σ₂, σ₃, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
        Matrix.one_apply] <;> norm_num

/-- Each line squares to one. -/
theorem γ_mul_self (s : Fin 5) : γ s * γ s = 1 := by
  have h := clifford s s
  simp only [ite_true] at h
  rw [← two_smul ℂ (γ s * γ s)] at h
  exact smul_right_injective _ two_ne_zero h

/-- Perpendicular lines anticommute. -/
theorem γ_anticomm {s t : Fin 5} (h : s ≠ t) : γ s * γ t = -(γ t * γ s) := by
  have h' := clifford s t
  simp only [h, ite_false, zero_smul] at h'
  exact eq_neg_of_add_eq_zero_left h'

/-- The product of the five directions is a number: `γ₀ γ₁ γ₂ γ₃ γ₄ = 1`. -/
theorem γ_prod : γ 0 * γ 1 * γ 2 * γ 3 * γ 4 = 1 := by
  simp only [γ, Matrix.cons_val]
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, ← mul_kronecker_mul, ← mul_kronecker_mul]
  have h1 : σ₁ * σ₃ * σ₂ * σ₂ * σ₂ = (-I) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [σ₁, σ₂, σ₃, Matrix.mul_apply, Fin.sum_univ_two]
  have h2 : (1 : Matrix (Fin 2) (Fin 2) ℂ) * 1 * σ₁ * σ₂ * σ₃ = I • 1 := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [σ₁, σ₂, σ₃, Matrix.mul_apply, Fin.sum_univ_two]
  rw [h1, h2, Matrix.smul_kronecker, Matrix.kronecker_smul, one_kronecker_one, smul_smul]
  simp

end Comparison

end
