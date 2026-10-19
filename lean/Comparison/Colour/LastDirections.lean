module

public import Comparison.Elements.OneThing

/-!
# Book XV. The last-step directions, and one share per light line (Proposition 85)

The last-step directions are the spins one half of
Proposition 34, with the three Pauli matrices `σ₁, σ₂, σ₃` (`pauli3`).

* `dot2 = Σ_a σ_a ⊗ σ_a` on two last-step directions: `dot2_eq`: `σ₁·σ₂ = 2P − 1` (`P` the swap of the two last-step directions);
  `dot2_sq`: `(σ₁·σ₂ − 1)(σ₁·σ₂ + 3) = 0`; `dot2_agree`: `+1` on every symmetric state (the last-step directions
  agree); `dot2_differ`: `−3` on every antisymmetric state (the last-step directions differ).
* `dot3 = Σ_{i<j} σ_i·σ_j` on three last-step directions: `dot3_mulVec`: `dot3 v = 2(P₁₂ + P₁₃ + P₂₃)v − 3v`;
  `dot3_sq`: `(dot3 − 3)(dot3 + 3) = 0` (`swapSum_twice`: `Q² = 3Q`); `dot3_agree`: `+3` on every
  symmetric state (all agree);
  `dot3_differ`: `−3` on every state whose three swaps sum to zero (one differs), e.g.
  `|↑↑↓⟩ − |↑↓↑⟩` (`dot3_example`).
* `lastDirection_cost`: `m_p = 3u − 3A` and `3u + 3A = 3b m_p` with `b = 7/16` give `A = (5/96)m_p`,
  `u = (37/96)m_p` and the share `u − A = m_p/3`.
-/

@[expose] public section

namespace Comparison

open Matrix hiding J
open Complex Kronecker

/-- The three Pauli matrices. -/
def pauli3 : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ := ![σ₁, σ₂, σ₃]

/-! ## Two last-step directions -/

/-- `σ₁·σ₂ = Σ_a σ_a ⊗ σ_a` on two last-step directions. -/
def dot2 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ := ∑ a, pauli3 a ⊗ₖ pauli3 a

/-- The swap of two last-step directions. -/
def swap2 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun p q => if p.1 = q.2 ∧ p.2 = q.1 then 1 else 0

/-- **`σ₁·σ₂ = 2P − 1`.** -/
theorem dot2_eq : dot2 = (2 : ℂ) • swap2 - 1 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [dot2, pauli3, σ₁, σ₂, σ₃, Fin.sum_univ_three, swap2] <;> norm_num

theorem swap2_mulVec (v : Fin 2 × Fin 2 → ℂ) : swap2 *ᵥ v = fun p => v (p.2, p.1) := by
  ext ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [swap2, Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem swap2_sq : swap2 * swap2 = 1 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [swap2, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

/-- **The two values:** `(σ₁·σ₂ − 1)(σ₁·σ₂ + 3) = 0`. -/
theorem dot2_sq : (dot2 - 1) * (dot2 + (3 : ℂ) • 1) = 0 := by
  rw [dot2_eq]
  have e : ((2 : ℂ) • swap2 - 1 - 1) * ((2 : ℂ) • swap2 - 1 + (3 : ℂ) • 1) =
      (4 : ℂ) • (swap2 * swap2) - (4 : ℂ) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    module
  rw [e, swap2_sq, sub_self]

/-- **Two last-step directions that agree count `+1`:** `σ₁·σ₂ v = v` for every symmetric `v`. -/
theorem dot2_agree (v : Fin 2 × Fin 2 → ℂ) (hv : ∀ a b, v (a, b) = v (b, a)) :
    dot2 *ᵥ v = v := by
  rw [dot2_eq, Matrix.sub_mulVec, Matrix.smul_mulVec, swap2_mulVec, Matrix.one_mulVec]
  ext ⟨a, b⟩
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [← hv a b]
  ring

/-- **Two last-step directions that differ count `−3`:** `σ₁·σ₂ v = −3v` for every antisymmetric `v`. -/
theorem dot2_differ (v : Fin 2 × Fin 2 → ℂ) (hv : ∀ a b, v (a, b) = -v (b, a)) :
    dot2 *ᵥ v = (-3 : ℂ) • v := by
  rw [dot2_eq, Matrix.sub_mulVec, Matrix.smul_mulVec, swap2_mulVec, Matrix.one_mulVec]
  ext ⟨a, b⟩
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have := hv b a
  rw [this]
  ring

/-! ## Three last-step directions -/

/-- Three last-step directions: `((a, b), c)`. -/
abbrev LastDirections3 := (Fin 2 × Fin 2) × Fin 2

/-- `Σ_{i<j} σ_i·σ_j` on three last-step directions. -/
def dot3 : Matrix LastDirections3 LastDirections3 ℂ :=
  ∑ a, ((pauli3 a ⊗ₖ pauli3 a) ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ) +
    (pauli3 a ⊗ₖ (1 : Matrix (Fin 2) (Fin 2) ℂ)) ⊗ₖ pauli3 a +
    ((1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ pauli3 a) ⊗ₖ pauli3 a)

/-- The three swaps of three last-step directions, on states. -/
def swap12 (v : LastDirections3 → ℂ) : LastDirections3 → ℂ := fun p => v ((p.1.2, p.1.1), p.2)
def swap13 (v : LastDirections3 → ℂ) : LastDirections3 → ℂ := fun p => v ((p.2, p.1.2), p.1.1)
def swap23 (v : LastDirections3 → ℂ) : LastDirections3 → ℂ := fun p => v ((p.1.1, p.2), p.1.2)

/-- The sum of the three swaps, `(P₁₂ + P₁₃ + P₂₃) v`. -/
def swapSum (v : LastDirections3 → ℂ) : LastDirections3 → ℂ := swap12 v + swap13 v + swap23 v

set_option maxHeartbeats 4000000 in
-- eight entries, each a sum over the three Pauli matrices and eight states
/-- **`Σ_{i<j} σ_i·σ_j = 2(P₁₂ + P₁₃ + P₂₃) − 3`** on every state. -/
theorem dot3_mulVec (v : LastDirections3 → ℂ) :
    dot3 *ᵥ v = (2 : ℂ) • swapSum v - (3 : ℂ) • v := by
  ext ⟨⟨a, b⟩, c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [dot3, pauli3, σ₁, σ₂, σ₃, Fin.sum_univ_three,
      Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply,
      swapSum, swap12, swap13, swap23] <;> ring

/-- **All three last-step directions agree: `+3`.** -/
theorem dot3_agree (v : LastDirections3 → ℂ) (h12 : swap12 v = v) (h13 : swap13 v = v)
    (h23 : swap23 v = v) : dot3 *ᵥ v = (3 : ℂ) • v := by
  rw [dot3_mulVec, swapSum, h12, h13, h23]
  module

/-- **One last-step direction differs: `−3`** on every state whose three swaps sum to zero. -/
theorem dot3_differ (v : LastDirections3 → ℂ) (h : swapSum v = 0) :
    dot3 *ᵥ v = (-3 : ℂ) • v := by
  rw [dot3_mulVec, h]
  module

/-- `|↑↑↓⟩ − |↑↓↑⟩`. -/
def oneDiffers : LastDirections3 → ℂ := fun p =>
  if p = ((0, 0), 1) then 1 else if p = ((0, 1), 0) then -1 else 0

theorem dot3_example : dot3 *ᵥ oneDiffers = (-3 : ℂ) • oneDiffers := by
  apply dot3_differ
  ext ⟨⟨a, b⟩, c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [oneDiffers, swapSum, swap12, swap13, swap23]

/-- `|↑↑↑⟩`. -/
def allAgree : LastDirections3 → ℂ := fun p => if p = ((0, 0), 0) then 1 else 0

theorem dot3_example_agree : dot3 *ᵥ allAgree = (3 : ℂ) • allAgree := by
  apply dot3_agree <;>
  · ext ⟨⟨a, b⟩, c⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [allAgree, swap12, swap13, swap23]

/-- The three swaps twice: `Q² = 3Q` (no state of three last-step directions is odd under every swap). -/
theorem swapSum_twice (v : LastDirections3 → ℂ) : swapSum (swapSum v) = (3 : ℂ) • swapSum v := by
  ext ⟨⟨a, b⟩, c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> simp [swapSum, swap12, swap13, swap23] <;> ring

theorem swapSum_smul (c : ℂ) (v : LastDirections3 → ℂ) : swapSum (c • v) = c • swapSum v := by
  ext p
  simp [swapSum, swap12, swap13, swap23]
  ring

/-- **The three last-step directions take two values:** `(dot3 − 3)(dot3 + 3) = 0` on every state. -/
theorem dot3_sq (v : LastDirections3 → ℂ) :
    (dot3 - (3 : ℂ) • 1) *ᵥ ((dot3 + (3 : ℂ) • 1) *ᵥ v) = 0 := by
  have h1 : (dot3 + (3 : ℂ) • 1) *ᵥ v = (2 : ℂ) • swapSum v := by
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dot3_mulVec]
    abel
  rw [h1, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dot3_mulVec, swapSum_smul,
    swapSum_twice]
  module

/-! ## The last-step direction cost and the share of a light line -/

/-- **The last-step direction cost and one share per light line:** `m_p = 3u − 3A` (the nucleon, last-step directions `−3`) and
`3u + 3A = 3b m_p` (the Δ, last-step directions `+3`, `b = 7/16`) give `A = (5/96)m_p`, `u = (37/96)m_p`, and the
share of one light line `λ = u − A = m_p/3`. -/
theorem lastDirection_cost (m u A : ℝ) (hN : m = 3 * u - 3 * A) (hΔ : 3 * u + 3 * A = 3 * (7 / 16) * m) :
    A = 5 / 96 * m ∧ u = 37 / 96 * m ∧ u - A = m / 3 ∧ 4 * A = 5 / 24 * m := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

end Comparison

end
