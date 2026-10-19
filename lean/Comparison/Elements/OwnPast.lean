module

public import Comparison.Elements.TwoThings

/-!
# Book II, Proposition 13: one's own past and a neighbour

* `partnerOp X = J Xᵀ J†`, the conjugate of an operator (`X^♯ = Θ X† Θ⁻¹`);
  `partnerOp_eq_self_iff`: a Hermitian `X` is its own conjugate exactly when it commutes with the
  quaternionic structure (so exactly for `X` in `ℝ1 ⊕ Q`); `partnerOp_γ`, `partnerOp_one`.
* `partnerTwo`: taking the quaternionic structure on the second of two systems, `X ⊗ Y ↦ X ⊗ Y^♯`
  (`partnerTwo_kron`).
* `partnerTwo_swap`, `partnerTwo_Eop`: **it exchanges the swap `P` and `E`**;
  `partnerTwo_L`: **it keeps the comparison `L`** (P2 (b): one's own past and a neighbour are
  compared alike).
-/

@[expose] public section

namespace Comparison

open Matrix hiding J
open Complex Kronecker

/-- The conjugate of an operator: `X^♯ = J Xᵀ J†`. -/
def partnerOp (X : Matrix Four Four ℂ) : Matrix Four Four ℂ := J * Xᵀ * Jᴴ

theorem J_conjTranspose_mul' : Jᴴ * J = 1 := by
  rw [J_conjTranspose, Matrix.neg_mul, J_mul_J, neg_neg]

/-- **A Hermitian operator is its own conjugate exactly when it commutes with the quaternionic structure.** -/
theorem partnerOp_eq_self_iff (X : Matrix Four Four ℂ) (hX : Xᴴ = X) :
    partnerOp X = X ↔ X * J = J * X.map star := by
  have hT : X.map star = Xᵀ := by
    ext i j
    have := congrFun (congrFun hX j) i
    simp only [Matrix.conjTranspose_apply] at this
    simp [← this]
  rw [hT, partnerOp]
  constructor
  · intro h
    calc X * J = J * Xᵀ * Jᴴ * J := by rw [h]
      _ = J * Xᵀ := by rw [Matrix.mul_assoc, J_conjTranspose_mul', Matrix.mul_one]
  · intro h
    rw [← h, Matrix.mul_assoc, J_mul_conjTranspose, Matrix.mul_one]

theorem partnerOp_γ (s : Fin 5) : partnerOp (γ s) = γ s :=
  (partnerOp_eq_self_iff _ (γ_conjTranspose s)).mpr (γ_mul_J s)

theorem partnerOp_one : partnerOp 1 = 1 := by
  rw [partnerOp, Matrix.transpose_one, Matrix.mul_one, J_mul_conjTranspose]

/-- The partial transpose on the second system. -/
def transposeTwo (M : Matrix Two Two ℂ) : Matrix Two Two ℂ :=
  Matrix.of fun p q => M (p.1, q.2) (q.1, p.2)

/-- **Taking the quaternionic structure on the second system:** `M ↦ (1 ⊗ J) M^{T₂} (1 ⊗ J†)`. -/
def partnerTwo (M : Matrix Two Two ℂ) : Matrix Two Two ℂ :=
  (1 ⊗ₖ J) * transposeTwo M * (1 ⊗ₖ Jᴴ)

theorem transposeTwo_kron (X Y : Matrix Four Four ℂ) : transposeTwo (X ⊗ₖ Y) = X ⊗ₖ Yᵀ := by
  ext ⟨x, y⟩ ⟨x', y'⟩
  simp [transposeTwo]

/-- `X ⊗ Y ↦ X ⊗ Y^♯`. -/
theorem partnerTwo_kron (X Y : Matrix Four Four ℂ) : partnerTwo (X ⊗ₖ Y) = X ⊗ₖ partnerOp Y := by
  rw [partnerTwo, transposeTwo_kron, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.one_mul,
    Matrix.mul_one, partnerOp]

theorem partnerTwo_add (M N : Matrix Two Two ℂ) :
    partnerTwo (M + N) = partnerTwo M + partnerTwo N := by
  have : transposeTwo (M + N) = transposeTwo M + transposeTwo N := by
    ext p q
    simp [transposeTwo]
  rw [partnerTwo, this, Matrix.mul_add, Matrix.add_mul]
  rfl

theorem partnerTwo_smul (c : ℂ) (M : Matrix Two Two ℂ) :
    partnerTwo (c • M) = c • partnerTwo M := by
  have : transposeTwo (c • M) = c • transposeTwo M := by
    ext p q
    simp [transposeTwo]
  rw [partnerTwo, this, Matrix.mul_smul, Matrix.smul_mul]
  rfl

theorem partnerTwo_sum (f : Fin 5 → Matrix Two Two ℂ) :
    partnerTwo (∑ s, f s) = ∑ s, partnerTwo (f s) := by
  simp only [Fin.sum_univ_five, partnerTwo_add]

set_option maxHeartbeats 8000000 in
-- 256 entries of a 16 × 16 identity
/-- **Taking the quaternionic structure on one system turns the swap into `E`.** -/
theorem partnerTwo_swap : partnerTwo swap = Eop := by
  ext ⟨⟨a, b⟩, ⟨c, d⟩⟩ ⟨⟨e, f⟩, ⟨g, h⟩⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    fin_cases e <;> fin_cases f <;> fin_cases g <;> fin_cases h <;>
    simp [partnerTwo, transposeTwo, swap, Eop, Ω, relOf, MΩ, J, ε, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply, RCLike.conj_ofNat] <;> norm_num

set_option maxHeartbeats 8000000 in
-- 256 entries of a 16 × 16 identity
/-- **... and `E` into the swap.** -/
theorem partnerTwo_Eop : partnerTwo Eop = swap := by
  ext ⟨⟨a, b⟩, ⟨c, d⟩⟩ ⟨⟨e, f⟩, ⟨g, h⟩⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    fin_cases e <;> fin_cases f <;> fin_cases g <;> fin_cases h <;>
    simp [partnerTwo, transposeTwo, swap, Eop, Ω, relOf, MΩ, J, ε, Matrix.mul_apply,
      Fintype.sum_prod_type, Fin.sum_univ_two, Matrix.one_apply, RCLike.conj_ofNat] <;> norm_num

/-- **Taking the quaternionic structure on one system keeps the comparison** (P2 (b)). -/
theorem partnerTwo_L : partnerTwo L = L := by
  rw [L, partnerTwo_add, partnerTwo_kron, partnerOp_one, partnerTwo_sum]
  simp only [partnerTwo_kron, partnerOp_γ]

/-- The same, read through the swap and the singlet: `2(P + E) ↦ 2(E + P)`. -/
theorem partnerTwo_swap_singlet : partnerTwo ((2 : ℂ) • (swap + Eop)) = (2 : ℂ) • (Eop + swap) := by
  rw [partnerTwo_smul, partnerTwo_add, partnerTwo_swap, partnerTwo_Eop]

end Comparison

end
