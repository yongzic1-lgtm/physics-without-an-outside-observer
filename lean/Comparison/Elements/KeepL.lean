module

public import Comparison.Elements.TwoThings
public import Comparison.Elements.SixDirections

/-!
# Book III, Proposition 17 (iv): the rotations that keep the singlet and the rotations that keep `L`

* `pf_conj`: `Pf(U M Uᵀ) = det U · Pf M` for antisymmetric `M`.
* `det_eq_one_of_keeps_J`: a matrix with `U J Uᵀ = J` has determinant one (Prop. 6).
* `keeps_singlet_iff`: `(U ⊗ U) Ω = Ω ⟺ U J Uᵀ = J`.
* `keeps_L_iff`: a rotation (unitary, determinant one) keeps the comparison `L` exactly when
  `U J Uᵀ = J` or `U J Uᵀ = −J`; `neg_iff_I_smul`: the second is `i U ∈ Sp(2)`.
  So the rotations that keep `L` are `Sp(2)` and `i·Sp(2)`.
-/

@[expose] public section

namespace Comparison

open Matrix hiding J
open Complex Kronecker

set_option maxHeartbeats 4000000 in
-- one polynomial identity of degree six in twenty-two entries
/-- **The Pfaffian law:** `Pf(U M Uᵀ) = det U · Pf M` for every antisymmetric `M`. -/
theorem pf_conj (U M : Matrix Four Four ℂ) (hM : Mᵀ = -M) :
    pf (U * M * Uᵀ) = U.det * pf M := by
  have h : ∀ i j, M j i = -M i j := fun i j => by
    have := congrFun (congrFun hM i) j
    simpa using this
  have hd : ∀ i, M i i = 0 := fun i => by
    have := h i i
    linear_combination this / 2
  rw [det_four, det_fin_four]
  simp only [pf, Matrix.mul_apply, Matrix.transpose_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  rw [h (0, 0) (0, 1), h (0, 0) (1, 0), h (0, 0) (1, 1),
    h (0, 1) (1, 0), h (0, 1) (1, 1), h (1, 0) (1, 1), hd (0, 0), hd (0, 1), hd (1, 0),
    hd (1, 1)]
  ring

theorem pf_smul (c : ℂ) (M : Matrix Four Four ℂ) : pf (c • M) = c ^ 2 * pf M := by
  simp only [pf, Matrix.smul_apply, smul_eq_mul]
  ring

/-- **The rotations that keep the join have determinant one** (Prop. 6). -/
theorem det_eq_one_of_keeps_J (U : Matrix Four Four ℂ) (h : U * J * Uᵀ = J) : U.det = 1 := by
  have := pf_conj U J J_transpose
  rw [h, pf_J, mul_one] at this
  exact this.symm

/-- If `U J Uᵀ = c J` then `c² = det U`. -/
theorem sq_eq_det_of_keeps_J_up_to (U : Matrix Four Four ℂ) (c : ℂ)
    (h : U * J * Uᵀ = c • J) : c ^ 2 = U.det := by
  have := pf_conj U J J_transpose
  rw [h, pf_smul, pf_J, mul_one, mul_one] at this
  exact this

/-- `U ⊗ U` carries the singlet to the two-spinor state with matrix `U M_Ω Uᵀ`. -/
theorem kron_mulVec_Ω (U : Matrix Four Four ℂ) : (U ⊗ₖ U) *ᵥ Ω = relOf (U * MΩ * Uᵀ) := by
  rw [Ω, kron_mulVec_relOf]

/-- **The rotations that keep the singlet:** `(U ⊗ U) Ω = Ω ⟺ U J Uᵀ = J`. -/
theorem keeps_singlet_iff (U : Matrix Four Four ℂ) : (U ⊗ₖ U) *ᵥ Ω = Ω ↔ U * J * Uᵀ = J := by
  rw [kron_mulVec_Ω, Ω]
  constructor
  · intro h
    have h' := relOf_injective h
    rw [MΩ, Matrix.mul_smul, Matrix.smul_mul] at h'
    have := congrArg (fun M => (-2 : ℂ) • M) h'
    simpa [smul_smul] using this
  · intro h
    rw [MΩ, Matrix.mul_smul, Matrix.smul_mul, h]

theorem kron_swap_comm (U : Matrix Four Four ℂ) : (U ⊗ₖ U) * swap = swap * (U ⊗ₖ U) := by
  ext ⟨x, y⟩ ⟨x', y'⟩
  simp [swap, Matrix.mul_apply, sum_two, ite_and, mul_comm]

theorem Eop_mulVec (w : Two → ℂ) : Eop *ᵥ w = (4 * (star Ω ⬝ᵥ w)) • Ω := by
  ext p
  simp only [Eop, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
    Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  ring

theorem kron_unitary (U : Matrix Four Four ℂ) (hU : U * Uᴴ = 1) :
    (U ⊗ₖ U)ᴴ * (U ⊗ₖ U) = 1 := by
  have hU' : Uᴴ * U = 1 := mul_eq_one_comm.mp hU
  rw [conjTranspose_kronecker, ← mul_kronecker_mul, hU', one_kronecker_one]

theorem mul_Eop (A : Matrix Two Two ℂ) :
    A * Eop = Matrix.of fun p q => 4 * (A *ᵥ Ω) p * star (Ω q) := by
  ext p q
  simp only [Eop, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

theorem Eop_mul (A : Matrix Two Two ℂ) :
    Eop * A = Matrix.of fun p q => 4 * Ω p * (star Ω ᵥ* A) q := by
  ext p q
  simp only [Eop, Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.of_apply, Finset.mul_sum,
    Pi.star_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  ring

/-- **The rotations that keep the comparison:** a unitary `U` of determinant one keeps `L` exactly
when `U J Uᵀ = J` or `U J Uᵀ = −J`. -/
theorem keeps_L_iff (U : Matrix Four Four ℂ) (hU : U * Uᴴ = 1) (hdet : U.det = 1) :
    (U ⊗ₖ U) * L = L * (U ⊗ₖ U) ↔ U * J * Uᵀ = J ∨ U * J * Uᵀ = -J := by
  have hE : (U ⊗ₖ U) * L = L * (U ⊗ₖ U) ↔ (U ⊗ₖ U) * Eop = Eop * (U ⊗ₖ U) := by
    rw [L_eq_swap_singlet, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
      kron_swap_comm]
    constructor
    · intro h
      have h2 := smul_right_injective _ (two_ne_zero' ℂ) h
      exact add_left_cancel h2
    · intro h
      rw [h]
  rw [hE]
  constructor
  · intro h
    have hv := congrArg (fun M => M *ᵥ Ω) h
    simp only [← Matrix.mulVec_mulVec, Eop_mulVec, Matrix.mulVec_smul, Ω_norm] at hv
    set c := star Ω ⬝ᵥ ((U ⊗ₖ U) *ᵥ Ω)
    have hc : (U ⊗ₖ U) *ᵥ Ω = c • Ω := by
      have : (4 : ℂ) • ((U ⊗ₖ U) *ᵥ Ω) = (4 : ℂ) • (c • Ω) := by
        rw [smul_smul]
        simpa using hv
      exact smul_right_injective _ (by norm_num) this
    have hJ : U * J * Uᵀ = c • J := by
      rw [kron_mulVec_Ω, Ω, ← relOf_smul] at hc
      have h' := relOf_injective hc
      rw [MΩ, Matrix.mul_smul, Matrix.smul_mul, smul_comm] at h'
      exact smul_right_injective _ (by norm_num) h'
    have hc2 := sq_eq_det_of_keeps_J_up_to U c hJ
    rw [hdet] at hc2
    have hfac : (c - 1) * (c + 1) = 0 := by linear_combination hc2
    rcases mul_eq_zero.mp hfac with h1 | h1
    · left
      rw [hJ, sub_eq_zero.mp h1, one_smul]
    · right
      rw [hJ, eq_neg_of_add_eq_zero_left h1, neg_one_smul]
  · intro h
    obtain ⟨ε, hε, hεs, hJ⟩ : ∃ ε : ℂ, ε * ε = 1 ∧ star ε = ε ∧ U * J * Uᵀ = ε • J := by
      rcases h with h | h
      · exact ⟨1, by norm_num, by simp, by rw [h, one_smul]⟩
      · exact ⟨-1, by norm_num, by simp, by rw [h, neg_one_smul]⟩
    have hv : (U ⊗ₖ U) *ᵥ Ω = ε • Ω := by
      rw [kron_mulVec_Ω, Ω, MΩ, Matrix.mul_smul, Matrix.smul_mul, hJ, smul_comm, relOf_smul]
    have hv' : (U ⊗ₖ U)ᴴ *ᵥ Ω = ε • Ω := by
      have h1 := congrArg (fun w => (U ⊗ₖ U)ᴴ *ᵥ w) hv
      simp only [Matrix.mulVec_mulVec, kron_unitary U hU, Matrix.one_mulVec,
        Matrix.mulVec_smul] at h1
      calc (U ⊗ₖ U)ᴴ *ᵥ Ω = (ε * ε) • ((U ⊗ₖ U)ᴴ *ᵥ Ω) := by rw [hε, one_smul]
        _ = ε • (ε • ((U ⊗ₖ U)ᴴ *ᵥ Ω)) := by rw [smul_smul]
        _ = ε • Ω := by rw [← h1]
    have hw : star Ω ᵥ* (U ⊗ₖ U) = ε • star Ω := by
      have h2 := Matrix.star_mulVec ((U ⊗ₖ U)ᴴ) Ω
      rw [Matrix.conjTranspose_conjTranspose, hv', star_smul, hεs] at h2
      exact h2.symm
    rw [mul_Eop, Eop_mul, hv, hw]
    ext p q
    simp only [Matrix.of_apply, Pi.smul_apply, Pi.star_apply, smul_eq_mul]
    ring

/-- `U J Uᵀ = −J` exactly when `i U` keeps the join: the second set is `i·Sp(2)`. -/
theorem neg_iff_I_smul (U : Matrix Four Four ℂ) :
    U * J * Uᵀ = -J ↔ (I • U) * J * (I • U)ᵀ = J := by
  have h : (I • U) * J * (I • U)ᵀ = -(U * J * Uᵀ) := by
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      Complex.I_mul_I, neg_one_smul]
  rw [h, neg_eq_iff_eq_neg]

end Comparison

end
