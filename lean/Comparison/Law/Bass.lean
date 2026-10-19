module

public import Comparison.Law.Meetings

/-!
# The law, X: Bass's identity with the lines' weights (Proposition 161, the vertex form)

* `ihara_bass_weighted`: **for five operators with scalar squares, `Γ_t² = c_t`,**
  `∏_t det(1 − uΓ_t) · det(1 − uB) = ∏_t (1 − u²c_t)^{|V|} · det(1 − Σ_t u(Γ_t − uc_t)/(1 − u²c_t))`
  wherever every `1 − u²c_t ≠ 0` (Book X's `ihara_bass` is the case `c_t = 1`).
* `bass_line_weights`: **with a weight `w_t` on the steps along each line `t`, the same at every
  vertex,** `det(I − uB_w) = ∏_links det(1 − u²W_eW_ē) · det(I − Â + D̂)` on the sixteen vertices, with
  `∏_links = ∏_t (1 − u²w_t²)⁸` (eight links along each line), `Â = Σ_t u(1 − u²w_t²)⁻¹ w_t X_t` and
  `D̂ = Σ_t u²(1 − u²w_t²)⁻¹ w_t²`: the eighty-state law is the law at the vertices, weight by weight.
-/

@[expose] public section

namespace Comparison

open Matrix

namespace Law

section Weighted

variable {K : Type*} [Field K] {V : Type*} [Fintype V] [DecidableEq V]

/-- **Bass's identity for five operators with scalar squares.** -/
theorem ihara_bass_weighted (Γ : Fin 5 → Matrix V V K) (c : Fin 5 → K)
    (hΓ : ∀ t, Γ t * Γ t = c t • 1) (u : K) (hc : ∀ t, 1 - u ^ 2 * c t ≠ 0) :
    (∏ t, (1 - u • Γ t).det) * (1 - u • stepOp Γ).det =
      (∏ t, (1 - u ^ 2 * c t) ^ Fintype.card V) *
        (1 - ∑ t, (u / (1 - u ^ 2 * c t)) • (Γ t - (u * c t) • 1)).det := by
  set bd := blockDiagonal Γ with hbd
  have hbd2 : bd * bd = blockDiagonal fun t => c t • (1 : Matrix V V K) := by
    rw [hbd, ← blockDiagonal_mul]
    simp only [hΓ]
  have hdetG : (1 - u • bd).det = ∏ t, (1 - u • Γ t).det := by
    have h : (blockDiagonal fun t => 1 - u • Γ t) = 1 - u • bd := by
      rw [hbd, show (fun t => 1 - u • Γ t) = (1 : Fin 5 → Matrix V V K) - u • Γ from rfl,
        blockDiagonal_sub, blockDiagonal_one, blockDiagonal_smul]
    rw [← h, det_blockDiagonal]
  set E : Matrix (V × Fin 5) (V × Fin 5) K :=
    blockDiagonal fun t => (1 - u ^ 2 * c t) • (1 : Matrix V V K) with hE
  set Einv : Matrix (V × Fin 5) (V × Fin 5) K :=
    blockDiagonal fun t => (1 - u ^ 2 * c t)⁻¹ • (1 : Matrix V V K) with hEinv
  have hEEinv : E * Einv = 1 := by
    rw [hE, hEinv, ← blockDiagonal_mul]
    have : (fun t => (1 - u ^ 2 * c t) • (1 : Matrix V V K) * (1 - u ^ 2 * c t)⁻¹ • 1) =
        fun _ => 1 := by
      funext t
      rw [smul_mul_smul_comm, Matrix.one_mul, mul_inv_cancel₀ (hc t), one_smul]
    rw [this]
    exact blockDiagonal_one
  have hEeq : E = 1 - u ^ 2 • (bd * bd) := by
    rw [hbd2, hE]
    ext ⟨i, a⟩ ⟨j, b⟩
    simp only [blockDiagonal_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.sub_apply,
      Prod.mk.injEq, smul_eq_mul]
    by_cases hab : a = b
    · subst hab
      by_cases hij : i = j <;> simp [hij]
    · simp [hab]
  have hdetE : E.det = ∏ t, (1 - u ^ 2 * c t) ^ Fintype.card V := by
    rw [hE, det_blockDiagonal]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [det_smul, det_one, mul_one]
  have hprod : (1 - u • bd) * (1 - u • stepOp Γ) =
      E * (1 - (Einv * (u • (bd - u • (bd * bd)) * colX V K)) * rowY V K) := by
    have hL : (1 - u • bd) * (1 - u • stepOp Γ) =
        E - (u • (bd - u • (bd * bd)) * colX V K) * rowY V K := by
      rw [stepOp_eq, hEeq]
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.mul_assoc, smul_sub, smul_smul]
      rw [← hbd]
      simp only [← Matrix.mul_assoc]
      module
    rw [hL, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hEEinv,
      Matrix.one_mul, Matrix.mul_assoc]
  have hcollapse : rowY V K * (Einv * (u • (bd - u • (bd * bd)) * colX V K)) =
      ∑ t, (u / (1 - u ^ 2 * c t)) • (Γ t - (u * c t) • 1) := by
    have hblk : Einv * (u • (bd - u • (bd * bd))) =
        blockDiagonal fun t => (u / (1 - u ^ 2 * c t)) • (Γ t - (u * c t) • 1) := by
      rw [hbd2, hEinv, hbd, Matrix.mul_smul, Matrix.mul_sub, ← blockDiagonal_mul,
        ← blockDiagonal_smul, ← blockDiagonal_mul, ← blockDiagonal_sub, ← blockDiagonal_smul]
      congr 1
      funext t
      simp only [Pi.smul_apply, Pi.sub_apply, smul_mul_smul_comm, Matrix.smul_mul, Matrix.one_mul,
        smul_sub, smul_smul, div_eq_mul_inv]
      ext i j
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> ring
    rw [← Matrix.mul_assoc Einv, hblk, ← Matrix.mul_assoc, rowY_blockDiagonal_colX]
  have h := congrArg Matrix.det hprod
  rw [det_mul, det_mul, hdetG, det_one_sub_mul_comm, hcollapse, hdetE] at h
  exact h

end Weighted

/-- **Bass's identity with a weight on the steps along each line** (Proposition 161, the vertex form):
`det(I − uB_w) = ∏_t (1 − u²w_t²)⁸ · det(I − Â + D̂)` on the sixteen vertices,
`Â = Σ_t u(1 − u²w_t²)⁻¹ w_t X_t`, `D̂ = Σ_t u²(1 − u²w_t²)⁻¹ w_t²`. -/
theorem bass_line_weights (w : Fin 5 → ℂ) (u : ℂ) (hc : ∀ t, 1 - u ^ 2 * w t ^ 2 ≠ 0) :
    (1 - u • stepOp (fun t => w t • transitionMat t)).det =
      (∏ t, (1 - u ^ 2 * w t ^ 2) ^ 8) *
        (1 - ∑ t, (u / (1 - u ^ 2 * w t ^ 2) * w t) • transitionMat t +
          (∑ t, u ^ 2 / (1 - u ^ 2 * w t ^ 2) * w t ^ 2) • (1 : Matrix (Fin 16) (Fin 16) ℂ)).det := by
  have hsq : ∀ t, (w t • transitionMat t) * (w t • transitionMat t) = (w t ^ 2) • 1 := by
    intro t
    rw [smul_mul_smul_comm, transitionMat_mul_self, sq]
  have h := ihara_bass_weighted (fun t => w t • transitionMat t) (fun t => w t ^ 2) hsq u hc
  have hΓ : ∀ t, (1 - u • (w t • transitionMat t)).det = (1 - u ^ 2 * w t ^ 2) ^ 8 := by
    intro t
    rw [smul_smul, det_one_sub_transitionMat]
    ring
  simp only [hΓ, Fintype.card_fin] at h
  have hprod_ne : (∏ t, (1 - u ^ 2 * w t ^ 2) ^ 8) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun t _ => pow_ne_zero _ (hc t)
  have hpow : (∏ t, (1 - u ^ 2 * w t ^ 2) ^ 16) =
      (∏ t, (1 - u ^ 2 * w t ^ 2) ^ 8) * (∏ t, (1 - u ^ 2 * w t ^ 2) ^ 8) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun t _ => ?_
    ring
  have hmat : (1 - ∑ t, (u / (1 - u ^ 2 * w t ^ 2)) • (w t • transitionMat t - (u * w t ^ 2) • 1) :
        Matrix (Fin 16) (Fin 16) ℂ) =
      1 - ∑ t, (u / (1 - u ^ 2 * w t ^ 2) * w t) • transitionMat t +
        (∑ t, u ^ 2 / (1 - u ^ 2 * w t ^ 2) * w t ^ 2) • (1 : Matrix (Fin 16) (Fin 16) ℂ) := by
    simp only [smul_sub, smul_smul, Finset.sum_sub_distrib, Finset.sum_smul]
    have e : ∀ t, u / (1 - u ^ 2 * w t ^ 2) * (u * w t ^ 2) = u ^ 2 / (1 - u ^ 2 * w t ^ 2) * w t ^ 2 := by
      intro t
      ring
    simp only [e]
    abel
  rw [hpow, hmat] at h
  exact mul_left_cancel₀ hprod_ne (by linear_combination h)

end Law

end Comparison

end
