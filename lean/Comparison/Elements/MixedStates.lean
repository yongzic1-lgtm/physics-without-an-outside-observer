module

public import Comparison.Elements.TwoThings

/-!
# Book II, Proposition 12 for mixed states

A mixed state of one system is a positive semidefinite `ρ` with `tr ρ = 1`; its line is
`m_s(ρ) = Re tr(ρ γ_s)`.

* `sum_mixedLine_sq_le`: `|m(ρ)|² ≤ 1`.
* `trace_prod_disagreement`: `tr[(ρ ⊗ σ)(6 − L)] = 5 − m(ρ)·m(σ)`.
* `disagreement_mixed_ge`: two mixed states taken separately disagree by at least `4`.
* `disagreement_mixture_ge`: so does every mixture of such pairs.
-/

@[expose] public section

namespace Comparison

open Matrix hiding J
open Complex Kronecker
open scoped ComplexOrder

/-- The line of a mixed state: `m_s(ρ) = Re tr(ρ γ_s)`. -/
noncomputable def mixedLine (ρ : Matrix Four Four ℂ) (s : Fin 5) : ℝ := (ρ * γ s).trace.re

theorem trace_mul_γ_eq (ρ : Matrix Four Four ℂ) (hρ : ρᴴ = ρ) (s : Fin 5) :
    (ρ * γ s).trace = (mixedLine ρ s : ℂ) :=
  (trace_mul_re_of_hermitian hρ (γ_conjTranspose s)).symm

/-- **The line of a mixed state has length at most one.** -/
theorem sum_mixedLine_sq_le (ρ : Matrix Four Four ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    ∑ s, mixedLine ρ s ^ 2 ≤ 1 := by
  set m := mixedLine ρ with hm
  set G : Matrix Four Four ℂ := ∑ s, (m s : ℂ) • γ s with hG
  have hH : ρᴴ = ρ := hρ.isHermitian
  have hGH : Gᴴ = G := by
    simp [hG, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, γ_conjTranspose]
  have hG2 : G * G = ((∑ s, m s ^ 2 : ℝ) : ℂ) • (1 : Matrix Four Four ℂ) := by
    rw [hG, sq_sum]
    push_cast
    rfl
  have hpsd := hρ.conjTranspose_mul_mul_same (1 - G)
  have hnn := hpsd.trace_nonneg
  have hBB : (1 - G) * (1 - G)ᴴ =
      ((1 + ∑ s, m s ^ 2 : ℝ) : ℂ) • (1 : Matrix Four Four ℂ) - (2 : ℂ) • G := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hGH, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hG2]
    push_cast
    module
  have htrG : (ρ * G).trace = ((∑ s, m s ^ 2 : ℝ) : ℂ) := by
    rw [hG, Matrix.mul_sum, Matrix.trace_sum]
    push_cast
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Matrix.mul_smul, Matrix.trace_smul, trace_mul_γ_eq ρ hH s, smul_eq_mul, sq]
  have key : ((1 - G)ᴴ * ρ * (1 - G)).trace = ((1 - ∑ s, m s ^ 2 : ℝ) : ℂ) := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm, hBB, Matrix.mul_sub,
      Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_sub, Matrix.trace_smul,
      Matrix.trace_smul, htr, htrG]
    push_cast
    simp only [smul_eq_mul]
    ring
  rw [key] at hnn
  have := Complex.le_def.mp hnn
  simp only [Complex.zero_re, Complex.ofReal_re] at this
  linarith [this.1]

theorem trace_kron_mul_kron (A B C D : Matrix Four Four ℂ) :
    ((A ⊗ₖ B) * (C ⊗ₖ D)).trace = (A * C).trace * (B * D).trace := by
  rw [← mul_kronecker_mul, trace_kronecker]

/-- **The disagreement of two mixed states taken separately** is `5 − m(ρ)·m(σ)`. -/
theorem trace_prod_disagreement (ρ σ : Matrix Four Four ℂ) (hρ : ρᴴ = ρ) (hσ : σᴴ = σ)
    (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) :
    ((ρ ⊗ₖ σ) * disagreement).trace =
      ((5 - ∑ s, mixedLine ρ s * mixedLine σ s : ℝ) : ℂ) := by
  rw [disagreement, L, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_add,
    Matrix.mul_sum, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_sum,
    trace_kronecker, trace_kron_mul_kron, Matrix.mul_one, Matrix.mul_one, hρ1, hσ1]
  simp only [trace_kron_mul_kron, trace_mul_γ_eq ρ hρ, trace_mul_γ_eq σ hσ]
  push_cast
  simp only [smul_eq_mul]
  ring

/-- **Two mixed states taken separately disagree by at least four.** -/
theorem disagreement_mixed_ge (ρ σ : Matrix Four Four ℂ) (hρ : ρ.PosSemidef)
    (hσ : σ.PosSemidef) (hρ1 : ρ.trace = 1) (hσ1 : σ.trace = 1) :
    4 ≤ ((ρ ⊗ₖ σ) * disagreement).trace.re := by
  rw [trace_prod_disagreement ρ σ hρ.isHermitian hσ.isHermitian hρ1 hσ1, Complex.ofReal_re]
  have h1 := sum_mixedLine_sq_le ρ hρ hρ1
  have h2 := sum_mixedLine_sq_le σ hσ hσ1
  have h3 : ∑ s, mixedLine ρ s * mixedLine σ s ≤
      (∑ s, mixedLine ρ s ^ 2 + ∑ s, mixedLine σ s ^ 2) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_le_sum fun s _ => ?_
    nlinarith [sq_nonneg (mixedLine ρ s - mixedLine σ s)]
  linarith

/-- **Every mixture of pairs prepared apart disagrees by at least four.** -/
theorem disagreement_mixture_ge {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hp1 : ∑ i, p i = 1) (ρ σ : ι → Matrix Four Four ℂ) (hρ : ∀ i, (ρ i).PosSemidef)
    (hσ : ∀ i, (σ i).PosSemidef) (hρ1 : ∀ i, (ρ i).trace = 1) (hσ1 : ∀ i, (σ i).trace = 1) :
    4 ≤ ((∑ i, (p i : ℂ) • (ρ i ⊗ₖ σ i)) * disagreement).trace.re := by
  rw [Finset.sum_mul, Matrix.trace_sum, Complex.re_sum]
  simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.re_ofReal_mul]
  calc (4 : ℝ) = ∑ i, p i * 4 := by rw [← Finset.sum_mul, hp1, one_mul]
    _ ≤ ∑ i, p i * ((ρ i ⊗ₖ σ i) * disagreement).trace.re :=
        Finset.sum_le_sum fun i _ =>
          mul_le_mul_of_nonneg_left (disagreement_mixed_ge _ _ (hρ i) (hσ i) (hρ1 i) (hσ1 i))
            (hp i)

end Comparison

end
