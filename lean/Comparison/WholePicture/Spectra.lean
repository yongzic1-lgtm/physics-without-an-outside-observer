module

public import Mathlib

/-!
# The whole picture: spectra of symmetric matrices from finite data

Tools for statements 6 and 11: a real symmetric
matrix killed by a polynomial has its eigenvalues among the roots; the characteristic polynomial is
then the product over the roots with the multiplicities counted, and the trace and the rank read
those counts.

* `eig_root_quadratic`, `eig_root_cubic`: `A² + aA + b = 0` (resp. the cubic) puts every eigenvalue
  on a root.
* `charpoly_of_values`: `det(X − A) = Π_{x ∈ s} (X − x)^{#{i : λ_i = x}}` when every `λ_i ∈ s`.
* `trace_of_values`: `tr A = Σ_{x ∈ s} x · #{i : λ_i = x}`; `card_of_values`: the counts add to
  `|n|`; `rank_of_values`: `rank A = Σ_{x ∈ s, x ≠ 0} #{i : λ_i = x}`.
-/

@[expose] public section

namespace Comparison.WholePicture

open Matrix Polynomial

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem eigvec_ne_zero {A : Matrix n n ℝ} (hA : A.IsHermitian) (i : n) :
    (⇑(hA.eigenvectorBasis i) : n → ℝ) ≠ 0 :=
  (WithLp.ofLp_eq_zero 2).ne.2 (hA.eigenvectorBasis.orthonormal.ne_zero i)

/-- **A quadratic that kills a symmetric matrix kills each eigenvalue.** -/
theorem eig_root_quadratic {A : Matrix n n ℝ} (hA : A.IsHermitian) (a b : ℝ)
    (h : A * A + a • A + b • (1 : Matrix n n ℝ) = 0) (i : n) :
    hA.eigenvalues i ^ 2 + a * hA.eigenvalues i + b = 0 := by
  set v : n → ℝ := ⇑(hA.eigenvectorBasis i)
  set μ := hA.eigenvalues i
  have hv : A *ᵥ v = μ • v := hA.mulVec_eigenvectorBasis i
  have hv0 : v ≠ 0 := eigvec_ne_zero hA i
  have h2 : (A * A) *ᵥ v = (μ ^ 2) • v := by
    rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, hv, smul_smul, sq]
  have hz := congrArg (fun M => M *ᵥ v) h
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec,
    h2, hv] at hz
  have h0 : (μ ^ 2 + a * μ + b) • v = 0 := by
    rw [← hz]
    module
  rcases smul_eq_zero.mp h0 with h' | h'
  · exact h'
  · exact absurd h' hv0

/-- **A cubic that kills a symmetric matrix kills each eigenvalue.** -/
theorem eig_root_cubic {A : Matrix n n ℝ} (hA : A.IsHermitian) (a b c : ℝ)
    (h : A * A * A + a • (A * A) + b • A + c • (1 : Matrix n n ℝ) = 0) (i : n) :
    hA.eigenvalues i ^ 3 + a * hA.eigenvalues i ^ 2 + b * hA.eigenvalues i + c = 0 := by
  set v : n → ℝ := ⇑(hA.eigenvectorBasis i)
  set μ := hA.eigenvalues i
  have hv : A *ᵥ v = μ • v := hA.mulVec_eigenvectorBasis i
  have hv0 : v ≠ 0 := eigvec_ne_zero hA i
  have h2 : (A * A) *ᵥ v = (μ ^ 2) • v := by
    rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, hv, smul_smul, sq]
  have h3 : (A * A * A) *ᵥ v = (μ ^ 3) • v := by
    rw [← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, h2, smul_smul]
    congr 1
    ring
  have hz := congrArg (fun M => M *ᵥ v) h
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec,
    h2, h3, hv] at hz
  have h0 : (μ ^ 3 + a * μ ^ 2 + b * μ + c) • v = 0 := by
    rw [← hz]
    module
  rcases smul_eq_zero.mp h0 with h' | h'
  · exact h'
  · exact absurd h' hv0

/-- **The characteristic polynomial from the eigenvalue counts:** if every eigenvalue lies in `s`,
`det(X − A) = Π_{x ∈ s} (X − x)^{#{i : λ_i = x}}`. -/
theorem charpoly_of_values {A : Matrix n n ℝ} (hA : A.IsHermitian) (s : Finset ℝ)
    (hs : ∀ i, hA.eigenvalues i ∈ s) :
    A.charpoly = ∏ x ∈ s, (X - C x) ^ (Finset.univ.filter fun i => hA.eigenvalues i = x).card := by
  rw [hA.charpoly_eq]
  simp only [RCLike.ofReal_real_eq_id, id]
  rw [← Finset.prod_fiberwise_of_maps_to (g := hA.eigenvalues) (t := s) (fun i _ => hs i)]
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [Finset.prod_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2]), Finset.prod_const]

/-- **The trace from the eigenvalue counts.** -/
theorem trace_of_values {A : Matrix n n ℝ} (hA : A.IsHermitian) (s : Finset ℝ)
    (hs : ∀ i, hA.eigenvalues i ∈ s) :
    A.trace = ∑ x ∈ s, x * (Finset.univ.filter fun i => hA.eigenvalues i = x).card := by
  rw [hA.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id]
  rw [← Finset.sum_fiberwise_of_maps_to (g := hA.eigenvalues) (t := s) (fun i _ => hs i)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_congr rfl (fun i hi => by rw [(Finset.mem_filter.mp hi).2]), Finset.sum_const,
    nsmul_eq_mul, mul_comm]

/-- **The counts add to the dimension.** -/
theorem card_of_values {A : Matrix n n ℝ} (hA : A.IsHermitian) (s : Finset ℝ)
    (hs : ∀ i, hA.eigenvalues i ∈ s) :
    ∑ x ∈ s, (Finset.univ.filter fun i => hA.eigenvalues i = x).card = Fintype.card n := by
  rw [← Finset.card_univ, ← Finset.card_eq_sum_card_fiberwise (fun i _ => hs i)]

/-- **The rank from the eigenvalue counts:** the nonzero eigenvalues. -/
theorem rank_of_values {A : Matrix n n ℝ} (hA : A.IsHermitian) (s : Finset ℝ)
    (hs : ∀ i, hA.eigenvalues i ∈ s) :
    A.rank = ∑ x ∈ s.erase 0, (Finset.univ.filter fun i => hA.eigenvalues i = x).card := by
  rw [hA.rank_eq_card_non_zero_eigs, Fintype.card_subtype,
    Finset.card_eq_sum_card_fiberwise (f := hA.eigenvalues) (t := s.erase 0)
      (fun i hi => by
        simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hi
        exact Finset.mem_erase.mpr ⟨hi, hs i⟩)]
  refine Finset.sum_congr rfl fun x hx => ?_
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    rw [h]
    exact Finset.ne_of_mem_erase hx

end Comparison.WholePicture

end
