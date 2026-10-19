import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The geometry of comparison: `det e^A = e^{tr A}`

For every complex square matrix `A`,
`det (exp A) = exp (tr A)` (`det_exp`), the identity that puts the exponentials of the trace-zero
generators of a real form into its group of determinant one (Prop. 21, the real forms as groups).

The proof: `f(t) = det e^{tA}` has `f(s + t) = f(s)f(t)`; at `t = 0` its derivative is `tr A`, since
`det` is the sum over the permutations of products of entries, `e^{tA} = 1 + tA + o(t)`, and only the
identity contributes at first order (a permutation fixing all points but one is the identity); so
`f′ = (tr A)f`, and `f(t)e^{−t tr A}` has derivative zero: it is `1`.
-/

open Matrix

namespace Comparison.System

namespace Geometry

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A permutation that fixes every point but one is the identity. -/
theorem perm_eq_one_of_fix_but (σ : Equiv.Perm n) (i : n) (h : ∀ j, j ≠ i → σ j = j) : σ = 1 := by
  have hi : σ i = i := by
    by_contra hne
    exact hne (σ.injective (h (σ i) hne))
  ext j
  by_cases hj : j = i
  · rw [hj, hi]; rfl
  · rw [h j hj]; rfl

/-- The entries of `e^{tA}` have the derivative `A i j` at `t = 0`. -/
theorem hasDerivAt_exp_smul_entry (A : Matrix n n ℂ) (i j : n) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp (t • A) i j) (A i j) 0 := by
  letI : NormedRing (Matrix n n ℂ) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℝ (Matrix n n ℂ) := Matrix.linftyOpNormedAlgebra
  haveI : CompleteSpace (Matrix n n ℂ) := FiniteDimensional.complete ℝ (Matrix n n ℂ)
  have h1 := hasDerivAt_exp_smul_const (𝕂 := ℝ) A (0 : ℝ)
  rw [zero_smul, NormedSpace.exp_zero, one_mul] at h1
  let L : Matrix n n ℂ →ₗ[ℝ] ℂ :=
    { toFun := fun M => M i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have h2 := (LinearMap.toContinuousLinearMap L).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
  exact h2

/-- **The derivative of `det e^{tA}` at `t = 0` is `tr A`.** -/
theorem hasDerivAt_det_exp_smul (A : Matrix n n ℂ) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp (t • A)).det) A.trace 0 := by
  have hP : HasDerivAt
      (fun t : ℝ => ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ i, NormedSpace.exp (t • A) (σ i) i)
      (∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∑ i, (∏ j ∈ Finset.univ.erase i, NormedSpace.exp ((0 : ℝ) • A) (σ j) j) • A (σ i) i) 0 := by
    apply HasDerivAt.fun_sum
    intro σ _
    exact (HasDerivAt.fun_finsetProd (f := fun i (t : ℝ) => NormedSpace.exp (t • A) (σ i) i)
      (fun i _ => hasDerivAt_exp_smul_entry A (σ i) i)).const_mul _
  have hdet : (fun t : ℝ => (NormedSpace.exp (t • A)).det) =
      fun t => ∑ σ : Equiv.Perm n, ((Equiv.Perm.sign σ : ℤ) : ℂ) *
        ∏ i, NormedSpace.exp (t • A) (σ i) i := by
    funext t
    rw [Matrix.det_apply']
  rw [hdet]
  convert hP using 1
  rw [zero_smul, NormedSpace.exp_zero]
  rw [Finset.sum_eq_single (1 : Equiv.Perm n)]
  · simp [Matrix.trace, Matrix.one_apply]
  · intro σ _ hσ
    rw [Finset.sum_eq_zero, mul_zero]
    intro i _
    by_cases hfix : ∀ j, j ≠ i → σ j = j
    · exact absurd (perm_eq_one_of_fix_but σ i hfix) hσ
    · push_neg at hfix
      obtain ⟨j, hji, hσj⟩ := hfix
      rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)]
      · simp
      · simp [Matrix.one_apply, hσj]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **`det e^A = e^{tr A}`** for every complex square matrix `A`. -/
theorem det_exp (A : Matrix n n ℂ) : (NormedSpace.exp A).det = Complex.exp A.trace := by
  set f : ℝ → ℂ := fun t => (NormedSpace.exp (t • A)).det with hf
  have hmul : ∀ s t : ℝ, f (s + t) = f s * f t := by
    intro s t
    simp only [hf, add_smul]
    rw [Matrix.exp_add_of_commute _ _ (((Commute.refl A).smul_left s).smul_right t), Matrix.det_mul]
  have hd : ∀ t : ℝ, HasDerivAt f (f t * A.trace) t := by
    intro t
    have h0 : HasDerivAt (fun h : ℝ => f t * f h) (f t * A.trace) (t - t) := by
      rw [sub_self]
      exact (hasDerivAt_det_exp_smul A).const_mul (f t)
    have h1 := HasDerivAt.comp_sub_const t t h0
    have heq : (fun x : ℝ => f t * f (x - t)) = f := by
      funext x
      rw [← hmul]
      congr 1
      ring
    rw [heq] at h1
    exact h1
  set c := A.trace with hc
  set g : ℝ → ℂ := fun t => f t * Complex.exp (-((t : ℂ) * c)) with hg
  have hgd : ∀ t : ℝ, HasDerivAt g 0 t := by
    intro t
    have hl : HasDerivAt (fun s : ℝ => -((s : ℂ) * c)) (-(((1 : ℝ) : ℂ) * c)) t :=
      ((hasDerivAt_id t).ofReal_comp.mul_const c).neg
    have he := hl.cexp
    have := (hd t).mul he
    convert this using 1
    push_cast
    ring
  have hconst := is_const_of_deriv_eq_zero (fun t => (hgd t).differentiableAt)
    (fun t => (hgd t).deriv) 1 0
  have hg0 : g 0 = 1 := by simp [hg, hf]
  have hg1 : g 1 = (NormedSpace.exp A).det * Complex.exp (-c) := by simp [hg, hf]
  rw [hg0, hg1] at hconst
  have e : (NormedSpace.exp A).det =
      (NormedSpace.exp A).det * Complex.exp (-c) * Complex.exp c := by
    rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
  rw [e, hconst, one_mul]

/-- The exponential of a trace-zero matrix has determinant one. -/
theorem det_exp_of_trace_zero (A : Matrix n n ℂ) (h : A.trace = 0) : (NormedSpace.exp A).det = 1 := by
  rw [det_exp, h, Complex.exp_zero]

end Geometry

end Comparison.System
