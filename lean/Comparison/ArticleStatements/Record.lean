import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# A record is part of the comparison
# (statement 37, the record sum and the detection probability)

Statement 37: `P_record = Σ_(a,b) A_a conj(A_b) ⟨r_b|r_a⟩`, `P_detect = Tr(G†FGρ)`, `ρ = XX†`, `F = YY†`:
the cofactor carries the record of a state `Σ_a A_a |a⟩|r_a⟩`, identical records add amplitudes, orthogonal
records add counts, and the doubled kernel represents preparation and detection by `‖Y†GX‖²`.

* `Prec_eq_norm`: **`P_record = ‖Σ_a A_a r_a‖²`**, the squared length of the recorded state.
* `Prec_orthonormal`: **orthogonal records add counts**, `P_record = Σ_a |A_a|²`.
* `Prec_identical`: **identical records add amplitudes**, `P_record = |Σ_a A_a|²`.
* `Pdetect_eq`: **`Tr(G†FGρ) = Tr((Y†GX)†(Y†GX)) = ‖Y†GX‖²`** for `ρ = XX†`, `F = YY†`.

The cofactor identity `V†T^(⊗3)V = (adj T)ᵀ` itself is not proved here.
-/

open Matrix

namespace Comparison.ArticleStatements.Record

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- **The record sum** `P_record = Σ_(a,b) A_a conj(A_b) ⟨r_b|r_a⟩`. -/
noncomputable def Prec (A : ι → ℂ) (r : ι → κ → ℂ) : ℂ :=
  ∑ a, ∑ b, A a * star (A b) * (star (r b) ⬝ᵥ r a)

/-- **`P_record = ‖Σ_a A_a r_a‖²`.** -/
theorem Prec_eq_norm (A : ι → ℂ) (r : ι → κ → ℂ) :
    Prec A r = star (∑ b, A b • r b) ⬝ᵥ (∑ a, A a • r a) := by
  have hs : star (∑ b, A b • r b) = ∑ b, star (A b) • star (r b) := by
    ext k
    simp [Finset.sum_apply, star_sum, star_mul']
  rw [Prec, hs, sum_dotProduct, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [dotProduct_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- **Orthogonal records add counts:** `P_record = Σ_a A_a conj(A_a)`. -/
theorem Prec_orthonormal [DecidableEq ι] (A : ι → ℂ) (r : ι → κ → ℂ)
    (hr : ∀ a b, star (r b) ⬝ᵥ r a = if a = b then 1 else 0) :
    Prec A r = ∑ a, A a * star (A a) := by
  rw [Prec]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [hr, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

/-- **Identical records add amplitudes:** with one unit record `s`, `P_record = (Σ_a A_a) conj(Σ_a A_a)`. -/
theorem Prec_identical (A : ι → ℂ) (s : κ → ℂ) (hs : star s ⬝ᵥ s = 1) :
    Prec A (fun _ => s) = (∑ a, A a) * star (∑ a, A a) := by
  simp only [Prec]
  rw [star_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hs, mul_one]

/-- **The doubled kernel's detection probability is a squared length:**
`Tr(G†FGρ) = Tr((Y†GX)†(Y†GX))` for `ρ = XX†`, `F = YY†`. -/
theorem Pdetect_eq {n p q : Type*} [Fintype n] [Fintype p] [Fintype q]
    (G : Matrix n n ℂ) (X : Matrix n p ℂ) (Y : Matrix n q ℂ) :
    (Gᴴ * (Y * Yᴴ) * G * (X * Xᴴ)).trace = ((Yᴴ * G * X)ᴴ * (Yᴴ * G * X)).trace := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have e : Gᴴ * (Y * Yᴴ) * G * (X * Xᴴ) = (Gᴴ * Y * (Yᴴ * G * X)) * Xᴴ := by
    simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- The squared length is a sum of squared moduli: `Tr(M†M) = Σ_(i,j) |M_ij|²`. -/
theorem trace_conjTranspose_mul_self {p q : Type*} [Fintype p] [Fintype q] (M : Matrix p q ℂ) :
    (Mᴴ * M).trace = ∑ j, ∑ i, star (M i j) * M i j := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply]

end Comparison.ArticleStatements.Record

#print axioms Comparison.ArticleStatements.Record.Prec_eq_norm
#print axioms Comparison.ArticleStatements.Record.Prec_orthonormal
#print axioms Comparison.ArticleStatements.Record.Prec_identical
#print axioms Comparison.ArticleStatements.Record.Pdetect_eq
#print axioms Comparison.ArticleStatements.Record.trace_conjTranspose_mul_self
