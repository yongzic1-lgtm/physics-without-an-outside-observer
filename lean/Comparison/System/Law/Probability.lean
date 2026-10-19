import Comparison.System.Postulates
import Comparison.Existence.Born

/-!
# The proof system, the law: Proposition 58, probability

`K` an invertible operator, `G = K⁻¹`, a preparation `X`
and a detection `Y`; the doubled operator `𝔻(s, t) = [[K, −sXX†], [−tYY†, K†]]`.

* `doubled_log_deriv_t`: for every `s`, `t ↦ −log det 𝔻(s, t)` has the derivative `s·tr(G†YY†GXX†)` at
  `t = 0`;
* `prop_58`: **`∂_s∂_t[−log det 𝔻]_{s=t=0} = tr(G†YY†GXX†) = ‖Y†GX‖² ≥ 0`**: the function
  `s ↦ ∂_t[−log det 𝔻(s, t)]_{t=0}` has the derivative `tr(G†YY†GXX†)` at `s = 0`, and that trace is the sum of
  the squared sizes of the entries of `Y†GX`.
-/

open Matrix Comparison Filter Topology

namespace Comparison.System

namespace Law

variable {n p q : Type*} [Fintype n] [Fintype p] [Fintype q] [DecidableEq n] [DecidableEq p]
  [DecidableEq q]

/-- `det(1 − x M)` is continuous in `x`. -/
theorem continuous_det_one_sub_smul (M : Matrix n n ℂ) :
    Continuous (fun x : ℂ => (1 - x • M).det) := by
  have : (fun x : ℂ => (1 - x • M).det) =
      fun x => ((1 - (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C).det).eval x := by
    funext x
    exact det_one_sub_smul_poly M x
  rw [this]
  exact Polynomial.continuous _

/-- **For every `s`, `∂_t[−log det 𝔻(s, t)]_{t=0} = s·tr(G†YY†GXX†)`.** -/
theorem doubled_log_deriv_t (K : Matrix n n ℂ) [Invertible K] (X : Matrix n p ℂ) (Y : Matrix n q ℂ)
    (s : ℂ) :
    HasDerivAt (fun t : ℂ => -Complex.log (doubled K X Y s t).det) (s * (bornM K X Y).trace) 0 := by
  -- near `t = 0`, `det(1 − tsM)` is near `1`, so it is not zero
  have hc : Continuous (fun t : ℂ => (1 - (t * s) • (bornM K X Y)).det) :=
    (continuous_det_one_sub_smul (bornM K X Y)).comp
      (continuous_id.mul continuous_const : Continuous fun t : ℂ => t * s)
  have h0 : (fun t : ℂ => (1 - (t * s) • (bornM K X Y)).det) 0 ≠ 0 := by simp
  have hne : ∀ᶠ t in 𝓝 (0 : ℂ), (1 - (t * s) • (bornM K X Y)).det ≠ 0 :=
    hc.continuousAt.eventually_ne h0
  have heq : (fun t : ℂ => -Complex.log (doubled K X Y s t).det) =ᶠ[𝓝 0]
      fun t => -(Real.log (Complex.normSq K.det) : ℂ) - Complex.log (1 - (s * t) • (bornM K X Y)).det := by
    filter_upwards [hne] with t ht
    rw [log_doubled K X Y s t ht, mul_comm t s]
  have hb := (born_mixed (bornM K X Y)).1 s
  have hd : HasDerivAt (fun t : ℂ => -(Real.log (Complex.normSq K.det) : ℂ) -
      Complex.log (1 - (s * t) • (bornM K X Y)).det) (s * (bornM K X Y).trace) 0 := by
    refine (hb.const_add (-(Real.log (Complex.normSq K.det) : ℂ))).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => ?_)
    simp only [sub_eq_add_neg]
  exact hd.congr_of_eventuallyEq heq

end Law

open Comparison.System.Law

/-- **Proposition 58, probability.** For an invertible `K`, `G = K⁻¹`, a preparation `X` and a detection `Y`:
for every `s` the derivative `∂_t[−log det 𝔻(s, t)]` at `t = 0` is `s·tr(G†YY†GXX†)`; the function
`s ↦ ∂_t[−log det 𝔻(s, t)]_{t=0}` has the derivative `tr(G†YY†GXX†)` at `s = 0`; this trace is
`‖Y†GX‖² = Σ |(Y†GX)_{ij}|²`, a non-negative real number. -/
theorem prop_58 {n p q : Type*} [Fintype n] [Fintype p] [Fintype q] [DecidableEq n] [DecidableEq p]
    [DecidableEq q] (K : Matrix n n ℂ) [Invertible K] (X : Matrix n p ℂ) (Y : Matrix n q ℂ) :
    (∀ s : ℂ, HasDerivAt (fun t : ℂ => -Complex.log (doubled K X Y s t).det)
      (s * (bornM K X Y).trace) 0) ∧
    HasDerivAt (fun s : ℂ => deriv (fun t : ℂ => -Complex.log (doubled K X Y s t).det) 0)
      (bornM K X Y).trace 0 ∧
    (bornM K X Y).trace = ((∑ i, ∑ j, Complex.normSq ((Yᴴ * ⅟K * X) i j) : ℝ) : ℂ) ∧
    0 ≤ ∑ i, ∑ j, Complex.normSq ((Yᴴ * ⅟K * X) i j) := by
  refine ⟨doubled_log_deriv_t K X Y, ?_, bornM_trace K X Y, bornM_trace_nonneg K X Y⟩
  have e : (fun s : ℂ => deriv (fun t : ℂ => -Complex.log (doubled K X Y s t).det) 0) =
      fun s => s * (bornM K X Y).trace := by
    funext s
    exact (doubled_log_deriv_t K X Y s).deriv
  rw [e]
  simpa using (hasDerivAt_id (0 : ℂ)).mul_const (bornM K X Y).trace

end Comparison.System
