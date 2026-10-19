import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.RCLike.Basic

/-!
# The sector phase as a series
# (statement 36, Proposition 115)

The article's statement 36 writes the sum over the closed colour sectors as a series over all integer
charges, with nonnegative summable weights `a_q`, reciprocal under `q ↦ −q`:

    Z_top(θ) = Σ_(q∈ℤ) a_q e^(iqθ),   |Z_top(θ)| ≤ Z_top(0),   |Z_top(θ)| = Z_top(0) ⟹ e^(iθ) = 1,
    θ̄ = θ + arg det(M_uM_d).

ArticleStatements/SectorSum.lean proves this for a finite family of connections, with the weights built from
the law; this file proves it for every summable family of sector weights.

* `summable_term`, `summable_cos`, `summable_sin`: the series converge absolutely.
* `sin_tsum_zero`, `Ztop_eq_cos`: **`Z_top(θ) = Σ_q a_q cos(qθ)` is real** when `a_(−q) = a_q`.
* `Ztop_zero`: `Z_top(0) = Σ_q a_q`.
* `norm_Ztop_le`: **`|Z_top(θ)| ≤ Z_top(0)`** for nonnegative weights.
* `norm_Ztop_eq_iff`: **`|Z_top(θ)| = Z_top(0)` exactly when `θ ∈ 2πℤ`**, when `a_0 > 0` and `a_1 > 0`;
  `exp_eq_one_of_max`: then `e^(iθ) = 1`; `norm_Ztop_lt`: strictly smaller elsewhere.
* `theta_bar_series`: **with a positive mass determinant, `θ̄ = θ + arg det(M_uM_d) ∈ 2πℤ` where the sum
  over sectors is largest.**
-/

open scoped ComplexOrder

namespace Comparison.ArticleStatements.Series

/-- **The sum over sectors** `Z_top(θ) = Σ_(q∈ℤ) a_q e^(iqθ)`. -/
noncomputable def Ztop (a : ℤ → ℝ) (θ : ℝ) : ℂ :=
  ∑' q : ℤ, (a q : ℂ) * Complex.exp (((q : ℝ) * θ : ℝ) * Complex.I)

variable {a : ℤ → ℝ}

theorem norm_term (ha : ∀ q, 0 ≤ a q) (θ : ℝ) (q : ℤ) :
    ‖(a q : ℂ) * Complex.exp (((q : ℝ) * θ : ℝ) * Complex.I)‖ = a q := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_of_nonneg (ha q)]

theorem summable_term (ha : ∀ q, 0 ≤ a q) (hs : Summable a) (θ : ℝ) :
    Summable (fun q : ℤ => (a q : ℂ) * Complex.exp (((q : ℝ) * θ : ℝ) * Complex.I)) :=
  Summable.of_norm (hs.congr fun q => (norm_term ha θ q).symm)

theorem summable_cos (ha : ∀ q, 0 ≤ a q) (hs : Summable a) (θ : ℝ) :
    Summable (fun q : ℤ => a q * Real.cos (q * θ)) :=
  Summable.of_norm_bounded hs fun q => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha q)]
    exact mul_le_of_le_one_right (ha q) (Real.abs_cos_le_one _)

theorem summable_sin (ha : ∀ q, 0 ≤ a q) (hs : Summable a) (θ : ℝ) :
    Summable (fun q : ℤ => a q * Real.sin (q * θ)) :=
  Summable.of_norm_bounded hs fun q => by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (ha q)]
    exact mul_le_of_le_one_right (ha q) (Real.abs_sin_le_one _)

/-- The odd part cancels: `Σ_q a_q sin(qθ) = 0` when `a_(−q) = a_q`. -/
theorem sin_tsum_zero (hsym : ∀ q, a (-q) = a q) (θ : ℝ) :
    ∑' q : ℤ, a q * Real.sin (q * θ) = 0 := by
  have h : ∑' q : ℤ, a q * Real.sin (q * θ) = -∑' q : ℤ, a q * Real.sin (q * θ) := by
    rw [← tsum_neg, ← Equiv.tsum_eq (Equiv.neg ℤ)]
    refine tsum_congr fun q => ?_
    simp only [Equiv.neg_apply, hsym, Int.cast_neg, neg_mul, Real.sin_neg, mul_neg]
  linarith

/-- **`Z_top(θ) = Σ_q a_q cos(qθ)`, a real number.** -/
theorem Ztop_eq_cos (ha : ∀ q, 0 ≤ a q) (hs : Summable a) (hsym : ∀ q, a (-q) = a q) (θ : ℝ) :
    Ztop a θ = ((∑' q : ℤ, a q * Real.cos (q * θ) : ℝ) : ℂ) := by
  have h2 : HasSum (fun q : ℤ => (a q : ℂ) * Complex.exp (((q : ℝ) * θ : ℝ) * Complex.I))
      ((∑' q : ℤ, a q * Real.cos (q * θ) : ℝ) : ℂ) := by
    rw [Complex.hasSum_iff]
    constructor
    · have e : ∀ q : ℤ, ((a q : ℂ) * Complex.exp (((q : ℝ) * θ : ℝ) * Complex.I)).re =
          a q * Real.cos (q * θ) := by
        intro q
        rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
      simp only [e, Complex.ofReal_re]
      exact (summable_cos ha hs θ).hasSum
    · have e : ∀ q : ℤ, ((a q : ℂ) * Complex.exp (((q : ℝ) * θ : ℝ) * Complex.I)).im =
          a q * Real.sin (q * θ) := by
        intro q
        rw [Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
      simp only [e, Complex.ofReal_im]
      have h := (summable_sin ha hs θ).hasSum
      rwa [sin_tsum_zero hsym θ] at h
  exact h2.tsum_eq

/-- `Z_top(0) = Σ_q a_q`. -/
theorem Ztop_zero (ha : ∀ q, 0 ≤ a q) (hs : Summable a) (hsym : ∀ q, a (-q) = a q) :
    Ztop a 0 = ((∑' q : ℤ, a q : ℝ) : ℂ) := by
  rw [Ztop_eq_cos ha hs hsym]
  simp

/-- **`|Z_top(θ)| ≤ Z_top(0)`** for nonnegative summable weights. -/
theorem norm_Ztop_le (ha : ∀ q, 0 ≤ a q) (hs : Summable a) (θ : ℝ) :
    ‖Ztop a θ‖ ≤ ∑' q : ℤ, a q := by
  have h := norm_tsum_le_tsum_norm
    (f := fun q : ℤ => (a q : ℂ) * Complex.exp (((q : ℝ) * θ : ℝ) * Complex.I))
    (hs.congr fun q => (norm_term ha θ q).symm)
  rwa [tsum_congr fun q => norm_term ha θ q] at h

/-- **The sum over sectors is largest exactly at `θ ∈ 2πℤ`**, when the sectors `0` and `1` have
positive weight. -/
theorem norm_Ztop_eq_iff (ha : ∀ q, 0 ≤ a q) (hs : Summable a) (hsym : ∀ q, a (-q) = a q)
    (h0 : 0 < a 0) (h1 : 0 < a 1) (θ : ℝ) :
    ‖Ztop a θ‖ = ∑' q : ℤ, a q ↔ ∃ k : ℤ, θ = k * (2 * Real.pi) := by
  rw [Ztop_eq_cos ha hs hsym, Complex.norm_real, Real.norm_eq_abs]
  have hR : 0 ≤ ∑' q : ℤ, a q := tsum_nonneg ha
  have hc := summable_cos ha hs θ
  constructor
  · intro h
    rcases (abs_eq hR).mp h with hf | hf
    · have hsum : HasSum (fun q : ℤ => a q * (1 - Real.cos (q * θ))) 0 := by
        have e : (fun q : ℤ => a q * (1 - Real.cos (q * θ))) =
            fun q => a q - a q * Real.cos (q * θ) := by
          funext q
          ring
        rw [e]
        have h2 := hs.hasSum.sub hc.hasSum
        rwa [hf, sub_self] at h2
      have hz := (hasSum_zero_iff_of_nonneg fun q =>
        mul_nonneg (ha q) (by linarith [Real.cos_le_one (q * θ)])).mp hsum
      have h1' := congrFun hz 1
      simp only [Int.cast_one, one_mul, Pi.zero_apply] at h1'
      have hcos : Real.cos θ = 1 := by
        have h3 := (mul_eq_zero.mp h1').resolve_left h1.ne'
        linarith
      obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff θ).mp hcos
      exact ⟨n, hn.symm⟩
    · exfalso
      have hsum : HasSum (fun q : ℤ => a q * (1 + Real.cos (q * θ))) 0 := by
        have e : (fun q : ℤ => a q * (1 + Real.cos (q * θ))) =
            fun q => a q + a q * Real.cos (q * θ) := by
          funext q
          ring
        rw [e]
        have h2 := hs.hasSum.add hc.hasSum
        rwa [hf, add_neg_cancel] at h2
      have hz := (hasSum_zero_iff_of_nonneg fun q =>
        mul_nonneg (ha q) (by linarith [Real.neg_one_le_cos (q * θ)])).mp hsum
      have h0' := congrFun hz 0
      simp only [Int.cast_zero, zero_mul, Real.cos_zero, Pi.zero_apply] at h0'
      linarith
  · rintro ⟨k, rfl⟩
    have hcos : ∀ q : ℤ, Real.cos (q * (k * (2 * Real.pi))) = 1 := by
      intro q
      have e : (q : ℝ) * (k * (2 * Real.pi)) = ((q * k : ℤ) : ℝ) * (2 * Real.pi) := by
        push_cast
        ring
      rw [e, Real.cos_int_mul_two_pi]
    simp only [hcos, mul_one]
    exact abs_of_nonneg hR

/-- **Where the sum over sectors is largest, `e^(iθ) = 1`.** -/
theorem exp_eq_one_of_max (ha : ∀ q, 0 ≤ a q) (hs : Summable a) (hsym : ∀ q, a (-q) = a q)
    (h0 : 0 < a 0) (h1 : 0 < a 1) (θ : ℝ) (hmax : ‖Ztop a θ‖ = ∑' q : ℤ, a q) :
    Complex.exp ((θ : ℂ) * Complex.I) = 1 := by
  obtain ⟨k, rfl⟩ := (norm_Ztop_eq_iff ha hs hsym h0 h1 θ).mp hmax
  have e : (((k : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I = (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [e, Complex.exp_int_mul_two_pi_mul_I]

/-- **Away from `2πℤ` the sum over sectors is strictly smaller.** -/
theorem norm_Ztop_lt (ha : ∀ q, 0 ≤ a q) (hs : Summable a) (hsym : ∀ q, a (-q) = a q)
    (h0 : 0 < a 0) (h1 : 0 < a 1) (θ : ℝ) (hθ : ∀ k : ℤ, θ ≠ k * (2 * Real.pi)) :
    ‖Ztop a θ‖ < ∑' q : ℤ, a q := by
  refine lt_of_le_of_ne (norm_Ztop_le ha hs θ) fun h => ?_
  obtain ⟨k, hk⟩ := (norm_Ztop_eq_iff ha hs hsym h0 h1 θ).mp h
  exact hθ k hk

/-- **θ̄ = 0 where the sum over sectors is largest**: with a positive mass determinant `det(M_uM_d)`,
`θ̄ = θ + arg det(M_uM_d) ∈ 2πℤ`. -/
theorem theta_bar_series (ha : ∀ q, 0 ≤ a q) (hs : Summable a) (hsym : ∀ q, a (-q) = a q)
    (h0 : 0 < a 0) (h1 : 0 < a 1) (θ : ℝ) (hmax : ‖Ztop a θ‖ = ∑' q : ℤ, a q) (detM : ℂ)
    (hM : 0 < detM) : ∃ k : ℤ, θ + Complex.arg detM = k * (2 * Real.pi) := by
  obtain ⟨hre, him⟩ := Complex.pos_iff.mp hM
  have e : detM = (detM.re : ℂ) := Complex.ext (by simp) (by simp [← him])
  rw [e, Complex.arg_ofReal_of_nonneg hre.le, add_zero]
  exact (norm_Ztop_eq_iff ha hs hsym h0 h1 θ).mp hmax

end Comparison.ArticleStatements.Series

#print axioms Comparison.ArticleStatements.Series.norm_term
#print axioms Comparison.ArticleStatements.Series.summable_term
#print axioms Comparison.ArticleStatements.Series.summable_cos
#print axioms Comparison.ArticleStatements.Series.summable_sin
#print axioms Comparison.ArticleStatements.Series.sin_tsum_zero
#print axioms Comparison.ArticleStatements.Series.Ztop_eq_cos
#print axioms Comparison.ArticleStatements.Series.Ztop_zero
#print axioms Comparison.ArticleStatements.Series.norm_Ztop_le
#print axioms Comparison.ArticleStatements.Series.norm_Ztop_eq_iff
#print axioms Comparison.ArticleStatements.Series.exp_eq_one_of_max
#print axioms Comparison.ArticleStatements.Series.norm_Ztop_lt
#print axioms Comparison.ArticleStatements.Series.theta_bar_series
