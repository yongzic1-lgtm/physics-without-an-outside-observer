import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# The coupling as the mixed derivative of the two-source function (Eq. (31))

Two ends meet at the channels `x` with chances `P₁(x)`, `P₂(x)`. With a source on each end, the closed member
`(+1, 1)` of the source family (Proposition 110), `Z = det(I − J)^{−1}` with `J = J₁ diag P₁ + J₂ diag P₂` on the
channels, has `W(J₁, J₂) = log Z = −Σ_x log(1 − J₁P₁(x) − J₂P₂(x))`, and

* `mixed_derivative` (**Eq. (31)**): **`∂²W/∂J₁∂J₂ = Σ_x P₁(x)P₂(x)`** at `J = 0`, the coupling `σ`;
* `equal_places`: for two ends each reaching one of `N` equal channels with chance `e/N`, `σ = e²/N` (Proposition 64).
-/

namespace Comparison.Article

open Real

/-- The two-source function on the channels. -/
noncomputable def Wtwo {N : ℕ} (P₁ P₂ : Fin N → ℝ) (J₁ J₂ : ℝ) : ℝ :=
  -∑ x, Real.log (1 - J₁ * P₁ x - J₂ * P₂ x)

/-- The first derivative in `J₁` at `J₁ = 0`, for `J₂` with every `1 − J₂P₂(x) ≠ 0`. -/
theorem Wtwo_deriv₁ {N : ℕ} (P₁ P₂ : Fin N → ℝ) (J₂ : ℝ) (h : ∀ x, 1 - J₂ * P₂ x ≠ 0) :
    HasDerivAt (fun J₁ => Wtwo P₁ P₂ J₁ J₂) (∑ x, P₁ x / (1 - J₂ * P₂ x)) 0 := by
  have hx : ∀ x ∈ Finset.univ, HasDerivAt (fun J₁ => Real.log (1 - J₁ * P₁ x - J₂ * P₂ x))
      (-P₁ x / (1 - J₂ * P₂ x)) 0 := by
    intro x _
    have hl : HasDerivAt (fun J₁ : ℝ => 1 - J₁ * P₁ x - J₂ * P₂ x) (-(1 * P₁ x)) 0 := by
      have := ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub ((hasDerivAt_id' (0 : ℝ)).mul_const (P₁ x))).sub_const
        (J₂ * P₂ x)
      convert this using 1
      ring
    have hne : (1 : ℝ) - 0 * P₁ x - J₂ * P₂ x ≠ 0 := by simpa using h x
    have := hl.log hne
    convert this using 1
    simp
  have hs := HasDerivAt.sum hx
  have hn := hs.neg
  unfold Wtwo
  convert hn using 1
  · funext J₁
    simp [Finset.sum_apply]
  · rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring

/-- **Eq. (31): the coupling is the mixed derivative**, `∂²W/∂J₁∂J₂ = Σ_x P₁(x)P₂(x)` at `J = 0`. -/
theorem mixed_derivative {N : ℕ} (P₁ P₂ : Fin N → ℝ) :
    deriv (fun J₂ => deriv (fun J₁ => Wtwo P₁ P₂ J₁ J₂) 0) 0 = ∑ x, P₁ x * P₂ x := by
  -- near `J₂ = 0` the inner derivative is `Σ P₁/(1 − J₂P₂)`
  have hev : (fun J₂ => deriv (fun J₁ => Wtwo P₁ P₂ J₁ J₂) 0) =ᶠ[nhds 0]
      fun J₂ => ∑ x, P₁ x / (1 - J₂ * P₂ x) := by
    have hc : ∀ x, ContinuousAt (fun J₂ : ℝ => 1 - J₂ * P₂ x) 0 := fun x =>
      (continuous_const.sub (continuous_id.mul continuous_const)).continuousAt
    have hev' : ∀ᶠ J₂ in nhds (0 : ℝ), ∀ x, 1 - J₂ * P₂ x ≠ 0 := by
      rw [Filter.eventually_all]
      intro x
      exact (hc x).eventually_ne (by simp)
    filter_upwards [hev'] with J₂ hJ
    exact (Wtwo_deriv₁ P₁ P₂ J₂ hJ).deriv
  rw [hev.deriv_eq]
  have hx : ∀ x ∈ Finset.univ, HasDerivAt (fun J₂ : ℝ => P₁ x / (1 - J₂ * P₂ x)) (P₁ x * P₂ x) 0 := by
    intro x _
    have hl : HasDerivAt (fun J₂ : ℝ => 1 - J₂ * P₂ x) (0 - 1 * P₂ x) 0 :=
      (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub ((hasDerivAt_id' (0 : ℝ)).mul_const (P₂ x))
    have := (hasDerivAt_const (0 : ℝ) (P₁ x)).div hl (by simp)
    convert this using 1
    simp
  have hs := HasDerivAt.sum hx
  have hs' : HasDerivAt (fun J₂ : ℝ => ∑ x, P₁ x / (1 - J₂ * P₂ x)) (∑ x, P₁ x * P₂ x) 0 := by
    convert hs using 1
    funext J₂
    simp [Finset.sum_apply]
  exact hs'.deriv

/-- **Two ends on `N` equal channels:** `σ = Σ_p (e/N)² = e²/N` (Proposition 64). -/
theorem equal_places (N : ℕ) (hN : 0 < N) (e : ℝ) : ∑ _x : Fin N, (e / N) * (e / N) = e ^ 2 / N := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

end Comparison.Article
