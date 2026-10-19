import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Asymptotics.Ring
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Module

/-!
# A closed walk to the second order, with its remainder (Proposition 38; S38 of the public edition)

For four rotations `a₁, …, a₄` of the steps of a square, in any complete normed real algebra (the rotations of the article are
`4 × 4` matrices), the holonomy `hol(t) = e^{ta₄}e^{ta₃}e^{ta₂}e^{ta₁}` is

**`hol(t) = exp(t Σ aᵢ + (t²/2) Σ_{i>j} [aᵢ, aⱼ]) + O(t³)`** (`bch_line`),

that is `log hol = Σ aᵢ + ½ Σ_{i>j} [aᵢ, aⱼ] + O(a³)`. The proof carries second-order jets: `Jet f c₀ c₁ c₂` says
`f(t) = c₀ + t c₁ + t² c₂ + O(t³)` near `t = 0`.

* `jet_exp_line`: `e^{ta} = 1 + t a + t² a²/2 + O(t³)` (Taylor's formula for the exponential's power series);
* `jet_mul`: jets multiply, `(f g)` has `(f₀g₀, f₀g₁ + f₁g₀, f₀g₂ + f₁g₁ + f₂g₀)`;
* `jet_exp_curve`: `exp(tS + t²D) = 1 + tS + t²(D + S²/2) + O(t³)`;
* `bch_line`: the two jets agree by `bch_second_order` (`Splits.lean`), so the difference is `O(t³)`.
-/

namespace Comparison.Article

open Asymptotics Filter NormedSpace Topology

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

/-- **A second-order jet:** `f t = c₀ + t c₁ + t² c₂ + O(t³)` near `0`. -/
def Jet (f : ℝ → A) (c₀ c₁ c₂ : A) : Prop :=
  (fun t : ℝ => f t - (c₀ + t • c₁ + (t ^ 2) • c₂)) =O[𝓝 0] fun t : ℝ => t ^ 3

/-- Two curves with one jet differ by `O(t³)`. -/
theorem Jet.sub_isBigO {f g : ℝ → A} {c₀ c₁ c₂ : A} (hf : Jet f c₀ c₁ c₂) (hg : Jet g c₀ c₁ c₂) :
    (fun t => f t - g t) =O[𝓝 0] fun t : ℝ => t ^ 3 := by
  have := hf.sub hg
  refine this.congr_left fun t => ?_
  abel

/-- `t³ X + t⁴ Y = O(t³)` near `0`. -/
theorem cube_quart_isBigO (X Y : A) :
    (fun t : ℝ => (t ^ 3) • X + (t ^ 4) • Y) =O[𝓝 0] fun t : ℝ => t ^ 3 := by
  refine IsBigO.of_bound (‖X‖ + ‖Y‖) ?_
  have hball : ∀ᶠ t : ℝ in 𝓝 0, |t| ≤ 1 := by
    have : Metric.closedBall (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Metric.closedBall_mem_nhds 0 one_pos
    filter_upwards [this] with t ht
    simpa [Metric.mem_closedBall, Real.dist_eq] using ht
  filter_upwards [hball] with t ht
  have h1 := norm_add_le ((t ^ 3) • X) ((t ^ 4) • Y)
  rw [norm_smul, norm_smul] at h1
  have h4 : ‖t ^ 4‖ ≤ ‖t ^ 3‖ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_pow]
    have := abs_nonneg t
    calc |t| ^ 4 = |t| ^ 3 * |t| := by ring
      _ ≤ |t| ^ 3 * 1 := by gcongr
      _ = |t| ^ 3 := by ring
  calc ‖(t ^ 3) • X + (t ^ 4) • Y‖ ≤ ‖t ^ 3‖ * ‖X‖ + ‖t ^ 4‖ * ‖Y‖ := h1
    _ ≤ ‖t ^ 3‖ * ‖X‖ + ‖t ^ 3‖ * ‖Y‖ := by gcongr
    _ = (‖X‖ + ‖Y‖) * ‖t ^ 3‖ := by ring

/-- A polynomial curve is bounded near `0`. -/
theorem poly_bounded (c₀ c₁ c₂ : A) :
    (fun t : ℝ => c₀ + t • c₁ + (t ^ 2) • c₂) =O[𝓝 0] fun _ : ℝ => (1 : ℝ) := by
  have hc : Continuous fun t : ℝ => c₀ + t • c₁ + (t ^ 2) • c₂ := by fun_prop
  exact (hc.tendsto 0).isBigO_one (F := ℝ)

/-- **Jets multiply.** -/
theorem jet_mul {f g : ℝ → A} {f₀ f₁ f₂ g₀ g₁ g₂ : A} (hf : Jet f f₀ f₁ f₂) (hg : Jet g g₀ g₁ g₂)
    (hgb : g =O[𝓝 0] fun _ : ℝ => (1 : ℝ)) :
    Jet (fun t => f t * g t) (f₀ * g₀) (f₀ * g₁ + f₁ * g₀) (f₀ * g₂ + f₁ * g₁ + f₂ * g₀) := by
  unfold Jet at *
  set Pf : ℝ → A := fun t => f₀ + t • f₁ + (t ^ 2) • f₂ with hPf
  set Pg : ℝ → A := fun t => g₀ + t • g₁ + (t ^ 2) • g₂ with hPg
  have hpoly : ∀ t : ℝ, Pf t * Pg t - (f₀ * g₀ + t • (f₀ * g₁ + f₁ * g₀) + (t ^ 2) • (f₀ * g₂ + f₁ * g₁ + f₂ * g₀)) =
      (t ^ 3) • (f₁ * g₂ + f₂ * g₁) + (t ^ 4) • (f₂ * g₂) := by
    intro t
    simp only [hPf, hPg, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, smul_add]
    module
  have e : (fun t : ℝ => f t * g t - (f₀ * g₀ + t • (f₀ * g₁ + f₁ * g₀) + (t ^ 2) • (f₀ * g₂ + f₁ * g₁ + f₂ * g₀))) =
      fun t => ((t ^ 3) • (f₁ * g₂ + f₂ * g₁) + (t ^ 4) • (f₂ * g₂)) + Pf t * (g t - Pg t) + (f t - Pf t) * g t := by
    funext t
    rw [← hpoly t]
    noncomm_ring
  rw [e]
  have h1 := cube_quart_isBigO (f₁ * g₂ + f₂ * g₁) (f₂ * g₂)
  have h2 : (fun t => Pf t * (g t - Pg t)) =O[𝓝 0] fun t : ℝ => (1 : ℝ) * t ^ 3 :=
    (poly_bounded f₀ f₁ f₂).mul hg
  have h3 : (fun t => (f t - Pf t) * g t) =O[𝓝 0] fun t : ℝ => t ^ 3 * (1 : ℝ) := hf.mul hgb
  simp only [one_mul, mul_one] at h2 h3
  exact (h1.add h2).add h3

/-- `exp y = 1 + y + y²/2 + O(‖y‖³)`. -/
theorem exp_second_order :
    (fun y : A => exp y - (1 + y + (1 / 2 : ℝ) • (y * y))) =O[𝓝 0] fun y : A => ‖y‖ ^ 3 := by
  have h := (exp_hasFPowerSeriesAt_zero (𝕂 := ℝ) (𝔸 := A)).isBigO_sub_partialSum_pow 3
  refine h.congr_left fun y => ?_
  simp only [zero_add, FormalMultilinearSeries.partialSum, Finset.sum_range_succ, Finset.range_zero,
    Finset.sum_empty, expSeries_apply_eq]
  simp [pow_two, Nat.factorial]

/-- `‖Z t‖³ = O(t³)` for a curve with `‖Z t‖ ≤ K|t|` near `0`. -/
theorem norm_cube_isBigO {Z : ℝ → A} (K : ℝ) (hK : ∀ᶠ t in 𝓝 (0 : ℝ), ‖Z t‖ ≤ K * |t|) :
    (fun t => ‖Z t‖ ^ 3) =O[𝓝 0] fun t : ℝ => t ^ 3 := by
  refine IsBigO.of_bound (|K| ^ 3) ?_
  filter_upwards [hK] with t ht
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow, abs_pow, abs_norm]
  have h0 : ‖Z t‖ ≤ |K| * |t| := le_trans ht (by gcongr; exact le_abs_self K)
  calc ‖Z t‖ ^ 3 ≤ (|K| * |t|) ^ 3 := by gcongr
    _ = |K| ^ 3 * |t| ^ 3 := by ring

/-- **The exponential of a curve `tS + t²D`:** `1 + tS + t²(D + S²/2) + O(t³)`. -/
theorem jet_exp_curve (S D : A) :
    Jet (fun t : ℝ => exp (t • S + (t ^ 2) • D)) 1 S (D + (1 / 2 : ℝ) • (S * S)) := by
  unfold Jet
  set Z : ℝ → A := fun t => t • S + (t ^ 2) • D with hZ
  have hZt : Tendsto Z (𝓝 0) (𝓝 0) := by
    have hc : Continuous Z := by rw [hZ]; fun_prop
    simpa [hZ] using hc.tendsto 0
  have hK : ∀ᶠ t in 𝓝 (0 : ℝ), ‖Z t‖ ≤ (‖S‖ + ‖D‖) * |t| := by
    have : Metric.closedBall (0 : ℝ) 1 ∈ 𝓝 (0 : ℝ) := Metric.closedBall_mem_nhds 0 one_pos
    filter_upwards [this] with t ht
    have ht' : |t| ≤ 1 := by simpa [Metric.mem_closedBall, Real.dist_eq] using ht
    have h1 := norm_add_le (t • S) ((t ^ 2) • D)
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_pow] at h1
    have h2 : |t| ^ 2 ≤ |t| := by nlinarith [abs_nonneg t]
    calc ‖Z t‖ ≤ |t| * ‖S‖ + |t| ^ 2 * ‖D‖ := h1
      _ ≤ |t| * ‖S‖ + |t| * ‖D‖ := by gcongr
      _ = (‖S‖ + ‖D‖) * |t| := by ring
  have hR := (exp_second_order (A := A)).comp_tendsto hZt
  have hR' : (fun t => exp (Z t) - (1 + Z t + (1 / 2 : ℝ) • (Z t * Z t))) =O[𝓝 0] fun t : ℝ => t ^ 3 :=
    hR.trans (norm_cube_isBigO _ hK)
  have hpoly : ∀ t : ℝ, (1 + Z t + (1 / 2 : ℝ) • (Z t * Z t)) - (1 + t • S + (t ^ 2) • (D + (1 / 2 : ℝ) • (S * S))) =
      (t ^ 3) • ((1 / 2 : ℝ) • (S * D + D * S)) + (t ^ 4) • ((1 / 2 : ℝ) • (D * D)) := by
    intro t
    simp only [hZ, add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_smul, smul_add]
    module
  have e : (fun t : ℝ => exp (Z t) - (1 + t • S + (t ^ 2) • (D + (1 / 2 : ℝ) • (S * S)))) =
      fun t => (exp (Z t) - (1 + Z t + (1 / 2 : ℝ) • (Z t * Z t))) +
        ((t ^ 3) • ((1 / 2 : ℝ) • (S * D + D * S)) + (t ^ 4) • ((1 / 2 : ℝ) • (D * D))) := by
    funext t
    rw [← hpoly t]
    abel
  rw [e]
  exact hR'.add (cube_quart_isBigO _ _)

/-- **`e^{ta} = 1 + ta + t²a²/2 + O(t³)`.** -/
theorem jet_exp_line (a : A) : Jet (fun t : ℝ => exp (t • a)) 1 a ((1 / 2 : ℝ) • (a * a)) := by
  have h := jet_exp_curve a 0
  unfold Jet at h ⊢
  simpa using h

theorem exp_line_bounded (a : A) : (fun t : ℝ => exp (t • a)) =O[𝓝 0] fun _ : ℝ => (1 : ℝ) := by
  have h1 : ContinuousAt (fun t : ℝ => t • a) 0 := by fun_prop
  have h2 : ContinuousAt (exp : A → A) ((fun t : ℝ => t • a) 0) := (exp_analytic (𝕂 := ℝ) _).continuousAt
  have hc : ContinuousAt (fun t : ℝ => exp (t • a)) 0 :=
    ContinuousAt.comp (g := (exp : A → A)) (f := fun t : ℝ => t • a) (x := 0) h2 h1
  exact hc.tendsto.isBigO_one (F := ℝ)

/-- The sum of the commutators of a square's four rotations, later before earlier. -/
def squareC (a₁ a₂ a₃ a₄ : A) : A :=
  (a₂ * a₁ - a₁ * a₂) + (a₃ * a₁ - a₁ * a₃) + (a₃ * a₂ - a₂ * a₃) + (a₄ * a₁ - a₁ * a₄) +
    (a₄ * a₂ - a₂ * a₄) + (a₄ * a₃ - a₃ * a₄)

/-- **Proposition 38: the closed walk to the second order.**
`e^{ta₄}e^{ta₃}e^{ta₂}e^{ta₁} = exp(t Σ aᵢ + (t²/2) Σ_{i>j} [aᵢ, aⱼ]) + O(t³)`. -/
theorem bch_line (a₁ a₂ a₃ a₄ : A) :
    (fun t : ℝ => exp (t • a₄) * exp (t • a₃) * exp (t • a₂) * exp (t • a₁) -
        exp (t • (a₁ + a₂ + a₃ + a₄) + (t ^ 2) • ((1 / 2 : ℝ) • squareC a₁ a₂ a₃ a₄))) =O[𝓝 0]
      fun t : ℝ => t ^ 3 := by
  have j43 := jet_mul (jet_exp_line a₄) (jet_exp_line a₃) (exp_line_bounded a₃)
  have j432 := jet_mul j43 (jet_exp_line a₂) (exp_line_bounded a₂)
  have j4321 := jet_mul j432 (jet_exp_line a₁) (exp_line_bounded a₁)
  have jZ := jet_exp_curve (a₁ + a₂ + a₃ + a₄) ((1 / 2 : ℝ) • squareC a₁ a₂ a₃ a₄)
  -- the two jets agree
  have key : Jet (fun t : ℝ => exp (t • a₄) * exp (t • a₃) * exp (t • a₂) * exp (t • a₁)) 1
      (a₁ + a₂ + a₃ + a₄) ((1 / 2 : ℝ) • squareC a₁ a₂ a₃ a₄ + (1 / 2 : ℝ) • ((a₁ + a₂ + a₃ + a₄) * (a₁ + a₂ + a₃ + a₄))) := by
    unfold Jet at j4321 ⊢
    refine j4321.congr_left fun t => ?_
    congr 1
    simp only [squareC, one_mul, mul_one, add_mul, mul_add, smul_add, smul_sub, mul_sub, sub_mul,
      smul_mul_assoc, mul_smul_comm, smul_smul]
    module
  exact key.sub_isBigO jZ

end Comparison.Article
