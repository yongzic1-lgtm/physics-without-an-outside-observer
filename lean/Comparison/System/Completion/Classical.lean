import Comparison.System.Completion.Numbers
import Comparison.WholePicture.TheLaw
import Comparison.Formulas.Kernel
import Comparison.Formulas.Sweep
import Comparison.Article.Series
import Comparison.WholePicture.SecondVariation

set_option linter.style.longLine false

/-!
# The proof system, the completions, part 7: the classical theory is the law's long-wave limit (Eqs. (46), (47))

The law's own transformation, the response held against a fixed clock, and the constant as
the ratio that stays.
-/

namespace Comparison.System

open Real Complex Matrix Filter Topology Comparison Comparison.Law Comparison.System.Completion

/-- **Equation (46), the law's own transformation.** For every matrix `A` and `u ≠ 0`:
`K(v) = c₁K(u) + c₀I` with `K(u) = (1 + 4u²) − uA`, `c₁ = v/u`, `c₀ = 1 + 4v² − c₁(1 + 4u²)`; the grade factors
transform alike, `k_N(v) = (v/u)k_N(u) + c₀`; and `K(v)/v = K(u)/u + (χ(v) − χ(u))I` with `χ(u) = 1/u + 4u − 5`. -/
theorem eq_46 :
    (∀ {n : Type} [DecidableEq n] (A : Matrix n n ℂ) (u v : ℂ), u ≠ 0 →
      (1 + 4 * v ^ 2) • (1 : Matrix n n ℂ) - v • A =
        (v / u) • ((1 + 4 * u ^ 2) • (1 : Matrix n n ℂ) - u • A) +
          (1 + 4 * v ^ 2 - v / u * (1 + 4 * u ^ 2)) • (1 : Matrix n n ℂ)) ∧
    (∀ N u v : ℂ, u ≠ 0 → WholePicture.kN N v = v / u * WholePicture.kN N u + (1 + 4 * v ^ 2 - v / u * (1 + 4 * u ^ 2))) ∧
    (∀ {n : Type} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (u v : ℂ), u ≠ 0 → v ≠ 0 →
      (1 / v) • ((1 + 4 * v ^ 2) • (1 : Matrix n n ℂ) - v • A) =
        (1 / u) • ((1 + 4 * u ^ 2) • (1 : Matrix n n ℂ) - u • A) + (Formulas.chi v - Formulas.chi u) • 1) ∧
    (∀ u : ℂ, Formulas.chi u = 1 / u + 4 * u - 5) :=
  ⟨fun A u v hu => WholePicture.law_transformation A u v hu, fun N u v hu => WholePicture.grade_factor_transformation N u v hu,
    fun A u v hu hv => Formulas.own_transformation A u v hu hv, fun u => rfl⟩

/-- **Equation (47), a response held against a fixed clock runs.** The law's second variation in the link phases is
`−κ(w)G` with `κ(w) = 2w⁴/(1 − 5w²)²` for every `w` with `1 − 5w² ≠ 0` (W's Prop. 116); `κ` at `w = u/(1 + 4u²)` is
`2u⁴/(1 + 3u² + 16u⁴)² = 2u⁴ − 12u⁶ − 10u⁸ + 360u¹⁰ + ⋯`, with the remainder written out and bounded by
`2u¹²(555 + 5364u² + 16000u⁴ + 46080u⁶)`. -/
theorem eq_47 :
    (∀ (w : ℂ), 1 - 5 * w ^ 2 ≠ 0 → ∀ j k : Fin 40,
      WholePicture.hessLaw w j k = -(2 * w ^ 4 / (1 - 5 * w ^ 2) ^ 2) * (GZ j k : ℂ)) ∧
    (∀ u : ℝ, 2 * (u / (1 + 4 * u ^ 2)) ^ 4 / (1 - 5 * (u / (1 + 4 * u ^ 2)) ^ 2) ^ 2 =
      2 * u ^ 4 / (1 + 3 * u ^ 2 + 16 * u ^ 4) ^ 2) ∧
    (∀ u : ℝ, 2 * u ^ 4 / (1 + 3 * u ^ 2 + 16 * u ^ 4) ^ 2 =
      2 * u ^ 4 - 12 * u ^ 6 - 10 * u ^ 8 + 360 * u ^ 10 -
        2 * u ^ 12 * (555 + 5364 * u ^ 2 + 16000 * u ^ 4 + 46080 * u ^ 6) / (1 + 3 * u ^ 2 + 16 * u ^ 4) ^ 2) ∧
    (∀ u : ℝ, |2 * u ^ 4 / (1 + 3 * u ^ 2 + 16 * u ^ 4) ^ 2 - (2 * u ^ 4 - 12 * u ^ 6 - 10 * u ^ 8 + 360 * u ^ 10)| ≤
      2 * u ^ 12 * (555 + 5364 * u ^ 2 + 16000 * u ^ 4 + 46080 * u ^ 6)) :=
  ⟨fun w hw j k => WholePicture.hessLaw_eq w hw j k, Article.kappa_in_u, Article.kappa_series,
    Article.kappa_series_bound⟩

/-- **The constant is the ratio that stays (the classical-limit section).** For every central weight `(p, q)`
(`p, q > 0`), `𝒥_DE/𝒞_W = (rs − 5 Tr P_DP_E)/72` (`r = |D|`, `s = |E|`); one pair of directions on opposite sides is `1/72` of the clock at
every weight; as `χ` varies, with `p = 1/(χ + 4)`, `q = 1/(χ + 8)`, the clock is `9(χ + 4)(χ + 8)/(3χ + 20)²` and the pair
`(χ + 4)(χ + 8)/(8(3χ + 20)²)`: at `u = 1/4` (`χ = 0`) the pair is `1/100` against the clock `18/25`, and as
`χ → ∞` (`u → 0`) the pair tends to `1/72` against the clock `1`; and `1/72 = −Φ(1)/(4(1 + Φ(1)))`. -/
theorem classical_ratio :
    (∀ p q : ℝ, 0 < p → 0 < q → ∀ D E : Finset (Fin 5),
      Formulas.JDE p q D E = Formulas.CW p q / 72 * (D.card * E.card - 5 * ((projD D) * (projD E)).trace)) ∧
    (∀ p q : ℝ, 0 < p → 0 < q → Formulas.JDE p q {0} {1} / Formulas.CW p q = 1 / 72) ∧
    (∀ χ : ℝ, 0 ≤ χ → ∀ a b : Fin 5, a ≠ b →
      Formulas.CW (1 / (χ + 4)) (1 / (χ + 8)) = 9 * (χ + 4) * (χ + 8) / (3 * χ + 20) ^ 2 ∧
        Formulas.JDE (1 / (χ + 4)) (1 / (χ + 8)) {a} {b} = (χ + 4) * (χ + 8) / (8 * (3 * χ + 20) ^ 2)) ∧
    (∀ a b : Fin 5, a ≠ b → Formulas.JDE (1 / 4) (1 / 8) {a} {b} = 1 / 100) ∧
    Formulas.CW (1 / 4) (1 / 8) = 18 / 25 ∧
    (Tendsto (fun χ : ℝ => (χ + 4) * (χ + 8) / (8 * (3 * χ + 20) ^ 2)) atTop (𝓝 (1 / 72)) ∧
      Tendsto (fun χ : ℝ => 9 * (χ + 4) * (χ + 8) / (3 * χ + 20) ^ 2) atTop (𝓝 1)) ∧
    ((1 / 72 : ℝ) : ℂ) = -Law.Phi 1 / (4 * (1 + Law.Phi 1)) := by
  refine ⟨fun p q hp hq D E => Formulas.sweep p q hp hq D E, fun p q hp hq => (Formulas.sweep_ratios p q hp hq).1,
    fun χ hχ a b hab => Formulas.sweep_gap χ hχ a b hab, fun a b hab => Formulas.sweep_zero a b hab, ?_,
    Formulas.sweep_limit, (Formulas.crossing_g_sq 1 1 one_pos one_pos).2.1⟩
  have h := (Formulas.sweep_gap 0 le_rfl 0 1 (by decide)).1
  have e1 : (1 : ℝ) / (0 + 4) = 1 / 4 := by norm_num
  have e2 : (1 : ℝ) / (0 + 8) = 1 / 8 := by norm_num
  rw [e1, e2] at h
  rw [h]
  norm_num

end Comparison.System
