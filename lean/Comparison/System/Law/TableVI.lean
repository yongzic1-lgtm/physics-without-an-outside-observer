import Comparison.System.Postulates
import Comparison.System.Law.Equations
import Comparison.System.Existence.ExcursionVisits
import Comparison.Existence.Moments
import Comparison.Existence.AvailableTransitions
import Comparison.Colour.Visits
import Comparison.WholePicture.Polar
import Comparison.WholePicture.OneArc
import Comparison.ArticleStatements.Radar
import Comparison.Formulas.Sweep

/-!
# The proof system, the law: Table VI, the functions of the law

Each row of Table VI of the main text, in its own words, from the
theorems that count it on the step `B`: the excursion and the signed excursion (`Existence/Excursion.lean`), the visits of one excursion
(`Existence/Moments.lean`, `Colour/Visits.lean`), the transitions of one excursion (`Existence/AvailableTransitions.lean`), the Green function
(`Law/Equations.lean`: `eq_20`), the polar step, the charge current and `24/11` (`WholePicture/Polar.lean`,
`ArticleStatements/Radar.lean`), the vertical grade against the parallel clocks (`Formulas/Sweep.lean`) and the one marked
arc (`WholePicture/OneArc.lean`).
-/

open Matrix Complex Comparison Polynomial

namespace Comparison.System

open Comparison.System.Law

/-- **Table VI, the functions of the law, every one counted on the step `B`** (`z = 4u`).
`F`: every excursion closes, `F(1) = Σ f = 1`, after `F′(1) = Σ n f = 16` steps on average, `Var ℓ = 156`.
`Φ`: `Φ(±1) = −1/19`, `Φ(±i) = −1/13`. The visits of one excursion (`F(z, x, y)` with `y` marking a plane and `x` a
line): `E P = 10`, `E Q = 5`, `Var P = 84`, `Var Q = 12`, `Cov(P, Q) = 30`, the moments of the symmetric and
vector states each excursion meets, counted over the excursions (`ℓ = 1 + P + Q`; E's Prop. 29), which the derivatives of `F` are. One excursion's visits to the symmetric states, the sum over the excursions of `x^P` (E's `plane_visits_gf`),
`G_P(x) = x(1 + x)/(16 − 11x − 3x²) = F(1, 1, x)`, with its pole `x_c = (√313 − 11)/6 > 1`. The transitions of one excursion:
`74` states, `M = 296` transitions, `C_h = 60` along the last-step direction, `C_j = 59` along each other line, `34` of the `74` leaving the
last-step direction undivided. `(5 − A)⁺ = (7 + A)/32 − 3J/128` and `b = 7/16`. The polar step (on the canonical step `B ℝ`, `stepR_eq`): `BᵀB` has the eigenvalues `1`
(64 times) and `16` (16 times), `|B| = 1 + 3Π` is symmetric with `|B|² = BᵀB` and the eigenvalues `1` and `4`, and
`|B| = 2(e^ξΠ + e^{−ξ}(1 − Π)) = 2e^{ξ(2Π−I)}` with `ξ = log 2`, `tanh(ξ/4) = 3 − 2√2`. The charges of the five
directions: `c = 2 Var = 8/15`. `Tr L²/4 = 24` against the `1 + 10 = 11` positive vertices. `𝒥_DE = C_W(|D||E| −
5 Tr P_DP_E)/72` for every positive grade weights. One of the `320` arcs marked with a phase:
`D_θ(u) = D(u) + (e^{−iθ} − 1)uD′(u)/320`.
Recognition: the last row is the electron's rotation of the critical zero, `θ/320` per step. -/
theorem table_VI :
    -- F
    (HasSum excursionLaw 1 ∧ HasSum (fun n : ℕ => (n : ℝ) * excursionLaw n) 16 ∧
      (∑' n : ℕ, (n : ℝ) ^ 2 * excursionLaw n) - (∑' n : ℕ, (n : ℝ) * excursionLaw n) ^ 2 = 156 ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 → HasSum (fun n => (excursionLaw n : ℂ) * z ^ n) (excursionGF z)) ∧
      excursionGF 1 = 1 ∧ HasDerivAt excursionGF 16 1) ∧
    -- Φ
    ((∀ z : ℂ, ‖z‖ ≤ 1 → HasSum (fun n => (signedLaw n : ℂ) * z ^ n) (Comparison.Law.Phi z)) ∧
      Comparison.Law.Phi 1 = -1 / 19 ∧ Comparison.Law.Phi (-1) = -1 / 19 ∧
      Comparison.Law.Phi I = -1 / 13 ∧ Comparison.Law.Phi (-I) = -1 / 13) ∧
    -- the visits of one excursion
    (deriv (fun y => excursionF 1 1 y) 1 = 10 ∧ deriv (fun x => excursionF 1 x 1) 1 = 5 ∧
      deriv (deriv (fun y => excursionF 1 1 y)) 1 + deriv (fun y => excursionF 1 1 y) 1 -
          (deriv (fun y => excursionF 1 1 y) 1) ^ 2 = 84 ∧
      deriv (deriv (fun x => excursionF 1 x 1)) 1 + deriv (fun x => excursionF 1 x 1) 1 -
          (deriv (fun x => excursionF 1 x 1) 1) ^ 2 = 12 ∧
      deriv (fun x => deriv (fun y => excursionF 1 x y) 1) 1 -
          deriv (fun y => excursionF 1 1 y) 1 * deriv (fun x => excursionF 1 x 1) 1 = 30 ∧
      -- the same moments counted over the excursions (Prop. 29): `P`, `Q` the symmetric and vector states an excursion meets
      (∀ m, Comparison.System.Existence.statLaw Comparison.System.Existence.fP m =
        (∑ w ∈ excursions m, (Comparison.System.Existence.cP w : ℝ)) / (5 * 4 ^ (m - 1))) ∧
      (∀ m, Comparison.System.Existence.statLaw Comparison.System.Existence.fQ m =
        (∑ w ∈ excursions m, (Comparison.System.Existence.cQ w : ℝ)) / (5 * 4 ^ (m - 1))) ∧
      HasSum (Comparison.System.Existence.statLaw Comparison.System.Existence.fP) 10 ∧
      HasSum (Comparison.System.Existence.statLaw Comparison.System.Existence.fQ) 5 ∧
      Comparison.System.Existence.varP = 84 ∧ Comparison.System.Existence.varQ = 12 ∧
      Comparison.System.Existence.covPQ = 30 ∧
      (∀ w : List (Fin 5), IsExcursion w →
        1 + Comparison.System.Existence.cP w + Comparison.System.Existence.cQ w = w.length) ∧
      deriv (fun y => excursionF 1 1 y) 1 = Comparison.System.Existence.excursionMean Comparison.System.Existence.fP ∧
      deriv (fun x => excursionF 1 x 1) 1 = Comparison.System.Existence.excursionMean Comparison.System.Existence.fQ) ∧
    -- one excursion's visits to the symmetric states and their pole
    ((∀ x : ℂ, ‖x‖ ≤ 1 → HasSum (fun m => (∑ w ∈ excursions m, x ^ Comparison.System.Existence.cP w) / (5 * 4 ^ (m - 1)))
        (x * (1 + x) / (16 - 11 * x - 3 * x ^ 2))) ∧
      (∀ y : ℝ, GP y = excursionF 1 1 y) ∧ (∀ x : ℝ, GP x = x * (1 + x) / (16 - 11 * x - 3 * x ^ 2)) ∧
      (∀ x : ℝ, 16 - 11 * x - 3 * x ^ 2 = -3 * (x - xc) * (x - xc')) ∧
      xc = (Real.sqrt 313 - 11) / 6 ∧ 1 < xc ∧
      (∀ x : ℝ, 0 ≤ x → x ≤ 1 → 0 < 16 - 11 * x - 3 * x ^ 2)) ∧
    -- the transitions of one excursion
    (∀ h : Fin 5, (excursionStates h).card = 74 ∧ ∑ j, alongCount h j = 296 ∧ alongCount h h = 60 ∧
      (∀ j, j ≠ h → alongCount h j = 59) ∧
      ((excursionStates h).filter fun s => h ∉ disagreeSet s.1).card = 34) ∧
    -- the Green function at the critical step
    (WholePicture.greenM = (1 / 32 : ℝ) • ((7 : ℝ) • (1 : Matrix (Fin 16) (Fin 16) ℝ) + A ℝ) -
        (3 / 128 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ)) ∧
      (∀ X : Matrix (Fin 16) (Fin 16) ℝ, WholePicture.lapM * X * WholePicture.lapM = WholePicture.lapM →
        X * WholePicture.lapM * X = X → (WholePicture.lapM * X)ᵀ = WholePicture.lapM * X →
        (X * WholePicture.lapM)ᵀ = X * WholePicture.lapM → X = WholePicture.greenM) ∧
      (∀ f : Fin 16, (disagreeSet f).card = 2 →
        WholePicture.greenM 0 0 + WholePicture.greenM f f - 2 * WholePicture.greenM 0 f = 7 / 16)) ∧
    -- the polar step
    (((B ℝ)ᵀ * B ℝ).charpoly = (X - C (1 : ℝ)) ^ 64 * (X - C (16 : ℝ)) ^ 16 ∧
      WholePicture.absB.IsHermitian ∧ WholePicture.absB * WholePicture.absB = (B ℝ)ᵀ * B ℝ ∧
      WholePicture.absB.charpoly = (X - C (1 : ℝ)) ^ 64 * (X - C (4 : ℝ)) ^ 16 ∧
      WholePicture.absB = (2 : ℝ) • (Real.exp (Real.log 2) • WholePicture.lastDirectionProj +
        Real.exp (-Real.log 2) • (1 - WholePicture.lastDirectionProj)) ∧
      Real.tanh (Real.log 2 / 4) = 3 - 2 * Real.sqrt 2) ∧
    -- the charges of the five directions
    2 * ((∑ s, WholePicture.lineCharge s ^ 2) / 5 - ((∑ s, WholePicture.lineCharge s) / 5) ^ 2) = 8 / 15 ∧
    -- 24/11
    ((L * L).trace / 4 = 24 ∧
      Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' L) 6) +
        Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' L) 2) = 11) ∧
    -- the vertical grade and the parallel clocks
    (∀ (p q : ℝ), 0 < p → 0 < q → ∀ D E : Finset (Fin 5),
      Formulas.JDE p q D E = Formulas.CW p q / 72 *
        (D.card * E.card - 5 * ((projD D) * (projD E)).trace)) ∧
    -- one marked arc
    (∀ (p q : State), Continues q p → ∀ θ u : ℂ,
      (1 - u • WholePicture.Bmark p q (Complex.exp (-Complex.I * θ))).det =
        WholePicture.lawPoly.eval u + (Complex.exp (-Complex.I * θ) - 1) * u *
          (Polynomial.derivative WholePicture.lawPoly).eval u / 320) := by
  obtain ⟨-, hG1, -, hG2, hG3, -⟩ := eq_20
  have h29 := Comparison.System.Existence.prop_29
  refine ⟨⟨excursion_total, excursion_mean, excursion_variance, excursion_gf_eq, excursionGF_one, excursionGF_deriv_one⟩,
    ⟨signed_gf_eq, ?_, ?_, ?_, ?_⟩, ⟨EP_eq, EQ_eq, visit_moments.1, visit_moments.2.1,
      visit_moments.2.2.1, h29.2.2.2.2.2.1, h29.2.2.2.2.2.2.1, h29.2.2.2.2.2.2.2.1, h29.2.2.2.2.2.2.2.2.1,
      h29.2.2.2.2.2.2.2.2.2.2.2.2.1, h29.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h29.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      h29.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h29.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
      h29.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1⟩, ⟨fun x hx => Comparison.System.Existence.plane_visits_gf x hx, GP_eq, fun x => rfl, GP_denominator, rfl,
      xc_gt_one, GP_denom_pos⟩,
    fun h => ⟨card_excursionStates h, availableTransitions_total h, (availableTransitions_along h).1, (availableTransitions_along h).2, availableTransitions_up h⟩,
    ⟨hG1, hG2, hG3⟩, ⟨WholePicture.stepR_gram_charpoly, WholePicture.absB_symm, WholePicture.absB_sq,
      WholePicture.absB_charpoly, WholePicture.absB_polar, ArticleStatements.Radar.tanh_quarter⟩,
    WholePicture.charge_current, WholePicture.twentyfour_eleven,
    fun p q hp hq D E => Formulas.sweep p q hp hq D E,
    fun p q harc θ u => WholePicture.one_arc_phase p q harc θ u⟩
  · norm_num [Comparison.Law.Phi]
  · norm_num [Comparison.Law.Phi]
  · have e4 : I ^ 4 = 1 := Complex.I_pow_four
    have e2 : I ^ 2 = -1 := Complex.I_sq
    rw [Comparison.Law.Phi, e4, e2]
    norm_num
  · have e2 : (-I) ^ 2 = -1 := by rw [neg_sq, Complex.I_sq]
    have e4 : (-I) ^ 4 = 1 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, e2]
      norm_num
    rw [Comparison.Law.Phi, e4, e2]
    norm_num

end Comparison.System
