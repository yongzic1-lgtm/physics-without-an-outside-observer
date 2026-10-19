import Comparison.System.Postulates
import Comparison.System.Existence.Numbered
import Comparison.System.Existence.ExcursionVisits
import Comparison.Existence.Moments
import Comparison.Existence.AvailableTransitions
import Comparison.Colour.Inventory
import Comparison.RuleAndLaw.CriticalGerm
import Comparison.WholePicture.Polar
import Comparison.ArticleStatements.Radar

/-!
# SI S3, statements 9 to 11: the two first returns, one excursion, the Green function and the polar step

About the model; every candidate system is the model up to one
rotation (`System.uniqueness`).
-/

namespace Comparison.System

open Matrix Complex Polynomial

namespace S3

/-- **The exponential of a reflection.** For an idempotent `P`, `X = 2P − 1` has `X² = 1` and
`exp(tX) = e^t P + e^{−t}(1 − P)`. -/
theorem exp_smul_reflection {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℝ)
    (hP : P * P = P) (t : ℝ) :
    NormedSpace.exp (t • ((2 : ℝ) • P - 1)) = Real.exp t • P + Real.exp (-t) • (1 - P) := by
  have hX : ∀ k : ℕ, ((2 : ℝ) • P - 1) ^ k = P + ((-1 : ℝ) ^ k) • (1 - P) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih, pow_succ]
      simp only [add_mul, mul_sub, sub_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one, hP]
      module
  have h1 : HasSum (fun k : ℕ => t ^ k / k.factorial) (Real.exp t) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp t
  have h2 : HasSum (fun k : ℕ => (-t) ^ k / k.factorial) (Real.exp (-t)) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp (-t)
  have hsum := (h1.smul_const P).add (h2.smul_const (1 - P))
  rw [NormedSpace.exp_eq_tsum ℝ]
  refine HasSum.tsum_eq ?_
  convert hsum using 1
  funext k
  rw [_root_.smul_pow, hX k, neg_pow]
  module

end S3

open S3

/-- **SI S3, statement 9: the two first returns.** The plain and the signed first returns from the
singlet back to the singlet, with `z = 4u` (the weights `f_n`, `φ_n` of the excursions of length `n`), have the
generating functions `F(z) = z⁴(1 + z)/(16 − 8z − 3z² − 3z³)` and `Φ(z) = −z⁴/(16 + 3z²)` on
`‖z‖ ≤ 1`; `F(1) = 1`, `F′(1) = Eℓ = 16`, `Var ℓ = 156`, `Φ(±1) = −1/19`, `Φ(±i) = −1/13`. -/
theorem S3_9 :
    (∀ z : ℂ, ‖z‖ ≤ 1 → HasSum (fun n => (excursionLaw n : ℂ) * z ^ n) (excursionGF z)) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 → HasSum (fun n => (signedLaw n : ℂ) * z ^ n) (Law.Phi z)) ∧
    HasSum excursionLaw 1 ∧
    HasSum (fun n : ℕ => (n : ℝ) * excursionLaw n) 16 ∧
    (∑' n : ℕ, (n : ℝ) ^ 2 * excursionLaw n) - (∑' n : ℕ, (n : ℝ) * excursionLaw n) ^ 2 = 156 ∧
    Law.Phi 1 = -1 / 19 ∧ Law.Phi (-1) = -1 / 19 ∧
    Law.Phi I = -1 / 13 ∧ Law.Phi (-I) = -1 / 13 ∧
    HasSum signedLaw (-1 / 19) ∧ HasSum (fun n => (signedLaw n : ℂ) * I ^ n) (-1 / 13) := by
  have hI2 : (-I) ^ 2 = -1 := by rw [neg_sq, I_sq]
  have hI4 : (-I) ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hI2]; norm_num
  refine ⟨excursion_gf_eq, signed_gf_eq, excursion_total, excursion_mean, excursion_variance, ?_, ?_, ?_, ?_,
    Φ_one, Φ_I⟩
  · simp only [Law.Phi]
    norm_num
  · simp only [Law.Phi]
    norm_num
  · simp only [Law.Phi, I_pow_four, I_sq]
    norm_num
  · simp only [Law.Phi, hI4, hI2]
    norm_num

/-- **SI S3, statement 10: the visits, the visits to the symmetric states and the transitions of one excursion.** An excursion meets
`P` symmetric states and `Q` vector states (`Existence.cP w`, `Existence.cQ w`); an excursion of length
`n` has the weight `1/(5·4ⁿ⁻¹)` (`Existence.statLaw`). Over the excursions: `EP = 10`, `EQ = 5`,
`Var P = 84`, `Var Q = 12`, `Cov(P, Q) = 30`, `Var P − Cov²/Var Q = 9`, and `ℓ = 1 + P + Q` for
every excursion; the visits to the symmetric states over the excursions have the generating function
`G_P(x) = Σ_m Σ_{excursions of length m} x^P/(5·4^{m−1}) = x(1 + x)/(16 − 11x − 3x²)` for `‖x‖ ≤ 1`. With
`F(z, x, y)` the excursion's generating function in the steps, the arrivals at the vector states and the visits to the symmetric states
(`excursionF`, the solution of the first-step equations), these moments are `∂_yF`, `∂_xF`, `∂_y²F`,
`∂_x²F`, `∂_x∂_yF` at `z = x = y = 1`, so `EP = ∂_yF = 10`, `EQ = ∂_xF = 5`; `G_P(x) = F(1, 1, x)`,
with the pole `x_c = (√313 − 11)/6`; an excursion begun after a step along `h` has 74 states, `M = 296`
transitions,
`C_h = 60` along `h`, `C_j = 59` along each other line and 34 states that leave `h` undivided; and
its self-interaction add to `Σ_transitions (6 + [s = h]) = 1836`. Uses Prop. 29 (`prop_29`) and Prop. 31. -/
theorem S3_10 :
    ((∀ m, Existence.statLaw Existence.fP m =
        (∑ w ∈ excursions m, (Existence.cP w : ℝ)) / (5 * 4 ^ (m - 1))) ∧
      (∀ m, Existence.statLaw Existence.fQ m =
        (∑ w ∈ excursions m, (Existence.cQ w : ℝ)) / (5 * 4 ^ (m - 1))) ∧
      HasSum (Existence.statLaw Existence.fP) 10 ∧ HasSum (Existence.statLaw Existence.fQ) 5 ∧
      Existence.varP = 84 ∧ Existence.varQ = 12 ∧ Existence.covPQ = 30 ∧
      Existence.varP - Existence.covPQ ^ 2 / Existence.varQ = 9 ∧
      (∀ w : List (Fin 5), IsExcursion w → 1 + Existence.cP w + Existence.cQ w = w.length) ∧
      ∀ x : ℂ, ‖x‖ ≤ 1 → HasSum (fun m => (∑ w ∈ excursions m, x ^ Existence.cP w) / (5 * 4 ^ (m - 1)))
        (x * (1 + x) / (16 - 11 * x - 3 * x ^ 2))) ∧
    (deriv (fun y => excursionF 1 1 y) 1 = Existence.excursionMean Existence.fP ∧
      deriv (fun x => excursionF 1 x 1) 1 = Existence.excursionMean Existence.fQ ∧
      deriv (deriv (fun y => excursionF 1 1 y)) 1 = Existence.excursionMean Existence.fPP ∧
      deriv (deriv (fun x => excursionF 1 x 1)) 1 = Existence.excursionMean Existence.fQQ ∧
      deriv (fun x => deriv (fun y => excursionF 1 x y) 1) 1 = Existence.excursionMean Existence.fPQ) ∧
    deriv (fun y => excursionF 1 1 y) 1 = 10 ∧ deriv (fun x => excursionF 1 x 1) 1 = 5 ∧
    (deriv (deriv (fun y => excursionF 1 1 y)) 1 + deriv (fun y => excursionF 1 1 y) 1 -
        (deriv (fun y => excursionF 1 1 y) 1) ^ 2 = 84 ∧
      deriv (deriv (fun x => excursionF 1 x 1)) 1 + deriv (fun x => excursionF 1 x 1) 1 -
        (deriv (fun x => excursionF 1 x 1) 1) ^ 2 = 12 ∧
      deriv (fun x => deriv (fun y => excursionF 1 x y) 1) 1 -
        deriv (fun y => excursionF 1 1 y) 1 * deriv (fun x => excursionF 1 x 1) 1 = 30 ∧
      (84 : ℝ) - 30 ^ 2 / 12 = 9 ∧ (84 : ℝ) + 12 + 2 * 30 = 156) ∧
    (∀ x : ℝ, GP x = excursionF 1 1 x ∧ GP x = x * (1 + x) / (16 - 11 * x - 3 * x ^ 2)) ∧
    (∀ x : ℝ, 16 - 11 * x - 3 * x ^ 2 = -3 * (x - xc) * (x - xc')) ∧
    xc = (Real.sqrt 313 - 11) / 6 ∧ 1 < xc ∧
    (∀ h : Fin 5, (excursionStates h).card = 74 ∧ ∑ j, alongCount h j = 296 ∧
      alongCount h h = 60 ∧ (∀ j, j ≠ h → alongCount h j = 59) ∧
      ((excursionStates h).filter fun s => h ∉ disagreeSet s.1).card = 34 ∧
      ∑ p ∈ Finset.univ.filter (fun p : State × State => inExcursion h p.1 = true ∧ Continues p.1 p.2),
        (6 + if p.2.2 = h then 1 else 0) = 1836 ∧ 6 * 296 + 60 = 1836) := by
  obtain ⟨-, -, -, -, -, hP, hQ, sP, sQ, -, -, -, vP, vQ, cv, v9, hlen, dP, dQ, dPP, dQQ, dPQ⟩ :=
    prop_29
  refine ⟨⟨hP, hQ, sP, sQ, vP, vQ, cv, v9, hlen, Existence.plane_visits_gf⟩,
    ⟨dP, dQ, dPP, dQQ, dPQ⟩, EP_eq, EQ_eq, visit_moments, fun x => ⟨GP_eq x, rfl⟩, GP_denominator,
    rfl, xc_gt_one,
    fun h => ⟨card_excursionStates h, availableTransitions_total h, (availableTransitions_along h).1, (availableTransitions_along h).2,
      availableTransitions_up h, transition_inventory h, by norm_num⟩⟩

/-- **SI S3, statement 11: the Green function, the polar step, the charge current and 24/11.**
(i) `G = (7 + A)/32 − 3𝐉/128` satisfies the four Penrose equations for `5 − A` and is the only
matrix that does: `(5 − A)⁺ = G`; the resistance from the singlet to every plane is `56/128 = 7/16 = b`
and to every vector state `48/128`. (ii) `BᵀB = 1 + 15Π` with `Π` the projector on the groups of
five targets of one two-spinor state; `|B| = 1 + 3Π` is symmetric with `|B|² = BᵀB` and
`det(X − |B|) = (X − 1)⁶⁴(X − 4)¹⁶`: the singular values of `B` are 1 and 4;
`|B| = 2(e^ξ Π + e^{−ξ}(1 − Π)) = 2e^{ξ(2Π − I)}` with `ξ = log 2`, and `tanh(ξ/4) = 3 − 2√2 =
tan²(π/8)`.
(iii) The line charges have `c = 2 Var Q = 8/15`. (iv) `Tr L²/4 = 24` against the `1 + 10 = 11`
positive vertices of `L`. -/
theorem S3_11 :
    (WholePicture.lapM * WholePicture.greenM * WholePicture.lapM = WholePicture.lapM ∧
      WholePicture.greenM * WholePicture.lapM * WholePicture.greenM = WholePicture.greenM ∧
      (WholePicture.lapM * WholePicture.greenM)ᵀ = WholePicture.lapM * WholePicture.greenM ∧
      (WholePicture.greenM * WholePicture.lapM)ᵀ = WholePicture.greenM * WholePicture.lapM) ∧
    (∀ X : Matrix (Fin 16) (Fin 16) ℝ,
      WholePicture.lapM * X * WholePicture.lapM = WholePicture.lapM →
      X * WholePicture.lapM * X = X → (WholePicture.lapM * X)ᵀ = WholePicture.lapM * X →
      (X * WholePicture.lapM)ᵀ = X * WholePicture.lapM → X = WholePicture.greenM) ∧
    WholePicture.lapM = (5 : ℝ) • (1 : Matrix (Fin 16) (Fin 16) ℝ) - A ℝ ∧
    WholePicture.greenM = (1 / 32 : ℝ) • ((7 : ℝ) • (1 : Matrix (Fin 16) (Fin 16) ℝ) +
      Matrix.of fun x y => (WholePicture.adjZ x y : ℝ)) -
        (3 / 128 : ℝ) • (Matrix.of fun _ _ => (1 : ℝ)) ∧
    (∀ f : Fin 16, (disagreeSet f).card = 2 → RuleAndLaw.res128 0 f = 56) ∧
    (∀ l : Fin 16, (disagreeSet l).card = 4 → RuleAndLaw.res128 0 l = 48) ∧
    (56 : ℚ) / 128 = 7 / 16 ∧
    stepRᵀ * stepR = 1 + (15 : ℝ) • WholePicture.lastDirectionProj ∧
    WholePicture.lastDirectionProj * WholePicture.lastDirectionProj = WholePicture.lastDirectionProj ∧
    WholePicture.absB = 1 + (3 : ℝ) • WholePicture.lastDirectionProj ∧
    WholePicture.absB.IsHermitian ∧
    WholePicture.absB * WholePicture.absB = stepRᵀ * stepR ∧
    WholePicture.absB.charpoly = (X - C (1 : ℝ)) ^ 64 * (X - C (4 : ℝ)) ^ 16 ∧
    (stepRᵀ * stepR).charpoly = (X - C (1 : ℝ)) ^ 64 * (X - C (16 : ℝ)) ^ 16 ∧
    WholePicture.absB = (2 : ℝ) • (Real.exp (Real.log 2) • WholePicture.lastDirectionProj +
      Real.exp (-Real.log 2) • (1 - WholePicture.lastDirectionProj)) ∧
    WholePicture.absB =
      (2 : ℝ) • NormedSpace.exp (Real.log 2 • ((2 : ℝ) • WholePicture.lastDirectionProj - 1)) ∧
    Real.tanh (Real.log 2 / 4) = 3 - 2 * Real.sqrt 2 ∧
    Real.tan (Real.pi / 8) ^ 2 = 3 - 2 * Real.sqrt 2 ∧
    2 * ((∑ s, WholePicture.lineCharge s ^ 2) / 5 - ((∑ s, WholePicture.lineCharge s) / 5) ^ 2) =
      8 / 15 ∧
    (L * L).trace / 4 = 24 ∧
    Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' L) 6) +
      Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' L) 2) = 11 := by
  obtain ⟨r1, r2, r3⟩ := RuleAndLaw.resistance_values
  exact ⟨WholePicture.green_penrose, fun X h1 h2 h3 h4 => WholePicture.green_pinv X h1 h2 h3 h4,
    wholePicture_lapM_eq, WholePicture.greenM_eq, r2, r3, by norm_num, WholePicture.stepR_gram_proj,
    WholePicture.lastDirectionProj_idem, rfl, WholePicture.absB_symm, WholePicture.absB_sq,
    WholePicture.absB_charpoly, WholePicture.stepR_gram_charpoly, WholePicture.absB_polar,
    by rw [exp_smul_reflection _ WholePicture.lastDirectionProj_idem, ← WholePicture.absB_polar],
    ArticleStatements.Radar.tanh_quarter, ArticleStatements.Radar.tan_sq_pi_div_eight,
    WholePicture.charge_current, WholePicture.twentyfour_eleven.1, WholePicture.twentyfour_eleven.2⟩

end Comparison.System
