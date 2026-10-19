import Comparison.Article.QNucleon
import Comparison.Law.Rows

/-!
# The nuclei (Proposition 125; Eq. (50); Proposition S125 of the public edition)

* `incPoly`, `incidence_light` (**Eq. (50)**): **`B(A, Z) = B_d [C(A,2) + (13/16) C(A,3) + (61/16) C(A,4)] −
  (α m_p/9) C(Z,2)`**, whose values at `(2, 1)`, `(3, 1)`, `(3, 2)`, `(4, 2)` are the deuteron, the triton, the helion
  and helium-4 of rows G10, N01, N02, N03 (`v_D − 3 = 13/16`, `v_D = 61/16`).
* `vD_three_ways`: **`v_D = Var D = 61/16 = 3 + χ_A Var Q/Eℓ = [(Var P − Var Q)² + 4 Cov²]/(9 Eℓ²)`**, with
  `Var D` the spread of the clock's ten gaps (`Law/Rows.lean`: `clock_moments`).
* `betaC`, `cluster_bonds` (**the cluster bonds**): `B(4n, 2n) = n B_α + β_n χ_A B_d + Δ_at(2n)`,
  **`β_n = 0, 3, 6, 8` for `n = 2, …, 5` and `3n − 6` beyond**, `χ_A = 13/12`, for the thirteen rows N04 to N16.
* `saturation_point`: **`r₀ = k_C |u| λ_p/a = 3λ_p/(4a)`, `n₀ = 3/(4π r₀³)`, `e₀ = −m_p a² n_s`** with
  `n_s = 39/40`: rows N21, N22.
-/

namespace Comparison.Article

open Real

/-! ## The incidence polynomial -/

/-- **The incidence polynomial** over pairs, triangles and tetrahedra, less the Coulomb pairs. -/
noncomputable def incPoly (Bd c : ℝ) (A Z : ℕ) : ℝ :=
  Bd * ((A.choose 2 : ℝ) + 13 / 16 * (A.choose 3 : ℝ) + 61 / 16 * (A.choose 4 : ℝ)) - c * (Z.choose 2 : ℝ)

/-- **Eq. (50): the light nuclei are the incidence polynomial** at `(2, 1)`, `(3, 1)`, `(3, 2)`, `(4, 2)`. -/
theorem incidence_light :
    incPoly qBd qCoul 2 1 = qBd ∧ incPoly qBd qCoul 3 1 = qBt ∧ incPoly qBd qCoul 3 2 = qBh ∧
      incPoly qBd qCoul 4 2 = qBa ∧ qCoul = qAlpha * qMp / 9 ∧
      ((8.481159640565 : ℝ) < rowN01 ∧ rowN01 < 8.481159640575) ∧
      ((7.720392725255 : ℝ) < rowN02 ∧ rowN02 < 7.720392725265) ∧
      ((28.29763250885 : ℝ) < rowN03 ∧ rowN03 < 28.29763250895) := by
  refine ⟨?_, ?_, ?_, ?_, rfl, rowN01_digits, rowN02_digits, rowN03_digits⟩ <;>
  · simp only [incPoly, qBt, qBh, qBa]
    norm_num [Nat.choose]

/-- **`v_D = 61/16` three ways:** the spread of the clock's gaps, `3 + χ_A Var Q/Eℓ`, and
`[(Var P − Var Q)² + 4 Cov²]/(9Eℓ²)` with `Var P = 84`, `Var Q = 12`, `Cov = 30`, `Eℓ = 16`. -/
theorem vD_three_ways :
    (1 / 10) * ∑ i, Comparison.Law.clockGap Comparison.Law.sLastDirectionSinglet i ^ 2 - 2 ^ 2 = 61 / 16 ∧
      (3 : ℝ) + 13 / 12 * 12 / 16 = 61 / 16 ∧ (((84 : ℝ) - 12) ^ 2 + 4 * 30 ^ 2) / (9 * 16 ^ 2) = 61 / 16 ∧
      (61 / 16 : ℝ) - 3 = 13 / 16 := by
  refine ⟨Comparison.Law.clock_moments.2, by norm_num, by norm_num, by norm_num⟩

/-! ## The cluster bonds -/

/-- **The cluster bonds** `β_n = 0, 3, 6, 8` for `n = 2, …, 5` and `3n − 6` beyond. -/
noncomputable def betaC (n : ℕ) : ℝ :=
  if n = 2 then 0 else if n = 3 then 3 else if n = 4 then 6 else if n = 5 then 8 else 3 * n - 6

/-- The atomic term `Δ_at(Z)`: the Thomas–Fermi energy of the `Z` electrons less their measured binding `E_e`,
in MeV. -/
noncomputable def atomicCorr (Z : ℝ) (Ee : ℝ) : ℝ :=
  (qCTF * Z ^ (7 / 3 : ℝ) * qMe * qAlpha ^ 2 * 1000000 - Ee) * (1 / 1000000)

/-- **The cluster bonds:** `B(4n, 2n) = n B_α + β_n χ_A B_d + Δ_at(2n)` for the rows N04 to N16, `χ_A = 13/12`. -/
theorem cluster_bonds :
    rowN04 = (2 : ℝ) * qBa + betaC 2 * (13 / 12) * qBd + atomicCorr 4 ((135984345996929 : ℝ) / 2500000000000) ∧
      rowN05 = (3 : ℝ) * qBa + betaC 3 * (13 / 12) * qBd + atomicCorr 6 ((407953037990787 : ℝ) / 5000000000000) ∧
      rowN06 = (4 : ℝ) * qBa + betaC 4 * (13 / 12) * qBd + atomicCorr 8 ((135984345996929 : ℝ) / 1250000000000) ∧
      rowN07 = (5 : ℝ) * qBa + betaC 5 * (13 / 12) * qBd + atomicCorr 10 ((135984345996929 : ℝ) / 1000000000000) ∧
      rowN08 = (6 : ℝ) * qBa + betaC 6 * (13 / 12) * qBd + atomicCorr 12 ((407953037990787 : ℝ) / 2500000000000) ∧
      rowN09 = (7 : ℝ) * qBa + betaC 7 * (13 / 12) * qBd + atomicCorr 14 ((951890421978503 : ℝ) / 5000000000000) ∧
      rowN10 = (8 : ℝ) * qBa + betaC 8 * (13 / 12) * qBd + atomicCorr 16 ((135984345996929 : ℝ) / 625000000000) ∧
      rowN11 = (9 : ℝ) * qBa + betaC 9 * (13 / 12) * qBd + atomicCorr 18 ((1223859113972361 : ℝ) / 5000000000000) ∧
      rowN12 = (10 : ℝ) * qBa + betaC 10 * (13 / 12) * qBd + atomicCorr 20 ((135984345996929 : ℝ) / 500000000000) ∧
      rowN13 = (11 : ℝ) * qBa + betaC 11 * (13 / 12) * qBd + atomicCorr 22 ((1495827805966219 : ℝ) / 5000000000000) ∧
      rowN14 = (12 : ℝ) * qBa + betaC 12 * (13 / 12) * qBd + atomicCorr 24 ((407953037990787 : ℝ) / 1250000000000) ∧
      rowN15 = (13 : ℝ) * qBa + betaC 13 * (13 / 12) * qBd + atomicCorr 26 ((1767796497960077 : ℝ) / 5000000000000) ∧
      rowN16 = (14 : ℝ) * qBa + betaC 14 * (13 / 12) * qBd + atomicCorr 28 ((951890421978503 : ℝ) / 2500000000000) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rowN04, atomicCorr]; simp only [betaC]; norm_num
  · rw [rowN05, atomicCorr]; simp only [betaC]; norm_num
  · rw [rowN06, atomicCorr]; simp only [betaC]; norm_num
  · rw [rowN07, atomicCorr]; simp only [betaC]; norm_num
  · rw [rowN08, atomicCorr]; simp only [betaC]; norm_num
  · rw [rowN09, atomicCorr]; simp only [betaC]; norm_num
  · rw [rowN10, atomicCorr]; simp only [betaC]; norm_num
  · rw [rowN11, atomicCorr]; simp only [betaC]; norm_num
  · rw [rowN12, atomicCorr]; simp only [betaC]; norm_num
  · rw [rowN13, atomicCorr]; simp only [betaC]; norm_num
  · rw [rowN14, atomicCorr]; simp only [betaC]; norm_num
  · rw [rowN15, atomicCorr]; simp only [betaC]; norm_num
  · rw [rowN16, atomicCorr]; simp only [betaC]; norm_num

/-! ## The saturation point -/

/-- **The saturation point:** `r₀ = k_C|u|λ_p/a = 3λ_p/(4a)`, `n₀ = 3/(4π r₀³)`, `e₀ = −m_p a² n_s`, `n_s = 39/40`. -/
theorem saturation_point :
    qR0 = 3 * (1 / 4) * qLp / (5 / 38) ∧ rowN21 = 3 / (4 * π * qR0 ^ 3) ∧ rowN22 = -(39 / 40 * (qMp * (5 / 38) ^ 2)) ∧
      ((0.1385842276655 : ℝ) < rowN21 ∧ rowN21 < 0.1385842276665) ∧
      ((-15.83821480585 : ℝ) < rowN22 ∧ rowN22 < -15.83821480575) := by
  refine ⟨by rw [qR0] <;> ring, by rw [rowN21] <;> ring, by rw [rowN22, qMa2] <;> norm_num, rowN21_digits,
    rowN22_digits⟩

end Comparison.Article
