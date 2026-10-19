import Comparison.Law.Rows

/-!
# Book XXIV in Lean, part C

Proposition 211: the retained rows written as compositions whose factors are the
one rule's values at their divided sets and counts of the walk, each equal to its row of `Law/Rows.lean`. Parts A and B
(`FactorsA.lean`, `FactorsB.lean`) hold Propositions 200 to 210; this file restates the factors it needs
so that it stands alone.

* `LOmegaR_eq`: `L(Ω) = 1 + L@{} = 6`.
* `rowPRule_eq`: **the proton** `L(Ω)M + C_h + (1/L(Ω)) log E_U({}) + V_{B_L}(a) + V′_{B_h̄}(a)/Eℓ`
  with `L(Ω) = 1 + L@{}` is `rowP`, the `protonPole` in `(1836.152673412, 1836.1526734121)`.
* `rowLam_first_order`: **the Λ** `E_U({})^{v}` with `v = 60/320`, the first-order rate of the available
  transitions along the last-step direction (Proposition 204's reading; the exact zero under the same weight is another
  number, see `FactorsD.lean`).
* `proton_radius_factor`: **`r_p = Eℓ^{s@{n}} λ_p`**, `16^{1/2} = 4`.
* `rows_rule_values`: the remaining rows' factors at their divided sets: `k_C b = 21/16` (Δ), the clock's
  exponent `−k_C s@{h} = −3/2` and the ends `2/|Φ@{}| = 38` (π⁰), `arg z@F = π` (π±), `2k_C = 6` (ρ),
  `|u_S| = 1/4` and `1/L(Ω) = 1/6` (the mass operator), `R_ud = 34/74`, `κ`'s base `e/t = 3/2` at
  `{t, n}` with the exponent `Eℓ/E P`, and `1/α`'s `c_L f = 27/3700` with `f = e@{t,n}²/N(C)`.
-/

open Comparison Comparison.Law Matrix

namespace Comparison.RuleAndLaw

/-- `L(Ω) = 1 + L@{}`, the comparison at the singlet as one more than the comparison at here. -/
noncomputable def LOmegaR : ℝ := 1 + (LZ sHere : ℝ)

theorem LOmegaR_eq : LOmegaR = 6 := by
  rw [LOmegaR, show LZ sHere = 5 by decide]
  norm_num

/-- **The proton with every `6` a rule value**, `L(Ω) = 1 + L@{}`. -/
noncomputable def rowPRule : ℝ :=
  LOmegaR * 296 + 60 + (1 / LOmegaR) * Real.log (EUS sHere) + volume BL (aS sHere).re +
    (-(7 * (aS sHere).re ^ 6)) / 16

theorem rowPRule_eq : rowPRule = rowP ∧ rowPRule = protonPole ∧
    (1836.152673412 : ℝ) < rowPRule ∧ rowPRule < 1836.1526734121 := by
  have h : rowPRule = rowP := by
    rw [rowPRule, rowP, LOmegaR_eq]
  refine ⟨h, h.trans row_p.1, ?_, ?_⟩
  · rw [h]
    exact row_p.2.1
  · rw [h]
    exact row_p.2.2

/-- **The Λ at the first order of its available-transition weight:** `E_U({})^{v}`, `v = 60/320` the first-order
rate of the weight on the sixty available transitions along the last-step direction. -/
theorem rowLam_first_order :
    rowLam = (EUS sHere) ^ (piU ⬝ᵥ (hadPow lawP (availableTransitionsAlongX 0) 1 *ᵥ 1)) ∧
      rowLam = (5 / 2 : ℝ) ^ (3 / 16 : ℝ) := by
  refine ⟨?_, row_Lam.1⟩
  rw [row_Lam.2, rowLam]

/-- **`r_p = Eℓ^{s@{n}} λ_p`**: the root, read at `{n}`, of the mean excursion `Eℓ = 16`. -/
theorem proton_radius_factor : (16 : ℝ) ^ (powS sSinglet) = 4 := by
  rw [table_singlet.2.2.2.2.1, ← Real.sqrt_eq_rpow, show (16 : ℝ) = 4 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]

/-- **The factors of the other retained rows, each the rule's value at its divided set or a count.** -/
theorem rows_rule_values :
    -- the Δ: `k_C b(w@{}) = 21/16`
    ((((LZ sHere - LZ sC) / 2 : ℤ) : ℝ) * (bS sHere).re = 21 / 16) ∧
    -- the π⁰: the clock's exponent `−k_C s@{h} = −3/2`, the two closed ends `2/|Φ@{}| = 38`
    (-((((LZ sHere - LZ sC) / 2 : ℤ) : ℝ) * powS sLastDirection) = -(3 / 2)) ∧ endsReturn sHere = 38 ∧
    -- the π±: the plane's phase `arg z@F = π`
    Complex.arg (zS sF) = Real.pi ∧
    -- the ρ: the transfer's divisor `2k_C = 6`
    (2 * ((((LZ sHere - LZ sC) / 2 : ℤ) : ℝ)) = 6) ∧
    -- the mass operator: `|u_S| = 1/4` at both signs of a plane, `1/L(Ω) = 1/6`
    ‖uS sPlane‖ = 1 / 4 ∧ ‖uS sPlaneSinglet‖ = 1 / 4 ∧ 1 / LOmegaR = 1 / 6 ∧
    -- `κ`'s base at `{t, n}`
    eS sLineSinglet / tS sLineSinglet = 3 / 2 ∧
    -- `1/α`'s plane meeting `f = e@{t,n}²/N(C)` and the share `c_L f`
    meetS sLineSinglet (NS sC) = 9 / 250 ∧ (15 / 74 : ℝ) * (9 / 250) = 27 / 3700 := by
  have hk : ((LZ sHere - LZ sC) / 2 : ℤ) = 3 := by decide
  have hu : ∀ S : Finset (Fin 6), ‖uS S‖ = 1 / 4 := by
    intro S
    rw [uS, norm_div, zS, norm_pow, Complex.norm_I, one_pow]
    norm_num
  have hp : powS sLastDirection = 1 / 2 := (table_line sLastDirection (Or.inr rfl)).2.2.2.2.1
  have hF : zS sF = -1 := (table_lineSinglet sF (Or.inr (Or.inr (Or.inr rfl)))).1
  refine ⟨?_, ?_, piece_38, ?_, ?_, hu _, hu _, ?_, piece_kappa_base, piece_f, by norm_num⟩
  · rw [hk, piece_b_here]
    norm_num
  · rw [hk, hp]
    norm_num
  · rw [hF, Complex.arg_neg_one]
  · rw [hk]
    norm_num
  · rw [LOmegaR_eq]

end Comparison.RuleAndLaw

#print axioms Comparison.RuleAndLaw.LOmegaR_eq
#print axioms Comparison.RuleAndLaw.rowPRule_eq
#print axioms Comparison.RuleAndLaw.rowLam_first_order
#print axioms Comparison.RuleAndLaw.proton_radius_factor
#print axioms Comparison.RuleAndLaw.rows_rule_values
