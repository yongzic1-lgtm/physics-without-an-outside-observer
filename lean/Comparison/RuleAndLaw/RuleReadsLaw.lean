import Comparison.Law.Rule
import Comparison.Existence.Excursion
import Comparison.Existence.Return

/-!
# The one rule reads the law at its divided set

The law `Z = det(I − uB[U])⁻¹` counts every closed walk once; its
first return is the excursion (Proposition 55: `1 − 1/R₋(u) = Φ(4u)`, Return.lean), and the one rule reads
it at a divided set `S` with the step weight `u_S = z_S/4` (Proposition 56). These theorems make that
reading exact at all 64 divided sets:

* `four_uS`, `norm_zS`: `4u_S = z_S` and `|z_S| = 1`.
* `rule_reads_signed_return`: **the rule's `Φ_S` is the law's signed first return at `u_S`**: the
  sum over all excursions `w`, each with its Clifford sign and weight `(4u_S)^{|w|}/(5·4^{|w|−1})`,
  converges to `Φ_S` (`signed_gf`).
* `rule_reads_resolvent`: **`1 − 1/R₋(u_S) = Φ_S`**, with `R₋(u) = (1 + 3u²)/(1 + 3u² + 16u⁴)` the
  law's signed diagonal return at the singlet (Proposition 55).
* `rule_reads_excursion`: the counted excursion at `u_S` converges to `F(z_S)`, the unsigned first return.
* `rule_reads_excursion_values`: `F(1) = 1` at the even divided sets with `z = 1`, and the signed returns
  `Φ = −1/19` (even) and `−1/13` (odd), the one sign `P = z_S²` deciding between them.
-/

open Comparison Comparison.Law

namespace Comparison.RuleAndLaw

theorem four_uS (S : Finset (Fin 6)) : 4 * uS S = zS S := by
  rw [uS]
  ring

theorem norm_zS (S : Finset (Fin 6)) : ‖zS S‖ = 1 := by
  rw [zS, norm_pow, Complex.norm_I, one_pow]

/-- **The rule's `Φ_S` is the law's signed first return read at the step weight `u_S = z_S/4`.** -/
theorem rule_reads_signed_return (S : Finset (Fin 6)) :
    HasSum (fun n => (signedLaw n : ℂ) * (4 * uS S) ^ n) (PhiS S) := by
  rw [four_uS, PhiS, Phi]
  exact signed_gf (zS S) (le_of_eq (norm_zS S))

/-- **The counted excursion at `u_S`** converges to `F(z_S) = z⁴(1 + z)/(16 − 8z − 3z² − 3z³)`. -/
theorem rule_reads_excursion (S : Finset (Fin 6)) :
    HasSum (fun n => (excursionLaw n : ℂ) * (4 * uS S) ^ n)
      (zS S ^ 4 * (1 + zS S) / (16 - 8 * zS S - 3 * zS S ^ 2 - 3 * zS S ^ 3)) := by
  rw [four_uS]
  exact excursion_gf (zS S) (le_of_eq (norm_zS S))

/-- **`1 − 1/R₋(u_S) = Φ_S`**: the law's signed diagonal return at the singlet, read at `u_S`,
renews to the rule's signed excursion. -/
theorem rule_reads_resolvent (S : Finset (Fin 6)) :
    1 - 1 / ((1 + 3 * uS S ^ 2) / (1 + 3 * uS S ^ 2 + 16 * uS S ^ 4)) = PhiS S := by
  have h2 : uS S ^ 2 = (signS S : ℂ) / 16 := uS_sq S
  have h4 : uS S ^ 4 = 1 / 256 := by
    rw [show uS S ^ 4 = (uS S ^ 2) ^ 2 by ring, h2]
    rcases signS_cases S with h | h <;> rw [h] <;> norm_num
  have hD : 1 + 3 * uS S ^ 2 + 16 * uS S ^ 4 ≠ 0 := by
    rw [h2, h4]
    rcases signS_cases S with h | h <;> rw [h] <;> norm_num
  have hD' : 1 + 3 * uS S ^ 2 ≠ 0 := by
    rw [h2]
    rcases signS_cases S with h | h <;> rw [h] <;> norm_num
  obtain ⟨e1, e2⟩ := signed_excursion_from_returns (uS S) hD hD'
  rw [e1, e2, four_uS, PhiS, Phi]

/-- At the even divided sets with `z_S = 1` the counted excursion closes, `F(1) = 1`; the signed excursion is
`−1/19` at every even divided set and `−1/13` at every odd one. -/
theorem rule_reads_excursion_values (S : Finset (Fin 6)) :
    (zS S = 1 → zS S ^ 4 * (1 + zS S) / (16 - 8 * zS S - 3 * zS S ^ 2 - 3 * zS S ^ 3) = 1) ∧
      (Even S.card → PhiS S = -1 / 19) ∧ (Odd S.card → PhiS S = -1 / 13) := by
  refine ⟨fun h => ?_, (PhiS_values S).1, (PhiS_values S).2⟩
  rw [h]
  norm_num

end Comparison.RuleAndLaw

#print axioms Comparison.RuleAndLaw.rule_reads_signed_return
#print axioms Comparison.RuleAndLaw.rule_reads_excursion
#print axioms Comparison.RuleAndLaw.rule_reads_resolvent
#print axioms Comparison.RuleAndLaw.rule_reads_excursion_values
#print axioms Comparison.RuleAndLaw.four_uS
#print axioms Comparison.RuleAndLaw.norm_zS
