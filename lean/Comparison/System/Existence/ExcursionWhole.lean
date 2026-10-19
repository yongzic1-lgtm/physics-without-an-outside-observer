import Comparison.System.Existence.Excursion
import Comparison.System.Existence.ExcursionVisits

/-!
# The proof system, the existence layer: Propositions 30 and 31 whole

Prop. 30: there is no excursion of length below four
(`excursions_short`), so the twenty excursions of length four are the shortest. Prop. 31: the states an excursion's steps reach are
the seventy-four for every number of steps from four on (`reach_eq_inExcursion`): the reached set is closed, since the one
state set apart off the start's vertex, `(T_h, h)`, has as predecessors only the five states at the vertex.
-/

namespace Comparison.System.Existence

open Finset

/-- **No excursion is shorter than four steps.** -/
theorem excursions_short : ∀ n < 4, excursions n = ∅ := by
  decide +kernel

/-- One more step adds no state to the seventy-four. -/
theorem reach_fixed : ∀ (h : Fin 5) (s : State),
    (inExcursion h s || (decide (s.1 ≠ 0) && (preds s).any (inExcursion h))) = inExcursion h s := by
  decide +kernel

/-- **The states an excursion's steps reach, from four steps on, are the seventy-four.** -/
theorem reach_eq_inExcursion (h : Fin 5) : ∀ k, 3 ≤ k → ∀ s, reach h k s = inExcursion h s := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact excursionStates_eq_reach h
  | succ k hk ih =>
    intro s
    have e : reach h k = inExcursion h := funext ih
    show (reach h k s || (decide (s.1 ≠ 0) && (preds s).any (reach h k))) = inExcursion h s
    rw [e]
    exact reach_fixed h s

/-- **Proposition 30 (the signed excursion).** `A₋ = Σ_t γ_t ⊗ 1` on the sixteen two-spinor states has `A₋² = 5`; at the end of an
excursion the two-spinor state is `σ_w Ω`, `σ_w = ±1`; `Φ(z) = Σ_n zⁿ Σ_{excursions w, |w| = n} σ_w/(5·4ⁿ⁻¹) = −z⁴/(16 + 3z²)`; the
signed counts of the lengths `4, …, 8` are `−20, 0, 60, 0, −180`; no excursion is shorter than four, and the twenty
shortest excursions are the words `tsts` and come back with `−1`; `Φ(1) = −1/19`, `Φ(i) = −1/13`; an excursion keeps its sign
with chance `9/19` and reverses it with chance `10/19`, `a = (F(1) − Φ(1))/8 = 5/38`; and
`b = Var P/(2(Var P + Var Q)) = 7/16`.

Recognition: the sign `−1` of `tsts` is spin one half; the lean `10/19` toward reversal is attraction. Uses
Props. 4, 10, 24, 29. -/
theorem prop_30_full :
    (∑ t, lineOnRel t) * (∑ t, lineOnRel t) = (5 : ℂ) • (1 : Matrix Two Two ℂ) ∧
    (∀ w : List (Fin 5), relOfWord w = 0 → relLine w = (coef w : ℂ) • Ω ∧ (coef w = 1 ∨ coef w = -1)) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 → HasSum (fun n => (signedLaw n : ℂ) * z ^ n) (-z ^ 4 / (16 + 3 * z ^ 2))) ∧
    [signedExcursionCount 4, signedExcursionCount 5, signedExcursionCount 6, signedExcursionCount 7, signedExcursionCount 8] =
      [-20, 0, 60, 0, -180] ∧
    (∀ n < 4, excursions n = ∅) ∧
    (excursions 4).card = 20 ∧ (∀ w ∈ excursions 4, coef w = -1 ∧ ∃ s t : Fin 5, s ≠ t ∧ w = [t, s, t, s]) ∧
    HasSum signedLaw (-1 / 19) ∧ HasSum (fun n => (signedLaw n : ℂ) * Complex.I ^ n) (-1 / 13) ∧
    ((∑' n, excursionLaw n) + (∑' n, signedLaw n)) / 2 = 9 / 19 ∧
    ((∑' n, excursionLaw n) - (∑' n, signedLaw n)) / 2 = 10 / 19 ∧
    ((∑' n, excursionLaw n) - (∑' n, signedLaw n)) / 8 = 5 / 38 ∧
    varP / (2 * (varP + varQ)) = 7 / 16 := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12⟩ := prop_30
  exact ⟨p1, p2, p3, p4, excursions_short, p5, p6, p7, p8, p9, p10, p11, p12⟩

/-- **Proposition 31 (the transitions of one excursion).** An excursion that begins at a moment whose last-step direction is `h` can be in
`80 − 5 − 1 = 74` states (the five `(∅, t)` end it; `(T_h, h)` is reached only from the start's vertex, by the
undo); they are exactly the states its steps reach, within four steps and for every number of steps from four on; the
uniform law on them is the stationary law of the steps watched on them (each state takes in and gives out the total
weight one); `M = 4·74 = 296` continuations, `C_h = 60` along `h` and `C_j = 59` along each other line;
`c_L = 15/74`, `σ = 75/74`, `η = 295/296`, `σ + 4η = 5`, `η/σ = 59/60`, `σ − 1 = 4(1 − η) = 1/74`; `34` of the `74`
leave `h` undivided, `R_ud = 17/37`.

Recognition: existing tilts a line toward its own direction by one part in `296`. Uses Props. 24, 26. -/
theorem prop_31_full (h : Fin 5) :
    (excursionStates h).card = 74 ∧ (∀ s : State, reach h 3 s = inExcursion h s) ∧
    (∀ k, 3 ≤ k → ∀ s : State, reach h k s = inExcursion h s) ∧
    (∀ s : State, Continues s (lastDirectionRel h, h) → s.1 = 0) ∧
    (∀ s' : State, inExcursion h s' → watchedIn64 h s' = 64) ∧
    (∀ s : State, inExcursion h s → watchedOut64 h s = 64) ∧
    alongCount h h = 60 ∧ (∀ j, j ≠ h → alongCount h j = 59) ∧ ∑ j, alongCount h j = 296 ∧
    (let M : ℚ := ∑ j, (alongCount h j : ℚ)
     let Ch : ℚ := alongCount h h
     let σ : ℚ := 5 * Ch / M
     let η : ℚ := 5 * 59 / M
     Ch / M = 15 / 74 ∧ σ = 75 / 74 ∧ η = 295 / 296 ∧ σ + 4 * η = 5 ∧ η / σ = 59 / 60 ∧
       σ - 1 = 4 * (1 - η) ∧ σ - 1 = 1 / 74 ∧ 6 * M + Ch = 1836) ∧
    ((excursionStates h).filter fun s => h ∉ disagreeSet s.1).card = 34 ∧ (34 : ℚ) / 74 = 17 / 37 := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩ := prop_31 h
  exact ⟨p1, p2, reach_eq_inExcursion h, p3, p4, p5, p6, p7, p8, p9, p10, p11⟩

end Comparison.System.Existence
