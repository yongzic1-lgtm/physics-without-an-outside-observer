import Comparison.System.Existence.ExcursionMoments
import Comparison.System.Existence.Line

/-!
# The proof system, the existence layer: the excursion (Propositions 29 to 31)

Book VI, second half: the excursion (Prop. 29), the signed excursion
(Prop. 30), the transitions of one excursion (Prop. 31). Prop. 29's visits are the moments of the symmetric and vector states the
excursions meet, counted over the excursions (`System/Existence/ExcursionMoments.lean`), not only the derivatives of a rational
function.
-/

namespace Comparison.System.Existence

open Matrix Complex Kronecker

/-- The mean of a statistic over the excursions, `E F = Σ_n Σ_{excursions of length n} F(P, Q)/(5·4ⁿ⁻¹)`. -/
noncomputable def excursionMean (F : ℕ → ℕ → ℤ) : ℝ := ∑' m, statLaw F m

theorem excursionMean_P : excursionMean fP = 10 := by rw [excursionMean, ← lawP_eq, hasSum_lawP.tsum_eq]
theorem excursionMean_Q : excursionMean fQ = 5 := by rw [excursionMean, ← lawQ_eq, hasSum_lawQ.tsum_eq]
theorem excursionMean_PP : excursionMean fPP = 174 := by rw [excursionMean, ← lawPP_eq, hasSum_lawPP.tsum_eq]
theorem excursionMean_QQ : excursionMean fQQ = 32 := by rw [excursionMean, ← lawQQ_eq, hasSum_lawQQ.tsum_eq]
theorem excursionMean_PQ : excursionMean fPQ = 80 := by rw [excursionMean, ← lawPQ_eq, hasSum_lawPQ.tsum_eq]

/-- `Var P = E P(P − 1) + E P − (E P)²`. -/
noncomputable def varP : ℝ := excursionMean fPP + excursionMean fP - excursionMean fP ^ 2
/-- `Var Q = E Q(Q − 1) + E Q − (E Q)²`. -/
noncomputable def varQ : ℝ := excursionMean fQQ + excursionMean fQ - excursionMean fQ ^ 2
/-- `Cov(P, Q) = E PQ − E P · E Q`. -/
noncomputable def covPQ : ℝ := excursionMean fPQ - excursionMean fP * excursionMean fQ

theorem varP_eq : varP = 84 := by rw [varP, excursionMean_PP, excursionMean_P]; norm_num
theorem varQ_eq : varQ = 12 := by rw [varQ, excursionMean_QQ, excursionMean_Q]; norm_num
theorem covPQ_eq : covPQ = 30 := by rw [covPQ, excursionMean_PQ, excursionMean_P, excursionMean_Q]; norm_num

/-- **Proposition 29 (the excursion).** With `f_n` the excursions among the walks of length `n`, divided by `5·4ⁿ⁻¹`:
`F(z) = Σ f_n zⁿ = z⁴(1 + z)/(16 − 8z − 3z² − 3z³)` (for `|z| ≤ 1`); `F(1) = 1`, `Eℓ = F′(1) = Σ n f_n = 16`,
`Var ℓ = 156`; the excursions of length `4, …, 8` number `20, 120, 300, 1200, 4740`; with `P` and `Q` the symmetric and
the vector states an excursion meets, `E P = 10`, `E Q = 5`, `Var P = 84`, `Var Q = 12`, `Cov(P, Q) = 30`,
`Var P − Cov²/Var Q = 9`; an excursion of `ℓ` steps has `ℓ = 1 + P + Q`; and the derivatives of B.29's `F(z, x, y)` at
`(1, 1, 1)` are these moments.

Recognition: a walk comes back to the vertex of its start with chance one, in sixteen steps on average; an excursion
meets one of each of the fifteen two-spinor states other than the singlet on average. Uses Props. 24 to 26, P2 (a). -/
theorem prop_29 :
    (∀ z : ℂ, ‖z‖ ≤ 1 → HasSum (fun n => (excursionLaw n : ℂ) * z ^ n)
      (z ^ 4 * (1 + z) / (16 - 8 * z - 3 * z ^ 2 - 3 * z ^ 3))) ∧
    HasSum excursionLaw 1 ∧ HasSum (fun n : ℕ => (n : ℝ) * excursionLaw n) 16 ∧
    (∑' n : ℕ, (n : ℝ) ^ 2 * excursionLaw n) - (∑' n : ℕ, (n : ℝ) * excursionLaw n) ^ 2 = 156 ∧
    [excursionCount 4, excursionCount 5, excursionCount 6, excursionCount 7, excursionCount 8] = [20, 120, 300, 1200, 4740] ∧
    (∀ m, statLaw fP m = (∑ w ∈ excursions m, (cP w : ℝ)) / (5 * 4 ^ (m - 1))) ∧
    (∀ m, statLaw fQ m = (∑ w ∈ excursions m, (cQ w : ℝ)) / (5 * 4 ^ (m - 1))) ∧
    HasSum (statLaw fP) 10 ∧ HasSum (statLaw fQ) 5 ∧
    HasSum (statLaw fPP) 174 ∧ HasSum (statLaw fQQ) 32 ∧ HasSum (statLaw fPQ) 80 ∧
    varP = 84 ∧ varQ = 12 ∧ covPQ = 30 ∧ varP - covPQ ^ 2 / varQ = 9 ∧
    (∀ w : List (Fin 5), IsExcursion w → 1 + cP w + cQ w = w.length) ∧
    deriv (fun y => excursionF 1 1 y) 1 = excursionMean fP ∧ deriv (fun x => excursionF 1 x 1) 1 = excursionMean fQ ∧
    deriv (deriv (fun y => excursionF 1 1 y)) 1 = excursionMean fPP ∧
    deriv (deriv (fun x => excursionF 1 x 1)) 1 = excursionMean fQQ ∧
    deriv (fun x => deriv (fun y => excursionF 1 x y) 1) 1 = excursionMean fPQ := by
  have hl := excursionCount_values
  simp only [List.cons.injEq] at hl
  refine ⟨excursion_gf, excursion_total, excursion_mean, excursion_variance, ?_, fun m => ?_, fun m => ?_,
    lawP_eq ▸ hasSum_lawP, lawQ_eq ▸ hasSum_lawQ, lawPP_eq ▸ hasSum_lawPP, lawQQ_eq ▸ hasSum_lawQQ,
    lawPQ_eq ▸ hasSum_lawPQ, varP_eq, varQ_eq, covPQ_eq, ?_, fun w hw => excursion_length_eq hw, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.cons.injEq]
    exact ⟨hl.2.2.2.1, hl.2.2.2.2.1, hl.2.2.2.2.2.1, hl.2.2.2.2.2.2.1, hl.2.2.2.2.2.2.2.1, trivial⟩
  · simp only [statLaw, excursionSum, fP]
    push_cast
    rfl
  · simp only [statLaw, excursionSum, fQ]
    push_cast
    rfl
  · rw [varP_eq, covPQ_eq, varQ_eq]; norm_num
  · rw [EP_eq, excursionMean_P]
  · rw [EQ_eq, excursionMean_Q]
  · rw [FPP_eq, excursionMean_PP]
  · rw [FQQ_eq, excursionMean_QQ]
  · rw [FPQ_eq, excursionMean_PQ]

set_option maxHeartbeats 1000000 in
/-- The twenty shortest excursions are the words `tsts`, and each comes back with `−1`. -/
theorem excursions_four : ∀ w ∈ excursions 4, coef w = -1 ∧ ∃ s t : Fin 5, s ≠ t ∧ w = [t, s, t, s] := by
  decide +kernel

theorem excursions_four_card : (excursions 4).card = 20 := by
  have hl := excursionCount_values
  simp only [List.cons.injEq] at hl
  exact hl.2.2.2.1

theorem signed_values :
    [signedExcursionCount 4, signedExcursionCount 5, signedExcursionCount 6, signedExcursionCount 7, signedExcursionCount 8] =
      [-20, 0, 60, 0, -180] := by
  have e4 := signedExcursionCount_even 0
  have e6 := signedExcursionCount_even 1
  have e8 := signedExcursionCount_even 2
  have o5 := signedExcursionCount_odd 1
  have o7 := signedExcursionCount_odd 2
  norm_num at e4 e6 e8 o5 o7
  rw [e4, e6, e8, o5, o7]

theorem end_of_excursion (w : List (Fin 5)) (hw : relOfWord w = 0) :
    relLine w = (coef w : ℂ) • Ω ∧ (coef w = 1 ∨ coef w = -1) :=
  ⟨by rw [relLine, excursion_rel hw], coef_values w⟩

/-- **Proposition 30 (the signed excursion).** `A₋ = Σ_t γ_t ⊗ 1` on the sixteen two-spinor states has `A₋² = 5`; at the end of an
excursion the two-spinor state is `σ_w Ω`, `σ_w = ±1`; `Φ(z) = Σ_n zⁿ Σ_{excursions w, |w| = n} σ_w/(5·4ⁿ⁻¹) = −z⁴/(16 + 3z²)`; the
signed counts of the lengths `4, …, 8` are `−20, 0, 60, 0, −180`; the twenty shortest excursions are the words `tsts`
and come back with `−1`; `Φ(1) = −1/19`, `Φ(i) = −1/13`; an excursion keeps its sign with chance `9/19` and reverses it
with chance `10/19`, `a = (F(1) − Φ(1))/8 = 5/38`; and `b = Var P/(2(Var P + Var Q)) = 7/16`.

Recognition: the sign `−1` of `tsts` is spin one half; the lean `10/19` toward reversal is attraction. Uses
Props. 4, 10, 24, 29. -/
theorem prop_30 :
    (∑ t, lineOnRel t) * (∑ t, lineOnRel t) = (5 : ℂ) • (1 : Matrix Two Two ℂ) ∧
    (∀ w : List (Fin 5), relOfWord w = 0 → relLine w = (coef w : ℂ) • Ω ∧ (coef w = 1 ∨ coef w = -1)) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 → HasSum (fun n => (signedLaw n : ℂ) * z ^ n) (-z ^ 4 / (16 + 3 * z ^ 2))) ∧
    [signedExcursionCount 4, signedExcursionCount 5, signedExcursionCount 6, signedExcursionCount 7, signedExcursionCount 8] =
      [-20, 0, 60, 0, -180] ∧
    (excursions 4).card = 20 ∧ (∀ w ∈ excursions 4, coef w = -1 ∧ ∃ s t : Fin 5, s ≠ t ∧ w = [t, s, t, s]) ∧
    HasSum signedLaw (-1 / 19) ∧ HasSum (fun n => (signedLaw n : ℂ) * Complex.I ^ n) (-1 / 13) ∧
    ((∑' n, excursionLaw n) + (∑' n, signedLaw n)) / 2 = 9 / 19 ∧
    ((∑' n, excursionLaw n) - (∑' n, signedLaw n)) / 2 = 10 / 19 ∧
    ((∑' n, excursionLaw n) - (∑' n, signedLaw n)) / 8 = 5 / 38 ∧
    varP / (2 * (varP + varQ)) = 7 / 16 := by
  obtain ⟨a1, a2, a3⟩ := a_value
  have hb : varP / (2 * (varP + varQ)) = 7 / 16 := by rw [varP_eq, varQ_eq]; norm_num
  exact ⟨Aminus_sq, end_of_excursion, signed_gf, signed_values, excursions_four_card, excursions_four, Φ_one, Φ_I, a2, a3, a1,
    hb⟩

/-- **Proposition 31 (the transitions of one excursion).** An excursion that begins at a moment whose last-step direction is `h` can be in
`80 − 5 − 1 = 74` states (the five `(∅, t)` end it; `(T_h, h)` is reached only from the start's vertex, by the
undo); they are exactly the states its steps reach; the uniform law on them is the stationary law of the steps watched
on them (each state takes in and gives out the total weight one); `M = 4·74 = 296` continuations, `C_h = 60` along
`h` and `C_j = 59` along each other line; `c_L = 15/74`, `σ = 75/74`, `η = 295/296`, `σ + 4η = 5`, `η/σ = 59/60`,
`σ − 1 = 4(1 − η) = 1/74`; `34` of the `74` leave `h` undivided, `R_ud = 17/37`.

Recognition: existing tilts a line toward its own direction by one part in `296`. Uses Props. 24, 26. -/
theorem prop_31 (h : Fin 5) :
    (excursionStates h).card = 74 ∧ (∀ s : State, reach h 3 s = inExcursion h s) ∧
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
    ((excursionStates h).filter fun s => h ∉ disagreeSet s.1).card = 34 ∧ (34 : ℚ) / 74 = 17 / 37 :=
  ⟨card_excursionStates h, excursionStates_eq_reach h, undo_state_only_from_place h, watched_inflow h, watched_outflow h,
    (availableTransitions_along h).1, (availableTransitions_along h).2, availableTransitions_total h, availableTransitions_shares h, availableTransitions_up h, by norm_num⟩

end Comparison.System.Existence
