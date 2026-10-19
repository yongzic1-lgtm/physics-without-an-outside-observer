module

public import Comparison.Colour.Arcs
public import Comparison.Colour.LastDirections
public import Comparison.Existence.Zero

/-!
# Book XVII. The string, the Δ, the strange share, the octet's isospin identity: the finite
statements (Propositions 95, 97, 98, 100)

Prop. 96 is in Visits.lean
(`regression`, `pole_condition`, `pion_radius`, `vector_pole`).

* **Prop. 95.** `arcs_along`: on the eighty states each line takes `64` of the `320` arcs, `1/5`;
  `lastDirections_doubly_stochastic`: the last-step directions' step `(𝟏𝟏ᵀ − 1)/4` has rows and columns summing to one,
  so the uniform law on the five directions is stationary (with `lastDirection_stationary`, Zero.lean).
* **Prop. 97.** `delta_counts`: `(16 + 5)/16 = 21/16 = 3·(7/16) = 84/64 = (3/2)·84/96`;
  `6·(5/96) = 5/16`; `37/96 + 5/96 = 7/16`; `84 + 12 = 6·16`, `84 = 4(16 + 5)`.
* **Prop. 98.** `trace_dot2`: `Tr σ₁·σ₂ = 0` (`+1` three times, `−3` once), so the spin average
  `(3V + P)/4` holds no last-step direction term; `strange_share`: if `(3K* + K)/4 = λ + λ_s + c_m` and
  `(3ω + π⁰)/4 = 2λ + c_m`, then `λ_s − λ = [(3K* + K) − (3ω + π⁰)]/4`, whatever `c_m`.
* **Prop. 100.** `coleman_glashow`: for any one-line terms `u` and pair terms `f` of the totally antisymmetric state
  of three world lines, `Σ⁺ − Σ⁻ + Ξ⁻ − Ξ⁰ = p − n`.
-/

@[expose] public section

namespace Comparison

open Matrix

/-! ## Prop. 95: one line's share of the steps -/

/-- **Each line takes `64` of the `320` arcs.** -/
theorem arcs_along : ∀ j : Fin 5, (arcs.filter fun b => b.2.2 = j).card = 64 := by
  decide +kernel

/-- **The last-step directions' step is doubly stochastic.** -/
theorem lastDirections_doubly_stochastic :
    (∀ i : Fin 5, ∑ j, lastDirectionStep i j = 1) ∧ (∀ j : Fin 5, ∑ i, lastDirectionStep i j = 1) := by
  constructor <;> intro i <;> fin_cases i <;>
    simp [lastDirectionStep, ones5, Fin.sum_univ_five, Matrix.one_apply] <;> norm_num

/-! ## Prop. 97: the Δ's counts -/

theorem delta_counts :
    ((16 + 5 : ℚ) / 16 = 21 / 16 ∧ (21 / 16 : ℚ) = 3 * (7 / 16) ∧ (21 / 16 : ℚ) = 84 / 64 ∧
      (21 / 16 : ℚ) = 3 / 2 * (84 / 96)) ∧
    (6 * (5 / 96 : ℚ) = 5 / 16) ∧ (37 / 96 + 5 / 96 : ℚ) = 7 / 16 ∧
    (84 + 12 : ℕ) = 6 * 16 ∧ (84 : ℕ) = 4 * (16 + 5) := by
  norm_num

/-! ## Prop. 98: the strange share from two spin averages -/

theorem trace_swap2 : swap2.trace = 2 := by
  simp only [Matrix.trace, Matrix.diag, swap2, Matrix.of_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  norm_num

/-- **`Tr σ₁·σ₂ = 0`:** `+1` on three states and `−3` on one. -/
theorem trace_dot2 : dot2.trace = 0 ∧ 3 * (1 : ℤ) + 1 * (-3) = 0 := by
  refine ⟨?_, by norm_num⟩
  rw [dot2_eq, Matrix.trace_sub, Matrix.trace_smul, trace_swap2, Matrix.trace_one]
  simp
  norm_num

/-- **The strange share from two spin averages:** the meson constant cancels. -/
theorem strange_share (K Kst ω π lam lams cm : ℝ)
    (hK : (3 * Kst + K) / 4 = lam + lams + cm) (hω : (3 * ω + π) / 4 = 2 * lam + cm) :
    lams - lam = ((3 * Kst + K) - (3 * ω + π)) / 4 := by
  linarith

/-! ## Prop. 100: the octet's isospin identity -/

/-- The mass of a totally antisymmetric state of three world lines `q₁q₂q₃` with the like pair `q₁q₂` (last-step directions `+1`) and the two
unlike pairs (last-step directions `−2`): one-line terms plus pair terms. -/
def octetMass (u : Fin 3 → ℝ) (f : Sym2 (Fin 3) → ℤ → ℝ) (q₁ q₂ q₃ : Fin 3) : ℝ :=
  u q₁ + u q₂ + u q₃ + f s(q₁, q₂) 1 + f s(q₁, q₃) (-2) + f s(q₂, q₃) (-2)

/-- **Coleman–Glashow:** with `u, d, s = 0, 1, 2`, `Σ⁺ = uus`, `Σ⁻ = dds`, `Ξ⁰ = ssu`, `Ξ⁻ = ssd`,
`p = uud`, `n = ddu`: `Σ⁺ − Σ⁻ + Ξ⁻ − Ξ⁰ = p − n` for every `u` and `f`. -/
theorem coleman_glashow (u : Fin 3 → ℝ) (f : Sym2 (Fin 3) → ℤ → ℝ) :
    octetMass u f 0 0 2 - octetMass u f 1 1 2 + octetMass u f 2 2 1 - octetMass u f 2 2 0 =
      octetMass u f 0 0 1 - octetMass u f 1 1 0 := by
  simp only [octetMass]
  have e1 : s((2 : Fin 3), (0 : Fin 3)) = s(0, 2) := Sym2.eq_swap
  have e2 : s((2 : Fin 3), (1 : Fin 3)) = s(1, 2) := Sym2.eq_swap
  have e3 : s((1 : Fin 3), (0 : Fin 3)) = s(0, 1) := Sym2.eq_swap
  rw [e1, e2, e3]
  ring

end Comparison

end
