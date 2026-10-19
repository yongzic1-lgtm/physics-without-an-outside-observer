import Comparison.Existence.Matter

/-!
# One trace for the weak and the colour rotations

Statement 33 of the article: on one generation, the sixteen two-spinor states, the normalized traces of the
squares of the weak isospin `T₃ = (N_k − N_h)/2` and of a colour generator `T_c = ([c₁ ∈ S] − [c₂ ∈ S])/2`
are both `1/8`, so the weak and the colour currents have one normalization (`g₂ = g₃` at the source),
and the angle of the charge is `Tr T₃² / Tr Q² = 3/8`, with `Q = N_k − N_C/3 = T₃ + Y`
(`charge_eq`, Existence/Matter.lean).

* `sum_isospin6_sq`: `Σ (6T₃)² = 72`; `sum_charge3_sq`: `Σ (3Q)² = 48`; `sum_colour2_sq`: `Σ (2T_c)² = 8`
  (integer forms, by `decide +kernel`, for every plane `{h, k}` and every pair of lines `c₁ ≠ c₂`).
* `trace_isospin_sq`: `(1/16) Σ T₃² = 1/8`; `trace_colour_sq`: `(1/16) Σ T_c² = 1/8`;
  `trace_charge_sq`: `Σ Q² = 16/3`; `weak_angle_source`: `Σ T₃² / Σ Q² = 3/8`;
  `one_trace`: the weak and the colour normalized traces are equal.
-/

namespace Comparison.ArticleStatements

open Comparison

/-- Twice a colour generator `diag(1/2, −1/2, 0)` on the lines `c₁, c₂`: `2T_c = [c₁ ∈ S] − [c₂ ∈ S]`. -/
def colour2 (c₁ c₂ : Fin 5) (r : Fin 16) : ℤ :=
  (if c₁ ∈ disagreeSet r then 1 else 0) - (if c₂ ∈ disagreeSet r then 1 else 0)

/-- The colour generator `T_c`. -/
def colour (c₁ c₂ : Fin 5) (r : Fin 16) : ℚ := (colour2 c₁ c₂ r : ℚ) / 2

theorem sum_isospin6_sq : ∀ h k : Fin 5, h ≠ k → ∑ r, isospin6 h k r ^ 2 = 72 := by
  decide +kernel

theorem sum_charge3_sq : ∀ h k : Fin 5, h ≠ k → ∑ r, charge3 h k r ^ 2 = 48 := by
  decide +kernel

theorem sum_colour2_sq : ∀ c₁ c₂ : Fin 5, c₁ ≠ c₂ → ∑ r, colour2 c₁ c₂ r ^ 2 = 8 := by
  decide +kernel

/-- **`Σ T₃² = 2`** on the sixteen two-spinor states. -/
theorem sum_isospin_sq (h k : Fin 5) (hk : h ≠ k) : ∑ r, isospin h k r ^ 2 = 2 := by
  simp only [isospin_eq, div_pow, ← Finset.sum_div]
  rw [show (∑ r, (isospin6 h k r : ℚ) ^ 2) = ((∑ r, isospin6 h k r ^ 2 : ℤ) : ℚ) by push_cast; rfl,
    sum_isospin6_sq h k hk]
  norm_num

/-- **`Σ Q² = 16/3`** on the sixteen two-spinor states. -/
theorem trace_charge_sq (h k : Fin 5) (hk : h ≠ k) : ∑ r, charge h k r ^ 2 = 16 / 3 := by
  simp only [charge_eq3, div_pow, ← Finset.sum_div]
  rw [show (∑ r, (charge3 h k r : ℚ) ^ 2) = ((∑ r, charge3 h k r ^ 2 : ℤ) : ℚ) by push_cast; rfl,
    sum_charge3_sq h k hk]
  norm_num

/-- **`Σ T_c² = 2`** on the sixteen two-spinor states. -/
theorem sum_colour_sq (c₁ c₂ : Fin 5) (hc : c₁ ≠ c₂) : ∑ r, colour c₁ c₂ r ^ 2 = 2 := by
  simp only [colour, div_pow, ← Finset.sum_div]
  rw [show (∑ r, (colour2 c₁ c₂ r : ℚ) ^ 2) = ((∑ r, colour2 c₁ c₂ r ^ 2 : ℤ) : ℚ) by push_cast; rfl,
    sum_colour2_sq c₁ c₂ hc]
  norm_num

/-- **`(1/16) Tr T₃² = 1/8`.** -/
theorem trace_isospin_sq (h k : Fin 5) (hk : h ≠ k) : (∑ r, isospin h k r ^ 2) / 16 = 1 / 8 := by
  rw [sum_isospin_sq h k hk]
  norm_num

/-- **`(1/16) Tr T_c² = 1/8`.** -/
theorem trace_colour_sq (c₁ c₂ : Fin 5) (hc : c₁ ≠ c₂) : (∑ r, colour c₁ c₂ r ^ 2) / 16 = 1 / 8 := by
  rw [sum_colour_sq c₁ c₂ hc]
  norm_num

/-- **One trace:** the weak isospin and every colour generator have the same normalized square trace. -/
theorem one_trace (h k c₁ c₂ : Fin 5) (hk : h ≠ k) (hc : c₁ ≠ c₂) :
    (∑ r, isospin h k r ^ 2) / 16 = (∑ r, colour c₁ c₂ r ^ 2) / 16 := by
  rw [trace_isospin_sq h k hk, trace_colour_sq c₁ c₂ hc]

/-- **`sin²θ = Tr T₃² / Tr Q² = 3/8`** at the source. -/
theorem weak_angle_source (h k : Fin 5) (hk : h ≠ k) :
    (∑ r, isospin h k r ^ 2) / (∑ r, charge h k r ^ 2) = 3 / 8 := by
  rw [sum_isospin_sq h k hk, trace_charge_sq h k hk]
  norm_num

end Comparison.ArticleStatements

#print axioms Comparison.ArticleStatements.sum_isospin6_sq
#print axioms Comparison.ArticleStatements.sum_charge3_sq
#print axioms Comparison.ArticleStatements.sum_colour2_sq
#print axioms Comparison.ArticleStatements.sum_isospin_sq
#print axioms Comparison.ArticleStatements.trace_charge_sq
#print axioms Comparison.ArticleStatements.sum_colour_sq
#print axioms Comparison.ArticleStatements.trace_isospin_sq
#print axioms Comparison.ArticleStatements.trace_colour_sq
#print axioms Comparison.ArticleStatements.one_trace
#print axioms Comparison.ArticleStatements.weak_angle_source
