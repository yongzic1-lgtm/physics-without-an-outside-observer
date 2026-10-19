import Comparison.System.Postulates
import Comparison.Law.Meetings

/-!
# The proof system, the law: Proposition 131, the meeting's factor of the law

With `K_V = θ_V(𝐉 − I)` on the five directions,
`θ_V = diag ε(V)`, `ε_t(V) = (−1)^{[t ∈ V]}`, `a = 5 − |V|`, `d = |V|`:

* `pattern_zpow`: **`det(I − uK_V) = (1 + u)^{a−1}(1 − u)^{d−1}(1 + 4u² − u(a − d))` at every one of the
  32 patterns `V`**, with integer powers (at `V = ∅` and `V = [5]` one power is `−1`), for `u² ≠ 1`;
* `prop_131`: Proposition 131 as one statement.
-/

open Matrix Comparison

namespace Comparison.System

namespace Law

/-- **The meeting's factor at every one of the 32 patterns**, with integer powers, for `u² ≠ 1`. -/
theorem pattern_zpow (V : Finset (Fin 5)) (u : ℂ) (hu : u ^ 2 ≠ 1) :
    (1 - u • Law.patternK (R := ℂ) V).det =
      (1 + u) ^ (((5 - V.card : ℕ) : ℤ) - 1) * (1 - u) ^ ((V.card : ℤ) - 1) *
        (1 + 4 * u ^ 2 - u * (((5 - V.card : ℕ) : ℂ) - (V.card : ℂ))) := by
  have hp : (1 + u) ≠ 0 := by
    intro h0
    apply hu
    have : u = -1 := by linear_combination h0
    rw [this]
    norm_num
  have hm : (1 - u) ≠ 0 := by
    intro h0
    apply hu
    have : u = 1 := by linear_combination -h0
    rw [this]
    norm_num
  have h := Law.pattern_factor u V
  have hV : V.card ≤ 5 := by
    have := Finset.card_le_univ V
    simpa using this
  have hc : ((5 - V.card : ℕ) : ℂ) = 5 - (V.card : ℂ) := by
    rw [Nat.cast_sub hV]
    norm_num
  have e1 : (1 + u) ^ (5 - V.card) = (1 + u) * (1 + u) ^ (((5 - V.card : ℕ) : ℤ) - 1) := by
    rw [← zpow_natCast, ← zpow_one_add₀ hp]
    congr 1
    ring
  have e2 : (1 - u) ^ V.card = (1 - u) * (1 - u) ^ ((V.card : ℤ) - 1) := by
    rw [← zpow_natCast, ← zpow_one_add₀ hm]
    congr 1
    ring
  rw [e1, e2] at h
  have h1 : (1 - u ^ 2) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  apply mul_left_cancel₀ h1
  rw [hc]
  linear_combination h

end Law

open Comparison.System.Law

/-- **Proposition 131, the meeting's factor of the law.** With `K_V = θ_V(𝐉 − I)`, `a = 5 − |V|`,
`d = |V|`: `det(I − uK_V) = (1 + u)^{a−1}(1 − u)^{d−1}(1 + 4u² − u(a − d))` at every one of the 32 patterns
(`u² ≠ 1`, integer powers); over the sixteen meetings `Σ_U(a − 1) = Σ_U(d − 1) = 24`; the character transform
makes the step the direct sum of the meetings' blocks, `(𝒳 ⊗ 1)B(𝒳 ⊗ 1) = ⊕_U K_U`; `∏_U det(I − uK_U) =
det(I − uB) = (1 − u²)²⁴ ∏_U (1 + 4u² − uλ_U)` with `λ_U = a − d`; the product over the sixteen counterparts is
`det(I + uB)`. -/
theorem prop_131 :
    (∀ (V : Finset (Fin 5)) (u : ℂ), u ^ 2 ≠ 1 →
      (1 - u • Law.patternK (R := ℂ) V).det =
        (1 + u) ^ (((5 - V.card : ℕ) : ℤ) - 1) * (1 - u) ^ ((V.card : ℤ) - 1) *
          (1 + 4 * u ^ 2 - u * (((5 - V.card : ℕ) : ℂ) - (V.card : ℂ)))) ∧
    (∑ U : Fin 16, ((5 - (disagreeSet U).card : ℤ) - 1)) = 24 ∧
    (∑ U : Fin 16, (((disagreeSet U).card : ℤ) - 1)) = 24 ∧
    Law.charX80 ℚ * contB * Law.charX80 ℚ = Law.meetBlocks ℚ (Law.lastDirectionK ℚ) ∧
    (∀ u : ℂ, ∏ U : Fin 16, (1 - u • Law.patternK (R := ℂ) (disagreeSet U)).det =
      (1 - u • stepOp transitionMat).det) ∧
    (∀ u : ℂ, ∏ U : Fin 16, (1 - u • Law.patternK (R := ℂ) (disagreeSet U)).det =
      (1 - u ^ 2) ^ 24 * ∏ U : Fin 16,
        (1 + 4 * u ^ 2 - u * (((5 - (disagreeSet U).card : ℕ) : ℂ) - ((disagreeSet U).card : ℂ)))) ∧
    (∀ u : ℂ, ∏ U : Fin 16, (1 - u • Law.patternK (R := ℂ) (disagreeSet U)ᶜ).det =
      (1 + u • stepOp transitionMat).det) := by
  refine ⟨pattern_zpow, Law.sum_agree_minus_one.1, Law.sum_agree_minus_one.2, Law.prop130_B,
    Law.law_meetings, fun u => ?_, Law.law_twins⟩
  rw [Law.law_meetings_closed]
  congr 1
  refine Finset.prod_congr rfl fun U _ => ?_
  have hV : (disagreeSet U).card ≤ 5 := by
    have := Finset.card_le_univ (disagreeSet U)
    simpa using this
  rw [Nat.cast_sub hV]
  push_cast
  ring

end Comparison.System
