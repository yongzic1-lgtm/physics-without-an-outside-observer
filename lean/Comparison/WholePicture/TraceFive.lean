module

public import Comparison.Existence.LastDirectionSplit

/-!
# The whole picture, statement 15: the trace of the five directions in the section's form

`trace_five` (`LastDirectionSplit.lean`) gives
`tr(γ_aγ_bγ_cγ_dγ_e) = 4ε_{abcde}` and `γ_prod` (`OneThing.lean`) gives `γ₀γ₁γ₂γ₃γ₄ = 1`;
together:

* `trace_five_volume`: **`tr(γ_hγ_aγ_bγ_cγ_d) · 1 = 4ε_{habcd} · (γ₀γ₁γ₂γ₃γ₄)`** for all five
  indices.
-/

@[expose] public section

namespace Comparison.WholePicture

open Matrix

/-- **`tr(γ_hγ_aγ_bγ_cγ_d) = 4ε_{habcd} · (γ₀γ₁γ₂γ₃γ₄)`**, the product of the five directions being a
number. -/
theorem trace_five_volume (h a b c d : Fin 5) :
    (γ h * γ a * γ b * γ c * γ d).trace • (1 : Matrix Four Four ℂ) =
      (4 * (lc5 h a b c d : ℂ)) • (γ 0 * γ 1 * γ 2 * γ 3 * γ 4) := by
  rw [trace_five, γ_prod]

end Comparison.WholePicture
