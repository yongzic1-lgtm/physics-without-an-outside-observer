import Comparison.Existence.Exterior
import Comparison.Article.Whole

/-!
# Proposition 33's step on the exterior algebra of the six

The instance of `Article/Whole.lean` at the adding and removing operators `εx`, `ιx` of
`Existence/Exterior.lean` (`n = 6`, complex coefficients): with `J_a = εx a + ιx a` (`Jx`) and the whole
`w = J₀J₁⋯J₅`, **`w ε_a = −ι_a w`**, so `w ε(v) w⁻¹ = −ι(v)`.

This file is not imported by the root `Comparison.Article` (the names of `Existence/Exterior.lean` clash with
`Colour/GramTerm.lean` and `Elements/Half.lean` there); it is built on its own with
`lake build Comparison.Article.WholeExterior`.
-/

namespace Comparison.Article

/-- The whole is the product of the six lines `Jx`. -/
theorem whole_eq_Jx :
    whole (A := Module.End ℂ (Finset (Fin 6) → ℂ)) (fun a => Comparison.εx a) (fun a => Comparison.ιx a) =
      Comparison.Jx 0 * Comparison.Jx 1 * Comparison.Jx 2 * Comparison.Jx 3 * Comparison.Jx 4 * Comparison.Jx 5 :=
  rfl

/-- **Proposition 33's step on the exterior algebra:** `w εx_a = −ιx_a w`. -/
theorem whole_turns_adding_exterior (a : Fin 6) :
    whole (A := Module.End ℂ (Finset (Fin 6) → ℂ)) (fun a => Comparison.εx a) (fun a => Comparison.ιx a) *
        Comparison.εx a =
      -(Comparison.ιx a * whole (A := Module.End ℂ (Finset (Fin 6) → ℂ)) (fun a => Comparison.εx a)
        (fun a => Comparison.ιx a)) :=
  whole_turns_adding _ _ (fun a b => Comparison.εx_εx_add a b) (fun a b => Comparison.ιx_ιx_add a b)
    (fun a b => Comparison.εx_ιx_add a b) a

end Comparison.Article
