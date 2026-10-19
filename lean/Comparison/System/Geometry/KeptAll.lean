import Comparison.System.Geometry.KeptFour

/-!
# The geometry of comparison: Proposition 15 whole

The statement of Proposition 15 as one theorem,
the conjunction of what `Kept.lean` (every `N`; `N = 1, 2`), `KeptThree.lean` (`N = 3`) and
`KeptFour.lean` (`N = 4`) prove.
-/

open scoped Kronecker
open Matrix Complex Module

namespace Comparison.System

open Comparison.System.Geometry

/-- **Proposition 15 (swaps and the singlet make every kept operator).** For every number `N` of systems,
every element of the algebra of swaps and pairings (`brauerAlg N`), every swap and every pairing is kept
by every `U^{⊗N}`, `U ∈ Sp(2)`; the kept operators are `ℂ1` on one system (dimension 1), `span{1, P, E}`
on two (independent, dimension 3), and on three and on four systems exactly the sums of products of swaps
and pairings, of dimensions 14 and 84, spanned by independent products. Status: partial; every `N ≥ 5` is
missing (the first fundamental theorem of invariant theory for `Sp(2)`). Recognition: none. -/
theorem prop_15 :
    ((∀ N : ℕ, ∀ X ∈ brauerAlg N, KeptN N X) ∧
      (∀ (N : ℕ) (π : Equiv.Perm (Fin N)), KeptN N (permOp π)) ∧
      (∀ (N : ℕ) (a b : Fin N), a ≠ b → KeptN N (Eab a b)) ∧
      keptOne = Submodule.span ℂ {(1 : Matrix Four Four ℂ)} ∧ finrank ℂ keptOne = 1 ∧
      keptTwo = Submodule.span ℂ (Set.range ![(1 : Matrix Two Two ℂ), swap, Eop]) ∧
      LinearIndependent ℂ ![(1 : Matrix Two Two ℂ), swap, Eop] ∧ finrank ℂ keptTwo = 3) ∧
    ((∀ X : Op 3, KeptN 3 X ↔ X ∈ brauerAlg 3) ∧ finrank ℂ (keptN 3) = 14 ∧
      keptN 3 = Submodule.span ℂ (Set.range B3) ∧ LinearIndependent ℂ B3) ∧
    ((∀ X : Op 4, KeptN 4 X ↔ X ∈ brauerAlg 4) ∧ finrank ℂ (keptN 4) = 84 ∧
      keptN 4 = Submodule.span ℂ (Set.range B4) ∧ LinearIndependent ℂ B4) :=
  ⟨kept_up_to_two, kept_three_statement, kept_four_statement⟩

end Comparison.System
