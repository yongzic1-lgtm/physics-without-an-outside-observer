module

public import Comparison.Elements.TwoThings
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# Book VI. Existence: the transitions of one line on the sixteen two-spinor states

The sixteen two-spinor states are indexed as in
`TwoThings.lean`: `rel k = (B_k ⊗ 1) Ω` with `B_k = 1, γ_t, γ_s γ_t` and disagreement sets
`disagreeSet k`.

* `transition t k`: the two-spinor state that the change `t` makes from the two-spinor state `k`;
  `disagreeSet_transition`: `S ↦ S △ ([5] ∖ {t})` (Elements, Prop. 14).
* `γ_mul_relOp`: `γ_t B_k = ± B_{transition t k}` with the sign `transitionSign t k`; `line_moves_rel`:
  `(γ_t ⊗ 1) e_k = ± e_{transition t k}`: applying a line to one system moves a two-spinor state to a two-spinor state.
* `transition_transition`, `transition_ne`, `transition_eq_transition_iff`: each change is an involution with no fixed two-spinor state,
  and the five changes lead from each two-spinor state to five different two-spinor states.
* `card_neighbours`, `common_neighbours`, `card_edges`: the transitions are the Clebsch graph: five
  neighbours, none in common for neighbours, two in common otherwise, forty pairs.
* `State`: a two-spinor state together with the change that led to it, `16 × 5 = 80` states;
  `card_continuations`, `card_predecessors`: every state has exactly four continuations (all changes
  but the one just made) and exactly four states lead to it.

The matrix identities are checked over the Gaussian integers `ℤ[i]` by `decide` and carried to `ℂ`
by the ring map `ℤ[i] → ℂ`.
-/

@[expose] public section

namespace Comparison

open Matrix hiding J
open Complex Kronecker

/-! ## The transition table -/

/-- The transition of the change `t` on the sixteen two-spinor states. -/
def transition : Fin 5 → Fin 16 → Fin 16 :=
  ![![1, 0, 6, 7, 8, 9, 2, 3, 4, 5, 15, 14, 13, 12, 11, 10],
    ![2, 6, 0, 10, 11, 12, 1, 15, 14, 13, 3, 4, 5, 9, 8, 7],
    ![3, 7, 10, 0, 13, 14, 15, 1, 12, 11, 2, 9, 8, 4, 5, 6],
    ![4, 8, 11, 13, 0, 15, 14, 12, 1, 10, 9, 2, 7, 3, 6, 5],
    ![5, 9, 12, 14, 15, 0, 13, 11, 10, 1, 8, 7, 2, 6, 3, 4]]

/-- The sign of the transition: `γ_t B_k = transitionSign t k • B_{transition t k}`. -/
def transitionSign : Fin 5 → Fin 16 → ℤ :=
  ![![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, -1, 1, -1, -1, 1, -1],
    ![1, -1, 1, 1, 1, 1, -1, 1, -1, 1, 1, 1, 1, 1, -1, 1],
    ![1, -1, -1, 1, 1, 1, -1, -1, 1, -1, -1, -1, 1, 1, 1, -1],
    ![1, -1, -1, -1, 1, 1, 1, -1, -1, 1, 1, -1, -1, -1, 1, 1],
    ![1, -1, -1, -1, -1, 1, -1, 1, -1, -1, -1, 1, -1, -1, -1, -1]]

/-- **Elements, Prop. 14:** the change `t` turns agreement into disagreement and back on the four
lines other than `t`: `S ↦ S △ ([5] ∖ {t})`. -/
theorem disagreeSet_transition (t : Fin 5) (k : Fin 16) :
    disagreeSet (transition t k) = symmDiff (disagreeSet k) (Finset.univ.erase t) := by
  revert t k
  decide

/-- A change done twice is no change. -/
theorem transition_transition (t : Fin 5) (k : Fin 16) : transition t (transition t k) = k := by
  revert t k
  decide

/-- No change leaves a two-spinor state where it is. -/
theorem transition_ne (t : Fin 5) (k : Fin 16) : transition t k ≠ k := by
  revert t k
  decide

/-- The five changes lead from each two-spinor state to five different two-spinor states. -/
theorem transition_eq_transition_iff (t t' : Fin 5) (k : Fin 16) : transition t k = transition t' k ↔ t = t' := by
  revert t t' k
  decide

/-- The sign of a change done twice: `transitionSign t (transition t k) * transitionSign t k = 1`. -/
theorem transitionSign_transition (t : Fin 5) (k : Fin 16) : transitionSign t (transition t k) * transitionSign t k = 1 := by
  revert t k
  decide

/-! ## The transitions are the lines applied to one system (Prop. 14 in matrices) -/

/-- The Gaussian integer `i`. -/
def iZ : GaussianInt := ⟨0, 1⟩

/-- Pauli matrices over `ℤ[i]`. -/
def σ₁Z : Matrix (Fin 2) (Fin 2) GaussianInt := !![0, 1; 1, 0]
def σ₂Z : Matrix (Fin 2) (Fin 2) GaussianInt := !![0, -iZ; iZ, 0]
def σ₃Z : Matrix (Fin 2) (Fin 2) GaussianInt := !![1, 0; 0, -1]

/-- The five directions over `ℤ[i]`. -/
def γZ : Fin 5 → Matrix Four Four GaussianInt :=
  ![σ₁Z ⊗ₖ 1, σ₃Z ⊗ₖ 1, σ₂Z ⊗ₖ σ₁Z, σ₂Z ⊗ₖ σ₂Z, σ₂Z ⊗ₖ σ₃Z]

/-- The operators of the sixteen two-spinor states over `ℤ[i]`. -/
def relOpZ : Fin 16 → Matrix Four Four GaussianInt :=
  ![1, γZ 0, γZ 1, γZ 2, γZ 3, γZ 4,
    γZ 0 * γZ 1, γZ 0 * γZ 2, γZ 0 * γZ 3, γZ 0 * γZ 4, γZ 1 * γZ 2, γZ 1 * γZ 3, γZ 1 * γZ 4,
    γZ 2 * γZ 3, γZ 2 * γZ 4, γZ 3 * γZ 4]

theorem γZ_map (t : Fin 5) : (γZ t).map GaussianInt.toComplex = γ t := by
  fin_cases t <;>
  · four_ext <;>
      simp [γZ, γ, σ₁Z, σ₂Z, σ₃Z, σ₁, σ₂, σ₃, iZ, GaussianInt.toComplex_def']

theorem relOpZ_map (k : Fin 16) : (relOpZ k).map GaussianInt.toComplex = relOp k := by
  fin_cases k <;>
    simp [relOpZ, relOp, Matrix.map_mul, γZ_map, Matrix.map_one]

theorem γZ_mul_relOpZ : ∀ (t : Fin 5) (k : Fin 16),
    γZ t * relOpZ k = (transitionSign t k : GaussianInt) • relOpZ (transition t k) := by
  decide +kernel

/-- **A line applied to one system moves a two-spinor state to a two-spinor state:**
`γ_t B_k = (transitionSign t k) B_{transition t k}`. -/
theorem γ_mul_relOp (t : Fin 5) (k : Fin 16) :
    γ t * relOp k = (transitionSign t k : ℂ) • relOp (transition t k) := by
  rw [← γZ_map, ← relOpZ_map, ← relOpZ_map, ← Matrix.map_mul, γZ_mul_relOpZ]
  ext i j
  simp

/-- **Elements, Prop. 14 on the two-spinor states:** `(γ_t ⊗ 1) e_k = ± e_{transition t k}`. -/
theorem line_moves_rel (t : Fin 5) (k : Fin 16) :
    (γ t ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ rel k = (transitionSign t k : ℂ) • rel (transition t k) := by
  rw [rel_eq_relOf, rel_eq_relOf, kron_mulVec_relOf, Matrix.transpose_one, Matrix.mul_one,
    ← Matrix.mul_assoc, γ_mul_relOp, Matrix.smul_mul, relOf_smul]

/-! ## The Clebsch graph -/

/-- Two two-spinor states are neighbours when one change leads from one to the other. -/
def Adjacent (k l : Fin 16) : Prop := ∃ t, transition t k = l

instance : DecidableRel Adjacent := fun k l => by unfold Adjacent; infer_instance

theorem adjacent_symm (k l : Fin 16) : Adjacent k l ↔ Adjacent l k := by
  revert k l
  decide

/-- Every two-spinor state has five neighbours. -/
theorem card_neighbours (k : Fin 16) : (Finset.univ.filter (Adjacent k)).card = 5 := by
  revert k
  decide

/-- **The Clebsch graph:** two neighbours have no neighbour in common, two other two-spinor states have
two. -/
theorem common_neighbours (k l : Fin 16) (h : k ≠ l) :
    (Finset.univ.filter fun m => Adjacent k m ∧ Adjacent l m).card =
      if Adjacent k l then 0 else 2 := by
  revert k l
  decide

/-- The sixteen two-spinor states and their transitions have forty pairs of neighbours. -/
theorem card_edges :
    (Finset.univ.filter fun p : Fin 16 × Fin 16 => p.1 < p.2 ∧ Adjacent p.1 p.2).card = 40 := by
  decide

/-! ## The eighty states and their four continuations -/

/-- A state of a line: a two-spinor state together with the change that led to it. -/
abbrev State := Fin 16 × Fin 5

theorem card_state : Fintype.card State = 80 := by decide

/-- `s'` continues `s`: the change of `s'` is not the change just made, and it moves the two-spinor state
of `s` to the two-spinor state of `s'`. -/
def Continues (s s' : State) : Prop := s'.2 ≠ s.2 ∧ s'.1 = transition s'.2 s.1

instance : DecidableRel Continues := fun s s' => by unfold Continues; infer_instance

/-- **Every state has exactly four continuations.** -/
theorem card_continuations (s : State) :
    (Finset.univ.filter (Continues s)).card = 4 := by
  revert s
  decide +kernel

/-- **Exactly four states lead to each state.** -/
theorem card_predecessors (s' : State) :
    (Finset.univ.filter fun s => Continues s s').card = 4 := by
  revert s'
  decide +kernel

/-- The continuation by the change just made would undo it: it returns to the two-spinor state before. -/
theorem undo_returns (k : Fin 16) (t : Fin 5) : transition t (transition t k) = k := transition_transition t k

end Comparison

end
