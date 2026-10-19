module

public import Comparison.Existence.Walk

/-!
# Book VI. Existence: the available transitions of a line (Proposition 31)

An excursion that begins at a moment whose last-step direction
is `h` never steps along `h` first (that would be the undo, no step), and it ends at the five
states `(∅, t)` of the start's vertex.

* `excursionStates h`: the eighty states less the five at the start's vertex and the undo state
  `(T_h, h)`; `card_excursionStates`: `74`.
* `undo_state_only_from_place`: `(T_h, h)` is reached only from the start's vertex, by the step `h`.
* `preds`, `mem_preds`: the four states that lead to a state; `reach h k`: the states reached
  within `k + 1` steps of an excursion begun with last-step direction `h`, never at the start's vertex;
  `excursionStates_eq_reach`: within four steps they are exactly the `74`.
* `watchedIn64`, `watched_inflow`; `watchedOut64`, `watched_outflow`: the walk watched on the `74`
  (an excursion through the six states set apart counted with its weight `4^{-length}`) gives
  every state of the `74` the total weight one coming in and going out: the uniform law on them is
  its stationary law.
* `availableTransitions_along`: along `h` there are `60` continuations, along each other line `59`;
  `availableTransitions_total`: `M = 296 = 4 · 74`; `availableTransitions_shares`: `c_L = 15/74`, `σ = 75/74`, `η = 295/296`,
  `σ + 4η = 5`, `η/σ = 59/60`, `σ − 1 = 4(1 − η) = 1/74`, `6M + C_h = 1836`;
  `availableTransitions_up`: `34` of the `74` leave `h` undivided, `R_ud = 34/74 = 17/37`.
-/

@[expose] public section

namespace Comparison

/-- The vector state of the last-step direction, `T_h`: the two-spinor state the step `h` makes from the singlet. -/
def lastDirectionRel (h : Fin 5) : Fin 16 := transition h 0

/-- A state of an excursion begun at a moment whose last-step direction is `h`: not at the start's vertex, not the undo
state `(T_h, h)`. -/
def inExcursion (h : Fin 5) (s : State) : Bool := decide (s.1 ≠ 0) && decide (s ≠ (lastDirectionRel h, h))

/-- **The states of an excursion begun at a moment whose last-step direction is `h`.** -/
def excursionStates (h : Fin 5) : Finset State := Finset.univ.filter fun s => inExcursion h s

/-- **Seventy-four states.** -/
theorem card_excursionStates (h : Fin 5) : (excursionStates h).card = 74 := by
  revert h
  decide +kernel

/-- **The undo state `(T_h, h)` is reached only from the start's vertex, by the step `h`.** -/
theorem undo_state_only_from_place (h : Fin 5) (s : State) (hs : Continues s (lastDirectionRel h, h)) :
    s.1 = 0 := by
  obtain ⟨_, h2⟩ := hs
  have : transition h (transition h s.1) = transition h (lastDirectionRel h) := by rw [← h2]
  rw [transition_transition] at this
  rw [this, lastDirectionRel, transition_transition]

/-- The four states that lead to `s'`: `(transition t S', g)` for each `g ≠ t`, where `s' = (S', t)`. -/
def preds (s' : State) : List State :=
  ((List.finRange 5).filter fun g => g ≠ s'.2).map fun g => (transition s'.2 s'.1, g)

/-- The four states that continue `s`: `(transition g S, g)` for each `g ≠ t`, where `s = (S, t)`. -/
def succs (s : State) : List State :=
  ((List.finRange 5).filter fun g => g ≠ s.2).map fun g => (transition g s.1, g)

theorem mem_preds : ∀ s s' : State, s ∈ preds s' ↔ Continues s s' := by
  decide +kernel

theorem mem_succs : ∀ s s' : State, s' ∈ succs s ↔ Continues s s' := by
  decide +kernel

/-- The states reached within `k + 1` steps of an excursion begun with last-step direction `h`: the first step is any
`t ≠ h`; every later state continues a reached state and is not at the start's vertex. -/
def reach (h : Fin 5) : ℕ → State → Bool
  | 0 => fun s => decide (s.2 ≠ h) && decide (s.1 = transition s.2 0)
  | k + 1 => fun s => reach h k s || (decide (s.1 ≠ 0) && (preds s).any (reach h k))

/-- **Every state but the six set apart is reached, within four steps.** -/
theorem excursionStates_eq_reach : ∀ (h : Fin 5) (s : State), reach h 3 s = inExcursion h s := by
  decide +kernel

/-! ## The walk watched on the seventy-four -/

/-- Sixty-four times the weight that the walk watched on the seventy-four brings into `s'`: a step
from one of them (`1/4`), or a path through one (`1/16`) or two (`1/64`) of the six set apart. -/
def watchedIn64 (h : Fin 5) (s' : State) : ℕ :=
  16 * ((preds s').filter (inExcursion h)).length +
  4 * (((preds s').filter fun e => !inExcursion h e).map fun e =>
    ((preds e).filter (inExcursion h)).length).sum +
  (((preds s').filter fun e => !inExcursion h e).map fun e =>
    (((preds e).filter fun e' => !inExcursion h e').map fun e' =>
      ((preds e').filter (inExcursion h)).length).sum).sum

/-- Sixty-four times the weight that the walk watched on the seventy-four takes out of `s`. -/
def watchedOut64 (h : Fin 5) (s : State) : ℕ :=
  16 * ((succs s).filter (inExcursion h)).length +
  4 * (((succs s).filter fun e => !inExcursion h e).map fun e =>
    ((succs e).filter (inExcursion h)).length).sum +
  (((succs s).filter fun e => !inExcursion h e).map fun e =>
    (((succs e).filter fun e' => !inExcursion h e').map fun e' =>
      ((succs e').filter (inExcursion h)).length).sum).sum

/-- The six states set apart: the five at the start's vertex and the undo state. -/
def setApart (h : Fin 5) : List State := [(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (lastDirectionRel h, h)]

theorem mem_setApart : ∀ (h : Fin 5) (s : State), s ∈ setApart h ↔ inExcursion h s = false := by
  decide +kernel

/-- No walk stays three steps among the six set apart, so the paths above are all the excursions. -/
theorem setApart_short : ∀ h : Fin 5, ∀ e₁ ∈ setApart h, ∀ e₂ ∈ setApart h, ∀ e₃ ∈ setApart h,
    ¬(Continues e₁ e₂ ∧ Continues e₂ e₃) := by
  decide +kernel

/-- **The uniform law on the seventy-four is stationary for the walk watched on them:** every
state of the seventy-four receives the total weight one. -/
theorem watched_inflow : ∀ (h : Fin 5) (s' : State), inExcursion h s' → watchedIn64 h s' = 64 := by
  decide +kernel

/-- Every state of the seventy-four gives the total weight one: the watched walk loses nothing. -/
theorem watched_outflow : ∀ (h : Fin 5) (s : State), inExcursion h s → watchedOut64 h s = 64 := by
  decide +kernel

/-! ## The counts -/

/-- The continuations along the line `j` from the seventy-four: one from every state whose last-step direction is
not `j`. -/
def alongCount (h j : Fin 5) : ℕ := ((excursionStates h).filter fun s => s.2 ≠ j).card

/-- **Sixty along the last-step direction, fifty-nine along each other line.** -/
theorem availableTransitions_along : ∀ h : Fin 5, alongCount h h = 60 ∧ ∀ j, j ≠ h → alongCount h j = 59 := by
  decide +kernel

/-- **`M = 296 = 4 · 74` continuations.** -/
theorem availableTransitions_total : ∀ h : Fin 5, ∑ j, alongCount h j = 296 := by
  decide +kernel

/-- **The shares:** `c_L = 15/74`, `σ = 75/74`, `η = 295/296`, `σ + 4η = 5`, `η/σ = 59/60`,
`σ − 1 = 4(1 − η) = 1/74`, `6M + C_h = 1836`. -/
theorem availableTransitions_shares (h : Fin 5) :
    let M : ℚ := ∑ j, (alongCount h j : ℚ)
    let Ch : ℚ := alongCount h h
    let σ : ℚ := 5 * Ch / M
    let η : ℚ := 5 * 59 / M
    Ch / M = 15 / 74 ∧ σ = 75 / 74 ∧ η = 295 / 296 ∧ σ + 4 * η = 5 ∧ η / σ = 59 / 60 ∧
      σ - 1 = 4 * (1 - η) ∧ σ - 1 = 1 / 74 ∧ 6 * M + Ch = 1836 := by
  have hM : (∑ j, (alongCount h j : ℚ)) = 296 := by
    have := availableTransitions_total h
    exact_mod_cast this
  have hC : (alongCount h h : ℚ) = 60 := by
    have := (availableTransitions_along h).1
    exact_mod_cast this
  simp only [hM, hC]
  norm_num

/-- **`34` of the seventy-four leave the last-step direction undivided:** `R_ud = 34/74 = 17/37`. -/
theorem availableTransitions_up :
    ∀ h : Fin 5, ((excursionStates h).filter fun s => h ∉ disagreeSet s.1).card = 34 := by
  decide +kernel

end Comparison

end
