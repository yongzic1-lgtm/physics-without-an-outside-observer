import Comparison.Law.Composite
import Comparison.Existence.Table
import Comparison.Existence.Zero

/-!
# The coupling's steps R1 to R6 (Prop. 194), each as its finite statement

`c = 32/60 = 8/15` for every line the levels ride on. Each step of the derivation is a finite
statement of the geometry; here each is one theorem, assembled from the theorems that carry it.

* `coupling_R1`: the meeting of two lines at a transition is their two-spinor state `e_S`: **`(γ_t ⊗ γ_t) e_S =
  ε_t(S) e_S`**, `n_t e_S = [t ∈ S] e_S`, and the sixteen two-spinor states are orthonormal.
* `coupling_R2`: a unit moved rotation has mass `2` (`massForm_unit_moved`), the line's clock is moved
  at `{r}`, and **the meeting's division moves `(n r)` exactly at the two-spinor states containing `r`, at
  `8` of the `15`**.
* `coupling_R3`: `r`'s time division moves `8` and keeps `7` of the fifteen rotations and moves the
  two-spinor state's own rotation exactly when `r ∈ S`; the two pairings: on the line side (`G = I`) the law
  factors over the two levels, on the meeting side (`G = 𝟏𝟏ᵀ`) one level `S₁ + S₂`.
* `coupling_R4`: the bound state's transitions: **`60` steps along `r` off the singlet**, `4` at each of the
  fifteen two-spinor states; the available transitions of `h` have `60` along `h`, `59` along each other line, and
  `E_H = (16 − 1)/5 = 3`.
* `coupling_R5`: **`c = 𝟏ᵀB_rΛ_rΠ𝟏 / 𝟏ᵀB_rΠ𝟏 = 32/60`**, and the meeting matrix
  `Σ (4/60) G ∘ G = I + (8/15)(𝐉 − I)`.
* `coupling_R6`: **the same `8/15` along `h` in the available transitions of `h` and along every line**.
* `coupling_derived`: **`c = 8/15` and `1 − c = 7/15`**.
-/

namespace Comparison.GroupsContinuumLaw

open Matrix Kronecker Comparison Comparison.Law

/-- The transitions along `r` at the two-spinor state `U`: one from each last-step direction other than `r`. -/
theorem transitions_per_relation : ∀ (r : Fin 5) (U : Fin 16),
    (Finset.univ.filter fun p : State × State => p.1.1 = U ∧ Continues p.1 p.2 ∧ p.2.2 = r).card =
      4 := by
  decide +kernel

/-- **R1.** -/
theorem coupling_R1 :
    (∀ (u : Fin 5) (k : Fin 16),
      (γ u ⊗ₖ γ u) *ᵥ rel k = (if u ∈ disagreeSet k then -1 else 1 : ℂ) • rel k) ∧
    (∀ (u : Fin 5) (k : Fin 16),
      count u *ᵥ rel k = (if u ∈ disagreeSet k then 1 else 0 : ℂ) • rel k) ∧
    (∀ k l : Fin 16, star (rel k) ⬝ᵥ rel l = if k = l then 1 else 0) :=
  ⟨agreement, count_rel, rel_inner⟩

/-- **R2.** -/
theorem coupling_R2 :
    (∀ (n : ℕ) (D : Finset (Fin n)) (a b : Fin n), a ∈ D → b ∉ D →
      massForm D (unitTurn a b) (unitTurn a b) = 2) ∧
    (∀ h : Fin 5, Moved {h.succ} (Sum.inl h)) ∧
    (∀ (r : Fin 5) (U : Fin 16), movesTurn (relDiv U) 0 r.succ = decide (r ∈ disagreeSet U)) ∧
    (∀ r : Fin 5, (Finset.univ.filter fun U : Fin 16 => U ≠ 0 ∧ r ∈ disagreeSet U).card = 8) :=
  ⟨fun _ D _ _ ha hb => massForm_unit_moved D ha hb, clock_line_moved, prop192_moves,
    prop192_count⟩

/-- **R3.** -/
theorem coupling_R3 :
    (∀ r : Fin 5,
      (turns6.filter fun p => movesTurn {0, r.succ} p.1 p.2 = true).card = 8 ∧
        (turns6.filter fun p => movesTurn {0, r.succ} p.1 p.2 = false).card = 7) ∧
    (∀ (r : Fin 5) (U : Fin 16), U ≠ 0 →
      movesTurn {0, r.succ} (relTurn U).1 (relTurn U).2 = decide (r ∈ disagreeSet U)) ∧
    (∀ {n : Type} [Fintype n] [DecidableEq n] (S₁ S₂ : ℝ) (M : Matrix n n ℝ),
      (1 - levelOp S₁ S₂ 0 ⊗ₖ M).det = (1 - S₁ • M).det * (1 - S₂ • M).det) ∧
    (∀ {n : Type} [Fintype n] [DecidableEq n] (S₁ S₂ : ℝ), S₂ ≠ 0 → S₁ + S₂ ≠ 0 →
      ∀ M : Matrix n n ℝ, (1 - levelOp S₁ S₂ 1 ⊗ₖ M).det = (1 - (S₁ + S₂) • M).det) :=
  ⟨time_division_turns, relTurn_moved, fun S₁ S₂ M => line_side_det S₁ S₂ M,
    fun S₁ S₂ hS hT M => meeting_side_det S₁ S₂ hS hT M⟩

/-- **R4.** -/
theorem coupling_R4 :
    (∀ r : Fin 5, ∑ s : State, ∑ s' : State,
      (if Continues s s' ∧ s'.2 = r ∧ s.1 ≠ 0 then 1 else 0 : ℕ) = 60) ∧
    (∀ (r : Fin 5) (U : Fin 16),
      (Finset.univ.filter fun p : State × State => p.1.1 = U ∧ Continues p.1 p.2 ∧
        p.2.2 = r).card = 4) ∧
    (∀ h : Fin 5, alongCount h h = 60 ∧ ∀ j, j ≠ h → alongCount h j = 59) ∧
    ((16 : ℚ) - 1) / 5 = 3 :=
  ⟨count_transitions, transitions_per_relation, availableTransitions_along, steps_along_lastDirection_count.2.1⟩

/-- **R5.** -/
theorem coupling_R5 (r : Fin 5) :
    ((1 : State → ℚ) ⬝ᵥ ((stepsAlong r * lamR r * offSinglet) *ᵥ 1)) /
        ((1 : State → ℚ) ⬝ᵥ ((stepsAlong r * offSinglet) *ᵥ 1)) = 32 / 60 ∧
    ∑ U ∈ Finset.univ.filter (fun U : Fin 16 => U ≠ 0), (4 / 60 : ℚ) • (recordG r U ⊙ recordG r U) =
      1 + (8 / 15 : ℚ) • ((Matrix.of fun _ _ => (1 : ℚ)) - 1) := by
  refine ⟨?_, meeting_matrix_trace r⟩
  rw [(prop195 r).2.2]
  norm_num

/-- **R6.** -/
theorem coupling_R6 :
    (∀ h : Fin 5, ((1 : State → ℚ) ⬝ᵥ ((stepsAlong h * lamR h * availableTransitionsProj h) *ᵥ 1)) /
        ((1 : State → ℚ) ⬝ᵥ ((stepsAlong h * availableTransitionsProj h) *ᵥ 1)) = 8 / 15) ∧
    (∀ r : Fin 5, ((1 : State → ℚ) ⬝ᵥ ((stepsAlong r * lamR r * offSinglet) *ᵥ 1)) /
        ((1 : State → ℚ) ⬝ᵥ ((stepsAlong r * offSinglet) *ᵥ 1)) = 8 / 15) :=
  ⟨prop195_availableTransitions, fun r => (prop195 r).2.2⟩

/-- **The coupling derived:** `c = 32/60 = 8/15` and `1 − c = 7/15`. -/
theorem coupling_derived : (32 : ℚ) / 60 = 8 / 15 ∧ 1 - (8 : ℚ) / 15 = 7 / 15 := by
  norm_num

end Comparison.GroupsContinuumLaw
