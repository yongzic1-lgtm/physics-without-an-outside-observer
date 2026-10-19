import Comparison.System.Existence.Line

/-!
# The proof system, the existence layer: Proposition 24 with P5 on the step sequences

A world line takes one step at each moment (P5 (a), `Steps`);
each step changes its two-spinor state to its own previous moment (P5 (b), `ChangesEachStep`) exactly when every first segment of its
steps is a walk (`changesEachStep_iff_histories`); and its two-spinor state at the moment `n` (P5 (c), `relAt`) is the
two-spinor state of the word of its first `n` steps (`relAt_eq_relation_of_word`). The proofs are A's (`Finite/Ties.lean`),
restated here so that the layer does not import the finite layer.
-/

namespace Comparison.System.Existence

/-- The first `n + 1` steps: the step `t n` before the first `n`. -/
theorem between_zero_succ_steps (t : Steps) (n : ℕ) : between t 0 (n + 1) = t n :: between t 0 n := by
  simp [between, List.range_succ]

/-- **P5 (c) on the words:** the two-spinor state at the moment `n` is the two-spinor state of the word of the first `n` steps. -/
theorem relAt_eq_relation_of_word (t : Steps) (n : ℕ) : relAt t n = relationOf (between t 0 n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [between_zero_succ_steps, relAt, ih]
    rfl

/-- **P5 (b) makes the walks:** a sequence of steps changes its two-spinor state at each step exactly when each of its
first segments is a walk. -/
theorem changesEachStep_iff_histories (t : Steps) : ChangesEachStep t ↔ ∀ n, IsHistory (between t 0 n) := by
  constructor
  · intro ht n
    induction n with
    | zero => exact List.IsChain.nil
    | succ n ih =>
      rw [between_zero_succ_steps]
      cases n with
      | zero =>
        rw [show between t 0 0 = [] from rfl]
        exact List.isChain_singleton _
      | succ m =>
        rw [between_zero_succ_steps] at ih ⊢
        exact List.isChain_cons_cons.mpr ⟨ht m, ih⟩
  · intro h k
    have hk := h (k + 2)
    rw [between_zero_succ_steps, between_zero_succ_steps] at hk
    exact (List.isChain_cons_cons.mp hk).1

/-- **Proposition 24 (a walk is a reduced word).** `γ_sγ_t` is a number exactly when `s = t`; the step `s`
changes the two-spinor state to its own previous moment, `ℓ_t`, exactly when `s ≠ t`, so the words in which every step changes
that two-spinor state (P5 (b)) are the reduced words, the walks; a line's steps (P5 (a)) change the two-spinor state at each step
exactly when every first segment of them is a walk, and its two-spinor state at the moment `n` is the two-spinor state of the
word of its first `n` steps (P5 (c)); every word reduces to exactly one reduced word by removing pairs `tt`; there
are `5·4ⁿ⁻¹` walks of length `n ≥ 1` (here `n + 1`, `5·4ⁿ`).

Recognition: none (each walk has four continuations, Prop. 26). Uses Props. 4, 10, P5 (a), (b), (c). -/
theorem prop_24_full :
    (∀ s t : Fin 5, (∃ c : ℂ, γ s * γ t = c • (1 : Matrix Four Four ℂ)) ↔ s = t) ∧
    (∀ s t : Fin 5, ell s = ell t ↔ s = t) ∧
    (∀ w : List (Fin 5), w.IsChain (fun s t => ell s ≠ ell t) ↔ IsHistory w) ∧
    (∀ t : Steps, ChangesEachStep t ↔ ∀ n, IsHistory (between t 0 n)) ∧
    (∀ (t : Steps) (n : ℕ), relAt t n = relationOf (between t 0 n)) ∧
    (∀ w : List (Fin 5), ∃! w' : List (Fin 5), Relation.ReflTransGen Cancel w w' ∧ IsHistory w') ∧
    (∀ n : ℕ, ((words (n + 1)).filter IsHistory).card = 5 * 4 ^ n) := by
  obtain ⟨p1, p2, p3, p4, p5⟩ := prop_24
  exact ⟨p1, p2, p3, changesEachStep_iff_histories, relAt_eq_relation_of_word, p4, p5⟩

end Comparison.System.Existence
