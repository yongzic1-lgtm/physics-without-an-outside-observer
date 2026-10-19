import Comparison.Law.Rows

/-!
# Book XXIV in Lean, part A

Propositions 200 to 203 (Book XXIV): the factors as values of the rule. Built on `Comparison.Law.Rule` and
`Comparison.Law.Rows`.

* **Prop. 200, the rule in four classes.** `rule_classes`: every divided set has `P = 1, L = 5` or
  `P = −1` with `|L| = 5, 3, 1`; `card_class_*`: these classes hold `32, 2, 10, 20` of the 64
  divided sets; `rule_values_classes`: on them `(e, Ψ, Φ) = (3/5, 1/28, −1/19)`, `(3/5, −1/22, −1/13)`,
  `(1/3, −1/6, −1/13)`, `(−1, 1/2, −1/13)`; `card_psi_compact`, `card_e_compact`: Proposition 108's
  compact forms hold at `52` and at `42` divided sets exactly.
* **Prop. 201, the three corrections.** `correction_singlet`: at `{n}` the reflection is `3/5` while
  `1 − 2/(4 + P)` gives `1/3`; `correction_offdiag`: Proposition 44's off-divided-set diagonal
  `2/L_S − 1` is `−3` at `C`, where the reflection is `−1`; `phi_is_psi_at_u`: `Φ_S = −P Ψ(u_S²)` at every
  divided set.
* **Prop. 202, the six, the three, the four.** `kC = (L@{} − L@C)/2 = 3`, the lines of `C`;
  `kC_response`: `L@{} − 8|u@{}| = 1/|u@{}| − 1 = k_C` and `2(1 − |u|)/|u| = 2k_C`; `uS_norm`:
  `|u_S| = 1/4` at every divided set; `LOmega_forms`: `L(Ω) = 1 + L@{} = 2k_C = 6 = Tr L²/16`;
  `trL2_lines`: with `d = 3, …, 9` lines the mean square comparison over the `2^{d−1}` two-spinor states is
  `1 + d`; `sixes_agree_iff`: `1 + d = 2(d − 2)` only at `d = 5`.
* **Prop. 203, the unit.** `one_closed_four`: from every arc exactly one closed walk of length
  four comes back, `a t a t`; `four_history_sign`: its sign is `γ_tγ_aγ_tγ_a = −1`;
  `trace_four`: `Tr B⁴ = 320`; `least_count`: the weight `z@{} = det Σ₆[∅, ∅] = 1` on one transition
  turns the zero at `|u@{}|/80 = 1/320`, the available transitions weight `L(Ω) + [along h]` at `1836/320`.
-/

open Comparison Comparison.Law Matrix

namespace Comparison.RuleAndLaw

/-! ## Proposition 200: the one rule at every divided set, in four classes -/

/-- **Every divided set is in one of four classes** of `(P, |L_S|)`. -/
theorem rule_classes (S : Finset (Fin 6)) :
    (signS S = 1 ∧ LZ S = 5) ∨
      (signS S = -1 ∧ (|LZ S| = 5 ∨ |LZ S| = 3 ∨ |LZ S| = 1)) := by
  revert S
  decide

theorem card_class_even :
    (Finset.univ.filter fun S : Finset (Fin 6) => signS S = 1).card = 32 := by
  decide

theorem card_class_five :
    (Finset.univ.filter fun S : Finset (Fin 6) => signS S = -1 ∧ |LZ S| = 5).card = 2 := by
  decide

theorem card_class_three :
    (Finset.univ.filter fun S : Finset (Fin 6) => signS S = -1 ∧ |LZ S| = 3).card = 10 := by
  decide

theorem card_class_one :
    (Finset.univ.filter fun S : Finset (Fin 6) => signS S = -1 ∧ |LZ S| = 1).card = 20 := by
  decide

/-- The class with `|L| = 5` and `P = −1` is `{n}` and the five directions. -/
theorem class_five_members :
    (Finset.univ.filter fun S : Finset (Fin 6) => signS S = -1 ∧ |LZ S| = 5) =
      {{0}, {1, 2, 3, 4, 5}} := by
  decide

theorem abs_cast_LZ (S : Finset (Fin 6)) : |(LZ S : ℝ)| = ((|LZ S| : ℤ) : ℝ) := by
  push_cast
  rfl

/-- The association read through `(P, |L|)`. -/
theorem psi_of (S : Finset (Fin 6)) (P L : ℤ) (hP : signS S = P) (hL : |LZ S| = L) :
    PsiS S = (P : ℂ) / ((L : ℂ) ^ 2 + 3 * (P : ℂ)) := by
  rw [PsiS_eq, LS_eq_LZ, hP]
  have h2 : (LZ S : ℂ) ^ 2 = ((|LZ S| : ℤ) : ℂ) ^ 2 := by
    rw [← Int.cast_pow, ← Int.cast_pow, sq_abs]
  rw [h2, hL]

/-- The reflection read through `|L|`. -/
theorem e_of (S : Finset (Fin 6)) (L : ℤ) (hL : |LZ S| = L) : eS S = 1 - 2 / (L : ℝ) := by
  rw [eS, norm_wS, abs_cast_LZ, hL]
  ring

/-- **The rule's values on the four classes.** -/
theorem rule_values_classes (S : Finset (Fin 6)) :
    (signS S = 1 → eS S = 3 / 5 ∧ PsiS S = 1 / 28 ∧ PhiS S = -1 / 19) ∧
    (signS S = -1 → |LZ S| = 5 → eS S = 3 / 5 ∧ PsiS S = -1 / 22 ∧ PhiS S = -1 / 13) ∧
    (signS S = -1 → |LZ S| = 3 → eS S = 1 / 3 ∧ PsiS S = -1 / 6 ∧ PhiS S = -1 / 13) ∧
    (signS S = -1 → |LZ S| = 1 → eS S = -1 ∧ PsiS S = 1 / 2 ∧ PhiS S = -1 / 13) := by
  refine ⟨fun hP => ?_, fun hP hL => ?_, fun hP hL => ?_, fun hP hL => ?_⟩
  · have hL5 : LZ S = 5 := by
      rcases rule_classes S with h | h
      · exact h.2
      · rw [hP] at h
        exact absurd h.1 (by decide)
    have hA : |LZ S| = 5 := by rw [hL5]; decide
    refine ⟨by rw [e_of S 5 hA]; norm_num, by rw [psi_of S 1 5 hP hA]; norm_num,
      by rw [PhiS_eq, hP]; norm_num⟩
  · exact ⟨by rw [e_of S 5 hL]; norm_num, by rw [psi_of S (-1) 5 hP hL]; norm_num,
      by rw [PhiS_eq, hP]; norm_num⟩
  · exact ⟨by rw [e_of S 3 hL]; norm_num, by rw [psi_of S (-1) 3 hP hL]; norm_num,
      by rw [PhiS_eq, hP]; norm_num⟩
  · exact ⟨by rw [e_of S 1 hL]; norm_num, by rw [psi_of S (-1) 1 hP hL]; norm_num,
      by rw [PhiS_eq, hP]; norm_num⟩

/-- **Proposition 108's compact association `1/(15 + 13P)` holds at exactly 52 divided sets**
(the 32 even ones and the 20 of 3|3), by `PsiS_plane`. -/
theorem card_psi_compact :
    (Finset.univ.filter fun S : Finset (Fin 6) =>
      Even S.card ∨ linesIn S = 2 ∨ linesIn S = 3).card = 52 := by
  decide

/-- **Proposition 108's compact reflection `1 − 2/(4 + P)` holds at exactly 42 divided sets** (the 32 even
ones and the 10 of a line alone and its complement), by `eS_four`. -/
theorem card_e_compact :
    (Finset.univ.filter fun S : Finset (Fin 6) =>
      signS S = 1 ∨ linesIn S = 1 ∨ linesIn S = 4).card = 42 := by
  decide

/-! ## Proposition 201: the three corrections -/

/-- **At the singlet `{n}` the reflection is `3/5`, while `1 − 2/(4 + P)` would give `1/3`**: Proposition
108's proof step for a divided set of one line or of none fails at the singlet (Proposition 201). -/
theorem correction_singlet :
    eS sSinglet = 3 / 5 ∧ (1 : ℝ) - 2 / (4 + (signS sSinglet : ℝ)) = 1 / 3 := by
  refine ⟨table_singlet.2.2.2.2.2.1, ?_⟩
  rw [show signS sSinglet = -1 by decide]
  norm_num

/-- **Proposition 44's off-divided-set diagonal `2/L_S − 1` is `−3` at `C`, where the reflection is
`e_C = −1`**: the reflection is `1 − 2/|L_S|`, not `2/L_S − 1` in size (Proposition 201). -/
theorem correction_offdiag : (2 / (LZ sC : ℝ) - 1) = -3 ∧ eS sC = -1 := by
  refine ⟨?_, table_C.2.2.2.2.2.1⟩
  rw [show LZ sC = -1 by decide]
  norm_num

/-- **`Φ_S = −P Ψ(u_S²)` at every divided set**: the signed excursion is the association read at the
step's weight `u_S²`. -/
theorem phi_is_psi_at_u (S : Finset (Fin 6)) : PhiS S = -(signS S : ℂ) * Psi (uS S ^ 2) := by
  rw [PhiS_eq, uS_sq, Psi]
  rcases signS_cases S with h | h <;> rw [h] <;> push_cast <;> norm_num

/-! ## Proposition 202: the six, the three and the four -/

/-- **`k_C = (L@{} − L@C)/2`**, the response that counts the lines of the strong divided set. -/
def kC : ℤ := (LZ sHere - LZ sC) / 2

theorem kC_eq : kC = 3 := by decide

/-- `k_C` is the number of lines of `C`. -/
theorem kC_lines : (linesIn sC : ℤ) = kC := by decide

/-- **`|u_S| = 1/4` at every divided set.** -/
theorem uS_norm (S : Finset (Fin 6)) : ‖uS S‖ = 1 / 4 := by
  rw [uS, norm_div, zS, norm_pow, Complex.norm_I, one_pow]
  norm_num

/-- **`L@{} − 8|u@{}| = 1/|u@{}| − 1 = k_C`, `2(1 − |u@{}|)/|u@{}| = 2k_C`.** -/
theorem kC_response :
    (LZ sHere : ℝ) - 8 * ‖uS sHere‖ = kC ∧ 1 / ‖uS sHere‖ - 1 = (kC : ℝ) ∧
      2 * (1 - ‖uS sHere‖) / ‖uS sHere‖ = 2 * (kC : ℝ) := by
  rw [uS_norm, kC_eq, show LZ sHere = 5 by decide]
  norm_num

/-- **`L(Ω) = 1 + L@{} = 2k_C = 6`, and `Tr L²/16 = 6`.** -/
theorem LOmega_forms :
    (Lvalue 0 : ℤ) = 1 + LZ sHere ∧ (Lvalue 0 : ℤ) = 2 * kC ∧ (Lvalue 0 : ℤ) = 6 ∧
      (L * L).trace / 16 = (6 : ℂ) := by
  refine ⟨by decide, by decide, by decide, trace_L_sq⟩

/-- The sum of the squared comparison over the `2^{d−1}` two-spinor states of `d` lines,
`L(S) = 1 + d − 2|S|` on the even sets `S`. -/
def trL2 (d : ℕ) : ℤ :=
  ∑ S ∈ (Finset.univ : Finset (Finset (Fin d))).filter (fun S => Even S.card),
    (1 + (d : ℤ) - 2 * (S.card : ℤ)) ^ 2

/-- **With `d = 3, …, 9` lines the mean square comparison is `1 + d`**: `Tr L² = (1 + d)·2^{d−1}`. -/
theorem trL2_lines :
    trL2 3 = 4 * 2 ^ 2 ∧ trL2 4 = 5 * 2 ^ 3 ∧ trL2 5 = 6 * 2 ^ 4 ∧ trL2 6 = 7 * 2 ^ 5 ∧
      trL2 7 = 8 * 2 ^ 6 ∧ trL2 8 = 9 * 2 ^ 7 ∧ trL2 9 = 10 * 2 ^ 8 := by
  decide +kernel

/-- **The sixes agree only at five lines**: `L(Ω) = 1 + d` and the critical response
`2k_C = 2(d − 2)` are equal exactly when `d = 5`. -/
theorem sixes_agree_iff (d : ℕ) : (1 + (d : ℤ) = 2 * ((d : ℤ) - 2)) ↔ d = 5 := by
  omega

/-- With `d` lines the step weighs `u = 1/(d − 1)` and `2(1 − u)/u = 2(d − 2)`. -/
theorem response_d_lines (d : ℕ) (hd : 2 ≤ d) :
    2 * (1 - 1 / ((d : ℝ) - 1)) / (1 / ((d : ℝ) - 1)) = 2 * ((d : ℝ) - 2) := by
  have h1 : (d : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  field_simp
  ring

/-! ## Proposition 203: the unit, the least count -/

/-- One step along `b` from a state. -/
def stepAlong (s : State) (b : Fin 5) : State := (transition b s.1, b)

theorem continues_stepAlong (s : State) (b : Fin 5) : Continues s (stepAlong s b) ↔ b ≠ s.2 := by
  simp [Continues, stepAlong]

/-- **Each arc begins exactly one closed walk of length four**: after the step `a` from the
state `s = (S, t)`, exactly one triple of further steps, each not the undo of the one before, comes
back to `s`: `(t, a, t)`, the walk `a t a t`. -/
theorem one_closed_four : ∀ (s : State) (a : Fin 5), a ≠ s.2 →
    ((Finset.univ : Finset (Fin 5 × Fin 5 × Fin 5)).filter fun q =>
      q.1 ≠ a ∧ q.2.1 ≠ q.1 ∧ q.2.2 ≠ q.2.1 ∧
        stepAlong (stepAlong (stepAlong (stepAlong s a) q.1) q.2.1) q.2.2 = s) =
      {(s.2, a, s.2)} := by
  decide +kernel

/-- **The closed walk of length four comes back with `−1`**: `γ_tγ_aγ_tγ_a = −1` for `a ≠ t`. -/
theorem four_history_sign {a t : Fin 5} (h : a ≠ t) : γ t * γ a * γ t * γ a = -1 := by
  have h1 : γ a * γ t = -(γ t * γ a) := γ_anticomm h
  calc γ t * γ a * γ t * γ a = γ t * (γ a * γ t) * γ a := by noncomm_ring
    _ = γ t * (-(γ t * γ a)) * γ a := by rw [h1]
    _ = -((γ t * γ t) * (γ a * γ a)) := by noncomm_ring
    _ = -1 := by rw [γ_mul_self, γ_mul_self, one_mul]

/-- **`Tr B⁴ = 320`**: one closed walk of length four from each of the 320 arcs. -/
theorem trace_four : (contB ^ 4).trace = 320 := trace_law_pow.2.2.2.1

/-- **The least count**: the weight `z@{} = det Σ₆[∅, ∅] = 1` on one transition turns the long-range zero
at `|u@{}|/80 = 1/320` per unit phase per step (the electron), and the available transitions weight
`L(Ω) + [along h]` at `1836/320` (the proton's count); the ratio is `1836`. -/
theorem least_count (h : Fin 5) (a₀ s₀ : State) (h₀ : Continues a₀ s₀) :
    zS sHere = 1 ∧ minor carriedC sHere sHere = 1 ∧ ‖uS sHere‖ / 80 = 1 / 320 ∧
      piU ⬝ᵥ (hadPow lawP (oneTransitionX a₀ s₀) 1 *ᵥ 1) = 1 / 320 ∧
      piU ⬝ᵥ (hadPow lawP (availableTransitionsLawX h (transitionX h)) 1 *ᵥ 1) = 1836 / 320 := by
  refine ⟨table_here.1, ?_, by rw [uS_norm]; norm_num, one_transition_angle_rate a₀ s₀ h₀,
    availableTransitions_angle_rate h⟩
  rw [minor_carriedC_self]
  simp [sHere, signS, linesIn]

/-- With the phase on every transition the unit would be the available transitions itself: `1836/296 = 6.2027…`
instead of `1836`. -/
theorem every_transition_reading : (1836 : ℚ) / 296 = 6 + 15 / 74 := by norm_num

end Comparison.RuleAndLaw

#print axioms Comparison.RuleAndLaw.rule_classes
#print axioms Comparison.RuleAndLaw.rule_values_classes
#print axioms Comparison.RuleAndLaw.card_psi_compact
#print axioms Comparison.RuleAndLaw.card_e_compact
#print axioms Comparison.RuleAndLaw.correction_singlet
#print axioms Comparison.RuleAndLaw.correction_offdiag
#print axioms Comparison.RuleAndLaw.phi_is_psi_at_u
#print axioms Comparison.RuleAndLaw.kC_response
#print axioms Comparison.RuleAndLaw.LOmega_forms
#print axioms Comparison.RuleAndLaw.trL2_lines
#print axioms Comparison.RuleAndLaw.sixes_agree_iff
#print axioms Comparison.RuleAndLaw.one_closed_four
#print axioms Comparison.RuleAndLaw.four_history_sign
#print axioms Comparison.RuleAndLaw.least_count
#print axioms Comparison.RuleAndLaw.card_class_even
#print axioms Comparison.RuleAndLaw.card_class_five
#print axioms Comparison.RuleAndLaw.card_class_three
#print axioms Comparison.RuleAndLaw.card_class_one
#print axioms Comparison.RuleAndLaw.class_five_members
#print axioms Comparison.RuleAndLaw.abs_cast_LZ
#print axioms Comparison.RuleAndLaw.psi_of
#print axioms Comparison.RuleAndLaw.e_of
#print axioms Comparison.RuleAndLaw.kC_eq
#print axioms Comparison.RuleAndLaw.kC_lines
#print axioms Comparison.RuleAndLaw.uS_norm
#print axioms Comparison.RuleAndLaw.response_d_lines
#print axioms Comparison.RuleAndLaw.continues_stepAlong
#print axioms Comparison.RuleAndLaw.trace_four
#print axioms Comparison.RuleAndLaw.every_transition_reading
