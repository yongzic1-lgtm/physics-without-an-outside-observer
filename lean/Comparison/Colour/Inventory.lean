module

public import Comparison.Colour.BoundStates
public import Comparison.Colour.ClosedAvailableTransitions
public import Comparison.Existence.Words

/-!
# Book XIV. The inventory of the closed available transitions; pole and source (Propositions 78, 79, 86)

A transition is one of the `M = 296`
continuations out of the seventy-four available directed edges of `h`.

**Prop. 86 (P.1), the transition's weight.**
* `transition_weight`: `⟨Ω, (L + γ_h ⊗ γ_t)Ω⟩ = 6 + δ_th` for every line `t`: the moment compared with
  itself on the six terms of `L`, and one more when the step is along the last-step direction.

**Prop. 78, the inventory.**
* `transition_inventory`: `Σ_transitions (6 + [along h]) = 1836` on the transitions themselves, for every last-step direction;
  `inventory_by_lines`: `Σ_t C_t(6 + δ_th) = 6M + C_h = 1836`;
  `inventory_trace`: `(M/5) Tr R_h(6 + P_h) = 1836` with `R_h = diag(σ, η, η, η, η)`;
  `availableTransitions_diag`: `R_h(t, t) = 5C_t/M`, `σ` on `h` and `η` on the others;
  `inventory_rates`: `1836/296 = 6 + 15/74`; `6·74/5 + 3 = 91.8`; `320/16 = 20` excursions;
  `20·91.8 = 1836`.

**Prop. 79, pole and source.**
* `pole_of_count`: `S(ζ, j) = cζ − jm` vanishes at `ζ₀ = jm/c`, `(ζ − ζ₀)/S = 1/c`, and `ζ₀`
  moves by `m/c` per unit of `j`; `−∂_j S = m`.
* `rest_poles`: `1/σ = 74/75`, `1/η = 296/295`, `(σ + 4η)/5 = 1`, `σ − 1 = 4(1 − η) = 1/74`.
* `record_count`: with the record `(T_h, h)` added, every line is asked `60` times.
* `three_readings`: for `X = 6 + P_h`: source `(M/5) Tr R_h X = 1836`, pole
  `(M/5) Tr R_h⁻¹X = 40588112/22125` (`= 1834.4909…`), every line alike `(300/5) Tr X = 1860`.
-/

@[expose] public section

namespace Comparison

open Matrix
open Complex Kronecker

/-! ## Prop. 86: the transition's weight -/

/-- `(γ_h ⊗ γ_t)Ω = (γ_hγ_t ⊗ 1)Ω`: a line on the second system moves to the first. -/
theorem pair_on_singlet (h t : Fin 5) :
    (γ h ⊗ₖ γ t) *ᵥ Ω = ((γ h * γ t) ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω := by
  rw [Ω, kron_mulVec_relOf, kron_mulVec_relOf, Matrix.transpose_one, Matrix.mul_one]
  simp only [Matrix.mul_assoc, MΩ_mul_γ_transpose]

theorem singlet_inner_plane (h t : Fin 5) :
    star Ω ⬝ᵥ (((γ h * γ t) ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω) = if h = t then 1 else 0 := by
  rw [Ω, kron_mulVec_relOf, Matrix.transpose_one, Matrix.mul_one, dot_relOf, Matrix.trace_mul_comm,
    Matrix.mul_assoc, MΩ_mul_conjTranspose, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
    trace_γ_mul_γ]
  split_ifs <;> norm_num

/-- **Prop. 86, the transition's weight:** `⟨Ω, (L + γ_h ⊗ γ_t)Ω⟩ = 6 + δ_th`. -/
theorem transition_weight (h t : Fin 5) :
    star Ω ⬝ᵥ ((L + γ h ⊗ₖ γ t) *ᵥ Ω) = 6 + if t = h then 1 else 0 := by
  rw [Matrix.add_mulVec, dotProduct_add, L_singlet, dotProduct_smul, Ω_norm, pair_on_singlet,
    singlet_inner_plane]
  rcases eq_or_ne t h with e | e
  · subst e
    simp
  · simp [e, Ne.symm e]

/-! ## Prop. 78: the inventory -/

/-- **The inventory on the transitions:** `Σ_transitions (6 + [along h]) = 6M + C_h = 1836`, each transition counted
once. -/
theorem transition_inventory : ∀ h : Fin 5,
    ∑ p ∈ Finset.univ.filter (fun p : State × State => inExcursion h p.1 = true ∧ Continues p.1 p.2),
      (6 + if p.2.2 = h then 1 else 0) = 1836 := by
  decide +kernel

/-- `Σ_t C_t(6 + δ_th) = 6M + C_h = 1836`. -/
theorem inventory_by_lines (h : Fin 5) :
    ∑ t, (alongCount h t : ℚ) * (6 + if t = h then 1 else 0) = 1836 := by
  have hM : (∑ j, (alongCount h j : ℚ)) = 296 := by
    have := availableTransitions_total h
    exact_mod_cast this
  have hC : (alongCount h h : ℚ) = 60 := by
    have := (availableTransitions_along h).1
    exact_mod_cast this
  have e : ∀ t, (alongCount h t : ℚ) * (6 + if t = h then 1 else 0) =
      6 * (alongCount h t : ℚ) + if t = h then (alongCount h t : ℚ) else 0 := by
    intro t
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun t _ => e t), Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_ite_eq', hM]
  simp only [Finset.mem_univ, ↓reduceIte, hC]
  norm_num

/-- `σ = 75/74`. -/
def σc : ℚ := 75 / 74
/-- `η = 295/296`. -/
def ηc : ℚ := 295 / 296

/-- The available transitions as the count per step of each line: `R_h = diag(σ, η, η, η, η)` with `σ` on `h`. -/
def availableTransitionsDiag (h : Fin 5) : Matrix (Fin 5) (Fin 5) ℚ :=
  Matrix.diagonal fun t => if t = h then σc else ηc

/-- `R_h(t, t) = 5C_t/M`. -/
theorem availableTransitions_diag (h t : Fin 5) :
    availableTransitionsDiag h t t = 5 * (alongCount h t : ℚ) / ∑ j, (alongCount h j : ℚ) := by
  have hM : (∑ j, (alongCount h j : ℚ)) = 296 := by
    have := availableTransitions_total h
    exact_mod_cast this
  rw [hM, availableTransitionsDiag, Matrix.diagonal_apply_eq]
  by_cases ht : t = h
  · subst ht
    have hC : (alongCount t t : ℚ) = 60 := by
      have := (availableTransitions_along t).1
      exact_mod_cast this
    simp only [↓reduceIte, hC, σc]
    norm_num
  · have hC : (alongCount h t : ℚ) = 59 := by
      have := (availableTransitions_along h).2 t ht
      exact_mod_cast this
    simp only [ht, ↓reduceIte, hC, ηc]
    norm_num

/-- The weight `X = L(Ω) + P_h = 6 + P_h` on the five directions. -/
def weightX (h : Fin 5) : Matrix (Fin 5) (Fin 5) ℚ :=
  Matrix.diagonal fun t => 6 + if t = h then 1 else 0

theorem trace_diag_mul (f g : Fin 5 → ℚ) :
    (Matrix.diagonal f * Matrix.diagonal g).trace = ∑ t, f t * g t := by
  rw [Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]

/-- **`(M/5) Tr R_h(L(Ω) + P_h) = 1836`.** -/
theorem inventory_trace (h : Fin 5) : (296 / 5 : ℚ) * (availableTransitionsDiag h * weightX h).trace = 1836 := by
  rw [availableTransitionsDiag, weightX, trace_diag_mul]
  fin_cases h <;> simp [Fin.sum_univ_five, σc, ηc] <;> norm_num

/-- **The rates:** `1836/296 = 6 + 15/74` per transition; `6·74/5 + 3 = 91.8` per excursion; `320/16 = 20`
excursions in a stationary cycle; `20·91.8 = 1836`. -/
theorem inventory_rates :
    (1836 : ℚ) / 296 = 6 + 15 / 74 ∧ (6 * 74 / 5 + 3 : ℚ) = 459 / 5 ∧ (320 : ℚ) / 16 = 20 ∧
      20 * (459 / 5 : ℚ) = 1836 := by
  norm_num

/-! ## Prop. 79: pole and source -/

/-- **A pole carries the inverse of its count, a source the count itself:** `S(ζ, j) = cζ − jm`
vanishes at `ζ₀ = jm/c`, has `(ζ − ζ₀)/S(ζ, j) = 1/c` away from it, and `ζ₀` moves with slope
`m/c`. -/
theorem pole_of_count (c j m ζ : ℝ) (hc : c ≠ 0) :
    c * (j * m / c) - j * m = 0 ∧
      (ζ ≠ j * m / c → (ζ - j * m / c) / (c * ζ - j * m) = 1 / c) ∧
      HasDerivAt (fun j' : ℝ => j' * m / c) (m / c) j ∧
      HasDerivAt (fun j' : ℝ => -(c * ζ - j' * m)) m j := by
  have e : c * ζ - j * m = c * (ζ - j * m / c) := by
    rw [mul_sub, mul_div_assoc', mul_div_cancel_left₀ _ hc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mul_div_assoc', mul_div_cancel_left₀ _ hc, sub_self]
  · intro hζ
    have hz : ζ - j * m / c ≠ 0 := sub_ne_zero.mpr hζ
    rw [e, div_mul_eq_div_div_swap, div_self hz]
  · have := ((hasDerivAt_id j).mul_const m).div_const c
    simpa using this
  · have h1 : HasDerivAt (fun j' : ℝ => j' * m - c * ζ) m j := by
      simpa using ((hasDerivAt_id j).mul_const m).sub_const (c * ζ)
    convert h1 using 1
    funext x
    ring

/-- **The rest poles:** `1/σ = 74/75` on `h`, `1/η = 296/295` on the others; every line alike,
`(σ + 4η)/5 = 1`; `σ − 1 = 4(1 − η) = 1/74`. -/
theorem rest_poles :
    1 / σc = 74 / 75 ∧ 1 / ηc = 296 / 295 ∧ (σc + 4 * ηc) / 5 = 1 ∧ σc - 1 = 4 * (1 - ηc) ∧
      σc - 1 = 1 / 74 := by
  norm_num [σc, ηc]

/-- **With the record `(T_h, h)` added, every line is asked sixty times.** -/
theorem record_count : ∀ h j : Fin 5,
    (Finset.univ.filter fun s : State =>
      (inExcursion h s = true ∨ s = (lastDirectionRel h, h)) ∧ s.2 ≠ j).card = 60 := by
  decide +kernel

/-- **The three readings of `X = L(Ω) + P_h`:** the source `(M/5) Tr R_h X = 1836`, the pole
`(M/5) Tr R_h⁻¹ X = 40588112/22125`, every line alike `(300/5) Tr X = 1860`. -/
theorem three_readings (h : Fin 5) :
    (296 / 5 : ℚ) * ∑ t, (if t = h then σc else ηc) * (6 + if t = h then 1 else 0) = 1836 ∧
    (296 / 5 : ℚ) * ∑ t, (if t = h then σc else ηc)⁻¹ * (6 + if t = h then 1 else 0) =
      40588112 / 22125 ∧
    (300 / 5 : ℚ) * ∑ t, ((6 : ℚ) + if t = h then 1 else 0) = 1860 := by
  fin_cases h <;> simp [Fin.sum_univ_five, σc, ηc] <;> norm_num

theorem pole_reading_value :
    (1834.49 : ℚ) < 40588112 / 22125 ∧ (40588112 : ℚ) / 22125 < 1834.50 := by
  norm_num

end Comparison

end
