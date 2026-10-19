module

public import Comparison.WholePicture.Spectra
public import Comparison.Mass.Harmonic
public import Comparison.Colour.GramTerm
public import Comparison.Existence.Matter

/-!
# The whole picture, statement 11: the polar step, the charge current and 24/11

`B = stepR` is step on the eighty states
over `ℝ` (`B_{s′s} = 1` when `s′` continues `s`). The Green function
`(5 − A)⁺ = (7 + A)/32 − 3J/128` and `b = 7/16` stand in `RuleAndLaw/CriticalGerm.lean`
(`green_identity`, `resistance_values`).

* `stepR_gram`: **`BᵀB = I₁₆ ⊗ (I + 3J₅)`**: `4` on the diagonal, `3` between two states of one
  two-spinor state, `0` across two-spinor states; `stepR_gram_proj`: `BᵀB = 1 + 15Π`, `Π = I₁₆ ⊗ J₅/5`, an
  orthogonal projector of trace `16` (`lastDirectionProj_idem`, `lastDirectionProj_symm`, `trace_lastDirectionProj`).
* `stepR_gram_charpoly`: **`det(X − BᵀB) = (X − 1)⁶⁴ (X − 16)¹⁶`**, so **the singular values of `B`
  are `1` (sixty-four times) and `4` (sixteen times)**; `absB = 1 + 3Π`: `absB_sq`: `|B|² = BᵀB`;
  `absB_charpoly`: `det(X − |B|) = (X − 1)⁶⁴(X − 4)¹⁶`; `absB_polar`:
  **`|B| = 2(e^ξΠ + e^{−ξ}(1 − Π))` with `ξ = log 2`**, the spectral form of `2e^{ξ(2Π − I)}`
  (`tanh(ξ/4) = 3 − 2√2` is `ArticleStatements/Radar.lean`'s `tanh_quarter`).
* `lineCharge = (0, 1, −1/3, −1/3, −1/3)`; `charge_additive`: the charge of every two-spinor state is the
  sum of its lines' charges; `charge_current`: **`c = 2 Var Q = 8/15`** over the five directions.
* `twentyfour_eleven`: **`Tr L²/4 = 24`** and the positive vertices `1 + 10 = 11`.
-/

@[expose] public section

namespace Comparison.WholePicture

open Matrix Polynomial

/-! ## The polar step -/

/-- The last-step direction's projector `Π = I₁₆ ⊗ J₅/5`: the mean over the five last-step directions of one two-spinor state. -/
noncomputable def lastDirectionProj : Matrix State State ℝ :=
  Matrix.of fun p q => if p.1 = q.1 then 1 / 5 else 0

theorem transition_inj (s : Fin 5) {x y : Fin 16} (h : transition s x = transition s y) : x = y := by
  have := congrArg (transition s) h
  rwa [transition_transition, transition_transition] at this

theorem sum_transition_transition (s : Fin 5) (x y : Fin 16) :
    ∑ z : Fin 16, (if z = transition s x then (1 : ℝ) else 0) * (if z = transition s y then 1 else 0) =
      if x = y then 1 else 0 := by
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (transition s x)]
  simp only [Finset.mem_univ, ite_true]
  by_cases h : x = y
  · simp [h]
  · have : transition s x ≠ transition s y := fun e => h (transition_inj s e)
    simp [h, this]

theorem two_avoid_count (t t' : Fin 5) :
    ∑ s : Fin 5, (if s ≠ t then (1 : ℝ) else 0) * (if s ≠ t' then 1 else 0) =
      if t = t' then 4 else 3 := by
  fin_cases t <;> fin_cases t' <;> simp [Fin.sum_univ_five] <;> norm_num

/-- **`BᵀB = I₁₆ ⊗ (I + 3J₅)`**: two states of one two-spinor state share `3` continuations (`4` with
themselves), two states of different two-spinor states none. -/
theorem stepR_gram (p q : State) :
    (stepRᵀ * stepR) p q = if p.1 = q.1 then (if p.2 = q.2 then 4 else 3) else 0 := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, stepR, stepT, Matrix.of_apply, Continues]
  rw [Fintype.sum_prod_type_right]
  have h : ∀ (s : Fin 5) (z : Fin 16),
      (if s ≠ p.2 ∧ z = transition s p.1 then (1 : ℝ) else 0) *
          (if s ≠ q.2 ∧ z = transition s q.1 then (1 : ℝ) else 0) =
        ((if s ≠ p.2 then (1 : ℝ) else 0) * (if s ≠ q.2 then 1 else 0)) *
          ((if z = transition s p.1 then (1 : ℝ) else 0) * (if z = transition s q.1 then 1 else 0)) := by
    intro s z
    by_cases h1 : s ≠ p.2 <;> by_cases h2 : z = transition s p.1 <;> by_cases h3 : s ≠ q.2 <;>
      by_cases h4 : z = transition s q.1 <;> simp [h1, h2, h3, h4]
  simp only [h, ← Finset.mul_sum, sum_transition_transition]
  by_cases hx : p.1 = q.1
  · simp only [hx, ite_true, mul_one]
    exact two_avoid_count p.2 q.2
  · simp [hx]

/-- **`BᵀB = 1 + 15Π`.** -/
theorem stepR_gram_proj : stepRᵀ * stepR = 1 + (15 : ℝ) • lastDirectionProj := by
  ext p q
  rw [stepR_gram, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, lastDirectionProj, Matrix.of_apply]
  rcases p with ⟨x, t⟩
  rcases q with ⟨y, t'⟩
  by_cases hx : x = y <;> by_cases ht : t = t' <;> simp [hx, ht] <;> norm_num

theorem lastDirectionProj_symm : lastDirectionProjᵀ = lastDirectionProj := by
  ext p q
  simp only [Matrix.transpose_apply, lastDirectionProj, Matrix.of_apply]
  by_cases h : p.1 = q.1
  · simp [h]
  · simp [h, Ne.symm h]

/-- `Π² = Π`. -/
theorem lastDirectionProj_idem : lastDirectionProj * lastDirectionProj = lastDirectionProj := by
  ext p q
  simp only [Matrix.mul_apply, lastDirectionProj, Matrix.of_apply]
  rw [Fintype.sum_prod_type]
  by_cases h : p.1 = q.1
  · simp only [h, ite_true]
    rw [Finset.sum_eq_single q.1]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  · simp only [h, ite_false]
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun s _ => ?_
    by_cases h1 : p.1 = x
    · have : ¬ x = q.1 := fun e => h (h1.trans e)
      simp [this]
    · simp [h1]

/-- `tr Π = 16`. -/
theorem trace_lastDirectionProj : lastDirectionProj.trace = 16 := by
  simp only [Matrix.trace, Matrix.diag, lastDirectionProj, Matrix.of_apply, ite_true, Finset.sum_const,
    Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  norm_num

theorem stepR_gram_symm : (stepRᵀ * stepR).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul,
    Matrix.transpose_transpose]

/-- `(BᵀB − 1)(BᵀB − 16) = 0`. -/
theorem stepR_gram_quadratic :
    (stepRᵀ * stepR) * (stepRᵀ * stepR) + (-17 : ℝ) • (stepRᵀ * stepR) +
      (16 : ℝ) • (1 : Matrix State State ℝ) = 0 := by
  rw [stepR_gram_proj]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, lastDirectionProj_idem]
  module

theorem trace_stepR_gram : (stepRᵀ * stepR).trace = 320 := by
  rw [stepR_gram_proj, Matrix.trace_add, Matrix.trace_smul, trace_lastDirectionProj, Matrix.trace_one]
  simp only [Fintype.card_prod, Fintype.card_fin, smul_eq_mul]
  norm_num

/-- **The singular values of `B`:** `det(X − BᵀB) = (X − 1)⁶⁴ (X − 16)¹⁶`, so `B` has the singular
values `1` (sixty-four times) and `4` (sixteen times). -/
theorem stepR_gram_charpoly :
    (stepRᵀ * stepR).charpoly = (X - C (1 : ℝ)) ^ 64 * (X - C (16 : ℝ)) ^ 16 := by
  set hA := stepR_gram_symm
  have hroot := eig_root_quadratic hA (-17) 16 stepR_gram_quadratic
  have hs : ∀ i, hA.eigenvalues i ∈ ({1, 16} : Finset ℝ) := by
    intro i
    have h := hroot i
    have : (hA.eigenvalues i - 1) * (hA.eigenvalues i - 16) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h1 | h1
    · simp [sub_eq_zero.mp h1]
    · simp [sub_eq_zero.mp h1]
  have hcard := card_of_values hA _ hs
  have htr := trace_of_values hA _ hs
  rw [trace_stepR_gram] at htr
  rw [charpoly_of_values hA _ hs]
  rw [Finset.sum_pair (by norm_num : (1 : ℝ) ≠ 16)] at hcard htr
  rw [Finset.prod_pair (by norm_num : (1 : ℝ) ≠ 16)]
  simp only [Fintype.card_prod, Fintype.card_fin] at hcard
  set n1 := (Finset.univ.filter fun i => hA.eigenvalues i = 1).card
  set n16 := (Finset.univ.filter fun i => hA.eigenvalues i = 16).card
  have h1 : (n1 : ℝ) + n16 = 80 := by exact_mod_cast hcard
  have e16 : n16 = 16 := by
    have : (n16 : ℝ) = 16 := by linarith
    exact_mod_cast this
  have e1 : n1 = 64 := by omega
  rw [e1, e16]

/-- **The polar step** `|B| = 1 + 3Π`. -/
noncomputable def absB : Matrix State State ℝ := 1 + (3 : ℝ) • lastDirectionProj

/-- `|B|² = BᵀB`. -/
theorem absB_sq : absB * absB = stepRᵀ * stepR := by
  rw [stepR_gram_proj, absB]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
    Matrix.mul_smul, lastDirectionProj_idem]
  module

theorem absB_symm : absB.IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, absB, Matrix.transpose_add,
    Matrix.transpose_one, Matrix.transpose_smul, lastDirectionProj_symm]

/-- `det(X − |B|) = (X − 1)⁶⁴(X − 4)¹⁶`: the singular values `1` and `4`. -/
theorem absB_charpoly : absB.charpoly = (X - C (1 : ℝ)) ^ 64 * (X - C (4 : ℝ)) ^ 16 := by
  set hA := absB_symm
  have hq : absB * absB + (-5 : ℝ) • absB + (4 : ℝ) • (1 : Matrix State State ℝ) = 0 := by
    rw [absB]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, lastDirectionProj_idem]
    module
  have hroot := eig_root_quadratic hA (-5) 4 hq
  have hs : ∀ i, hA.eigenvalues i ∈ ({1, 4} : Finset ℝ) := by
    intro i
    have h := hroot i
    have : (hA.eigenvalues i - 1) * (hA.eigenvalues i - 4) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h1 | h1
    · simp [sub_eq_zero.mp h1]
    · simp [sub_eq_zero.mp h1]
  have htrace : absB.trace = 128 := by
    rw [absB, Matrix.trace_add, Matrix.trace_smul, trace_lastDirectionProj, Matrix.trace_one]
    simp only [Fintype.card_prod, Fintype.card_fin, smul_eq_mul]
    norm_num
  have hcard := card_of_values hA _ hs
  have htr := trace_of_values hA _ hs
  rw [htrace] at htr
  rw [charpoly_of_values hA _ hs]
  rw [Finset.sum_pair (by norm_num : (1 : ℝ) ≠ 4)] at hcard htr
  rw [Finset.prod_pair (by norm_num : (1 : ℝ) ≠ 4)]
  simp only [Fintype.card_prod, Fintype.card_fin] at hcard
  set n1 := (Finset.univ.filter fun i => hA.eigenvalues i = 1).card
  set n4 := (Finset.univ.filter fun i => hA.eigenvalues i = 4).card
  have h1 : (n1 : ℝ) + n4 = 80 := by exact_mod_cast hcard
  have e4 : n4 = 16 := by
    have : (n4 : ℝ) = 16 := by linarith
    exact_mod_cast this
  have e1 : n1 = 64 := by omega
  rw [e1, e4]

/-- **The polar form** `|B| = 2(e^ξ Π + e^{−ξ}(1 − Π))` with `ξ = log 2`. -/
theorem absB_polar :
    absB = (2 : ℝ) • (Real.exp (Real.log 2) • lastDirectionProj +
      Real.exp (-Real.log 2) • (1 - lastDirectionProj)) := by
  rw [Real.exp_log (by norm_num), Real.exp_neg, Real.exp_log (by norm_num), absB]
  module

/-! ## The charge current -/

/-- The charges of the five directions `h, k, c₁, c₂, c₃` (Proposition 65): `(0, 1, −1/3, −1/3, −1/3)`.
-/
def lineCharge : Fin 5 → ℚ := ![0, 1, -1 / 3, -1 / 3, -1 / 3]

/-- Three times the charges of the five directions. -/
def lineCharge3 : Fin 5 → ℤ := ![0, 3, -1, -1, -1]

theorem charge3_additive : ∀ r : Fin 16, charge3 0 1 r = ∑ s ∈ disagreeSet r, lineCharge3 s := by
  decide

/-- The charge of every two-spinor state is the sum of its lines' charges (the plane `{0, 1}`). -/
theorem charge_additive (r : Fin 16) : charge 0 1 r = ∑ s ∈ disagreeSet r, lineCharge s := by
  rw [charge_eq3, charge3_additive, Int.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun s _ => ?_
  fin_cases s <;> simp [lineCharge, lineCharge3]

/-- **The charge current two lines carry together:** `c = 2 Var Q = 8/15` over the five directions. -/
theorem charge_current :
    2 * ((∑ s, lineCharge s ^ 2) / 5 - ((∑ s, lineCharge s) / 5) ^ 2) = 8 / 15 := by
  simp [lineCharge, Fin.sum_univ_five]
  norm_num

/-! ## 24/11 -/

/-- **`Tr L²/4 = 24`** traceless rotations against the **`1 + 10 = 11`** positive vertices. -/
theorem twentyfour_eleven :
    (L * L).trace / 4 = 24 ∧
    Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' L) 6) +
      Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' L) 2) = 11 := by
  constructor
  · have h := trace_L_sq
    linear_combination 4 * h
  · rw [finrank_eigenspace_L_six, finrank_eigenspace_L_two]

end Comparison.WholePicture

end
