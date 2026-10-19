module

public import Comparison.Existence.Walk

/-!
# Book VI. Existence: the coin of one step (Proposition 28)

The amplitude of one step among the five
changes is the coin `σ = (2/5) 𝟙𝟙ᵀ − 1` (`𝟙𝟙ᵀ` the all-ones matrix): the undo direction carries
`2/5 − 1 = −3/5`, the reflection, and each of the four others `2/5`.

* `coin_apply`: the entries `−3/5` on the diagonal and `2/5` off it; `coin_transpose`: `σᵀ = σ`.
* `coin_mul_self`: `σ² = 1`; `coin_unitary`: `σ σ† = 1` over `ℂ`; `coin_column`: every column has
  length one, `(3/5)² + 4 (2/5)² = 1`; `coin_mulVec_ones`: `σ 𝟙 = 𝟙`; `coin_trace`: `tr σ = −3`.
* `involutions_ones`: the involutions `α + β 𝟙𝟙ᵀ` are exactly `±1` and `±σ`.
* `stepU`: the coin on the eighty states, `U(S, t) = Σ_s σ_st (transition s S, s)`;
  `stepU_eq`: `U = (2/5) B − (3/5) R` with `B` the four continuations and `R` the undo;
  `stepU_orthogonal`: `Uᵀ U = 1`.
-/

@[expose] public section

namespace Comparison

open Matrix hiding J
open Kronecker

/-- The all-ones `5 × 5` matrix `𝟙𝟙ᵀ`. -/
def ones5 : Matrix (Fin 5) (Fin 5) ℚ := Matrix.of fun _ _ => 1

/-- **The coin** `σ = (2/5) 𝟙𝟙ᵀ − 1`. -/
def coin : Matrix (Fin 5) (Fin 5) ℚ := (2 / 5 : ℚ) • ones5 - 1

/-- The coin's entries: the reflection `−3/5` back along the undo, `2/5` along each other change. -/
theorem coin_apply (i j : Fin 5) : coin i j = if i = j then -3 / 5 else 2 / 5 := by
  simp only [coin, ones5, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.one_apply,
    smul_eq_mul]
  split_ifs <;> norm_num

theorem coin_transpose : coinᵀ = coin := by
  ext i j
  simp only [Matrix.transpose_apply, coin_apply, eq_comm]

/-- **The coin is an involution:** `σ² = 1`. -/
theorem coin_mul_self : coin * coin = 1 := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_five]
  fin_cases i <;> fin_cases j <;> simp [coin_apply, Matrix.one_apply] <;> norm_num

/-- The coin is orthogonal: `σᵀ σ = 1`. -/
theorem coin_orthogonal : coinᵀ * coin = 1 := by
  rw [coin_transpose, coin_mul_self]

/-- The coin over `ℂ`. -/
noncomputable def coinC : Matrix (Fin 5) (Fin 5) ℂ := coin.map fun q : ℚ => (q : ℂ)

theorem coinC_apply (i j : Fin 5) : coinC i j = if i = j then -3 / 5 else 2 / 5 := by
  simp only [coinC, Matrix.map_apply, coin_apply]
  split_ifs <;> push_cast <;> ring

/-- **The coin is unitary:** `σ σ† = 1` over `ℂ`. -/
theorem coin_unitary : coinC * coinCᴴ = 1 := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_five]
  simp only [Matrix.conjTranspose_apply, coinC_apply]
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply] <;> norm_num

/-- Every column of the coin has length one: `(3/5)² + 4 (2/5)² = 1`. -/
theorem coin_column (j : Fin 5) : ∑ i, coin i j ^ 2 = 1 := by
  rw [Fin.sum_univ_five]
  fin_cases j <;> simp [coin_apply] <;> norm_num

/-- The coin keeps the mean line: `σ 𝟙 = 𝟙`. -/
theorem coin_mulVec_ones : coin *ᵥ (fun _ => 1) = fun _ => 1 := by
  funext i
  simp only [Matrix.mulVec, dotProduct, mul_one]
  rw [Fin.sum_univ_five]
  fin_cases i <;> simp [coin_apply] <;> norm_num

theorem coin_trace : coin.trace = -3 := by
  simp only [Matrix.trace, Matrix.diag, coin_apply, ite_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  norm_num

theorem ones5_mul_self : ones5 * ones5 = (5 : ℚ) • ones5 := by
  ext i j
  simp [ones5, Matrix.mul_apply]

/-- **The involutions made of `1` and `𝟙𝟙ᵀ`:** `(α + β 𝟙𝟙ᵀ)² = 1` exactly for `±1` and
`±σ`; `σ` itself is `α = −1, β = 2/5`. -/
theorem involutions_ones (α β : ℚ) :
    (α • (1 : Matrix (Fin 5) (Fin 5) ℚ) + β • ones5) * (α • 1 + β • ones5) = 1 ↔
      (α = 1 ∧ β = 0) ∨ (α = -1 ∧ β = 0) ∨ (α = -1 ∧ β = 2 / 5) ∨ (α = 1 ∧ β = -2 / 5) := by
  have key : (α • (1 : Matrix (Fin 5) (Fin 5) ℚ) + β • ones5) * (α • 1 + β • ones5) =
      (α ^ 2) • 1 + (2 * α * β + 5 * β ^ 2) • ones5 := by
    rw [add_mul, mul_add, mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, ones5_mul_self, smul_smul, smul_smul,
      smul_smul, smul_smul]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [key]
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    simp only [ones5, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
      smul_eq_mul] at h00 h01
    norm_num at h00 h01
    have hα : α ^ 2 = 1 := by linarith
    have hβ : β * (2 * α + 5 * β) = 0 := by linarith
    have hα' : (α - 1) * (α + 1) = 0 := by linear_combination hα
    rcases mul_eq_zero.mp hβ with hb | hb <;> rcases mul_eq_zero.mp hα' with ha | ha
    · left; exact ⟨by linarith, hb⟩
    · right; left; exact ⟨by linarith, hb⟩
    · right; right; right; exact ⟨by linarith, by linarith⟩
    · right; right; left; exact ⟨by linarith, by linarith⟩
  · intro h
    have h1 : α ^ 2 = 1 := by
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
    have h2 : 2 * α * β + 5 * β ^ 2 = 0 := by
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
    rw [h1, h2, one_smul, zero_smul, add_zero]

/-- The coin is `−1 + (2/5) 𝟙𝟙ᵀ`, one of the two involutions `±σ` that are not `±1`. -/
theorem coin_eq : coin = (-1 : ℚ) • (1 : Matrix (Fin 5) (Fin 5) ℚ) + (2 / 5 : ℚ) • ones5 := by
  rw [coin]
  module

/-! ## The coin on the eighty states -/

/-- The undo of a state: `(S, t) ↦ (transition t S, t)`; it is also the shift of the step `t`. -/
def undoState (s : State) : State := (transition s.2 s.1, s.2)

theorem undoState_undoState (s : State) : undoState (undoState s) = s := by
  simp [undoState, transition_transition]

/-- The undo `R` as a matrix on the eighty states. -/
def undoR : Matrix State State ℚ := Matrix.of fun s' s => if s' = undoState s then 1 else 0

/-- The four continuations `B`: entry `1` when `s'` continues `s`. -/
def contB : Matrix State State ℚ := Matrix.of fun s' s => if Continues s s' then 1 else 0

/-- The coin on the last-step direction, `1 ⊗ σ`. -/
def coinLastDirection : Matrix State State ℚ := (1 : Matrix (Fin 16) (Fin 16) ℚ) ⊗ₖ coin

/-- **The coin on the eighty states:** the state `(S, t)` goes to `Σ_s σ_st (transition s S, s)`. -/
def stepU : Matrix State State ℚ :=
  Matrix.of fun s' s => if s'.1 = transition s'.2 s.1 then coin s'.2 s.2 else 0

/-- **`U = (2/5) B − (3/5) R`:** four continuations with `2/5`, the undo with the reflection `−3/5`. -/
theorem stepU_eq : stepU = (2 / 5 : ℚ) • contB - (3 / 5 : ℚ) • undoR := by
  ext ⟨k', u'⟩ ⟨k, u⟩
  simp only [stepU, contB, undoR, undoState, Matrix.of_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, coin_apply]
  by_cases h : u' = u
  · subst h
    by_cases hk : k' = transition u' k <;> simp [Continues, Prod.ext_iff, hk] <;> norm_num
  · simp [Continues, Prod.ext_iff, h]

theorem undoR_transpose : undoRᵀ = undoR := by
  ext s' s
  simp only [Matrix.transpose_apply, undoR, Matrix.of_apply]
  by_cases h : s' = undoState s
  · rw [ite_eq_left h, ite_eq_left (by rw [h, undoState_undoState])]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h (by rw [h', undoState_undoState]))]

/-- **The undo is an involution:** `R² = 1`. -/
theorem undoR_mul_self : undoR * undoR = 1 := by
  ext s'' s
  rw [Matrix.mul_apply, Finset.sum_eq_single (undoState s)]
  · simp only [undoR, Matrix.of_apply, ite_true, mul_one, Matrix.one_apply, undoState_undoState]
  · intro b _ hb
    simp [undoR, hb]
  · simp

/-- `U` is the undo-shift after the coin on the last-step direction: `U = R (1 ⊗ σ)`. -/
theorem stepU_eq_mul : stepU = undoR * coinLastDirection := by
  ext ⟨k', u'⟩ ⟨k, u⟩
  rw [Matrix.mul_apply, Finset.sum_eq_single (undoState (k', u'))]
  · simp only [undoR, Matrix.of_apply, undoState_undoState, ite_true, one_mul]
    simp only [stepU, coinLastDirection, undoState, Matrix.kroneckerMap_apply, Matrix.one_apply]
    by_cases h : k' = transition u' k
    · subst h
      simp [transition_transition]
    · have h' : ¬transition u' k' = k := fun h'' => h (by rw [← h'', transition_transition])
      simp [h, h']
  · intro b _ hb
    simp only [undoR, Matrix.of_apply]
    rw [ite_eq_right, zero_mul]
    intro h
    apply hb
    rw [h, undoState_undoState]
  · simp

theorem coinLastDirection_orthogonal : coinLastDirectionᵀ * coinLastDirection = 1 := by
  rw [coinLastDirection, ← Matrix.kroneckerMap_transpose, ← Matrix.mul_kronecker_mul, Matrix.transpose_one,
    Matrix.one_mul, coin_orthogonal, Matrix.one_kronecker_one]

/-- **The coin on the eighty states is orthogonal:** `Uᵀ U = 1`. -/
theorem stepU_orthogonal : stepUᵀ * stepU = 1 := by
  rw [stepU_eq_mul, Matrix.transpose_mul, undoR_transpose, Matrix.mul_assoc,
    ← Matrix.mul_assoc undoR, undoR_mul_self, Matrix.one_mul, coinLastDirection_orthogonal]

end Comparison

end
