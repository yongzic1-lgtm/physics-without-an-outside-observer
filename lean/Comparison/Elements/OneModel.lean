module

public import Comparison.Elements.Observables

/-!
# Book I, Proposition 3: one model

On `ℂ^{2n}`, indexed by `Fin n × Fin 2`, the standard join is `Jn n = 1 ⊗ ε` (`n` blocks `ε`
on the diagonal) and the quaternionic structure is `Θ v = Jn n v̄`. P3's second clause asks that some
distinction is not zero and that every distinction squares to a number (`P3 n`).

* `not_P3_zero`, `distinctionN_one_eq_zero`: at `n = 0` and `n = 1` every distinction is zero.
* `diagWitness_isDistinction`, `diagWitness_sq_ne`: for `n ≥ 3` the quaternionic diagonal
  matrix `diag(1, -1, 0, …) ⊗ 1` is a distinction whose square is not a number.
* `P3_two`: at `n = 2` it holds (Book I).
* `one_model`: `P3 n ↔ n = 2`.
-/

@[expose] public section

namespace Comparison

open Matrix hiding J
open Complex Kronecker

/-- The standard join on `ℂ^{2n}`: `n` blocks `ε` on the diagonal. -/
def Jn (n : ℕ) : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ :=
  (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ ε

/-- A distinction of the standard model with `n` quaternionic dimensions: Hermitian, of trace
zero, commuting with the quaternionic structure `Θ v = Jn n v̄`. -/
def IsDistinctionN (n : ℕ) (a : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) : Prop :=
  aᴴ = a ∧ a.trace = 0 ∧ a * Jn n = Jn n * a.map star

/-- P3's second clause at size `n`: some distinction is not zero, and every distinction squares
to a real number. -/
def P3 (n : ℕ) : Prop :=
  (∃ a, IsDistinctionN n a ∧ a ≠ 0) ∧
    ∀ a, IsDistinctionN n a →
      ∃ c : ℝ, a * a = (c : ℂ) • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ)

/-- At `n = 2` the standard join is the join `J` of Book I. -/
theorem Jn_two : Jn 2 = J := rfl

theorem isDistinctionN_two (a : Matrix Four Four ℂ) : IsDistinctionN 2 a ↔ IsDistinction a :=
  Iff.rfl

/-- At `n = 2`, P3 holds. -/
theorem P3_two : P3 2 := P3_holds

/-- At `n = 0` there is nothing to distinguish. -/
theorem not_P3_zero : ¬ P3 0 := by
  rintro ⟨⟨a, -, ha⟩, -⟩
  apply ha
  ext ⟨i, _⟩
  exact i.elim0

set_option linter.flexible false in
-- the entry equations are read off by `simp` and closed by `linarith`
/-- At `n = 1` every distinction is zero. -/
theorem distinctionN_one_eq_zero (a : Matrix (Fin 1 × Fin 2) (Fin 1 × Fin 2) ℂ)
    (ha : IsDistinctionN 1 a) : a = 0 := by
  obtain ⟨hH, htr, hJ⟩ := ha
  have e : ∀ i j, (a * Jn 1) i j = (Jn 1 * a.map star) i j := fun i j => by rw [hJ]
  have h1 := e (0, 0) (0, 0)
  have h2 := e (0, 0) (0, 1)
  have h4 := congrFun (congrFun hH (0, 0)) (0, 1)
  have h5 := congrFun (congrFun hH (0, 0)) (0, 0)
  have h6 := congrFun (congrFun hH (0, 1)) (0, 1)
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, Jn, ε,
    Matrix.conjTranspose_apply] at h1 h2 h4 h5 h6
  simp [Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two] at htr
  rw [Complex.ext_iff] at h1 h2 h4 h5 h6 htr
  simp at h1 h2 h4 h5 h6 htr
  ext ⟨i, α⟩ ⟨j, β⟩
  fin_cases i
  fin_cases j
  fin_cases α <;> fin_cases β <;> apply Complex.ext <;> simp <;> linarith

theorem not_P3_one : ¬ P3 1 := by
  rintro ⟨⟨a, ha, hne⟩, -⟩
  exact hne (distinctionN_one_eq_zero a ha)

/-- The real diagonal `diag(1, -1, 0, …)` on `n ≥ 3` quaternionic dimensions. -/
def diagEntries (m : ℕ) : Fin (m + 3) → ℝ :=
  Pi.single ⟨0, by omega⟩ 1 - Pi.single ⟨1, by omega⟩ 1

/-- The quaternionic diagonal matrix `diag(1, -1, 0, …) ⊗ 1` on `ℂ^{2(m+3)}`. -/
noncomputable def diagWitness (m : ℕ) : Matrix (Fin (m + 3) × Fin 2) (Fin (m + 3) × Fin 2) ℂ :=
  Matrix.diagonal (fun i => (diagEntries m i : ℂ)) ⊗ₖ 1

theorem diagEntries_sum (m : ℕ) : ∑ i, diagEntries m i = 0 := by
  simp [diagEntries, Finset.sum_sub_distrib]

theorem diagEntries_zero (m : ℕ) : diagEntries m ⟨0, by omega⟩ = 1 := by
  simp [diagEntries]

theorem diagEntries_two (m : ℕ) : diagEntries m ⟨2, by omega⟩ = 0 := by
  simp [diagEntries]

theorem diagWitness_map_star (m : ℕ) : (diagWitness m).map star = diagWitness m := by
  ext ⟨i, α⟩ ⟨j, β⟩
  simp only [diagWitness, Matrix.map_apply, Matrix.kroneckerMap_apply, Matrix.diagonal_apply,
    Matrix.one_apply]
  split_ifs <;> simp

/-- For `n = m + 3 ≥ 3`, `diag(1, -1, 0, …) ⊗ 1` is a distinction. -/
theorem diagWitness_isDistinction (m : ℕ) : IsDistinctionN (m + 3) (diagWitness m) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [diagWitness, conjTranspose_kronecker, Matrix.diagonal_conjTranspose,
      Matrix.conjTranspose_one]
    congr 2
    funext i
    simp
  · rw [diagWitness, trace_kronecker, Matrix.trace_diagonal]
    have := diagEntries_sum m
    have h : ∑ i, (diagEntries m i : ℂ) = 0 := by exact_mod_cast this
    rw [h, zero_mul]
  · rw [diagWitness_map_star, diagWitness, Jn, ← mul_kronecker_mul, ← mul_kronecker_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]

/-- For `n = m + 3 ≥ 3` the square of `diag(1, -1, 0, …) ⊗ 1` is not a number. -/
theorem diagWitness_sq_ne (m : ℕ) (c : ℂ) :
    diagWitness m * diagWitness m ≠
      c • (1 : Matrix (Fin (m + 3) × Fin 2) (Fin (m + 3) × Fin 2) ℂ) := by
  intro h
  have h0 := congrFun (congrFun h (⟨0, by omega⟩, 0)) (⟨0, by omega⟩, 0)
  have h2 := congrFun (congrFun h (⟨2, by omega⟩, 0)) (⟨2, by omega⟩, 0)
  rw [diagWitness, ← mul_kronecker_mul] at h0 h2
  simp only [Matrix.kroneckerMap_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq,
    Matrix.mul_one, Matrix.one_apply_eq, Matrix.smul_apply, smul_eq_mul, diagEntries_zero,
    diagEntries_two] at h0 h2
  norm_num at h0 h2
  rw [← h0] at h2
  norm_num at h2

theorem not_P3_of_three_le (n : ℕ) (hn : 3 ≤ n) : ¬ P3 n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rintro ⟨-, hsq⟩
  obtain ⟨c, hc⟩ := hsq _ (diagWitness_isDistinction m)
  exact diagWitness_sq_ne m c hc

/-- **One model.** On `ℂ^{2n}` with the standard join, some distinction is not zero and every
distinction squares to a number exactly when `n = 2`: four amplitudes. -/
theorem one_model (n : ℕ) : P3 n ↔ n = 2 := by
  constructor
  · intro h
    rcases Nat.lt_or_ge n 3 with hn | hn
    · interval_cases n
      · exact absurd h not_P3_zero
      · exact absurd h not_P3_one
      · rfl
    · exact absurd h (not_P3_of_three_le n hn)
  · rintro rfl
    exact P3_two

end Comparison

end
