module

public import Comparison.Elements.Observables

/-!
# Book I, Propositions 5 and 7: the two sides of a line and their overlap

For `n ∈ ℝ⁵`, `γ(n) = Σ n_s γ_s` (`γv`), and for a unit `n` the plus side of the line `n` is
`Q_n = (1 + γ(n)) / 2` (`side`).

* `anticomm_γv`: `γ(n) γ(m) + γ(m) γ(n) = 2 (n·m)`: perpendicular lines anticommute.
* `γv_mul_self`: `γ(n)² = |n|²`, so `γ(n)` is a line exactly when `|n| = 1`.
* `side_mul_self`, `side_add_side_neg`, `side_mul_side_neg`: `Q_n² = Q_n`, `Q_n + Q_{−n} = 1`,
  `Q_n Q_{−n} = 0`: a line splits a system into two sides.
* `trace_side`: `tr Q_n = 2`: each side has two dimensions.
* `overlap`: **`Q_n Q_m Q_n = ((1 + n·m) / 2) Q_n`**, and the same number with `n` and `m`
  exchanged (`overlap_symm`).
-/

@[expose] public section

namespace Comparison

open Matrix hiding J
open Complex Kronecker

/-- `γ(n) = Σ n_s γ_s`, the distinction with coordinates `n`. -/
noncomputable def γv (n : Fin 5 → ℝ) : Matrix Four Four ℂ := ∑ s, (n s : ℂ) • γ s

/-- The plus side of the line `n`: `Q_n = (1 + γ(n)) / 2`. -/
noncomputable def side (n : Fin 5 → ℝ) : Matrix Four Four ℂ := (1 / 2 : ℂ) • (1 + γv n)

theorem γv_mul_self (n : Fin 5 → ℝ) :
    γv n * γv n = ((∑ s, n s ^ 2 : ℝ) : ℂ) • (1 : Matrix Four Four ℂ) := by
  rw [γv, sq_sum]
  push_cast
  rfl

theorem γv_add (n m : Fin 5 → ℝ) : γv (n + m) = γv n + γv m := by
  simp only [γv, Pi.add_apply, Complex.ofReal_add, add_smul, Finset.sum_add_distrib]

theorem γv_neg (n : Fin 5 → ℝ) : γv (-n) = -γv n := by
  simp only [γv, Pi.neg_apply, Complex.ofReal_neg, neg_smul, Finset.sum_neg_distrib]

/-- **Perpendicular lines anticommute:** `γ(n) γ(m) + γ(m) γ(n) = 2 (n·m)`. -/
theorem anticomm_γv (n m : Fin 5 → ℝ) :
    γv n * γv m + γv m * γv n = ((2 * ∑ s, n s * m s : ℝ) : ℂ) • (1 : Matrix Four Four ℂ) := by
  have h := γv_mul_self (n + m)
  rw [γv_add, add_mul, mul_add, mul_add, γv_mul_self, γv_mul_self] at h
  have e : ((∑ s, (n + m) s ^ 2 : ℝ) : ℂ) =
      ((∑ s, n s ^ 2 : ℝ) : ℂ) + ((2 * ∑ s, n s * m s : ℝ) : ℂ) + ((∑ s, m s ^ 2 : ℝ) : ℂ) := by
    simp only [Pi.add_apply]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring
  rw [e, add_smul, add_smul] at h
  set A := ((∑ s, n s ^ 2 : ℝ) : ℂ) • (1 : Matrix Four Four ℂ)
  set B := ((∑ s, m s ^ 2 : ℝ) : ℂ) • (1 : Matrix Four Four ℂ)
  calc γv n * γv m + γv m * γv n = (A + γv n * γv m + (γv m * γv n + B)) - A - B := by abel
    _ = (A + ((2 * ∑ s, n s * m s : ℝ) : ℂ) • (1 : Matrix Four Four ℂ) + B) - A - B := by rw [h]
    _ = ((2 * ∑ s, n s * m s : ℝ) : ℂ) • (1 : Matrix Four Four ℂ) := by abel

theorem side_mul_self (n : Fin 5 → ℝ) (hn : ∑ s, n s ^ 2 = 1) : side n * side n = side n := by
  have hX : γv n * γv n = 1 := by rw [γv_mul_self, hn]; simp
  simp only [side, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add, Matrix.one_mul,
    Matrix.mul_one, hX]
  module

theorem side_add_side_neg (n : Fin 5 → ℝ) : side n + side (-n) = 1 := by
  simp only [side, γv_neg]
  module

theorem side_mul_side_neg (n : Fin 5 → ℝ) (hn : ∑ s, n s ^ 2 = 1) : side n * side (-n) = 0 := by
  have hX : γv n * γv n = 1 := by rw [γv_mul_self, hn]; simp
  simp only [side, γv_neg, Matrix.smul_mul, Matrix.mul_smul, add_mul, mul_add,
    Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg, hX]
  module

/-- **Each side has two dimensions:** `tr Q_n = 2`. -/
theorem trace_side (n : Fin 5 → ℝ) : (side n).trace = 2 := by
  simp only [side, γv, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one, Matrix.trace_sum,
    γ_trace, smul_eq_mul]
  simp
  norm_num

/-- **The overlap of two sides:** `Q_n Q_m Q_n = ((1 + n·m) / 2) Q_n` for unit `n`. -/
theorem overlap (n m : Fin 5 → ℝ) (hn : ∑ s, n s ^ 2 = 1) :
    side n * side m * side n = (((1 + ∑ s, n s * m s) / 2 : ℝ) : ℂ) • side n := by
  set X := γv n with hXdef
  set Y := γv m with hYdef
  set c : ℝ := ∑ s, n s * m s with hc
  have hXX : X * X = 1 := by rw [hXdef, γv_mul_self, hn]; simp
  have hXY : X * Y + Y * X = ((2 * c : ℝ) : ℂ) • (1 : Matrix Four Four ℂ) := anticomm_γv n m
  have hYX : Y * X = ((2 * c : ℝ) : ℂ) • (1 : Matrix Four Four ℂ) - X * Y := by
    rw [← hXY]
    abel
  have hXYX : X * Y * X = ((2 * c : ℝ) : ℂ) • X - Y := by
    rw [Matrix.mul_assoc, hYX, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, ← Matrix.mul_assoc,
      hXX, Matrix.one_mul]
  have key : (1 + X) * (1 + Y) * (1 + X) = ((2 + 2 * c : ℝ) : ℂ) • (1 + X) := by
    calc (1 + X) * (1 + Y) * (1 + X) = 1 + X + X + X * X + Y + Y * X + X * Y + X * Y * X := by
          noncomm_ring
      _ = 1 + X + X + 1 + Y + (((2 * c : ℝ) : ℂ) • (1 : Matrix Four Four ℂ) - X * Y) + X * Y +
          (((2 * c : ℝ) : ℂ) • X - Y) := by rw [hXX, hYX, hXYX]
      _ = ((2 + 2 * c : ℝ) : ℂ) • (1 + X) := by
          push_cast
          module
  have h8 : side n * side m * side n = (1 / 8 : ℂ) • ((1 + X) * (1 + Y) * (1 + X)) := by
    simp only [side, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    norm_num
    rfl
  rw [h8, key, smul_smul, side, smul_smul]
  congr 1
  push_cast
  ring

/-- The overlap is the same number with the two lines exchanged. -/
theorem overlap_symm (n m : Fin 5 → ℝ) :
    ∑ s, n s * m s = ∑ s, m s * n s :=
  Finset.sum_congr rfl fun _ _ => mul_comm _ _

end Comparison

end
