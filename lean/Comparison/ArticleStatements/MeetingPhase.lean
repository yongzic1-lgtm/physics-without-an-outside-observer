import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# The phase of a composition (statement 22)

Statement 22: `q_bc = conj(q_ab) q_ac`, `q_ab q_bc conj(q_ac) = 1`, `G_q = D_q† G₊ D_q`,
`spec G₊ = {1 − √c}^(m−1) ∪ {1 + (m − 1)√c}`, `c = 8/15`. With `s = √c` the coherent meeting matrix of
`m` lines is `G₊ = 1` on the diagonal and `s` off it.

* `det_scalar_add_ones`: `det(a·1 + b·𝟏𝟏ᵀ) = a^(m−1)(a + mb)` for `m ≥ 1` (the matrix determinant lemma).
* `Gplus_eq`, `Gplus_mulVec_ones`, `Gplus_mulVec_sum_zero`: `G₊ = (1 − s)·1 + s·𝟏𝟏ᵀ`; **`G₊𝟏 = (1 + (m−1)s)𝟏`**
  and **`G₊v = (1 − s)v` whenever `Σ v = 0`**.
* `charpoly_Gplus`: **`det(x − G₊) = (x − (1 − s))^(m−1) (x − (1 + (m−1)s))`**, so the spectrum is
  `1 − s` with multiplicity `m − 1` and `1 + (m − 1)s` once; `det_Gplus`.
* `gauge_flat`: phases `q_ab = conj(q_a) q_b` from unit numbers at the lines satisfy
  **`q_bc = conj(q_ab) q_ac`** and **`q_ab q_bc conj(q_ac) = 1`** (a flat triangle; conversely a flat set of
  pair phases is of this form, ArticleStatements/CommonClock.lean `clock_of_loops_close`).
* `Gq_apply`, `charpoly_Gq`: **`G_q = D_q† G₊ D_q`** has entries `1` and `q_ab s`, and the same
  characteristic polynomial: every vertex-phase choice is the same bound state in a changed frame.
-/

open Matrix

namespace Comparison.ArticleStatements.Phase

variable {m : ℕ}

/-- The all-ones matrix `𝟏𝟏ᵀ`. -/
def ones (m : ℕ) : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun _ _ => 1

/-- **The matrix determinant lemma for `a·1 + b·𝟏𝟏ᵀ`.** -/
theorem det_scalar_add_ones (hm : 1 ≤ m) (a b : ℂ) :
    (a • (1 : Matrix (Fin m) (Fin m) ℂ) + b • ones m).det = a ^ (m - 1) * (a + m * b) := by
  by_cases ha : a = 0
  · subst ha
    rcases Nat.lt_or_ge m 2 with h2 | h2
    · have hm1 : m = 1 := by omega
      subst hm1
      simp [ones, Matrix.det_unique]
    · have hrow : ((0 : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) + b • ones m) ⟨0, by omega⟩ =
          ((0 : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) + b • ones m) ⟨1, by omega⟩ := by
        ext j
        simp [ones]
      rw [Matrix.det_zero_of_row_eq (by simp [Fin.ext_iff]) hrow, zero_pow (by omega), zero_mul]
  · have e : a • (1 : Matrix (Fin m) (Fin m) ℂ) + b • ones m =
        a • (1 + replicateCol Unit (fun _ : Fin m => b / a) * replicateRow Unit (fun _ : Fin m => (1 : ℂ))) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, ones, Matrix.of_apply, smul_eq_mul,
        Matrix.mul_apply, replicateCol_apply, replicateRow_apply, Finset.univ_unique,
        Finset.sum_singleton]
      field_simp
    rw [e, Matrix.det_smul, det_one_add_replicateCol_mul_replicateRow, Fintype.card_fin]
    simp only [dotProduct, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    rw [pow_succ]
    field_simp
    push_cast
    ring

/-- **The coherent meeting matrix** of `m` lines: `1` on the diagonal and `s = √c` off it. -/
def Gplus (m : ℕ) (s : ℂ) : Matrix (Fin m) (Fin m) ℂ := Matrix.of fun i j => if i = j then 1 else s

theorem Gplus_eq (s : ℂ) : Gplus m s = (1 - s) • (1 : Matrix (Fin m) (Fin m) ℂ) + s • ones m := by
  ext i j
  by_cases h : i = j <;> simp [Gplus, ones, h]

/-- **`G₊𝟏 = (1 + (m − 1)s)𝟏`.** -/
theorem Gplus_mulVec_ones (s : ℂ) :
    Gplus m s *ᵥ (fun _ => 1) = fun _ => 1 + (m - 1) * s := by
  ext i
  rw [Gplus_eq, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, ones,
    Matrix.of_apply, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **`G₊v = (1 − s)v` whenever `Σ_i v_i = 0`.** -/
theorem Gplus_mulVec_sum_zero (s : ℂ) (v : Fin m → ℂ) (hv : ∑ i, v i = 0) :
    Gplus m s *ᵥ v = (1 - s) • v := by
  ext i
  rw [Gplus_eq, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, ones,
    Matrix.of_apply, one_mul, hv, mul_zero, add_zero]

/-- **The characteristic polynomial:** `det(x − G₊) = (x − (1 − s))^(m−1) (x − (1 + (m − 1)s))`. -/
theorem charpoly_Gplus (hm : 1 ≤ m) (s x : ℂ) :
    (x • (1 : Matrix (Fin m) (Fin m) ℂ) - Gplus m s).det =
      (x - (1 - s)) ^ (m - 1) * (x - (1 + (m - 1) * s)) := by
  have e : x • (1 : Matrix (Fin m) (Fin m) ℂ) - Gplus m s =
      (x - (1 - s)) • (1 : Matrix (Fin m) (Fin m) ℂ) + (-s) • ones m := by
    rw [Gplus_eq]
    module
  rw [e, det_scalar_add_ones hm]
  congr 1
  ring

/-- `det G₊ = (1 − s)^(m−1) (1 + (m − 1)s)`. -/
theorem det_Gplus (hm : 1 ≤ m) (s : ℂ) :
    (Gplus m s).det = (1 - s) ^ (m - 1) * (1 + (m - 1) * s) := by
  rw [Gplus_eq, det_scalar_add_ones hm]
  congr 1
  ring

/-- **A flat set of pair phases:** from unit numbers `q_a` at the lines, `q_ab = conj(q_a) q_b` gives
`q_bc = conj(q_ab) q_ac` and `q_ab q_bc conj(q_ac) = 1`. -/
theorem gauge_flat (q : Fin m → ℂ) (hq : ∀ a, star (q a) * q a = 1) (a b c : Fin m) :
    star (q b) * q c = star (star (q a) * q b) * (star (q a) * q c) ∧
      (star (q a) * q b) * (star (q b) * q c) * star (star (q a) * q c) = 1 := by
  have ha := hq a
  have hb := hq b
  have hc := hq c
  constructor
  · rw [star_mul', star_star]
    linear_combination (-(star (q b) * q c)) * ha
  · rw [star_mul', star_star]
    linear_combination (star (q b) * q b * (star (q c) * q c)) * ha + (star (q c) * q c) * hb + hc

/-- **`G_q = D_q† G₊ D_q`** has `1` on the diagonal and `q_ab s` off it. -/
theorem Gq_apply (q : Fin m → ℂ) (hq : ∀ a, star (q a) * q a = 1) (s : ℂ) (a b : Fin m) :
    (diagonal (fun i => star (q i)) * Gplus m s * diagonal q) a b =
      if a = b then 1 else star (q a) * q b * s := by
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Gplus, Matrix.of_apply]
  by_cases h : a = b
  · subst h
    rw [ite_eq_left rfl, ite_eq_left rfl, mul_one]
    exact hq a
  · rw [ite_eq_right h, ite_eq_right h]
    ring

/-- **Every vertex-phase choice is the same bound state in a changed frame:** `G_q` and `G₊` have the same
characteristic polynomial. -/
theorem charpoly_Gq (q : Fin m → ℂ) (hq : ∀ a, star (q a) * q a = 1) (s x : ℂ) :
    (x • (1 : Matrix (Fin m) (Fin m) ℂ) - diagonal (fun i => star (q i)) * Gplus m s * diagonal q).det =
      (x • (1 : Matrix (Fin m) (Fin m) ℂ) - Gplus m s).det := by
  have hD : diagonal (fun i => star (q i)) * diagonal q = (1 : Matrix (Fin m) (Fin m) ℂ) := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact hq i
  have e : x • (1 : Matrix (Fin m) (Fin m) ℂ) - diagonal (fun i => star (q i)) * Gplus m s * diagonal q =
      diagonal (fun i => star (q i)) * (x • (1 : Matrix (Fin m) (Fin m) ℂ) - Gplus m s) * diagonal q := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hD]
  rw [e, Matrix.det_mul, Matrix.det_mul]
  have h1 : (diagonal (fun i => star (q i))).det * (diagonal q).det = 1 := by
    rw [← Matrix.det_mul, hD, Matrix.det_one]
  linear_combination (x • (1 : Matrix (Fin m) (Fin m) ℂ) - Gplus m s).det * h1

end Comparison.ArticleStatements.Phase

#print axioms Comparison.ArticleStatements.Phase.det_scalar_add_ones
#print axioms Comparison.ArticleStatements.Phase.Gplus_eq
#print axioms Comparison.ArticleStatements.Phase.Gplus_mulVec_ones
#print axioms Comparison.ArticleStatements.Phase.Gplus_mulVec_sum_zero
#print axioms Comparison.ArticleStatements.Phase.charpoly_Gplus
#print axioms Comparison.ArticleStatements.Phase.det_Gplus
#print axioms Comparison.ArticleStatements.Phase.gauge_flat
#print axioms Comparison.ArticleStatements.Phase.Gq_apply
#print axioms Comparison.ArticleStatements.Phase.charpoly_Gq
