import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.NoncommRing
import Mathlib.Data.Complex.Basic

/-!
# The curvature split by a division, and the second order of a closed walk
(Propositions 40 and 38)

* `kept_mul_kept`, `kept_mul_moved`, `moved_mul_kept`, `moved_mul_moved`: under a division `θ` (`θ² = 1`) the kept
  operators commute with `θ` and the moved ones anticommute; kept·kept and moved·moved are kept, kept·moved and
  moved·kept are moved.
* `curvature_split` (**Proposition 40**): for a connection `A_μ = A_k,μ + A_m,μ` split into kept and moved parts,
  with `dA` split alike, **`F = dA + [A, A]` splits as `F_k = dA_k + [A_k, A_k] + [A_m, A_m]` (kept) and
  `F_m = dA_m + [A_k, A_m] + [A_m, A_k] = D_{A_k}A_m` (moved)**: `F_k = F(A_k) + (A_m ∧ A_m)_k`, `F_m = D_{A_k}A_m`.
* `bch_second_order` (**Proposition 38**, the second order of `log hol`): for the four rotations of a square,
  the second-order part of `e^{a₄}e^{a₃}e^{a₂}e^{a₁}` is `½(Σ aᵢ)² + ½ Σ_{i>j}[aᵢ, aⱼ]`, so
  **`log hol = Σ aᵢ + ½ Σ_{i>j} [aᵢ, aⱼ]`** through the second order (`log_hol_second_order`, the first and second
  coefficients of `log(1 + X)` with `X = tS + t²Y`).
-/

namespace Comparison.Article

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## Proposition 40: kept and moved, and the curvature split -/

/-- Kept by the division `θ`: commutes with it. -/
def IsKept (θ X : Matrix n n ℂ) : Prop := X * θ = θ * X

/-- Moved by the division `θ`: anticommutes with it. -/
def IsMoved (θ X : Matrix n n ℂ) : Prop := X * θ = -(θ * X)

theorem kept_mul_kept {θ X Y : Matrix n n ℂ} (hX : IsKept θ X) (hY : IsKept θ Y) : IsKept θ (X * Y) := by
  unfold IsKept at *
  rw [Matrix.mul_assoc, hY, ← Matrix.mul_assoc, hX, Matrix.mul_assoc]

theorem kept_mul_moved {θ X Y : Matrix n n ℂ} (hX : IsKept θ X) (hY : IsMoved θ Y) : IsMoved θ (X * Y) := by
  unfold IsKept IsMoved at *
  rw [Matrix.mul_assoc, hY, Matrix.mul_neg, ← Matrix.mul_assoc, hX, Matrix.mul_assoc]

theorem moved_mul_kept {θ X Y : Matrix n n ℂ} (hX : IsMoved θ X) (hY : IsKept θ Y) : IsMoved θ (X * Y) := by
  unfold IsKept IsMoved at *
  rw [Matrix.mul_assoc, hY, ← Matrix.mul_assoc, hX, Matrix.neg_mul, Matrix.mul_assoc]

theorem moved_mul_moved {θ X Y : Matrix n n ℂ} (hX : IsMoved θ X) (hY : IsMoved θ Y) : IsKept θ (X * Y) := by
  unfold IsKept IsMoved at *
  rw [Matrix.mul_assoc, hY, Matrix.mul_neg, ← Matrix.mul_assoc, hX, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]

theorem kept_add {θ X Y : Matrix n n ℂ} (hX : IsKept θ X) (hY : IsKept θ Y) : IsKept θ (X + Y) := by
  unfold IsKept at *
  rw [Matrix.add_mul, Matrix.mul_add, hX, hY]

theorem moved_add {θ X Y : Matrix n n ℂ} (hX : IsMoved θ X) (hY : IsMoved θ Y) : IsMoved θ (X + Y) := by
  unfold IsMoved at *
  rw [Matrix.add_mul, Matrix.mul_add, hX, hY, neg_add]

theorem kept_sub {θ X Y : Matrix n n ℂ} (hX : IsKept θ X) (hY : IsKept θ Y) : IsKept θ (X - Y) := by
  unfold IsKept at *
  rw [Matrix.sub_mul, Matrix.mul_sub, hX, hY]

theorem moved_sub {θ X Y : Matrix n n ℂ} (hX : IsMoved θ X) (hY : IsMoved θ Y) : IsMoved θ (X - Y) := by
  unfold IsMoved at *
  rw [Matrix.sub_mul, Matrix.mul_sub, hX, hY]
  abel

/-- The commutator. -/
def brk (X Y : Matrix n n ℂ) : Matrix n n ℂ := X * Y - Y * X

/-- **Proposition 40: the curvature split.** With `A = A_k + A_m` and `dA = dA_k + dA_m` split by the division,
the curvature `F_{μν} = dA_{μν} + [A_μ, A_ν]` is `F_k + F_m` with `F_k = dA_k + [A_k, A_k] + [A_m, A_m]` kept and
`F_m = dA_m + [A_k, A_m] + [A_m, A_k]` moved. -/
theorem curvature_split {θ : Matrix n n ℂ} {d : ℕ} (Ak Am : Fin d → Matrix n n ℂ)
    (dAk dAm : Fin d → Fin d → Matrix n n ℂ) (hk : ∀ μ, IsKept θ (Ak μ)) (hm : ∀ μ, IsMoved θ (Am μ))
    (hdk : ∀ μ ν, IsKept θ (dAk μ ν)) (hdm : ∀ μ ν, IsMoved θ (dAm μ ν)) (μ ν : Fin d) :
    (dAk μ ν + dAm μ ν) + brk (Ak μ + Am μ) (Ak ν + Am ν) =
        (dAk μ ν + brk (Ak μ) (Ak ν) + brk (Am μ) (Am ν)) +
          (dAm μ ν + brk (Ak μ) (Am ν) + brk (Am μ) (Ak ν)) ∧
      IsKept θ (dAk μ ν + brk (Ak μ) (Ak ν) + brk (Am μ) (Am ν)) ∧
      IsMoved θ (dAm μ ν + brk (Ak μ) (Am ν) + brk (Am μ) (Ak ν)) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [brk]
    noncomm_ring
  · exact kept_add (kept_add (hdk μ ν) (kept_sub (kept_mul_kept (hk μ) (hk ν)) (kept_mul_kept (hk ν) (hk μ))))
      (kept_sub (moved_mul_moved (hm μ) (hm ν)) (moved_mul_moved (hm ν) (hm μ)))
  · exact moved_add (moved_add (hdm μ ν) (moved_sub (kept_mul_moved (hk μ) (hm ν)) (moved_mul_kept (hm ν) (hk μ))))
      (moved_sub (moved_mul_kept (hm μ) (hk ν)) (kept_mul_moved (hk ν) (hm μ)))

/-! ## Proposition 38: the second order of a closed walk -/

/-- **The second order of `e^{a₄}e^{a₃}e^{a₂}e^{a₁}`** (twice): `Σ aᵢ² + 2Σ_{i>j} aᵢaⱼ = (Σ aᵢ)² + Σ_{i>j} [aᵢ, aⱼ]`. -/
theorem bch_second_order (a₁ a₂ a₃ a₄ : Matrix n n ℂ) :
    (a₁ * a₁ + a₂ * a₂ + a₃ * a₃ + a₄ * a₄) +
        2 * (a₂ * a₁ + a₃ * a₁ + a₃ * a₂ + a₄ * a₁ + a₄ * a₂ + a₄ * a₃) =
      (a₁ + a₂ + a₃ + a₄) * (a₁ + a₂ + a₃ + a₄) +
        (brk a₂ a₁ + brk a₃ a₁ + brk a₃ a₂ + brk a₄ a₁ + brk a₄ a₂ + brk a₄ a₃) := by
  simp only [brk]
  noncomm_ring

/-- **`log hol` through the second order.** If `hol = 1 + tS + t²Y + …` with `2Y = S² + C`, then
`log hol = (hol − 1) − (hol − 1)²/2 + …` has first coefficient `S` and second coefficient `Y − S²/2 = C/2`:
`log hol = Σ aᵢ + ½ Σ_{i>j} [aᵢ, aⱼ] + O(a³)`. -/
theorem log_hol_second_order (S Y C : Matrix n n ℂ) (hY : (2 : ℂ) • Y = S * S + C) :
    Y - (1 / 2 : ℂ) • (S * S) = (1 / 2 : ℂ) • C := by
  have : Y = (1 / 2 : ℂ) • (S * S + C) := by
    rw [← hY, smul_smul]
    norm_num
  rw [this, smul_add]
  abel

end Comparison.Article
