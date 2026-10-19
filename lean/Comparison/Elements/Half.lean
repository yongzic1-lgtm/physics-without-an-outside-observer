module

public import Mathlib

/-!
# Book IV, Proposition 19: the square root of the sign

In a basis of P1's real six, a division is a set `D` of divided directions. Its sign `θ_D`
(`signD`) is `−1` on `D` and `+1` off `D`; its half `q_D` (`half`) is `i` on `D` and `1` off `D`.

* `half_mul_self`: `q_D² = θ_D`; `half_transpose_mul`: `q_Dᵀ q_D = θ_D`;
  `half_conjTranspose_mul`: `q_D† q_D = 1`; `half_pow_four`: `q_D⁴ = 1`;
  `half_mul_half_compl`: `q_D q_{D′} = i`.
* `halves_iff`, `halves_solutions`: for every division but the point (and its complement),
  `(α + β θ_D)² = θ_D` exactly for `(α, β) = ±((1+i)/2, (1−i)/2)` and `±((1−i)/2, (1+i)/2)`,
  that is `±q_D` and `±q̄_D` (`half_eq`); `no_real_half`: no real `α, β` do it.
* `metric`: `g_D(v) = p(q_D v) = Σ_{D′} z² − Σ_D z²`.
* `half_on_sets`: the square root of the sign multiplies the set `S` of the sixty-four by `i^{|S ∩ D|}`;
  `sets_count`: `i^{|S|}` is `1, i, −1, −i` on `16, 12, 16, 20` of the sixty-four sets.
-/

@[expose] public section

namespace Comparison

open Matrix
open Complex

/-- The sign of a division of the six: `−1` on the divided directions, `+1` on the others. -/
def signD (D : Finset (Fin 6)) : Matrix (Fin 6) (Fin 6) ℂ :=
  Matrix.diagonal fun c => if c ∈ D then -1 else 1

/-- The half of a division: `i` on the divided directions, `1` on the others. -/
def half (D : Finset (Fin 6)) : Matrix (Fin 6) (Fin 6) ℂ :=
  Matrix.diagonal fun c => if c ∈ D then I else 1

/-- **`q_D² = θ_D`.** -/
theorem half_mul_self (D : Finset (Fin 6)) : half D * half D = signD D := by
  rw [half, signD, Matrix.diagonal_mul_diagonal]
  congr 1
  funext c
  split_ifs <;> simp

/-- **`q_Dᵀ q_D = θ_D`:** the square root of the sign squares to the sign also with the transpose. -/
theorem half_transpose_mul (D : Finset (Fin 6)) : (half D)ᵀ * half D = signD D := by
  rw [half, Matrix.diagonal_transpose, ← half, half_mul_self]

/-- **`q_D† q_D = 1`:** the square root of the sign keeps lengths. -/
theorem half_conjTranspose_mul (D : Finset (Fin 6)) : (half D)ᴴ * half D = 1 := by
  rw [half, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext c
  by_cases h : c ∈ D <;> simp [h]

theorem signD_mul_self (D : Finset (Fin 6)) : signD D * signD D = 1 := by
  rw [signD, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext c
  split_ifs <;> simp

/-- **`q_D⁴ = 1`.** -/
theorem half_pow_four (D : Finset (Fin 6)) : half D ^ 4 = 1 := by
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, half_mul_self, signD_mul_self]

/-- **The square roots of the two parts make the quarter turn:** `q_D q_{D′} = i`. -/
theorem half_mul_half_compl (D : Finset (Fin 6)) :
    half D * half Dᶜ = I • (1 : Matrix (Fin 6) (Fin 6) ℂ) := by
  rw [half, half, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one, ← Matrix.diagonal_smul]
  congr 1
  funext c
  by_cases h : c ∈ D <;> simp [h]

theorem combo_eq (D : Finset (Fin 6)) (α β : ℂ) :
    α • (1 : Matrix (Fin 6) (Fin 6) ℂ) + β • signD D =
      Matrix.diagonal fun c => if c ∈ D then α - β else α + β := by
  rw [signD, ← Matrix.diagonal_one, ← Matrix.diagonal_smul, ← Matrix.diagonal_smul,
    Matrix.diagonal_add]
  congr 1
  funext c
  by_cases h : c ∈ D <;> simp [h, sub_eq_add_neg]

/-- **The square roots made from the sign alone:** for a division that divides something and not
everything, `(α + β θ_D)² = θ_D` exactly when `α² + β² = 0` and `2αβ = 1`. -/
theorem halves_iff (D : Finset (Fin 6)) (hD : D.Nonempty) (hD' : Dᶜ.Nonempty) (α β : ℂ) :
    (α • (1 : Matrix (Fin 6) (Fin 6) ℂ) + β • signD D) *
        (α • (1 : Matrix (Fin 6) (Fin 6) ℂ) + β • signD D) = signD D ↔
      α ^ 2 + β ^ 2 = 0 ∧ 2 * α * β = 1 := by
  rw [combo_eq, Matrix.diagonal_mul_diagonal, signD]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := hD
    obtain ⟨c', hc'⟩ := hD'
    rw [Finset.mem_compl] at hc'
    have h1 := congrFun (Matrix.diagonal_injective h) c
    have h2 := congrFun (Matrix.diagonal_injective h) c'
    simp only [hc, hc', ite_true, ite_false] at h1 h2
    constructor
    · linear_combination h1 / 2 + h2 / 2
    · linear_combination h2 / 2 - h1 / 2
  · rintro ⟨h1, h2⟩
    congr 1
    funext c
    split_ifs
    · linear_combination h1 - h2
    · linear_combination h1 + h2

/-- **There are exactly four square roots:** `±((1+i)/2, (1−i)/2)` and `±((1−i)/2, (1+i)/2)`. -/
theorem halves_solutions (α β : ℂ) :
    (α ^ 2 + β ^ 2 = 0 ∧ 2 * α * β = 1) ↔
      (α = (1 + I) / 2 ∧ β = (1 - I) / 2) ∨ (α = -((1 + I) / 2) ∧ β = -((1 - I) / 2)) ∨
      (α = (1 - I) / 2 ∧ β = (1 + I) / 2) ∨ (α = -((1 - I) / 2) ∧ β = -((1 + I) / 2)) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hs : (α + β - 1) * (α + β + 1) = 0 := by linear_combination h1 + h2
    have hd : (α - β - I) * (α - β + I) = 0 := by
      linear_combination h1 - h2 - Complex.I_sq
    rcases mul_eq_zero.mp hs with hs | hs <;> rcases mul_eq_zero.mp hd with hd | hd
    · exact Or.inl ⟨by linear_combination hs / 2 + hd / 2, by linear_combination hs / 2 - hd / 2⟩
    · exact Or.inr (Or.inr (Or.inl
        ⟨by linear_combination hs / 2 + hd / 2, by linear_combination hs / 2 - hd / 2⟩))
    · exact Or.inr (Or.inr (Or.inr
        ⟨by linear_combination hs / 2 + hd / 2, by linear_combination hs / 2 - hd / 2⟩))
    · exact Or.inr (Or.inl
        ⟨by linear_combination hs / 2 + hd / 2, by linear_combination hs / 2 - hd / 2⟩)
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
      constructor <;> ring_nf <;> simp [Complex.I_sq] <;> ring_nf

/-- The half is made from the sign: `q_D = (1+i)/2 + ((1−i)/2) θ_D`. -/
theorem half_eq (D : Finset (Fin 6)) :
    half D = ((1 + I) / 2) • (1 : Matrix (Fin 6) (Fin 6) ℂ) + ((1 - I) / 2) • signD D := by
  rw [combo_eq, half]
  congr 1
  funext c
  split_ifs <;> ring

/-- **No real half:** no real `α, β` have `α² + β² = 0` and `2αβ = 1`. -/
theorem no_real_half (α β : ℝ) : ¬ (α ^ 2 + β ^ 2 = 0 ∧ 2 * α * β = 1) := by
  rintro ⟨h1, h2⟩
  have hα : α = 0 := by nlinarith [sq_nonneg α, sq_nonneg β]
  rw [hα] at h2
  norm_num at h2

/-- **The metric of a division:** `p(q_D z) = Σ_{D′} z² − Σ_D z²`, with `p = Σ z²` on P1's real
six (the bilinear form, no conjugation). -/
theorem metric (D : Finset (Fin 6)) (z : Fin 6 → ℂ) :
    (half D *ᵥ z) ⬝ᵥ (half D *ᵥ z) = ∑ c, (if c ∈ D then -1 else 1) * z c ^ 2 := by
  simp only [half, Matrix.mulVec_diagonal, dotProduct]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs
  · rw [mul_mul_mul_comm, Complex.I_mul_I]
    ring
  · ring

/-- **The half on the sixty-four sets:** the set `S` is multiplied by `i^{|S ∩ D|}`. -/
theorem half_on_sets (D S : Finset (Fin 6)) :
    ∏ c ∈ S, (if c ∈ D then I else 1) = I ^ (S ∩ D).card := by
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one,
    Finset.filter_mem_eq_inter]

/-- **`i^{|S|}` is `1, i, −1, −i` on `16, 12, 16, 20` of the sixty-four sets.** -/
theorem sets_count :
    (Finset.univ.filter fun S : Finset (Fin 6) => S.card % 4 = 0).card = 16 ∧
    (Finset.univ.filter fun S : Finset (Fin 6) => S.card % 4 = 1).card = 12 ∧
    (Finset.univ.filter fun S : Finset (Fin 6) => S.card % 4 = 2).card = 16 ∧
    (Finset.univ.filter fun S : Finset (Fin 6) => S.card % 4 = 3).card = 20 := by
  decide +kernel

end Comparison

end
