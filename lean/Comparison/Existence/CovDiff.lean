module

public import Comparison.Existence.Gauge

/-!
# Book VII. The covariant difference of a division and of its half (Proposition 39)

On the real `n × n` matrices
(`n = 6`: P1's real six), with `projD D`, `massForm D` of `Gauge.lean`.

* `covDiff U Px Py = U P(y) U⁻¹ − P(x)` (`U⁻¹ = Uᵀ`): the division held at `y` carried to `x`, less
  the division held at `x`.
* `covDiff_rename`: **`DP ↦ g_x DP g_x⁻¹`** when `U ↦ g_x U g_y⁻¹` and `P(·) ↦ g P(·) g⁻¹`.
* `covDiff_near_one`: with `U = 1 + A`, `A` antisymmetric,
  **`DP = (P(y) − P(x)) + [A, P(y)] − A P(y) A`**: near one, `DP = dP + [A, P] + O(A²)`.
* `covDiff_turn`: along a rotation `X` with `P(x) = P(y) = P`, `DP = [X, P] − XPX`.
* `qHalf P = 1 + (i − 1)P`, `covDiffC`; `covDiff_half`: **`Dq_D = (i − 1) DP_D`**.
* `frobSq`: `‖M‖² = Σ |M_ij|²`; `frobSq_half`: **`‖(i − 1)M‖² = 2‖M‖²`**; `half_mass`: along a
  rotation `X`, `‖(i − 1)[X, P_D]‖² = 2 M_D(X, X)`.
-/

@[expose] public section

namespace Comparison

open Matrix
open scoped Matrix

section CovDiff

variable {n : ℕ}

/-- **The covariant difference** `DP = U P(y) U⁻¹ − P(x)` with `U⁻¹ = Uᵀ`. -/
def covDiff (U Px Py : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  U * Py * Uᵀ - Px

/-- **A gauge transformation turns the covariant difference at its own vertex:** with
`U ↦ g_x U g_y⁻¹`, `P(x) ↦ g_x P(x) g_x⁻¹` and `P(y) ↦ g_y P(y) g_y⁻¹`, `DP ↦ g_x DP g_x⁻¹`. -/
theorem covDiff_rename (U Px Py gx gy : Matrix (Fin n) (Fin n) ℝ) (hgy : gyᵀ * gy = 1) :
    covDiff (gx * U * gyᵀ) (gx * Px * gxᵀ) (gy * Py * gyᵀ) = gx * covDiff U Px Py * gxᵀ := by
  have key : ∀ Z : Matrix (Fin n) (Fin n) ℝ, gyᵀ * (gy * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, hgy, Matrix.one_mul]
  simp only [covDiff, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
    Matrix.mul_sub, Matrix.sub_mul, key]

/-- **Near one:** with `U = 1 + A`, `A` antisymmetric,
`DP = (P(y) − P(x)) + [A, P(y)] − A P(y) A`. -/
theorem covDiff_near_one (A Px Py : Matrix (Fin n) (Fin n) ℝ) (hA : Aᵀ = -A) :
    covDiff (1 + A) Px Py = (Py - Px) + (A * Py - Py * A) - A * Py * A := by
  simp only [covDiff, Matrix.transpose_add, Matrix.transpose_one, hA]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_neg,
    Matrix.neg_mul]
  abel

/-- **Along a rotation:** with `P(x) = P(y) = P`, `DP = [X, P] − XPX`. -/
theorem covDiff_turn (X P : Matrix (Fin n) (Fin n) ℝ) (hX : Xᵀ = -X) :
    covDiff (1 + X) P P = (X * P - P * X) - X * P * X := by
  rw [covDiff_near_one X P P hX, sub_self, zero_add]

/-- A real matrix read as a complex one. -/
noncomputable def toC : Matrix (Fin n) (Fin n) ℝ →+* Matrix (Fin n) (Fin n) ℂ :=
  Complex.ofRealHom.mapMatrix

theorem toC_apply (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : toC M i j = (M i j : ℂ) := rfl

/-- The half of a division: `q_D = 1 + (i − 1) P_D`. -/
noncomputable def qHalf (P : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  1 + (Complex.I - 1) • toC P

/-- The covariant difference of complex matrices carried by a real `U`. -/
noncomputable def covDiffC (U : Matrix (Fin n) (Fin n) ℝ) (Qx Qy : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  toC U * Qy * toC Uᵀ - Qx

/-- **`Dq_D = (i − 1) DP_D`** for orthogonal `U`. -/
theorem covDiff_half (U Px Py : Matrix (Fin n) (Fin n) ℝ) (hU : U * Uᵀ = 1) :
    covDiffC U (qHalf Px) (qHalf Py) = (Complex.I - 1) • toC (covDiff U Px Py) := by
  have hUc : toC U * toC Uᵀ = 1 := by rw [← map_mul, hU, map_one]
  have hmap : toC (covDiff U Px Py) = toC U * toC Py * toC Uᵀ - toC Px := by
    rw [covDiff, map_sub, map_mul, map_mul]
  rw [hmap, covDiffC, qHalf, qHalf]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, hUc,
    smul_sub]
  abel

/-- `‖M‖² = Σ_ij |M_ij|²`. -/
noncomputable def frobSq (M : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (M i j)

/-- **`‖(i − 1)M‖² = 2‖M‖²`** for a real `M`. -/
theorem frobSq_half (M : Matrix (Fin n) (Fin n) ℝ) :
    frobSq ((Complex.I - 1) • toC M) = 2 * ∑ i, ∑ j, M i j ^ 2 := by
  have h : Complex.normSq (Complex.I - 1) = 2 := by
    rw [Complex.normSq_apply]
    simp
    norm_num
  simp only [frobSq, Matrix.smul_apply, toC_apply, smul_eq_mul, map_mul, h,
    Complex.normSq_ofReal, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- **Along a rotation the change of the square root of the sign is twice the mass form:**
`‖(i − 1)[X, P_D]‖² = 2‖[X, P_D]‖² = 2 M_D(X, X)`. -/
theorem half_mass (D : Finset (Fin n)) (X : Matrix (Fin n) (Fin n) ℝ) :
    frobSq ((Complex.I - 1) • toC (X * projD D - projD D * X)) = 2 * massForm D X X := by
  rw [frobSq_half, massForm_self_eq]

end CovDiff

end Comparison

end
