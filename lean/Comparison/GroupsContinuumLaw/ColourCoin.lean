import Comparison.Existence.Coin

/-!
# The odd coin, `T = I₈/24`, the doubled determinant `1/72` and the singlet `1/(3√8)`

At an odd line `t` the divided set's metric `G = diag(−1, 1, 1, 1, 1)`
(the line `0` negative) has `L = 𝟏ᵀG𝟏 = 3` and the transfer coin `C = (2/L) 𝟏𝟏ᵀG − I`.

* `transfer_involution`, `transfer_signed_flux`, `transfer_column_norm`: `C² = I`, `CᵀGC = G`, a
  positive column has norm `17/9`; `transfer_echo`: the reflection on a positive line is `−1/3`.
* `crossed_transfer`, `crossed_echo`: **crossing the negative channel turns the transfer coin into the
  native coin**, `(2/5)𝟏𝟏ᵀ − I`, with the reflection `−3/5`; `cross_solves_boundary`: the crossing formula
  solves the exchanged boundary problem for every matrix with `M₀₀ ≠ 0`.
* `colour_transfer`: on the eight adjoint channels, `K = C ⊗ I₈`, `X = e_j ⊗ I₈/√8`, `Y = −X`:
  **`T = Yᵀ K⁻¹ X = I₈/24`**; `doubled_coefficient`: the doubled completion's mixed coefficient
  `tr(K⁻ᵀYYᵀK⁻¹XXᵀ) = ‖T‖² = 8/24² = 1/72` (`Existence/Born.lean: born_mixed` identifies this trace
  as `∂_s∂_t[−log det 𝔻]`); `singlet_amplitude`: **`⟨Ω₈, vec T⟩ = 1/(3√8)`**, its square `1/72`,
  `‖Ω₈‖ = 1`; `scattering_transfer`: the native coin gives `3I₈/40` and `9/200` instead.
-/

namespace Comparison.GroupsContinuumLaw

open Matrix Kronecker

/-- The metric of the odd divided set: the line `0` negative. -/
def gOdd : Matrix (Fin 5) (Fin 5) ℚ := Matrix.diagonal ![-1, 1, 1, 1, 1]

/-- The all-ones matrix. -/
def j5 : Matrix (Fin 5) (Fin 5) ℚ := Matrix.of fun _ _ => 1

/-- **The transfer coin** `C = (2/3)𝟏𝟏ᵀG − I` (`L = 3`). -/
def transfer : Matrix (Fin 5) (Fin 5) ℚ := (2 / 3 : ℚ) • (j5 * gOdd) - 1

theorem transfer_apply (i j : Fin 5) :
    transfer i j = (2 / 3) * (if j = 0 then -1 else 1) - (if i = j then 1 else 0) := by
  fin_cases i <;> fin_cases j <;>
    simp [transfer, j5, gOdd, Matrix.mul_apply, Fin.sum_univ_five, Matrix.one_apply] <;> norm_num

theorem transfer_involution : transfer * transfer = 1 := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_five]
  simp only [transfer_apply]
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply] <;> norm_num

theorem transfer_signed_flux : transferᵀ * gOdd * transfer = gOdd := by
  ext i j
  rw [Matrix.mul_apply, Fin.sum_univ_five]
  simp only [Matrix.mul_apply, Fin.sum_univ_five, Matrix.transpose_apply, transfer_apply, gOdd,
    Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;> simp <;> norm_num

theorem transfer_column_norm : ∑ i, transfer i 1 * transfer i 1 = 17 / 9 := by
  rw [Fin.sum_univ_five]
  simp only [transfer_apply]
  norm_num

/-- The reflection of the transfer coin on a positive line: `−1/3`. -/
theorem transfer_echo : transfer 1 1 = -1 / 3 := by
  rw [transfer_apply]
  norm_num

/-- **The crossing of the negative channel:** solve the transfer for the exchanged boundary data. -/
def cross (M : Matrix (Fin 5) (Fin 5) ℚ) : Matrix (Fin 5) (Fin 5) ℚ := fun i j =>
  if i = 0 then (if j = 0 then (M 0 0)⁻¹ else -M 0 j / M 0 0)
  else (if j = 0 then M i 0 / M 0 0 else M i j - M i 0 * M 0 j / M 0 0)

/-- **Crossing turns the transfer coin into the native coin** `(2/5)𝟏𝟏ᵀ − I`. -/
theorem crossed_transfer : cross transfer = coin := by
  ext i j
  rw [coin_apply]
  simp only [cross, transfer_apply]
  fin_cases i <;> fin_cases j <;> simp <;> norm_num

theorem crossed_echo : cross transfer 1 1 = -3 / 5 := by
  rw [crossed_transfer, coin_apply]
  norm_num

/-- The exchanged boundary data. -/
def exchangeIn (x y : Fin 5 → ℚ) : Fin 5 → ℚ := fun i => if i = 0 then y 0 else x i
def exchangeOut (x y : Fin 5 → ℚ) : Fin 5 → ℚ := fun i => if i = 0 then x 0 else y i

/-- **The crossing solves the exchanged boundary problem:** if `Mx = y`, then
`cross(M) (y₀, x₁, …, x₄) = (x₀, y₁, …, y₄)`. -/
theorem cross_solves_boundary (M : Matrix (Fin 5) (Fin 5) ℚ) (x y : Fin 5 → ℚ) (h00 : M 0 0 ≠ 0)
    (h : M *ᵥ x = y) : cross M *ᵥ exchangeIn x y = exchangeOut x y := by
  have hy : ∀ i, y i = M i 0 * x 0 + M i 1 * x 1 + M i 2 * x 2 + M i 3 * x 3 + M i 4 * x 4 := by
    intro i
    rw [← h, Matrix.mulVec, dotProduct, Fin.sum_univ_five]
  funext i
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_five, cross, exchangeIn, exchangeOut]
  fin_cases i <;> simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one, Fin.reduceFinMk, ↓reduceIte,
    Fin.reduceEq] <;> simp only [hy] <;> field_simp <;> ring

/-! ## The eight adjoint channels -/

/-- The transfer coin over `ℝ`. -/
noncomputable def transferR : Matrix (Fin 5) (Fin 5) ℝ := (Rat.castHom ℝ).mapMatrix transfer

/-- The positive line `j = 1` as a column. -/
def lineCol : Matrix (Fin 5) Unit ℝ := fun a _ => if a = 1 then 1 else 0

/-- The local operator on the eight channels: `K = C ⊗ I₈`. -/
noncomputable def kLoc : Matrix (Fin 5 × Fin 8) (Fin 5 × Fin 8) ℝ := transferR ⊗ₖ 1

/-- The preparation `X = e_j ⊗ I₈/√8` (unit Hilbert–Schmidt norm) and the detection `Y = −X`. -/
noncomputable def prepX : Matrix (Fin 5 × Fin 8) (Unit × Fin 8) ℝ :=
  lineCol ⊗ₖ ((Real.sqrt 8)⁻¹ • (1 : Matrix (Fin 8) (Fin 8) ℝ))

noncomputable def detY : Matrix (Fin 5 × Fin 8) (Unit × Fin 8) ℝ := -prepX

theorem transferR_sq : transferR * transferR = 1 := by
  rw [transferR, ← map_mul, transfer_involution, map_one]

/-- The local operator is its own inverse: `K² = 1`. -/
theorem kLoc_sq : kLoc * kLoc = 1 := by
  rw [kLoc, ← Matrix.mul_kronecker_mul, transferR_sq, Matrix.one_mul, Matrix.one_kronecker_one]

theorem lineCol_sandwich : lineColᵀ * transferR * lineCol = Matrix.of fun _ _ => (-1 / 3 : ℝ) := by
  ext i j
  simp only [lineCol, Matrix.mul_apply, Matrix.transpose_apply, transferR, RingHom.mapMatrix_apply,
    Matrix.map_apply, Rat.coe_castHom, Fin.sum_univ_five, Matrix.of_apply]
  simp only [Fin.isValue, Fin.reduceEq, ↓reduceIte, zero_mul, mul_zero, add_zero, zero_add, one_mul,
    mul_one, transfer_echo]
  push_cast
  ring

theorem sqrt8_sq : (Real.sqrt 8)⁻¹ * (Real.sqrt 8)⁻¹ = 1 / 8 := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- **The colour transfer:** `T = Yᵀ K⁻¹ X = I₈/24` (with `K⁻¹ = K`). -/
theorem colour_transfer : detYᵀ * kLoc * prepX = (1 / 24 : ℝ) • (1 : Matrix (Unit × Fin 8) (Unit × Fin 8) ℝ) := by
  rw [detY, Matrix.transpose_neg, prepX, kLoc, ← Matrix.kroneckerMap_transpose, Matrix.neg_mul,
    Matrix.neg_mul,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, lineCol_sandwich]
  rw [Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_one, Matrix.smul_mul, Matrix.one_mul,
    smul_smul, sqrt8_sq]
  ext ⟨u, a⟩ ⟨v, b⟩
  simp only [Matrix.neg_apply, Matrix.kroneckerMap_apply, Matrix.of_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, Prod.mk.injEq]
  have : u = v := Subsingleton.elim u v
  subst this
  by_cases hab : a = b <;> simp [hab] <;> ring

/-- **The doubled determinant's mixed coefficient:** `tr(Kᵀ YYᵀ K XXᵀ) = ‖T‖²_HS = 8/24² = 1/72`. -/
theorem doubled_coefficient :
    (kLocᵀ * (detY * detYᵀ) * kLoc * (prepX * prepXᵀ)).trace = 1 / 72 := by
  have e : (kLocᵀ * (detY * detYᵀ) * kLoc * (prepX * prepXᵀ)).trace =
      ((detYᵀ * kLoc * prepX)ᵀ * (detYᵀ * kLoc * prepX)).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [e, colour_transfer, Matrix.transpose_smul, Matrix.transpose_one, smul_mul_smul_comm,
    Matrix.one_mul, Matrix.trace_smul, Matrix.trace_one]
  simp [Fintype.card_prod]
  norm_num

/-- The adjoint singlet `Ω₈ = vec(I₈)/√8`. -/
noncomputable def adjointSinglet : Matrix (Unit × Fin 8) (Unit × Fin 8) ℝ :=
  (Real.sqrt 8)⁻¹ • (1 : Matrix (Unit × Fin 8) (Unit × Fin 8) ℝ)

theorem sum_diag_one (f : Unit × Fin 8 → Unit × Fin 8 → ℝ) (c : ℝ) (hf : ∀ i j, f i j = if i = j then c else 0) :
    ∑ i, ∑ j, f i j = 8 * c := by
  simp only [hf, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_prod, Fintype.card_unit, Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-- **The singlet amplitude:** `⟨Ω₈, vec T⟩ = 1/(3√8)`, its square `1/72`, and `‖Ω₈‖ = 1`. -/
theorem singlet_amplitude :
    ∑ i, ∑ j, adjointSinglet i j * (detYᵀ * kLoc * prepX) i j = 1 / (3 * Real.sqrt 8) ∧
      (∑ i, ∑ j, adjointSinglet i j * (detYᵀ * kLoc * prepX) i j) ^ 2 = 1 / 72 ∧
      ∑ i, ∑ j, adjointSinglet i j ^ 2 = 1 := by
  have h8 : Real.sqrt 8 ^ 2 = 8 := Real.sq_sqrt (by norm_num)
  have h8p : 0 < Real.sqrt 8 := by positivity
  have hamp : ∑ i, ∑ j, adjointSinglet i j * (detYᵀ * kLoc * prepX) i j = 1 / (3 * Real.sqrt 8) := by
    rw [colour_transfer]
    rw [sum_diag_one _ ((Real.sqrt 8)⁻¹ * (1 / 24)) (fun i j => by
      simp only [adjointSinglet, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> ring)]
    field_simp
    ring
  refine ⟨hamp, ?_, ?_⟩
  · rw [hamp, div_pow, mul_pow, h8]
    norm_num
  · rw [sum_diag_one _ ((Real.sqrt 8)⁻¹ ^ 2) (fun i j => by
      simp only [adjointSinglet, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split_ifs <;> ring)]
    rw [inv_pow, h8]
    norm_num

/-- **The native coin's reflection gives the scattering amplitude** `3I₈/40`, with `‖·‖² = 9/200`:
crossing changes the reflection. -/
theorem scattering_transfer :
    -(1 / 8 : ℚ) * coin 1 1 = 3 / 40 ∧ (8 : ℚ) * (3 / 40) ^ 2 = 9 / 200 ∧
      -(1 / 8 : ℚ) * transfer 1 1 = 1 / 24 ∧ (8 : ℚ) * (1 / 24) ^ 2 = 1 / 72 := by
  rw [coin_apply, transfer_echo]
  norm_num

end Comparison.GroupsContinuumLaw
