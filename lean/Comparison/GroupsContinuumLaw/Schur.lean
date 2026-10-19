import Comparison.Existence.IharaBass
import Comparison.Existence.Closing

/-!
# The resolved law's two eliminations (the continuum limit, part one)

The step `B` lifts to a two-sheet chart in which the five line transitions are involutions; first the last
line and then the second sheet are eliminated. The finite identities of those eliminations:

* `bass_resolvent`: for five involutions, `T = diag(Γ_t)` with `T² = 1`, the copy maps with `YX = 5`,
  the edge operator `K_e = I − uB`, `B = T(XY − I)`, and the vertex operator
  `K_v = (1 + 4u²)I − uYTX`: **`K_v⁻¹ = (I + uY K_e⁻¹ T X)/(1 − u²)`** (the resolvent, not only the
  determinant, of the Ihara–Bass reduction); `stepOp_bass_resolvent`: the same for `B = stepOp Γ`.
* `normalized_schur`: eliminating the second sheet of `K = [[aI, −uF], [−uG, aI]]`, `a = 1 + 4u²`,
  **`aI − (u²/a)FG = ρ Q`** with `ρ = 5u²ε²/a` and **`Q = M_ε(u)² + L_ε`**,
  `M_ε(u)² = ((u⁻¹ + 4u)² − 25)/(5ε²)`, `L_ε = (25I − FG)/(5ε²)`;
  `normalized_schur_inverse`: **`Q⁻¹ = ρ · (K⁻¹)₁₁`**.
* `kinetic_sum_of_squares`: for five unitaries `U_t` and `F = Σ U_t`,
  `25I − FF* = Σ_{s<t}(U_s − U_t)(U_s − U_t)*`: the kinetic part `L_ε` is positive and local.
* `affine_change`: changing `u` shifts `Q` by a multiple of the identity (the mass intercept).
-/

namespace Comparison.GroupsContinuumLaw

open Matrix

section Resolvent

variable {e v : Type*} [Fintype e] [Fintype v] [DecidableEq e] [DecidableEq v]

/-- **The Bass resolvent:** if `Ge` is a left inverse of `K_e = 1 − uT(XY − 1)` and `Gv` a left
inverse of `K_v = (1 + 4u²) − uYTX`, with `T² = 1`, `YX = 5` and `1 − u² ≠ 0`, then
`Gv = (1 − u²)⁻¹ (1 + u Y Ge T X)`. -/
theorem bass_resolvent (u : ℂ) (T : Matrix e e ℂ) (X : Matrix e v ℂ) (Y : Matrix v e ℂ)
    (Ge : Matrix e e ℂ) (Gv : Matrix v v ℂ) (hT : T * T = 1) (hYX : Y * X = (5 : ℂ) • 1)
    (hev : Ge * (1 - u • (T * (X * Y - 1))) = 1)
    (hv : Gv * ((1 + 4 * u ^ 2) • (1 : Matrix v v ℂ) - u • (Y * T * X)) = 1)
    (hu : 1 - u ^ 2 ≠ 0) :
    Gv = (1 - u ^ 2)⁻¹ • (1 + u • (Y * Ge * T * X)) := by
  set Ke : Matrix e e ℂ := 1 - u • (T * (X * Y - 1)) with hKe
  set A : Matrix v v ℂ := Y * (T * X) with hA
  -- `K_e X = X − 4u T X`
  have hB : Ke * X = X - (4 * u) • (T * X) := by
    rw [hKe, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.sub_mul,
      Matrix.mul_assoc, hYX, Matrix.mul_smul, Matrix.mul_one, Matrix.one_mul]
    simp only [Matrix.mul_sub, Matrix.mul_smul, smul_sub, smul_smul]
    module
  -- `K_e (T X) = T X + u X − u T X A`
  have hC : Ke * (T * X) = T * X + u • X - u • (T * X * A) := by
    rw [hKe, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.sub_mul,
      Matrix.one_mul, Matrix.mul_sub, ← Matrix.mul_assoc T T X, hT, Matrix.one_mul, hA]
    simp only [Matrix.mul_assoc, smul_sub]
    abel
  have hGX : Ge * X = X + (4 * u) • (Ge * (T * X)) := by
    have h : Ge * (Ke * X) = Ge * (X - (4 * u) • (T * X)) := by rw [hB]
    rw [← Matrix.mul_assoc, hev, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_smul] at h
    rw [eq_comm, sub_eq_iff_eq_add] at h
    exact h
  have hGTX : Ge * (T * X) * ((1 + 4 * u ^ 2) • (1 : Matrix v v ℂ) - u • A) = T * X - u • X := by
    have h : Ge * (Ke * (T * X)) = Ge * (T * X + u • X - u • (T * X * A)) := by rw [hC]
    rw [← Matrix.mul_assoc, hev, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_add, Matrix.mul_smul,
      Matrix.mul_smul, hGX] at h
    have hassoc : Ge * (T * X * A) = Ge * (T * X) * A := by simp only [Matrix.mul_assoc]
    rw [hassoc] at h
    set W := Ge * (T * X) with hW
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, h]
    module
  have hleft : ((1 - u ^ 2)⁻¹ • (1 + u • (Y * Ge * T * X))) *
      ((1 + 4 * u ^ 2) • (1 : Matrix v v ℂ) - u • (Y * T * X)) = 1 := by
    have hYG : Y * Ge * T * X = Y * (Ge * (T * X)) := by simp only [Matrix.mul_assoc]
    have hYTX : Y * T * X = A := by rw [hA, Matrix.mul_assoc]
    rw [hYG, hYTX, Matrix.smul_mul, Matrix.add_mul, Matrix.one_mul, Matrix.smul_mul,
      Matrix.mul_assoc, hGTX, Matrix.mul_sub, Matrix.mul_smul, hYX, ← hA]
    rw [show (1 + 4 * u ^ 2) • (1 : Matrix v v ℂ) - u • A + u • (A - u • (5 : ℂ) • 1) =
      (1 - u ^ 2) • (1 : Matrix v v ℂ) by module]
    rw [smul_smul, inv_mul_cancel₀ hu, one_smul]
  have hright := mul_eq_one_comm.mp hleft
  calc Gv = Gv * (((1 + 4 * u ^ 2) • (1 : Matrix v v ℂ) - u • (Y * T * X)) *
        ((1 - u ^ 2)⁻¹ • (1 + u • (Y * Ge * T * X)))) := by rw [hright, Matrix.mul_one]
    _ = (1 - u ^ 2)⁻¹ • (1 + u • (Y * Ge * T * X)) := by rw [← Matrix.mul_assoc, hv, Matrix.one_mul]

end Resolvent

section StepOp

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **The resolvent of the vertex operator from the step**, for any five involutions `Γ_t`:
`K_v⁻¹ = (1 − u²)⁻¹ (1 + u Y (1 − uB)⁻¹ T X)`, `B = stepOp Γ`, `T = blockDiagonal Γ`. -/
theorem stepOp_bass_resolvent (Γ : Fin 5 → Matrix V V ℂ) (hΓ : ∀ t, Γ t * Γ t = 1) (u : ℂ)
    (hu : 1 - u ^ 2 ≠ 0) (hB : IsUnit (1 - u • stepOp Γ).det)
    (hK : IsUnit ((1 + 4 * u ^ 2) • (1 : Matrix V V ℂ) - u • ∑ t, Γ t).det) :
    ((1 + 4 * u ^ 2) • (1 : Matrix V V ℂ) - u • ∑ t, Γ t)⁻¹ =
      (1 - u ^ 2)⁻¹ • (1 + u • (rowY V ℂ * (1 - u • stepOp Γ)⁻¹ * blockDiagonal Γ * colX V ℂ)) := by
  have hT : blockDiagonal Γ * blockDiagonal Γ = 1 := by
    rw [← blockDiagonal_mul]
    simp only [hΓ]
    exact blockDiagonal_one
  have hstep : stepOp Γ = blockDiagonal Γ * (colX V ℂ * rowY V ℂ - 1) := by
    rw [stepOp_eq, Matrix.mul_sub, Matrix.mul_one]
  have hsum : rowY V ℂ * blockDiagonal Γ * colX V ℂ = ∑ t, Γ t := rowY_blockDiagonal_colX Γ
  apply bass_resolvent u (blockDiagonal Γ) (colX V ℂ) (rowY V ℂ) _ _ hT (rowY_mul_colX) _ _ hu
  · rw [← hstep]
    exact Matrix.nonsing_inv_mul _ hB
  · rw [hsum]
    exact Matrix.nonsing_inv_mul _ hK

end StepOp

section Sheets

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The kinetic intercept `M_ε(u)² = ((u⁻¹ + 4u)² − 25)/(5ε²)`. -/
noncomputable def massIntercept (u ε : ℂ) : ℂ := ((u⁻¹ + 4 * u) ^ 2 - 25) / (5 * ε ^ 2)

/-- The kinetic operator `L_ε = (25I − FG)/(5ε²)`. -/
noncomputable def kinetic (F G : Matrix n n ℂ) (ε : ℂ) : Matrix n n ℂ :=
  (1 / (5 * ε ^ 2)) • ((25 : ℂ) • (1 : Matrix n n ℂ) - F * G)

/-- `Q = M_ε(u)² + L_ε`. -/
noncomputable def normalizedQ (F G : Matrix n n ℂ) (u ε : ℂ) : Matrix n n ℂ :=
  massIntercept u ε • (1 : Matrix n n ℂ) + kinetic F G ε

/-- The scale `ρ = 5u²ε²/(1 + 4u²)`. -/
noncomputable def schurScale (u ε : ℂ) : ℂ := 5 * u ^ 2 * ε ^ 2 / (1 + 4 * u ^ 2)

/-- **The exact Schur identity:** eliminating the second sheet,
`(1 + 4u²)I − (u²/(1 + 4u²)) FG = ρ (M_ε(u)² + L_ε)`. -/
theorem normalized_schur (F G : Matrix n n ℂ) (u ε : ℂ) (hu : u ≠ 0) (hε : ε ≠ 0)
    (ha : 1 + 4 * u ^ 2 ≠ 0) :
    (1 + 4 * u ^ 2) • (1 : Matrix n n ℂ) - (u ^ 2 / (1 + 4 * u ^ 2)) • (F * G) =
      schurScale u ε • normalizedQ F G u ε := by
  have h5 : (5 : ℂ) * ε ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hε)
  rw [normalizedQ, kinetic, massIntercept, schurScale]
  rw [show (5 * u ^ 2 * ε ^ 2 / (1 + 4 * u ^ 2)) •
      ((((u⁻¹ + 4 * u) ^ 2 - 25) / (5 * ε ^ 2)) • (1 : Matrix n n ℂ) +
        (1 / (5 * ε ^ 2)) • ((25 : ℂ) • (1 : Matrix n n ℂ) - F * G)) =
      ((5 * u ^ 2 * ε ^ 2 / (1 + 4 * u ^ 2)) *
        (((u⁻¹ + 4 * u) ^ 2 - 25) / (5 * ε ^ 2) + 25 / (5 * ε ^ 2))) • (1 : Matrix n n ℂ) -
      ((5 * u ^ 2 * ε ^ 2 / (1 + 4 * u ^ 2)) * (1 / (5 * ε ^ 2))) • (F * G) by module]
  have ha' : 1 + u ^ 2 * 4 ≠ 0 := by rwa [mul_comm (u ^ 2) 4]
  have e : u ^ 2 * (u⁻¹ + 4 * u) ^ 2 = (1 + 4 * u ^ 2) ^ 2 := by
    field_simp <;> ring
  have c1 : (5 * u ^ 2 * ε ^ 2 / (1 + 4 * u ^ 2)) *
      (((u⁻¹ + 4 * u) ^ 2 - 25) / (5 * ε ^ 2) + 25 / (5 * ε ^ 2)) = 1 + 4 * u ^ 2 := by
    rw [← add_div, sub_add_cancel]
    rw [show 5 * u ^ 2 * ε ^ 2 / (1 + 4 * u ^ 2) * ((u⁻¹ + 4 * u) ^ 2 / (5 * ε ^ 2)) =
      (u ^ 2 * (u⁻¹ + 4 * u) ^ 2) / (1 + 4 * u ^ 2) by field_simp]
    rw [e, sq, mul_div_assoc, div_self ha, mul_one]
  have c2 : (5 * u ^ 2 * ε ^ 2 / (1 + 4 * u ^ 2)) * (1 / (5 * ε ^ 2)) = u ^ 2 / (1 + 4 * u ^ 2) := by
    field_simp
  rw [c1, c2]

/-- The second-sheet block operator `K = [[aI, −uF], [−uG, aI]]`. -/
noncomputable def sheetK (F G : Matrix n n ℂ) (u : ℂ) : Matrix (n ⊕ n) (n ⊕ n) ℂ :=
  fromBlocks ((1 + 4 * u ^ 2) • 1) (-u • F) (-u • G) ((1 + 4 * u ^ 2) • 1)

/-- **The first-sheet block of the inverse is the normalized Green operator:**
`Q⁻¹ = ρ (K⁻¹)₁₁`. -/
theorem normalized_schur_inverse (F G : Matrix n n ℂ) (u ε : ℂ) (hu : u ≠ 0) (hε : ε ≠ 0)
    (ha : 1 + 4 * u ^ 2 ≠ 0) (hQ : IsUnit (normalizedQ F G u ε).det) :
    (normalizedQ F G u ε)⁻¹ = schurScale u ε • ((sheetK F G u)⁻¹).toBlocks₁₁ := by
  set a : ℂ := 1 + 4 * u ^ 2 with ha_def
  have hρ : schurScale u ε ≠ 0 := by
    rw [schurScale]
    exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hu))
      (pow_ne_zero 2 hε)) ha
  letI hD : Invertible (a • (1 : Matrix n n ℂ)) :=
    ⟨a⁻¹ • 1, by rw [smul_mul_smul_comm, Matrix.one_mul, inv_mul_cancel₀ ha, one_smul],
      by rw [smul_mul_smul_comm, Matrix.one_mul, mul_inv_cancel₀ ha, one_smul]⟩
  have hinvD : ⅟(a • (1 : Matrix n n ℂ)) = a⁻¹ • 1 := rfl
  have hBDC : (-u • F) * (a⁻¹ • (1 : Matrix n n ℂ)) * (-u • G) = (u ^ 2 / a) • (F * G) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]
    congr 1
    field_simp <;> ring
  have hS : schurS (a • 1) (-u • F) (-u • G) (a • (1 : Matrix n n ℂ)) =
      schurScale u ε • normalizedQ F G u ε := by
    rw [schurS, hinvD, hBDC, ← normalized_schur F G u ε hu hε ha]
  have hSunit : IsUnit (schurS (a • 1) (-u • F) (-u • G) (a • (1 : Matrix n n ℂ))).det := by
    rw [hS, Matrix.det_smul]
    exact (IsUnit.pow _ (isUnit_iff_ne_zero.mpr hρ)).mul hQ
  letI hSi : Invertible (schurS (a • 1) (-u • F) (-u • G) (a • (1 : Matrix n n ℂ))) :=
    Matrix.invertibleOfIsUnitDet _ hSunit
  have hK := schur_inv (a • 1) (-u • F) (-u • G) (a • (1 : Matrix n n ℂ))
  have hKdef : sheetK F G u = fromBlocks (a • 1) (-u • F) (-u • G) (a • (1 : Matrix n n ℂ)) := rfl
  rw [hKdef, hK]
  have hblock : (schurR (-u • G) (a • (1 : Matrix n n ℂ)) *
      ⅟(schurS (a • 1) (-u • F) (-u • G) (a • (1 : Matrix n n ℂ))) *
        schurL (-u • F) (a • (1 : Matrix n n ℂ)) + schurQ (a • (1 : Matrix n n ℂ))).toBlocks₁₁ =
      ⅟(schurS (a • 1) (-u • F) (-u • G) (a • (1 : Matrix n n ℂ))) := by
    rw [schurR, schurL, schurQ, fromRows_mul, fromRows_mul_fromCols, fromBlocks_add,
      toBlocks_fromBlocks₁₁, Matrix.one_mul, Matrix.mul_one, add_zero]
  have hinv2 : (schurScale u ε • normalizedQ F G u ε)⁻¹ =
      (schurScale u ε)⁻¹ • (normalizedQ F G u ε)⁻¹ := by
    letI := invertibleOfNonzero hρ
    exact (Matrix.inv_smul _ _ hQ).trans (by rw [invOf_eq_inv])
  rw [hblock, Matrix.invOf_eq_nonsing_inv, hS, hinv2, smul_smul, mul_inv_cancel₀ hρ, one_smul]

/-- **The kinetic part is a sum of squares:** for five unitaries `U_t`, with `F = Σ U_t`,
`25 I − F F* = Σ_{s<t} (U_s − U_t)(U_s − U_t)*`. -/
theorem kinetic_sum_of_squares (U : Fin 5 → Matrix n n ℂ) (hU : ∀ t, U t * (U t)ᴴ = 1) :
    (25 : ℂ) • (1 : Matrix n n ℂ) - (∑ t, U t) * (∑ t, U t)ᴴ =
      ∑ s : Fin 5, ∑ t : Fin 5, if s < t then (U s - U t) * (U s - U t)ᴴ else 0 := by
  simp only [Matrix.conjTranspose_sum, Fin.sum_univ_five, Matrix.conjTranspose_add, Matrix.add_mul,
    Matrix.mul_add, Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, hU]
  simp only [Fin.isValue, Fin.reduceLT, ↓reduceIte, Nat.ofNat_pos, lt_self_iff_false]
  module

/-- **The affine change of the step weight shifts only the mass intercept.** -/
theorem affine_change (F G : Matrix n n ℂ) (u v ε : ℂ) :
    normalizedQ F G v ε - normalizedQ F G u ε =
      (massIntercept v ε - massIntercept u ε) • (1 : Matrix n n ℂ) := by
  rw [normalizedQ, normalizedQ, sub_smul]
  abel

/-- At the point `u = i/4` the intercept is `M_ε²ε² = −34/5`. -/
theorem imaginary_quarter_intercept (ε : ℂ) (hε : ε ≠ 0) :
    ε ^ 2 * massIntercept (Complex.I / 4) ε = -34 / 5 := by
  rw [massIntercept]
  have hI : (Complex.I / 4)⁻¹ = -4 * Complex.I := by
    rw [inv_div, div_eq_iff Complex.I_ne_zero]
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [hI]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

end Sheets

end Comparison.GroupsContinuumLaw
