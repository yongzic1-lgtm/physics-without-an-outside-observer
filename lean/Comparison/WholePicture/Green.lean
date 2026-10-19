module

public import Comparison.WholePicture.Circulation

/-!
# The whole picture, statement 11: `(5 − A)⁺ = (7 + A)/32 − 3J/128` as the Moore–Penrose inverse

`green_identity`
(`RuleAndLaw/CriticalGerm.lean`) and `green_identity_local` (`Circulation.lean`) give
`(5 − A)·128G = 128 − 8J`. Here the four Penrose equations, so that `G` is the pseudo-inverse itself
and not only a Green function:

* `lapM = 5 − A` and `greenM = G` over `ℝ`; `greenM_eq`: **`G = (7 + A)/32 − 3J/128`**.
* `lap_mul_green`, `green_mul_lap`: `(5 − A)G = G(5 − A) = 1 − J/16`, the projector off the
  constants.
* `green_penrose`: **`MGM = M`, `GMG = G`, `(MG)ᵀ = MG`, `(GM)ᵀ = GM`** for `M = 5 − A`.
* `penrose_unique`: two solutions of the four Penrose equations are equal (any square matrices over
  a commutative ring); `green_pinv`: **every `X` with the four Penrose equations for `5 − A` is
  `G`**: `(5 − A)⁺ = (7 + A)/32 − 3J/128`.
-/

@[expose] public section

namespace Comparison.WholePicture

open Matrix

/-- **The Moore–Penrose inverse is unique:** two matrices that satisfy the four Penrose equations
for `M` are equal. -/
theorem penrose_unique {n : Type*} [Fintype n] {R : Type*} [CommRing R]
    (M G₁ G₂ : Matrix n n R)
    (h1 : M * G₁ * M = M) (h2 : G₁ * M * G₁ = G₁) (h3 : (M * G₁)ᵀ = M * G₁)
    (h4 : (G₁ * M)ᵀ = G₁ * M)
    (k1 : M * G₂ * M = M) (k2 : G₂ * M * G₂ = G₂) (k3 : (M * G₂)ᵀ = M * G₂)
    (k4 : (G₂ * M)ᵀ = G₂ * M) : G₁ = G₂ := by
  have e1 : G₁ = G₁ * M * G₂ := by
    calc G₁ = G₁ * (M * G₁) := by rw [← Matrix.mul_assoc, h2]
      _ = G₁ * (M * G₁)ᵀ := by rw [h3]
      _ = G₁ * (G₁ᵀ * Mᵀ) := by rw [Matrix.transpose_mul]
      _ = G₁ * (G₁ᵀ * (M * G₂ * M)ᵀ) := by rw [k1]
      _ = G₁ * (G₁ᵀ * Mᵀ * (M * G₂)ᵀ) := by
        rw [Matrix.transpose_mul (M * G₂) M, Matrix.mul_assoc]
      _ = G₁ * ((M * G₁)ᵀ * (M * G₂)ᵀ) := by rw [Matrix.transpose_mul M G₁]
      _ = G₁ * (M * G₁ * (M * G₂)) := by rw [h3, k3]
      _ = G₁ * M * G₁ * (M * G₂) := by simp only [Matrix.mul_assoc]
      _ = G₁ * M * G₂ := by rw [h2, Matrix.mul_assoc]
  have e2 : G₂ = G₁ * M * G₂ := by
    calc G₂ = G₂ * M * G₂ := k2.symm
      _ = (G₂ * M)ᵀ * G₂ := by rw [k4]
      _ = Mᵀ * G₂ᵀ * G₂ := by rw [Matrix.transpose_mul]
      _ = (M * G₁ * M)ᵀ * G₂ᵀ * G₂ := by rw [h1]
      _ = (G₁ * M)ᵀ * (Mᵀ * G₂ᵀ) * G₂ := by
        rw [Matrix.mul_assoc M G₁ M, Matrix.transpose_mul M (G₁ * M), Matrix.mul_assoc (G₁ * M)ᵀ]
      _ = (G₁ * M)ᵀ * (G₂ * M)ᵀ * G₂ := by rw [Matrix.transpose_mul G₂ M]
      _ = G₁ * M * (G₂ * M) * G₂ := by rw [h4, k4]
      _ = G₁ * M * (G₂ * M * G₂) := by simp only [Matrix.mul_assoc]
      _ = G₁ * M * G₂ := by rw [k2]
  rw [e1, ← e2]

set_option maxRecDepth 10000 in
/-- `G(5 − A)·128 = 128 − 8J`. -/
theorem green_identity_right : ∀ x y : Fin 16,
    ∑ z, green128 x z * ((if z = y then 5 else 0) - adjZ z y) = (if x = y then 128 else 0) - 8 := by
  decide +kernel

/-- The columns of `5 − A` and of `128G` add to nothing. -/
theorem lap_col_sum : ∀ y : Fin 16, ∑ x, ((if x = y then 5 else 0) - adjZ x y) = 0 := by
  decide +kernel

theorem green_col_sum : ∀ y : Fin 16, ∑ x, green128 x y = 0 := by
  decide +kernel

/-- `M = 5 − A` over `ℝ`. -/
def lapM : Matrix (Fin 16) (Fin 16) ℝ :=
  Matrix.of fun x y => (((if x = y then 5 else 0) - adjZ x y : ℤ) : ℝ)

/-- `G = 128G/128` over `ℝ`. -/
noncomputable def greenM : Matrix (Fin 16) (Fin 16) ℝ :=
  Matrix.of fun x y => (green128 x y : ℝ) / 128

/-- `1 − J/16`. -/
noncomputable def offConst : Matrix (Fin 16) (Fin 16) ℝ :=
  Matrix.of fun x y => (if x = y then 1 else 0) - 1 / 16

/-- **`G = (7 + A)/32 − 3J/128`.** -/
theorem greenM_eq : greenM = (1 / 32 : ℝ) • ((7 : ℝ) • (1 : Matrix (Fin 16) (Fin 16) ℝ) +
    Matrix.of fun x y => (adjZ x y : ℝ)) - (3 / 128 : ℝ) • Matrix.of fun _ _ => (1 : ℝ) := by
  ext x y
  simp only [greenM, green128, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply,
    Matrix.add_apply, Matrix.one_apply, smul_eq_mul]
  push_cast
  split_ifs <;> ring

/-- **`(5 − A) G = 1 − J/16`.** -/
theorem lap_mul_green : lapM * greenM = offConst := by
  ext x y
  have h := congrArg (fun n : ℤ => (n : ℝ)) (green_identity_local x y)
  push_cast at h
  simp only [Matrix.mul_apply, lapM, greenM, offConst, Matrix.of_apply]
  push_cast
  have e : ∑ z, ((if x = z then (5 : ℝ) else 0) - (adjZ x z : ℝ)) * ((green128 z y : ℝ) / 128) =
      (∑ z, ((if x = z then (5 : ℝ) else 0) - (adjZ x z : ℝ)) * (green128 z y : ℝ)) / 128 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun z _ => ?_
    ring
  rw [e, h]
  split_ifs <;> norm_num

/-- **`G (5 − A) = 1 − J/16`.** -/
theorem green_mul_lap : greenM * lapM = offConst := by
  ext x y
  have h := congrArg (fun n : ℤ => (n : ℝ)) (green_identity_right x y)
  push_cast at h
  simp only [Matrix.mul_apply, lapM, greenM, offConst, Matrix.of_apply]
  push_cast
  have e : ∑ z, (green128 x z : ℝ) / 128 * ((if z = y then (5 : ℝ) else 0) - (adjZ z y : ℝ)) =
      (∑ z, (green128 x z : ℝ) * ((if z = y then (5 : ℝ) else 0) - (adjZ z y : ℝ))) / 128 := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun z _ => ?_
    ring
  rw [e, h]
  split_ifs <;> norm_num

theorem offConst_mul_lap : offConst * lapM = lapM := by
  ext x y
  have h := congrArg (fun n : ℤ => (n : ℝ)) (lap_col_sum y)
  push_cast at h
  simp only [Matrix.mul_apply, lapM, offConst, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  push_cast
  rw [← Finset.mul_sum, h]
  ring

theorem offConst_mul_green : offConst * greenM = greenM := by
  ext x y
  have h := congrArg (fun n : ℤ => (n : ℝ)) (green_col_sum y)
  push_cast at h
  simp only [Matrix.mul_apply, greenM, offConst, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [← Finset.mul_sum, ← Finset.sum_div, h]
  ring

theorem offConst_transpose : offConstᵀ = offConst := by
  ext x y
  simp only [Matrix.transpose_apply, offConst, Matrix.of_apply]
  by_cases h : x = y
  · rw [h]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

/-- **The four Penrose equations for `M = 5 − A` and `G = (7 + A)/32 − 3J/128`.** -/
theorem green_penrose :
    lapM * greenM * lapM = lapM ∧ greenM * lapM * greenM = greenM ∧
      (lapM * greenM)ᵀ = lapM * greenM ∧ (greenM * lapM)ᵀ = greenM * lapM := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [lap_mul_green, offConst_mul_lap]
  · rw [green_mul_lap, offConst_mul_green]
  · rw [lap_mul_green, offConst_transpose]
  · rw [green_mul_lap, offConst_transpose]

/-- **`(5 − A)⁺ = (7 + A)/32 − 3J/128`:** every matrix that satisfies the four Penrose equations for
`5 − A` is `G`. -/
theorem green_pinv (X : Matrix (Fin 16) (Fin 16) ℝ) (h1 : lapM * X * lapM = lapM)
    (h2 : X * lapM * X = X) (h3 : (lapM * X)ᵀ = lapM * X) (h4 : (X * lapM)ᵀ = X * lapM) :
    X = greenM :=
  penrose_unique lapM X greenM h1 h2 h3 h4 green_penrose.1 green_penrose.2.1 green_penrose.2.2.1
    green_penrose.2.2.2

end Comparison.WholePicture
