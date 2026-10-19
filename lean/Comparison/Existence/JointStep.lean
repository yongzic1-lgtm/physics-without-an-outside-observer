module

public import Comparison.Existence.Covariance
public import Comparison.Existence.Gauge

/-!
# Book VII. One step joins the two: the joint step `𝒯 = J(a)Λ(U)` (Proposition 37)

On the sixty-four sets of the six
(any number `n` of directions), with `Λ(O) = extMap O` of `Covariance.lean`.

* `jointStep a U = J(a) Λ(U)`: divide along `a`, carry the gauge by `U`.
* `Jv_mul_extMap`: **dividing then carrying is carrying then dividing**,
  `J(a) Λ(O) = Λ(O) J(O⁻¹a)` for orthogonal `O`.
* `jointStep_rename`: **`Λ(g_x) 𝒯_xy Λ(g_y)⁻¹ = J(g_x a) Λ(g_x U g_y⁻¹)`**: the joint step is gauge-transformed
  like one transport, with the direction `a ↦ g_x a`.
* `jointStep_inv`: **`𝒯_xy⁻¹ = J(U_yx a) Λ(U_yx)`** with `U_yx = U_xy⁻¹`, for a unit direction `a`
  (both products are `1`).
* `connStep`, `connStep_rename`, `connStep_inv`: the same for a connection of P4 with values in the
  rotations of the six (`Gauge.lean`'s `Connection`, `Connection.rename`):
  `Λ(g_x) 𝒯[U](x, y) Λ(g_y)⁻¹ = 𝒯[g·U](x, y)` with `a ↦ g_x a`.
-/

@[expose] public section

namespace Comparison

open Finset
open scoped Matrix

section Joint

variable {n : ℕ}

/-- **The joint step** `𝒯 = J(a) Λ(U)`. -/
noncomputable def jointStep (a : Fin n → ℝ) (U : Matrix (Fin n) (Fin n) ℝ) :
    Module.End ℝ (Finset (Fin n) → ℝ) :=
  Jv a * extMap U

theorem transpose_orth {O : Matrix (Fin n) (Fin n) ℝ} (hO : Oᵀ * O = 1) : Oᵀᵀ * Oᵀ = 1 := by
  rw [Matrix.transpose_transpose]
  exact mul_eq_one_comm.mp hO

/-- **Dividing then carrying is carrying then dividing:** `J(a) Λ(O) = Λ(O) J(O⁻¹ a)` for
orthogonal `O` (`O⁻¹ = Oᵀ`). -/
theorem Jv_mul_extMap (O : Matrix (Fin n) (Fin n) ℝ) (hO : Oᵀ * O = 1) (a : Fin n → ℝ) :
    Jv a * extMap O = extMap O * Jv (Oᵀ *ᵥ a) := by
  rw [extMap_Jv O hO, Matrix.mulVec_mulVec, mul_eq_one_comm.mp hO, Matrix.one_mulVec]

/-- **The gauge transformation of the joint step:** `Λ(g_x) 𝒯 Λ(g_y)⁻¹ = J(g_x a) Λ(g_x U g_y⁻¹)` for
orthogonal `g_x`, with `Λ(g_y)⁻¹ = Λ(g_yᵀ)` (`extMap_mul_transpose`). -/
theorem jointStep_rename (a : Fin n → ℝ) (U gx gy : Matrix (Fin n) (Fin n) ℝ) (hgx : gxᵀ * gx = 1) :
    extMap gx * jointStep a U * extMap gyᵀ = jointStep (gx *ᵥ a) (gx * U * gyᵀ) := by
  rw [jointStep, jointStep]
  calc extMap gx * (Jv a * extMap U) * extMap gyᵀ
      = (extMap gx * Jv a) * (extMap U * extMap gyᵀ) := by simp only [mul_assoc]
    _ = (Jv (gx *ᵥ a) * extMap gx) * extMap (U * gyᵀ) := by rw [extMap_Jv gx hgx, ← extMap_mul]
    _ = Jv (gx *ᵥ a) * extMap (gx * U * gyᵀ) := by
        rw [mul_assoc (Jv (gx *ᵥ a)), ← extMap_mul, Matrix.mul_assoc]

/-- An orthogonal matrix keeps the length. -/
theorem dot_orth {O : Matrix (Fin n) (Fin n) ℝ} (hO : Oᵀ * O = 1) (a : Fin n → ℝ) :
    (O *ᵥ a) ⬝ᵥ (O *ᵥ a) = a ⬝ᵥ a := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hO,
    Matrix.one_mulVec]

/-- **The step back:** for a unit direction `a` and orthogonal `U`,
`(J(a)Λ(U)) (J(Uᵀa)Λ(Uᵀ)) = 1` and `(J(Uᵀa)Λ(Uᵀ)) (J(a)Λ(U)) = 1`: `𝒯_xy⁻¹ = J(U_yx a) Λ(U_yx)`. -/
theorem jointStep_inv (a : Fin n → ℝ) (ha : a ⬝ᵥ a = 1) (U : Matrix (Fin n) (Fin n) ℝ)
    (hU : Uᵀ * U = 1) :
    jointStep a U * jointStep (Uᵀ *ᵥ a) Uᵀ = 1 ∧ jointStep (Uᵀ *ᵥ a) Uᵀ * jointStep a U = 1 := by
  have hU' : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  rw [jointStep, jointStep]
  constructor
  · calc Jv a * extMap U * (Jv (Uᵀ *ᵥ a) * extMap Uᵀ)
        = Jv a * (extMap U * Jv (Uᵀ *ᵥ a)) * extMap Uᵀ := by simp only [mul_assoc]
      _ = Jv a * (Jv a * extMap U) * extMap Uᵀ := by
          rw [extMap_Jv U hU, Matrix.mulVec_mulVec, hU', Matrix.one_mulVec]
      _ = (Jv a * Jv a) * (extMap U * extMap Uᵀ) := by simp only [mul_assoc]
      _ = 1 := by rw [Jv_mul_self, ha, one_smul, one_mul, (extMap_mul_transpose U hU).1]
  · calc Jv (Uᵀ *ᵥ a) * extMap Uᵀ * (Jv a * extMap U)
        = Jv (Uᵀ *ᵥ a) * (extMap Uᵀ * Jv a) * extMap U := by simp only [mul_assoc]
      _ = Jv (Uᵀ *ᵥ a) * (Jv (Uᵀ *ᵥ a) * extMap Uᵀ) * extMap U := by
          rw [extMap_Jv Uᵀ (transpose_orth hU)]
      _ = (Jv (Uᵀ *ᵥ a) * Jv (Uᵀ *ᵥ a)) * (extMap Uᵀ * extMap U) := by simp only [mul_assoc]
      _ = 1 := by
          rw [Jv_mul_self, dot_orth (transpose_orth hU), ha, one_smul, one_mul,
            (extMap_mul_transpose U hU).2]

end Joint

/-! ## The joint step of a connection of P4 -/

section Connection

variable {n : ℕ} {X : Type*}

/-- The rotations of the six. -/
abbrev Rot (n : ℕ) := Matrix.orthogonalGroup (Fin n) ℝ

theorem rot_transpose_mul (g : Rot n) : (g : Matrix (Fin n) (Fin n) ℝ)ᵀ * g = 1 :=
  orthogonal_transpose_mul g.2

theorem rot_inv_val (g : Rot n) :
    ((g⁻¹ : Rot n) : Matrix (Fin n) (Fin n) ℝ) = (g : Matrix (Fin n) (Fin n) ℝ)ᵀ := by
  rw [Matrix.UnitaryGroup.inv_val, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]

/-- **The joint step of a connection:** `𝒯[U](x, y) = J(a) Λ(U_xy)`. -/
noncomputable def connStep (c : Connection X (Rot n)) (a : Fin n → ℝ) (x y : X) :
    Module.End ℝ (Finset (Fin n) → ℝ) :=
  jointStep a (c.U x y : Matrix (Fin n) (Fin n) ℝ)

/-- **Proposition 37, the gauge transformation:** under a gauge transformation `g`,
`Λ(g_x) 𝒯[U](x, y) Λ(g_y)⁻¹ = 𝒯[g·U](x, y)` with the direction `a ↦ g_x a`. -/
theorem connStep_rename (c : Connection X (Rot n)) (g : X → Rot n) (a : Fin n → ℝ) (x y : X) :
    extMap (g x : Matrix (Fin n) (Fin n) ℝ) * connStep c a x y *
        extMap ((g y)⁻¹ : Rot n) =
      connStep (c.rename g) ((g x : Matrix (Fin n) (Fin n) ℝ) *ᵥ a) x y := by
  rw [connStep, connStep, rot_inv_val, jointStep_rename a _ _ _ (rot_transpose_mul (g x))]
  congr 1

/-- **Proposition 37, the step back:** `𝒯[U](x, y)⁻¹ = 𝒯[U](y, x)` with the direction carried,
`J(U_yx a)Λ(U_yx)`, for a unit direction. -/
theorem connStep_inv (c : Connection X (Rot n)) (a : Fin n → ℝ) (ha : a ⬝ᵥ a = 1) (x y : X) :
    connStep c a x y * connStep c ((c.U y x : Matrix (Fin n) (Fin n) ℝ) *ᵥ a) y x = 1 ∧
      connStep c ((c.U y x : Matrix (Fin n) (Fin n) ℝ) *ᵥ a) y x * connStep c a x y = 1 := by
  have hyx : (c.U y x : Matrix (Fin n) (Fin n) ℝ) = (c.U x y : Matrix (Fin n) (Fin n) ℝ)ᵀ := by
    rw [c.U_inv, rot_inv_val]
  rw [connStep, connStep, hyx]
  exact jointStep_inv a ha _ (rot_transpose_mul (c.U x y))

end Connection

end Comparison

end
