import Comparison.System.Basic
import Comparison.System.Completion.Ext.Planes
import Comparison.System.Table.Neutrinos

set_option linter.style.longLine false

/-!
# The proof system, the completions: the three pairings of the four directions beside `h` (row L04)

The four lines other than the direction `h` of the last step pair in exactly three ways, `(ab|cd)`, `(ac|bd)`,
`(ad|bc)`. Their normalized sums on the ten symmetric states,

  `U_h = (e_ab + e_cd, e_ac + e_bd, e_ad + e_bc)/√2`,

are read against the rooted inverse `Γ_P`, the inverse of `5I − A` with the singlet removed, on the ten.

* `rooted_inverse`: **`(5I − A)` without the singlet times `rootedInv32` is `32I`** on the fifteen other two-spinor
  states; `rooted_plane_block`: its block on the ten symmetric states is `7I + 7J + A_P`, so `Γ_P = (7I + 7J + A_P)/32`.
* `plane_inverse`, `GammaP_mul_inv`: **`Γ_P⁻¹ = (24I − 4A_P − J)/5`**.
* `pairCols h`: the three pairings beside `h` as columns on the ten (`pairPlanes_pairings`: they are the pairings of
  `WholePicture.pairingsBeside h`); `pairCols_gram`: `VᵀV = 2I₃`, `VᵀA_PV = 2I₃`, `VᵀJV = 4J₃`, so `U_h = V/√2` has
  `U_hᵀU_h = I₃`, `U_hᵀA_PU_h = I₃`, `U_hᵀJU_h = 2J₃`; `pairing_response_Z`: `Vᵀ(24I − 4A_P − J)V = 40I₃ − 4J₃`.
* `pairing_response`: **`10U_hᵀΓ_P⁻¹U_h = 40I₃ − 4J₃` at every `h`**; `response_spectrum`: **spectrum `28, 40, 40`**,
  the common mode `28 = 1/Ψ@{a,b}` (`common_mode`).
* `row_L04_pairings`: row L04 with the three pairings' response.
-/

namespace Comparison.System.Completion.Families

open Matrix

/-! ## The rooted inverse on the ten symmetric states -/

/-- `32` times the inverse of `5I − A` with the singlet removed, on the fifteen other two-spinor states (the five
vector states, then the ten symmetric states, in the order of `disagreeSet`). -/
def rootedInv32 : Matrix (Fin 15) (Fin 15) ℤ :=
  !![12, 5, 5, 5, 5, 7, 7, 7, 7, 6, 6, 6, 6, 6, 6;
     5, 12, 5, 5, 5, 7, 6, 6, 6, 7, 7, 7, 6, 6, 6;
     5, 5, 12, 5, 5, 6, 7, 6, 6, 7, 6, 6, 7, 7, 6;
     5, 5, 5, 12, 5, 6, 6, 7, 6, 6, 7, 6, 7, 6, 7;
     5, 5, 5, 5, 12, 6, 6, 6, 7, 6, 6, 7, 6, 7, 7;
     7, 7, 6, 6, 6, 14, 7, 7, 7, 7, 7, 7, 8, 8, 8;
     7, 6, 7, 6, 6, 7, 14, 7, 7, 7, 8, 8, 7, 7, 8;
     7, 6, 6, 7, 6, 7, 7, 14, 7, 8, 7, 8, 7, 8, 7;
     7, 6, 6, 6, 7, 7, 7, 7, 14, 8, 8, 7, 8, 7, 7;
     6, 7, 7, 6, 6, 7, 7, 8, 8, 14, 7, 7, 7, 7, 8;
     6, 7, 6, 7, 6, 7, 8, 7, 8, 7, 14, 7, 7, 8, 7;
     6, 7, 6, 6, 7, 7, 8, 8, 7, 7, 7, 14, 8, 7, 7;
     6, 6, 7, 7, 6, 8, 7, 7, 8, 7, 7, 8, 14, 7, 7;
     6, 6, 7, 6, 7, 8, 7, 8, 7, 7, 8, 7, 7, 14, 7;
     6, 6, 6, 7, 7, 8, 8, 7, 7, 8, 7, 7, 7, 7, 14]

/-- **The rooted inverse:** `(5I − A)` without the singlet, times `rootedInv32`, is `32I`. -/
theorem rooted_inverse :
    ((5 : ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ) - A ℤ).submatrix Fin.succ Fin.succ * rootedInv32 = (32 : ℤ) • 1 := by
  decide +kernel

/-- The ten symmetric states among the fifteen: `planeRel i = i + 6`, the place `i + 5` after the singlet. -/
def planeIdx (i : Fin 10) : Fin 15 := ⟨i.val + 5, by omega⟩

theorem planeIdx_succ (i : Fin 10) : Fin.succ (planeIdx i) = SysPlanes.planeRel i := by
  revert i
  decide

/-- **`32Γ_P = 7I + 7J + A_P`:** the block of the rooted inverse on the ten symmetric states. -/
theorem rooted_plane_block :
    rootedInv32.submatrix planeIdx planeIdx = (7 : ℤ) • 1 + 7 • SysPlanes.J10 + SysPlanes.petAdj := by
  decide +kernel

/-- `Γ_P = (7I + 7J + A_P)/32`. -/
def GammaP : Matrix (Fin 10) (Fin 10) ℚ :=
  (1 / 32 : ℚ) • (rootedInv32.submatrix planeIdx planeIdx).map (Int.castRingHom ℚ)

/-- `Γ_P⁻¹ = (24I − 4A_P − J)/5`. -/
def GammaPinv : Matrix (Fin 10) (Fin 10) ℚ :=
  (1 / 5 : ℚ) • ((24 : ℤ) • (1 : Matrix (Fin 10) (Fin 10) ℤ) - 4 • SysPlanes.petAdj - SysPlanes.J10).map (Int.castRingHom ℚ)

theorem plane_inverse :
    ((7 : ℤ) • 1 + 7 • SysPlanes.J10 + SysPlanes.petAdj) * ((24 : ℤ) • (1 : Matrix (Fin 10) (Fin 10) ℤ) - 4 • SysPlanes.petAdj - SysPlanes.J10) =
      (160 : ℤ) • 1 := by
  decide +kernel

/-- **`Γ_PΓ_P⁻¹ = I`.** -/
theorem GammaP_mul_inv : GammaP * GammaPinv = 1 := by
  rw [GammaP, GammaPinv, rooted_plane_block, Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← Matrix.map_mul,
    plane_inverse]
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, smul_eq_mul, Int.coe_castRingHom]
  split_ifs <;> norm_num

/-! ## The three pairings beside `h` -/

/-- The four lines other than `h`, in increasing order. -/
def others : Fin 5 → Fin 4 → Fin 5 :=
  ![![1, 2, 3, 4], ![0, 2, 3, 4], ![0, 1, 3, 4], ![0, 1, 2, 4], ![0, 1, 2, 3]]

/-- The two planes of the pairing `p` beside `h`: `(ab|cd)`, `(ac|bd)`, `(ad|bc)` of the four other lines
`a < b < c < d`. -/
def pairPlanes (h : Fin 5) (p : Fin 3) : Finset (Fin 5) × Finset (Fin 5) :=
  match p.val with
  | 0 => ({others h 0, others h 1}, {others h 2, others h 3})
  | 1 => ({others h 0, others h 2}, {others h 1, others h 3})
  | _ => ({others h 0, others h 3}, {others h 1, others h 2})

/-- They are the three pairings of `WholePicture.pairingsBeside h`. -/
theorem pairPlanes_pairings : ∀ h : Fin 5,
    (Finset.univ.image fun p : Fin 3 => ({(pairPlanes h p).1, (pairPlanes h p).2} : Finset (Finset (Fin 5)))) =
      WholePicture.pairingsBeside h := by
  decide +kernel

/-- The three pairings beside `h` as columns on the ten symmetric states: `e_ab + e_cd`, `e_ac + e_bd`, `e_ad + e_bc`. -/
def pairCols (h : Fin 5) : Matrix (Fin 10) (Fin 3) ℤ := Matrix.of fun i p =>
  if SysPlanes.planeSet i = (pairPlanes h p).1 ∨ SysPlanes.planeSet i = (pairPlanes h p).2 then 1 else 0

/-- `J₃`. -/
def J3 : Matrix (Fin 3) (Fin 3) ℤ := Matrix.of fun _ _ => 1

/-- `VᵀV = 2I₃`, `VᵀA_PV = 2I₃`, `VᵀJV = 4J₃`. -/
theorem pairCols_gram : ∀ h : Fin 5, (pairCols h)ᵀ * pairCols h = (2 : ℤ) • 1 ∧
    (pairCols h)ᵀ * SysPlanes.petAdj * pairCols h = (2 : ℤ) • 1 ∧ (pairCols h)ᵀ * SysPlanes.J10 * pairCols h = (4 : ℤ) • J3 := by
  decide +kernel

/-- `Vᵀ(24I − 4A_P − J)V = 40I₃ − 4J₃`. -/
theorem pairing_response_Z : ∀ h : Fin 5,
    (pairCols h)ᵀ * ((24 : ℤ) • (1 : Matrix (Fin 10) (Fin 10) ℤ) - 4 • SysPlanes.petAdj - SysPlanes.J10) * pairCols h =
      (40 : ℤ) • 1 - 4 • J3 := by
  decide +kernel

/-- The normalized pairings `U_h = V/√2` over `ℝ`. -/
noncomputable def Uh (h : Fin 5) : Matrix (Fin 10) (Fin 3) ℝ := (Real.sqrt 2)⁻¹ • (pairCols h).map (Int.castRingHom ℝ)

/-- `Γ_P⁻¹` over `ℝ`. -/
noncomputable def GammaPinvR : Matrix (Fin 10) (Fin 10) ℝ :=
  (1 / 5 : ℝ) • ((24 : ℤ) • (1 : Matrix (Fin 10) (Fin 10) ℤ) - 4 • SysPlanes.petAdj - SysPlanes.J10).map (Int.castRingHom ℝ)

theorem sqrt_two_inv_sq : (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ = (1 / 2 : ℝ) := by
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num)]
  norm_num

theorem smul_sandwich (c d : ℝ) (V : Matrix (Fin 10) (Fin 3) ℝ) (M : Matrix (Fin 10) (Fin 10) ℝ) :
    (c • V)ᵀ * (d • M) * (c • V) = (c * c * d) • (Vᵀ * M * V) := by
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  congr 1
  ring

/-- **`U_hᵀU_h = I₃`.** -/
theorem Uh_orthonormal (h : Fin 5) : (Uh h)ᵀ * Uh h = 1 := by
  rw [Uh, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, sqrt_two_inv_sq,
    ← Matrix.transpose_map, ← Matrix.map_mul, (pairCols_gram h).1]
  ext i j
  simp only [Matrix.smul_apply, Matrix.map_apply, Matrix.one_apply, smul_eq_mul, Int.coe_castRingHom]
  split_ifs <;> norm_num

/-- **The three pairings' response: `10U_hᵀΓ_P⁻¹U_h = 40I₃ − 4J₃`** at every `h`. -/
theorem pairing_response (h : Fin 5) :
    (10 : ℝ) • ((Uh h)ᵀ * GammaPinvR * Uh h) = ((40 : ℤ) • (1 : Matrix (Fin 3) (Fin 3) ℤ) - 4 • J3).map (Int.castRingHom ℝ) := by
  rw [Uh, GammaPinvR, smul_sandwich, smul_smul, sqrt_two_inv_sq, ← Matrix.transpose_map, ← Matrix.map_mul,
    ← Matrix.map_mul, pairing_response_Z h]
  norm_num

/-- **The spectrum `28, 40, 40`** of `40I₃ − 4J₃`: `28` on `(1, 1, 1)`, `40` on `(1, −1, 0)` and `(1, 0, −1)`. -/
theorem response_spectrum :
    ((40 : ℤ) • (1 : Matrix (Fin 3) (Fin 3) ℤ) - 4 • J3) *ᵥ ![1, 1, 1] = (28 : ℤ) • ![1, 1, 1] ∧
      ((40 : ℤ) • (1 : Matrix (Fin 3) (Fin 3) ℤ) - 4 • J3) *ᵥ ![1, -1, 0] = (40 : ℤ) • ![1, -1, 0] ∧
      ((40 : ℤ) • (1 : Matrix (Fin 3) (Fin 3) ℤ) - 4 • J3) *ᵥ ![1, 0, -1] = (40 : ℤ) • ![1, 0, -1] := by
  decide +kernel

/-- **The common mode `28 = 1/Ψ@{a,b}`.** -/
theorem common_mode : (Comparison.Law.PsiS Comparison.Law.sPlane)⁻¹ = 28 := by
  rw [Comparison.Law.piece_Psi_plane]
  norm_num

end Comparison.System.Completion.Families

namespace Comparison.System

open Matrix Comparison.System.Completion

/-- **Row L04, with the three pairings' response.** The four lines beside the last-step direction pair in exactly three
ways (`row_L04`); their normalized sums `U_h` on the ten symmetric states have `10U_hᵀΓ_P⁻¹U_h = 40I₃ − 4J₃` against the
rooted inverse `Γ_P = (7I + 7J + A_P)/32` of `5I − A` without the singlet, `Γ_P⁻¹ = (24I − 4A_P − J)/5`, at every `h`;
spectrum `28, 40, 40`, the common mode `28 = 1/Ψ@{a,b}`. Recognition: the three charged families. -/
theorem row_L04_pairings :
    Table.Row.L04 = 3 ∧ (∀ h : Fin 5, (WholePicture.pairingsBeside h).card = 3) ∧
    Families.GammaP * Families.GammaPinv = 1 ∧
    (∀ h : Fin 5, (Families.Uh h)ᵀ * Families.Uh h = 1 ∧
      (10 : ℝ) • ((Families.Uh h)ᵀ * Families.GammaPinvR * Families.Uh h) =
        ((40 : ℤ) • (1 : Matrix (Fin 3) (Fin 3) ℤ) - 4 • Families.J3).map (Int.castRingHom ℝ)) ∧
    ((40 : ℤ) • (1 : Matrix (Fin 3) (Fin 3) ℤ) - 4 • Families.J3) *ᵥ ![1, 1, 1] = (28 : ℤ) • ![1, 1, 1] ∧
    (Comparison.Law.PsiS Comparison.Law.sPlane)⁻¹ = 28 :=
  ⟨row_L04.1, row_L04.2, Families.GammaP_mul_inv,
    fun h => ⟨Families.Uh_orthonormal h, Families.pairing_response h⟩, Families.response_spectrum.1,
    Families.common_mode⟩

end Comparison.System
