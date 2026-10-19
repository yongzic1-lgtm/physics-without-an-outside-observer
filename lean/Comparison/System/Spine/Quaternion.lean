import Comparison.System.Postulates

/-!
# The proof system, the spine: every candidate system is a quaternionic plane

For every candidate system `S` (P1 to P3 in their mathematical
form), the real-linear maps `i` (multiplication by the complex unit) and `Θ` (the quaternionic structure) satisfy
`i² = Θ² = −1`, `Θi = −iΘ`: they are the quaternion units `i`, `j`, and `k = iΘ`. So `S.H` is a
module
over the quaternions `ℍ`, and `dim_ℍ H = 2`: the quaternionic plane `ℍ²` (Prop. 1, `H = ℍⁿ`, with
`n = 2` by the uniqueness theorem).

* `CandidateSystem.unitI`, `CandidateSystem.unitJ`: `i` and `Θ` as real-linear maps.
* `CandidateSystem.quatBasis`: the quaternion basis `i, Θ, iΘ` of `End_ℝ(H)`.
* `CandidateSystem.quatHom : ℍ →ₐ[ℝ] End_ℝ(H)`, `CandidateSystem.quatModule : Module ℍ H`.
* `quaternionic_plane`: `dim_ℝ H = 8`, `dim_ℝ ℍ = 4` and `dim_ℍ H = 2`.
-/

namespace Comparison.System

open Complex Quaternion

namespace CandidateSystem

variable (S : CandidateSystem)

/-- The complex unit `i` acting on the states, as a real-linear map. -/
noncomputable def unitI : Module.End ℝ S.H where
  toFun v := Complex.I • v
  map_add' _ _ := smul_add _ _ _
  map_smul' r v := (smul_comm Complex.I r v)

/-- The quaternionic structure `Θ`, as a real-linear map. -/
noncomputable def unitJ : Module.End ℝ S.H where
  toFun := S.partner.Θ
  map_add' := S.partner.map_add
  map_smul' r v := by
    have h : (r • v : S.H) = ((r : ℂ) • v) := (Complex.coe_smul r v).symm
    simp only [RingHom.id_apply]
    rw [h, S.partner.map_smul, Complex.star_def, Complex.conj_ofReal, Complex.coe_smul]

theorem unitI_apply (v : S.H) : S.unitI v = Complex.I • v := rfl

theorem unitJ_apply (v : S.H) : S.unitJ v = S.partner.Θ v := rfl

/-- **The quaternion basis** `i, Θ, iΘ`: `i² = −1`, `Θ² = −1`, `iΘ = k`, `Θi = −k`. -/
noncomputable def quatBasis : QuaternionAlgebra.Basis (Module.End ℝ S.H) (-1 : ℝ) 0 (-1) where
  i := S.unitI
  j := S.unitJ
  k := S.unitI * S.unitJ
  i_mul_i := by
    ext v
    rw [Module.End.mul_apply, unitI_apply, unitI_apply, smul_smul, Complex.I_mul_I, neg_one_smul]
    simp
  j_mul_j := by
    ext v
    rw [Module.End.mul_apply, unitJ_apply, unitJ_apply, S.partner.Θ_Θ]
    simp
  i_mul_j := rfl
  j_mul_i := by
    ext v
    rw [Module.End.mul_apply, unitJ_apply, unitI_apply, S.partner.map_smul, Complex.star_def,
      Complex.conj_I]
    simp [unitI_apply, unitJ_apply]

/-- **The quaternions act on the states of every candidate system.** -/
noncomputable def quatHom : ℍ[ℝ] →ₐ[ℝ] Module.End ℝ S.H := S.quatBasis.liftHom

/-- **`H` is a module over the quaternions.** -/
noncomputable abbrev quatModule : Module ℍ[ℝ] S.H := Module.compHom S.H S.quatHom.toRingHom

theorem quat_smul_def (q : ℍ[ℝ]) (v : S.H) :
    @HSMul.hSMul ℍ[ℝ] S.H S.H (@instHSMul _ _ S.quatModule.toSMul) q v = S.quatHom q v := rfl

theorem quatTower : @IsScalarTower ℝ ℍ[ℝ] S.H _ S.quatModule.toSMul _ := by
  let _ := S.quatModule
  refine ⟨fun r q v => ?_⟩
  change S.quatHom (r • q) v = r • S.quatHom q v
  rw [map_smul, LinearMap.smul_apply]

end CandidateSystem

open CandidateSystem

/-- **Every candidate system is the quaternionic plane:** `dim_ℝ H = 8`, `dim_ℝ ℍ = 4`, and with the
quaternion action `i`, `Θ`, `iΘ`, `dim_ℍ H = 2`. Every candidate system: `System.uniqueness`. -/
theorem quaternionic_plane (S : CandidateSystem) :
    Module.finrank ℝ S.H = 8 ∧ Module.finrank ℝ ℍ[ℝ] = 4 ∧
      @Module.finrank ℍ[ℝ] S.H _ _ S.quatModule = 2 := by
  let _ := S.quatModule
  have := S.quatTower
  have h8 : Module.finrank ℝ S.H = 8 := (uniqueness S).2.2.2.2.2.2
  have h4 : Module.finrank ℝ ℍ[ℝ] = 4 := Quaternion.finrank_eq_four
  refine ⟨h8, h4, ?_⟩
  have := Module.finrank_mul_finrank ℝ ℍ[ℝ] S.H
  rw [h4, h8] at this
  omega

end Comparison.System
