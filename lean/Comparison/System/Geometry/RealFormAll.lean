import Comparison.System.Geometry.RealFormGroup
import Mathlib.Analysis.Matrix.Spectrum

/-!
# The geometry of comparison: the real form of every division

For every division of P1's real six, given by
its orthogonal projector `P` (symmetric, idempotent):

* `P = R·P_S·Rᵀ` for a rotation `R` (`RᵀR = 1`, `det R = 1`) and a coordinate set `S`
  (`exists_rot_projOf`: the spectral theorem, eigenvalues `0, 1`, one sign flip for `det R = 1`);
* `R` lifts to an element of `SU(4)` `U ∈ SU(4)` with `U ι(z) Uᵀ = ι(Rz)` on the six (`lift_rot`, from
  `GroupsContinuumLaw.rot6_onto`);
* the square root of the sign of `P` is the turned half of `S` (`halfSix_conj`), and the action of the generators is
  carried by the rotation (`act_conj`), so Definition 15's real form of `P` is `U · realFormAlg (P_S) · U⁻¹`
  (`realFormAlg_conj`), the conjugate of the real form of a coordinate division
  (`realFormAlg_every_division`); the kept and moved generators of `P` are `R X Rᵀ` for those of `S`
  (`keptBy_conj`, `movedBy_conj`).
-/

open scoped InnerProductSpace Kronecker ComplexOrder
open Matrix Complex Module

namespace Comparison.System

namespace Geometry

/-! ## A symmetric projector is a coordinate projector in a rotated basis -/

theorem projOf_transpose (S : Finset (Fin 6)) : (projOf S)ᵀ = projOf S := by
  unfold projOf
  exact Matrix.diagonal_transpose _

/-- The sign flip of the first direction. -/
noncomputable def flip0 : Matrix (Fin 6) (Fin 6) ℝ := Matrix.diagonal fun a => if a = 0 then -1 else 1

theorem flip0_transpose : flip0ᵀ = flip0 := Matrix.diagonal_transpose _

theorem flip0_mul_self : flip0 * flip0 = 1 := by
  unfold flip0
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem flip0_det : flip0.det = -1 := by
  unfold flip0
  rw [Matrix.det_diagonal, Fin.prod_univ_succ]
  simp

theorem flip0_projOf (S : Finset (Fin 6)) : flip0 * projOf S * flip0 = projOf S := by
  unfold flip0 projOf
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  split_ifs <;> norm_num

theorem exists_rot_projOf (P : Matrix (Fin 6) (Fin 6) ℝ) (hS : Pᵀ = P) (hP : P * P = P) :
    ∃ (R : Matrix (Fin 6) (Fin 6) ℝ) (S : Finset (Fin 6)), Rᵀ * R = 1 ∧ R.det = 1 ∧
      P = R * projOf S * Rᵀ := by
  have hH : P.IsHermitian := by
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, hS]
  have hspec := hH.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial] at hspec
  have hUU := Unitary.coe_star_mul_self hH.eigenvectorUnitary
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at hUU
  generalize (hH.eigenvectorUnitary : Matrix (Fin 6) (Fin 6) ℝ) = U at hspec hUU
  generalize (RCLike.ofReal ∘ hH.eigenvalues : Fin 6 → ℝ) = d at hspec
  have hUU' : U * Uᵀ = 1 := mul_eq_one_comm.mp hUU
  have hDD : Matrix.diagonal d * Matrix.diagonal d = Matrix.diagonal d := by
    have h1 : Uᵀ * P * U = Matrix.diagonal d := by
      rw [hspec]
      simp only [← Matrix.mul_assoc, hUU, Matrix.one_mul]
      rw [Matrix.mul_assoc, hUU, Matrix.mul_one]
    calc Matrix.diagonal d * Matrix.diagonal d = (Uᵀ * P * U) * (Uᵀ * P * U) := by rw [h1]
      _ = Uᵀ * (P * (U * Uᵀ) * P) * U := by simp only [Matrix.mul_assoc]
      _ = Uᵀ * P * U := by rw [hUU', Matrix.mul_one, hP, Matrix.mul_assoc]
      _ = Matrix.diagonal d := h1
  have hd01 : ∀ a, d a = 0 ∨ d a = 1 := by
    intro a
    have h := congrFun (congrFun hDD a) a
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq] at h
    exact IsIdempotentElem.iff_eq_zero_or_one.mp h
  set S : Finset (Fin 6) := Finset.univ.filter fun a => d a = 1 with hSdef
  have hdiag : Matrix.diagonal d = projOf S := by
    unfold projOf
    congr 1
    funext a
    rcases hd01 a with h | h
    · have ha : a ∉ S := by simp [hSdef, h]
      rw [if_neg ha, h]
    · have ha : a ∈ S := by simp [hSdef, h]
      rw [if_pos ha, h]
  rw [hdiag] at hspec
  clear hDD hd01
  have hdet : U.det * U.det = 1 := by
    have h := congrArg Matrix.det hUU
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  rcases mul_self_eq_one_iff.mp hdet with h1 | h1
  · exact ⟨U, S, hUU, h1, hspec⟩
  · refine ⟨U * flip0, S, ?_, ?_, ?_⟩
    · rw [Matrix.transpose_mul, flip0_transpose, Matrix.mul_assoc, ← Matrix.mul_assoc Uᵀ, hUU,
        Matrix.one_mul, flip0_mul_self]
    · rw [Matrix.det_mul, h1, flip0_det]
      norm_num
    · rw [Matrix.transpose_mul, flip0_transpose]
      calc P = U * projOf S * Uᵀ := hspec
        _ = U * (flip0 * projOf S * flip0) * Uᵀ := by rw [flip0_projOf]
        _ = U * flip0 * projOf S * (flip0 * Uᵀ) := by simp only [Matrix.mul_assoc]

/-! ## The rotation lifts to an element of `SU(4)` -/

/-- The linear map of `E6` given by a matrix. -/
noncomputable def matLM (R : Matrix (Fin 6) (Fin 6) ℝ) : GroupsContinuumLaw.E6 →ₗ[ℝ] GroupsContinuumLaw.E6 :=
  ((WithLp.linearEquiv 2 ℝ (Fin 6 → ℝ)).symm : (Fin 6 → ℝ) →ₗ[ℝ] GroupsContinuumLaw.E6) ∘ₗ Matrix.toLin' R ∘ₗ
    ((WithLp.linearEquiv 2 ℝ (Fin 6 → ℝ)) : GroupsContinuumLaw.E6 →ₗ[ℝ] (Fin 6 → ℝ))

theorem matLM_apply (R : Matrix (Fin 6) (Fin 6) ℝ) (t : GroupsContinuumLaw.E6) :
    matLM R t = WithLp.toLp 2 (R *ᵥ WithLp.ofLp t) := rfl

/-- The rotation of `E6` given by an orthogonal matrix. -/
noncomputable def matLI (R : Matrix (Fin 6) (Fin 6) ℝ) (hR : Rᵀ * R = 1) :
    GroupsContinuumLaw.E6 →ₗᵢ[ℝ] GroupsContinuumLaw.E6 where
  toLinearMap := matLM R
  norm_map' t := by
    change ‖matLM R t‖ = ‖t‖
    rw [matLM_apply]
    have h : ∑ a, (R *ᵥ WithLp.ofLp t) a ^ 2 = ∑ a, (WithLp.ofLp t) a ^ 2 := by
      set v := WithLp.ofLp t
      have e1 : ∑ a, (R *ᵥ v) a ^ 2 = (R *ᵥ v) ⬝ᵥ (R *ᵥ v) := by
        simp only [dotProduct, sq]
      have e2 : ∑ a, v a ^ 2 = v ⬝ᵥ v := by
        simp only [dotProduct, sq]
      rw [e1, e2, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hR,
        Matrix.one_mulVec]
    have h2 : ‖WithLp.toLp 2 (R *ᵥ WithLp.ofLp t)‖ ^ 2 = ‖t‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
      simpa using h
    rw [← Real.sqrt_sq (norm_nonneg (WithLp.toLp 2 (R *ᵥ WithLp.ofLp t))), ← Real.sqrt_sq (norm_nonneg t), h2]

theorem matLI_apply (R : Matrix (Fin 6) (Fin 6) ℝ) (hR : Rᵀ * R = 1) (t : GroupsContinuumLaw.E6) :
    matLI R hR t = WithLp.toLp 2 (R *ᵥ WithLp.ofLp t) := rfl

theorem det_matLI (R : Matrix (Fin 6) (Fin 6) ℝ) (hR : Rᵀ * R = 1) :
    LinearMap.det (matLI R hR).toLinearMap = R.det := by
  have h : (matLI R hR).toLinearMap = matLM R := rfl
  have hc := LinearMap.det_conj (Matrix.toLin' R) (WithLp.linearEquiv 2 ℝ (Fin 6 → ℝ)).symm
  rw [LinearEquiv.symm_symm] at hc
  rw [h, matLM, hc, LinearMap.det_toLin']

/-- **Every rotation of the six lifts to an element of `SU(4)`:** for `RᵀR = 1`, `det R = 1` there is `U ∈ SU(4)`
with `U ι(z) Uᵀ = ι(Rz)` for every point `z` of the six (complex coordinates). -/
theorem lift_rot (R : Matrix (Fin 6) (Fin 6) ℝ) (hR : Rᵀ * R = 1) (hdet : R.det = 1) :
    ∃ U : GroupsContinuumLaw.SU4, ∀ z : Fin 6 → ℂ,
      (U : Matrix Four Four ℂ) * GroupsContinuumLaw.ιC z * (U : Matrix Four Four ℂ)ᵀ =
        GroupsContinuumLaw.ιC (R.map ((↑) : ℝ → ℂ) *ᵥ z) := by
  set φ : GroupsContinuumLaw.E6 ≃ₗᵢ[ℝ] GroupsContinuumLaw.E6 := (matLI R hR).toLinearIsometryEquiv rfl with hφ
  have hφdet : LinearMap.det φ.toLinearMap = 1 := by
    have e : φ.toLinearMap = (matLI R hR).toLinearMap := by
      apply LinearMap.ext; intro t; rfl
    rw [e, det_matLI, hdet]
  obtain ⟨U, hU⟩ := GroupsContinuumLaw.rot6_onto φ hφdet
  refine ⟨U, fun z => ?_⟩
  have hreal : ∀ t : Fin 6 → ℝ, (U : Matrix Four Four ℂ) * GroupsContinuumLaw.ιC (fun a => ((t a : ℝ) : ℂ)) *
      (U : Matrix Four Four ℂ)ᵀ = GroupsContinuumLaw.ιC (fun a => (((R *ᵥ t) a : ℝ) : ℂ)) := by
    intro t
    have h1 := GroupsContinuumLaw.ι6_rot6 U (WithLp.toLp 2 t)
    have h2 : GroupsContinuumLaw.rot6V U (WithLp.toLp 2 t) = φ (WithLp.toLp 2 t) := by
      rw [← GroupsContinuumLaw.rot6Hom_apply, hU]
    rw [h2] at h1
    exact h1.symm
  have hz : z = (fun a => (((fun b => (z b).re) a : ℝ) : ℂ)) +
      Complex.I • (fun a => (((fun b => (z b).im) a : ℝ) : ℂ)) := by
    funext a
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm]
    exact (Complex.re_add_im (z a)).symm
  have hRz : R.map ((↑) : ℝ → ℂ) *ᵥ z = (fun a => (((R *ᵥ fun b => (z b).re) a : ℝ) : ℂ)) +
      Complex.I • (fun a => (((R *ᵥ fun b => (z b).im) a : ℝ) : ℂ)) := by
    funext a
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    conv_lhs => rw [← Complex.re_add_im (z b)]
    ring
  rw [hRz]
  conv_lhs => rw [hz]
  rw [GroupsContinuumLaw.ιC_add, Matrix.mul_add, Matrix.add_mul, ιC_smul, Matrix.mul_smul, Matrix.smul_mul,
    hreal, hreal, GroupsContinuumLaw.ιC_add, ιC_smul]

/-! ## The half and the action under a rotation -/

theorem halfOf_conj (P R : Matrix (Fin 6) (Fin 6) ℝ) (hR : Rᵀ * R = 1) :
    halfOf (R * P * Rᵀ) = R.map ((↑) : ℝ → ℂ) * halfOf P * Rᵀ.map ((↑) : ℝ → ℂ) := by
  have hRR : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  have hm : R.map ((↑) : ℝ → ℂ) * Rᵀ.map ((↑) : ℝ → ℂ) = 1 := by
    rw [← map_ofReal_mul, hRR]
    ext i j
    simp [Matrix.one_apply]
    split_ifs <;> simp
  simp only [halfOf, map_ofReal_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul,
    Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, hm]

theorem act_conj (U : GroupsContinuumLaw.SU4) (X A : Matrix Four Four ℂ) :
    act ((U : Matrix Four Four ℂ) * X * (U : Matrix Four Four ℂ)⁻¹)
        ((U : Matrix Four Four ℂ) * A * (U : Matrix Four Four ℂ)ᵀ) =
      (U : Matrix Four Four ℂ) * act X A * (U : Matrix Four Four ℂ)ᵀ := by
  have hdet : IsUnit (U : Matrix Four Four ℂ).det := by
    rw [(Matrix.mem_specialUnitaryGroup_iff.mp U.2).2]; exact isUnit_one
  have hinv : (U : Matrix Four Four ℂ)⁻¹ * (U : Matrix Four Four ℂ) = 1 :=
    Matrix.nonsing_inv_mul _ hdet
  have hT : (U : Matrix Four Four ℂ)ᵀ * ((U : Matrix Four Four ℂ)⁻¹)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hinv, Matrix.transpose_one]
  simp only [act, Matrix.transpose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  congr 2
  · rw [← Matrix.mul_assoc (U : Matrix Four Four ℂ)⁻¹, hinv, Matrix.one_mul]
  · rw [← Matrix.mul_assoc ((U : Matrix Four Four ℂ)ᵀ), hT, Matrix.one_mul]

/-- `q_{RPRᵀ}(ℝ⁶)` is the turned `q_P(ℝ⁶)`. -/
theorem halfSix_conj (P R : Matrix (Fin 6) (Fin 6) ℝ) (hR : Rᵀ * R = 1) (U : GroupsContinuumLaw.SU4)
    (hU : ∀ z : Fin 6 → ℂ, (U : Matrix Four Four ℂ) * GroupsContinuumLaw.ιC z * (U : Matrix Four Four ℂ)ᵀ =
      GroupsContinuumLaw.ιC (R.map ((↑) : ℝ → ℂ) *ᵥ z)) (A : Matrix Four Four ℂ) :
    A ∈ halfSix (R * P * Rᵀ) ↔ ∃ B ∈ halfSix P,
      A = (U : Matrix Four Four ℂ) * B * (U : Matrix Four Four ℂ)ᵀ := by
  have hcast : ∀ t : Fin 6 → ℝ, (Rᵀ.map ((↑) : ℝ → ℂ)) *ᵥ (fun a => ((t a : ℝ) : ℂ)) =
      fun a => (((Rᵀ *ᵥ t) a : ℝ) : ℂ) := by
    intro t; funext a
    simp [Matrix.mulVec, dotProduct, Matrix.map_apply]
  have hcast' : ∀ t : Fin 6 → ℝ, (R.map ((↑) : ℝ → ℂ)) *ᵥ (fun a => ((t a : ℝ) : ℂ)) =
      fun a => (((R *ᵥ t) a : ℝ) : ℂ) := by
    intro t; funext a
    simp [Matrix.mulVec, dotProduct, Matrix.map_apply]
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨_, ⟨Rᵀ *ᵥ t, rfl⟩, ?_⟩
    rw [hU, halfOf_conj P R hR, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcast]
  · rintro ⟨B, ⟨t, rfl⟩, rfl⟩
    refine ⟨R *ᵥ t, ?_⟩
    have hRt : Rᵀ *ᵥ (R *ᵥ t) = t := by rw [Matrix.mulVec_mulVec, hR, Matrix.one_mulVec]
    rw [hU, halfOf_conj P R hR, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcast, hRt]

/-- **Definition 15 under a rotation:** `X` is a generator of the real form of `P` exactly when `UXU⁻¹`
is one of `RPRᵀ`. -/
theorem realFormAlg_conj (P R : Matrix (Fin 6) (Fin 6) ℝ) (hR : Rᵀ * R = 1) (U : GroupsContinuumLaw.SU4)
    (hU : ∀ z : Fin 6 → ℂ, (U : Matrix Four Four ℂ) * GroupsContinuumLaw.ιC z * (U : Matrix Four Four ℂ)ᵀ =
      GroupsContinuumLaw.ιC (R.map ((↑) : ℝ → ℂ) *ᵥ z)) (X : Matrix Four Four ℂ) :
    (U : Matrix Four Four ℂ) * X * (U : Matrix Four Four ℂ)⁻¹ ∈ realFormAlg (R * P * Rᵀ) ↔
      X ∈ realFormAlg P := by
  have hdet : IsUnit (U : Matrix Four Four ℂ).det := by
    rw [(Matrix.mem_specialUnitaryGroup_iff.mp U.2).2]; exact isUnit_one
  have hinv : (U : Matrix Four Four ℂ)⁻¹ * (U : Matrix Four Four ℂ) = 1 :=
    Matrix.nonsing_inv_mul _ hdet
  have hinv' : (U : Matrix Four Four ℂ) * (U : Matrix Four Four ℂ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hdet
  have htr : ((U : Matrix Four Four ℂ) * X * (U : Matrix Four Four ℂ)⁻¹).trace = X.trace := by
    rw [Matrix.trace_mul_cycle, hinv, Matrix.one_mul]
  have hUT : IsUnit ((U : Matrix Four Four ℂ)ᵀ).det := by
    rw [Matrix.det_transpose, (Matrix.mem_specialUnitaryGroup_iff.mp U.2).2]; exact isUnit_one
  have hcancel : ∀ B C : Matrix Four Four ℂ,
      (U : Matrix Four Four ℂ) * B * (U : Matrix Four Four ℂ)ᵀ =
        (U : Matrix Four Four ℂ) * C * (U : Matrix Four Four ℂ)ᵀ → B = C := by
    intro B C h
    have h1 := congrArg (fun M => (U : Matrix Four Four ℂ)⁻¹ * M * ((U : Matrix Four Four ℂ)ᵀ)⁻¹) h
    simp only [← Matrix.mul_assoc, hinv, Matrix.one_mul] at h1
    rwa [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hUT, Matrix.mul_one, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ hUT, Matrix.mul_one] at h1
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨htr ▸ h1, fun B hB => ?_⟩
    have hA : (U : Matrix Four Four ℂ) * B * (U : Matrix Four Four ℂ)ᵀ ∈ halfSix (R * P * Rᵀ) :=
      (halfSix_conj P R hR U hU _).mpr ⟨B, hB, rfl⟩
    have h3 := h2 _ hA
    rw [act_conj] at h3
    obtain ⟨C, hC, hC'⟩ := (halfSix_conj P R hR U hU _).mp h3
    rw [hcancel _ _ hC']
    exact hC
  · rintro ⟨h1, h2⟩
    refine ⟨htr.symm ▸ h1, fun A hA => ?_⟩
    obtain ⟨B, hB, rfl⟩ := (halfSix_conj P R hR U hU _).mp hA
    rw [act_conj]
    exact (halfSix_conj P R hR U hU _).mpr ⟨_, h2 B hB, rfl⟩

/-- Kept and moved under the rotation: `θ_{RPRᵀ} = Rθ_PRᵀ`. -/
theorem signOf_conj (P R : Matrix (Fin 6) (Fin 6) ℝ) (hR : Rᵀ * R = 1) :
    signOf (R * P * Rᵀ) = R * signOf P * Rᵀ := by
  have hRR : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  simp only [signOf, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
    hRR]

theorem rconj_mul (R A B : Matrix (Fin 6) (Fin 6) ℝ) (hR : Rᵀ * R = 1) :
    (R * A * Rᵀ) * (R * B * Rᵀ) = R * (A * B) * Rᵀ := by
  calc (R * A * Rᵀ) * (R * B * Rᵀ) = R * A * (Rᵀ * R) * B * Rᵀ := by simp only [Matrix.mul_assoc]
    _ = R * (A * B) * Rᵀ := by rw [hR, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem rconj_cancel (R A B : Matrix (Fin 6) (Fin 6) ℝ) (hR : Rᵀ * R = 1)
    (h : R * A * Rᵀ = R * B * Rᵀ) : A = B := by
  have hRR : R * Rᵀ = 1 := mul_eq_one_comm.mp hR
  have h1 : Rᵀ * (R * A * Rᵀ) * R = Rᵀ * (R * B * Rᵀ) * R := by rw [h]
  calc A = Rᵀ * (R * A * Rᵀ) * R := by
        simp only [← Matrix.mul_assoc, hR, Matrix.one_mul]; rw [Matrix.mul_assoc, hR, Matrix.mul_one]
    _ = Rᵀ * (R * B * Rᵀ) * R := h1
    _ = B := by
        simp only [← Matrix.mul_assoc, hR, Matrix.one_mul]; rw [Matrix.mul_assoc, hR, Matrix.mul_one]

theorem keptBy_conj (P R X : Matrix (Fin 6) (Fin 6) ℝ) (hR : Rᵀ * R = 1) :
    KeptBy (R * P * Rᵀ) (R * X * Rᵀ) ↔ KeptBy P X := by
  unfold KeptBy
  rw [signOf_conj P R hR, rconj_mul R _ _ hR, rconj_mul R _ _ hR]
  exact ⟨fun h => rconj_cancel R _ _ hR h, fun h => by rw [h]⟩

theorem movedBy_conj (P R X : Matrix (Fin 6) (Fin 6) ℝ) (hR : Rᵀ * R = 1) :
    MovedBy (R * P * Rᵀ) (R * X * Rᵀ) ↔ MovedBy P X := by
  unfold MovedBy
  rw [signOf_conj P R hR, rconj_mul R _ _ hR, rconj_mul R _ _ hR]
  have hneg : ∀ M : Matrix (Fin 6) (Fin 6) ℝ, -(R * M * Rᵀ) = R * (-M) * Rᵀ := by
    intro M; rw [Matrix.mul_neg, Matrix.neg_mul]
  rw [hneg]
  exact ⟨fun h => rconj_cancel R _ _ hR h, fun h => by rw [h]⟩

/-- **The real form of every division** is the turned real form of a coordinate division: for every
symmetric projector `P` of the six there are a set `S` and a rotation `U ∈ SU(4)` with
`X ∈ realFormAlg P ↔ U⁻¹XU ∈ realFormAlg (P_S)`, and `realFormAlg (P_S)` is the real span of the
fifteen `realGen6 S`. -/
theorem realFormAlg_every_division (P : Matrix (Fin 6) (Fin 6) ℝ) (hS : Pᵀ = P) (hP : P * P = P) :
    ∃ (S : Finset (Fin 6)) (U : GroupsContinuumLaw.SU4), ∀ X : Matrix Four Four ℂ,
      X ∈ realFormAlg P ↔
        (U : Matrix Four Four ℂ)⁻¹ * X * (U : Matrix Four Four ℂ) ∈
          (Submodule.span ℝ (Set.range (realGen6 S)) : Set (Matrix Four Four ℂ)) := by
  obtain ⟨R, S, hR, hdet, hPR⟩ := exists_rot_projOf P hS hP
  obtain ⟨U, hU⟩ := lift_rot R hR hdet
  refine ⟨S, U, fun X => ?_⟩
  have hd : IsUnit (U : Matrix Four Four ℂ).det := by
    rw [(Matrix.mem_specialUnitaryGroup_iff.mp U.2).2]; exact isUnit_one
  have hX : (U : Matrix Four Four ℂ) * ((U : Matrix Four Four ℂ)⁻¹ * X * (U : Matrix Four Four ℂ)) *
      (U : Matrix Four Four ℂ)⁻¹ = X := by
    simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]
    rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
  rw [← realFormAlg_ofSet, ← realFormAlg_conj (projOf S) R hR U hU, hX, ← hPR]

end Geometry

open Comparison.System.Geometry


end Comparison.System
