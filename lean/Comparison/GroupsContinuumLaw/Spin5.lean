import Comparison.Elements.Observables
import Comparison.Elements.KeepL
import Comparison.Elements.SixDirections

/-!
# `Sp(2) → SO(5)` onto, with kernel `±1` (Prop. 6)

`Sp(2)` is the group of unitary rotations that keep the join, `U J Uᵀ = J` (equivalently `UΘ = ΘU`,
`Elements/SixDirections.lean`: `keeps_partner_iff`). For a vector `x` of `Q = ℝ⁵` write
`γ(x) = Σ_s x_s γ_s`. Proved here:

* `sp2_conj_line`: **`U γ(x) U† = γ(R_U x)`** with `R_U x` the coordinates of `U γ(x) U†`
  (`Elements/Observables.lean`: `eq_sum_coord`); `rotE U` is a linear isometry of `ℝ⁵` and
  `rotHom : Sp(2) →* O(5)` is a homomorphism of groups.
* `rot_lineElt`: for a unit vector `v`, `γ(v) ∈ Sp(2)` and `R_{γ(v)} = −ρ_v`, minus the reflection
  in `v^⊥`; `plane_turn`: `c + s γ_aγ_b` (`c² + s² = 1`) turns `γ_a` into `(c² − s²)γ_a − 2cs γ_b`.
* `rot_det`: **`det R_U = 1`** (Cartan–Dieudonné, Mathlib's `reflections_generate_dim`, and
  `γ₀γ₁γ₂γ₃γ₄ = 1`, which forbids `R_U = −1`);
* `rot_onto`: **every rotation of determinant one is some `R_U`**;
* `rot_ker`: **`R_U = 1` iff `U = ±1`**; `scalar_of_comm`: what commutes with the five directions is a
  number.
-/

namespace Comparison.GroupsContinuumLaw

open Matrix hiding J
open Complex

noncomputable section

/-- The five directions' space `Q = ℝ⁵`. -/
abbrev E5 := EuclideanSpace ℝ (Fin 5)

/-! ## The line of a vector -/

/-- `γ(x) = Σ_s x_s γ_s`. -/
def gE (x : E5) : Matrix Four Four ℂ := ∑ s, ((x s : ℝ) : ℂ) • γ s

theorem gE_toLp (f : Fin 5 → ℝ) : gE (WithLp.toLp 2 f) = ∑ s, ((f s : ℝ) : ℂ) • γ s := by
  simp [gE]

theorem gE_add (x y : E5) : gE (x + y) = gE x + gE y := by
  simp [gE, add_smul, Finset.sum_add_distrib]

theorem gE_smul (c : ℝ) (x : E5) : gE (c • x) = (c : ℂ) • gE x := by
  simp only [gE, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul, Finset.smul_sum, smul_smul]

theorem gE_neg (x : E5) : gE (-x) = -gE x := by
  simp [gE, Finset.sum_neg_distrib]

theorem gE_sub (x y : E5) : gE (x - y) = gE x - gE y := by
  rw [sub_eq_add_neg, gE_add, gE_neg, ← sub_eq_add_neg]

theorem coord_gE (x : E5) : coord (gE x) = x.ofLp := coord_sum x.ofLp

theorem gE_injective : Function.Injective gE := by
  intro x y h
  have := congrArg coord h
  rw [coord_gE, coord_gE] at this
  exact WithLp.ofLp_injective 2 this

theorem gE_isDistinction (x : E5) : IsDistinction (gE x) := sum_isDistinction x.ofLp

theorem gE_hermitian (x : E5) : (gE x)ᴴ = gE x := (gE_isDistinction x).1

theorem gE_sq (x : E5) : gE x * gE x = ((∑ s, x s ^ 2 : ℝ) : ℂ) • (1 : Matrix Four Four ℂ) := by
  rw [gE, sq_sum]
  push_cast
  try rfl

theorem gE_anti (x y : E5) :
    gE x * gE y + gE y * gE x = ((2 * ∑ s, x s * y s : ℝ) : ℂ) • (1 : Matrix Four Four ℂ) := by
  have hxy := gE_sq (x + y)
  rw [gE_add] at hxy
  have e : gE x * gE y + gE y * gE x =
      (gE x + gE y) * (gE x + gE y) - gE x * gE x - gE y * gE y := by noncomm_ring
  rw [e, hxy, gE_sq, gE_sq, ← sub_smul, ← sub_smul]
  congr 1
  simp only [PiLp.add_apply]
  push_cast
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

theorem gE_single (s : Fin 5) : gE (EuclideanSpace.single s 1) = γ s := by
  simp [gE, PiLp.single_apply]

/-! ## The ten rotations -/

/-- **`Sp(2)`: the unitary rotations that keep the join**, `U J Uᵀ = J`. -/
def Sp2 : Subgroup (Matrix.unitaryGroup Four ℂ) where
  carrier := {U | (U : Matrix Four Four ℂ) * J * (U : Matrix Four Four ℂ)ᵀ = J}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    change (a : Matrix Four Four ℂ) * (b : Matrix Four Four ℂ) * J *
      ((a : Matrix Four Four ℂ) * (b : Matrix Four Four ℂ))ᵀ = J
    rw [Matrix.transpose_mul]
    calc (a : Matrix Four Four ℂ) * (b : Matrix Four Four ℂ) * J *
          ((b : Matrix Four Four ℂ)ᵀ * (a : Matrix Four Four ℂ)ᵀ)
        = (a : Matrix Four Four ℂ) * ((b : Matrix Four Four ℂ) * J * (b : Matrix Four Four ℂ)ᵀ) *
            (a : Matrix Four Four ℂ)ᵀ := by
          simp only [Matrix.mul_assoc]
      _ = J := by rw [hb, ha]
  one_mem' := by
    change (1 : Matrix Four Four ℂ) * J * (1 : Matrix Four Four ℂ)ᵀ = J
    simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_ofPred_eq] at ha ⊢
    rw [Matrix.UnitaryGroup.inv_val]
    have h1 : star (a : Matrix Four Four ℂ) * a = 1 := Matrix.UnitaryGroup.star_mul_self a
    have h2 : (a : Matrix Four Four ℂ)ᵀ * (star (a : Matrix Four Four ℂ))ᵀ = 1 := by
      rw [← Matrix.transpose_mul, h1, Matrix.transpose_one]
    calc star (a : Matrix Four Four ℂ) * J * (star (a : Matrix Four Four ℂ))ᵀ
        = star (a : Matrix Four Four ℂ) *
            ((a : Matrix Four Four ℂ) * J * (a : Matrix Four Four ℂ)ᵀ) *
            (star (a : Matrix Four Four ℂ))ᵀ := by rw [ha]
      _ = (star (a : Matrix Four Four ℂ) * (a : Matrix Four Four ℂ)) * J *
            ((a : Matrix Four Four ℂ)ᵀ * (star (a : Matrix Four Four ℂ))ᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = J := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]

/-- The matrix of an element of `Sp(2)`. -/
abbrev mat (U : Sp2) : Matrix Four Four ℂ := ((U : Matrix.unitaryGroup Four ℂ) : Matrix Four Four ℂ)

theorem mat_mul (U V : Sp2) : mat (U * V) = mat U * mat V := rfl

theorem mat_one : mat 1 = 1 := rfl

theorem mat_inv (U : Sp2) : mat U⁻¹ = star (mat U) := rfl

theorem sp2_unitary (U : Sp2) : mat U * star (mat U) = 1 :=
  Matrix.mem_unitaryGroup_iff.mp (U : Matrix.unitaryGroup Four ℂ).2

theorem sp2_unitary' (U : Sp2) : star (mat U) * mat U = 1 :=
  Matrix.UnitaryGroup.star_mul_self _

theorem sp2_keepJ (U : Sp2) : mat U * J * (mat U)ᵀ = J := U.2

/-- **`Sp(2) = {U : UΘ = ΘU}`.** -/
theorem sp2_partner (U : Sp2) : ∀ v, mat U *ᵥ Θ v = Θ (mat U *ᵥ v) :=
  (keeps_partner_iff _ (by rw [← Matrix.star_eq_conjTranspose]; exact sp2_unitary U)).2 U.2

/-- **The ten rotations have determinant one.** -/
theorem sp2_det (U : Sp2) : (mat U).det = 1 := det_eq_one_of_keeps_J _ U.2

/-- A rotation of `Sp(2)` carries a distinction to a distinction. -/
theorem conj_isDistinction (U : Sp2) {a : Matrix Four Four ℂ} (ha : IsDistinction a) :
    IsDistinction (mat U * a * star (mat U)) := by
  obtain ⟨h1, h2, h3⟩ := ha
  refine ⟨?_, ?_, ?_⟩
  · simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, h1, Matrix.mul_assoc]
  · rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, sp2_unitary', Matrix.one_mul, h2]
  · rw [← commutes_Θ_iff] at h3 ⊢
    intro v
    have hU := sp2_partner U
    have hUi := sp2_partner U⁻¹
    rw [mat_inv] at hUi
    simp only [← Matrix.mulVec_mulVec]
    rw [hUi, h3, hU]

/-! ## The rotation of a rotation -/

/-- `R_U x`: the coordinates of `U γ(x) U†`. -/
def rotV (U : Sp2) (x : E5) : E5 := WithLp.toLp 2 (coord (mat U * gE x * star (mat U)))

/-- **`U γ(x) U† = γ(R_U x)`.** -/
theorem sp2_conj_line (U : Sp2) (x : E5) : gE (rotV U x) = mat U * gE x * star (mat U) := by
  rw [rotV, gE_toLp]
  exact (eq_sum_coord _ (conj_isDistinction U (gE_isDistinction x))).symm

theorem rotV_add (U : Sp2) (x y : E5) : rotV U (x + y) = rotV U x + rotV U y := by
  apply gE_injective
  rw [gE_add, sp2_conj_line, sp2_conj_line, sp2_conj_line, gE_add, Matrix.mul_add, Matrix.add_mul]

theorem rotV_smul (U : Sp2) (c : ℝ) (x : E5) : rotV U (c • x) = c • rotV U x := by
  apply gE_injective
  rw [gE_smul, sp2_conj_line, sp2_conj_line, gE_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem rotV_sumsq (U : Sp2) (x : E5) : ∑ s, rotV U x s ^ 2 = ∑ s, x s ^ 2 := by
  have h := gE_sq (rotV U x)
  rw [sp2_conj_line] at h
  have e : mat U * gE x * star (mat U) * (mat U * gE x * star (mat U)) =
      mat U * (gE x * gE x) * star (mat U) := by
    calc mat U * gE x * star (mat U) * (mat U * gE x * star (mat U))
        = mat U * gE x * (star (mat U) * mat U) * gE x * star (mat U) := by
          simp only [Matrix.mul_assoc]
      _ = mat U * (gE x * gE x) * star (mat U) := by
          rw [sp2_unitary', Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [e, gE_sq, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, sp2_unitary] at h
  have h1 : (1 : Matrix Four Four ℂ) ≠ 0 := one_ne_zero
  have := smul_left_injective ℂ h1 h
  exact_mod_cast this.symm

theorem rotV_norm (U : Sp2) (x : E5) : ‖rotV U x‖ = ‖x‖ := by
  have h : ‖rotV U x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, rotV_sumsq]
  rw [← Real.sqrt_sq (norm_nonneg (rotV U x)), ← Real.sqrt_sq (norm_nonneg x), h]

/-- `R_U` as a linear isometry. -/
def rotLI (U : Sp2) : E5 →ₗᵢ[ℝ] E5 where
  toFun := rotV U
  map_add' := rotV_add U
  map_smul' := fun c x => by rw [RingHom.id_apply]; exact rotV_smul U c x
  norm_map' := rotV_norm U

/-- `R_U` as an element of `O(5)`. -/
def rotE (U : Sp2) : E5 ≃ₗᵢ[ℝ] E5 := (rotLI U).toLinearIsometryEquiv rfl

theorem rotE_apply (U : Sp2) (x : E5) : rotE U x = rotV U x := rfl

theorem rotV_one (x : E5) : rotV 1 x = x := by
  apply gE_injective
  rw [sp2_conj_line, mat_one]
  simp

theorem rotV_mul (U V : Sp2) (x : E5) : rotV (U * V) x = rotV U (rotV V x) := by
  apply gE_injective
  rw [sp2_conj_line, sp2_conj_line, sp2_conj_line, mat_mul, star_mul]
  simp only [Matrix.mul_assoc]

/-- **`U ↦ R_U` is a homomorphism `Sp(2) → O(5)`.** -/
def rotHom : Sp2 →* (E5 ≃ₗᵢ[ℝ] E5) where
  toFun := rotE
  map_one' := LinearIsometryEquiv.ext fun x => by
    rw [rotE_apply, rotV_one]; rfl
  map_mul' := fun U V => LinearIsometryEquiv.ext fun x => by
    rw [rotE_apply, rotV_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply, rotE_apply,
      rotE_apply]

theorem rotHom_apply (U : Sp2) (x : E5) : rotHom U x = rotV U x := rfl

/-! ## A unit line is a rotation, and it reflects -/

theorem inner_E5 (x y : E5) : inner ℝ x y = ∑ s, x s * y s := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, mul_comm]

theorem norm_sq_E5 (x : E5) : ‖x‖ ^ 2 = ∑ s, x s ^ 2 := EuclideanSpace.real_norm_sq_eq x

/-- The reflection in `u^⊥`: `ρ_u x = x − (2⟨u, x⟩/‖u‖²) u`. -/
theorem refl_apply (u x : E5) :
    (ℝ ∙ u)ᗮ.reflection x = x - (2 * (inner ℝ u x / ‖u‖ ^ 2)) • u := by
  rw [Submodule.reflection_orthogonal_apply, Submodule.reflection_singleton_apply]
  simp only [RCLike.ofReal_real_eq_id, id]
  rw [neg_sub, two_smul, two_mul, add_smul]

/-- A unit line `γ(v)` as an element of `Sp(2)`. -/
def lineElt (v : E5) (hv : ∑ s, v s ^ 2 = 1) : Sp2 :=
  ⟨⟨gE v, by
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, gE_hermitian, gE_sq, hv]
      simp⟩, by
    show gE v * J * (gE v)ᵀ = J
    have hU : gE v * (gE v)ᴴ = 1 := by rw [gE_hermitian, gE_sq, hv]; simp
    exact (keeps_partner_iff _ hU).1 ((commutes_Θ_iff _).2 (gE_isDistinction v).2.2)⟩

theorem mat_lineElt (v : E5) (hv : ∑ s, v s ^ 2 = 1) : mat (lineElt v hv) = gE v := rfl

/-- **A unit line acts on the five directions as minus the reflection in its perpendicular.** -/
theorem rot_lineElt (v : E5) (hv : ∑ s, v s ^ 2 = 1) (x : E5) :
    rotV (lineElt v hv) x = -((ℝ ∙ v)ᗮ.reflection x) := by
  apply gE_injective
  have hn : ‖v‖ ^ 2 = 1 := by rw [norm_sq_E5, hv]
  rw [sp2_conj_line, mat_lineElt, refl_apply, hn, div_one, inner_E5, gE_neg, gE_sub, gE_smul,
    Matrix.star_eq_conjTranspose, gE_hermitian]
  have ha := gE_anti v x
  have hs := gE_sq v
  rw [hv] at hs
  have e : gE v * gE x * gE v = (gE v * gE x + gE x * gE v) * gE v - gE x * (gE v * gE v) := by
    noncomm_ring
  rw [e, ha, hs]
  simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
  push_cast
  simp only [one_smul]
  abel

/-- **The generator `½γ_aγ_b` turns the plane `(a, b)`:** `c + sγ_aγ_b` carries `γ_a` to
`(c² − s²)γ_a − 2cs γ_b`. -/
theorem plane_turn (a b : Fin 5) (hab : a ≠ b) (c s : ℂ) :
    (c • (1 : Matrix Four Four ℂ) + s • (γ a * γ b)) * γ a *
        (c • (1 : Matrix Four Four ℂ) - s • (γ a * γ b)) =
      (c ^ 2 - s ^ 2) • γ a - (2 * c * s) • γ b := by
  have h1 : γ a * γ b * γ a = -γ b := by
    rw [γ_anticomm hab, Matrix.neg_mul, Matrix.mul_assoc, γ_mul_self, Matrix.mul_one]
  have h2 : γ a * (γ a * γ b) = γ b := by rw [← Matrix.mul_assoc, γ_mul_self, Matrix.one_mul]
  have h3 : γ a * γ b * γ a * (γ a * γ b) = -(γ b * γ a * γ b) := by
    rw [h1, Matrix.neg_mul, Matrix.mul_assoc]
  have h4 : γ b * γ a * γ b = -γ a := by
    rw [γ_anticomm (Ne.symm hab), Matrix.neg_mul, Matrix.mul_assoc, γ_mul_self, Matrix.mul_one]
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, smul_sub, smul_smul]
  rw [h2, h3, h4, h1]
  module

/-! ## What commutes with the five directions is a number -/

theorem comm_obs (M : Matrix Four Four ℂ) (h : ∀ s, γ s * M = M * γ s) (k : Fin 16) :
    Commute (obs k) M := by
  have hc : ∀ s, Commute (γ s) M := fun s => h s
  have hp : ∀ a b, Commute (I • (γ a * γ b)) M := fun a b =>
    ((hc a).mul_left (hc b)).smul_left I
  fin_cases k
  exacts [Commute.one_left M, hc 0, hc 1, hc 2, hc 3, hc 4, hp 0 1, hp 0 2, hp 0 3, hp 0 4,
    hp 1 2, hp 1 3, hp 1 4, hp 2 3, hp 2 4, hp 3 4]

theorem commute_all (M : Matrix Four Four ℂ) (h : ∀ s, γ s * M = M * γ s)
    (A : Matrix Four Four ℂ) : Commute A M := by
  have hA : A ∈ Submodule.span ℂ (Set.range obs) := by rw [obs_span]; trivial
  induction hA using Submodule.span_induction with
  | mem x hx => obtain ⟨k, rfl⟩ := hx; exact comm_obs M h k
  | zero => exact Commute.zero_left M
  | add x y _ _ hx hy => exact hx.add_left hy
  | smul a x _ hx => exact hx.smul_left a

/-- **What commutes with the five directions is a number.** -/
theorem scalar_of_comm (M : Matrix Four Four ℂ) (h : ∀ s, γ s * M = M * γ s) :
    ∃ c : ℂ, M = c • (1 : Matrix Four Four ℂ) := by
  obtain ⟨c, hc⟩ := Matrix.mem_range_scalar_iff_commute_single'.2
    (fun i j => commute_all M h _)
  refine ⟨c, ?_⟩
  rw [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

/-! ## The kernel -/

theorem conj_gamma_of_rot (U : Sp2) (hU : ∀ x, rotV U x = x) (s : Fin 5) :
    γ s * mat U = mat U * γ s := by
  have h := sp2_conj_line U (EuclideanSpace.single s 1)
  rw [hU, gE_single] at h
  calc γ s * mat U = mat U * γ s * star (mat U) * mat U := by rw [← h]
    _ = mat U * γ s := by rw [Matrix.mul_assoc, sp2_unitary', Matrix.mul_one]

/-- **The kernel: `R_U = 1` exactly when `U = ±1`.** -/
theorem rot_ker (U : Sp2) : rotHom U = 1 ↔ mat U = 1 ∨ mat U = -1 := by
  constructor
  · intro h
    have hU : ∀ x, rotV U x = x := fun x => by
      have := congrArg (fun e : E5 ≃ₗᵢ[ℝ] E5 => e x) h
      simpa [rotHom_apply] using this
    obtain ⟨c, hc⟩ := scalar_of_comm (mat U) (conj_gamma_of_rot U hU)
    have hJ := sp2_keepJ U
    simp only [hc, Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul] at hJ
    have hJ0 : J (0, 0) (0, 1) = 1 := by simp [J, ε]
    have hc2 : c * c = 1 := by
      have := congrFun (congrFun hJ (0, 0)) (0, 1)
      simp only [Matrix.smul_apply, smul_eq_mul, hJ0, mul_one] at this
      exact this
    have : (c - 1) * (c + 1) = 0 := by linear_combination hc2
    rcases mul_eq_zero.1 this with h1 | h1
    · left; rw [hc, sub_eq_zero.1 h1, one_smul]
    · right; rw [hc, eq_neg_of_add_eq_zero_left h1, neg_smul, one_smul]
  · intro h
    refine LinearIsometryEquiv.ext fun x => ?_
    rw [rotHom_apply]
    apply gE_injective
    rw [sp2_conj_line]
    rcases h with h | h <;> rw [h] <;> simp

/-! ## The determinant -/

/-- A rotation that reverses every line does not exist: `γ₀γ₁γ₂γ₃γ₄ = 1`. -/
theorem no_reversal (V : Sp2) (hV : ∀ x, rotV V x = -x) : False := by
  have hs : ∀ s, mat V * γ s = -(γ s * mat V) := by
    intro s
    have h := sp2_conj_line V (EuclideanSpace.single s 1)
    rw [hV, gE_neg, gE_single] at h
    calc mat V * γ s = mat V * γ s * star (mat V) * mat V := by
          rw [Matrix.mul_assoc _ (star _), sp2_unitary', Matrix.mul_one]
      _ = -(γ s * mat V) := by rw [← h, Matrix.neg_mul]
  have e : ∀ s (X : Matrix Four Four ℂ), mat V * (γ s * X) = -(γ s * (mat V * X)) := by
    intro s X
    rw [← Matrix.mul_assoc, hs, Matrix.neg_mul, Matrix.mul_assoc]
  have hp : γ 0 * (γ 1 * (γ 2 * (γ 3 * γ 4))) = 1 := by
    rw [← γ_prod]; simp only [Matrix.mul_assoc]
  have key : mat V = -mat V := by
    calc mat V = mat V * (γ 0 * (γ 1 * (γ 2 * (γ 3 * γ 4)))) := by
          rw [hp, Matrix.mul_one]
      _ = -(γ 0 * (γ 1 * (γ 2 * (γ 3 * (γ 4 * mat V))))) := by
          rw [e, e, e, e, hs]
          simp only [Matrix.mul_neg, neg_neg]
      _ = -mat V := by
          rw [show γ 0 * (γ 1 * (γ 2 * (γ 3 * (γ 4 * mat V)))) =
            (γ 0 * (γ 1 * (γ 2 * (γ 3 * γ 4)))) * mat V by simp only [Matrix.mul_assoc],
            hp, Matrix.one_mul]
  have h0 : mat V = 0 := by
    have h2 : (2 : ℂ) • mat V = 0 := by
      rw [two_smul]; nth_rewrite 2 [key]; exact add_neg_cancel _
    exact (smul_eq_zero.1 h2).resolve_left two_ne_zero
  have := sp2_unitary V
  rw [h0, Matrix.zero_mul] at this
  exact zero_ne_one this

/-- The reflections in hyperplanes. -/
def refl (v : E5) : E5 ≃ₗᵢ[ℝ] E5 := (ℝ ∙ v)ᗮ.reflection

theorem det_refl (v : E5) : LinearMap.det (refl v).toLinearMap = if v = 0 then 1 else -1 := by
  rw [refl, Submodule.det_reflection, Submodule.orthogonal_orthogonal]
  split_ifs with hv
  · subst hv
    rw [Submodule.finrank_eq_zero.2 (by simp : (ℝ ∙ (0 : E5)) = ⊥), pow_zero]
  · rw [finrank_span_singleton hv, pow_one]

/-- The number of nonzero vectors of a list. -/
def nz (l : List E5) : ℕ := l.countP (fun v => v ≠ 0)

/-- **Every product of reflections is `±R_W`** for some `W ∈ Sp(2)`, with sign `(−1)^{nz}`. -/
theorem realize (l : List E5) :
    ∃ W : Sp2, ∀ x, (l.map refl).prod x = ((-1 : ℝ) ^ nz l) • rotV W x := by
  induction l with
  | nil => exact ⟨1, fun x => by simp [nz, rotV_one]⟩
  | cons v l ih =>
    obtain ⟨W, hW⟩ := ih
    by_cases hv : v = 0
    · refine ⟨W, fun x => ?_⟩
      rw [List.map_cons, List.prod_cons, LinearIsometryEquiv.coe_mul, Function.comp_apply, hW,
        refl, refl_apply, hv]
      simp [nz, List.countP_cons]
    · have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
      set w : E5 := ‖v‖⁻¹ • v with hw
      have hw1 : ∑ s, w s ^ 2 = 1 := by
        rw [← norm_sq_E5, hw, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn, one_pow]
      refine ⟨lineElt w hw1 * W, fun x => ?_⟩
      have hrefl : ∀ y, refl v y = -rotV (lineElt w hw1) y := by
        intro y
        rw [rot_lineElt, neg_neg, refl, refl_apply, refl_apply, hw, real_inner_smul_left, norm_smul,
          norm_inv, norm_norm, inv_mul_cancel₀ hn, one_pow, div_one, smul_smul]
        congr 2
        field_simp
      rw [List.map_cons, List.prod_cons, LinearIsometryEquiv.coe_mul, Function.comp_apply, hW,
        hrefl, rotV_mul, rotV_smul]
      simp [nz, List.countP_cons, hv, pow_succ]

theorem det_prod_refl (l : List E5) :
    LinearMap.det ((l.map refl).prod).toLinearMap = (-1 : ℝ) ^ nz l := by
  induction l with
  | nil =>
    simp only [List.map_nil, List.prod_nil, nz, List.countP_nil, pow_zero]
    exact LinearMap.det_id
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons]
    have : ((refl v * (l.map refl).prod).toLinearMap : E5 →ₗ[ℝ] E5) =
        (refl v).toLinearMap ∘ₗ ((l.map refl).prod).toLinearMap := rfl
    rw [this, LinearMap.det_comp, ih, det_refl]
    by_cases hv : v = 0
    · simp [hv, nz]
    · simp [hv, nz, List.countP_cons, pow_succ]

theorem rotV_neg (W : Sp2) (x : E5) : rotV W (-x) = -rotV W x := by
  rw [show -x = (-1 : ℝ) • x by simp, rotV_smul]
  simp

/-- **`det R_U = 1`: the ten rotations give rotations.** -/
theorem rot_det (U : Sp2) : LinearMap.det (rotHom U).toLinearMap = 1 := by
  obtain ⟨l, -, hl⟩ := (rotHom U).reflections_generate_dim
  obtain ⟨W, hW⟩ := realize l
  have hl' : rotHom U = (l.map refl).prod := hl
  have hdet : LinearMap.det (rotHom U).toLinearMap = (-1 : ℝ) ^ nz l := by
    rw [hl']
    exact det_prod_refl l
  rcases neg_one_pow_eq_or ℝ (nz l) with h | h
  · rw [hdet, h]
  · exfalso
    apply no_reversal (W⁻¹ * U)
    intro x
    have hx := hW x
    rw [h, neg_one_smul, ← hl', rotHom_apply] at hx
    rw [rotV_mul, hx, rotV_neg, ← rotV_mul, inv_mul_cancel, rotV_one]

/-- **`Sp(2)` maps onto `SO(5)`.** -/
theorem rot_onto (φ : E5 ≃ₗᵢ[ℝ] E5) (hφ : LinearMap.det φ.toLinearMap = 1) :
    ∃ U : Sp2, rotHom U = φ := by
  obtain ⟨l, -, hl⟩ := φ.reflections_generate_dim
  obtain ⟨W, hW⟩ := realize l
  have hdet : LinearMap.det φ.toLinearMap = (-1 : ℝ) ^ nz l := by
    rw [show φ = (l.map fun v => (ℝ ∙ v)ᗮ.reflection).prod from hl]
    exact det_prod_refl l
  rw [hφ] at hdet
  refine ⟨W, LinearIsometryEquiv.ext fun x => ?_⟩
  rw [rotHom_apply, show φ = (l.map refl).prod from hl, hW, ← hdet, one_smul]

/-- **`Sp(2)/{±1} = SO(5)`**, in one statement. -/
theorem sp2_mod_sign_is_SO5 :
    (∀ U : Sp2, LinearMap.det (rotHom U).toLinearMap = 1) ∧
    (∀ φ : E5 ≃ₗᵢ[ℝ] E5, LinearMap.det φ.toLinearMap = 1 → ∃ U : Sp2, rotHom U = φ) ∧
    (∀ U : Sp2, rotHom U = 1 ↔ mat U = 1 ∨ mat U = -1) :=
  ⟨rot_det, rot_onto, rot_ker⟩

end

end Comparison.GroupsContinuumLaw
