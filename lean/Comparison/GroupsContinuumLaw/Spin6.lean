import Comparison.GroupsContinuumLaw.Six

/-!
# `SU(4) → SO(6)` onto, with kernel `±1` (Prop. 17, part two)

On P1's real six (`Six.lean`: `rot6Hom`, `U ι(t) Uᵀ = ι(R_U t)`), with `e₀ = Ω`'s direction `J`
and the five `i ℓ_s` as `emb`:

* `rot6_sp2_e0`, `rot6_sp2_emb`: a rotation of `Sp(2)` fixes `e₀` and turns the five `iℓ_s` as it turns
  the lines; `stabilizer_singlet`: **the rotations that keep the singlet are `Sp(2)`**;
* `boost`: `B = c + s·iγ(m)` (`c² + s² = 1`, `|m| = 1`) is in `SU(4)` and sends `e₀` to
  `(c² − s²) e₀ + 2cs m`; `turn_singlet`: **`(e^{iaγ_s} ⊗ e^{iaγ_s}) Ω = cos 2a Ω + sin 2a iℓ_s`**
  (with `e^{iaγ_s} = cos a + i sin a γ_s`); `places_of_singlet`: **`SU(4)` takes `Ω` to every unit
  vector of the six** (`S⁵ = SU(4)/Sp(2)`);
* `rot6_det`: **`det R_U = 1`**; `rot6_onto`: **every rotation of determinant one is some `R_U`**;
  `rot6_ker`: **`R_U = 1` iff `U = ±1`**; `rot6_i`: `i·1` reverses all six directions.
-/

namespace Comparison.GroupsContinuumLaw

open Matrix hiding J
open Complex Kronecker

noncomputable section

/-! ## Determinants of isometries -/

theorem det_reflection_zero {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] :
    LinearMap.det ((ℝ ∙ (0 : F))ᗮ.reflection).toLinearMap = 1 := by
  rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal,
    Submodule.finrank_eq_zero.2 (by simp), pow_zero]

theorem det_reflection_ne {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] {v : F} (hv : v ≠ 0) :
    LinearMap.det ((ℝ ∙ v)ᗮ.reflection).toLinearMap = -1 := by
  rw [Submodule.det_reflection, Submodule.orthogonal_orthogonal, finrank_span_singleton hv,
    pow_one]

theorem det_prod_reflection_pm {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (l : List F) :
    LinearMap.det ((l.map fun v => (ℝ ∙ v)ᗮ.reflection).prod).toLinearMap = 1 ∨
      LinearMap.det ((l.map fun v => (ℝ ∙ v)ᗮ.reflection).prod).toLinearMap = -1 := by
  induction l with
  | nil =>
    left
    simp only [List.map_nil, List.prod_nil]
    exact LinearMap.det_id
  | cons v l ih =>
    rw [List.map_cons, List.prod_cons]
    have e : (((ℝ ∙ v)ᗮ.reflection * (l.map fun v => (ℝ ∙ v)ᗮ.reflection).prod).toLinearMap :
        F →ₗ[ℝ] F) = ((ℝ ∙ v)ᗮ.reflection).toLinearMap ∘ₗ
          ((l.map fun v => (ℝ ∙ v)ᗮ.reflection).prod).toLinearMap := rfl
    rw [e, LinearMap.det_comp]
    by_cases hv : v = 0
    · subst hv
      rw [det_reflection_zero, one_mul]
      exact ih
    · rw [det_reflection_ne hv]
      rcases ih with h | h <;> rw [h] <;> norm_num

/-- **The determinant of an isometry is `±1`** (Cartan–Dieudonné). -/
theorem det_isometry_pm {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (φ : F ≃ₗᵢ[ℝ] F) :
    LinearMap.det φ.toLinearMap = 1 ∨ LinearMap.det φ.toLinearMap = -1 := by
  obtain ⟨l, -, hl⟩ := φ.reflections_generate_dim
  rw [hl]
  exact det_prod_reflection_pm l

theorem det_mul_isometry {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (φ ψ : F ≃ₗᵢ[ℝ] F) :
    LinearMap.det (φ * ψ).toLinearMap =
      LinearMap.det φ.toLinearMap * LinearMap.det ψ.toLinearMap := by
  have e : ((φ * ψ).toLinearMap : F →ₗ[ℝ] F) = φ.toLinearMap ∘ₗ ψ.toLinearMap := rfl
  rw [e, LinearMap.det_comp]

/-! ## `Sp(2)` inside `SU(4)`, and the six split as `e₀` and the five -/

/-- A rotation of `Sp(2)` as a rotation of `SU(4)`. -/
def toSU4 (W : Sp2) : SU4 := ⟨mat W, (W : Matrix.unitaryGroup Four ℂ).2, sp2_det W⟩

theorem toSU4_coe (W : Sp2) : ((toSU4 W : SU4) : Matrix Four Four ℂ) = mat W := rfl

/-- The direction of the singlet, `e₀`. -/
def e0 : E6 := EuclideanSpace.single 0 1

/-- The five `iℓ_s` inside the six. -/
def embL : E5 →ₗ[ℝ] E6 where
  toFun x := WithLp.toLp 2 (Fin.cons 0 x.ofLp)
  map_add' x y := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c x := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- The last five coordinates. -/
def tailL : E6 →ₗ[ℝ] E5 where
  toFun t := WithLp.toLp 2 fun j => t j.succ
  map_add' s t := by ext j; simp
  map_smul' c t := by ext j; simp

theorem embL_zero (x : E5) : embL x 0 = 0 := by simp [embL]

theorem embL_succ (x : E5) (j : Fin 5) : embL x j.succ = x j := by simp [embL]

theorem tailL_embL (x : E5) : tailL (embL x) = x := by
  ext j
  simp [tailL, embL]

theorem e0_zero : e0 0 = 1 := by simp [e0]

theorem e0_succ (j : Fin 5) : e0 j.succ = 0 := by simp [e0, PiLp.single_apply, Fin.succ_ne_zero]

theorem decomp_six (t : E6) : t = t 0 • e0 + embL (tailL t) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [e0_zero, embL_zero]
  · simp [e0_succ, embL_succ, tailL]

theorem sumsq_embL (x : E5) : ∑ a, embL x a ^ 2 = ∑ j, x j ^ 2 := by
  rw [Fin.sum_univ_succ, embL_zero]
  simp [embL_succ]

theorem norm_embL (x : E5) : ‖embL x‖ = ‖x‖ := by
  have h : ‖embL x‖ ^ 2 = ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, sumsq_embL]
  rw [← Real.sqrt_sq (norm_nonneg (embL x)), ← Real.sqrt_sq (norm_nonneg x), h]

theorem ι6_e0 : ι6 e0 = J := by
  have : ι6 e0 = ιC (Pi.single 0 1) := by
    rw [ι6]
    congr 1
    funext a
    by_cases ha : a = 0 <;> simp [e0, PiLp.single_apply, Pi.single_apply, ha]
  rw [this, ← sixP1_eq_ιC, sixP1_zero]

theorem ι6_embL (x : E5) : ι6 (embL x) = I • (gE x * J) := by
  rw [ι6, ιC, Fin.sum_univ_succ, gE, Finset.sum_mul, Finset.smul_sum]
  simp only [embL_zero, embL_succ, Complex.ofReal_zero, zero_smul, zero_add, sixP1_succ]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_mul, smul_comm]

theorem ι6_add_smul (a : ℝ) (x : E5) : ι6 (a • e0 + embL x) = (a : ℂ) • J + I • (gE x * J) := by
  rw [ι6_add, ι6_smul, ι6_e0, ι6_embL]

/-! ## The ten rotations on the six -/

theorem J_transpose_sp2 (W : Sp2) : J * (mat W)ᵀ = star (mat W) * J := by
  calc J * (mat W)ᵀ = star (mat W) * (mat W * J * (mat W)ᵀ) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, sp2_unitary', Matrix.one_mul]
    _ = star (mat W) * J := by rw [sp2_keepJ]

theorem rot6_sp2_e0 (W : Sp2) : rot6V (toSU4 W) e0 = e0 := by
  apply ι6_injective
  rw [ι6_rot6, ι6_e0]
  exact sp2_keepJ W

/-- **A rotation of `Sp(2)` turns the five `iℓ_s` as it turns the five directions.** -/
theorem rot6_sp2_emb (W : Sp2) (x : E5) : rot6V (toSU4 W) (embL x) = embL (rotV W x) := by
  apply ι6_injective
  rw [ι6_rot6, ι6_embL, ι6_embL, sp2_conj_line, toSU4_coe, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [J_transpose_sp2]

/-- The rotations of `SU(4)` that fix `e₀` as elements of `Sp(2)`. -/
def sp2OfFix (V : SU4) (h : rot6V V e0 = e0) : Sp2 :=
  ⟨⟨V, V.2.1⟩, by
    have := congrArg ι6 h
    rw [ι6_rot6, ι6_e0] at this
    exact this⟩

theorem toSU4_sp2OfFix (V : SU4) (h : rot6V V e0 = e0) : toSU4 (sp2OfFix V h) = V := rfl

/-- **The rotations that keep the singlet are `Sp(2)`.** -/
theorem stabilizer_singlet (U : SU4) :
    rot6Hom U e0 = e0 ↔ (U : Matrix Four Four ℂ) * J * (U : Matrix Four Four ℂ)ᵀ = J := by
  rw [rot6Hom_apply]
  constructor
  · intro h
    have := congrArg ι6 h
    rwa [ι6_rot6, ι6_e0] at this
  · intro h
    apply ι6_injective
    rw [ι6_rot6, ι6_e0, h]

/-! ## The determinant on the ten -/

/-- The standard bases. -/
abbrev b6 : Module.Basis (Fin 6) ℝ E6 := PiLp.basisFun 2 ℝ (Fin 6)
abbrev b5 : Module.Basis (Fin 5) ℝ E5 := PiLp.basisFun 2 ℝ (Fin 5)

theorem b6_zero : b6 0 = e0 := by simp [e0]

theorem b6_succ (s : Fin 5) : b6 s.succ = embL (b5 s) := by
  ext r
  refine Fin.cases ?_ (fun j => ?_) r
  · simp [embL_zero, PiLp.single_apply, Fin.succ_ne_zero]
  · simp [embL_succ, PiLp.single_apply]

/-- **A map that fixes `e₀` and acts on the five as `g` has the determinant of `g`.** -/
theorem det_block (f : E6 →ₗ[ℝ] E6) (g : E5 →ₗ[ℝ] E5) (h0 : f e0 = e0)
    (h1 : ∀ x, f (embL x) = embL (g x)) : LinearMap.det f = LinearMap.det g := by
  rw [← LinearMap.det_toMatrix b6, ← LinearMap.det_toMatrix b5, Matrix.det_succ_row_zero,
    Fin.sum_univ_succ]
  have hz : LinearMap.toMatrix b6 b6 f 0 0 = 1 := by
    rw [LinearMap.toMatrix_apply, b6_zero, h0, PiLp.basisFun_repr, e0_zero]
  have hs : ∀ s : Fin 5, LinearMap.toMatrix b6 b6 f 0 s.succ = 0 := by
    intro s
    rw [LinearMap.toMatrix_apply, b6_succ, h1, PiLp.basisFun_repr, embL_zero]
  have hsub : (LinearMap.toMatrix b6 b6 f).submatrix Fin.succ Fin.succ =
      LinearMap.toMatrix b5 b5 g := by
    ext r s
    rw [Matrix.submatrix_apply, LinearMap.toMatrix_apply,
      LinearMap.toMatrix_apply, b6_succ, h1, PiLp.basisFun_repr, PiLp.basisFun_repr, embL_succ]
  simp [hz, hs, Fin.succAbove_zero, hsub]

theorem rot6_sp2_det (W : Sp2) : LinearMap.det (rot6Hom (toSU4 W)).toLinearMap = 1 := by
  rw [det_block (rot6Hom (toSU4 W)).toLinearMap (rotHom W).toLinearMap (rot6_sp2_e0 W)
    (rot6_sp2_emb W)]
  exact rot_det W

/-! ## The boosts -/

/-- `iγ(m)`. -/
def Kmat (m : E5) : Matrix Four Four ℂ := I • gE m

theorem Kmat_sq (m : E5) (hm : ∑ k, m k ^ 2 = 1) : Kmat m * Kmat m = -1 := by
  rw [Kmat, Matrix.smul_mul, Matrix.mul_smul, smul_smul, gE_sq, hm, I_mul_I]
  simp

theorem Kmat_star (m : E5) : star (Kmat m) = -Kmat m := by
  rw [Kmat, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul, gE_hermitian]
  simp

theorem gE_J_transpose (m : E5) : J * (gE m)ᵀ = gE m * J := by
  rw [gE, Matrix.transpose_sum, Matrix.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Matrix.transpose_smul, Matrix.mul_smul, J_mul_γ_transpose, Matrix.smul_mul]

/-- The boost `c + s·iγ(m)`. -/
def boostM (c s : ℝ) (m : E5) : Matrix Four Four ℂ := (c : ℂ) • (1 : Matrix Four Four ℂ) +
  (s : ℂ) • Kmat m

theorem boostM_sq (c s : ℝ) (m : E5) (hm : ∑ k, m k ^ 2 = 1) :
    boostM c s m * boostM c s m = boostM (c ^ 2 - s ^ 2) (2 * c * s) m := by
  have hK := Kmat_sq m hm
  simp only [boostM, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one, smul_smul, hK]
  push_cast
  module

theorem boostM_star (c s : ℝ) (m : E5) :
    star (boostM c s m) = (c : ℂ) • (1 : Matrix Four Four ℂ) - (s : ℂ) • Kmat m := by
  rw [boostM, star_add, star_smul, star_smul, star_one, Kmat_star]
  simp [sub_eq_add_neg]

theorem boostM_unitary (c s : ℝ) (m : E5) (hcs : c ^ 2 + s ^ 2 = 1) (hm : ∑ k, m k ^ 2 = 1) :
    boostM c s m * star (boostM c s m) = 1 := by
  have hK := Kmat_sq m hm
  have hc : (c : ℂ) * c + (s : ℂ) * s = 1 := by
    have : c * c + s * s = 1 := by nlinarith
    exact_mod_cast this
  rw [boostM_star, boostM]
  calc ((c : ℂ) • (1 : Matrix Four Four ℂ) + (s : ℂ) • Kmat m) *
        ((c : ℂ) • (1 : Matrix Four Four ℂ) - (s : ℂ) • Kmat m)
      = ((c : ℂ) * c) • (1 : Matrix Four Four ℂ) - ((s : ℂ) * s) • (Kmat m * Kmat m) := by
        simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.one_mul, Matrix.mul_one, smul_smul]
        module
    _ = 1 := by rw [hK, smul_neg, sub_neg_eq_add, ← add_smul, hc, one_smul]

theorem boostM_det (c s : ℝ) (m : E5) (hcs : c ^ 2 + s ^ 2 = 1) (hm : ∑ k, m k ^ 2 = 1) :
    (boostM c s m).det = 1 := by
  have e : boostM c s m = (c : ℂ) • (1 : Matrix Four Four ℂ) +
      ∑ k, ((s : ℂ) * I * (m k : ℂ)) • γ k := by
    rw [boostM, Kmat, gE, Finset.smul_sum, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_smul, smul_smul, mul_assoc]
  rw [e, det_cone]
  have h1 : ∑ k, ((s : ℂ) * I * (m k : ℂ)) ^ 2 = -((s : ℂ) ^ 2) := by
    have : ∑ k, ((s : ℂ) * I * (m k : ℂ)) ^ 2 = (s : ℂ) ^ 2 * I ^ 2 * ((∑ k, m k ^ 2 : ℝ) : ℂ) := by
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [this, hm, I_sq]
    push_cast
    ring
  rw [h1]
  have : ((c : ℂ) ^ 2 + (s : ℂ) ^ 2) = 1 := by exact_mod_cast hcs
  rw [sub_neg_eq_add, this, one_pow]

/-- The boost as an element of `SU(4)`. -/
def boost (c s : ℝ) (m : E5) (hcs : c ^ 2 + s ^ 2 = 1) (hm : ∑ k, m k ^ 2 = 1) : SU4 :=
  ⟨boostM c s m, Matrix.mem_unitaryGroup_iff.2 (boostM_unitary c s m hcs hm),
    boostM_det c s m hcs hm⟩

theorem boost_coe (c s : ℝ) (m : E5) (hcs : c ^ 2 + s ^ 2 = 1) (hm : ∑ k, m k ^ 2 = 1) :
    ((boost c s m hcs hm : SU4) : Matrix Four Four ℂ) = boostM c s m := rfl

theorem boostM_J (c s : ℝ) (m : E5) (hm : ∑ k, m k ^ 2 = 1) :
    boostM c s m * J * (boostM c s m)ᵀ =
      ((c ^ 2 - s ^ 2 : ℝ) : ℂ) • J + I • (gE ((2 * c * s) • m) * J) := by
  have hJB : J * (boostM c s m)ᵀ = boostM c s m * J := by
    rw [boostM, Kmat, Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul,
      Matrix.transpose_smul, Matrix.transpose_one, Matrix.mul_add, Matrix.mul_smul,
      Matrix.mul_smul, Matrix.mul_smul, gE_J_transpose, Matrix.mul_one, Matrix.add_mul,
      Matrix.smul_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]
  rw [Matrix.mul_assoc, hJB, ← Matrix.mul_assoc, boostM_sq c s m hm, boostM, Kmat, gE_smul,
    Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.smul_mul]
  push_cast
  rw [smul_comm (((2 : ℂ) * c * s)) I]

/-- **The boost turns `e₀` to `(c² − s²) e₀ + 2cs·m`.** -/
theorem rot6_boost (c s : ℝ) (m : E5) (hcs : c ^ 2 + s ^ 2 = 1) (hm : ∑ k, m k ^ 2 = 1) :
    rot6V (boost c s m hcs hm) e0 = (c ^ 2 - s ^ 2) • e0 + embL ((2 * c * s) • m) := by
  apply ι6_injective
  rw [ι6_rot6, ι6_e0, boost_coe, boostM_J c s m hm, ι6_add_smul]

/-- **`(e^{iaγ_s} ⊗ e^{iaγ_s}) Ω = cos 2a Ω + sin 2a iℓ_s`**, with `e^{iaγ_s} = cos a + i sin a γ_s`
and `ℓ_s = (γ_s ⊗ 1) Ω`. -/
theorem turn_singlet (a : ℝ) (s : Fin 5) :
    (boostM (Real.cos a) (Real.sin a) (EuclideanSpace.single s 1) ⊗ₖ
        boostM (Real.cos a) (Real.sin a) (EuclideanSpace.single s 1)) *ᵥ Ω =
      (Real.cos (2 * a) : ℂ) • Ω + (Real.sin (2 * a) : ℂ) • (I • ((γ s ⊗ₖ 1) *ᵥ Ω)) := by
  have hm : ∑ k, (EuclideanSpace.single s (1 : ℝ) : E5) k ^ 2 = 1 := by
    simp [PiLp.single_apply]
  rw [kron_mulVec_Ω, Ω, kron_mulVec_relOf]
  simp only [← relOf_smul, ← relOf_add]
  congr 1
  rw [MΩ, Matrix.mul_smul, Matrix.smul_mul, boostM_J _ _ _ hm, gE_smul, gE_single,
    Real.cos_two_mul, Real.sin_two_mul, Real.sin_sq]
  simp only [Matrix.transpose_one, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul, smul_add,
    smul_smul]
  push_cast
  module

/-! ## Every unit vector of the six is a vertex of the singlet -/

theorem sumsq_tail (n : E6) : ∑ a, n a ^ 2 = n 0 ^ 2 + ∑ j, tailL n j ^ 2 := by
  rw [Fin.sum_univ_succ]
  simp [tailL]

theorem exists_boost (n : E6) (hn : ∑ a, n a ^ 2 = 1) :
    ∃ (c s : ℝ) (m : E5) (hcs : c ^ 2 + s ^ 2 = 1) (hm : ∑ k, m k ^ 2 = 1),
      0 ≤ s ∧ rot6V (boost c s m hcs hm) e0 = n := by
  set v := tailL n with hv
  have hsum : n 0 ^ 2 + ∑ j, v j ^ 2 = 1 := by rw [← sumsq_tail]; exact hn
  have hv0 : 0 ≤ ∑ j, v j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hle : n 0 ^ 2 ≤ 1 := by linarith
  have hlo : -1 ≤ n 0 := by nlinarith
  have hhi : n 0 ≤ 1 := by nlinarith
  set c := Real.sqrt ((1 + n 0) / 2) with hc
  set s := Real.sqrt ((1 - n 0) / 2) with hs
  have hc2 : c ^ 2 = (1 + n 0) / 2 := Real.sq_sqrt (by linarith)
  have hs2 : s ^ 2 = (1 - n 0) / 2 := Real.sq_sqrt (by linarith)
  have hcs : c ^ 2 + s ^ 2 = 1 := by rw [hc2, hs2]; ring
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have hdiff : c ^ 2 - s ^ 2 = n 0 := by rw [hc2, hs2]; ring
  set r := ‖v‖ with hr
  have hr2 : r ^ 2 = ∑ j, v j ^ 2 := EuclideanSpace.real_norm_sq_eq v
  have h2cs : 2 * c * s = r := by
    have hsq : (2 * c * s) ^ 2 = r ^ 2 := by
      rw [hr2]
      have : (2 * c * s) ^ 2 = 4 * c ^ 2 * s ^ 2 := by ring
      rw [this, hc2, hs2]
      nlinarith
    have h1 : 0 ≤ 2 * c * s := by positivity
    have h2 : 0 ≤ r := norm_nonneg _
    nlinarith [sq_nonneg (2 * c * s - r), sq_nonneg (2 * c * s + r)]
  by_cases hv' : v = 0
  · set m : E5 := EuclideanSpace.single 0 1
    have hm : ∑ k, m k ^ 2 = 1 := by simp [m, PiLp.single_apply]
    refine ⟨c, s, m, hcs, hm, hs0, ?_⟩
    rw [rot6_boost, hdiff, h2cs, hr, hv', norm_zero, zero_smul]
    conv_rhs => rw [decomp_six n]
    rw [← hv, hv']
  · have hrpos : r ≠ 0 := norm_ne_zero_iff.2 hv'
    set m : E5 := r⁻¹ • v
    have hm : ∑ k, m k ^ 2 = 1 := by
      rw [← EuclideanSpace.real_norm_sq_eq, norm_smul, norm_inv, norm_norm, ← hr,
        inv_mul_cancel₀ hrpos, one_pow]
    refine ⟨c, s, m, hcs, hm, hs0, ?_⟩
    rw [rot6_boost, hdiff, h2cs, smul_smul, mul_inv_cancel₀ hrpos, one_smul]
    exact (decomp_six n).symm

/-- **`SU(4)` takes `Ω` to every unit vector of the six: the vertices of the singlet are `S⁵`.** -/
theorem places_of_singlet (n : E6) (hn : ‖n‖ = 1) : ∃ U : SU4, rot6Hom U e0 = n := by
  have hn' : ∑ a, n a ^ 2 = 1 := by rw [← EuclideanSpace.real_norm_sq_eq, hn, one_pow]
  obtain ⟨c, s, m, hcs, hm, -, h⟩ := exists_boost n hn'
  exact ⟨boost c s m hcs hm, h⟩

/-- The half boost. -/
theorem boost_half (c s : ℝ) (m : E5) (hcs : c ^ 2 + s ^ 2 = 1) (hm : ∑ k, m k ^ 2 = 1)
    (hs : 0 ≤ s) : ∃ (c' s' : ℝ) (hcs' : c' ^ 2 + s' ^ 2 = 1),
      boost c s m hcs hm = boost c' s' m hcs' hm * boost c' s' m hcs' hm := by
  have hlo : -1 ≤ c := by nlinarith
  have hhi : c ≤ 1 := by nlinarith
  set c' := Real.sqrt ((1 + c) / 2)
  set s' := Real.sqrt ((1 - c) / 2)
  have hc2 : c' ^ 2 = (1 + c) / 2 := Real.sq_sqrt (by linarith)
  have hs2 : s' ^ 2 = (1 - c) / 2 := Real.sq_sqrt (by linarith)
  have hcs' : c' ^ 2 + s' ^ 2 = 1 := by rw [hc2, hs2]; ring
  have hdiff : c' ^ 2 - s' ^ 2 = c := by rw [hc2, hs2]; ring
  have h2 : 2 * c' * s' = s := by
    have hsq : (2 * c' * s') ^ 2 = s ^ 2 := by
      have : (2 * c' * s') ^ 2 = 4 * c' ^ 2 * s' ^ 2 := by ring
      rw [this, hc2, hs2]
      nlinarith
    have h1 : 0 ≤ 2 * c' * s' := by positivity
    nlinarith [sq_nonneg (2 * c' * s' - s), sq_nonneg (2 * c' * s' + s)]
  refine ⟨c', s', hcs', ?_⟩
  apply Subtype.ext
  change boostM c s m = boostM c' s' m * boostM c' s' m
  rw [boostM_sq c' s' m hm, hdiff, h2]

theorem rot6_boost_det (c s : ℝ) (m : E5) (hcs : c ^ 2 + s ^ 2 = 1) (hm : ∑ k, m k ^ 2 = 1)
    (hs : 0 ≤ s) : LinearMap.det (rot6Hom (boost c s m hcs hm)).toLinearMap = 1 := by
  obtain ⟨c', s', hcs', h⟩ := boost_half c s m hcs hm hs
  rw [h, map_mul, det_mul_isometry]
  rcases det_isometry_pm (rot6Hom (boost c' s' m hcs' hm)) with h1 | h1 <;> rw [h1] <;> norm_num

/-! ## Determinant one, onto, and the kernel -/

theorem su4_star_mul (U : SU4) : star U * U = 1 := Subtype.ext (su4_unitary_left U)

theorem su4_mul_star (U : SU4) : U * star U = 1 := Subtype.ext (su4_unitary U)

/-- **`det R_U = 1`: the fifteen rotations give rotations.** -/
theorem rot6_det (U : SU4) : LinearMap.det (rot6Hom U).toLinearMap = 1 := by
  have hn : ∑ a, rot6Hom U e0 a ^ 2 = 1 := by
    rw [rot6Hom_apply, rot6V_sumsq]
    simp [e0, PiLp.single_apply]
  obtain ⟨c, s, m, hcs, hm, hs, hB⟩ := exists_boost _ hn
  set B := boost c s m hcs hm
  have hfix : rot6V (star B * U) e0 = e0 := by
    rw [rot6V_mul, ← rot6Hom_apply U e0, ← hB, ← rot6V_mul, su4_star_mul, rot6V_one]
  have hU : U = B * toSU4 (sp2OfFix (star B * U) hfix) := by
    rw [toSU4_sp2OfFix, ← mul_assoc, su4_mul_star, one_mul]
  rw [hU, map_mul, det_mul_isometry, rot6_boost_det c s m hcs hm hs, rot6_sp2_det, one_mul]

/-- **`SU(4)` maps onto `SO(6)`.** -/
theorem rot6_onto (φ : E6 ≃ₗᵢ[ℝ] E6) (hφ : LinearMap.det φ.toLinearMap = 1) :
    ∃ U : SU4, rot6Hom U = φ := by
  have hn : ∑ a, φ e0 a ^ 2 = 1 := by
    rw [← EuclideanSpace.real_norm_sq_eq, LinearIsometryEquiv.norm_map]
    simp [e0]
  obtain ⟨c, s, m, hcs, hm, hs, hB⟩ := exists_boost _ hn
  set B := boost c s m hcs hm
  set ψ : E6 ≃ₗᵢ[ℝ] E6 := rot6Hom (star B) * φ with hψ
  have hψ0 : ψ e0 = e0 := by
    rw [hψ, LinearIsometryEquiv.coe_mul, Function.comp_apply, rot6Hom_apply, ← hB, ← rot6V_mul,
      su4_star_mul, rot6V_one]
  have hperp : ∀ x, ψ (embL x) 0 = 0 := by
    intro x
    have h := LinearIsometryEquiv.inner_map_map ψ e0 (embL x)
    rw [hψ0] at h
    have h1 : ∀ y : E6, inner ℝ e0 y = y 0 := fun y => by
      simp [e0, EuclideanSpace.inner_single_left]
    rw [h1, h1, embL_zero] at h
    exact h
  have hemb : ∀ x, ψ (embL x) = embL (tailL (ψ (embL x))) := by
    intro x
    conv_lhs => rw [decomp_six (ψ (embL x))]
    rw [hperp, zero_smul, zero_add]
  let gL : E5 →ₗᵢ[ℝ] E5 :=
    { toLinearMap := tailL ∘ₗ ψ.toLinearMap ∘ₗ embL
      norm_map' := fun x => by
        change ‖tailL (ψ (embL x))‖ = ‖x‖
        rw [← norm_embL, ← hemb, LinearIsometryEquiv.norm_map, norm_embL] }
  let g : E5 ≃ₗᵢ[ℝ] E5 := gL.toLinearIsometryEquiv rfl
  have hg : ∀ x, ψ (embL x) = embL (g x) := fun x => hemb x
  have hdetψ : LinearMap.det ψ.toLinearMap = 1 := by
    rw [hψ, det_mul_isometry, rot6_det, hφ, one_mul]
  have hdetg : LinearMap.det g.toLinearMap = 1 := by
    rw [← det_block ψ.toLinearMap g.toLinearMap hψ0 hg, hdetψ]
  obtain ⟨W, hW⟩ := rot_onto g hdetg
  refine ⟨B * toSU4 W, LinearIsometryEquiv.ext fun t => ?_⟩
  have hψt : ψ t = rot6V (toSU4 W) t := by
    conv_lhs => rw [decomp_six t]
    conv_rhs => rw [decomp_six t]
    rw [LinearIsometryEquiv.map_add, LinearIsometryEquiv.map_smul, hψ0, hg, rot6V_add,
      rot6V_smul, rot6_sp2_e0, rot6_sp2_emb, ← rotHom_apply, hW]
  rw [rot6Hom_apply, rot6V_mul, ← hψt, hψ, LinearIsometryEquiv.coe_mul, Function.comp_apply,
    rot6Hom_apply, ← rot6V_mul, su4_mul_star, rot6V_one]

/-- **The kernel: `R_U = 1` exactly when `U = ±1`.** -/
theorem rot6_ker (U : SU4) :
    rot6Hom U = 1 ↔ (U : Matrix Four Four ℂ) = 1 ∨ (U : Matrix Four Four ℂ) = -1 := by
  constructor
  · intro h
    have hU : ∀ t, rot6V U t = t := fun t => by
      have := congrArg (fun e : E6 ≃ₗᵢ[ℝ] E6 => e t) h
      simpa [rot6Hom_apply] using this
    set W := sp2OfFix U (hU e0)
    have hW : rotHom W = 1 := by
      refine LinearIsometryEquiv.ext fun x => ?_
      rw [rotHom_apply]
      have h1 := rot6_sp2_emb W x
      rw [toSU4_sp2OfFix, hU] at h1
      have := congrArg tailL h1
      rw [tailL_embL, tailL_embL] at this
      exact this.symm
    exact (rot_ker W).1 hW
  · intro h
    refine LinearIsometryEquiv.ext fun t => ?_
    rw [rot6Hom_apply]
    apply ι6_injective
    rw [ι6_rot6]
    rcases h with h | h <;> rw [h] <;> simp

/-- **`SU(4)/{±1} = SO(6)`**, in one statement. -/
theorem su4_mod_sign_is_SO6 :
    (∀ U : SU4, LinearMap.det (rot6Hom U).toLinearMap = 1) ∧
    (∀ φ : E6 ≃ₗᵢ[ℝ] E6, LinearMap.det φ.toLinearMap = 1 → ∃ U : SU4, rot6Hom U = φ) ∧
    (∀ U : SU4, rot6Hom U = 1 ↔ (U : Matrix Four Four ℂ) = 1 ∨ (U : Matrix Four Four ℂ) = -1) :=
  ⟨rot6_det, rot6_onto, rot6_ker⟩

theorem iOne_unitary :
    (I • (1 : Matrix Four Four ℂ)) * star (I • (1 : Matrix Four Four ℂ)) = 1 := by
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
  simp

theorem iOne_det : (I • (1 : Matrix Four Four ℂ)).det = 1 := by
  rw [Matrix.det_smul, Matrix.det_one, mul_one]
  have : Fintype.card Four = 4 := by simp [Four]
  rw [this, Complex.I_pow_four]

/-- `i·1`, of determinant one, reverses all six directions. -/
def iOne : SU4 := ⟨I • (1 : Matrix Four Four ℂ), Matrix.mem_unitaryGroup_iff.2 iOne_unitary,
  iOne_det⟩

theorem rot6_i (t : E6) : rot6Hom iOne t = -t := by
  rw [rot6Hom_apply]
  apply ι6_injective
  rw [ι6_rot6, show -t = (-1 : ℝ) • t by simp, ι6_smul]
  change I • (1 : Matrix Four Four ℂ) * ι6 t * (I • (1 : Matrix Four Four ℂ))ᵀ = _
  rw [Matrix.transpose_smul, Matrix.transpose_one, Matrix.smul_mul, Matrix.one_mul,
    Matrix.mul_smul, Matrix.mul_one, smul_smul, I_mul_I]
  simp

end

end Comparison.GroupsContinuumLaw
