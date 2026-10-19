module

public import Comparison.Elements.Observables

/-!
# The Elements of Comparison in Lean. Book III: the six directions

The six directions are the antisymmetric two-spinor states of two systems. Their matrices are spanned by
the singlet `J` and the five directions `γ_s J` (P3's six); P1's real six carry an extra `i` on the lines.

* `sixP3_transpose`, `sixP1_transpose`: the six are antisymmetric.
* `pf`: the Pfaffian of a `4 × 4` matrix; `pf_J = 1`; `det_eq_pf_sq`: `det M = (Pf M)²` for
  antisymmetric `M`.
* `sign_of_time`: `Pf(t₀ J + Σ t_s γ_s J) / Pf J = t₀² − Σ t_s²`.
* `pf_P1_six`: `Pf(t₀ J + Σ t_s (i γ_s J)) / Pf J = t₀² + Σ t_s²`.
* `det_cone`: `det(t₀ + Σ t_s γ_s) = (t₀² − Σ t_s²)²`.
* `su4`, `gen`, `finrank_su4 = 15`: the fifteen generators `i γ_s` and `i (i γ_s γ_t)`.
* `sp2`, `finrank_sp2 = 10`: the generators that keep the join, `X J + J Xᵀ = 0`, are the ten.
* `line_turns_singlet`: the five `i γ_s` move the join, `X J + J Xᵀ = 2 i γ_s J`.
* `keeps_partner_iff`: a unitary keeps the quaternionic structure exactly when `U J Uᵀ = J`.
-/

@[expose] public section

namespace Comparison

open Matrix hiding J
open Complex Kronecker

/-! ## The six directions and the Pfaffian -/

/-- P3's six: the singlet `J` and the five directions `γ_s J`. -/
def sixP3 : Fin 6 → Matrix Four Four ℂ := ![J, γ 0 * J, γ 1 * J, γ 2 * J, γ 3 * J, γ 4 * J]

/-- P1's real six: the singlet `J` and `i γ_s J`. -/
def sixP1 : Fin 6 → Matrix Four Four ℂ :=
  ![J, I • (γ 0 * J), I • (γ 1 * J), I • (γ 2 * J), I • (γ 3 * J), I • (γ 4 * J)]

theorem γ_mul_J_transpose (s : Fin 5) : (γ s * J)ᵀ = -(γ s * J) := by
  have h := γ_mul_J s
  have hH := γ_conjTranspose s
  have hT : (γ s).map star = (γ s)ᵀ := by
    ext i j
    have := congrFun (congrFun hH j) i
    simp only [Matrix.conjTranspose_apply] at this
    simp [← this]
  rw [Matrix.transpose_mul, J_transpose, h, hT, Matrix.neg_mul]

/-- **The six directions are antisymmetric** (P3's form). -/
theorem sixP3_transpose (a : Fin 6) : (sixP3 a)ᵀ = -sixP3 a := by
  fin_cases a
  · exact J_transpose
  all_goals exact γ_mul_J_transpose _

theorem smul_γ_mul_J_transpose (s : Fin 5) : (I • (γ s * J))ᵀ = -(I • (γ s * J)) := by
  rw [Matrix.transpose_smul, γ_mul_J_transpose, smul_neg]

/-- P1's real six are antisymmetric. -/
theorem sixP1_transpose (a : Fin 6) : (sixP1 a)ᵀ = -sixP1 a := by
  fin_cases a
  · exact J_transpose
  all_goals exact smul_γ_mul_J_transpose _

/-- The Pfaffian of a `4 × 4` matrix, `M₁₂ M₃₄ − M₁₃ M₂₄ + M₁₄ M₂₃`, in the order
`(0,0), (0,1), (1,0), (1,1)` of `Four`. -/
def pf (M : Matrix Four Four ℂ) : ℂ :=
  M (0, 0) (0, 1) * M (1, 0) (1, 1) - M (0, 0) (1, 0) * M (0, 1) (1, 1) +
    M (0, 0) (1, 1) * M (0, 1) (1, 0)

theorem pf_J : pf J = 1 := by
  simp [pf, J, ε]

/-- **The sign of time.** On the singlet and the five directions,
`Pf(t₀ J + Σ t_s γ_s J) / Pf J = t₀² − Σ t_s²`: one plus sign and five minus signs. -/
theorem sign_of_time (t₀ : ℂ) (t : Fin 5 → ℂ) :
    pf (t₀ • J + ∑ s, t s • (γ s * J)) / pf J = t₀ ^ 2 - ∑ s, t s ^ 2 := by
  rw [pf_J, div_one]
  simp [pf, J, ε, γ, σ₁, σ₂, σ₃, Fin.sum_univ_five, Matrix.mul_apply, Fintype.sum_prod_type,
    Fin.sum_univ_two]
  ring_nf
  simp only [Complex.I_sq]
  ring

/-- **With the extra `i` on the lines (P1's real six) the Pfaffian is the length:**
`Pf(t₀ J + Σ t_s (i γ_s J)) / Pf J = t₀² + Σ t_s²`. -/
theorem pf_P1_six (t₀ : ℂ) (t : Fin 5 → ℂ) :
    pf (t₀ • J + ∑ s, t s • (I • (γ s * J))) / pf J = t₀ ^ 2 + ∑ s, t s ^ 2 := by
  have h : ∀ s, t s • (I • (γ s * J)) = (I * t s) • (γ s * J) := by
    intro s
    rw [smul_smul, mul_comm]
  simp only [h]
  rw [sign_of_time]
  simp only [mul_pow, Complex.I_sq, neg_one_mul, Finset.sum_neg_distrib, sub_neg_eq_add]

/-! ## The determinant and the cone -/

/-- `Four` listed as `Fin 4`. -/
def fourEquiv : Four ≃ Fin 4 where
  toFun p := ![![0, 1], ![2, 3]] p.1 p.2
  invFun i := ![(0, 0), (0, 1), (1, 0), (1, 1)] i
  left_inv := by decide
  right_inv := by decide

/-- The determinant of a `4 × 4` matrix, by its first row. -/
theorem det_fin_four (a b c d e f g h i j k l m n o p : ℂ) :
    (!![a, b, c, d; e, f, g, h; i, j, k, l; m, n, o, p] : Matrix (Fin 4) (Fin 4) ℂ).det =
      a * (f * (k * p - l * o) - g * (j * p - l * n) + h * (j * o - k * n))
      - b * (e * (k * p - l * o) - g * (i * p - l * m) + h * (i * o - k * m))
      + c * (e * (j * p - l * n) - f * (i * p - l * m) + h * (i * n - j * m))
      - d * (e * (j * o - k * n) - f * (i * o - k * m) + g * (i * n - j * m)) := by
  rw [Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Fin.succAbove]
  ring

/-- A matrix on `Four` has the determinant of its `Fin 4` form. -/
theorem det_four (M : Matrix Four Four ℂ) : M.det =
    (!![M (0, 0) (0, 0), M (0, 0) (0, 1), M (0, 0) (1, 0), M (0, 0) (1, 1);
        M (0, 1) (0, 0), M (0, 1) (0, 1), M (0, 1) (1, 0), M (0, 1) (1, 1);
        M (1, 0) (0, 0), M (1, 0) (0, 1), M (1, 0) (1, 0), M (1, 0) (1, 1);
        M (1, 1) (0, 0), M (1, 1) (0, 1), M (1, 1) (1, 0), M (1, 1) (1, 1)] :
      Matrix (Fin 4) (Fin 4) ℂ).det := by
  rw [← Matrix.det_reindex_self fourEquiv M]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- **`det M = (Pf M)²` for an antisymmetric `4 × 4` matrix.** -/
theorem det_eq_pf_sq (M : Matrix Four Four ℂ) (hM : Mᵀ = -M) : M.det = pf M ^ 2 := by
  have h : ∀ i j, M j i = -M i j := fun i j => by
    have := congrFun (congrFun hM i) j
    simpa using this
  have hd : ∀ i, M i i = 0 := fun i => by
    have := h i i
    linear_combination this / 2
  rw [det_four, det_fin_four, h (0, 0) (0, 1), h (0, 0) (1, 0), h (0, 0) (1, 1),
    h (0, 1) (1, 0), h (0, 1) (1, 1), h (1, 0) (1, 1), hd (0, 0), hd (0, 1), hd (1, 0),
    hd (1, 1)]
  simp only [pf]
  ring

theorem det_J : J.det = 1 := by
  rw [det_eq_pf_sq J J_transpose, pf_J, one_pow]

/-- **The cone of the one and the five directions:** `det(t₀ + Σ t_s γ_s) = (t₀² − Σ t_s²)²`. -/
theorem det_cone (t₀ : ℂ) (t : Fin 5 → ℂ) :
    (t₀ • (1 : Matrix Four Four ℂ) + ∑ s, t s • γ s).det = (t₀ ^ 2 - ∑ s, t s ^ 2) ^ 2 := by
  set X := t₀ • (1 : Matrix Four Four ℂ) + ∑ s, t s • γ s with hX
  have hXJ : X * J = t₀ • J + ∑ s, t s • (γ s * J) := by
    rw [hX, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, Finset.sum_mul]
    simp only [Matrix.smul_mul]
  have hanti : (X * J)ᵀ = -(X * J) := by
    rw [hXJ, Matrix.transpose_add, Matrix.transpose_smul, J_transpose, Matrix.transpose_sum]
    simp only [Matrix.transpose_smul, γ_mul_J_transpose, smul_neg, Finset.sum_neg_distrib,
      neg_add]
  have hdet : (X * J).det = X.det := by
    rw [Matrix.det_mul, det_J, mul_one]
  rw [← hdet, det_eq_pf_sq _ hanti, hXJ]
  have := sign_of_time t₀ t
  rw [pf_J, div_one] at this
  rw [this]

/-! ## The fifteen rotations and the ten -/

/-- The generators of the rotations: anti-Hermitian matrices of trace zero. -/
def su4 : Submodule ℝ (Matrix Four Four ℂ) where
  carrier := {X | Xᴴ = -X ∧ X.trace = 0}
  add_mem' := fun {X Y} (hX : Xᴴ = -X ∧ X.trace = 0) (hY : Yᴴ = -Y ∧ Y.trace = 0) =>
    show (X + Y)ᴴ = -(X + Y) ∧ (X + Y).trace = 0 by
      rw [Matrix.conjTranspose_add, hX.1, hY.1, Matrix.trace_add, hX.2, hY.2]
      exact ⟨by abel, by simp⟩
  zero_mem' := show (0 : Matrix Four Four ℂ)ᴴ = -0 ∧ (0 : Matrix Four Four ℂ).trace = 0 by simp
  smul_mem' := fun r X (hX : Xᴴ = -X ∧ X.trace = 0) =>
    show (r • X)ᴴ = -(r • X) ∧ (r • X).trace = 0 by
      rw [Matrix.conjTranspose_smul, hX.1, star_trivial, Matrix.trace_smul, hX.2]
      exact ⟨by rw [smul_neg], by simp⟩

/-- Where the ten symmetric states sit among the sixteen. -/
def planeIdx (f : Fin 10) : Fin 16 := Fin.natAdd 6 f

/-- The index of a generator among the sixteen observables. -/
def genIdx : Fin 5 ⊕ Fin 10 → Fin 16
  | Sum.inl s => lineIdx s
  | Sum.inr f => planeIdx f

theorem genIdx_injective : Function.Injective genIdx := by
  decide

/-- **The fifteen generators:** `i γ_s` (five) and `i (i γ_s γ_t)` (ten). -/
noncomputable def gen (x : Fin 5 ⊕ Fin 10) : Matrix Four Four ℂ := I • obs (genIdx x)

theorem obs_trace (k : Fin 16) : (obs k).trace = if k = 0 then 4 else 0 := by
  have := trace_obs_mul k 0
  simpa [obs] using this

theorem genIdx_ne_zero (x : Fin 5 ⊕ Fin 10) : genIdx x ≠ 0 := by
  revert x
  decide

theorem gen_mem (x : Fin 5 ⊕ Fin 10) : gen x ∈ su4 := by
  refine ⟨?_, ?_⟩
  · rw [gen, Matrix.conjTranspose_smul, obs_conjTranspose]
    simp
  · rw [gen, Matrix.trace_smul, obs_trace]
    simp [genIdx_ne_zero x]

/-- Multiplication by `i`, a real-linear map. -/
def mulI : Matrix Four Four ℂ →ₗ[ℝ] Matrix Four Four ℂ where
  toFun X := I • X
  map_add' X Y := smul_add I X Y
  map_smul' r X := smul_comm I r X

theorem gen_linearIndependent : LinearIndependent ℝ gen := by
  have h1 : LinearIndependent ℝ (obs ∘ genIdx) :=
    obs_linearIndependent_real.comp _ genIdx_injective
  have hker : LinearMap.ker mulI = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro X hX
    have : I • X = 0 := hX
    simpa using this
  exact h1.map' mulI hker

/-- Every generator is a real combination of the fifteen. -/
theorem su4_eq_span : su4 = Submodule.span ℝ (Set.range gen) := by
  apply le_antisymm
  · intro X hX
    obtain ⟨hXa, hXt⟩ := hX
    have hH : ((-I) • X)ᴴ = (-I) • X := by
      rw [Matrix.conjTranspose_smul, hXa]
      simp
    have hexp := hermitian_expand _ hH
    have hc0 : (τ ((-I) • X * obs 0)).re = 0 := by
      simp [τ, obs, Matrix.trace_smul, hXt]
    have hX' : X = ∑ k, ((τ ((-I) • X * obs k)).re : ℂ) • (I • obs k) := by
      calc X = I • ((-I) • X) := by
            rw [smul_smul]
            simp
        _ = I • ∑ k, ((τ ((-I) • X * obs k)).re : ℂ) • obs k := by rw [← hexp]
        _ = ∑ k, ((τ ((-I) • X * obs k)).re : ℂ) • (I • obs k) := by
            rw [Finset.smul_sum]
            exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
    rw [hX']
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : k = 0
    · subst hk
      rw [hc0]
      simp
    · have hk' : ∃ x, genIdx x = k := by
        revert hk
        revert k
        decide
      obtain ⟨x, rfl⟩ := hk'
      rw [Complex.coe_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact gen_mem x

/-- **There are fifteen rotations:** the generators form a real space of dimension 15. -/
theorem finrank_su4 : Module.finrank ℝ su4 = 15 := by
  rw [su4_eq_span, finrank_span_eq_card gen_linearIndependent]
  simp

/-- How a generator moves the join: `X ↦ X J + J Xᵀ`. -/
noncomputable def joinMap : Matrix Four Four ℂ →ₗ[ℝ] Matrix Four Four ℂ where
  toFun X := X * J + J * Xᵀ
  map_add' X Y := by
    rw [Matrix.add_mul, Matrix.transpose_add, Matrix.mul_add]
    abel
  map_smul' r X := by
    simp [smul_add]

theorem obs_transpose (k : Fin 16) : (obs k)ᵀ = (obs k).map star := by
  ext i j
  have := congrFun (congrFun (obs_conjTranspose k) j) i
  simp only [Matrix.conjTranspose_apply] at this
  simp [← this]

theorem obsParity_sq (k : Fin 16) : obsParity k * obsParity k = 1 := by
  fin_cases k <;> simp [obsParity]

/-- `X J + J Xᵀ = (1 + parity) X J` on the sixteen observables. -/
theorem obs_join (k : Fin 16) :
    obs k * J + J * (obs k)ᵀ = (1 + obsParity k) • (obs k * J) := by
  have h := obs_mul_J k
  have h2 : J * (obs k).map star = obsParity k • (obs k * J) := by
    rw [h, smul_smul, obsParity_sq, one_smul]
  rw [obs_transpose, h2, add_smul, one_smul]

/-- **The five `i γ_s` move the join:** `X J + J Xᵀ = 2 i γ_s J`. -/
theorem line_turns_singlet (s : Fin 5) : joinMap (gen (Sum.inl s)) = (2 * I) • (γ s * J) := by
  change gen (Sum.inl s) * J + J * (gen (Sum.inl s))ᵀ = _
  rw [gen, Matrix.smul_mul, Matrix.transpose_smul, Matrix.mul_smul, ← smul_add, obs_join]
  have hp : obsParity (genIdx (Sum.inl s)) = 1 := by
    fin_cases s <;> rfl
  rw [hp, smul_smul]
  simp only [genIdx, obs_lineIdx]
  congr 1
  ring

/-- **The ten symmetric states keep the join:** `X J + J Xᵀ = 0`. -/
theorem plane_keeps_singlet (f : Fin 10) : joinMap (gen (Sum.inr f)) = 0 := by
  change gen (Sum.inr f) * J + J * (gen (Sum.inr f))ᵀ = _
  rw [gen, Matrix.smul_mul, Matrix.transpose_smul, Matrix.mul_smul, ← smul_add, obs_join]
  have hp : obsParity (genIdx (Sum.inr f)) = -1 := by
    fin_cases f <;> rfl
  rw [hp]
  simp

/-- The generators that keep the join: `sp(2)`. -/
noncomputable def sp2 : Submodule ℝ (Matrix Four Four ℂ) := su4 ⊓ LinearMap.ker joinMap

theorem γ_linearIndependent_real : LinearIndependent ℝ γ := by
  have h := obs_linearIndependent_real.comp lineIdx (by decide)
  convert h using 1
  funext s
  simp [obs_lineIdx]

/-- **The rotations that keep the join are the ten symmetric states.** -/
theorem sp2_eq_span : sp2 = Submodule.span ℝ (Set.range fun f : Fin 10 => gen (Sum.inr f)) := by
  apply le_antisymm
  · intro X hXmem
    rw [sp2, Submodule.mem_inf] at hXmem
    obtain ⟨hX, hker⟩ := hXmem
    rw [su4_eq_span, Submodule.mem_span_range_iff_exists_fun] at hX
    obtain ⟨c, rfl⟩ := hX
    rw [LinearMap.mem_ker, map_sum] at hker
    simp only [map_smul, Fintype.sum_sum_type, line_turns_singlet, plane_keeps_singlet, smul_zero,
      Finset.sum_const_zero, add_zero] at hker
    have hline : ∀ s, c (Sum.inl s) = 0 := by
      have h1 : (∑ s, c (Sum.inl s) • γ s) * J = 0 := by
        have : (2 * I) • ((∑ s, c (Sum.inl s) • γ s) * J) = 0 := by
          rw [Finset.sum_mul, Finset.smul_sum]
          rw [← hker]
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [Matrix.smul_mul, smul_comm]
        rcases smul_eq_zero.mp this with h | h
        · norm_num at h
        · exact h
      have h2 : ∑ s, c (Sum.inl s) • γ s = 0 := by
        have := congrArg (· * Jᴴ) h1
        simpa [Matrix.mul_assoc, J_mul_conjTranspose] using this
      exact (Fintype.linearIndependent_iff.mp γ_linearIndependent_real) _ h2
    rw [Fintype.sum_sum_type]
    simp only [hline, zero_smul, Finset.sum_const_zero, zero_add]
    exact Submodule.sum_mem _ fun f _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨f, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨f, rfl⟩
    exact ⟨gen_mem _, plane_keeps_singlet f⟩

/-- **Ten of the fifteen rotations keep the join.** -/
theorem finrank_sp2 : Module.finrank ℝ sp2 = 10 := by
  rw [sp2_eq_span, finrank_span_eq_card]
  · simp
  · exact gen_linearIndependent.comp _ Sum.inr_injective

/-- The five that move the join, and the ten that keep it, make all fifteen. -/
theorem fifteen_eq_ten_add_five :
    Module.finrank ℝ su4 = Module.finrank ℝ sp2 + 5 := by
  rw [finrank_su4, finrank_sp2]

/-- **A unitary keeps the quaternionic structure exactly when it keeps the join:** `U Θ = Θ U ⟺ U J Uᵀ = J`. -/
theorem keeps_partner_iff (U : Matrix Four Four ℂ) (hU : U * Uᴴ = 1) :
    (∀ v, U *ᵥ Θ v = Θ (U *ᵥ v)) ↔ U * J * Uᵀ = J := by
  rw [commutes_Θ_iff]
  have h1 : U.map star * Uᵀ = 1 := by
    have := congrArg Matrix.transpose hU
    rw [Matrix.transpose_mul, Matrix.transpose_one] at this
    rw [← this]
    ext i j
    simp [Matrix.mul_apply, mul_comm]
  have h2 : Uᵀ * U.map star = 1 := mul_eq_one_comm.mp h1
  constructor
  · intro h
    rw [h, Matrix.mul_assoc, h1, Matrix.mul_one]
  · intro h
    calc U * J = U * J * (Uᵀ * U.map star) := by rw [h2, Matrix.mul_one]
      _ = U * J * Uᵀ * U.map star := by simp only [Matrix.mul_assoc]
      _ = J * U.map star := by rw [h]

end Comparison

end
