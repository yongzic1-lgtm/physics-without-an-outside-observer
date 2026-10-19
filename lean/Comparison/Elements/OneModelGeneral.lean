module

public import Comparison.Elements.Partner

/-!
# Proposition 23: P1 to P3 have one model

For every finite-dimensional complex inner-product space `H` with a quaternionic structure `T` (P1, P3 (a)),
the distinctions of P3 (b) are the self-adjoint operators of trace zero that commute with `Θ`
(`IsDistinctionH`), and `P3H T` says that some distinction is not zero and every distinction
squares to a real number.

* `isDistinctionH_iff`: in a normal basis of the quaternionic structure, an operator is a distinction exactly
  when its matrix is a distinction of the standard model `(ℂ^{2n}, J_n K)`.
* `P3H_iff`: `P3H T ⟺ P3 n` for the normal basis of size `n`.
* `one_model_general`: **`P3H T ⟺ dim H = 4`.** With `exists_normal_basis` and `coord_Θ` this is
  Proposition 23: every model of P1 to P3 is `ℂ⁴` with the quaternionic structure `J₀ K`, up to a unitary map.
-/

@[expose] public section

namespace Comparison

open scoped InnerProductSpace
open Matrix hiding J
open Complex Kronecker

namespace Partner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
variable (T : Partner H)

/-- A distinction of `(H, Θ)` (P3 (b)): self-adjoint, of trace zero, commuting with the quaternionic structure. -/
def IsDistinctionH (a : H →ₗ[ℂ] H) : Prop :=
  IsSelfAdjoint a ∧ LinearMap.trace ℂ H a = 0 ∧ ∀ v, a (T.Θ v) = T.Θ (a v)

/-- P3's second clause for `(H, Θ)`: some distinction is not zero, and every distinction squares
to a real number. -/
def P3H : Prop :=
  (∃ a, T.IsDistinctionH a ∧ a ≠ 0) ∧
    ∀ a, T.IsDistinctionH a → ∃ c : ℝ, a * a = (c : ℂ) • (1 : H →ₗ[ℂ] H)

variable {ι : Type*} [Fintype ι]

/-- The coordinates of `a v` are the matrix of `a` times the coordinates of `v`. -/
theorem coord_apply [DecidableEq ι] (b : OrthonormalBasis ι ℂ H) (a : H →ₗ[ℂ] H) (v : H) (p : ι) :
    ⟪b p, a v⟫_ℂ = (LinearMap.toMatrixOrthonormal b a *ᵥ fun q => ⟪b q, v⟫_ℂ) p := by
  conv_lhs => rw [← b.sum_repr' v, map_sum]
  rw [inner_sum]
  simp only [LinearMap.map_smul, inner_smul_right, Matrix.mulVec, dotProduct,
    LinearMap.toMatrixOrthonormal_apply_apply]
  exact Finset.sum_congr rfl fun q _ => mul_comm _ _

omit [FiniteDimensional ℂ H] in
theorem eq_of_coord (b : OrthonormalBasis ι ℂ H) {v w : H}
    (h : ∀ p, ⟪b p, v⟫_ℂ = ⟪b p, w⟫_ℂ) : v = w := by
  rw [← b.sum_repr' v, ← b.sum_repr' w]
  simp only [h]

omit [FiniteDimensional ℂ H] in
theorem exists_coord (b : OrthonormalBasis ι ℂ H) (x : ι → ℂ) :
    ∃ v : H, ∀ p, ⟪b p, v⟫_ℂ = x p := by
  classical
  refine ⟨∑ q, x q • b q, fun p => ?_⟩
  simp only [inner_sum, inner_smul_right, orthonormal_iff_ite.mp b.orthonormal, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem star_mulVec_map (M : Matrix ι ι ℂ) (x : ι → ℂ) :
    star (M *ᵥ x) = M.map star *ᵥ star x := by
  ext i
  simp [Matrix.mulVec, dotProduct, star_sum]

/-- **In a normal basis, a distinction of `(H, Θ)` is a distinction of the standard model.** -/
theorem isDistinctionH_iff {n : ℕ} (b : OrthonormalBasis (Fin n × Fin 2) ℂ H)
    (hb : ∀ k, b (k, 1) = -T.Θ (b (k, 0))) (a : H →ₗ[ℂ] H) :
    T.IsDistinctionH a ↔ IsDistinctionN n (LinearMap.toMatrixOrthonormal b a) := by
  set M := LinearMap.toMatrixOrthonormal b a with hM
  have hsa : IsSelfAdjoint a ↔ Mᴴ = M := by
    rw [IsSelfAdjoint, hM, ← Matrix.star_eq_conjTranspose, ← map_star]
    exact (LinearMap.toMatrixOrthonormal b).injective.eq_iff.symm
  have htr : LinearMap.trace ℂ H a = M.trace := by
    rw [LinearMap.trace_eq_matrix_trace ℂ b.toBasis]
    rfl
  have hΘ : (∀ v, a (T.Θ v) = T.Θ (a v)) ↔ M * Jn n = Jn n * M.map star := by
    constructor
    · intro h
      rw [Matrix.ext_iff_mulVec]
      intro w
      obtain ⟨v, hv⟩ := exists_coord b (star w)
      have hcv : (fun q => ⟪b q, v⟫_ℂ) = star w := funext hv
      ext p
      have e := congrArg (fun z => ⟪b p, z⟫_ℂ) (h v)
      rw [coord_apply, T.coord_Θ b hb] at e
      have hav : (fun q => ⟪b q, a v⟫_ℂ) = M *ᵥ (fun q => ⟪b q, v⟫_ℂ) := by
        funext q
        exact coord_apply b a v q
      have hΘv : (fun q => ⟪b q, T.Θ v⟫_ℂ) = Jn n *ᵥ star (fun q => ⟪b q, v⟫_ℂ) := by
        funext q
        exact T.coord_Θ b hb v q
      rw [hΘv] at e
      rw [show (fun q => star ⟪b q, a v⟫_ℂ) = star (fun q => ⟪b q, a v⟫_ℂ) from rfl, hav,
        star_mulVec_map, hcv, star_star] at e
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact e
    · intro h v
      apply eq_of_coord b
      intro p
      have hav : (fun q => ⟪b q, a v⟫_ℂ) = M *ᵥ (fun q => ⟪b q, v⟫_ℂ) := by
        funext q
        exact coord_apply b a v q
      have hΘv : (fun q => ⟪b q, T.Θ v⟫_ℂ) = Jn n *ᵥ star (fun q => ⟪b q, v⟫_ℂ) := by
        funext q
        exact T.coord_Θ b hb v q
      rw [coord_apply, T.coord_Θ b hb, hΘv,
        show (fun q => star ⟪b q, a v⟫_ℂ) = star (fun q => ⟪b q, a v⟫_ℂ) from rfl, hav,
        star_mulVec_map, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]
  rw [IsDistinctionH, IsDistinctionN, hsa, htr, hΘ]

/-- **P3 for `(H, Θ)` is P3 for the standard model of the same size.** -/
theorem P3H_iff {n : ℕ} (b : OrthonormalBasis (Fin n × Fin 2) ℂ H)
    (hb : ∀ k, b (k, 1) = -T.Θ (b (k, 0))) : T.P3H ↔ P3 n := by
  set e := LinearMap.toMatrixOrthonormal b with he
  have hsq : ∀ (a : H →ₗ[ℂ] H) (c : ℝ),
      a * a = (c : ℂ) • (1 : H →ₗ[ℂ] H) ↔
        e a * e a = (c : ℂ) • (1 : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℂ) := by
    intro a c
    rw [← _root_.map_mul, ← _root_.map_one e, ← _root_.map_smul]
    exact (EquivLike.injective e).eq_iff.symm
  constructor
  · rintro ⟨⟨a, ha, ha0⟩, hall⟩
    refine ⟨⟨e a, (T.isDistinctionH_iff b hb a).mp ha, ?_⟩, fun M hM => ?_⟩
    · intro h0
      exact ha0 (e.injective (h0.trans (_root_.map_zero e).symm))
    · obtain ⟨a, rfl⟩ := e.surjective M
      obtain ⟨c, hc⟩ := hall a ((T.isDistinctionH_iff b hb a).mpr hM)
      exact ⟨c, (hsq a c).mp hc⟩
  · rintro ⟨⟨M, hM, hM0⟩, hall⟩
    obtain ⟨a, rfl⟩ := e.surjective M
    refine ⟨⟨a, (T.isDistinctionH_iff b hb a).mpr hM, ?_⟩, fun a' ha' => ?_⟩
    · intro h0
      exact hM0 (by rw [h0, _root_.map_zero])
    · obtain ⟨c, hc⟩ := hall (e a') ((T.isDistinctionH_iff b hb a').mp ha')
      exact ⟨c, (hsq a' c).mpr hc⟩

/-- **One model (Prop. 23).** For every system `H` with a quaternionic structure, some distinction is not zero and
every distinction squares to a number exactly when `H` has four complex dimensions. -/
theorem one_model_general : T.P3H ↔ Module.finrank ℂ H = 4 := by
  obtain ⟨n, b, hb⟩ := T.exists_normal_basis
  rw [T.P3H_iff b hb, one_model, Partner.finrank_eq b]
  constructor <;> intro h <;> omega

end Partner

end Comparison

end
