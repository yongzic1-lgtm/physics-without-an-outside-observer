import Comparison.System.Postulates
import Comparison.WholePicture.Cells
import Comparison.Existence.Return
import Comparison.RuleAndLaw.RuleReadsLaw
import Comparison.System.Law.Cells

/-!
# SI S3, statements 5 to 8: the law, the cells, the signed step, positivity

About the model; every candidate system is the model up to one
rotation (`System.uniqueness`).
-/

namespace Comparison.System

open Matrix Complex Polynomial
open scoped Kronecker ComplexOrder

/-- **SI S3, statement 5: the law and its sixteen meetings.** For every `u`,
`det(I − uB) = (1 − u²)²⁴ k₀(u) k₂(u)¹⁰ k₄(u)⁵` with `k_N(u) = 1 + 4u² − u(5 − 2N)`, and,
wherever the right side is defined (`u ≠ 1`),
`det(I − uB) = ∏_U (1 + u)^{a_U − 1}(1 − u)^{d_U − 1}[1 + 4u² − u(a_U − d_U)]` over the sixteen
meetings `U`, with `a_U = 5 − |U|`, `d_U = |U|`; the sixteen meeting blocks multiply to the law. -/
theorem S3_5 :
    (∀ u : ℂ, law u = (1 - u ^ 2) ^ 24 * WholePicture.kN 0 u * WholePicture.kN 2 u ^ 10 *
      WholePicture.kN 4 u ^ 5) ∧
    (∀ u : ℂ, u ≠ 1 → law u =
      ∏ U : Fin 16, (1 + u) ^ ((WholePicture.agreeCount U : ℤ) - 1) *
        (1 - u) ^ ((WholePicture.disagreeCount U : ℤ) - 1) *
        (1 + 4 * u ^ 2 -
          u * ((WholePicture.agreeCount U : ℂ) - (WholePicture.disagreeCount U : ℂ)))) ∧
    (∀ U : Fin 16, WholePicture.agreeCount U = 5 - (disagreeSet U).card ∧
      WholePicture.disagreeCount U = (disagreeSet U).card) ∧
    (∀ u : ℂ, ∏ U : Fin 16, (1 - u • Law.patternK (R := ℂ) (disagreeSet U)).det = law u) := by
  refine ⟨fun u => ?_, fun u hu => ?_, fun U => ⟨rfl, rfl⟩, fun u => ?_⟩
  · rw [law_eq_D_plus]
    exact WholePicture.law_grade_factors u
  · rw [law_eq_D_plus]
    exact WholePicture.law_over_meetings u hu
  · rw [law_eq_D_plus]
    exact Law.law_meetings u

/-- **SI S3, statement 6: the cells of the real projective four-space.** The two-spinor states and their
steps are the cells of `ℝP⁴`: 16 two-spinor states, 40 links (each a pair of neighbours), 40 squares, 20
cubes (every cube of the five-cube with the whole flip appears once) and 5 four-cells; the boundary
of a boundary is nothing (`∂∂ = 0`, over `ℤ/2`, and with orientations over `ℤ` in every degree);
there is one class in each dimension mod 2, `dim(ker ∂_k / im ∂_{k+1}) = 1` for `k = 0, …, 4`; the
Euler number is one; the circulation `C` of link phases around the squares annihilates the gradients
(`C · grad = 0`, over `ℤ`), `rank C = 25` and `det(X − CᵀC) = X¹⁵(X − 4)¹⁰(X − 8)¹⁵`. -/
theorem S3_6 :
    (Finset.univ.filter fun p : Fin 16 × Fin 16 => p.1 < p.2 ∧ Adjacent p.1 p.2).card = 40 ∧
    (∀ l : Fin 40, transition (WholePicture.linkLine l) (linkU l) = linkV l) ∧
    (∀ q : Fin 40, (WholePicture.sqSet q).card = 4) ∧
    (∀ (x : Fin 16) (a b d : Fin 5), a < b → b < d →
      ∃ c : Fin 20, WholePicture.cubeSet c = WholePicture.cubeOf x a b d ∧
        WholePicture.cubeA c = a ∧ WholePicture.cubeB c = b ∧ WholePicture.cubeD c = d) ∧
    (∀ c : Fin 20, (WholePicture.cubeSet c).card = 8) ∧
    (WholePicture.bd1 * WholePicture.bd2 = 0 ∧ WholePicture.bd2 * WholePicture.bd3 = 0 ∧
      WholePicture.bd3 * WholePicture.bd4 = 0) ∧
    (WholePicture.cMat * Law.gradZ' = 0 ∧ Law.cubeBdZ * WholePicture.cMat = 0 ∧
      Law.fourBdZ * Law.cubeBdZ = 0) ∧
    (Module.finrank (ZMod 2) (LinearMap.ker (0 : Matrix (Fin 0) (Fin 16) (ZMod 2)).mulVecLin ⧸
        (LinearMap.range WholePicture.bd1.mulVecLin).comap
          (LinearMap.ker (0 : Matrix (Fin 0) (Fin 16) (ZMod 2)).mulVecLin).subtype) = 1 ∧
      Module.finrank (ZMod 2) (LinearMap.ker WholePicture.bd1.mulVecLin ⧸
        (LinearMap.range WholePicture.bd2.mulVecLin).comap
          (LinearMap.ker WholePicture.bd1.mulVecLin).subtype) = 1 ∧
      Module.finrank (ZMod 2) (LinearMap.ker WholePicture.bd2.mulVecLin ⧸
        (LinearMap.range WholePicture.bd3.mulVecLin).comap
          (LinearMap.ker WholePicture.bd2.mulVecLin).subtype) = 1 ∧
      Module.finrank (ZMod 2) (LinearMap.ker WholePicture.bd3.mulVecLin ⧸
        (LinearMap.range WholePicture.bd4.mulVecLin).comap
          (LinearMap.ker WholePicture.bd3.mulVecLin).subtype) = 1 ∧
      Module.finrank (ZMod 2) (LinearMap.ker WholePicture.bd4.mulVecLin ⧸
        (LinearMap.range (0 : Matrix (Fin 5) (Fin 0) (ZMod 2)).mulVecLin).comap
          (LinearMap.ker WholePicture.bd4.mulVecLin).subtype) = 1) ∧
    ((16 : ℤ) - 40 + 40 - 20 + 5 = 1) ∧
    (∀ (q : Fin 40) (x : Fin 16),
      ∑ l : Fin 40,
        cZ q l * ((if linkV l = x then 1 else 0) - (if linkU l = x then 1 else 0)) = 0) ∧
    WholePicture.cReal.rank = 25 ∧
    (WholePicture.cRealᵀ * WholePicture.cReal).charpoly =
      X ^ 15 * (X - C (4 : ℝ)) ^ 10 * (X - C (8 : ℝ)) ^ 15 := by
  exact ⟨card_edges, WholePicture.linkLine_spec, WholePicture.card_sqSet,
    WholePicture.cubes_complete, WholePicture.card_cubeSet, WholePicture.bd_bd, Law.bd_bd_int,
    WholePicture.homology_mod_two, WholePicture.euler_number, cZ_div,
    WholePicture.rank_cReal, WholePicture.cReal_gram_charpoly⟩

/-- **SI S3, statement 7: the signed step.** `A₋ = A₋ᵀ`, `A₋² = 5I`,
`det(I − uB₋) = (1 − u²)²⁴(1 + 3u² + 16u⁴)⁸` for every `u`, and at the four points `u = i^d/4` `u = i^k/4`,
`1 − 1/R₋(u) = Φ(i^k)` with `R₋(u) = (1 + 3u²)/(1 + 3u² + 16u⁴)` and `Φ(z) = −z⁴/(16 + 3z²)`. -/
theorem S3_7 :
    Aminusᵀ = Aminus ∧ Aminus * Aminus = (5 : ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ) ∧
    (∀ u : ℂ, (1 - u • Bminus).det = (1 - u ^ 2) ^ 24 * (1 + 3 * u ^ 2 + 16 * u ^ 4) ^ 8) ∧
    (∀ k : ℕ, 1 - 1 / ((1 + 3 * (I ^ k / 4) ^ 2) /
        (1 + 3 * (I ^ k / 4) ^ 2 + 16 * (I ^ k / 4) ^ 4)) = Law.Phi (I ^ k)) := by
  refine ⟨sadjZ_transpose, sadjZ_sq, D_minus, fun k => ?_⟩
  have hk : (I ^ k) ^ 2 = 1 ∨ (I ^ k) ^ 2 = -1 := by
    rw [← pow_mul, mul_comm, pow_mul, I_sq]
    rcases Nat.even_or_odd k with he | ho
    · exact Or.inl he.neg_one_pow
    · exact Or.inr ho.neg_one_pow
  have h4 : (I ^ k) ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
    rcases hk with h | h <;> rw [h] <;> norm_num
  rw [Law.Phi]
  rcases hk with h | h
  · have e2 : (I ^ k / 4) ^ 2 = 1 / 16 := by rw [div_pow, h]; norm_num
    have e4 : (I ^ k / 4) ^ 4 = 1 / 256 := by rw [div_pow, h4]; norm_num
    rw [e2, e4, h4, h]
    norm_num
  · have e2 : (I ^ k / 4) ^ 2 = -1 / 16 := by rw [div_pow, h]; norm_num
    have e4 : (I ^ k / 4) ^ 4 = 1 / 256 := by rw [div_pow, h4]; norm_num
    rw [e2, e4, h4, h]
    norm_num

/-- **SI S3, statement 8: positivity below the critical step.** For every unitary connection `U` on
the links (rotations of any size `n`) the operator `(1 + 4u²) − uA_U`, `A_U = Σ_t Γ_t[U]`, is Hermitian,
and for `0 ≤ u < 1/4` it is bounded below by `(1 − u)(1 − 4u) > 0`:
`Re⟨x, ((1 + 4u²) − uA_U)x⟩ ≥ (1 − u)(1 − 4u)⟨x, x⟩` for every `x`. So the law has no zero there:
`det(I − uB[U]) > 0`. -/
theorem S3_8 {n : Type*} [Fintype n] [DecidableEq n]
    (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ)) (u : ℝ) (hu0 : 0 ≤ u) (hu : u < 1 / 4) :
    ((1 + 4 * (u : ℂ) ^ 2) • (1 : Matrix (Fin 16 × n) (Fin 16 × n) ℂ) -
        (u : ℂ) • ∑ t, WholePicture.connStep c t)ᴴ =
      (1 + 4 * (u : ℂ) ^ 2) • (1 : Matrix (Fin 16 × n) (Fin 16 × n) ℂ) -
        (u : ℂ) • ∑ t, WholePicture.connStep c t ∧
    (∀ x : Fin 16 × n → ℂ, (1 - u) * (1 - 4 * u) * (star x ⬝ᵥ x).re ≤
      (star x ⬝ᵥ (((1 + 4 * (u : ℂ) ^ 2) • (1 : Matrix (Fin 16 × n) (Fin 16 × n) ℂ) -
        (u : ℂ) • ∑ t, WholePicture.connStep c t) *ᵥ x)).re) ∧
    0 < (1 - u) * (1 - 4 * u) ∧
    0 < (1 - (u : ℂ) • Bconn c).det := by
  refine ⟨?_, WholePicture.law_quad_unitary c u hu0, by nlinarith,
    WholePicture.law_weight_pos_unitary c u hu0 hu⟩
  have h1 : star (1 + 4 * (u : ℂ) ^ 2) = 1 + 4 * (u : ℂ) ^ 2 := by
    rw [show (1 + 4 * (u : ℂ) ^ 2) = ((1 + 4 * u ^ 2 : ℝ) : ℂ) by push_cast; ring]
    exact Complex.conj_ofReal _
  have h2 : star (u : ℂ) = (u : ℂ) := Complex.conj_ofReal u
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_one, Matrix.conjTranspose_sum, h1, h2]
  simp only [WholePicture.connStep_herm]

end Comparison.System
