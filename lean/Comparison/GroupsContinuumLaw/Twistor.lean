import Comparison.Elements.Overlap
import Comparison.Elements.TwoThings

/-!
# The sphere of lines is `ℍP¹`, and the twistor map `ℂP³ → S⁴` has fibre `ℂP¹` (Prop. 8)

A two-dimensional subspace of `H = ℂ⁴` kept by `Θ` (a quaternionic line of `ℍ² = ℂ⁴`) is given by
its orthogonal projector `P`: Hermitian, `P² = P`, `tr P = 2`, `PΘ = ΘP` (`IsQProj`).

* `side_isQProj`, `qproj_eq_side`, `side_injective`: **`n ↦ Q_n` is a bijection from the unit
  sphere `S⁴` of `Q = ℝ⁵` onto the quaternionic lines**; `sphereEquivHP1` packages it.
* `twistor_projector`: **`|ψ|² + γ(n(ψ)) = 2(|ψ⟩⟨ψ| + |Θψ⟩⟨Θψ|)`** for every state, so
  `side_lineOf`: `Q_{n(ψ)} = |ψ⟩⟨ψ| + |Θψ⟩⟨Θψ|`, the projector onto `span{ψ, Θψ}`;
* `lineOf_phase`: `n(cψ) = |c|² n(ψ)`, so `n` is a map of `ℂP³`;
* `fibre_iff`: **for unit states, `n(φ) = n(ψ)` iff `φ ∈ span{ψ, Θψ}`**; `Θ_orth`, `Θ_norm`: `ψ` and
  `Θψ` are orthonormal, so the fibre is the unit sphere of a two-dimensional space up to phase:
  `ℂP¹`.
-/

namespace Comparison.GroupsContinuumLaw

open Matrix hiding J
open Complex

noncomputable section

/-! ## The quaternionic lines -/

/-- The orthogonal projector of a two-dimensional subspace kept by `Θ`. -/
def IsQProj (P : Matrix Four Four ℂ) : Prop :=
  Pᴴ = P ∧ P * P = P ∧ P.trace = 2 ∧ P * J = J * P.map star

theorem γv_isDistinction (n : Fin 5 → ℝ) : IsDistinction (γv n) := sum_isDistinction n

theorem commutes_lin (X Y : Matrix Four Four ℂ) (hX : X * J = J * X.map star)
    (hY : Y * J = J * Y.map star) (a b : ℝ) :
    ((a : ℂ) • X + (b : ℂ) • Y) * J = J * ((a : ℂ) • X + (b : ℂ) • Y).map star := by
  rw [← commutes_Θ_iff] at hX hY ⊢
  intro v
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, hX, hY, Θ_add, Θ_smul, Complex.star_def,
    Complex.conj_ofReal]

theorem one_commutes : (1 : Matrix Four Four ℂ) * J = J * (1 : Matrix Four Four ℂ).map star := by
  rw [← commutes_Θ_iff]
  intro v
  simp

/-- **Each side of a unit line is a quaternionic line.** -/
theorem side_isQProj (n : Fin 5 → ℝ) (hn : ∑ s, n s ^ 2 = 1) : IsQProj (side n) := by
  obtain ⟨h1, -, h3⟩ := γv_isDistinction n
  refine ⟨?_, side_mul_self n hn, trace_side n, ?_⟩
  · simp [side, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, h1]
  · have e : side n = ((1 / 2 : ℝ) : ℂ) • (1 : Matrix Four Four ℂ) + ((1 / 2 : ℝ) : ℂ) • γv n := by
      rw [side, smul_add]
      push_cast
      rfl
    rw [e]
    exact commutes_lin _ _ one_commutes h3 _ _

/-- **Every quaternionic line is the side of a unit line.** -/
theorem qproj_eq_side (P : Matrix Four Four ℂ) (hP : IsQProj P) :
    ∃ n : Fin 5 → ℝ, ∑ s, n s ^ 2 = 1 ∧ P = side n := by
  obtain ⟨h1, h2, h3, h4⟩ := hP
  set A := (2 : ℂ) • P - 1 with hA
  have hAd : IsDistinction A := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hA, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, h1, Matrix.conjTranspose_one]
      simp
    · rw [hA, Matrix.trace_sub, Matrix.trace_smul, h3, Matrix.trace_one]
      simp [Four]
      norm_num
    · have e : A = ((2 : ℝ) : ℂ) • P + ((-1 : ℝ) : ℂ) • (1 : Matrix Four Four ℂ) := by
        rw [hA]
        push_cast
        module
      rw [e]
      exact commutes_lin _ _ h4 one_commutes _ _
  have hAA : A * A = 1 := by
    rw [hA]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, h2, smul_smul]
    module
  have hsq := distinction_sq A hAd
  rw [hAA] at hsq
  have hn : ∑ s, coord A s ^ 2 = 1 := by
    have := congrFun (congrFun hsq (0, 0)) (0, 0)
    simp at this
    exact_mod_cast this.symm
  refine ⟨coord A, hn, ?_⟩
  have hAγ : A = γv (coord A) := eq_sum_coord A hAd
  rw [side, ← hAγ, hA]
  module

theorem side_injective : Function.Injective side := by
  intro n m h
  have h' : γv n = γv m := by
    have := congrArg (fun X => (2 : ℂ) • X - 1) h
    simp only [side, smul_smul] at this
    norm_num at this
    exact this
  have := congrArg coord h'
  rwa [γv, γv, coord_sum, coord_sum] at this

/-- **`S⁴ = ℍP¹`:** the unit lines and the quaternionic lines, one to one. -/
def sphereEquivHP1 : {n : Fin 5 → ℝ // ∑ s, n s ^ 2 = 1} ≃ {P : Matrix Four Four ℂ // IsQProj P} where
  toFun n := ⟨side n.1, side_isQProj n.1 n.2⟩
  invFun P := ⟨(qproj_eq_side P.1 P.2).choose, (qproj_eq_side P.1 P.2).choose_spec.1⟩
  left_inv n := by
    apply Subtype.ext
    apply side_injective
    exact ((qproj_eq_side (side n.1) (side_isQProj n.1 n.2)).choose_spec.2).symm
  right_inv P := by
    apply Subtype.ext
    exact ((qproj_eq_side P.1 P.2).choose_spec.2).symm

/-! ## The twistor map -/

set_option maxHeartbeats 8000000 in
/-- **`|ψ|² + γ(n(ψ)) = 2(|ψ⟩⟨ψ| + |Θψ⟩⟨Θψ|)`.** -/
theorem twistor_projector (ψ : Four → ℂ) :
    (normSq ψ : ℂ) • (1 : Matrix Four Four ℂ) + γv (lineOf ψ) =
      (2 : ℂ) • (vecMulVec ψ (star ψ) + vecMulVec (Θ ψ) (star (Θ ψ))) := by
  four_ext <;> apply Complex.ext <;>
    simp [normSq, lineOf, γv, γ, σ₁, σ₂, σ₃, Θ, J, ε, Matrix.vecMulVec_apply, Matrix.mulVec,
      dotProduct, Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_five, Matrix.one_apply] <;>
    ring

/-- **`Q_{n(ψ)} = |ψ⟩⟨ψ| + |Θψ⟩⟨Θψ|`** for a unit state. -/
theorem side_lineOf (ψ : Four → ℂ) (hψ : normSq ψ = 1) :
    side (lineOf ψ) = vecMulVec ψ (star ψ) + vecMulVec (Θ ψ) (star (Θ ψ)) := by
  have h := twistor_projector ψ
  rw [hψ, Complex.ofReal_one, one_smul] at h
  rw [side, h, smul_smul]
  norm_num

/-- The line of a state depends only on the state up to a factor: `n(cψ) = |c|² n(ψ)`. -/
theorem lineOf_phase (c : ℂ) (ψ : Four → ℂ) (s : Fin 5) :
    lineOf (c • ψ) s = Complex.normSq c * lineOf ψ s := by
  simp only [lineOf, Matrix.mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
  rw [← mul_assoc, show c * star c = ((Complex.normSq c : ℝ) : ℂ) from Complex.mul_conj c,
    Complex.re_ofReal_mul]

theorem vecMulVec_mulVec' (a b v : Four → ℂ) :
    vecMulVec a (star b) *ᵥ v = (star b ⬝ᵥ v) • a := by
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Finset.mul_sum, mul_comm, mul_left_comm]

theorem dot_Θ_self (ψ : Four → ℂ) : star (Θ ψ) ⬝ᵥ ψ = 0 := by
  have h := Θ_orth ψ
  have : star (Θ ψ) ⬝ᵥ ψ = star (star ψ ⬝ᵥ Θ ψ) := by
    simp [dotProduct, star_sum, mul_comm]
  rw [this, h, star_zero]

theorem normSq_Θ (ψ : Four → ℂ) : star (Θ ψ) ⬝ᵥ Θ ψ = star ψ ⬝ᵥ ψ := Θ_norm ψ

/-- The side of `n(ψ)` holds `ψ` and `Θψ`. -/
theorem side_lineOf_fixes (ψ : Four → ℂ) (hψ : normSq ψ = 1) :
    side (lineOf ψ) *ᵥ ψ = ψ ∧ side (lineOf ψ) *ᵥ Θ ψ = Θ ψ := by
  have h1 : star ψ ⬝ᵥ ψ = 1 := by rw [dot_self_eq, hψ, Complex.ofReal_one]
  rw [side_lineOf ψ hψ, Matrix.add_mulVec, Matrix.add_mulVec, vecMulVec_mulVec',
    vecMulVec_mulVec', vecMulVec_mulVec', vecMulVec_mulVec', h1, dot_Θ_self, Θ_orth,
    normSq_Θ, h1]
  simp

/-- On the plus side of a unit line, a unit state has that line. -/
theorem lineOf_of_side (n : Fin 5 → ℝ) (hn : ∑ s, n s ^ 2 = 1) (φ : Four → ℂ)
    (hφ : normSq φ = 1) (h : side n *ᵥ φ = φ) : lineOf φ = n := by
  have hγ : γv n *ᵥ φ = φ := by
    have e : side n *ᵥ φ = (1 / 2 : ℂ) • (φ + γv n *ᵥ φ) := by
      rw [side, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec]
    rw [e] at h
    calc γv n *ᵥ φ = (2 : ℂ) • ((1 / 2 : ℂ) • (φ + γv n *ᵥ φ)) - φ := by module
      _ = (2 : ℂ) • φ - φ := by rw [h]
      _ = φ := by module
  funext s
  have hanti := anticomm_γv n (Pi.single s 1)
  have hγs : γv (Pi.single s 1) = γ s := by
    simp [γv, Pi.single_apply]
  rw [hγs] at hanti
  have hsum : ∑ k, n k * (Pi.single s (1 : ℝ) : Fin 5 → ℝ) k = n s := by
    simp [Pi.single_apply]
  rw [hsum] at hanti
  have h1 : star φ ⬝ᵥ φ = 1 := by rw [dot_self_eq, hφ, Complex.ofReal_one]
  have key := congrArg (fun M => star φ ⬝ᵥ (M *ᵥ φ)) hanti
  simp only [Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, h1, smul_eq_mul, mul_one, ← Matrix.mulVec_mulVec, hγ] at key
  have hH : star φ ⬝ᵥ (γv n *ᵥ (γ s *ᵥ φ)) = star φ ⬝ᵥ (γ s *ᵥ φ) := by
    have hh : (γv n)ᴴ = γv n := (γv_isDistinction n).1
    rw [Matrix.dotProduct_mulVec]
    congr 1
    rw [← hh, ← Matrix.star_mulVec, hγ]
  rw [hH, dot_γ_eq] at key
  have := congrArg Complex.re key
  simp at this
  linarith

/-- **The fibre: for unit states, `n(φ) = n(ψ)` iff `φ ∈ span{ψ, Θψ}`.** -/
theorem fibre_iff (ψ φ : Four → ℂ) (hψ : normSq ψ = 1) (hφ : normSq φ = 1) :
    lineOf φ = lineOf ψ ↔ ∃ a b : ℂ, φ = a • ψ + b • Θ ψ := by
  constructor
  · intro h
    have hfix := (side_lineOf_fixes φ hφ).1
    rw [h, side_lineOf ψ hψ, Matrix.add_mulVec, vecMulVec_mulVec', vecMulVec_mulVec'] at hfix
    exact ⟨star ψ ⬝ᵥ φ, star (Θ ψ) ⬝ᵥ φ, hfix.symm⟩
  · rintro ⟨a, b, rfl⟩
    apply lineOf_of_side (lineOf ψ) (lineOf_unit ψ hψ) _ hφ
    obtain ⟨h1, h2⟩ := side_lineOf_fixes ψ hψ
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, h1, h2]

end

end Comparison.GroupsContinuumLaw
