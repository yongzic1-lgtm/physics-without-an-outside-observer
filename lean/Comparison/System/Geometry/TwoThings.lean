import Comparison.System.Geometry.Definitions
import Comparison.Article.Commutant2
import Comparison.Elements.MixedStates

/-!
# The geometry of comparison, Book II: two systems (Propositions 9 to 14)

* `prop_9`: the singlet is the same in every basis, its matrix is `−½` the quaternionic structure's in every basis,
  `‖Ω‖ = 1`, `PΩ = −Ω`, `(1 ⊗ X)Ω = (X♯ ⊗ 1)Ω` for **every** `X`, the ten rotations keep exactly `ℂΩ`,
  `Tr₂|Ω⟩⟨Ω| = ¼`.
* `prop_10`: the sixteen two-spinor states `e_S = ±(γ_S ⊗ 1)Ω` (even `S`), orthonormal, `n_t e_S = [t ∈ S]e_S`,
  `L e_S = (6 − 2|S|)e_S`, the spectrum `6¹ ⊕ 2¹⁰ ⊕ (−2)⁵`.
* `prop_11`: `L = 2(P + E)`, `P` on the sixteen, `L = Σ X_α ⊗ X_α` in every orthonormal basis,
  `E = |J⟩⟨J|`, `E² = 4E`, `PE = EP = −E`.
* `prop_12`: `6 − L = ½Σ(γ_s ⊗ 1 − 1 ⊗ γ_s)² = 2N ≥ 0`, zero only on `ℂΩ`, at least four on separate
  mixed states.
* `prop_13`: `X = X† = X♯ ⟺ X ∈ ℝ1 ⊕ Q`; the commutant `a + bP + cE`; the quaternionic structure on one system
  exchanges `P` and `E`; kept by both `⟺ a + b(P + E)`.
* `prop_14`: one line on one system, the Clebsch graph.
-/

open scoped InnerProductSpace Kronecker ComplexOrder
open Matrix Complex Module

namespace Comparison.System

namespace Geometry

/-! ## Proposition 9 -/

/-- `X♯ M_Ω = M_Ω Xᵀ` for every operator `X`. -/
theorem partnerOp_mul_MΩ (X : Matrix Four Four ℂ) : partnerOp X * MΩ = MΩ * Xᵀ := by
  rw [partnerOp, MΩ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.mul_assoc,
    J_conjTranspose_mul', Matrix.mul_one]

/-- **`(1 ⊗ X)Ω = (X♯ ⊗ 1)Ω` for every operator `X`.** -/
theorem kron_one_partner (X : Matrix Four Four ℂ) :
    ((1 : Matrix Four Four ℂ) ⊗ₖ X) *ᵥ Ω = (partnerOp X ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω := by
  rw [Ω, kron_mulVec_relOf, kron_mulVec_relOf, Matrix.one_mul, Matrix.transpose_one,
    Matrix.mul_one, partnerOp_mul_MΩ]

/-- The one and the distinctions: the real combinations `c·1 + Σ t_s γ_s` (`ℝ1 ⊕ Q`). -/
def InR1Q (X : Matrix Four Four ℂ) : Prop :=
  ∃ (c : ℝ) (t : Fin 5 → ℝ), X = (c : ℂ) • (1 : Matrix Four Four ℂ) + ∑ s, (t s : ℂ) • γ s

theorem partnerOp_add (X Y : Matrix Four Four ℂ) : partnerOp (X + Y) = partnerOp X + partnerOp Y := by
  simp [partnerOp, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

theorem partnerOp_smul (c : ℂ) (X : Matrix Four Four ℂ) : partnerOp (c • X) = c • partnerOp X := by
  simp [partnerOp, Matrix.transpose_smul]

theorem partnerOp_sum (f : Fin 5 → Matrix Four Four ℂ) :
    partnerOp (∑ s, f s) = ∑ s, partnerOp (f s) := by
  simp only [Fin.sum_univ_five, partnerOp_add]

theorem trace_real_of_hermitian (X : Matrix Four Four ℂ) (hX : Xᴴ = X) :
    ((X.trace.re : ℝ) : ℂ) = X.trace := by
  have h : star X.trace = X.trace := by rw [← Matrix.trace_conjTranspose, hX]
  exact Complex.conj_eq_iff_re.mp h

/-- **`X = X† = X♯ ⟺ X ∈ ℝ1 ⊕ Q`.** -/
theorem mem_R1Q_iff (X : Matrix Four Four ℂ) : (Xᴴ = X ∧ partnerOp X = X) ↔ InR1Q X := by
  constructor
  · rintro ⟨hH, hP⟩
    have hJ : X * J = J * X.map star := (partnerOp_eq_self_iff X hH).mp hP
    set c : ℝ := X.trace.re / 4 with hc
    set a : Matrix Four Four ℂ := X - (c : ℂ) • 1 with ha
    have hd : IsDistinction a := by
      refine ⟨?_, ?_, ?_⟩
      · rw [ha, Matrix.conjTranspose_sub, hH, Matrix.conjTranspose_smul, Matrix.conjTranspose_one]
        simp
      · rw [ha, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one]
        have hr := trace_real_of_hermitian X hH
        simp only [Fintype.card_prod, Fintype.card_fin, smul_eq_mul]
        rw [← hr, hc]
        push_cast
        ring
      · have hm : a.map star = X.map star - (c : ℂ) • 1 := by
          ext i j
          simp [ha, Matrix.one_apply]
          split_ifs <;> simp
        rw [hm, ha, Matrix.sub_mul, Matrix.mul_sub, hJ, Matrix.smul_mul, Matrix.mul_smul,
          Matrix.one_mul, Matrix.mul_one]
    refine ⟨c, coord a, ?_⟩
    rw [← eq_sum_coord a hd, ha]
    abel
  · rintro ⟨c, t, rfl⟩
    refine ⟨?_, ?_⟩
    · simp [Matrix.conjTranspose_add, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
        γ_conjTranspose]
    · rw [partnerOp_add, partnerOp_smul, partnerOp_one, partnerOp_sum]
      simp only [partnerOp_smul, partnerOp_γ]

/-- **`(a ⊗ 1)Ω = (1 ⊗ a)Ω` for every `a ∈ ℝ1 ⊕ Q`.** -/
theorem same_side_of_R1Q (a : Matrix Four Four ℂ) (ha : InR1Q a) :
    (a ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω = ((1 : Matrix Four Four ℂ) ⊗ₖ a) *ᵥ Ω := by
  rw [kron_one_partner, ((mem_R1Q_iff a).mpr ha).2]

/-- The matrix of the quaternionic structure in the orthonormal basis of the columns of a unitary `U`. -/
def partnerMatrixOf (U : Matrix Four Four ℂ) : Matrix Four Four ℂ := Uᴴ * J * U.map star

/-- In the basis of the columns of `U` the quaternionic structure has the matrix `partnerMatrixOf U`. -/
theorem partner_in_basis (U : Matrix Four Four ℂ) (hU : U * Uᴴ = 1) (v : Four → ℂ) :
    Θ (U *ᵥ v) = U *ᵥ (partnerMatrixOf U *ᵥ star v) := by
  rw [partnerMatrixOf, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hU,
    Matrix.one_mul, Θ, star_mulVec', Matrix.mulVec_mulVec]

/-- **The matrix of the singlet is `−½` the quaternionic structure's in every orthonormal basis.** -/
theorem singlet_in_basis (U : Matrix Four Four ℂ) (hU : U * Uᴴ = 1) :
    relOf (U * ((-(1 / 2) : ℂ) • partnerMatrixOf U) * Uᵀ) = Ω := by
  have hU' : U.map star * Uᵀ = 1 := by
    ext i j
    have h1 := congrFun (congrFun hU i) j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at h1
    simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, Matrix.one_apply]
    have h2 := congrArg star h1
    simp only [star_sum, star_mul', star_star] at h2
    rw [h2]
    split_ifs <;> simp
  rw [Ω, MΩ, partnerMatrixOf, Matrix.mul_smul, Matrix.smul_mul]
  congr 2
  simp only [← Matrix.mul_assoc]
  rw [hU, Matrix.one_mul, Matrix.mul_assoc, hU', Matrix.mul_one]

/-! ## Proposition 10: the sixteen two-spinor states as `(γ_S ⊗ 1)Ω` -/

theorem relOpZ_gammaDZ : ∀ k : Fin 16,
    relOpZ k = gammaDZ (disagreeSet k) ∨ relOpZ k = -gammaDZ (disagreeSet k) := by
  decide +kernel

theorem relOpZ_gammaDZ_even : ∀ k : Fin 16, (disagreeSet k).card ≠ 4 →
    relOpZ k = gammaDZ (disagreeSet k) := by
  decide +kernel

/-- **`e_S = (γ_S ⊗ 1)Ω` up to a sign**, with the sign `+` on the singlet and the ten symmetric states. -/
theorem rel_eq_gammaS (k : Fin 16) :
    (rel k = (gammaS (disagreeSet k) ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω ∨
      rel k = -((gammaS (disagreeSet k) ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω)) ∧
    ((disagreeSet k).card ≠ 4 →
      rel k = (gammaS (disagreeSet k) ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω) := by
  have hmap : ∀ M : Matrix Four Four GaussianInt, (-M).map GaussianInt.toComplex =
      -(M.map GaussianInt.toComplex) := fun M => by ext i j; simp
  have hrel : rel k = (relOp k ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω := rfl
  refine ⟨?_, fun h => ?_⟩
  · rcases relOpZ_gammaDZ k with h | h
    · left
      rw [hrel, ← relOpZ_map, h, gammaDZ_map]
    · right
      have hnk : (-gammaS (disagreeSet k)) ⊗ₖ (1 : Matrix Four Four ℂ) =
          -(gammaS (disagreeSet k) ⊗ₖ (1 : Matrix Four Four ℂ)) := by
        ext p q
        simp [Matrix.kronecker_apply]
      rw [hrel, ← relOpZ_map, h, hmap, gammaDZ_map, hnk, Matrix.neg_mulVec]
  · rw [hrel, ← relOpZ_map, relOpZ_gammaDZ_even k h, gammaDZ_map]

/-- **The sixteen two-spinor states are labelled by the sixteen even sets of lines.** -/
theorem disagreeSet_even : (∀ k : Fin 16, Even (disagreeSet k).card) ∧
    Function.Injective disagreeSet ∧
    ∀ S : Finset (Fin 5), Even S.card → ∃ k, disagreeSet k = S := by
  refine ⟨by decide, by decide, by decide⟩

/-! ## Proposition 12: `6 − L = 2N ≥ 0` -/

/-- **`6 − L = 2N`.** -/
theorem disagreement_eq_two_N : disagreement = (2 : ℂ) • Ncount := by
  simp only [disagreement, L, Ncount, count, Finset.smul_sum, smul_smul, one_kronecker_one]
  rw [Fin.sum_univ_five, Fin.sum_univ_five]
  norm_num
  module

theorem diff_hermitian (s : Fin 5) :
    (γ s ⊗ₖ (1 : Matrix Four Four ℂ) - 1 ⊗ₖ γ s)ᴴ = γ s ⊗ₖ (1 : Matrix Four Four ℂ) - 1 ⊗ₖ γ s := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_kronecker,
    γ_conjTranspose, Matrix.conjTranspose_one]

/-- **`6 − L ≥ 0`.** -/
theorem disagreement_posSemidef : disagreement.PosSemidef := by
  rw [disagreement_sum_sq]
  apply Matrix.PosSemidef.smul _ (by rw [Complex.le_def]; norm_num : (0 : ℂ) ≤ 1 / 2)
  apply Matrix.posSemidef_sum
  intro s _
  have h := Matrix.posSemidef_conjTranspose_mul_self (γ s ⊗ₖ (1 : Matrix Four Four ℂ) - 1 ⊗ₖ γ s)
  rwa [diff_hermitian] at h

/-! ## Proposition 13: what the ten rotations and P2 (b) keep -/

theorem partnerTwo_one : partnerTwo (1 : Matrix Two Two ℂ) = 1 := by
  have h := partnerTwo_kron (1 : Matrix Four Four ℂ) 1
  rw [partnerOp_one, Matrix.one_kronecker_one] at h
  exact h

theorem Sp2_comm_Eop (U : Matrix Four Four ℂ) (hU : U * Uᴴ = 1) (hJ : U * J * Uᵀ = J) :
    Eop * (U ⊗ₖ U) = (U ⊗ₖ U) * Eop := by
  have hdet := det_eq_one_of_keeps_J U hJ
  have hL := (keeps_L_iff U hU hdet).mpr (Or.inl hJ)
  rw [L_eq_swap_singlet, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul,
    kron_swap_comm] at hL
  have h2 := smul_right_injective _ (two_ne_zero' ℂ) hL
  exact (add_left_cancel h2).symm

/-- **Kept by every rotation of `Sp(2)` and by P2 (b) exactly when `X = a + b(P + E)`.** -/
theorem kept_both_iff (X : Matrix Two Two ℂ) :
    ((∀ U : Matrix Four Four ℂ, U * Uᴴ = 1 → U * J * Uᵀ = J → X * (U ⊗ₖ U) = (U ⊗ₖ U) * X) ∧
        partnerTwo X = X) ↔
      ∃ a b : ℂ, X = a • (1 : Matrix Two Two ℂ) + b • (swap + Eop) := by
  constructor
  · rintro ⟨hK, hP⟩
    have hX := Comparison.Article.commutant_two X hK
    set x0 := star (rel 0) ⬝ᵥ (X *ᵥ rel 0)
    set xF := star (rel 6) ⬝ᵥ (X *ᵥ rel 6)
    set xL := star (rel 1) ⬝ᵥ (X *ᵥ rel 1)
    have hform : X = ((xF + xL) / 2) • (1 : Matrix Two Two ℂ) + ((xF - xL) / 2) • swap +
        ((x0 - xL) / 4) • Eop := by
      rw [hX]; module
    have hpart : partnerTwo X = ((xF + xL) / 2) • (1 : Matrix Two Two ℂ) + ((xF - xL) / 2) • Eop +
        ((x0 - xL) / 4) • swap := by
      conv_lhs => rw [hform]
      rw [partnerTwo_add, partnerTwo_add, partnerTwo_smul, partnerTwo_smul, partnerTwo_smul,
        partnerTwo_one, partnerTwo_swap, partnerTwo_Eop]
    have hdiff : (0 : ℂ) • (1 : Matrix Two Two ℂ) + ((xF - xL) / 2 - (x0 - xL) / 4) • swap +
        ((x0 - xL) / 4 - (xF - xL) / 2) • Eop = 0 := by
      have e := hP
      rw [hpart] at e
      conv_rhs at e => rw [hform]
      have : ((xF + xL) / 2) • (1 : Matrix Two Two ℂ) + ((xF - xL) / 2) • swap +
          ((x0 - xL) / 4) • Eop - (((xF + xL) / 2) • (1 : Matrix Two Two ℂ) +
          ((xF - xL) / 2) • Eop + ((x0 - xL) / 4) • swap) = 0 := by rw [e]; abel
      rw [← this]; module
    obtain ⟨-, hb, -⟩ := Comparison.Article.one_swap_E_independent _ _ _ hdiff
    refine ⟨(xF + xL) / 2, (xF - xL) / 2, ?_⟩
    rw [hform]
    have hb' : (x0 - xL) / 4 = (xF - xL) / 2 := by linear_combination -hb
    rw [hb']
    module
  · rintro ⟨a, b, rfl⟩
    refine ⟨fun U hU hJ => ?_, ?_⟩
    · have hE := Sp2_comm_Eop U hU hJ
      have hS := kron_swap_comm U
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one, hE, hS]
    · rw [partnerTwo_add, partnerTwo_smul, partnerTwo_smul, partnerTwo_one, partnerTwo_add,
        partnerTwo_swap, partnerTwo_Eop, add_comm Eop swap]

/-- `N e_S = |S| e_S`: the count of disagreeing lines on the sixteen two-spinor states. -/
theorem Ncount_rel (k : Fin 16) : Ncount *ᵥ rel k = ((disagreeSet k).card : ℂ) • rel k := by
  rw [Ncount, Matrix.sum_mulVec]
  simp only [count_rel, ← Finset.sum_smul]
  congr 1
  rw [Finset.sum_boole]
  simp

/-- `(6 − L)e_S = 2|S|e_S`: the disagreement is `0, 4, 8` on the singlet, the symmetric states and the vector
states. -/
theorem disagreement_rel (k : Fin 16) :
    disagreement *ᵥ rel k = ((2 * (disagreeSet k).card : ℕ) : ℂ) • rel k := by
  rw [disagreement_eq_two_N, Matrix.smul_mulVec, Ncount_rel, smul_smul]
  congr 1
  push_cast
  ring

/-- `a + bP + cE` commutes with every `U ⊗ U`, `U ∈ Sp(2)`. -/
theorem kept_span_commutes (a b c : ℂ) (U : Matrix Four Four ℂ) (hU : U * Uᴴ = 1)
    (hJ : U * J * Uᵀ = J) :
    (a • (1 : Matrix Two Two ℂ) + b • swap + c • Eop) * (U ⊗ₖ U) =
      (U ⊗ₖ U) * (a • (1 : Matrix Two Two ℂ) + b • swap + c • Eop) := by
  have h1 := kron_swap_comm U
  have h2 := Sp2_comm_Eop U hU hJ
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, h1, h2]

/-- **P2 fixes the comparison.** An operator on two systems is kept by every `U ⊗ U`, `U ∈ Sp(2)`, and
by the exchange (P2 (a)), and by the quaternionic structure taken on one system (P2 (b)), exactly when it is `a + bL`
(the proof of `P2_iff`). -/
theorem P2_fixes_comparison (X : Matrix Two Two ℂ) :
    P2a X ∧ P2b X ↔ ∃ a b : ℂ, X = a • (1 : Matrix Two Two ℂ) + b • L := by
  constructor
  · rintro ⟨⟨hU, -⟩, hP⟩
    have hK : ∀ U : Matrix Four Four ℂ, U * Uᴴ = 1 → U * J * Uᵀ = J →
        X * (U ⊗ₖ U) = (U ⊗ₖ U) * X := by
      intro U hu hJ
      have hmem : U ∈ Matrix.unitaryGroup Four ℂ :=
        Matrix.mem_unitaryGroup_iff.mpr (by rwa [Matrix.star_eq_conjTranspose])
      exact (hU ⟨U, hmem⟩ hJ).symm
    obtain ⟨a, b, hX⟩ := (kept_both_iff X).mp ⟨hK, hP⟩
    refine ⟨a, b / 2, ?_⟩
    rw [hX, L_eq_two_swap_Eop, smul_smul, div_mul_cancel₀ b two_ne_zero]
  · rintro ⟨a, b, rfl⟩
    obtain ⟨⟨hL, hS⟩, hP⟩ := comparison_P2
    refine ⟨⟨fun U hU => ?_, ?_⟩, ?_⟩
    · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one, hL U hU]
    · simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
        Matrix.mul_one, hS]
    · change partnerTwo (a • (1 : Matrix Two Two ℂ) + b • L) = a • (1 : Matrix Two Two ℂ) + b • L
      rw [partnerTwo_add, partnerTwo_smul, partnerTwo_smul, partnerTwo_one, partnerTwo_L]

/-- The transitions of a plane `{a, b}`: along `a` to `ℓ_b`, along `b` to `ℓ_a`, along an outside line `u`
to the plane of the two other outside lines. -/
theorem plane_transitions : ∀ a b u : Fin 5, a ≠ b →
    symmDiff ({a, b} : Finset (Fin 5)) (Finset.univ.erase u) =
      if u = a then Finset.univ.erase b else if u = b then Finset.univ.erase a
      else Finset.univ \ {a, b, u} := by
  decide

end Geometry

open Comparison.System.Geometry

/-- **Proposition 9 (the singlet).** The singlet `Ω = ½Σ_j u_j ⊗ Θu_j` is the same in every orthonormal
basis, its matrix in every orthonormal basis is `−½` the matrix of the quaternionic structure there (in the standard
basis `M_Ω = −½J`), `‖Ω‖ = 1`, `PΩ = −Ω`; `(1 ⊗ X)Ω = (X♯ ⊗ 1)Ω` for every operator `X`, so
`(a ⊗ 1)Ω = (1 ⊗ a)Ω` for every `a ∈ ℝ1 ⊕ Q`; the two-spinor states kept by every rotation of `Sp(2)` are exactly
`ℂΩ`; and `Tr₂|Ω⟩⟨Ω| = ¼·1`. Recognition: none. -/
theorem prop_9 :
    (∀ U : Matrix Four Four ℂ, U * Uᴴ = 1 →
      (1 / 2 : ℂ) • ∑ j : Four, (fun p : Two => U p.1 j * Θ (fun i => U i j) p.2) = Ω) ∧
    (∀ U : Matrix Four Four ℂ, U * Uᴴ = 1 →
      (∀ v, Θ (U *ᵥ v) = U *ᵥ (partnerMatrixOf U *ᵥ star v)) ∧
      relOf (U * ((-(1 / 2) : ℂ) • partnerMatrixOf U) * Uᵀ) = Ω) ∧
    MΩ = (-(1 / 2) : ℂ) • J ∧
    star Ω ⬝ᵥ Ω = 1 ∧ swap *ᵥ Ω = -Ω ∧
    (∀ X : Matrix Four Four ℂ, ((1 : Matrix Four Four ℂ) ⊗ₖ X) *ᵥ Ω =
      (partnerOp X ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω) ∧
    (∀ a, InR1Q a → (a ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω = ((1 : Matrix Four Four ℂ) ⊗ₖ a) *ᵥ Ω) ∧
    (∀ v : Two → ℂ, (∀ U : Matrix Four Four ℂ, U * Uᴴ = 1 → U * J * Uᵀ = J → (U ⊗ₖ U) *ᵥ v = v) ↔
      ∃ c : ℂ, v = c • Ω) ∧
    (∀ i j : Four, ∑ k : Four, Ω (i, k) * star (Ω (j, k)) = (1 / 4 : ℂ) * (if i = j then 1 else 0)) :=
  ⟨Ω_basis_free, fun U hU => ⟨partner_in_basis U hU, singlet_in_basis U hU⟩, rfl, Ω_norm,
    ArticleStatements.swap_singlet, kron_one_partner, same_side_of_R1Q, Article.kept_by_turns_iff,
    Article.partial_trace_singlet⟩

/-- **Proposition 10 (the sixteen two-spinor states and the comparison).** The sixteen two-spinor states
`e_S = (γ_S ⊗ 1)Ω`, labelled by the sixteen even sets `S` of lines (up to the sign on the five vector
states `ℓ_t = (γ_t ⊗ 1)Ω = ±e_{T_t}`), are orthonormal; `n_t e_S = [t ∈ S]e_S`; `L e_S =
(6 − 2|S|)e_S`; so `L` has the values `6, 2, −2` with multiplicities `1, 10, 5` and no other.
Recognition: the sixteen states of one generation of matter; the grade `N = |S|`. -/
theorem prop_10 :
    ((∀ k : Fin 16, Even (disagreeSet k).card) ∧ Function.Injective disagreeSet ∧
      ∀ S : Finset (Fin 5), Even S.card → ∃ k, disagreeSet k = S) ∧
    (∀ k : Fin 16, (rel k = (gammaS (disagreeSet k) ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω ∨
        rel k = -((gammaS (disagreeSet k) ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω)) ∧
      ((disagreeSet k).card ≠ 4 →
        rel k = (gammaS (disagreeSet k) ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω)) ∧
    (∀ k l : Fin 16, star (rel k) ⬝ᵥ rel l = if k = l then 1 else 0) ∧
    (∀ (u : Fin 5) (k : Fin 16), count u *ᵥ rel k = (if u ∈ disagreeSet k then 1 else 0 : ℂ) • rel k) ∧
    (∀ k : Fin 16, L *ᵥ rel k = ((6 : ℂ) - 2 * (disagreeSet k).card) • rel k) ∧
    finrank ℂ (Module.End.eigenspace (Matrix.toLin' L) 6) = 1 ∧
    finrank ℂ (Module.End.eigenspace (Matrix.toLin' L) 2) = 10 ∧
    finrank ℂ (Module.End.eigenspace (Matrix.toLin' L) (-2)) = 5 ∧
    (∀ μ : ℂ, μ ≠ 6 → μ ≠ 2 → μ ≠ -2 → Module.End.eigenspace (Matrix.toLin' L) μ = ⊥) :=
  ⟨disagreeSet_even, rel_eq_gammaS, rel_inner, count_rel, L_rel, finrank_eigenspace_L_six,
    finrank_eigenspace_L_two, finrank_eigenspace_L_neg_two, eigenspace_L_other⟩

/-- **Proposition 11 (the comparison is the swap and the singlet).** `L = 1 ⊗ 1 + Σ_s γ_s ⊗ γ_s =
2(P + E)`; `P` is `+1` on the ten symmetric states and `−1` on the singlet and the five directions; `L = Σ_α X_α ⊗ X_α`
for every orthonormal basis `X_α = Σ_β O_{αβ}Y_β` of `ℝ1 ⊕ Q`; `E = |J⟩⟨J|`, `E² = 4E`,
`PE = EP = −E`, `P² = 1`; on one system's operators the comparison has the eigenvectors `1` (value 6),
`γ_aγ_b` (2) and `γ_a` (−2). Recognition: one comparison tells one of three facts. -/
theorem prop_11 :
    L = (1 : Matrix Four Four ℂ) ⊗ₖ 1 + ∑ s, γ s ⊗ₖ γ s ∧ L = (2 : ℂ) • (swap + Eop) ∧
    (∀ k : Fin 16, swap *ᵥ rel k = (if (disagreeSet k).card = 2 then 1 else -1 : ℂ) • rel k) ∧
    (∀ O : Matrix (Fin 6) (Fin 6) ℝ, (∀ a c : Fin 6, (1 / 4 : ℂ) *
        ((∑ b, (O a b : ℂ) • Article.Ybasis b) * (∑ d, (O c d : ℂ) • Article.Ybasis d)).trace =
          if a = c then 1 else 0) →
      L = ∑ a, (∑ b, (O a b : ℂ) • Article.Ybasis b) ⊗ₖ (∑ d, (O a d : ℂ) • Article.Ybasis d)) ∧
    Eop = vecMulVec (relOf J) (star (relOf J)) ∧ Eop * Eop = (4 : ℂ) • Eop ∧
    swap * Eop = -Eop ∧ Eop * swap = -Eop ∧ swap * swap = 1 ∧
    WholePicture.compOp 1 = (6 : ℂ) • (1 : Matrix Four Four ℂ) ∧
    (∀ a, WholePicture.compOp (γ a) = (-2 : ℂ) • γ a) ∧
    (∀ a b : Fin 5, a ≠ b → WholePicture.compOp (γ a * γ b) = (2 : ℂ) • (γ a * γ b)) := by
  refine ⟨rfl, L_eq_swap_singlet, fun k => ?_, Article.comparison_every_basis, Eop_eq_pairing',
    ArticleStatements.Eop_mul_Eop, ArticleStatements.swap_mul_Eop, ArticleStatements.Eop_mul_swap,
    ArticleStatements.swap_mul_swap, WholePicture.compOp_one, WholePicture.compOp_line,
    fun a b h => WholePicture.compOp_plane h⟩
  rw [swap_rel, swapSign]
  split_ifs <;> simp

/-- **Proposition 12 (disagreement).** `6 − L = ½Σ_s(γ_s ⊗ 1 − 1 ⊗ γ_s)² = 2N ≥ 0`, which is `0, 4, 8`
on the singlet, the symmetric states and the vector states (`(6 − L)e_S = 2|S|e_S`); it is zero exactly
on `ℂΩ`; two unit states taken apart, and two mixed states taken separately or any mixture of such
pairs, disagree by at least four, with `Tr[(ρ ⊗ σ)(6 − L)] = 5 − m_ρ·m_σ` and `|m_ρ| ≤ 1`.
Recognition: the singlet cannot be made from two systems apart; it is entangled. -/
theorem prop_12 :
    disagreement = (1 / 2 : ℂ) • ∑ s, (γ s ⊗ₖ 1 - 1 ⊗ₖ γ s) * (γ s ⊗ₖ 1 - 1 ⊗ₖ γ s) ∧
    disagreement = (2 : ℂ) • Ncount ∧
    (∀ k : Fin 16, disagreement *ᵥ rel k = ((2 * (disagreeSet k).card : ℕ) : ℂ) • rel k) ∧
    disagreement.PosSemidef ∧
    (∀ v : Two → ℂ, disagreement *ᵥ v = 0 ↔ ∃ c : ℂ, v = c • Ω) ∧
    (∀ a b : Four → ℂ, normSq a = 1 → normSq b = 1 →
      4 ≤ (star (prodRel a b) ⬝ᵥ (disagreement *ᵥ prodRel a b)).re) ∧
    (∀ ρ : Matrix Four Four ℂ, ρ.PosSemidef → ρ.trace = 1 → ∑ s, mixedLine ρ s ^ 2 ≤ 1) ∧
    (∀ ρ σ : Matrix Four Four ℂ, ρᴴ = ρ → σᴴ = σ → ρ.trace = 1 → σ.trace = 1 →
      ((ρ ⊗ₖ σ) * disagreement).trace = ((5 - ∑ s, mixedLine ρ s * mixedLine σ s : ℝ) : ℂ)) ∧
    (∀ ρ σ : Matrix Four Four ℂ, ρ.PosSemidef → σ.PosSemidef → ρ.trace = 1 → σ.trace = 1 →
      4 ≤ ((ρ ⊗ₖ σ) * disagreement).trace.re) ∧
    (∀ {ι : Type} [Fintype ι] (p : ι → ℝ), (∀ i, 0 ≤ p i) → ∑ i, p i = 1 →
      ∀ ρ σ : ι → Matrix Four Four ℂ, (∀ i, (ρ i).PosSemidef) → (∀ i, (σ i).PosSemidef) →
      (∀ i, (ρ i).trace = 1) → (∀ i, (σ i).trace = 1) →
      4 ≤ ((∑ i, (p i : ℂ) • (ρ i ⊗ₖ σ i)) * disagreement).trace.re) :=
  ⟨disagreement_sum_sq, disagreement_eq_two_N, disagreement_rel, disagreement_posSemidef,
    disagreement_eq_zero_iff,
    disagreement_prodRel_ge, sum_mixedLine_sq_le, trace_prod_disagreement, disagreement_mixed_ge,
    fun p hp hp1 ρ σ hρ hσ hρ1 hσ1 => disagreement_mixture_ge p hp hp1 ρ σ hρ hσ hρ1 hσ1⟩

/-- **Proposition 13 (one's own past and a neighbour).** `X = X† = X♯ ⟺ X ∈ ℝ1 ⊕ Q`; the operators on
two systems kept by every `U ⊗ U`, `U ∈ Sp(2)`, are exactly the `a + bP + cE`, with `1, P, E` independent; the
quaternionic structure on one system, `X ⊗ Y ↦ X ⊗ Y♯`, takes `1 ↦ 1`, `P ↦ E`, `E ↦ P`, `L ↦ L`; the operators kept
by both are `a + b(P + E)`, and those that satisfy P2 (kept by every `U ⊗ U` and the exchange, and by the
quaternionic structure on one system) are exactly `a + bL`. Recognition: meeting a neighbour is a crossing and meeting one's own past
a join; inertia is gravity. -/
theorem prop_13 :
    (∀ X : Matrix Four Four ℂ, (Xᴴ = X ∧ partnerOp X = X) ↔ InR1Q X) ∧
    (∀ X : Matrix Two Two ℂ,
      (∀ U : Matrix Four Four ℂ, U * Uᴴ = 1 → U * J * Uᵀ = J → X * (U ⊗ₖ U) = (U ⊗ₖ U) * X) ↔
      ∃ a b c : ℂ, X = a • (1 : Matrix Two Two ℂ) + b • swap + c • Eop) ∧
    (∀ a b c : ℂ, a • (1 : Matrix Two Two ℂ) + b • swap + c • Eop = 0 → a = 0 ∧ b = 0 ∧ c = 0) ∧
    (∀ X Y : Matrix Four Four ℂ, partnerTwo (X ⊗ₖ Y) = X ⊗ₖ partnerOp Y) ∧
    partnerTwo 1 = 1 ∧ partnerTwo swap = Eop ∧ partnerTwo Eop = swap ∧ partnerTwo L = L ∧
    (∀ X : Matrix Two Two ℂ,
      ((∀ U : Matrix Four Four ℂ, U * Uᴴ = 1 → U * J * Uᵀ = J → X * (U ⊗ₖ U) = (U ⊗ₖ U) * X) ∧
        partnerTwo X = X) ↔ ∃ a b : ℂ, X = a • (1 : Matrix Two Two ℂ) + b • (swap + Eop)) ∧
    (∀ X : Matrix Two Two ℂ, P2a X ∧ P2b X ↔ ∃ a b : ℂ, X = a • (1 : Matrix Two Two ℂ) + b • L) := by
  refine ⟨mem_R1Q_iff, fun X => ⟨fun hX => ?_, ?_⟩, Article.one_swap_E_independent, partnerTwo_kron,
    partnerTwo_one, partnerTwo_swap, partnerTwo_Eop, partnerTwo_L, kept_both_iff, P2_fixes_comparison⟩
  · have h := Article.commutant_two X hX
    set x0 := star (rel 0) ⬝ᵥ (X *ᵥ rel 0)
    set xF := star (rel 6) ⬝ᵥ (X *ᵥ rel 6)
    set xL := star (rel 1) ⬝ᵥ (X *ᵥ rel 1)
    refine ⟨(xF + xL) / 2, (xF - xL) / 2, (x0 - xL) / 4, ?_⟩
    rw [h]
    module
  · rintro ⟨a, b, c, rfl⟩ U hU hJ
    exact kept_span_commutes a b c U hU hJ

/-- **Proposition 14 (one line on one system).** Applying the line `t` to one system moves each two-spinor state
to a two-spinor state, `(γ_t ⊗ 1)e_S = ±e_{S △ T_t}`; each transition is an involution without fixed two-spinor state; from
every two-spinor state the five directions lead to five different two-spinor states; the singlet goes to the five vector
states, a vector state `ℓ_t` to the singlet and the four symmetric states through `t`, a plane `{a, b}` to `ℓ_a`,
`ℓ_b` and the three symmetric states of the lines outside it; the sixteen two-spinor states with these transitions are the
strongly regular graph (16, 5, 0, 2): five
neighbours, none in common for neighbours, two in common otherwise, forty pairs. Recognition: the
Clebsch graph, what a world line steps through. -/
theorem prop_14 :
    (∀ (t : Fin 5) (k : Fin 16), disagreeSet (transition t k) = symmDiff (disagreeSet k) (Finset.univ.erase t)) ∧
    (∀ (t : Fin 5) (k : Fin 16),
      (γ t ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ rel k = (transitionSign t k : ℂ) • rel (transition t k)) ∧
    (∀ t k, transition t (transition t k) = k) ∧ (∀ t k, transition t k ≠ k) ∧
    (∀ t t' k, transition t k = transition t' k ↔ t = t') ∧
    (∀ t : Fin 5, disagreeSet (transition t 0) = Finset.univ.erase t) ∧
    (∀ t s : Fin 5, disagreeSet (transition s (transition t 0)) = if s = t then ∅ else {s, t}) ∧
    (∀ (k : Fin 16) (a b : Fin 5), a ≠ b → disagreeSet k = {a, b} → ∀ u : Fin 5,
      disagreeSet (transition u k) = if u = a then Finset.univ.erase b else if u = b then Finset.univ.erase a
        else Finset.univ \ {a, b, u}) ∧
    (∀ k : Fin 16, (Finset.univ.filter (Adjacent k)).card = 5) ∧
    (∀ k l : Fin 16, k ≠ l → (Finset.univ.filter fun m => Adjacent k m ∧ Adjacent l m).card =
      if Adjacent k l then 0 else 2) ∧
    (Finset.univ.filter fun p : Fin 16 × Fin 16 => p.1 < p.2 ∧ Adjacent p.1 p.2).card = 40 :=
  ⟨disagreeSet_transition, line_moves_rel, transition_transition, transition_ne, transition_eq_transition_iff, by decide, by decide,
    fun k a b hab hk u => by rw [disagreeSet_transition, hk]; exact plane_transitions a b u hab,
    card_neighbours, common_neighbours, card_edges⟩

end Comparison.System
