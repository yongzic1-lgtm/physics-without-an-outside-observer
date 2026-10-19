import Comparison.Elements.TwoThings

/-!
# Four amplitudes and one side of a plane
# (statements 2 and 4)

**Statement 2.** Two compared distinctions have four ends joined by the identity `I`, the exchange `P`
(`swap`) or the alternating join `E` (`Eop = 4|Ω⟩⟨Ω|`); a closed join has value `δ`. On the sixteen
two-spinor states of the unique model (Proposition 23, `δ = 4`):

* `swap_mul_swap`, `Eop_mul_Eop`, `swap_mul_Eop`, `Eop_mul_swap`: **`P² = I`, `E² = δE`, `PE = EP = −E`**,
  with `swap_singlet`: `PΩ = −Ω`.
* `trace_one_two`, `trace_swap`, `trace_Eop`: `Tr I = 16 = δ²`, `Tr P = 4 = δ`, `Tr E = 4 = δ`.
* `projSinglet`, `projSymmetric`, `projVector`: `Π₀ = E/δ`, `Π_F = (I + P)/2`, `Π_L = (I − P)/2 − E/δ`;
  `proj_idem`, `proj_orth`, `proj_sum`: three orthogonal projectors adding to `I`;
  `L_proj`: **`L = 2(P + E) = 6Π₀ + 2Π_F − 2Π_L`**; `trace_proj`: their traces `1, 10, 5`, so `d = 5`.
* `equal_counts`: **`d = (δ − 2)(δ + 1)/2` and `δ = d − 1` force `δ = 4` and `d = 5`**: joining closes a loop
  with count `δ`, continuing leaves `d − 1` choices, and equal right equates the two counts.

**Statement 4.** `det_planeMat`: **`det(tI + x·σ) = t² − |x|²`** for the Pauli matrices of Book I;
`planeMat_hermitian`: for real `t, x` the matrix is Hermitian.
-/

open Matrix hiding J
open Complex Kronecker

namespace Comparison.ArticleStatements

/-! ## Statement 2: the identity, the exchange and the join -/

theorem swap_symm (p q : Two) : swap p q = swap q p := by
  simp only [swap, Matrix.of_apply]
  by_cases h : p.1 = q.2 ∧ p.2 = q.1
  · rw [ite_eq_left h, ite_eq_left ⟨h.2.symm, h.1.symm⟩]
  · rw [ite_eq_right h, ite_eq_right fun h' => h ⟨h'.2.symm, h'.1.symm⟩]

theorem swap_real (p q : Two) : star (swap p q) = swap p q := by
  simp only [swap, Matrix.of_apply]
  split_ifs <;> simp

/-- **`P² = I`.** -/
theorem swap_mul_swap : swap * swap = 1 := by
  ext p q
  rw [Matrix.mul_apply, Finset.sum_eq_single (p.2, p.1)]
  · simp only [swap, Matrix.of_apply, Matrix.one_apply]
    by_cases h : p = q
    · subst h
      simp
    · have h' : ¬(p.2 = q.2 ∧ p.1 = q.1) := fun h2 => h (Prod.ext h2.2 h2.1)
      simp [h, h']
  · intro r _ hr
    simp only [swap, Matrix.of_apply]
    have h2 : ¬(p.1 = r.2 ∧ p.2 = r.1) := fun h3 => hr (Prod.ext h3.2.symm h3.1.symm)
    simp [h2]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **The exchange reverses the singlet:** `PΩ = −Ω`. -/
theorem swap_singlet : swap *ᵥ Ω = -Ω := by
  have hM : MΩᵀ = -MΩ := by rw [MΩ, Matrix.transpose_smul, J_transpose, smul_neg]
  rw [Ω, swap_relOf, hM]
  ext p
  simp [relOf]

theorem sum_star_singlet : ∑ r, star (Ω r) * Ω r = 1 := by
  simpa [dotProduct] using Ω_norm

/-- **`E² = δE`** with `δ = 4`. -/
theorem Eop_mul_Eop : Eop * Eop = (4 : ℂ) • Eop := by
  ext p q
  rw [Matrix.mul_apply, Matrix.smul_apply]
  simp only [Eop, Matrix.of_apply, smul_eq_mul]
  calc ∑ r, 4 * Ω p * star (Ω r) * (4 * Ω r * star (Ω q)) =
        16 * Ω p * star (Ω q) * ∑ r, star (Ω r) * Ω r := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        ring
    _ = 4 * (4 * Ω p * star (Ω q)) := by
        rw [sum_star_singlet]
        ring

/-- **`PE = −E`.** -/
theorem swap_mul_Eop : swap * Eop = -Eop := by
  ext p q
  have h := congrFun swap_singlet p
  simp only [Matrix.mulVec, dotProduct, Pi.neg_apply] at h
  rw [Matrix.mul_apply, Matrix.neg_apply]
  simp only [Eop, Matrix.of_apply]
  calc ∑ r, swap p r * (4 * Ω r * star (Ω q)) = 4 * (∑ r, swap p r * Ω r) * star (Ω q) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun r _ => ?_
        ring
    _ = -(4 * Ω p * star (Ω q)) := by
        rw [h]
        ring

/-- **`EP = −E`.** -/
theorem Eop_mul_swap : Eop * swap = -Eop := by
  ext p q
  have h := congrFun swap_singlet q
  simp only [Matrix.mulVec, dotProduct, Pi.neg_apply] at h
  have h' : ∑ r, star (Ω r) * swap r q = -star (Ω q) := by
    have h2 := congrArg star h
    rw [star_sum, star_neg] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [star_mul', swap_real, swap_symm q r, mul_comm]
  rw [Matrix.mul_apply, Matrix.neg_apply]
  simp only [Eop, Matrix.of_apply]
  calc ∑ r, 4 * Ω p * star (Ω r) * swap r q = 4 * Ω p * ∑ r, star (Ω r) * swap r q := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        ring
    _ = -(4 * Ω p * star (Ω q)) := by
        rw [h']
        ring

theorem trace_one_two : (1 : Matrix Two Two ℂ).trace = 16 := by
  rw [Matrix.trace_one]
  simp [Fintype.card_prod]

theorem trace_swap : swap.trace = 4 := by
  have hc : (Finset.univ.filter fun x : Two => x.1 = x.2 ∧ x.2 = x.1).card = 4 := by decide
  simp only [Matrix.trace, Matrix.diag, swap, Matrix.of_apply]
  rw [Finset.sum_boole, hc]
  norm_num

theorem trace_Eop : Eop.trace = 4 := by
  simp only [Matrix.trace, Matrix.diag, Eop, Matrix.of_apply]
  calc ∑ p, 4 * Ω p * star (Ω p) = 4 * ∑ p, star (Ω p) * Ω p := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun p _ => ?_
        ring
    _ = 4 := by rw [sum_star_singlet, mul_one]

/-- `Π₀ = E/δ`, the singlet. -/
noncomputable def projSinglet : Matrix Two Two ℂ := (1 / 4 : ℂ) • Eop
/-- `Π_F = (I + P)/2`, the ten symmetric states. -/
noncomputable def projSymmetric : Matrix Two Two ℂ := (1 / 2 : ℂ) • (1 + swap)
/-- `Π_L = (I − P)/2 − E/δ`, the five directions. -/
noncomputable def projVector : Matrix Two Two ℂ := (1 / 2 : ℂ) • (1 - swap) - (1 / 4 : ℂ) • Eop

/-- The three are projectors. -/
theorem proj_idem : projSinglet * projSinglet = projSinglet ∧ projSymmetric * projSymmetric = projSymmetric ∧
    projVector * projVector = projVector := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [projSinglet, Matrix.smul_mul, Matrix.mul_smul, Eop_mul_Eop]
    module
  · simp only [projSymmetric, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one, swap_mul_swap]
    module
  · simp only [projVector, Matrix.smul_mul, Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, swap_mul_swap, swap_mul_Eop, Eop_mul_swap, Eop_mul_Eop]
    module

/-- The three are mutually orthogonal. -/
theorem proj_orth : projSinglet * projSymmetric = 0 ∧ projSinglet * projVector = 0 ∧ projSymmetric * projVector = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [projSinglet, projSymmetric, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_one,
      Eop_mul_swap]
    module
  · simp only [projSinglet, projVector, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_sub, Matrix.mul_one,
      Eop_mul_swap, Eop_mul_Eop]
    module
  · simp only [projSymmetric, projVector, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, swap_mul_swap, swap_mul_Eop]
    module

/-- They add to the identity. -/
theorem proj_sum : projSinglet + projSymmetric + projVector = 1 := by
  simp only [projSinglet, projSymmetric, projVector]
  module

/-- **`L = 2(P + E) = 6Π₀ + 2Π_F − 2Π_L`.** -/
theorem L_proj : L = (6 : ℂ) • projSinglet + (2 : ℂ) • projSymmetric - (2 : ℂ) • projVector := by
  rw [L_eq_swap_singlet]
  simp only [projSinglet, projSymmetric, projVector]
  module

/-- **The traces `1, 10, 5`:** the singlet, the ten symmetric states and the five directions. -/
theorem trace_proj : projSinglet.trace = 1 ∧ projSymmetric.trace = 10 ∧ projVector.trace = 5 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [projSinglet, Matrix.trace_smul, trace_Eop, smul_eq_mul]
    norm_num
  · rw [projSymmetric, Matrix.trace_smul, Matrix.trace_add, trace_one_two, trace_swap, smul_eq_mul]
    norm_num
  · rw [projVector, Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_sub,
      trace_one_two, trace_swap, trace_Eop, smul_eq_mul, smul_eq_mul]
    norm_num

/-- **Equal counts force four amplitudes:** `2d = (δ − 2)(δ + 1)` (the five directions, `Tr Π_L`) and
`δ = d − 1` (a loop's count equals the choices left to a continued walk) give `δ = 4`, `d = 5`. -/
theorem equal_counts (δ d : ℤ) (h1 : 2 * d = (δ - 2) * (δ + 1)) (h2 : δ = d - 1) (hδ : 0 < δ) :
    δ = 4 ∧ d = 5 := by
  have h : (δ - 4) * (δ + 1) = 0 := by linear_combination -h1 - 2 * h2
  rcases mul_eq_zero.mp h with h3 | h3
  · constructor <;> omega
  · omega

/-- In the model `δ = 4`: `Tr Π_L = (Tr I − Tr P)/2 − Tr E/δ = (δ − 2)(δ + 1)/2 = 5 = δ + 1`. -/
theorem counts_in_model : ((16 : ℂ) - 4) / 2 - 4 / 4 = ((4 : ℂ) - 2) * (4 + 1) / 2 ∧
    ((4 : ℂ) - 2) * (4 + 1) / 2 = 4 + 1 := by
  norm_num

/-! ## Statement 4: one side of a plane as a Hermitian two-by-two matrix -/

/-- `tI + x₁σ₁ + x₂σ₂ + x₃σ₃`. -/
noncomputable def planeMat (t x₁ x₂ x₃ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  t • (1 : Matrix (Fin 2) (Fin 2) ℂ) + x₁ • σ₁ + x₂ • σ₂ + x₃ • σ₃

/-- **`det(tI + x·σ) = t² − |x|²`.** -/
theorem det_planeMat (t x₁ x₂ x₃ : ℂ) :
    (planeMat t x₁ x₂ x₃).det = t ^ 2 - x₁ ^ 2 - x₂ ^ 2 - x₃ ^ 2 := by
  rw [Matrix.det_fin_two]
  simp [planeMat, σ₁, σ₂, σ₃]
  linear_combination x₂ ^ 2 * Complex.I_sq

/-- For real `t, x` the plane matrix is Hermitian. -/
theorem planeMat_hermitian (t x₁ x₂ x₃ : ℝ) :
    (planeMat t x₁ x₂ x₃)ᴴ = planeMat t x₁ x₂ x₃ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [planeMat, σ₁, σ₂, σ₃, Matrix.conjTranspose_apply]

end Comparison.ArticleStatements

#print axioms Comparison.ArticleStatements.swap_symm
#print axioms Comparison.ArticleStatements.swap_real
#print axioms Comparison.ArticleStatements.swap_mul_swap
#print axioms Comparison.ArticleStatements.swap_singlet
#print axioms Comparison.ArticleStatements.sum_star_singlet
#print axioms Comparison.ArticleStatements.Eop_mul_Eop
#print axioms Comparison.ArticleStatements.swap_mul_Eop
#print axioms Comparison.ArticleStatements.Eop_mul_swap
#print axioms Comparison.ArticleStatements.trace_one_two
#print axioms Comparison.ArticleStatements.trace_swap
#print axioms Comparison.ArticleStatements.trace_Eop
#print axioms Comparison.ArticleStatements.proj_idem
#print axioms Comparison.ArticleStatements.proj_orth
#print axioms Comparison.ArticleStatements.proj_sum
#print axioms Comparison.ArticleStatements.L_proj
#print axioms Comparison.ArticleStatements.trace_proj
#print axioms Comparison.ArticleStatements.equal_counts
#print axioms Comparison.ArticleStatements.counts_in_model
#print axioms Comparison.ArticleStatements.det_planeMat
#print axioms Comparison.ArticleStatements.planeMat_hermitian
