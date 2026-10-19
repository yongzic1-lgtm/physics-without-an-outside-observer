module

public import Comparison.Existence.Table
public import Comparison.Elements.KeepL

/-!
# Book IX. The rotations of a pair, the last-step direction, singlet, symmetric and vector states (Propositions 46, 47, 48)

**Prop. 46.** The ten lines of a pair on `H ⊗ H ⊗ ℂ²`: `Γ_a = γ_a ⊗ 1 ⊗ σ_x` and
`Γ_{5+a} = 1 ⊗ γ_a ⊗ σ_y` (`tenLine (inl a)`, `tenLine (inr a)`).
* `tenLine_clifford`: `Γ_xΓ_y + Γ_yΓ_x = 2δ_xy`: ten anticommuting lines.
* `comparison_as_turn`: `−i Σ_t Γ_tΓ_{5+t} = (L − 1) ⊗ σ_z`: on the two-spinor states (`σ_z = +1`) the
  comparison less one is the rotation of each line of one system toward the same line of the other.
* `swap_rel`: the swap `P` is `−1` on the singlet and the five vector states and `+1` on the ten symmetric states;
  `quarter_comparison`: `e^{−iπL/4} = −iP` on each of the sixteen two-spinor states.

**Prop. 47, the last-step direction** (`h, k` the plane's lines, three lines outside, on `ℂ⁵ = C ⊕ F`):
* `lastDirection_weights`: the four rotations of the plane send the last-step direction to vectors of squared length `1, 0, ½, ½`
  and the nine of `u(3)` fix it: three of the thirteen move the last-step direction, `w_h = 3/13`,
  `χ_h = w_h(1 − w_h) = 30/169`.
* `traceless_gram`: without the common phase the two diagonal rotations have the Gram form
  `[[½, ½(3/5)^{1/2}], [½(3/5)^{1/2}, 3/10]]`: determinant `0`, trace `4/5`, and its third part
  `1 − (½)/(4/5) = 3/8`; `hypercharge_turn`: the entries of that form from `Y`.

**Prop. 48, singlet, symmetric and vector states.** `irreps`: the sixteen two-spinor states disagree on `0, 2` or `4` lines,
`1 + 10 + 5`, none on more; `irrep_projectors`: `Π₀ = E/4`, `Π_F = (1 + P)/2`, `Π_L = (1 − P)/2 − E/4`
are `1` on the singlet, the symmetric states, the vector states respectively and `0` on the others.
-/

@[expose] public section

namespace Comparison

open Matrix hiding J
open Complex Kronecker

/-! ## The ten lines of a pair -/

/-- The ten lines of a pair: `Γ_a = γ_a ⊗ 1 ⊗ σ_x`, `Γ_{5+a} = 1 ⊗ γ_a ⊗ σ_y`. -/
noncomputable def tenLine : Fin 5 ⊕ Fin 5 → Matrix (Two × Fin 2) (Two × Fin 2) ℂ
  | Sum.inl a => (γ a ⊗ₖ (1 : Matrix Four Four ℂ)) ⊗ₖ σ₁
  | Sum.inr a => ((1 : Matrix Four Four ℂ) ⊗ₖ γ a) ⊗ₖ σ₂

theorem σ₁_sq : σ₁ * σ₁ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σ₁, Matrix.mul_apply, Fin.sum_univ_two]

theorem σ₂_sq : σ₂ * σ₂ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σ₂, Matrix.mul_apply, Fin.sum_univ_two]

theorem σ₁σ₂_anti : σ₁ * σ₂ + σ₂ * σ₁ = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σ₁, σ₂, Matrix.mul_apply, Fin.sum_univ_two]

theorem σ₁σ₂_eq : σ₁ * σ₂ = I • σ₃ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [σ₁, σ₂, σ₃, Matrix.mul_apply, Fin.sum_univ_two]

theorem kron3_mul (A B : Matrix Four Four ℂ) (C : Matrix (Fin 2) (Fin 2) ℂ)
    (A' B' : Matrix Four Four ℂ) (C' : Matrix (Fin 2) (Fin 2) ℂ) :
    ((A ⊗ₖ B) ⊗ₖ C) * ((A' ⊗ₖ B') ⊗ₖ C') = ((A * A') ⊗ₖ (B * B')) ⊗ₖ (C * C') := by
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]

/-- **Ten anticommuting lines:** `Γ_xΓ_y + Γ_yΓ_x = 2δ_xy`. -/
theorem tenLine_clifford (x y : Fin 5 ⊕ Fin 5) :
    tenLine x * tenLine y + tenLine y * tenLine x = if x = y then (2 : ℂ) • 1 else 0 := by
  rcases x with a | a <;> rcases y with b | b
  · simp only [tenLine, kron3_mul, Matrix.mul_one, σ₁_sq, ← Matrix.add_kronecker, clifford,
      Sum.inl.injEq]
    split_ifs <;> simp [Matrix.smul_kronecker, Matrix.one_kronecker_one]
  · simp only [tenLine, kron3_mul, Matrix.mul_one, Matrix.one_mul, reduceCtorEq, ↓reduceIte]
    rw [← Matrix.kronecker_add, σ₁σ₂_anti, Matrix.kronecker_zero]
  · simp only [tenLine, kron3_mul, Matrix.mul_one, Matrix.one_mul, reduceCtorEq, ↓reduceIte]
    rw [← Matrix.kronecker_add, add_comm (σ₂ * σ₁), σ₁σ₂_anti, Matrix.kronecker_zero]
  · simp only [tenLine, kron3_mul, Matrix.one_mul, σ₂_sq, Sum.inr.injEq]
    rw [← Matrix.add_kronecker, ← Matrix.kronecker_add, clifford]
    split_ifs
    · rw [Matrix.kronecker_smul, Matrix.smul_kronecker, Matrix.one_kronecker_one,
        Matrix.one_kronecker_one]
    · simp

/-- **The comparison is a rotation of the ten lines:** `−i Σ_t Γ_tΓ_{5+t} = (L − 1) ⊗ σ_z`. -/
theorem comparison_as_turn :
    (-I) • ∑ t, tenLine (Sum.inl t) * tenLine (Sum.inr t) = (L - 1) ⊗ₖ σ₃ := by
  have e : ∀ t, tenLine (Sum.inl t) * tenLine (Sum.inr t) = (I • (γ t ⊗ₖ γ t)) ⊗ₖ σ₃ := by
    intro t
    simp only [tenLine, kron3_mul, Matrix.mul_one, Matrix.one_mul, σ₁σ₂_eq,
      Matrix.kronecker_smul, Matrix.smul_kronecker]
  simp only [e, L, add_sub_cancel_left]
  rw [Finset.smul_sum]
  have : ∀ t, (-I) • ((I • (γ t ⊗ₖ γ t)) ⊗ₖ σ₃) = (γ t ⊗ₖ γ t) ⊗ₖ σ₃ := by
    intro t
    rw [Matrix.smul_kronecker, smul_smul]
    simp
  simp only [this]
  ext i j
  simp [Matrix.sum_apply, Matrix.kroneckerMap_apply, Finset.sum_mul]

/-! ## The swap on the sixteen two-spinor states -/

/-- The swap's sign on the sixteen two-spinor states: `−1` on the singlet and the vector states, `+1` on
the symmetric states. -/
def swapSign (k : Fin 16) : ℤ := if (disagreeSet k).card = 2 then 1 else -1

theorem relOpZ_J_transpose : ∀ k : Fin 16,
    (relOpZ k * JZ)ᵀ = (swapSign k : GaussianInt) • (relOpZ k * JZ) := by
  decide +kernel

theorem relOp_J_transpose (k : Fin 16) :
    (relOp k * J)ᵀ = (swapSign k : ℂ) • (relOp k * J) := by
  have e : relOp k * J = (relOpZ k * JZ).map GaussianInt.toComplex := by
    rw [Matrix.map_mul, relOpZ_map, JZ_map]
  rw [e, ← Matrix.transpose_map, relOpZ_J_transpose k, map_intSmul]

/-- **The swap on the sixteen two-spinor states:** `−1` on the singlet and the five vector states, `+1` on
the ten symmetric states. -/
theorem swap_rel (k : Fin 16) : swap *ᵥ rel k = (swapSign k : ℂ) • rel k := by
  rw [rel_eq_relOf, swap_relOf, MΩ, Matrix.mul_smul, Matrix.transpose_smul, relOp_J_transpose,
    smul_comm, ← relOf_smul]

theorem irrep_cases : ∀ k : Fin 16,
    (k = 0 ∧ (disagreeSet k).card = 0 ∧ swapSign k = -1) ∨
      (k ≠ 0 ∧ (disagreeSet k).card = 2 ∧ swapSign k = 1) ∨
      (k ≠ 0 ∧ (disagreeSet k).card = 4 ∧ swapSign k = -1) := by
  decide

theorem irrep_values : ∀ k : Fin 16,
    (Lvalue k = 6 ∧ swapSign k = -1) ∨ (Lvalue k = 2 ∧ swapSign k = 1) ∨
      (Lvalue k = -2 ∧ swapSign k = -1) := by
  decide

/-- **A quarter of the comparison is the swap:** `e^{−iπL/4} = −iP` on each of the sixteen
two-spinor states. -/
theorem quarter_comparison (k : Fin 16) :
    Complex.exp (-(Real.pi / 4 : ℂ) * (Lvalue k : ℂ) * I) • rel k = (-I) • (swap *ᵥ rel k) := by
  rw [swap_rel, smul_smul]
  congr 1
  rcases irrep_values k with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> push_cast
  · have : -((Real.pi : ℂ) / 4) * 6 * I = -(Real.pi * I) + -Real.pi / 2 * I := by ring
    rw [this, Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I,
      Complex.exp_neg_pi_div_two_mul_I]
    simp
  · have : -((Real.pi : ℂ) / 4) * 2 * I = -Real.pi / 2 * I := by ring
    rw [this, Complex.exp_neg_pi_div_two_mul_I]
    ring
  · have : -((Real.pi : ℂ) / 4) * (-2) * I = Real.pi / 2 * I := by ring
    rw [this, Complex.exp_pi_div_two_mul_I]
    ring

/-! ## Prop. 48: singlet, symmetric and vector states -/

/-- **Singlet, symmetric and vector states:** the sixteen two-spinor states disagree on `0`, `2` or `4` lines, `1 + 10 + 5`. -/
theorem irreps :
    (∀ k : Fin 16, (disagreeSet k).card = 0 ∨ (disagreeSet k).card = 2 ∨
      (disagreeSet k).card = 4) ∧
    (Finset.univ.filter fun k : Fin 16 => (disagreeSet k).card = 0).card = 1 ∧
    (Finset.univ.filter fun k : Fin 16 => (disagreeSet k).card = 2).card = 10 ∧
    (Finset.univ.filter fun k : Fin 16 => (disagreeSet k).card = 4).card = 5 := by
  decide

theorem Eop_rel (k : Fin 16) : Eop *ᵥ rel k = (if k = 0 then (4 : ℂ) else 0) • rel k := by
  rw [Eop_mulVec, ← rel_zero, rel_inner]
  by_cases h : k = 0
  · subst h
    simp
  · simp [h, Ne.symm h]

/-- **The projectors onto the singlet, the symmetric and the vector states:** `Π₀ = E/4`, `Π_F = (1 + P)/2`, `Π_L = (1 − P)/2 − E/4` are
one on the singlet, the symmetric states and the vector states respectively, zero on the rest. -/
theorem irrep_projectors (k : Fin 16) :
    ((1 / 4 : ℂ) • Eop) *ᵥ rel k = (if (disagreeSet k).card = 0 then 1 else 0 : ℂ) • rel k ∧
    ((1 / 2 : ℂ) • (1 + swap)) *ᵥ rel k =
      (if (disagreeSet k).card = 2 then 1 else 0 : ℂ) • rel k ∧
    ((1 / 2 : ℂ) • (1 - swap) - (1 / 4 : ℂ) • Eop) *ᵥ rel k =
      (if (disagreeSet k).card = 4 then 1 else 0 : ℂ) • rel k := by
  simp only [Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
    swap_rel, Eop_rel]
  rcases irrep_cases k with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · subst h1
    simp only [h2, h3, ↓reduceIte]
    refine ⟨?_, ?_, ?_⟩ <;> push_cast <;> module
  · simp only [h1, h2, h3, ↓reduceIte]
    refine ⟨?_, ?_, ?_⟩ <;> push_cast <;> module
  · simp only [h1, h2, h3, ↓reduceIte]
    refine ⟨?_, ?_, ?_⟩ <;> push_cast <;> module

/-! ## Prop. 47: the last-step direction -/

/-- The outer product `u v†` on `ℂ⁵`. -/
def outer (u v : Fin 5 → ℂ) : Matrix (Fin 5) (Fin 5) ℂ := Matrix.of fun i j => u i * star (v j)

/-- The last-step direction `h = e₃` and the plane's other line `k = e₄`; the three outside lines are `0, 1, 2`. -/
def lastDirectionVec : Fin 5 → ℂ := Pi.single 3 1
def otherVec : Fin 5 → ℂ := Pi.single 4 1

/-- The squared length of a vector of `ℂ⁵`. -/
noncomputable def sqLen (v : Fin 5 → ℂ) : ℝ := ∑ i, Complex.normSq (v i)

theorem outer_mulVec (u v w : Fin 5 → ℂ) : outer u v *ᵥ w = (star v ⬝ᵥ w) • u := by
  ext i
  simp only [outer, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.smul_apply, smul_eq_mul,
    Pi.star_apply, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem star_lastDirection_lastDirection : star lastDirectionVec ⬝ᵥ lastDirectionVec = 1 := by
  simp [lastDirectionVec, dotProduct, Pi.single_apply, Fin.sum_univ_five]

theorem star_other_lastDirection : star otherVec ⬝ᵥ lastDirectionVec = 0 := by
  simp [lastDirectionVec, otherVec, dotProduct, Pi.single_apply, Fin.sum_univ_five]

theorem sqLen_smul (c : ℂ) (v : Fin 5 → ℂ) : sqLen (c • v) = Complex.normSq c * sqLen v := by
  simp only [sqLen, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]

theorem sqLen_neg (v : Fin 5 → ℂ) : sqLen (-v) = sqLen v := by
  simp [sqLen]

theorem sqLen_lastDirection : sqLen lastDirectionVec = 1 := by
  simp [sqLen, lastDirectionVec, Pi.single_apply, Fin.sum_univ_five]

theorem sqLen_other : sqLen otherVec = 1 := by
  simp [sqLen, otherVec, Pi.single_apply, Fin.sum_univ_five]

/-- **The last-step direction's weights:** of the four rotations of the plane, `i hh†`, `i kk†`, `i(hk† + kh†)/√2`,
`(hk† − kh†)/√2`, the first moves the last-step direction with weight `1`, the second leaves it, the last two
with `½` each; the rotations of the three outside lines fix it. -/
theorem lastDirection_weights :
    sqLen ((I • outer lastDirectionVec lastDirectionVec) *ᵥ lastDirectionVec) = 1 ∧
    sqLen ((I • outer otherVec otherVec) *ᵥ lastDirectionVec) = 0 ∧
    sqLen (((I / Real.sqrt 2) • (outer lastDirectionVec otherVec + outer otherVec lastDirectionVec)) *ᵥ lastDirectionVec) =
      1 / 2 ∧
    sqLen (((1 / Real.sqrt 2 : ℂ) • (outer lastDirectionVec otherVec - outer otherVec lastDirectionVec)) *ᵥ
      lastDirectionVec) = 1 / 2 ∧
    ∀ X : Matrix (Fin 5) (Fin 5) ℂ, (∀ i j, 3 ≤ j.val → X i j = 0) → X *ᵥ lastDirectionVec = 0 := by
  have h2 : Complex.normSq ((Real.sqrt 2 : ℂ)) = 2 := by
    rw [Complex.normSq_ofReal, Real.mul_self_sqrt (by norm_num)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.smul_mulVec, outer_mulVec, star_lastDirection_lastDirection, one_smul, sqLen_smul, sqLen_lastDirection]
    simp
  · rw [Matrix.smul_mulVec, outer_mulVec, star_other_lastDirection, zero_smul, smul_zero]
    simp [sqLen]
  · rw [Matrix.smul_mulVec, Matrix.add_mulVec, outer_mulVec, outer_mulVec, star_lastDirection_lastDirection,
      star_other_lastDirection, one_smul, zero_smul, zero_add, sqLen_smul, sqLen_other]
    rw [Complex.normSq_div, Complex.normSq_I, h2]
    norm_num
  · rw [Matrix.smul_mulVec, Matrix.sub_mulVec, outer_mulVec, outer_mulVec, star_lastDirection_lastDirection,
      star_other_lastDirection, one_smul, zero_smul, zero_sub, smul_neg, sqLen_neg, sqLen_smul, sqLen_other,
      Complex.normSq_div, Complex.normSq_one, h2]
    norm_num
  · intro X hX
    ext i
    simp only [Matrix.mulVec, dotProduct, lastDirectionVec, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Pi.zero_apply]
    exact hX i 3 (by decide)

/-- **Three of the thirteen move the last-step direction:** `w_h = 3/13` and `χ_h = w_h(1 − w_h) = 30/169`. -/
theorem lastDirection_share : (3 : ℚ) / 13 * (1 - 3 / 13) = 30 / 169 := by norm_num

/-- **Without the common phase:** the Gram form of the two diagonal rotations on the last-step direction,
`[[½, g], [g, 3/10]]` with `g² = (½)²(3/5)`, has determinant `0` and trace `4/5`; then
`sin²θ = 1 − (½)/(4/5) = 3/8`. -/
theorem traceless_gram (g : ℝ) (hg : g ^ 2 = (1 / 2) ^ 2 * (3 / 5)) :
    (1 / 2 : ℝ) * (3 / 10) - g ^ 2 = 0 ∧ (1 / 2 : ℝ) + 3 / 10 = 4 / 5 ∧
      1 - (1 / 2 : ℝ) / (4 / 5) = 3 / 8 := by
  refine ⟨?_, by norm_num, by norm_num⟩
  rw [hg]
  norm_num

/-- The hypercharge as a rotation: `Y = diag(−⅓, −⅓, −⅓, ½, ½)` has `|Y|² = 5/6`; the rotation `iY/|Y|`
sends the last-step direction to `(i/2)h/|Y|`, of squared length `3/10`, and its real product with the rotation
`i(hh† − kk†)/√2` is `½(3/5)^{1/2}`. -/
theorem hypercharge_turn :
    (3 * (1 / 3 : ℝ) ^ 2 + 2 * (1 / 2) ^ 2 = 5 / 6) ∧
    ((1 / 2 : ℝ) ^ 2 / (5 / 6) = 3 / 10) ∧
    ((1 / Real.sqrt 2 * (1 / 2) / Real.sqrt (5 / 6)) ^ 2 = (1 / 2) ^ 2 * (3 / 5)) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  rw [div_pow, mul_pow, div_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt (by norm_num)]
  norm_num

end Comparison

end
