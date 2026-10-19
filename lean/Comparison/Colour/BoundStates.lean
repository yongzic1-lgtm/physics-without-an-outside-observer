module

public import Comparison.Existence.Pair

/-!
# Book XIII. Where the two bound states land (Proposition 75)

In the model of Proposition 23:
the five directions `γ 0, …, γ 4` with `γ₀γ₁γ₂γ₃γ₄ = 1` (`γ_prod`).

* `inversions`, `orderSign`: the sign of an ordering of the five directions, `(−1)^{inversions}`.
* `five_lines`: for every ordering `(a, b, c, d, e)` of the five directions,
  `γ_aγ_bγ_cγ_dγ_e = sgn · 1` (all `120` orderings, checked over `ℤ[i]`).
* `colour_product`: for the ordering `(h, k, c₁, c₂, c₃)`, `γ_{c₁}γ_{c₂}γ_{c₃} = −sgn · γ_hγ_k`;
  `colour_product_oriented`: in an orientation with `γ_hγ_kγ_{c₁}γ_{c₂}γ_{c₃} = 1`,
  `γ_{c₁}γ_{c₂}γ_{c₃} = −γ_hγ_k`; `colour_product_model`: `γ₂γ₃γ₄ = −γ₀γ₁`.
* `levi3`, `eps_lines`: `ε^{abc}γ_{c_a}γ_{c_b}γ_{c_c} = 6γ_{c₁}γ_{c₂}γ_{c₃}` for three
  different lines.
* `planeRel h k = (γ_hγ_k ⊗ 1)Ω`; `baryon_lands_on_plane`:
  `(γ_{c₁}γ_{c₂}γ_{c₃} ⊗ 1)Ω = −sgn · e_{hk}` (`= −e_{hk}` in the orientation with sign `+1`);
  `L_planeRel`: `L e_{hk} = 2 e_{hk}`.
* `meson_either_end`: `(γ_c ⊗ 1)Ω = (1 ⊗ γ_c)Ω`; `meson_lands_on_singlet`:
  `Σ_{c ∈ C} (γ_c ⊗ γ_c)Ω = 3Ω` for the three lines `C` outside a plane; `L_singlet`: `L Ω = 6Ω`.
-/

@[expose] public section

namespace Comparison

open Matrix hiding J
open Complex Kronecker

/-! ## The five directions in every order -/

/-- The inversions of a list of lines: the pairs that stand in the wrong order. -/
def inversions : List (Fin 5) → ℕ
  | [] => 0
  | x :: xs => (xs.filter fun y => decide (y < x)).length + inversions xs

/-- The sign of an ordering: `(−1)^{inversions}`. -/
def orderSign (l : List (Fin 5)) : ℤ := (-1) ^ inversions l

theorem five_linesZ : ∀ a b c d e : Fin 5, [a, b, c, d, e].Nodup →
    γZ a * γZ b * γZ c * γZ d * γZ e = (orderSign [a, b, c, d, e] : GaussianInt) • 1 := by
  decide +kernel

theorem map_one_gauss :
    (1 : Matrix Four Four GaussianInt).map GaussianInt.toComplex = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

/-- **The five directions in every order:** `γ_aγ_bγ_cγ_dγ_e = sgn(a b c d e) · 1`. -/
theorem five_lines (a b c d e : Fin 5) (h : [a, b, c, d, e].Nodup) :
    γ a * γ b * γ c * γ d * γ e = (orderSign [a, b, c, d, e] : ℂ) • 1 := by
  have e1 := congrArg (fun M => M.map GaussianInt.toComplex) (five_linesZ a b c d e h)
  simp only [Matrix.map_mul (f := GaussianInt.toComplex), γZ_map, map_intSmul,
    map_one_gauss] at e1
  exact e1

/-- The orientation of Proposition 23 has sign `+1`. -/
theorem orderSign_model : orderSign [0, 1, 2, 3, 4] = 1 := by decide

theorem γ_mul_γ_mul (s : Fin 5) (X : Matrix Four Four ℂ) : γ s * (γ s * X) = X := by
  rw [← Matrix.mul_assoc, γ_mul_self, Matrix.one_mul]

/-- **Three colour lines multiply to the plane `hk`:** for the ordering `(h, k, c₁, c₂, c₃)`,
`γ_{c₁}γ_{c₂}γ_{c₃} = −sgn · γ_hγ_k`. -/
theorem colour_product (h k c₁ c₂ c₃ : Fin 5) (hn : [h, k, c₁, c₂, c₃].Nodup) :
    γ c₁ * γ c₂ * γ c₃ = -((orderSign [h, k, c₁, c₂, c₃] : ℂ) • (γ h * γ k)) := by
  have hhk : h ≠ k := by
    intro e
    subst e
    simp at hn
  have h5 := five_lines h k c₁ c₂ c₃ hn
  have key : γ c₁ * γ c₂ * γ c₃ = (γ k * γ h) * (γ h * γ k * γ c₁ * γ c₂ * γ c₃) := by
    simp only [Matrix.mul_assoc, γ_mul_γ_mul]
  rw [key, h5, Matrix.mul_smul, Matrix.mul_one, γ_anticomm (Ne.symm hhk), smul_neg]

/-- **In an orientation with `γ_hγ_kγ_{c₁}γ_{c₂}γ_{c₃} = 1`, `γ_{c₁}γ_{c₂}γ_{c₃} = −γ_hγ_k`.** -/
theorem colour_product_oriented (h k c₁ c₂ c₃ : Fin 5) (hn : [h, k, c₁, c₂, c₃].Nodup)
    (hs : orderSign [h, k, c₁, c₂, c₃] = 1) :
    γ c₁ * γ c₂ * γ c₃ = -(γ h * γ k) := by
  rw [colour_product h k c₁ c₂ c₃ hn, hs]
  simp

/-- **In the model:** `γ₂γ₃γ₄ = −γ₀γ₁`. -/
theorem colour_product_model : γ 2 * γ 3 * γ 4 = -(γ 0 * γ 1) :=
  colour_product_oriented 0 1 2 3 4 (by decide) orderSign_model

/-! ## The alternating sum over the orders of three lines -/

/-- The alternating symbol on three letters. -/
def levi3 : Fin 3 → Fin 3 → Fin 3 → ℤ :=
  ![![![0, 0, 0], ![0, 0, 1], ![0, -1, 0]],
    ![![0, 0, -1], ![0, 0, 0], ![1, 0, 0]],
    ![![0, 1, 0], ![-1, 0, 0], ![0, 0, 0]]]

theorem levi3_values : levi3 0 1 2 = 1 ∧ levi3 1 2 0 = 1 ∧ levi3 2 0 1 = 1 ∧ levi3 1 0 2 = -1 ∧
    levi3 0 2 1 = -1 ∧ levi3 2 1 0 = -1 := by decide

/-- In any ring, three pairwise anticommuting elements: every order of their product is the
sign of the order times `xyz`. -/
theorem three_orders {R : Type*} [Ring R] (x y z : R) (hxy : x * y = -(y * x))
    (hxz : x * z = -(z * x)) (hyz : y * z = -(z * y)) :
    y * x * z = -(x * y * z) ∧ x * z * y = -(x * y * z) ∧ y * z * x = x * y * z ∧
      z * x * y = x * y * z ∧ z * y * x = -(x * y * z) := by
  have hyx : y * x = -(x * y) := by rw [hxy, neg_neg]
  have hzx : z * x = -(x * z) := by rw [hxz, neg_neg]
  have hzy : z * y = -(y * z) := by rw [hyz, neg_neg]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hyx, neg_mul]
  · rw [mul_assoc, hzy, mul_neg, ← mul_assoc]
  · rw [mul_assoc, hzx, mul_neg, ← mul_assoc, hyx, neg_mul, neg_neg]
  · rw [hzx, neg_mul, mul_assoc, hzy, mul_neg, neg_neg, ← mul_assoc]
  · rw [hzy, neg_mul, mul_assoc, hzx, mul_neg, ← mul_assoc, hyx, neg_mul, neg_neg]

/-- **`ε^{abc}γ_aγ_bγ_c = 6γ_{c₁}γ_{c₂}γ_{c₃}`** for three different lines `c₁, c₂, c₃`. -/
theorem eps_lines (c : Fin 3 → Fin 5) (hc : Function.Injective c) :
    ∑ a, ∑ b, ∑ d, (levi3 a b d : ℂ) • (γ (c a) * γ (c b) * γ (c d)) =
      (6 : ℂ) • (γ (c 0) * γ (c 1) * γ (c 2)) := by
  have h01 : c 0 ≠ c 1 := fun e => absurd (hc e) (by decide)
  have h02 : c 0 ≠ c 2 := fun e => absurd (hc e) (by decide)
  have h12 : c 1 ≠ c 2 := fun e => absurd (hc e) (by decide)
  obtain ⟨t1, t2, t3, t4, t5⟩ := three_orders (γ (c 0)) (γ (c 1)) (γ (c 2)) (γ_anticomm h01)
    (γ_anticomm h02) (γ_anticomm h12)
  simp only [Fin.sum_univ_three, levi3, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Int.cast_zero, zero_smul, add_zero,
    zero_add, Int.cast_one, one_smul, Int.cast_neg, neg_smul]
  rw [t1, t2, t3, t4, t5]
  module

/-! ## The baryon's antisymmetric state lands on the plane `hk` -/

/-- The symmetric state of the ordered pair `(h, k)`: `e_{hk} = (γ_hγ_k ⊗ 1)Ω`. -/
noncomputable def planeRel (h k : Fin 5) : Two → ℂ := ((γ h * γ k) ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω

/-- **The baryon's antisymmetric state lands on the plane `hk`:** `(γ_{c₁}γ_{c₂}γ_{c₃} ⊗ 1)Ω = −sgn · e_{hk}`. -/
theorem baryon_lands_on_plane (h k c₁ c₂ c₃ : Fin 5) (hn : [h, k, c₁, c₂, c₃].Nodup) :
    ((γ c₁ * γ c₂ * γ c₃) ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω =
      -((orderSign [h, k, c₁, c₂, c₃] : ℂ) • planeRel h k) := by
  rw [colour_product h k c₁ c₂ c₃ hn, ← neg_smul, Matrix.smul_kronecker, Matrix.smul_mulVec,
    neg_smul, planeRel]

/-- In the model: `(γ₂γ₃γ₄ ⊗ 1)Ω = −e_{01}`. -/
theorem baryon_lands_on_plane_model :
    ((γ 2 * γ 3 * γ 4) ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω = -planeRel 0 1 := by
  rw [baryon_lands_on_plane 0 1 2 3 4 (by decide), orderSign_model]
  simp

theorem planeRel_eq (h k : Fin 5) : planeRel h k = relOf (γ h * γ k * MΩ) := by
  rw [planeRel, Ω, kron_mulVec_relOf, Matrix.transpose_one, Matrix.mul_one]

/-- A line `γ_s` turns `γ_hγ_k` into `∓γ_hγ_k`: minus exactly when `s` is a line of the plane. -/
theorem γ_conj_plane (s h k : Fin 5) (hk : h ≠ k) :
    γ s * γ h * γ k * γ s =
      (if s ∈ ({h, k} : Finset (Fin 5)) then -1 else 1 : ℂ) • (γ h * γ k) := by
  rw [show γ s * γ h * γ k * γ s = γ s * (γ h * γ k) * γ s by simp only [Matrix.mul_assoc]]
  by_cases hs : s = h
  · subst hs
    rw [γ_conj_plane_left hk]
    simp
  · by_cases hs' : s = k
    · subst hs'
      rw [γ_conj_plane_right hk]
      simp
    · rw [γ_conj_plane_out hs hs']
      simp [hs, hs']

/-- **The comparison on a symmetric state:** `L e_{hk} = 2 e_{hk}`. -/
theorem L_planeRel (h k : Fin 5) (hk : h ≠ k) : L *ᵥ planeRel h k = (2 : ℂ) • planeRel h k := by
  have each : ∀ s, (γ s ⊗ₖ γ s) *ᵥ planeRel h k =
      (if s ∈ ({h, k} : Finset (Fin 5)) then -1 else 1 : ℂ) • planeRel h k := by
    intro s
    rw [planeRel_eq, kron_mulVec_relOf]
    simp only [Matrix.mul_assoc]
    rw [MΩ_mul_γ_transpose]
    simp only [← Matrix.mul_assoc]
    rw [γ_conj_plane s h k hk, Matrix.smul_mul, relOf_smul]
  rw [L, Matrix.add_mulVec, one_kronecker_one, Matrix.one_mulVec, Matrix.sum_mulVec]
  simp only [each]
  rw [← Finset.sum_smul, sum_sign, Finset.card_pair hk]
  module

/-! ## The meson's bound state lands on the singlet -/

/-- **A line closes with its conjugate from either end:** `(γ_c ⊗ 1)Ω = (1 ⊗ γ_c)Ω`. -/
theorem meson_either_end (c : Fin 5) : (γ c ⊗ₖ 1) *ᵥ Ω = (1 ⊗ₖ γ c) *ᵥ Ω :=
  (same_from_either_thing c).symm

/-- The three lines outside the plane `{h, k}`. -/
def outside (h k : Fin 5) : Finset (Fin 5) := Finset.univ.filter fun c => c ≠ h ∧ c ≠ k

theorem card_outside (h k : Fin 5) (hk : h ≠ k) : (outside h k).card = 3 := by
  revert h k
  decide

/-- **The meson's bound state lands on the singlet:** `Σ_{c ∈ C} (γ_c ⊗ γ_c)Ω = 3Ω`. -/
theorem meson_lands_on_singlet (h k : Fin 5) (hk : h ≠ k) :
    ∑ c ∈ outside h k, (γ c ⊗ₖ γ c) *ᵥ Ω = (3 : ℂ) • Ω := by
  have h0 : ∀ c, c ∉ disagreeSet 0 := by decide
  have each : ∀ c, (γ c ⊗ₖ γ c) *ᵥ Ω = Ω := by
    intro c
    have := agreement c 0
    rw [rel_zero] at this
    rw [this]
    simp [h0 c]
  simp only [each, Finset.sum_const, card_outside h k hk]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  norm_num

/-- **The singlet has the comparison `6`:** `L Ω = 6Ω`. -/
theorem L_singlet : L *ᵥ Ω = (6 : ℂ) • Ω := by
  have := L_rel 0
  rw [rel_zero] at this
  rw [this]
  have h0 : (disagreeSet 0).card = 0 := by decide
  rw [h0]
  norm_num

end Comparison

end
