import Comparison.Existence.Pair

/-!
# The operators the rotations keep (Proposition 13's second line; Propositions 15 and A15 at `N = 1, 2`)

**`N = 2`.** An operator `X` on `H ⊗ H` that commutes with every `U ⊗ U`, `U ∈ Sp(2)` (`UU† = 1`, `UJUᵀ = J`),
is `a + bP + cE` (`commutant_two`), and `1`, `P`, `E` are independent (`one_swap_E_independent`): the kept
operators form a space of dimension three. The proof uses two types of rotations of `Sp(2)`: `γ_aγ_b`, whose
square `U ⊗ U` is diagonal on the sixteen two-spinor states with the sixteen distinct characters, so `X` is diagonal
there; and `(1 + γ_aγ_b)/√2`, which with them gives `γ_aγ_b ⊗ 1 + 1 ⊗ γ_aγ_b`, whose matrix elements join the
two-spinor states of the singlet, the symmetric or the vector states, so `X` is constant on the singlet, the symmetric or the vector states: `X = x₀Π₀ + x_FΠ_F + x_LΠ_L`.

**`N = 1`.** An operator on `H` that commutes with every rotation of `Sp(2)` is a number (`commutant_one`).

**`N = 3, 4`** (dimensions 14 and 84) rest on the first fundamental theorem of invariant theory for `Sp(2)`
and on Weyl's integral; they stay open here.
-/

namespace Comparison.Article

open Matrix hiding J
open Complex Kronecker

/-! ## The sixteen two-spinor states as a basis -/

theorem rel_expand (v : Two → ℂ) : v = ∑ l, (star (rel l) ⬝ᵥ v) • rel l := by
  have hv : v ∈ Submodule.span ℂ (Set.range rel) := by rw [rel_span]; trivial
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hv
  have hcoef : ∀ l, star (rel l) ⬝ᵥ v = c l := by
    intro l
    rw [← hc, dotProduct_sum]
    simp only [dotProduct_smul, rel_inner, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp
  conv_lhs => rw [← hc]
  exact Finset.sum_congr rfl fun l _ => by rw [hcoef]

theorem mat_ext_rel (M N : Matrix Two Two ℂ) (h : ∀ k, M *ᵥ rel k = N *ᵥ rel k) : M = N := by
  have hv : ∀ v, M *ᵥ v = N *ᵥ v := by
    intro v
    rw [rel_expand v, Matrix.mulVec_sum, Matrix.mulVec_sum]
    exact Finset.sum_congr rfl fun l _ => by rw [Matrix.mulVec_smul, Matrix.mulVec_smul, h]
  apply Matrix.toLin'.injective
  ext v
  simp [Matrix.toLin'_apply, hv]

theorem inner_mulVec_herm (M : Matrix Two Two ℂ) (hM : Mᴴ = M) (v w : Two → ℂ) :
    star v ⬝ᵥ (M *ᵥ w) = star (M *ᵥ v) ⬝ᵥ w := by
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec, hM]

/-! ## The rotations `γ_aγ_b` and `(1 + γ_aγ_b)/√2` are in `Sp(2)` -/

theorem γγ_unitary {a b : Fin 5} (hab : a ≠ b) : (γ a * γ b) * (γ a * γ b)ᴴ = 1 := by
  rw [Matrix.conjTranspose_mul, γ_conjTranspose, γ_conjTranspose]
  calc γ a * γ b * (γ b * γ a) = γ a * (γ b * γ b) * γ a := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [γ_mul_self, Matrix.mul_one, γ_mul_self]

theorem J_γ_transpose (s : Fin 5) : J * (γ s)ᵀ = γ s * J := (γ_mul_J_eq s).symm

theorem γγ_keeps_J {a b : Fin 5} : (γ a * γ b) * J * (γ a * γ b)ᵀ = J := by
  rw [Matrix.transpose_mul]
  calc γ a * γ b * J * ((γ b)ᵀ * (γ a)ᵀ) = γ a * γ b * (J * (γ b)ᵀ) * (γ a)ᵀ := by
        simp only [Matrix.mul_assoc]
    _ = γ a * (γ b * γ b) * (J * (γ a)ᵀ) := by rw [J_γ_transpose]; simp only [Matrix.mul_assoc]
    _ = γ a * (γ a * J) := by rw [γ_mul_self, Matrix.mul_one, J_γ_transpose]
    _ = J := by rw [← Matrix.mul_assoc, γ_mul_self, Matrix.one_mul]

theorem γγ_sq {a b : Fin 5} (hab : a ≠ b) : (γ a * γ b) * (γ a * γ b) = -1 := by
  calc γ a * γ b * (γ a * γ b) = γ a * (γ b * γ a) * γ b := by simp only [Matrix.mul_assoc]
    _ = γ a * (-(γ a * γ b)) * γ b := by rw [γ_anticomm (Ne.symm hab)]
    _ = -((γ a * γ a) * (γ b * γ b)) := by simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    _ = -1 := by rw [γ_mul_self, γ_mul_self, Matrix.mul_one]

theorem γγ_conjTranspose {a b : Fin 5} (hab : a ≠ b) : (γ a * γ b)ᴴ = -(γ a * γ b) := by
  rw [Matrix.conjTranspose_mul, γ_conjTranspose, γ_conjTranspose, γ_anticomm (Ne.symm hab)]

theorem J_γγ_transpose {a b : Fin 5} : J * (γ a * γ b)ᵀ = (γ b * γ a) * J := by
  rw [Matrix.transpose_mul, ← Matrix.mul_assoc, J_γ_transpose, Matrix.mul_assoc, J_γ_transpose,
    ← Matrix.mul_assoc]

/-- The quarter turn `(1 + γ_aγ_b)/√2`. -/
noncomputable def qturn (a b : Fin 5) : Matrix Four Four ℂ := ((√2 : ℝ) : ℂ)⁻¹ • (1 + γ a * γ b)

theorem sqrt2_inv_sq : (((√2 : ℝ) : ℂ)⁻¹) ^ 2 = 1 / 2 := by
  rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
  norm_num

theorem qturn_unitary {a b : Fin 5} (hab : a ≠ b) : qturn a b * (qturn a b)ᴴ = 1 := by
  have hs : star (((√2 : ℝ) : ℂ)⁻¹) = ((√2 : ℝ) : ℂ)⁻¹ := by simp
  rw [qturn, Matrix.conjTranspose_smul, hs, Matrix.conjTranspose_add, Matrix.conjTranspose_one,
    γγ_conjTranspose hab]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [← sq, sqrt2_inv_sq,
    show (1 + γ a * γ b) * (1 + -(γ a * γ b)) = 1 - (γ a * γ b) * (γ a * γ b) by noncomm_ring,
    γγ_sq hab, sub_neg_eq_add, ← two_smul ℂ (1 : Matrix Four Four ℂ), smul_smul]
  norm_num

theorem qturn_keeps_J {a b : Fin 5} (hab : a ≠ b) : qturn a b * J * (qturn a b)ᵀ = J := by
  rw [qturn, Matrix.transpose_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [← sq, sqrt2_inv_sq, Matrix.transpose_add, Matrix.transpose_one]
  have h1 : (1 + γ a * γ b) * J * (1 + (γ a * γ b)ᵀ) =
      J + (γ a * γ b) * J + J * (γ a * γ b)ᵀ + (γ a * γ b) * J * (γ a * γ b)ᵀ := by noncomm_ring
  rw [h1, γγ_keeps_J, J_γγ_transpose, γ_anticomm (Ne.symm hab)]
  rw [show J + γ a * γ b * J + -(γ a * γ b) * J + J = (2 : ℂ) • J by
    rw [two_smul]; noncomm_ring, smul_smul]
  norm_num

/-! ## The characters of the sixteen two-spinor states -/

/-- The sign of the line `u` on the two-spinor state `k`. -/
def lsign (u : Fin 5) (k : Fin 16) : ℂ := if u ∈ disagreeSet k then -1 else 1

theorem γγ_kron_rel (a b : Fin 5) (k : Fin 16) :
    ((γ a * γ b) ⊗ₖ (γ a * γ b)) *ᵥ rel k = (lsign a k * lsign b k) • rel k := by
  rw [Matrix.mul_kronecker_mul, ← Matrix.mulVec_mulVec, agreement, Matrix.mulVec_smul, agreement,
    smul_smul, lsign, lsign, mul_comm]

theorem γγ_kron_herm (a b : Fin 5) (hab : a ≠ b) :
    ((γ a * γ b) ⊗ₖ (γ a * γ b))ᴴ = (γ a * γ b) ⊗ₖ (γ a * γ b) := by
  rw [Matrix.conjTranspose_kronecker, γγ_conjTranspose hab, ← neg_one_smul ℂ (γ a * γ b),
    Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul]
  norm_num

theorem lsign_real (u : Fin 5) (k : Fin 16) : star (lsign u k) = lsign u k := by
  unfold lsign; split_ifs <;> simp

/-- The sign as an integer. -/
def lsignZ (u : Fin 5) (k : Fin 16) : ℤ := if u ∈ disagreeSet k then -1 else 1

theorem lsign_eq (u : Fin 5) (k : Fin 16) : lsign u k = (lsignZ u k : ℂ) := by
  unfold lsign lsignZ; split_ifs <;> simp

theorem charactersZ_separate : ∀ j k : Fin 16, j ≠ k →
    ∃ a b : Fin 5, a ≠ b ∧ lsignZ a j * lsignZ b j ≠ lsignZ a k * lsignZ b k := by
  decide

/-- **Distinct two-spinor states have distinct characters** under the pairs of lines. -/
theorem characters_separate (j k : Fin 16) (hjk : j ≠ k) :
    ∃ a b : Fin 5, a ≠ b ∧ lsign a j * lsign b j ≠ lsign a k * lsign b k := by
  obtain ⟨a, b, hab, h⟩ := charactersZ_separate j k hjk
  refine ⟨a, b, hab, ?_⟩
  rw [lsign_eq, lsign_eq, lsign_eq, lsign_eq]
  exact_mod_cast h

/-! ## `N = 2`: the commutant -/

/-- The quarter turn's square on two systems gives the generator `γ_aγ_b ⊗ 1 + 1 ⊗ γ_aγ_b`. -/
theorem qturn_kron (a b : Fin 5) :
    qturn a b ⊗ₖ qturn a b = (1 / 2 : ℂ) • (1 + ((γ a * γ b) ⊗ₖ 1 + 1 ⊗ₖ (γ a * γ b)) +
      (γ a * γ b) ⊗ₖ (γ a * γ b)) := by
  rw [qturn, Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul, ← sq, sqrt2_inv_sq]
  rw [Matrix.add_kronecker, Matrix.kronecker_add, Matrix.kronecker_add, Matrix.one_kronecker_one]
  congr 1
  abel

theorem MΩ_γγ_transpose {a b : Fin 5} (hab : a ≠ b) : MΩ * (γ a * γ b)ᵀ = -(γ a * γ b) * MΩ := by
  rw [Matrix.transpose_mul, ← Matrix.mul_assoc, MΩ_mul_γ_transpose, Matrix.mul_assoc, MΩ_mul_γ_transpose,
    ← Matrix.mul_assoc, γ_anticomm (Ne.symm hab)]

/-- The generator on a two-spinor state: `(A ⊗ 1 + 1 ⊗ A) e_k = ([A, B_k] ⊗ 1) Ω` for `A = γ_aγ_b`. -/
theorem gen_rel {a b : Fin 5} (hab : a ≠ b) (k : Fin 16) :
    ((γ a * γ b) ⊗ₖ 1 + 1 ⊗ₖ (γ a * γ b)) *ᵥ rel k =
      relOf ((γ a * γ b * relOp k - relOp k * (γ a * γ b)) * MΩ) := by
  rw [Matrix.add_mulVec, rel_eq_relOf, kron_mulVec_relOf, kron_mulVec_relOf, Matrix.transpose_one,
    Matrix.mul_one, Matrix.one_mul, ← relOf_add]
  congr 1
  rw [Matrix.mul_assoc (relOp k), MΩ_γγ_transpose hab]
  noncomm_ring

/-- A step that joins two two-spinor states of the singlet, the symmetric or the vector states: `[γ_aγ_b, B_k] = d B_j` with `d ≠ 0`. -/
theorem join_step {a b : Fin 5} (hab : a ≠ b) {j k : Fin 16} {d : ℂ} (hd : d ≠ 0)
    (hjk : γ a * γ b * relOp k - relOp k * (γ a * γ b) = d • relOp j) (X : Matrix Two Two ℂ)
    (hT : X * ((γ a * γ b) ⊗ₖ 1 + 1 ⊗ₖ (γ a * γ b)) = ((γ a * γ b) ⊗ₖ 1 + 1 ⊗ₖ (γ a * γ b)) * X)
    (xj xk : ℂ) (hxj : X *ᵥ rel j = xj • rel j) (hxk : X *ᵥ rel k = xk • rel k) : xj = xk := by
  have hT' : ((γ a * γ b) ⊗ₖ 1 + 1 ⊗ₖ (γ a * γ b)) *ᵥ rel k = d • rel j := by
    rw [gen_rel hab, hjk, Matrix.smul_mul, relOf_smul, ← rel_eq_relOf]
  have e := congrArg (fun M => M *ᵥ rel k) hT
  simp only at e
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hT', hxk] at e
  simp only [Matrix.mulVec_smul] at e
  rw [hT', hxj, smul_smul, smul_smul] at e
  have hrel := congrArg (fun v => star (rel j) ⬝ᵥ v) e
  simp only [dotProduct_smul, rel_inner, if_true, smul_eq_mul, mul_one] at hrel
  exact mul_left_cancel₀ hd (by rw [hrel]; ring)

/-! The thirteen joining steps: four along the lines, nine among the symmetric states. -/

theorem js_line0 : γ 0 * γ 1 * relOp 1 - relOp 1 * (γ 0 * γ 1) = (-2 : ℂ) • relOp 2 := by
  four_ext <;> simp [relOp, γ, σ₁, σ₂, σ₃, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
    ring
theorem js_line1 : γ 1 * γ 2 * relOp 2 - relOp 2 * (γ 1 * γ 2) = (-2 : ℂ) • relOp 3 := by
  four_ext <;> simp [relOp, γ, σ₁, σ₂, σ₃, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
    ring
theorem js_line2 : γ 2 * γ 3 * relOp 3 - relOp 3 * (γ 2 * γ 3) = (-2 : ℂ) • relOp 4 := by
  four_ext <;> simp [relOp, γ, σ₁, σ₂, σ₃, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
    ring
theorem js_line3 : γ 3 * γ 4 * relOp 4 - relOp 4 * (γ 3 * γ 4) = (-2 : ℂ) • relOp 5 := by
  four_ext <;> simp [relOp, γ, σ₁, σ₂, σ₃, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
    ring
theorem js_f10 : γ 0 * γ 2 * relOp 6 - relOp 6 * (γ 0 * γ 2) = (2 : ℂ) • relOp 10 := by
  four_ext <;> simp [relOp, γ, σ₁, σ₂, σ₃, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
    ring
theorem js_f11 : γ 0 * γ 3 * relOp 6 - relOp 6 * (γ 0 * γ 3) = (2 : ℂ) • relOp 11 := by
  four_ext <;> simp [relOp, γ, σ₁, σ₂, σ₃, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
    ring
theorem js_f12 : γ 0 * γ 4 * relOp 6 - relOp 6 * (γ 0 * γ 4) = (2 : ℂ) • relOp 12 := by
  four_ext <;> simp [relOp, γ, σ₁, σ₂, σ₃, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
    ring
theorem js_f7 : γ 1 * γ 2 * relOp 6 - relOp 6 * (γ 1 * γ 2) = (-2 : ℂ) • relOp 7 := by
  four_ext <;> simp [relOp, γ, σ₁, σ₂, σ₃, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
    ring
theorem js_f8 : γ 1 * γ 3 * relOp 6 - relOp 6 * (γ 1 * γ 3) = (-2 : ℂ) • relOp 8 := by
  four_ext <;> simp [relOp, γ, σ₁, σ₂, σ₃, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
    ring
theorem js_f9 : γ 1 * γ 4 * relOp 6 - relOp 6 * (γ 1 * γ 4) = (-2 : ℂ) • relOp 9 := by
  four_ext <;> simp [relOp, γ, σ₁, σ₂, σ₃, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
    ring
theorem js_f13 : γ 1 * γ 3 * relOp 10 - relOp 10 * (γ 1 * γ 3) = (2 : ℂ) • relOp 13 := by
  four_ext <;> simp [relOp, γ, σ₁, σ₂, σ₃, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
    ring
theorem js_f14 : γ 1 * γ 4 * relOp 10 - relOp 10 * (γ 1 * γ 4) = (2 : ℂ) • relOp 14 := by
  four_ext <;> simp [relOp, γ, σ₁, σ₂, σ₃, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
    ring
theorem js_f15 : γ 1 * γ 4 * relOp 11 - relOp 11 * (γ 1 * γ 4) = (2 : ℂ) • relOp 15 := by
  four_ext <;> simp [relOp, γ, σ₁, σ₂, σ₃, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two] <;>
    ring

/-- **Proposition 13, second line: an operator on two systems that commutes with every `U ⊗ U`,
`U ∈ Sp(2)`, is a combination of the singlet, the symmetric and the vector states `Π₀ = E/4`, `Π_F = (1 + P)/2`, `Π_L = (1 − P)/2 − E/4`,
that is of `1`, `P` and `E`.** -/
theorem commutant_two (X : Matrix Two Two ℂ)
    (hX : ∀ U : Matrix Four Four ℂ, U * Uᴴ = 1 → U * J * Uᵀ = J → X * (U ⊗ₖ U) = (U ⊗ₖ U) * X) :
    X = (star (rel 0) ⬝ᵥ (X *ᵥ rel 0)) • ((1 / 4 : ℂ) • Eop) +
      (star (rel 6) ⬝ᵥ (X *ᵥ rel 6)) • ((1 / 2 : ℂ) • (1 + swap)) +
      (star (rel 1) ⬝ᵥ (X *ᵥ rel 1)) • ((1 / 2 : ℂ) • (1 - swap) - (1 / 4 : ℂ) • Eop) := by
  have hD : ∀ a b : Fin 5, a ≠ b →
      X * ((γ a * γ b) ⊗ₖ (γ a * γ b)) = ((γ a * γ b) ⊗ₖ (γ a * γ b)) * X :=
    fun a b hab => hX _ (γγ_unitary hab) γγ_keeps_J
  have hT : ∀ a b : Fin 5, a ≠ b → X * ((γ a * γ b) ⊗ₖ 1 + 1 ⊗ₖ (γ a * γ b)) =
      ((γ a * γ b) ⊗ₖ 1 + 1 ⊗ₖ (γ a * γ b)) * X := by
    intro a b hab
    have h := hX _ (qturn_unitary hab) (qturn_keeps_J hab)
    rw [qturn_kron, Matrix.mul_smul, Matrix.smul_mul] at h
    have h2 : X * (1 + ((γ a * γ b) ⊗ₖ 1 + 1 ⊗ₖ (γ a * γ b)) + (γ a * γ b) ⊗ₖ (γ a * γ b)) =
        (1 + ((γ a * γ b) ⊗ₖ 1 + 1 ⊗ₖ (γ a * γ b)) + (γ a * γ b) ⊗ₖ (γ a * γ b)) * X := by
      have h' := congrArg (fun M => (2 : ℂ) • M) h
      simp only [smul_smul] at h'
      norm_num at h'
      exact h'
    rw [Matrix.mul_add, Matrix.mul_add, Matrix.add_mul, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
      hD a b hab] at h2
    exact add_left_cancel (add_right_cancel h2)
  have hdiag : ∀ j k : Fin 16, j ≠ k → star (rel j) ⬝ᵥ (X *ᵥ rel k) = 0 := by
    intro j k hjk
    obtain ⟨a, b, hab, hne⟩ := characters_separate j k hjk
    have e := congrArg (fun M => M *ᵥ rel k) (hD a b hab)
    simp only at e
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, γγ_kron_rel, Matrix.mulVec_smul] at e
    have hrel := congrArg (fun v => star (rel j) ⬝ᵥ v) e
    try simp only at hrel
    rw [inner_mulVec_herm _ (γγ_kron_herm a b hab), γγ_kron_rel, star_smul, smul_dotProduct,
      dotProduct_smul, star_mul', lsign_real, lsign_real] at hrel
    simp only [smul_eq_mul] at hrel
    have : (lsign a k * lsign b k - lsign a j * lsign b j) * (star (rel j) ⬝ᵥ (X *ᵥ rel k)) = 0 := by
      rw [sub_mul, hrel]; ring
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h).symm hne
    · exact h
  have hx : ∀ k : Fin 16, X *ᵥ rel k = (star (rel k) ⬝ᵥ (X *ᵥ rel k)) • rel k := by
    intro k
    conv_lhs => rw [rel_expand (X *ᵥ rel k)]
    rw [Finset.sum_eq_single k (fun l _ hl => by rw [hdiag l k hl, zero_smul]) (by simp)]
  have j1 := join_step (by decide) (by norm_num) js_line0 X (hT _ _ (by decide)) _ _ (hx 2) (hx 1)
  have j2 := join_step (by decide) (by norm_num) js_line1 X (hT _ _ (by decide)) _ _ (hx 3) (hx 2)
  have j3 := join_step (by decide) (by norm_num) js_line2 X (hT _ _ (by decide)) _ _ (hx 4) (hx 3)
  have j4 := join_step (by decide) (by norm_num) js_line3 X (hT _ _ (by decide)) _ _ (hx 5) (hx 4)
  have f10 := join_step (by decide) (by norm_num) js_f10 X (hT _ _ (by decide)) _ _ (hx 10) (hx 6)
  have f11 := join_step (by decide) (by norm_num) js_f11 X (hT _ _ (by decide)) _ _ (hx 11) (hx 6)
  have f12 := join_step (by decide) (by norm_num) js_f12 X (hT _ _ (by decide)) _ _ (hx 12) (hx 6)
  have f7 := join_step (by decide) (by norm_num) js_f7 X (hT _ _ (by decide)) _ _ (hx 7) (hx 6)
  have f8 := join_step (by decide) (by norm_num) js_f8 X (hT _ _ (by decide)) _ _ (hx 8) (hx 6)
  have f9 := join_step (by decide) (by norm_num) js_f9 X (hT _ _ (by decide)) _ _ (hx 9) (hx 6)
  have f13 := join_step (by decide) (by norm_num) js_f13 X (hT _ _ (by decide)) _ _ (hx 13) (hx 10)
  have f14 := join_step (by decide) (by norm_num) js_f14 X (hT _ _ (by decide)) _ _ (hx 14) (hx 10)
  have f15 := join_step (by decide) (by norm_num) js_f15 X (hT _ _ (by decide)) _ _ (hx 15) (hx 11)
  -- the value of `X` on each two-spinor state is that of its set of states
  have hval : ∀ k : Fin 16, star (rel k) ⬝ᵥ (X *ᵥ rel k) =
      if (disagreeSet k).card = 0 then star (rel 0) ⬝ᵥ (X *ᵥ rel 0)
      else if (disagreeSet k).card = 2 then star (rel 6) ⬝ᵥ (X *ᵥ rel 6)
      else star (rel 1) ⬝ᵥ (X *ᵥ rel 1) := by
    intro k
    fin_cases k
    · rfl
    · rfl
    · exact j1
    · exact j2.trans j1
    · exact j3.trans (j2.trans j1)
    · exact j4.trans (j3.trans (j2.trans j1))
    · rfl
    · exact f7
    · exact f8
    · exact f9
    · exact f10
    · exact f11
    · exact f12
    · exact f13.trans f10
    · exact f14.trans f10
    · exact f15.trans f11
  apply mat_ext_rel
  intro k
  obtain ⟨p0, pF, pL⟩ := irrep_projectors k
  rw [hx k, hval k, Matrix.add_mulVec, Matrix.add_mulVec,
    Matrix.smul_mulVec (star (rel 0) ⬝ᵥ (X *ᵥ rel 0)) ((1 / 4 : ℂ) • Eop) (rel k),
    Matrix.smul_mulVec (star (rel 6) ⬝ᵥ (X *ᵥ rel 6)) ((1 / 2 : ℂ) • (1 + swap)) (rel k),
    Matrix.smul_mulVec (star (rel 1) ⬝ᵥ (X *ᵥ rel 1)) ((1 / 2 : ℂ) • (1 - swap) - (1 / 4 : ℂ) • Eop) (rel k),
    p0, pF, pL]
  have hc : (disagreeSet k).card = 0 ∨ (disagreeSet k).card = 2 ∨ (disagreeSet k).card = 4 := by
    fin_cases k <;> decide
  rcases hc with h | h | h <;> simp [h]

/-- `1`, `P` and `E` are independent: the kept operators on two systems form a space of dimension three. -/
theorem one_swap_E_independent (a b c : ℂ) (h : a • (1 : Matrix Two Two ℂ) + b • swap + c • Eop = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have e : ∀ k, (a • (1 : Matrix Two Two ℂ) + b • swap + c • Eop) *ᵥ rel k = 0 := by
    intro k; rw [h]; simp
  have i0 := congrArg (fun v => star (rel 0) ⬝ᵥ v) (e 0)
  have i6 := congrArg (fun v => star (rel 6) ⬝ᵥ v) (e 6)
  have i1 := congrArg (fun v => star (rel 1) ⬝ᵥ v) (e 1)
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, swap_rel, Eop_mulVec,
    ← rel_zero, dotProduct_add, dotProduct_smul, rel_inner, smul_eq_mul] at i0 i6 i1
  simp [swapSign, disagreeSet] at i0 i6 i1
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (1 / 2 : ℂ) * i6 + (1 / 2 : ℂ) * i1
  · linear_combination (1 / 2 : ℂ) * i6 - (1 / 2 : ℂ) * i1
  · linear_combination (1 / 4 : ℂ) * i0 - (1 / 4 : ℂ) * i1

/-! ## `N = 1` -/

theorem trace_mul_anticomm (X Y G : Matrix Four Four ℂ) (hG : G * G = 1) (hXG : X * G = G * X)
    (hYG : Y * G = -(G * Y)) : (X * Y).trace = 0 := by
  have hGYG : G * Y * G = -(Y * G * G) := by
    have : G * Y = -(Y * G) := by rw [hYG, neg_neg]
    rw [this, Matrix.neg_mul]
  have h : (X * Y).trace = -(X * Y).trace := by
    have e1 : (X * Y).trace = (X * Y * G * G).trace := by
      rw [Matrix.mul_assoc (X * Y), hG, Matrix.mul_one]
    have e2 : (X * Y * G * G).trace = (G * (X * Y * G)).trace := Matrix.trace_mul_comm (X * Y * G) G
    have e3 : G * (X * Y * G) = X * (G * Y * G) := by
      rw [show G * (X * Y * G) = (G * X) * Y * G by simp only [Matrix.mul_assoc], ← hXG]
      simp only [Matrix.mul_assoc]
    conv_lhs => rw [e1, e2, e3, hGYG, Matrix.mul_assoc Y G G, hG, Matrix.mul_one, Matrix.mul_neg,
      Matrix.trace_neg]
  have : (2 : ℂ) * (X * Y).trace = 0 := by linear_combination h
  simpa using this

theorem plane_anti (a b : Fin 5) (hab : a ≠ b) :
    (I • (γ a * γ b)) * γ a = -(γ a * (I • (γ a * γ b))) := by
  rw [Matrix.smul_mul, Matrix.mul_smul, ← smul_neg]
  congr 1
  calc γ a * γ b * γ a = γ a * (γ b * γ a) := Matrix.mul_assoc _ _ _
    _ = γ a * (-(γ a * γ b)) := by rw [γ_anticomm (Ne.symm hab)]
    _ = -(γ a * (γ a * γ b)) := by rw [Matrix.mul_neg]

/-- **`N = 1`: an operator on one system that commutes with every rotation of `Sp(2)` is a number.** -/
theorem commutant_one (X : Matrix Four Four ℂ)
    (hX : ∀ U : Matrix Four Four ℂ, U * Uᴴ = 1 → U * J * Uᵀ = J → X * U = U * X) :
    X = τ X • 1 := by
  have hγγ : ∀ a b : Fin 5, a ≠ b → X * (γ a * γ b) = (γ a * γ b) * X :=
    fun a b hab => hX _ (γγ_unitary hab) γγ_keeps_J
  -- `γ₀ = (γ₁γ₂)(γ₃γ₄)` and `γ_s = γ₀ (γ₀ γ_s)`
  have h0 : γ 0 = (γ 1 * γ 2) * (γ 3 * γ 4) := by
    have := γ_prod
    calc γ 0 = γ 0 * (γ 0 * γ 1 * γ 2 * γ 3 * γ 4) := by rw [this, Matrix.mul_one]
      _ = (γ 0 * γ 0) * (γ 1 * γ 2) * (γ 3 * γ 4) := by simp only [Matrix.mul_assoc]
      _ = (γ 1 * γ 2) * (γ 3 * γ 4) := by rw [γ_mul_self, Matrix.one_mul]
  have hc0 : X * γ 0 = γ 0 * X := by
    rw [h0, ← Matrix.mul_assoc, hγγ 1 2 (by decide), Matrix.mul_assoc, hγγ 3 4 (by decide),
      ← Matrix.mul_assoc]
  have hc : ∀ s : Fin 5, X * γ s = γ s * X := by
    intro s
    by_cases hs : s = 0
    · subst hs; exact hc0
    · have e : γ s = γ 0 * (γ 0 * γ s) := by rw [← Matrix.mul_assoc, γ_mul_self, Matrix.one_mul]
      rw [e, ← Matrix.mul_assoc, hc0, Matrix.mul_assoc, hγγ 0 s (Ne.symm hs), ← Matrix.mul_assoc]
  have hanti : ∀ k : Fin 16, k ≠ 0 → ∃ s : Fin 5, obs k * γ s = -(γ s * obs k) := by
    intro k hk
    fin_cases k
    · exact absurd rfl hk
    · exact ⟨1, γ_anticomm (s := 0) (t := 1) (by decide)⟩
    · exact ⟨0, γ_anticomm (s := 1) (t := 0) (by decide)⟩
    · exact ⟨0, γ_anticomm (s := 2) (t := 0) (by decide)⟩
    · exact ⟨0, γ_anticomm (s := 3) (t := 0) (by decide)⟩
    · exact ⟨0, γ_anticomm (s := 4) (t := 0) (by decide)⟩
    · exact ⟨0, plane_anti 0 1 (by decide)⟩
    · exact ⟨0, plane_anti 0 2 (by decide)⟩
    · exact ⟨0, plane_anti 0 3 (by decide)⟩
    · exact ⟨0, plane_anti 0 4 (by decide)⟩
    · exact ⟨1, plane_anti 1 2 (by decide)⟩
    · exact ⟨1, plane_anti 1 3 (by decide)⟩
    · exact ⟨1, plane_anti 1 4 (by decide)⟩
    · exact ⟨2, plane_anti 2 3 (by decide)⟩
    · exact ⟨2, plane_anti 2 4 (by decide)⟩
    · exact ⟨3, plane_anti 3 4 (by decide)⟩
  have hτ : ∀ k : Fin 16, k ≠ 0 → τ (X * obs k) = 0 := by
    intro k hk
    obtain ⟨s, hs⟩ := hanti k hk
    rw [τ, trace_mul_anticomm X (obs k) (γ s) (γ_mul_self s) (hc s) hs, zero_div]
  conv_lhs => rw [expand X]
  rw [Fin.sum_univ_succ, Finset.sum_eq_zero (fun k _ => by rw [hτ k.succ (Fin.succ_ne_zero k), zero_smul]),
    add_zero, show obs 0 = 1 from rfl, Matrix.mul_one]

end Comparison.Article
