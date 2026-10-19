module

public import Comparison.Elements.TwoThings
public import Comparison.Elements.Half
public import Comparison.Existence.Matter

/-!
# The whole picture, statements 1 to 4: the geometry of comparison

What already stands elsewhere in the project is cited;
this file holds what was missing for statements 1 to 4.

* **Statement 1.** `Eop_eq_pairing`: **`E = |J⟩⟨J|`**, the pairing vector being the join `J` read as
  a two-spinor state (`Jᵀ = −J` is `J_transpose`). `compOp X = X + Σ_t γ_t X γ_t`, the comparison acting on
  one system's operators: `L_on_operator`, **`L (X ⊗ 1)Ω = (L(X) ⊗ 1)Ω`**; `compOp_relOp`:
  `L(B_k) = (6 − 2|T_k|) B_k`; `compOp_one`, `compOp_line`, `compOp_plane`: **`L(I) = 6I`,
  `L(γ_a) = −2γ_a`, `L(γ_aγ_b) = 2γ_aγ_b`**: the eigenvectors `I`, `γ_a`, `γ_aγ_b`.
* **Statement 2.** `half_general`, `half_general_unitary`: for every Hermitian idempotent `P`,
  **`q = I − P + iP` has `q² = I − 2P = θ` and `q†q = I`**. `card_inter_add`, `description_sign`:
  **`i^{|S∩D|} i^{|T∩D|} = (−1)^{|S∩T∩D|} i^{|(S△T)∩D|}`** for all `D, S, T ⊆ Fin 6`;
  `description_carries_product`: in any algebra whose words multiply as `e_S e_T = c(S,T) e_{S△T}`,
  **`q_D(e_S) q_D(e_T) = (−1)^{|S∩T∩D|} q_D(e_S e_T)`** with `q_D(e_U) = i^{|U∩D|} e_U`.
* **Statement 3.** `hyper6_fifth`, `hyper_fifth`: **`Σ Y⁵ = 5/9`** over the sixteen, for every plane;
  `three_pairings`: **the four lines beside a last-step direction pair in exactly three ways**.
* **Statement 4.** The twelve rotations `gen12` of `s(u(2) ⊕ u(3))` (the plane's two lines `0, 1` and the
  three lines `2, 3, 4` outside it), orthonormal for `Re tr(X†Y)`: `gen12_antiHermitian`,
  `gen12_trace`, `gen12_block`, `gen12_orthonormal`. `lastDirectionGram i j = Re⟨X_i h, X_j h⟩` at the last-step direction
  `h = e₀`: `lastDirectionGram_eq` writes it as `TᵀT`, `lastDirectionImg_mul_transpose` gives
  `TTᵀ = diag(4/5, ½, ½, 0⁷)`, and `lastDirectionGram_charpoly`: **`det(X − G) = X⁹ (X − ½)² (X − 4/5)`**:
  nonzero eigenvalues `½, ½, 4/5` and nine zeros; `source_ratios`: `(½)/(4/5) = 5/8`,
  `1 − 5/8 = 3/8`.
-/

@[expose] public section

namespace Comparison.WholePicture

open Matrix hiding J
open Complex Kronecker Polynomial

/-! ## Statement 1 -/

/-- **`E = |J⟩⟨J|`:** the pairing is the rank-one form on the join `J` read as a two-spinor state. -/
theorem Eop_eq_pairing : Eop = vecMulVec (relOf J) (star (relOf J)) := by
  ext p q
  simp only [Eop, Ω, MΩ, relOf, Matrix.of_apply, vecMulVec_apply, Pi.star_apply,
    Matrix.smul_apply, smul_eq_mul, star_mul', star_neg, star_div₀, star_one, star_ofNat]
  ring

/-- The comparison acting on one system's operators: `L(X) = X + Σ_t γ_t X γ_t`. -/
noncomputable def compOp (X : Matrix Four Four ℂ) : Matrix Four Four ℂ := X + ∑ t, γ t * X * γ t

theorem relOf_sum {ι : Type*} (s : Finset ι) (M : ι → Matrix Four Four ℂ) :
    relOf (∑ i ∈ s, M i) = ∑ i ∈ s, relOf (M i) := by
  ext p
  simp [relOf, Matrix.sum_apply, Finset.sum_apply]

/-- **The comparison on the two-spinor state `(X ⊗ 1)Ω` is the comparison on the operator `X`.** -/
theorem L_on_operator (X : Matrix Four Four ℂ) :
    L *ᵥ ((X ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω) =
      (compOp X ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω := by
  rw [Ω, kron_mulVec_relOf, kron_mulVec_relOf, Matrix.transpose_one, Matrix.mul_one,
    Matrix.mul_one, L, Matrix.add_mulVec, one_kronecker_one, Matrix.one_mulVec, Matrix.sum_mulVec]
  simp only [kron_mulVec_relOf]
  have h : ∀ t : Fin 5, γ t * (X * MΩ) * (γ t)ᵀ = γ t * X * γ t * MΩ := by
    intro t
    simp only [Matrix.mul_assoc, MΩ_mul_γ_transpose]
  simp only [h, compOp, Matrix.add_mul, Finset.sum_mul, relOf_add, relOf_sum]

/-- `L(B_k) = (6 − 2|T_k|) B_k` on the sixteen operators of one system. -/
theorem compOp_relOp (k : Fin 16) :
    compOp (relOp k) = ((6 : ℂ) - 2 * (disagreeSet k).card) • relOp k := by
  rw [compOp]
  simp only [γ_conj_relOp]
  rw [← Finset.sum_smul, sum_sign]
  module

/-- **`L(I) = 6I`:** the singlet. -/
theorem compOp_one : compOp 1 = (6 : ℂ) • (1 : Matrix Four Four ℂ) := by
  have h := compOp_relOp 0
  simpa [relOp, disagreeSet] using h

/-- **`L(γ_a) = −2γ_a`:** the five directions. -/
theorem compOp_line (a : Fin 5) : compOp (γ a) = (-2 : ℂ) • γ a := by
  rw [compOp]
  have hc : ∀ t : Fin 5, γ t * γ a * γ t =
      (if t ∈ Finset.univ.erase a then -1 else 1 : ℂ) • γ a := by
    intro t
    by_cases ht : t = a
    · subst ht
      simp [γ_mul_self]
    · have hm : t ∈ Finset.univ.erase a := Finset.mem_erase.mpr ⟨ht, Finset.mem_univ _⟩
      rw [γ_conj_line_ne ht]
      simp [hm]
  simp only [hc]
  rw [← Finset.sum_smul, sum_sign, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
    Fintype.card_fin]
  norm_num
  module

/-- **`L(γ_aγ_b) = 2γ_aγ_b`** for `a ≠ b`: the ten symmetric states. -/
theorem compOp_plane {a b : Fin 5} (hab : a ≠ b) : compOp (γ a * γ b) = (2 : ℂ) • (γ a * γ b) := by
  rw [compOp]
  have hc : ∀ t : Fin 5, γ t * (γ a * γ b) * γ t =
      (if t ∈ ({a, b} : Finset (Fin 5)) then -1 else 1 : ℂ) • (γ a * γ b) := by
    intro t
    by_cases ha : t = a
    · subst ha
      rw [γ_conj_plane_left hab]
      simp
    · by_cases hb : t = b
      · subst hb
        rw [γ_conj_plane_right hab]
        simp
      · have hm : t ∉ ({a, b} : Finset (Fin 5)) := by simp [ha, hb]
        rw [γ_conj_plane_out ha hb]
        simp [hm]
  simp only [hc]
  rw [← Finset.sum_smul, sum_sign, Finset.card_pair hab]
  norm_num
  module

/-! ## Statement 2 -/

/-- **The half of a distinction:** for every idempotent `P`, `q = I − P + iP` has
`q² = I − 2P = θ`. -/
theorem half_general {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ) (hP : P * P = P) :
    (1 - P + I • P) * (1 - P + I • P) = 1 - (2 : ℂ) • P := by
  have e : (1 - P + I • P) = 1 + (I - 1) • P := by module
  have h1 : (1 + (I - 1) • P) * (1 + (I - 1) • P) =
      1 + (2 * (I - 1) + (I - 1) * (I - 1)) • P := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, hP]
    module
  have h2 : 2 * (I - 1) + (I - 1) * (I - 1) = (-2 : ℂ) := by linear_combination I_sq
  rw [e, h1, h2]
  module

/-- **The half is unitary:** for a Hermitian idempotent `P`, `q†q = I`. -/
theorem half_general_unitary {n : Type*} [Fintype n] [DecidableEq n] (P : Matrix n n ℂ)
    (hP : P * P = P) (hH : Pᴴ = P) :
    (1 - P + I • P)ᴴ * (1 - P + I • P) = 1 := by
  have e : (1 - P + I • P) = 1 + (I - 1) • P := by module
  have hs : star (I - 1) = -I - 1 := by simp [Complex.conj_I]
  have e' : (1 - P + I • P)ᴴ = 1 + (-I - 1) • P := by
    rw [e, Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_smul, hH, hs]
  have h1 : (1 + (-I - 1) • P) * (1 + (I - 1) • P) =
      1 + ((-I - 1) + (I - 1) + (-I - 1) * (I - 1)) • P := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, hP]
    module
  have h2 : (-I - 1) + (I - 1) + (-I - 1) * (I - 1) = (0 : ℂ) := by
    linear_combination (-1 : ℂ) * I_sq
  rw [e', e, h1, h2, zero_smul, add_zero]

theorem card_inter_eq_sum (X D : Finset (Fin 6)) :
    (X ∩ D).card = ∑ x ∈ D, if x ∈ X then 1 else 0 := by
  rw [Finset.sum_boole, Nat.cast_id, Finset.filter_mem_eq_inter, Finset.inter_comm]

/-- `|S ∩ D| + |T ∩ D| = |(S △ T) ∩ D| + 2|S ∩ T ∩ D|`. -/
theorem card_inter_add (D S T : Finset (Fin 6)) :
    (S ∩ D).card + (T ∩ D).card = ((symmDiff S T) ∩ D).card + 2 * (S ∩ T ∩ D).card := by
  rw [card_inter_eq_sum S D, card_inter_eq_sum T D, card_inter_eq_sum (symmDiff S T) D,
    card_inter_eq_sum (S ∩ T) D, ← Finset.sum_add_distrib, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hS : x ∈ S <;> by_cases hT : x ∈ T <;> simp [hS, hT, Finset.mem_symmDiff]

/-- **A description carries its algebra**, the scalar form:
`i^{|S∩D|} i^{|T∩D|} = (−1)^{|S∩T∩D|} i^{|(S△T)∩D|}` for every division `D` and all words `S, T`. -/
theorem description_sign (D S T : Finset (Fin 6)) :
    I ^ (S ∩ D).card * I ^ (T ∩ D).card =
      (-1) ^ (S ∩ T ∩ D).card * I ^ ((symmDiff S T) ∩ D).card := by
  rw [← pow_add, card_inter_add, pow_add, pow_mul, I_sq]
  ring

/-- **A description carries its algebra:** in any complex algebra whose words multiply as
`e_S e_T = c(S, T) e_{S△T}` (the Clifford algebra of the six is one), the square root of the sign of a division,
`q_D(e_U) = i^{|U∩D|} e_U`, changes the product of two words by the sign of their common part
inside the division: `q_D(e_S) q_D(e_T) = (−1)^{|S∩T∩D|} q_D(e_S e_T)`, where
`q_D(e_S e_T) = c(S, T) i^{|(S△T)∩D|} e_{S△T}`. -/
theorem description_carries_product {A : Type*} [Ring A] [Algebra ℂ A]
    (e : Finset (Fin 6) → A) (c : Finset (Fin 6) → Finset (Fin 6) → ℂ)
    (he : ∀ S T, e S * e T = c S T • e (symmDiff S T)) (D S T : Finset (Fin 6)) :
    (I ^ (S ∩ D).card • e S) * (I ^ (T ∩ D).card • e T) =
      ((-1 : ℂ) ^ (S ∩ T ∩ D).card) •
        ((c S T * I ^ ((symmDiff S T) ∩ D).card) • e (symmDiff S T)) := by
  rw [smul_mul_smul_comm, he, smul_smul, smul_smul, description_sign]
  congr 1
  ring

/-! ## Statement 3 -/

theorem hyper6_fifth : ∀ h k : Fin 5, h ≠ k → ∑ r, hyper6 h k r ^ 5 = 4320 := by
  decide +kernel

/-- **`Σ Y⁵ = 5/9`** over the sixteen two-spinor states of one generation, for every plane. -/
theorem hyper_fifth (h k : Fin 5) (hk : h ≠ k) : ∑ r, hyper h k r ^ 5 = 5 / 9 := by
  simp only [hyper_eq, div_pow, ← Finset.sum_div]
  simp only [← Int.cast_pow, ← Int.cast_sum, hyper6_fifth h k hk]
  norm_num

/-- The ways to split the four lines beside the last-step direction `h` into two pairs. -/
def pairingsBeside (h : Fin 5) : Finset (Finset (Finset (Fin 5))) :=
  ((Finset.univ.erase h).powersetCard 2).image fun P => {P, (Finset.univ.erase h) \ P}

/-- **Three families:** the four lines beside a last-step direction pair in exactly three ways. -/
theorem three_pairings : ∀ h : Fin 5, (pairingsBeside h).card = 3 := by
  decide

/-! ## Statement 4: the last-step direction's Gram on `s(u(2) ⊕ u(3))` -/

/-- The integer real parts of the twelve rotations before normalization: `E_ab − E_ba` for the pairs
`(0,1)`, `(2,3)`, `(2,4)`, `(3,4)` at the odd vertices `1, 3, 5, 7`. -/
def genRe : Fin 12 → Fin 5 → Fin 5 → ℤ :=
  ![(0 : Fin 5 → Fin 5 → ℤ),
    !![0, 1, 0, 0, 0; -1, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0],
    0, !![0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, -1, 0, 0; 0, 0, 0, 0, 0],
    0, !![0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, 0, 0; 0, 0, -1, 0, 0],
    0, !![0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, -1, 0],
    0, 0, 0, 0]

/-- The integer imaginary parts of the twelve rotations before normalization: `E_ab + E_ba` for the same
pairs at the even vertices `0, 2, 4, 6`, then `diag(1, −1, 0, 0, 0)`, `diag(0, 0, 1, −1, 0)`,
`diag(0, 0, 1, 1, −2)` and the hypercharge `diag(3, 3, −2, −2, −2)`. -/
def genIm : Fin 12 → Fin 5 → Fin 5 → ℤ :=
  ![!![0, 1, 0, 0, 0; 1, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0], 0,
    !![0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 1, 0; 0, 0, 1, 0, 0; 0, 0, 0, 0, 0], 0,
    !![0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, 0, 0; 0, 0, 1, 0, 0], 0,
    !![0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 1; 0, 0, 0, 1, 0], 0,
    !![1, 0, 0, 0, 0; 0, -1, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, -1, 0; 0, 0, 0, 0, 0],
    !![0, 0, 0, 0, 0; 0, 0, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, -2],
    !![3, 0, 0, 0, 0; 0, 3, 0, 0, 0; 0, 0, -2, 0, 0; 0, 0, 0, -2, 0; 0, 0, 0, 0, -2]]

/-- The squared Frobenius length of each unnormalized rotation. -/
def genNorm : Fin 12 → ℕ := ![2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 6, 30]

/-- **The twelve rotations**, normalized: `X_j = (genRe_j + i genIm_j)/√n_j`. -/
noncomputable def gen12 (j : Fin 12) : Matrix (Fin 5) (Fin 5) ℂ :=
  (((Real.sqrt (genNorm j))⁻¹ : ℝ) : ℂ) •
    Matrix.of fun a b => ((genRe j a b : ℂ) + I * (genIm j a b : ℂ))

theorem genRe_antisymm : ∀ (j : Fin 12) (a b : Fin 5), genRe j b a = -genRe j a b := by decide
theorem genIm_symm : ∀ (j : Fin 12) (a b : Fin 5), genIm j b a = genIm j a b := by decide
theorem genRe_trace : ∀ j : Fin 12, ∑ a, genRe j a a = 0 := by decide
theorem genIm_trace : ∀ j : Fin 12, ∑ a, genIm j a a = 0 := by decide

/-- The block of a line: `true` on the plane `{0, 1}`, `false` on the three lines outside. -/
def inPlane (a : Fin 5) : Bool := decide (a.val < 2)

/-- The rotations keep the split of the five directions into the plane `{0, 1}` and the three lines outside.
-/
theorem gen_block : ∀ (j : Fin 12) (a b : Fin 5), inPlane a ≠ inPlane b →
    genRe j a b = 0 ∧ genIm j a b = 0 := by decide

/-- The unnormalized rotations are orthogonal with the lengths `n_j`. -/
theorem gen_gram_int : ∀ i j : Fin 12,
    ∑ a : Fin 5, ∑ b : Fin 5, (genRe i a b * genRe j a b + genIm i a b * genIm j a b) =
      if i = j then (genNorm i : ℤ) else 0 := by decide +kernel

theorem genNorm_pos (j : Fin 12) : (0 : ℝ) < genNorm j := by
  fin_cases j <;> simp [genNorm]

theorem gen12_apply (j : Fin 12) (a b : Fin 5) :
    gen12 j a b = (((Real.sqrt (genNorm j))⁻¹ : ℝ) : ℂ) *
      ((genRe j a b : ℂ) + I * (genIm j a b : ℂ)) := by
  simp only [gen12, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]

theorem gen12_re (j : Fin 12) (a b : Fin 5) :
    (gen12 j a b).re = (Real.sqrt (genNorm j))⁻¹ * genRe j a b := by
  rw [gen12_apply]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
    Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im, Complex.mul_im]
  ring

theorem gen12_im (j : Fin 12) (a b : Fin 5) :
    (gen12 j a b).im = (Real.sqrt (genNorm j))⁻¹ * genIm j a b := by
  rw [gen12_apply]
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.add_im,
    Complex.I_re, Complex.I_im, Complex.intCast_re, Complex.intCast_im, Complex.mul_re]
  ring

/-- **The twelve are rotations:** `X_j† = −X_j`. -/
theorem gen12_antiHermitian (j : Fin 12) : (gen12 j)ᴴ = -gen12 j := by
  ext a b
  have hr := genRe_antisymm j a b
  have hi := genIm_symm j a b
  apply Complex.ext
  · simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Complex.star_def, Complex.conj_re,
      Complex.neg_re, gen12_re, hr]
    push_cast
    ring
  · simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, Complex.star_def, Complex.conj_im,
      Complex.neg_im, gen12_im, hi]

/-- The twelve have trace zero. -/
theorem gen12_trace (j : Fin 12) : (gen12 j).trace = 0 := by
  have hr := genRe_trace j
  have hi := genIm_trace j
  simp only [Matrix.trace, Matrix.diag]
  simp only [gen12_apply, ← Finset.mul_sum, Finset.sum_add_distrib]
  rw [← Int.cast_sum, ← Int.cast_sum, hr, hi]
  simp

/-- The twelve keep the split `2 + 3`: no entry joins the plane to the outside lines. -/
theorem gen12_block (j : Fin 12) (a b : Fin 5) (h : inPlane a ≠ inPlane b) :
    gen12 j a b = 0 := by
  rw [gen12_apply, (gen_block j a b h).1, (gen_block j a b h).2]
  simp

theorem sqrt_inv_mul_self (n : ℝ) (hn : 0 ≤ n) : (Real.sqrt n)⁻¹ * (Real.sqrt n)⁻¹ = n⁻¹ := by
  rw [← mul_inv, Real.mul_self_sqrt hn]

/-- **The twelve are orthonormal** for `⟨X, Y⟩ = Re tr(X†Y)`. -/
theorem gen12_orthonormal (i j : Fin 12) :
    ((gen12 i)ᴴ * gen12 j).trace.re = if i = j then 1 else 0 := by
  have hsum : ((gen12 i)ᴴ * gen12 j).trace.re =
      (Real.sqrt (genNorm i))⁻¹ * (Real.sqrt (genNorm j))⁻¹ *
        ∑ a : Fin 5, ∑ b : Fin 5,
          ((genRe i a b * genRe j a b + genIm i a b * genIm j a b : ℤ) : ℝ) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Complex.re_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, gen12_re,
      gen12_im]
    push_cast
    ring
  rw [hsum]
  simp only [← Int.cast_sum, gen_gram_int]
  split_ifs with h
  · subst h
    have hp := genNorm_pos i
    push_cast
    rw [sqrt_inv_mul_self _ hp.le]
    field_simp
  · simp

/-- The last-step direction `h = e₀`. -/
def lastDirectionE : Fin 5 → ℂ := Pi.single 0 1

/-- **The last-step direction's Gram** `G_ij = Re⟨X_i h, X_j h⟩`. -/
noncomputable def lastDirectionGram : Matrix (Fin 12) (Fin 12) ℝ :=
  Matrix.of fun i j => (star (gen12 i *ᵥ lastDirectionE) ⬝ᵥ (gen12 j *ᵥ lastDirectionE)).re

/-- The last-step direction's column of each unnormalized rotation, as a real vector: `(Re, Im)` of `X_j e₀`. -/
def colZ (j : Fin 12) (p : Fin 5 × Fin 2) : ℤ := if p.2 = 0 then genRe j p.1 0 else genIm j p.1 0

/-- The last-step direction's images as real vectors: `T_{p, j} = colZ j p / √n_j`. -/
noncomputable def lastDirectionImg : Matrix (Fin 5 × Fin 2) (Fin 12) ℝ :=
  Matrix.of fun p j => (Real.sqrt (genNorm j))⁻¹ * colZ j p

theorem gen12_mulVec_lastDirectionE (j : Fin 12) (a : Fin 5) : (gen12 j *ᵥ lastDirectionE) a = gen12 j a 0 := by
  simp [lastDirectionE, Matrix.mulVec, dotProduct, Pi.single_apply]

/-- **`G = TᵀT`.** -/
theorem lastDirectionGram_eq : lastDirectionGram = lastDirectionImgᵀ * lastDirectionImg := by
  ext i j
  simp only [lastDirectionGram, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, lastDirectionImg,
    dotProduct, Pi.star_apply, gen12_mulVec_lastDirectionE, Complex.re_sum, Fintype.sum_prod_type,
    Fin.sum_univ_two, colZ]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im, gen12_re,
    gen12_im]
  simp

/-- `30/n_j`. -/
def genW : Fin 12 → ℤ := ![15, 15, 15, 15, 15, 15, 15, 15, 15, 15, 5, 1]

theorem genW_eq (j : Fin 12) : (genW j : ℝ) / 30 = ((genNorm j : ℝ))⁻¹ := by
  fin_cases j <;> norm_num [genW, genNorm]

/-- Thirty times the diagonal of `TTᵀ`: `24` on `Im e₀`, `15` on `Re e₁` and on `Im e₁`. -/
def lastDirectionDiagZ : Fin 5 × Fin 2 → ℤ := fun p =>
  if p = (0, 1) then 24 else if p = (1, 0) ∨ p = (1, 1) then 15 else 0

theorem lastDirection_column_sum : ∀ x y : Fin 5 × Fin 2,
    ∑ j : Fin 12, genW j * colZ j x * colZ j y = if x = y then lastDirectionDiagZ x else 0 := by
  decide +kernel

/-- The diagonal of `TTᵀ`. -/
noncomputable def lastDirectionDiag : Fin 5 × Fin 2 → ℝ := fun p => (lastDirectionDiagZ p : ℝ) / 30

/-- **`TTᵀ = diag(4/5, ½, ½, 0, …, 0)`.** -/
theorem lastDirectionImg_mul_transpose : lastDirectionImg * lastDirectionImgᵀ = Matrix.diagonal lastDirectionDiag := by
  ext x y
  have hR : ∀ j : Fin 12, lastDirectionImg x j * lastDirectionImg y j =
      ((genW j * colZ j x * colZ j y : ℤ) : ℝ) / 30 := by
    intro j
    simp only [lastDirectionImg, Matrix.of_apply]
    have hp := genNorm_pos j
    have hw := genW_eq j
    push_cast
    calc (Real.sqrt (genNorm j))⁻¹ * (colZ j x : ℝ) * ((Real.sqrt (genNorm j))⁻¹ * (colZ j y : ℝ))
        = ((Real.sqrt (genNorm j))⁻¹ * (Real.sqrt (genNorm j))⁻¹) * (colZ j x * colZ j y) := by ring
      _ = ((genNorm j : ℝ))⁻¹ * (colZ j x * colZ j y) := by rw [sqrt_inv_mul_self _ hp.le]
      _ = (genW j : ℝ) * colZ j x * colZ j y / 30 := by rw [← hw]; ring
  simp only [Matrix.mul_apply, Matrix.transpose_apply, hR, ← Finset.sum_div, ← Int.cast_sum,
    lastDirection_column_sum, Matrix.diagonal_apply, lastDirectionDiag]
  split_ifs <;> simp

theorem prod_lastDirectionDiag :
    ∏ p : Fin 5 × Fin 2, (X - C (lastDirectionDiag p)) =
      X ^ 7 * (X - C (1 / 2 : ℝ)) ^ 2 * (X - C (4 / 5 : ℝ)) := by
  simp only [Fintype.prod_prod_type, Fin.prod_univ_succ, Fin.prod_univ_zero, lastDirectionDiag, lastDirectionDiagZ]
  norm_num
  ring

/-- **The last-step direction's Gram on `s(u(2) ⊕ u(3))`:** `det(X − G) = X⁹ (X − ½)² (X − 4/5)`: the nonzero
eigenvalues `½, ½, 4/5` (`W⁺, W⁻, Z`) and nine zeros (the photon and the eight colour rotations). -/
theorem lastDirectionGram_charpoly :
    lastDirectionGram.charpoly = X ^ 9 * (X - C (1 / 2 : ℝ)) ^ 2 * (X - C (4 / 5 : ℝ)) := by
  have h := Matrix.charpoly_mul_comm' lastDirectionImgᵀ lastDirectionImg
  rw [← lastDirectionGram_eq, lastDirectionImg_mul_transpose, Matrix.charpoly_diagonal, prod_lastDirectionDiag] at h
  simp only [Fintype.card_prod, Fintype.card_fin] at h
  have hX : (X : ℝ[X]) ^ 10 ≠ 0 := pow_ne_zero _ X_ne_zero
  apply mul_left_cancel₀ hX
  rw [h]
  ring

/-- At the source `M_W²/M_Z² = (½)/(4/5) = 5/8` and `sin²θ = 1 − 5/8 = 3/8`. -/
theorem source_ratios : (1 / 2 : ℝ) / (4 / 5) = 5 / 8 ∧ 1 - (1 / 2 : ℝ) / (4 / 5) = 3 / 8 := by
  constructor <;> norm_num

end Comparison.WholePicture

end
