import Comparison.WholePicture.TheLaw

/-!
# The comparison is the propagation kernel (Prop. S54a; formulas (10) to (13), (17))

Proposition S54a. `Hp` has the sixteen paired vectors `rel k = (B_k ⊗ 1)Ω` as
its columns (`B_k = 1, γ_t, γ_sγ_t`, equal to the ordered product `γ_S` of the lines of
`S = disagreeSet k` up to a sign), `Wc = W` the characters `W_{xS} = (1/4)(−1)^{|x ∩ S|}`, and
`Tk = T = H Wᵀ`.

* `Hp_unitary`, `Hp_L`: `H†H = 1`, `H†LH = diag(6 − 2|S|)`; `Wc_apply`, `Wc_orth`: `W` is orthogonal;
  `A_eq`: `A = W diag(5 − 2|S|) Wᵀ`.
* `Tk_unitary`, `Tk_kernel`: **`T†T = I` and `T†(6I − L)T = 5I − A`**: the disagreement is the transitions'
  operator.
* `det_conj_rect`: `det(T†MT) = det(T†T) det M` for `T` with as many rows as columns.
* `det_gap`: `det[(6I − L) + cI] = c(c + 4)¹⁰(c + 8)⁵`; `law_gap`:
  **`det(I − uB) = (1 − u²)²⁴ u¹⁶ det[(6I − L) + χ(u)I]`**, `χ(u) = 1/u + 4u − 5` (`chi_eq`:
  `= (1 − u)(1 − 4u)/u`); `law_bass_form`: `det(I − uB) = (1 − u²)²⁴ det[(1 + 4u²)I − uA]`.
* `kN_gap`: **`k_N(u) = u(2N + χ(u))`**; `chi_quarters`: **`χ(i^k/4) = 0, −5 − 3i, −10, −5 + 3i`**;
  `kN_plane_gap`: `k_N(−1/4) = (5 − N)/2`; `transmission_echo`: `t, e, t_ℓ, e_ℓ = 2/5, 3/5, 2/3, 1/3`.
* `kappa_gap`: **`κ = 2w⁴/(1 − 5w²)² = 2/[(χ + 5)² − 5]²`, `w = u/(1 + 4u²) = 1/(χ + 5)`**;
  `kappa_gap_values`: `1/200` at `χ = 0, −10` and `1/98` at `χ = −5 ± 3i`.
* `own_transformation`: **`K₁₆(v)/v = K₁₆(u)/u + [χ(v) − χ(u)]I`** for every operator `A`.
-/

namespace Comparison.Formulas

open Matrix Complex

/-! ## A determinant through a rectangular unitary -/

/-- `det(T†MT) = det(T†T) det M` when `T` has as many rows as columns. -/
theorem det_conj_rect {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (e : n ≃ m) (T : Matrix m n ℂ) (M : Matrix m m ℂ) :
    (Tᴴ * M * T).det = (Tᴴ * T).det * M.det := by
  set S : Matrix m m ℂ := T.submatrix id e.symm with hS
  have h1 : Tᴴ * M * T = (Sᴴ * M * S).submatrix e e := by
    ext i j
    simp [hS, Matrix.mul_apply, Matrix.conjTranspose_apply]
  have h2 : Tᴴ * T = (Sᴴ * S).submatrix e e := by
    ext i j
    simp [hS, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [h1, h2, Matrix.det_submatrix_equiv_self, Matrix.det_submatrix_equiv_self, det_mul, det_mul,
    det_mul]
  ring

/-! ## The paired vectors, the characters and `T = H Wᵀ` -/

/-- The paired vectors as the columns of `H`. -/
noncomputable def Hp : Matrix Two (Fin 16) ℂ := Matrix.of fun p k => rel k p

/-- The characters `W_{xS} = (1/4)(−1)^{|x ∩ S|}`. -/
noncomputable def Wc : Matrix (Fin 16) (Fin 16) ℂ := (1 / 4 : ℂ) • charTableC

/-- `T = H Wᵀ`. -/
noncomputable def Tk : Matrix Two (Fin 16) ℂ := Hp * Wcᵀ

/-- The transitions' operator `A` on the sixteen two-spinor states. -/
noncomputable def A16 : Matrix (Fin 16) (Fin 16) ℂ := ∑ t, transitionMat t

theorem Wc_apply (x S : Fin 16) :
    Wc x S = (1 / 4 : ℂ) * (-1) ^ (disagreeSet x ∩ disagreeSet S).card := by
  rw [Wc, Matrix.smul_apply, charTableC, Matrix.map_apply, charTable_eq]
  simp

theorem charTable_symm : charTableᵀ = charTable := by
  rw [charTable_eq]
  ext i j
  simp [Finset.inter_comm]

theorem Wc_transpose : Wcᵀ = Wc := by
  rw [Wc, Matrix.transpose_smul, charTableC, ← Matrix.transpose_map, charTable_symm]

theorem Wc_conjTranspose : Wcᴴ = Wc := by
  ext i j
  rw [Matrix.conjTranspose_apply, Wc_apply, Wc_apply, Finset.inter_comm]
  simp

theorem Wc_orth : Wc * Wc = 1 := by
  rw [Wc, smul_mul_smul_comm, charTableC_mul_self, smul_smul]
  norm_num

theorem Hp_unitary : Hpᴴ * Hp = 1 := by
  ext k l
  have h := rel_inner k l
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Hp, Matrix.of_apply, Matrix.one_apply]
  rw [← h]
  rfl

theorem Hp_L : Hpᴴ * L * Hp = Matrix.diagonal fun k => ((Lvalue k : ℤ) : ℂ) := by
  ext k l
  have h : star (rel k) ⬝ᵥ (L *ᵥ rel l) =
      Matrix.diagonal (fun k => ((Lvalue k : ℤ) : ℂ)) k l := by
    rw [L_rel', dotProduct_smul, rel_inner, Matrix.diagonal_apply]
    by_cases hkl : k = l
    · subst hkl
      simp
    · simp [hkl]
  rw [← h]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Hp, Matrix.of_apply, dotProduct,
    Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  simp only [Pi.star_apply]
  ring

/-- **`A = W diag(5 − 2|S|) Wᵀ`.** -/
theorem A_eq : A16 = Wc * Matrix.diagonal (fun l => ((charValue l : ℤ) : ℂ)) * Wc := by
  have h := adjacency_mul_charTable_C
  have hC : charTableC * charTableC = (16 : ℂ) • 1 := charTableC_mul_self
  have e : A16 = (1 / 16 : ℂ) • ((A16 * charTableC) * charTableC) := by
    rw [Matrix.mul_assoc, hC, Matrix.mul_smul, Matrix.mul_one, smul_smul]
    norm_num
  rw [e, A16, h, Wc]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  norm_num

/-- **`T` is unitary.** -/
theorem Tk_unitary : Tkᴴ * Tk = 1 := by
  rw [Tk, Matrix.conjTranspose_mul, Wc_transpose, Wc_conjTranspose, Matrix.mul_assoc,
    ← Matrix.mul_assoc Hpᴴ, Hp_unitary, Matrix.one_mul, Wc_orth]

/-- **The disagreement is the transitions' operator:** `T†(6I − L)T = 5I − A`. -/
theorem Tk_kernel : Tkᴴ * disagreement * Tk = (5 : ℂ) • 1 - A16 := by
  have hD : Hpᴴ * disagreement * Hp =
      Matrix.diagonal fun k => (6 : ℂ) - ((Lvalue k : ℤ) : ℂ) := by
    rw [disagreement, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one,
      Matrix.smul_mul, Hp_unitary, Hp_L]
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply,
      smul_eq_mul]
    split_ifs <;> ring
  have h5 : (5 : ℂ) • (1 : Matrix (Fin 16) (Fin 16) ℂ) - A16 =
      Wc * (Matrix.diagonal fun k => (6 : ℂ) - ((Lvalue k : ℤ) : ℂ)) * Wc := by
    have hsplit : (Matrix.diagonal fun k => (6 : ℂ) - ((Lvalue k : ℤ) : ℂ)) =
        (5 : ℂ) • 1 - Matrix.diagonal (fun l => ((charValue l : ℤ) : ℂ)) := by
      ext i j
      simp only [Matrix.diagonal_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
        smul_eq_mul, charValue_eq_L]
      split_ifs <;> push_cast <;> ring
    rw [hsplit, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Wc_orth, A_eq]
  have e : Tkᴴ * disagreement * Tk = Wc * (Hpᴴ * disagreement * Hp) * Wc := by
    rw [Tk, Matrix.conjTranspose_mul, Wc_transpose, Wc_conjTranspose,
      Matrix.mul_assoc Wc Hpᴴ disagreement, Matrix.mul_assoc Wc (Hpᴴ * disagreement) (Hp * Wc),
      ← Matrix.mul_assoc (Hpᴴ * disagreement) Hp Wc, ← Matrix.mul_assoc Wc]
  rw [e, hD, h5]

/-! ## The law as the comparison with one movable gap -/

/-- **The gap** `χ(u) = 1/u + 4u − 5`. -/
noncomputable def chi (u : ℂ) : ℂ := 1 / u + 4 * u - 5

theorem chi_eq (u : ℂ) (hu : u ≠ 0) : chi u = (1 - u) * (1 - 4 * u) / u := by
  rw [chi]
  field_simp
  ring

theorem two_card : Fintype.card Two = Fintype.card (Fin 16) := by simp

/-- **`det[(6I − L) + cI] = c(c + 4)¹⁰(c + 8)⁵`.** -/
theorem det_gap (c : ℂ) : (disagreement + c • 1).det = c * (c + 4) ^ 10 * (c + 8) ^ 5 := by
  obtain ⟨e⟩ : Nonempty (Fin 16 ≃ Two) := Fintype.card_eq.mp two_card.symm
  have h := det_conj_rect e Tk (disagreement + c • 1)
  rw [Tk_unitary, det_one, one_mul, Matrix.mul_add, Matrix.add_mul, Tk_kernel, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.mul_one, Tk_unitary] at h
  rw [← h]
  have e2 : (5 : ℂ) • (1 : Matrix (Fin 16) (Fin 16) ℂ) - A16 + c • 1 =
      (5 + c) • (1 : Matrix (Fin 16) (Fin 16) ℂ) - (1 : ℂ) • A16 := by
    rw [one_smul, add_smul]
    abel
  rw [e2, A16, det_of_diag _ _ adjacency_mul_charTable_C]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, charValue]
  simp [disagreeSet]
  ring

/-- **The Bass form:** `det(I − uB) = (1 − u²)²⁴ det[(1 + 4u²)I − uA]`. -/
theorem law_bass_form (u : ℂ) :
    (1 - u • stepOp transitionMat).det =
      (1 - u ^ 2) ^ 24 * ((1 + 4 * u ^ 2) • (1 : Matrix (Fin 16) (Fin 16) ℂ) - u • A16).det := by
  rw [D_plus, A16, det_vertex_plus]
  ring

/-- **The law is the comparison with one movable gap:**
`det(I − uB) = (1 − u²)²⁴ u¹⁶ det[(6I − L) + χ(u)I]`. -/
theorem law_gap (u : ℂ) (hu : u ≠ 0) :
    (1 - u • stepOp transitionMat).det = (1 - u ^ 2) ^ 24 * u ^ 16 * (disagreement + chi u • 1).det := by
  rw [D_plus, det_gap]
  have h0 : u * chi u = (1 - u) * (1 - 4 * u) := by
    rw [chi]
    field_simp
    ring
  have h4 : u * (chi u + 4) = 1 - u + 4 * u ^ 2 := by
    rw [chi]
    field_simp
    ring
  have h8 : u * (chi u + 8) = 1 + 3 * u + 4 * u ^ 2 := by
    rw [chi]
    field_simp
    ring
  have e : u ^ 16 * (chi u * (chi u + 4) ^ 10 * (chi u + 8) ^ 5) =
      (u * chi u) * (u * (chi u + 4)) ^ 10 * (u * (chi u + 8)) ^ 5 := by ring
  have key : u ^ 16 * (chi u * (chi u + 4) ^ 10 * (chi u + 8) ^ 5) =
      (1 - u) * (1 - 4 * u) * (1 - u + 4 * u ^ 2) ^ 10 * (1 + 3 * u + 4 * u ^ 2) ^ 5 := by
    rw [e, h0, h4, h8]
  calc (1 - u ^ 2) ^ 24 * (1 - u) * (1 - 4 * u) * (1 - u + 4 * u ^ 2) ^ 10 *
        (1 + 3 * u + 4 * u ^ 2) ^ 5
      = (1 - u ^ 2) ^ 24 * ((1 - u) * (1 - 4 * u) * (1 - u + 4 * u ^ 2) ^ 10 *
          (1 + 3 * u + 4 * u ^ 2) ^ 5) := by ring
    _ = (1 - u ^ 2) ^ 24 * (u ^ 16 * (chi u * (chi u + 4) ^ 10 * (chi u + 8) ^ 5)) := by
          rw [key]
    _ = _ := by ring

/-- **The grade factors read the gap:** `k_N(u) = u(2N + χ(u))`. -/
theorem kN_gap (N u : ℂ) (hu : u ≠ 0) : WholePicture.kN N u = u * (2 * N + chi u) := by
  rw [WholePicture.kN, chi]
  field_simp
  ring

/-- **The gap at the four points `u = i^d/4`:** `χ(i^k/4) = 0, −5 − 3i, −10, −5 + 3i`. -/
theorem chi_quarters :
    chi (1 / 4) = 0 ∧ chi (I / 4) = -5 - 3 * I ∧ chi (-1 / 4) = -10 ∧ chi (-I / 4) = -5 + 3 * I := by
  have hI : (I / 4)⁻¹ = -4 * I := by
    rw [inv_div, div_eq_mul_inv, Complex.inv_I]
    ring
  have hI' : (-I / 4)⁻¹ = 4 * I := by
    rw [inv_div, div_eq_mul_inv, inv_neg, Complex.inv_I]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [chi]
    norm_num
  · rw [chi, one_div, hI]
    ring
  · rw [chi]
    norm_num
  · rw [chi, one_div, hI']
    ring

/-- At the point `u = −1/4`, `χ = −10` and `k_N(−1/4) = (5 − N)/2`. -/
theorem kN_plane_gap (N : ℂ) :
    chi (-1 / 4) = -10 ∧ WholePicture.kN N (-1 / 4) = (-1 / 4) * (2 * N + chi (-1 / 4)) ∧
      WholePicture.kN N (-1 / 4) = (5 - N) / 2 := by
  refine ⟨chi_quarters.2.2.1, kN_gap N _ (by norm_num), ?_⟩
  rw [WholePicture.kN]
  ring

/-- **The transmission and the reflection at a plane and at a line:** `t = 1/k₀ = 2/5`, `e = k₂/k₀ = 3/5`,
`t_ℓ = 1/k₂ = 2/3`, `e_ℓ = k₄/k₂ = 1/3`, all at `u = −1/4`. -/
theorem transmission_echo :
    1 / WholePicture.kR 0 (-1 / 4) = 2 / 5 ∧
      WholePicture.kR 2 (-1 / 4) / WholePicture.kR 0 (-1 / 4) = 3 / 5 ∧
      1 / WholePicture.kR 2 (-1 / 4) = 2 / 3 ∧
      WholePicture.kR 4 (-1 / 4) / WholePicture.kR 2 (-1 / 4) = 1 / 3 := by
  simp only [WholePicture.kR]
  norm_num

/-! ## The stiffness and the law's own transformation as functions of the gap -/

/-- **`κ = 2w⁴/(1 − 5w²)² = 2/[(χ + 5)² − 5]²` with `w = u/(1 + 4u²) = 1/(χ + 5)`.** -/
theorem kappa_gap (u : ℂ) (hu : u ≠ 0) (h4 : 1 + 4 * u ^ 2 ≠ 0) :
    (u / (1 + 4 * u ^ 2))⁻¹ = chi u + 5 ∧
      2 * (u / (1 + 4 * u ^ 2)) ^ 4 / (1 - 5 * (u / (1 + 4 * u ^ 2)) ^ 2) ^ 2 =
        2 / ((chi u + 5) ^ 2 - 5) ^ 2 := by
  have hw : (u / (1 + 4 * u ^ 2))⁻¹ = chi u + 5 := by
    rw [inv_div, chi]
    field_simp
    ring
  refine ⟨hw, ?_⟩
  set w := u / (1 + 4 * u ^ 2) with hwdef
  have hw0 : w ≠ 0 := div_ne_zero hu h4
  rw [← hw]
  by_cases h5 : 1 - 5 * w ^ 2 = 0
  · have h5' : (w⁻¹) ^ 2 - 5 = 0 := by
      have : w⁻¹ ^ 2 - 5 = (1 - 5 * w ^ 2) / w ^ 2 := by
        field_simp
      rw [this, h5, zero_div]
    rw [h5, h5']
    simp
  · have h5' : (w⁻¹) ^ 2 - 5 ≠ 0 := by
      have : w⁻¹ ^ 2 - 5 = (1 - 5 * w ^ 2) / w ^ 2 := by
        field_simp
      rw [this]
      exact div_ne_zero h5 (pow_ne_zero _ hw0)
    field_simp

/-- `κ(χ) = 2/[(χ + 5)² − 5]²` is `1/200` at the singlet and the plane (`χ = 0, −10`) and `1/98` at the
last-step direction and colour (`χ = −5 ∓ 3i`). -/
theorem kappa_gap_values :
    (2 : ℂ) / ((chi (1 / 4) + 5) ^ 2 - 5) ^ 2 = 1 / 200 ∧
      (2 : ℂ) / ((chi (-1 / 4) + 5) ^ 2 - 5) ^ 2 = 1 / 200 ∧
      (2 : ℂ) / ((chi (I / 4) + 5) ^ 2 - 5) ^ 2 = 1 / 98 ∧
      (2 : ℂ) / ((chi (-I / 4) + 5) ^ 2 - 5) ^ 2 = 1 / 98 := by
  obtain ⟨h1, hi, hm, hmi⟩ := chi_quarters
  have hI2 : I ^ 2 = -1 := I_sq
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1]
    norm_num
  · rw [hm]
    norm_num
  · rw [hi]
    have : ((-5 - 3 * I + 5) ^ 2 - 5) = (-14 : ℂ) := by
      ring_nf
      rw [hI2]
      ring
    rw [this]
    norm_num
  · rw [hmi]
    have : ((-5 + 3 * I + 5) ^ 2 - 5) = (-14 : ℂ) := by
      ring_nf
      rw [hI2]
      ring
    rw [this]
    norm_num

/-- **The law's own transformation is a shift of the gap:**
`K(v)/v = K(u)/u + [χ(v) − χ(u)] I` for `K(u) = (1 + 4u²) − uA` and any operator `A`. -/
theorem own_transformation {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (u v : ℂ)
    (hu : u ≠ 0) (hv : v ≠ 0) :
    (1 / v) • ((1 + 4 * v ^ 2) • (1 : Matrix n n ℂ) - v • A) =
      (1 / u) • ((1 + 4 * u ^ 2) • (1 : Matrix n n ℂ) - u • A) + (chi v - chi u) • 1 := by
  rw [smul_sub, smul_sub, smul_smul, smul_smul, smul_smul, smul_smul, one_div_mul_cancel hv,
    one_div_mul_cancel hu, one_smul, chi, chi]
  have e1 : 1 / v * (1 + 4 * v ^ 2) = 1 / v + 4 * v := by
    field_simp
  have e2 : 1 / u * (1 + 4 * u ^ 2) = 1 / u + 4 * u := by
    field_simp
  rw [e1, e2]
  module

end Comparison.Formulas
