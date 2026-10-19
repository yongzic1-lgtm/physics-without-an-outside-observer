import Comparison.Article.RowsExact

/-!
# The mixings (Proposition 122, Eqs. (42) to (44))

The rotation `R_ij(s, φ)` in the plane `(i, j)` with `(R_ij)_ii = (R_ij)_jj = (1 − s²)^{1/2}`,
`(R_ij)_ij = s e^{−iφ}`, `(R_ij)_ji = −s e^{iφ}`; the quark frame `V = R₂₃(s₂₃) R₁₃(s₁₃, δ_q) R₁₂(s₁₂)` with
`s₁₂ = 9/40`, `s₂₃ = 1/24`, `s₁₃ = 3/800` (rows C01 to C03) and `δ_q = arg(b + w_C) = arg(7 + 16i)`
(Proposition 50); the lepton frame `U = R₁₂(√(2b) s₁₂, π/2 − δ_q)† R₂₃(2^{-1/2}) R₁₂(b^{1/2})`.

* `wC_eq`, `deltaQ_eq_arg`: **`w_C = i` and `δ_q = arg(b + w_C) = arg(7 + 16i)`**; `cos_deltaQ`,
  `sin_deltaQ`: `7/√305`, `16/√305`.
* `ckmV_eq`, `pmnsU_eq`: **every entry of `V` and `U`** in the cosines and sines.
-/

namespace Comparison.Article

open Real Complex Comparison.Law

/-- The cosine of a rotation of sine `s`. -/
noncomputable def cosOf (s : ℝ) : ℝ := √(1 - s ^ 2)

/-- `R₁₂(s, φ)`. -/
noncomputable def R12 (s φ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(cosOf s : ℂ), s * Complex.exp (-(φ * I)), 0; -(s * Complex.exp (φ * I)), (cosOf s : ℂ), 0;
    0, 0, 1]

/-- `R₁₃(s, φ)`. -/
noncomputable def R13 (s φ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(cosOf s : ℂ), 0, s * Complex.exp (-(φ * I)); 0, 1, 0;
    -(s * Complex.exp (φ * I)), 0, (cosOf s : ℂ)]

/-- `R₂₃(s, φ)`. -/
noncomputable def R23 (s φ : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, 0, 0; 0, (cosOf s : ℂ), s * Complex.exp (-(φ * I));
    0, -(s * Complex.exp (φ * I)), (cosOf s : ℂ)]

/-! ## The complex weight: `δ_q = arg(b + w_C)` -/

/-- **`w_C = i`** (Proposition 44 at `C`). -/
theorem wC_eq : wS sC = I := table_C.2.2.1

/-- **The quark phase `δ_q = arg(b + w_C)`.** -/
noncomputable def deltaQ : ℝ := Complex.arg (bS sHere + wS sC)

theorem deltaQ_eq_arg : deltaQ = Complex.arg (7 + 16 * I) := by
  rw [deltaQ, wC_eq, piece_b_here]
  have : (7 + 16 * I : ℂ) = ((16 : ℝ) : ℂ) * (7 / 16 + I) := by push_cast; ring
  rw [this, Complex.arg_real_mul _ (by norm_num : (0 : ℝ) < 16)]

theorem abs_7_16 : ‖(7 + 16 * I : ℂ)‖ = √305 := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  congr 1
  simp
  norm_num

theorem cos_deltaQ : Real.cos deltaQ = 7 / √305 := by
  rw [deltaQ_eq_arg, Complex.cos_arg (by
    intro h
    have := congrArg Complex.re h
    simp at this), abs_7_16]
  simp

theorem sin_deltaQ : Real.sin deltaQ = 16 / √305 := by
  rw [deltaQ_eq_arg, Complex.sin_arg, abs_7_16]
  simp

theorem exp_deltaQ : Complex.exp (deltaQ * I) = ((7 / √305 : ℝ) : ℂ) + ((16 / √305 : ℝ) : ℂ) * I := by
  rw [← cos_deltaQ, ← sin_deltaQ, Complex.exp_mul_I]
  push_cast
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem exp_neg_deltaQ :
    Complex.exp (-(deltaQ * I)) = ((7 / √305 : ℝ) : ℂ) - ((16 / √305 : ℝ) : ℂ) * I := by
  rw [show -(deltaQ * I) = ((-deltaQ : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg, cos_deltaQ, sin_deltaQ]
  push_cast
  ring

/-! ## The quark frame -/

/-- **`V = R₂₃(s₂₃) R₁₃(s₁₃, δ_q) R₁₂(s₁₂)`** with the rows C01 to C03. -/
noncomputable def ckmV : Matrix (Fin 3) (Fin 3) ℂ :=
  R23 rowC02 0 * R13 rowC03 deltaQ * R12 rowC01 0

/-- The real parameters: `c = (1 − s²)^{1/2}`, `cos δ`, `sin δ`. -/
noncomputable def c12 : ℝ := cosOf (9 / 40)
noncomputable def c23 : ℝ := cosOf (1 / 24)
noncomputable def c13 : ℝ := cosOf (3 / 800)
noncomputable def cdq : ℝ := 7 / √305
noncomputable def sdq : ℝ := 16 / √305

/-- **The entries of the quark frame.** -/
theorem ckmV_eq : ckmV =
    !![((c12 * c13 : ℝ) : ℂ), ((9 / 40 * c13 : ℝ) : ℂ), ((3 / 800 : ℝ) : ℂ) * (cdq - sdq * I);
      -(((9 / 40 * c23 : ℝ) : ℂ)) - ((c12 * (1 / 24) * (3 / 800) : ℝ) : ℂ) * (cdq + sdq * I),
        ((c12 * c23 : ℝ) : ℂ) - ((9 / 40 * (1 / 24) * (3 / 800) : ℝ) : ℂ) * (cdq + sdq * I),
        ((1 / 24 * c13 : ℝ) : ℂ);
      ((9 / 40 * (1 / 24) : ℝ) : ℂ) - ((c12 * c23 * (3 / 800) : ℝ) : ℂ) * (cdq + sdq * I),
        -(((c12 * (1 / 24) : ℝ) : ℂ)) - ((9 / 40 * c23 * (3 / 800) : ℝ) : ℂ) * (cdq + sdq * I),
        ((c23 * c13 : ℝ) : ℂ)] := by
  rw [ckmV, rowC01_digits, rowC02_eq, rowC03_digits, R23, R13, R12, exp_deltaQ, exp_neg_deltaQ]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, c12, c23, c13, cdq, sdq] <;> norm_num <;> ring

/-! ## The lepton frame -/

/-- The sine of the first lepton rotation, `√(2b) s₁₂`. -/
noncomputable def sP : ℝ := √(2 * (bS sHere).re) * rowC01

/-- **`U = R₁₂(√(2b) s₁₂, π/2 − δ_q)† R₂₃(2^{-1/2}) R₁₂(b^{1/2})`.** -/
noncomputable def pmnsU : Matrix (Fin 3) (Fin 3) ℂ :=
  (R12 sP (π / 2 - deltaQ)).conjTranspose * R23 (1 / √2) 0 * R12 √((bS sHere).re) 0

noncomputable def cP : ℝ := cosOf sP
noncomputable def sB : ℝ := √(7 / 16)
noncomputable def c2 : ℝ := 1 / √2

theorem sP_eq : sP = √(7 / 8) * (9 / 40) := by
  rw [sP, piece_b_here, rowC01_digits]
  norm_num

theorem cosOf_half : cosOf (1 / √2) = 1 / √2 := by
  rw [cosOf, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [show (1 : ℝ) - 1 ^ 2 / 2 = 1 / 2 by norm_num, Real.sqrt_div' 1 (by norm_num : (0 : ℝ) ≤ 2)]
  simp

theorem cosOf_sB : cosOf √(7 / 16) = 3 / 4 := by
  rw [cosOf, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7 / 16)]
  rw [show (1 : ℝ) - 7 / 16 = (3 / 4) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

theorem exp_phiL : Complex.exp ((π / 2 - deltaQ : ℝ) * I) = (sdq : ℂ) + (cdq : ℂ) * I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two_sub,
    Real.sin_pi_div_two_sub, cos_deltaQ, sin_deltaQ, sdq, cdq]

theorem exp_neg_phiL : Complex.exp (-((π / 2 - deltaQ : ℝ) * I)) = (sdq : ℂ) - (cdq : ℂ) * I := by
  rw [show -((π / 2 - deltaQ : ℝ) * I) = ((-(π / 2 - deltaQ) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
    Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub, cos_deltaQ, sin_deltaQ, sdq, cdq]
  push_cast
  ring

/-- **The entries of the lepton frame**, `c₂ = s₂ = 2^{-1/2}`, `c_b = 3/4`, `s_b = (7/16)^{1/2}`. -/
theorem pmnsU_eq : pmnsU =
    !![((3 / 4 * cP : ℝ) : ℂ) + ((c2 * sB * sP : ℝ) : ℂ) * (sdq - cdq * I),
        ((cP * sB : ℝ) : ℂ) - ((c2 * (3 / 4) * sP : ℝ) : ℂ) * (sdq - cdq * I),
        -(((c2 * sP : ℝ) : ℂ) * (sdq - cdq * I));
      -(((c2 * cP * sB : ℝ) : ℂ)) + ((3 / 4 * sP : ℝ) : ℂ) * (sdq + cdq * I),
        ((c2 * (3 / 4) * cP : ℝ) : ℂ) + ((sB * sP : ℝ) : ℂ) * (sdq + cdq * I),
        ((cP * c2 : ℝ) : ℂ);
      ((c2 * sB : ℝ) : ℂ), -(((3 / 4) * c2 : ℝ) : ℂ), ((c2 : ℝ) : ℂ)] := by
  have hb : (bS sHere).re = 7 / 16 := by rw [piece_b_here]; norm_num
  rw [pmnsU, R12, R12, R23, hb, cosOf_half, cosOf_sB, exp_phiL, exp_neg_phiL]
  rw [show cosOf sP = cP from rfl]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply, sB, c2] <;> ring

/-! ## The argument of a complex number by the arctangent -/

/-- `arg w = arctan(Im w/Re w)` when `Re w > 0`. -/
theorem arg_eq_arctan {w : ℂ} (h : 0 < w.re) : Complex.arg w = Real.arctan (w.im / w.re) := by
  have h1 : |Complex.arg w| < π / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl h)
  rw [abs_lt] at h1
  rw [← Complex.tan_arg, Real.arctan_tan h1.1 h1.2]

/-- **The second quadrant:** `arg w = π/2 + arctan(−Re w/Im w)` when `Re w < 0 < Im w`. -/
theorem arg_second {w : ℂ} (hre : w.re < 0) (him : 0 < w.im) :
    Complex.arg w = π / 2 + Real.arctan (-w.re / w.im) := by
  have hw : w ≠ 0 := by
    intro h
    rw [h] at him
    simp at him
  have hθ := Complex.arg_of_re_neg_of_im_nonneg hre him.le
  have ha := Real.neg_pi_div_two_le_arcsin ((-w).im / ‖w‖)
  have hlt : Complex.arg w < π := Complex.arg_lt_pi_iff.mpr (Or.inr him.ne')
  have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have key : Real.tan (Complex.arg w - π / 2) = -w.re / w.im := by
    rw [Real.tan_eq_sin_div_cos, Real.sin_sub_pi_div_two, Real.cos_sub_pi_div_two,
      Complex.cos_arg hw, Complex.sin_arg]
    field_simp
  have hI : Complex.arg w - π / 2 ∈ Set.Ioo (-(π / 2)) (π / 2) := by
    constructor <;> linarith [Real.pi_pos]
  rw [← key, Real.arctan_tan hI.1 hI.2]
  ring

/-- **The third quadrant:** `arg w = arctan(Im w/Re w) − π` when `Re w < 0` and `Im w < 0`. -/
theorem arg_third {w : ℂ} (hre : w.re < 0) (him : w.im < 0) :
    Complex.arg w = Real.arctan (w.im / w.re) - π := by
  have hθ := Complex.arg_of_re_neg_of_im_neg hre him
  have ha := Real.arcsin_le_pi_div_two ((-w).im / ‖w‖)
  have ha' := Real.neg_pi_div_two_le_arcsin ((-w).im / ‖w‖)
  have hneg : (-w).im / ‖w‖ > 0 := by
    have hw : w ≠ 0 := by
      intro h
      rw [h] at him
      simp at him
    have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
    simp only [Complex.neg_im]
    exact div_pos (by linarith) hn
  have hpos : 0 < Real.arcsin ((-w).im / ‖w‖) := Real.arcsin_pos.mpr hneg
  have hlt : Real.arcsin ((-w).im / ‖w‖) < π / 2 := by
    rcases eq_or_lt_of_le ha with h | h
    · exfalso
      rw [Real.arcsin_eq_pi_div_two] at h
      have hw : w ≠ 0 := by
        intro h0
        rw [h0] at him
        simp at him
      have hn : 0 < ‖w‖ := norm_pos_iff.mpr hw
      rw [le_div_iff₀ hn, one_mul] at h
      have : ‖w‖ ≤ |w.im| := by
        simp only [Complex.neg_im] at h
        rw [abs_of_neg him]
        linarith
      have hre2 : 0 < w.re ^ 2 := by nlinarith
      have : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        ring
      nlinarith [abs_nonneg w.im, sq_abs w.im, norm_nonneg w]
    · exact h
  have key : Real.tan (Complex.arg w + π) = w.im / w.re := by
    rw [Real.tan_add_pi, Complex.tan_arg]
  have hI : Complex.arg w + π ∈ Set.Ioo (-(π / 2)) (π / 2) := by
    rw [hθ]
    constructor <;> linarith [Real.pi_pos]
  rw [← key, Real.arctan_tan hI.1 hI.2]
  ring

/-- `arg (a/b) = arg (a · conj b)` for `b ≠ 0`. -/
theorem arg_div_eq_arg_mul_conj (a b : ℂ) (hb : b ≠ 0) :
    Complex.arg (a / b) = Complex.arg (a * (starRingEnd ℂ) b) := by
  have hn : 0 < Complex.normSq b := Complex.normSq_pos.mpr hb
  rw [div_eq_mul_inv, Complex.inv_def, ← mul_assoc, mul_comm, Complex.arg_real_mul _ (inv_pos.mpr hn)]

end Comparison.Article
