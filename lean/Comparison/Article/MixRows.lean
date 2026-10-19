import Comparison.Article.Mixing
import Comparison.Article.QMix

/-!
# The mixing rows as compositions of the frames `V` and `U`

Each row is the article's composition of the entries of `ckmV` or `pmnsU` (`Mixing.lean`), proved equal to
its closed form of `QMix.lean` and so placed within its printed digits: A003, G09, S05 (`|V_ud|`), K05, C09,
C04, C05, the triangle's angles C06 to C08, the lepton angles C10 to C13, `J_l` (T06) and the Dirac phase
`δ_l` (C14).
-/

namespace Comparison.Article

open Real Complex Comparison.Law

/-! ## The parameters are the generated atoms -/

theorem c12_eq : c12 = qc12 := rfl
theorem c23_eq : c23 = qc23 := rfl
theorem c13_eq : c13 = qc13 := rfl
theorem cdq_eq : cdq = qcdq := rfl
theorem sdq_eq : sdq = qsdq := rfl
theorem sB_eq : sB = qsB := rfl
theorem c2_eq : c2 = qc2 := rfl
theorem sP_eq' : sP = qsP := sP_eq
theorem cP_eq : cP = qcP := by rw [cP, cosOf, sP_eq']; rfl

theorem atoms_pos : 0 < qc12 ∧ 0 < qc23 ∧ 0 < qc13 ∧ 0 < qcdq ∧ 0 < qsdq ∧ 0 < qsP ∧ 0 < qcP ∧
    0 < qsB ∧ 0 < qc2 :=
  ⟨lt_of_lt_of_le (by norm_num) qc12_bnd.1, lt_of_lt_of_le (by norm_num) qc23_bnd.1,
    lt_of_lt_of_le (by norm_num) qc13_bnd.1, lt_of_lt_of_le (by norm_num) qcdq_bnd.1,
    lt_of_lt_of_le (by norm_num) qsdq_bnd.1, lt_of_lt_of_le (by norm_num) qsP_bnd.1,
    lt_of_lt_of_le (by norm_num) qcP_bnd.1, lt_of_lt_of_le (by norm_num) qsB_bnd.1,
    lt_of_lt_of_le (by norm_num) qc2_bnd.1⟩

/-- The quark frame in the generated atoms. -/
theorem ckmV_eq' : ckmV =
    !![((qc12 * qc13 : ℝ) : ℂ), ((9 / 40 * qc13 : ℝ) : ℂ), ((3 / 800 : ℝ) : ℂ) * (qcdq - qsdq * I);
      -(((9 / 40 * qc23 : ℝ) : ℂ)) - ((qc12 * (1 / 24) * (3 / 800) : ℝ) : ℂ) * (qcdq + qsdq * I),
        ((qc12 * qc23 : ℝ) : ℂ) - ((9 / 40 * (1 / 24) * (3 / 800) : ℝ) : ℂ) * (qcdq + qsdq * I),
        ((1 / 24 * qc13 : ℝ) : ℂ);
      ((9 / 40 * (1 / 24) : ℝ) : ℂ) - ((qc12 * qc23 * (3 / 800) : ℝ) : ℂ) * (qcdq + qsdq * I),
        -(((qc12 * (1 / 24) : ℝ) : ℂ)) - ((9 / 40 * qc23 * (3 / 800) : ℝ) : ℂ) * (qcdq + qsdq * I),
        ((qc23 * qc13 : ℝ) : ℂ)] := by
  rw [ckmV_eq, c12_eq, c23_eq, c13_eq, cdq_eq, sdq_eq]

/-- The lepton frame in the generated atoms. -/
theorem pmnsU_eq' : pmnsU =
    !![((3 / 4 * qcP : ℝ) : ℂ) + ((qc2 * qsB * qsP : ℝ) : ℂ) * (qsdq - qcdq * I),
        ((qcP * qsB : ℝ) : ℂ) - ((qc2 * (3 / 4) * qsP : ℝ) : ℂ) * (qsdq - qcdq * I),
        -(((qc2 * qsP : ℝ) : ℂ) * (qsdq - qcdq * I));
      -(((qc2 * qcP * qsB : ℝ) : ℂ)) + ((3 / 4 * qsP : ℝ) : ℂ) * (qsdq + qcdq * I),
        ((qc2 * (3 / 4) * qcP : ℝ) : ℂ) + ((qsB * qsP : ℝ) : ℂ) * (qsdq + qcdq * I),
        ((qcP * qc2 : ℝ) : ℂ);
      ((qc2 * qsB : ℝ) : ℂ), -(((3 / 4) * qc2 : ℝ) : ℂ), ((qc2 : ℝ) : ℂ)] := by
  rw [pmnsU_eq, cP_eq, sB_eq, sP_eq', c2_eq, cdq_eq, sdq_eq]

/-- The real and imaginary parts of the explicit entries. -/
macro "mix_simp" : tactic => `(tactic| simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
  Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Matrix.empty_val',
  Matrix.cons_val_fin_one, Matrix.head_fin_const, Complex.mul_re, Complex.mul_im, Complex.add_re,
  Complex.add_im, Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.conj_re,
  Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im])

theorem normSq_eq_sq_norm (z : ℂ) : ‖z‖ ^ 2 = z.re * z.re + z.im * z.im := by
  rw [Complex.sq_norm, Complex.normSq_apply]

/-! ## `|V_ud|` and the rows that carry it -/

theorem norm_Vud : ‖ckmV 0 0‖ = qAbsVud := by
  rw [ckmV_eq']
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.empty_val',
    Matrix.cons_val_fin_one]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mul_pos atoms_pos.1 atoms_pos.2.2.1)]
  rfl

/-- **Row A003, `(5m_p/36)|V_ud|`.** -/
noncomputable def rowA003 : ℝ := 5 * qMp / 36 * ‖ckmV 0 0‖

theorem rowA003_eq : rowA003 = qRowA003 := by rw [rowA003, norm_Vud]; rfl

theorem rowA003_digits : 126.9732228855 < rowA003 ∧ rowA003 < 126.9732228865 := by
  rw [rowA003_eq]; exact qRowA003_digits

/-- **Row G09, `f_π |V_ud|`.** -/
noncomputable def rowG09 : ℝ := qFpi * ‖ckmV 0 0‖

theorem rowG09_eq : rowG09 = qRowG09 := by rw [rowG09, norm_Vud]; rfl

theorem rowG09_digits : 127.1813712525 < rowG09 ∧ rowG09 < 127.1813712535 := by
  rw [rowG09_eq]; exact qRowG09_digits

/-- **Row S05, the neutron's lifetime `5099.33 s/(1.03983 |V_ud|²(1 + 3g_A²))`.** -/
noncomputable def rowS05 : ℝ := 5099.33 / (1.03983 * ‖ckmV 0 0‖ ^ 2 * (1 + 3 * qGA ^ 2))

theorem rowS05_eq : rowS05 = qRowS05 := by rw [rowS05, norm_Vud, qRowS05]; norm_num

theorem rowS05_digits : 878.0514118265 < rowS05 ∧ rowS05 < 878.0514118275 := by
  rw [rowS05_eq]; exact qRowS05_digits

/-! ## The diagonal and the two rows -/

/-- **Row K05, the diagonal quark current `Σ_i |V_ii|²`.** -/
noncomputable def rowK05 : ℝ := ‖ckmV 0 0‖ ^ 2 + ‖ckmV 1 1‖ ^ 2 + ‖ckmV 2 2‖ ^ 2

theorem rowK05_eq : rowK05 = qRowK05 := by
  rw [rowK05, normSq_eq_sq_norm, normSq_eq_sq_norm, normSq_eq_sq_norm, ckmV_eq', qRowK05, qDiagSum]
  mix_simp
  ring

theorem rowK05_digits : 2.895310844875 < rowK05 ∧ rowK05 < 2.895310844885 := by
  rw [rowK05_eq]; exact qRowK05_digits

/-- **Row C09, the two-row current `Σ_{i = u, c} Σ_j |V_ij|²`.** -/
noncomputable def rowC09 : ℝ :=
  ‖ckmV 0 0‖ ^ 2 + ‖ckmV 0 1‖ ^ 2 + ‖ckmV 0 2‖ ^ 2 + (‖ckmV 1 0‖ ^ 2 + ‖ckmV 1 1‖ ^ 2 + ‖ckmV 1 2‖ ^ 2)

theorem rowC09_eq : rowC09 = qTwoRows := by
  rw [rowC09]
  simp only [normSq_eq_sq_norm]
  rw [ckmV_eq', qTwoRows]
  mix_simp
  ring

/-- **Row C09 is `2`: two rows of a unitary matrix.** -/
theorem rowC09_digits : rowC09 = 2 := by
  rw [rowC09_eq, qTwoRows]
  have h1 : qc12 ^ 2 = 1 - (9 / 40) ^ 2 := by
    rw [qc12, Real.sq_sqrt (by norm_num)]
  have h2 : qc23 ^ 2 = 1 - (1 / 24) ^ 2 := by
    rw [qc23, Real.sq_sqrt (by norm_num)]
  have h3 : qc13 ^ 2 = 1 - (3 / 800) ^ 2 := by
    rw [qc13, Real.sq_sqrt (by norm_num)]
  have h4 : qsdq ^ 2 = 1 - qcdq ^ 2 := by
    rw [qsdq, qcdq, div_pow, div_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  linear_combination ((40960000 * qc13 ^ 2 + 40960000 * qc23 ^ 2 + qcdq ^ 2 + qsdq ^ 2) / 40960000) * h1 +
    1 * h2 + (577 / 576) * h3 + (577 / 40960000) * h4

/-! ## The phase and the quartet -/

/-- **Row C04, `δ_q = arg(b + w_C)`.** -/
noncomputable def rowC04 : ℝ := deltaQ

theorem rowC04_eq : rowC04 = qRowC04 := by
  rw [rowC04, deltaQ_eq_arg, arg_eq_arctan (by simp)]
  have : (7 + 16 * I : ℂ).im / (7 + 16 * I : ℂ).re = ((7 : ℝ) / 16)⁻¹ := by simp
  rw [this, Real.arctan_inv_of_pos (by norm_num), qRowC04]

theorem rowC04_digits : 1.15838588515 < rowC04 ∧ rowC04 < 1.15838588525 := by
  rw [rowC04_eq]; exact qRowC04_digits

/-- **Row C05, `10⁵ Im(V_us V_cb V_ub* V_cs*)`.** -/
noncomputable def rowC05 : ℝ :=
  10 ^ 5 * (ckmV 0 1 * ckmV 1 2 * (starRingEnd ℂ) (ckmV 0 2) * (starRingEnd ℂ) (ckmV 1 1)).im

theorem rowC05_eq : rowC05 = qRowC05 := by
  rw [rowC05, ckmV_eq', qRowC05, qJq]
  mix_simp
  ring

theorem rowC05_digits : 3.135509175785 < rowC05 ∧ rowC05 < 3.135509175795 := by
  rw [rowC05_eq]; exact qRowC05_digits

/-! ## The unitarity triangle -/

theorem neg_lt_of_bnd {x a b : ℝ} (h : Bnd x a b) (hb : b < 0) : x < 0 := lt_of_le_of_lt h.2 hb
theorem pos_of_bnd {x a b : ℝ} (h : Bnd x a b) (ha : 0 < a) : 0 < x := lt_of_lt_of_le ha h.1

theorem deg_second (t : ℝ) : 180 / π * (π / 2 + t) = 90 + 180 * t / π := by
  field_simp
  ring

/-- **Row C06, the triangle angle `α = arg(−V_td V_tb*/V_ud V_ub*)`** in degrees. -/
noncomputable def rowC06 : ℝ :=
  180 / π * Complex.arg (-(ckmV 2 0 * (starRingEnd ℂ) (ckmV 2 2)) / (ckmV 0 0 * (starRingEnd ℂ) (ckmV 0 2)))

theorem rowC06_eq : rowC06 = qRowC06 := by
  have hre : (-(ckmV 2 0 * (starRingEnd ℂ) (ckmV 2 2)) *
      (starRingEnd ℂ) (ckmV 0 0 * (starRingEnd ℂ) (ckmV 0 2))).re = qReAlpha := by
    rw [ckmV_eq', qReAlpha]; mix_simp; ring
  have him : (-(ckmV 2 0 * (starRingEnd ℂ) (ckmV 2 2)) *
      (starRingEnd ℂ) (ckmV 0 0 * (starRingEnd ℂ) (ckmV 0 2))).im = qImAlpha := by
    rw [ckmV_eq', qImAlpha]; mix_simp; ring
  have hb : ckmV 0 0 * (starRingEnd ℂ) (ckmV 0 2) ≠ 0 := by
    intro h
    have h0 : (-(ckmV 2 0 * (starRingEnd ℂ) (ckmV 2 2)) *
        (starRingEnd ℂ) (ckmV 0 0 * (starRingEnd ℂ) (ckmV 0 2))).im = 0 := by rw [h]; simp
    rw [him] at h0
    linarith [pos_of_bnd qImAlpha_bnd (by norm_num)]
  have s1 : qReAlpha < 0 := neg_lt_of_bnd qReAlpha_bnd (by norm_num)
  have s2 : 0 < qImAlpha := pos_of_bnd qImAlpha_bnd (by norm_num)
  rw [rowC06, arg_div_eq_arg_mul_conj _ _ hb, arg_second (hre ▸ s1) (him ▸ s2), hre, him, deg_second,
    qRowC06]

theorem rowC06_digits : 90.71377306425 < rowC06 ∧ rowC06 < 90.71377306435 := by
  rw [rowC06_eq]; exact qRowC06_digits

/-- **Row C07, the triangle angle `β = arg(−V_cd V_cb*/V_td V_tb*)`** in degrees. -/
noncomputable def rowC07 : ℝ :=
  180 / π * Complex.arg (-(ckmV 1 0 * (starRingEnd ℂ) (ckmV 1 2)) / (ckmV 2 0 * (starRingEnd ℂ) (ckmV 2 2)))

theorem rowC07_eq : rowC07 = qRowC07 := by
  have hre : (-(ckmV 1 0 * (starRingEnd ℂ) (ckmV 1 2)) *
      (starRingEnd ℂ) (ckmV 2 0 * (starRingEnd ℂ) (ckmV 2 2))).re = qReBeta := by
    rw [ckmV_eq', qReBeta]; mix_simp; ring
  have him : (-(ckmV 1 0 * (starRingEnd ℂ) (ckmV 1 2)) *
      (starRingEnd ℂ) (ckmV 2 0 * (starRingEnd ℂ) (ckmV 2 2))).im = qImBeta := by
    rw [ckmV_eq', qImBeta]; mix_simp; ring
  have hb : ckmV 2 0 * (starRingEnd ℂ) (ckmV 2 2) ≠ 0 := by
    intro h
    have h0 : (-(ckmV 1 0 * (starRingEnd ℂ) (ckmV 1 2)) *
        (starRingEnd ℂ) (ckmV 2 0 * (starRingEnd ℂ) (ckmV 2 2))).im = 0 := by rw [h]; simp
    rw [him] at h0
    linarith [pos_of_bnd qImBeta_bnd (by norm_num)]
  have s1 : 0 < qReBeta := pos_of_bnd qReBeta_bnd (by norm_num)
  rw [rowC07, arg_div_eq_arg_mul_conj _ _ hb, arg_eq_arctan (hre ▸ s1), hre, him, qRowC07]
  ring

theorem rowC07_digits : 22.95114393535 < rowC07 ∧ rowC07 < 22.95114393545 := by
  rw [rowC07_eq]; exact qRowC07_digits

/-- **Row C08, the triangle angle `γ = arg(−V_ud V_ub*/V_cd V_cb*)`** in degrees. -/
noncomputable def rowC08 : ℝ :=
  180 / π * Complex.arg (-(ckmV 0 0 * (starRingEnd ℂ) (ckmV 0 2)) / (ckmV 1 0 * (starRingEnd ℂ) (ckmV 1 2)))

theorem rowC08_eq : rowC08 = qRowC08 := by
  have hre : (-(ckmV 0 0 * (starRingEnd ℂ) (ckmV 0 2)) *
      (starRingEnd ℂ) (ckmV 1 0 * (starRingEnd ℂ) (ckmV 1 2))).re = qReGamma := by
    rw [ckmV_eq', qReGamma]; mix_simp; ring
  have him : (-(ckmV 0 0 * (starRingEnd ℂ) (ckmV 0 2)) *
      (starRingEnd ℂ) (ckmV 1 0 * (starRingEnd ℂ) (ckmV 1 2))).im = qImGamma := by
    rw [ckmV_eq', qImGamma]; mix_simp; ring
  have hb : ckmV 1 0 * (starRingEnd ℂ) (ckmV 1 2) ≠ 0 := by
    intro h
    have h0 : (-(ckmV 0 0 * (starRingEnd ℂ) (ckmV 0 2)) *
        (starRingEnd ℂ) (ckmV 1 0 * (starRingEnd ℂ) (ckmV 1 2))).im = 0 := by rw [h]; simp
    rw [him] at h0
    linarith [pos_of_bnd qImGamma_bnd (by norm_num)]
  have hR := pos_of_bnd qReGamma_bnd (by norm_num)
  have hI := pos_of_bnd qImGamma_bnd (by norm_num)
  rw [rowC08, arg_div_eq_arg_mul_conj _ _ hb, arg_eq_arctan (hre ▸ hR), hre, him]
  have : qImGamma / qReGamma = (qReGamma / qImGamma)⁻¹ := by rw [inv_div]
  rw [this, Real.arctan_inv_of_pos (div_pos hR hI), qRowC08]
  field_simp
  ring

theorem rowC08_digits : 66.33508300025 < rowC08 ∧ rowC08 < 66.33508300035 := by
  rw [rowC08_eq]; exact qRowC08_digits

/-! ## The lepton angles and quartet -/

/-- **Row C11, `s²₁₃ = |U_e3|²`.** -/
noncomputable def rowC11 : ℝ := ‖pmnsU 0 2‖ ^ 2

theorem rowC11_eq : rowC11 = qRowC11 := by
  rw [rowC11, normSq_eq_sq_norm, pmnsU_eq', qRowC11, qU02sq]; mix_simp; ring

/-- **Row C11 is `b s₁₂²/2 = 567/25600`.** -/
theorem rowC11_exact : rowC11 = 567 / 25600 := by
  rw [rowC11_eq, qRowC11, qU02sq]
  have h1 : qsP ^ 2 = 7 / 8 * (9 / 40) ^ 2 := by
    rw [qsP, mul_pow, Real.sq_sqrt (by norm_num)]
  have h2 : qc2 ^ 2 = 1 / 2 := by
    rw [qc2, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have h3 : qsdq ^ 2 + qcdq ^ 2 = 1 := by
    rw [qsdq, qcdq, div_pow, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have e : qc2 ^ 2 * qsP ^ 2 * (qsdq ^ 2 + qcdq ^ 2) = 567 / 25600 := by
    rw [h1, h2, h3]; norm_num
  linear_combination e

theorem rowC11_digits : rowC11 = 0.0221484375 := by rw [rowC11_exact]; norm_num

/-- **Row C10, `s²₁₂ = |U_e2|²/(1 − |U_e3|²)`.** -/
noncomputable def rowC10 : ℝ := ‖pmnsU 0 1‖ ^ 2 / (1 - ‖pmnsU 0 2‖ ^ 2)

theorem rowC10_eq : rowC10 = qRowC10 := by
  have hu : ‖pmnsU 0 1‖ ^ 2 = qU01sq := by
    rw [normSq_eq_sq_norm, pmnsU_eq', qU01sq]; mix_simp; ring
  rw [rowC10, hu, ← rowC11, rowC11_eq, qRowC11, qRowC10]

theorem rowC10_digits : 0.3050896109225 < rowC10 ∧ rowC10 < 0.3050896109235 := by
  rw [rowC10_eq]; exact qRowC10_digits

/-- **Row C12, `sin²2θ₁₃ = 4s²₁₃(1 − s²₁₃)`.** -/
noncomputable def rowC12 : ℝ := 4 * rowC11 * (1 - rowC11)

theorem rowC12_digits : 0.08663153686515 < rowC12 ∧ rowC12 < 0.08663153686525 := by
  rw [rowC12, rowC11_exact]; norm_num

/-- **Row C13, `s²₂₃ = |U_μ3|²/(1 − |U_e3|²)`.** -/
noncomputable def rowC13 : ℝ := ‖pmnsU 1 2‖ ^ 2 / (1 - ‖pmnsU 0 2‖ ^ 2)

theorem rowC13_eq : rowC13 = qRowC13 := by
  have hu : ‖pmnsU 1 2‖ ^ 2 = qU12sq := by
    rw [normSq_eq_sq_norm, pmnsU_eq', qU12sq]; mix_simp; ring
  rw [rowC13, hu, ← rowC11, rowC11_eq, qRowC11, qRowC13]

theorem rowC13_digits : 0.4886749490665 < rowC13 ∧ rowC13 < 0.4886749490675 := by
  rw [rowC13_eq]; exact qRowC13_digits

/-- **Row T06, the lepton quartet `J_l = Im(U_e1 U_μ2 U_e2* U_μ1*)`.** -/
noncomputable def rowT06 : ℝ :=
  (pmnsU 0 0 * pmnsU 1 1 * (starRingEnd ℂ) (pmnsU 0 1) * (starRingEnd ℂ) (pmnsU 1 0)).im

theorem rowT06_eq : rowT06 = qRowT06 := by
  rw [rowT06, pmnsU_eq', qRowT06, qJl]; mix_simp; ring

theorem rowT06_digits : -0.01446443474635 < rowT06 ∧ rowT06 < -0.01446443474625 := by
  rw [rowT06_eq]; exact qRowT06_digits

/-! ## The lepton phase -/

/-- The scale `(s²₁₂c²₁₂s²₂₃c²₂₃s²₁₃)^{1/2}` of the standard parametrization. -/
noncomputable def scaleL : ℝ :=
  √(rowC10 * (1 - rowC10) * rowC13 * (1 - rowC13) * rowC11)

/-- The sine side `J_l/(scale c²₁₃)`. -/
noncomputable def yLside : ℝ := rowT06 / (scaleL * (1 - rowC11))

/-- The cosine side `(|U_μ1|² − s²₁₂c²₂₃ − c²₁₂s²₂₃s²₁₃)/(2 scale)`. -/
noncomputable def xLside : ℝ :=
  (‖pmnsU 1 0‖ ^ 2 - rowC10 * (1 - rowC13) - (1 - rowC10) * rowC13 * rowC11) / (2 * scaleL)

/-- **Row C14, the Dirac phase `δ_l` of `U`** in degrees on `[0, 360)`: `atan2` of the two sides. -/
noncomputable def rowC14 : ℝ := 180 / π * Complex.arg (xLside + yLside * I) + 360

theorem scaleL_eq : scaleL = qScale := by
  rw [scaleL, rowC10_eq, rowC13_eq, rowC11_eq, qScale, qRowC10, qRowC13, qRowC11, qS12, qS23]

theorem yL_eq : yLside = qYL := by
  rw [yLside, scaleL_eq, rowT06_eq, rowC11_eq, qYL, qRowT06, qRowC11]
  ring

theorem xL_eq : xLside = qXL := by
  have hu : ‖pmnsU 1 0‖ ^ 2 = qU10sq := by
    rw [normSq_eq_sq_norm, pmnsU_eq', qU10sq]; mix_simp; ring
  rw [xLside, hu, scaleL_eq, rowC10_eq, rowC13_eq, rowC11_eq, qXL, qRowC10, qRowC13, qRowC11, qS12, qS23]
  ring

theorem rowC14_eq : rowC14 = qRowC14 := by
  have hx : xLside < 0 := by rw [xL_eq]; exact neg_lt_of_bnd qXL_bnd (by norm_num)
  have hy : yLside < 0 := by rw [yL_eq]; exact neg_lt_of_bnd qYL_bnd (by norm_num)
  have hre : (((xLside : ℂ) + (yLside : ℂ) * I)).re = xLside := by simp
  have him : (((xLside : ℂ) + (yLside : ℂ) * I)).im = yLside := by simp
  have hx' : (((xLside : ℂ) + (yLside : ℂ) * I)).re < 0 := by rw [hre]; exact hx
  have hy' : (((xLside : ℂ) + (yLside : ℂ) * I)).im < 0 := by rw [him]; exact hy
  rw [rowC14, arg_third hx' hy', hre, him, xL_eq, yL_eq, qRowC14, neg_div_neg_eq]
  field_simp
  ring

theorem rowC14_digits : 205.5842258345 < rowC14 ∧ rowC14 < 205.5842258355 := by
  rw [rowC14_eq]; exact qRowC14_digits

end Comparison.Article
