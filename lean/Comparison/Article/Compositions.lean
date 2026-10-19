import Comparison.Article.QCosmos
import Comparison.Article.RowsExact
import Comparison.Article.MixRows
import Comparison.Existence.Zero
import Comparison.WholePicture.Polar

/-!
# The compositions of single propositions, assembled

Each theorem gathers, for one proposition, the composition the proposition states (as an equation between the
generated quantity and its native form) and the printed digits of the rows that carry it.

* `eh_own_count` (**Eq. (19)**): `E_H = 3` as its own count, the expected steps along the last-step direction per excursion
  (`Existence/Zero.lean`: `steps_along_lastDirection`), and `E_H = Eℓ C_h/320 = 16·60/320`.
* `sizes_moments_cosmos` (**Proposition 70**): `r_p = 4ħ/m_pc`, `μ_p = [(Var ℓ/20)S_μ]^{1/2}`,
  `S_μ = 1 − ε₂/(Eℓ² b)`, `η_B = 3a¹¹`, `Λℓ_P² = 3τ(α_G s)³` with `τ = 2π/(Eℓ m_p/m_e)`, `s = 3/50`.
* `one_sequence` (**Proposition 118**): `M_Pl = m_p/W`, `M_off = M_Pl/3⁶`, `M_R = M_Pl/3⁹`, `M_off/M_R = 27`,
  `M_off³ = M_Pl M_R²`, `v/m_p = M/(√2 (9/10) W_W)^{1/2} = 262.418158676`, `τ(p → e⁺π⁰) = 72²ħ/(3²⁴W⁴m_p)`, and
  `α_s > α > G_F m_p² > α_G`.
* `nucleon_at_rest` (**Proposition 120**, **Eq. (39)**): `μ_p`, `μ_n = −(44/23)S_μ^{1/2}` with
  `44/23 = 4(1 + E_P)/23`, `g_A = (5/3)(2/5)^{2b/3}`, `4λ_p`, `τ_n`, to their digits.
* `pion_constant` (**Proposition 121**): `f_π = η m_p (2k_C)^{1/2}/(2π μ_p)`.
* `cosmos` (**Proposition 127**): `η_B = 3a¹¹`, `A_s = 12a¹¹(k_*ℓ)^{−1/40}`, `n_s = 39/40`, `N_eff = 3ησ^{4/3}`
  with `T_ν/T_γ = (4σ/11)^{1/3}` (`neff_temperature`), `Tr L²/4 = 24` against `1 + 10 = 11`, and `one_surface`:
  with `ρ_Λ/ρ_m = c a³` there is exactly one surface with `ρ_Λ/ρ_m = 24/11`.
-/

namespace Comparison.Article

open Real

/-! ## Eq. (19): `E_H` as its own count -/

/-- **`E_H = 3` as its own count**, and `E_H = Eℓ C_h/320`. -/
theorem eh_own_count (h : Fin 5) :
    HasSum (fun n => (∑ s ∈ (excursionStates h).filter (fun s => s.2 ≠ h), (stateCount n s : ℝ)) /
      (5 * 4 ^ n) / 4) 3 ∧ (16 : ℚ) * 60 / 320 = 3 :=
  ⟨steps_along_lastDirection h, by norm_num⟩

/-! ## Proposition 70 -/

/-- **Proposition 70: sizes, moments and the cosmos, as compositions.** -/
theorem sizes_moments_cosmos :
    rowG01 = 4 * (qHc / qMp) ∧ qMup = √((156 / 20) * qSmu) ∧
      qSmu = 1 - qEps2 / (16 ^ 2 * (7 / 16)) ∧ rowF01 = 3 * (5 / 38 : ℝ) ^ 11 * 10 ^ 10 ∧
      qLam = 3 * qTau * (qW ^ 2 * (3 / 50)) ^ 3 ∧ qTau = 2 * π / (16 * qRp) ∧
      ((8.412356402125e-1 : ℝ) < rowG01 ∧ rowG01 < 8.412356402135e-1) ∧
      ((2.79284734525 : ℝ) < qMup ∧ qMup < 2.79284734535) ∧
      ((6.140047623455 : ℝ) < rowF01 ∧ rowF01 < 6.140047623465) := by
  refine ⟨by rw [rowG01, qLp], by rw [qMup]; norm_num, by rw [qSmu]; norm_num, by rw [rowF01]; norm_num,
    by rw [qLam]; ring, rfl, rowG01_digits, ?_, rowF01_digits⟩
  have h := rowG03_digits
  rw [rowG03] at h
  exact h

/-! ## Proposition 118: the one sequence -/

theorem qMp_pos'' : 0 < qMp := lt_of_lt_of_le (by norm_num) qMp_bnd.1

/-- **`v/m_p = M/(√2 (9/10) W_W)^{1/2}`.** -/
theorem v_over_mp : qV / (qMp / 1000) = 296 / √(√2 * ((9 / 10) * qWW)) := by
  have hm : 0 < qMp / 1000 := by have := qMp_pos''; positivity
  have hW : 0 < qWW := lt_of_lt_of_le (by norm_num) qWW_bnd.1
  have hG : 0 < qGF := lt_of_lt_of_le (by norm_num) qGF_bnd.1
  have hA : qV = (√(√2 * qGF))⁻¹ := by
    rw [qV, Real.rpow_neg (mul_nonneg (Real.sqrt_nonneg 2) hG.le), ← Real.sqrt_eq_rpow]
  have e : √(√2 * qGF) = √(√2 * ((9 / 10) * qWW)) / (296 * (qMp / 1000)) := by
    rw [qGF, qGFmp2]
    rw [show √2 * ((9 / 10) * qWW / 87616 / (qMp / 1000) ^ 2) =
        (√2 * ((9 / 10) * qWW)) / (296 * (qMp / 1000)) ^ 2 by field_simp; ring]
    rw [Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by positivity)]
  have hs : 0 < √(√2 * ((9 / 10) * qWW)) := Real.sqrt_pos.mpr (by positivity)
  rw [hA, e]
  field_simp
  exact div_self qMp_pos''.ne'

/-- **Proposition 118: the one sequence.** -/
theorem one_sequence :
    qMpl = (qMp / 1000) / qW ∧ qMoff = qMpl / 3 ^ 6 ∧ qMR = qMpl / 3 ^ 9 ∧ qMoff / qMR = 27 ∧
      qMoff ^ 3 = qMpl * qMR ^ 2 ∧
      qV / (qMp / 1000) = 296 / √(√2 * ((9 / 10) * qWW)) ∧
      ((262.4181586755 : ℝ) < qV / (qMp / 1000) ∧ qV / (qMp / 1000) < 262.4181586765) ∧
      qExcursion = 72 ^ 2 * qHbar / (3 ^ 24 * qW ^ 4 * qMp) / 31557600 ∧
      qW ^ 2 < qGFmp2 ∧ qGFmp2 < qAlpha ∧ qAlpha < qAlphaS ∧
      ((1.220889811885 : ℝ) < rowD05 ∧ rowD05 < 1.220889811895) ∧
      ((1.674745969655e16 : ℝ) < rowT02 ∧ rowT02 < 1.674745969665e16) ∧
      ((6.202762850605e14 : ℝ) < rowT01 ∧ rowT01 < 6.202762850615e14) ∧
      ((1.169710989455e37 : ℝ) < rowK06 ∧ rowK06 < 1.169710989465e37) := by
  have hW : 0 < qW := lt_of_lt_of_le (by norm_num) qW_bnd.1
  have hMpl : 0 < qMpl := by rw [qMpl]; have := qMp_pos''; positivity
  have hvm : Bnd (qV / (qMp / 1000)) _ _ :=
    Bnd.div qV_bnd (Bnd.div qMp_bnd (Bnd.const (1000 : ℝ)) (by norm_num) (by norm_num)) (by norm_num)
      (by norm_num)
  have hW2 : Bnd (qW ^ 2) _ _ := Bnd.pow qW_bnd (by norm_num) 2
  refine ⟨rfl, by rw [qMoff]; ring, by rw [qMR]; ring, ?_, ?_, v_over_mp,
    hvm.strict (by norm_num) (by norm_num), by rw [qExcursion]; norm_num, ?_, ?_, ?_, rowD05_digits,
    rowT02_digits, rowT01_digits, rowK06_digits⟩
  · rw [qMoff, qMR]
    field_simp
    norm_num
  · rw [qMoff, qMR]
    ring
  · exact lt_of_le_of_lt hW2.2 (lt_of_lt_of_le (by norm_num) qGFmp2_bnd.1)
  · exact lt_of_le_of_lt qGFmp2_bnd.2 (lt_of_lt_of_le (by norm_num) qAlpha_bnd.1)
  · exact lt_of_le_of_lt qAlpha_bnd.2 (lt_of_lt_of_le (by norm_num) qAlphaS_bnd.1)

/-! ## Propositions 120 and 121, Eq. (39) -/

/-- **Proposition 120, Eq. (39): the nucleon at rest, as compositions.** -/
theorem nucleon_at_rest :
    qMup = √((156 / 20) * qSmu) ∧ qMun = -((4 * (1 + 10) / 23) * √qSmu) ∧
      qSmu = 1 - qEps2 / (16 ^ 2 * (7 / 16)) ∧ qEps2 = qAlpha ^ 2 / (1 + qAlpha / 10) ∧
      qGA = 5 / 3 * (2 / 5 : ℝ) ^ (2 * (7 / 16) / 3 : ℝ) ∧ rowG01 = 4 * qLp ∧
      ((2.79284734525 : ℝ) < rowG03 ∧ rowG03 < 2.79284734535) ∧
      ((-1.913043023815 : ℝ) < rowG04 ∧ rowG04 < -1.913043023805) ∧
      ((1.275800928115 : ℝ) < rowS01 ∧ rowS01 < 1.275800928125) ∧
      ((8.412356402125e-1 : ℝ) < rowG01 ∧ rowG01 < 8.412356402135e-1) ∧
      ((878.0514118265 : ℝ) < rowS05 ∧ rowS05 < 878.0514118275) := by
  refine ⟨by rw [qMup]; norm_num, by rw [qMun]; norm_num, by rw [qSmu]; norm_num, rfl, ?_, rfl,
    rowG03_digits, rowG04_digits, rowS01_digits, rowG01_digits, rowS05_digits⟩
  rw [qGA]
  norm_num

/-- **Proposition 121: `f_π = η m_p (2k_C)^{1/2}/(2π μ_p)`**, `η = 295/296`, `k_C = 3`, to its digits. -/
theorem pion_constant :
    qFpi = (295 / 296) * qMp * √(2 * 3) / (2 * π * qMup) ∧
      ((1.305291954775e2 : ℝ) < rowG08 ∧ rowG08 < 1.305291954785e2) := by
  refine ⟨by rw [qFpi]; norm_num, rowG08_digits⟩

/-! ## Proposition 127: the cosmos -/

/-- **`N_eff = 3ησ^{4/3} = 3η (11/4)^{4/3} (T_ν/T_γ)⁴` with `T_ν/T_γ = (4σ/11)^{1/3}`.** -/
theorem neff_temperature :
    3 * (295 / 296) * ((4 * (75 / 74) / 11 : ℝ) ^ (1 / 3 : ℝ)) ^ 4 * (11 / 4 : ℝ) ^ (4 / 3 : ℝ) =
      3 * (295 / 296) * (75 / 74 : ℝ) ^ (4 / 3 : ℝ) := by
  have hx : (0 : ℝ) ≤ 4 * (75 / 74) / 11 := by norm_num
  have e1 : ((4 * (75 / 74) / 11 : ℝ) ^ (1 / 3 : ℝ)) ^ 4 = (4 * (75 / 74) / 11 : ℝ) ^ (4 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  have e2 : (4 * (75 / 74) / 11 : ℝ) ^ (4 / 3 : ℝ) * (11 / 4 : ℝ) ^ (4 / 3 : ℝ) = (75 / 74 : ℝ) ^ (4 / 3 : ℝ) := by
    rw [← Real.mul_rpow hx (by norm_num)]
    norm_num
  rw [e1, mul_assoc, e2]

/-- **The one surface:** with `ρ_Λ/ρ_m = c a³` (`c > 0`), exactly one `a > 0` has `ρ_Λ/ρ_m = 24/11`. -/
theorem one_surface (c : ℝ) (hc : 0 < c) : ∃! a : ℝ, 0 < a ∧ c * a ^ 3 = 24 / 11 := by
  have hq : (0 : ℝ) < 24 / 11 / c := by positivity
  refine ⟨(24 / 11 / c) ^ (1 / 3 : ℝ), ⟨by positivity, ?_⟩, ?_⟩
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le]
    norm_num
    field_simp
  · rintro a ⟨ha, hca⟩
    have h3 : a ^ 3 = 24 / 11 / c := by
      field_simp
      linarith
    rw [← h3, ← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    norm_num

/-- **Proposition 127: the cosmos, as compositions.** -/
theorem cosmos :
    rowF01 = 3 * (5 / 38 : ℝ) ^ 11 * 10 ^ 10 ∧ qAs = 12 * (5 / 38 : ℝ) ^ 11 * qKl ∧
      qKl = ((1 / 20) * qEll) ^ (-(1 / 40 : ℝ)) ∧ rowC15 = 39 / 40 ∧
      rowF04 = 3 * (295 / 296) * (75 / 74 : ℝ) ^ (4 / 3 : ℝ) ∧
      ((6.140047623455 : ℝ) < rowF01 ∧ rowF01 < 6.140047623465) ∧
      ((3.061309860145 : ℝ) < rowF03 ∧ rowF03 < 3.061309860155) ∧
      ((3.043857273615 : ℝ) < rowF04 ∧ rowF04 < 3.043857273625) ∧
      (L * L).trace / 4 = 24 ∧
      Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' L) 6) +
        Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' L) 2) = 11 := by
  refine ⟨by rw [rowF01] <;> norm_num, by rw [qAs] <;> norm_num, by rw [qKl] <;> norm_num, ?_, ?_,
    rowF01_digits, rowF03_digits, rowF04_digits, Comparison.WholePicture.twentyfour_eleven.1,
    Comparison.WholePicture.twentyfour_eleven.2⟩
  · rw [rowC15_digits]; norm_num
  · rw [rowF04]; norm_num

/-! ## Proposition 68 (S68 of the public edition): the weak, the Higgs and the top -/

/-- **Proposition 68 as compositions:** `G_F m_p² = (1 − 1/N₂) W_W/M²`, the weak angle `ŝ² = 3N_h`, the scalar
`m_H = v(2πα/χ_h)^{1/2}` with `χ_h = 30/169`, the top `m_t = v(η/2σ)^{1/2}` with `η/2σ = 59/120`, and the top's
Yukawa coupling `y_t = √2 m_t/v = (η/σ)^{1/2} = (59/60)^{1/2}`. -/
theorem weak_higgs_top :
    qGFmp2 = (1 - 1 / 10) * qWW / 296 ^ 2 ∧ qSw = 3 * qNh ∧
      qMh = qV * √(2 * π * qAlpha / (30 / 169)) ∧ qMt = qV * √((295 / 296) / (2 * (75 / 74))) ∧
      √2 * qMt / qV = √((295 / 296) / (75 / 74)) ∧
      ((125.1347715925 : ℝ) < qMh ∧ qMh < 125.1347715935) ∧
      ((172.6466136135 : ℝ) < qMt ∧ qMt < 172.6466136145) := by
  have hV : qV ≠ 0 := (lt_of_lt_of_le (by norm_num) qV_bnd.1).ne'
  refine ⟨by rw [qGFmp2] <;> norm_num, rfl, by rw [qMh] <;> ring_nf, by rw [qMt] <;> norm_num, ?_,
    qMh_bnd.strict (by norm_num) (by norm_num), qMt_bnd.strict (by norm_num) (by norm_num)⟩
  rw [qMt]
  have e : √2 * (qV * √(59 / 120)) / qV = √2 * √(59 / 120) := by
    field_simp
  rw [e, ← Real.sqrt_mul (by norm_num)]
  norm_num

end Comparison.Article
