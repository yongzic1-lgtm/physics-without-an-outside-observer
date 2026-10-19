import Comparison.Article.QMisc
import Comparison.Article.Deuteron
import Comparison.Article.Mixing
import Comparison.ArticleStatements.Radar

/-!
# The assembled statements of single propositions

* `electroweak_poles` (**Proposition 119**; S119 of the public edition): `ŝ² = 3N_h`, `3N_con`,
  `s²_OS = 3N_h/(1 + f)`, `M_W = v(πα/((1 − f)s²_OS))^{1/2}`, `M_Z = M_W/(1 − s²_OS)^{1/2}` and `G_F`, each to the
  digits the proposition prints.
* `weak_composition` (**Proposition 68**): `G_F m_p² = (9/10) W_W/M²` with `N_h` summed at the clock's `h`.
* `seesaw_root`, `neutrino_seesaw`, `seesaw_ratio`, `neutrinos` (**Proposition 123**; S123): the roots of
  `x(X_R + x) = δ²`, the masses `0`, `8.6126720` and `50.198331` meV, `m₂/m₃ = ρ` to `10⁻²⁶`,
  `ρ⁻² = 17 + 12√2`, `Σ m = 0.0588110` eV.
* `neutrino_sum_beside_bounds` (**Proposition 187**): the splittings `7.4178·10⁻⁵` and `2.5199·10⁻³` eV² at `+0.38`
  and `+0.40` standard deviations, the least sum `0.05869(26)` eV, the bound `0.081` above the sum and `0.055` lying `0.0037` below
  the least sum.
* `deuteron` (**Proposition 124**; S124, Eq. (40) of the public edition): the binding as a composition and to its
  digits, `m_d/m_p`, the pole matrix with `g = 7/18`, `P_D = 2/51`, and `μ_d` in both forms and to its digits.
* `crossed_plane` (**Proposition 50**): `b + w_C = 7/16 + i`, `w_C = i`, `δ_q = arg(7 + 16i) = π/2 − arctan(7/16)
  = 1.15839`, and `−1.15839` with the other orientation.
* `line_factor` (**Proposition 51**): `1 + 3u + 4u²` is `2` at `u = 1/4`, `(3/4)(1 + i)` at `u = i/4` with phase
  `π/4`, `tan²(π/8) = 3 − 2√2 = 0.171573`, and real and positive at every even divided set.
* `echoes` (**Proposition 97**): `tanh log 2 = 3/5`, `tanh(log 2/2) = 1/3`, `tanh(log 2/4) = 3 − 2√2`.
-/

namespace Comparison.Article

open Real

/-! ## Proposition 119: the electroweak poles -/

/-- **Proposition 119.** The electroweak poles, each to the digits the proposition prints. -/
theorem electroweak_poles :
    qSw = 3 * qNh ∧ qOsw = qSw / (1 + 9 / 250) ∧
      qMw = qV * √(π * qAlpha / ((1 - 9 / 250) * qOsw)) ∧ qMz = qMw / √(1 - qOsw) ∧
      qGF = (9 / 10) * qWW / 296 ^ 2 / (qMp / 1000) ^ 2 ∧
      ((0.23125752165 : ℝ) < qSw ∧ qSw < 0.23125752175) ∧
      ((0.23155023385 : ℝ) < 3 * qNcon ∧ 3 * qNcon < 0.23155023395) ∧
      ((0.22322154595 : ℝ) < qOsw ∧ qOsw < 0.22322154605) ∧
      ((80.366251035 : ℝ) < qMw ∧ qMw < 80.366251045) ∧
      ((91.185361515 : ℝ) < qMz ∧ qMz < 91.185361525) ∧
      ((1.166378855e-5 : ℝ) < qGF ∧ qGF < 1.166378865e-5) := by
  refine ⟨rfl, ?_, ?_, rfl, ?_, qSw_bnd.strict (by norm_num) (by norm_num), ?_,
    qOsw_bnd.strict (by norm_num) (by norm_num), qMw_bnd.strict (by norm_num) (by norm_num),
    qMz_bnd.strict (by norm_num) (by norm_num), qGF_bnd.strict (by norm_num) (by norm_num)⟩
  · rw [qOsw]; norm_num
  · rw [qMw]; norm_num
  · rw [qGF, qGFmp2]; norm_num
  · have h := rowD09_bnd
    rw [rowD09] at h
    exact h.strict (by norm_num) (by norm_num)

/-- **Proposition 68: the weak composition.** `G_F m_p² = (9/10) W_W/M²`, `M = 296`, with the repeated returns
`N_h` summed at the overlap `h` of the clock at `{h, n}`. -/
theorem weak_composition :
    qGFmp2 = (9 / 10) * qWW / 296 ^ 2 ∧ qNh = NhOf (Comparison.Law.hOv Comparison.Law.sLastDirectionSinglet) ∧
      ((1.0268265e-5 : ℝ) < qGFmp2 ∧ qGFmp2 < 1.0268275e-5) := by
  refine ⟨by rw [qGFmp2]; norm_num, by rw [hOv_eq]; rfl, qGFmp2_bnd.strict (by norm_num) (by norm_num)⟩

/-! ## Proposition 123: the neutrinos -/

/-- The nonnegative root of `x(X + x) = d²`. -/
noncomputable def seesawX (X d : ℝ) : ℝ := 2 * d ^ 2 / (X + √(X ^ 2 + 4 * d ^ 2))

/-- **The seesaw root:** `x = 2d²/(X + (X² + 4d²)^{1/2})` is the one nonnegative root of `x(X + x) = d²`. -/
theorem seesaw_root {X d : ℝ} (hX : 0 < X) :
    0 ≤ seesawX X d ∧ seesawX X d * (X + seesawX X d) = d ^ 2 ∧
      ∀ y : ℝ, 0 ≤ y → y * (X + y) = d ^ 2 → y = seesawX X d := by
  set s := √(X ^ 2 + 4 * d ^ 2) with hs
  have hs2 : s ^ 2 = X ^ 2 + 4 * d ^ 2 := by rw [hs, Real.sq_sqrt (by positivity)]
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsX : X ≤ s := by
    rw [hs]; exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg d])
  have hpos : 0 < X + s := by linarith
  have hx : seesawX X d = (s - X) / 2 := by
    rw [seesawX, ← hs, div_eq_div_iff hpos.ne' (by norm_num)]
    nlinarith [hs2]
  have hroot : seesawX X d * (X + seesawX X d) = d ^ 2 := by
    rw [hx]; nlinarith [hs2]
  refine ⟨by rw [hx]; linarith, hroot, fun y hy hy2 => ?_⟩
  have hx0 : 0 ≤ seesawX X d := by rw [hx]; linarith
  have h : (y - seesawX X d) * (y + seesawX X d + X) = 0 := by nlinarith [hroot, hy2]
  rcases mul_eq_zero.mp h with h | h
  · linarith
  · nlinarith

theorem seesawX_zero (X : ℝ) : seesawX X 0 = 0 := by simp [seesawX]

/-- The masses `m₂`, `m₃` (in eV) are the seesaw roots at `X_R = M_R/m_p` and `δ₂ = ρ^{1/2} δ₃`,
`δ₃ = σ (v/m_p)/√2`. -/
theorem qM2_seesaw : qM2 = seesawX qXR qY2 * qMp * 1000000 := by
  rw [qM2, seesawX]; ring_nf

theorem qM3_seesaw : qM3 = seesawX qXR qY3 * qMp * 1000000 := by
  rw [qM3, seesawX]; ring_nf

theorem qXR_pos : 0 < qXR := lt_of_lt_of_le (by norm_num) qXR_bnd.1
theorem qMp_pos' : 0 < qMp := lt_of_lt_of_le (by norm_num) qMp_bnd.1
theorem qYfac_pos : 0 < qYfac := lt_of_lt_of_le (by norm_num) qYfac_bnd.1
theorem qRho_pos : 0 < qRho := lt_of_lt_of_le (by norm_num) qRho_bnd.1

/-- **The neutral roots:** `x_i(X_R + x_i) = δ_i²` for the three neutral lines, `δ = (0, ρ^{1/2}, 1) δ₃`. -/
theorem neutrino_seesaw :
    seesawX qXR 0 = 0 ∧
      (qM2 / (qMp * 1000000)) * (qXR + qM2 / (qMp * 1000000)) = qY2 ^ 2 ∧
      (qM3 / (qMp * 1000000)) * (qXR + qM3 / (qMp * 1000000)) = qY3 ^ 2 ∧
      qY2 = √qRho * qY3 := by
  have hm : qMp * 1000000 ≠ 0 := by have := qMp_pos'; positivity
  have e2 : qM2 / (qMp * 1000000) = seesawX qXR qY2 := by
    rw [qM2_seesaw, div_eq_iff hm]; ring
  have e3 : qM3 / (qMp * 1000000) = seesawX qXR qY3 := by
    rw [qM3_seesaw, div_eq_iff hm]; ring
  refine ⟨seesawX_zero _, ?_, ?_, ?_⟩
  · rw [e2]; exact (seesaw_root qXR_pos).2.1
  · rw [e3]; exact (seesaw_root qXR_pos).2.1
  · rw [qY2, qY3]; ring

/-- **`m₂/m₃ = ρ` up to `ρ(1 − ρ)δ₃²/X_R²`:** the ratio of the two seesaw roots with `δ₂² = ρ δ₃²`. -/
theorem seesaw_ratio {X y ρ : ℝ} (hX : 0 < X) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hy : y ≠ 0) :
    0 ≤ seesawX X (√ρ * y) / seesawX X y - ρ ∧
      seesawX X (√ρ * y) / seesawX X y - ρ ≤ ρ * (1 - ρ) * y ^ 2 / X ^ 2 := by
  have e2 : (√ρ * y) ^ 2 = ρ * y ^ 2 := by rw [mul_pow, Real.sq_sqrt hρ0]
  have hy2 : 0 < y ^ 2 := by positivity
  set s2 := √(X ^ 2 + 4 * (ρ * y ^ 2)) with hs2
  set s3 := √(X ^ 2 + 4 * y ^ 2) with hs3
  have hs2sq : s2 ^ 2 = X ^ 2 + 4 * (ρ * y ^ 2) := by rw [hs2, Real.sq_sqrt (by positivity)]
  have hs3sq : s3 ^ 2 = X ^ 2 + 4 * y ^ 2 := by rw [hs3, Real.sq_sqrt (by positivity)]
  have hs2X : X ≤ s2 := by rw [hs2]; exact Real.le_sqrt_of_sq_le (by nlinarith)
  have hs3X : X ≤ s3 := by rw [hs3]; exact Real.le_sqrt_of_sq_le (by nlinarith)
  have hs23 : s2 ≤ s3 := Real.sqrt_le_sqrt (by nlinarith)
  have hp2 : 0 < X + s2 := by linarith
  have hp3 : 0 < X + s3 := by linarith
  have hratio : seesawX X (√ρ * y) / seesawX X y - ρ = ρ * (s3 - s2) / (X + s2) := by
    rw [seesawX, seesawX, e2, ← hs2, ← hs3]
    field_simp
    ring
  rw [hratio]
  have hdiff : (s3 - s2) * (2 * X) ≤ 4 * (1 - ρ) * y ^ 2 := by nlinarith
  constructor
  · apply div_nonneg _ hp2.le
    exact mul_nonneg hρ0 (by linarith)
  · rw [div_le_div_iff₀ hp2 (by positivity)]
    have h1 : (s3 - s2) * X ≤ 2 * (1 - ρ) * y ^ 2 := by nlinarith
    have h2 : (s3 - s2) * X ^ 2 ≤ (1 - ρ) * y ^ 2 * (X + s2) := by
      have h3 : 0 ≤ (1 - ρ) * y ^ 2 := mul_nonneg (by linarith) hy2.le
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h2 hρ0]

/-- **`ρ⁻² = (3 + 2√2)² = 17 + 12√2`** with `ρ = 3 − 2√2 = tan²(π/8)`. -/
theorem rho_inv_sq : qRho = Real.tan (π / 8) ^ 2 ∧ qRho⁻¹ = 3 + 2 * √2 ∧ (qRho ^ 2)⁻¹ = 17 + 12 * √2 := by
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : qRho ≠ 0 := qRho_pos.ne'
  have hinv : qRho⁻¹ = 3 + 2 * √2 := by
    apply inv_eq_of_mul_eq_one_right
    rw [qRho]; linear_combination (-4) * h2
  refine ⟨by rw [Comparison.ArticleStatements.Radar.tan_sq_pi_div_eight, qRho], hinv, ?_⟩
  rw [← inv_pow, hinv]; linear_combination 4 * h2

/-- **Proposition 123: the neutrinos.** The roots, the masses `0`, `8.6126720` and `50.198331` meV,
`m₂/m₃ = ρ` to `2·10⁻²⁶`, `ρ = tan²(π/8)`, `ρ⁻² = 17 + 12√2`, and `Σ m = 0.0588110` eV. -/
theorem neutrinos :
    ((8.61267195 : ℝ) < qM2meV ∧ qM2meV < 8.61267205) ∧
      ((50.1983305 : ℝ) < qM3meV ∧ qM3meV < 50.1983315) ∧
      (0 ≤ qM2 / qM3 - qRho ∧ qM2 / qM3 - qRho < 2e-26) ∧
      qRho = Real.tan (π / 8) ^ 2 ∧ (qRho ^ 2)⁻¹ = 17 + 12 * √2 ∧
      ((0.05881095 : ℝ) < qSumNu ∧ qSumNu < 0.05881105) := by
  have hm : qMp * 1000000 ≠ 0 := by have := qMp_pos'; positivity
  have hratio : qM2 / qM3 = seesawX qXR (√qRho * qY3) / seesawX qXR qY3 := by
    rw [qM2_seesaw, qM3_seesaw, mul_assoc, mul_assoc, mul_div_mul_right _ _ hm,
      show qY2 = √qRho * qY3 by rw [qY2, qY3, mul_comm]]
  have hr := seesaw_ratio qXR_pos qRho_pos.le (le_trans qRho_bnd.2 (by norm_num)) (qYfac_pos.ne' : qYfac ≠ 0)
  rw [show qYfac = qY3 by rw [qY3]] at hr
  have hb : qRho * (1 - qRho) * qY3 ^ 2 / qXR ^ 2 < 2e-26 := by
    have h1 := Bnd.sub (Bnd.const 1) qRho_bnd
    have h2 := Bnd.mul qRho_bnd h1 (by norm_num) (by norm_num)
    have h3 := Bnd.pow (show Bnd qY3 _ _ from qYfac_bnd) (by norm_num) 2
    have h4 := Bnd.mul h2 h3 (by norm_num) (by norm_num)
    have h5 := Bnd.pow qXR_bnd (by norm_num) 2
    have h6 := Bnd.div h4 h5 (by norm_num) (by norm_num)
    exact lt_of_le_of_lt h6.2 (by norm_num)
  refine ⟨qM2meV_digits, qM3meV_digits, ⟨?_, ?_⟩, rho_inv_sq.1, rho_inv_sq.2.2, qSumNu_digits⟩
  · rw [hratio]; exact hr.1
  · rw [hratio]; exact lt_of_le_of_lt hr.2 hb

/-! ## Proposition 187: the neutrino mass sum beside the newest cosmic bound -/

/-- **Proposition 187.** With `m₁ = 0` the splittings are `m₂² = 7.4178·10⁻⁵` and `m₃² = 2.5199·10⁻³` eV², at
`+0.38` and `+0.40` standard deviations of JUNO 2026 (`7.388(78)·10⁻⁵`, `2.509(+27)·10⁻³`); the least sum the measured
splittings allow is `0.05869(26)` eV; the bound `0.081` eV stands above `Σ m_ν`, and the bound `0.055` eV lies
`0.0037` eV below the least sum. -/
theorem neutrino_sum_beside_bounds :
    ((7.41775e-5 : ℝ) < qM2 ^ 2 ∧ qM2 ^ 2 < 7.41785e-5) ∧
      ((2.51985e-3 : ℝ) < qM3 ^ 2 ∧ qM3 ^ 2 < 2.51995e-3) ∧
      ((0.375 : ℝ) < (qM2 ^ 2 - 7.388e-5) / 0.078e-5 ∧ (qM2 ^ 2 - 7.388e-5) / 0.078e-5 < 0.385) ∧
      ((0.395 : ℝ) < (qM3 ^ 2 - 2.509e-3) / 0.027e-3 ∧ (qM3 ^ 2 - 2.509e-3) / 0.027e-3 < 0.405) ∧
      qLeastSum = √7.388e-5 + √2.509e-3 ∧
      ((0.058685 : ℝ) < qLeastSum ∧ qLeastSum < 0.058695) ∧
      ((0.000255 : ℝ) < qLeastWidth ∧ qLeastWidth < 0.000265) ∧
      qSumNu < 0.081 ∧ qBelowLeast = qLeastSum - 0.055 ∧
      ((0.00365 : ℝ) < qBelowLeast ∧ qBelowLeast < 0.00375) := by
  have h2 := Bnd.pow qM2_bnd (by norm_num) 2
  have h3 := Bnd.pow qM3_bnd (by norm_num) 2
  refine ⟨h2.strict (by norm_num) (by norm_num), h3.strict (by norm_num) (by norm_num), ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    by rw [qLeastSum]; norm_num, qLeastSum_digits, qLeastWidth_digits,
    lt_trans qSumNu_digits.2 (by norm_num), by rw [qBelowLeast]; norm_num, qBelowLeast_digits⟩
  · rw [lt_div_iff₀ (by norm_num)]; have := h2.1; norm_num at this ⊢; linarith
  · rw [div_lt_iff₀ (by norm_num)]; have := h2.2; norm_num at this ⊢; linarith
  · rw [lt_div_iff₀ (by norm_num)]; have := h3.1; norm_num at this ⊢; linarith
  · rw [div_lt_iff₀ (by norm_num)]; have := h3.2; norm_num at this ⊢; linarith

/-! ## Proposition 124: the deuteron -/

/-- **Proposition 124: the deuteron.** `u_B = B_d/m_p = χ_A^{1/2} a³ [1 − (1 − k₃) ε₂]` with `χ_A = 13/12` and
`1 − k₃ = 41/40`, `B_d = 2.2245664631` MeV; `m_d/m_p = 1 + m_n/m_p − u_B = 1.99900750127`; the pole matrix at
`g = α_s²/Ψ₁ = 7/18` has the poles `−2/9` and `49/9`, and the D share at the low pole is `P_D = 2/51`;
`μ_d = (16μ_S + g_L)/17 − u_B(μ_S − g_L)/(20 + 13u_B) = 0.857438233519`. -/
theorem deuteron :
    qBd / qMp = √(1 / (1 + (Comparison.Law.PhiS Comparison.Law.sC).re)) *
        (Comparison.Law.aS Comparison.Law.sHere).re ^ 3 *
        (1 - (1 + Comparison.Law.tS Comparison.Law.sHere / 16) * qEps2) ∧
      1 / (1 + (Comparison.Law.PhiS Comparison.Law.sC).re) = 13 / 12 ∧
      1 + Comparison.Law.tS Comparison.Law.sHere / 16 = 41 / 40 ∧
      ((2.22456646305 : ℝ) < qBd ∧ qBd < 2.22456646315) ∧
      qMd / qMp = 1 + qMn / qMp - qBd / qMp ∧
      ((1.999007501265 : ℝ) < qMd / qMp ∧ qMd / qMp < 1.999007501275) ∧
      gD = 7 / 18 ∧ deutM.mulVec vLow = (-2 / 9 : ℝ) • vLow ∧ deutM.mulVec vHigh = (49 / 9 : ℝ) • vHigh ∧
      deutD_share = 2 / 51 ∧
      qMud = (16 * qMus + qGl) / 17 - qUB * (qMus - qGl) / (20 + 13 * qUB) ∧
      qMus = qMup + qMun ∧ qGl = qMn / (qMp + qMn) ∧ qUB = qBd / qMp ∧
      ((0.8574382335185 : ℝ) < qMud ∧ qMud < 0.8574382335195) := by
  have hm : qMp ≠ 0 := qMp_pos'.ne'
  refine ⟨uB_composition, chiA_eq, one_sub_k3, rowG10_digits, ?_, rowG12_digits, gD_eq,
    deutM_eigen.1, deutM_eigen.2.1, deutD_share_eq, by rw [qMud], rfl, rfl, rfl, rowG13_digits⟩
  rw [qMd]; field_simp

/-! ## Proposition 50: the complex weight -/

/-- **Proposition 50: the complex weight.** `b + w_C = 7/16 + i` with `w_C = i`; `δ_q = arg(7 + 16i) =
arctan(16/7) = π/2 − arctan(7/16) = 1.15839`, and with the other orientation `w = −i`, `−1.15839`. -/
theorem crossed_plane :
    Comparison.Law.wS Comparison.Law.sC = Complex.I ∧
      Comparison.Law.bS Comparison.Law.sHere + Comparison.Law.wS Comparison.Law.sC = 7 / 16 + Complex.I ∧
      deltaQ = Complex.arg (7 + 16 * Complex.I) ∧ deltaQ = Real.arctan (16 / 7) ∧ deltaQ = qDeltaQ5 ∧
      ((1.158385 : ℝ) < deltaQ ∧ deltaQ < 1.158395) ∧
      Complex.arg (7 / 16 - Complex.I) = -deltaQ := by
  have hb : Comparison.Law.bS Comparison.Law.sHere = 7 / 16 := by
    have := Comparison.Law.piece_b_here
    simpa using this
  have harg : Complex.arg (7 + 16 * Complex.I) = Real.arctan (16 / 7) := by
    rw [arg_eq_arctan (by simp)]
    congr 1
    simp
  have hq : deltaQ = qDeltaQ5 := by
    rw [deltaQ_eq_arg, harg, qDeltaQ5, show (16 / 7 : ℝ) = (7 / 16)⁻¹ by norm_num,
      Real.arctan_inv_of_pos (by norm_num)]
  refine ⟨wC_eq, by rw [wC_eq, hb], deltaQ_eq_arg, by rw [deltaQ_eq_arg, harg], hq,
    by rw [hq]; exact qDeltaQ5_digits, ?_⟩
  have hc : (7 / 16 - Complex.I : ℂ) = (starRingEnd ℂ) (7 / 16 + Complex.I) := by
    apply Complex.ext
    · rw [Complex.conj_re]; simp
    · rw [Complex.conj_im]; simp
  rw [hc, Complex.arg_conj]
  have hpi : Complex.arg (7 / 16 + Complex.I) ≠ π := by
    rw [Ne, Complex.arg_eq_pi_iff]; norm_num
  simp only [hpi, ↓reduceIte]
  rw [deltaQ, wC_eq, hb]

/-! ## Proposition 51: the line factor at the last-step direction's phase -/

/-- The factor of the law on the vector states. -/
def lineFactor (u : ℂ) : ℂ := 1 + 3 * u + 4 * u ^ 2

/-- **Proposition 51: the line factor at the last-step direction's phase.** `1 + 3u + 4u²` is `2` at `u = 1/4` and
`(3/4)(1 + i)` at `u = i/4`, of phase `π/4` (half phase `π/8`); `tan²(π/8) = 3 − 2√2 = 0.171573`; at every even
divided set (`u = i^{|S|}/4`, `|S|` even) it is real and positive. -/
theorem line_factor :
    lineFactor (1 / 4) = 2 ∧ lineFactor (Complex.I / 4) = 3 / 4 * (1 + Complex.I) ∧
      Complex.arg (lineFactor (Complex.I / 4)) = π / 4 ∧
      Real.tan (π / 8) ^ 2 = 3 - 2 * √2 ∧ ((0.1715725 : ℝ) < 3 - 2 * √2 ∧ 3 - 2 * √2 < 0.1715735) ∧
      ∀ m : ℕ, (lineFactor (Complex.I ^ (2 * m) / 4)).im = 0 ∧ 0 < (lineFactor (Complex.I ^ (2 * m) / 4)).re := by
  have hI : lineFactor (Complex.I / 4) = 3 / 4 * (1 + Complex.I) := by
    rw [lineFactor]; ring_nf; rw [Complex.I_sq]; ring
  refine ⟨by rw [lineFactor]; norm_num, hI, ?_, Comparison.ArticleStatements.Radar.tan_sq_pi_div_eight, ?_, ?_⟩
  · rw [hI, arg_eq_arctan (by simp)]
    have : (3 / 4 * (1 + Complex.I)).im / (3 / 4 * (1 + Complex.I)).re = 1 := by simp
    rw [this, Real.arctan_one]
  · have h := qRho_bnd
    rw [qRho] at h
    exact h.strict (by norm_num) (by norm_num)
  · intro m
    have hp : Complex.I ^ (2 * m) = ((-1 : ℝ) ^ m : ℝ) := by
      rw [pow_mul, Complex.I_sq]; push_cast; ring
    rw [hp, lineFactor]
    rcases neg_one_pow_eq_or ℝ m with h | h <;> rw [h] <;> norm_num

/-! ## Proposition 97: the reflections are radar steps -/

theorem tanh_eq (x : ℝ) : Real.tanh x = (Real.exp (2 * x) - 1) / (Real.exp (2 * x) + 1) := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have h1 : Real.exp (2 * x) = Real.exp x * Real.exp x := by rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp (-x) = (Real.exp x)⁻¹ := Real.exp_neg x
  have hx : 0 < Real.exp x := Real.exp_pos x
  rw [h1, h2]
  field_simp

/-- **Proposition 97: the reflections are radar steps.** `tanh log 2 = 3/5`, `tanh(log 2/2) = 1/3`,
`tanh(log 2/4) = 3 − 2√2 = tan²(π/8)`. -/
theorem echoes :
    Real.tanh (Real.log 2) = 3 / 5 ∧ Real.tanh (Real.log 2 / 2) = 1 / 3 ∧
      Real.tanh (Real.log 2 / 4) = 3 - 2 * √2 ∧ 3 - 2 * √2 = Real.tan (π / 8) ^ 2 := by
  have e1 : Real.exp (2 * Real.log 2) = 4 := by
    rw [show 2 * Real.log 2 = Real.log 4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring]
    exact Real.exp_log (by norm_num)
  have e2 : Real.exp (2 * (Real.log 2 / 2)) = 2 := by
    rw [show 2 * (Real.log 2 / 2) = Real.log 2 by ring]; exact Real.exp_log (by norm_num)
  have e4 : Real.exp (2 * (Real.log 2 / 4)) = √2 := by
    rw [show 2 * (Real.log 2 / 4) = Real.log 2 / 2 by ring, Real.sqrt_eq_rpow, Real.rpow_def_of_pos (by norm_num)]
    ring_nf
  have h2 : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  refine ⟨by rw [tanh_eq, e1]; norm_num, by rw [tanh_eq, e2]; norm_num, ?_,
    Comparison.ArticleStatements.Radar.tan_sq_pi_div_eight.symm⟩
  rw [tanh_eq, e4]
  have hp : 0 < √2 + 1 := by positivity
  rw [div_eq_iff hp.ne']
  nlinarith [h2]

end Comparison.Article
