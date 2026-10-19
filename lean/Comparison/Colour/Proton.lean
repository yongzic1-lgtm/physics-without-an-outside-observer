module

public import Mathlib

/-!
# Book XIV. The proton's pole and gravity hung on it (Propositions 82, 83): the numbers

**Prop. 82.** `protonPole = 6M + C_h + (1/6) log(5/2) − a⁵ − b a⁶` with `M = 296`, `C_h = 60`,
`a = 5/38`, `b = 7/16`.
* `log_five_halves`: `log(5/2)` within `1.5·10⁻¹⁰` of `S₁₄ + 287209/414355`, from Mathlib's bound on
  `log 2` (`Real.log_two_near_10`) and fourteen terms of `−log(1 − 1/5) = Σ 5^{−i}/i`.
* `protonPole_bounds`: `1836.152673412 < m_p/m_e < 1836.1526734121`;
  `protonPole_pull`: against CODATA 2022's `1836.152673426(32)` the pull lies in `(−0.44, −0.43)`.
* `pole_terms`: `a⁵ = 3125/79235168`, `ba⁶ = 109375/48174982144`.

**Prop. 83.** `W = (t^{Eℓ}η^{E_H})³` with `t = 2/5`, `Eℓ = 16`, `η = 295/296`, `E_H = 3`.
* `W_eq`: `W = (2/5)⁴⁸(295/296)⁹`; `alphaG_eq`: `α_G = W² = (2/5)⁹⁶(295/296)¹⁸`, a rational number;
  `alphaG_bounds`: `5.9061524937·10⁻³⁹ < α_G < 5.9061524938·10⁻³⁹`.
* `gravity_pull`: against `G m_p²/(ħc)` with CODATA 2022's `G = 6.67430(15)·10⁻¹¹`,
  `m_p = 1.67262192595·10⁻²⁷ kg`, `ħ = 1.054571817·10⁻³⁴ J s`, `c = 299792458 m/s` (inputs), the pull lies in `(0.0230, 0.0231)`.
* `gravity_logs`: `−log W = 3Eℓ log(1/t) + 3E_H log(1/η) = 48 log(5/2) + 9 log(296/295)`,
  `48 log(5/2) = 288 h_p`, `288 = L(Ω)·3Eℓ`; `planck_from_proton`:
  `−log W = 288(m_p/m_e − 6M − C_h + a⁵ + ba⁶) + 9 log(296/295)`.
* `planck_mass`: `M_Pl = m_p/W` lies in `(1.22088981, 1.22088982)·10¹⁹ GeV` with
  `m_p = 938.27208943 MeV`.
-/

@[expose] public section

namespace Comparison

/-! ## Prop. 82 -/

/-- The fourteen-term partial sum of `−log(1 − 1/5) = log(5/4)`. -/
theorem log_five_fourths_sum :
    (∑ i ∈ Finset.range 14, (1 / 5 : ℝ) ^ (i + 1) / (i + 1)) =
      98159192078393 / 439892578125000 := by
  norm_num [Finset.sum_range_succ]

/-- **`log(5/2)` to `1.5·10⁻¹⁰`.** -/
theorem log_five_halves :
    (98159192078393 / 439892578125000 : ℝ) + 287209 / 414355 - 1 / 10 ^ 10 - 4096 / 10 ^ 14 -
          1 / 10 ^ 15 < Real.log (5 / 2) ∧
      Real.log (5 / 2) <
        98159192078393 / 439892578125000 + 287209 / 414355 + 1 / 10 ^ 10 + 4096 / 10 ^ 14 +
          1 / 10 ^ 15 := by
  have h2 := Real.log_two_near_10
  have hs := Real.abs_log_sub_add_sum_range_le (x := (1 / 5 : ℝ)) (by norm_num) 14
  rw [log_five_fourths_sum] at hs
  have e : Real.log (5 / 2) = Real.log 2 - Real.log (1 - 1 / 5) := by
    rw [← Real.log_div (x := 2) (y := 1 - 1 / 5) (by norm_num) (by norm_num)]
    norm_num
  have ht : |(1 / 5 : ℝ)| ^ (14 + 1) / (1 - |(1 / 5 : ℝ)|) = 4096 / 10 ^ 14 := by
    norm_num [abs_of_pos]
  rw [ht] at hs
  rw [abs_le] at h2 hs
  obtain ⟨h2a, h2b⟩ := h2
  obtain ⟨hsa, hsb⟩ := hs
  rw [e]
  constructor <;> linarith

/-- **The proton's pole:** `6M + C_h + (1/6) log(5/2) − a⁵ − b a⁶`. -/
noncomputable def protonPole : ℝ :=
  6 * 296 + 60 + (1 / 6) * Real.log (5 / 2) - (5 / 38) ^ 5 - (7 / 16) * (5 / 38) ^ 6

theorem pole_terms : ((5 : ℚ) / 38) ^ 5 = 3125 / 79235168 ∧
    (7 / 16 : ℚ) * (5 / 38) ^ 6 = 109375 / 48174982144 ∧ (6 * 296 + 60 : ℕ) = 1836 := by
  norm_num

/-- **`1836.152673412 < m_p/m_e < 1836.1526734121`.** -/
theorem protonPole_bounds : (1836.152673412 : ℝ) < protonPole ∧ protonPole < 1836.1526734121 := by
  obtain ⟨hl, hu⟩ := log_five_halves
  unfold protonPole
  constructor <;> norm_num <;> linarith

/-- **The pull against CODATA 2022's `1836.152673426(32)` lies in `(−0.44, −0.43)`.** -/
theorem protonPole_pull :
    (-0.44 : ℝ) < (protonPole - 1836.152673426) / 0.000000032 ∧
      (protonPole - 1836.152673426) / 0.000000032 < -0.43 := by
  obtain ⟨hl, hu⟩ := log_five_halves
  have hw : (0 : ℝ) < 0.000000032 := by norm_num
  rw [lt_div_iff₀ hw, div_lt_iff₀ hw]
  unfold protonPole
  constructor <;> norm_num <;> linarith

/-! ## Prop. 83 -/

/-- The gravitational amplitude `W = (t^{Eℓ}η^{E_H})³`. -/
def Wgrav : ℚ := ((2 / 5) ^ 16 * (295 / 296) ^ 3) ^ 3

/-- `α_G = W²`. -/
def alphaG : ℚ := Wgrav ^ 2

theorem W_eq : Wgrav = (2 / 5) ^ 48 * (295 / 296) ^ 9 := by
  rw [Wgrav]
  ring

theorem alphaG_eq : alphaG = (2 / 5) ^ 96 * (295 / 296) ^ 18 := by
  rw [alphaG, W_eq]
  ring

/-- **`5.9061524937·10⁻³⁹ < α_G < 5.9061524938·10⁻³⁹`.** -/
theorem alphaG_bounds : (5.9061524937e-39 : ℚ) < alphaG ∧ alphaG < 5.9061524938e-39 := by
  rw [alphaG_eq]
  norm_num

/-- The record: `G m_p²/(ħc)` with CODATA 2022's `G`, `m_p`, `ħ`, `c` (an input). -/
def alphaGrec : ℚ := 6.67430e-11 * (1.67262192595e-27) ^ 2 / (1.054571817e-34 * 299792458)

/-- Its width from `G`'s `0.00015·10⁻¹¹`. -/
def alphaGwid : ℚ := alphaGrec * (0.00015 / 6.67430)

/-- **The pull of `α_G = W²` against the record lies in `(0.0230, 0.0231)`.** -/
theorem gravity_pull :
    (0.0230 : ℚ) < (alphaG - alphaGrec) / alphaGwid ∧
      (alphaG - alphaGrec) / alphaGwid < 0.0231 := by
  rw [alphaG_eq, alphaGwid, alphaGrec]
  norm_num

/-- **The logarithms:** `−log W = 3Eℓ log(1/t) + 3E_H log(1/η) = 48 log(5/2) + 9 log(296/295)`;
`48 log(5/2) = 288 h_p` with `h_p = (1/6) log(5/2)`; `288 = L(Ω)·3Eℓ`. -/
theorem gravity_logs :
    -Real.log ((2 / 5 : ℝ) ^ 48 * (295 / 296) ^ 9) =
        3 * 16 * Real.log (1 / (2 / 5)) + 3 * 3 * Real.log (1 / (295 / 296)) ∧
      3 * 16 * Real.log (1 / (2 / 5 : ℝ)) + 3 * 3 * Real.log (1 / (295 / 296)) =
        48 * Real.log (5 / 2) + 9 * Real.log (296 / 295) ∧
      48 * Real.log (5 / 2) = 288 * ((1 / 6) * Real.log (5 / 2)) ∧ (288 : ℕ) = 6 * (3 * 16) := by
  refine ⟨?_, ?_, ?_, by norm_num⟩
  · rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      one_div, Real.log_inv, one_div, Real.log_inv]
    push_cast
    ring
  · norm_num
  · ring

/-- **Gravity on the proton's pole:**
`−log W = 288(m_p/m_e − 6M − C_h + a⁵ + ba⁶) + 9 log(296/295)`. -/
theorem planck_from_proton :
    -Real.log ((2 / 5 : ℝ) ^ 48 * (295 / 296) ^ 9) =
      288 * (protonPole - (6 * 296 + 60) + (5 / 38) ^ 5 + (7 / 16) * (5 / 38) ^ 6) +
        9 * Real.log (296 / 295) := by
  obtain ⟨h1, h2, -, -⟩ := gravity_logs
  rw [h1, h2, protonPole]
  ring

/-- **The Planck mass `M_Pl = m_p/W`** with `m_p = 938.27208943 MeV`, in GeV:
`1.22088981·10¹⁹ < M_Pl < 1.22088982·10¹⁹`. -/
theorem planck_mass :
    (1.22088981e19 : ℚ) < 938.27208943 / Wgrav / 1000 ∧
      938.27208943 / Wgrav / 1000 < 1.22088982e19 := by
  rw [W_eq]
  norm_num

end Comparison

end
