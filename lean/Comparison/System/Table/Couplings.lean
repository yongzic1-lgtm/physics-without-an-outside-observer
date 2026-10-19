import Comparison.System.Completion.Numbers

set_option linter.style.longLine false

/-!
# The proof system, the table, part 2: the couplings and the last-step direction

Rows D01 to D05, D08 to D17, L15, L19, L20, S07, S16, T01, T02 of Table X, each defined as
its composition in the law's numbers and proved equal to its closed form, with the interval of its printed digits
(through intervals, `Article/RowsCouplings.lean`).

Recognitions: D01 the strong coupling `α_s(M_Z)`, D02 the inverse electric coupling `1/α`, D03 the Fermi coefficient
`G_F` [10⁻⁵ GeV⁻²], D04 the gravitational coupling `Gm_p²/ħc` [10⁻³⁹], D05 the Planck mass [10¹⁹ GeV], D08 the
MS-bar weak angle, D09 the effective weak angle, D10 the on-shell weak angle, D11 and L15 the W mass [GeV], D12 the
Z mass [GeV], D13 `M_W/M_Z`, D14 the weak correction `δ_inv`, D15 the electroweak scale `v` [GeV], D16 the scalar
(Higgs) mass [GeV], D17 the top mass [GeV], L19 and L20 the clock-independent bounds on `1/α` and the weak angle,
S07 the top mass second construction [GeV], S16 the five-flavour one-loop scale marker [MeV], T01 the heavy neutral
threshold `M_R` [GeV], T02 the heavy plane-changing threshold `M_off` [GeV]. The meeting rule `σ = e²/N` (Prop. 64), the
contact retained once (Prop. 65), the weak retained excursion (Prop. 68) and the vector poles (Prop. 119) are the theory's
compositions, each proved as its proposition (Props. 64 and 65 in `Completion/Constants.lean`, Prop. 68 in
`Completion/Whole.lean`, Prop. 119 in `Completion/Spectrum.lean`). T01 and T02 are `M_Pl det(G⁻¹H)` and
`M_Pl det_ℂ(G_off⁻¹H_off)`: the coherent comparison pulled back by the exterior representation to the kept algebra, of
real dimension nine, and to `Hom_ℂ(F, C)`, of complex dimension six (`Num.neutralR`, `Num.neutralOff`,
`Completion/Ext/Neutral.lean`). Outside inputs: `m_e c²` (the unit), the one-loop `β₀ = 23/3` of S16.
-/

namespace Comparison.System.Table

open Real Complex Matrix Comparison Comparison.Law Comparison.System.Completion

namespace Row

/-- D01, `α_s = k₄/(k₂(k_C² − 1)^{1/2})`. -/
noncomputable def D01 : ℝ := Num.alphaS
/-- D02, `1/α = N₂(1 − x)k₀²/(c_L k₂²)`. -/
noncomputable def D02 : ℝ := (Num.N2 : ℝ) * (1 - Num.x) * Num.k 0 ^ 2 / (Num.cL * Num.k 2 ^ 2)
/-- D03, `G_F = (1 − 1/N₂)W_W/(M²m_p²)` in units of `10⁻⁵ GeV⁻²`. -/
noncomputable def D03 : ℝ := Num.GF * 100000
/-- D04, `W²` in units of `10⁻³⁹`. -/
noncomputable def D04 : ℝ := Num.W ^ 2 * 10 ^ 39
/-- D05, `m_p/W` in units of `10¹⁹ GeV`. -/
noncomputable def D05 : ℝ := Num.MPl / 10 ^ 19
/-- D08, `3N_h`. -/
noncomputable def D08 : ℝ := Num.sw2
/-- D09, `3N_con`. -/
noncomputable def D09 : ℝ := 3 * Num.Ncon
/-- D10, `s² = 3N_h/(1 + f)`. -/
noncomputable def D10 : ℝ := Num.s2
/-- D11, `[παv²/((1 − f)s²)]^{1/2}` [GeV]. -/
noncomputable def D11 : ℝ := Num.v * √(π * Num.alpha / ((1 - Num.f) * Num.s2))
/-- D12, `D11/(1 − s²)^{1/2}` [GeV]. -/
noncomputable def D12 : ℝ := D11 / √(1 - Num.s2)
/-- D13, `D11/D12`. -/
noncomputable def D13 : ℝ := D11 / D12
/-- D14, `f = e²/N₂`. -/
noncomputable def D14 : ℝ := Num.f
/-- D15, `v = (√2G_F)^{−1/2}` [GeV]. -/
noncomputable def D15 : ℝ := Num.v
/-- D16, `v(2πα/χ_h)^{1/2}` [GeV]. -/
noncomputable def D16 : ℝ := Num.v * √(2 * π * Num.alpha / Num.chih)
/-- D17, `v(η/2σ)^{1/2}` [GeV]. -/
noncomputable def D17 : ℝ := Num.v * √(Num.eta / (2 * Num.sigma))
/-- L15, as D11. -/
noncomputable def L15 : ℝ := D11
/-- L19, `[1 − ν/(M + 1 + N(1))]/(c_L f)`: `1/α` at the clock's endpoint `h = 1`. -/
noncomputable def L19 : ℝ := (1 - Num.nu * 1 / ((Num.M : ℝ) + 1 + Num.Nof 1)) / (Num.cL * Num.f)
/-- L20, `3N(1)`. -/
noncomputable def L20 : ℝ := 3 * Num.Nof 1
/-- S07, `m_p²/(E_P m_e)` [GeV]. -/
noncomputable def S07 : ℝ := Num.mp ^ 2 / (Num.EP * Num.me) / 1000
/-- S16, `M_Z e^{−2π/(β₀α_s)}` with `β₀ = 23/3` [MeV]. -/
noncomputable def S16 : ℝ := D12 * 1000 * Real.exp (-(2 * π / ((23 / 3) * Num.alphaS)))
/-- T01, `M_R = M_Pl det(G⁻¹H) = M_Pl e_line⁹` [GeV]. -/
noncomputable def T01 : ℝ := Num.MPl * Num.neutralR
/-- T02, `M_off = M_Pl det_ℂ(G_off⁻¹H_off) = M_Pl e_line⁶` [GeV]. -/
noncomputable def T02 : ℝ := Num.MPl * Num.neutralOff

end Row

theorem D11_eq_q : Row.D11 = Article.qMw := by
  rw [Row.D11, Num.v_eq_q, Num.alpha_eq_q, Num.f_eq, Num.s2_eq_q, Article.qMw]; norm_num

theorem D12_eq_q : Row.D12 = Article.qMz := by
  rw [Row.D12, D11_eq_q, Num.s2_eq_q, Article.qMz]

end Comparison.System.Table

namespace Comparison.System

open Real Complex Matrix Comparison Comparison.Law Comparison.System.Completion Comparison.System.Table

/-- **Row D01.** `α_s = k₄/(k₂√(k_C² − 1)) = (1/72)^{1/2} = 0.117851130198`. Recognition: the strong coupling. -/
theorem row_D01 : Table.Row.D01 = √(1 / 72) ∧
    (0.1178511301975 : ℝ) < Table.Row.D01 ∧ Table.Row.D01 < 0.1178511301985 := by
  refine ⟨by rw [Table.Row.D01, Num.alphaS_eq_q, Article.qAlphaS], ?_⟩
  rw [Table.Row.D01, Num.alphaS_eq_q]; exact Article.rowD01_digits

/-- **Row D02.** `1/α = N₂(1 − x)k₀²/(c_Lk₂²) = 3700/27 − (37/120)h/(297 + N_h) = 137.035999177`.
Recognition: the inverse electric coupling. -/
theorem row_D02 : Table.Row.D02 = 3700 / 27 - 37 / 120 * Num.h / (297 + Num.Nh) ∧
    (137.0359991765 : ℝ) < Table.Row.D02 ∧ Table.Row.D02 < 137.0359991775 := by
  have e : Table.Row.D02 = (1 - Article.qX) / (27 / 3700) := by
    rw [Table.Row.D02, Num.N2_eq, Num.x_eq_q, Num.k_zero, Num.k_two, Num.cL_eq]; field_simp; ring
  refine ⟨?_, ?_⟩
  · rw [e, ← Num.x_eq_q, Num.x, Num.nu_eq, Num.M_eq]
    rw [show ((296 : ℕ) : ℝ) + 1 + Num.Nh = 297 + Num.Nh by push_cast; ring]
    have : (297 : ℝ) + Num.Nh ≠ 0 := by
      rw [Num.Nh_eq_q]; have := Article.qNh_bnd.1; intro h; linarith
    field_simp; ring
  · rw [e]; exact Article.rowD02_digits

/-- **Row D03.** `G_F = (1 − 1/N₂)W_W/(M²m_p²) = 1.16637885871·10⁻⁵ GeV⁻²`. Recognition: the Fermi coefficient. -/
theorem row_D03 : Table.Row.D03 = (1 - 1 / 10) * Num.WW / 296 ^ 2 / (Num.mp / 1000) ^ 2 * 100000 ∧
    (1.166378858705 : ℝ) < Table.Row.D03 ∧ Table.Row.D03 < 1.166378858715 := by
  refine ⟨by rw [Table.Row.D03, Num.GF, Num.GFmp2, Num.N2_eq, Num.M_eq]; push_cast; ring, ?_⟩
  rw [Table.Row.D03, Num.GF_eq_q]; exact Article.rowD03_digits

/-- **Row D04.** `W² = [(2/5)⁴⁸(295/296)⁹]² = 5.90615249377·10⁻³⁹`. Recognition: `Gm_p²/ħc`. -/
theorem row_D04 : Table.Row.D04 = ((2 / 5) ^ 48 * (295 / 296) ^ 9) ^ 2 * 10 ^ 39 ∧
    (5.906152493765 : ℝ) < Table.Row.D04 ∧ Table.Row.D04 < 5.906152493775 := by
  refine ⟨by rw [Table.Row.D04, Num.W_closed], ?_⟩
  rw [Table.Row.D04, Num.W_eq_q]
  have := Article.rowD04_digits
  rw [Article.rowD04] at this
  convert this using 2 <;> norm_num

/-- **Row D05.** `M_Pl = m_p/W = 1.22088981189·10¹⁹ GeV`. Recognition: the Planck mass. -/
theorem row_D05 : Table.Row.D05 = Num.mp / 1000 / Num.W / 10 ^ 19 ∧
    (1.220889811885 : ℝ) < Table.Row.D05 ∧ Table.Row.D05 < 1.220889811895 := by
  refine ⟨rfl, ?_⟩
  rw [Table.Row.D05, Num.MPl_eq_q]
  have := Article.rowD05_digits
  rw [Article.rowD05] at this
  convert this using 2 <;> norm_num

/-- **Row D08.** `3N_h = 0.231257521689`. Recognition: the MS-bar weak angle. -/
theorem row_D08 : Table.Row.D08 = 3 * Num.Nh ∧
    (0.2312575216885 : ℝ) < Table.Row.D08 ∧ Table.Row.D08 < 0.2312575216895 := by
  refine ⟨rfl, ?_⟩
  rw [Table.Row.D08, Num.sw2_eq_q]; exact Article.rowD08_digits

/-- **Row D09.** `3N_con = 0.231550233938`. Recognition: the effective weak angle. -/
theorem row_D09 : Table.Row.D09 = 3 * Num.Ncon ∧
    (0.2315502339375 : ℝ) < Table.Row.D09 ∧ Table.Row.D09 < 0.2315502339385 := by
  refine ⟨rfl, ?_⟩
  rw [Table.Row.D09, Num.Ncon]; exact Article.rowD09_digits

/-- **Row D10.** `s² = 3N_h/(1 + f) = 0.223221546032`. Recognition: the on-shell weak angle. -/
theorem row_D10 : Table.Row.D10 = 3 * Num.Nh / (1 + 9 / 250) ∧
    (0.2232215460315 : ℝ) < Table.Row.D10 ∧ Table.Row.D10 < 0.2232215460325 := by
  refine ⟨by rw [Table.Row.D10, Num.s2, Num.sw2, Num.f_eq], ?_⟩
  rw [Table.Row.D10, Num.s2_eq_q]; exact Article.rowD10_digits

/-- **Row D11.** `M_W = [παv²/((1 − f)s²)]^{1/2} = 80.3662510403 GeV`. Recognition: the W mass. -/
theorem row_D11 : Table.Row.D11 = Num.v * √(π * Num.alpha / ((1 - Num.f) * Num.s2)) ∧
    (80.36625104025 : ℝ) < Table.Row.D11 ∧ Table.Row.D11 < 80.36625104035 := by
  refine ⟨rfl, ?_⟩
  rw [D11_eq_q]; exact Article.rowD11_digits

/-- **Row D12.** `M_Z = M_W/(1 − s²)^{1/2} = 91.1853615183 GeV`. Recognition: the Z mass. -/
theorem row_D12 : Table.Row.D12 = Table.Row.D11 / √(1 - Num.s2) ∧
    (91.18536151825 : ℝ) < Table.Row.D12 ∧ Table.Row.D12 < 91.18536151835 := by
  refine ⟨rfl, ?_⟩
  rw [D12_eq_q]; exact Article.rowD12_digits

/-- **Row D13.** `M_W/M_Z = (1 − s²)^{1/2} = 0.881350358239`. Recognition: the W/Z mass ratio. -/
theorem row_D13 : Table.Row.D13 = √(1 - Num.s2) ∧
    (0.8813503582385 : ℝ) < Table.Row.D13 ∧ Table.Row.D13 < 0.8813503582395 := by
  have hW : Table.Row.D11 ≠ 0 := by
    rw [D11_eq_q]; have := Article.rowD11_digits.1
    rw [Article.rowD11] at this; intro h; rw [h] at this; norm_num at this
  have hs : 0 < 1 - Num.s2 := by
    rw [Num.s2_eq_q]; have := Article.rowD10_digits.2
    rw [Article.rowD10] at this; linarith
  refine ⟨?_, ?_⟩
  · rw [Table.Row.D13, Table.Row.D12]; field_simp [(Real.sqrt_pos.mpr hs).ne']
  · rw [Table.Row.D13, D11_eq_q, D12_eq_q]
    have := Article.rowD13_digits
    rw [Article.rowD13] at this; exact this

/-- **Row D14.** `f = e²/N₂ = 9/250`. Recognition: the weak correction `δ_inv`. -/
theorem row_D14 : Table.Row.D14 = 9 / 250 := Num.f_eq

/-- **Row D15.** `v = (√2G_F)^{−1/2} = 246.219634043 GeV`. Recognition: the electroweak scale. -/
theorem row_D15 : Table.Row.D15 = (√2 * Num.GF) ^ (-(1 / 2 : ℝ)) ∧
    (246.2196340425 : ℝ) < Table.Row.D15 ∧ Table.Row.D15 < 246.2196340435 := by
  refine ⟨rfl, ?_⟩
  rw [Table.Row.D15, Num.v_eq_q]; exact Article.rowD15_digits

/-- **Row D16.** `m_H = v(2πα/χ_h)^{1/2}`, `χ_h = 30/169`: `125.134771593 GeV`. Recognition: the scalar mass. -/
theorem row_D16 : Table.Row.D16 = Num.v * √(2 * π * Num.alpha / (30 / 169)) ∧
    (125.1347715925 : ℝ) < Table.Row.D16 ∧ Table.Row.D16 < 125.1347715935 := by
  refine ⟨by rw [Table.Row.D16, Num.chih_eq], ?_⟩
  rw [Table.Row.D16, Num.v_eq_q, Num.alpha_eq_q, Num.chih_eq]
  have := Article.rowD16_digits
  rw [Article.rowD16, Article.qMh] at this; exact this

/-- **Row D17.** `m_t = v(η/2σ)^{1/2} = v(59/120)^{1/2} = 172.646613614 GeV`. Recognition: the top mass. -/
theorem row_D17 : Table.Row.D17 = Num.v * √(59 / 120) ∧
    (172.6466136135 : ℝ) < Table.Row.D17 ∧ Table.Row.D17 < 172.6466136145 := by
  have e : Table.Row.D17 = Num.v * √(59 / 120) := by
    rw [Table.Row.D17, Num.eta_eq, Num.sigma_eq]; norm_num
  refine ⟨e, ?_⟩
  rw [e, Num.v_eq_q]
  have := Article.rowD17_digits
  rw [Article.rowD17, Article.qMt] at this; exact this

/-- **Row L15.** As D11. Recognition: the W pole mass test. -/
theorem row_L15 : Table.Row.L15 = Table.Row.D11 ∧
    (80.36625104025 : ℝ) < Table.Row.L15 ∧ Table.Row.L15 < 80.36625104035 := ⟨rfl, row_D11.2⟩

/-- **Row L19.** `1/α` at the clock's endpoint `h = 1`: `3700/27 − (37/120)/(297 + N(1)) = 137.035999147`.
Recognition: the clock-independent lower bound on `1/α`. -/
theorem row_L19 : Table.Row.L19 = 3700 / 27 - 37 / 120 / (297 + Num.Nof 1) ∧
    (137.0359991465 : ℝ) < Table.Row.L19 ∧ Table.Row.L19 < 137.0359991475 := by
  have e : Table.Row.L19 = (1 - (9 / 4000) / (297 + N1)) / (27 / 3700) := by
    rw [Table.Row.L19, Num.nu_eq, Num.M_eq, Num.cL_eq, Num.f_eq, Num.Nof, ← Article.N1_eq_NhOf_one]
    norm_num
  have hN : (297 : ℝ) + N1 ≠ 0 := by have := N1_bounds.1; intro h; linarith
  refine ⟨?_, ?_⟩
  · rw [e, Num.Nof, ← Article.N1_eq_NhOf_one]; field_simp; ring
  · rw [e]; exact Article.rowL19_digits

/-- **Row L20.** `3N(1) = 0.231264231358`. Recognition: the clock-independent upper bound on the weak angle. -/
theorem row_L20 : Table.Row.L20 = 3 * N1 ∧
    (0.2312642313575 : ℝ) < Table.Row.L20 ∧ Table.Row.L20 < 0.2312642313585 := by
  refine ⟨by rw [Table.Row.L20, Num.Nof, ← Article.N1_eq_NhOf_one], ?_⟩
  rw [Table.Row.L20, Num.Nof, ← Article.N1_eq_NhOf_one]; exact Article.rowL20_digits

/-- **Row S07.** `m_p²/(E_P m_e) = 172.281080538 GeV`. Recognition: the top mass, second construction. -/
theorem row_S07 : Table.Row.S07 = Num.mp ^ 2 / (10 * Num.me) / 1000 ∧
    (172.2810805375 : ℝ) < Table.Row.S07 ∧ Table.Row.S07 < 172.2810805385 := by
  refine ⟨by rw [Table.Row.S07, Num.EP_eq], ?_⟩
  rw [Table.Row.S07, Num.EP_eq, Num.mp_eq_q, Num.me_eq_q, sq]
  exact Article.rowS07_digits

/-- **Row S16.** `M_Z e^{−2π/(β₀α_s)}`, `β₀ = 23/3`: `87.0577778265 MeV`. Recognition: the five-flavour one-loop
scale marker; `β₀` is the classical one-loop coefficient (outside input). -/
theorem row_S16 : Table.Row.S16 = Table.Row.D12 * 1000 * Real.exp (-(2 * π / ((23 / 3) * √(1 / 72)))) ∧
    (87.05777782645 : ℝ) < Table.Row.S16 ∧ Table.Row.S16 < 87.05777782655 := by
  refine ⟨by rw [Table.Row.S16, Num.alphaS_eq_q, Article.qAlphaS], ?_⟩
  rw [Table.Row.S16, D12_eq_q, Num.alphaS_eq_q]; exact Article.rowS16_digits

/-- **Row T01.** `M_R = M_Pl det(G⁻¹H) = M_Pl 3⁻⁹ = 6.20276285061·10¹⁴ GeV`, the exponent nine the real dimension of
the kept algebra (`Num.neutralR_eq`). Recognition: the heavy neutral threshold. -/
theorem row_T01 : Table.Row.T01 = Num.MPl * (1 / 3) ^ 9 ∧
    (6.202762850605e14 : ℝ) < Table.Row.T01 ∧ Table.Row.T01 < 6.202762850615e14 := by
  refine ⟨by rw [Table.Row.T01, Num.neutralR_eq.2], ?_⟩
  rw [Table.Row.T01, Num.MPl_eq_q, Num.neutralR_eq.2]
  have := Article.rowT01_digits
  rw [Article.rowT01, Article.qMR] at this; exact this

/-- **Row T02.** `M_off = M_Pl det_ℂ(G_off⁻¹H_off) = M_Pl 3⁻⁶ = 1.67474596966·10¹⁶ GeV`, the exponent six the complex
dimension of `Hom_ℂ(F, C)` (`Num.neutralOff_eq`). Recognition: the heavy plane-changing threshold. -/
theorem row_T02 : Table.Row.T02 = Num.MPl * (1 / 3) ^ 6 ∧
    (1.674745969655e16 : ℝ) < Table.Row.T02 ∧ Table.Row.T02 < 1.674745969665e16 := by
  refine ⟨by rw [Table.Row.T02, Num.neutralOff_eq.2], ?_⟩
  rw [Table.Row.T02, Num.MPl_eq_q, Num.neutralOff_eq.2]
  have := Article.rowT02_digits
  rw [Article.rowT02, Article.qMoff] at this; exact this

end Comparison.System
