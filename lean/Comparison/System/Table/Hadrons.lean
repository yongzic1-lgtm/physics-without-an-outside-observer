import Comparison.System.Table.Leptons
import Comparison.System.Table.Mixings

set_option linter.style.longLine false

/-!
# The proof system, the table, part 6: the nucleon, the pions, the kaons, the deuteron

Rows A002, A003, G01 to G13, I08, I09, J03 to J09, J17, J18, L13, S01 to S05, T07 of Table X
(Props. 70, 84, 120, 121, 124, 196 to 198; Eqs. (39) to (41)).

Recognitions: A002 the pion decay constant second construction [MeV], A003 its product with `|V_ud|` [MeV], G01 the
proton charge radius [fm], G02 the Δ mass [MeV], G03 and G04 the proton and neutron moments [μ_N], G05 their ratio,
G06 and J05 the neutral pion mass [MeV], G07 and J06 the charged pion mass [MeV], G08 the pion decay constant [MeV],
G09 its product with `|V_ud|` [MeV], G10 and L13 the deuteron binding [MeV], G11 the deuteron mass [MeV], G12
`m_d/m_p`, G13 the deuteron moment [μ_N], I08 the topological curvature, I09 the fourth strong cumulant, J03 the Λ
[MeV], J04 the Δ Breit–Wigner [MeV], J07 the ρ pole `Re s` [GeV²], J08 and J09 the neutral and charged kaon [MeV],
J17 the temperature at which colour stops binding [MeV], J18 the Δ pole [MeV], S01 the axial coupling `g_A`, S02 and
S03 the axial radius [fm², fm], S04 the pion charge radius [fm], S05 the neutron lifetime [s], T07 the deuteron's
D-state share. The compositions (the size as the root of a count, the moments, the two-end block, the light level
through the one composition, the deuteron's pole) are the theory's (C), each proved as its proposition (Props. 70, 84,
120, 121, 124, 196 to 198); S05 uses the classical
normalization `5099.33 s`, `1.03983` of the neutron's decay rate (outside), and every row in MeV the unit `m_e c²`.
-/

namespace Comparison.System.Table

open Real Complex Matrix Comparison Comparison.Law Comparison.System.Completion

namespace Row

/-- The neutron's mass `m_n = m_p (m_n/m_p)` [MeV]. -/
noncomputable def mn : ℝ := Num.mp * B13
/-- G01, `Eℓ^{1/2}λ_p = 4λ_p` [fm]. -/
noncomputable def G01 : ℝ := √Num.El * Num.lp
/-- G02, J04, J18, `k_C b m_p` [MeV]. -/
noncomputable def G02 : ℝ := (Num.kC : ℝ) * Num.b * Num.mp
noncomputable def J04 : ℝ := G02
noncomputable def J18 : ℝ := G02
/-- `ε₂ = α²/(1 + α/N₂)`, the electric contact at an odd vertex, and `S_μ = 1 − ε₂/(Eℓ²b)`. -/
noncomputable def eps2 : ℝ := Num.alpha ^ 2 / (1 + Num.alpha / Num.N2)
noncomputable def Smu : ℝ := 1 - eps2 / (Num.El ^ 2 * Num.b)
/-- G03, `μ_p = [(Var ℓ/2N₂)S_μ]^{1/2}`. -/
noncomputable def G03 : ℝ := √(Num.VarEll / (2 * Num.N2) * Smu)
/-- G04, `μ_n = −[4(1 + E_P)/(Tr L²/4 − 1)]S_μ^{1/2}`. -/
noncomputable def G04 : ℝ := -(4 * (1 + Num.EP) / (((L * L).trace).re / 4 - 1) * √Smu)
/-- G05, `μ_n/μ_p`. -/
noncomputable def G05 : ℝ := G04 / G03
/-- G06, J05, `[(2/|Φ(z_{})|)h m_e m_p]^{1/2}` [MeV]. -/
noncomputable def G06 : ℝ := √(endsReturn sHere * Num.h * Num.me * Num.mp)
noncomputable def J05 : ℝ := G06
/-- `Δ_el = πα m_p²/(Eℓ(1 − αbΦ(i)))`, the plane's electric self-energy. -/
noncomputable def Del : ℝ :=
  π * Num.alpha * Num.mp ^ 2 / (Num.El * (1 - Num.alpha * Num.b * (Num.Phi I).re))
/-- G07, J06, `(m_π⁰² + Δ_el)^{1/2}` [MeV]. -/
noncomputable def G07 : ℝ := √(G06 ^ 2 + Del)
noncomputable def J06 : ℝ := G07
/-- G08, `f_π = ηm_p(2k_C)^{1/2}/(2πμ_p)` [MeV]. -/
noncomputable def G08 : ℝ := Num.eta * Num.mp * √(2 * (Num.kC : ℝ)) / (2 * π * G03)
/-- G09, `f_π|V_ud|` [MeV]. -/
noncomputable def G09 : ℝ := G08 * ‖V 0 0‖
/-- G10, L13, `B_d = m_pχ_A^{1/2}a³[1 − (1 + t/Eℓ)ε₂]` [MeV]. -/
noncomputable def G10 : ℝ := Num.mp * √Num.chiA * Num.a ^ 3 * (1 - (1 + Num.t / Num.El) * eps2)
noncomputable def L13 : ℝ := G10
/-- G11, `m_p + m_n − B_d` [MeV]. -/
noncomputable def G11 : ℝ := Num.mp + mn - G10
/-- G12, `m_d/m_p`. -/
noncomputable def G12 : ℝ := G11 / Num.mp
/-- G13, `μ_d = (16μ_S + g_l)/17 − u_B(μ_S − g_l)/(20 + 13u_B)`, `μ_S = μ_p + μ_n`, `g_l = m_n/(m_p + m_n)`,
`u_B = B_d/m_p`. -/
noncomputable def G13 : ℝ :=
  (16 * (G03 + G04) + mn / (Num.mp + mn)) / 17 -
    G10 / Num.mp * (G03 + G04 - mn / (Num.mp + mn)) / (20 + 13 * (G10 / Num.mp))
/-- J03, `m_n k₀^{E_H/Eℓ}` [MeV]. -/
noncomputable def J03 : ℝ := mn * Num.k 0 ^ (Num.EH / Num.El)
/-- J07, `2k_C m_p² log x_c` [GeV²]. -/
noncomputable def J07 : ℝ := 2 * (Num.kC : ℝ) * Num.mp ^ 2 * Real.log Num.xc / 1000000
/-- J17, `m_p/(d + 1)`, `d + 1 = L(Ω)` [MeV]. -/
noncomputable def J17 : ℝ := Num.mp / Num.LOmega
/-- S01, `g_A = (5/3)t^{2b/3}`. -/
noncomputable def S01 : ℝ := 5 / 3 * Num.t ^ (2 * Num.b / 3)
/-- S02, `(Var P − Cov²/Var Q)λ_p²` [fm²]; S03 its root [fm]; S04 `E_P^{1/2}λ_p` [fm]. -/
noncomputable def S02 : ℝ := (Num.VarP - Num.Cov ^ 2 / Num.VarQ) * Num.lp * Num.lp
noncomputable def S03 : ℝ := √(Num.VarP - Num.Cov ^ 2 / Num.VarQ) * Num.lp
noncomputable def S04 : ℝ := √Num.EP * Num.lp
/-- S05, `τ_n = 5099.33 s/(1.03983|V_ud|²(1 + 3g_A²))`: the classical normalization `2π³ħ⁷/(G_F²m_e⁵c⁴f)` and the
radiative factor are outside, and the normalization carries the measured Fermi constant `G_F` (outside input). -/
noncomputable def S05 : ℝ := 5099.33 / (1.03983 * ‖V 0 0‖ ^ 2 * (1 + 3 * S01 ^ 2))
/-- A002, `5m_p/36` [MeV]; A003, `(5m_p/36)|V_ud|` [MeV]: model rows with the factor `5/36`, the axial residue at the
pion pole of the second construction; that factor read from a law object is the statement that completes them. -/
noncomputable def A002 : ℝ := 5 * Num.mp / 36
noncomputable def A003 : ℝ := 5 * Num.mp / 36 * ‖V 0 0‖
/-- T07, the D-state share at the deuteron's low pole (Prop. 124). -/
noncomputable def T07 : ℝ := Article.deutD_share

/-- The three light coloured poles `(S_u, S_d, S_s) ∝ (R_ud, 1, p)` and their 2×2 mixing block. -/
noncomputable def trM : ℝ := (Num.Rud + 1) + (Num.Rud + 1 + 4 * B04) / 3
noncomputable def detM : ℝ := ((Num.Rud + 1) * (Num.Rud + 1 + 4 * B04) - (Num.Rud - 1) ^ 2) / 3
noncomputable def lamMin : ℝ := (trM - √(trM * trM - 4 * detM)) / 2
noncomputable def invSum : ℝ := 1 / Num.Rud + 1 + 1 / B04
/-- I08, `1/(λ_min Σ_q S_q⁻¹)`; I09, `−Σ_q S_q⁻³/(12(Σ_q S_q⁻¹)³)`. -/
noncomputable def I08 : ℝ := 1 / (lamMin * invSum)
noncomputable def I09 : ℝ := -((1 / Num.Rud) ^ 3 + 1 + (1 / B04) ^ 3) / (12 * invSum ^ 3)

/-- **The light level** `S_d` (Prop. 197): the `S ≥ 0` with `6m_p² Tr δ₁(R(R_udS, S; 8/15)) = m_π⁰²`. -/
noncomputable def Sd : ℝ := Classical.choose Article.light_level_exists
/-- J08, `K⁰ = [6m_p² Tr δ₁(R(S_d, pS_d; 8/15))]^{1/2}` [MeV]; J09, `K±` with the marked plane current. -/
noncomputable def J08 : ℝ := Article.rowJ08Of Sd
noncomputable def J09 : ℝ := Article.rowJ09Of Sd

end Row

theorem Sd_mem : Row.Sd ∈ Set.Icc Article.sdLo Article.sdHi :=
  (Classical.choose_spec Article.light_level_exists).1

theorem Sd_eq : light_level_equation Row.Sd Article.qMp (Article.qPi0 ^ 2) :=
  (Classical.choose_spec Article.light_level_exists).2

theorem Sd_nonneg : 0 ≤ Row.Sd := le_trans (by norm_num [Article.sdLo]) Sd_mem.1

theorem mn_eq_q : Row.mn = Article.qMn := by
  rw [Row.mn, Num.mp_eq_q, B13_eq_q, Article.qMn]

theorem eps2_eq_q : Row.eps2 = Article.qEps2 := by
  rw [Row.eps2, Num.alpha_eq_q, Num.N2_eq, Article.qEps2]; norm_num

theorem Smu_eq_q : Row.Smu = Article.qSmu := by
  rw [Row.Smu, eps2_eq_q, Num.El_eq, Num.b_eq, Article.qSmu]; norm_num

theorem G03_eq_q : Row.G03 = Article.qMup := by
  rw [Row.G03, Smu_eq_q, Num.VarEll_eq, Num.N2_eq, Article.qMup]; norm_num

theorem G04_eq_q : Row.G04 = Article.qMun := by
  rw [Row.G04, Smu_eq_q, Num.EP_eq, Article.trace_L_sq_re, Article.qMun]; norm_num

theorem G06_eq_q : Row.G06 = Article.qPi0 := by
  rw [Row.G06, piece_38, Num.h_eq_q, Num.me_eq_q, Num.mp_eq_q, Article.qPi0]

theorem Del_eq_q : Row.Del = Article.qElec := by
  rw [Row.Del, Num.alpha_eq_q, Num.mp_eq_q, Num.El_eq, Num.b_eq, Num.Phi_I, Article.qElec]; norm_num

theorem G07_eq_q : Row.G07 = Article.qPip := by
  rw [Row.G07, G06_eq_q, Del_eq_q, Article.qPip]

theorem G08_eq_q : Row.G08 = Article.qFpi := by
  rw [Row.G08, Num.eta_eq, Num.mp_eq_q, Num.kC_eq, G03_eq_q, Article.qFpi]; norm_num

theorem G10_eq_q : Row.G10 = Article.qBd := by
  rw [Row.G10, Num.mp_eq_q, Num.chiA_eq, Num.a_eq, Num.t_eq, Num.El_eq, eps2_eq_q, Article.qBd]; norm_num

theorem G11_eq_q : Row.G11 = Article.qMd := by
  rw [Row.G11, Num.mp_eq_q, mn_eq_q, G10_eq_q, Article.qMd]

theorem S01_eq_q : Row.S01 = Article.qGA := by
  rw [Row.S01, Num.t_eq, Num.b_eq, Article.qGA]; norm_num

end Comparison.System.Table

namespace Comparison.System

open Real Complex Matrix Comparison Comparison.Law Comparison.System.Completion Comparison.System.Table

/-- **Row G01.** `Eℓ^{1/2}λ_p = 4λ_p = 0.841235640213 fm`. Recognition: the proton charge radius. -/
theorem row_G01 : Table.Row.G01 = 4 * Num.lp ∧
    (0.8412356402125 : ℝ) < Table.Row.G01 ∧ Table.Row.G01 < 0.8412356402135 := by
  have e : Table.Row.G01 = 4 * Num.lp := by
    rw [Table.Row.G01, Num.El_eq, show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨e, ?_⟩
  rw [e, Num.lp_eq_q]; exact Article.rowG01_digits

/-- **Row G02.** `k_C b m_p = (21/16)m_p = 1231.48211736 MeV`. Recognition: the Δ mass. -/
theorem row_G02 : Table.Row.G02 = 21 / 16 * Num.mp ∧
    (1231.482117355 : ℝ) < Table.Row.G02 ∧ Table.Row.G02 < 1231.482117365 := by
  have e : Table.Row.G02 = 21 / 16 * Num.mp := by
    rw [Table.Row.G02, Num.kC_eq, Num.b_eq]; push_cast; ring
  refine ⟨e, ?_⟩
  rw [e, Num.mp_eq_q]; exact Article.rowG02_digits

/-- **Row J04.** As G02. Recognition: the Δ, Breit–Wigner. -/
theorem row_J04 : Table.Row.J04 = Table.Row.G02 ∧
    (1231.482117355 : ℝ) < Table.Row.J04 ∧ Table.Row.J04 < 1231.482117365 := ⟨rfl, row_G02.2⟩

/-- **Row J18.** As G02. Recognition: the Δ, pole (a composite of several lines beyond its first pole: its complex
pole is one of the many-body places). -/
theorem row_J18 : Table.Row.J18 = Table.Row.G02 ∧
    (1231.482117355 : ℝ) < Table.Row.J18 ∧ Table.Row.J18 < 1231.482117365 := ⟨rfl, row_G02.2⟩

/-- **Row G03.** `μ_p = [(Var ℓ/2N₂)S_μ]^{1/2} = 2.7928473453`. Recognition: the proton moment [μ_N]. -/
theorem row_G03 : Table.Row.G03 = √(39 / 5 * Table.Row.Smu) ∧
    (2.79284734525 : ℝ) < Table.Row.G03 ∧ Table.Row.G03 < 2.79284734535 := by
  refine ⟨by rw [Table.Row.G03, Num.VarEll_eq, Num.N2_eq]; norm_num, ?_⟩
  rw [G03_eq_q]; exact Article.rowG03_digits

/-- **Row G04.** `μ_n = −(44/23)S_μ^{1/2} = −1.91304302381`, `44/23 = 4(1 + E_P)/(Tr L²/4 − 1)`. Recognition: the
neutron moment [μ_N]. -/
theorem row_G04 : Table.Row.G04 = -(44 / 23 * √Table.Row.Smu) ∧
    (-1.913043023815 : ℝ) < Table.Row.G04 ∧ Table.Row.G04 < -1.913043023805 := by
  refine ⟨by rw [Table.Row.G04, Num.EP_eq, Article.trace_L_sq_re]; norm_num, ?_⟩
  rw [G04_eq_q]; exact Article.rowG04_digits

/-- **Row G05.** `μ_n/μ_p = −0.684979444733`. Recognition: the moment ratio. -/
theorem row_G05 : Table.Row.G05 = Table.Row.G04 / Table.Row.G03 ∧
    (-0.6849794447335 : ℝ) < Table.Row.G05 ∧ Table.Row.G05 < -0.6849794447325 := by
  refine ⟨rfl, ?_⟩
  rw [Table.Row.G05, G04_eq_q, G03_eq_q]; exact Article.rowG05_digits

/-- **Row G06.** `m_π⁰ = [(2/|Φ(z_{})|)h m_e m_p]^{1/2} = (38h m_e m_p)^{1/2} = 134.97704456 MeV`. Recognition: the
neutral pion mass. -/
theorem row_G06 : Table.Row.G06 = √(38 * Num.h * Num.me * Num.mp) ∧
    (134.977044555 : ℝ) < Table.Row.G06 ∧ Table.Row.G06 < 134.977044565 := by
  refine ⟨by rw [Table.Row.G06, piece_38], ?_⟩
  rw [G06_eq_q]; exact Article.rowG06_digits

/-- **Row J05.** As G06. -/
theorem row_J05 : Table.Row.J05 = Table.Row.G06 ∧
    (134.977044555 : ℝ) < Table.Row.J05 ∧ Table.Row.J05 < 134.977044565 := ⟨rfl, row_G06.2⟩

/-- **Row G07.** `m_π± = (m_π⁰² + Δ_el)^{1/2}`, `Δ_el = πα m_p²/(Eℓ(1 − αbΦ(i)))`: `139.570386614 MeV`.
Recognition: the charged pion mass. -/
theorem row_G07 : Table.Row.G07 = √(Table.Row.G06 ^ 2 + Table.Row.Del) ∧
    (139.5703866135 : ℝ) < Table.Row.G07 ∧ Table.Row.G07 < 139.5703866145 := by
  refine ⟨rfl, ?_⟩
  rw [G07_eq_q]; exact Article.rowG07_digits

/-- **Row J06.** As G07. -/
theorem row_J06 : Table.Row.J06 = Table.Row.G07 ∧
    (139.5703866135 : ℝ) < Table.Row.J06 ∧ Table.Row.J06 < 139.5703866145 := ⟨rfl, row_G07.2⟩

/-- **Row G08.** `f_π = ηm_p(2k_C)^{1/2}/(2πμ_p) = 130.529195478 MeV`. Recognition: the pion decay constant. -/
theorem row_G08 : Table.Row.G08 = 295 / 296 * Num.mp * √6 / (2 * π * Table.Row.G03) ∧
    (130.5291954775 : ℝ) < Table.Row.G08 ∧ Table.Row.G08 < 130.5291954785 := by
  refine ⟨by rw [Table.Row.G08, Num.eta_eq, Num.kC_eq]; norm_num, ?_⟩
  rw [G08_eq_q]; exact Article.rowG08_digits

/-- **Row G09.** `f_π|V_ud| = 127.181371253 MeV`. Recognition: the pion constant times `V_ud`. -/
theorem row_G09 : Table.Row.G09 = Table.Row.G08 * ‖Table.Row.V 0 0‖ ∧
    (127.1813712525 : ℝ) < Table.Row.G09 ∧ Table.Row.G09 < 127.1813712535 := by
  refine ⟨rfl, ?_⟩
  rw [Table.Row.G09, G08_eq_q, V_eq]; exact Article.rowG09_digits

/-- **Row G10.** `B_d = m_pχ_A^{1/2}a³[1 − (1 + t/Eℓ)ε₂] = 2.2245664631 MeV`. Recognition: the deuteron binding. -/
theorem row_G10 : Table.Row.G10 = Num.mp * √(13 / 12) * (5 / 38) ^ 3 * (1 - 41 / 40 * Table.Row.eps2) ∧
    (2.22456646305 : ℝ) < Table.Row.G10 ∧ Table.Row.G10 < 2.22456646315 := by
  refine ⟨by rw [Table.Row.G10, Num.chiA_eq, Num.a_eq, Num.t_eq, Num.El_eq]; norm_num, ?_⟩
  rw [G10_eq_q]; exact Article.rowG10_digits

/-- **Row L13.** As G10. Recognition: the completed deuteron binding. -/
theorem row_L13 : Table.Row.L13 = Table.Row.G10 ∧
    (2.22456646305 : ℝ) < Table.Row.L13 ∧ Table.Row.L13 < 2.22456646315 := ⟨rfl, row_G10.2⟩

/-- **Row G11.** `m_p + m_n − B_d = 1875.61294498 MeV`. Recognition: the deuteron mass. -/
theorem row_G11 : Table.Row.G11 = Num.mp + Table.Row.mn - Table.Row.G10 ∧
    (1875.612944975 : ℝ) < Table.Row.G11 ∧ Table.Row.G11 < 1875.612944985 := by
  refine ⟨rfl, ?_⟩
  rw [G11_eq_q]; exact Article.rowG11_digits

/-- **Row G12.** `m_d/m_p = 1.99900750127`. Recognition: deuteron/proton. -/
theorem row_G12 : Table.Row.G12 = Table.Row.G11 / Num.mp ∧
    (1.999007501265 : ℝ) < Table.Row.G12 ∧ Table.Row.G12 < 1.999007501275 := by
  refine ⟨rfl, ?_⟩
  rw [Table.Row.G12, G11_eq_q, Num.mp_eq_q]; exact Article.rowG12_digits

/-- **Row G13.** `μ_d = 0.857438233519`. Recognition: the deuteron moment [μ_N]. -/
theorem row_G13 : (0.8574382335185 : ℝ) < Table.Row.G13 ∧ Table.Row.G13 < 0.8574382335195 := by
  have e : Table.Row.G13 = Article.qMud := by
    rw [Table.Row.G13, G03_eq_q, G04_eq_q, mn_eq_q, Num.mp_eq_q, G10_eq_q, Article.qMud, Article.qMus,
      Article.qGl, Article.qUB]
  rw [e]; exact Article.rowG13_digits

/-- **Row J03.** `m_n k₀^{E_H/Eℓ} = m_n(5/2)^{3/16} = 1115.68290091 MeV`. Recognition: the Λ. -/
theorem row_J03 : Table.Row.J03 = Table.Row.mn * (5 / 2) ^ (3 / 16 : ℝ) ∧
    (1115.682900905 : ℝ) < Table.Row.J03 ∧ Table.Row.J03 < 1115.682900915 := by
  have e : Table.Row.J03 = Table.Row.mn * (5 / 2) ^ (3 / 16 : ℝ) := by
    rw [Table.Row.J03, Num.k_zero, Num.EH_eq, Num.El_eq]
  refine ⟨e, ?_⟩
  rw [e, mn_eq_q]; exact Article.rowJ03_digits

/-- **Row J07.** `2k_C m_p² log x_c = 0.576408555494 GeV²`, `x_c = (√313 − 11)/6`. Recognition: the ρ pole,
`Re s`. -/
theorem row_J07 : Table.Row.J07 = 6 * Num.mp ^ 2 * Real.log ((√313 - 11) / 6) / 1000000 ∧
    (0.5764085554935 : ℝ) < Table.Row.J07 ∧ Table.Row.J07 < 0.5764085554945 := by
  have e : Table.Row.J07 = 6 * Num.mp ^ 2 * Real.log ((√313 - 11) / 6) / 1000000 := by
    rw [Table.Row.J07, Num.kC_eq, Num.xc, Comparison.xc]; push_cast; ring
  refine ⟨e, ?_⟩
  rw [e, Num.mp_eq_q]; exact Article.rowJ07_digits

/-- **Row J08.** `K⁰ = [6m_p² Tr δ₁(R(S_d, pS_d; 8/15))]^{1/2} = 497.613584451 MeV` at the light level `S_d`.
Recognition: the neutral kaon. -/
theorem row_J08 : (497.6135844505 : ℝ) < Table.Row.J08 ∧ Table.Row.J08 < 497.6135844515 :=
  Article.rowJ08_digits Table.Row.Sd Sd_nonneg Sd_eq

/-- **Row J09.** `K± = [6m_p² Tr δ₁(R(R_udS_d, pS_d; 8/15)) + (48/25)Δ_el]^{1/2} = 493.665032668 MeV`.
Recognition: the charged kaon, with the marked plane current. -/
theorem row_J09 : (493.6650326675 : ℝ) < Table.Row.J09 ∧ Table.Row.J09 < 493.6650326685 :=
  Article.rowJ09_digits Table.Row.Sd Sd_nonneg Sd_eq

/-- **Row J17.** `m_p/(d + 1) = m_p/L(Ω) = 156.37868157 MeV`. Recognition: the temperature at which colour stops
binding. -/
theorem row_J17 : Table.Row.J17 = Num.mp / 6 ∧
    (156.378681565 : ℝ) < Table.Row.J17 ∧ Table.Row.J17 < 156.378681575 := by
  have e : Table.Row.J17 = Num.mp / 6 := by rw [Table.Row.J17, Num.LOmega_eq]
  refine ⟨e, ?_⟩
  rw [e, Num.mp_eq_q]; exact Article.rowJ17_digits

/-- **Row S01.** `g_A = (5/3)t^{2b/3} = (5/3)(2/5)^{7/24} = 1.27580092812`. Recognition: the axial coupling; the
coefficient `5/3 = ⟨p↑|Σ_rσ_zτ_z|p↑⟩` of the three lines with spin and isospin (`Formulas.axial_Pp`). -/
theorem row_S01 : Table.Row.S01 = 5 / 3 * (2 / 5 : ℝ) ^ (7 / 24 : ℝ) ∧
    (1.275800928115 : ℝ) < Table.Row.S01 ∧ Table.Row.S01 < 1.275800928125 := by
  refine ⟨by rw [S01_eq_q, Article.qGA], ?_⟩
  rw [S01_eq_q]; exact Article.rowS01_digits

/-- **Row S02.** `(Var P − Cov²/Var Q)λ_p² = 9λ_p² = 0.39806853883 fm²`. Recognition: the axial radius squared. -/
theorem row_S02 : Table.Row.S02 = 9 * Num.lp * Num.lp ∧
    (0.398068538825 : ℝ) < Table.Row.S02 ∧ Table.Row.S02 < 0.398068538835 := by
  have e : Table.Row.S02 = 9 * Num.lp * Num.lp := by
    rw [Table.Row.S02, Num.VarP_eq, Num.Cov_eq, Num.VarQ_eq]; norm_num
  refine ⟨e, ?_⟩
  rw [e, Num.lp_eq_q]; exact Article.rowS02_digits

/-- **Row S03.** `3λ_p = 0.63092673016 fm`. Recognition: the axial radius. -/
theorem row_S03 : Table.Row.S03 = 3 * Num.lp ∧
    (0.630926730155 : ℝ) < Table.Row.S03 ∧ Table.Row.S03 < 0.630926730165 := by
  have e : Table.Row.S03 = 3 * Num.lp := by
    rw [Table.Row.S03, Num.VarP_eq, Num.Cov_eq, Num.VarQ_eq,
      show (84 : ℝ) - 30 ^ 2 / 12 = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  refine ⟨e, ?_⟩
  rw [e, Num.lp_eq_q]; exact Article.rowS03_digits

/-- **Row S04.** `E_P^{1/2}λ_p = √10 λ_p = 0.665055167996 fm`. Recognition: the pion charge radius. -/
theorem row_S04 : Table.Row.S04 = √10 * Num.lp ∧
    (0.6650551679955 : ℝ) < Table.Row.S04 ∧ Table.Row.S04 < 0.6650551679965 := by
  have e : Table.Row.S04 = √10 * Num.lp := by rw [Table.Row.S04, Num.EP_eq]
  refine ⟨e, ?_⟩
  rw [e, Num.lp_eq_q]; exact Article.rowS04_digits

/-- **Row S05.** `τ_n = 5099.33 s/(1.03983|V_ud|²(1 + 3g_A²)) = 878.051411827 s`. Recognition: the neutron
lifetime; the normalization `5099.33 s`, `1.03983` is classical (outside). -/
theorem row_S05 : (878.0514118265 : ℝ) < Table.Row.S05 ∧ Table.Row.S05 < 878.0514118275 := by
  rw [Table.Row.S05, V_eq, S01_eq_q]; exact Article.rowS05_digits

/-- **Row A002.** `5m_p/36 = 130.315567975 MeV`. Recognition: the pion decay constant, second construction. -/
theorem row_A002 : Table.Row.A002 = 5 * Num.mp / 36 ∧
    (130.3155679745 : ℝ) < Table.Row.A002 ∧ Table.Row.A002 < 130.3155679755 := by
  refine ⟨rfl, ?_⟩
  rw [Table.Row.A002, Num.mp_eq_q]; exact Article.rowA002_digits

/-- **Row A003.** `(5m_p/36)|V_ud| = 126.973222886 MeV`. Recognition: the pion current product, second
construction. -/
theorem row_A003 : Table.Row.A003 = 5 * Num.mp / 36 * ‖Table.Row.V 0 0‖ ∧
    (126.9732228855 : ℝ) < Table.Row.A003 ∧ Table.Row.A003 < 126.9732228865 := by
  refine ⟨rfl, ?_⟩
  rw [Table.Row.A003, Num.mp_eq_q, V_eq]; exact Article.rowA003_digits

/-- **Row T07.** The D-state share at the low pole `−2/9` of `[[0, g√8], [g√8, 6 − 2g]]`, `g = α_s²/Ψ₁ = 7/18`:
`P_D = 2/51`. Recognition: the deuteron's D-state share. -/
theorem row_T07 : Table.Row.T07 = 2 / 51 := Article.deutD_share_eq

/-- **Row I08.** `1/(λ_min Σ_q S_q⁻¹) = 0.212911371927`. Recognition: the topological curvature
`χ/(F_π²m_π⁰²)`. -/
theorem row_I08 : (0.2129113719265 : ℝ) < Table.Row.I08 ∧ Table.Row.I08 < 0.2129113719275 := by
  have e : Table.Row.I08 = Article.rowI08 := by
    rw [Table.Row.I08, Table.Row.lamMin, Table.Row.trM, Table.Row.detM, Table.Row.invSum, Num.Rud_eq,
      B04_eq_q, Article.rowI08, Article.qLow, Article.qTrM, Article.qDetM, Article.qInvSum]
    norm_num
  rw [e]; exact Article.rowI08_digits

/-- **Row I09.** `−Σ_qS_q⁻³/(12(Σ_qS_q⁻¹)³) = −0.0280584730988`. Recognition: the fourth strong cumulant `b₂`. -/
theorem row_I09 : (-0.02805847309885 : ℝ) < Table.Row.I09 ∧ Table.Row.I09 < -0.02805847309875 := by
  have e : Table.Row.I09 = Article.rowI09 := by
    rw [Table.Row.I09, Table.Row.invSum, Num.Rud_eq, B04_eq_q, Article.rowI09, Article.qInvSum]
    norm_num
    ring
  rw [e]; exact Article.rowI09_digits

end Comparison.System
