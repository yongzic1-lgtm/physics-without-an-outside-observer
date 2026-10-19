import Comparison.System.Completion.Numbers
import Comparison.System.Completion.Ext.Idempotent
import Comparison.System.Table.Leptons
import Comparison.System.Table.Couplings
import Comparison.System.Table.Mixings
import Comparison.System.Table.Cosmos
import Comparison.System.Table.Neutrinos
import Comparison.System.Table.Hadrons
import Comparison.System.Table.Nuclei
import Comparison.Article.Marks

set_option linter.style.longLine false

/-!
# The proof system, the completions, part 3: the constants and the spectrum (SI Props. 118 to 127; Eqs. (39) to (45))

Each proposition is stated in the law's numbers (`Numbers.lean`) and the rows of Table X
(`System/Table/*.lean`), which carry its values with rational bounds.
-/

namespace Comparison.System

open Real Complex Matrix Comparison Comparison.Law Comparison.System.Completion Comparison.System.Table

/-- **Proposition 118 (the one sequence).** `M_Pl = m_p/W = 1.22088981·10¹⁹ GeV`, `M_off = M_Pl e_line⁶ = M_Pl/3⁶`,
`M_R = M_Pl e_line⁹ = M_Pl/3⁹`: `M_off/M_R = 27`, `M_off³ = M_PlM_R²`; the exponents are counts, `9 = dim su(3) + 1`
(the kept colour rotations, `u(3)`) and `6 = 2·3` (the rotations across the split of the five directions into the plane and its three
outside lines), and the rows read them as determinants: `M_R = M_Pl det(G⁻¹H)` over the nine real coordinates of the kept
algebra and `M_off = M_Pl det_ℂ(G_off⁻¹H_off)` over the six complex ones of `Hom_ℂ(F, C)` (`Num.neutralR_eq`,
`Num.neutralOff_eq`); `v/m_p = M/(√2(1 − 1/N₂)W_W)^{1/2} = 262.418158676`, `m_H = v(2πα/χ_h)^{1/2}`, `M_t = v(η/2σ)^{1/2}`;
`m_μ/m_e = 𝓛(10, 2, +1)`, `m_τ/m_μ = 𝓛(5, −2, +1)`, `m_s/m_d = p`, `m_b/m_s = qη`, `m_c/m_s = R_udκ⁵`,
`m_u/m_d = R_ud = 17/37`, `κ = (3/2)^{8/5}`; every division `D` of the six moves `|D|(6 − |D|)`
rotations, `9, 8, 5, 0` at the types `3|3, 2|4, 1|5, 0|6`, and `α_s > α > G_Fm_p² > α_G`; the partial lifetime
`ħ(M_off/m_p)⁴/(α_s⁴m_p) = 72²ħ/(3²⁴W⁴m_p) = 1.16971·10³⁷ yr`.

Recognition: the Planck mass, the plane-changing and heavy neutral thresholds, the electroweak scale, the order of
the four forces, the proton's partial lifetime. The sequence (one third per kept colour rotation, per rotation across the two sides) is the
theory's composition. -/
theorem prop_118 :
    Num.MPl = (Num.mp / 1000) / Num.W ∧ Table.Row.T02 = Num.MPl * (1 / 3) ^ 6 ∧
    Table.Row.T01 = Num.MPl * (1 / 3) ^ 9 ∧ Table.Row.T02 / Table.Row.T01 = 27 ∧
    Table.Row.T02 ^ 3 = Num.MPl * Table.Row.T01 ^ 2 ∧
    Module.finrank ℝ Formulas.su3 + 1 = 9 ∧
    ((Finset.univ : Finset (Fin 5)).filter (fun a => a ∈ ({0, 1} : Finset (Fin 5)))).card *
      ((Finset.univ : Finset (Fin 5)).filter (fun a => a ∉ ({0, 1} : Finset (Fin 5)))).card = 6 ∧
    Num.v / (Num.mp / 1000) = (Num.M : ℝ) / √(√2 * ((1 - 1 / (Num.N2 : ℝ)) * Num.WW)) ∧
    ((262.4181586755 : ℝ) < Num.v / (Num.mp / 1000) ∧ Num.v / (Num.mp / 1000) < 262.4181586765) ∧
    (∀ D : Finset (Fin 6), (Finset.univ.filter (Moved D)).card = D.card * (6 - D.card)) ∧
    3 * (6 - 3) = 9 ∧ 2 * (6 - 2) = 8 ∧ 1 * (6 - 1) = 5 ∧ 0 * (6 - 0) = 0 ∧
    Num.W ^ 2 < Num.GFmp2 ∧ Num.GFmp2 < Num.alpha ∧ Num.alpha < Num.alphaS ∧
    Table.Row.K06 = 72 ^ 2 * Num.hbar / (3 ^ 24 * Num.W ^ 4 * Num.mp) / Num.year ∧
    ((1.169710989455e37 : ℝ) < Table.Row.K06 ∧ Table.Row.K06 < 1.169710989465e37) ∧
    ((1.674745969655e16 : ℝ) < Table.Row.T02 ∧ Table.Row.T02 < 1.674745969665e16) ∧
    ((6.202762850605e14 : ℝ) < Table.Row.T01 ∧ Table.Row.T01 < 6.202762850615e14) ∧
    Table.Row.D16 ^ 2 = 2 * π * Num.alpha * Num.v ^ 2 / Num.chih ∧
    Table.Row.D17 = Num.v * √(Num.eta / (2 * Num.sigma)) ∧
    massOp .symmetric sPlane = 3 ^ (5 : ℝ) * Real.exp (-(9 / 56)) * Num.MQ (9 / 4000) ^ (1 / 6 : ℝ) ∧
    massOp .vector sPlane = 3 ^ (5 / 2 : ℝ) * Real.exp (1 / 14 + 2 * (9 / 4000)) ∧
    Table.Row.ms / Table.Row.md = Table.Row.B04 ∧ Table.Row.mb / Table.Row.ms = Table.Row.q * Num.eta ∧
    Table.Row.mc / Table.Row.ms = Num.Rud * Num.kappa ^ 5 ∧ Table.Row.B09 = Num.Rud ∧ Num.Rud = 17 / 37 ∧
    Num.kappa = (3 / 2) ^ (8 / 5 : ℝ) := by
  have hl := Article.one_sequence
  have hmpw : Table.Row.T01 ≠ 0 := by
    intro h; have := row_T01.2.1; rw [h] at this; norm_num at this
  have hα : 0 ≤ Num.alpha := by
    rw [Num.alpha_eq_q]; exact (lt_of_lt_of_le (by norm_num) Article.qAlpha_bnd.1).le
  have hmd : Table.Row.md ≠ 0 := by rw [Table.Row.md, Num.eta_eq]; positivity
  refine ⟨rfl, row_T02.1, row_T01.1, ?_, ?_, by rw [Formulas.finrank_su3], by decide, ?_, ?_, card_moved,
    by norm_num, by norm_num, by norm_num, by norm_num, ?_, ?_, ?_, row_K06.1, row_K06.2, row_T02.2, row_T01.2, ?_,
    rfl, row_mu, row_tau, ?_, ?_, ?_, by rw [row_B09, Num.Rud_eq], Num.Rud_eq, Num.kappa_eq⟩
  · rw [row_T02.1, row_T01.1]
    have : Num.MPl ≠ 0 := by
      rw [Num.MPl_eq_q]; have := Article.qMpl_bnd.1; intro h; rw [h] at this; norm_num at this
    field_simp; norm_num
  · rw [row_T02.1, row_T01.1]; ring
  · rw [Num.M_eq, Num.N2_eq, show ((296 : ℕ) : ℝ) = 296 by norm_num,
      show (1 : ℝ) - 1 / ((10 : ℕ) : ℝ) = 9 / 10 by norm_num, Num.v_eq_q, Num.mp_eq_q, Num.WW_eq_q]
    exact hl.2.2.2.2.2.1
  · rw [Num.v_eq_q, Num.mp_eq_q]; exact hl.2.2.2.2.2.2.1
  · rw [Num.W_eq_q, Num.GFmp2_eq_q]; exact hl.2.2.2.2.2.2.2.2.1
  · rw [Num.GFmp2_eq_q, Num.alpha_eq_q]; exact hl.2.2.2.2.2.2.2.2.2.1
  · rw [Num.alpha_eq_q, Num.alphaS_eq_q]; exact hl.2.2.2.2.2.2.2.2.2.2.1
  · have hc : 0 ≤ 2 * π * Num.alpha / Num.chih := by rw [Num.chih_eq]; positivity
    rw [Table.Row.D16, mul_pow, Real.sq_sqrt hc]; ring
  · rw [Table.Row.ms]; exact mul_div_cancel_left₀ _ hmd
  · rw [Table.Row.mb, Table.Row.B05]; field_simp [Table.ms_pos.ne']
  · rw [Table.Row.mc]; field_simp [Table.ms_pos.ne']

/-- **Proposition 119 (the electroweak poles).** `ŝ² = 3N_h = 0.2312575217`, `3N_con = 0.2315502339`,
`s²_OS = 3N_h/(1 + f) = 0.2232215460`; `M_W = v(πα/((1 − f)s²_OS))^{1/2} = 80.36625104 GeV`,
`M_Z = M_W/(1 − s²_OS)^{1/2} = 91.18536152 GeV`, `G_F = (1 − 1/N₂)W_W/(M²m_p²) = 1.16637886·10⁻⁵ GeV⁻²`; with
`N_con = Σ_k p^con_k`, `p^con_k = −Φ(z_k)` at odd `k` and `[F(z_k) + F(−z_k)]/2` at even `k`, `z_k = 4(i/4)^k`
(real: `z_{2m} = 4(−1/16)^m`).

Recognition: the weak angles, the W and Z masses, Fermi's constant; the vector poles of the last-step direction's Gram form at
the coupling `πα` and the scale `v` are the theory's composition. -/
theorem prop_119 :
    Num.sw2 = 3 * Num.Nh ∧ Table.Row.D09 = 3 * Num.Ncon ∧ Num.s2 = 3 * Num.Nh / (1 + Num.f) ∧
    Table.Row.D11 = Num.v * √(π * Num.alpha / ((1 - Num.f) * Num.s2)) ∧
    Table.Row.D12 = Table.Row.D11 / √(1 - Num.s2) ∧
    Num.GF = (1 - 1 / (Num.N2 : ℝ)) * Num.WW / (Num.M : ℝ) ^ 2 / (Num.mp / 1000) ^ 2 ∧
    Num.Ncon = ∑' k : ℕ, Article.repRcon (k + 1) ∧
    (∀ k : ℕ, Article.repRcon k = if Odd k then repR k else
      (Article.excursionFr (4 * (-1 / 16 : ℝ) ^ (k / 2)) + Article.excursionFr (-(4 * (-1 / 16 : ℝ) ^ (k / 2)))) / 2) ∧
    ((0.2312575216885 : ℝ) < Num.sw2 ∧ Num.sw2 < 0.2312575216895) ∧
    ((0.2315502339375 : ℝ) < Table.Row.D09 ∧ Table.Row.D09 < 0.2315502339385) ∧
    ((0.2232215460315 : ℝ) < Num.s2 ∧ Num.s2 < 0.2232215460325) ∧
    ((80.36625104025 : ℝ) < Table.Row.D11 ∧ Table.Row.D11 < 80.36625104035) ∧
    ((91.18536151825 : ℝ) < Table.Row.D12 ∧ Table.Row.D12 < 91.18536151835) ∧
    ((1.166378858705 : ℝ) < Table.Row.D03 ∧ Table.Row.D03 < 1.166378858715) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    fun _ => rfl, row_D08.2, row_D09.2, row_D10.2, row_D11.2, row_D12.2, row_D03.2⟩

/-- **The variance of `H(y)^n` at `y = 1`:** `G″(1) + G′(1) − G′(1)² = n(H″(1) + H′(1) − H′(1)²) = n·9/4` for
`G = H^n`, `H` the visits to the symmetric states between two arrivals at the vector states (`H(1) = 1`, `H′(1) = 5/2`, `H″(1) = 6`). -/
theorem Completion.Comp.pgf_power_variance (n : ℕ) :
    deriv (deriv (fun y => Article.Hpgf y ^ n)) 1 + deriv (fun y => Article.Hpgf y ^ n) 1 -
      deriv (fun y => Article.Hpgf y ^ n) 1 ^ 2 = n * (9 / 4) := by
  set D : ℝ → ℝ := fun y => (4 + 8 * y - 2 * y ^ 2) / (4 - 2 * y) ^ 2 with hDdef
  have hH1 : Article.Hpgf 1 = 1 := by rw [Article.Hpgf]; norm_num
  have hD1 : D 1 = 5 / 2 := by rw [hDdef]; norm_num
  have hG : ∀ y : ℝ, y ≠ 2 →
      HasDerivAt (fun y => Article.Hpgf y ^ n) ((n : ℝ) * Article.Hpgf y ^ (n - 1) * D y) y := fun y hy =>
    (Article.Hpgf_hasDerivAt y hy).pow n
  have hG1 : deriv (fun y => Article.Hpgf y ^ n) 1 = n * (5 / 2) := by
    rw [(hG 1 (by norm_num)).deriv, hH1, hD1, one_pow, mul_one]
  have hev : deriv (fun y => Article.Hpgf y ^ n) =ᶠ[nhds 1]
      fun y => (n : ℝ) * Article.Hpgf y ^ (n - 1) * D y := by
    filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 2 by norm_num)] with y hy
    exact (hG y hy).deriv
  have hDd : HasDerivAt D 6 1 := by
    have hN := ((hasDerivAt_const (1 : ℝ) (4 : ℝ)).add ((hasDerivAt_id' (1 : ℝ)).const_mul 8)).sub
        ((hasDerivAt_pow 2 (1 : ℝ)).const_mul 2)
    have hDn := ((hasDerivAt_const (1 : ℝ) (4 : ℝ)).sub ((hasDerivAt_id' (1 : ℝ)).const_mul 2)).pow 2
    have h := hN.div hDn (by norm_num)
    refine h.congr_deriv ?_
    norm_num
  have hP : HasDerivAt (fun y => (n : ℝ) * Article.Hpgf y ^ (n - 1))
      ((n : ℝ) * (((n - 1 : ℕ) : ℝ) * Article.Hpgf 1 ^ (n - 1 - 1) * D 1)) 1 :=
    ((Article.Hpgf_hasDerivAt 1 (by norm_num)).pow (n - 1)).const_mul (n : ℝ)
  have h2 : HasDerivAt (fun y => (n : ℝ) * Article.Hpgf y ^ (n - 1) * D y)
      ((n : ℝ) * (((n - 1 : ℕ) : ℝ) * Article.Hpgf 1 ^ (n - 1 - 1) * D 1) * D 1 +
        (n : ℝ) * Article.Hpgf 1 ^ (n - 1) * 6) 1 := hP.mul hDd
  have hG2 : deriv (deriv (fun y => Article.Hpgf y ^ n)) 1 =
      (n : ℝ) * (((n - 1 : ℕ) : ℝ) * (5 / 2)) * (5 / 2) + n * 6 := by
    rw [hev.deriv_eq, h2.deriv, hH1, hD1, one_pow, one_pow, mul_one, mul_one]
  rw [hG2, hG1]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp
  · rw [Nat.cast_sub (by omega : 1 ≤ n)]
    push_cast
    ring

/-- **Proposition 120 (the neighbours of the proton at rest: the moments of one excursion).** In units of `λ_p²`,
`r_p² : r_π² : r_A² = Eℓ : E_P : E Var(P|Q) = 16 : 10 : 9`: the marked excursion `F(1; x, y) = x²H(y)/(4 − 3xH(y)) =
Σ_{q≥2}(1/4)(3/4)^{q−2}x^qH(y)^{q−1}` gives `P(Q = q) = (1/4)(3/4)^{q−2}` and `E[y^P | Q = q] = H(y)^{q−1}`, so
`Var(P | Q = q) = (q − 1)(H″(1) + H′(1) − H′(1)²) = (q − 1)·9/4`, `E Var(P|Q) = (9/4)E(Q − 1) = 9 = Var P − Cov²/Var Q`;
`m_Δ = (Var P/4Eℓ)m_p = 3bm_p`; `r_n² = −6bλ_p² = −2(m_Δ/m_p)λ_p²`;
`μ_p² = (Var ℓ/20)S_μ = 8n_sS_μ`, `μ_n = −(44/23)S_μ^{1/2}` with `44/23 = 4(1 + E_P)/(Tr L²/4 − 1)`,
`S_μ = 1 − ε₂/(Eℓ²b)`, `ε₂ = α²/(1 + α/10)`; `g_A = (5/3)(2/5)^{2b/3}`, `5/3 = ⟨p↑|Σ_rσ_zτ_z|p↑⟩` on the three
lines with spin and isospin; `m_n/m_p = (5/2)^{5a⁴ + 4a¹⁰ + 10c_Lba⁶}`; the values `μ_p = 2.7928473453`,
`μ_n = −1.91304302381`, `g_A = 1.27580092812`.

Recognition: the charge, pion and axial radii, the Δ, the neutron's charge radius, the magnetic moments, the axial
coupling, the neutron/proton ratio. The size as the root of a count, the moments' compositions and the proton as
`P_{p↑}` on the three lines are the theory's (C, R). -/
theorem prop_120 :
    Num.El = 16 ∧ Num.EP = 10 ∧
    (∀ x y : ℝ, y ≠ 2 → |3 * x * Article.Hpgf y / 4| < 1 →
      HasSum (fun m : ℕ => (1 / 4 * (3 / 4 : ℝ) ^ m) * (x ^ (m + 2) * Article.Hpgf y ^ (m + 1))) (excursionF 1 x y)) ∧
    (∀ m : ℕ, deriv (deriv (fun y => Article.Hpgf y ^ (m + 1))) 1 + deriv (fun y => Article.Hpgf y ^ (m + 1)) 1 -
      deriv (fun y => Article.Hpgf y ^ (m + 1)) 1 ^ 2 = ((m : ℝ) + 1) * (9 / 4)) ∧
    (HasSum (fun m : ℕ => (1 / 4 * (3 / 4 : ℝ) ^ m) * (((m : ℝ) + 1) * (9 / 4))) 9 ∧
      Num.VarP - Num.Cov ^ 2 / Num.VarQ = 9) ∧
    Num.VarP / (4 * Num.El) = 3 * Num.b ∧ -6 * Num.b = -2 * (3 * Num.b) ∧
    Num.VarEll / 20 = 8 * Num.ns ∧ Table.Row.G03 ^ 2 = Num.VarEll / 20 * Table.Row.Smu ∧
    Table.Row.G04 = -(44 / 23 * √Table.Row.Smu) ∧
    (44 : ℝ) / 23 = 4 * (1 + Num.EP) / (((L * L).trace).re / 4 - 1) ∧
    Table.Row.Smu = 1 - Table.Row.eps2 / (Num.El ^ 2 * Num.b) ∧
    Table.Row.eps2 = Num.alpha ^ 2 / (1 + Num.alpha / 10) ∧
    Table.Row.S01 = 5 / 3 * (2 / 5 : ℝ) ^ (2 * Num.b / 3) ∧
    (Formulas.Nucleon.Pp * Formulas.Nucleon.axial).trace = 5 / 3 ∧
    Table.Row.B13 = (5 / 2 : ℝ) ^ (5 * Num.a ^ 4 + 4 * Num.a ^ 10 + 10 * Num.cL * Num.b * Num.a ^ 6) ∧
    ((2.79284734525 : ℝ) < Table.Row.G03 ∧ Table.Row.G03 < 2.79284734535) ∧
    ((-1.913043023815 : ℝ) < Table.Row.G04 ∧ Table.Row.G04 < -1.913043023805) ∧
    ((1.275800928115 : ℝ) < Table.Row.S01 ∧ Table.Row.S01 < 1.275800928125) := by
  have hS : 0 ≤ Table.Row.Smu := by
    rw [Smu_eq_q]; exact (lt_of_lt_of_le (by norm_num) Article.qSmu_bnd.1).le
  refine ⟨Num.El_eq, Num.EP_eq, fun x y hy h => ?_, fun m => ?_,
    ⟨Article.expected_conditional_variance.1, by rw [Num.VarP_eq, Num.Cov_eq, Num.VarQ_eq]; norm_num⟩, ?_, by ring,
    ?_, ?_, row_G04.1, ?_, rfl,
    by rw [Table.Row.eps2, Num.N2_eq]; norm_num, ?_, Formulas.Nucleon.axial_Pp, ?_, row_G03.2, row_G04.2, row_S01.2⟩
  · have hD : 4 - 3 * x * Article.Hpgf y ≠ 0 := by
      intro h0
      have h1 : 3 * x * Article.Hpgf y / 4 = 1 := by linarith
      rw [h1] at h
      norm_num at h
    rw [Article.excursion_marked_factor x y hy hD]
    exact Article.excursion_by_arrivals x (Article.Hpgf y) h
  · exact (Completion.Comp.pgf_power_variance (m + 1)).trans (by norm_num)
  · rw [Num.VarP_eq, Num.El_eq, Num.b_eq]; norm_num
  · rw [Num.VarEll_eq, Num.ns_eq]; norm_num
  · have h2 : 0 ≤ Num.VarEll / 20 * Table.Row.Smu := by rw [Num.VarEll_eq]; positivity
    rw [Table.Row.G03, Num.N2_eq, Real.sq_sqrt (by rw [Num.VarEll_eq]; positivity)]; ring
  · rw [Num.EP_eq, Article.trace_L_sq_re]; norm_num
  · rw [Table.Row.S01, Num.t_eq]
  · rw [B13_closed, Num.a_eq, Num.cL_eq, Num.b_eq]

/-- **Proposition 121 (the pions).** The two-end block `T = [[0, x], [y, 0]]` has `T² = xy` and
`det(1 − T)⁻¹ = Σ_k(xy)^k`: the shortest closed walk through both heads weighs their product;
`m_π⁰² = 38h m_em_p` with `38 = 2/|Φ(z_{})|`; `m_π±² = m_π⁰² + πα m_p²/(Eℓ(1 − αbΦ(i)))` with `π = arg z_F`;
`f_π = ηm_p√6/(2πμ_p)`, `√6 = L(Ω)^{1/2}`; the values `134.97704456`, `139.570386614`, `130.529195478 MeV`.

Recognition: the neutral and charged pions and the pion decay constant; the two ends (the electron's least count
and the proton's available transitions at here) and the plane contact are the theory's composition. -/
theorem prop_121 :
    (∀ x y : ℝ, (!![0, x; y, 0] : Matrix (Fin 2) (Fin 2) ℝ) ^ 2 = (x * y) • 1) ∧
    (∀ x : ℝ, |x| < 1 → HasSum (fun k : ℕ => x ^ k) (1 - x)⁻¹) ∧
    endsReturn sHere = 38 ∧ Table.Row.G06 = √(38 * Num.h * Num.me * Num.mp) ∧
    zS sF = -1 ∧ Complex.arg (zS sF) = π ∧
    Table.Row.G07 = √(Table.Row.G06 ^ 2 + π * Num.alpha * Num.mp ^ 2 /
      (Num.El * (1 - Num.alpha * Num.b * (Num.Phi I).re))) ∧
    Table.Row.G08 = Num.eta * Num.mp * √Num.LOmega / (2 * π * Table.Row.G03) ∧
    ((134.977044555 : ℝ) < Table.Row.G06 ∧ Table.Row.G06 < 134.977044565) ∧
    ((139.5703866135 : ℝ) < Table.Row.G07 ∧ Table.Row.G07 < 139.5703866145) ∧
    ((130.5291954775 : ℝ) < Table.Row.G08 ∧ Table.Row.G08 < 130.5291954785) :=
  ⟨blk_square, fun x hx => Comparison.RuleAndLaw.exchange_series x hx, piece_38, row_G06.1,
    (Comparison.RuleAndLaw.plane_phase).1, (Comparison.RuleAndLaw.plane_phase).2, rfl,
    by rw [Table.Row.G08, Num.kC_eq, Num.LOmega_eq]; norm_num, row_G06.2, row_G07.2, row_G08.2⟩

/-- **Proposition 122 (mixing).** The characters of the bound state are moments of one excursion: `k(e) = V_C/(EℓE_U) = 9/40`,
`k(exchange) = 4/Tr L² = 1/24`, `k(5-cycle) = (2/5)k(exchange) = 1/60`, `k(3-cycle) = −1/(EℓE_U) = −1/40`,
`1 + k(3-cycle) = Var ℓ/(E_PEℓ) = 39/40` (with `120k(g)` the plane contrasts' idempotent of Prop. 73);
`V_q = R₂₃(1/24)R₁₃(3/800, δ_q)R₁₂(9/40)`, `δ_q = arg(b + w_C) = arg(7 + 16i)`;
`U_l = R₁₂(√(2b)·9/40, π/2 − δ_q)†R₂₃(2^{−1/2})R₁₂(b^{1/2})`, with `e^{i(π/2 − δ_q)} = (16 + 7i)/√305`; then
`s₁₃² = bs₁₂² = 567/25600`.

Recognition: the quark and lepton mixing matrices and phases. -/
theorem prop_122 :
    (SysPlanes.kk 1 = 27 ∧ SysPlanes.kk SysPlanes.exch = 5 ∧ SysPlanes.kk SysPlanes.cyc5 = 2 ∧
      SysPlanes.kk SysPlanes.cyc3 = -3) ∧
    (27 : ℝ) / 120 = Table.Row.VC / (Num.El * Num.EU) ∧ (5 : ℝ) / 120 = 4 / ((L * L).trace).re ∧
    (2 : ℝ) / 120 = 2 / 5 * (4 / ((L * L).trace).re) ∧ (-3 : ℝ) / 120 = -1 / (Num.El * Num.EU) ∧
    1 + (-3 : ℝ) / 120 = Num.VarEll / (Num.EP * Num.El) ∧
    Table.Row.V = Article.R23 (1 / 24) 0 * Article.R13 (3 / 800) Table.Row.C04 * Article.R12 (9 / 40) 0 ∧
    Table.Row.C04 = Complex.arg (bS sHere + wS sC) ∧ wS sC = I ∧ Table.Row.C04 = Complex.arg (7 + 16 * I) ∧
    Table.Row.U = (Article.R12 (√(2 * Num.b) * (9 / 40)) (π / 2 - Table.Row.C04)).conjTranspose *
      Article.R23 (1 / √2) 0 * Article.R12 √Num.b 0 ∧
    Complex.exp ((π / 2 - Table.Row.C04 : ℝ) * I) = (Article.sdq : ℂ) + (Article.cdq : ℂ) * I ∧
    Table.Row.C11 = Num.b * (9 / 40) ^ 2 := by
  refine ⟨SysPlanes.k_values, ?_, ?_, ?_, ?_, ?_, ?_, rfl, Article.wC_eq, Article.deltaQ_eq_arg, ?_,
    Article.exp_phiL, ?_⟩
  · rw [VC_eq, Num.El_eq, Num.EU_eq]; norm_num
  · rw [Article.trace_L_sq_re]; norm_num
  · rw [Article.trace_L_sq_re]; norm_num
  · rw [Num.El_eq, Num.EU_eq]; norm_num
  · rw [Num.VarEll_eq, Num.EP_eq, Num.El_eq]; norm_num
  · rw [Table.Row.V, row_C02, row_C03, row_C01]
  · rw [Table.Row.U, row_C01]
  · rw [row_C11, Num.b_eq]; norm_num

/-- **The splitting ratio against `ρ⁻²`:** with `ρ ≤ m₂/m₃ < ρ + 2·10⁻²⁶`, `0 ≤ ρ⁻² − (m₃/m₂)² < 10⁻²²`. -/
theorem Completion.Comp.splitting_ratio :
    0 ≤ (Num.rhoNu ^ 2)⁻¹ - Table.Row.E05 ∧ (Num.rhoNu ^ 2)⁻¹ - Table.Row.E05 < 1e-22 := by
  have hn := (Article.neutrinos).2.2.1
  rw [← Num.mnu2_eq_q, ← Num.mnu3_eq_q, ← Num.rhoNu_eq_q] at hn
  have hρ : Num.rhoNu = 3 - 2 * √2 := by rw [Num.rhoNu_eq_q, Article.qRho]
  have hs1 : (1.41421356 : ℝ) < √2 := by
    rw [show (1.41421356 : ℝ) = √(1.41421356 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hs2 : √2 < (1.41421357 : ℝ) := by
    rw [show (1.41421357 : ℝ) = √(1.41421357 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hρlo : (0.1715 : ℝ) < Num.rhoNu := by rw [hρ]; linarith
  have hρhi : Num.rhoNu < (0.1716 : ℝ) := by rw [hρ]; linarith
  set r := Num.mnu2 / Num.mnu3 with hr
  have hE : Table.Row.E05 = (r ^ 2)⁻¹ := by rw [Table.Row.E05, hr, ← inv_pow, inv_div]
  have hρr : Num.rhoNu ≤ r := by linarith [hn.1]
  have hrε : r < Num.rhoNu + 2e-26 := by linarith [hn.2]
  have hρ0 : 0 < Num.rhoNu := by linarith
  have hr0 : 0 < r := by linarith
  rw [hE]
  constructor
  · have : (r ^ 2)⁻¹ ≤ (Num.rhoNu ^ 2)⁻¹ := inv_anti₀ (by positivity) (by gcongr)
    linarith
  · have h1 : ((Num.rhoNu + 2e-26) ^ 2)⁻¹ ≤ (r ^ 2)⁻¹ := inv_anti₀ (by positivity) (by gcongr)
    have h2 : (Num.rhoNu ^ 2)⁻¹ - ((Num.rhoNu + 2e-26) ^ 2)⁻¹ < 1e-22 := by
      rw [inv_sub_inv (by positivity) (by positivity), div_lt_iff₀ (by positivity)]
      have ha : (0.0294 : ℝ) ≤ Num.rhoNu ^ 2 := by nlinarith
      have hb : (0.0294 : ℝ) ≤ (Num.rhoNu + 2e-26) ^ 2 := by nlinarith
      have hab : (0.0294 : ℝ) * 0.0294 ≤ Num.rhoNu ^ 2 * (Num.rhoNu + 2e-26) ^ 2 :=
        mul_le_mul ha hb (by norm_num) (by positivity)
      nlinarith
    linarith

/-- **Proposition 123 (the neutrinos).** For every `X > 0` and `d`, `x = 2d²/(X + (X² + 4d²)^{1/2})` is the one
nonnegative root of `x(X + x) = d²`, the light zero of `det [[x, d], [d, X + x]]`; at `X_R = M_R/m_p = e_line⁹/W` and
`δ = σ(v/m_p)(0, ρ^{1/2}, 1)/√2`, `ρ = tan²(π/8) = 3 − 2√2`: `m₁ = 0`, `m₂ = 8.6126720 meV`, `m₃ = 50.198331 meV`;
`m₂/m₃ = ρ` to `2·10⁻²⁶`; `Δm²₃₁/Δm²₂₁ = (m₃/m₂)²` (row E05, `m₁ = 0`) stands within `10⁻²²` below
`ρ⁻² = 17 + 12√2`; `Σm = 0.0588110 eV`.

Recognition: the light neutrino masses (the seesaw with the Dirac mass `σv/√2` and the heavy neutral pole). -/
theorem prop_123 :
    (∀ X d : ℝ, 0 < X → 0 ≤ Article.seesawX X d ∧ Article.seesawX X d * (X + Article.seesawX X d) = d ^ 2 ∧
      ∀ y : ℝ, 0 ≤ y → y * (X + y) = d ^ 2 → y = Article.seesawX X d) ∧
    Num.XR = Num.eLine ^ 9 / Num.W ∧ Num.eLine ^ 9 = 1 / 3 ^ 9 ∧
    Num.delta3 = Num.sigma * Num.v / (Num.mp / 1000) / √2 ∧ Num.delta2 = Num.delta3 * √Num.rhoNu ∧
    Num.rhoNu = Real.tan (π / 8) ^ 2 ∧ Num.rhoNu = 3 - 2 * √2 ∧
    (∀ d : ℝ, Num.seesaw d = Article.seesawX Num.XR d) ∧ Num.seesaw 0 = 0 ∧
    ((8.61267195 : ℝ) < Num.mnu2 * 1000 ∧ Num.mnu2 * 1000 < 8.61267205) ∧
    ((50.1983305 : ℝ) < Num.mnu3 * 1000 ∧ Num.mnu3 * 1000 < 50.1983315) ∧
    (0 ≤ Num.mnu2 / Num.mnu3 - Num.rhoNu ∧ Num.mnu2 / Num.mnu3 - Num.rhoNu < 2e-26) ∧
    (Num.rhoNu ^ 2)⁻¹ = 17 + 12 * √2 ∧
    Table.Row.E05 = (Num.mnu3 / Num.mnu2) ^ 2 ∧
    (0 ≤ (Num.rhoNu ^ 2)⁻¹ - Table.Row.E05 ∧ (Num.rhoNu ^ 2)⁻¹ - Table.Row.E05 < 1e-22) ∧
    ((0.05881095 : ℝ) < Num.mnu2 + Num.mnu3 ∧ Num.mnu2 + Num.mnu3 < 0.05881105) := by
  have hn := Article.neutrinos
  have hE := Completion.Comp.splitting_ratio
  refine ⟨fun X d hX => Article.seesaw_root hX, rfl, by rw [Num.eLine_eq]; norm_num, rfl, rfl, rfl,
    by rw [Num.rhoNu_eq_q, Article.qRho], fun d => by rw [Num.seesaw, Article.seesawX]; ring_nf,
    seesaw_zero, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Num.mnu2_eq_q]; exact hn.1
  · rw [Num.mnu3_eq_q]; exact hn.2.1
  · rw [Num.mnu2_eq_q, Num.mnu3_eq_q, Num.rhoNu_eq_q]; exact hn.2.2.1
  · rw [Num.rhoNu_eq_q]; exact hn.2.2.2.2.1
  · exact ⟨rfl, hE, by rw [Num.mnu2_eq_q, Num.mnu3_eq_q]; exact hn.2.2.2.2.2⟩

/-- **Proposition 124 (the deuteron).** `u_B = B_d/m_p = χ_A^{1/2}a³[1 − (1 − k₃)ε₂]` with `χ_A = 1/(1 + Φ(i)) =
13/12` and `1 − k₃ = 1 + t/Eℓ = 41/40` (`k₃ = k(3-cycle) = −1/40`): `B_d = 2.2245664631 MeV`;
`m_d/m_p = 1 + m_n/m_p − u_B = 1.99900750127`; the pole matrix `[[0, g√8], [g√8, 6 − 2g]]` at
`g = α_s²/Ψ₁ = 7/18` has the poles `49/9` and `−2/9`, and the D share at the low pole is `P_D = 2/51`;
`μ_d = (16μ_S + g_l)/17 − u_B(μ_S − g_l)/(20 + 13u_B) = 0.857438233519`, `μ_S = μ_p + μ_n`, `g_l = m_n/(m_p + m_n)`.

Recognition: the deuteron's binding, mass ratio, D-state share and moment. -/
theorem prop_124 :
    Table.Row.G10 / Num.mp = √Num.chiA * Num.a ^ 3 * (1 - (1 + Num.t / Num.El) * Table.Row.eps2) ∧
    Num.chiA = 1 / (1 + (Num.Phi I).re) ∧ Num.chiA = 13 / 12 ∧ 1 + Num.t / Num.El = 41 / 40 ∧
    1 + Num.t / Num.El = 1 - (SysPlanes.kk SysPlanes.cyc3 : ℝ) / 120 ∧
    ((2.22456646305 : ℝ) < Table.Row.G10 ∧ Table.Row.G10 < 2.22456646315) ∧
    Table.Row.G12 = 1 + Table.Row.mn / Num.mp - Table.Row.G10 / Num.mp ∧
    ((1.999007501265 : ℝ) < Table.Row.G12 ∧ Table.Row.G12 < 1.999007501275) ∧
    Article.gD = 7 / 18 ∧ Article.gD = meetS sLine (NS sF) / (PsiS sPlane).re ∧
    Article.deutM.mulVec Article.vLow = (-2 / 9 : ℝ) • Article.vLow ∧
    Article.deutM.mulVec Article.vHigh = (49 / 9 : ℝ) • Article.vHigh ∧
    Table.Row.T07 = 2 / 51 ∧
    ((0.8574382335185 : ℝ) < Table.Row.G13 ∧ Table.Row.G13 < 0.8574382335195) := by
  have hm : Num.mp ≠ 0 := by
    rw [Num.mp_eq_q]; exact (lt_of_lt_of_le (by norm_num) Article.qMp_bnd.1).ne'
  refine ⟨?_, ?_, Num.chiA_eq, ?_, ?_, row_G10.2, ?_, row_G12.2, Article.gD_eq, rfl,
    (Article.deutM_eigen).1, (Article.deutM_eigen).2.1, row_T07, row_G13⟩
  · rw [Table.Row.G10]; field_simp
  · rw [Num.chiA, Num.Phi_I]; norm_num
  · rw [Num.t_eq, Num.El_eq]; norm_num
  · rw [SysPlanes.k_values.2.2.2, Num.t_eq, Num.El_eq]; norm_num
  · rw [Table.Row.G12, Table.Row.G11]; field_simp

/-- The nuclear binding of the alpha-cluster nucleus `(4n, 2n)`: `B(4n, 2n) = nB_α + β_nχ_AB_d` [MeV]. -/
noncomputable def Completion.Comp.nuclearB (n : ℕ) : ℝ :=
  (n : ℝ) * Table.Row.N03 + Article.betaC n * Num.chiA * Table.Row.G10

/-- **Proposition 125 (the nuclei).** `v_D = Var D = 61/16 = 3 + χ_A Var Q/Eℓ = [(Var P − Var Q)² + 4Cov²]/(9Eℓ²)`
over the clock's ten gaps; the incidence polynomial `B(A, Z) = B_d[C(A, 2) + (v_D − 3)C(A, 3) + v_DC(A, 4)] −
(αm_p/9)C(Z, 2)`, `9 = V_C`: triton `8.48116`, helion `7.72039`, helium-4 `28.29763 MeV`;
`B(4n, 2n) = nB_α + β_nχ_AB_d`, the rows N04 to N16 `B(4n, 2n) + Δ_at(2n)`, with the bonds `β_n = 0, 3, 6, 8` at
`n = 2, …, 5` and `3n − 6` beyond; `r₀ = k_C|u@{}|λ_p/a = 3λ_p/(4a)`,
`n₀ = 3/(4πr₀³)`, `e₀ = −m_pa²n_s`.

Recognition: the nuclear bindings and the saturation point; the incidence expansion and the bonds are the theory's
compositions, proved here with the bonds as given; the geometry of `β_n`, the rank of a rigid frame of `n` touching
spheres on the A₃ lattice, is the statement that completes Prop. 125. -/
theorem prop_125 :
    (1 / 10) * ∑ i, clockGap sLastDirectionSinglet i ^ 2 - 2 ^ 2 = 61 / 16 ∧
    (3 : ℝ) + Num.chiA * Num.VarQ / Num.El = 61 / 16 ∧
    ((Num.VarP - Num.VarQ) ^ 2 + 4 * Num.Cov ^ 2) / (9 * Num.El ^ 2) = 61 / 16 ∧
    Table.Row.tau3 = 61 / 16 - 3 ∧ Table.Row.VC = 9 ∧
    (∀ A Z : ℕ, Table.Row.Binc A Z = Table.Row.G10 * ((A.choose 2 : ℝ) + Table.Row.tau3 * (A.choose 3 : ℝ) +
      ((Num.kC : ℝ) + Table.Row.tau3) * (A.choose 4 : ℝ)) - Num.alpha * Num.mp / Table.Row.VC * (Z.choose 2 : ℝ)) ∧
    ((8.481159640565 : ℝ) < Table.Row.N01 ∧ Table.Row.N01 < 8.481159640575) ∧
    ((7.720392725255 : ℝ) < Table.Row.N02 ∧ Table.Row.N02 < 7.720392725265) ∧
    ((28.29763250885 : ℝ) < Table.Row.N03 ∧ Table.Row.N03 < 28.29763250895) ∧
    (∀ n : ℕ, Completion.Comp.nuclearB n = (n : ℝ) * Table.Row.N03 + Article.betaC n * Num.chiA * Table.Row.G10 ∧
      Table.Row.cluster n = Completion.Comp.nuclearB n + Table.Row.atomic (2 * n)) ∧
    (Article.betaC 2 = 0 ∧ Article.betaC 3 = 3 ∧ Article.betaC 4 = 6 ∧ Article.betaC 5 = 8 ∧
      ∀ n : ℕ, 6 ≤ n → Article.betaC n = 3 * n - 6) ∧
    Table.Row.r0 = 3 * Num.lp / (4 * Num.a) ∧ Table.Row.N21 = 3 / (4 * π * Table.Row.r0 ^ 3) ∧
    Table.Row.N22 = -(Num.mp * Num.a ^ 2 * Num.ns) ∧
    ((0.1385842276655 : ℝ) < Table.Row.N21 ∧ Table.Row.N21 < 0.1385842276665) ∧
    ((-15.83821480585 : ℝ) < Table.Row.N22 ∧ Table.Row.N22 < -15.83821480575) := by
  refine ⟨clock_moments.2, ?_, ?_, by rw [tau3_eq]; norm_num, VC_eq, fun A Z => rfl, row_N01, row_N02, row_N03,
    fun n => ⟨rfl, rfl⟩, ⟨by norm_num [Article.betaC], by norm_num [Article.betaC], by norm_num [Article.betaC],
      by norm_num [Article.betaC], fun n hn => ?_⟩, ?_, rfl, ?_, row_N21.2, row_N22.2⟩
  · rw [Num.chiA_eq, Num.VarQ_eq, Num.El_eq]; norm_num
  · rw [Num.VarP_eq, Num.VarQ_eq, Num.Cov_eq, Num.El_eq]; norm_num
  · have h2 : n ≠ 2 := by omega
    have h3 : n ≠ 3 := by omega
    have h4 : n ≠ 4 := by omega
    have h5 : n ≠ 5 := by omega
    simp [Article.betaC, h2, h3, h4, h5]
  · rw [Table.Row.r0, Num.kC_eq, table_here.2.2.2.1]; norm_num; ring
  · rw [Table.Row.N22, Table.Row.ma2, Num.ns]; ring

/-- **Proposition 127 (the cosmos).** `η_B = 3a¹¹`; `A_s = 12a¹¹(k_*ℓ)^{n_s − 1}`, `n_s = 1 − t/Eℓ = 39/40`, the 3 and the
12 the first and the second derivative of the one connected source `C(j) = a¹¹ log G(e^j)` (`Table.F01_source`,
`Table.As_source`);
`N_eff = 3ησ^{4/3} = 3η(11/4)^{4/3}(T_ν/T_γ)⁴` with `T_ν/T_γ = (4σ/11)^{1/3}`; the ratio `24/11` is
`(Tr L²/4)/(1 + E_P)`, the twenty-four traceless rotations against the eleven positive vertices
(`dim E₆(L) + dim E₂(L) = 11`); and for every `c > 0` exactly one `a > 0` has `ca³ = 24/11`.

Recognition: baryons per photon, the primordial amplitude, the tilt, the effective neutrino number and the neutrino
temperature, the present (`ρ_Λ/ρ_m = 24/11`). The occupations and the cold-matter ratio `a¹⁶X_R` are the theory's;
the one surface is proved for the densities' law `ρ_Λ/ρ_m = ca³`, and that law from the occupations of the places is
the statement that completes Prop. 127. -/
theorem prop_127 :
    Table.Row.F01 = 3 * Num.a ^ 11 * 10 ^ 10 ∧
    Table.Row.As = 12 * Num.a ^ 11 * (Num.kstar * Num.ell) ^ (Num.ns - 1) ∧ Num.ns = 39 / 40 ∧
    Table.Row.F04 = 3 * Num.eta * Num.sigma ^ (4 / 3 : ℝ) ∧
    3 * Num.eta * ((4 * Num.sigma / 11) ^ (1 / 3 : ℝ)) ^ 4 * (11 / 4 : ℝ) ^ (4 / 3 : ℝ) =
      3 * Num.eta * Num.sigma ^ (4 / 3 : ℝ) ∧
    (L * L).trace / 4 = 24 ∧
    Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' L) 6) +
      Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' L) 2) = 11 ∧
    (24 : ℝ) / 11 = (((L * L).trace).re / 4) / (1 + Num.EP) ∧
    (∀ c : ℝ, 0 < c → ∃! a : ℝ, 0 < a ∧ c * a ^ 3 = 24 / 11) := by
  refine ⟨Table.F01_source, Table.As_source, Num.ns_eq, rfl, by rw [Num.eta_eq, Num.sigma_eq]; exact Article.neff_temperature,
    WholePicture.twentyfour_eleven.1,
    WholePicture.twentyfour_eleven.2, ?_, fun c hc => Article.one_surface c hc⟩
  rw [Article.trace_L_sq_re, Num.EP_eq]; norm_num

/-- **Equation (39).** `g_A = (5/3)(2/5)^{2b/3} = 1.27580092812`, `μ_p = 2.7928473453`, `μ_n = −1.91304302381`,
`4λ_p = 0.841235640213 fm`, `τ_n = 878.051411827 s`. -/
theorem eq_39 :
    Table.Row.S01 = 5 / 3 * (2 / 5 : ℝ) ^ (7 / 24 : ℝ) ∧
    ((1.275800928115 : ℝ) < Table.Row.S01 ∧ Table.Row.S01 < 1.275800928125) ∧
    ((2.79284734525 : ℝ) < Table.Row.G03 ∧ Table.Row.G03 < 2.79284734535) ∧
    ((-1.913043023815 : ℝ) < Table.Row.G04 ∧ Table.Row.G04 < -1.913043023805) ∧
    Table.Row.G01 = 4 * Num.lp ∧
    ((0.8412356402125 : ℝ) < Table.Row.G01 ∧ Table.Row.G01 < 0.8412356402135) ∧
    ((878.0514118265 : ℝ) < Table.Row.S05 ∧ Table.Row.S05 < 878.0514118275) :=
  ⟨row_S01.1, row_S01.2, row_G03.2, row_G04.2, row_G01.1, row_G01.2, row_S05⟩

/-- **Equation (40).** `m_Λ = m_n(5/2)^{3/16} = 1115.68290091 MeV`, `m_Δ = 3bm_p = 1231.48211736 MeV`. -/
theorem eq_40 :
    Table.Row.J03 = Table.Row.mn * (5 / 2) ^ (3 / 16 : ℝ) ∧
    ((1115.682900905 : ℝ) < Table.Row.J03 ∧ Table.Row.J03 < 1115.682900915) ∧
    Table.Row.G02 = 3 * Num.b * Num.mp ∧
    ((1231.482117355 : ℝ) < Table.Row.G02 ∧ Table.Row.G02 < 1231.482117365) :=
  ⟨row_J03.1, row_J03.2, by rw [Table.Row.G02, Num.kC_eq]; push_cast; ring, row_G02.2⟩

/-- **Equation (41).** `B_d = m_pχ_A^{1/2}a³[1 − (1 + t/Eℓ)ε₂] = 2.2245664631 MeV`, `ε₂ = α²/(1 + α/N₂)`. -/
theorem eq_41 :
    Table.Row.G10 = Num.mp * √Num.chiA * Num.a ^ 3 * (1 - (1 + Num.t / Num.El) * Table.Row.eps2) ∧
    Table.Row.eps2 = Num.alpha ^ 2 / (1 + Num.alpha / Num.N2) ∧
    ((2.22456646305 : ℝ) < Table.Row.G10 ∧ Table.Row.G10 < 2.22456646315) :=
  ⟨rfl, rfl, row_G10.2⟩

/-- **Equation (42).** `s₁₂ = (Var P − Cov²/Var Q)/(Eℓ·5/2) = 9/40`, `s₂₃ = 4/Tr L² = 1/24`,
`s₁₃ = s₁₂ t s₂₃ = 3/800`, `δ_q = arg(b + w_C) = arg(b + i) = arg(7 + 16i)`. -/
theorem eq_42 :
    Table.Row.C01 = 9 / 40 ∧ Table.Row.C02 = 1 / 24 ∧ Table.Row.C03 = 3 / 800 ∧
    Table.Row.C04 = Complex.arg (bS sHere + I) ∧ Table.Row.C04 = Complex.arg (7 + 16 * I) := by
  refine ⟨row_C01, row_C02, row_C03, ?_, row_C04.1⟩
  rw [Table.Row.C04, Article.wC_eq]

/-- **Equation (43).** `α = 90.7137730643°`, `β = 22.9511439354°`, `γ = 66.3350830003°`. -/
theorem eq_43 :
    ((90.71377306425 : ℝ) < Table.Row.C06 ∧ Table.Row.C06 < 90.71377306435) ∧
    ((22.95114393535 : ℝ) < Table.Row.C07 ∧ Table.Row.C07 < 22.95114393545) ∧
    ((66.33508300025 : ℝ) < Table.Row.C08 ∧ Table.Row.C08 < 66.33508300035) :=
  ⟨row_C06, row_C07, row_C08⟩

/-- **Equation (44).** `U = R₁₂(√(2b)s₁₂, π/2 − δ_q)†R₂₃(1/√2)R₁₂(√b)`: `s₁₂² = 0.305090`,
`s₁₃² = 0.0221484`, `s₂₃² = 0.488675`, `δ_l = 205.584°`, `J_l = −0.014464`. -/
theorem eq_44 :
    Table.Row.U = (Article.R12 (√(2 * Num.b) * Table.Row.C01) (π / 2 - Table.Row.C04)).conjTranspose *
      Article.R23 (1 / √2) 0 * Article.R12 √Num.b 0 ∧
    ((0.3050896109225 : ℝ) < Table.Row.C10 ∧ Table.Row.C10 < 0.3050896109235) ∧
    Table.Row.C11 = 567 / 25600 ∧
    ((0.4886749490665 : ℝ) < Table.Row.C13 ∧ Table.Row.C13 < 0.4886749490675) ∧
    ((205.5842258345 : ℝ) < Table.Row.C14 ∧ Table.Row.C14 < 205.5842258355) ∧
    ((-0.01446443474635 : ℝ) < Table.Row.T06 ∧ Table.Row.T06 < -0.01446443474625) :=
  ⟨rfl, row_C10, row_C11, row_C13, row_C14, row_T06⟩

/-- **Equation (45).** `Λℓ_P² = 3W⁶τs³ = 2.855223·10⁻¹²²`, `τ = 2π/(Eℓ m_p/m_e)`, `s = 3/50`. -/
theorem eq_45 :
    Table.Row.LambdaLP2 = 3 * Num.W ^ 6 * Num.tau * Num.s ^ 3 ∧ Num.tau = 2 * π / (Num.El * Num.protonPole) ∧
    Num.s = 3 / 50 ∧ ((2.855223243005 : ℝ) < Table.Row.D06 ∧ Table.Row.D06 < 2.855223243015) :=
  ⟨rfl, rfl, Num.s_eq, row_D06.2⟩

end Comparison.System
