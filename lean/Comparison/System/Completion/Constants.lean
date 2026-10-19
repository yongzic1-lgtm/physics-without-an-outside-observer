import Comparison.System.Completion.Numbers
import Comparison.System.Completion.Ext.Idempotent
import Comparison.System.Table.Couplings
import Comparison.System.Table.Hadrons
import Comparison.System.Table.Cosmos
import Comparison.WholePicture.SecondVariation

set_option linter.style.longLine false

/-!
# The proof system, the completions, part 1: the constants (SI Props. 64 to 73; Eqs. (31) to (36))

Each `prop_N` is the whole SI Proposition N as one Lean statement in the law's numbers of
`Numbers.lean`; each `eq_N` the main text's equation N. The plane contrasts (Prop. 73) come from the copy
`System/Completion/Ext/Planes.lean` (namespace `Comparison.SysPlanes`) of `Existence/Planes.lean`.
-/

namespace Comparison.System

open Real Complex Matrix Comparison Comparison.Law Comparison.System.Completion

/-- **Proposition 64 (the meeting).** Two ends each reaching one of `N` equal channels with chance `e/N` meet with
`σ = Σ_p (e/N)² = e²/N`, for every `N` and `e`. The plane meeting: the departures from the symmetric states are `200`, `120` of them to the
symmetric states, twelve to each of the ten symmetric states, so a arrival at a symmetric state is the ratio of the two counts, `s = 12/200 = e/N₂ = 3/50`
with `e = e@{t,n} = 3/5`, and `f = Σ_planes s² = 9/250`. The colour meeting: the ends at `{t}` with `e_line = 1/3` on
the rotations of the `k_C` lines less the common phase, `k_C² − 1 = 8 = dim su(3)`: `α_s² = Σ_8 (e_line/8)² = 1/72`, and
as an amplitude `α_s = (1/72)^{1/2}`. Per mean excursion, `ν = f/Eℓ = 9/4000`.

Recognition: `f` the plane (electric) meeting, `α_s` the colour (strong) coupling, `ν` the clock's rate. The vertices a
count or an amplitude takes (two-spinor states; rotations less the common phase) are the theory's reading of Prop. 42. -/
theorem prop_64 :
    (∀ (N : ℕ), 0 < N → ∀ e : ℝ, ∑ _x : Fin N, (e / N) * (e / N) = e ^ 2 / N) ∧
    ((Finset.univ ×ˢ Finset.univ).filter fun p : State × State =>
        (disagreeSet p.1.1).card = 2 ∧ Continues p.1 p.2).card = 200 ∧
    ((Finset.univ ×ˢ Finset.univ).filter fun p : State × State =>
        (disagreeSet p.1.1).card = 2 ∧ Continues p.1 p.2 ∧ (disagreeSet p.2.1).card = 2).card = 120 ∧
    (∀ k : Fin 16, (disagreeSet k).card = 2 →
      ((Finset.univ ×ˢ Finset.univ).filter fun p : State × State =>
        (disagreeSet p.1.1).card = 2 ∧ Continues p.1 p.2 ∧ p.2.1 = k).card = 12 ∧
      (((Finset.univ ×ˢ Finset.univ).filter fun p : State × State =>
          (disagreeSet p.1.1).card = 2 ∧ Continues p.1 p.2 ∧ p.2.1 = k).card : ℝ) /
        ((Finset.univ ×ˢ Finset.univ).filter fun p : State × State =>
          (disagreeSet p.1.1).card = 2 ∧ Continues p.1 p.2).card = eS sLineSinglet / Num.N2) ∧
    eS sLineSinglet / Num.N2 = 3 / 50 ∧
    Num.f = ∑ _x : Fin Num.N2, (eS sLineSinglet / Num.N2) ^ 2 ∧ Num.f = 9 / 250 ∧
    Num.kC ^ 2 - 1 = 8 ∧ Module.finrank ℝ Formulas.su3 = Num.kC ^ 2 - 1 ∧
    ∑ _x : Fin (Module.finrank ℝ Formulas.su3), (Num.eLine / 8) ^ 2 = 1 / 72 ∧
    Num.alphaS ^ 2 = 1 / 72 ∧ Num.alphaS = (1 / 72 : ℝ) ^ (1 / 2 : ℝ) ∧
    Num.nu = Num.f / Num.El ∧ Num.nu = 9 / 4000 := by
  have he : eS sLineSinglet = 3 / 5 := (table_lineSinglet sLineSinglet (Or.inl rfl)).2.2.2.2.2.1
  have hd := plane_departures
  refine ⟨fun N hN e => Article.equal_places N hN e, hd.1, hd.2.2.1, fun k hk => ⟨hd.2.2.2 k hk, ?_⟩,
    ?_, ?_, Num.f_eq, by simp [Num.kC_eq], by simp [Formulas.finrank_su3, Num.kC_eq], ?_, Num.alphaS_sq, ?_, ?_,
    Num.nu_eq⟩
  · rw [hd.2.2.2 k hk, hd.1, he, Num.N2_eq]; norm_num
  · rw [he, Num.N2_eq]; norm_num
  · rw [Num.f_eq, he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Num.N2_eq]; norm_num
  · rw [Formulas.finrank_su3, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Num.eLine_eq]; norm_num
  · rw [Num.alphaS_eq_q, Article.qAlphaS, Real.sqrt_eq_rpow]
  · rw [Num.f_eq, Num.El_eq, Num.nu_eq]; norm_num

/-- **Proposition 65 (the electric coupling).** For every last-step direction `h`, line `k ≠ h` of its plane, step `t` and two-spinor state
`S`: `Q(S △ T_t) + Q(S) = q_t(2[t ∈ S] − 1)` with `q_h = 0`, `q_k = 1`, `q_c = −1/3`; the step along the last-step direction
gives off no charge. `α₀ = c_L f = 27/3700`, `1/α₀ = 3700/27 = 137.037`; with the contact `x = νh/(M + 1 + N_h)`,
`α = c_Lf/(1 − x)` and `1/α = 3700/27 − (37/120)h/(297 + N_h)`.

Recognition: `Q` the electric charge, `α` the fine-structure constant; the contact retained once as `1/(1 − x)` over
the `M + 1` steps (Prop. 110's open member) is the theory's composition. -/
theorem prop_65 :
    (∀ (h k : Fin 5), h ≠ k → ∀ (t : Fin 5) (r : Fin 16),
      Comparison.charge h k (transition t r) + Comparison.charge h k r =
        ((Article.qline3 h k t : ℚ) / 3) * (2 * (if t ∈ disagreeSet r then 1 else 0) - 1)) ∧
    (∀ (h k : Fin 5), h ≠ k → (Article.qline3 h k h : ℚ) / 3 = 0 ∧ (Article.qline3 h k k : ℚ) / 3 = 1 ∧
      ∀ c, c ≠ h → c ≠ k → (Article.qline3 h k c : ℚ) / 3 = -1 / 3) ∧
    (∀ (h k : Fin 5), h ≠ k → ∀ r : Fin 16, Comparison.charge h k (transition h r) = -Comparison.charge h k r) ∧
    Num.cL * Num.f = 27 / 3700 ∧ ((137.0365 : ℝ) < 3700 / 27 ∧ (3700 / 27 : ℝ) < 137.0375) ∧
    Num.alpha = Num.cL * Num.f / (1 - Num.x) ∧
    1 / Num.alpha = 3700 / 27 - 37 / 120 * Num.h / (297 + Num.Nh) := by
  refine ⟨fun h k hk t r => Article.charge_step h k hk t r, ?_, fun h k hk r => Article.lastDirection_step_neutral h k hk r,
    ?_, ⟨by norm_num, by norm_num⟩, rfl, ?_⟩
  · intro h k hk
    refine ⟨by simp [Article.qline3], by simp [Article.qline3, hk.symm], fun c hch hck => ?_⟩
    simp [Article.qline3, hch, hck]
  · rw [Num.cL_eq, Num.f_eq]; norm_num
  · have hN : (297 : ℝ) + Num.Nh ≠ 0 := by
      rw [Num.Nh_eq_q]; have := Article.qNh_bnd.1; intro h; linarith
    rw [Num.alpha, Num.x, Num.cL_eq, Num.f_eq, Num.nu_eq, Num.M_eq]
    have hx : (1 : ℝ) - 9 / 4000 * Num.h / ((296 : ℕ) + 1 + Num.Nh) ≠ 0 := by
      rw [← Num.nu_eq, ← Num.M_eq, ← Num.x, Num.x_eq_q]
      have := Article.qX_bnd.2; intro h; norm_num at this; linarith
    rw [show ((296 : ℕ) : ℝ) + 1 + Num.Nh = 297 + Num.Nh by push_cast; ring] at hx ⊢
    field_simp
    ring

/-- **Proposition 66 (gravity).** `W = t^{k_CEℓ}η^{k_CE_H} = (t^{Eℓ}η^{E_H})³ = (2/5)⁴⁸(295/296)⁹`, `Eℓ = 16`,
`E_H = 3`; `α_G = W² = 5.90615249·10⁻³⁹`; for every flux `θ` on the forty links with `‖θ_cyc‖² ≤ 1/100` (`θ_cyc` the
part no gauge transformation removes), the long-range zero `u_c` of `(1 + 4u²) − uλ_max(A_θ)` has
`|log 4u_c − ‖θ_cyc‖²/48| ≤ ‖θ_cyc‖⁴/20`, and a gauge transformation does not move `λ_max`; `48 = n(d − 2) = 2(m − n)` with
`n = 16` vertices, `d = 5`, `m = 40` links.

Recognition: `α_G = Gm_p²/ħc`; the per-line excursion `t^{Eℓ}η^{E_H}` taken once on each of the three lines outside the
plane, and the meeting at the point, are the theory's composition. -/
theorem prop_66 :
    Num.W = (Num.t ^ Num.El * Num.eta ^ Num.EH) ^ 3 ∧ Num.W = (2 / 5) ^ 48 * (295 / 296) ^ 9 ∧
    ((5.9061524937e-39 : ℝ) < Num.W ^ 2 ∧ Num.W ^ 2 < 5.9061524938e-39) ∧
    (∀ θ : Fin 40 → ℝ, WholePicture.sqL (WholePicture.thetaCyc θ) ≤ 1 / 100 →
      |Real.log (4 * WholePicture.ucrit θ) - WholePicture.sqL (WholePicture.thetaCyc θ) / 48| ≤
        WholePicture.sqL (WholePicture.thetaCyc θ) ^ 2 / 20 ∧
      1 + 4 * WholePicture.ucrit θ ^ 2 = WholePicture.ucrit θ * WholePicture.lamMax θ) ∧
    (∀ (θ : Fin 40 → ℝ) (φ : Fin 16 → ℝ),
      WholePicture.lamMax (θ + WholePicture.gradR φ) = WholePicture.lamMax θ) ∧
    (Finset.univ.filter fun p : Fin 16 × Fin 16 => p.1 < p.2 ∧ Adjacent p.1 p.2).card = 40 ∧
    Fintype.card (Fin 16) * (Fintype.card (Fin 5) - 2) = 48 ∧
    2 * ((Finset.univ.filter fun p : Fin 16 × Fin 16 => p.1 < p.2 ∧ Adjacent p.1 p.2).card -
      Fintype.card (Fin 16)) = 48 := by
  refine ⟨?_, Num.W_closed, ?_, fun θ hθ => ⟨(WholePicture.long_range_zero θ hθ).2.2,
    (WholePicture.long_range_zero θ hθ).2.1⟩, WholePicture.lamMax_gauge, card_edges, by simp,
    by rw [card_edges]; simp⟩
  · rw [Num.W, Num.El_eq, Num.EH_eq, Num.kC_eq, Num.t_eq, Num.eta_eq]
    rw [show ((3 : ℕ) : ℝ) * 16 = ((48 : ℕ) : ℝ) by norm_num, show ((3 : ℕ) : ℝ) * 3 = ((9 : ℕ) : ℝ) by norm_num,
      show (16 : ℝ) = ((16 : ℕ) : ℝ) by norm_num, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num]
    simp only [Real.rpow_natCast]
    ring
  · rw [Num.W_closed]; constructor <;> norm_num

/-- **Proposition 68 (the weak, the Higgs and the top).** `G_Fm_p² = (1 − 1/10)W_W/M²` with
`W_W = F(h)h⁻⁴(1 − 2b + 2bh)` and `2b = Var P/(Var P + Var Q) = 7/8`; `ŝ² = 3N_h`, `N_h = Σ_k hᵏp_k`,
`p₁ = −Φ(i) = 1/13`, whose first term `3/13` is the share that moves the last-step direction `w_h`; `m_H² = 2παv²/χ_h`,
`χ_h = w_h(1 − w_h) = 30/169`; `y_t² = η/σ = C_j/C_h = 59/60`, `M_t = v(η/2σ)^{1/2}`; and the values
`G_F = 1.16637886·10⁻⁵ GeV⁻²`, `ŝ² = 0.231258`, `m_H = 125.135 GeV`, `M_t = 172.647 GeV`.

Recognition: `G_F` Fermi's constant, `ŝ²` the weak angle, `m_H` the Higgs mass, `y_t` the top's Yukawa coupling. The
weak contact (two ends, each one continuation `1/M`, on the nine symmetric states), the retained excursion `W_W` and the Higgs
quartic `πα/χ_h` are the theory's compositions. -/
theorem Completion.Comp.weak_higgs_top :
    Num.GFmp2 = (1 - 1 / (Num.N2 : ℝ)) * Num.WW / (Num.M : ℝ) ^ 2 ∧
    Num.WW = Num.Fr Num.h / Num.h ^ 4 * (1 - 2 * Num.b + 2 * Num.b * Num.h) ∧
    2 * Num.b = Num.VarP / (Num.VarP + Num.VarQ) ∧ 2 * Num.b = 7 / 8 ∧
    Num.sw2 = 3 * Num.Nh ∧ Num.Nh = ∑' k : ℕ, Num.h ^ (k + 1) * repR (k + 1) ∧
    repR 1 = 1 / 13 ∧ -(Num.Phi I) = 1 / 13 ∧ 3 * repR 1 = Num.wh ∧
    Num.chih = Num.wh * (1 - Num.wh) ∧ Num.chih = 30 / 169 ∧
    Table.Row.D16 ^ 2 = 2 * π * Num.alpha * Num.v ^ 2 / Num.chih ∧
    Num.eta / Num.sigma = (Num.Cj : ℝ) / Num.Ch ∧ Num.eta / Num.sigma = 59 / 60 ∧
    Table.Row.D17 = Num.v * √(Num.eta / (2 * Num.sigma)) ∧
    ((1.166378858705 : ℝ) < Table.Row.D03 ∧ Table.Row.D03 < 1.166378858715) ∧
    ((0.2312575216885 : ℝ) < Num.sw2 ∧ Num.sw2 < 0.2312575216895) ∧
    ((125.1347715925 : ℝ) < Table.Row.D16 ∧ Table.Row.D16 < 125.1347715935) ∧
    ((172.6466136135 : ℝ) < Table.Row.D17 ∧ Table.Row.D17 < 172.6466136145) := by
  have hv : 0 ≤ Num.v := by rw [Num.v_eq_q]; exact (lt_of_lt_of_le (by norm_num) Article.qV_bnd.1).le
  have hα : 0 ≤ Num.alpha := by
    rw [Num.alpha_eq_q]; exact (lt_of_lt_of_le (by norm_num) Article.qAlpha_bnd.1).le
  refine ⟨rfl, rfl, ?_, by rw [Num.b_eq]; norm_num, rfl,
    rfl, repR_one, by rw [Num.Phi_I]; norm_num, by rw [repR_one, Num.wh_eq]; norm_num, rfl, Num.chih_eq, ?_, ?_, ?_,
    rfl,
    row_D03.2, row_D08.2, row_D16.2, row_D17.2⟩
  · rw [Num.b_eq, Num.VarP_eq, Num.VarQ_eq]; norm_num
  · have hc : 0 ≤ 2 * π * Num.alpha / Num.chih := by rw [Num.chih_eq]; positivity
    rw [Table.Row.D16, mul_pow, Real.sq_sqrt hc]; ring
  · rw [Num.eta, Num.sigma]
    have : (Num.M : ℝ) ≠ 0 := by rw [Num.M_eq]; norm_num
    have : (Num.Ch : ℝ) ≠ 0 := by rw [Num.Ch_eq]; norm_num
    field_simp
  · rw [Num.eta_eq, Num.sigma_eq]; norm_num

/-- **Proposition 69 (leptons and quarks).** The mass operator on the symmetric and the vector states at the two signs of a plane,
`R(Π, S) = e@{t}^{−n_Π/2}exp[−Ψ(w_S²)L_Π(n_Π − ε_S)/4]·clock_Π`, with `Ψ_+ = Ψ@{a,b} = 1/28`,
`Ψ_− = Ψ@{a,b,n} = 1/2`, `ε_+ = 1`, `ε_− = 0`, the clock's ten gaps of the marks `(0, 1, 2, 3, 19)/4` of mean
`E_D = 2`: `m_μ/m_e = 3⁵e^{−9/56}M_Q(ν)^{1/6}`, `m_τ/m_μ = 3^{5/2}e^{1/14 + 2ν}`, `p = 3⁵e^{−5/2}M_Q(−ν)^{1/6}`,
`q = 3^{5/2}e^{5/4 − 5ν/2}`; the down sequence gives `m_b/m_s = qη`; the up sequence `m_u/m_d = R_ud = 17/37` and
`m_c/m_s = R_udκ⁵` with `κ = (e/t)@{t,n}^{Eℓ/E_P} = (3/2)^{8/5}`; in units of `m_e`,
`(m_d, m_s, m_b) = 3^{3/2}(1/η, p/η, pq)`, `m_s/m_d = p` and `m_t = R_udκ^{15/2}m_b`; the line clock is
`exp[(n − ε_S)z_S²νE_D/4]` with `E_D = (1/10)Σ_D D = 2`.

Recognition: the muon, tau and quark mass ratios. The mass operator itself (one association per two-spinor state of the
cumulative projectors, the plane and line clocks) is the theory's composition. -/
theorem prop_69 :
    PsiS sPlane = 1 / 28 ∧ PsiS sPlaneSinglet = 1 / 2 ∧ epsRec sPlane = 1 ∧ epsRec sPlaneSinglet = 0 ∧
    (∀ i : Fin 10, clockGap sLastDirectionSinglet i =
      ![1 / 4, 2 / 4, 3 / 4, 19 / 4, 1 / 4, 2 / 4, 18 / 4, 1 / 4, 17 / 4, 16 / 4] i) ∧
    (1 / 10) * ∑ i, clockGap sLastDirectionSinglet i = 2 ∧
    massOp .symmetric sPlane = 3 ^ (5 : ℝ) * Real.exp (-(9 / 56)) * Num.MQ (9 / 4000) ^ (1 / 6 : ℝ) ∧
    massOp .vector sPlane = 3 ^ (5 / 2 : ℝ) * Real.exp (1 / 14 + 2 * (9 / 4000)) ∧
    massOp .symmetric sPlaneSinglet = 3 ^ (5 : ℝ) * Real.exp (-(5 / 2)) * Num.MQ (-(9 / 4000)) ^ (1 / 6 : ℝ) ∧
    massOp .vector sPlaneSinglet = 3 ^ (5 / 2 : ℝ) * Real.exp (5 / 4 - 5 * (9 / 4000) / 2) ∧
    Table.Row.mb / Table.Row.ms = Table.Row.q * Num.eta ∧
    Table.Row.B09 = 17 / 37 ∧ Table.Row.B11 = 17 / 37 * Num.kappa ^ 5 ∧
    Num.kappa = (3 / 2) ^ (8 / 5 : ℝ) ∧
    Table.Row.md = 3 ^ (3 / 2 : ℝ) / Num.eta ∧ Table.Row.ms = 3 ^ (3 / 2 : ℝ) * Table.Row.B04 / Num.eta ∧
    Table.Row.mb = 3 ^ (3 / 2 : ℝ) * (Table.Row.B04 * Table.Row.q) ∧ Table.Row.ms / Table.Row.md = Table.Row.B04 ∧
    Table.Row.mt = Num.Rud * Num.kappa ^ (15 / 2 : ℝ) * Table.Row.mb ∧
    (∀ S : Finset (Fin 6), clockOn .vector S = Real.exp ((statesN .vector - epsRec S) * ((signS S : ℝ) * nuS sLastDirectionSinglet) *
      ((1 / 10) * ∑ i, clockGap sLastDirectionSinglet i) / 4)) := by
  have heta : Num.eta ≠ 0 := by rw [Num.eta_eq]; norm_num
  have hmd : Table.Row.md ≠ 0 := by rw [Table.Row.md, Num.eta_eq]; positivity
  refine ⟨piece_Psi_plane, piece_Psi_planeSinglet, piece_eps.1, piece_eps.2, clockGap_hn, clock_moments.1,
    row_mu, row_tau, row_p_quark, row_q_quark, ?_, row_B09, ?_, Num.kappa_eq, rfl, ?_, ?_, ?_, rfl, ?_⟩
  · rw [Table.Row.mb, Table.Row.B05]; field_simp [Table.ms_pos.ne']
  · rw [Table.Row.B11, Table.Row.mc, Num.Rud_eq]; field_simp [Table.ms_pos.ne']
  · rw [Table.Row.ms, Table.Row.md]; ring
  · rw [Table.Row.mb, Table.Row.ms, Table.Row.md, Table.Row.B05, div_mul_eq_mul_div, div_mul_eq_mul_div,
      div_eq_iff heta]
    ring
  · rw [Table.Row.ms]; exact mul_div_cancel_left₀ _ hmd
  · intro S
    rw [clock_moments.1]
    simp only [clockOn]
    congr 1
    ring

/-- **Proposition 70 (sizes, moments and the cosmos).** A size of a closed excursion is the root of a count, read at
`{n}` with the power `s@{n} = 1/2`: `r_p = Eℓ^{1/2}λ_p = 4λ_p` and `r_π² = −6 d/dQ² G_P(e^{−Q²λ²/6})|₀ = E_Pλ²`
for every extent `λ`; `μ_p = [(Var ℓ/20)S_μ]^{1/2}`; `η_B = 3a¹¹`; `Λℓ_P² = 3τ(α_Gs)³ = 3W⁶τs³` with
`τ = 2π/(Eℓ m_p/m_e)` and `s = 3/50`; and the values `r_p = 0.84124 fm`, `η_B = 6.140·10⁻¹⁰`,
`Λℓ_P² = 2.855·10⁻¹²²`.

Recognition: the proton and pion charge radii, the proton's moment, baryons per photon, the cosmological constant;
the extent `λ_p = ħ/m_pc` of one step and the legs of `Λ` are the theory's. -/
theorem prop_70 :
    Num.El ^ (powS sSinglet) = 4 ∧ √Num.El = 4 ∧ Table.Row.G01 = Num.El ^ (powS sSinglet) * Num.lp ∧
    (∀ lam : ℝ, HasDerivAt (fun q : ℝ => GP (Real.exp (-(q * lam ^ 2) / 6))) (10 * (-(lam ^ 2) / 6)) 0 ∧
      -6 * (10 * (-(lam ^ 2) / 6)) = Num.EP * lam ^ 2) ∧
    Num.VarEll / 20 = 39 / 5 ∧ Table.Row.G03 = √(Num.VarEll / 20 * Table.Row.Smu) ∧
    Table.Row.F01 = 3 * Num.a ^ 11 * 10 ^ 10 ∧
    Table.Row.LambdaLP2 = 3 * Num.tau * (Num.W ^ 2 * Num.s) ^ 3 ∧ Num.s = 3 / 50 ∧
    ((0.8412356402125 : ℝ) < Table.Row.G01 ∧ Table.Row.G01 < 0.8412356402135) ∧
    ((6.140047623455 : ℝ) < Table.Row.F01 ∧ Table.Row.F01 < 6.140047623465) ∧
    ((2.855223243005 : ℝ) < Table.Row.D06 ∧ Table.Row.D06 < 2.855223243015) := by
  have hr : Num.El ^ (powS sSinglet) = 4 := by rw [Num.El_eq]; exact Comparison.RuleAndLaw.proton_radius_factor
  refine ⟨hr, ?_, by rw [hr, row_G01.1], fun lam => ⟨(pion_radius lam).1, ?_⟩, ?_, ?_, Table.F01_source,
    by rw [Table.Row.LambdaLP2]; ring, Num.s_eq, row_G01.2, row_F01.2, row_D06.2⟩
  · rw [Num.El_eq, show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  · rw [(pion_radius lam).2, Num.EP_eq]
  · rw [Num.VarEll_eq]; norm_num
  · rw [Table.Row.G03, Num.N2_eq]; norm_num

/-- **Proposition 72 (the repeated return is the law one level up).** With `u = i/4`, the excursions' generating
functions read at the powers of the last-step direction's phase: for every `k ≥ 1`, `p_k = Σ_n (−φ(n))(4uᵏ)ⁿ` (odd `k`) or
`Σ_n f(n)(4uᵏ)ⁿ` (even `k`), which is `−Φ(4uᵏ)` or `F(4uᵏ)`, real and positive, with `p_k ≤ (1/10)(1/256)^{k−1}`
for `k ≥ 2`; `p₁ = −Φ(i) = 1/13`, `p₂ = F(−1/4) = 1/6096`; `N(h) = Σ_k hᵏp_k`, and
`N(1) = 0.0770880771192…`.

Recognition: `N(h)` at the clock's overlap is the last-step direction's repeated return at `u = i/4` of the weak angle. The product
`Z₂(h) = Π_w(1 − hy_w)⁻¹` enters only through its logarithmic derivative's coefficients `p_k`. -/
theorem prop_72 :
    (∀ k : ℕ, 1 ≤ k →
      HasSum (fun n => (if Odd k then -(signedLaw n : ℂ) else (excursionLaw n : ℂ)) * (zPow k) ^ n) (repReturn k) ∧
      repReturn k = (repR k : ℂ) ∧ 0 < repR k) ∧
    (∀ k : ℕ, 2 ≤ k → repR k ≤ (1 / 10) * (1 / 256) ^ (k - 1)) ∧
    HasSum (fun n => -(signedLaw n : ℂ) * (4 * (I / 4)) ^ n) (1 / 13) ∧
    HasSum (fun n => (excursionLaw n : ℂ) * (4 * (I / 4) ^ 2) ^ n) (1 / 6096) ∧
    (∀ y : ℝ, Num.Nof y = ∑' k : ℕ, y ^ (k + 1) * repR (k + 1)) ∧
    Num.Nof 1 = N1 ∧ ((0.0770880771192245 : ℝ) < N1 ∧ N1 < 0.0770880771192250) :=
  ⟨fun k hk => ⟨Comparison.repReturn_hasSum k hk, Comparison.repReturn_real k hk, Comparison.repR_pos k hk⟩,
    fun k hk => (Comparison.repR_bound k hk).2, p_one, p_two, fun _ => rfl,
    (Article.N1_eq_NhOf_one).symm, N1_bounds⟩

/-- **`k` is central:** `k(hgh⁻¹) = k(g)` for all relabellings `g, h` of the five directions (sign and fixed points of a
conjugate). -/
theorem Completion.Comp.kk_central (g h : Equiv.Perm (Fin 5)) : SysPlanes.kk (h * g * h⁻¹) = SysPlanes.kk g := by
  have hs : SysPlanes.sgn (h * g * h⁻¹) = SysPlanes.sgn g := by
    unfold SysPlanes.sgn
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, mul_comm (Equiv.Perm.sign h),
      mul_assoc, Int.units_mul_self, mul_one]
  have hL : SysPlanes.fixL (h * g * h⁻¹) = SysPlanes.fixL g := by
    unfold SysPlanes.fixL
    congr 1
    refine Finset.card_bij (fun t _ => h⁻¹ t) (fun t ht => ?_) (fun a _ b _ hab => (Equiv.injective h⁻¹) hab)
      (fun s hs => ⟨h s, ?_, by simp⟩)
    · have ht' : h (g (h⁻¹ t)) = t := by simpa [Equiv.Perm.mul_apply] using (Finset.mem_filter.mp ht).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      have := congrArg (fun x => h⁻¹ x) ht'
      simpa using this
    · have hs' : g s = s := (Finset.mem_filter.mp hs).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      simp [Equiv.Perm.mul_apply, hs']
  have hF : SysPlanes.fixF (h * g * h⁻¹) = SysPlanes.fixF g := by
    unfold SysPlanes.fixF
    congr 1
    refine Finset.card_bij (fun i _ => SysPlanes.actF h⁻¹ i) (fun i hi => ?_)
      (fun a _ b _ hab => (SysPlanes.actF_inj h⁻¹).mp hab) (fun j hj => ⟨SysPlanes.actF h j, ?_, ?_⟩)
    · have hi' : SysPlanes.actF (h * g * h⁻¹) i = i := (Finset.mem_filter.mp hi).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [SysPlanes.actF_mul, SysPlanes.actF_mul] at hi'
      have := congrArg (SysPlanes.actF h⁻¹) hi'
      rwa [SysPlanes.actF_inv_actF] at this
    · have hj' : SysPlanes.actF g j = j := (Finset.mem_filter.mp hj).2
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [SysPlanes.actF_mul, SysPlanes.actF_mul, SysPlanes.actF_inv_actF, hj']
    · exact SysPlanes.actF_inv_actF h j
  unfold SysPlanes.kk SysPlanes.chi32
  rw [hs, hL, hF]

/-- **Proposition 73 (the plane contrasts).** From a plane the step along an outside line lands on the plane of the
other two outside lines; two symmetric states are one step apart exactly when disjoint: the Petersen graph, `A² = 2 − A + J`;
`Δ_F = 3 − A_F` has `det(X − Δ_F) = X(X − 2)⁵(X − 5)⁴`; over the nine contrasts `Σ x^{Δ_F} = 5x² + 4x⁵`; the
central idempotent `k(g) = (1 + sgn g + 5χ_[3,2](g))/120 = [1 + sgn g(5T(g) − 4)]/120`, `T(g)` the perfect
matchings `g` keeps (the Petersen graph has six), with `k(e) = 27/120`, `k(exchange) = 5/120`,
`k(5-cycle) = 2/120`, `k(3-cycle) = −3/120`, `Σ_g k(g) = 1` and `k·k = k`; the 120 relabellings commute with `Δ_F`,
the symmetric states carry `1 + χ_[4,1] + χ_[3,2]` and the lines `1 + χ_[4,1]`, the eigenprojectors of `0, 2, 5` (ranks
`1, 5, 4`) carry `1`, `χ_[3,2]`, `χ_[4,1]`, each irreducible (`Σ_gχ² = 120`, the characters orthogonal): the ten symmetric states
are `[5] + [3,2] + [4,1]`, the contrasts at `2` are `[3,2]` and at `5` are `[4,1]`; and `k` is central,
`k(hgh⁻¹) = k(g)`. -/
theorem prop_73 :
    (∀ i : Fin 10, ∀ c : Fin 5, c ∉ SysPlanes.planeSet i →
      ∃ j, transition c (SysPlanes.planeRel i) = SysPlanes.planeRel j ∧
        SysPlanes.planeSet j = Finset.univ \ insert c (SysPlanes.planeSet i)) ∧
    (∀ i j : Fin 10, (∃ c, transition c (SysPlanes.planeRel i) = SysPlanes.planeRel j) ↔
      Disjoint (SysPlanes.planeSet i) (SysPlanes.planeSet j)) ∧
    SysPlanes.petAdj * SysPlanes.petAdj = (2 : ℤ) • 1 - SysPlanes.petAdj + SysPlanes.J10 ∧
    SysPlanes.planeLap.charpoly = Polynomial.X * (Polynomial.X - 2) ^ 5 * (Polynomial.X - 5) ^ 4 ∧
    (∀ x : ℝ, ∑ i ∈ Finset.univ.filter (fun i : Fin 10 => SysPlanes.eigD i ≠ 0),
      x ^ (SysPlanes.eigD i).toNat = 5 * x ^ 2 + 4 * x ^ 5) ∧
    (SysPlanes.kk 1 = 27 ∧ SysPlanes.kk SysPlanes.exch = 5 ∧ SysPlanes.kk SysPlanes.cyc5 = 2 ∧
      SysPlanes.kk SysPlanes.cyc3 = -3) ∧
    ∑ g : Equiv.Perm (Fin 5), SysPlanes.kk g = 120 ∧
    (∀ g : Equiv.Perm (Fin 5),
      ∑ h : Equiv.Perm (Fin 5), SysPlanes.kk h * SysPlanes.kk (h⁻¹ * g) = 120 * SysPlanes.kk g) ∧
    (∀ S : Finset (Fin 15), SysPlanes.IsPerfectMatching S ↔ S ∈ SysPlanes.matchings) ∧
    (∀ g : Equiv.Perm (Fin 5), SysPlanes.kk g = 1 + SysPlanes.sgn g * (5 * SysPlanes.keptMatchings g - 4)) ∧
    (∀ g : Equiv.Perm (Fin 5), SysPlanes.planeLapZ * SysPlanes.permF g = SysPlanes.permF g * SysPlanes.planeLapZ) ∧
    (∀ g : Equiv.Perm (Fin 5), SysPlanes.fixF g = 1 + SysPlanes.chi41 g + SysPlanes.chi32 g ∧
      SysPlanes.fixL g = 1 + SysPlanes.chi41 g) ∧
    (SysPlanes.P0Z * SysPlanes.P0Z = (10 : ℤ) • SysPlanes.P0Z ∧ SysPlanes.P2Z * SysPlanes.P2Z = (6 : ℤ) • SysPlanes.P2Z ∧
      SysPlanes.P5Z * SysPlanes.P5Z = (15 : ℤ) • SysPlanes.P5Z ∧
      SysPlanes.P0Z * SysPlanes.P2Z = 0 ∧ SysPlanes.P0Z * SysPlanes.P5Z = 0 ∧ SysPlanes.P2Z * SysPlanes.P5Z = 0 ∧
      (3 : ℤ) • SysPlanes.P0Z + (5 : ℤ) • SysPlanes.P2Z + (2 : ℤ) • SysPlanes.P5Z = (30 : ℤ) • 1 ∧
      SysPlanes.planeLapZ * SysPlanes.P0Z = 0 ∧ SysPlanes.planeLapZ * SysPlanes.P2Z = (2 : ℤ) • SysPlanes.P2Z ∧
      SysPlanes.planeLapZ * SysPlanes.P5Z = (5 : ℤ) • SysPlanes.P5Z ∧
      SysPlanes.P0Z.trace = 10 * 1 ∧ SysPlanes.P2Z.trace = 6 * 5 ∧ SysPlanes.P5Z.trace = 15 * 4) ∧
    (∀ g : Equiv.Perm (Fin 5), (SysPlanes.P0Z * SysPlanes.permF g).trace = 10 * 1 ∧
      (SysPlanes.P2Z * SysPlanes.permF g).trace = 6 * SysPlanes.chi32 g ∧
      (SysPlanes.P5Z * SysPlanes.permF g).trace = 15 * SysPlanes.chi41 g) ∧
    (∑ g : Equiv.Perm (Fin 5), SysPlanes.chi32 g ^ 2 = 120 ∧ ∑ g : Equiv.Perm (Fin 5), SysPlanes.chi41 g ^ 2 = 120 ∧
      ∑ g : Equiv.Perm (Fin 5), SysPlanes.chi32 g * SysPlanes.chi41 g = 0 ∧
      ∑ g : Equiv.Perm (Fin 5), SysPlanes.chi32 g = 0 ∧ ∑ g : Equiv.Perm (Fin 5), SysPlanes.chi41 g = 0 ∧
      ∑ g : Equiv.Perm (Fin 5), SysPlanes.sgn g * SysPlanes.chi32 g = 0 ∧
      ∑ g : Equiv.Perm (Fin 5), SysPlanes.sgn g * SysPlanes.chi41 g = 0 ∧ ∑ g : Equiv.Perm (Fin 5), SysPlanes.sgn g = 0) ∧
    (∀ g h : Equiv.Perm (Fin 5), SysPlanes.kk (h * g * h⁻¹) = SysPlanes.kk g) :=
  ⟨SysPlanes.plane_step_outside, SysPlanes.petersen_steps, SysPlanes.petersen_srg, SysPlanes.planeLap_charpoly,
    fun x => SysPlanes.contrast_sum x, SysPlanes.k_values, SysPlanes.k_sum, SysPlanes.k_idem,
    SysPlanes.perfect_matchings, SysPlanes.k_second_form, SysPlanes.planeLap_comm_perm, SysPlanes.planes_char,
    SysPlanes.projectors, fun g => ⟨SysPlanes.trace_P0 g, SysPlanes.trace_P2 g, SysPlanes.trace_P5 g⟩,
    SysPlanes.char_norms, Completion.Comp.kk_central⟩

open Filter Topology Asymptotics in
/-- **Proposition 71 (the long-range zero under a weight on the steps).** For every weighted walk `P(s)` (a finite
nonnegative step with `P(0)` stochastic, `π` its positive stationary law, `P(s) = P₀ + sP₁ + (s²/2)P₂ + O(s³)`) and
every Poisson solution `g`: `log ρ(s)` has the derivative `v = πP₁𝟏` at `0` and
`log ρ(s) = sv + (s²/2)σ² + O(s³)`, `σ² = πP₂𝟏 + 2πP₁g − v²`; since `u_c = 1/ρ(B_s)`, `log 4u_c(s) = −log ρ(B_s/4)`.
A weight `t` on every step moves the zero to `1/(4t)`, `log 4u_c = log(1/t)`. On the eighty states the steps along
a last-step direction have `v = 1/5` and `σ² = 12/125`; per excursion the available transitions of `h` are visited `74/5` times and takes
`E_H = C_h/20 = (Eℓ − 1)/5 = 3` continuations along `h`; a divergence-free flux `θ` has the variance
`‖θ‖²/24` per step and `log 4u_c = ‖θ_cyc‖²/48 + O(θ⁴)`; marks on the arrivals at symmetric states and vector states have
`v = (E_P, E_Q)/Eℓ = (10, 5)/16`, and the centred marks `(P − (E_P/Eℓ)ℓ, Q − (E_Q/Eℓ)ℓ)` (`ℓ = P + Q + 1`) have the
covariance `MΣMᵀ = [[39/16, −45/32], [−45/32, 63/64]]` with `Σ = [[Var P, Cov], [Cov, Var Q]] = [[84, 30], [30, 12]]`.

The theorem proves the expansion for every weighted walk and the numbers above; the spread per step of the marks as
`C/Eℓ`, from the independence of the excursions, is the statement that completes Prop. 71. -/
theorem prop_71 :
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (P : ℝ → Matrix ι ι ℝ) (P0 P1 P2 : Matrix ι ι ℝ)
      (p₀ : ι → ℝ), WeightedWalk P P0 P1 P2 p₀ → ∀ g : ι → ℝ,
        (1 - P0) *ᵥ g = P1 *ᵥ 1 - (p₀ ⬝ᵥ (P1 *ᵥ 1)) • 1 → p₀ ⬝ᵥ g = 0 →
        HasDerivAt (fun s => Real.log (perronRoot P s)) (p₀ ⬝ᵥ (P1 *ᵥ 1)) 0 ∧
        (fun s => Real.log (perronRoot P s) - (s * (p₀ ⬝ᵥ (P1 *ᵥ 1)) + s ^ 2 / 2 *
          (p₀ ⬝ᵥ (P2 *ᵥ 1) + 2 * (p₀ ⬝ᵥ (P1 *ᵥ g)) - (p₀ ⬝ᵥ (P1 *ᵥ 1)) ^ 2))) =O[𝓝 0] (fun s => s ^ 3)) ∧
    (∀ t : ℝ, 0 < t →
      (1 - ((1 / (4 * t) : ℝ) : ℂ) • ((t : ℂ) • stepT (fun _ _ => (1 : ℂ)))).det = 0 ∧
      (∀ u : ℝ, 0 ≤ u → u < 1 / (4 * t) → (1 - (u : ℂ) • ((t : ℂ) • stepT (fun _ _ => (1 : ℂ)))).det ≠ 0) ∧
      Real.log (4 * (1 / (4 * t))) = Real.log (1 / t)) ∧
    (∀ h : Fin 5, HasDerivAt (fun s => Real.log (perronRoot (lastDirectionWalk h) s)) (1 / 5) 0 ∧
      (fun s => Real.log (perronRoot (lastDirectionWalk h) s) - (s * (1 / 5) + s ^ 2 / 2 * (12 / 125)))
        =O[𝓝 0] (fun s => s ^ 3)) ∧
    (∀ h : Fin 5, HasSum (fun n => (∑ s ∈ excursionStates h, (stateCount n s : ℝ)) / (5 * 4 ^ n)) (74 / 5) ∧
      HasSum (fun n => (∑ s ∈ (excursionStates h).filter (fun s => s.2 ≠ h), (stateCount n s : ℝ)) /
        (5 * 4 ^ n) / 4) 3) ∧
    (Num.Ch : ℝ) / 20 = 3 ∧ (Num.El - 1) / 5 = 3 ∧
    (∀ θ : Fin 40 → ℝ, (∀ x, WholePicture.divR θ x = 0) →
      (∑ x, ∑ t, ∑ s, (if s = t then 0 else
        ((4 * GroupsContinuumLaw.phase16 θ (transition s x) x - GroupsContinuumLaw.phase16 θ x (transition t x)) / 3) ^ 2)) / 320 =
        WholePicture.sqL θ / 24) ∧
    Num.EP / Num.El = 10 / 16 ∧ Num.EQ / Num.El = 5 / 16 ∧
    (!![1 - Num.EP / Num.El, -(Num.EP / Num.El); -(Num.EQ / Num.El), 1 - Num.EQ / Num.El] :
        Matrix (Fin 2) (Fin 2) ℝ) * (!![Num.VarP, Num.Cov; Num.Cov, Num.VarQ] : Matrix (Fin 2) (Fin 2) ℝ) *
      Matrix.transpose (!![1 - Num.EP / Num.El, -(Num.EP / Num.El); -(Num.EQ / Num.El), 1 - Num.EQ / Num.El] :
        Matrix (Fin 2) (Fin 2) ℝ) =
      (!![39 / 16, -45 / 32; -45 / 32, 63 / 64] : Matrix (Fin 2) (Fin 2) ℝ) := by
  refine ⟨fun P P0 P1 P2 p₀ hW g hg hpg => perron_log hW g hg hpg, fun t ht => weight_moves_zero t ht,
    fun h => ⟨(lastDirection_velocity h).2.1, (lastDirection_velocity h).2.2⟩,
    fun h => ⟨availableTransitions_visits h, steps_along_lastDirection h⟩, ?_, ?_, fun θ hθ => GroupsContinuumLaw.phase_variance θ hθ,
    ?_, ?_, ?_⟩
  · rw [Num.Ch_eq]; norm_num
  · rw [Num.El_eq]; norm_num
  · rw [Num.EP_eq, Num.El_eq]
  · rw [Num.EQ_eq, Num.El_eq]
  · rw [Num.EP_eq, Num.EQ_eq, Num.El_eq, Num.VarP_eq, Num.Cov_eq, Num.VarQ_eq]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;> norm_num

/-- **Equation (31).** The coupling is the mixed derivative of the two-source function on the vertices,
`σ = ∂²W/∂J₁∂J₂ = Σ_x P₁(x)P₂(x)`, `W = −Σ_x log(1 − J₁P₁(x) − J₂P₂(x))` (the closed member of the source family with
the two ends' chances on the vertices), for every number of vertices and every two chance vectors; with `N` equal
channels, `σ = e²/N`. Recognition: `σ` the coupling between two charges (Coulomb) and two masses (Newton). The same
derivative for sources that do not act on the vertices one by one, `Tr(K⁻¹X₁K⁻¹X₂)` by Jacobi's formula applied twice,
is the statement that completes Eq. (31). -/
theorem eq_31 :
    (∀ (N : ℕ) (P₁ P₂ : Fin N → ℝ),
      deriv (fun J₂ => deriv (fun J₁ => Article.Wtwo P₁ P₂ J₁ J₂) 0) 0 = ∑ x, P₁ x * P₂ x) ∧
    (∀ (N : ℕ), 0 < N → ∀ e : ℝ, ∑ _x : Fin N, (e / N) * (e / N) = e ^ 2 / N) :=
  ⟨fun _ P₁ P₂ => Article.mixed_derivative P₁ P₂, fun N hN e => Article.equal_places N hN e⟩

/-- **Equation (32).** The contact `x = νh/(M + 1 + N_h)`, `ν = e_even²/(N₂Eℓ) = 9/4000`, and
`x = 7.5735725447·10⁻⁶`. -/
theorem eq_32 :
    Num.x = Num.nu * Num.h / ((Num.M : ℝ) + 1 + Num.Nh) ∧ Num.nu = Num.e ^ 2 / (Num.N2 * Num.El) ∧
    Num.nu = 9 / 4000 ∧ ((7.5735725447e-6 : ℝ) < Num.x ∧ Num.x < 7.5735725448e-6) := by
  refine ⟨rfl, ?_, Num.nu_eq, ?_⟩
  · rw [Num.nu_eq, Num.e_eq, Num.N2_eq, Num.El_eq]; norm_num
  · rw [Num.x_eq_q]
    exact ⟨lt_of_lt_of_le (by norm_num) Article.qX_bnd.1, lt_of_le_of_lt Article.qX_bnd.2 (by norm_num)⟩

/-- **Equation (33).** `h = [M_Q(ν)M_Q(−ν)]^{−3/2}`, `M_Q(s) = (1/10)Σ_D e^{−sD}` over the ten gaps of the clock's
marks `(0, 1, 2, 3, −1/Φ(1))/4 = (0, 1, 2, 3, 19)/4`; `h = 0.99997104932968…` (Prop. 206). -/
theorem eq_33 :
    Num.h = (Num.MQ Num.nu * Num.MQ (-Num.nu)) ^ (-(3 / 2 : ℝ)) ∧ Num.nu = 9 / 4000 ∧
    (∀ x : ℝ, Num.MQ x = (1 / 10) * ∑ i, Real.exp (-(x * clockGap sLastDirectionSinglet i))) ∧
    longMark sLastDirectionSinglet = 19 ∧ -1 / Num.Phi 1 = 19 ∧
    ((0.99997104932968 : ℝ) < Num.h ∧ Num.h < 0.99997104932969) := by
  refine ⟨by rw [Num.nu_eq]; exact Num.h_closed, Num.nu_eq, fun x => rfl, piece_longMark_hn,
    by rw [Num.Phi_one]; norm_num, ?_⟩
  rw [Num.h_eq_q]
  exact ⟨lt_of_lt_of_le (by norm_num) Article.qH_bnd.1, lt_of_le_of_lt Article.qH_bnd.2 (by norm_num)⟩

/-- **Equation (34).** `N_h = Re Σ_{j ≥ 1} hʲp_j(4(i/4)ʲ)` with `p_j = −Φ` at odd `j` and `F` at even `j`;
`N_h = 0.07708584056314…`. -/
theorem eq_34 :
    Num.Nh = ∑' k : ℕ, Num.h ^ (k + 1) * repR (k + 1) ∧
    (∀ k : ℕ, 1 ≤ k → repReturn k = (repR k : ℂ) ∧
      HasSum (fun n => (if Odd k then -(signedLaw n : ℂ) else (excursionLaw n : ℂ)) * (zPow k) ^ n) (repReturn k)) ∧
    ((0.07708584056314 : ℝ) < Num.Nh ∧ Num.Nh < 0.07708584056315) := by
  refine ⟨rfl, fun k hk => ⟨Comparison.repReturn_real k hk, Comparison.repReturn_hasSum k hk⟩, ?_⟩
  rw [Num.Nh_eq_q]
  exact ⟨lt_of_lt_of_le (by norm_num) Article.qNh_bnd.1, lt_of_le_of_lt Article.qNh_bnd.2 (by norm_num)⟩

/-- **Equation (35).** `log 4u_c = ‖θ_cyc‖²/48 + O(θ⁴)` (with the explicit bound `‖θ_cyc‖⁴/20` for
`‖θ_cyc‖² ≤ 1/100`), `48 = k_C Eℓ = 2(40 − 16)`. -/
theorem eq_35 :
    (∀ θ : Fin 40 → ℝ, WholePicture.sqL (WholePicture.thetaCyc θ) ≤ 1 / 100 →
      |Real.log (4 * WholePicture.ucrit θ) - WholePicture.sqL (WholePicture.thetaCyc θ) / 48| ≤
        WholePicture.sqL (WholePicture.thetaCyc θ) ^ 2 / 20) ∧
    (Num.kC : ℝ) * Num.El = 48 ∧
    2 * ((Finset.univ.filter fun p : Fin 16 × Fin 16 => p.1 < p.2 ∧ Adjacent p.1 p.2).card -
      Fintype.card (Fin 16)) = 48 := by
  refine ⟨fun θ hθ => (WholePicture.long_range_zero θ hθ).2.2, ?_, by rw [card_edges]; simp⟩
  rw [Num.kC_eq, Num.El_eq]; norm_num

/-- **Equation (36), its numbers.** With the stiffness `κ = 2w⁴/(1 − 5w²)² = 2/[(χ + 5)² − 5]²` at the point `u = −1/4`
(`χ = 0, −10`: `κ = 1/200`) and at colour (`χ = −5 ± 3i`: `κ = 1/98`): `8πκα = 9.170124·10⁻⁴`,
`8πκα_s = 3.022369·10⁻²`, `1/16πα = 2.726245`; `κ` is the law's response: the second variation of the law in the
link phases is `−(2w⁴/(1 − 5w²)²)G` for every `w` with `1 − 5w² ≠ 0` (W's Prop. 116). The identity
`∫F² = 8πκα‖Cθ‖²` itself, the continuum field in units of the charge, stands with W's continuum limit and completes
Eq. (36). -/
theorem eq_36 :
    (∀ (w : ℂ), 1 - 5 * w ^ 2 ≠ 0 → ∀ j k : Fin 40,
      WholePicture.hessLaw w j k = -(2 * w ^ 4 / (1 - 5 * w ^ 2) ^ 2) * (GZ j k : ℂ)) ∧
    (2 : ℂ) / ((Formulas.chi (1 / 4) + 5) ^ 2 - 5) ^ 2 = 1 / 200 ∧
    (2 : ℂ) / ((Formulas.chi (I / 4) + 5) ^ 2 - 5) ^ 2 = 1 / 98 ∧
    ((9.1701235e-4 : ℝ) < 8 * π * (1 / 200) * Num.alpha ∧ 8 * π * (1 / 200) * Num.alpha < 9.1701245e-4) ∧
    ((3.0223685e-2 : ℝ) < 8 * π * (1 / 98) * Num.alphaS ∧ 8 * π * (1 / 98) * Num.alphaS < 3.0223695e-2) ∧
    ((2.7262445 : ℝ) < 1 / (16 * π * Num.alpha) ∧ 1 / (16 * π * Num.alpha) < 2.7262455) := by
  rw [Num.alpha_eq_q, Num.alphaS_eq_q]
  exact ⟨fun w hw j k => WholePicture.hessLaw_eq w hw j k, Formulas.kappa_gap_values.1,
    Formulas.kappa_gap_values.2.2.1, Article.flux_metric_numbers⟩

end Comparison.System
