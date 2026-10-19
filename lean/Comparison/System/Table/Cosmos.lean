import Comparison.System.Completion.Numbers

set_option linter.style.longLine false

/-!
# The proof system, the table, part 4: the stationary state, gravity's sequence, the partial lifetime

Rows C15, C16, L06, F01, F03, F04, F13, L07, L08, D06, D07, L09, L10, L11, S08, S09, T03,
T04, K06, L12 of Table X (Props. 70, 118, 127; Eq. (45)).

Recognitions: C15 the scalar tilt `n_s`, C16 and L06 its running, F01 baryons per photon `η_B` [10⁻¹⁰], F03 the
primordial amplitude `ln(10¹⁰A_s)`, F04 the effective neutrino number, F13 and L07 the spatial curvature, L08 the
equation of state of the constant term, D06 the cosmological constant `Λℓ_P²` [10⁻¹²²], D07 and L09 the drift of `α`
in a potential, L10 the de Sitter horizon entropy, L11 the tensor-to-scalar ratio in the de Sitter convention, S08
the primordial amplitude second construction [10⁻⁹], S09 the cold/baryon count second construction, T03 the de
Sitter radius [Mpc], T04 the de Sitter temperature [eV], K06 and L12 the proton's partial lifetime [yr].

What is the law's and what is not: `n_s = 1 − t/Eℓ`, `η_B = 3a¹¹`, `N_eff = 3ησ^{4/3}`, `Λℓ_P² = 3W⁶τs³`, `ℓ`,
`A_s = 12a¹¹(k_*ℓ)^{n_s−1}` and the lifetime are compositions of the law's numbers (the occupation rules of Prop. 127
and the sequence of Prop. 118 are the theory's, C). The 3 and the 12 have one source: `η_B = C′(0)` and
`A_s = C″(0)(k_*ℓ)^{n_s−1}`, the two derivatives of the connected source `C(j) = a¹¹ log G(e^j)` of the one positive
volume, `G(x) = 1/(4 − 3x)` the arrivals at the vector states beyond the two compulsory ones of every return
(`Num.sourceC`, `Num.sourceC_deriv`, `Num.sourceC_second`). Rows C16, L06, D07, L09 are the derivative of a constant:
the law's `n_s` carries no scale and `α` no vertex, by their definitions; F13, L07 (`Ω_k = 0`) and L08 (`w = −1`) are
stated by the theory, the first as the flat stationary frame, the second as the stress `−ρη` of a constant term; the
law's statements behind these seven (a spectrum from the law at each scale, the frame's curvature and the constant
term from the field equations) stand with W's continuum limit. Outside inputs: `m_e c²`, `ħ`, `ħc`, the megaparsec,
the Julian year, the pivot `k_* = 0.05 Mpc⁻¹`.
-/

namespace Comparison.System.Table

open Real Complex Matrix Comparison Comparison.Law Comparison.System.Completion

namespace Row

/-- C15, `n_s = 1 − t/Eℓ`. -/
noncomputable def C15 : ℝ := Num.ns
/-- F01, `η_B = C′(0) = a¹¹E K = 3a¹¹` [10⁻¹⁰]: the first derivative of the connected source. -/
noncomputable def F01 : ℝ := deriv Num.sourceC 0 * 10 ^ 10
/-- `A_s = C″(0)(k_*ℓ)^{n_s−1} = a¹¹Var K(k_*ℓ)^{n_s−1} = 12a¹¹(k_*ℓ)^{n_s−1}`: the second derivative of the same source. -/
noncomputable def As : ℝ := deriv (deriv Num.sourceC) 0 * (Num.kstar * Num.ell) ^ (Num.ns - 1)
/-- F03, `ln(10¹⁰A_s)`. -/
noncomputable def F03 : ℝ := Real.log (10 ^ 10 * As)
/-- F04, `N_eff = 3ησ^{4/3}`. -/
noncomputable def F04 : ℝ := 3 * Num.eta * Num.sigma ^ (4 / 3 : ℝ)
/-- `Λℓ_P² = 3W⁶τs³`. -/
noncomputable def LambdaLP2 : ℝ := 3 * Num.W ^ 6 * Num.tau * Num.s ^ 3
/-- D06, `Λℓ_P²` [10⁻¹²²]. -/
noncomputable def D06 : ℝ := LambdaLP2 * 10 ^ 122
/-- L10, `3π/Λℓ_P²`. -/
noncomputable def L10 : ℝ := 3 * π / LambdaLP2
/-- L11, `16Λℓ_P²/(3π C″(0)) = 16Λℓ_P²/(3π·12a¹¹)`. -/
noncomputable def L11 : ℝ := 16 * LambdaLP2 / (3 * π * deriv (deriv Num.sourceC) 0)
/-- S08, `b²⁴(k_*ℓ)^{n_s−1}` [10⁻⁹]. -/
noncomputable def S08 : ℝ := Num.b ^ 24 * (Num.kstar * Num.ell) ^ (Num.ns - 1) * 10 ^ 9
/-- S09, `M/(M − 4C_h)`. -/
noncomputable def S09 : ℝ := (Num.M : ℝ) / ((Num.M : ℝ) - 4 * Num.Ch)
/-- T03, `ℓ = λ_p/(W²(τs³)^{1/2})` [Mpc]. -/
noncomputable def T03 : ℝ := Num.ell
/-- T04, `ħc/(2πℓ)` [eV]. -/
noncomputable def T04 : ℝ := Num.hc * 10 ^ 6 / (2 * π * Num.ell * Num.Mpc)
/-- K06, L12, `ħ(M_off/m_p)⁴/(α_s⁴m_p)` with `M_off/m_p = e_line⁶/W` [yr]. -/
noncomputable def K06 : ℝ := Num.hbar * (Num.eLine ^ 6 / Num.W) ^ 4 / (Num.alphaS ^ 4 * Num.mp) / Num.year
noncomputable def L12 : ℝ := K06
/-- F13, L07, `Ω_k`: the value the theory states for the stationary frame (no law object computes it yet). -/
def F13 : ℝ := 0
def L07 : ℝ := 0

end Row

theorem LambdaLP2_eq_q : Row.LambdaLP2 = Article.qLam := by
  rw [Row.LambdaLP2, Num.W_eq_q, Num.tau_eq_q, Num.s_eq, Article.qLam]; norm_num

/-- **`η_B = C′(0) = a¹¹E K = 3a¹¹`** (`Num.sourceC_deriv`, `Num.EK_eq`). -/
theorem F01_source : Row.F01 = 3 * Num.a ^ 11 * 10 ^ 10 := by
  rw [Row.F01, Num.sourceC_deriv, Num.EK_eq]
  ring

/-- **`A_s = C″(0)(k_*ℓ)^{n_s−1} = 12a¹¹(k_*ℓ)^{n_s−1}`** (`Num.sourceC_second`, `Num.VarK_eq`). -/
theorem As_source : Row.As = 12 * Num.a ^ 11 * (Num.kstar * Num.ell) ^ (Num.ns - 1) := by
  rw [Row.As, Num.sourceC_second, Num.VarK_eq]
  ring

/-- `L11 = 16Λℓ_P²/(3π·12a¹¹)`. -/
theorem L11_source : Row.L11 = 16 * Row.LambdaLP2 / (3 * π * (12 * Num.a ^ 11)) := by
  rw [Row.L11, Num.sourceC_second, Num.VarK_eq]
  ring

theorem As_eq_q : Row.As = Article.qAs := by
  rw [As_source, Num.a_eq, Num.kstar, Num.ell_eq_q, Num.ns_eq, Article.qAs, Article.qKl]; norm_num

end Comparison.System.Table

namespace Comparison.System

open Real Complex Matrix Comparison Comparison.Law Comparison.System.Completion Comparison.System.Table

/-- **Row C15.** `n_s = 1 − t/Eℓ = 39/40`. Recognition: the scalar tilt. -/
theorem row_C15 : Table.Row.C15 = 39 / 40 := Num.ns_eq

/-- **Row C16.** The law's tilt is one number, with no scale: its running `d n_s/d ln k` is the derivative of a
constant, `0`. Recognition: the running of the tilt. The law's spectrum at each scale is the statement that completes
the row. -/
theorem row_C16 : deriv (fun _lnk : ℝ => Table.Row.C15) 0 = 0 := deriv_const 0 _

/-- **Row L06.** As C16. Recognition: the scalar-index running. -/
theorem row_L06 : deriv (fun _lnk : ℝ => Table.Row.C15) 0 = 0 := deriv_const 0 _

/-- **Row F01.** `η_B = C′(0) = a¹¹E K = 3a¹¹ = 6.14004762346·10⁻¹⁰`, the first derivative of the connected source
`C(j) = a¹¹ log G(e^j)` (`F01_source`). Recognition: baryons per photon. -/
theorem row_F01 : Table.Row.F01 = 3 * (5 / 38) ^ 11 * 10 ^ 10 ∧
    (6.140047623455 : ℝ) < Table.Row.F01 ∧ Table.Row.F01 < 6.140047623465 := by
  have e : Table.Row.F01 = Article.rowF01 := by rw [F01_source, Num.a_eq, Article.rowF01]; norm_num
  exact ⟨by rw [F01_source, Num.a_eq], by rw [e]; exact Article.rowF01_digits⟩

/-- **Row F03.** `ln(10¹⁰A_s)`, `A_s = C″(0)(k_*ℓ)^{n_s−1} = a¹¹Var K(k_*ℓ)^{n_s−1} = 12a¹¹(k_*ℓ)^{n_s−1}`, the
second derivative of the same source (`As_source`): `3.06130986015`. Recognition: the primordial amplitude;
`k_* = 0.05 Mpc⁻¹` is the measurement's pivot (outside). -/
theorem row_F03 : Table.Row.F03 = Real.log (10 ^ 10 * (12 * (5 / 38) ^ 11 * (1 / 20 * Num.ell) ^ (-(1 / 40 : ℝ)))) ∧
    (3.061309860145 : ℝ) < Table.Row.F03 ∧ Table.Row.F03 < 3.061309860155 := by
  refine ⟨by rw [Table.Row.F03, As_source, Num.a_eq, Num.kstar, Num.ns_eq]; norm_num, ?_⟩
  rw [Table.Row.F03, As_eq_q]
  have := Article.rowF03_digits
  rw [Article.rowF03] at this
  convert this using 3 <;> norm_num

/-- **Row F04.** `N_eff = 3ησ^{4/3} = 3.04385727362`. Recognition: the effective neutrino number. -/
theorem row_F04 : Table.Row.F04 = 3 * (295 / 296) * (75 / 74 : ℝ) ^ (4 / 3 : ℝ) ∧
    (3.043857273615 : ℝ) < Table.Row.F04 ∧ Table.Row.F04 < 3.043857273625 := by
  have e : Table.Row.F04 = 3 * (295 / 296) * (75 / 74 : ℝ) ^ (4 / 3 : ℝ) := by
    rw [Table.Row.F04, Num.eta_eq, Num.sigma_eq]
  refine ⟨e, ?_⟩
  rw [e]
  have := Article.rowF04_digits
  rw [Article.rowF04] at this
  convert this using 2 <;> norm_num

/-- **Row F13.** `Ω_k = 0`. Recognition: the spatial curvature; the theory states the stationary frame flat; the
frame's curvature from the field equations is the statement that completes the row. -/
theorem row_F13 : Table.Row.F13 = 0 := rfl

/-- **Row L07.** As F13. -/
theorem row_L07 : Table.Row.L07 = 0 := rfl

/-- **Row L08.** A constant term's stress `T = −ρη` has `w = p/ρ = −1`. Recognition: the equation of state of the
constant term. -/
theorem row_L08 : Article.rowL08 = -1 := Article.rowL08_digits

/-- **Row D06.** `Λℓ_P² = 3W⁶τs³ = 2.85522324301·10⁻¹²²`. Recognition: the cosmological constant. -/
theorem row_D06 : Table.Row.D06 = 3 * Num.W ^ 6 * Num.tau * (3 / 50) ^ 3 * 10 ^ 122 ∧
    (2.855223243005 : ℝ) < Table.Row.D06 ∧ Table.Row.D06 < 2.855223243015 := by
  refine ⟨by rw [Table.Row.D06, Table.Row.LambdaLP2, Num.s_eq], ?_⟩
  rw [Table.Row.D06, LambdaLP2_eq_q]
  have := Article.rowD06_digits
  rw [Article.rowD06] at this
  convert this using 2 <;> norm_num

/-- **Row D07.** `α` is one number of the law, with no vertex: `d log α/d(Φ/c²)` is the derivative of a constant,
`0`. Recognition: the drift of `α` in a gravitational potential. -/
theorem row_D07 : deriv (fun _phi : ℝ => Real.log Num.alpha) 0 = 0 := deriv_const 0 _

/-- **Row L09.** As D07. Recognition: a recorded electric fact does not change. -/
theorem row_L09 : deriv (fun _phi : ℝ => Real.log Num.alpha) 0 = 0 := deriv_const 0 _

/-- **Row L10.** `3π/Λℓ_P² = 3.30089003858·10¹²²`. Recognition: the de Sitter horizon entropy. -/
theorem row_L10 : Table.Row.L10 = 3 * π / Table.Row.LambdaLP2 ∧
    (3.300890038575e122 : ℝ) < Table.Row.L10 ∧ Table.Row.L10 < 3.300890038585e122 := by
  refine ⟨rfl, ?_⟩
  rw [Table.Row.L10, LambdaLP2_eq_q]; exact Article.rowL10_digits

/-- **Row L11.** `16Λℓ_P²/(3π·12a¹¹) = 1.9735911755·10⁻¹¹³`. Recognition: the tensor-to-scalar ratio in the de
Sitter convention. -/
theorem row_L11 : Table.Row.L11 = 16 * Table.Row.LambdaLP2 / (3 * π * (12 * (5 / 38) ^ 11)) ∧
    (1.97359117545e-113 : ℝ) < Table.Row.L11 ∧ Table.Row.L11 < 1.97359117555e-113 := by
  refine ⟨by rw [L11_source, Num.a_eq], ?_⟩
  rw [L11_source, LambdaLP2_eq_q, Num.a_eq]
  have := Article.rowL11_digits
  rw [Article.rowL11] at this
  convert this using 3 <;> norm_num

/-- **Row S08.** `b²⁴(k_*ℓ)^{n_s−1} = 2.1025756247·10⁻⁹`. Recognition: the primordial amplitude, second
construction. -/
theorem row_S08 : Table.Row.S08 = (7 / 16) ^ 24 * (1 / 20 * Num.ell) ^ (-(1 / 40 : ℝ)) * 10 ^ 9 ∧
    (2.10257562465 : ℝ) < Table.Row.S08 ∧ Table.Row.S08 < 2.10257562475 := by
  refine ⟨by rw [Table.Row.S08, Num.b_eq, Num.kstar, Num.ns_eq]; norm_num, ?_⟩
  rw [Table.Row.S08, Num.b_eq, Num.kstar, Num.ell_eq_q, Num.ns_eq]
  have := Article.rowS08_digits
  rw [Article.rowS08, Article.qKl] at this
  convert this using 3 <;> norm_num

/-- **Row S09.** `M/(M − 4C_h) = 37/7`. Recognition: the cold/baryon count, second construction. -/
theorem row_S09 : Table.Row.S09 = 37 / 7 := by
  rw [Table.Row.S09, Num.M_eq, Num.Ch_eq]; norm_num

/-- **Row T03.** `ℓ = λ_p/(W²(τs³)^{1/2}) = 5369.08213305 Mpc`. Recognition: the de Sitter radius. -/
theorem row_T03 : Table.Row.T03 = Num.lp / (Num.W ^ 2 * √(Num.tau * (3 / 50) ^ 3)) / Num.Mpc ∧
    (5369.082133045 : ℝ) < Table.Row.T03 ∧ Table.Row.T03 < 5369.082133055 := by
  refine ⟨by rw [Table.Row.T03, Num.ell, Num.s_eq], ?_⟩
  rw [Table.Row.T03, Num.ell_eq_q]; exact Article.rowT03_digits

/-- **Row T04.** `ħc/(2πℓ) = 1.89564063246·10⁻³⁴ eV`. Recognition: the de Sitter temperature. -/
theorem row_T04 : Table.Row.T04 = Num.hc * 10 ^ 6 / (2 * π * Num.ell * Num.Mpc) ∧
    (1.895640632455e-34 : ℝ) < Table.Row.T04 ∧ Table.Row.T04 < 1.895640632465e-34 := by
  refine ⟨rfl, ?_⟩
  rw [Table.Row.T04, Num.hc_eq_q, Num.ell_eq_q, Num.Mpc]
  have := Article.rowT04_digits
  rw [Article.rowT04] at this
  convert this using 3 <;> norm_num

/-- **Row K06.** `ħ(M_off/m_p)⁴/(α_s⁴m_p) = 72²ħ/(3²⁴W⁴m_p) = 1.16971098946·10³⁷ yr`. Recognition: the proton's
partial lifetime `τ/B(e⁺π⁰)`. -/
theorem row_K06 : Table.Row.K06 = 72 ^ 2 * Num.hbar / (3 ^ 24 * Num.W ^ 4 * Num.mp) / Num.year ∧
    (1.169710989455e37 : ℝ) < Table.Row.K06 ∧ Table.Row.K06 < 1.169710989465e37 := by
  have hW : Num.W ≠ 0 := by rw [Num.W_closed]; positivity
  have hm : Num.mp ≠ 0 := by
    rw [Num.mp_eq_q]; exact (lt_of_lt_of_le (by norm_num) Article.qMp_bnd.1).ne'
  have ha : Num.alphaS ^ 4 = 1 / 72 ^ 2 := by
    rw [show Num.alphaS ^ 4 = (Num.alphaS ^ 2) ^ 2 by ring, Num.alphaS_sq]; norm_num
  have e : Table.Row.K06 = 72 ^ 2 * Num.hbar / (3 ^ 24 * Num.W ^ 4 * Num.mp) / Num.year := by
    rw [Table.Row.K06, ha, Num.eLine_eq]
    field_simp
  refine ⟨e, ?_⟩
  rw [e, Num.hbar_eq_q, Num.W_eq_q, Num.mp_eq_q, Num.year]
  have := Article.rowK06_digits
  rw [Article.rowK06, Article.qExcursion] at this
  convert this using 3 <;> norm_num

/-- **Row L12.** As K06. -/
theorem row_L12 : Table.Row.L12 = Table.Row.K06 ∧
    (1.169710989455e37 : ℝ) < Table.Row.L12 ∧ Table.Row.L12 < 1.169710989465e37 := ⟨rfl, row_K06.2⟩

end Comparison.System
