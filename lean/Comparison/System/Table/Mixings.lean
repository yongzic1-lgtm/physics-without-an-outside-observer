import Comparison.System.Completion.Numbers

set_option linter.style.longLine false

/-!
# The proof system, the table, part 3: the mixings

Rows C01 to C14, K05, T06 of Table X. The quark frame `V = R₂₃(s₂₃)R₁₃(s₁₃, δ_q)R₁₂(s₁₂)` and
the lepton frame `U = R₁₂(√(2b)s₁₂, π/2 − δ_q)†R₂₃(2^{−1/2})R₁₂(b^{1/2})` (Prop. 122, Eqs. (42), (44)) are built from
the excursion's moments (`s₁₂ = (Var P − Cov²/Var Q)/(Eℓk₀)`), the comparison (`s₂₃ = 4/Tr L²`), the transmission
(`s₁₃ = s₁₂ t s₂₃`), the rule's complex weight (`δ_q = arg(b + w_C)`) and `b = b(w@{})`; `Article.ckmV` and
`Article.pmnsU` are these frames (`Article/Mixing.lean`), and the rows' intervals are (`Article/MixRows.lean`).

Recognitions: C01 to C03 the quark mixing sines, C04 the quark phase, C05 the quark quartet `J_q` [10⁻⁵], C06 to C08
the unitarity triangle's angles [deg], C09 the two-row W current sum, C10 the solar lepton angle, C11 and C12 the
reactor angle, C13 the atmospheric angle, C14 the lepton phase [deg], K05 the diagonal quark current, T06 the lepton
quartet. The two frames' forms (which rotations, in which order) are the theory's (Prop. 122, C).
-/

namespace Comparison.System.Table

open Real Complex Matrix Comparison Comparison.Law Comparison.System.Completion

namespace Row

/-- C01, `s₁₂ = (Var P − Cov²/Var Q)/(Eℓk₀)`. -/
noncomputable def C01 : ℝ := (Num.VarP - Num.Cov ^ 2 / Num.VarQ) / (Num.El * Num.k 0)
/-- C02, `s₂₃ = 4/Tr L²`. -/
noncomputable def C02 : ℝ := 4 / ((L * L).trace).re
/-- C03, `s₁₃ = s₁₂ t s₂₃`. -/
noncomputable def C03 : ℝ := C01 * Num.t * C02
/-- C04, `δ_q = arg(b + w_C)`. -/
noncomputable def C04 : ℝ := Complex.arg (bS sHere + wS sC)
/-- The quark frame `V = R₂₃(s₂₃)R₁₃(s₁₃, δ_q)R₁₂(s₁₂)`. -/
noncomputable def V : Matrix (Fin 3) (Fin 3) ℂ := Article.R23 C02 0 * Article.R13 C03 C04 * Article.R12 C01 0
/-- The lepton frame `U = R₁₂(√(2b)s₁₂, π/2 − δ_q)†R₂₃(2^{−1/2})R₁₂(b^{1/2})`. -/
noncomputable def U : Matrix (Fin 3) (Fin 3) ℂ :=
  (Article.R12 (√(2 * Num.b) * C01) (π / 2 - C04)).conjTranspose * Article.R23 (1 / √2) 0 *
    Article.R12 √Num.b 0
/-- C05, `10⁵ Im(V_usV_cbV_ub*V_cs*)`. -/
noncomputable def C05 : ℝ := 10 ^ 5 * (V 0 1 * V 1 2 * (starRingEnd ℂ) (V 0 2) * (starRingEnd ℂ) (V 1 1)).im
/-- C06, `arg(−V_tdV_tb*/V_udV_ub*)` [deg]. -/
noncomputable def C06 : ℝ :=
  180 / π * Complex.arg (-(V 2 0 * (starRingEnd ℂ) (V 2 2)) / (V 0 0 * (starRingEnd ℂ) (V 0 2)))
/-- C07, `arg(−V_cdV_cb*/V_tdV_tb*)` [deg]. -/
noncomputable def C07 : ℝ :=
  180 / π * Complex.arg (-(V 1 0 * (starRingEnd ℂ) (V 1 2)) / (V 2 0 * (starRingEnd ℂ) (V 2 2)))
/-- C08, `arg(−V_udV_ub*/V_cdV_cb*)` [deg]. -/
noncomputable def C08 : ℝ :=
  180 / π * Complex.arg (-(V 0 0 * (starRingEnd ℂ) (V 0 2)) / (V 1 0 * (starRingEnd ℂ) (V 1 2)))
/-- C09, `Σ_{i=u,c}Σ_j|V_ij|²`. -/
noncomputable def C09 : ℝ :=
  ‖V 0 0‖ ^ 2 + ‖V 0 1‖ ^ 2 + ‖V 0 2‖ ^ 2 + (‖V 1 0‖ ^ 2 + ‖V 1 1‖ ^ 2 + ‖V 1 2‖ ^ 2)
/-- C11, `|U_e3|²`. -/
noncomputable def C11 : ℝ := ‖U 0 2‖ ^ 2
/-- C10, `|U_e2|²/(1 − |U_e3|²)`. -/
noncomputable def C10 : ℝ := ‖U 0 1‖ ^ 2 / (1 - ‖U 0 2‖ ^ 2)
/-- C12, `4s₁₃²(1 − s₁₃²)`. -/
noncomputable def C12 : ℝ := 4 * C11 * (1 - C11)
/-- C13, `|U_μ3|²/(1 − |U_e3|²)`. -/
noncomputable def C13 : ℝ := ‖U 1 2‖ ^ 2 / (1 - ‖U 0 2‖ ^ 2)
/-- T06, `Im(U_e1U_μ2U_e2*U_μ1*)`. -/
noncomputable def T06 : ℝ := (U 0 0 * U 1 1 * (starRingEnd ℂ) (U 0 1) * (starRingEnd ℂ) (U 1 0)).im
/-- The scale `s₁₂c₁₂s₂₃c₂₃s₁₃` of the standard parametrization, and `cos δ_l`, `sin δ_l c₁₃²` from the entries. -/
noncomputable def scaleL : ℝ := √(C10 * (1 - C10) * C13 * (1 - C13) * C11)
noncomputable def xL : ℝ := (‖U 1 0‖ ^ 2 - C10 * (1 - C13) - (1 - C10) * C13 * C11) / (2 * scaleL)
noncomputable def yL : ℝ := T06 / (scaleL * (1 - C11))
/-- C14, the Dirac phase of `U` in the standard parametrization [deg]. -/
noncomputable def C14 : ℝ := 180 / π * Complex.arg ((xL : ℂ) + (yL : ℂ) * I) + 360
/-- K05, `Σ_i|V_ii|²`. -/
noncomputable def K05 : ℝ := ‖V 0 0‖ ^ 2 + ‖V 1 1‖ ^ 2 + ‖V 2 2‖ ^ 2

end Row

theorem C01_eq : Row.C01 = Article.rowC01 := by
  norm_num [Row.C01, Num.VarP, Num.VarQ, Num.Cov, Num.El_eq, Num.k_zero, Article.rowC01, piece_EU_here]

theorem C01_val : Row.C01 = 9 / 40 := by
  rw [C01_eq, Article.rowC01_digits]; norm_num

theorem C02_eq : Row.C02 = Article.rowC02 := rfl

theorem C03_eq : Row.C03 = Article.rowC03 := by
  rw [Row.C03, Article.rowC03, C01_eq, C02_eq, Num.t]

theorem C04_eq : Row.C04 = Article.deltaQ := rfl

theorem V_eq : Row.V = Article.ckmV := by
  rw [Row.V, Article.ckmV, C01_eq, C02_eq, C03_eq, C04_eq]

theorem U_eq : Row.U = Article.pmnsU := by
  rw [Row.U, Article.pmnsU, Article.sP, C01_eq, C04_eq, Num.b]

end Comparison.System.Table

namespace Comparison.System

open Real Complex Matrix Comparison Comparison.Law Comparison.System.Completion Comparison.System.Table

/-- **Row C01.** `s₁₂ = (Var P − Cov²/Var Q)/(Eℓk₀) = 9/40`. Recognition: the first quark mixing. -/
theorem row_C01 : Table.Row.C01 = 9 / 40 := C01_val

/-- **Row C02.** `s₂₃ = 4/Tr L² = 1/24`. Recognition: the second quark mixing. -/
theorem row_C02 : Table.Row.C02 = 1 / 24 := Article.rowC02_eq

/-- **Row C03.** `s₁₃ = s₁₂ t s₂₃ = 3/800`. Recognition: the far quark mixing. -/
theorem row_C03 : Table.Row.C03 = 3 / 800 := by
  rw [C03_eq, Article.rowC03_digits]; norm_num

/-- **Row C04.** `δ_q = arg(b + w_C) = arg(7 + 16i) = 1.1583858852`. Recognition: the quark phase [rad]. -/
theorem row_C04 : Table.Row.C04 = Complex.arg (7 + 16 * I) ∧
    (1.15838588515 : ℝ) < Table.Row.C04 ∧ Table.Row.C04 < 1.15838588525 := by
  refine ⟨Article.deltaQ_eq_arg, ?_⟩
  rw [C04_eq]; exact Article.rowC04_digits

/-- **Row C05.** `10⁵ Im(V_usV_cbV_ub*V_cs*) = 3.13550917579`. Recognition: the quark quartet `J_q` [10⁻⁵]. -/
theorem row_C05 : (3.135509175785 : ℝ) < Table.Row.C05 ∧ Table.Row.C05 < 3.135509175795 := by
  rw [Table.Row.C05, V_eq]; exact Article.rowC05_digits

/-- **Row C06.** `arg(−V_tdV_tb*/V_udV_ub*) = 90.7137730643°`. Recognition: the triangle angle `α`. -/
theorem row_C06 : (90.71377306425 : ℝ) < Table.Row.C06 ∧ Table.Row.C06 < 90.71377306435 := by
  rw [Table.Row.C06, V_eq]; exact Article.rowC06_digits

/-- **Row C07.** `arg(−V_cdV_cb*/V_tdV_tb*) = 22.9511439354°`. Recognition: the triangle angle `β`. -/
theorem row_C07 : (22.95114393535 : ℝ) < Table.Row.C07 ∧ Table.Row.C07 < 22.95114393545 := by
  rw [Table.Row.C07, V_eq]; exact Article.rowC07_digits

/-- **Row C08.** `arg(−V_udV_ub*/V_cdV_cb*) = 66.3350830003°`. Recognition: the triangle angle `γ`. -/
theorem row_C08 : (66.33508300025 : ℝ) < Table.Row.C08 ∧ Table.Row.C08 < 66.33508300035 := by
  rw [Table.Row.C08, V_eq]; exact Article.rowC08_digits

/-- **Row C09.** Two rows of a unitary frame: `Σ_{i=u,c}Σ_j|V_ij|² = 2`. Recognition: the two-row W current sum. -/
theorem row_C09 : Table.Row.C09 = 2 := by
  rw [Table.Row.C09, V_eq]; exact Article.rowC09_digits

/-- **Row C10.** `|U_e2|²/(1 − |U_e3|²) = 0.305089610923`. Recognition: the solar lepton angle `s₁₂²`. -/
theorem row_C10 : (0.3050896109225 : ℝ) < Table.Row.C10 ∧ Table.Row.C10 < 0.3050896109235 := by
  rw [Table.Row.C10, U_eq]; exact Article.rowC10_digits

/-- **Row C11.** `|U_e3|² = b s₁₂² = 567/25600 = 0.0221484375`. Recognition: the reactor angle `s₁₃²`. -/
theorem row_C11 : Table.Row.C11 = 567 / 25600 := by
  rw [Table.Row.C11, U_eq]; exact Article.rowC11_exact

/-- **Row C12.** `4s₁₃²(1 − s₁₃²) = 0.0866315368652`. Recognition: the reactor angle `sin²2θ₁₃`. -/
theorem row_C12 : Table.Row.C12 = 4 * (567 / 25600) * (1 - 567 / 25600) ∧
    (0.08663153686515 : ℝ) < Table.Row.C12 ∧ Table.Row.C12 < 0.08663153686525 := by
  refine ⟨by rw [Table.Row.C12, row_C11], ?_⟩
  rw [Table.Row.C12, row_C11]; norm_num

/-- **Row C13.** `|U_μ3|²/(1 − |U_e3|²) = 0.488674949067`. Recognition: the atmospheric angle `s₂₃²`. -/
theorem row_C13 : (0.4886749490665 : ℝ) < Table.Row.C13 ∧ Table.Row.C13 < 0.4886749490675 := by
  rw [Table.Row.C13, U_eq]; exact Article.rowC13_digits

/-- **Row T06.** `Im(U_e1U_μ2U_e2*U_μ1*) = −0.0144644347463`. Recognition: the lepton quartet `J_l`. -/
theorem row_T06 : (-0.01446443474635 : ℝ) < Table.Row.T06 ∧ Table.Row.T06 < -0.01446443474625 := by
  rw [Table.Row.T06, U_eq]; exact Article.rowT06_digits

/-- **Row C14.** The Dirac phase of `U`, `205.584225835°`. Recognition: the lepton phase `δ_l`. -/
theorem row_C14 : (205.5842258345 : ℝ) < Table.Row.C14 ∧ Table.Row.C14 < 205.5842258355 := by
  have h10 : Table.Row.C10 = Article.rowC10 := by rw [Table.Row.C10, U_eq, Article.rowC10]
  have h11 : Table.Row.C11 = Article.rowC11 := by rw [Table.Row.C11, U_eq, Article.rowC11]
  have h13 : Table.Row.C13 = Article.rowC13 := by rw [Table.Row.C13, U_eq, Article.rowC13]
  have h06 : Table.Row.T06 = Article.rowT06 := by rw [Table.Row.T06, U_eq, Article.rowT06]
  have e : Table.Row.C14 = Article.rowC14 := by
    rw [Table.Row.C14, Table.Row.xL, Table.Row.yL, Table.Row.scaleL, h10, h11, h13, h06, U_eq,
      Article.rowC14, Article.xLside, Article.yLside, Article.scaleL]
  rw [e]; exact Article.rowC14_digits

/-- **Row K05.** `Σ_i|V_ii|² = 2.89531084488`. Recognition: the diagonal quark current. -/
theorem row_K05 : (2.895310844875 : ℝ) < Table.Row.K05 ∧ Table.Row.K05 < 2.895310844885 := by
  rw [Table.Row.K05, V_eq]; exact Article.rowK05_digits

end Comparison.System
