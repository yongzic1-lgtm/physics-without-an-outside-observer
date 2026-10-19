import Comparison.System.Completion.Numbers

set_option linter.style.longLine false

/-!
# The proof system, the table, part 1: the lepton and quark rows, the proton and the neutron

Rows B01 to B14, J01, J02, L01, L05, L17 of Table X. Each row's value is **defined as
its composition in the law's numbers** (`System/Completion/Numbers.lean`: the rule's values at their divided sets, the
available transitions, the excursion, the clock) and proved equal to its exact closed form; the interval with rational ends that puts it
inside its printed digits comes from 26-digit intervals (`Article/QLeptonsQuarks.lean`) through the equality of
the two forms.

Recognitions (beside the theorems, never in them): B01 the muon/electron mass ratio, B02 tau/muon, B03 Koide's
statistic, B04 strange/down, B05 bottom/strange, B06 and B07 the down and up statistics, B08 the lepton/quark plane
quotient, B09 up/down, B10 the up factor per visit to the symmetric states, B11 charm/strange, B12 and J01 proton/electron, B13 and J02
neutron/proton, B14 neutron/electron, L01 the τ pole mass [MeV], L05 the forbidden charged-lepton threshold [MeV],
L17 the Koide discrimination. The mass operator on the symmetric and the vector states (Prop. 69) and the proton's pole as the sum of its
four terms (Prop. 82 (iv)) are the theory's compositions: the step from the law's zero to these sums is in the work
list.
-/

namespace Comparison.System.Table

open Real Complex Matrix Comparison Comparison.Law Comparison.System.Completion

namespace Row

/-- B01, the mass operator on the symmetric states at the count sign `{a, b}` (Prop. 69). -/
noncomputable def B01 : ℝ := massOp .symmetric sPlane
/-- B02, the vector states at `{a, b}`. -/
noncomputable def B02 : ℝ := massOp .vector sPlane
/-- B03, the Koide statistic of `1`, `B01`, `B01·B02`. -/
noncomputable def B03 : ℝ := (1 + B01 + B01 * B02) / (1 + √B01 + √(B01 * B02)) ^ 2
/-- B04, `p`: the symmetric states at the amplitude sign `{a, b, n}`. -/
noncomputable def B04 : ℝ := massOp .symmetric sPlaneSinglet
/-- `q`, the vector states at `{a, b, n}`. -/
noncomputable def q : ℝ := massOp .vector sPlaneSinglet
/-- B05, `qη`. -/
noncomputable def B05 : ℝ := q * Num.eta

/-- The down sequence `(m_d, m_s, m_b)/m_e = 3^{3/2}(1/η, p/η, pq)` and the up sequence
`(m_u, m_c, m_t) = R_ud(m_d, κ⁵m_s, κ^{15/2}m_b)` (Prop. 69), in units of `m_e`. -/
noncomputable def md : ℝ := 3 ^ (3 / 2 : ℝ) / Num.eta
noncomputable def ms : ℝ := md * B04
noncomputable def mb : ℝ := ms * B05
noncomputable def mu : ℝ := Num.Rud * md
noncomputable def mc : ℝ := Num.Rud * Num.kappa ^ 5 * ms
noncomputable def mt : ℝ := Num.Rud * Num.kappa ^ (15 / 2 : ℝ) * mb

/-- B06, `m_b²m_d/m_s³` on the down sequence. -/
noncomputable def B06 : ℝ := mb ^ 2 * md / ms ^ 3
/-- B07, `m_t²m_u/m_c³` on the up sequence. -/
noncomputable def B07 : ℝ := mt ^ 2 * mu / mc ^ 3
/-- B08, `B01/B04`. -/
noncomputable def B08 : ℝ := B01 / B04
/-- B09, `m_u/m_d` on the sequences. -/
noncomputable def B09 : ℝ := mu / md
/-- B10, `κ = (e@{t,n}/t@{t,n})^{Eℓ/E_P}`. -/
noncomputable def B10 : ℝ := Num.kappa
/-- B11, `m_c/m_s` on the sequences. -/
noncomputable def B11 : ℝ := mc / ms
/-- B12, the proton's pole (Prop. 82). -/
noncomputable def B12 : ℝ := Num.protonPole
/-- B13, `E_U^{Σ_contrasts a^{2Δ_F} + N₂c_L b a⁶}` (Prop. 120). -/
noncomputable def B13 : ℝ := Num.EU ^ Num.neutronExponent
/-- B14, `B12·B13`. -/
noncomputable def B14 : ℝ := B12 * B13
/-- J01, J02: as B12, B13. -/
noncomputable def J01 : ℝ := B12
noncomputable def J02 : ℝ := B13
/-- L01, `m_e·B01·B02` [MeV]. -/
noncomputable def L01 : ℝ := Num.me * B01 * B02
/-- L05, the line block's main term `e@{t}^{−5/2} m_e = 3^{5/2}m_e` [MeV]. -/
noncomputable def L05 : ℝ := eS sLine ^ (-(5 / 2 : ℝ)) * Num.me
/-- L17, as B03. -/
noncomputable def L17 : ℝ := B03

end Row

/-! ## Bridges to the closed forms -/

theorem B01_eq_q : Row.B01 = Article.qRmu := by
  rw [Row.B01, row_mu, Article.clockMQ_plus, Article.qRmu]
  norm_num

theorem B02_eq_q : Row.B02 = Article.qRtau := by
  rw [Row.B02, row_tau, Article.qRtau]
  norm_num

theorem B04_eq_q : Row.B04 = Article.qP := Article.massOp_p

theorem q_eq_q : Row.q = Article.qQ := by
  rw [Row.q, row_q_quark, Article.qQ]
  norm_num

theorem eta_pos : 0 < Num.eta := by rw [Num.eta_eq]; norm_num

theorem kappa_pos : 0 < Num.kappa := by rw [Num.kappa_eq]; positivity

theorem B04_pos : 0 < Row.B04 := by
  rw [B04_eq_q]; exact lt_of_lt_of_le (by norm_num) Article.qP_bnd.1

theorem q_pos : 0 < Row.q := by
  rw [q_eq_q]; exact lt_of_lt_of_le (by norm_num) Article.qQ_bnd.1

theorem md_pos : 0 < Row.md := by
  rw [Row.md]; have := eta_pos; positivity

theorem ms_pos : 0 < Row.ms := mul_pos md_pos B04_pos

theorem B12_eq_q : Row.B12 = Article.qRp := Num.protonPole_eq_q

theorem B13_closed : Row.B13 = (5 / 2 : ℝ) ^ (5 * (5 / 38 : ℝ) ^ 4 + 4 * (5 / 38) ^ 10 +
    10 * (15 / 74) * (7 / 16) * (5 / 38) ^ 6) := by
  rw [Row.B13, Num.EU_eq, Num.neutronExponent_closed]

theorem B13_eq_q : Row.B13 = Article.qRn := by
  rw [B13_closed, Article.qRn, Article.qLog52, Real.rpow_def_of_pos (by norm_num)]
  congr 1
  norm_num

/-- **The up statistic equals the down statistic**: the up sequence multiplies the down masses by `R_ud`, `R_udκ⁵`,
`R_udκ^{15/2}`, and `(κ^{15/2})²/(κ⁵)³ = 1`, `R_ud²R_ud/R_ud³ = 1`. -/
theorem up_statistic_eq_down : Row.B07 = Row.B06 := by
  have hR : Num.Rud ≠ 0 := by rw [Num.Rud_eq]; norm_num
  have hk : 0 < Num.kappa := kappa_pos
  have hms : 0 < Row.ms := ms_pos
  have h15 : (Num.kappa ^ (15 / 2 : ℝ)) ^ 2 = Num.kappa ^ 15 := by
    rw [← Real.rpow_natCast (Num.kappa ^ (15 / 2 : ℝ)) 2, ← Real.rpow_mul hk.le,
      ← Real.rpow_natCast Num.kappa 15]
    norm_num
  have hk5 : Num.kappa ^ 5 ≠ 0 := pow_ne_zero _ hk.ne'
  simp only [Row.B07, Row.B06, Row.mt, Row.mu, Row.mc]
  field_simp
  rw [h15]
  ring

end Comparison.System.Table

namespace Comparison.System

open Real Complex Matrix Comparison Comparison.Law Comparison.System.Completion Comparison.System.Table

/-- **Row B01.** `m_μ/m_e = 3⁵e^{−9/56}M_Q(ν)^{1/6} = 206.768283945`. Recognition: the muon/electron mass ratio. -/
theorem row_B01 : Table.Row.B01 = 3 ^ (5 : ℝ) * Real.exp (-(9 / 56)) * Num.MQ (9 / 4000) ^ (1 / 6 : ℝ) ∧
    (206.7682839445 : ℝ) < Table.Row.B01 ∧ Table.Row.B01 < 206.7682839455 := by
  refine ⟨row_mu, ?_⟩
  rw [B01_eq_q]; exact Article.rowB01_digits

/-- **Row B02.** `m_τ/m_μ = 3^{5/2}e^{1/14 + 2ν} = 16.8181606411`. Recognition: tau/muon. -/
theorem row_B02 : Table.Row.B02 = 3 ^ (5 / 2 : ℝ) * Real.exp (1 / 14 + 2 * (9 / 4000)) ∧
    (16.81816064105 : ℝ) < Table.Row.B02 ∧ Table.Row.B02 < 16.81816064115 := by
  refine ⟨row_tau, ?_⟩
  rw [B02_eq_q]; exact Article.rowB02_digits

/-- **Row B03.** `(1 + r_μ + r_μr_τ)/(1 + r_μ^{1/2} + (r_μr_τ)^{1/2})² = 0.666667259761`. Recognition: Koide's
statistic. -/
theorem row_B03 : Table.Row.B03 = (1 + Table.Row.B01 + Table.Row.B01 * Table.Row.B02) /
      (1 + √Table.Row.B01 + √(Table.Row.B01 * Table.Row.B02)) ^ 2 ∧
    (0.6666672597605 : ℝ) < Table.Row.B03 ∧ Table.Row.B03 < 0.6666672597615 := by
  refine ⟨rfl, ?_⟩
  rw [Table.Row.B03, B01_eq_q, B02_eq_q]; exact Article.rowB03_digits

/-- **Row B04.** `p = 3⁵e^{−5/2}M_Q(−ν)^{1/6} = 19.9616523938`. Recognition: strange/down. -/
theorem row_B04 : Table.Row.B04 = 3 ^ (5 : ℝ) * Real.exp (-(5 / 2)) * Num.MQ (-(9 / 4000)) ^ (1 / 6 : ℝ) ∧
    (19.96165239375 : ℝ) < Table.Row.B04 ∧ Table.Row.B04 < 19.96165239385 := by
  refine ⟨row_p_quark, ?_⟩
  rw [B04_eq_q]; exact Article.rowB04_digits

/-- **Row B05.** `qη = 3^{5/2}e^{5/4 − 5ν/2}·295/296 = 53.9210868808`. Recognition: bottom/strange. -/
theorem row_B05 : Table.Row.B05 = 3 ^ (5 / 2 : ℝ) * Real.exp (5 / 4 - 5 * (9 / 4000) / 2) * (295 / 296) ∧
    (53.92108688075 : ℝ) < Table.Row.B05 ∧ Table.Row.B05 < 53.92108688085 := by
  refine ⟨by rw [Table.Row.B05, Table.Row.q, row_q_quark, Num.eta_eq], ?_⟩
  rw [Table.Row.B05, q_eq_q, Num.eta_eq]; exact Article.rowB05_digits

/-- **Row B06.** `m_b²m_d/m_s³ = (qη)²/p = 145.653453585`. Recognition: the down statistic. -/
theorem row_B06 : Table.Row.B06 = Table.Row.B05 ^ 2 / Table.Row.B04 ∧
    (145.6534535845 : ℝ) < Table.Row.B06 ∧ Table.Row.B06 < 145.6534535855 := by
  have e : Table.Row.B06 = Table.Row.B05 ^ 2 / Table.Row.B04 := by
    rw [Table.Row.B06, Table.Row.mb, Table.Row.ms]
    have := md_pos.ne'; have := B04_pos.ne'
    field_simp
  refine ⟨e, ?_⟩
  rw [e, Table.Row.B05, q_eq_q, Num.eta_eq, B04_eq_q]; exact Article.rowB06_digits

/-- **Row B07.** The up sequence gives `m_t²m_u/m_c³ = m_b²m_d/m_s³ = 145.653453585`. Recognition: the up statistic. -/
theorem row_B07 : Table.Row.B07 = Table.Row.B06 ∧
    (145.6534535845 : ℝ) < Table.Row.B07 ∧ Table.Row.B07 < 145.6534535855 := by
  refine ⟨up_statistic_eq_down, ?_⟩
  rw [up_statistic_eq_down]; exact row_B06.2

/-- **Row B08.** `(m_μ/m_e)/p = 10.3582749497`. Recognition: the lepton/quark plane quotient. -/
theorem row_B08 : Table.Row.B08 = Table.Row.B01 / Table.Row.B04 ∧
    (10.35827494965 : ℝ) < Table.Row.B08 ∧ Table.Row.B08 < 10.35827494975 := by
  refine ⟨rfl, ?_⟩
  rw [Table.Row.B08, B01_eq_q, B04_eq_q]; exact Article.rowB08_digits

/-- **Row B09.** `m_u/m_d = R_ud = 34/74 = 17/37`. Recognition: up/down. -/
theorem row_B09 : Table.Row.B09 = 17 / 37 := by
  rw [Table.Row.B09, Table.Row.mu]
  field_simp [md_pos.ne']
  rw [Num.Rud_eq]
  norm_num

/-- **Row B10.** `κ = (3/2)^{8/5} = 1.91313675094`. Recognition: the up factor per visit to the symmetric states. -/
theorem row_B10 : Table.Row.B10 = (3 / 2) ^ (8 / 5 : ℝ) ∧
    (1.913136750935 : ℝ) < Table.Row.B10 ∧ Table.Row.B10 < 1.913136750945 := by
  refine ⟨Num.kappa_eq, ?_⟩
  rw [Table.Row.B10, Num.kappa_eq_q]; exact Article.rowB10_digits

/-- **Row B11.** `m_c/m_s = R_udκ⁵ = 11.7754434122`. Recognition: charm/strange. -/
theorem row_B11 : Table.Row.B11 = 17 / 37 * ((3 / 2) ^ (8 / 5 : ℝ)) ^ 5 ∧
    (11.77544341215 : ℝ) < Table.Row.B11 ∧ Table.Row.B11 < 11.77544341225 := by
  have e : Table.Row.B11 = Num.Rud * Num.kappa ^ 5 := by
    rw [Table.Row.B11, Table.Row.mc]; field_simp [ms_pos.ne']
  refine ⟨by rw [e, Num.Rud_eq, Num.kappa_eq], ?_⟩
  rw [e, Num.Rud_eq, Num.kappa_eq_q]; exact Article.rowB11_digits

/-- **Row B12.** `6M + C_h + (1/6)log(5/2) − a⁵ − ba⁶ = 1836.15267341`. Recognition: proton/electron. -/
theorem row_B12 : Table.Row.B12 = 6 * 296 + 60 + (1 / 6) * Real.log (5 / 2) - (5 / 38) ^ 5 - (7 / 16) * (5 / 38) ^ 6 ∧
    (1836.152673405 : ℝ) < Table.Row.B12 ∧ Table.Row.B12 < 1836.152673415 := by
  refine ⟨Num.protonPole_closed, ?_⟩
  rw [B12_eq_q]; exact Article.rowB12_digits

/-- **Row B13.** `(5/2)^{5a⁴ + 4a¹⁰ + 10c_Lba⁶} = 1.00137841956`. Recognition: neutron/proton. -/
theorem row_B13 : Table.Row.B13 = (5 / 2 : ℝ) ^ (5 * (5 / 38 : ℝ) ^ 4 + 4 * (5 / 38) ^ 10 +
      10 * (15 / 74) * (7 / 16) * (5 / 38) ^ 6) ∧
    (1.001378419555 : ℝ) < Table.Row.B13 ∧ Table.Row.B13 < 1.001378419565 := by
  refine ⟨B13_closed, ?_⟩
  rw [B13_eq_q]; exact Article.rowB13_digits

/-- **Row B14.** `B12·B13 = 1838.68366218`. Recognition: neutron/electron. -/
theorem row_B14 : Table.Row.B14 = Table.Row.B12 * Table.Row.B13 ∧
    (1838.683662175 : ℝ) < Table.Row.B14 ∧ Table.Row.B14 < 1838.683662185 := by
  refine ⟨rfl, ?_⟩
  rw [Table.Row.B14, B12_eq_q, B13_eq_q]; exact Article.rowB14_digits

/-- **Row J01.** As B12. -/
theorem row_J01 : Table.Row.J01 = Table.Row.B12 ∧
    (1836.152673405 : ℝ) < Table.Row.J01 ∧ Table.Row.J01 < 1836.152673415 := ⟨rfl, row_B12.2⟩

/-- **Row J02.** As B13. -/
theorem row_J02 : Table.Row.J02 = Table.Row.B13 ∧
    (1.001378419555 : ℝ) < Table.Row.J02 ∧ Table.Row.J02 < 1.001378419565 := ⟨rfl, row_B13.2⟩

/-- **Row L01.** `m_e r_μ r_τ = 1776.97954286 MeV`. Recognition: the τ pole mass; `m_e` is the unit (outside). -/
theorem row_L01 : Table.Row.L01 = Num.me * Table.Row.B01 * Table.Row.B02 ∧
    (1776.979542855 : ℝ) < Table.Row.L01 ∧ Table.Row.L01 < 1776.979542865 := by
  refine ⟨rfl, ?_⟩
  rw [Table.Row.L01, B01_eq_q, B02_eq_q, Num.me_eq_q]
  exact Article.rowL01_digits

/-- **Row L05.** `3^{5/2}m_e = 7.96568530689 MeV`, the line block's main term. Recognition: the forbidden
charged-lepton threshold. -/
theorem row_L05 : Table.Row.L05 = 3 ^ (5 / 2 : ℝ) * Num.me ∧
    (7.965685306885 : ℝ) < Table.Row.L05 ∧ Table.Row.L05 < 7.965685306895 := by
  have e : Table.Row.L05 = 3 ^ (5 / 2 : ℝ) * Num.me := by
    rw [Table.Row.L05, (table_line sLine (Or.inl rfl)).2.2.2.2.2.1]
    rw [show (1 / 3 : ℝ) ^ (-(5 / 2 : ℝ)) = 3 ^ (5 / 2 : ℝ) by
      rw [one_div, Real.inv_rpow (by norm_num), ← Real.rpow_neg (by norm_num)]; norm_num]
  refine ⟨e, ?_⟩
  rw [e, Num.me_eq_q]
  exact Article.rowL05_digits

/-- **Row L17.** As B03. -/
theorem row_L17 : Table.Row.L17 = Table.Row.B03 ∧
    (0.6666672597605 : ℝ) < Table.Row.L17 ∧ Table.Row.L17 < 0.6666672597615 := ⟨rfl, row_B03.2⟩

end Comparison.System
