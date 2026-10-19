import Comparison.System.Completion.Numbers

set_option linter.style.longLine false

/-!
# The proof system, the table, part 5: the neutral poles, the families, the strong phase, the frame

Rows E01 to E07, K02, K03, L03, L04, L14, K01, L16, H01, H02, H03, L18 of Table X.

The light neutral poles are the light zeros of `det [[x, δ_i], [δ_i, X_R + x]]`, `δ = σ(v/m_p)(0, ρ_ν^{1/2}, 1)/√2`,
`X_R = e_line⁹/W`, `ρ_ν = tan²(π/8)` (Prop. 123, Eq. (44)'s neighbours): the root `x = 2δ²/(X_R + (X_R² + 4δ²)^{1/2})`
is the one nonnegative root (`Article.seesaw_root`). The families are the three pairings of the four lines beside
the last-step direction; the colour components are `k_C² − 1`; the strong phase is the argument of every closed weight of the law
below the critical step, zero for every Hermitian-involution connection (Prop. 115, W's).

Recognitions: E01 to E03 the neutrino splittings [10⁻⁵, 10⁻³ eV²], E04 `m₂/m₃`, E05 the splitting ratio, E06 the
heaviest light neutrino [meV], E07 the light neutrino channels, K02 and K03 the neutrino mass sum [eV], L03 the
light-limit splitting ratio, L04 the charged families, L14 the colour component count, K01 and L16 the strong phase
`θ̄`, H01 the light bending `1 + γ`, H02 the geodetic drift over its Einstein value, H03 the success of two orders
added with their record, L18 the second-order light-bending coefficient. H01, H02 and L18 are the classical
linearized frame with `γ = 1` (and `β = ε = 1` at second order) read off the trace-reversed static field; the frame
term's field equation from the law is W's Eq. (30), proved on the cells (`eq_30`), and its continuum limit completes
these rows. The three pairings' response on the ten symmetric states, `10U_hᵀΓ_P⁻¹U_h = 40I₃ − 4J₃`, is
`row_L04_pairings` (`Completion/Families.lean`).
-/

namespace Comparison.System.Table

open Real Complex Matrix Comparison Comparison.Law Comparison.System.Completion

namespace Row

/-- E01, `m₂² − m₁²` with `m₁ = 0` [10⁻⁵ eV²]. -/
noncomputable def E01 : ℝ := Num.mnu2 * Num.mnu2 * 100000
/-- E02, `m₃² − m₁²` [10⁻³ eV²]. -/
noncomputable def E02 : ℝ := Num.mnu3 * Num.mnu3 * 1000
/-- E03, `m₃² − m₂²` [10⁻³ eV²]. -/
noncomputable def E03 : ℝ := (Num.mnu3 * Num.mnu3 - Num.mnu2 * Num.mnu2) * 1000
/-- E04, `m₂/m₃`. -/
noncomputable def E04 : ℝ := Num.mnu2 / Num.mnu3
/-- E05, `(m₃/m₂)²`. -/
noncomputable def E05 : ℝ := (Num.mnu3 / Num.mnu2) ^ 2
/-- E06, `m₃` [meV]. -/
noncomputable def E06 : ℝ := Num.mnu3 * 1000
/-- K02, K03, `m₁ + m₂ + m₃` with `m₁ = Num.seesaw 0 = 0` [eV]. -/
noncomputable def K02 : ℝ := Num.seesaw 0 * Num.mp * 1000000 + Num.mnu2 + Num.mnu3
noncomputable def K03 : ℝ := K02
/-- L03, `ρ_ν⁻²`. -/
noncomputable def L03 : ℝ := 1 / Num.rhoNu ^ 2
/-- E07, L04, the pairings of the four lines beside the last-step direction. -/
noncomputable def E07 : ℝ := ((WholePicture.pairingsBeside 0).card : ℝ)
noncomputable def L04 : ℝ := ((WholePicture.pairingsBeside 0).card : ℝ)
/-- L14, `k_C² − 1`. -/
noncomputable def L14 : ℝ := (Num.kC : ℝ) ^ 2 - 1

end Row

theorem seesaw_zero : Num.seesaw 0 = 0 := by simp [Num.seesaw]

end Comparison.System.Table

namespace Comparison.System

open Real Complex Matrix Comparison Comparison.Law Comparison.System.Completion Comparison.System.Table

/-- **Row E01.** `m₂² = 7.41781185257·10⁻⁵ eV²`. Recognition: the solar splitting. -/
theorem row_E01 : (7.417811852565 : ℝ) < Table.Row.E01 ∧ Table.Row.E01 < 7.417811852575 := by
  rw [Table.Row.E01, Num.mnu2_eq_q]; exact Article.rowE01_digits

/-- **Row E02.** `m₃² = 2.51987242994·10⁻³ eV²`. Recognition: the splitting `Δm²₃₁`. -/
theorem row_E02 : (2.519872429935 : ℝ) < Table.Row.E02 ∧ Table.Row.E02 < 2.519872429945 := by
  rw [Table.Row.E02, Num.mnu3_eq_q]; exact Article.rowE02_digits

/-- **Row E03.** `m₃² − m₂² = 2.44569431142·10⁻³ eV²`. Recognition: the splitting `Δm²₃₂`. -/
theorem row_E03 : (2.445694311415 : ℝ) < Table.Row.E03 ∧ Table.Row.E03 < 2.445694311425 := by
  rw [Table.Row.E03, Num.mnu2_eq_q, Num.mnu3_eq_q]; exact Article.rowE03_digits

/-- **Row E04.** `m₂/m₃ = 0.171572875254` (`= ρ_ν` to `2·10⁻²⁶`). Recognition: the neutrino mass ratio. -/
theorem row_E04 : (0.1715728752535 : ℝ) < Table.Row.E04 ∧ Table.Row.E04 < 0.1715728752545 := by
  rw [Table.Row.E04, Num.mnu2_eq_q, Num.mnu3_eq_q]; exact Article.rowE04_digits

/-- **Row E05.** `(m₃/m₂)² = 33.9705627485`. Recognition: the splitting ratio. -/
theorem row_E05 : (33.97056274845 : ℝ) < Table.Row.E05 ∧ Table.Row.E05 < 33.97056274855 := by
  rw [Table.Row.E05, Num.mnu2_eq_q, Num.mnu3_eq_q]; exact Article.rowE05_digits

/-- **Row E06.** `m₃ = 50.1983309478 meV`. Recognition: the heaviest light neutrino. -/
theorem row_E06 : (50.19833094775 : ℝ) < Table.Row.E06 ∧ Table.Row.E06 < 50.19833094785 := by
  rw [Table.Row.E06, Num.mnu3_eq_q]; exact Article.rowE06_digits

/-- **Row E07.** The three pairings of the four lines beside the last-step direction: `3`. Recognition: the light neutrino
channels. -/
theorem row_E07 : Table.Row.E07 = 3 := Article.rowE07_digits

/-- **Row K02.** `m₁ + m₂ + m₃ = 0.0588110029214 eV`, `m₁ = 0`. Recognition: the neutrino mass sum. -/
theorem row_K02 : (0.05881100292135 : ℝ) < Table.Row.K02 ∧ Table.Row.K02 < 0.05881100292145 := by
  rw [Table.Row.K02, seesaw_zero, zero_mul, zero_mul, zero_add, Num.mnu2_eq_q, Num.mnu3_eq_q]
  exact Article.rowK02_digits

/-- **Row K03.** As K02. -/
theorem row_K03 : (0.05881100292135 : ℝ) < Table.Row.K03 ∧ Table.Row.K03 < 0.05881100292145 := row_K02

/-- **Row L03.** `ρ_ν⁻² = (3 + 2√2)² = 33.9705627485`. Recognition: the light-limit splitting ratio. -/
theorem row_L03 : Table.Row.L03 = 17 + 12 * √2 ∧
    (33.97056274845 : ℝ) < Table.Row.L03 ∧ Table.Row.L03 < 33.97056274855 := by
  refine ⟨?_, ?_⟩
  · rw [Table.Row.L03, Num.rhoNu_eq_q, one_div]; exact (Article.rho_inv_sq).2.2
  · rw [Table.Row.L03, Num.rhoNu_eq_q]; exact Article.rowL03_digits

/-- **Row L04.** The four lines beside the last-step direction pair in exactly three ways: `3`, at every last-step direction. Recognition: the
number of charged families. -/
theorem row_L04 : Table.Row.L04 = 3 ∧ ∀ h : Fin 5, (WholePicture.pairingsBeside h).card = 3 :=
  Article.rowL04_digits

/-- **Row L14.** `k_C² − 1 = 8` (the eight traceless rotations of the three lines, `Formulas.finrank_su3`).
Recognition: the colour component count. -/
theorem row_L14 : Table.Row.L14 = 8 := by
  rw [Table.Row.L14, Num.kC_eq]; norm_num

/-- **Row K01.** For every connection by Hermitian involutions on the steps and every `0 ≤ u < 1/4`, the closed
weight `det(1 − uB[Γ])` has argument `0`. Recognition: the strong phase `θ̄ = 0`. -/
theorem row_K01 {ι : Type*} [Fintype ι] [DecidableEq ι] (Γ : Fin 5 → Matrix ι ι ℂ)
    (hH : ∀ t, (Γ t).conjTranspose = Γ t) (hG : ∀ t, Γ t * Γ t = 1) (u : ℝ) (hu0 : 0 ≤ u)
    (hu : u < 1 / 4) : Complex.arg (1 - (u : ℂ) • stepOp Γ).det = 0 :=
  (Article.rowK01_digits Γ hH hG u hu0 hu).1

/-- **Row L16.** As K01. -/
theorem row_L16 {ι : Type*} [Fintype ι] [DecidableEq ι] (Γ : Fin 5 → Matrix ι ι ℂ)
    (hH : ∀ t, (Γ t).conjTranspose = Γ t) (hG : ∀ t, Γ t * Γ t = 1) (u : ℝ) (hu0 : 0 ≤ u)
    (hu : u < 1 / 4) : Complex.arg (1 - (u : ℂ) • stepOp Γ).det = 0 := row_K01 Γ hH hG u hu0 hu

/-- **Row H01.** The linearized frame's static field `h̄ = diag(4U, 0, 0, 0)` gives `γ = 1`, `1 + γ = 2`.
Recognition: the light bending. (A classical map; the frame term's field equation from the law, W's Eq. (30) in the
continuum, completes it.) -/
theorem row_H01 : Article.rowH01 = 2 := Article.rowH01_digits

/-- **Row H02.** `(1/2 + γ)/(3/2) = 1`. Recognition: the geodetic drift over its Einstein value (classical map). -/
theorem row_H02 : Article.rowH02 = 1 := Article.rowH02_digits

/-- **Row L18.** `π(8 + 8γ − 4β + 3ε)/4 = 15π/4` at `γ = β = ε = 1` (`β`, `ε` the frame's second order, set to
one). Recognition: the second-order light-bending coefficient (classical map). -/
theorem row_L18 : Article.rowL18c = 15 * π / 4 := Article.rowL18c_eq

/-- **Row H03.** Two orders that both succeed, superposed with amplitudes `α`, `β` and recorded by orthogonal
records, succeed with chance `|α|² + |β|² = 1` (the records remove the interference). Recognition: the success of
two orders added with their record. -/
theorem row_H03 {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (ψ₁ ψ₂ : Fin n → ℂ) (α β : ℂ)
    (h1 : P.mulVec ψ₁ = ψ₁) (h2 : P.mulVec ψ₂ = ψ₂) (n1 : ∑ i, Complex.normSq (ψ₁ i) = 1)
    (n2 : ∑ i, Complex.normSq (ψ₂ i) = 1) (hab : Complex.normSq α + Complex.normSq β = 1) :
    Article.successWithRecords P ψ₁ ψ₂ α β = 1 :=
  Article.rowH03_success P ψ₁ ψ₂ α β h1 h2 n1 n2 hab

end Comparison.System
