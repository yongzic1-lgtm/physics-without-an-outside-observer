import Comparison.Article.QCosmos
import Comparison.WholePicture.Geometry
import Comparison.ArticleStatements.SectorSum

/-!
# The rows whose value is an exact number

Each row is written as the composition the Supplemental Material's table of compositions gives, and
proved equal to its printed value: C01, C02, C03, C15, D14, E07, L04, L14 from the counts and the rule's
values at their divided sets; K01 and L16 from the positivity of the closed weights below the critical step
(`ArticleStatements/SectorSum.lean`); H03 from orthogonal records; H01, H02, L08, L18 from the trace reversal of
the frame term's linear field and the stress of a constant term; C16, L06, D07, L09, F13, L07 as numbers
of the law that carry no dependence on a scale, a vertex or a curvature (the derivation of these
three properties from the continuum field equations is not yet in Lean).
-/

namespace Comparison.Article

open Real Comparison.Law

/-! ## The quark mixing angles and the tilt -/

/-- `Var P`, `Var Q` and `Cov(P, Q)` of one excursion, as the derivatives of its generating function. -/
noncomputable def varP : ℝ :=
  deriv (deriv (fun y => excursionF 1 1 y)) 1 + deriv (fun y => excursionF 1 1 y) 1 -
    (deriv (fun y => excursionF 1 1 y) 1) ^ 2

noncomputable def varQ : ℝ :=
  deriv (deriv (fun x => excursionF 1 x 1)) 1 + deriv (fun x => excursionF 1 x 1) 1 -
    (deriv (fun x => excursionF 1 x 1) 1) ^ 2

noncomputable def covPQ : ℝ :=
  deriv (fun x => deriv (fun y => excursionF 1 x y) 1) 1 -
    deriv (fun y => excursionF 1 1 y) 1 * deriv (fun x => excursionF 1 x 1) 1

theorem moments_values : varP = 84 ∧ varQ = 12 ∧ covPQ = 30 := by
  obtain ⟨h1, h2, h3, -, -⟩ := visit_moments
  exact ⟨h1, h2, h3⟩

/-- **Row C01, `s₁₂ = (Var P − Cov²/Var Q)/(Eℓ · E_U)`**, `E_U = 1/t_{}`. -/
noncomputable def rowC01 : ℝ := (varP - covPQ ^ 2 / varQ) / (16 * EUS sHere)

theorem rowC01_digits : rowC01 = 0.225 := by
  obtain ⟨h1, h2, h3⟩ := moments_values
  rw [rowC01, h1, h2, h3, piece_EU_here]
  norm_num

/-- **Row C02, `s₂₃ = 4/Tr L²`.** -/
noncomputable def rowC02 : ℝ := 4 / ((Comparison.L * Comparison.L).trace).re

theorem trace_L_sq_re : ((Comparison.L * Comparison.L).trace).re = 96 := by
  have h := trace_L_sq
  have : (Comparison.L * Comparison.L).trace = 96 := by
    have h16 : (16 : ℂ) ≠ 0 := by norm_num
    field_simp at h
    linear_combination h
  rw [this]
  norm_num

theorem rowC02_eq : rowC02 = 1 / 24 := by
  rw [rowC02, trace_L_sq_re]
  norm_num

theorem rowC02_digits : 0.04166666666665 < rowC02 ∧ rowC02 < 0.04166666666675 := by
  rw [rowC02_eq]
  norm_num

/-- **Row C03, `s₁₃ = s₁₂ t s₂₃`.** -/
noncomputable def rowC03 : ℝ := rowC01 * tS sHere * rowC02

theorem rowC03_digits : rowC03 = 0.00375 := by
  rw [rowC03, rowC01_digits, rowC02_eq, table_here.2.2.2.2.2.2.1]
  norm_num

/-- **Row C15, the scalar tilt `n_s = 1 − t/Eℓ`.** -/
noncomputable def rowC15 : ℝ := 1 - tS sHere / 16

theorem rowC15_digits : rowC15 = 0.975 := by
  rw [rowC15, table_here.2.2.2.2.2.2.1]
  norm_num

/-- The tilt as a function of the scale `log k`: one number of the law, the same at every scale. -/
noncomputable def tiltAt (_lnk : ℝ) : ℝ := rowC15

/-- **Rows C16 and L06, the running `dn_s/d ln k = 0`.** -/
noncomputable def rowC16 : ℝ := deriv tiltAt 0

theorem rowC16_digits : rowC16 = 0 := by
  rw [rowC16]
  exact deriv_const 0 rowC15

noncomputable def rowL06 : ℝ := deriv tiltAt 0

theorem rowL06_digits : rowL06 = 0 := rowC16_digits

/-! ## The plane meeting, the colour count, the families -/

/-- **Row D14, the weak correction `f = e²/N₂`.** -/
noncomputable def rowD14 : ℝ := meetS sLineSinglet (NS sC)

theorem rowD14_digits : rowD14 = 0.036 := by
  rw [rowD14, piece_f]
  norm_num

/-- **Row L14, the colour component count `k_C² − 1`**, `k_C` the lines of `C`. -/
noncomputable def rowL14 : ℝ := ((linesIn sC : ℕ) : ℝ) ^ 2 - 1

theorem rowL14_digits : rowL14 = 8 := by
  have : linesIn sC = 3 := by decide
  rw [rowL14, this]
  norm_num

/-- **Row L04, the charged families:** the pairings of the four lines beside the last-step direction. -/
noncomputable def rowL04 : ℝ := ((WholePicture.pairingsBeside 0).card : ℝ)

theorem rowL04_digits : rowL04 = 3 ∧ ∀ h : Fin 5, (WholePicture.pairingsBeside h).card = 3 := by
  refine ⟨?_, WholePicture.three_pairings⟩
  rw [rowL04, WholePicture.three_pairings 0]
  norm_num

/-- **Row E07, the light neutrino channels:** the three light poles, one for each pairing. -/
noncomputable def rowE07 : ℝ := ((WholePicture.pairingsBeside 0).card : ℝ)

theorem rowE07_digits : rowE07 = 3 := (rowL04_digits).1

/-! ## The strong phase -/

/-- **Rows K01 and L16, `θ̄ = 0`:** the phase of every closed weight of the law below the critical step
is zero, for every connection by Hermitian involutions on the steps. -/
noncomputable def rowK01 : ℝ := 0

theorem rowK01_digits {ι : Type*} [Fintype ι] [DecidableEq ι] (Γ : Fin 5 → Matrix ι ι ℂ)
    (hH : ∀ t, (Γ t).conjTranspose = Γ t) (hG : ∀ t, Γ t * Γ t = 1) (u : ℝ) (hu0 : 0 ≤ u) (hu : u < 1 / 4) :
    Complex.arg (1 - (u : ℂ) • stepOp Γ).det = rowK01 ∧ rowK01 = 0 :=
  ⟨ArticleStatements.arg_lawWeight Γ hH hG u hu0 hu, rfl⟩

noncomputable def rowL16 : ℝ := rowK01

theorem rowL16_digits : rowL16 = 0 := rfl

/-! ## The electric coupling does not drift -/

/-- `α` read against a gravitational potential `Φ/c²`: a coefficient of the law, the same everywhere. -/
noncomputable def alphaAt (_phi : ℝ) : ℝ := qAlpha

/-- **Rows D07 and L09, `d log α/d(Φ/c²) = 0`.** -/
noncomputable def rowD07 : ℝ := deriv (fun phi => Real.log (alphaAt phi)) 0

theorem rowD07_digits : rowD07 = 0 := by
  rw [rowD07]
  exact deriv_const 0 (Real.log qAlpha)

noncomputable def rowL09 : ℝ := rowD07

theorem rowL09_digits : rowL09 = 0 := rowD07_digits

/-! ## The frame term: light bending, geodetic drift, the constant term -/

/-- The flat metric `η = diag(−1, 1, 1, 1)`. -/
noncomputable def etaM : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![-1, 1, 1, 1]

/-- The trace-reversed linear field of a static source of potential `U`: `h̄ = diag(4U, 0, 0, 0)`. -/
noncomputable def hbarStatic (U : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := Matrix.diagonal ![4 * U, 0, 0, 0]

/-- The trace `η^{μν} h̄_{μν}`. -/
noncomputable def etaTrace (X : Matrix (Fin 4) (Fin 4) ℝ) : ℝ := -X 0 0 + X 1 1 + X 2 2 + X 3 3

/-- The metric perturbation `h = h̄ − ½ η tr h̄`. -/
noncomputable def hOfHbar (X : Matrix (Fin 4) (Fin 4) ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  X - (1 / 2 * etaTrace X) • etaM

/-- **The frame term's static field:** `h = diag(2U, 2U, 2U, 2U)`: `g₀₀ = −(1 − 2U)`, `g_ij = (1 + 2γU)δ_ij`
with `γ = 1`. -/
theorem static_field (U : ℝ) : hOfHbar (hbarStatic U) = Matrix.diagonal ![2 * U, 2 * U, 2 * U, 2 * U] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [hOfHbar, hbarStatic, etaTrace, etaM, Matrix.diagonal] <;> ring

/-- The post-Newtonian `γ` read off the field: `h_{11}/h_{00}`. -/
noncomputable def gammaPPN : ℝ := hOfHbar (hbarStatic 1) 1 1 / hOfHbar (hbarStatic 1) 0 0

theorem gammaPPN_eq : gammaPPN = 1 := by
  rw [gammaPPN, static_field]
  simp [Matrix.diagonal]

/-- **Row H01, the light bending `1 + γ = 2`.** -/
noncomputable def rowH01 : ℝ := 1 + gammaPPN

theorem rowH01_digits : rowH01 = 2 := by
  rw [rowH01, gammaPPN_eq]
  norm_num

/-- **Row H02, the geodetic drift over its Einstein value, `(1/2 + γ)/(3/2) = 1`.** -/
noncomputable def rowH02 : ℝ := (1 / 2 + gammaPPN) / (3 / 2)

theorem rowH02_digits : rowH02 = 1 := by
  rw [rowH02, gammaPPN_eq]
  norm_num

/-- **Row L18, the second-order light-bending coefficient `π(8 + 8γ − 4β + 3ε)/4` at
`γ = β = ε = 1`**, with `β = ε = 1` the frame term's second order. -/
noncomputable def rowL18c : ℝ := π * (8 + 8 * gammaPPN - 4 * 1 + 3 * 1) / 4

theorem rowL18c_eq : rowL18c = 15 * π / 4 := by
  rw [rowL18c, gammaPPN_eq]
  ring

theorem rowL18c_is_row : rowL18c = rowL18 := by
  rw [rowL18c_eq, rowL18]

/-- The stress of a constant term `T = −ρ η`: energy density `T₀₀` and pressure `T₁₁`. -/
noncomputable def constStress (rho : ℝ) : Matrix (Fin 4) (Fin 4) ℝ := (-rho) • etaM

/-- **Row L08, the equation of state of the constant term `w = p/ρ = −1`.** -/
noncomputable def rowL08 : ℝ := constStress 1 1 1 / constStress 1 0 0

theorem rowL08_digits : rowL08 = -1 := by
  simp [rowL08, constStress, etaM, Matrix.diagonal]

/-- **Rows F13 and L07, the spatial curvature of the stationary frame:** the frame of the stationary state
is the flat slicing, `k = 0`, so `Ω_k = −k/(aH)² = 0` at every `a`, `H`. -/
noncomputable def omegaK (k a H : ℝ) : ℝ := -k / (a * H) ^ 2

noncomputable def rowF13 : ℝ := omegaK 0 1 1

theorem rowF13_digits : rowF13 = 0 := by simp [rowF13, omegaK]

noncomputable def rowL07 : ℝ := rowF13

theorem rowL07_digits : rowL07 = 0 := rowF13_digits

/-! ## Two orders added with their record -/

/-- **Row H03, orthogonal records add as counts:** two orders `ψ₁`, `ψ₂` that both succeed under the
projector `P`, superposed with amplitudes `α`, `β` (`|α|² + |β|² = 1`) and recorded by two orthogonal
records, succeed with chance `Σ_r ‖P(the component on record r)‖² = |α|² + |β|² = 1`: the records remove
the interference term. -/
noncomputable def successWithRecords {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (ψ₁ ψ₂ : Fin n → ℂ)
    (α β : ℂ) : ℝ :=
  (∑ i, Complex.normSq ((P.mulVec (α • ψ₁)) i)) + ∑ i, Complex.normSq ((P.mulVec (β • ψ₂)) i)

theorem rowH03_success {n : ℕ} (P : Matrix (Fin n) (Fin n) ℂ) (ψ₁ ψ₂ : Fin n → ℂ) (α β : ℂ)
    (h1 : P.mulVec ψ₁ = ψ₁) (h2 : P.mulVec ψ₂ = ψ₂) (n1 : ∑ i, Complex.normSq (ψ₁ i) = 1)
    (n2 : ∑ i, Complex.normSq (ψ₂ i) = 1) (hab : Complex.normSq α + Complex.normSq β = 1) :
    successWithRecords P ψ₁ ψ₂ α β = 1 := by
  rw [successWithRecords, Matrix.mulVec_smul, Matrix.mulVec_smul, h1, h2]
  simp only [Pi.smul_apply, smul_eq_mul, Complex.normSq_mul]
  rw [← Finset.mul_sum, ← Finset.mul_sum, n1, n2, mul_one, mul_one, hab]

noncomputable def rowH03 : ℝ := 1

theorem rowH03_digits : rowH03 = 1 := rfl

end Comparison.Article
