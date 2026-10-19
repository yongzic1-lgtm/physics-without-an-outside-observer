import Comparison.System.Postulates
import Comparison.System.Law.Cells
import Comparison.Article.LocalForm

/-!
# The proof system, the law: Proposition 63 and equations (28), (30), the local form

`prop_63` is the local form on the article's own finite cell
complex, the cells of `RP⁴` (`Article/LocalForm.lean`): the plane's kept phase with its current, the last-step direction's length with
its potential and its Yukawa source, and the first-order step of a line; their assembled action is stationary in all
its fields together exactly when Maxwell's equations and the scalar's equation hold, and the homogeneous pair is
`∂∂ = 0` with orientations over `ℤ` (`Law/Cells.lean`). The continuum assembly `∫d⁴x√−g` (the limit of the cells),
the non-abelian covariant derivative, the curvature term's variation in `e` and `ω`, and the currents as the minimal
couplings of the matter fields stand with the continuum limit and complete Prop. 63 and Eqs. (28) and (30).
-/

open Matrix Comparison Comparison.Article Comparison.WholePicture

namespace Comparison.System

open Comparison.System.Law

/-- **Proposition 63, the local form** (on the cells of `RP⁴`). The assembled action
`Γ(θ, φ) = −κ‖Cθ‖² + ⟨j, θ⟩ − [Σ_links |φ_v − φ_u|² + Σ_x λ(|φ_x|² − c)² + Σ_x 2Re(s̄_xφ_x)]` is stationary in all
its fields together exactly when `2κCᵀCθ = j` (Maxwell's inhomogeneous equations; the homogeneous pair is
`D·C = 0`, the boundary of a boundary, with `C·grad = 0`) and `(Lφ)_x + 2λ(|φ_x|² − c)φ_x + s_x = 0` (the scalar's
equation, `L = gradᵀgrad`); a current that sources a stationary field is conserved, and the gauge action does not see
a gradient when the current is conserved; the potential is least exactly at `|φ|² = c = v²/2`, about which the radial
mode has `m_H² = 2λv²`; the chart's Dirac operator `Σ_μ p_μΓ_μ + iMΓ₄` has a nonzero null vector exactly on the mass
shell `p² = M²`. Recognition: `θ` the electromagnetic potential, `φ` the Higgs field, `s = ψ̄_R𝒴†ψ_L`. -/
theorem prop_63 :
    (∀ (κ lam c : ℝ) (j : Fin 40 → ℝ) (s : Fin 16 → ℂ) (θ : Fin 40 → ℝ) (φ : Fin 16 → ℂ),
      Stationary (localAction κ lam c j s) (θ, φ) ↔
        (2 * κ) • ((cRealᵀ * cReal) *ᵥ θ) = j ∧ ∀ x, scalarEq lam c s φ x = 0) ∧
    (∀ (κ : ℝ) (j θ : Fin 40 → ℝ),
      Stationary (gaugeAction κ j) θ ↔ (2 * κ) • ((cRealᵀ * cReal) *ᵥ θ) = j) ∧
    (∀ (lam c : ℝ) (s φ : Fin 16 → ℂ),
      Stationary (scalarAction lam c s) φ ↔ ∀ x, scalarEq lam c s φ x = 0) ∧
    (∀ {κ : ℝ} {j θ : Fin 40 → ℝ}, Stationary (gaugeAction κ j) θ → gradCᵀ *ᵥ j = 0) ∧
    (∀ (κ : ℝ) (j θ : Fin 40 → ℝ) (χ : Fin 16 → ℝ),
      gaugeAction κ j (θ + gradC *ᵥ χ) = gaugeAction κ j θ - (gradCᵀ *ᵥ j) ⬝ᵥ χ ∧
        (gradCᵀ *ᵥ j = 0 → gaugeAction κ j (θ + gradC *ᵥ χ) = gaugeAction κ j θ)) ∧
    (cMat * gradZ' = 0 ∧ cubeBdZ * cMat = 0 ∧ fourBdZ * cubeBdZ = 0) ∧
    (∀ {lam : ℝ}, 0 < lam → ∀ c r : ℝ, 0 ≤ lam * (r - c) ^ 2 ∧ (lam * (r - c) ^ 2 = 0 ↔ r = c)) ∧
    (∀ lam v h : ℝ, lam * ((v + h) ^ 2 / 2 - v ^ 2 / 2) ^ 2 =
      lam * v ^ 2 * h ^ 2 + lam * v * h ^ 3 + lam * h ^ 4 / 4) ∧
    (∀ (O : Matrix (Fin 5) (Fin 5) ℝ), O * Oᵀ = 1 → ∀ (p : Fin 4 → ℝ) (M : ℝ),
      (∃ ψ : Four → ℂ, ψ ≠ 0 ∧ Article.diracOp O p M *ᵥ ψ = 0) ↔ ∑ μ, p μ ^ 2 = M ^ 2) :=
  ⟨local_form, gauge_stationary_iff, scalar_stationary_iff, fun h => current_conserved h,
    gauge_invariant, bd_bd_int, fun hl c r => potential_minimum hl c r, potential_about_minimum,
    fun O hO p M => dirac_mass_shell O hO p M⟩

/-- **Equation (28), Maxwell's equations on the cells:** `D·C = 0` and `C·grad = 0` (the homogeneous pair, the
boundary of a boundary, with orientations over `ℤ`), and `δ_θ[κ‖Cθ‖² − ⟨j, θ⟩] = 0 ⟺ 2κCᵀCθ = j` (the
inhomogeneous pair) with the current conserved. -/
theorem eq_28 :
    (cMat * gradZ' = 0 ∧ cubeBdZ * cMat = 0) ∧
    (∀ (κ : ℝ) (j θ : Fin 40 → ℝ),
      Stationary (gaugeAction κ j) θ ↔ (2 * κ) • ((cRealᵀ * cReal) *ᵥ θ) = j) ∧
    (∀ {κ : ℝ} {j θ : Fin 40 → ℝ}, Stationary (gaugeAction κ j) θ → gradCᵀ *ᵥ j = 0) :=
  ⟨⟨bd_bd_int.1, bd_bd_int.2.1⟩, gauge_stationary_iff, fun h => current_conserved h⟩

/-- **Equation (30), the action, on the cells:** the assembled action is stationary exactly when its field equations
hold. -/
theorem eq_30 (κ lam c : ℝ) (j : Fin 40 → ℝ) (s : Fin 16 → ℂ) (θ : Fin 40 → ℝ) (φ : Fin 16 → ℂ) :
    Stationary (localAction κ lam c j s) (θ, φ) ↔
      (2 * κ) • ((cRealᵀ * cReal) *ᵥ θ) = j ∧ ∀ x, scalarEq lam c s φ x = 0 :=
  local_form κ lam c j s θ φ

end Comparison.System
