import Comparison.WholePicture.OneArc
import Comparison.Colour.BoundStates
import Comparison.Formulas.Kernel

/-!
# The finite statements of the main line that had no theorem (formulas (3), (14), (29))

* `LOmega_inner`: **`L(Ω) = ⟨Ω, LΩ⟩ = 6`** (formula (3)).
* `chi_near_zero`: **`χ(1/4 − δ) = 12δ + 16δ²/(1/4 − δ)`**, so at `δ = ε²m²/24` the gap is
  `ε²m²/2 + O(ε⁴)` (`chi_mass_shell`, formula (14)); `chi_near_zero_bound`: `0 ≤ χ − 12δ ≤ 128δ²` for
  `0 ≤ δ ≤ 1/8`.
* `lawPoly_eq`, `one_arc_explicit`: **`D_θ(u) = D(u) + (e^{−iθ} − 1)uD′(u)/320`** at every one of the
  320 arcs with `D(u) = (1 − u²)²⁴(1 − u)(1 − 4u)(1 − u + 4u²)¹⁰(1 + 3u + 4u²)⁵` written out (formula
  (29); the cofactor identity is `WholePicture.one_arc`, `arc_cofactor_const`).
-/

namespace Comparison.Formulas

open Matrix Polynomial Complex

/-- **`L(Ω) = ⟨Ω, LΩ⟩ = 6`.** -/
theorem LOmega_inner : star Ω ⬝ᵥ (L *ᵥ Ω) = 6 := by
  rw [L_singlet, dotProduct_smul, Ω_norm, smul_eq_mul, mul_one]

/-- **Near the one zero:** `χ(1/4 − δ) = 12δ + 16δ²/(1/4 − δ)`. -/
theorem chi_near_zero (δ : ℂ) (hδ : δ ≠ 1 / 4) :
    chi (1 / 4 - δ) = 12 * δ + 16 * δ ^ 2 / (1 / 4 - δ) := by
  have h : (1 / 4 - δ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hδ)
  have h4 : (1 - δ * 4) ≠ 0 := by
    intro h0
    apply h
    linear_combination h0 / 4
  have e : (1 / 4 - δ) = (1 - δ * 4) / 4 := by ring
  rw [chi, e]
  field_simp
  ring

/-- **The gap is half the mass squared:** at `u = 1/4 − ε²m²/24`,
`χ = ε²m²/2 + 16δ²/(1/4 − δ)` with `δ = ε²m²/24`. -/
theorem chi_mass_shell (ε m : ℂ) (hδ : ε ^ 2 * m ^ 2 / 24 ≠ 1 / 4) :
    chi (1 / 4 - ε ^ 2 * m ^ 2 / 24) =
      ε ^ 2 * m ^ 2 / 2 + 16 * (ε ^ 2 * m ^ 2 / 24) ^ 2 / (1 / 4 - ε ^ 2 * m ^ 2 / 24) := by
  rw [chi_near_zero _ hδ]
  ring

/-- The remainder is of second order: `0 ≤ χ(1/4 − δ) − 12δ ≤ 128δ²` for real `0 ≤ δ ≤ 1/8`. -/
theorem chi_near_zero_bound (δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1 / 8) :
    0 ≤ 1 / (1 / 4 - δ) + 4 * (1 / 4 - δ) - 5 - 12 * δ ∧
      1 / (1 / 4 - δ) + 4 * (1 / 4 - δ) - 5 - 12 * δ ≤ 128 * δ ^ 2 := by
  have hpos : 0 < 1 / 4 - δ := by linarith
  have h4 : (1 - δ * 4) ≠ 0 := by
    intro h0
    linarith
  have e : 1 / (1 / 4 - δ) + 4 * (1 / 4 - δ) - 5 - 12 * δ = 16 * δ ^ 2 / (1 / 4 - δ) := by
    rw [show (1 / 4 - δ) = (1 - δ * 4) / 4 by ring]
    field_simp
    ring
  rw [e]
  constructor
  · positivity
  · rw [div_le_iff₀ hpos]
    nlinarith [sq_nonneg δ]

/-! ## The one arc with the law written out -/

/-- **The law** `D(u) = (1 − u²)²⁴(1 − u)(1 − 4u)(1 − u + 4u²)¹⁰(1 + 3u + 4u²)⁵`. -/
noncomputable def lawD : ℂ[X] :=
  (1 - X ^ 2) ^ 24 * (1 - X) * (1 - 4 * X) * (1 - X + 4 * X ^ 2) ^ 10 * (1 + 3 * X + 4 * X ^ 2) ^ 5

theorem lawPoly_eq : WholePicture.lawPoly = lawD := by
  apply Polynomial.funext
  intro u
  rw [WholePicture.lawPoly_eval, WholePicture.Bc_eq, D_plus]
  simp [lawD]

/-- **Formula (29), one arc marked exactly:** at every one of the 320 arcs `q → p`,
`D_θ(u) = D(u) + (e^{−iθ} − 1) u D′(u)/320`. -/
theorem one_arc_explicit (p q : State) (harc : Continues q p) (θ u : ℂ) :
    (1 - u • WholePicture.Bmark p q (Complex.exp (-Complex.I * θ))).det =
      lawD.eval u + (Complex.exp (-Complex.I * θ) - 1) * u * (derivative lawD).eval u / 320 := by
  rw [WholePicture.one_arc_phase p q harc θ u, lawPoly_eq]

end Comparison.Formulas
