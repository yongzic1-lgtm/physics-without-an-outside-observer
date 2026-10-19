import Comparison.WholePicture.Cells
import Comparison.Existence.Motion

/-!
# The local form on the cells (Proposition 63; Eq. (30) and Eq. (28);
Proposition S63 and Eq. (43) of the public edition)

Proposition 63 assembles the terms of Propositions 59 to 62 into one action and states that its stationarity
gives their equations and the scalar's equation `D_μ D^μ φ − ∂V/∂φ† − ψ̄_R 𝒴† ψ_L = 0`. This file proves the
assembled statement on the article's own finite cell complex, the cells of `RP⁴` (sixteen vertices, forty links, forty
squares; `WholePicture/Cells.lean`), where every variation is a finite one:

* `Stationary`: `δΓ = 0` at a configuration, the derivative of `t ↦ Γ(x + t η)` at `0` vanishing for every
  variation `η`.
* `gaugeAction κ j θ = κ ‖Cθ‖² − ⟨j, θ⟩`: the plane's kept phase on the links with the second variation of
  Proposition 62 and a current `j`; `gauge_first_variation`, `gauge_stationary_iff`: **`δ_θ Γ = 0` iff
  `2κ CᵀC θ = j`**, Maxwell's inhomogeneous equations on the cells (the homogeneous ones are `∂∂ = 0`,
  `Cells.bd_bd`); `cReal_mul_grad`: `C · grad = 0`; `gauge_invariant`: the action does not see `θ + grad χ` when
  the current is conserved; `current_conserved`: **every current that sources a stationary field is conserved**,
  `gradᵀ j = 0`.
* `scalarAction λ c s φ = Σ_links |φ_v − φ_u|² + Σ_x λ(|φ_x|² − c)² + Σ_x 2 Re(s̄_x φ_x)`: the last-step direction's length
  with its potential and the Yukawa source `s = ψ̄_R 𝒴† ψ_L`; `scalar_first_variation`, `scalar_stationary_iff`:
  **`δ_φ Γ = 0` iff `(Lφ)_x + 2λ(|φ_x|² − c)φ_x + s_x = 0` at every vertex**, with `L = gradᵀ grad` the Laplacian
  of the cells: the scalar's equation `−Δφ + ∂V/∂φ† + ψ̄_R 𝒴† ψ_L = 0` at `c = v²/2`.
* `local_form`: **the assembled action `Γ = −κ‖Cθ‖² + ⟨j, θ⟩ − (scalar)` is stationary in all its fields
  together iff both field equations hold.**
* `potential_minimum`, `potential_about_minimum`: the potential is least exactly at `|φ|² = v²/2`, and about it
  the radial mode has `m_H² = 2λv²`.
* `dirac_mass_shell`: **the chart's Dirac operator `Σ_μ p_μ Γ_μ + iM Γ₄` (Proposition 60) has a nonzero null
  vector iff `p² = M²`**: every solution of the first-order equation is on the mass shell.

Not in this file, and not yet in Lean: the continuum assembly `∫ d⁴x √−g` of the finite action (the limit of the
lattice spacing), the currents `j` and `s` as the minimal couplings of the matter fields, and the variation of the
curvature term `tr(γ_h 𝓕 ∧ 𝓕)` in `e` and `ω` (whose algebraic identity and `Λ = 3/ℓ²` are
`WholePicture/Curvature.lean`).
-/

namespace Comparison.Article

open Matrix hiding J
open Comparison.WholePicture

/-! ## The first variation -/

section Variation

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- **`δS = 0` at `x`:** the first variation of `S` vanishes in every direction. -/
def Stationary (S : E → ℝ) (x : E) : Prop :=
  ∀ η : E, HasDerivAt (fun t : ℝ => S (x + t • η)) 0 0

theorem stationary_iff_of_hasDerivAt {S : E → ℝ} {x : E} {D : E → ℝ}
    (hD : ∀ η, HasDerivAt (fun t : ℝ => S (x + t • η)) (D η) 0) :
    Stationary S x ↔ ∀ η, D η = 0 := by
  constructor
  · intro h η
    exact (hD η).unique (h η)
  · intro h η
    have := hD η
    rwa [h η] at this

end Variation

theorem hasDerivAt_quad (a b c : ℝ) : HasDerivAt (fun t : ℝ => a + t * b + t ^ 2 * c) b 0 := by
  have h1 : HasDerivAt (fun t : ℝ => t * b) (1 * b) 0 := (hasDerivAt_id' 0).mul_const b
  have h2 : HasDerivAt (fun t : ℝ => t ^ 2 * c) (((2 : ℕ) : ℝ) * (0 : ℝ) ^ (2 - 1) * c) 0 :=
    (hasDerivAt_pow 2 (0 : ℝ)).mul_const c
  have h := ((hasDerivAt_const (0 : ℝ) a).add h1).add h2
  convert h using 1
  simp

/-! ## The cells: gradient and circulation -/

/-- **The gradient on the cells:** links × vertices, `+1` at the link's head and `−1` at its tail. -/
def gradZ : Matrix (Fin 40) (Fin 16) ℤ :=
  Matrix.of fun l x => (if linkV l = x then 1 else 0) - (if linkU l = x then 1 else 0)

noncomputable def gradC : Matrix (Fin 40) (Fin 16) ℝ := gradZ.map (Int.castRingHom ℝ)

/-- **`C · grad = 0`:** a phase that is a gradient has no circulation around any square. -/
theorem cReal_mul_grad : cReal * gradC = 0 := by
  have h : cMat * gradZ = 0 := by
    ext q x
    simp only [Matrix.mul_apply, cMat, gradZ, Matrix.of_apply, Matrix.zero_apply]
    exact cZ_div q x
  have h' := congrArg (fun M => M.map (Int.castRingHom ℝ)) h
  simp only [Matrix.map_mul, Matrix.map_zero _ (map_zero _)] at h'
  rw [cReal, gradC]
  exact h'

/-! ## The gauge field: Maxwell's equations on the cells -/

/-- **The gauge action:** `κ ‖Cθ‖² − ⟨j, θ⟩`. -/
noncomputable def gaugeAction (κ : ℝ) (j θ : Fin 40 → ℝ) : ℝ :=
  κ * ∑ q, (cReal *ᵥ θ) q ^ 2 - ∑ l, j l * θ l

theorem gram_dot (θ η : Fin 40 → ℝ) :
    ∑ q, (cReal *ᵥ θ) q * (cReal *ᵥ η) q = ∑ l, η l * ((cRealᵀ * cReal) *ᵥ θ) l := by
  have e : η ⬝ᵥ ((cRealᵀ * cReal) *ᵥ θ) = (cReal *ᵥ η) ⬝ᵥ (cReal *ᵥ θ) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  have e2 : ∑ q, (cReal *ᵥ θ) q * (cReal *ᵥ η) q = (cReal *ᵥ η) ⬝ᵥ (cReal *ᵥ θ) := by
    rw [dotProduct]
    exact Finset.sum_congr rfl fun q _ => mul_comm _ _
  rw [e2, ← e, dotProduct]

/-- **The first variation of the gauge action** in the direction `η`: `Σ_l η_l (2κ (CᵀCθ)_l − j_l)`. -/
theorem gauge_first_variation (κ : ℝ) (j θ η : Fin 40 → ℝ) :
    HasDerivAt (fun t : ℝ => gaugeAction κ j (θ + t • η))
      (∑ l, η l * (2 * κ * ((cRealᵀ * cReal) *ᵥ θ) l - j l)) 0 := by
  have e : (fun t : ℝ => gaugeAction κ j (θ + t • η)) = fun t =>
      (κ * ∑ q, (cReal *ᵥ θ) q ^ 2 - ∑ l, j l * θ l) +
        t * (2 * κ * ∑ q, (cReal *ᵥ θ) q * (cReal *ᵥ η) q - ∑ l, j l * η l) +
        t ^ 2 * (κ * ∑ q, (cReal *ᵥ η) q ^ 2) := by
    funext t
    simp only [gaugeAction, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  rw [e]
  refine (hasDerivAt_quad _ _ _).congr_deriv ?_
  rw [gram_dot]
  simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem sum_mul_self_eq_zero {n : ℕ} {w : Fin n → ℝ} (h : ∑ l, w l * w l = 0) : w = 0 := by
  have h' := (Finset.sum_eq_zero_iff_of_nonneg (fun l _ => mul_self_nonneg (w l))).mp h
  funext l
  exact mul_self_eq_zero.mp (h' l (Finset.mem_univ l))

/-- **`δ_θ Γ = 0` iff `2κ CᵀC θ = j`:** Maxwell's inhomogeneous equations on the cells. -/
theorem gauge_stationary_iff (κ : ℝ) (j θ : Fin 40 → ℝ) :
    Stationary (gaugeAction κ j) θ ↔ (2 * κ) • ((cRealᵀ * cReal) *ᵥ θ) = j := by
  rw [stationary_iff_of_hasDerivAt (gauge_first_variation κ j θ)]
  constructor
  · intro h
    have h0 := sum_mul_self_eq_zero (h (fun l => 2 * κ * ((cRealᵀ * cReal) *ᵥ θ) l - j l))
    funext l
    have := congrFun h0 l
    simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at this ⊢
    linarith
  · intro h η
    have h' : ∀ l, 2 * κ * ((cRealᵀ * cReal) *ᵥ θ) l - j l = 0 := by
      intro l
      have := congrFun h l
      simp only [Pi.smul_apply, smul_eq_mul] at this
      linarith
    simp [h']

/-- **The current is conserved:** a current that sources a stationary field has `gradᵀ j = 0`. -/
theorem current_conserved {κ : ℝ} {j θ : Fin 40 → ℝ} (h : Stationary (gaugeAction κ j) θ) :
    gradCᵀ *ᵥ j = 0 := by
  rw [gauge_stationary_iff] at h
  rw [← h, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.transpose_mul,
    cReal_mul_grad, Matrix.transpose_zero, Matrix.zero_mul, Matrix.zero_mulVec, smul_zero]

/-- **Gauge invariance:** the flux does not see a gradient, so `Γ(θ + grad χ) = Γ(θ) − ⟨gradᵀ j, χ⟩`, and the
action is invariant when the current is conserved. -/
theorem gauge_invariant (κ : ℝ) (j θ : Fin 40 → ℝ) (χ : Fin 16 → ℝ) :
    gaugeAction κ j (θ + gradC *ᵥ χ) = gaugeAction κ j θ - (gradCᵀ *ᵥ j) ⬝ᵥ χ ∧
      (gradCᵀ *ᵥ j = 0 → gaugeAction κ j (θ + gradC *ᵥ χ) = gaugeAction κ j θ) := by
  have hC : cReal *ᵥ (θ + gradC *ᵥ χ) = cReal *ᵥ θ := by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, cReal_mul_grad, Matrix.zero_mulVec, add_zero]
  have hj : ∑ l, j l * (θ + gradC *ᵥ χ) l = ∑ l, j l * θ l + (gradCᵀ *ᵥ j) ⬝ᵥ χ := by
    have : (gradCᵀ *ᵥ j) ⬝ᵥ χ = j ⬝ᵥ (gradC *ᵥ χ) := by
      rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
    rw [this, dotProduct, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Pi.add_apply]
    ring
  have key : gaugeAction κ j (θ + gradC *ᵥ χ) = gaugeAction κ j θ - (gradCᵀ *ᵥ j) ⬝ᵥ χ := by
    rw [gaugeAction, gaugeAction, hC, hj]
    ring
  refine ⟨key, fun h0 => ?_⟩
  rw [key, h0, zero_dotProduct, sub_zero]

/-! ## The scalar: the last-step direction's length, its potential and the Yukawa source -/

/-- **The scalar's action on the cells:** the hop on the forty links, the potential `λ(|φ_x|² − c)²` at the
sixteen vertices, and the Yukawa source `s`. -/
noncomputable def scalarAction (lam c : ℝ) (s φ : Fin 16 → ℂ) : ℝ :=
  ∑ l, Complex.normSq (φ (linkV l) - φ (linkU l)) + ∑ x, lam * (Complex.normSq (φ x) - c) ^ 2 +
    ∑ x, 2 * ((starRingEnd ℂ) (s x) * φ x).re

/-- The Laplacian of the cells, `L = gradᵀ grad`: `(Lφ)_x = Σ_l ([v_l = x] − [u_l = x])(φ_{v_l} − φ_{u_l})`. -/
noncomputable def lapC (φ : Fin 16 → ℂ) (x : Fin 16) : ℂ :=
  ∑ l, ((if linkV l = x then 1 else 0) - (if linkU l = x then 1 else 0)) * (φ (linkV l) - φ (linkU l))

/-- **The scalar's field equation** at the vertex `x`: `(Lφ)_x + 2λ(|φ_x|² − c)φ_x + s_x`. -/
noncomputable def scalarEq (lam c : ℝ) (s φ : Fin 16 → ℂ) (x : Fin 16) : ℂ :=
  lapC φ x + ((2 * lam * (Complex.normSq (φ x) - c) : ℝ) : ℂ) * φ x + s x

theorem normSq_line (a b : ℂ) (t : ℝ) :
    Complex.normSq (a + (t : ℂ) * b) =
      Complex.normSq a + t * (2 * (a * (starRingEnd ℂ) b).re) + t ^ 2 * Complex.normSq b := by
  rw [Complex.normSq_add, Complex.normSq_mul, Complex.normSq_ofReal]
  have : a * (starRingEnd ℂ) ((t : ℂ) * b) = (t : ℂ) * (a * (starRingEnd ℂ) b) := by
    rw [map_mul, Complex.conj_ofReal]; ring
  rw [this, Complex.re_ofReal_mul]
  ring

theorem hasDerivAt_normSq_line (a b : ℂ) :
    HasDerivAt (fun t : ℝ => Complex.normSq (a + (t : ℂ) * b)) (2 * (a * (starRingEnd ℂ) b).re) 0 := by
  have e : (fun t : ℝ => Complex.normSq (a + (t : ℂ) * b)) = fun t =>
      Complex.normSq a + t * (2 * (a * (starRingEnd ℂ) b).re) + t ^ 2 * Complex.normSq b := by
    funext t; exact normSq_line a b t
  rw [e]
  exact hasDerivAt_quad _ _ _

/-- Summation by parts on the cells: `Σ_l a_l conj(η_{v_l} − η_{u_l}) = Σ_x (Lφ)_x conj η_x`. -/
theorem hop_by_parts (φ η : Fin 16 → ℂ) :
    ∑ l, (φ (linkV l) - φ (linkU l)) * (starRingEnd ℂ) (η (linkV l) - η (linkU l)) =
      ∑ x, lapC φ x * (starRingEnd ℂ) (η x) := by
  simp only [lapC, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h1 : ∑ x : Fin 16, (if linkV l = x then (1 : ℂ) else 0) * (φ (linkV l) - φ (linkU l)) *
      (starRingEnd ℂ) (η x) = (φ (linkV l) - φ (linkU l)) * (starRingEnd ℂ) (η (linkV l)) := by
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have h2 : ∑ x : Fin 16, (if linkU l = x then (1 : ℂ) else 0) * (φ (linkV l) - φ (linkU l)) *
      (starRingEnd ℂ) (η x) = (φ (linkV l) - φ (linkU l)) * (starRingEnd ℂ) (η (linkU l)) := by
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [sub_mul, Finset.sum_sub_distrib]
  rw [h1, h2, map_sub]
  ring

/-- **The first variation of the scalar's action** in the direction `η`:
`Σ_x 2 Re(E_x conj η_x)` with `E_x` the field equation. -/
theorem scalar_first_variation (lam c : ℝ) (s φ η : Fin 16 → ℂ) :
    HasDerivAt (fun t : ℝ => scalarAction lam c s (φ + t • η))
      (∑ x, 2 * (scalarEq lam c s φ x * (starRingEnd ℂ) (η x)).re) 0 := by
  have e : (fun t : ℝ => scalarAction lam c s (φ + t • η)) = fun t : ℝ =>
      (∑ l, Complex.normSq ((φ (linkV l) - φ (linkU l)) + (t : ℂ) * (η (linkV l) - η (linkU l))) +
        ∑ x, lam * (Complex.normSq (φ x + (t : ℂ) * η x) - c) ^ 2) +
        ∑ x, (2 * ((starRingEnd ℂ) (s x) * φ x).re + t * (2 * ((starRingEnd ℂ) (s x) * η x).re)) := by
    funext t
    simp only [scalarAction, Pi.add_apply, Pi.smul_apply, Complex.real_smul]
    congr 1
    · congr 1
      refine Finset.sum_congr rfl fun l _ => ?_
      congr 1
      ring
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [mul_add, Complex.add_re, show (starRingEnd ℂ) (s x) * ((t : ℂ) * η x) =
        (t : ℂ) * ((starRingEnd ℂ) (s x) * η x) by ring, Complex.re_ofReal_mul]
      ring
  rw [e]
  have h1 := HasDerivAt.sum (u := Finset.univ) (fun l (_ : l ∈ Finset.univ) =>
    hasDerivAt_normSq_line (φ (linkV l) - φ (linkU l)) (η (linkV l) - η (linkU l)))
  have h2 := HasDerivAt.sum (u := Finset.univ) (fun x (_ : x ∈ Finset.univ) =>
    (((hasDerivAt_normSq_line (φ x) (η x)).sub_const c).pow 2).const_mul lam)
  have h3 := HasDerivAt.sum (u := Finset.univ) (fun x (_ : x ∈ Finset.univ) =>
    (hasDerivAt_quad (2 * ((starRingEnd ℂ) (s x) * φ x).re)
      (2 * ((starRingEnd ℂ) (s x) * η x).re) 0))
  have h := (h1.add h2).add h3
  refine (h.congr_of_eventuallyEq ?_).congr_deriv ?_
  · refine Filter.Eventually.of_forall fun t => ?_
    simp
  · simp only [Complex.ofReal_zero, zero_mul, add_zero, Nat.cast_ofNat]
    have hp := hop_by_parts φ η
    have hre := congrArg Complex.re hp
    simp only [Complex.re_sum] at hre
    rw [show ∑ l, 2 * ((φ (linkV l) - φ (linkU l)) * (starRingEnd ℂ) (η (linkV l) - η (linkU l))).re =
      2 * ∑ l, ((φ (linkV l) - φ (linkU l)) * (starRingEnd ℂ) (η (linkV l) - η (linkU l))).re by
        rw [Finset.mul_sum], hre, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [scalarEq, add_mul, Complex.add_re, mul_assoc, Complex.re_ofReal_mul]
    have hs : ((starRingEnd ℂ) (s x) * η x).re = (s x * (starRingEnd ℂ) (η x)).re := by
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    rw [hs]
    ring

/-- **`δ_φ Γ = 0` iff the scalar's equation holds at every vertex.** -/
theorem scalar_stationary_iff (lam c : ℝ) (s φ : Fin 16 → ℂ) :
    Stationary (scalarAction lam c s) φ ↔ ∀ x, scalarEq lam c s φ x = 0 := by
  rw [stationary_iff_of_hasDerivAt (scalar_first_variation lam c s φ)]
  constructor
  · intro h
    have h0 := h (scalarEq lam c s φ)
    have hn : ∀ x, 0 ≤ 2 * (scalarEq lam c s φ x * (starRingEnd ℂ) (scalarEq lam c s φ x)).re := by
      intro x
      rw [Complex.mul_conj, Complex.ofReal_re]
      have := Complex.normSq_nonneg (scalarEq lam c s φ x)
      linarith
    have h' := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hn x)).mp h0
    intro x
    have hx := h' x (Finset.mem_univ x)
    rw [Complex.mul_conj, Complex.ofReal_re] at hx
    exact Complex.normSq_eq_zero.mp (by linarith)
  · intro h η
    simp [h]

/-! ## The assembled action -/

/-- **The local form on the cells:** `Γ(θ, φ) = −κ‖Cθ‖² + ⟨j, θ⟩ − [Σ |φ_v − φ_u|² + Σ λ(|φ|² − c)² +
Σ 2 Re(s̄ φ)]`, the plane's kept phase with its current and the last-step direction's length with its potential and its Yukawa
source. -/
noncomputable def localAction (κ lam c : ℝ) (j : Fin 40 → ℝ) (s : Fin 16 → ℂ)
    (F : (Fin 40 → ℝ) × (Fin 16 → ℂ)) : ℝ :=
  -gaugeAction κ j F.1 - scalarAction lam c s F.2

/-- **Proposition 63 on the cells: `δΓ = 0` gives the field equations.** The assembled action is stationary in
all its fields together exactly when Maxwell's equations `2κ CᵀC θ = j` and the scalar's equation
`(Lφ)_x + 2λ(|φ_x|² − c)φ_x + s_x = 0` hold. -/
theorem local_form (κ lam c : ℝ) (j : Fin 40 → ℝ) (s : Fin 16 → ℂ) (θ : Fin 40 → ℝ) (φ : Fin 16 → ℂ) :
    Stationary (localAction κ lam c j s) (θ, φ) ↔
      (2 * κ) • ((cRealᵀ * cReal) *ᵥ θ) = j ∧ ∀ x, scalarEq lam c s φ x = 0 := by
  have hD : ∀ η : (Fin 40 → ℝ) × (Fin 16 → ℂ), HasDerivAt
      (fun t : ℝ => localAction κ lam c j s ((θ, φ) + t • η))
      (-(∑ l, η.1 l * (2 * κ * ((cRealᵀ * cReal) *ᵥ θ) l - j l)) -
        ∑ x, 2 * (scalarEq lam c s φ x * (starRingEnd ℂ) (η.2 x)).re) 0 := by
    intro η
    have h := (gauge_first_variation κ j θ η.1).neg.sub (scalar_first_variation lam c s φ η.2)
    convert h using 1
    funext t
    simp [localAction]
  rw [stationary_iff_of_hasDerivAt hD, ← gauge_stationary_iff, ← scalar_stationary_iff,
    stationary_iff_of_hasDerivAt (gauge_first_variation κ j θ),
    stationary_iff_of_hasDerivAt (scalar_first_variation lam c s φ)]
  constructor
  · intro h
    refine ⟨fun η => ?_, fun η => ?_⟩
    · have := h (η, 0)
      simpa using this
    · have := h (0, η)
      simpa using this
  · rintro ⟨h1, h2⟩ η
    rw [h1 η.1, h2 η.2]
    ring

/-! ## The potential and the Dirac operator -/

/-- **The potential is least exactly on `|φ|² = c`** (`c = v²/2`). -/
theorem potential_minimum {lam : ℝ} (hl : 0 < lam) (c r : ℝ) :
    0 ≤ lam * (r - c) ^ 2 ∧ (lam * (r - c) ^ 2 = 0 ↔ r = c) := by
  refine ⟨by positivity, ⟨fun h => ?_, fun h => by rw [h]; ring⟩⟩
  have : (r - c) ^ 2 = 0 := by
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hl.ne'
    · exact h
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  linarith

/-- **About the minimum** `φ = (v + h)/√2` the potential is `λv²h² + λvh³ + λh⁴/4`: the radial mode has
`m_H² = 2λv²`. -/
theorem potential_about_minimum (lam v h : ℝ) :
    lam * ((v + h) ^ 2 / 2 - v ^ 2 / 2) ^ 2 = lam * v ^ 2 * h ^ 2 + lam * v * h ^ 3 + lam * h ^ 4 / 4 := by
  ring

/-- The Dirac operator of the chart at momentum `p` and mass `M` (Proposition 60). -/
noncomputable def diracOp (O : Matrix (Fin 5) (Fin 5) ℝ) (p : Fin 4 → ℝ) (M : ℝ) : Matrix Four Four ℂ :=
  ∑ μ : Fin 4, (p μ : ℂ) • γv (O μ.castSucc) + (Complex.I * M) • γv (O (Fin.last 4))

/-- **The first-order equation is on the mass shell:** the chart's Dirac operator has a nonzero null vector
exactly when `Σ_μ p_μ² = M²`. -/
theorem dirac_mass_shell (O : Matrix (Fin 5) (Fin 5) ℝ) (hO : O * Oᵀ = 1) (p : Fin 4 → ℝ) (M : ℝ) :
    (∃ ψ : Four → ℂ, ψ ≠ 0 ∧ diracOp O p M *ᵥ ψ = 0) ↔ ∑ μ, p μ ^ 2 = M ^ 2 := by
  have hsq : diracOp O p M * diracOp O p M = ((∑ μ, p μ ^ 2 - M ^ 2 : ℝ) : ℂ) • (1 : Matrix Four Four ℂ) :=
    dirac_square O hO p M
  constructor
  · rintro ⟨ψ, hψ, hD⟩
    have h2 : (diracOp O p M * diracOp O p M) *ᵥ ψ = 0 := by
      rw [← Matrix.mulVec_mulVec, hD, Matrix.mulVec_zero]
    rw [hsq, Matrix.smul_mulVec, Matrix.one_mulVec] at h2
    rcases smul_eq_zero.mp h2 with h | h
    · have h' : (∑ μ, p μ ^ 2 - M ^ 2 : ℝ) = 0 := by exact_mod_cast h
      linarith
    · exact absurd h hψ
  · intro h
    have hz : diracOp O p M * diracOp O p M = 0 := by
      rw [hsq, h, sub_self, Complex.ofReal_zero, zero_smul]
    have hdet : (diracOp O p M).det = 0 := by
      have := congrArg Matrix.det hz
      rw [Matrix.det_mul, Matrix.det_zero] at this
      exact mul_self_eq_zero.mp this
    obtain ⟨ψ, hψ, hD⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    exact ⟨ψ, hψ, hD⟩

end Comparison.Article
