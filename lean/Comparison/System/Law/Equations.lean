import Comparison.System.Postulates
import Comparison.System.Law.Critical
import Comparison.Existence.IharaBass
import Comparison.Existence.PlaquetteData
import Comparison.Existence.Excursion
import Comparison.Existence.Motion
import Comparison.Mass.Taylor
import Comparison.Law.Rule
import Comparison.WholePicture.TheLaw
import Comparison.WholePicture.Connection
import Comparison.WholePicture.Green
import Comparison.System.Existence.Six

/-!
# The determinant, returns, critical step and dispersion

The declarations `eq_13` to `eq_18`, `eq_20`, `eq_24` and `eq_25` collect
the theorems of `Existence/IharaBass.lean` (the law and the signed law),
`WholePicture/TheLaw.lean` (the grade factors), `Existence/Excursion.lean` (the excursion and the signed excursion),
`WholePicture/Connection.lean` (positivity for every connection), `WholePicture/Green.lean` (the Green function),
`Mass/Taylor.lean` and `Law/Critical.lean` (the critical step) and `Existence/Motion.lean` (the step in motion).
The declaration `eq_12` is in `Law/Euler.lean`; `eq_19`, `eq_21`, `eq_22`
and `eq_23` are in `Law/Quarters.lean`.
-/

open Matrix Complex Comparison Filter Topology Asymptotics

namespace Comparison.System

namespace Law

/-- The links of the sixteen two-spinor states (unordered pairs of neighbours). -/
def linkCount : ℕ := (Finset.univ.filter fun p : Fin 16 × Fin 16 => p.1 < p.2 ∧ Adjacent p.1 p.2).card

/-- The two-spinor states (characters) of grade `N`: `N` lines on which the two systems disagree. -/
def gradeCount (N : ℕ) : ℕ := (Finset.univ.filter fun x : Fin 16 => (disagreeSet x).card = N).card

theorem gradeCount_values : gradeCount 0 = 1 ∧ gradeCount 2 = 10 ∧ gradeCount 4 = 5 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

theorem grade_cases : ∀ x : Fin 16,
    (disagreeSet x).card = 0 ∨ (disagreeSet x).card = 2 ∨ (disagreeSet x).card = 4 := by
  decide

theorem charValue_grade : ∀ l : Fin 16, charValue l = 5 - 2 * ((disagreeSet l).card : ℤ) := by
  intro l; rfl

/-- The first return of the excursion has the derivative `16` at `z = 1`. -/
theorem excursionGF_deriv_one : HasDerivAt excursionGF 16 1 := by
  have hN : HasDerivAt (fun z : ℂ => z ^ 4 * (1 + z)) 9 1 := by
    have h := (hasDerivAt_pow 4 (1 : ℂ)).mul ((hasDerivAt_id (1 : ℂ)).const_add 1)
    convert h using 1 <;> first | (funext z; simp) | norm_num
  have hD : HasDerivAt (fun z : ℂ => 16 - 8 * z - 3 * z ^ 2 - 3 * z ^ 3) (-23) 1 := by
    have h := ((((hasDerivAt_id (1 : ℂ)).const_mul 8).const_sub 16).sub
      ((hasDerivAt_pow 2 (1 : ℂ)).const_mul 3)).sub ((hasDerivAt_pow 3 (1 : ℂ)).const_mul 3)
    convert h using 1 <;> first | (funext z; simp) | norm_num
  have hD0 : (16 - 8 * (1 : ℂ) - 3 * 1 ^ 2 - 3 * 1 ^ 3) ≠ 0 := by norm_num
  have h := hN.div hD hD0
  change HasDerivAt (fun z : ℂ => z ^ 4 * (1 + z) / (16 - 8 * z - 3 * z ^ 2 - 3 * z ^ 3)) 16 1
  convert h using 1 <;> first | (funext z; simp) | norm_num

theorem excursionGF_one : excursionGF 1 = 1 := by
  norm_num [excursionGF]

/-- `R₋(u) = (1 + 3u²)/(1 + 3u² + 16u⁴)` renews to the signed excursion: `1 − 1/R₋(u) = Φ(4u)`. -/
theorem renewal_minus (u : ℂ) (h1 : 1 + 3 * u ^ 2 ≠ 0) (h2 : 1 + 3 * u ^ 2 + 16 * u ^ 4 ≠ 0) :
    1 - 1 / ((1 + 3 * u ^ 2) / (1 + 3 * u ^ 2 + 16 * u ^ 4)) = Comparison.Law.Phi (4 * u) := by
  have h3 : (16 + 3 * (4 * u) ^ 2) ≠ 0 := by
    intro h; apply h1; linear_combination h / 16
  have e1 : (16 + 3 * (4 * u) ^ 2) = 16 * (1 + 3 * u ^ 2) := by ring
  have e2 : (4 * u) ^ 4 = 256 * u ^ 4 := by ring
  rw [Comparison.Law.Phi, one_div_div, e1, e2]
  field_simp
  ring

theorem Ipow_sq_cases (k : ℕ) : (I ^ k) ^ 2 = 1 ∨ (I ^ k) ^ 2 = -1 := by
  rw [← pow_mul, mul_comm, pow_mul, I_sq]
  rcases neg_one_pow_eq_or ℂ k with h | h <;> simp [h]

theorem Ipow_pow_four (k : ℕ) : (I ^ k) ^ 4 = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, Complex.I_pow_four, one_pow]

end Law

open Comparison.System.Law

/-- **Equation (13), the law:** `det(I₈₀ − uB) = (1 − u²)²⁴(1 − u)(1 − 4u)(1 − u + 4u²)¹⁰(1 + 3u + 4u²)⁵
= (1 − u²)^{40−16} ∏_N k_N(u)^{dim N}` for every `u`, where `40` counts the links and `16` the two-spinor states, and
`dim N` counts the characters of grade `N`: `1, 10, 5` for `N = 0, 2, 4`, the only grades.
Every candidate system: System.uniqueness. -/
theorem eq_13 :
    (∀ u : ℂ, law u = (1 - u ^ 2) ^ 24 * (1 - u) * (1 - 4 * u) * (1 - u + 4 * u ^ 2) ^ 10 *
      (1 + 3 * u + 4 * u ^ 2) ^ 5) ∧
    (∀ u : ℂ, law u = (1 - u ^ 2) ^ (linkCount - Fintype.card (Fin 16)) *
      WholePicture.kN 0 u ^ gradeCount 0 * WholePicture.kN 2 u ^ gradeCount 2 *
        WholePicture.kN 4 u ^ gradeCount 4) ∧
    linkCount = 40 ∧ Fintype.card (Fin 16) = 16 ∧
    gradeCount 0 = 1 ∧ gradeCount 2 = 10 ∧ gradeCount 4 = 5 ∧
    (∀ x : Fin 16, (disagreeSet x).card = 0 ∨ (disagreeSet x).card = 2 ∨ (disagreeSet x).card = 4) := by
  have hl : linkCount = 40 := card_edges
  obtain ⟨g0, g2, g4⟩ := gradeCount_values
  refine ⟨fun u => by rw [law_eq_D_plus, D_plus], fun u => ?_, hl, Fintype.card_fin 16, g0, g2, g4,
    grade_cases⟩
  rw [law_eq_D_plus, WholePicture.law_grade_factors, hl, g0, g2, g4, Fintype.card_fin, pow_one]

/-- **Equation (14), the grade factor:** `k_N(u) = 1 + 4u² − u(5 − 2N)`, and `5 − 2N` is the eigenvalue of the
adjacency on the characters of grade `N` (`A·χ = χ·diag(5 − 2N)`). -/
theorem eq_14 :
    (∀ N u : ℂ, WholePicture.kN N u = 1 + 4 * u ^ 2 - u * (5 - 2 * N)) ∧
    (∀ l : Fin 16, charValue l = 5 - 2 * ((disagreeSet l).card : ℤ)) ∧
    A ℤ * charTable = charTable * Matrix.diagonal charValue := by
  refine ⟨fun N u => rfl, charValue_grade, ?_⟩
  rw [← adjacencyZ_eq]
  exact adjacency_mul_charTable

/-- **Equation (15), the signed law:** `det(I − uB₋) = (1 − u²)²⁴(1 + 3u² + 16u⁴)⁸` for every `u`, and
`A₋² = 5` (in the basis of the two-spinor states, and as `Σ_t γ_t ⊗ 1` on the sixteen amplitudes of two systems). -/
theorem eq_15 :
    (∀ u : ℂ, (1 - u • Bminus).det = (1 - u ^ 2) ^ 24 * (1 + 3 * u ^ 2 + 16 * u ^ 4) ^ 8) ∧
    Aminus * Aminus = (5 : ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ) ∧
    (∑ t, lineOnRel t) * (∑ t, lineOnRel t) = (5 : ℂ) • (1 : Matrix Two Two ℂ) :=
  ⟨fun u => D_minus u, sadjZ_sq, Aminus_sq⟩

/-- **Equation (16), the renewal at the four points `u = i^d/4`:** with `R₋(u) = (1 + 3u²)/(1 + 3u² + 16u⁴)`,
`1 − 1/R₋(u) = Φ(4u)` wherever the denominators do not vanish, and at `u = i^k/4` for every `k`
(`Φ(z) = −z⁴/(16 + 3z²)`): `1 − 1/R₋(i^k/4) = Φ(i^k)`. That `R₋` is the walk's renewed signed return is
Proposition 55 (`prop_55`). -/
theorem eq_16 :
    (∀ u : ℂ, 1 + 3 * u ^ 2 ≠ 0 → 1 + 3 * u ^ 2 + 16 * u ^ 4 ≠ 0 →
      1 - 1 / ((1 + 3 * u ^ 2) / (1 + 3 * u ^ 2 + 16 * u ^ 4)) = Comparison.Law.Phi (4 * u)) ∧
    ∀ k : ℕ, 1 - 1 / ((1 + 3 * (I ^ k / 4) ^ 2) / (1 + 3 * (I ^ k / 4) ^ 2 + 16 * (I ^ k / 4) ^ 4)) =
      Comparison.Law.Phi (I ^ k) := by
  refine ⟨renewal_minus, fun k => ?_⟩
  have e2 : (I ^ k / 4) ^ 2 = (I ^ k) ^ 2 / 16 := by ring
  have e4 : (I ^ k / 4) ^ 4 = 1 / 256 := by rw [div_pow, Ipow_pow_four]; norm_num
  have h1 : 1 + 3 * (I ^ k / 4) ^ 2 ≠ 0 := by
    rw [e2]; rcases Ipow_sq_cases k with h | h <;> rw [h] <;> norm_num
  have h2 : 1 + 3 * (I ^ k / 4) ^ 2 + 16 * (I ^ k / 4) ^ 4 ≠ 0 := by
    rw [e2, e4]; rcases Ipow_sq_cases k with h | h <;> rw [h] <;> norm_num
  rw [renewal_minus _ h1 h2]
  congr 1
  ring

/-- **Equation (17), positivity for every connection:** `(1 + 4u²) − uA_U ⪰ (1 − u)(1 − 4u)` for every unitary
connection `U` and every `u ≥ 0`, with `(1 − u)(1 − 4u) = 1 + 4u² − 5u`. -/
theorem eq_17 :
    (∀ (n : Type) [Fintype n] [DecidableEq n] (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ))
      (u : ℝ), 0 ≤ u → ∀ x : Fin 16 × n → ℂ,
      (1 - u) * (1 - 4 * u) * (star x ⬝ᵥ x).re ≤
        (star x ⬝ᵥ (((1 + 4 * (u : ℂ) ^ 2) • (1 : Matrix (Fin 16 × n) (Fin 16 × n) ℂ) -
          (u : ℂ) • ∑ t, WholePicture.connStep c t) *ᵥ x)).re) ∧
    ∀ u : ℝ, (1 - u) * (1 - 4 * u) = 1 + 4 * u ^ 2 - 5 * u :=
  ⟨fun n _ _ c u hu x => WholePicture.law_quad_unitary c u hu x, fun u => by ring⟩

/-- **Equation (18), the two first returns:** `F(z) = z⁴(1 + z)/(16 − 8z − 3z² − 3z³)` and `Φ(z) = −z⁴/(16 + 3z²)`
are the sums of the excursion's and the signed excursion's series on `|z| ≤ 1` (`z = 4u`); `F(1) = Σ f_n = 1` and
`F′(1) = Σ n f_n = 16`. -/
theorem eq_18 :
    (∀ z : ℂ, ‖z‖ ≤ 1 → HasSum (fun n => (excursionLaw n : ℂ) * z ^ n) (excursionGF z)) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 → HasSum (fun n => (signedLaw n : ℂ) * z ^ n) (Comparison.Law.Phi z)) ∧
    excursionGF 1 = 1 ∧ HasDerivAt excursionGF 16 1 ∧ HasSum excursionLaw 1 ∧
    HasSum (fun n : ℕ => (n : ℝ) * excursionLaw n) 16 :=
  ⟨excursion_gf_eq, signed_gf_eq, excursionGF_one, excursionGF_deriv_one, excursion_total, excursion_mean⟩

/-- **Equation (20), the Green function of the critical germ:** `(5 − A)⁺ = (7 + A)/32 − 3J/128`: the matrix
`G = (7 + A)/32 − 3J/128` satisfies the four Penrose equations for `M = 5 − A`, and every matrix that satisfies
them is `G`; the resistance `R(x, y) = G_xx + G_yy − 2G_xy` from the start's vertex is `b = 7/16` to every plane and
`3/8` to every line. -/
theorem eq_20 :
    WholePicture.lapM = (5 : ℝ) • (1 : Matrix (Fin 16) (Fin 16) ℝ) - A ℝ ∧
    WholePicture.greenM = (1 / 32 : ℝ) • ((7 : ℝ) • (1 : Matrix (Fin 16) (Fin 16) ℝ) + A ℝ) -
      (3 / 128 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ)) ∧
    (WholePicture.lapM * WholePicture.greenM * WholePicture.lapM = WholePicture.lapM ∧
      WholePicture.greenM * WholePicture.lapM * WholePicture.greenM = WholePicture.greenM ∧
      (WholePicture.lapM * WholePicture.greenM)ᵀ = WholePicture.lapM * WholePicture.greenM ∧
      (WholePicture.greenM * WholePicture.lapM)ᵀ = WholePicture.greenM * WholePicture.lapM) ∧
    (∀ X : Matrix (Fin 16) (Fin 16) ℝ, WholePicture.lapM * X * WholePicture.lapM = WholePicture.lapM →
      X * WholePicture.lapM * X = X → (WholePicture.lapM * X)ᵀ = WholePicture.lapM * X →
      (X * WholePicture.lapM)ᵀ = X * WholePicture.lapM → X = WholePicture.greenM) ∧
    (∀ f : Fin 16, (disagreeSet f).card = 2 →
      WholePicture.greenM 0 0 + WholePicture.greenM f f - 2 * WholePicture.greenM 0 f = 7 / 16) ∧
    (∀ l : Fin 16, (disagreeSet l).card = 4 →
      WholePicture.greenM 0 0 + WholePicture.greenM l l - 2 * WholePicture.greenM 0 l = 3 / 8) := by
  have hA : (Matrix.of fun x y => ((WholePicture.adjZ x y : ℤ) : ℝ)) = A ℝ := by
    ext x y
    rw [Matrix.of_apply, wholePicture_adjZ_eq, ← A_map ℝ]
    simp
  have hres : ∀ f : Fin 16, (disagreeSet f).card = 2 →
      WholePicture.green128 0 0 + WholePicture.green128 f f - 2 * WholePicture.green128 0 f = 56 := by
    decide +kernel
  have hres' : ∀ l : Fin 16, (disagreeSet l).card = 4 →
      WholePicture.green128 0 0 + WholePicture.green128 l l - 2 * WholePicture.green128 0 l = 48 := by
    decide +kernel
  refine ⟨wholePicture_lapM_eq, by rw [WholePicture.greenM_eq, hA], WholePicture.green_penrose,
    WholePicture.green_pinv, fun f hf => ?_, fun l hl => ?_⟩
  · have h := congrArg (fun z : ℤ => (z : ℝ)) (hres f hf)
    simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat] at h
    simp only [WholePicture.greenM, Matrix.of_apply]
    linear_combination h / 128
  · have h := congrArg (fun z : ℤ => (z : ℝ)) (hres' l hl)
    simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_ofNat] at h
    simp only [WholePicture.greenM, Matrix.of_apply]
    linear_combination h / 128

/-- **Equation (24), the law near its critical step:** at `u = 1/4 − ε²m²/24`, for every `C³` function `ψ`,
`(1 + 4u²)ψ(x) − u Σ_t ψ(x + εv_t) = (ε²/8)(m²ψ(x) − Δψ(x)) + O(ε³)`, and `Δ = Σ_t (v_t·∇)²` is the Laplacian of
`𝟏^⊥ = ℝ⁴`: `Σ_t D²ψ(v_t, v_t) = Σ_{i=1}^4 D²ψ(f_i, f_i)` for every orthonormal basis `f` of `𝟏^⊥`. -/
theorem eq_24 :
    (∀ (ψ : (Fin 5 → ℝ) → ℝ), ContDiff ℝ 3 ψ → ∀ (x : Fin 5 → ℝ) (m : ℝ),
      (fun ε : ℝ => (1 + 4 * (1 / 4 - ε ^ 2 * m ^ 2 / 24) ^ 2) * ψ x -
        (1 / 4 - ε ^ 2 * m ^ 2 / 24) * ∑ t, ψ (x + ε • vR t) -
        ε ^ 2 / 8 * (m ^ 2 * ψ x - stepLaplacian ψ x)) =O[𝓝 0] (fun ε : ℝ => ε ^ 3)) ∧
    (∀ (ψ : (Fin 5 → ℝ) → ℝ), ContDiff ℝ 2 ψ → ∀ (x : Fin 5 → ℝ) (f : Fin 4 → Fin 5 → ℝ),
      (∀ i j, f i ⬝ᵥ f j = if i = j then 1 else 0) → (∀ i, ∑ a, f i a = 0) →
      stepLaplacian ψ x = ∑ i, fderiv ℝ (fderiv ℝ ψ) x (f i) (f i)) :=
  ⟨fun ψ hψ x m => critical_operator ψ hψ x m,
    fun ψ hψ x f hon hperp => stepLaplacian_eq_frame ψ hψ x f hon hperp⟩

/-- **Equation (25), the dispersion of one step in motion:** for `U = e^{−ikγ_j}e^{−iμγ_h}` (the matrix
exponentials) with `j ≠ h`,
`U + U† = 2 cos k cos μ`; every eigenvalue `λ` of `U` has `|λ| = 1` and `Re λ = cos ω = cos μ cos k`; and for
`|μ|, |k| ≤ 1/2`, `ω = arccos(cos μ cos k)` has `ω² = μ² + k² − μ²k²/3 + O((μ² + k²)³)`, with the explicit bound
`3(μ² + k²)³`. -/
theorem eq_25 :
    (∀ (k μ : ℝ) (j h : Fin 5), stepMotion k μ j h =
      NormedSpace.exp ((-k) • (I • γ j)) * NormedSpace.exp ((-μ) • (I • γ h))) ∧
    (∀ (k μ : ℝ) (j h : Fin 5), j ≠ h → stepMotion k μ j h + (stepMotion k μ j h)ᴴ =
      ((2 * Real.cos k * Real.cos μ : ℝ) : ℂ) • (1 : Matrix Four Four ℂ)) ∧
    (∀ (k μ : ℝ) (j h : Fin 5), j ≠ h → ∀ v : Four → ℂ, v ≠ 0 → ∀ lam : ℂ,
      stepMotion k μ j h *ᵥ v = lam • v → lam.re = Real.cos k * Real.cos μ ∧ Complex.normSq lam = 1) ∧
    (∀ μ k : ℝ, |μ| ≤ 1 / 2 → |k| ≤ 1 / 2 →
      |Real.arccos (Real.cos μ * Real.cos k) ^ 2 - (μ ^ 2 + k ^ 2 - μ ^ 2 * k ^ 2 / 3)| ≤
        3 * (μ ^ 2 + k ^ 2) ^ 3) :=
  ⟨fun k μ j h => by
      rw [Comparison.System.Existence.exp_iγ, Comparison.System.Existence.exp_iγ]; rfl,
    fun k μ _ _ hjh => stepMotion_add_adjoint k μ hjh,
    fun k μ _ _ hjh v hv lam hlam => eigen_phase k μ hjh v hv lam hlam,
    fun μ k hμ hk => dispersion_series μ k hμ hk⟩

end Comparison.System
