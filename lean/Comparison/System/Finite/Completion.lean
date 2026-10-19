import Comparison.System.Postulates
import Comparison.WholePicture.Moment
import Comparison.WholePicture.MomentSubspaces
import Comparison.ArticleStatements.MixedMoment
import Comparison.RuleAndLaw.FactorsA
import Comparison.WholePicture.TraceFive
import Comparison.WholePicture.Curvature
import Comparison.Existence.LastDirectionSplit
import Comparison.Existence.Moments
import Comparison.Existence.AvailableTransitions
import Comparison.Colour.Proton
import Comparison.Mass.Simple
import Comparison.Colour.Arcs
import Comparison.System.Geometry.SixDirections
import Comparison.System.Law.Critical
import Comparison.System.Law.Phases
import Comparison.System.Completion.Numbers

/-!
# SI S3, statements 12 to 17: the mixed moment, one marked arc, the step weights, the field
# equations, the closed forms of the constants, the long-range zero

About the model; every candidate system is the model up to one
rotation (`System.uniqueness`).
-/

namespace Comparison.System

open Matrix Complex Polynomial Filter Topology Asymptotics

namespace S3

/-- The variance form of the clock: `Σ W(|S| − μ)²/Z = Σ W|S|²/Z − μ²`. -/
theorem clockW_eq (w2 w4 : ℝ) (hZ : 10 * w2 + 5 * w4 ≠ 0) :
    WholePicture.clockW w2 w4 = 9 / 8 *
      ((∑ S ∈ WholePicture.fifteen, WholePicture.cw w2 w4 S * (S.card : ℝ) ^ 2) /
          WholePicture.Zc w2 w4 - WholePicture.meanGrade w2 w4 ^ 2) := by
  have hZ' : WholePicture.Zc w2 w4 ≠ 0 := by rw [WholePicture.Zc_eq]; exact hZ
  rw [WholePicture.clockW]
  congr 1
  have expand : ∀ S ∈ WholePicture.fifteen,
      WholePicture.cw w2 w4 S * ((S.card : ℝ) - WholePicture.meanGrade w2 w4) ^ 2 =
        WholePicture.cw w2 w4 S * (S.card : ℝ) ^ 2 -
          2 * WholePicture.meanGrade w2 w4 * (WholePicture.cw w2 w4 S * S.card) +
            WholePicture.meanGrade w2 w4 ^ 2 * WholePicture.cw w2 w4 S := by
    intro S _
    ring
  rw [Finset.sum_congr rfl expand, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  have hmean : ∑ S ∈ WholePicture.fifteen, WholePicture.cw w2 w4 S * (S.card : ℝ) =
      WholePicture.meanGrade w2 w4 * WholePicture.Zc w2 w4 := by
    rw [WholePicture.meanGrade, div_mul_cancel₀ _ hZ']
  rw [hmean, show (∑ S ∈ WholePicture.fifteen, WholePicture.cw w2 w4 S) =
    WholePicture.Zc w2 w4 from rfl]
  field_simp
  ring

/-- `κ(u) = 2w⁴/(1 − 5w²)²` at `w = u/(1 + 4u²)` is `2u⁴/(1 + 3u² + 16u⁴)²`. -/
theorem kappa_u (u : ℂ) (h1 : 1 + 4 * u ^ 2 ≠ 0) (_h2 : 1 + 3 * u ^ 2 + 16 * u ^ 4 ≠ 0) :
    2 * (u / (1 + 4 * u ^ 2)) ^ 4 / (1 - 5 * (u / (1 + 4 * u ^ 2)) ^ 2) ^ 2 =
      2 * u ^ 4 / (1 + 3 * u ^ 2 + 16 * u ^ 4) ^ 2 := by
  have ha2 : (1 + 4 * u ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 h1
  have e : 1 - 5 * (u / (1 + 4 * u ^ 2)) ^ 2 =
      (1 + 3 * u ^ 2 + 16 * u ^ 4) / (1 + 4 * u ^ 2) ^ 2 := by
    rw [eq_div_iff ha2, div_pow, sub_mul, mul_assoc, div_mul_cancel₀ _ ha2]
    ring
  rw [e, div_pow, div_pow, ← pow_mul, mul_div_assoc', show (2 : ℕ) * 2 = 4 from rfl,
    div_div_div_cancel_right₀ (pow_ne_zero 4 h1)]

/-- **The series of `κ`:** `2u⁴/(1 + 3u² + 16u⁴)² = 2u⁴ − 12u⁶ − 10u⁸ + 360u¹⁰ + O(u¹²)`. -/
theorem kappa_series :
    (fun u : ℂ => 2 * u ^ 4 / (1 + 3 * u ^ 2 + 16 * u ^ 4) ^ 2 -
      (2 * u ^ 4 - 12 * u ^ 6 - 10 * u ^ 8 + 360 * u ^ 10)) =O[𝓝 0] fun u => u ^ 12 := by
  set D : ℂ → ℂ := fun u => 1 + 3 * u ^ 2 + 16 * u ^ 4 with hD
  have hDc : Continuous D := by fun_prop
  have hD0 : D 0 ≠ 0 := by simp [hD]
  have hev : ∀ᶠ u in 𝓝 (0 : ℂ), D u ≠ 0 := hDc.continuousAt.eventually_ne hD0
  set g : ℂ → ℂ := fun u =>
    (-1110 - 10728 * u ^ 2 - 32000 * u ^ 4 - 92160 * u ^ 6) / D u ^ 2 with hg
  have hgc : ContinuousAt g 0 :=
    ContinuousAt.div (by fun_prop) (hDc.continuousAt.pow 2) (pow_ne_zero 2 hD0)
  have hgO : g =O[𝓝 0] (fun _ => (1 : ℂ)) := hgc.tendsto.isBigO_one ℂ
  have h1 : (fun u : ℂ => u ^ 12 * g u) =O[𝓝 0] fun u => u ^ 12 * 1 :=
    (isBigO_refl (fun u : ℂ => u ^ 12) _).mul hgO
  simp only [mul_one] at h1
  refine h1.congr' ?_ EventuallyEq.rfl
  filter_upwards [hev] with u hu
  have hu2 : D u ^ 2 ≠ 0 := pow_ne_zero 2 hu
  have key : 2 * u ^ 4 - (2 * u ^ 4 - 12 * u ^ 6 - 10 * u ^ 8 + 360 * u ^ 10) * D u ^ 2 =
      u ^ 12 * (-1110 - 10728 * u ^ 2 - 32000 * u ^ 4 - 92160 * u ^ 6) := by
    simp only [hD]
    ring
  change u ^ 12 * g u = 2 * u ^ 4 / D u ^ 2 - (2 * u ^ 4 - 12 * u ^ 6 - 10 * u ^ 8 + 360 * u ^ 10)
  simp only [hg]
  rw [← mul_div_assoc, ← key, sub_div, mul_div_cancel_right₀ _ hu2]

/-- **The Dirac square in the chart.** For an orthonormal basis `b₀, …, b₃` of `𝟏^⊥ ⊂ ℝ⁵`, the four
`Γ^μ = γ(b_μ) = Σ_t v_t^μ γ_t` and `γ(m) = Σ_t γ_t/√5` satisfy `(Σ_μ p_μ Γ^μ + Mγ(m))² = p² + M²`.
-/
theorem chart_dirac (b : Fin 4 → Fin 5 → ℝ)
    (hb : ∀ μ ν, ∑ t, b μ t * b ν t = if μ = ν then 1 else 0) (h1 : ∀ μ, ∑ t, b μ t = 0)
    (p : Fin 4 → ℝ) (M : ℝ) :
    (∑ μ, (p μ : ℂ) • γv (b μ) + (M : ℂ) • γv (fun _ => 1 / Real.sqrt 5)) *
      (∑ μ, (p μ : ℂ) • γv (b μ) + (M : ℂ) • γv (fun _ => 1 / Real.sqrt 5)) =
      ((∑ μ, p μ ^ 2 + M ^ 2 : ℝ) : ℂ) • (1 : Matrix Four Four ℂ) := by
  set v : Fin 5 → ℝ := fun t => ∑ μ, p μ * b μ t + M * (1 / Real.sqrt 5) with hv
  have hγ : (∑ μ, (p μ : ℂ) • γv (b μ) + (M : ℂ) • γv (fun _ => 1 / Real.sqrt 5)) = γv v := by
    simp only [γv, hv, Finset.smul_sum, smul_smul, Complex.ofReal_add, Complex.ofReal_sum,
      Complex.ofReal_mul, add_smul, Finset.sum_add_distrib, Finset.sum_smul]
    rw [Finset.sum_comm]
  rw [hγ, γv_mul_self]
  congr 2
  have hc : (1 / Real.sqrt 5) ^ 2 = 1 / 5 := by
    rw [div_pow, one_pow, Real.sq_sqrt (by norm_num)]
  have hsq : ∀ t, v t ^ 2 = (∑ μ, p μ * b μ t) ^ 2 +
      2 * M * (1 / Real.sqrt 5) * (∑ μ, p μ * b μ t) + M ^ 2 * (1 / Real.sqrt 5) ^ 2 := by
    intro t
    simp only [hv]
    ring
  have hcross : ∑ t, ∑ μ, p μ * b μ t = 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, h1, mul_zero, Finset.sum_const_zero]
  have hsq2 : ∑ t, (∑ μ, p μ * b μ t) ^ 2 = ∑ μ, p μ ^ 2 := by
    have e : ∀ t, (∑ μ, p μ * b μ t) ^ 2 = ∑ μ, ∑ ν, p μ * p ν * (b μ t * b ν t) := by
      intro t
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun μ _ => Finset.sum_congr rfl fun ν _ => ?_
      ring
    simp only [e]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hb, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true]
    ring
  simp only [hsq, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, hcross, hsq2, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, hc]
  ring

/-! ### The motion of the critical zero under one marked arc -/

/-- The law as a function, `D(u) = det(I − uB)`. -/
noncomputable def lawD (u : ℂ) : ℂ := WholePicture.lawPoly.eval u

/-- Its derivative `D′(u)`. -/
noncomputable def lawD' (u : ℂ) : ℂ := (derivative WholePicture.lawPoly).eval u

theorem lawD_eq (u : ℂ) : lawD u = (1 - u ^ 2) ^ 24 * (1 - u) * (1 - 4 * u) *
    (1 - u + 4 * u ^ 2) ^ 10 * (1 + 3 * u + 4 * u ^ 2) ^ 5 := by
  rw [lawD, WholePicture.lawPoly_eval, WholePicture.Bc_eq, D_plus]

theorem lawD_quarter : lawD (1 / 4) = 0 := by
  rw [lawD_eq]
  norm_num

/-- The factors of the law beside `1 − 4u`. -/
noncomputable def lawRest (u : ℂ) : ℂ :=
  (1 - u ^ 2) ^ 24 * (1 - u) * (1 - u + 4 * u ^ 2) ^ 10 * (1 + 3 * u + 4 * u ^ 2) ^ 5

theorem lawD'_quarter : lawD' (1 / 4) = -4 * lawRest (1 / 4) := by
  have hR : DifferentiableAt ℂ lawRest (1 / 4) := by
    unfold lawRest
    fun_prop
  have h1 : HasDerivAt (fun u : ℂ => 1 - 4 * u) (-4) (1 / 4) := by
    simpa using ((hasDerivAt_id (1 / 4 : ℂ)).const_mul 4).const_sub 1
  have hprod := h1.mul hR.hasDerivAt
  have hfun : ((fun u : ℂ => 1 - 4 * u) * lawRest) = lawD := by
    funext u
    rw [Pi.mul_apply, lawD_eq, lawRest]
    ring
  rw [hfun] at hprod
  have h := (Polynomial.hasDerivAt WholePicture.lawPoly (1 / 4)).unique hprod
  rw [lawD', h]
  norm_num

theorem lawD'_quarter_ne : lawD' (1 / 4) ≠ 0 := by
  rw [lawD'_quarter, lawRest]
  norm_num

/-- **The phase of the marked arc that puts the zero of the marked law at `u`:**
`Z(u) = 1 − 320 D(u)/(uD′(u))`. -/
noncomputable def arcPhase (u : ℂ) : ℂ := 1 - 320 * lawD u / (u * lawD' u)

theorem arcPhase_quarter : arcPhase (1 / 4) = 1 := by
  rw [arcPhase, lawD_quarter, mul_zero, zero_div, sub_zero]

theorem hasStrictDerivAt_arcPhase : HasStrictDerivAt arcPhase (-1280) (1 / 4) := by
  have hD : HasStrictDerivAt lawD (lawD' (1 / 4)) (1 / 4) :=
    Polynomial.hasStrictDerivAt WholePicture.lawPoly (1 / 4 : ℂ)
  have hD' := Polynomial.hasStrictDerivAt (derivative WholePicture.lawPoly) (1 / 4 : ℂ)
  have hden := (hasStrictDerivAt_id (1 / 4 : ℂ)).mul hD'
  have hne : ((id : ℂ → ℂ) * fun x => (derivative WholePicture.lawPoly).eval x) (1 / 4) ≠ 0 :=
    mul_ne_zero (by norm_num) lawD'_quarter_ne
  have h := ((hD.const_mul 320).div hden hne).const_sub 1
  have e : arcPhase = fun x => 1 - ((fun y => 320 * lawD y) /
      ((id : ℂ → ℂ) * fun x => (derivative WholePicture.lawPoly).eval x)) x := by
    funext x
    rfl
  rw [e]
  convert h using 1
  have h0 : lawD (1 / 4) = 0 := lawD_quarter
  have hne' : lawD' (1 / 4) ≠ 0 := lawD'_quarter_ne
  simp only [Pi.mul_apply, id,
    show (derivative WholePicture.lawPoly).eval (1 / 4 : ℂ) = lawD' (1 / 4) from rfl,
    h0, mul_zero, zero_mul, sub_zero]
  field_simp
  ring

/-- **The critical zero moves with the phase of one marked arc:** there is a zero `u_c(z)` of the
marked law near `z = 1` with `u_c(1) = 1/4` and `u_c′(1) = −1/1280`. -/
theorem marked_zero : ∃ uc : ℂ → ℂ, uc 1 = 1 / 4 ∧ HasDerivAt uc (-1 / 1280) 1 ∧
    ∀ᶠ z in 𝓝 (1 : ℂ), lawD (uc z) + (z - 1) * uc z * lawD' (uc z) / 320 = 0 := by
  have hf := hasStrictDerivAt_arcPhase
  have hne : (-1280 : ℂ) ≠ 0 := by norm_num
  set g := hf.localInverse arcPhase (-1280) (1 / 4) hne with hg
  have hg1 : g 1 = 1 / 4 := by
    have h := HasStrictFDerivAt.localInverse_apply_image (hf.hasStrictFDerivAt_equiv hne)
    rw [arcPhase_quarter] at h
    exact h
  have hgd : HasStrictDerivAt g (-1280)⁻¹ 1 := by
    have h := hf.to_localInverse hne
    rw [arcPhase_quarter] at h
    exact h
  refine ⟨g, hg1, ?_, ?_⟩
  · have h := hgd.hasDerivAt
    convert h using 1
    norm_num
  · have hr := hf.eventually_right_inverse hne
    rw [arcPhase_quarter] at hr
    have hcont : ContinuousAt (fun z => g z * lawD' (g z)) 1 := by
      have hgc : ContinuousAt g 1 := hgd.hasDerivAt.continuousAt
      have hDc : Continuous lawD' := by
        unfold lawD'
        exact (derivative WholePicture.lawPoly).continuous
      exact hgc.mul (hDc.continuousAt.comp hgc)
    have hne1 : g 1 * lawD' (g 1) ≠ 0 := by
      rw [hg1]
      exact mul_ne_zero (by norm_num) lawD'_quarter_ne
    filter_upwards [hr, hcont.eventually_ne hne1] with z hz hw
    rw [arcPhase] at hz
    have h2 : 320 * lawD (g z) / (g z * lawD' (g z)) = 1 - z := by linear_combination -hz
    rw [div_eq_iff hw] at h2
    linear_combination h2 / 320

end S3

open S3

/-- **SI S3, statement 12: the mixed moment.** On the fifteen nonempty even two-spinor states `S`, with a
central weight `W_S = w₂` on the symmetric states and `w₄` on the complements of a line (`Z_W ≠ 0`),
`Z_W = Σ W_S`, `μ_W = Σ W_S|S|/Z_W`, `H_D(S) = (5|S∩D| − |D||S|)/4`,
`𝒥_DE = Σ W_S(|S| − μ_W)H_D(S)H_E(S)/Z_W` and `𝒞_W = (9/8)[Σ W_S|S|²/Z_W − μ_W²]`:
`𝒥_DE = 𝒞_W (rs − 5 Tr P_DP_E)/72` for every central weight and all `D, E`, with `r = |D|`,
`s = |E|`, `Tr P_DP_E = |D ∩ E|`; the same for every two subspaces; one pair of directions on opposite sides gives `1/72`
against `𝒞 = 1` at `u = 0` and `1/100` against `18/25` at the weights `1, 1/2` of `u = 1/4`; one
line
against four weighs `1/18 = −Φ(1)/(1 + Φ(1))`, a plane against its three outside lines
`1/12 = −Φ(i)/(1 + Φ(i))`. -/
theorem S3_12 :
    (∀ (D E : Finset (Fin 5)) (w2 w4 : ℝ), 10 * w2 + 5 * w4 ≠ 0 →
      WholePicture.mixedJ D E w2 w4 =
        WholePicture.clockW w2 w4 * ((D.card : ℝ) * E.card - 5 * (D ∩ E).card) / 72) ∧
    (∀ w2 w4 : ℝ, 10 * w2 + 5 * w4 ≠ 0 → WholePicture.clockW w2 w4 = 9 / 8 *
      ((∑ S ∈ WholePicture.fifteen, WholePicture.cw w2 w4 S * (S.card : ℝ) ^ 2) /
          WholePicture.Zc w2 w4 - WholePicture.meanGrade w2 w4 ^ 2)) ∧
    (∀ (P Q : Matrix (Fin 5) (Fin 5) ℂ) (r s : ℂ), Qᵀ = Q → P.trace = r → Q.trace = s →
      ∀ w₂ w₄ : ℂ, 10 * w₂ + 5 * w₄ ≠ 0 →
        WholePicture.wMoment w₂ w₄ (ArticleStatements.subTurn P r) (ArticleStatements.subTurn Q s) =
          WholePicture.wClock w₂ w₄ * (r * s - 5 * (P * Q).trace) / 72) ∧
    WholePicture.clockW 1 1 = 1 ∧
    (WholePicture.mixedJ {0} {1} 1 1 = 1 / 72 ∧ WholePicture.clockW 1 (1 / 2) = 18 / 25 ∧
      WholePicture.mixedJ {0} {1} 1 (1 / 2) = 1 / 100) ∧
    (∀ P : Matrix (Fin 5) (Fin 5) ℂ, Pᵀ = P → P * P = P → P.trace = 1 →
      ArticleStatements.kappa (ArticleStatements.subTurn P 1) (ArticleStatements.subTurn (1 - P) (5 - 1)) = 1 / 18 ∧
        (1 / 18 : ℝ) = -(∑' n, signedLaw n) / (1 + ∑' n, signedLaw n)) ∧
    (∀ P : Matrix (Fin 5) (Fin 5) ℂ, Pᵀ = P → P * P = P → P.trace = 2 →
      ArticleStatements.kappa (ArticleStatements.subTurn P 2) (ArticleStatements.subTurn (1 - P) (5 - 2)) = 1 / 12 ∧
        (1 / 12 : ℂ) =
          -(∑' n, (signedLaw n : ℂ) * I ^ n) / (1 + ∑' n, (signedLaw n : ℂ) * I ^ n)) :=
  ⟨WholePicture.mixed_moment_central, clockW_eq,
    fun P Q r s hQ hPr hQs w₂ w₄ hZ =>
      WholePicture.mixed_moment_central_subspaces P Q r s hQ hPr hQs w₂ w₄ hZ,
    WholePicture.clock_uniform, WholePicture.crossing_pair_quarter,
    ArticleStatements.kappa_one_against_four, ArticleStatements.kappa_plane_against_colour⟩

/-- **SI S3, statement 13: one marked arc.** With `D(u) = det(I − uB)` and `B_z` the step with one
of its 320 arcs marked by the phase `z` (`z = e^{−iθ}`), at every arc
`det(I − uB_z) = D(u) + (z − 1) u D′(u)/320`; every arc has the same cofactor; at the critical step
`D(1/4) = 0` and `D′(1/4) = −96(15/16)²⁴ ≠ 0`; and the critical zero moves with the phase:
there is a zero `u_c(z)` of the marked law for `z` near 1, `u_c(1) = 1/4`, `u_c′(1) = −1/1280`, so
`d/dθ [4u_c(e^{−iθ})] = i/320` at `θ = 0`: the marked line turns the critical zero by `θ/320`.
Recognition: the least closed count, the electron. -/
theorem S3_13 :
    arcs.card = 320 ∧
    (∀ (p q : State), Continues q p → ∀ z u : ℂ,
      (1 - u • WholePicture.Bmark p q z).det =
        WholePicture.lawPoly.eval u +
          (z - 1) * u * (derivative WholePicture.lawPoly).eval u / 320) ∧
    (∀ (p q : State), Continues q p → ∀ θ u : ℂ,
      (1 - u • WholePicture.Bmark p q (Complex.exp (-Complex.I * θ))).det =
        WholePicture.lawPoly.eval u +
          (Complex.exp (-Complex.I * θ) - 1) * u * (derivative WholePicture.lawPoly).eval u / 320) ∧
    (∀ (u : ℂ) (y : Fin 16) (t s : Fin 5), t ≠ s →
      (1 - u • WholePicture.Bc).adjugate (y, t) (transition s y, s) =
        (1 - u • WholePicture.Bc).adjugate (0, 0) (transition 1 0, 1)) ∧
    (∀ u : ℂ, WholePicture.lawPoly.eval u = law u) ∧
    law (1 / 4) = 0 ∧
    HasDerivAt (fun u : ℝ => (1 - u • stepR).det) (-96 * (15 / 16 : ℝ) ^ 24) (1 / 4) ∧
    (-96 * (15 / 16 : ℝ) ^ 24) ≠ 0 ∧
    (∃ uc : ℂ → ℂ, uc 1 = 1 / 4 ∧ HasDerivAt uc (-1 / 1280) 1 ∧
      (∀ᶠ z in 𝓝 (1 : ℂ), ∀ p q : State, Continues q p →
        (1 - uc z • WholePicture.Bmark p q z).det = 0) ∧
      HasDerivAt (fun θ : ℂ => 4 * uc (Complex.exp (-Complex.I * θ))) (Complex.I / 320) 0) := by
  refine ⟨card_arcs, WholePicture.one_arc, WholePicture.one_arc_phase,
    fun u y t s hts => WholePicture.arc_cofactor_const u y t s hts, lawPoly_eval_eq, ?_,
    law_deriv_quarter, by norm_num, ?_⟩
  · rw [law_eq_D_plus]
    exact D_plus_quarter.1
  · obtain ⟨uc, h1, hd, hz⟩ := marked_zero
    refine ⟨uc, h1, hd, ?_, ?_⟩
    · filter_upwards [hz] with z hz p q harc
      rw [WholePicture.one_arc p q harc z (uc z)]
      exact hz
    · have hexp : HasDerivAt (fun θ : ℂ => Complex.exp (-Complex.I * θ)) (-Complex.I) 0 := by
        have h := ((hasDerivAt_id (0 : ℂ)).const_mul (-Complex.I)).cexp
        simpa using h
      have hd' : HasDerivAt uc (-1 / 1280) (Complex.exp (-Complex.I * 0)) := by
        simpa using hd
      have h := (hd'.comp (0 : ℂ) hexp).const_mul 4
      exact h.congr_deriv (by ring)

/-- **SI S3, statement 14: the step weights of the 64 divided sets, and the counts at the four points `u = i^d/4`.**
For a divided set `S` of the six directions with `k_S` lines, `P = z_S² = (−1)^{|S|}` and
`L_S = 5 − k_S + k_S P`: the transmission and the reflection are the grade factors at the point `u = −1/4`,
`t_S = 2/|L_S| = 1/k_N(−¼)`, `e_S = 1 − 2/|L_S| = k_{N+2}(−¼)/k_N(−¼)`, `N = 5 − |L_S|`, with
`k₀, k₂, k₄ = 5/2, 3/2, 1/2` at `−¼`; `−1/(16 + 3P)` is `Φ(1)` at `P = 1` and `Φ(i)` at `P = −1`;
the 64 divided sets are 32 even (`e = 3/5`, `Ψ = 1/28`), two (`{n}` and the five directions: `3/5`, `−1/22`),
ten (`1/3`, `−1/6`) and twenty (`−1`, `1/2`); `g² = [−Φ(1)/(1 + Φ(1))]/4 = [−Φ(i)/(1 + Φ(i))]/6 =
e_line²/(k_C² − 1) = 1/72`; `a = 5/38`, `χ_A = 13/12`, `w_h = 3/13`, `χ_h = 30/169`. -/
theorem S3_14 :
    (∀ S : Finset (Fin 6), Law.tS S = 1 / WholePicture.kR (WholePicture.gradeS S) (-1 / 4) ∧
      Law.eS S = WholePicture.kR (WholePicture.gradeS S + 2) (-1 / 4) /
        WholePicture.kR (WholePicture.gradeS S) (-1 / 4)) ∧
    (WholePicture.kR 0 (-1 / 4) = 5 / 2 ∧ WholePicture.kR 2 (-1 / 4) = 3 / 2 ∧
      WholePicture.kR 4 (-1 / 4) = 1 / 2) ∧
    (-1 / (16 + 3 * 1) = Law.Phi 1 ∧ -1 / (16 + 3 * (-1)) = Law.Phi I) ∧
    (Finset.univ.filter fun S : Finset (Fin 6) => Law.signS S = 1).card = 32 ∧
    (Finset.univ.filter fun S : Finset (Fin 6) => Law.signS S = -1 ∧ |Law.LZ S| = 5) =
      {{0}, {1, 2, 3, 4, 5}} ∧
    (Finset.univ.filter fun S : Finset (Fin 6) => Law.signS S = -1 ∧ |Law.LZ S| = 3).card = 10 ∧
    (Finset.univ.filter fun S : Finset (Fin 6) => Law.signS S = -1 ∧ |Law.LZ S| = 1).card = 20 ∧
    (∀ S : Finset (Fin 6),
      (Law.signS S = 1 → Law.eS S = 3 / 5 ∧ Law.PsiS S = 1 / 28 ∧ Law.PhiS S = -1 / 19) ∧
      (Law.signS S = -1 → |Law.LZ S| = 5 →
        Law.eS S = 3 / 5 ∧ Law.PsiS S = -1 / 22 ∧ Law.PhiS S = -1 / 13) ∧
      (Law.signS S = -1 → |Law.LZ S| = 3 →
        Law.eS S = 1 / 3 ∧ Law.PsiS S = -1 / 6 ∧ Law.PhiS S = -1 / 13) ∧
      (Law.signS S = -1 → |Law.LZ S| = 1 →
        Law.eS S = -1 ∧ Law.PsiS S = 1 / 2 ∧ Law.PhiS S = -1 / 13)) ∧
    ((-(Law.Phi 1) / (1 + Law.Phi 1)) / 4 = 1 / 72 ∧
      (-(Law.Phi I) / (1 + Law.Phi I)) / 6 = 1 / 72 ∧
      (WholePicture.kR 4 (-1 / 4) / WholePicture.kR 2 (-1 / 4)) ^ 2 /
        ((1 / |(-1 / 4 : ℝ)| - 1) ^ 2 - 1) = 1 / 72) ∧
    ((1 - Law.Phi 1) / 8 = 5 / 38 ∧ 1 / (1 + Law.Phi I) = 13 / 12 ∧
      1 / (4 * (1 / (1 + Law.Phi I))) = 3 / 13 ∧
      (1 / (4 * (1 / (1 + Law.Phi I)))) * (1 - 1 / (4 * (1 / (1 + Law.Phi I)))) = 30 / 169) := by
  refine ⟨WholePicture.step_weights_are_grade_factors, WholePicture.grade_factors_plane_quarter,
    ⟨?_, ?_⟩, RuleAndLaw.card_class_even, RuleAndLaw.class_five_members, RuleAndLaw.card_class_three,
    RuleAndLaw.card_class_one, RuleAndLaw.rule_values_classes, WholePicture.one_crossing_pair,
    WholePicture.rule_constants⟩
  · simp only [Law.Phi]
    norm_num
  · norm_num [Law.Phi, I_pow_four, I_sq]

/-- **SI S3, statement 15: the field equations.** (a) At `u = 1/4 − ε²m²/24` the law's operator in
the chart is `(ε²/8)(m² − Δ) + O(ε³)` for every `C³` field, with `Δ = Σ_t (v_t·∇)²`, which is the
Laplacian of `𝟏^⊥ = ℝ⁴` in every orthonormal basis. (b) The step `U = e^{−ikγ_j}e^{−iμγ_h}` (the
exponentials themselves) has `U + U† = 2 cos k cos μ` for `j ≠ h`; for every orthonormal basis `b_μ`
of `𝟏^⊥`, `Γ^μ = γ(b_μ)` and `γ(m) = Σ_tγ_t/√5` are five anticommuting directions and
`(Γ·p + Mγ(m))² = p² + M²`. (c) The second variation of the signed law in the forty link phases is
`−κ(w)CᵀC`, `κ(w) = 2w⁴/(1 − 5w²)²`: as the Hessian `H(w) = −κ(w)CᵀC`, and along every direction `θ`
as the derivative of the law itself, `(log det)′(0) = 0`, `(log det)″(0) = −κ(w)‖Cθ‖²`; `κ = 1/200`
at
`w = ±1/5`, `1/98` at `w = ±i/3`. (d) `tr(γ_hγ_aγ_bγ_cγ_d) = 4ε_{habcd} γ₁⋯γ₅`. (e) The four rotations
that
move the last-step direction close into the six that keep it: `[γ_hγ_a, γ_hγ_b] = −2γ_aγ_b`. (f) With
`𝓕 = R − e∧e/ℓ²`, `tr(γ_h𝓕∧𝓕) − tr(γ_hR∧R) = −(4/ℓ²)(R − 6/ℓ²)`, and `24/ℓ⁴ = (4/ℓ²)·2Λ` exactly
when `Λ = 3/ℓ²`. (g) The law's own transformation `K(v) = (v/u)K(u) + c₀I`,
`c₀ = 1 + 4v² − (v/u)(1 + 4u²)`; `κ(u) = 2u⁴/(1 + 3u² + 16u⁴)² = 2u⁴ − 12u⁶ − 10u⁸ + 360u¹⁰ +
O(u¹²)`. -/
theorem S3_15 :
    (∀ (ψ : (Fin 5 → ℝ) → ℝ), ContDiff ℝ 3 ψ → ∀ (x : Fin 5 → ℝ) (m : ℝ),
      (fun ε : ℝ => (1 + 4 * (1 / 4 - ε ^ 2 * m ^ 2 / 24) ^ 2) * ψ x -
        (1 / 4 - ε ^ 2 * m ^ 2 / 24) * ∑ t, ψ (x + ε • vR t) -
        ε ^ 2 / 8 * (m ^ 2 * ψ x - stepLaplacian ψ x)) =O[𝓝 0] (fun ε : ℝ => ε ^ 3)) ∧
    (∀ (ψ : (Fin 5 → ℝ) → ℝ), ContDiff ℝ 2 ψ → ∀ (x : Fin 5 → ℝ) (f : Fin 4 → Fin 5 → ℝ),
      (∀ i j, f i ⬝ᵥ f j = if i = j then 1 else 0) → (∀ i, ∑ a, f i a = 0) →
      stepLaplacian ψ x = ∑ i, fderiv ℝ (fderiv ℝ ψ) x (f i) (f i)) ∧
    (∀ (k μ : ℝ) (j h : Fin 5),
      stepMotion k μ j h = NormedSpace.exp (((-k : ℝ) : ℂ) • (I • γ j)) *
        NormedSpace.exp (((-μ : ℝ) : ℂ) • (I • γ h))) ∧
    (∀ (k μ : ℝ) (j h : Fin 5), j ≠ h →
      stepMotion k μ j h + (stepMotion k μ j h)ᴴ =
        ((2 * Real.cos k * Real.cos μ : ℝ) : ℂ) • (1 : Matrix Four Four ℂ)) ∧
    (∀ (b : Fin 4 → Fin 5 → ℝ), (∀ μ ν, ∑ t, b μ t * b ν t = if μ = ν then 1 else 0) →
      (∀ μ, ∑ t, b μ t = 0) →
      (∀ μ ν, γv (b μ) * γv (b ν) + γv (b ν) * γv (b μ) =
        ((if μ = ν then 2 else 0 : ℝ) : ℂ) • (1 : Matrix Four Four ℂ)) ∧
      (∀ μ, γv (b μ) * γv (fun _ => 1 / Real.sqrt 5) +
        γv (fun _ => 1 / Real.sqrt 5) * γv (b μ) = 0) ∧
      γv (fun _ => 1 / Real.sqrt 5) * γv (fun _ => 1 / Real.sqrt 5) = 1 ∧
      ∀ (p : Fin 4 → ℝ) (M : ℝ),
        (∑ μ, (p μ : ℂ) • γv (b μ) + (M : ℂ) • γv (fun _ => 1 / Real.sqrt 5)) *
          (∑ μ, (p μ : ℂ) • γv (b μ) + (M : ℂ) • γv (fun _ => 1 / Real.sqrt 5)) =
          ((∑ μ, p μ ^ 2 + M ^ 2 : ℝ) : ℂ) • (1 : Matrix Four Four ℂ)) ∧
    (∀ (w : ℂ), 1 - 5 * w ^ 2 ≠ 0 → ∀ j k : Fin 40,
      WholePicture.hessLaw w j k = -(2 * w ^ 4 / (1 - 5 * w ^ 2) ^ 2) * (GZ j k : ℂ)) ∧
    (∀ (w : ℂ), 1 - 5 * w ^ 2 ≠ 0 → ∀ θ : Fin 40 → ℝ,
      Law.logDer w θ 0 = 0 ∧
      HasDerivAt (Law.logDer w θ) (-(2 * w ^ 4 / (1 - 5 * w ^ 2) ^ 2) * (plaqSq θ : ℂ)) 0) ∧
    (2 * (1 / 5 : ℂ) ^ 4 / (1 - 5 * (1 / 5) ^ 2) ^ 2 = 1 / 200 ∧
      2 * (-1 / 5 : ℂ) ^ 4 / (1 - 5 * (-1 / 5) ^ 2) ^ 2 = 1 / 200 ∧
      2 * (I / 3) ^ 4 / (1 - 5 * (I / 3) ^ 2) ^ 2 = 1 / 98 ∧
      2 * (-I / 3) ^ 4 / (1 - 5 * (-I / 3) ^ 2) ^ 2 = 1 / 98) ∧
    (∀ h a b c d : Fin 5, (γ h * γ a * γ b * γ c * γ d).trace • (1 : Matrix Four Four ℂ) =
      (4 * (lc5 h a b c d : ℂ)) • (γ 0 * γ 1 * γ 2 * γ 3 * γ 4)) ∧
    (∀ h a b : Fin 5, a ≠ h → b ≠ h → a ≠ b →
      (γ h * γ a) * (γ h * γ b) - (γ h * γ b) * (γ h * γ a) = (-2 : ℂ) • (γ a * γ b)) ∧
    (∀ (R : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ), (∀ a b e f, R a b f e = -R a b e f) → ∀ ℓ : ℝ,
      WholePicture.wedge (fun p q => WholePicture.onPairs R p q - WholePicture.frameP p q / ℓ ^ 2)
          (fun p q => WholePicture.onPairs R p q - WholePicture.frameP p q / ℓ ^ 2) -
        WholePicture.wedge (WholePicture.onPairs R) (WholePicture.onPairs R) =
          -(4 / ℓ ^ 2) * (WholePicture.scalarR R - 6 / ℓ ^ 2)) ∧
    (∀ ℓ : ℝ, ℓ ≠ 0 → ∀ Λ : ℝ, (24 / ℓ ^ 4 = (4 / ℓ ^ 2) * (2 * Λ)) ↔ Λ = 3 / ℓ ^ 2) ∧
    (∀ {n : Type} [DecidableEq n] (A : Matrix n n ℂ) (u v : ℂ), u ≠ 0 →
      (1 + 4 * v ^ 2) • (1 : Matrix n n ℂ) - v • A =
        (v / u) • ((1 + 4 * u ^ 2) • (1 : Matrix n n ℂ) - u • A) +
          (1 + 4 * v ^ 2 - v / u * (1 + 4 * u ^ 2)) • (1 : Matrix n n ℂ)) ∧
    (∀ u : ℂ, 1 + 4 * u ^ 2 ≠ 0 → 1 + 3 * u ^ 2 + 16 * u ^ 4 ≠ 0 →
      2 * (u / (1 + 4 * u ^ 2)) ^ 4 / (1 - 5 * (u / (1 + 4 * u ^ 2)) ^ 2) ^ 2 =
        2 * u ^ 4 / (1 + 3 * u ^ 2 + 16 * u ^ 4) ^ 2) ∧
    (fun u : ℂ => 2 * u ^ 4 / (1 + 3 * u ^ 2 + 16 * u ^ 4) ^ 2 -
      (2 * u ^ 4 - 12 * u ^ 6 - 10 * u ^ 8 + 360 * u ^ 10)) =O[𝓝 0] fun u => u ^ 12 := by
  refine ⟨critical_operator,
    fun ψ hψ x f hon hperp => Law.stepLaplacian_eq_frame ψ hψ x f hon hperp,
    fun k μ j h => ?_, fun k μ j h hjh => stepMotion_add_adjoint k μ hjh,
    fun b hb h1 => ⟨fun μ ν => ?_, fun μ => ?_, ?_, chart_dirac b hb h1⟩,
    WholePicture.hessLaw_eq,
    fun w hw θ => ⟨(Law.law_small_phases w hw θ).2.2.1, (Law.law_small_phases w hw θ).2.2.2.1⟩,
    ?_, WholePicture.trace_five_volume,
    fun h a b ha hb hab => lastDirection_commutator ha hb hab, WholePicture.curvature_identity,
    WholePicture.lambda_three, fun A u v hu => WholePicture.law_transformation A u v hu,
    kappa_u, kappa_series⟩
  · rw [stepMotion, (Geometry.exp_line_on_singlet (-k) j).1, (Geometry.exp_line_on_singlet (-μ) h).1,
      expIγ, expIγ]
    congr 1 <;> simp only [smul_smul, mul_comm]
  · rw [anticomm_γv, hb]
    split_ifs <;> simp
  · rw [anticomm_γv]
    have : ∑ s, b μ s * (1 / Real.sqrt 5) = 0 := by rw [← Finset.sum_mul, h1, zero_mul]
    rw [this]
    simp
  · rw [γv_mul_self]
    have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    simp only [div_pow, one_pow, h5, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    norm_num
  · obtain ⟨-, -, -, -, k1, k2, k3, k4⟩ := WholePicture.kappa_quarters
    exact ⟨k1, k2, k3, k4⟩

/-- **SI S3, statement 16: the closed forms of the constants.** (i) `α_s² = e_line²/(k_C² − 1) =
1/72`
with `e_line = k₄(−¼)/k₂(−¼)` and `k_C = 1/|u| − 1 = 3` at `u = −¼`. (ii) For every last-step direction `h` and
every other line `j`: the plane `{h, j}` leaves `k_C = 3` lines; the mean excursion is `Eℓ = 16`; the
steps along the last-step direction per excursion are `E_H = Eℓ C_h/320 = 3`; `η = 5C_j/M = 295/296`; and
`W = k₀(−¼)^{−k_CEℓ} η^{k_CE_H} = (2/5)⁴⁸(295/296)⁹`. (iii) The pole
`6M + C_h + (1/6)log k₀(−¼) − a⁵ − ba⁶`, with `M = Σ_j C_j = 296`, `C_h = 60`,
`a = (F(1) − Φ(1))/8 = 5/38`, `b = Var P/(2(Var P + Var Q)) = 7/16`, lies in
`(1836.152673412, 1836.1526734121)`; pole of the law objects (the transitions,
`log E_U / L(Ω)` with `L(Ω) = ⟨Ω, LΩ⟩ = 6` and `E_U = 5/2`, the signed-volume terms) is this number.
Recognition: `α_s`, the gravitational coupling `W`, `m_p/m_e`. -/
theorem S3_16 :
    (WholePicture.kR 4 (-1 / 4) / (WholePicture.kR 2 (-1 / 4) *
        Real.sqrt ((1 / |(-1 / 4 : ℝ)| - 1) ^ 2 - 1))) ^ 2 = 1 / 72 ∧
    (1 / |(-1 / 4 : ℝ)| - 1 = 3) ∧
    (∀ h j : Fin 5, j ≠ h →
      ((Finset.univ : Finset (Fin 5)) \ {h, j}).card = 3 ∧
      HasSum (fun n : ℕ => (n : ℝ) * excursionLaw n) 16 ∧
      (16 * (alongCount h h : ℝ)) / 320 = 3 ∧
      (5 * (alongCount h j : ℝ)) / (∑ i, (alongCount h i : ℝ)) = 295 / 296 ∧
      WholePicture.kR 0 (-1 / 4) ^ (-((3 : ℤ) * 16)) *
          ((5 * (alongCount h j : ℝ)) / (∑ i, (alongCount h i : ℝ))) ^ (3 * 3) =
        (2 / 5) ^ 48 * (295 / 296) ^ 9 ∧
      ((Wgrav : ℚ) : ℝ) = (2 / 5) ^ 48 * (295 / 296) ^ 9) ∧
    (∀ h : Fin 5,
      protonPole = 6 * (∑ i, (alongCount h i : ℝ)) + (alongCount h h : ℝ) +
        (1 / 6) * Real.log (WholePicture.kR 0 (-1 / 4)) -
        (((∑' n, excursionLaw n) - (∑' n, signedLaw n)) / 8) ^ 5 -
        ((deriv (deriv (fun y => excursionF 1 1 y)) 1 + deriv (fun y => excursionF 1 1 y) 1 -
            (deriv (fun y => excursionF 1 1 y) 1) ^ 2) /
          (2 * ((deriv (deriv (fun y => excursionF 1 1 y)) 1 + deriv (fun y => excursionF 1 1 y) 1 -
            (deriv (fun y => excursionF 1 1 y) 1) ^ 2) +
            (deriv (deriv (fun x => excursionF 1 x 1)) 1 + deriv (fun x => excursionF 1 x 1) 1 -
              (deriv (fun x => excursionF 1 x 1) 1) ^ 2)))) *
          (((∑' n, excursionLaw n) - (∑' n, signedLaw n)) / 8) ^ 6) ∧
    (Completion.Num.LOmega = 6 ∧ Completion.Num.EU = 5 / 2 ∧
      Completion.Num.protonPole =
        6 * 296 + 60 + (1 / 6) * Real.log (5 / 2) - (5 / 38) ^ 5 - (7 / 16) * (5 / 38) ^ 6 ∧
      Completion.Num.protonPole = protonPole) ∧
    ((1836.152673412 : ℝ) < protonPole ∧ protonPole < 1836.1526734121) := by
  obtain ⟨vP, vQ, -, -, -⟩ := visit_moments
  obtain ⟨ha, -, -⟩ := a_value
  have hk0 : WholePicture.kR 0 (-1 / 4) = 5 / 2 := WholePicture.grade_factors_plane_quarter.1
  have hcard : ∀ h j : Fin 5, j ≠ h → ((Finset.univ : Finset (Fin 5)) \ {h, j}).card = 3 := by
    decide
  refine ⟨WholePicture.alphaS_sq, by norm_num [abs_of_neg], fun h j hj => ?_, fun h => ?_,
    ⟨Completion.Num.LOmega_eq, Completion.Num.EU_eq, Completion.Num.protonPole_closed,
      by rw [Completion.Num.protonPole_closed, protonPole]⟩, protonPole_bounds⟩
  · have hM : (∑ i, (alongCount h i : ℝ)) = 296 := by exact_mod_cast availableTransitions_total h
    have hh : (alongCount h h : ℝ) = 60 := by exact_mod_cast (availableTransitions_along h).1
    have hjj : (alongCount h j : ℝ) = 59 := by exact_mod_cast (availableTransitions_along h).2 j hj
    refine ⟨hcard h j hj, excursion_mean, by rw [hh]; norm_num, by rw [hjj, hM]; norm_num, ?_,
      (WholePicture.gravity_grade_form).2⟩
    rw [hjj, hM, show (5 * 59 / 296 : ℝ) = 295 / 296 by norm_num]
    exact (WholePicture.gravity_grade_form).1
  · have hM : (∑ i, (alongCount h i : ℝ)) = 296 := by exact_mod_cast availableTransitions_total h
    have hh : (alongCount h h : ℝ) = 60 := by exact_mod_cast (availableTransitions_along h).1
    rw [hM, hh, vP, vQ, ha, hk0, protonPole]
    norm_num

/-- **SI S3, statement 17: the long-range zero under a circulation.** For phases `θ` on the forty
links: the largest value `λ_max(A_θ)` of the phased adjacency is an eigenvalue and bounds every
eigenvalue; no gauge transformation moves it and it depends only on the cyclic part `θ_cyc`; and for
`‖θ_cyc‖² ≤ 1/100`: `|λ_max(A_θ) − (5 − ‖θ_cyc‖²/16)| ≤ ‖θ_cyc‖⁴/10`, the long-range zero
`u_c = (λ_max − √(λ_max² − 16))/8` satisfies `1 + 4u_c² = u_c λ_max(A_θ)`, and
`|log 4u_c − ‖θ_cyc‖²/48| ≤ ‖θ_cyc‖⁴/20`: `log 4u_c = ‖θ_cyc‖²/48 + O(θ⁴)`. -/
theorem S3_17 :
    (∀ θ : Fin 40 → ℝ, Module.End.HasEigenvalue (Matrix.toEuclideanLin (WholePicture.magAdj θ))
      (WholePicture.lamMax θ : ℂ)) ∧
    (∀ (θ : Fin 40 → ℝ) (μ : ℂ) (v : Fin 16 → ℂ), v ≠ 0 → WholePicture.magAdj θ *ᵥ v = μ • v →
      μ.re ≤ WholePicture.lamMax θ) ∧
    (∀ (θ : Fin 40 → ℝ) (φ : Fin 16 → ℝ),
      WholePicture.lamMax (θ + WholePicture.gradR φ) = WholePicture.lamMax θ) ∧
    (∀ θ : Fin 40 → ℝ, WholePicture.lamMax θ = WholePicture.lamMax (WholePicture.thetaCyc θ)) ∧
    (∀ θ : Fin 40 → ℝ, WholePicture.sqL (WholePicture.thetaCyc θ) ≤ 1 / 100 →
      |WholePicture.lamMax θ - (5 - WholePicture.sqL (WholePicture.thetaCyc θ) / 16)| ≤
          WholePicture.sqL (WholePicture.thetaCyc θ) ^ 2 / 10 ∧
        1 + 4 * WholePicture.ucrit θ ^ 2 = WholePicture.ucrit θ * WholePicture.lamMax θ ∧
        |Real.log (4 * WholePicture.ucrit θ) - WholePicture.sqL (WholePicture.thetaCyc θ) / 48| ≤
          WholePicture.sqL (WholePicture.thetaCyc θ) ^ 2 / 20) :=
  ⟨WholePicture.lamMax_hasEigenvalue, WholePicture.eigen_le_lamMax, WholePicture.lamMax_gauge,
    WholePicture.lamMax_cyc, WholePicture.long_range_zero⟩

end Comparison.System
