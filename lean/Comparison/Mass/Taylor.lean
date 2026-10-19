module

public import Comparison.Existence.Motion

/-!
# The road to the masses: the Taylor steps of Propositions 59 and 60

**Proposition 59, the law near its critical step.** In the chart `ℝ⁵` (the five steps less their
mean, `v_t = e_t − 𝟏/5`, `Σ_t v_t = 0`), for `ψ ∈ C³`:
* `step_first_order`: the first-order terms cancel, `Σ_t Dψ(x) v_t = 0`;
* `taylor_step`: **`Σ_t ψ(x + εv_t) = 5ψ(x) + (ε²/2) Δψ(x) + O(ε³)`**, with
  `Δψ(x) = Σ_t (d/dε)² ψ(x + εv_t)|₀` the Laplacian along the five steps;
* `critical_operator`: **at `u = 1/4 − ε²m²/24`, `(1 + 4u²)ψ(x) − u Σ_t ψ(x + εv_t) =
  (ε²/8)(m²ψ(x) − Δψ(x)) + O(ε³)`**: the distance below the critical step is the mass squared.

**Proposition 60, one step in motion.**
* `cos_six`: `cos x = 1 − x²/2 + x⁴/24 + O(x⁶)` with the bound `|x|⁶·7/4320` for `|x| ≤ 1`;
* `dispersion_series`: for `|μ|, |k| ≤ 1/2`, the eigenphase `ω = arccos(cos μ cos k)` satisfies
  **`|ω² − (μ² + k² − μ²k²/3)| ≤ 3(μ² + k²)³`**: `ω² = μ² + k² − μ²k²/3 + O((|μ| + |k|)⁶)`.
-/

@[expose] public section

namespace Comparison

open Filter Topology Asymptotics

/-! ## Proposition 59 -/

/-- The five steps less their mean, as vectors of the chart `ℝ⁵`. -/
noncomputable def vR (t : Fin 5) : Fin 5 → ℝ := fun s => (if s = t then 1 else 0) - 1 / 5

theorem vR_sum : ∑ t, vR t = 0 := by
  funext s
  simp only [vR, Finset.sum_apply, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ,
    ↓reduceIte, Finset.sum_const, Finset.card_univ, Fintype.card_fin, Pi.zero_apply,
    nsmul_eq_mul]
  norm_num

/-- The second derivative of `ψ` along the step `v_t` at `x`. -/
noncomputable def stepSecond (ψ : (Fin 5 → ℝ) → ℝ) (x : Fin 5 → ℝ) (t : Fin 5) : ℝ :=
  iteratedDeriv 2 (fun e : ℝ => ψ (x + e • vR t)) 0

/-- **The Laplacian along the five steps**, `Δψ(x) = Σ_t (v_t·∇)²ψ(x)`. -/
noncomputable def stepLaplacian (ψ : (Fin 5 → ℝ) → ℝ) (x : Fin 5 → ℝ) : ℝ :=
  ∑ t, stepSecond ψ x t

theorem line_hasDerivAt (x v : Fin 5 → ℝ) (e : ℝ) :
    HasDerivAt (fun e : ℝ => x + e • v) v e := by
  simpa using ((hasDerivAt_id e).smul_const v).const_add x

/-- **The first-order terms cancel:** `Σ_t Dψ(x)v_t = 0`. -/
theorem step_first_order (ψ : (Fin 5 → ℝ) → ℝ) (hψ : ContDiff ℝ 3 ψ) (x : Fin 5 → ℝ) :
    ∑ t, deriv (fun e : ℝ => ψ (x + e • vR t)) 0 = 0 := by
  have hd : Differentiable ℝ ψ := hψ.differentiable (by norm_num)
  have e1 : ∀ t, deriv (fun e : ℝ => ψ (x + e • vR t)) 0 = fderiv ℝ ψ x (vR t) := by
    intro t
    have h := (hd (x + (0 : ℝ) • vR t)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (line_hasDerivAt x (vR t) 0)
    simp only [zero_smul, add_zero] at h
    exact h.deriv
  simp only [e1]
  rw [← map_sum, vR_sum, map_zero]

theorem line_contDiff (ψ : (Fin 5 → ℝ) → ℝ) (hψ : ContDiff ℝ 3 ψ) (x v : Fin 5 → ℝ) :
    ContDiff ℝ 3 (fun e : ℝ => ψ (x + e • v)) :=
  hψ.comp (contDiff_const.add (contDiff_id.smul contDiff_const))

/-- Taylor along one line: `g(ε) − (g(0) + εg'(0) + (ε²/2)g''(0)) = O(ε³)`. -/
theorem line_taylor (g : ℝ → ℝ) (hg : ContDiff ℝ 3 g) :
    (fun ε : ℝ => g ε - (g 0 + ε * deriv g 0 + ε ^ 2 / 2 * iteratedDeriv 2 g 0)) =O[𝓝 0]
      (fun ε : ℝ => ε ^ 3) := by
  have ho := taylor_isLittleO_univ (x₀ := (0 : ℝ)) hg
  have e : ∀ ε : ℝ, taylorWithinEval g 3 Set.univ 0 ε =
      g 0 + ε * deriv g 0 + ε ^ 2 / 2 * iteratedDeriv 2 g 0 + ε ^ 3 / 6 * iteratedDeriv 3 g 0 := by
    intro ε
    rw [taylor_within_apply]
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
      iteratedDerivWithin_univ, iteratedDeriv_zero, iteratedDeriv_one, sub_zero, smul_eq_mul,
      Nat.factorial]
    push_cast
    ring
  have h1 : (fun ε : ℝ => g ε - taylorWithinEval g 3 Set.univ 0 ε) =O[𝓝 0] (fun ε : ℝ => ε ^ 3) := by
    simpa using ho.isBigO
  have h2 : (fun ε : ℝ => ε ^ 3 / 6 * iteratedDeriv 3 g 0) =O[𝓝 0] (fun ε : ℝ => ε ^ 3) := by
    have := (Asymptotics.isBigO_refl (fun ε : ℝ => ε ^ 3) (𝓝 0)).const_mul_left
      (iteratedDeriv 3 g 0 / 6)
    refine this.congr' (Filter.Eventually.of_forall fun ε => ?_) EventuallyEq.rfl
    ring
  refine (h1.add h2).congr' (Filter.Eventually.of_forall fun ε => ?_) EventuallyEq.rfl
  simp only [e]
  ring

/-- **The Taylor step of Proposition 59:** `Σ_t ψ(x + εv_t) = 5ψ(x) + (ε²/2)Δψ(x) + O(ε³)`. -/
theorem taylor_step (ψ : (Fin 5 → ℝ) → ℝ) (hψ : ContDiff ℝ 3 ψ) (x : Fin 5 → ℝ) :
    (fun ε : ℝ => ∑ t, ψ (x + ε • vR t) - (5 * ψ x + ε ^ 2 / 2 * stepLaplacian ψ x)) =O[𝓝 0]
      (fun ε : ℝ => ε ^ 3) := by
  have hsum := Asymptotics.IsBigO.fun_sum (s := Finset.univ) fun t (_ : t ∈ Finset.univ) =>
    line_taylor (fun e : ℝ => ψ (x + e • vR t)) (line_contDiff ψ hψ x (vR t))
  have hfirst := step_first_order ψ hψ x
  refine hsum.congr' (Filter.Eventually.of_forall fun ε => ?_) EventuallyEq.rfl
  simp only [zero_smul, add_zero, stepLaplacian, stepSecond]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, ← Finset.mul_sum, ← Finset.mul_sum, hfirst]
  simp only [nsmul_eq_mul]
  ring

/-- **The law near its critical step (Proposition 59):** at `u = 1/4 − ε²m²/24`,
`(1 + 4u²)ψ(x) − u Σ_t ψ(x + εv_t) = (ε²/8)(m²ψ(x) − Δψ(x)) + O(ε³)`. -/
theorem critical_operator (ψ : (Fin 5 → ℝ) → ℝ) (hψ : ContDiff ℝ 3 ψ) (x : Fin 5 → ℝ) (m : ℝ) :
    (fun ε : ℝ => (1 + 4 * (1 / 4 - ε ^ 2 * m ^ 2 / 24) ^ 2) * ψ x -
        (1 / 4 - ε ^ 2 * m ^ 2 / 24) * ∑ t, ψ (x + ε • vR t) -
        ε ^ 2 / 8 * (m ^ 2 * ψ x - stepLaplacian ψ x)) =O[𝓝 0] (fun ε : ℝ => ε ^ 3) := by
  have hT := taylor_step ψ hψ x
  have hu : (fun ε : ℝ => (1 / 4 - ε ^ 2 * m ^ 2 / 24)) =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) := by
    have : Tendsto (fun ε : ℝ => (1 / 4 - ε ^ 2 * m ^ 2 / 24)) (𝓝 0)
        (𝓝 (1 / 4 - 0 ^ 2 * m ^ 2 / 24)) := by
      apply Continuous.tendsto
      fun_prop
    exact this.isBigO_one (F := ℝ)
  have h1 : (fun ε : ℝ => -((1 / 4 - ε ^ 2 * m ^ 2 / 24) *
      (∑ t, ψ (x + ε • vR t) - (5 * ψ x + ε ^ 2 / 2 * stepLaplacian ψ x)))) =O[𝓝 0]
      (fun ε : ℝ => ε ^ 3) := by
    simpa using (hu.mul hT).neg_left
  have h4 : (fun ε : ℝ => ε ^ 4 * (m ^ 4 / 144 * ψ x + m ^ 2 / 48 * stepLaplacian ψ x)) =O[𝓝 0]
      (fun ε : ℝ => ε ^ 3) := by
    have hb : (fun ε : ℝ => ε * (m ^ 4 / 144 * ψ x + m ^ 2 / 48 * stepLaplacian ψ x)) =O[𝓝 0]
        (fun _ : ℝ => (1 : ℝ)) := by
      have : Tendsto (fun ε : ℝ => ε * (m ^ 4 / 144 * ψ x + m ^ 2 / 48 * stepLaplacian ψ x))
          (𝓝 0) (𝓝 (0 * (m ^ 4 / 144 * ψ x + m ^ 2 / 48 * stepLaplacian ψ x))) := by
        apply Continuous.tendsto
        fun_prop
      exact this.isBigO_one (F := ℝ)
    have := (Asymptotics.isBigO_refl (fun ε : ℝ => ε ^ 3) (𝓝 0)).mul hb
    refine this.congr' (Filter.Eventually.of_forall fun ε => ?_) (Filter.Eventually.of_forall
      fun ε => by simp)
    ring
  have hsum := h1.add h4
  refine hsum.congr' (Filter.Eventually.of_forall fun ε => ?_) (Filter.Eventually.of_forall
    fun ε => by simp)
  simp only [Pi.neg_apply]
  ring

/-! ## Proposition 60 -/

/-- **`cos x = 1 − x²/2 + x⁴/24 + O(x⁶)`:** `|cos x − (1 − x²/2 + x⁴/24)| ≤ |x|⁶ · 7/4320` for
`|x| ≤ 1`. -/
theorem cos_six (x : ℝ) (hx : |x| ≤ 1) :
    |Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24)| ≤ |x| ^ 6 * (7 / 4320) := by
  have hx' : ‖(x : ℂ) * Complex.I‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    exact hx
  have h := Complex.exp_bound hx' (n := 6) (by norm_num)
  have e1 : (∑ m ∈ Finset.range 6, ((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)) =
      ((1 - x ^ 2 / 2 + x ^ 4 / 24 : ℝ) : ℂ) + ((x - x ^ 3 / 6 + x ^ 5 / 120 : ℝ) : ℂ) * Complex.I := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, Nat.factorial]
    push_cast
    ring_nf
    simp only [Complex.I_sq, Complex.I_pow_four]
    have hI3 : Complex.I ^ 3 = -Complex.I := by
      rw [pow_succ, Complex.I_sq]
      ring
    have hI5 : Complex.I ^ 5 = Complex.I := by
      rw [pow_succ, Complex.I_pow_four, one_mul]
    rw [hI3, hI5]
    ring
  rw [e1] at h
  have hre : Real.cos x - (1 - x ^ 2 / 2 + x ^ 4 / 24) =
      (Complex.exp ((x : ℂ) * Complex.I) - (((1 - x ^ 2 / 2 + x ^ 4 / 24 : ℝ) : ℂ) +
        ((x - x ^ 3 / 6 + x ^ 5 / 120 : ℝ) : ℂ) * Complex.I)).re := by
    rw [Complex.sub_re, Complex.exp_ofReal_mul_I_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    ring
  rw [hre]
  refine (Complex.abs_re_le_norm _).trans (h.trans (le_of_eq ?_))
  rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  norm_num [Nat.factorial]

/-- The residual of the polynomial part, in the variables `s = a + b`, `Q₂`, `Q₃`:
`|2Q₃ − s(Q₂ − Q₃)/3 + (Q₂ − Q₃)²/3| ≤ s³/8` when `0 ≤ s ≤ 1/2`, `0 ≤ Q₂ ≤ s²/8`, `|Q₃| ≤ s³/100`. -/
theorem residual_bound (s Q2 Q3 : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 / 2) (hQ2a : 0 ≤ Q2)
    (hQ2b : Q2 ≤ s ^ 2 / 8) (hQ3 : |Q3| ≤ s ^ 3 / 100) :
    |2 * Q3 - s * (Q2 - Q3) / 3 + (Q2 - Q3) ^ 2 / 3| ≤ s ^ 3 / 8 := by
  have hs32 : s ^ 3 ≤ s ^ 2 / 2 := by
    have : s ^ 3 = s * s ^ 2 := by ring
    rw [this]
    have := sq_nonneg s
    nlinarith
  have hs43 : s ^ 4 ≤ s ^ 3 / 2 := by
    have : s ^ 4 = s * s ^ 3 := by ring
    rw [this]
    have := pow_nonneg hs0 3
    nlinarith
  have hQ3' := abs_le.mp hQ3
  have hdiff : |Q2 - Q3| ≤ s ^ 2 / 4 := by
    rw [abs_le]
    constructor <;> linarith [hQ3'.1, hQ3'.2]
  have hsd : |s * (Q2 - Q3)| ≤ s ^ 3 / 4 := by
    rw [abs_mul, abs_of_nonneg hs0]
    calc s * |Q2 - Q3| ≤ s * (s ^ 2 / 4) := mul_le_mul_of_nonneg_left hdiff hs0
      _ = s ^ 3 / 4 := by ring
  have hsq : (Q2 - Q3) ^ 2 ≤ s ^ 4 / 16 := by
    have h := pow_le_pow_left₀ (abs_nonneg (Q2 - Q3)) hdiff 2
    rw [sq_abs] at h
    calc (Q2 - Q3) ^ 2 ≤ (s ^ 2 / 4) ^ 2 := h
      _ = s ^ 4 / 16 := by ring
  have hsq0 : 0 ≤ (Q2 - Q3) ^ 2 := sq_nonneg _
  have hsd' := abs_le.mp hsd
  rw [abs_le]
  constructor <;> linarith [hQ3'.1, hQ3'.2, hsd'.1, hsd'.2]

/-- The polynomial part: `|2D₀ + D₀²/3 − (a + b − ab/3)| ≤ (a + b)³/8` for `0 ≤ a, b ≤ 1/4`, with
`D₀ = 1 − (1 − a/2 + a²/24)(1 − b/2 + b²/24)`. -/
theorem dispersion_poly (a b : ℝ) (ha : 0 ≤ a) (ha' : a ≤ 1 / 4) (hb : 0 ≤ b) (hb' : b ≤ 1 / 4) :
    |2 * (1 - (1 - a / 2 + a ^ 2 / 24) * (1 - b / 2 + b ^ 2 / 24)) +
      (1 - (1 - a / 2 + a ^ 2 / 24) * (1 - b / 2 + b ^ 2 / 24)) ^ 2 / 3 -
      (a + b - a * b / 3)| ≤ (a + b) ^ 3 / 8 := by
  have hR : 2 * (1 - (1 - a / 2 + a ^ 2 / 24) * (1 - b / 2 + b ^ 2 / 24)) +
      (1 - (1 - a / 2 + a ^ 2 / 24) * (1 - b / 2 + b ^ 2 / 24)) ^ 2 / 3 - (a + b - a * b / 3) =
      2 * ((a ^ 2 * b + a * b ^ 2) / 48 - a ^ 2 * b ^ 2 / 576) -
        (a + b) * (((a ^ 2 + b ^ 2) / 24 + a * b / 4) -
          ((a ^ 2 * b + a * b ^ 2) / 48 - a ^ 2 * b ^ 2 / 576)) / 3 +
        (((a ^ 2 + b ^ 2) / 24 + a * b / 4) -
          ((a ^ 2 * b + a * b ^ 2) / 48 - a ^ 2 * b ^ 2 / 576)) ^ 2 / 3 := by
    ring
  rw [hR]
  have hs0 : 0 ≤ a + b := by linarith
  have hs1 : a + b ≤ 1 / 2 := by linarith
  have hab0 : 0 ≤ a * b := mul_nonneg ha hb
  have hab : a * b ≤ (a + b) ^ 2 / 4 := by nlinarith [sq_nonneg (a - b)]
  apply residual_bound (a + b) _ _ hs0 hs1
  · positivity
  · nlinarith [sq_nonneg (a - b)]
  · have e : (a ^ 2 * b + a * b ^ 2) / 48 - a ^ 2 * b ^ 2 / 576 =
        a * b * (a + b) / 48 - (a * b) ^ 2 / 576 := by ring
    rw [e]
    have h1 : a * b * (a + b) ≤ (a + b) ^ 3 / 4 := by
      have := mul_le_mul_of_nonneg_right hab hs0
      calc a * b * (a + b) ≤ (a + b) ^ 2 / 4 * (a + b) := this
        _ = (a + b) ^ 3 / 4 := by ring
    have h1' : 0 ≤ a * b * (a + b) := mul_nonneg hab0 hs0
    have h2 : (a * b) ^ 2 ≤ (a + b) ^ 3 / 32 := by
      have hsq := pow_le_pow_left₀ hab0 hab 2
      have h4 : ((a + b) ^ 2 / 4) ^ 2 = (a + b) ^ 4 / 16 := by ring
      have h43 : (a + b) ^ 4 ≤ (a + b) ^ 3 / 2 := by
        have : (a + b) ^ 4 = (a + b) * (a + b) ^ 3 := by ring
        rw [this]
        have := pow_nonneg hs0 3
        nlinarith
      linarith
    have h2' : 0 ≤ (a * b) ^ 2 := sq_nonneg _
    rw [abs_le]
    constructor <;> linarith

/-- The inverse step: if `0 ≤ W ≤ 1`, `|e₃| ≤ (7/4320)W³` and `D = W/2 − W²/24 − e₃`, then
`W ≤ 4D` and `|W − 2D − D²/3| ≤ (11/10)D³`. -/
theorem inverse_step (W e3 D : ℝ) (hW0 : 0 ≤ W) (hW1 : W ≤ 1) (he3 : |e3| ≤ W ^ 3 * (7 / 4320))
    (hD : D = W / 2 - W ^ 2 / 24 - e3) :
    W ≤ 4 * D ∧ 0 ≤ D ∧ |W - 2 * D - D ^ 2 / 3| ≤ 11 / 10 * D ^ 3 := by
  have hW2 : W ^ 2 ≤ W := by nlinarith
  have hW3 : W ^ 3 ≤ W ^ 2 := by
    have : W ^ 3 = W * W ^ 2 := by ring
    rw [this]
    have := sq_nonneg W
    nlinarith
  have he3' := abs_le.mp he3
  have hW4D : W ≤ 4 * D := by
    rw [hD]
    linarith [he3'.1, he3'.2]
  have hD0 : 0 ≤ D := by linarith
  refine ⟨hW4D, hD0, ?_⟩
  have e : W - 2 * D - D ^ 2 / 3 = (W - 2 * D) * (W + 2 * D) / 12 + 2 * e3 := by
    rw [hD]
    ring
  have hm : |W - 2 * D| ≤ W ^ 2 / 10 := by
    have e' : W - 2 * D = W ^ 2 / 12 + 2 * e3 := by
      rw [hD]
      ring
    rw [e', abs_le]
    constructor <;> linarith [he3'.1, he3'.2, sq_nonneg W]
  have hW2D : W ^ 2 ≤ 16 * D ^ 2 := by
    have := pow_le_pow_left₀ hW0 hW4D 2
    nlinarith
  have hW3D : W ^ 3 ≤ 64 * D ^ 3 := by
    have := pow_le_pow_left₀ hW0 hW4D 3
    nlinarith
  have hpos : 0 ≤ W + 2 * D := by linarith
  have hp : |(W - 2 * D) * (W + 2 * D) / 12| ≤ 8 / 10 * D ^ 3 := by
    rw [abs_div, abs_mul, abs_of_nonneg hpos, show |(12 : ℝ)| = 12 by norm_num]
    have h1 : |W - 2 * D| * (W + 2 * D) ≤ W ^ 2 / 10 * (6 * D) :=
      mul_le_mul hm (by linarith) hpos (by positivity)
    have h2 : W ^ 2 / 10 * (6 * D) ≤ 16 * D ^ 2 / 10 * (6 * D) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h3 : 16 * D ^ 2 / 10 * (6 * D) = 96 / 10 * D ^ 3 := by ring
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 12)]
    linarith
  rw [e]
  calc |(W - 2 * D) * (W + 2 * D) / 12 + 2 * e3| ≤ |(W - 2 * D) * (W + 2 * D) / 12| + |2 * e3| :=
        abs_add_le _ _
    _ ≤ 8 / 10 * D ^ 3 + 2 * (W ^ 3 * (7 / 4320)) := by
        rw [abs_mul, show |(2 : ℝ)| = 2 by norm_num]
        linarith
    _ ≤ 11 / 10 * D ^ 3 := by linarith

/-- The product of the two cosines against its polynomial part:
`|cos μ cos k − A B| ≤ (μ² + k²)³/200`, `A = 1 − μ²/2 + μ⁴/24`, `B = 1 − k²/2 + k⁴/24`. -/
theorem cos_mul_bound (μ k : ℝ) (hμ : |μ| ≤ 1 / 2) (hk : |k| ≤ 1 / 2) :
    |Real.cos μ * Real.cos k - (1 - μ ^ 2 / 2 + μ ^ 4 / 24) * (1 - k ^ 2 / 2 + k ^ 4 / 24)| ≤
      (μ ^ 2 + k ^ 2) ^ 3 / 200 := by
  have ha0 : 0 ≤ μ ^ 2 := sq_nonneg μ
  have hb0 : 0 ≤ k ^ 2 := sq_nonneg k
  have ha1 : μ ^ 2 ≤ 1 / 4 := by
    have := sq_abs μ
    nlinarith [abs_nonneg μ]
  have hb1 : k ^ 2 ≤ 1 / 4 := by
    have := sq_abs k
    nlinarith [abs_nonneg k]
  have h1 := cos_six μ (by linarith)
  have h2 := cos_six k (by linarith)
  have hμ6 : |μ| ^ 6 = (μ ^ 2) ^ 3 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, sq_abs]
  have hk6 : |k| ^ 6 = (k ^ 2) ^ 3 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, sq_abs]
  rw [hμ6] at h1
  rw [hk6] at h2
  set A := 1 - μ ^ 2 / 2 + μ ^ 4 / 24 with hA
  set B := 1 - k ^ 2 / 2 + k ^ 4 / 24 with hB
  set e1 := Real.cos μ - A with he1
  set e2 := Real.cos k - B with he2
  have hμ4 : μ ^ 4 = (μ ^ 2) ^ 2 := by ring
  have hk4 : k ^ 4 = (k ^ 2) ^ 2 := by ring
  have hA0 : 0 ≤ A := by rw [hA, hμ4]; nlinarith
  have hA1 : A ≤ 1 := by rw [hA, hμ4]; nlinarith
  have hB0 : 0 ≤ B := by rw [hB, hk4]; nlinarith
  have hB1 : B ≤ 1 := by rw [hB, hk4]; nlinarith
  have hs3a : (μ ^ 2) ^ 3 ≤ (μ ^ 2 + k ^ 2) ^ 3 := pow_le_pow_left₀ ha0 (by linarith) 3
  have hs3b : (k ^ 2) ^ 3 ≤ (μ ^ 2 + k ^ 2) ^ 3 := pow_le_pow_left₀ hb0 (by linarith) 3
  have hs3 : (μ ^ 2 + k ^ 2) ^ 3 ≤ 1 / 8 := by
    have := pow_le_pow_left₀ (by linarith : 0 ≤ μ ^ 2 + k ^ 2) (by linarith : μ ^ 2 + k ^ 2 ≤ 1 / 2) 3
    linarith
  have he1b : |e1| ≤ (μ ^ 2 + k ^ 2) ^ 3 / 600 := by linarith [pow_nonneg ha0 3]
  have he2b : |e2| ≤ (μ ^ 2 + k ^ 2) ^ 3 / 600 := by linarith [pow_nonneg hb0 3]
  have hexp : Real.cos μ * Real.cos k - A * B = A * e2 + B * e1 + e1 * e2 := by
    simp only [he1, he2]
    ring
  rw [hexp]
  have k1 : |A * e2| ≤ |e2| := by
    rw [abs_mul, abs_of_nonneg hA0]
    exact mul_le_of_le_one_left (abs_nonneg _) hA1
  have k2 : |B * e1| ≤ |e1| := by
    rw [abs_mul, abs_of_nonneg hB0]
    exact mul_le_of_le_one_left (abs_nonneg _) hB1
  have k3 : |e1 * e2| ≤ |e1| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) (by linarith)
  calc |A * e2 + B * e1 + e1 * e2| ≤ |A * e2| + |B * e1| + |e1 * e2| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ (μ ^ 2 + k ^ 2) ^ 3 / 200 := by linarith

set_option maxHeartbeats 1000000 in
/-- **Proposition 60, the dispersion series:** for `|μ|, |k| ≤ 1/2` the eigenphase
`ω = arccos(cos μ cos k)` of one step in motion has `|ω² − (μ² + k² − μ²k²/3)| ≤ 3(μ² + k²)³`. -/
theorem dispersion_series (μ k : ℝ) (hμ : |μ| ≤ 1 / 2) (hk : |k| ≤ 1 / 2) :
    |Real.arccos (Real.cos μ * Real.cos k) ^ 2 - (μ ^ 2 + k ^ 2 - μ ^ 2 * k ^ 2 / 3)| ≤
      3 * (μ ^ 2 + k ^ 2) ^ 3 := by
  have ha0 : 0 ≤ μ ^ 2 := sq_nonneg μ
  have hb0 : 0 ≤ k ^ 2 := sq_nonneg k
  have ha1 : μ ^ 2 ≤ 1 / 4 := by
    have := sq_abs μ
    nlinarith [abs_nonneg μ]
  have hb1 : k ^ 2 ≤ 1 / 4 := by
    have := sq_abs k
    nlinarith [abs_nonneg k]
  have hE := cos_mul_bound μ k hμ hk
  have hpoly := dispersion_poly (μ ^ 2) (k ^ 2) ha0 ha1 hb0 hb1
  have hμ4 : μ ^ 4 = (μ ^ 2) ^ 2 := by ring
  have hk4 : k ^ 4 = (k ^ 2) ^ 2 := by ring
  rw [hμ4, hk4] at hE
  -- the polynomial part `D₀ = 1 − AB`
  set D0 := 1 - (1 - μ ^ 2 / 2 + (μ ^ 2) ^ 2 / 24) * (1 - k ^ 2 / 2 + (k ^ 2) ^ 2 / 24) with hD0
  set c := Real.cos μ * Real.cos k with hc
  set s := μ ^ 2 + k ^ 2 with hs
  have hs0 : 0 ≤ s := by linarith
  have hs1 : s ≤ 1 / 2 := by linarith
  have hs3 : s ^ 3 ≤ 1 / 8 := by
    have := pow_le_pow_left₀ hs0 hs1 3
    linarith
  have hE' := abs_le.mp hE
  have hD0s : 0 ≤ D0 ∧ D0 ≤ s / 2 := by
    have hAl : 1 - μ ^ 2 / 2 ≤ 1 - μ ^ 2 / 2 + (μ ^ 2) ^ 2 / 24 := by
      have := sq_nonneg (μ ^ 2)
      linarith
    have hsqa : (μ ^ 2) ^ 2 ≤ μ ^ 2 / 4 := by
      calc (μ ^ 2) ^ 2 = μ ^ 2 * μ ^ 2 := by ring
        _ ≤ μ ^ 2 * (1 / 4) := mul_le_mul_of_nonneg_left ha1 ha0
        _ = μ ^ 2 / 4 := by ring
    have hAu : 1 - μ ^ 2 / 2 + (μ ^ 2) ^ 2 / 24 ≤ 1 := by linarith
    have hBl : 1 - k ^ 2 / 2 ≤ 1 - k ^ 2 / 2 + (k ^ 2) ^ 2 / 24 := by
      have := sq_nonneg (k ^ 2)
      linarith
    have hsqb : (k ^ 2) ^ 2 ≤ k ^ 2 / 4 := by
      calc (k ^ 2) ^ 2 = k ^ 2 * k ^ 2 := by ring
        _ ≤ k ^ 2 * (1 / 4) := mul_le_mul_of_nonneg_left hb1 hb0
        _ = k ^ 2 / 4 := by ring
    have hBu : 1 - k ^ 2 / 2 + (k ^ 2) ^ 2 / 24 ≤ 1 := by linarith
    have hA0 : 0 ≤ 1 - μ ^ 2 / 2 := by linarith
    have hB0 : 0 ≤ 1 - k ^ 2 / 2 := by linarith
    have hprod := mul_le_mul hAl hBl hB0 (by linarith)
    have hprod1 := mul_le_one₀ hAu (by linarith) hBu
    have hab := mul_nonneg ha0 hb0
    have e : (1 - μ ^ 2 / 2) * (1 - k ^ 2 / 2) = 1 - s / 2 + μ ^ 2 * k ^ 2 / 4 := by
      rw [hs]
      ring
    constructor
    · rw [hD0]
      linarith
    · rw [hD0]
      linarith
  have hc1 : c ≤ 1 := by
    have hm := mul_le_one₀ (Real.abs_cos_le_one μ) (abs_nonneg _) (Real.abs_cos_le_one k)
    calc c ≤ |c| := le_abs_self c
      _ = |Real.cos μ| * |Real.cos k| := by rw [hc, abs_mul]
      _ ≤ 1 := hm
  have hcD : c = 1 - D0 + (c - (1 - D0)) := by ring
  have hEc : |c - (1 - D0)| ≤ s ^ 3 / 200 := by
    have : c - (1 - D0) = c - (1 - μ ^ 2 / 2 + (μ ^ 2) ^ 2 / 24) *
        (1 - k ^ 2 / 2 + (k ^ 2) ^ 2 / 24) := by
      rw [hD0]
      ring
    rw [this]
    exact hE
  have hEc' := abs_le.mp hEc
  have hc0 : 2 / 3 ≤ c := by
    linarith [hD0s.2]
  -- the eigenphase
  set ω := Real.arccos c with hω
  have hω0 : 0 ≤ ω := Real.arccos_nonneg c
  have hω1 : ω ≤ 1 := by
    have hc' : Real.cos 1 ≤ c := le_trans Real.cos_one_le (by linarith)
    have := Real.arccos_le_arccos hc'
    rwa [Real.arccos_cos (by norm_num) (by linarith [Real.pi_gt_three])] at this
  have hcosω : Real.cos ω = c := Real.cos_arccos (by linarith) hc1
  have h3 := cos_six ω (by rw [abs_of_nonneg hω0]; exact hω1)
  have hω6 : |ω| ^ 6 = (ω ^ 2) ^ 3 := by
    rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, sq_abs]
  rw [hω6, show ω ^ 4 = (ω ^ 2) ^ 2 by ring, hcosω] at h3
  have hW0 : 0 ≤ ω ^ 2 := sq_nonneg ω
  have hW1 : ω ^ 2 ≤ 1 := pow_le_one₀ hω0 hω1
  obtain ⟨hW4D, hD0', hkey⟩ := inverse_step (ω ^ 2) (c - (1 - ω ^ 2 / 2 + (ω ^ 2) ^ 2 / 24))
    (1 - c) hW0 hW1 h3 (by ring)
  -- `D = 1 − c` against `D₀`
  have hDs : 1 - c ≤ s := by
    have hs3' : s ^ 3 ≤ s := pow_le_of_le_one hs0 (by linarith) (by norm_num)
    linarith [hD0s.2]
  have hmid : |(2 * (1 - c) + (1 - c) ^ 2 / 3) - (2 * D0 + D0 ^ 2 / 3)| ≤ 3 * (s ^ 3 / 200) := by
    have e : (2 * (1 - c) + (1 - c) ^ 2 / 3) - (2 * D0 + D0 ^ 2 / 3) =
        -(c - (1 - D0)) * (2 + ((1 - c) + D0) / 3) := by ring
    have hfac0 : 0 ≤ 2 + ((1 - c) + D0) / 3 := by linarith [hD0s.1]
    have hfac : 2 + ((1 - c) + D0) / 3 ≤ 3 := by
      linarith [hD0s.2]
    rw [e, abs_mul, abs_neg, abs_of_nonneg hfac0]
    calc |c - (1 - D0)| * (2 + ((1 - c) + D0) / 3) ≤ (s ^ 3 / 200) * 3 :=
          mul_le_mul hEc hfac hfac0 (by positivity)
      _ = 3 * (s ^ 3 / 200) := by ring
  have hD3 : (1 - c) ^ 3 ≤ s ^ 3 := pow_le_pow_left₀ hD0' hDs 3
  have e : ω ^ 2 - (μ ^ 2 + k ^ 2 - μ ^ 2 * k ^ 2 / 3) = (ω ^ 2 - 2 * (1 - c) - (1 - c) ^ 2 / 3) +
      ((2 * (1 - c) + (1 - c) ^ 2 / 3) - (2 * D0 + D0 ^ 2 / 3)) +
      (2 * D0 + D0 ^ 2 / 3 - (μ ^ 2 + k ^ 2 - μ ^ 2 * k ^ 2 / 3)) := by ring
  rw [e]
  calc |(ω ^ 2 - 2 * (1 - c) - (1 - c) ^ 2 / 3) +
        ((2 * (1 - c) + (1 - c) ^ 2 / 3) - (2 * D0 + D0 ^ 2 / 3)) +
        (2 * D0 + D0 ^ 2 / 3 - (μ ^ 2 + k ^ 2 - μ ^ 2 * k ^ 2 / 3))| ≤
        |ω ^ 2 - 2 * (1 - c) - (1 - c) ^ 2 / 3| +
          |(2 * (1 - c) + (1 - c) ^ 2 / 3) - (2 * D0 + D0 ^ 2 / 3)| +
          |2 * D0 + D0 ^ 2 / 3 - (μ ^ 2 + k ^ 2 - μ ^ 2 * k ^ 2 / 3)| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ 11 / 10 * (1 - c) ^ 3 + 3 * (s ^ 3 / 200) + s ^ 3 / 8 := by
        have hp' : |2 * D0 + D0 ^ 2 / 3 - (μ ^ 2 + k ^ 2 - μ ^ 2 * k ^ 2 / 3)| ≤ s ^ 3 / 8 := hpoly
        linarith
    _ ≤ 3 * s ^ 3 := by linarith [hD3, pow_nonneg hs0 3]

end Comparison

end
