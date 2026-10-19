import Comparison.ArticleStatements.SectorSum

/-!
# The sum over sectors as an integral over the connections (Prop. 115)

`ArticleStatements/SectorSum.lean` proves Prop. 115 for a finite family of connections. Here the sum is an
integral: `(Ω, μ)` any finite measure space of connections (the product of Haar measures over the
links, for instance), `w : Ω → ℝ` the law's weight (`lawWeight_pos`: `det(I − uB[U]) > 0` for
`0 ≤ u < ¼` and every unitary connection), `q : Ω → ℤ` the charge, `τ` the reversal
(`lawWeight_conj_eq`: it keeps the weight and reverses the charge), measure preserving.

* `Zint θ = ∫ w(U) e^{i q(U) θ} dμ(U)`; `Zint_real`: **it is real**, `∫ w cos(qθ)`;
* `aSector n = ∫_{q = n} w`; `aSector_pos`: **positive on every sector of positive measure**;
  `aSector_symm`: **`a_{−n} = a_n`**;
* `Zint_norm_le`: **`|Z(θ)| ≤ Z(0)`**; `Zint_max_iff`: **with the sectors `0` and `1` of positive
  measure, `|Z(θ)| = Z(0)` exactly when `θ ∈ 2πℤ`**: the angle of the sectors is zero;
* `law_sector_integral`: the same for the law's weight `Re det(I − uB[Γ U])` of a measurable family of
  unitary connections.
-/

namespace Comparison.GroupsContinuumLaw

open MeasureTheory Complex Matrix Comparison Comparison.ArticleStatements

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- **The sector sum as an integral over the connections.** -/
def Zint (w : Ω → ℝ) (q : Ω → ℤ) (θ : ℝ) : ℂ :=
  ∫ U, (w U : ℂ) * exp (((q U : ℝ) * θ : ℝ) * I) ∂μ

/-- The weight of the sector `n`. -/
def aSector (w : Ω → ℝ) (q : Ω → ℤ) (n : ℤ) : ℝ := ∫ U in {U | q U = n}, w U ∂μ

variable {μ}

theorem exp_eq_cos_sin (x : ℝ) : exp ((x : ℂ) * I) = (Real.cos x : ℂ) + (Real.sin x : ℂ) * I := by
  rw [exp_mul_I, ← ofReal_cos, ← ofReal_sin]

theorem integrable_mul_bounded (w : Ω → ℝ) (hw : Integrable w μ) (g : Ω → ℝ)
    (hg : AEStronglyMeasurable g μ) (hb : ∀ U, |g U| ≤ 1) : Integrable (fun U => w U * g U) μ := by
  refine hw.mul_of_top_left ?_
  exact memLp_top_of_bound hg 1 (Filter.Eventually.of_forall fun U => by
    rw [Real.norm_eq_abs]; exact hb U)

/-- **The sector sum is real:** `Z(θ) = ∫ w cos(qθ)`. -/
theorem Zint_real (w : Ω → ℝ) (q : Ω → ℤ) (hw : Integrable w μ) (hqm : Measurable q)
    (τ : Ω ≃ᵐ Ω) (hτ : MeasurePreserving τ μ μ) (hq : ∀ U, q (τ U) = -q U)
    (hwτ : ∀ U, w (τ U) = w U) (θ : ℝ) :
    Zint μ w q θ = ((∫ U, w U * Real.cos ((q U : ℝ) * θ) ∂μ : ℝ) : ℂ) := by
  have hmc : AEStronglyMeasurable (fun U => Real.cos ((q U : ℝ) * θ)) μ :=
    (Real.continuous_cos.measurable.comp
      ((measurable_from_top.comp hqm).mul_const θ)).aestronglyMeasurable
  have hms : AEStronglyMeasurable (fun U => Real.sin ((q U : ℝ) * θ)) μ :=
    (Real.continuous_sin.measurable.comp
      ((measurable_from_top.comp hqm).mul_const θ)).aestronglyMeasurable
  have hic := integrable_mul_bounded w hw _ hmc (fun U => Real.abs_cos_le_one _)
  have his := integrable_mul_bounded w hw _ hms (fun U => Real.abs_sin_le_one _)
  have hsin : ∫ U, w U * Real.sin ((q U : ℝ) * θ) ∂μ = 0 := by
    have h := hτ.integral_comp' (fun U => w U * Real.sin ((q U : ℝ) * θ))
    simp only [hq, hwτ, Int.cast_neg, neg_mul, Real.sin_neg, mul_neg] at h
    rw [integral_neg] at h
    linarith
  have e : (fun U => (w U : ℂ) * exp (((q U : ℝ) * θ : ℝ) * I)) =
      fun U => ((w U * Real.cos ((q U : ℝ) * θ) : ℝ) : ℂ) +
        ((w U * Real.sin ((q U : ℝ) * θ) : ℝ) : ℂ) * I := by
    funext U
    rw [exp_eq_cos_sin]
    push_cast
    ring
  have hc' : Integrable (fun U => ((w U * Real.cos ((q U : ℝ) * θ) : ℝ) : ℂ)) μ := hic.ofReal
  have hs' : Integrable (fun U => ((w U * Real.sin ((q U : ℝ) * θ) : ℝ) : ℂ) * I) μ :=
    (his.ofReal).mul_const I
  rw [Zint, e, integral_add hc' hs', integral_mul_const, integral_complex_ofReal,
    integral_complex_ofReal, hsin]
  simp

theorem Zint_zero (w : Ω → ℝ) (q : Ω → ℤ) : Zint μ w q 0 = ((∫ U, w U ∂μ : ℝ) : ℂ) := by
  rw [Zint]
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one]
  exact integral_complex_ofReal

/-- **`|Z(θ)| ≤ Z(0)`.** -/
theorem Zint_norm_le (w : Ω → ℝ) (q : Ω → ℤ) (hw0 : ∀ U, 0 ≤ w U) (θ : ℝ) :
    ‖Zint μ w q θ‖ ≤ ∫ U, w U ∂μ := by
  calc ‖Zint μ w q θ‖ ≤ ∫ U, ‖(w U : ℂ) * exp (((q U : ℝ) * θ : ℝ) * I)‖ ∂μ :=
        norm_integral_le_integral_norm _
    _ = ∫ U, w U ∂μ := by
        congr 1
        funext U
        rw [norm_mul, norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hw0 U)]

/-- **Every sector of positive measure has a positive weight.** -/
theorem aSector_pos (w : Ω → ℝ) (q : Ω → ℤ) (hw : Integrable w μ) (hqm : Measurable q)
    (hw0 : ∀ U, 0 < w U) (n : ℤ) (hn : 0 < μ {U | q U = n}) : 0 < aSector μ w q n := by
  have hs : MeasurableSet {U | q U = n} := hqm (measurableSet_singleton n)
  rw [aSector, setIntegral_pos_iff_support_of_nonneg_ae
    (Filter.Eventually.of_forall fun U => (hw0 U).le) hw.integrableOn]
  have hsupp : Function.support w = Set.univ := by
    ext U
    simp [(hw0 U).ne']
  rw [hsupp, Set.univ_inter]
  exact hn

/-- **`a_{−n} = a_n`.** -/
theorem aSector_symm (w : Ω → ℝ) (q : Ω → ℤ) (hqm : Measurable q) (τ : Ω ≃ᵐ Ω)
    (hτ : MeasurePreserving τ μ μ) (hq : ∀ U, q (τ U) = -q U) (hwτ : ∀ U, w (τ U) = w U)
    (n : ℤ) : aSector μ w q (-n) = aSector μ w q n := by
  have hs : ∀ m : ℤ, MeasurableSet {U | q U = m} := fun m => hqm (measurableSet_singleton m)
  rw [aSector, aSector, ← integral_indicator (hs _), ← integral_indicator (hs _)]
  have h := hτ.integral_comp' ({U | q U = -n}.indicator w)
  rw [← h]
  congr 1
  funext U
  simp only [Set.indicator, Set.mem_ofPred_eq, hq, neg_inj, hwτ]
  split_ifs <;> rfl

/-- **The angle of the sectors is zero:** with the sectors `0` and `1` of positive measure,
`|Z(θ)| = Z(0)` exactly when `θ ∈ 2πℤ`. -/
theorem Zint_max_iff (w : Ω → ℝ) (q : Ω → ℤ) (hw : Integrable w μ) (hqm : Measurable q)
    (hw0 : ∀ U, 0 < w U) (τ : Ω ≃ᵐ Ω) (hτ : MeasurePreserving τ μ μ) (hq : ∀ U, q (τ U) = -q U)
    (hwτ : ∀ U, w (τ U) = w U) (h0 : 0 < μ {U | q U = 0}) (h1 : 0 < μ {U | q U = 1}) (θ : ℝ) :
    ‖Zint μ w q θ‖ = ∫ U, w U ∂μ ↔ ∃ k : ℤ, θ = k * (2 * Real.pi) := by
  have hmc : AEStronglyMeasurable (fun U => Real.cos ((q U : ℝ) * θ)) μ :=
    (Real.continuous_cos.measurable.comp
      ((measurable_from_top.comp hqm).mul_const θ)).aestronglyMeasurable
  have hic := integrable_mul_bounded w hw _ hmc (fun U => Real.abs_cos_le_one _)
  have hZ := Zint_real w q hw hqm τ hτ hq hwτ θ
  constructor
  · intro h
    rw [hZ, Complex.norm_real, Real.norm_eq_abs] at h
    set c := ∫ U, w U * Real.cos ((q U : ℝ) * θ) ∂μ with hc
    rcases le_or_gt 0 c with hpos | hneg
    · rw [abs_of_nonneg hpos] at h
      -- `∫ w (1 − cos qθ) = 0`
      have hz : ∫ U, w U * (1 - Real.cos ((q U : ℝ) * θ)) ∂μ = 0 := by
        have e : (fun U => w U * (1 - Real.cos ((q U : ℝ) * θ))) =
            fun U => w U - w U * Real.cos ((q U : ℝ) * θ) := by funext U; ring
        rw [e, integral_sub hw hic, ← hc, h, sub_self]
      have hnn : 0 ≤ fun U => w U * (1 - Real.cos ((q U : ℝ) * θ)) := fun U =>
        mul_nonneg (hw0 U).le (by linarith [Real.cos_le_one ((q U : ℝ) * θ)])
      have hint : Integrable (fun U => w U * (1 - Real.cos ((q U : ℝ) * θ))) μ := by
        have e : (fun U => w U * (1 - Real.cos ((q U : ℝ) * θ))) =
            fun U => w U - w U * Real.cos ((q U : ℝ) * θ) := by funext U; ring
        rw [e]
        exact hw.sub hic
      have hae := (integral_eq_zero_iff_of_nonneg hnn hint).1 hz
      have hex : ∃ U, q U = 1 ∧ w U * (1 - Real.cos ((q U : ℝ) * θ)) = 0 := by
        by_contra hno
        push Not at hno
        have hsub : {U | q U = 1} ⊆ {U | w U * (1 - Real.cos ((q U : ℝ) * θ)) ≠ 0} :=
          fun U hU => hno U hU
        have hnull : μ {U | w U * (1 - Real.cos ((q U : ℝ) * θ)) ≠ 0} = 0 := by
          rw [Filter.EventuallyEq, ae_iff] at hae
          simpa using hae
        exact absurd (measure_mono_null hsub hnull) h1.ne'
      obtain ⟨U, hU1, hU⟩ := hex
      rw [hU1] at hU
      have hcos : Real.cos θ = 1 := by
        rcases mul_eq_zero.1 hU with h' | h'
        · exact absurd h' (hw0 U).ne'
        · push_cast at h'
          rw [one_mul] at h'
          linarith
      obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff θ).1 hcos
      exact ⟨k, hk.symm⟩
    · exfalso
      rw [abs_of_neg hneg] at h
      have hz : ∫ U, w U * (1 + Real.cos ((q U : ℝ) * θ)) ∂μ = 0 := by
        have e : (fun U => w U * (1 + Real.cos ((q U : ℝ) * θ))) =
            fun U => w U + w U * Real.cos ((q U : ℝ) * θ) := by funext U; ring
        rw [e, integral_add hw hic, ← hc]
        linarith
      have hnn : 0 ≤ fun U => w U * (1 + Real.cos ((q U : ℝ) * θ)) := fun U =>
        mul_nonneg (hw0 U).le (by linarith [Real.neg_one_le_cos ((q U : ℝ) * θ)])
      have hint : Integrable (fun U => w U * (1 + Real.cos ((q U : ℝ) * θ))) μ := by
        have e : (fun U => w U * (1 + Real.cos ((q U : ℝ) * θ))) =
            fun U => w U + w U * Real.cos ((q U : ℝ) * θ) := by funext U; ring
        rw [e]
        exact hw.add hic
      have hae := (integral_eq_zero_iff_of_nonneg hnn hint).1 hz
      have hex : ∃ U, q U = 0 ∧ w U * (1 + Real.cos ((q U : ℝ) * θ)) = 0 := by
        by_contra hno
        push Not at hno
        have hsub : {U | q U = 0} ⊆ {U | w U * (1 + Real.cos ((q U : ℝ) * θ)) ≠ 0} :=
          fun U hU => hno U hU
        have hnull : μ {U | w U * (1 + Real.cos ((q U : ℝ) * θ)) ≠ 0} = 0 := by
          rw [Filter.EventuallyEq, ae_iff] at hae
          simpa using hae
        exact absurd (measure_mono_null hsub hnull) h0.ne'
      obtain ⟨U, hU0, hU⟩ := hex
      rw [hU0] at hU
      simp at hU
      exact (hw0 U).ne' (by linarith)
  · rintro ⟨k, rfl⟩
    have hone : ∀ U, exp (((q U : ℝ) * (k * (2 * Real.pi)) : ℝ) * I) = 1 := by
      intro U
      rw [exp_eq_cos_sin]
      have hc : Real.cos ((q U : ℝ) * (k * (2 * Real.pi))) = 1 := by
        rw [Real.cos_eq_one_iff]
        exact ⟨q U * k, by push_cast; ring⟩
      have hs : Real.sin ((q U : ℝ) * (k * (2 * Real.pi))) = 0 := by
        rw [show (q U : ℝ) * (k * (2 * Real.pi)) = ((q U * k : ℤ) : ℝ) * (2 * Real.pi) by
          push_cast; ring]
        rw [Real.sin_eq_zero_iff]
        exact ⟨2 * (q U * k), by push_cast; ring⟩
      rw [hc, hs]
      simp
    have hZ0 : Zint μ w q (k * (2 * Real.pi)) = ((∫ U, w U ∂μ : ℝ) : ℂ) := by
      rw [Zint]
      simp only [hone, mul_one]
      exact integral_complex_ofReal
    rw [hZ0, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun U => (hw0 U).le)]

/-- **Prop. 115 as an integral over the connections:** for a measurable family of unitary
connections, the law's weight `Re det(I − uB[Γ U])` is positive, and the sector integral is real, at
most its value at `θ = 0`, and equal to it only at `θ ∈ 2πℤ`. -/
theorem law_sector_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Γ : Ω → Fin 5 → Matrix ι ι ℂ) (hH : ∀ U t, (Γ U t)ᴴ = Γ U t)
    (hG : ∀ U t, Γ U t * Γ U t = 1) (u : ℝ) (hu0 : 0 ≤ u) (hu : u < 1 / 4) (q : Ω → ℤ)
    (hqm : Measurable q) (hw : Integrable (fun U => ((1 - (u : ℂ) • stepOp (Γ U)).det).re) μ)
    (τ : Ω ≃ᵐ Ω) (hτ : MeasurePreserving τ μ μ) (hq : ∀ U, q (τ U) = -q U)
    (hΓτ : ∀ U, Γ (τ U) = conjConn (Γ U)) (h0 : 0 < μ {U | q U = 0})
    (h1 : 0 < μ {U | q U = 1}) (θ : ℝ) :
    (∀ U, 0 < ((1 - (u : ℂ) • stepOp (Γ U)).det).re) ∧
    ‖Zint μ (fun U => ((1 - (u : ℂ) • stepOp (Γ U)).det).re) q θ‖ ≤
      ∫ U, ((1 - (u : ℂ) • stepOp (Γ U)).det).re ∂μ ∧
    (‖Zint μ (fun U => ((1 - (u : ℂ) • stepOp (Γ U)).det).re) q θ‖ =
      ∫ U, ((1 - (u : ℂ) • stepOp (Γ U)).det).re ∂μ ↔ ∃ k : ℤ, θ = k * (2 * Real.pi)) := by
  have hpos : ∀ U, 0 < ((1 - (u : ℂ) • stepOp (Γ U)).det).re := fun U =>
    (Complex.pos_iff.mp (lawWeight_pos (Γ U) (hH U) (hG U) u hu0 hu)).1
  have hwτ : ∀ U, ((1 - (u : ℂ) • stepOp (Γ (τ U))).det).re =
      ((1 - (u : ℂ) • stepOp (Γ U)).det).re := by
    intro U
    rw [hΓτ U, lawWeight_conj_eq (Γ U) (hH U) (hG U) u hu0 hu]
  exact ⟨hpos, Zint_norm_le _ q (fun U => (hpos U).le) θ,
    Zint_max_iff _ q hw hqm hpos τ hτ hq hwτ h0 h1 θ⟩

end

end Comparison.GroupsContinuumLaw
