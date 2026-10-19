import Comparison.System.Postulates
import Comparison.GroupsContinuumLaw.SectorIntegral
import Comparison.WholePicture.Connection

/-!
# The proof system, the law: Proposition 115, the angle of the sectors is zero

Positivity below the critical step for every unitary connection
(`WholePicture/Connection.lean`), the weights real and kept by time reversal (`ArticleStatements/SectorSum.lean`), the sum
over sectors for a finite family (`SectorSource.prop115`, `prop115_max_iff`, `theta_bar_zero`) and as an integral over
any finite measure on the connections (`GroupsContinuumLaw/SectorIntegral.lean`). Here:

* `Zint_sector_series`: **the integral over the connections is the sum over the sectors,
  `Z(θ) = Σ_n a_n e^{inθ}`**, `a_n = ∫_{q = n} w`;
* `theta_bar_zero_integral`: **`θ̄ = θ + arg det M ∈ 2πℤ`** where `|Z(θ)| = Z(0)`, when `det M` is a positive
  number (a closed weight);
* `prop_115`: Proposition 115 as one statement.
-/

open MeasureTheory Complex Matrix Comparison Comparison.ArticleStatements Comparison.GroupsContinuumLaw
open scoped ComplexOrder

namespace Comparison.System

namespace Law

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **The sector series of the integral:** `Z(θ) = Σ_n a_n e^{inθ}` with `a_n = ∫_{q = n} w`. -/
theorem Zint_sector_series (w : Ω → ℝ) (q : Ω → ℤ) (hw : Integrable w μ) (hqm : Measurable q)
    (θ : ℝ) :
    HasSum (fun n : ℤ => (aSector μ w q n : ℂ) * exp (((n : ℝ) * θ : ℝ) * I)) (Zint μ w q θ) := by
  have hs : ∀ n : ℤ, MeasurableSet {U | q U = n} := fun n => hqm (measurableSet_singleton n)
  have hd : Pairwise (Function.onFun Disjoint fun n : ℤ => {U | q U = n}) := by
    intro m n hmn
    refine Set.disjoint_left.mpr fun U hU hU' => hmn ?_
    exact hU.symm.trans hU'
  have hunion : (⋃ n : ℤ, {U | q U = n}) = Set.univ := by
    ext U; simp
  set f : Ω → ℂ := fun U => (w U : ℂ) * exp (((q U : ℝ) * θ : ℝ) * I) with hf
  have hfi : Integrable f μ := by
    have hb : ∀ U, ‖exp (((q U : ℝ) * θ : ℝ) * I)‖ ≤ 1 := fun U => by
      rw [Complex.norm_exp_ofReal_mul_I]
    have hm : AEStronglyMeasurable (fun U => exp (((q U : ℝ) * θ : ℝ) * I)) μ := by
      apply Measurable.aestronglyMeasurable
      exact Complex.measurable_exp.comp (((Complex.measurable_ofReal.comp
        ((measurable_from_top.comp hqm).mul_const θ))).mul_const I)
    exact hw.ofReal.mul_of_top_left (memLp_top_of_bound hm 1 (Filter.Eventually.of_forall hb))
  have h := hasSum_integral_iUnion hs hd (by rw [hunion]; exact hfi.integrableOn)
  rw [hunion, Measure.restrict_univ] at h
  have e : ∀ n : ℤ, ∫ U in {U | q U = n}, f U ∂μ =
      (aSector μ w q n : ℂ) * exp (((n : ℝ) * θ : ℝ) * I) := by
    intro n
    have hc : ∀ U ∈ {U | q U = n}, f U = (w U : ℂ) * exp (((n : ℝ) * θ : ℝ) * I) := by
      intro U hU
      simp only [Set.mem_setOf_eq] at hU
      simp only [hf, hU]
    rw [setIntegral_congr_fun (hs n) hc, integral_mul_const, aSector, integral_complex_ofReal]
  simp only [e] at h
  exact h

/-- **`θ̄ = 0` where the integral over the sectors is largest:** if `|Z(θ)| = Z(0)` and the mass determinant
`det M` is a positive number, then `θ + arg det M ∈ 2πℤ`. -/
theorem theta_bar_zero_integral (w : Ω → ℝ) (q : Ω → ℤ) (hw : Integrable w μ) (hqm : Measurable q)
    (hw0 : ∀ U, 0 < w U) (τ : Ω ≃ᵐ Ω) (hτ : MeasurePreserving τ μ μ) (hq : ∀ U, q (τ U) = -q U)
    (hwτ : ∀ U, w (τ U) = w U) (h0 : 0 < μ {U | q U = 0}) (h1 : 0 < μ {U | q U = 1}) (θ : ℝ)
    (hmax : ‖Zint μ w q θ‖ = ∫ U, w U ∂μ) (detM : ℂ) (hM : 0 < detM) :
    ∃ k : ℤ, θ + Complex.arg detM = k * (2 * Real.pi) := by
  rw [arg_eq_zero_of_pos hM, add_zero]
  exact (Zint_max_iff w q hw hqm hw0 τ hτ hq hwτ h0 h1 θ).mp hmax

end Law

open Comparison.System.Law

/-- **Proposition 115, the angle of the sectors is zero.** For `0 ≤ u < 1/4` and every unitary connection
`(1 + 4u²) − uA_U ≥ (1 − u)(1 − 4u) > 0`, and the weight `det(I − uB[U])` is a positive real number kept by
time reversal; for a family of configurations (finite, or any finite measure on the connections) with the
charge `q` reversed by time reversal, `Z_top(θ) = Σ_n a_n e^{inθ}` with `a_n = a_{−n} > 0` on every inhabited
sector, `|Z_top(θ)| ≤ Z_top(0)`, with equality exactly at `θ ∈ 2πℤ` when the sectors `0` and `1` are inhabited;
and where it is largest, `θ̄ = θ + arg det M ∈ 2πℤ` whenever `det M` is a positive number.
Recognition: `det M = det(M_uM_d)`, the mass determinant, is a product of closed weights (Prop. 103); `θ̄` is the
strong phase; the bound `|θ̄| ≲ 10⁻¹⁰` is the neutron's electric dipole. -/
theorem prop_115 :
    (∀ (n : Type) [Fintype n] [DecidableEq n] (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ))
        (u : ℝ), 0 ≤ u → u < 1 / 4 →
      0 < (1 - u) * (1 - 4 * u) ∧
      (∀ x : Fin 16 × n → ℂ, (1 - u) * (1 - 4 * u) * (star x ⬝ᵥ x).re ≤
        (star x ⬝ᵥ (((1 + 4 * (u : ℂ) ^ 2) • (1 : Matrix (Fin 16 × n) (Fin 16 × n) ℂ) -
          (u : ℂ) • ∑ t, WholePicture.connStep c t) *ᵥ x)).re) ∧
      0 < (1 - (u : ℂ) • Bconn c).det ∧
      (1 - (u : ℂ) • stepOp (conjConn (WholePicture.connStep c))).det = (1 - (u : ℂ) • Bconn c).det) ∧
    (∀ (V : Type) [Fintype V] [DecidableEq V] (C : Type) [Fintype C] (S : SectorSource V C) (u : ℝ),
      0 ≤ u → u < 1 / 4 →
      ((∀ n : ℤ, (∃ c, S.q c = n) → 0 < S.a u n) ∧ (∀ n : ℤ, S.a u (-n) = S.a u n) ∧
        (∀ θ : ℝ, S.Ztop u θ = ∑ n ∈ Finset.univ.image S.q,
          S.a u n * Complex.exp (((n : ℝ) * θ : ℝ) * Complex.I)) ∧
        (∀ θ : ℝ, ‖S.Ztop u θ‖ ≤ (S.Ztop u 0).re)) ∧
      ((∃ c, S.q c = 0) → (∃ c, S.q c = 1) → ∀ θ : ℝ,
        (‖S.Ztop u θ‖ = (S.Ztop u 0).re ↔ ∃ k : ℤ, θ = k * (2 * Real.pi)) ∧
        (‖S.Ztop u θ‖ = (S.Ztop u 0).re → ∀ detM : ℂ, 0 < detM →
          ∃ k : ℤ, θ + Complex.arg detM = k * (2 * Real.pi)))) ∧
    (∀ (Ωc : Type) [MeasurableSpace Ωc] (μ : Measure Ωc) [IsFiniteMeasure μ] (w : Ωc → ℝ)
        (q : Ωc → ℤ), Integrable w μ → Measurable q → (∀ U, 0 < w U) →
      ∀ (τ : Ωc ≃ᵐ Ωc), MeasurePreserving τ μ μ → (∀ U, q (τ U) = -q U) → (∀ U, w (τ U) = w U) →
      (∀ θ : ℝ, HasSum (fun n : ℤ => (aSector μ w q n : ℂ) * exp (((n : ℝ) * θ : ℝ) * I))
        (Zint μ w q θ)) ∧
      (∀ n : ℤ, 0 < μ {U | q U = n} → 0 < aSector μ w q n) ∧
      (∀ n : ℤ, aSector μ w q (-n) = aSector μ w q n) ∧
      (∀ θ : ℝ, ‖Zint μ w q θ‖ ≤ ∫ U, w U ∂μ) ∧
      (0 < μ {U | q U = 0} → 0 < μ {U | q U = 1} → ∀ θ : ℝ,
        (‖Zint μ w q θ‖ = ∫ U, w U ∂μ ↔ ∃ k : ℤ, θ = k * (2 * Real.pi)) ∧
        (‖Zint μ w q θ‖ = ∫ U, w U ∂μ → ∀ detM : ℂ, 0 < detM →
          ∃ k : ℤ, θ + Complex.arg detM = k * (2 * Real.pi)))) := by
  refine ⟨fun n _ _ c u hu0 hu => ⟨mul_pos (by linarith) (by linarith),
      fun x => WholePicture.law_quad_unitary c u hu0 x,
      WholePicture.law_weight_pos_unitary c u hu0 hu,
      lawWeight_conj_eq _ (WholePicture.connStep_herm c) (WholePicture.connStep_sq c) u hu0 hu⟩,
    fun V _ _ C _ S u hu0 hu => ?_, fun Ωc _ μ _ w q hw hqm hw0 τ hτ hq hwτ => ?_⟩
  · obtain ⟨hp, hs, hser, -, -, hle⟩ := S.prop115 u hu0 hu
    refine ⟨⟨hp, hs, hser, hle⟩, fun h0 h1 θ => ⟨(S.prop115_max_iff u hu0 hu h0 h1 θ).2, ?_⟩⟩
    intro hmax detM hM
    exact S.theta_bar_zero u hu0 hu h0 h1 θ hmax detM hM
  · refine ⟨Zint_sector_series w q hw hqm, fun n hn => aSector_pos w q hw hqm hw0 n hn,
      fun n => aSector_symm w q hqm τ hτ hq hwτ n, fun θ => Zint_norm_le w q (fun U => (hw0 U).le) θ,
      fun h0 h1 θ => ⟨Zint_max_iff w q hw hqm hw0 τ hτ hq hwτ h0 h1 θ, ?_⟩⟩
    intro hmax detM hM
    exact theta_bar_zero_integral w q hw hqm hw0 τ hτ hq hwτ h0 h1 θ hmax detM hM

end Comparison.System
