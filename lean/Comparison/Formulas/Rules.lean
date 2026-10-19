import Comparison.Law.Rows
import Comparison.Colour.GramTerm

/-!
# The rules of the law as the gap varies (formulas (67) to (73))

`Law/Rule.lean` carries the
rule at all 64 divided sets (`PsiS_eq`, `norm_wS`, `eS_add_tS`, `NS_turns`) and `RuleAndLaw/FactorsA.lean` its classes; added here:

* `rule_signed_return` (67): **`Ψ_S = −Φ(4w_S)/(16w_S²)`** at every divided set: the association is the
  law's own signed first return read at the divided set's step.
* `sqrt_three_rule` (69): **`√3 = e@{t}^{−1/2}`**, `e@{t} = 1/3`.
* `clock_spread_is_excursion` (70): **`Var D = [(Var P − Var Q)² + 4Cov²]/(3Eℓ)² = 61/16` and
  `E_D = (Var P + Var Q)/(3Eℓ) = 2`**, with the excursion's moments as Lean computes them
  (`excursionVarP`, `excursionVarQ`, `excursionCov`, `excursionEl`); `clock_sweep_limit`: **`−log h(ν)/ν² → (3/2) Var D`**
  as `ν → 0`, `h(ν) = [M_Q(ν)M_Q(−ν)]^{−3/2}` (`clockTilt`), with the two-sided bounds
  `clock_pair_bounds` at every `ν`; `hOv_is_tilt`: the clock's `h` is `h(ν)` at `ν = 9/4000`.
* `detF0_is_transmission` (71): **`det F₀ = t@{} = 2/5`**.
* `W_minor` (73): **`W = det_C(t@{h,n}^{Eℓ} η^{E_H}) = (2/5)⁴⁸(295/296)⁹`**, the `3 × 3` diagonal minor on
  the lines of `C`.
-/

namespace Comparison.Formulas

open Comparison.Law Filter Topology

/-! ## (67) The one rule is the law's signed return -/

theorem wS_ne_zero (S : Finset (Fin 6)) : wS S ≠ 0 := by
  rw [wS]
  exact div_ne_zero (by rw [zS]; exact pow_ne_zero _ Complex.I_ne_zero) (LS_ne_zero S)

/-- **(67) The association is the law's own signed first return read at the divided set's step:**
`Ψ_S = −Φ(4w_S)/(16w_S²)`. -/
theorem rule_signed_return (S : Finset (Fin 6)) :
    PsiS S = -Phi (4 * wS S) / (16 * wS S ^ 2) := by
  have hw := wS_ne_zero S
  have hL := LS_ne_zero S
  have hden : LS S ^ 2 + 3 * (signS S : ℂ) ≠ 0 := by
    rw [LS_eq_LZ]
    exact_mod_cast LZ_sq_add_ne S
  have h1 : 1 + 3 * wS S ^ 2 ≠ 0 := by
    rw [wS_sq]
    intro h
    apply hden
    have e : 1 + 3 * ((signS S : ℂ) / LS S ^ 2) = (LS S ^ 2 + 3 * (signS S : ℂ)) / LS S ^ 2 := by
      field_simp
    rw [e] at h
    exact (div_eq_zero_iff.mp h).resolve_right (pow_ne_zero _ hL)
  rw [PsiS, Psi, Phi]
  have e1 : (4 * wS S) ^ 4 = 256 * wS S ^ 4 := by ring
  have e2 : (16 : ℂ) + 3 * (4 * wS S) ^ 2 = 16 * (1 + 3 * wS S ^ 2) := by ring
  rw [e1, e2]
  field_simp
  ring

/-! ## (69) The factor per two-spinor state -/

theorem eS_line : eS sLine = 1 / 3 := by
  have hL : LZ sLine = 3 := by decide
  rw [eS, norm_wS, hL]
  norm_num

/-- **(69) `√3 = e@{t}^{−1/2}`.** -/
theorem sqrt_three_rule : eS sLine ^ (-(1 / 2 : ℝ)) = Real.sqrt 3 := by
  rw [eS_line, show (1 / 3 : ℝ) = 3⁻¹ by norm_num, Real.inv_rpow (by norm_num),
    Real.rpow_neg (by norm_num), inv_inv, Real.sqrt_eq_rpow]

/-! ## (70) The clock's spread is the excursion's -/

/-- `Var P`, `Var Q`, `Cov(P, Q)` and `Eℓ` of one excursion, as the derivatives of its generating function. -/
noncomputable def excursionVarP : ℝ :=
  deriv (deriv (fun y => excursionF 1 1 y)) 1 + deriv (fun y => excursionF 1 1 y) 1 -
    (deriv (fun y => excursionF 1 1 y) 1) ^ 2

noncomputable def excursionVarQ : ℝ :=
  deriv (deriv (fun x => excursionF 1 x 1)) 1 + deriv (fun x => excursionF 1 x 1) 1 -
    (deriv (fun x => excursionF 1 x 1) 1) ^ 2

noncomputable def excursionCov : ℝ :=
  deriv (fun x => deriv (fun y => excursionF 1 x y) 1) 1 -
    deriv (fun y => excursionF 1 1 y) 1 * deriv (fun x => excursionF 1 x 1) 1

noncomputable def excursionEl : ℝ := deriv (fun z => excursionF z 1 1) 1

theorem excursion_moment_values : excursionVarP = 84 ∧ excursionVarQ = 12 ∧ excursionCov = 30 ∧ excursionEl = 16 := by
  obtain ⟨h1, h2, h3, -⟩ := visit_moments
  exact ⟨h1, h2, h3, El_eq⟩

/-- **(70) The clock's spread and mean are the excursion's:**
`Var D = [(Var P − Var Q)² + 4Cov²]/(3Eℓ)² = 61/16`, `E_D = (Var P + Var Q)/(3Eℓ) = 2`. -/
theorem clock_spread_is_excursion :
    (1 / 10) * ∑ i, clockGap sLastDirectionSinglet i ^ 2 - ((1 / 10) * ∑ i, clockGap sLastDirectionSinglet i) ^ 2 =
        ((excursionVarP - excursionVarQ) ^ 2 + 4 * excursionCov ^ 2) / (3 * excursionEl) ^ 2 ∧
      (1 / 10) * ∑ i, clockGap sLastDirectionSinglet i = (excursionVarP + excursionVarQ) / (3 * excursionEl) ∧
      ((excursionVarP - excursionVarQ) ^ 2 + 4 * excursionCov ^ 2) / (3 * excursionEl) ^ 2 = 61 / 16 := by
  obtain ⟨hP, hQ, hC, hE⟩ := excursion_moment_values
  obtain ⟨m1, m2⟩ := clock_moments
  rw [hP, hQ, hC, hE, m1]
  refine ⟨?_, by norm_num, by norm_num⟩
  norm_num at m2 ⊢
  linarith

/-! ## (70) The clock as its tilt varies -/

/-- The clock's two tilts, `P(ν) = M_Q(ν) M_Q(−ν)`. -/
noncomputable def clockPair (ν : ℝ) : ℝ := clockMQ sLastDirectionSinglet ν * clockMQ sLastDirectionSinglet (-ν)

/-- The clock's overlap as a function of the tilt, `h(ν) = [M_Q(ν)M_Q(−ν)]^{−3/2}`. -/
noncomputable def clockTilt (ν : ℝ) : ℝ := clockPair ν ^ (-(3 / 2 : ℝ))

/-- The clock's `h` is that overlap at the clock's own rate `ν = 9/4000`. -/
theorem hOv_is_tilt : hOv sLastDirectionSinglet = clockTilt (9 / 4000) := by
  rw [hOv, clockTilt, clockPair, piece_nu_hn]
  congr 2
  · rw [show signS sLastDirectionSinglet = 1 by decide]
    norm_num
  · rw [show signS (twin sLastDirectionSinglet) = -1 by decide]
    norm_num

/-- `e^t − 1 ≤ t e^t`. -/
theorem exp_sub_one_le' (t : ℝ) : Real.exp t - 1 ≤ t * Real.exp t := by
  have h := Real.add_one_le_exp (-t)
  have hpos := Real.exp_pos t
  have e : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h2 := mul_le_mul_of_nonneg_right h hpos.le
  rw [e] at h2
  linarith

/-- `y²/2 ≤ cosh y − 1 ≤ (y²/2) e^{y²/2}`. -/
theorem cosh_sub_one_bounds (y : ℝ) :
    y ^ 2 / 2 ≤ Real.cosh y - 1 ∧ Real.cosh y - 1 ≤ y ^ 2 / 2 * Real.exp (y ^ 2 / 2) := by
  constructor
  · have h1 : Real.cosh |y| = 1 + 2 * Real.sinh (|y| / 2) ^ 2 := by
      have := Real.cosh_two_mul (|y| / 2)
      rw [show 2 * (|y| / 2) = |y| by ring] at this
      rw [this, Real.cosh_sq]
      ring
    have h2 : |y| / 2 ≤ Real.sinh (|y| / 2) := Real.self_le_sinh_iff.mpr (by positivity)
    have h3 : (|y| / 2) ^ 2 ≤ Real.sinh (|y| / 2) ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
    rw [← Real.cosh_abs, h1]
    have : |y| ^ 2 = y ^ 2 := sq_abs y
    nlinarith [h3]
  · have h1 := Real.cosh_le_exp_half_sq y
    have h2 := exp_sub_one_le' (y ^ 2 / 2)
    linarith

/-- The ten gaps lie in `[1/4, 19/4]`. -/
theorem clockGap_range (i : Fin 10) : 1 / 4 ≤ clockGap sLastDirectionSinglet i ∧ clockGap sLastDirectionSinglet i ≤ 19 / 4 := by
  rw [clockGap_hn]
  fin_cases i <;> norm_num

/-- `P(ν) = (1/100) Σ_{i,j} cosh(ν(g_j − g_i))`. -/
theorem clockPair_cosh (ν : ℝ) :
    clockPair ν = (1 / 100) * ∑ i, ∑ j,
      Real.cosh (ν * (clockGap sLastDirectionSinglet j - clockGap sLastDirectionSinglet i)) := by
  have hexp : clockPair ν = (1 / 100) * ∑ i, ∑ j,
      Real.exp (ν * (clockGap sLastDirectionSinglet j - clockGap sLastDirectionSinglet i)) := by
    rw [clockPair, clockMQ, clockMQ, mul_mul_mul_comm, Finset.sum_mul_sum]
    congr 1
    · norm_num
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [← Real.exp_add]
      congr 1
      ring
  have hswap : (∑ i, ∑ j, Real.exp (ν * (clockGap sLastDirectionSinglet j - clockGap sLastDirectionSinglet i))) =
      ∑ i, ∑ j, Real.exp (-(ν * (clockGap sLastDirectionSinglet j - clockGap sLastDirectionSinglet i))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    congr 1
    ring
  have h2 : 2 * (∑ i, ∑ j, Real.cosh (ν * (clockGap sLastDirectionSinglet j - clockGap sLastDirectionSinglet i))) =
      (∑ i, ∑ j, Real.exp (ν * (clockGap sLastDirectionSinglet j - clockGap sLastDirectionSinglet i))) +
        ∑ i, ∑ j, Real.exp (-(ν * (clockGap sLastDirectionSinglet j - clockGap sLastDirectionSinglet i))) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Real.cosh_eq]
    ring
  rw [hexp]
  congr 1
  linarith [h2, hswap]

/-- `(1/100) Σ_{i,j} (g_j − g_i)²/2 = Var D = 61/16`. -/
theorem clock_pair_variance :
    (1 / 100) * ∑ i, ∑ j, (clockGap sLastDirectionSinglet j - clockGap sLastDirectionSinglet i) ^ 2 / 2 = 61 / 16 := by
  simp only [clockGap_hn, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num

/-- **The clock's two tilts, bounded at every `ν`:**
`(61/16)ν² ≤ P(ν) − 1 ≤ (61/16)ν² e^{81ν²/8}`. -/
theorem clock_pair_bounds (ν : ℝ) :
    61 / 16 * ν ^ 2 ≤ clockPair ν - 1 ∧ clockPair ν - 1 ≤ 61 / 16 * ν ^ 2 * Real.exp (81 * ν ^ 2 / 8) := by
  set d : Fin 10 → Fin 10 → ℝ := fun i j => clockGap sLastDirectionSinglet j - clockGap sLastDirectionSinglet i with hd
  have hsum1 : (∑ _i : Fin 10, ∑ _j : Fin 10, (1 : ℝ)) = 100 := by simp; norm_num
  have hP : clockPair ν - 1 = (1 / 100) * ∑ i, ∑ j, (Real.cosh (ν * d i j) - 1) := by
    rw [clockPair_cosh]
    simp only [Finset.sum_sub_distrib, hsum1, hd]
    ring
  have hV : (1 / 100) * ∑ i, ∑ j, (ν * d i j) ^ 2 / 2 = 61 / 16 * ν ^ 2 := by
    have := clock_pair_variance
    have e : ∀ i j, (ν * d i j) ^ 2 / 2 = ν ^ 2 * ((clockGap sLastDirectionSinglet j - clockGap sLastDirectionSinglet i) ^ 2 / 2) :=
      fun i j => by rw [hd]; ring
    simp only [e, ← Finset.mul_sum]
    rw [← this]
    ring
  have hdbound : ∀ i j, (ν * d i j) ^ 2 ≤ 81 / 4 * ν ^ 2 := by
    intro i j
    obtain ⟨a1, a2⟩ := clockGap_range i
    obtain ⟨b1, b2⟩ := clockGap_range j
    have hdd : d i j ^ 2 ≤ 81 / 4 := by
      rw [hd]
      nlinarith
    rw [mul_pow]
    nlinarith [sq_nonneg ν]
  constructor
  · rw [hP, ← hV]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => (cosh_sub_one_bounds _).1
  · rw [hP]
    have hterm : ∀ i j, Real.cosh (ν * d i j) - 1 ≤
        (ν * d i j) ^ 2 / 2 * Real.exp (81 * ν ^ 2 / 8) := by
      intro i j
      have h1 := (cosh_sub_one_bounds (ν * d i j)).2
      have h2 : Real.exp ((ν * d i j) ^ 2 / 2) ≤ Real.exp (81 * ν ^ 2 / 8) :=
        Real.exp_le_exp.mpr (by nlinarith [hdbound i j])
      have h3 : (ν * d i j) ^ 2 / 2 * Real.exp ((ν * d i j) ^ 2 / 2) ≤
          (ν * d i j) ^ 2 / 2 * Real.exp (81 * ν ^ 2 / 8) :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      linarith
    calc (1 / 100) * ∑ i, ∑ j, (Real.cosh (ν * d i j) - 1)
        ≤ (1 / 100) * ∑ i, ∑ j, ((ν * d i j) ^ 2 / 2 * Real.exp (81 * ν ^ 2 / 8)) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j) (by norm_num)
      _ = ((1 / 100) * ∑ i, ∑ j, (ν * d i j) ^ 2 / 2) * Real.exp (81 * ν ^ 2 / 8) := by
          simp only [← Finset.sum_mul]
          ring
      _ = 61 / 16 * ν ^ 2 * Real.exp (81 * ν ^ 2 / 8) := by rw [hV]

/-- **(70) The clock as its tilt varies:** `−log h(ν)/ν² → (3/2) Var D = (3/2)(61/16)` as `ν → 0`. -/
theorem clock_sweep_limit :
    Tendsto (fun ν : ℝ => -Real.log (clockTilt ν) / ν ^ 2) (𝓝[≠] 0) (𝓝 (3 / 2 * (61 / 16))) := by
  set V : ℝ := 61 / 16 with hVdef
  -- the two bounds of log P(ν)/ν²
  have hlog : ∀ ν : ℝ, ν ≠ 0 →
      V - V ^ 2 * ν ^ 2 * Real.exp (81 * ν ^ 2 / 4) ≤ Real.log (clockPair ν) / ν ^ 2 ∧
        Real.log (clockPair ν) / ν ^ 2 ≤ V * Real.exp (81 * ν ^ 2 / 8) := by
    intro ν hν
    obtain ⟨lo, hi⟩ := clock_pair_bounds ν
    have hν2 : 0 < ν ^ 2 := by positivity
    set X := clockPair ν - 1 with hX
    have hX0 : 0 ≤ X := le_trans (by positivity) lo
    have hPpos : 0 < clockPair ν := by linarith
    have hup : Real.log (clockPair ν) ≤ X := by
      have := Real.log_le_sub_one_of_pos hPpos
      linarith
    have hlow : X - X ^ 2 ≤ Real.log (clockPair ν) := by
      have h1 := Real.one_sub_inv_le_log_of_pos hPpos
      have h2 : X - X ^ 2 ≤ 1 - (clockPair ν)⁻¹ := by
        have e : 1 - (clockPair ν)⁻¹ = X / (1 + X) := by
          rw [show (1 : ℝ) + X = clockPair ν by rw [hX]; ring, hX, sub_div, div_self hPpos.ne',
            one_div]
        rw [e, le_div_iff₀ (by linarith)]
        nlinarith [sq_nonneg X, mul_nonneg hX0 (sq_nonneg X)]
      linarith
    have hE8 : 0 < Real.exp (81 * ν ^ 2 / 8) := Real.exp_pos _
    have hXsq : X ^ 2 ≤ V ^ 2 * ν ^ 4 * Real.exp (81 * ν ^ 2 / 4) := by
      have h1 : X ^ 2 ≤ (V * ν ^ 2 * Real.exp (81 * ν ^ 2 / 8)) ^ 2 :=
        pow_le_pow_left₀ hX0 hi 2
      have h2 : (V * ν ^ 2 * Real.exp (81 * ν ^ 2 / 8)) ^ 2 = V ^ 2 * ν ^ 4 * Real.exp (81 * ν ^ 2 / 4) := by
        rw [mul_pow, mul_pow, ← Real.exp_nat_mul]
        congr 2
        · ring
        · push_cast
          ring
      linarith
    constructor
    · rw [le_div_iff₀ hν2]
      have : V * ν ^ 2 - V ^ 2 * ν ^ 4 * Real.exp (81 * ν ^ 2 / 4) ≤ Real.log (clockPair ν) := by
        linarith
      nlinarith [this]
    · rw [div_le_iff₀ hν2]
      linarith
  -- the squeeze
  have hlimL : Tendsto (fun ν : ℝ => V - V ^ 2 * ν ^ 2 * Real.exp (81 * ν ^ 2 / 4)) (𝓝[≠] 0) (𝓝 V) := by
    have hc : Continuous (fun ν : ℝ => V - V ^ 2 * ν ^ 2 * Real.exp (81 * ν ^ 2 / 4)) := by fun_prop
    have h0 := hc.tendsto 0
    have h1 : V - V ^ 2 * (0 : ℝ) ^ 2 * Real.exp (81 * (0 : ℝ) ^ 2 / 4) = V := by simp
    rw [h1] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hlimU : Tendsto (fun ν : ℝ => V * Real.exp (81 * ν ^ 2 / 8)) (𝓝[≠] 0) (𝓝 V) := by
    have hc : Continuous (fun ν : ℝ => V * Real.exp (81 * ν ^ 2 / 8)) := by fun_prop
    have h0 := hc.tendsto 0
    have h1 : V * Real.exp (81 * (0 : ℝ) ^ 2 / 8) = V := by simp
    rw [h1] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hmain : Tendsto (fun ν : ℝ => Real.log (clockPair ν) / ν ^ 2) (𝓝[≠] 0) (𝓝 V) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlimL hlimU ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ν hν
      exact (hlog ν hν).1
    · filter_upwards [self_mem_nhdsWithin] with ν hν
      exact (hlog ν hν).2
  have hscaled := hmain.const_mul (3 / 2)
  refine Tendsto.congr' ?_ hscaled
  filter_upwards [self_mem_nhdsWithin] with ν hν
  have hPpos : 0 < clockPair ν := by
    have := (clock_pair_bounds ν).1
    nlinarith [sq_nonneg ν]
  rw [clockTilt, Real.log_rpow hPpos]
  ring

/-! ## (71) and (73) -/

/-- **(71) `det F₀ = t@{} = 2/5`.** -/
theorem detF0_is_transmission :
    ((((4 / 5 : ℚ) • gram3).det : ℚ) : ℝ) = tS sHere ∧ tS sHere = 2 / 5 := by
  have ht : tS sHere = 2 / 5 := by
    have hL : LZ sHere = 5 := by decide
    rw [tS, norm_wS, hL]
    norm_num
  refine ⟨?_, ht⟩
  rw [det_F0.1, ht]
  norm_num

theorem tS_hn : tS sLastDirectionSinglet = 2 / 5 := by
  have h := eS_add_tS sLastDirectionSinglet
  rw [eS_hn] at h
  linarith

/-- **(73) Gravity's amplitude as the minor on the word `C`:**
`W = det_C(t@{h,n}^{Eℓ} η^{E_H}) = (2/5)⁴⁸(295/296)⁹`, one typical excursion (`Eℓ = 16` steps, `E_H = 3`
transitions along the last-step direction) on each of the three lines outside the plane. -/
theorem W_minor :
    (Matrix.diagonal fun _ : sC => tS sLastDirectionSinglet ^ 16 * (295 / 296 : ℝ) ^ 3).det =
      (2 / 5 : ℝ) ^ 48 * (295 / 296) ^ 9 := by
  rw [Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, tS_hn]
  have hc : Fintype.card sC = 3 := by
    rw [Fintype.card_coe]
    decide
  rw [hc]
  ring

end Comparison.Formulas
