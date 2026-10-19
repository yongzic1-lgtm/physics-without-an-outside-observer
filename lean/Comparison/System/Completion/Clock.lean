import Comparison.System.Completion.Numbers
import Comparison.Formulas.Rules
import Comparison.Law.Rows
import Comparison.Law.Composite
import Comparison.Mass.Perron
import Comparison.RuleAndLaw.FactorsB

set_option linter.style.longLine false

/-!
# The proof system, the completions, part 9: the clock's overlap to fourth order (SI Prop. 206)

`−log h(ν) = (3/2)Var D ν² + O(ν⁴)` as a bound: the overlap as the tilt varies
`h(ν) = [M_Q(ν)M_Q(−ν)]^{−3/2}` with `M_Q(ν)M_Q(−ν) = (1/100)Σ_{i,j}e^{ν(D_j − D_i)}`, whose odd moments vanish by the
exchange of the two gaps.
-/

namespace Comparison.System.Completion.Comp

open Real Filter Topology Asymptotics Comparison Comparison.Law

/-- A double sum of an antisymmetric array vanishes. -/
theorem sum_antisymm {ι : Type*} [Fintype ι] (f : ι → ι → ℝ) (hf : ∀ i j, f j i = -f i j) :
    ∑ i, ∑ j, f i j = 0 := by
  have h1 : ∑ i, ∑ j, f i j = ∑ j, ∑ i, f i j := Finset.sum_comm
  have h2 : ∑ j, ∑ i, f i j = -∑ j, ∑ i, f j i := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun i _ => hf j i
  linarith

/-- `M_Q(ν)M_Q(−ν) = (1/100)Σ_{i,j}e^{ν(D_j − D_i)}`. -/
theorem clockPair_sum (ν : ℝ) : Formulas.clockPair ν =
    (1 / 100) * ∑ i : Fin 10, ∑ j : Fin 10, Real.exp (ν * (clockGap sLastDirectionSinglet j - clockGap sLastDirectionSinglet i)) := by
  rw [Formulas.clockPair, clockMQ, clockMQ]
  rw [show (1 / 10 : ℝ) * (∑ i, Real.exp (-(ν * clockGap sLastDirectionSinglet i))) *
        ((1 / 10) * ∑ i, Real.exp (-(-ν * clockGap sLastDirectionSinglet i))) =
      (1 / 100) * ((∑ i, Real.exp (-(ν * clockGap sLastDirectionSinglet i))) *
        ∑ i, Real.exp (-(-ν * clockGap sLastDirectionSinglet i))) by ring, Finset.sum_mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Real.exp_add]
  congr 1
  ring

theorem gap_bounds : ∀ i : Fin 10, 1 / 4 ≤ clockGap sLastDirectionSinglet i ∧ clockGap sLastDirectionSinglet i ≤ 19 / 4 := by
  intro i
  rw [clockGap_hn]
  fin_cases i <;> simp <;> norm_num

/-- `Σ_{i,j}(D_j − D_i)² = 2·100·Var D = 1525/2`. -/
theorem gap_square_sum :
    ∑ i : Fin 10, ∑ j : Fin 10, (clockGap sLastDirectionSinglet j - clockGap sLastDirectionSinglet i) ^ 2 = 1525 / 2 := by
  simp only [clockGap_hn, Fin.sum_univ_succ, Fin.sum_univ_zero]
  norm_num

/-- The cubic Taylor polynomial of `e^x` summed over the pairs of an array: `100 + ν²Σ(D_j − D_i)²/2`. -/
theorem pair_taylor_sum (D : Fin 10 → ℝ) (ν s2 : ℝ) (h2 : ∑ i, ∑ j, (D j - D i) ^ 2 = s2) :
    ∑ i, ∑ j, (1 + ν * (D j - D i) + (ν * (D j - D i)) ^ 2 / 2 + (ν * (D j - D i)) ^ 3 / 6) =
      100 + ν ^ 2 * s2 / 2 := by
  have a1 : ∑ i, ∑ j, ν * (D j - D i) = 0 :=
    sum_antisymm (fun i j => ν * (D j - D i)) (fun i j => by beta_reduce; ring)
  have a3 : ∑ i, ∑ j, (ν * (D j - D i)) ^ 3 = 0 :=
    sum_antisymm (fun i j => (ν * (D j - D i)) ^ 3) (fun i j => by beta_reduce; ring)
  have a2 : ∑ i, ∑ j, (ν * (D j - D i)) ^ 2 = ν ^ 2 * s2 := by
    rw [← h2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have lin : ∑ i, ∑ j, (1 + ν * (D j - D i) + (ν * (D j - D i)) ^ 2 / 2 + (ν * (D j - D i)) ^ 3 / 6) =
      ∑ _i : Fin 10, ∑ _j : Fin 10, (1 : ℝ) + ∑ i, ∑ j, ν * (D j - D i) +
        (∑ i, ∑ j, (ν * (D j - D i)) ^ 2) / 2 + (∑ i, ∑ j, (ν * (D j - D i)) ^ 3) / 6 := by
    simp only [Finset.sum_add_distrib, Finset.sum_div]
  rw [lin, a1, a2, a3]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- **The fourth-order bound for an array of gaps in `[1/4, 19/4]`.** -/
theorem pair_near (D : Fin 10 → ℝ) (hDb : ∀ i j, |D j - D i| ≤ 19 / 4)
    (h2 : ∑ i, ∑ j, (D j - D i) ^ 2 = 1525 / 2) (ν : ℝ) (hν : |ν| ≤ 1 / 5) :
    |(1 / 100) * ∑ i, ∑ j, Real.exp (ν * (D j - D i)) - 1 - 61 / 16 * ν ^ 2| ≤ 27 * ν ^ 4 := by
  have hT : ∀ i j, |Real.exp (ν * (D j - D i)) - (1 + ν * (D j - D i) + (ν * (D j - D i)) ^ 2 / 2 +
      (ν * (D j - D i)) ^ 3 / 6)| ≤ (ν * (D j - D i)) ^ 4 * (5 / 96) := by
    intro i j
    have hx : |ν * (D j - D i)| ≤ 1 := by
      rw [abs_mul]
      have h1 := hDb i j
      have h2 := abs_nonneg ν
      have h3 := abs_nonneg (D j - D i)
      nlinarith
    have hb := Article.exp_near (ν * (D j - D i)) 4 (by norm_num) hx
    have eP : Article.expPoly (ν * (D j - D i)) 4 =
        1 + ν * (D j - D i) + (ν * (D j - D i)) ^ 2 / 2 + (ν * (D j - D i)) ^ 3 / 6 := by
      norm_num [Article.expPoly, Finset.sum_range_succ, Nat.factorial] <;> ring
    have eE : Article.expErr (ν * (D j - D i)) 4 = (ν * (D j - D i)) ^ 4 * (5 / 96) := by
      rw [Article.expErr, ← abs_pow, abs_of_nonneg (by positivity)]
      norm_num [Nat.factorial]
    rw [eP, eE] at hb
    exact hb
  have hsum : (1 / 100) * ∑ i, ∑ j, Real.exp (ν * (D j - D i)) - 1 - 61 / 16 * ν ^ 2 =
      (1 / 100) * ∑ i, ∑ j, (Real.exp (ν * (D j - D i)) - (1 + ν * (D j - D i) +
        (ν * (D j - D i)) ^ 2 / 2 + (ν * (D j - D i)) ^ 3 / 6)) := by
    have hP := pair_taylor_sum D ν (1525 / 2) h2
    simp only [Finset.sum_sub_distrib]
    rw [hP]
    ring
  rw [hsum, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 100)]
  have hbound : |∑ i, ∑ j, (Real.exp (ν * (D j - D i)) - (1 + ν * (D j - D i) +
        (ν * (D j - D i)) ^ 2 / 2 + (ν * (D j - D i)) ^ 3 / 6))| ≤
      ∑ _i : Fin 10, ∑ _j : Fin 10, (19 / 4 : ℝ) ^ 4 * ν ^ 4 * (5 / 96) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    refine (hT i j).trans ?_
    have h4 : (ν * (D j - D i)) ^ 4 ≤ (19 / 4) ^ 4 * ν ^ 4 := by
      rw [mul_pow, mul_comm]
      have h5 : (D j - D i) ^ 4 ≤ (19 / 4) ^ 4 := by
        rw [show (D j - D i) ^ 4 = |D j - D i| ^ 4 by rw [← abs_pow, abs_of_nonneg (by positivity)]]
        exact pow_le_pow_left₀ (abs_nonneg _) (hDb i j) 4
      exact mul_le_mul_of_nonneg_right h5 (by positivity)
    nlinarith
  have hcount : ∑ _i : Fin 10, ∑ _j : Fin 10, (19 / 4 : ℝ) ^ 4 * ν ^ 4 * (5 / 96) =
      100 * ((19 / 4) ^ 4 * ν ^ 4 * (5 / 96)) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hcount] at hbound
  have hν4 : 0 ≤ ν ^ 4 := by positivity
  nlinarith

/-- **The clock's pair to fourth order:** for `|ν| ≤ 1/5`, `|M_Q(ν)M_Q(−ν) − 1 − (61/16)ν²| ≤ 27ν⁴`. -/
theorem clockPair_near (ν : ℝ) (hν : |ν| ≤ 1 / 5) :
    |Formulas.clockPair ν - 1 - 61 / 16 * ν ^ 2| ≤ 27 * ν ^ 4 := by
  rw [clockPair_sum]
  refine pair_near (clockGap sLastDirectionSinglet) (fun i j => ?_) gap_square_sum ν hν
  have hi := gap_bounds i
  have hj := gap_bounds j
  rw [abs_le]
  constructor <;> linarith [hi.1, hi.2, hj.1, hj.2]

/-- **`−log h(ν) = (3/2)Var D ν² + O(ν⁴)`.** -/
theorem minus_log_tilt :
    (fun ν : ℝ => -Real.log (Formulas.clockTilt ν) - 3 / 2 * (61 / 16) * ν ^ 2) =O[𝓝 0] (fun ν : ℝ => ν ^ 4) := by
  have hpos : ∀ ν : ℝ, 0 < Formulas.clockPair ν := fun ν =>
    mul_pos (RuleAndLaw.clockMQ_pos ν) (RuleAndLaw.clockMQ_pos (-ν))
  have hnear : ∀ᶠ ν in 𝓝 (0 : ℝ), |ν| ≤ 1 / 5 := by
    have : Set.Icc (-(1 / 5 : ℝ)) (1 / 5) ∈ 𝓝 (0 : ℝ) := Icc_mem_nhds (by norm_num) (by norm_num)
    filter_upwards [this] with ν hν
    exact abs_le.mpr hν
  have hP : (fun ν : ℝ => Formulas.clockPair ν - 1 - 61 / 16 * ν ^ 2) =O[𝓝 0] (fun ν : ℝ => ν ^ 4) := by
    refine Asymptotics.IsBigO.of_bound 27 ?_
    filter_upwards [hnear] with ν hν
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ν ^ 4)]
    exact clockPair_near ν hν
  have h42 : (fun ν : ℝ => ν ^ 4) =O[𝓝 0] (fun ν : ℝ => ν ^ 2) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [hnear] with ν hν
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ν ^ 4),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ν ^ 2), one_mul]
    have h1 : ν ^ 2 ≤ 1 := by
      have := sq_abs ν
      nlinarith [abs_nonneg ν]
    nlinarith [sq_nonneg ν]
  have hy : (fun ν : ℝ => Formulas.clockPair ν - 1) =O[𝓝 0] (fun ν : ℝ => ν ^ 2) := by
    have e : (fun ν : ℝ => Formulas.clockPair ν - 1) =
        fun ν => (Formulas.clockPair ν - 1 - 61 / 16 * ν ^ 2) + 61 / 16 * ν ^ 2 := by
      funext ν; ring
    rw [e]
    exact (hP.trans h42).add ((Asymptotics.isBigO_refl (fun ν : ℝ => ν ^ 2) (𝓝 0)).const_mul_left (61 / 16))
  have hy0 : Tendsto (fun ν : ℝ => Formulas.clockPair ν - 1) (𝓝 0) (𝓝 0) := by
    refine hy.trans_tendsto ?_
    have := (continuous_pow 2).tendsto (0 : ℝ)
    simpa using this
  have hlog : (fun ν : ℝ => Real.log (Formulas.clockPair ν) - (Formulas.clockPair ν - 1)) =O[𝓝 0]
      (fun ν : ℝ => (Formulas.clockPair ν - 1) ^ 2) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    have hsmall : ∀ᶠ ν in 𝓝 (0 : ℝ), |Formulas.clockPair ν - 1| ≤ 1 / 4 := by
      have := hy0.eventually (Metric.closedBall_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 4))
      filter_upwards [this] with ν hν
      simpa [Metric.mem_closedBall, Real.dist_eq] using hν
    filter_upwards [hsmall] with ν hν
    have hb := abs_log_one_add_sub_le (Formulas.clockPair ν - 1) (by linarith)
    have e : (1 : ℝ) + (Formulas.clockPair ν - 1) = Formulas.clockPair ν := by ring
    rw [e] at hb
    rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_of_nonneg (sq_nonneg (Formulas.clockPair ν - 1))]
    have hz := abs_nonneg (Formulas.clockPair ν - 1)
    have hsq : |Formulas.clockPair ν - 1| ^ 2 = (Formulas.clockPair ν - 1) ^ 2 := sq_abs _
    have h3 : |Formulas.clockPair ν - 1| ^ 3 ≤ |Formulas.clockPair ν - 1| ^ 2 / 4 := by
      have : |Formulas.clockPair ν - 1| ^ 3 = |Formulas.clockPair ν - 1| * |Formulas.clockPair ν - 1| ^ 2 := by ring
      rw [this]
      nlinarith [sq_nonneg (|Formulas.clockPair ν - 1|)]
    have htri : |Real.log (Formulas.clockPair ν) - (Formulas.clockPair ν - 1)| ≤
        |Real.log (Formulas.clockPair ν) - ((Formulas.clockPair ν - 1) - (Formulas.clockPair ν - 1) ^ 2 / 2)| +
          (Formulas.clockPair ν - 1) ^ 2 / 2 := by
      have := abs_sub_le (Real.log (Formulas.clockPair ν))
        ((Formulas.clockPair ν - 1) - (Formulas.clockPair ν - 1) ^ 2 / 2) (Formulas.clockPair ν - 1)
      have e2 : |(Formulas.clockPair ν - 1) - (Formulas.clockPair ν - 1) ^ 2 / 2 - (Formulas.clockPair ν - 1)| =
          (Formulas.clockPair ν - 1) ^ 2 / 2 := by
        rw [show (Formulas.clockPair ν - 1) - (Formulas.clockPair ν - 1) ^ 2 / 2 - (Formulas.clockPair ν - 1) =
          -((Formulas.clockPair ν - 1) ^ 2 / 2) by ring, abs_neg, abs_of_nonneg (by positivity)]
      linarith
    nlinarith
  have hlog4 : (fun ν : ℝ => Real.log (Formulas.clockPair ν) - 61 / 16 * ν ^ 2) =O[𝓝 0] (fun ν : ℝ => ν ^ 4) := by
    have e : (fun ν : ℝ => Real.log (Formulas.clockPair ν) - 61 / 16 * ν ^ 2) =
        fun ν => (Real.log (Formulas.clockPair ν) - (Formulas.clockPair ν - 1)) +
          (Formulas.clockPair ν - 1 - 61 / 16 * ν ^ 2) := by
      funext ν; ring
    rw [e]
    have hsq : (fun ν : ℝ => (Formulas.clockPair ν - 1) ^ 2) =O[𝓝 0] (fun ν : ℝ => ν ^ 4) := by
      have h := hy.pow 2
      have e4 : (fun ν : ℝ => (ν ^ 2) ^ 2) = fun ν : ℝ => ν ^ 4 := by
        funext ν
        ring
      simpa only [e4] using h
    exact (hlog.trans hsq).add hP
  have e : (fun ν : ℝ => -Real.log (Formulas.clockTilt ν) - 3 / 2 * (61 / 16) * ν ^ 2) =
      fun ν => (3 / 2 : ℝ) * (Real.log (Formulas.clockPair ν) - 61 / 16 * ν ^ 2) := by
    funext ν
    rw [Formulas.clockTilt, Real.log_rpow (hpos ν)]
    ring
  rw [e]
  exact hlog4.const_mul_left (3 / 2)

end Comparison.System.Completion.Comp

namespace Comparison.System

open Real Filter Topology Asymptotics Comparison Comparison.Law

/-- **Proposition 206, the fourth order.** `−log h(ν) = k_C·(1/2)[c_Q(ν) + c_Q(−ν)] = (3/2)Var D ν² + O(ν⁴)`,
`c_Q = log M_Q`, `Var D = 61/16`: for `|ν| ≤ 1/5`, `|M_Q(ν)M_Q(−ν) − 1 − (61/16)ν²| ≤ 27ν⁴`, and the remainder of
`−log h` is `O(ν⁴)`. -/
theorem Completion.Comp.clock_fourth_order :
    (∀ ν : ℝ, -Real.log (Formulas.clockTilt ν) =
      3 / 2 * (Real.log (clockMQ sLastDirectionSinglet ν) + Real.log (clockMQ sLastDirectionSinglet (-ν)))) ∧
    (∀ ν : ℝ, |ν| ≤ 1 / 5 → |Formulas.clockPair ν - 1 - 61 / 16 * ν ^ 2| ≤ 27 * ν ^ 4) ∧
    (fun ν : ℝ => -Real.log (Formulas.clockTilt ν) - 3 / 2 * (61 / 16) * ν ^ 2) =O[𝓝 0] (fun ν : ℝ => ν ^ 4) := by
  refine ⟨fun ν => ?_, Completion.Comp.clockPair_near, Completion.Comp.minus_log_tilt⟩
  have h1 := RuleAndLaw.clockMQ_pos ν
  have h2 := RuleAndLaw.clockMQ_pos (-ν)
  rw [Formulas.clockTilt, Formulas.clockPair, Real.log_rpow (mul_pos h1 h2), Real.log_mul h1.ne' h2.ne']
  ring

end Comparison.System
