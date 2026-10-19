import Comparison.Law.Rule
import Comparison.Existence.Gauge

/-!
# A response and its clock in one gap (Prop. S64a; formula (27))

Proposition S64a. On the fifteen nonempty even two-spinor states `S` (sets of lines,
`|S| = 2` the ten symmetric states, `|S| = 4` the five vector states) take **any** positive grade weights,
`p` on the symmetric states and `q` on the vector states (`wt`), and the expectation `ex` they define. With
the grade `N = |S|`, the response of the coordinate divided set `D`, `H_D(S) = (5|S ∩ D| − |D||S|)/4`,
`𝒥_DE = Cov(N, H_D H_E)` and `C_W = (9/8) Var N`:

* `sweep`: **`𝒥_DE = (C_W/72)(|D||E| − 5 tr P_D P_E)`** for all `D, E` and all `p, q > 0`
  (`trace_projD_mul`: `tr P_D P_E = |D ∩ E|`); `varN_eq`: `Var N = 8pq/(2p + q)²`.
* `sweep_gap`: with the resolvent's weights `p = 1/(χ + 4)`, `q = 1/(χ + 8)`, `χ ≥ 0`:
  **`C_W(χ) = 9(χ + 4)(χ + 8)/(3χ + 20)²`** and `𝒥_{{a}{b}} = (χ + 4)(χ + 8)/(8(3χ + 20)²)`, `1/100`
  at `χ = 0`.
* `sweep_ratios`: **`𝒥/C_W = 1/72`** for a pair of directions on opposite sides, **`4/72 = −Φ(1)/(1 + Φ(1))`** for a line
  against the other four, **`6/72 = −Φ(i)/(1 + Φ(i))`** for a plane against its three outside lines.
* `crossing_g_sq`: `g² = 1/72 = −Φ(1)/[4(1 + Φ(1))] = −Φ(i)/[6(1 + Φ(i))] = e_ℓ²/8`.
-/

namespace Comparison.Formulas

open Finset

/-! ## The weights, the expectation and the covariance -/

/-- The ten symmetric states. -/
def planeSets : Finset (Finset (Fin 5)) := univ.filter fun S => S.card = 2

/-- The five vector states. -/
def lineSets : Finset (Finset (Fin 5)) := univ.filter fun S => S.card = 4

/-- The fifteen nonempty even two-spinor states. -/
def evenSets : Finset (Finset (Fin 5)) := univ.filter fun S => S.card = 2 ∨ S.card = 4

/-- The grade weight: `p` on the symmetric states, `q` on the vector states. -/
def wt (p q : ℝ) (S : Finset (Fin 5)) : ℝ := if S.card = 2 then p else q

/-- The expectation in the weights `p`, `q`. -/
noncomputable def ex (p q : ℝ) (f : Finset (Fin 5) → ℝ) : ℝ :=
  (∑ S ∈ evenSets, wt p q S * f S) / ∑ S ∈ evenSets, wt p q S

/-- The covariance. -/
noncomputable def cv (p q : ℝ) (f g : Finset (Fin 5) → ℝ) : ℝ :=
  ex p q (fun S => f S * g S) - ex p q f * ex p q g

/-- The grade `N = |S|`. -/
def gradeN (S : Finset (Fin 5)) : ℝ := S.card

/-- The response of the coordinate divided set `D`: `H_D(S) = (5|S ∩ D| − |D||S|)/4`. -/
noncomputable def HD (D S : Finset (Fin 5)) : ℝ := (5 * ((S ∩ D).card : ℝ) - D.card * S.card) / 4

/-- The response of one line, `H_a = H_{{a}}`. -/
noncomputable def hl (a : Fin 5) (S : Finset (Fin 5)) : ℝ :=
  (5 * (if a ∈ S then (1 : ℝ) else 0) - S.card) / 4

/-- `C_W = (9/8) Var N`. -/
noncomputable def CW (p q : ℝ) : ℝ := 9 / 8 * cv p q gradeN gradeN

/-- `𝒥_DE = Cov(N, H_D H_E)`. -/
noncomputable def JDE (p q : ℝ) (D E : Finset (Fin 5)) : ℝ :=
  cv p q gradeN fun S => HD D S * HD E S

/-! ## Counting on the fifteen -/

theorem sum_even (p q : ℝ) (f : Finset (Fin 5) → ℝ) :
    ∑ S ∈ evenSets, wt p q S * f S = p * ∑ S ∈ planeSets, f S + q * ∑ S ∈ lineSets, f S := by
  rw [evenSets, planeSets, lineSets, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun S _ => ?_
  by_cases h2 : S.card = 2
  · simp [wt, h2]
  · by_cases h4 : S.card = 4
    · simp [wt, h2, h4]
    · simp [h2, h4]

/-- `4 H_a` as an integer. -/
def hz (a : Fin 5) (S : Finset (Fin 5)) : ℤ := 5 * (if a ∈ S then 1 else 0) - S.card

theorem hl_eq (a : Fin 5) (S : Finset (Fin 5)) : hl a S = (hz a S : ℝ) / 4 := by
  rw [hl, hz]
  push_cast
  ring

theorem count_plane : (∑ S ∈ planeSets, (S.card : ℤ)) = 20 ∧ (∑ S ∈ planeSets, (1 : ℤ)) = 10 ∧
    (∑ S ∈ planeSets, (S.card : ℤ) ^ 2) = 40 := by decide

theorem count_line : (∑ S ∈ lineSets, (S.card : ℤ)) = 20 ∧ (∑ S ∈ lineSets, (1 : ℤ)) = 5 ∧
    (∑ S ∈ lineSets, (S.card : ℤ) ^ 2) = 80 := by decide

theorem count_plane_pair : ∀ a b : Fin 5,
    (∑ S ∈ planeSets, hz a S * hz b S) = (if a = b then 60 else -15) ∧
      (∑ S ∈ planeSets, (S.card : ℤ) * (hz a S * hz b S)) = (if a = b then 120 else -30) := by
  decide

theorem count_line_pair : ∀ a b : Fin 5,
    (∑ S ∈ lineSets, hz a S * hz b S) = (if a = b then 20 else -5) ∧
      (∑ S ∈ lineSets, (S.card : ℤ) * (hz a S * hz b S)) = (if a = b then 80 else -20) := by
  decide

theorem real_sum_plane (f : Finset (Fin 5) → ℤ) :
    (∑ S ∈ planeSets, (f S : ℝ)) = ((∑ S ∈ planeSets, f S : ℤ) : ℝ) := by push_cast; rfl

theorem real_sum_line (f : Finset (Fin 5) → ℤ) :
    (∑ S ∈ lineSets, (f S : ℝ)) = ((∑ S ∈ lineSets, f S : ℤ) : ℝ) := by push_cast; rfl

/-! ## The grade's mean and spread -/

theorem total_weight (p q : ℝ) : ∑ S ∈ evenSets, wt p q S = 10 * p + 5 * q := by
  have h := sum_even p q (fun _ => 1)
  simp only [mul_one] at h
  rw [h]
  have h2 := count_plane.2.1
  have h4 := count_line.2.1
  have e2 : (∑ S ∈ planeSets, (1 : ℝ)) = 10 := by exact_mod_cast h2
  have e4 : (∑ S ∈ lineSets, (1 : ℝ)) = 5 := by exact_mod_cast h4
  rw [e2, e4]
  ring

theorem ex_N (p q : ℝ) : ex p q gradeN = (20 * p + 20 * q) / (10 * p + 5 * q) := by
  rw [ex, total_weight, sum_even]
  have e2 : (∑ S ∈ planeSets, gradeN S) = 20 := by
    have := count_plane.1
    simp only [gradeN]
    exact_mod_cast this
  have e4 : (∑ S ∈ lineSets, gradeN S) = 20 := by
    have := count_line.1
    simp only [gradeN]
    exact_mod_cast this
  rw [e2, e4]
  ring

theorem ex_N2 (p q : ℝ) :
    ex p q (fun S => gradeN S * gradeN S) = (40 * p + 80 * q) / (10 * p + 5 * q) := by
  rw [ex, total_weight, sum_even]
  have e2 : (∑ S ∈ planeSets, gradeN S * gradeN S) = 40 := by
    have := count_plane.2.2
    simp only [gradeN, ← sq]
    exact_mod_cast this
  have e4 : (∑ S ∈ lineSets, gradeN S * gradeN S) = 80 := by
    have := count_line.2.2
    simp only [gradeN, ← sq]
    exact_mod_cast this
  rw [e2, e4]
  ring

/-- **`Var N = 8pq/(2p + q)²`.** -/
theorem varN_eq (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    cv p q gradeN gradeN = 8 * p * q / (2 * p + q) ^ 2 := by
  rw [cv, ex_N2, ex_N]
  have h1 : (10 * p + 5 * q) ≠ 0 := by positivity
  have h2 : (2 * p + q) ≠ 0 := by positivity
  field_simp
  ring

/-! ## One line against one line -/

theorem ex_hh (p q : ℝ) (a b : Fin 5) :
    ex p q (fun S => hl a S * hl b S) =
      (p * (if a = b then 60 else -15) + q * (if a = b then 20 else -5)) /
        (16 * (10 * p + 5 * q)) := by
  rw [ex, total_weight, sum_even]
  have e2 : (∑ S ∈ planeSets, hl a S * hl b S) = (if a = b then 60 else -15) / 16 := by
    have h := (count_plane_pair a b).1
    simp only [hl_eq]
    rw [show (∑ S ∈ planeSets, (hz a S : ℝ) / 4 * ((hz b S : ℝ) / 4)) =
        (∑ S ∈ planeSets, ((hz a S * hz b S : ℤ) : ℝ)) / 16 by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun S _ => ?_
          push_cast
          ring]
    rw [real_sum_plane, h]
    split_ifs <;> norm_num
  have e4 : (∑ S ∈ lineSets, hl a S * hl b S) = (if a = b then 20 else -5) / 16 := by
    have h := (count_line_pair a b).1
    simp only [hl_eq]
    rw [show (∑ S ∈ lineSets, (hz a S : ℝ) / 4 * ((hz b S : ℝ) / 4)) =
        (∑ S ∈ lineSets, ((hz a S * hz b S : ℤ) : ℝ)) / 16 by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun S _ => ?_
          push_cast
          ring]
    rw [real_sum_line, h]
    split_ifs <;> norm_num
  rw [e2, e4]
  split_ifs <;> field_simp <;> ring

theorem ex_Nhh (p q : ℝ) (a b : Fin 5) :
    ex p q (fun S => gradeN S * (hl a S * hl b S)) =
      (p * (if a = b then 120 else -30) + q * (if a = b then 80 else -20)) /
        (16 * (10 * p + 5 * q)) := by
  rw [ex, total_weight, sum_even]
  have e2 : (∑ S ∈ planeSets, gradeN S * (hl a S * hl b S)) = (if a = b then 120 else -30) / 16 := by
    have h := (count_plane_pair a b).2
    simp only [hl_eq, gradeN]
    rw [show (∑ S ∈ planeSets, (S.card : ℝ) * ((hz a S : ℝ) / 4 * ((hz b S : ℝ) / 4))) =
        (∑ S ∈ planeSets, (((S.card : ℤ) * (hz a S * hz b S) : ℤ) : ℝ)) / 16 by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun S _ => ?_
          push_cast
          ring]
    rw [real_sum_plane, h]
    split_ifs <;> norm_num
  have e4 : (∑ S ∈ lineSets, gradeN S * (hl a S * hl b S)) = (if a = b then 80 else -20) / 16 := by
    have h := (count_line_pair a b).2
    simp only [hl_eq, gradeN]
    rw [show (∑ S ∈ lineSets, (S.card : ℝ) * ((hz a S : ℝ) / 4 * ((hz b S : ℝ) / 4))) =
        (∑ S ∈ lineSets, (((S.card : ℤ) * (hz a S * hz b S) : ℤ) : ℝ)) / 16 by
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun S _ => ?_
          push_cast
          ring]
    rw [real_sum_line, h]
    split_ifs <;> norm_num
  rw [e2, e4]
  split_ifs <;> field_simp <;> ring

/-- **One line against one line:** `Cov(N, H_aH_b) = (C_W/72)(1 − 5δ_ab)`. -/
theorem sweep_lines (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (a b : Fin 5) :
    cv p q gradeN (fun S => hl a S * hl b S) =
      CW p q / 72 * (1 - 5 * (if a = b then 1 else 0)) := by
  rw [CW, varN_eq p q hp hq, cv, ex_Nhh, ex_N, ex_hh]
  have h1 : (10 * p + 5 * q) ≠ 0 := by positivity
  have h2 : (2 * p + q) ≠ 0 := by positivity
  split_ifs <;> field_simp <;> ring

/-! ## Any two coordinate divided sets -/

theorem ex_sum {ι : Type*} (s : Finset ι) (p q : ℝ) (g : ι → Finset (Fin 5) → ℝ) :
    ex p q (fun S => ∑ i ∈ s, g i S) = ∑ i ∈ s, ex p q (g i) := by
  simp only [ex, Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_div]

theorem cv_sum {ι : Type*} (s : Finset ι) (p q : ℝ) (f : Finset (Fin 5) → ℝ)
    (g : ι → Finset (Fin 5) → ℝ) :
    cv p q f (fun S => ∑ i ∈ s, g i S) = ∑ i ∈ s, cv p q f (g i) := by
  simp only [cv, Finset.mul_sum]
  rw [ex_sum, ex_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]

theorem HD_eq (D S : Finset (Fin 5)) : HD D S = ∑ a ∈ D, hl a S := by
  simp only [HD, hl, ← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_boole, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.filter_mem_eq_inter, Finset.inter_comm]

/-- `tr P_D P_E = |D ∩ E|` for the coordinate projectors. -/
theorem trace_projD_mul (D E : Finset (Fin 5)) :
    ((projD D) * (projD E)).trace = ((D ∩ E).card : ℝ) := by
  rw [projD, projD, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]
  have h : ∀ x : Fin 5, ((if x ∈ D then (1 : ℝ) else 0) * (if x ∈ E then 1 else 0)) =
      if x ∈ D ∩ E then 1 else 0 := by
    intro x
    by_cases hD : x ∈ D <;> by_cases hE : x ∈ E <;> simp [hD, hE]
  simp only [h, Finset.sum_boole]
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter]

/-- `Σ_{a ∈ D} Σ_{b ∈ E} (1 − 5δ_ab) = |D||E| − 5|D ∩ E|`. -/
theorem double_count (D E : Finset (Fin 5)) :
    ∑ x ∈ D, ∑ y ∈ E, (1 - 5 * (if x = y then (1 : ℝ) else 0)) =
      (D.card : ℝ) * E.card - 5 * (D ∩ E).card := by
  have h1 : ∀ x, ∑ y ∈ E, (1 - 5 * (if x = y then (1 : ℝ) else 0)) =
      E.card - 5 * (if x ∈ E then 1 else 0) := by
    intro x
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.mul_sum,
      Finset.sum_ite_eq]
  simp only [h1]
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum, Finset.sum_boole,
    Finset.filter_mem_eq_inter]

/-- **A response and its clock in one gap:** for coordinate divided sets `D, E` and any positive grade
weights, `𝒥_DE = Cov(N, H_D H_E) = (C_W/72)(|D||E| − 5 tr P_D P_E)`. -/
theorem sweep (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (D E : Finset (Fin 5)) :
    JDE p q D E = CW p q / 72 * (D.card * E.card - 5 * ((projD D) * (projD E)).trace) := by
  rw [trace_projD_mul, JDE]
  have hprod : (fun S => HD D S * HD E S) = fun S => ∑ a ∈ D, ∑ b ∈ E, hl a S * hl b S := by
    funext S
    rw [HD_eq, HD_eq, Finset.sum_mul_sum]
  rw [hprod, cv_sum]
  simp only [cv_sum, sweep_lines p q hp hq]
  rw [← double_count]
  simp only [Finset.mul_sum]

/-! ## The dependence on the gap -/

/-- **With the resolvent's weights** `p = 1/(χ + 4)`, `q = 1/(χ + 8)`:
`C_W = 9(χ + 4)(χ + 8)/(3χ + 20)²` and `𝒥_{{a}{b}} = (χ + 4)(χ + 8)/(8(3χ + 20)²)`. -/
theorem sweep_gap (χ : ℝ) (hχ : 0 ≤ χ) (a b : Fin 5) (hab : a ≠ b) :
    CW (1 / (χ + 4)) (1 / (χ + 8)) = 9 * (χ + 4) * (χ + 8) / (3 * χ + 20) ^ 2 ∧
      JDE (1 / (χ + 4)) (1 / (χ + 8)) {a} {b} = (χ + 4) * (χ + 8) / (8 * (3 * χ + 20) ^ 2) := by
  have hp : 0 < 1 / (χ + 4) := by positivity
  have hq : 0 < 1 / (χ + 8) := by positivity
  have hcw : CW (1 / (χ + 4)) (1 / (χ + 8)) = 9 * (χ + 4) * (χ + 8) / (3 * χ + 20) ^ 2 := by
    rw [CW, varN_eq _ _ hp hq]
    have h4 : χ + 4 ≠ 0 := by positivity
    have h8 : χ + 8 ≠ 0 := by positivity
    have h20 : 3 * χ + 20 ≠ 0 := by positivity
    field_simp
    ring
  refine ⟨hcw, ?_⟩
  rw [sweep _ _ hp hq, hcw, trace_projD_mul]
  have hi : ({a} ∩ {b} : Finset (Fin 5)) = ∅ := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
    rintro rfl
    exact hab
  rw [hi]
  simp only [Finset.card_singleton, Finset.card_empty, Nat.cast_one, Nat.cast_zero]
  have h20 : 3 * χ + 20 ≠ 0 := by positivity
  field_simp
  ring

/-- At `χ = 0` the pair of directions on opposite sides's response is `1/100`. -/
theorem sweep_zero (a b : Fin 5) (hab : a ≠ b) : JDE (1 / 4) (1 / 8) {a} {b} = 1 / 100 := by
  have h := (sweep_gap 0 le_rfl a b hab).2
  norm_num at h ⊢
  rw [h]

/-- **One ratio for every value of the gap:** `𝒥/C_W = 1/72` for a pair of directions on opposite sides, `4/72 = −Φ(1)/(1 + Φ(1))`
for a line against the other four, `6/72 = −Φ(i)/(1 + Φ(i))` for a plane against its three outside
lines, at every positive `p, q`. -/
theorem sweep_ratios (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    JDE p q {0} {1} / CW p q = 1 / 72 ∧
      JDE p q {0} {1, 2, 3, 4} / CW p q = 1 / 18 ∧
      ((1 / 18 : ℝ) : ℂ) = -Law.Phi 1 / (1 + Law.Phi 1) ∧
      JDE p q {0, 1} {2, 3, 4} / CW p q = 1 / 12 ∧
      ((1 / 12 : ℝ) : ℂ) = -Law.Phi Complex.I / (1 + Law.Phi Complex.I) := by
  have hcw : CW p q ≠ 0 := by
    rw [CW, varN_eq p q hp hq]
    have : 0 < 2 * p + q := by positivity
    positivity
  have hI4 : Complex.I ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Complex.I_sq]
    norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [sweep p q hp hq, trace_projD_mul]
    rw [show ({0} ∩ {1} : Finset (Fin 5)) = ∅ by decide]
    field_simp
    norm_num
  · rw [sweep p q hp hq, trace_projD_mul]
    rw [show ({0} ∩ {1, 2, 3, 4} : Finset (Fin 5)) = ∅ by decide]
    simp only [Finset.card_singleton, Finset.card_empty]
    rw [show ({1, 2, 3, 4} : Finset (Fin 5)).card = 4 by decide]
    field_simp
    norm_num
  · simp only [Law.Phi]
    push_cast
    norm_num
  · rw [sweep p q hp hq, trace_projD_mul]
    rw [show ({0, 1} ∩ {2, 3, 4} : Finset (Fin 5)) = ∅ by decide]
    rw [show ({0, 1} : Finset (Fin 5)).card = 2 by decide,
      show ({2, 3, 4} : Finset (Fin 5)).card = 3 by decide]
    simp only [Finset.card_empty]
    field_simp
    norm_num
  · simp only [Law.Phi]
    rw [hI4, Complex.I_sq]
    push_cast
    norm_num

/-- **Formula (27):** `g² = 1/72 = −Φ(1)/[4(1 + Φ(1))] = −Φ(i)/[6(1 + Φ(i))] = e_ℓ²/8`, `e_ℓ = 1/3`,
and the pair of directions on opposite sides's response against its clock is that number at every `p, q > 0`. -/
theorem crossing_g_sq (p q : ℝ) (hp : 0 < p) (hq : 0 < q) :
    JDE p q {0} {1} / CW p q = 1 / 72 ∧
      ((1 / 72 : ℝ) : ℂ) = -Law.Phi 1 / (4 * (1 + Law.Phi 1)) ∧
      ((1 / 72 : ℝ) : ℂ) = -Law.Phi Complex.I / (6 * (1 + Law.Phi Complex.I)) ∧
      (1 / 72 : ℝ) = (1 / 3) ^ 2 / 8 := by
  have hI4 : Complex.I ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, Complex.I_sq]
    norm_num
  refine ⟨(sweep_ratios p q hp hq).1, ?_, ?_, by norm_num⟩
  · simp only [Law.Phi]
    push_cast
    norm_num
  · simp only [Law.Phi]
    rw [hI4, Complex.I_sq]
    push_cast
    norm_num

open Filter Topology in
/-- **For every value of the gap:** as `χ → ∞` the response of the pair of directions on opposite sides tends to `1/72` and its
clock to `1`. -/
theorem sweep_limit :
    Tendsto (fun χ : ℝ => (χ + 4) * (χ + 8) / (8 * (3 * χ + 20) ^ 2)) atTop (𝓝 (1 / 72)) ∧
      Tendsto (fun χ : ℝ => 9 * (χ + 4) * (χ + 8) / (3 * χ + 20) ^ 2) atTop (𝓝 1) := by
  constructor
  · have hg : ContinuousAt (fun t : ℝ => (1 + 4 * t) * (1 + 8 * t) / (8 * (3 + 20 * t) ^ 2)) 0 := by
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      norm_num
    have h := hg.tendsto.comp tendsto_inv_atTop_zero
    have h0 : ((1 : ℝ) + 4 * 0) * (1 + 8 * 0) / (8 * (3 + 20 * 0) ^ 2) = 1 / 72 := by
      norm_num
    rw [h0] at h
    refine Tendsto.congr' ?_ h
    filter_upwards [eventually_gt_atTop 0] with χ hχ
    have h1 : χ ≠ 0 := hχ.ne'
    have h2 : 3 * χ + 20 ≠ 0 := by positivity
    simp only [Function.comp]
    field_simp
  · have hg : ContinuousAt (fun t : ℝ => 9 * (1 + 4 * t) * (1 + 8 * t) / (3 + 20 * t) ^ 2) 0 := by
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      norm_num
    have h := hg.tendsto.comp tendsto_inv_atTop_zero
    have h0 : (9 : ℝ) * (1 + 4 * 0) * (1 + 8 * 0) / (3 + 20 * 0) ^ 2 = 1 := by
      norm_num
    rw [h0] at h
    refine Tendsto.congr' ?_ h
    filter_upwards [eventually_gt_atTop 0] with χ hχ
    have h1 : χ ≠ 0 := hχ.ne'
    have h2 : 3 * χ + 20 ≠ 0 := by positivity
    simp only [Function.comp]
    field_simp

end Comparison.Formulas
