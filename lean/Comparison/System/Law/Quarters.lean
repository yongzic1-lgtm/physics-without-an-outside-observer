import Comparison.System.Postulates
import Comparison.Existence.Zero
import Comparison.Existence.AvailableTransitions
import Comparison.Existence.Excursion
import Comparison.WholePicture.TheLaw

/-!
# The proof system, the law: the four points `u = i^d/4` (Eqs. (19), (21), (22), (23) and Table VII)

* `eq_19`: the transitions of one excursion and their shares, every count a theorem: `M = 296`, `C_h = 60`, `C_j = 59`,
  `74` states, `34` of them leaving the last-step direction undivided; `c_L = 15/74`, `σ = 75/74`, `η = 295/296`,
  `R_ud = 17/37`, `E_H = Eℓ C_h/320 = 3` with `Eℓ = 16` the mean length of an excursion and `E_H = 3` the expected
  steps along the last-step direction per excursion.
* `eq_21`: `k_N(−1/4) = (5 − N)/2 = 5/2, 3/2, 1/2`.
* `eq_22`, `eq_23`: `g² = 1/72` by its three expressions; `a = 5/38`, `χ_A = 13/12`, `w_h = 3/13`,
  `χ_h = 30/169`.
* `table_VII`: the law at its four points `u = i^k/4`, row by row, with the exact values
  (`F(±i) = (7 ± 12i)/193`, printed `0.0363 ± 0.0622i`).
-/

open Complex Comparison

namespace Comparison.System

namespace Law

/-- The excursion, `F(z) = z⁴(1 + z)/(16 − 8z − 3z² − 3z³)` (Proposition 29). -/
noncomputable def excursionFz (z : ℂ) : ℂ := z ^ 4 * (1 + z) / (16 - 8 * z - 3 * z ^ 2 - 3 * z ^ 3)

/-- The plane angle's step, `w = u/(1 + 4u²)`. -/
noncomputable def wOf (u : ℂ) : ℂ := u / (1 + 4 * u ^ 2)

/-- The stiffness of the plane angle, `κ(w) = 2w⁴/(1 − 5w²)²`. -/
noncomputable def kappaW (w : ℂ) : ℂ := 2 * w ^ 4 / (1 - 5 * w ^ 2) ^ 2

theorem I3 : I ^ 3 = -I := by rw [pow_succ, I_sq]; ring
theorem I4 : I ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, I_sq]; norm_num

end Law

open Comparison.System.Law

/-- **Eq. (19), the transitions of one excursion and their shares.** For an excursion begun with the last-step direction `h`: the
seventy-four states, `M = 296` continuations, `C_h = 60` along the last-step direction and `59` along each other line,
`34` states leaving the last-step direction undivided; `c_L = C_h/M = 15/74`, `σ = 5C_h/M = 75/74`, `η = 5·59/M = 295/296`,
`R_ud = 34/74 = 17/37`; the mean excursion `Eℓ = 16`, and `E_H = Eℓ C_h/320 = 3`, the expected steps along the last-step direction
per excursion. -/
theorem eq_19 (h : Fin 5) :
    (excursionStates h).card = 74 ∧
    (∑ j, (alongCount h j : ℚ)) = 296 ∧ (alongCount h h : ℚ) = 60 ∧
    (∀ j, j ≠ h → (alongCount h j : ℚ) = 59) ∧
    ((excursionStates h).filter fun s => h ∉ disagreeSet s.1).card = 34 ∧
    (alongCount h h : ℚ) / (∑ j, (alongCount h j : ℚ)) = 15 / 74 ∧
    5 * (alongCount h h : ℚ) / (∑ j, (alongCount h j : ℚ)) = 75 / 74 ∧
    5 * 59 / (∑ j, (alongCount h j : ℚ)) = 295 / 296 ∧
    (((excursionStates h).filter fun s => h ∉ disagreeSet s.1).card : ℚ) / (excursionStates h).card = 17 / 37 ∧
    HasSum (fun n : ℕ => (n : ℝ) * excursionLaw n) 16 ∧
    (16 : ℚ) * (alongCount h h : ℚ) / 320 = 3 ∧
    HasSum (fun n => (∑ s ∈ (excursionStates h).filter (fun s => s.2 ≠ h), (stateCount n s : ℝ)) /
      (5 * 4 ^ n) / 4) 3 := by
  have hM : (∑ j, (alongCount h j : ℚ)) = 296 := by exact_mod_cast availableTransitions_total h
  have hC : (alongCount h h : ℚ) = 60 := by exact_mod_cast (availableTransitions_along h).1
  have h59 : ∀ j, j ≠ h → (alongCount h j : ℚ) = 59 := fun j hj => by
    exact_mod_cast (availableTransitions_along h).2 j hj
  have h34 := availableTransitions_up h
  have h74 := card_excursionStates h
  refine ⟨h74, hM, hC, h59, h34, ?_, ?_, ?_, ?_, excursion_mean, ?_, steps_along_lastDirection h⟩
  · rw [hC, hM]; norm_num
  · rw [hC, hM]; norm_num
  · rw [hM]; norm_num
  · rw [h34, h74]; norm_num
  · rw [hC]; norm_num

/-- **Eq. (21):** at the point `u = −1/4` the grade factors are `k_N(−1/4) = (5 − N)/2 = 5/2, 3/2, 1/2`. -/
theorem eq_21 :
    (∀ N : ℂ, WholePicture.kN N (-1 / 4) = (5 - N) / 2) ∧
    WholePicture.kN (0 : ℂ) (-1 / 4) = 5 / 2 ∧ WholePicture.kN (2 : ℂ) (-1 / 4) = 3 / 2 ∧
    WholePicture.kN (4 : ℂ) (-1 / 4) = 1 / 2 := by
  refine ⟨fun N => ?_, ?_, ?_, ?_⟩ <;> simp only [WholePicture.kN] <;> ring

/-- **Eq. (22):** one pair of directions on opposite sides, `g² = −Φ(1)/4[1 + Φ(1)] = −Φ(i)/6[1 + Φ(i)] = e_line²/(k_C² − 1) = 1/72`,
with `e_line = k₄/k₂` at the point `u = −1/4` and `k_C = 1/|u| − 1 = 3`. -/
theorem eq_22 :
    (-(Law.Phi 1) / (1 + Law.Phi 1)) / 4 = 1 / 72 ∧
    (-(Law.Phi I) / (1 + Law.Phi I)) / 6 = 1 / 72 ∧
    (WholePicture.kN (4 : ℝ) (-1 / 4) / WholePicture.kN (2 : ℝ) (-1 / 4)) ^ 2 /
      ((1 / |(-1 / 4 : ℝ)| - 1) ^ 2 - 1) = 1 / 72 ∧
    1 / |(-1 / 4 : ℝ)| - 1 = 3 :=
  ⟨WholePicture.one_crossing_pair.1, WholePicture.one_crossing_pair.2.1,
    WholePicture.one_crossing_pair.2.2, by norm_num [abs_of_neg]⟩

/-- **Eq. (23):** `a = (1 − Φ(1))/8 = 5/38`, `χ_A = 1/(1 + Φ(i)) = 13/12`, `w_h = 1/(4χ_A) = 3/13`,
`χ_h = w_h(1 − w_h) = 30/169`. -/
theorem eq_23 :
    (1 - Law.Phi 1) / 8 = 5 / 38 ∧ 1 / (1 + Law.Phi I) = 13 / 12 ∧
    1 / (4 * (1 / (1 + Law.Phi I))) = 3 / 13 ∧
    (1 / (4 * (1 / (1 + Law.Phi I)))) * (1 - 1 / (4 * (1 / (1 + Law.Phi I)))) = 30 / 169 :=
  WholePicture.rule_constants

/-- **Table VII, the law at its four points `u = i^k/4`:** the grade factors `k₀, k₂, k₄`, `1 − u²`,
the plain and the signed first returns `F(4u)`, `Φ(4u)`, the step `w = u/(1 + 4u²)` and the stiffness
`κ(w)`; at the singlet (`u = 1/4`), the last-step direction (`i/4`), the plane (`−1/4`) and colour (`−i/4`). The printed
`F(±i) = 0.0363 ± 0.0622i` are `(7 ± 12i)/193` to four vertices. -/
theorem table_VII :
    (WholePicture.kN (0 : ℂ) (1 / 4) = 0 ∧ WholePicture.kN (2 : ℂ) (1 / 4) = 1 ∧
      WholePicture.kN (4 : ℂ) (1 / 4) = 2 ∧ 1 - (1 / 4 : ℂ) ^ 2 = 15 / 16 ∧
      excursionFz (4 * (1 / 4)) = 1 ∧ Law.Phi (4 * (1 / 4)) = -1 / 19 ∧ wOf (1 / 4) = 1 / 5 ∧
      kappaW (wOf (1 / 4)) = 1 / 200) ∧
    (WholePicture.kN (0 : ℂ) (I / 4) = (3 - 5 * I) / 4 ∧ WholePicture.kN (2 : ℂ) (I / 4) = (3 - I) / 4 ∧
      WholePicture.kN (4 : ℂ) (I / 4) = 3 * (1 + I) / 4 ∧ 1 - (I / 4) ^ 2 = 17 / 16 ∧
      excursionFz (4 * (I / 4)) = (7 + 12 * I) / 193 ∧ Law.Phi (4 * (I / 4)) = -1 / 13 ∧
      wOf (I / 4) = I / 3 ∧ kappaW (wOf (I / 4)) = 1 / 98) ∧
    (WholePicture.kN (0 : ℂ) (-1 / 4) = 5 / 2 ∧ WholePicture.kN (2 : ℂ) (-1 / 4) = 3 / 2 ∧
      WholePicture.kN (4 : ℂ) (-1 / 4) = 1 / 2 ∧ 1 - (-1 / 4 : ℂ) ^ 2 = 15 / 16 ∧
      excursionFz (4 * (-1 / 4)) = 0 ∧ Law.Phi (4 * (-1 / 4)) = -1 / 19 ∧ wOf (-1 / 4) = -1 / 5 ∧
      kappaW (wOf (-1 / 4)) = 1 / 200) ∧
    (WholePicture.kN (0 : ℂ) (-I / 4) = (3 + 5 * I) / 4 ∧ WholePicture.kN (2 : ℂ) (-I / 4) = (3 + I) / 4 ∧
      WholePicture.kN (4 : ℂ) (-I / 4) = 3 * (1 - I) / 4 ∧ 1 - (-I / 4) ^ 2 = 17 / 16 ∧
      excursionFz (4 * (-I / 4)) = (7 - 12 * I) / 193 ∧ Law.Phi (4 * (-I / 4)) = -1 / 13 ∧
      wOf (-I / 4) = -I / 3 ∧ kappaW (wOf (-I / 4)) = 1 / 98) ∧
    |(7 : ℝ) / 193 - 0.0363| < 0.00005 ∧ |(12 : ℝ) / 193 - 0.0622| < 0.00005 := by
  have h2 : I ^ 2 = -1 := I_sq
  have h3 := I3
  have h4 := I4
  have den_i : (16 - 8 * I - 3 * I ^ 2 - 3 * I ^ 3 : ℂ) = 19 - 5 * I := by
    rw [h2, h3]; ring
  have den_mi : (16 - 8 * (-I) - 3 * (-I) ^ 2 - 3 * (-I) ^ 3 : ℂ) = 19 + 5 * I := by
    rw [neg_sq, h2, show (-I) ^ 3 = -(I ^ 3) by ring, h3]; ring
  have ne_i : (19 - 5 * I : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have ne_mi : (19 + 5 * I : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this
  have n193 : (193 : ℂ) ≠ 0 := by norm_num
  have F_i : excursionFz I = (7 + 12 * I) / 193 := by
    rw [excursionFz, den_i, h4, div_eq_div_iff ne_i n193]
    linear_combination (60 : ℂ) * h2
  have F_mi : excursionFz (-I) = (7 - 12 * I) / 193 := by
    rw [excursionFz, den_mi, show (-I) ^ 4 = I ^ 4 by ring, h4, div_eq_div_iff ne_mi n193]
    linear_combination (60 : ℂ) * h2
  have Phi_i : Law.Phi I = -1 / 13 := by
    simp only [Law.Phi]; rw [h4, h2]; norm_num
  have Phi_mi : Law.Phi (-I) = -1 / 13 := by
    simp only [Law.Phi]; rw [show (-I) ^ 4 = I ^ 4 by ring, neg_sq, h4, h2]; norm_num
  have w_i : wOf (I / 4) = I / 3 := by
    rw [wOf, div_pow, h2]
    have : (1 + 4 * (-1 / 4 ^ 2) : ℂ) = 3 / 4 := by norm_num
    rw [this]; field_simp
  have w_mi : wOf (-I / 4) = -I / 3 := by
    rw [wOf, div_pow, neg_sq, h2]
    have : (1 + 4 * (-1 / 4 ^ 2) : ℂ) = 3 / 4 := by norm_num
    rw [this]; field_simp
  have k_i : kappaW (I / 3) = 1 / 98 := by
    rw [kappaW, div_pow, div_pow, h2, h4]; norm_num
  have k_mi : kappaW (-I / 3) = 1 / 98 := by
    rw [kappaW, div_pow, div_pow, neg_sq, show (-I) ^ 4 = I ^ 4 by ring, h2, h4]; norm_num
  have e_i : (4 : ℂ) * (I / 4) = I := by ring
  have e_mi : (4 : ℂ) * (-I / 4) = -I := by ring
  have sq_i : (I / 4) ^ 2 = -1 / 16 := by rw [div_pow, h2]; norm_num
  have sq_mi : (-I / 4) ^ 2 = -1 / 16 := by rw [div_pow, neg_sq, h2]; norm_num
  have w_q : wOf (1 / 4) = 1 / 5 := by norm_num [wOf]
  have w_mq : wOf (-1 / 4) = -1 / 5 := by norm_num [wOf]
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, w_q, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, w_i, ?_⟩,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, w_mq, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, w_mi, ?_⟩, ?_, ?_⟩
  · norm_num [WholePicture.kN]
  · norm_num [WholePicture.kN]
  · norm_num [WholePicture.kN]
  · norm_num
  · norm_num [excursionFz]
  · norm_num [Law.Phi]
  · rw [w_q]; norm_num [kappaW]
  · simp only [WholePicture.kN]; rw [sq_i]; ring
  · simp only [WholePicture.kN]; rw [sq_i]; ring
  · simp only [WholePicture.kN]; rw [sq_i]; ring
  · rw [sq_i]; norm_num
  · rw [e_i]; exact F_i
  · rw [e_i]; exact Phi_i
  · rw [w_i]; exact k_i
  · norm_num [WholePicture.kN]
  · norm_num [WholePicture.kN]
  · norm_num [WholePicture.kN]
  · norm_num
  · norm_num [excursionFz]
  · norm_num [Law.Phi]
  · rw [w_mq]; norm_num [kappaW]
  · simp only [WholePicture.kN]; rw [sq_mi]; ring
  · simp only [WholePicture.kN]; rw [sq_mi]; ring
  · simp only [WholePicture.kN]; rw [sq_mi]; ring
  · rw [sq_mi]; norm_num
  · rw [e_mi]; exact F_mi
  · rw [e_mi]; exact Phi_mi
  · rw [w_mi]; exact k_mi
  · rw [abs_sub_lt_iff]; constructor <;> norm_num
  · rw [abs_sub_lt_iff]; constructor <;> norm_num

end Comparison.System
