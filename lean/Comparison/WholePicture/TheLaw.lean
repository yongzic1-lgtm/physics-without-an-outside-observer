module

public import Comparison.Law.Meetings
public import Comparison.Law.Rule
public import Comparison.Colour.Proton

/-!
# The whole picture, statements 5, 14, 16 and the law's own transformation (statement 15)

* **Statement 5.** `kN N u = 1 + 4u² − u(5 − 2N)`, the grade factor. `law_grade_factors`:
  **`det(I − uB) = (1 − u²)²⁴ k₀ k₂¹⁰ k₄⁵`** (from `D_plus`). `meeting_factor_zpow`,
  `law_over_meetings`:
  **`det(I − uB) = Π_U (1 + u)^{a_U − 1}(1 − u)^{d_U − 1}[1 + 4u² − u(a_U − d_U)]`** over the
  sixteen meetings, `a_U`, `d_U` the lines on which its two systems agree and disagree (integer
  powers: at the singlet `d_U − 1 = −1`), for every `u ≠ 1` (from `law_meetings`).
* **Statement 14.** `step_weights_are_grade_factors`: **on all 64 divided sets `t_S = 1/k_N(−¼)` and
  `e_S = k_{N+2}(−¼)/k_N(−¼)` with `N = 5 − |L_S|`**; `grade_factors_plane_quarter`: `5/2, 3/2, 1/2`;
  `quarter_factors`: at `u = ¼` only `k₀` vanishes, and no grade factor vanishes at `i/4, −¼, −i/4`;
  `one_crossing_pair`:
  **`g² = [−Φ(1)/(1 + Φ(1))]/4 = [−Φ(i)/(1 + Φ(i))]/6 = e_line²/(k_C² − 1) = 1/72`**;
  `rule_constants`: **`a = (1 − Φ(1))/8 = 5/38`, `χ_A = 1/(1 + Φ(i)) = 13/12`,
  `w_h = 1/(4χ_A) = 3/13`, `χ_h = w_h(1 − w_h) = 30/169`**.
* **Statement 16.** `alphaS_sq`: **`α_s² = [k₄/(k₂√(k_C² − 1))]² = 1/72`** at the point `u = −1/4`;
  `gravity_grade_form`: **`W = k₀(−¼)^{−k_C Eℓ} η^{k_C E_H} = (2/5)⁴⁸(295/296)⁹`**, equal to `Wgrav`.
* **Statement 15, the law's own transformation.** `law_transformation`:
  **`K(v) = a K(u) + b I`, `a = v/u`, `b = 1 + 4v² − a(1 + 4u²)`** for `K(u) = (1 + 4u²) − uA` and
  any `A`; `grade_factor_transformation`: the same on the grade factors.
-/

@[expose] public section

namespace Comparison.WholePicture

open Matrix Complex

/-! ## Statement 5 -/

/-- **The grade factor** `k_N(u) = 1 + 4u² − u(5 − 2N)`. -/
def kN {R : Type*} [CommRing R] (N u : R) : R := 1 + 4 * u ^ 2 - u * (5 - 2 * N)

/-- **`det(I − uB) = (1 − u²)²⁴ k₀ k₂¹⁰ k₄⁵`.** -/
theorem law_grade_factors (u : ℂ) :
    (1 - u • stepOp transitionMat).det = (1 - u ^ 2) ^ 24 * kN 0 u * kN 2 u ^ 10 * kN 4 u ^ 5 := by
  rw [D_plus]
  simp only [kN]
  ring

/-- The lines on which the two systems of the meeting `U` agree, `a_U = 5 − |T_U|`. -/
def agreeCount (U : Fin 16) : ℕ := 5 - (disagreeSet U).card

/-- The lines on which they disagree, `d_U = |T_U|`. -/
def disagreeCount (U : Fin 16) : ℕ := (disagreeSet U).card

theorem disagree_card_cases (U : Fin 16) :
    (disagreeSet U).card = 0 ∨ (disagreeSet U).card = 2 ∨ (disagreeSet U).card = 4 := by
  revert U
  decide

/-- **One meeting's factor** `(1 + u)^{a − 1}(1 − u)^{d − 1}[1 + 4u² − u(a − d)]`, with integer
powers. -/
theorem meeting_factor_zpow (u : ℂ) (hu : u ≠ 1) (U : Fin 16) :
    (1 - u • Law.patternK (R := ℂ) (disagreeSet U)).det =
      (1 + u) ^ ((agreeCount U : ℤ) - 1) * (1 - u) ^ ((disagreeCount U : ℤ) - 1) *
        (1 + 4 * u ^ 2 - u * ((agreeCount U : ℂ) - (disagreeCount U : ℂ))) := by
  have h1u : (1 - u) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  simp only [agreeCount, disagreeCount]
  rcases disagree_card_cases U with h | h | h
  · have hU : disagreeSet U = ∅ := Finset.card_eq_zero.mp h
    rw [hU, Law.singlet_factor]
    simp only [Finset.card_empty, Nat.sub_zero, Nat.cast_ofNat, CharP.cast_eq_zero]
    norm_num
    field_simp
    ring
  · rw [Law.pattern_factor_cancelled _ (by omega) (by omega), h]
    norm_num
  · rw [Law.pattern_factor_cancelled _ (by omega) (by omega), h]
    norm_num

/-- **The law factors meeting by meeting:**
`det(I − uB) = Π_U (1 + u)^{a_U − 1}(1 − u)^{d_U − 1}[1 + 4u² − u(a_U − d_U)]` for every `u ≠ 1`. -/
theorem law_over_meetings (u : ℂ) (hu : u ≠ 1) :
    (1 - u • stepOp transitionMat).det =
      ∏ U : Fin 16, (1 + u) ^ ((agreeCount U : ℤ) - 1) * (1 - u) ^ ((disagreeCount U : ℤ) - 1) *
        (1 + 4 * u ^ 2 - u * ((agreeCount U : ℂ) - (disagreeCount U : ℂ))) := by
  rw [← Law.law_meetings]
  exact Finset.prod_congr rfl fun U _ => meeting_factor_zpow u hu U

/-! ## Statement 14 -/

/-- The grade factor at a real step. -/
def kR (N u : ℝ) : ℝ := 1 + 4 * u ^ 2 - u * (5 - 2 * N)

theorem kR_plane_quarter (N : ℝ) : kR N (-1 / 4) = (5 - N) / 2 := by
  unfold kR
  ring

/-- **The grade factors at the point `u = −1/4`:** `k₀, k₂, k₄ = 5/2, 3/2, 1/2`. -/
theorem grade_factors_plane_quarter :
    kR 0 (-1 / 4) = 5 / 2 ∧ kR 2 (-1 / 4) = 3 / 2 ∧ kR 4 (-1 / 4) = 1 / 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [kR_plane_quarter] <;> norm_num

/-- **At the four points `u = i^d/4`:** at `u = ¼` only `k₀` vanishes; at `i/4`, `−¼`, `−i/4` no grade factor
vanishes. -/
theorem quarter_factors :
    kN (0 : ℂ) (1 / 4) = 0 ∧ kN (2 : ℂ) (1 / 4) ≠ 0 ∧ kN (4 : ℂ) (1 / 4) ≠ 0 ∧
    (∀ k ∈ ({1, 2, 3} : Finset ℕ), ∀ N ∈ ({0, 2, 4} : Finset ℂ), kN N (I ^ k / 4) ≠ 0) := by
  refine ⟨by norm_num [kN], by norm_num [kN], by norm_num [kN], ?_⟩
  intro k hk N hN
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk hN
  rcases hk with rfl | rfl | rfl <;> rcases hN with rfl | rfl | rfl <;>
    simp [kN, pow_succ, Complex.ext_iff] <;> norm_num

/-- The grade a divided set's step lands on: `N_S = 5 − |L_S|`. -/
noncomputable def gradeS (S : Finset (Fin 6)) : ℝ := 5 - |(Law.LZ S : ℝ)|

/-- **The step weights of every divided set are the grade factors at the point `u = −1/4`:**
`t_S = 1/k_N(−¼)` and `e_S = k_{N+2}(−¼)/k_N(−¼)` with `N = 5 − |L_S|`, at all 64 divided sets. -/
theorem step_weights_are_grade_factors (S : Finset (Fin 6)) :
    Law.tS S = 1 / kR (gradeS S) (-1 / 4) ∧
      Law.eS S = kR (gradeS S + 2) (-1 / 4) / kR (gradeS S) (-1 / 4) := by
  have hL : |(Law.LZ S : ℝ)| ≠ 0 := by
    rw [abs_ne_zero]
    exact_mod_cast Law.LZ_ne_zero S
  simp only [Law.tS, Law.eS, Law.norm_wS, kR_plane_quarter, gradeS]
  set x := |(Law.LZ S : ℝ)| with hx
  rw [show (5 : ℝ) - (5 - x) = x by ring, show (5 : ℝ) - (5 - x + 2) = x - 2 by ring]
  constructor
  · field_simp
  · field_simp

/-- **One pair of directions on opposite sides**, by its three expressions:
`[−Φ(1)/(1 + Φ(1))]/4 = [−Φ(i)/(1 + Φ(i))]/6 = e_line²/(k_C² − 1) = 1/72`, with `e_line = k₄/k₂` at
the point `u = −1/4` and `k_C = 1/|u| − 1 = 3` the lines outside a plane. -/
theorem one_crossing_pair :
    (-(Law.Phi 1) / (1 + Law.Phi 1)) / 4 = 1 / 72 ∧
    (-(Law.Phi I) / (1 + Law.Phi I)) / 6 = 1 / 72 ∧
    (kR 4 (-1 / 4) / kR 2 (-1 / 4)) ^ 2 / ((1 / |(-1 / 4 : ℝ)| - 1) ^ 2 - 1) = 1 / 72 := by
  obtain ⟨_, h2, h4⟩ := grade_factors_plane_quarter
  refine ⟨?_, ?_, ?_⟩
  · simp only [Law.Phi]
    norm_num
  · simp only [Law.Phi]
    have h4I : I ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, I_sq]; norm_num
    rw [h4I, I_sq]
    norm_num
  · rw [h2, h4]
    norm_num

/-- **The constants of the rule:** `a = (1 − Φ(1))/8 = 5/38`, `χ_A = 1/(1 + Φ(i)) = 13/12`,
`w_h = 1/(4χ_A) = 3/13`, `χ_h = w_h(1 − w_h) = 30/169`. -/
theorem rule_constants :
    (1 - Law.Phi 1) / 8 = 5 / 38 ∧ 1 / (1 + Law.Phi I) = 13 / 12 ∧
    1 / (4 * (1 / (1 + Law.Phi I))) = 3 / 13 ∧
    (1 / (4 * (1 / (1 + Law.Phi I)))) * (1 - 1 / (4 * (1 / (1 + Law.Phi I)))) = 30 / 169 := by
  have hI : Law.Phi I = -1 / 13 := by
    simp only [Law.Phi]
    have h4I : I ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 by rfl, pow_mul, I_sq]; norm_num
    rw [h4I, I_sq]
    norm_num
  have h1 : Law.Phi 1 = -1 / 19 := by
    simp only [Law.Phi]
    norm_num
  rw [hI, h1]
  norm_num

/-! ## Statement 16 -/

/-- **`α_s² = 1/72`:** `α_s = k₄(−¼)/[k₂(−¼)√(k_C² − 1)]` with `k_C = 1/|u| − 1 = 3`. -/
theorem alphaS_sq :
    (kR 4 (-1 / 4) / (kR 2 (-1 / 4) * Real.sqrt ((1 / |(-1 / 4 : ℝ)| - 1) ^ 2 - 1))) ^ 2 =
      1 / 72 := by
  obtain ⟨_, h2, h4⟩ := grade_factors_plane_quarter
  rw [h2, h4]
  have habs : |(-1 / 4 : ℝ)| = 1 / 4 := by norm_num [abs_of_neg]
  rw [habs]
  have h8 : ((1 / (1 / 4 : ℝ) - 1) ^ 2 - 1) = 8 := by norm_num
  rw [h8, div_pow, mul_pow, Real.sq_sqrt (by norm_num)]
  norm_num

/-- **Gravity's closed form:** `W = k₀(−¼)^{−k_C Eℓ} η^{k_C E_H} = (2/5)⁴⁸(295/296)⁹`, with
`k_C = 3` lines, `Eℓ = 16` steps, `E_H = 3` steps along the last-step direction and `η = 295/296`; it is `Wgrav`. -/
theorem gravity_grade_form :
    kR 0 (-1 / 4) ^ (-(3 * 16 : ℤ)) * ((295 : ℝ) / 296) ^ (3 * 3) =
      (2 / 5) ^ 48 * (295 / 296) ^ 9 ∧
    ((Wgrav : ℚ) : ℝ) = (2 / 5) ^ 48 * (295 / 296) ^ 9 := by
  obtain ⟨h0, _, _⟩ := grade_factors_plane_quarter
  constructor
  · rw [h0]
    rw [show (-(3 * 16 : ℤ)) = -48 by norm_num, _root_.zpow_neg, zpow_ofNat]
    norm_num
  · rw [W_eq]
    push_cast
    ring

/-! ## Statement 15: the law's own transformation -/

/-- **The law's own transformation:** `K(v) = a K(u) + b I` with `a = v/u`,
`b = 1 + 4v² − a(1 + 4u²)`, for `K(u) = (1 + 4u²) − uA` and any operator `A`. -/
theorem law_transformation {n : Type*} [DecidableEq n] (A : Matrix n n ℂ) (u v : ℂ)
    (hu : u ≠ 0) :
    (1 + 4 * v ^ 2) • (1 : Matrix n n ℂ) - v • A =
      (v / u) • ((1 + 4 * u ^ 2) • (1 : Matrix n n ℂ) - u • A) +
        (1 + 4 * v ^ 2 - v / u * (1 + 4 * u ^ 2)) • (1 : Matrix n n ℂ) := by
  have h : v / u * u = v := div_mul_cancel₀ v hu
  rw [smul_sub, smul_smul, smul_smul, h]
  module

/-- **The same on the grade factors:** `k_N(v) = a k_N(u) + b`. -/
theorem grade_factor_transformation (N u v : ℂ) (hu : u ≠ 0) :
    kN N v = v / u * kN N u + (1 + 4 * v ^ 2 - v / u * (1 + 4 * u ^ 2)) := by
  simp only [kN]
  field_simp
  ring

end Comparison.WholePicture

end
