import Comparison.Existence.Moments
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The signed excursion with its marks (Proposition S109 of the public edition; Proposition 120's
`E Var(P|Q) = 9`)

* `marked_signed_excursion`: **`Φ(z; x, y) = −z⁴xy²/(16 + 3z²xy)`** is the sum of the signed first returns: the four-step
  returns `tsts`, `−z⁴xy²/16`, each further pair of steps through a line outside the plane adding `−3z²xy/16`; at
  `x = y = 1` it is `Φ(z) = −z⁴/(16 + 3z²)`.
* `excursion_marked_factor`: **the excursion at `z = 1` with its arrivals at the vector states marked by `x` and its visits to the symmetric states by `y` is
  `x² H(y)/(4 − 3x H(y))`, `H(y) = y(1 + y)/(2(2 − y))`** (`Colour/Visits.lean`: `excursionF`), and `excursion_by_arrivals`
  expands it: `P(Q = q) = (1/4)(3/4)^{q−2}` and **`E[y^P | Q = q] = H(y)^{q−1}`**.
* `H_moments`: `H(1) = 1`, `H'(1) = 5/2`, `H''(1) = 6`: between two arrivals at the vector states the visits to the symmetric states have mean
  `5/2` and variance `9/4`; `arrivals_mean`: `E(Q − 1) = 4`.
* `expected_conditional_variance`: **`E Var(P|Q) = (9/4) E(Q − 1) = 9 = Var P − Cov²/Var Q`** (with
  `Existence/Moments.lean`: `visit_moments`).
-/

namespace Comparison.Article

open Real

/-! ## The marked signed excursion -/

/-- **The marked signed excursion** as the sum of its first returns: `Σ_m (−z⁴xy²/16)(−3z²xy/16)^m`. -/
theorem marked_signed_excursion (z x y : ℝ) (h : |3 * z ^ 2 * x * y / 16| < 1) :
    HasSum (fun m : ℕ => (-(z ^ 4 * x * y ^ 2) / 16) * (-(3 * z ^ 2 * x * y) / 16) ^ m)
      (-(z ^ 4 * x * y ^ 2) / (16 + 3 * z ^ 2 * x * y)) := by
  have hr : ‖(-(3 * z ^ 2 * x * y) / 16)‖ < 1 := by
    rw [Real.norm_eq_abs, neg_div, abs_neg]; exact h
  have hg := (hasSum_geometric_of_norm_lt_one hr).mul_left (-(z ^ 4 * x * y ^ 2) / 16)
  convert hg using 1
  have h16 : (16 : ℝ) + 3 * z ^ 2 * x * y ≠ 0 := by
    intro h0
    have : 3 * z ^ 2 * x * y / 16 = -1 := by linarith
    rw [this] at h
    norm_num at h
  have h1 : (1 : ℝ) - -(3 * z ^ 2 * x * y) / 16 ≠ 0 := by
    intro h0
    apply h16
    linarith
  field_simp
  ring

/-- At `x = y = 1` the marked signed excursion is `Φ(z) = −z⁴/(16 + 3z²)`. -/
theorem marked_signed_excursion_one (z : ℝ) :
    -(z ^ 4 * 1 * 1 ^ 2) / (16 + 3 * z ^ 2 * 1 * 1) = -z ^ 4 / (16 + 3 * z ^ 2) := by
  ring

/-! ## The excursion at `z = 1` factorizes by its arrivals at the vector states -/

/-- `H(y) = y(1 + y)/(2(2 − y))`: the visits to the symmetric states between two arrivals at the vector states. -/
noncomputable def Hpgf (y : ℝ) : ℝ := y * (1 + y) / (2 * (2 - y))

/-- **The marked excursion at `z = 1`:** `F(1; x, y) = x² H(y)/(4 − 3x H(y))`. -/
theorem excursion_marked_factor (x y : ℝ) (hy : y ≠ 2) (hD : 4 - 3 * x * Hpgf y ≠ 0) :
    excursionF 1 x y = x ^ 2 * Hpgf y / (4 - 3 * x * Hpgf y) := by
  have h2 : (2 : ℝ) - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hy)
  have hden : excursionDen 1 x y = 2 * (2 - y) * (4 - 3 * x * Hpgf y) := by
    rw [excursionDen, Hpgf]
    field_simp
    ring
  have hden0 : excursionDen 1 x y ≠ 0 := by
    rw [hden]
    exact mul_ne_zero (mul_ne_zero two_ne_zero h2) hD
  rw [excursionF, hden]
  rw [Hpgf] at hD ⊢
  field_simp

/-- **By arrivals at the vector states:** `x²H/(4 − 3xH) = Σ_{q ≥ 2} (1/4)(3/4)^{q−2} x^q H^{q−1}`: `P(Q = q) =
(1/4)(3/4)^{q−2}` and `E[y^P | Q = q] = H(y)^{q−1}`. -/
theorem excursion_by_arrivals (x H : ℝ) (h : |3 * x * H / 4| < 1) :
    HasSum (fun m : ℕ => (1 / 4 * (3 / 4) ^ m) * (x ^ (m + 2) * H ^ (m + 1))) (x ^ 2 * H / (4 - 3 * x * H)) := by
  have hr : ‖3 * x * H / 4‖ < 1 := by rw [Real.norm_eq_abs]; exact h
  have hg := (hasSum_geometric_of_norm_lt_one hr).mul_left (x ^ 2 * H / 4)
  convert hg using 1
  · funext m
    ring
  · have h4 : (4 : ℝ) - 3 * x * H ≠ 0 := by
      intro h0
      have : 3 * x * H / 4 = 1 := by linarith
      rw [this] at h
      norm_num at h
    have h1 : (1 : ℝ) - 3 * x * H / 4 ≠ 0 := by
      intro h0; apply h4; linarith
    field_simp

theorem Hpgf_hasDerivAt (y : ℝ) (hy : y ≠ 2) :
    HasDerivAt Hpgf ((4 + 8 * y - 2 * y ^ 2) / (4 - 2 * y) ^ 2) y := by
  have h2 : (4 : ℝ) - 2 * y ≠ 0 := by intro h; apply hy; linarith
  have hN : HasDerivAt (fun y : ℝ => y + y ^ 2) (1 + 2 * y) y := by
    have := (hasDerivAt_id' y).add (hasDerivAt_pow 2 y)
    convert this using 1
    simp
  have hD : HasDerivAt (fun y : ℝ => 4 - 2 * y) (0 - 2 * 1) y :=
    (hasDerivAt_const y (4 : ℝ)).sub ((hasDerivAt_id' y).const_mul 2)
  have h := hN.div hD h2
  have e : Hpgf = fun y : ℝ => (y + y ^ 2) / (4 - 2 * y) := by
    funext y
    rw [Hpgf]
    ring
  rw [e]
  refine h.congr_deriv ?_
  field_simp
  ring

/-- **`H(1) = 1`, `H'(1) = 5/2`, `H''(1) = 6`**: mean `5/2`, variance `6 + 5/2 − (5/2)² = 9/4`. -/
theorem H_moments :
    Hpgf 1 = 1 ∧ deriv Hpgf 1 = 5 / 2 ∧ deriv (deriv Hpgf) 1 = 6 ∧
      (6 : ℝ) + 5 / 2 - (5 / 2) ^ 2 = 9 / 4 := by
  have hd : deriv Hpgf =ᶠ[nhds 1] fun y => (4 + 8 * y - 2 * y ^ 2) / (4 - 2 * y) ^ 2 := by
    filter_upwards [eventually_ne_nhds (show (1 : ℝ) ≠ 2 by norm_num)] with y hy
    exact (Hpgf_hasDerivAt y hy).deriv
  have h2 : HasDerivAt (fun y : ℝ => (4 + 8 * y - 2 * y ^ 2) / (4 - 2 * y) ^ 2) 6 1 := by
    have hN := ((hasDerivAt_const (1 : ℝ) (4 : ℝ)).add ((hasDerivAt_id' (1 : ℝ)).const_mul 8)).sub
        ((hasDerivAt_pow 2 (1 : ℝ)).const_mul 2)
    have hD := ((hasDerivAt_const (1 : ℝ) (4 : ℝ)).sub ((hasDerivAt_id' (1 : ℝ)).const_mul 2)).pow 2
    have h := hN.div hD (by norm_num)
    refine h.congr_deriv ?_
    norm_num
  refine ⟨by rw [Hpgf]; norm_num, ?_, ?_, by norm_num⟩
  · rw [(Hpgf_hasDerivAt 1 (by norm_num)).deriv]; norm_num
  · rw [hd.deriv_eq, h2.deriv]

/-- **`E(Q − 1) = 4`:** `Σ_{q ≥ 2} (q − 1)(1/4)(3/4)^{q−2} = 4`, and the arrivals' law sums to one. -/
theorem arrivals_mean :
    HasSum (fun m : ℕ => 1 / 4 * (3 / 4 : ℝ) ^ m) 1 ∧
      HasSum (fun m : ℕ => ((m : ℝ) + 1) * (1 / 4 * (3 / 4 : ℝ) ^ m)) 4 := by
  have hr : ‖(3 / 4 : ℝ)‖ < 1 := by rw [Real.norm_eq_abs]; norm_num [abs_of_pos]
  constructor
  · have := (hasSum_geometric_of_norm_lt_one hr).mul_left (1 / 4)
    convert this using 1
    norm_num
  · have h1 := (hasSum_coe_mul_geometric_of_norm_lt_one hr).mul_left (1 / 4)
    have h2 := (hasSum_geometric_of_norm_lt_one hr).mul_left (1 / 4)
    have := h1.add h2
    convert this using 1
    · funext m
      ring
    · norm_num

/-- **`E Var(P|Q) = (9/4) E(Q − 1) = 9 = Var P − Cov²/Var Q`.** -/
theorem expected_conditional_variance :
    HasSum (fun m : ℕ => (1 / 4 * (3 / 4 : ℝ) ^ m) * (((m : ℝ) + 1) * (9 / 4))) 9 ∧ (84 : ℝ) - 30 ^ 2 / 12 = 9 := by
  refine ⟨?_, by norm_num⟩
  have := arrivals_mean.2.mul_right (9 / 4)
  convert this using 1
  · funext m
    ring
  · norm_num

end Comparison.Article
