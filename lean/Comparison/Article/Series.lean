import Comparison.Law.Composite
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# The series of the law and of the level (Eqs. (47) to (49); Proposition 189)

* `kappa_in_u`, `kappa_series`, `kappa_series_bound` (**Eq. (47)**): with `w = u/(1 + 4u²)`,
  `κ(w) = 2w⁴/(1 − 5w²)² = 2u⁴/(1 + 3u² + 16u⁴)² = 2u⁴ − 12u⁶ − 10u⁸ + 360u¹⁰ + O(u¹²)`, with the remainder in
  closed form, `−2u¹²(555 + 5364u² + 16000u⁴ + 46080u⁶)/(1 + 3u² + 16u⁴)²`.
* `hasDerivAt_yR`, `level_derivatives`, `level_taylor` (**the level `δ₁` of Eq. (48)**): with `y = e^{δ₁} = 4u_c`,
  `y' = y(4 − 3y)/(8 − 3y)`, and the first four derivatives of `δ₁(S) = −log[(3 + (9 + 16e^{−S})^{1/2})/8]` at
  `S = 0` are `1/5`, `−12/125`, `12/3125`, `516/15625`: **`δ₁(S) = S/5 − (6/125)S² + (2/3125)S³ + d₄S⁴ + …`,
  `d₄ = 43/31250 = 0.0013760`**.
* `eigen_four`, `fourth_order_difference` (**Eq. (48), Proposition 189**): `Tr R⁴ = (1 − c)(S₁⁴ + S₂⁴) +
  c(S₁ + S₂)⁴ − 2c(1 − c)S₁²S₂²`, so through fourth order **the one composition differs from
  `(1 − c)δ_L + cδ_M` first by `−2c(1 − c)d₄S₁²S₂²`**.
* `equal_coupling_charpoly`, `equal_coupling_trace` (**Eq. (49)**): for `n + 1` lines of equal level `S` and equal
  coupling `g = c^{1/2}`, `R = S[(1 − g)I + g𝟙𝟙ᵀ]` has `det(X − R) = (X − (1 − g)S)ⁿ (X − (1 + ng)S)` for
  every `n`, so `Tr δ₁(R) = n δ₁((1 − g)S) + δ₁((1 + ng)S)`.
-/

namespace Comparison.Article

open Real Polynomial Comparison.Law

/-! ## Eq. (47): the series of `κ` -/

/-- **`κ` in the law's own variable:** `κ(w) = 2w⁴/(1 − 5w²)²` at `w = u/(1 + 4u²)` is
`2u⁴/(1 + 3u² + 16u⁴)²`. -/
theorem kappa_in_u (u : ℝ) :
    2 * (u / (1 + 4 * u ^ 2)) ^ 4 / (1 - 5 * (u / (1 + 4 * u ^ 2)) ^ 2) ^ 2 =
      2 * u ^ 4 / (1 + 3 * u ^ 2 + 16 * u ^ 4) ^ 2 := by
  have ha : (0 : ℝ) < 1 + 4 * u ^ 2 := by positivity
  have hb : (0 : ℝ) < 1 + 3 * u ^ 2 + 16 * u ^ 4 := by positivity
  have h5 : 1 - 5 * (u / (1 + 4 * u ^ 2)) ^ 2 = (1 + 3 * u ^ 2 + 16 * u ^ 4) / (1 + 4 * u ^ 2) ^ 2 := by
    field_simp
    ring
  rw [h5]
  field_simp

/-- **Eq. (47): the series of `κ` with its remainder in closed form.** -/
theorem kappa_series (u : ℝ) :
    2 * u ^ 4 / (1 + 3 * u ^ 2 + 16 * u ^ 4) ^ 2 =
      2 * u ^ 4 - 12 * u ^ 6 - 10 * u ^ 8 + 360 * u ^ 10 -
        2 * u ^ 12 * (555 + 5364 * u ^ 2 + 16000 * u ^ 4 + 46080 * u ^ 6) /
          (1 + 3 * u ^ 2 + 16 * u ^ 4) ^ 2 := by
  have hb : (0 : ℝ) < 1 + 3 * u ^ 2 + 16 * u ^ 4 := by positivity
  field_simp
  ring

/-- The remainder after `u¹⁰` is at most `2u¹²(555 + 5364u² + 16000u⁴ + 46080u⁶)`: the series is
`2u⁴ − 12u⁶ − 10u⁸ + 360u¹⁰ + O(u¹²)`. -/
theorem kappa_series_bound (u : ℝ) :
    |2 * u ^ 4 / (1 + 3 * u ^ 2 + 16 * u ^ 4) ^ 2 - (2 * u ^ 4 - 12 * u ^ 6 - 10 * u ^ 8 + 360 * u ^ 10)| ≤
      2 * u ^ 12 * (555 + 5364 * u ^ 2 + 16000 * u ^ 4 + 46080 * u ^ 6) := by
  rw [kappa_series]
  have hb : (1 : ℝ) ≤ (1 + 3 * u ^ 2 + 16 * u ^ 4) ^ 2 := by
    have : (1 : ℝ) ≤ 1 + 3 * u ^ 2 + 16 * u ^ 4 := by nlinarith [sq_nonneg u, sq_nonneg (u ^ 2)]
    nlinarith
  have hN : 0 ≤ 2 * u ^ 12 * (555 + 5364 * u ^ 2 + 16000 * u ^ 4 + 46080 * u ^ 6) := by positivity
  rw [show 2 * u ^ 4 - 12 * u ^ 6 - 10 * u ^ 8 + 360 * u ^ 10 -
      2 * u ^ 12 * (555 + 5364 * u ^ 2 + 16000 * u ^ 4 + 46080 * u ^ 6) / (1 + 3 * u ^ 2 + 16 * u ^ 4) ^ 2 -
      (2 * u ^ 4 - 12 * u ^ 6 - 10 * u ^ 8 + 360 * u ^ 10) =
      -(2 * u ^ 12 * (555 + 5364 * u ^ 2 + 16000 * u ^ 4 + 46080 * u ^ 6) /
        (1 + 3 * u ^ 2 + 16 * u ^ 4) ^ 2) by ring, abs_neg, abs_of_nonneg (by positivity)]
  exact div_le_self hN hb

/-! ## The level `δ₁` and its derivatives -/

/-- `y = 4u_c(S) = e^{δ₁(S)}`. -/
noncomputable def yR (S : ℝ) : ℝ := 4 * uLevel S

theorem yR_formula (S : ℝ) : yR S = 8 / (3 + √(9 + 16 * Real.exp (-S))) := by
  rw [yR, uLevel]
  ring

theorem rR_gt (S : ℝ) : 3 < √(9 + 16 * Real.exp (-S)) := by
  have h9 : √(9 : ℝ) = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [← h9]
  exact Real.sqrt_lt_sqrt (by norm_num) (by linarith [Real.exp_pos (-S)])

theorem yR_pos (S : ℝ) : 0 < yR S := by
  rw [yR_formula]
  have := rR_gt S
  positivity

theorem yR_lt (S : ℝ) : yR S < 4 / 3 := by
  have h := rR_gt S
  rw [yR_formula, div_lt_iff₀ (by linarith)]
  linarith

theorem den_pos (S : ℝ) : 0 < 8 - 3 * yR S := by linarith [yR_lt S]

theorem yR_zero : yR 0 = 1 := by
  rw [yR_formula, neg_zero, Real.exp_zero]
  rw [show (9 + 16 * 1 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num

theorem deltaLevel_eq_log (S : ℝ) : deltaLevel S = Real.log (yR S) := rfl

/-- `y' = y(4 − 3y)/(8 − 3y)`. -/
noncomputable def gR (y : ℝ) : ℝ := y * (4 - 3 * y) / (8 - 3 * y)

theorem hasDerivAt_yR (S : ℝ) : HasDerivAt yR (gR (yR S)) S := by
  have hr3 := rR_gt S
  have h1 : HasDerivAt (fun S => 9 + 16 * Real.exp (-S)) (16 * (Real.exp (-S) * (-1))) S :=
    (((Real.hasDerivAt_exp (-S)).comp S (hasDerivAt_neg S)).const_mul 16).const_add 9
  have h2 := h1.sqrt (by positivity)
  have h3 := (hasDerivAt_const S (8 : ℝ)).div ((hasDerivAt_const S (3 : ℝ)).add h2)
    (show (3 : ℝ) + √(9 + 16 * Real.exp (-S)) ≠ 0 by linarith)
  have e : yR = fun S => 8 / (3 + √(9 + 16 * Real.exp (-S))) := funext yR_formula
  rw [e]
  refine h3.congr_deriv ?_
  simp only [gR, Pi.add_apply]
  set r := √(9 + 16 * Real.exp (-S)) with hr
  have hrsq : r ^ 2 = 9 + 16 * Real.exp (-S) := Real.sq_sqrt (by positivity)
  have he : Real.exp (-S) = (r ^ 2 - 9) / 16 := by rw [hrsq]; ring
  rw [he]
  have hr0 : r ≠ 0 := by linarith
  have h3r : 3 + r ≠ 0 := by linarith
  have h8 : 8 - 3 * (8 / (3 + r)) = 8 * r / (3 + r) := by field_simp; ring
  rw [h8]
  field_simp
  ring

/-- `δ₁' = (4 − 3y)/(8 − 3y)`. -/
noncomputable def f1 (y : ℝ) : ℝ := (4 + (-3) * y ^ 1) / (8 - 3 * y) ^ 1
/-- `δ₁'' = −12y(4 − 3y)/(8 − 3y)³`. -/
noncomputable def f2 (y : ℝ) : ℝ := ((-48) * y ^ 1 + 36 * y ^ 2) / (8 - 3 * y) ^ 3
/-- `δ₁''' = 12y(4 − 3y)(9y² + 24y − 32)/(8 − 3y)⁵`. -/
noncomputable def f3 (y : ℝ) : ℝ :=
  ((-324) * y ^ 4 + (-432) * y ^ 3 + 2304 * y ^ 2 + (-1536) * y ^ 1) / (8 - 3 * y) ^ 5
/-- `δ₁'''' = −12y(4 − 3y)(81y⁴ + 1080y³ − 864y² − 1536y + 1024)/(8 − 3y)⁷`. -/
noncomputable def f4 (y : ℝ) : ℝ :=
  (2916 * y ^ 6 + 34992 * y ^ 5 + (-82944) * y ^ 4 + (-13824) * y ^ 3 + 110592 * y ^ 2 +
    (-49152) * y ^ 1) / (8 - 3 * y) ^ 7

theorem hasDerivAt_mono (c : ℝ) (k : ℕ) (y : ℝ) :
    HasDerivAt (fun y : ℝ => c * y ^ k) (c * ((k : ℝ) * y ^ (k - 1))) y :=
  (hasDerivAt_pow k y).const_mul c

theorem hasDerivAt_den (k : ℕ) (y : ℝ) :
    HasDerivAt (fun y : ℝ => (8 - 3 * y) ^ k) ((k : ℝ) * (8 - 3 * y) ^ (k - 1) * (0 - 3 * 1)) y :=
  ((hasDerivAt_const y (8 : ℝ)).sub ((hasDerivAt_id' y).const_mul 3)).pow k

theorem deriv_delta_eq (S : ℝ) : HasDerivAt deltaLevel (f1 (yR S)) S := by
  have h := (hasDerivAt_yR S).log (yR_pos S).ne'
  refine h.congr_deriv ?_
  have hy := (yR_pos S).ne'
  have hd := (den_pos S).ne'
  simp only [gR, f1]
  field_simp
  ring

theorem deriv_f1_eq (S : ℝ) : HasDerivAt (fun S => f1 (yR S)) (f2 (yR S)) S := by
  have hd := (den_pos S).ne'
  have hN := (hasDerivAt_const (yR S) (4 : ℝ)).add (hasDerivAt_mono (-3) 1 (yR S))
  have hf := hN.div (hasDerivAt_den 1 (yR S)) (pow_ne_zero _ hd)
  have h := hf.comp S (hasDerivAt_yR S)
  refine h.congr_deriv ?_
  simp only [gR, f2, Pi.add_apply]
  norm_num
  field_simp
  ring

theorem deriv_f2_eq (S : ℝ) : HasDerivAt (fun S => f2 (yR S)) (f3 (yR S)) S := by
  have hd := (den_pos S).ne'
  have hN := (hasDerivAt_mono (-48) 1 (yR S)).add (hasDerivAt_mono 36 2 (yR S))
  have hf := hN.div (hasDerivAt_den 3 (yR S)) (pow_ne_zero _ hd)
  have h := hf.comp S (hasDerivAt_yR S)
  refine h.congr_deriv ?_
  simp only [gR, f3, Pi.add_apply]
  norm_num
  field_simp
  ring

theorem deriv_f3_eq (S : ℝ) : HasDerivAt (fun S => f3 (yR S)) (f4 (yR S)) S := by
  have hd := (den_pos S).ne'
  have hN := (((hasDerivAt_mono (-324) 4 (yR S)).add (hasDerivAt_mono (-432) 3 (yR S))).add
    (hasDerivAt_mono 2304 2 (yR S))).add (hasDerivAt_mono (-1536) 1 (yR S))
  have hf := hN.div (hasDerivAt_den 5 (yR S)) (pow_ne_zero _ hd)
  have h := hf.comp S (hasDerivAt_yR S)
  refine h.congr_deriv ?_
  simp only [gR, f4, Pi.add_apply]
  norm_num
  field_simp
  ring

/-- **The derivatives of the level:** `δ₁^{(k)}(S) = f_k(e^{δ₁(S)})` for `k = 1, …, 4`. -/
theorem level_derivatives :
    iteratedDeriv 1 deltaLevel = (fun S => f1 (yR S)) ∧
      iteratedDeriv 2 deltaLevel = (fun S => f2 (yR S)) ∧
      iteratedDeriv 3 deltaLevel = (fun S => f3 (yR S)) ∧
      iteratedDeriv 4 deltaLevel = (fun S => f4 (yR S)) := by
  have d1 : iteratedDeriv 1 deltaLevel = fun S => f1 (yR S) := by
    rw [iteratedDeriv_succ, iteratedDeriv_zero]
    funext S
    exact (deriv_delta_eq S).deriv
  have d2 : iteratedDeriv 2 deltaLevel = fun S => f2 (yR S) := by
    rw [iteratedDeriv_succ, d1]
    funext S
    exact (deriv_f1_eq S).deriv
  have d3 : iteratedDeriv 3 deltaLevel = fun S => f3 (yR S) := by
    rw [iteratedDeriv_succ, d2]
    funext S
    exact (deriv_f2_eq S).deriv
  have d4 : iteratedDeriv 4 deltaLevel = fun S => f4 (yR S) := by
    rw [iteratedDeriv_succ, d3]
    funext S
    exact (deriv_f3_eq S).deriv
  exact ⟨d1, d2, d3, d4⟩

/-- **The level's Taylor coefficients at `S = 0`:** `δ₁(0) = 0` and `δ₁^{(k)}(0)/k! = 1/5, −6/125, 2/3125,
43/31250` for `k = 1, …, 4`: `δ₁(S) = S/5 − (6/125)S² + (2/3125)S³ + d₄S⁴ + O(S⁵)` with
**`d₄ = 43/31250 = 0.0013760`**. -/
theorem level_taylor :
    deltaLevel 0 = 0 ∧ iteratedDeriv 1 deltaLevel 0 = 1 / 5 ∧ iteratedDeriv 2 deltaLevel 0 / 2 = -6 / 125 ∧
      iteratedDeriv 3 deltaLevel 0 / 6 = 2 / 3125 ∧ iteratedDeriv 4 deltaLevel 0 / 24 = 43 / 31250 ∧
      (43 / 31250 : ℝ) = 0.0013760 := by
  obtain ⟨d1, d2, d3, d4⟩ := level_derivatives
  refine ⟨deltaLevel_zero, ?_, ?_, ?_, ?_, by norm_num⟩
  · rw [d1]; simp only [yR_zero, f1]; norm_num
  · rw [d2]; simp only [yR_zero, f2]; norm_num
  · rw [d3]; simp only [yR_zero, f3]; norm_num
  · rw [d4]; simp only [yR_zero, f4]; norm_num

/-! ## Eq. (48), Proposition 189: the fourth-order difference -/

/-- **`Tr R⁴ = (1 − c)(S₁⁴ + S₂⁴) + c(S₁ + S₂)⁴ − 2c(1 − c)S₁²S₂²`.** -/
theorem eigen_four (S₁ S₂ c : ℝ) (hd : 0 ≤ (S₁ - S₂) ^ 2 + 4 * c * S₁ * S₂) :
    eigenPlus S₁ S₂ c ^ 4 + eigenMinus S₁ S₂ c ^ 4 =
      (1 - c) * (S₁ ^ 4 + S₂ ^ 4) + c * (S₁ + S₂) ^ 4 - 2 * c * (1 - c) * S₁ ^ 2 * S₂ ^ 2 := by
  have h1 := eigen_sum S₁ S₂ c
  have h2 := eigen_prod S₁ S₂ c hd
  have e : eigenPlus S₁ S₂ c ^ 4 + eigenMinus S₁ S₂ c ^ 4 =
      ((eigenPlus S₁ S₂ c + eigenMinus S₁ S₂ c) ^ 2 - 2 * (eigenPlus S₁ S₂ c * eigenMinus S₁ S₂ c)) ^ 2 -
        2 * (eigenPlus S₁ S₂ c * eigenMinus S₁ S₂ c) ^ 2 := by ring
  rw [e, h1, h2]
  ring

/-- The level's Taylor polynomial to fourth order, `S/5 − (6/125)S² + (2/3125)S³ + d₄S⁴`. -/
noncomputable def levelT4 (d4 S : ℝ) : ℝ := S / 5 - 6 / 125 * S ^ 2 + 2 / 3125 * S ^ 3 + d4 * S ^ 4

/-- **The fourth-order difference (Eq. (48), Proposition 189):** on the two eigenvalues of `R`, the level's
fourth-order polynomial differs from `(1 − c)δ_L + cδ_M` by exactly `−2c(1 − c)d₄S₁²S₂²`; the orders one to
three agree. -/
theorem fourth_order_difference (S₁ S₂ c d4 : ℝ) (hd : 0 ≤ (S₁ - S₂) ^ 2 + 4 * c * S₁ * S₂) :
    levelT4 d4 (eigenPlus S₁ S₂ c) + levelT4 d4 (eigenMinus S₁ S₂ c) -
        ((1 - c) * (levelT4 d4 S₁ + levelT4 d4 S₂) + c * levelT4 d4 (S₁ + S₂)) =
      -2 * c * (1 - c) * d4 * S₁ ^ 2 * S₂ ^ 2 := by
  have h1 := eigen_sum S₁ S₂ c
  have h2 := eigen_sq S₁ S₂ c hd
  have h3 := eigen_cube S₁ S₂ c hd
  have h4 := eigen_four S₁ S₂ c hd
  simp only [levelT4]
  linear_combination (1 / 5 : ℝ) * h1 - 6 / 125 * h2 + 2 / 3125 * h3 + d4 * h4

/-! ## Eq. (49): equal coupling for every number of lines -/

/-- The meeting matrix of `n + 1` lines with equal coupling `g = c^{1/2}`: `(1 − g)I + g𝟙𝟙ᵀ`. -/
noncomputable def eqG (n : ℕ) (g : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  (1 - g) • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) + g • Matrix.of (fun _ _ => (1 : ℝ))

/-- **The equal-coupling eigenvalues for every `n`:** `det(X − S G) = (X − (1 − g)S)ⁿ (X − (1 + ng)S)`. -/
theorem equal_coupling_charpoly (n : ℕ) (S g : ℝ) :
    (S • eqG n g).charpoly = (X - C ((1 - g) * S)) ^ n * (X - C ((1 + n * g) * S)) := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hinf : ({(1 - g) * S}ᶜ : Set ℝ).Infinite := (Set.finite_singleton _).infinite_compl
  refine hinf.mono fun x hx => ?_
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
  show _ = _
  set a := x - (1 - g) * S with ha_def
  have ha : a ≠ 0 := sub_ne_zero.mpr hx
  have hM : Matrix.scalar (Fin (n + 1)) x - S • eqG n g =
      a • (1 + Matrix.replicateCol Unit (fun _ : Fin (n + 1) => -(S * g) / a) *
        Matrix.replicateRow Unit (fun _ : Fin (n + 1) => (1 : ℝ))) := by
    ext i j
    simp only [eqG, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.scalar_apply,
      Matrix.diagonal_apply, Matrix.one_apply, Matrix.of_apply, Matrix.mul_apply,
      Matrix.replicateCol_apply, Matrix.replicateRow_apply, smul_eq_mul, Finset.univ_unique,
      Finset.sum_singleton, mul_one]
    by_cases hij : i = j
    · simp only [hij, ↓reduceIte]
      field_simp
      ring
    · simp only [hij, ↓reduceIte]
      field_simp
      ring
  rw [Matrix.eval_charpoly, hM, Matrix.det_smul, Matrix.det_one_add_replicateCol_mul_replicateRow]
  simp only [dotProduct, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, Fintype.card_fin]
  rw [← ha_def, pow_succ]
  field_simp
  push_cast
  ring

/-- `Tr f(R)`: the sum of `f` over the eigenvalues of `R` with their multiplicities. -/
noncomputable def trF {n : ℕ} (f : ℝ → ℝ) (R : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (R.charpoly.roots.map f).sum

/-- **Eq. (49):** `Tr δ₁(R) = n δ₁((1 − g)S) + δ₁((1 + ng)S)` for `n + 1` lines of equal level and coupling. -/
theorem equal_coupling_trace (n : ℕ) (S g : ℝ) (f : ℝ → ℝ) :
    trF f (S • eqG n g) = n * f ((1 - g) * S) + f ((1 + n * g) * S) := by
  have hne : (X - C ((1 - g) * S)) ^ n * (X - C ((1 + n * g) * S)) ≠ 0 :=
    (((monic_X_sub_C _).pow n).mul (monic_X_sub_C _)).ne_zero
  rw [trF, equal_coupling_charpoly, roots_mul hne, roots_pow, roots_X_sub_C, roots_X_sub_C]
  simp [Multiset.map_nsmul, Multiset.sum_nsmul]

end Comparison.Article
