module

public import Comparison.Existence.Excursion

/-!
# Book XV. The visits to the symmetric states of one excursion, and the vector pole (Propositions 84, 96)

The classes of Proposition 29
(`stype`): `0` the start's vertex, `1` a vector state reached from it, `2` a vector state reached from
a symmetric state, `3` a symmetric state reached from a vector state, `4` a symmetric state reached from a symmetric state.

* `class_steps`: on the eighty states, the four continuations go: from the vertex, four to class 1;
  from class 1, four to class 3; from class 2, one to the vertex and three to class 3; from class 3,
  one to class 2 and three to class 4; from class 4, two to class 2 and two to class 4.
* `excursion_system`: with `z` per step, `x` per arrival at a vector state and `y` per arrival at a symmetric
  state, the first-step equations of one excursion on these classes are solved by `g₁ = z³xy(1 + zy)/D`,
  `g₂ = 2z(2 − zy)/D`, `g₃ = z²x(1 + zy)/D`, `g₄ = 2z²x/D`, and the excursion
  `F(z, x, y) = zx g₁ = z⁴x²y(1 + zy)/D`, `D = 16 − 8zy − 3z²xy − 3z³xy²` (B.29);
  `excursion_system_unique`: they have no other solution.
* `GP_eq`: `G_P(y) = F(1, 1, y) = y(1 + y)/(16 − 11y − 3y²)`; `GP_one`: `G_P(1) = 1`;
  `GP_deriv`: `G_P′(1) = 10 = E P`.
* `GP_denominator`: `16 − 11x − 3x² = −3(x − x_c)(x − x_c′)`, `x_c = (√313 − 11)/6`,
  `x_c′ = (−√313 − 11)/6`; `xc_gt_one`: `x_c > 1`; `GP_denom_pos`: no zero on `[0, 1]`.
* `regression`: **(Prop. 96, S-B)** with `h(x) = x(1 + x)/(2(2 − x))`, the symmetric states between two arrivals
  at the vector states, `F(1; y, x) = y²h(x)/(4 − 3y h(x))` (B.29 with `x` per plane and `y` per arrival
  at the vector states) and `G_P = h/(4 − 3h)`; `pole_condition`: `(3/4)h(x) = 1 ⟺ 3x² + 11x − 16 = 0`.
* `pion_radius`: with each visit to the symmetric states carrying `e^{−Q²λ²/6}`, `d/dQ² G_P(e^{−Q²λ²/6}) = −10λ²/6` at
  `Q² = 0`, so `r_π² = 10λ²`; `vector_pole`: `e^{−Q²λ²/6} = x_c` exactly at
  `−Q² = 6 log(x_c)/λ²`.
-/

@[expose] public section

namespace Comparison

/-! ## The classes of the eighty states -/

/-- **The steps between the classes**, counted on all eighty states. -/
theorem class_steps : ∀ s : State,
    (stype s = 0 → (Finset.univ.filter fun s' => Continues s s' ∧ stype s' = 1).card = 4) ∧
    (stype s = 1 → (Finset.univ.filter fun s' => Continues s s' ∧ stype s' = 3).card = 4) ∧
    (stype s = 2 → (Finset.univ.filter fun s' => Continues s s' ∧ stype s' = 0).card = 1 ∧
      (Finset.univ.filter fun s' => Continues s s' ∧ stype s' = 3).card = 3) ∧
    (stype s = 3 → (Finset.univ.filter fun s' => Continues s s' ∧ stype s' = 2).card = 1 ∧
      (Finset.univ.filter fun s' => Continues s s' ∧ stype s' = 4).card = 3) ∧
    (stype s = 4 → (Finset.univ.filter fun s' => Continues s s' ∧ stype s' = 2).card = 2 ∧
      (Finset.univ.filter fun s' => Continues s s' ∧ stype s' = 4).card = 2) := by
  decide +kernel

/-! ## The excursion's first-step equations, with its visits to the symmetric states marked -/

section System

/-- B.29's denominator. -/
noncomputable def excursionDen (z x y : ℝ) : ℝ :=
  16 - 8 * z * y - 3 * z ^ 2 * x * y - 3 * z ^ 3 * x * y ^ 2

/-- **The excursion with its steps, arrivals at the vector states and visits to the symmetric states marked** (B.29). -/
noncomputable def excursionF (z x y : ℝ) : ℝ := z ^ 4 * x ^ 2 * y * (1 + z * y) / excursionDen z x y

/-- **The first-step equations and their solution:** with `D = excursionDen z x y`,
`g₁ = z³xy(1 + zy)/D`, `g₂ = 2z(2 − zy)/D`, `g₃ = z²x(1 + zy)/D`, `g₄ = 2z²x/D` solve `g₁ = zy g₃`,
`g₂ = z/4 + (3/4)zy g₃`, `g₃ = (1/4)zx g₂ + (3/4)zy g₄`, `g₄ = (2/4)zx g₂ + (2/4)zy g₄`, and the
excursion is `zx g₁ = F(z, x, y)`. -/
theorem excursion_system (z x y : ℝ) (hD : excursionDen z x y ≠ 0) :
    z ^ 3 * x * y * (1 + z * y) / excursionDen z x y =
        z * y * (z ^ 2 * x * (1 + z * y) / excursionDen z x y) ∧
      2 * z * (2 - z * y) / excursionDen z x y =
        z / 4 + 3 / 4 * z * y * (z ^ 2 * x * (1 + z * y) / excursionDen z x y) ∧
      z ^ 2 * x * (1 + z * y) / excursionDen z x y =
        1 / 4 * z * x * (2 * z * (2 - z * y) / excursionDen z x y) +
          3 / 4 * z * y * (2 * z ^ 2 * x / excursionDen z x y) ∧
      2 * z ^ 2 * x / excursionDen z x y =
        2 / 4 * z * x * (2 * z * (2 - z * y) / excursionDen z x y) +
          2 / 4 * z * y * (2 * z ^ 2 * x / excursionDen z x y) ∧
      z * x * (z ^ 3 * x * y * (1 + z * y) / excursionDen z x y) = excursionF z x y := by
  simp only [excursionF]
  generalize hd : excursionDen z x y = D at hD ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · field_simp
  · field_simp
    rw [← hd, excursionDen]
    ring
  · field_simp
    ring
  · field_simp
    ring
  · field_simp

/-- **The first-step equations have no other solution.** -/
theorem excursion_system_unique (z x y g₁ g₂ g₃ g₄ : ℝ) (hD : excursionDen z x y ≠ 0)
    (h2 : 2 - z * y ≠ 0)
    (e₁ : g₁ = z * y * g₃) (e₂ : g₂ = z / 4 + 3 / 4 * z * y * g₃)
    (e₃ : g₃ = 1 / 4 * z * x * g₂ + 3 / 4 * z * y * g₄)
    (e₄ : g₄ = 2 / 4 * z * x * g₂ + 2 / 4 * z * y * g₄) :
    z * x * g₁ = excursionF z x y := by
  have h4 : g₄ * (2 - z * y) = z * x * g₂ := by linear_combination 2 * e₄
  have h3 : 2 * (2 - z * y) * g₃ = z * x * (1 + z * y) * g₂ := by
    linear_combination (2 * (2 - z * y)) * e₃ + (3 / 2 * z * y) * h4
  have hg2 : g₂ * excursionDen z x y = 2 * z * (2 - z * y) := by
    simp only [excursionDen]
    linear_combination (8 * (2 - z * y)) * e₂ + (3 * z * y) * h3
  have hg3 : (2 - z * y) * (2 * (g₃ * excursionDen z x y) - 2 * (z ^ 2 * x * (1 + z * y))) = 0 := by
    linear_combination (excursionDen z x y) * h3 + (z * x * (1 + z * y)) * hg2
  have hg3D : g₃ * excursionDen z x y = z ^ 2 * x * (1 + z * y) := by
    rcases mul_eq_zero.mp hg3 with h | h
    · exact absurd h h2
    · linear_combination h / 2
  rw [excursionF, eq_div_iff hD, e₁]
  linear_combination (z ^ 2 * x * y) * hg3D

end System

/-! ## `G_P`: the visits to the symmetric states of one excursion -/

/-- `G_P(y) = y(1 + y)/(16 − 11y − 3y²)`. -/
noncomputable def GP (y : ℝ) : ℝ := y * (1 + y) / (16 - 11 * y - 3 * y ^ 2)

/-- **`G_P(y) = F(1, 1, y)`.** -/
theorem GP_eq (y : ℝ) : GP y = excursionF 1 1 y := by
  simp only [GP, excursionF, excursionDen]
  ring_nf

/-- **`G_P(1) = 1`.** -/
theorem GP_one : GP 1 = 1 := by
  norm_num [GP]

/-- **`G_P′(1) = 10 = E P`.** -/
theorem GP_deriv : HasDerivAt GP 10 1 := by
  have hf : HasDerivAt (fun y : ℝ => y * (1 + y)) 3 1 :=
    ((hasDerivAt_id (1 : ℝ)).mul ((hasDerivAt_id (1 : ℝ)).const_add 1)).congr_deriv
      (by simp; norm_num)
  have hg : HasDerivAt (fun y : ℝ => 16 - 11 * y - 3 * y ^ 2) (-17) 1 :=
    ((((hasDerivAt_id (1 : ℝ)).const_mul 11).const_sub 16).sub
      ((hasDerivAt_pow 2 (1 : ℝ)).const_mul 3)).congr_deriv (by simp; norm_num)
  have := hf.div hg (by norm_num)
  exact this.congr_deriv (by norm_num)

/-- The vector pole: `x_c = (√313 − 11)/6`. -/
noncomputable def xc : ℝ := (Real.sqrt 313 - 11) / 6

/-- The other root, `(−√313 − 11)/6`. -/
noncomputable def xc' : ℝ := (-Real.sqrt 313 - 11) / 6

/-- **`16 − 11x − 3x² = −3(x − x_c)(x − x_c′)`.** -/
theorem GP_denominator (x : ℝ) : 16 - 11 * x - 3 * x ^ 2 = -3 * (x - xc) * (x - xc') := by
  have hs : Real.sqrt 313 ^ 2 = 313 := Real.sq_sqrt (by norm_num)
  simp only [xc, xc']
  linear_combination (-1 / 12 : ℝ) * hs

theorem xc_gt_one : 1 < xc := by
  have h17 : (17 : ℝ) < Real.sqrt 313 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  simp only [xc]
  linarith

theorem xc'_neg : xc' < 0 := by
  have := Real.sqrt_nonneg 313
  simp only [xc']
  linarith

/-- **`G_P` has no pole on `[0, 1]`.** -/
theorem GP_denom_pos (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) : 0 < 16 - 11 * x - 3 * x ^ 2 := by
  nlinarith

theorem xc_root : 3 * xc ^ 2 + 11 * xc - 16 = 0 := by
  have := GP_denominator xc
  simp only [sub_self, mul_zero, zero_mul] at this
  linarith

/-! ## Prop. 96: the symmetric states between two arrivals at the vector states -/

/-- The symmetric states between two arrivals at the vector states: `h(x) = x(1 + x)/(2(2 − x))`. -/
noncomputable def gapF (x : ℝ) : ℝ := x * (1 + x) / (2 * (2 - x))

/-- **The regression law:** with `x` per visit to the symmetric states and `y` per arrival at the vector states,
`F(1; y, x) = y²h(x)/(4 − 3y h(x))`, and `G_P = h/(4 − 3h)`. -/
theorem regression (x y : ℝ) (hx : x ≠ 2) (hD : excursionDen 1 y x ≠ 0) :
    excursionF 1 y x = y ^ 2 * gapF x / (4 - 3 * y * gapF x) ∧
      GP x = gapF x / (4 - 3 * gapF x) := by
  have h2 : (2 : ℝ) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  have hD' : 16 - 8 * x - 3 * y * x - 3 * y * x ^ 2 ≠ 0 := by
    simpa [excursionDen, mul_comm, mul_assoc, mul_left_comm] using hD
  have e4 : 4 - 3 * y * gapF x = (16 - 8 * x - 3 * y * x - 3 * y * x ^ 2) / (2 * (2 - x)) := by
    simp only [gapF]
    field_simp
    ring
  constructor
  · rw [e4]
    simp only [excursionF, excursionDen, gapF]
    field_simp
  · simp only [GP, gapF]
    by_cases hz : 16 - 11 * x - 3 * x ^ 2 = 0
    · have e : (4 : ℝ) - 3 * (x * (1 + x) / (2 * (2 - x))) =
          (16 - 11 * x - 3 * x ^ 2) / (2 * (2 - x)) := by
        field_simp
        ring
      rw [e, hz]
      simp
    · field_simp
      ring

/-- **The vector pole condition:** `(3/4)h(x) = 1 ⟺ 3x² + 11x − 16 = 0` (for `x ≠ 2`). -/
theorem pole_condition (x : ℝ) (hx : x ≠ 2) : 3 / 4 * gapF x = 1 ↔ 3 * x ^ 2 + 11 * x - 16 = 0 := by
  have h2 : (2 : ℝ) - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx)
  simp only [gapF]
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    field_simp
    linarith

/-! ## One step of extent per visit to the symmetric states -/

/-- **The pion's radius:** with `e^{−Q²λ²/6}` per visit to the symmetric states, `d/dQ² G_P(e^{−Q²λ²/6}) = −10λ²/6`
at `Q² = 0`; so `r_π² = −6·(−10λ²/6) = 10λ² = E P λ²`. -/
theorem pion_radius (lam : ℝ) :
    HasDerivAt (fun q : ℝ => GP (Real.exp (-(q * lam ^ 2) / 6))) (10 * (-(lam ^ 2) / 6)) 0 ∧
      -6 * (10 * (-(lam ^ 2) / 6)) = 10 * lam ^ 2 := by
  constructor
  · have hin : HasDerivAt (fun q : ℝ => -(q * lam ^ 2) / 6) (-(lam ^ 2) / 6) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).mul_const (lam ^ 2)).neg).div_const 6
      simpa using this
    have hexp := hin.exp
    have h1 : Real.exp (-(0 * lam ^ 2) / 6) = 1 := by simp
    rw [h1] at hexp
    have hG : HasDerivAt GP 10 (Real.exp (-(0 * lam ^ 2) / 6)) := by rw [h1]; exact GP_deriv
    have := hG.comp (0 : ℝ) hexp
    simpa [Function.comp_def] using this
  · ring

/-- **The vector pole:** `e^{−Q²λ²/6} = x_c` exactly at `−Q² = 6 log(x_c)/λ²`. -/
theorem vector_pole (lam q : ℝ) (hl : lam ≠ 0) :
    Real.exp (-(q * lam ^ 2) / 6) = xc ↔ -q = 6 * Real.log xc / lam ^ 2 := by
  have hx : 0 < xc := lt_trans one_pos xc_gt_one
  have hl2 : lam ^ 2 ≠ 0 := pow_ne_zero 2 hl
  constructor
  · intro h
    have := congrArg Real.log h
    rw [Real.log_exp] at this
    field_simp
    linarith
  · intro h
    rw [← Real.exp_log hx]
    congr 1
    field_simp at h
    linarith

end Comparison

end
