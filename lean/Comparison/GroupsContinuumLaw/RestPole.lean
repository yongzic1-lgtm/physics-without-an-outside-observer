import Mathlib

/-!
# The rest pole of the resolved law (the continuum limit, part two)

exact tuning to the rest zero. With `a = εΩ/√2` and the rest direction
`n = (1/√2, −1/√2, 0, 0, 0)`:

* `kappa ε w = (4/(5ε²))(cosh(εw/√2) − 1)(cosh(εw/√2) + 4)`; `continued_rest_symbol`: **the continued
  symbol at `p = −iωn` is `λ_ε(−iωn) = −κ_ε(ω)`**.
* `rest_pole_parameter`: with `s = 3 + 2cosh(εΩ/√2)` and **`u = 2/(s + √(s² − 16))`**,
  `u⁻¹ + 4u = s` and `(u⁻¹ + 4u)² = 25 + 5ε²κ_ε(Ω)`, so `M_ε(u)² = κ_ε(Ω)`: the scalar
  `Q = M_ε(u)² + λ_ε` vanishes at `p = −iΩn` (`rest_zero`); `uPole_bounds`: `0 < u ≤ 1/4`.
* `mass_parameter_inverse`: the subcritical root `u = 2/(s + √(s² − 16))`, `s = √(25 + 5ε²M²)`, has
  `(u⁻¹ + 4u)² = 25 + 5ε²M²` and `0 < u ≤ 1/4`.
* `kinetic_series`, `rest_series`: the coefficient certificates of
  `u = 1/4 − ε²M²/24 + 49ε⁴M⁴/4320 + O(ε⁶)` and `u = 1/4 − ε²Ω²/24 + 13ε⁴Ω⁴/1728 + O(ε⁶)`.
* `rest_kinetic_derivative`, `Zpole_pos`: `d/dω[κ(Ω) − κ(ω)] = −2ΩZ_ε(Ω)` at `ω = Ω` with
  `Z_ε(Ω) = √2(2cosh a + 3) sinh a/(5εΩ) > 0`: the pole is simple with residue `−1/(2ΩZ_ε)`.
-/

namespace Comparison.GroupsContinuumLaw

open Real

/-- `κ_ε(w) = (4/(5ε²))(cosh(εw/√2) − 1)(cosh(εw/√2) + 4)`. -/
noncomputable def kappaR (ε w : ℝ) : ℝ :=
  4 / (5 * ε ^ 2) * (cosh (ε * w / √2) - 1) * (cosh (ε * w / √2) + 4)

/-- The rest direction `n = (1/√2, −1/√2, 0, 0, 0)`. -/
noncomputable def restDir : Fin 5 → ℂ := ![1 / (√2 : ℂ), -1 / (√2 : ℂ), 0, 0, 0]

/-- The continued symbol `λ_ε(p) = (2/(5ε²)) Σ_{s<t} (1 − cos ε(p_s − p_t))`. -/
noncomputable def lamC (ε : ℂ) (p : Fin 5 → ℂ) : ℂ :=
  2 / (5 * ε ^ 2) * ∑ s : Fin 5, ∑ t : Fin 5,
    if s < t then 1 - Complex.cos (ε * (p s - p t)) else 0

theorem cos_neg_I_mul (y : ℝ) : Complex.cos (-(Complex.I * (y : ℂ))) = (cosh y : ℂ) := by
  rw [Complex.cos_neg, mul_comm, Complex.cos_mul_I, ← Complex.ofReal_cosh]

theorem sqrt2_ne : (√2 : ℝ) ≠ 0 := by positivity

theorem lamC_eq (ε : ℂ) (p : Fin 5 → ℂ) :
    lamC ε p = 2 / (5 * ε ^ 2) *
      ((1 - Complex.cos (ε * (p 0 - p 1))) + (1 - Complex.cos (ε * (p 0 - p 2))) +
        (1 - Complex.cos (ε * (p 0 - p 3))) + (1 - Complex.cos (ε * (p 0 - p 4))) +
        (1 - Complex.cos (ε * (p 1 - p 2))) + (1 - Complex.cos (ε * (p 1 - p 3))) +
        (1 - Complex.cos (ε * (p 1 - p 4))) + (1 - Complex.cos (ε * (p 2 - p 3))) +
        (1 - Complex.cos (ε * (p 2 - p 4))) + (1 - Complex.cos (ε * (p 3 - p 4)))) := by
  rw [lamC]
  congr 1
  simp only [Fin.sum_univ_five, Fin.isValue, Fin.reduceLT, ↓reduceIte, lt_self_iff_false]
  ring

/-- **The continued rest symbol:** `λ_ε(−iωn) = −κ_ε(ω)`. -/
theorem continued_rest_symbol (ε w : ℝ) (hε : ε ≠ 0) :
    lamC ε (fun i => -Complex.I * w * restDir i) = -(kappaR ε w : ℂ) := by
  set c : ℂ := 1 / (√2 : ℂ) with hc
  set b : ℝ := ε * w / √2 with hb
  have hbC : ((b : ℝ) : ℂ) = (ε : ℂ) * w * c := by
    rw [hb, hc]
    push_cast
    ring
  have hp : (fun i => -Complex.I * w * restDir i) = ![-Complex.I * w * c, Complex.I * w * c, 0, 0, 0] := by
    funext i
    fin_cases i <;> simp [restDir, hc] <;> ring
  rw [hp, lamC_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons, Fin.isValue]
  have e01 : (ε : ℂ) * (-Complex.I * w * c - Complex.I * w * c) = -(Complex.I * ((2 * b : ℝ) : ℂ)) := by
    push_cast
    rw [hbC]
    ring
  have e0k : (ε : ℂ) * (-Complex.I * w * c - 0) = -(Complex.I * ((b : ℝ) : ℂ)) := by
    rw [hbC]
    ring
  have e1k : (ε : ℂ) * (Complex.I * w * c - 0) = -(Complex.I * ((-b : ℝ) : ℂ)) := by
    push_cast
    rw [hbC]
    ring
  have ekl : (ε : ℂ) * ((0 : ℂ) - 0) = -(Complex.I * ((0 : ℝ) : ℂ)) := by simp
  rw [e01, e0k, e1k, ekl, cos_neg_I_mul, cos_neg_I_mul, cos_neg_I_mul, cos_neg_I_mul,
    Real.cosh_neg, Real.cosh_zero, Real.cosh_two_mul, Real.sinh_sq, kappaR, ← hb]
  have h5 : (5 : ℂ) * (ε : ℂ) ^ 2 ≠ 0 := by
    have : (ε : ℂ) ≠ 0 := by exact_mod_cast hε
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 this)
  push_cast
  field_simp
  ring

/-- `s = 3 + 2cosh(εΩ/√2)`. -/
noncomputable def sPole (ε Ω : ℝ) : ℝ := 3 + 2 * cosh (ε * Ω / √2)

/-- The rest pole `u = 2/(s + √(s² − 16))`. -/
noncomputable def uPole (ε Ω : ℝ) : ℝ := 2 / (sPole ε Ω + √(sPole ε Ω ^ 2 - 16))

theorem sPole_ge (ε Ω : ℝ) : 5 ≤ sPole ε Ω := by
  have := Real.one_le_cosh (ε * Ω / √2)
  rw [sPole]
  linarith

/-- For `s ≥ 5`, `u = 2/(s + √(s² − 16))` has `u⁻¹ + 4u = s` and `0 < u ≤ 1/4`. -/
theorem root_of_s (s : ℝ) (hs : 5 ≤ s) :
    (2 / (s + √(s ^ 2 - 16)))⁻¹ + 4 * (2 / (s + √(s ^ 2 - 16))) = s ∧
      0 < 2 / (s + √(s ^ 2 - 16)) ∧ 2 / (s + √(s ^ 2 - 16)) ≤ 1 / 4 := by
  have h16 : 0 ≤ s ^ 2 - 16 := by nlinarith
  have hr := Real.sq_sqrt h16
  have hr0 : 3 ≤ √(s ^ 2 - 16) := by
    rw [show (3 : ℝ) = √9 by rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hpos : 0 < s + √(s ^ 2 - 16) := by linarith
  refine ⟨?_, ?_, ?_⟩
  · field_simp
    nlinarith [hr]
  · positivity
  · rw [div_le_div_iff₀ hpos (by norm_num)]
    linarith

/-- **The exact tuning to the rest zero:** `(u⁻¹ + 4u)² = 25 + 5ε²κ_ε(Ω)` at `u = uPole ε Ω`. -/
theorem rest_pole_parameter (ε Ω : ℝ) (hε : ε ≠ 0) :
    ((uPole ε Ω)⁻¹ + 4 * uPole ε Ω) ^ 2 = 25 + 5 * ε ^ 2 * kappaR ε Ω := by
  obtain ⟨h1, _, _⟩ := root_of_s (sPole ε Ω) (sPole_ge ε Ω)
  rw [uPole, h1, sPole, kappaR]
  field_simp
  ring

theorem uPole_bounds (ε Ω : ℝ) : 0 < uPole ε Ω ∧ uPole ε Ω ≤ 1 / 4 := by
  obtain ⟨_, h2, h3⟩ := root_of_s (sPole ε Ω) (sPole_ge ε Ω)
  exact ⟨h2, h3⟩

/-- **The rest zero:** at `u = uPole ε Ω` the intercept equals `κ_ε(Ω)`, so the normalized scalar
`M_ε(u)² + λ_ε(p)` vanishes at the continued rest momentum `p = −iΩn`. -/
theorem rest_zero (ε Ω : ℝ) (hε : ε ≠ 0) :
    ((((uPole ε Ω)⁻¹ + 4 * uPole ε Ω) ^ 2 - 25) / (5 * ε ^ 2) : ℝ) = kappaR ε Ω ∧
      ((((uPole ε Ω)⁻¹ + 4 * uPole ε Ω) ^ 2 - 25) / (5 * ε ^ 2) : ℂ) +
        lamC ε (fun i => -Complex.I * Ω * restDir i) = 0 := by
  have h := rest_pole_parameter ε Ω hε
  have h5 : (5 : ℝ) * ε ^ 2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hε)
  have hreal : ((((uPole ε Ω)⁻¹ + 4 * uPole ε Ω) ^ 2 - 25) / (5 * ε ^ 2) : ℝ) = kappaR ε Ω := by
    rw [h, div_eq_iff h5]
    ring
  refine ⟨hreal, ?_⟩
  rw [continued_rest_symbol ε Ω hε]
  have hc : ((((uPole ε Ω)⁻¹ + 4 * uPole ε Ω) ^ 2 - 25) / (5 * ε ^ 2) : ℂ) = (kappaR ε Ω : ℂ) := by
    rw [← hreal]
    push_cast
    ring
  rw [hc]
  ring

/-- **The kinetic mass parameter:** `s = √(25 + 5ε²M²)`, `u = 2/(s + √(s² − 16))` has
`(u⁻¹ + 4u)² = 25 + 5ε²M²` and `0 < u ≤ 1/4`. -/
theorem mass_parameter_inverse (ε M : ℝ) :
    let s := √(25 + 5 * ε ^ 2 * M ^ 2)
    let u := 2 / (s + √(s ^ 2 - 16))
    (u⁻¹ + 4 * u) ^ 2 = 25 + 5 * ε ^ 2 * M ^ 2 ∧ 0 < u ∧ u ≤ 1 / 4 := by
  intro s u
  have h0 : 0 ≤ 25 + 5 * ε ^ 2 * M ^ 2 := by positivity
  have hs5 : 5 ≤ s := by
    rw [show (5 : ℝ) = √25 by rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (ε * M)])
  obtain ⟨h1, h2, h3⟩ := root_of_s s hs5
  refine ⟨?_, h2, h3⟩
  rw [h1, Real.sq_sqrt h0]

/-- **The kinetic-intercept series to fourth order:** `u_K = 1/4 − x/24 + 49x²/4320` solves
`(1 + 4u²)² = u²(25 + 5x)` up to `x³` (`x = ε²M²`); the certificate is exact. -/
theorem kinetic_series (x : ℝ) :
    (1 + 4 * (1 / 4 - x / 24 + 49 * x ^ 2 / 4320) ^ 2) ^ 2 -
        (1 / 4 - x / 24 + 49 * x ^ 2 / 4320) ^ 2 * (25 + 5 * x) =
      x ^ 3 * (-1441 / 51840 + 80329 / 18662400 * x - 5929 / 6220800 * x ^ 2 +
        112847 / 2519424000 * x ^ 3 - 117649 / 30233088000 * x ^ 4 +
        5764801 / 21767823360000 * x ^ 5) := by
  ring

/-- **The rest-pole series to fourth order:** `u_P = 1/4 − x/24 + 13x²/1728` solves
`1 + 4u² = u s` with `s = 5 + x/2 + x²/48 + O(x³)` (`x = ε²Ω²`, `s = 3 + 2cosh(εΩ/√2)`) up to
`x³`; the certificate is exact. -/
theorem rest_series (x : ℝ) :
    (1 + 4 * (1 / 4 - x / 24 + 13 * x ^ 2 / 1728) ^ 2) -
        (1 / 4 - x / 24 + 13 * x ^ 2 / 1728) * (5 + x / 2 + x ^ 2 / 48) =
      x ^ 3 * (-7 / 1296 + 13 / 186624 * x) := by
  ring

/-- The kinetic residue factor `Z_ε(Ω) = 2(2cosh a + 3) sinh a/(5εΩ√2)`, `a = εΩ/√2`
(`Zpole_eq`: this is `√2(2cosh a + 3) sinh a/(5εΩ)`). -/
noncomputable def Zpole (ε Ω : ℝ) : ℝ :=
  2 * (2 * cosh (ε * Ω / √2) + 3) * sinh (ε * Ω / √2) / (5 * ε * Ω * √2)

theorem Zpole_eq (ε Ω : ℝ) (hε : ε ≠ 0) (hΩ : Ω ≠ 0) :
    Zpole ε Ω = √2 * (2 * cosh (ε * Ω / √2) + 3) * sinh (ε * Ω / √2) / (5 * ε * Ω) := by
  have hs : (√2 : ℝ) * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs0 : (√2 : ℝ) ≠ 0 := sqrt2_ne
  rw [Zpole, div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (-5 * ε * Ω * (2 * cosh (ε * Ω / √2) + 3) * sinh (ε * Ω / √2)) * hs

theorem kappa_hasDerivAt (ε w : ℝ) :
    HasDerivAt (kappaR ε)
      (4 / (5 * ε ^ 2) * (ε / √2) * sinh (ε * w / √2) * (2 * cosh (ε * w / √2) + 3)) w := by
  have hb : HasDerivAt (fun w : ℝ => ε * w / √2) (ε / √2) w := by
    have := ((hasDerivAt_id w).const_mul ε).div_const √2
    simpa using this
  have hc : HasDerivAt (fun w : ℝ => cosh (ε * w / √2)) (sinh (ε * w / √2) * (ε / √2)) w :=
    (Real.hasDerivAt_cosh _).comp w hb
  have h1 := (hc.sub_const 1).const_mul (4 / (5 * ε ^ 2))
  have h2 := h1.mul (hc.add_const 4)
  have hk : kappaR ε = fun w => 4 / (5 * ε ^ 2) * (cosh (ε * w / √2) - 1) * (cosh (ε * w / √2) + 4) := by
    funext w
    rfl
  rw [hk]
  convert h2 using 1
  ring

/-- **The rest pole is simple:** `d/dω [κ_ε(Ω) − κ_ε(ω)]` at `ω = Ω` is `−2ΩZ_ε(Ω)`, so the scalar
`κ_ε(Ω) − κ_ε(ω)` has the residue `−1/(2ΩZ_ε(Ω))`. -/
theorem rest_kinetic_derivative (ε Ω : ℝ) (hε : ε ≠ 0) (hΩ : Ω ≠ 0) :
    HasDerivAt (fun w => kappaR ε Ω - kappaR ε w) (-2 * Ω * Zpole ε Ω) Ω := by
  have h := (hasDerivAt_const Ω (kappaR ε Ω)).sub (kappa_hasDerivAt ε Ω)
  convert h using 1
  have hs0 : (√2 : ℝ) ≠ 0 := sqrt2_ne
  rw [Zpole]
  field_simp
  ring

/-- **The residue factor is positive** for `ε, Ω > 0`. -/
theorem Zpole_pos (ε Ω : ℝ) (hε : 0 < ε) (hΩ : 0 < Ω) : 0 < Zpole ε Ω := by
  have ha : 0 < ε * Ω / √2 := by positivity
  have hsh : 0 < sinh (ε * Ω / √2) := Real.sinh_pos_iff.mpr ha
  have hch : 0 < 2 * cosh (ε * Ω / √2) + 3 := by
    have := Real.cosh_pos (ε * Ω / √2)
    linarith
  rw [Zpole]
  positivity

end Comparison.GroupsContinuumLaw
