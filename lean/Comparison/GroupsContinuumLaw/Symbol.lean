import Mathlib

/-!
# The symbol of the resolved law and the norm bound `5π²ε²/24` (the continuum limit, part three)

resolvent limit. The second-sheet Schur complement (`Schur.lean`) has, in a Fourier fibre with
momentum `p ∈ W = 𝟏^⊥ ⊂ ℝ⁵` (`Σ p = 0`), the symbol
`λ_ε(p) = (2/(5ε²)) Σ_{s<t} (1 − cos ε(p_s − p_t))`. Proved here:

* `cos_le_quartic`: `cos x ≤ 1 − x²/2 + x⁴/24`; `two_div_pi_sq_le`: `2x²/π² ≤ 1 − cos x` for `|x| ≤ π`.
* `roots_quadratic`, `roots_quartic_bound`, `basis_root_lower`: on `W`,
  `Σ_{s<t}(p_s − p_t)² = 5|p|²`, `Σ_{s<t}(p_s − p_t)⁴ ≤ 10|p|⁴`, `|p|² ≤ Σ_{i<4}(p_i − p_4)²`.
* `lambda_nonneg`, `lambda_error`: **`0 ≤ |p|² − λ_ε(p) ≤ ε²|p|⁴/6`**;
  `lambda_cell_lower`: on the reciprocal cell `|ε(p_i − p_4)| ≤ π`, **`λ_ε(p) ≥ 4|p|²/(5π²)`**.
* `inverse_symbol_bound`: on the cell, **`|(M² + λ_ε)⁻¹ − (M² + |p|²)⁻¹| ≤ 5π²ε²/24`**;
  `outside_cell_inverse_bound`: off the cell `(M² + |p|²)⁻¹ ≤ 2ε²/π² ≤ 5π²ε²/24`.
* `multiplier_bound`: the interpolated lattice resolvent (the lattice multiplier on the cell, extended
  by zero) and the continuum resolvent `(M² − Δ)⁻¹` differ by at most `5π²ε²/24` at every momentum of
  `W`; `resolvent_norm_bound`: **as operators on `L²` of the momenta (any measure carried by `W`, the
  Lebesgue measure on `W` or the finite Fourier modes of a torus), `‖(R_ε − R_0)f‖₂ ≤ (5π²ε²/24)‖f‖₂`**;
  by Plancherel this is the position-space operator norm.
-/

namespace Comparison.GroupsContinuumLaw

open Real MeasureTheory

/-! ## Two cosine inequalities -/

/-- **`cos x ≤ 1 − x²/2 + x⁴/24`** for every real `x`. -/
theorem cos_le_quartic (x : ℝ) : cos x ≤ 1 - x ^ 2 / 2 + x ^ 4 / 24 := by
  have key : ∀ y : ℝ, 0 ≤ y → cos y ≤ 1 - y ^ 2 / 2 + y ^ 4 / 24 := by
    intro y hy
    let f : ℝ → ℝ := fun x => 1 - x ^ 2 / 2 + x ^ 4 / 24 - cos x
    have hd : ∀ x, HasDerivAt f (-x + x ^ 3 / 6 + sin x) x := by
      intro x
      have h1 : HasDerivAt (fun x : ℝ => x ^ 2 / 2) x x := by
        have := ((hasDerivAt_pow 2 x).div_const 2)
        convert this using 1
        ring
      have h2 : HasDerivAt (fun x : ℝ => x ^ 4 / 24) (x ^ 3 / 6) x := by
        have := ((hasDerivAt_pow 4 x).div_const 24)
        convert this using 1
        ring
      have h3 := ((h1.const_sub 1).add h2).sub (Real.hasDerivAt_cos x)
      convert h3 using 1
      ring
    have hmono : MonotoneOn f (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · exact fun x _ => (hd x).continuousAt.continuousWithinAt
      · exact fun x _ => (hd x).differentiableAt.differentiableWithinAt
      · intro x hx
        rw [interior_Ici] at hx
        rw [(hd x).deriv]
        have := Real.sin_ge_sub_cube (le_of_lt hx)
        linarith
    have h0 : f 0 ≤ f y := hmono Set.self_mem_Ici hy hy
    simp only [f] at h0
    simp at h0
    linarith
  rcases le_total 0 x with h | h
  · exact key x h
  · have := key (-x) (by linarith)
    rw [Real.cos_neg] at this
    have e2 : (-x) ^ 2 = x ^ 2 := by ring
    have e4 : (-x) ^ 4 = x ^ 4 := by ring
    rw [e2, e4] at this
    exact this

/-- **`2x²/π² ≤ 1 − cos x`** for `|x| ≤ π`. -/
theorem two_div_pi_sq_le (x : ℝ) (hx : |x| ≤ π) : 2 * x ^ 2 / π ^ 2 ≤ 1 - cos x := by
  have hc : 1 - cos x = 2 * sin (|x| / 2) ^ 2 := by
    have h1 : cos x = cos |x| := by
      rcases le_total 0 x with h | h
      · rw [abs_of_nonneg h]
      · rw [abs_of_nonpos h, Real.cos_neg]
    rw [h1]
    have h2 : cos |x| = 1 - 2 * sin (|x| / 2) ^ 2 := by
      rw [show |x| = 2 * (|x| / 2) by ring, Real.cos_two_mul, Real.cos_sq']
      ring_nf
    rw [h2]
    ring
  have hy0 : 0 ≤ |x| / 2 := by positivity
  have hy1 : |x| / 2 ≤ π / 2 := by linarith
  have hs := Real.mul_le_sin hy0 hy1
  have hpi : 0 < π := Real.pi_pos
  have hs0 : 0 ≤ 2 / π * (|x| / 2) := by positivity
  have hsq : (2 / π * (|x| / 2)) ^ 2 ≤ sin (|x| / 2) ^ 2 := pow_le_pow_left₀ hs0 hs 2
  have e : (2 / π * (|x| / 2)) ^ 2 = x ^ 2 / π ^ 2 := by
    rw [show (2 / π * (|x| / 2)) = |x| / π by field_simp, div_pow, sq_abs]
  rw [hc]
  rw [e] at hsq
  have : 2 * x ^ 2 / π ^ 2 = 2 * (x ^ 2 / π ^ 2) := by ring
  rw [this]
  linarith

/-! ## Sums over the ten pairs -/

/-- A sum over the ten pairs `s < t` of five lines. -/
def pairSum (f : Fin 5 → Fin 5 → ℝ) : ℝ := ∑ s : Fin 5, ∑ t : Fin 5, if s < t then f s t else 0

theorem pairSum_eq (f : Fin 5 → Fin 5 → ℝ) :
    pairSum f = f 0 1 + f 0 2 + f 0 3 + f 0 4 + f 1 2 + f 1 3 + f 1 4 + f 2 3 + f 2 4 + f 3 4 := by
  rw [pairSum]
  simp only [Fin.sum_univ_five, Fin.isValue, Fin.reduceLT, ↓reduceIte, lt_self_iff_false]
  ring

/-- `|p|² = Σ p_i²`. -/
def norm2 (p : Fin 5 → ℝ) : ℝ := ∑ i, p i ^ 2

theorem norm2_nonneg (p : Fin 5 → ℝ) : 0 ≤ norm2 p := Finset.sum_nonneg fun i _ => sq_nonneg _

theorem norm2_expand (p : Fin 5 → ℝ) :
    norm2 p = p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 + p 4 ^ 2 := by
  rw [norm2, Fin.sum_univ_five]

theorem last_of_sum (p : Fin 5 → ℝ) (hp : ∑ i, p i = 0) : p 4 = -(p 0 + p 1 + p 2 + p 3) := by
  rw [Fin.sum_univ_five] at hp
  linarith

/-- **`Σ_{s<t} (p_s − p_t)² = 5|p|²`** on `W`. -/
theorem roots_quadratic (p : Fin 5 → ℝ) (hp : ∑ i, p i = 0) :
    pairSum (fun s t => (p s - p t) ^ 2) = 5 * norm2 p := by
  rw [pairSum_eq, norm2_expand, last_of_sum p hp]
  ring

theorem pair_le_two_norm (p : Fin 5 → ℝ) (s t : Fin 5) (hst : s ≠ t) :
    (p s - p t) ^ 2 ≤ 2 * norm2 p := by
  have h1 : (p s - p t) ^ 2 ≤ 2 * (p s ^ 2 + p t ^ 2) := by nlinarith [sq_nonneg (p s + p t)]
  have h2 : p s ^ 2 + p t ^ 2 ≤ norm2 p := by
    have := Finset.sum_le_sum_of_subset_of_nonneg (s := {s, t}) (t := Finset.univ)
      (f := fun i => p i ^ 2) (Finset.subset_univ _) (fun i _ _ => sq_nonneg _)
    rwa [Finset.sum_pair hst] at this
  linarith

/-- **`Σ_{s<t} (p_s − p_t)⁴ ≤ 10|p|⁴`** on `W`. -/
theorem roots_quartic_bound (p : Fin 5 → ℝ) (hp : ∑ i, p i = 0) :
    pairSum (fun s t => (p s - p t) ^ 4) ≤ 10 * norm2 p ^ 2 := by
  have hq : ∀ s t : Fin 5, s ≠ t → (p s - p t) ^ 4 ≤ 2 * norm2 p * (p s - p t) ^ 2 := by
    intro s t hst
    have h := pair_le_two_norm p s t hst
    have e : (p s - p t) ^ 4 = (p s - p t) ^ 2 * (p s - p t) ^ 2 := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right h (sq_nonneg _)
  have hsum := roots_quadratic p hp
  rw [pairSum_eq] at hsum ⊢
  have h2 := congrArg (fun x => 2 * norm2 p * x) hsum
  have := hq 0 1 (by decide); have := hq 0 2 (by decide); have := hq 0 3 (by decide)
  have := hq 0 4 (by decide); have := hq 1 2 (by decide); have := hq 1 3 (by decide)
  have := hq 1 4 (by decide); have := hq 2 3 (by decide); have := hq 2 4 (by decide)
  have := hq 3 4 (by decide)
  nlinarith

/-- **`|p|² ≤ Σ_{i<4} (p_i − p_4)²`** on `W`. -/
theorem basis_root_lower (p : Fin 5 → ℝ) (hp : ∑ i, p i = 0) :
    norm2 p ≤ (p 0 - p 4) ^ 2 + (p 1 - p 4) ^ 2 + (p 2 - p 4) ^ 2 + (p 3 - p 4) ^ 2 := by
  have e : (p 0 - p 4) ^ 2 + (p 1 - p 4) ^ 2 + (p 2 - p 4) ^ 2 + (p 3 - p 4) ^ 2 =
      norm2 p + 5 * p 4 ^ 2 := by
    rw [norm2_expand, last_of_sum p hp]
    ring
  rw [e]
  nlinarith [sq_nonneg (p 4)]

/-! ## The symbol -/

/-- **The symbol** `λ_ε(p) = (2/(5ε²)) Σ_{s<t} (1 − cos ε(p_s − p_t))`. -/
noncomputable def lam (ε : ℝ) (p : Fin 5 → ℝ) : ℝ :=
  2 / (5 * ε ^ 2) * pairSum (fun s t => 1 - cos (ε * (p s - p t)))

theorem lam_nonneg (ε : ℝ) (p : Fin 5 → ℝ) : 0 ≤ lam ε p := by
  rw [lam]
  apply mul_nonneg (by positivity)
  rw [pairSum_eq]
  have h : ∀ x : ℝ, 0 ≤ 1 - cos x := fun x => by linarith [Real.cos_le_one x]
  linarith [h (ε * (p 0 - p 1)), h (ε * (p 0 - p 2)), h (ε * (p 0 - p 3)), h (ε * (p 0 - p 4)),
    h (ε * (p 1 - p 2)), h (ε * (p 1 - p 3)), h (ε * (p 1 - p 4)), h (ε * (p 2 - p 3)),
    h (ε * (p 2 - p 4)), h (ε * (p 3 - p 4))]

/-- One pair: `0 ≤ d²/5 − (2/(5ε²))(1 − cos εd) ≤ ε²d⁴/60`. -/
theorem pair_error (ε d : ℝ) (hε : ε ≠ 0) :
    0 ≤ d ^ 2 / 5 - 2 / (5 * ε ^ 2) * (1 - cos (ε * d)) ∧
      d ^ 2 / 5 - 2 / (5 * ε ^ 2) * (1 - cos (ε * d)) ≤ ε ^ 2 * d ^ 4 / 60 := by
  have hk : 0 < 2 / (5 * ε ^ 2) := by positivity
  have hlo := Real.one_sub_sq_div_two_le_cos (x := ε * d)
  have hhi := cos_le_quartic (ε * d)
  have e1 : 2 / (5 * ε ^ 2) * ((ε * d) ^ 2 / 2) = d ^ 2 / 5 := by field_simp
  have e2 : 2 / (5 * ε ^ 2) * ((ε * d) ^ 2 / 2 - (ε * d) ^ 4 / 24) = d ^ 2 / 5 - ε ^ 2 * d ^ 4 / 60 := by
    field_simp
    ring
  have a1 : 2 / (5 * ε ^ 2) * (1 - cos (ε * d)) ≤ 2 / (5 * ε ^ 2) * ((ε * d) ^ 2 / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hk.le
  have a2 : 2 / (5 * ε ^ 2) * ((ε * d) ^ 2 / 2 - (ε * d) ^ 4 / 24) ≤
      2 / (5 * ε ^ 2) * (1 - cos (ε * d)) :=
    mul_le_mul_of_nonneg_left (by linarith) hk.le
  constructor <;> linarith

/-- **`0 ≤ |p|² − λ_ε(p) ≤ ε²|p|⁴/6`** on `W`. -/
theorem lambda_error (ε : ℝ) (hε : ε ≠ 0) (p : Fin 5 → ℝ) (hp : ∑ i, p i = 0) :
    0 ≤ norm2 p - lam ε p ∧ norm2 p - lam ε p ≤ ε ^ 2 / 6 * norm2 p ^ 2 := by
  have hq := roots_quadratic p hp
  have h4 := roots_quartic_bound p hp
  rw [pairSum_eq] at hq h4
  have e : norm2 p - lam ε p =
      ((p 0 - p 1) ^ 2 / 5 - 2 / (5 * ε ^ 2) * (1 - cos (ε * (p 0 - p 1)))) +
      ((p 0 - p 2) ^ 2 / 5 - 2 / (5 * ε ^ 2) * (1 - cos (ε * (p 0 - p 2)))) +
      ((p 0 - p 3) ^ 2 / 5 - 2 / (5 * ε ^ 2) * (1 - cos (ε * (p 0 - p 3)))) +
      ((p 0 - p 4) ^ 2 / 5 - 2 / (5 * ε ^ 2) * (1 - cos (ε * (p 0 - p 4)))) +
      ((p 1 - p 2) ^ 2 / 5 - 2 / (5 * ε ^ 2) * (1 - cos (ε * (p 1 - p 2)))) +
      ((p 1 - p 3) ^ 2 / 5 - 2 / (5 * ε ^ 2) * (1 - cos (ε * (p 1 - p 3)))) +
      ((p 1 - p 4) ^ 2 / 5 - 2 / (5 * ε ^ 2) * (1 - cos (ε * (p 1 - p 4)))) +
      ((p 2 - p 3) ^ 2 / 5 - 2 / (5 * ε ^ 2) * (1 - cos (ε * (p 2 - p 3)))) +
      ((p 2 - p 4) ^ 2 / 5 - 2 / (5 * ε ^ 2) * (1 - cos (ε * (p 2 - p 4)))) +
      ((p 3 - p 4) ^ 2 / 5 - 2 / (5 * ε ^ 2) * (1 - cos (ε * (p 3 - p 4)))) := by
    rw [lam, pairSum_eq]
    linear_combination (-1 / 5 : ℝ) * hq
  rw [e]
  obtain ⟨a01, b01⟩ := pair_error ε (p 0 - p 1) hε
  obtain ⟨a02, b02⟩ := pair_error ε (p 0 - p 2) hε
  obtain ⟨a03, b03⟩ := pair_error ε (p 0 - p 3) hε
  obtain ⟨a04, b04⟩ := pair_error ε (p 0 - p 4) hε
  obtain ⟨a12, b12⟩ := pair_error ε (p 1 - p 2) hε
  obtain ⟨a13, b13⟩ := pair_error ε (p 1 - p 3) hε
  obtain ⟨a14, b14⟩ := pair_error ε (p 1 - p 4) hε
  obtain ⟨a23, b23⟩ := pair_error ε (p 2 - p 3) hε
  obtain ⟨a24, b24⟩ := pair_error ε (p 2 - p 4) hε
  obtain ⟨a34, b34⟩ := pair_error ε (p 3 - p 4) hε
  have h4' := mul_le_mul_of_nonneg_left h4 (show (0 : ℝ) ≤ ε ^ 2 / 60 by positivity)
  generalize p 0 - p 1 = d01 at *
  generalize p 0 - p 2 = d02 at *
  generalize p 0 - p 3 = d03 at *
  generalize p 0 - p 4 = d04 at *
  generalize p 1 - p 2 = d12 at *
  generalize p 1 - p 3 = d13 at *
  generalize p 1 - p 4 = d14 at *
  generalize p 2 - p 3 = d23 at *
  generalize p 2 - p 4 = d24 at *
  generalize p 3 - p 4 = d34 at *
  generalize norm2 p = P at *
  constructor
  · linarith
  · linarith

/-- **On the reciprocal cell the symbol is elliptic:** `λ_ε(p) ≥ 4|p|²/(5π²)`. -/
theorem lambda_cell_lower (ε : ℝ) (hε : ε ≠ 0) (p : Fin 5 → ℝ) (hp : ∑ i, p i = 0)
    (hcell : ∀ i : Fin 4, |ε * (p i.castSucc - p 4)| ≤ π) :
    4 / (5 * π ^ 2) * norm2 p ≤ lam ε p := by
  have hpi : 0 < π := Real.pi_pos
  have c0 := two_div_pi_sq_le _ (hcell 0)
  have c1 := two_div_pi_sq_le _ (hcell 1)
  have c2 := two_div_pi_sq_le _ (hcell 2)
  have c3 := two_div_pi_sq_le _ (hcell 3)
  simp only [Fin.isValue, Fin.castSucc_zero, Fin.castSucc_one] at c0 c1 c2 c3
  have hz : ∀ x : ℝ, 0 ≤ 1 - cos x := fun x => by linarith [Real.cos_le_one x]
  have hb := basis_root_lower p hp
  have hk : 0 < 2 / (5 * ε ^ 2) := by positivity
  rw [lam, pairSum_eq]
  have hsum : 2 * (ε * (p 0 - p 4)) ^ 2 / π ^ 2 + 2 * (ε * (p 1 - p 4)) ^ 2 / π ^ 2 +
      2 * (ε * (p 2 - p 4)) ^ 2 / π ^ 2 + 2 * (ε * (p 3 - p 4)) ^ 2 / π ^ 2 ≤
      (1 - cos (ε * (p 0 - p 1))) + (1 - cos (ε * (p 0 - p 2))) + (1 - cos (ε * (p 0 - p 3))) +
      (1 - cos (ε * (p 0 - p 4))) + (1 - cos (ε * (p 1 - p 2))) + (1 - cos (ε * (p 1 - p 3))) +
      (1 - cos (ε * (p 1 - p 4))) + (1 - cos (ε * (p 2 - p 3))) + (1 - cos (ε * (p 2 - p 4))) +
      (1 - cos (ε * (p 3 - p 4))) := by
    have e2 : (2 : Fin 4).castSucc = 2 := rfl
    have e3 : (3 : Fin 4).castSucc = 3 := rfl
    rw [e2] at c2
    rw [e3] at c3
    linarith [hz (ε * (p 0 - p 1)), hz (ε * (p 0 - p 2)), hz (ε * (p 0 - p 3)),
      hz (ε * (p 1 - p 2)), hz (ε * (p 1 - p 3)), hz (ε * (p 2 - p 3))]
  have hmul := mul_le_mul_of_nonneg_left hsum hk.le
  have e : 2 / (5 * ε ^ 2) * (2 * (ε * (p 0 - p 4)) ^ 2 / π ^ 2 + 2 * (ε * (p 1 - p 4)) ^ 2 / π ^ 2 +
      2 * (ε * (p 2 - p 4)) ^ 2 / π ^ 2 + 2 * (ε * (p 3 - p 4)) ^ 2 / π ^ 2) =
      4 / (5 * π ^ 2) * ((p 0 - p 4) ^ 2 + (p 1 - p 4) ^ 2 + (p 2 - p 4) ^ 2 + (p 3 - p 4) ^ 2) := by
    field_simp
    ring
  rw [e] at hmul
  have hk2 : 0 ≤ 4 / (5 * π ^ 2) := by positivity
  have := mul_le_mul_of_nonneg_left hb hk2
  linarith

/-- The constant of the norm bound: `5π²ε²/24`. -/
noncomputable def normConst (ε : ℝ) : ℝ := 5 * π ^ 2 * ε ^ 2 / 24

/-- **On the cell, the lattice and continuum resolvent symbols differ by at most `5π²ε²/24`.** -/
theorem inverse_symbol_bound (ε M : ℝ) (hε : ε ≠ 0) (p : Fin 5 → ℝ) (hp : ∑ i, p i = 0)
    (hcell : ∀ i : Fin 4, |ε * (p i.castSucc - p 4)| ≤ π) :
    |(M ^ 2 + lam ε p)⁻¹ - (M ^ 2 + norm2 p)⁻¹| ≤ normConst ε := by
  have hpi : 0 < π := Real.pi_pos
  obtain ⟨herr0, herr⟩ := lambda_error ε hε p hp
  have hlow := lambda_cell_lower ε hε p hp hcell
  have hl0 := lam_nonneg ε p
  have hP := norm2_nonneg p
  have hK : 0 ≤ normConst ε := by rw [normConst]; positivity
  rcases eq_or_lt_of_le hP with hP0 | hPpos
  · have hl : lam ε p = 0 := by linarith
    rw [← hP0, hl, sub_self, abs_zero]
    exact hK
  · have hlpos : 0 < lam ε p := by
      have : 0 < 4 / (5 * π ^ 2) * norm2 p := by positivity
      linarith
    have hA : 0 < M ^ 2 + lam ε p := by positivity
    have hB : 0 < M ^ 2 + norm2 p := by positivity
    have hdiff : (M ^ 2 + lam ε p)⁻¹ - (M ^ 2 + norm2 p)⁻¹ =
        (norm2 p - lam ε p) / ((M ^ 2 + lam ε p) * (M ^ 2 + norm2 p)) := by
      rw [inv_sub_inv hA.ne' hB.ne']
      congr 1
      ring
    rw [hdiff, abs_of_nonneg (div_nonneg herr0 (by positivity)), div_le_iff₀ (by positivity)]
    have hAB : lam ε p * norm2 p ≤ (M ^ 2 + lam ε p) * (M ^ 2 + norm2 p) := by
      have h1 : lam ε p ≤ M ^ 2 + lam ε p := by nlinarith [sq_nonneg M]
      have h2 : norm2 p ≤ M ^ 2 + norm2 p := by nlinarith [sq_nonneg M]
      exact mul_le_mul h1 h2 hP hA.le
    have hcP : 4 / (5 * π ^ 2) * norm2 p * norm2 p ≤ lam ε p * norm2 p :=
      mul_le_mul_of_nonneg_right hlow hP
    have hKc : normConst ε * (4 / (5 * π ^ 2)) = ε ^ 2 / 6 := by
      rw [normConst]
      field_simp
      ring
    calc norm2 p - lam ε p ≤ ε ^ 2 / 6 * norm2 p ^ 2 := herr
      _ = normConst ε * (4 / (5 * π ^ 2) * norm2 p * norm2 p) := by rw [← hKc]; ring
      _ ≤ normConst ε * (lam ε p * norm2 p) := mul_le_mul_of_nonneg_left hcP hK
      _ ≤ normConst ε * ((M ^ 2 + lam ε p) * (M ^ 2 + norm2 p)) := mul_le_mul_of_nonneg_left hAB hK

/-- **Off the cell the continuum symbol is small:** `(M² + |p|²)⁻¹ ≤ 2ε²/π²`. -/
theorem outside_cell_inverse_bound (ε M : ℝ) (p : Fin 5 → ℝ)
    (hout : ∃ i : Fin 4, π ≤ |ε * (p i.castSucc - p 4)|) :
    (M ^ 2 + norm2 p)⁻¹ ≤ 2 * ε ^ 2 / π ^ 2 := by
  obtain ⟨i, hi⟩ := hout
  have hpi : 0 < π := Real.pi_pos
  have hd : π ^ 2 ≤ ε ^ 2 * (p i.castSucc - p 4) ^ 2 := by
    have h := pow_le_pow_left₀ hpi.le hi 2
    rwa [sq_abs, mul_pow] at h
  have hε : ε ≠ 0 := by
    rintro rfl
    rw [zero_pow two_ne_zero, zero_mul] at hd
    have : (0 : ℝ) < π ^ 2 := by positivity
    linarith
  have hne : i.castSucc ≠ (4 : Fin 5) := by
    intro h
    rw [h, sub_self, mul_zero, abs_zero] at hi
    linarith
  have hpair := pair_le_two_norm p i.castSucc 4 hne
  have hε2 : 0 < ε ^ 2 := by positivity
  have hlow : π ^ 2 / (2 * ε ^ 2) ≤ M ^ 2 + norm2 p := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg M]
  have hpos : 0 < π ^ 2 / (2 * ε ^ 2) := by positivity
  calc (M ^ 2 + norm2 p)⁻¹ ≤ (π ^ 2 / (2 * ε ^ 2))⁻¹ := inv_anti₀ hpos hlow
    _ = 2 * ε ^ 2 / π ^ 2 := by rw [inv_div]

theorem two_div_pi_sq_le_normConst (ε : ℝ) : 2 * ε ^ 2 / π ^ 2 ≤ normConst ε := by
  have hpi : 3 < π := Real.pi_gt_three
  have hpi0 : 0 < π := Real.pi_pos
  have h9 : (9 : ℝ) < π ^ 2 := by nlinarith
  have h81 : (81 : ℝ) < π ^ 4 := by
    have h := pow_lt_pow_left₀ h9 (by norm_num : (0 : ℝ) ≤ 9) two_ne_zero
    rw [← pow_mul] at h
    norm_num at h
    exact h
  rw [normConst, div_le_div_iff₀ (by positivity) (by norm_num)]
  have hpos : 0 ≤ ε ^ 2 * (5 * π ^ 4 - 48) := mul_nonneg (sq_nonneg ε) (by linarith)
  nlinarith [hpos]

open Classical in
/-- The interpolated lattice resolvent multiplier: the lattice symbol on the reciprocal cell, zero off
it. -/
noncomputable def latticeMult (ε M : ℝ) (p : Fin 5 → ℝ) : ℝ :=
  if ∀ i : Fin 4, |ε * (p i.castSucc - p 4)| ≤ π then (M ^ 2 + lam ε p)⁻¹ else 0

/-- The continuum resolvent multiplier `(M² + |p|²)⁻¹` of `(M² − Δ)⁻¹`. -/
noncomputable def continuumMult (M : ℝ) (p : Fin 5 → ℝ) : ℝ := (M ^ 2 + norm2 p)⁻¹

/-- **The two multipliers differ by at most `5π²ε²/24` at every momentum of `W`.** -/
theorem multiplier_bound (ε M : ℝ) (hε : ε ≠ 0) (p : Fin 5 → ℝ) (hp : ∑ i, p i = 0) :
    |latticeMult ε M p - continuumMult M p| ≤ normConst ε := by
  rw [latticeMult, continuumMult]
  split_ifs with hcell
  · exact inverse_symbol_bound ε M hε p hp hcell
  · push Not at hcell
    obtain ⟨i, hi⟩ := hcell
    have h := outside_cell_inverse_bound ε M p ⟨i, hi.le⟩
    have hpos : 0 ≤ (M ^ 2 + norm2 p)⁻¹ := by
      have := norm2_nonneg p
      positivity
    rw [zero_sub, abs_neg, abs_of_nonneg hpos]
    exact h.trans (two_div_pi_sq_le_normConst ε)

theorem lam_continuous (ε : ℝ) : Continuous (lam ε) := by
  unfold lam pairSum
  refine continuous_const.mul (continuous_finsetSum _ fun s _ => continuous_finsetSum _ fun t _ => ?_)
  split_ifs
  · fun_prop
  · exact continuous_const

theorem norm2_continuous : Continuous norm2 := by
  unfold norm2
  fun_prop

theorem latticeMult_measurable (ε M : ℝ) : Measurable (latticeMult ε M) := by
  unfold latticeMult
  refine Measurable.ite ?_ ((continuous_const.add (lam_continuous ε)).measurable.inv) measurable_const
  have : {p : Fin 5 → ℝ | ∀ i : Fin 4, |ε * (p i.castSucc - p 4)| ≤ π} =
      ⋂ i : Fin 4, {p : Fin 5 → ℝ | |ε * (p i.castSucc - p 4)| ≤ π} := by
    ext p
    simp
  rw [this]
  refine MeasurableSet.iInter fun i => measurableSet_le ?_ measurable_const
  fun_prop

theorem continuumMult_measurable (M : ℝ) : Measurable (continuumMult M) := by
  unfold continuumMult
  exact (continuous_const.add norm2_continuous).measurable.inv

/-- **The norm bound on the interpolated resolvents:** for every measure on the momenta carried by `W`
(the Lebesgue measure of `W`, or the finite Fourier modes of a periodic torus), the difference of the
interpolated lattice resolvent and the continuum resolvent, acting by multiplication on the Fourier
side, has `‖(R_ε − R_0) f‖₂ ≤ (5π²ε²/24) ‖f‖₂`. -/
theorem resolvent_norm_bound (ε M : ℝ) (hε : ε ≠ 0) (μ : Measure (Fin 5 → ℝ))
    (hμ : ∀ᵐ p ∂μ, ∑ i, p i = 0) (f : (Fin 5 → ℝ) → ℂ) (hf : AEStronglyMeasurable f μ) :
    eLpNorm (fun p => ((latticeMult ε M p - continuumMult M p : ℝ) : ℂ) * f p) 2 μ ≤
      ENNReal.ofReal (normConst ε) * eLpNorm f 2 μ := by
  have hm : AEStronglyMeasurable (fun p => ((latticeMult ε M p - continuumMult M p : ℝ) : ℂ)) μ :=
    (Complex.measurable_ofReal.comp
      ((latticeMult_measurable ε M).sub (continuumMult_measurable M))).aestronglyMeasurable
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul (hm.mul hf)
  filter_upwards [hμ] with p hp
  rw [Pi.mul_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (multiplier_bound ε M hε p hp) (norm_nonneg _)

end Comparison.GroupsContinuumLaw
