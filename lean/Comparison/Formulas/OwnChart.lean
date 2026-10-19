import Comparison.GroupsContinuumLaw.Chart
import Comparison.GroupsContinuumLaw.Symbol
import Comparison.Existence.Motion
import Comparison.Formulas.Kernel

/-!
# The law on its own chart (Prop. S59a; formula (16))

Proposition S59a, its finite statements. The chart is `VN N`
(`GroupsContinuumLaw/Chart.lean`): the vertices `Λ₀ ∪ (Λ₀ + v_h)` taken modulo `N` in every direction, the five
transitions `GammaN t` from sheet to sheet (`transitionN`), the step `chartStep = stepOp GammaN`.

* `det_one_sub_signed_involution`: an involution `Γ` reversed by a sign `S` (`SΓS = −Γ`, `S² = 1`) on
  `2m` states has `det(1 − uΓ) = (1 − u²)^m`; `det_GammaN`: every transition of the chart.
* `chart_bass`: **`det(I − uB_chart) = (1 − u²)^{E − V} det[(1 + 4u²)I − uA_chart]`** with `V = 2N⁴`
  vertices and `E = 5N⁴` links (`chart_counts`), for every `N ≥ 1` and every `u`; `chart_three`: the
  script's `3⁴` chart has `162` vertices and `405` links.
* `hop_sum`, `normSq_F`, `hop_sum_F`: **`25 − |F(k)|² = Σ_{s≠t} [1 − cos k·(v_s − v_t)]`**,
  `F(k) = Σ_t e^{ik·v_t}`, for every `k` (`x_t = k·v_t`); `hop_sum_lam`: it is `5 λ₁(k)`, symbol, so
  `chart_symbol_second_order`: **`0 ≤ |k|² − (25 − |F|²)/5 ≤ |k|⁴/6`**, `Q(k) = M² + |k|² + O(|k|⁴)`.
* The projection along `v_h` (`projOff`, `pvec`): `pvec_perp`, `hop_projects`
  (`P(v_s − v_t) = p_s − p_t`), `pvec_explicit` (`p_t = e_t − e_h + (5/4)v_h`), `pvec_gram`
  (**`p_s·p_t = δ_st − 1/4`**), `pvec_sum`, `gram_det` (**the Gram determinant of three of them is
  `1/4`**), `cell_volume` (**`V₃ = 1/2`**).
* `schur_symbol`: the two-sheet kernel `[[a, −uF], [−uF̄, a]]`, `a = 1 + 4u²`, has Schur complement
  **`a − u²|F|²/a = ρQ`, `ρ = 5u²/a`, `Q = M² + (25 − |F|²)/5`, `M² = ((1/u + 4u)² − 25)/5 = χ(χ + 10)/5`**.
* `continuation_lastDirection`, `rest_on_chart`: along the last-step direction's direction `k = iωv̂_h`,
  **`|F|² = 17 + 8cosh(√5ω/2)`, and `Q = 0` exactly when `cosh(√5ω/2) = 1 + 5M²/8`**.

The static response `G(r) = e^{−Mr}/(4πr)(1 + o(1))` needs the Fourier transform of `1/(M² + |k|²)` on
`ℝ³`, absent from Mathlib; what the continuum theorem carries is `continuum_limit`
(`GroupsContinuumLaw/Continuum.lean`): the chart lift, the exact Schur identity, the resolvent bound
`5π²ε²/24` against `(M² − Δ)⁻¹`, the rest pole and the balanced cone.
-/

namespace Comparison.Formulas

open Matrix Polynomial

/-! ## The determinant of one transition -/

/-- **An involution reversed by a sign has `det(1 − uΓ) = (1 − u²)^m` on `2m` states.** -/
theorem det_one_sub_signed_involution {V : Type*} [Fintype V] [DecidableEq V]
    (Γ S : Matrix V V ℂ) (hΓ : Γ * Γ = 1) (hS : S * S = 1) (hSΓ : S * Γ * S = -Γ)
    (m : ℕ) (hV : Fintype.card V = 2 * m) (u : ℂ) : (1 - u • Γ).det = (1 - u ^ 2) ^ m := by
  set Γ' : Matrix V V ℂ[X] := Γ.map C with hΓ'def
  set S' : Matrix V V ℂ[X] := S.map C with hS'def
  have hΓ' : Γ' * Γ' = 1 := by
    rw [hΓ'def, ← Matrix.map_mul, hΓ, Matrix.map_one _ (map_zero C) (map_one C)]
  have hS' : S' * S' = 1 := by
    rw [hS'def, ← Matrix.map_mul, hS, Matrix.map_one _ (map_zero C) (map_one C)]
  have hSΓ' : S' * Γ' * S' = -Γ' := by
    rw [hS'def, hΓ'def, ← Matrix.map_mul, ← Matrix.map_mul, hSΓ, Matrix.map_neg _ (map_neg C)]
  set P : ℂ[X] := (1 - (X : ℂ[X]) • Γ').det with hPdef
  have hconj : S' * (1 - (X : ℂ[X]) • Γ') * S' = 1 + (X : ℂ[X]) • Γ' := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hS', Matrix.mul_smul, Matrix.smul_mul, hSΓ',
      smul_neg, sub_neg_eq_add]
  have hplus : (1 + (X : ℂ[X]) • Γ').det = P := by
    rw [← hconj, det_mul, det_mul, mul_comm (S'.det) P, mul_assoc, ← det_mul, hS', det_one, mul_one]
  have hprod : (1 - (X : ℂ[X]) • Γ') * (1 + (X : ℂ[X]) • Γ') = (1 - (X : ℂ[X]) ^ 2) • (1 : Matrix V V ℂ[X]) := by
    have hsq : ((X : ℂ[X]) • Γ') * ((X : ℂ[X]) • Γ') = (X : ℂ[X]) ^ 2 • (1 : Matrix V V ℂ[X]) := by
      rw [smul_mul_smul_comm, hΓ', sq]
    have key : ∀ a : Matrix V V ℂ[X], (1 - a) * (1 + a) = 1 - a * a := fun a => by noncomm_ring
    rw [key, hsq, sub_smul, one_smul]
  have hPP : P * P = (1 - (X : ℂ[X]) ^ 2) ^ (2 * m) := by
    have h := congrArg Matrix.det hprod
    rw [det_mul, hplus, det_smul, det_one, mul_one, hV] at h
    exact h
  set Q : ℂ[X] := (1 - (X : ℂ[X]) ^ 2) ^ m with hQdef
  have hzero : (P - Q) * (P + Q) = 0 := by
    have : (P - Q) * (P + Q) = P * P - Q * Q := by ring
    rw [this, hPP, hQdef, ← pow_add, two_mul, sub_self]
  have hPQ : P = Q := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact sub_eq_zero.mp h
    · exfalso
      have h0 := congrArg (Polynomial.eval 0) h
      have hP0 : P.eval 0 = 1 := by
        rw [hPdef, ← det_one_sub_smul_poly Γ 0, zero_smul, sub_zero, det_one]
      rw [Polynomial.eval_add, hP0, hQdef] at h0
      simp at h0
  rw [det_one_sub_smul_poly Γ u, ← hΓ'def, ← hPdef, hPQ, hQdef]
  simp

/-! ## The chart's transitions and its Bass identity -/

variable {N : ℕ} [NeZero N]

/-- The sign of the two sheets. -/
noncomputable def sheetSign : Matrix (GroupsContinuumLaw.VN N) (GroupsContinuumLaw.VN N) ℂ :=
  Matrix.diagonal fun x => if x.2 then -1 else 1

theorem sheetSign_sq : sheetSign (N := N) * sheetSign = 1 := by
  rw [sheetSign, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext x
  by_cases h : x.2 <;> simp [h]

theorem transitionN_sheet (t : Fin 5) (x : GroupsContinuumLaw.VN N) : (GroupsContinuumLaw.transitionN t x).2 = !x.2 := by
  obtain ⟨z, s⟩ := x
  cases s <;> rfl

theorem sheetSign_Gamma (t : Fin 5) :
    sheetSign (N := N) * GroupsContinuumLaw.GammaN t * sheetSign = -GroupsContinuumLaw.GammaN t := by
  ext y x
  simp only [sheetSign, Matrix.diagonal_mul, Matrix.mul_diagonal, GroupsContinuumLaw.GammaN, Matrix.of_apply,
    Matrix.neg_apply]
  by_cases h : y = GroupsContinuumLaw.transitionN t x
  · subst h
    rw [transitionN_sheet]
    cases x.2 <;> simp
  · simp [h]

/-- **Every transition of the chart:** `det(1 − uΓ_t) = (1 − u²)^{N⁴}`. -/
theorem det_GammaN (t : Fin 5) (u : ℂ) :
    (1 - u • GroupsContinuumLaw.GammaN (N := N) t).det = (1 - u ^ 2) ^ (N ^ 4) :=
  det_one_sub_signed_involution _ sheetSign (GroupsContinuumLaw.GammaN_sq t) sheetSign_sq
    (sheetSign_Gamma t) (N ^ 4) GroupsContinuumLaw.card_VN u

/-- `det((1 + 4u²) − uA)` is a polynomial in `u`. -/
theorem det_vertex_poly {V : Type*} [Fintype V] [DecidableEq V] (A : Matrix V V ℂ) (u : ℂ) :
    ((1 + 4 * u ^ 2) • (1 : Matrix V V ℂ) - u • A).det =
      (((1 + 4 * (X : ℂ[X]) ^ 2) • (1 : Matrix V V ℂ[X]) - (X : ℂ[X]) • A.map C).det).eval u := by
  rw [← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j
  · subst h
    simp
    ring
  · simp [h]
    ring

/-- The vertices and the links of the chart: `V = 2N⁴`, `E = 5N⁴` (each link has one end on the sheet
`0` and a direction). -/
theorem chart_counts :
    Fintype.card (GroupsContinuumLaw.VN N) = 2 * N ^ 4 ∧ Fintype.card (GroupsContinuumLaw.ZN N × Fin 5) = 5 * N ^ 4 := by
  refine ⟨GroupsContinuumLaw.card_VN, ?_⟩
  simp [Fintype.card_prod, ZMod.card, mul_comm]

/-- The script's chart, `N = 3`: `162` vertices and `405` links. -/
theorem chart_three :
    Fintype.card (GroupsContinuumLaw.VN 3) = 162 ∧ Fintype.card (GroupsContinuumLaw.ZN 3 × Fin 5) = 405 := by
  constructor
  · rw [GroupsContinuumLaw.card_VN]
    norm_num
  · simp [Fintype.card_prod, ZMod.card]

/-- **The Bass identity on the law's own chart:**
`det(I − uB_chart) = (1 − u²)^{E − V} det[(1 + 4u²)I − uA_chart]`, `E − V = 3N⁴`, for every `u`. -/
theorem chart_bass (u : ℂ) :
    (1 - u • GroupsContinuumLaw.chartStep (N := N)).det =
      (1 - u ^ 2) ^ (3 * N ^ 4) *
        ((1 + 4 * u ^ 2) • (1 : Matrix (GroupsContinuumLaw.VN N) (GroupsContinuumLaw.VN N) ℂ) -
          u • ∑ t, GroupsContinuumLaw.GammaN (N := N) t).det := by
  revert u
  refine extend_from_generic
    (p := (1 - (X : ℂ[X]) • (GroupsContinuumLaw.chartStep (N := N)).map C).det)
    (q := (1 - (X : ℂ[X]) ^ 2) ^ (3 * N ^ 4) *
      ((1 + 4 * (X : ℂ[X]) ^ 2) • (1 : Matrix (GroupsContinuumLaw.VN N) (GroupsContinuumLaw.VN N) ℂ[X]) -
        (X : ℂ[X]) • (∑ t, GroupsContinuumLaw.GammaN (N := N) t).map C).det)
    (det_one_sub_smul_poly _) (fun u => by rw [Polynomial.eval_mul, ← det_vertex_poly]; simp) ?_
  intro u hu
  have h := ihara_bass (GroupsContinuumLaw.GammaN (N := N)) GroupsContinuumLaw.GammaN_sq u
  simp only [det_GammaN, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    GroupsContinuumLaw.card_VN] at h
  have hc : (1 - u ^ 2) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  apply mul_left_cancel₀ (pow_ne_zero (7 * N ^ 4) hc)
  rw [GroupsContinuumLaw.chartStep]
  linear_combination h

/-! ## The hop sum -/

/-- `|F|² = (Σ cos x_t)² + (Σ sin x_t)²` for `F = Σ_t e^{i x_t}`. -/
theorem normSq_F (x : Fin 5 → ℝ) :
    Complex.normSq (∑ t, Complex.exp ((x t : ℂ) * Complex.I)) =
      (∑ t, Real.cos (x t)) ^ 2 + (∑ t, Real.sin (x t)) ^ 2 := by
  rw [Complex.normSq_apply, Complex.re_sum, Complex.im_sum]
  simp only [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  ring

/-- **The hop sum:** `25 − |F|² = Σ_{s ≠ t} [1 − cos(x_s − x_t)]`. -/
theorem hop_sum (x : Fin 5 → ℝ) :
    25 - ((∑ t, Real.cos (x t)) ^ 2 + (∑ t, Real.sin (x t)) ^ 2) =
      ∑ s, ∑ t, (if s = t then 0 else 1 - Real.cos (x s - x t)) := by
  simp only [Fin.sum_univ_five, Real.cos_sub]
  simp only [Fin.isValue, Fin.reduceEq, if_true, if_false]
  linear_combination -(Real.sin_sq_add_cos_sq (x 0)) - Real.sin_sq_add_cos_sq (x 1) -
    Real.sin_sq_add_cos_sq (x 2) - Real.sin_sq_add_cos_sq (x 3) - Real.sin_sq_add_cos_sq (x 4)

/-- **`25 − |F(k)|² = Σ_{hops} (1 − cos k·h)`** with `x_t = k·v_t`. -/
theorem hop_sum_F (x : Fin 5 → ℝ) :
    25 - Complex.normSq (∑ t, Complex.exp ((x t : ℂ) * Complex.I)) =
      ∑ s, ∑ t, (if s = t then 0 else 1 - Real.cos (x s - x t)) := by
  rw [normSq_F, hop_sum]

/-- The hop sum over five is `5 λ₁`, symbol at unit step. -/
theorem hop_sum_lam (p : Fin 5 → ℝ) :
    (25 - ((∑ t, Real.cos (p t)) ^ 2 + (∑ t, Real.sin (p t)) ^ 2)) / 5 = GroupsContinuumLaw.lam 1 p := by
  rw [hop_sum, GroupsContinuumLaw.lam, GroupsContinuumLaw.pairSum_eq]
  simp only [Fin.sum_univ_five, Fin.isValue, Fin.reduceEq, if_true, if_false, one_mul]
  have hc : ∀ a b : ℝ, Real.cos (a - b) = Real.cos (b - a) := fun a b => by
    rw [← Real.cos_neg, neg_sub]
  rw [hc (p 1) (p 0), hc (p 2) (p 0), hc (p 3) (p 0), hc (p 4) (p 0), hc (p 2) (p 1),
    hc (p 3) (p 1), hc (p 4) (p 1), hc (p 3) (p 2), hc (p 4) (p 2), hc (p 4) (p 3)]
  ring

/-- **`Q(k) = M² + |k|² + O(|k|⁴)` in every direction:** `0 ≤ |k|² − (25 − |F|²)/5 ≤ |k|⁴/6` for
`k` in the chart's four directions (`Σ_t k·v_t = 0`). -/
theorem chart_symbol_second_order (p : Fin 5 → ℝ) (hp : ∑ i, p i = 0) :
    0 ≤ GroupsContinuumLaw.norm2 p - (25 - ((∑ t, Real.cos (p t)) ^ 2 + (∑ t, Real.sin (p t)) ^ 2)) / 5 ∧
      GroupsContinuumLaw.norm2 p - (25 - ((∑ t, Real.cos (p t)) ^ 2 + (∑ t, Real.sin (p t)) ^ 2)) / 5 ≤
        GroupsContinuumLaw.norm2 p ^ 2 / 6 := by
  rw [hop_sum_lam]
  obtain ⟨h1, h2⟩ := GroupsContinuumLaw.lambda_error 1 one_ne_zero p hp
  refine ⟨h1, ?_⟩
  calc _ ≤ (1 : ℝ) ^ 2 / 6 * GroupsContinuumLaw.norm2 p ^ 2 := h2
    _ = GroupsContinuumLaw.norm2 p ^ 2 / 6 := by ring

/-! ## The projection along the last-step direction -/

theorem dot_vline (a b : Fin 5) : vline a ⬝ᵥ vline b = (if a = b then 1 else 0) - 1 / 5 :=
  vline_dot a b

/-- The projection off the direction `v_h`. -/
def projOff (h : Fin 5) (w : Fin 5 → ℚ) : Fin 5 → ℚ :=
  w - ((w ⬝ᵥ vline h) / (vline h ⬝ᵥ vline h)) • vline h

/-- The projected hop `p_t = P(v_t − v_h)`. -/
def pvec (h t : Fin 5) : Fin 5 → ℚ := projOff h (vline t - vline h)

theorem vline_self (h : Fin 5) : vline h ⬝ᵥ vline h = 4 / 5 := by
  rw [dot_vline]
  norm_num

theorem hop_dot_vline (h t : Fin 5) :
    (vline t - vline h) ⬝ᵥ vline h = (if t = h then 0 else -1) := by
  rw [sub_dotProduct, dot_vline, dot_vline]
  by_cases ht : t = h <;> simp [ht] <;> norm_num

/-- `p_t ⊥ v_h`. -/
theorem pvec_perp (h t : Fin 5) : pvec h t ⬝ᵥ vline h = 0 := by
  rw [pvec, projOff, sub_dotProduct, smul_dotProduct, smul_eq_mul, vline_self]
  rw [hop_dot_vline]
  by_cases ht : t = h <;> simp [ht]

/-- **The hops project onto the differences of the `p_t`:** `P(v_s − v_t) = p_s − p_t`. -/
theorem hop_projects (h s t : Fin 5) : projOff h (vline s - vline t) = pvec h s - pvec h t := by
  simp only [pvec, projOff]
  rw [show vline s - vline t = (vline s - vline h) - (vline t - vline h) by abel, sub_dotProduct,
    sub_div, sub_smul]
  abel

/-- `p_t = e_t − e_h + (5/4) v_h` for `t ≠ h`. -/
theorem pvec_explicit (h t : Fin 5) (ht : t ≠ h) :
    pvec h t = (Pi.single t 1 - Pi.single h 1) + (5 / 4 : ℚ) • vline h := by
  rw [pvec, projOff, hop_dot_vline, if_neg ht, vline_self]
  funext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, vline, Pi.single_apply]
  by_cases hi : i = t <;> by_cases hj : i = h <;> simp [hi, hj] <;> norm_num

/-- **The Gram matrix of the projected hops:** `p_s·p_t = δ_st − 1/4` for `s, t ≠ h`. -/
theorem pvec_gram (h s t : Fin 5) (hs : s ≠ h) (ht : t ≠ h) :
    pvec h s ⬝ᵥ pvec h t = (if s = t then 1 else 0) - 1 / 4 := by
  simp only [pvec, projOff]
  rw [hop_dot_vline, hop_dot_vline, if_neg hs, if_neg ht, vline_self]
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    dot_vline, if_neg hs, if_neg ht, if_neg (Ne.symm hs), if_neg (Ne.symm ht), if_true]
  by_cases hst : s = t
  · subst hst
    simp
    norm_num
  · simp [hst]
    norm_num

/-- The projected hops sum to zero. -/
theorem pvec_sum (h : Fin 5) : ∑ t, pvec h t = 0 := by
  have hlin : ∀ w : Fin 5 → ℚ, projOff h w = w - ((w ⬝ᵥ vline h) / (4 / 5)) • vline h := by
    intro w
    rw [projOff, vline_self]
  simp only [pvec, hlin]
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul]
  have hs : ∑ t, (vline t - vline h) = -(5 : ℚ) • vline h := by
    rw [Finset.sum_sub_distrib, vline_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [← Nat.cast_smul_eq_nsmul ℚ]
    norm_num
  have hd : ∑ t, ((vline t - vline h) ⬝ᵥ vline h) / (4 / 5) = -5 := by
    rw [← Finset.sum_div, ← sum_dotProduct, hs, smul_dotProduct, vline_self]
    norm_num
  rw [hs, hd]
  module

/-- **The Gram determinant of three projected hops is `1/4`.** -/
theorem gram_det :
    (!![3 / 4, -1 / 4, -1 / 4; -1 / 4, 3 / 4, -1 / 4; -1 / 4, -1 / 4, 3 / 4] :
      Matrix (Fin 3) (Fin 3) ℚ).det = 1 / 4 := by
  rw [Matrix.det_fin_three]
  simp
  norm_num

/-- The Gram matrix of `p_a, p_b, p_c` for three distinct lines other than `h`. -/
theorem gram_three (h a b c : Fin 5) (ha : a ≠ h) (hb : b ≠ h) (hc : c ≠ h) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) :
    (Matrix.of fun i j : Fin 3 => pvec h (![a, b, c] i) ⬝ᵥ pvec h (![a, b, c] j)) =
      !![3 / 4, -1 / 4, -1 / 4; -1 / 4, 3 / 4, -1 / 4; -1 / 4, -1 / 4, 3 / 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pvec_gram h _ _ ha hb, pvec_gram h _ _ ha hc, pvec_gram h _ _ hb hc,
      pvec_gram h _ _ hb ha, pvec_gram h _ _ hc ha, pvec_gram h _ _ hc hb, pvec_gram h _ _ ha ha,
      pvec_gram h _ _ hb hb, pvec_gram h _ _ hc hc, hab, hac, hbc, Ne.symm hab, Ne.symm hac,
      Ne.symm hbc] <;> norm_num

/-- **The cell across `v_h` has volume `V₃ = √(1/4) = 1/2`.** -/
theorem cell_volume : Real.sqrt (1 / 4) = 1 / 2 := by
  rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-! ## The two-sheet kernel and its continuation along the last-step direction -/

/-- **The two-sheet kernel:** `det [[a, −uF], [−uF̄, a]] = a² − u²|F|²`, and its Schur complement
`a − u²|F|²/a = ρQ`, `ρ = 5u²/a`, `Q = M² + (25 − |F|²)/5`, `M² = ((1/u + 4u)² − 25)/5 = χ(χ + 10)/5`. -/
theorem schur_symbol (u F : ℂ) (hu : u ≠ 0) (ha : 1 + 4 * u ^ 2 ≠ 0) :
    (!![1 + 4 * u ^ 2, -u * F; -u * star F, 1 + 4 * u ^ 2] : Matrix (Fin 2) (Fin 2) ℂ).det =
        (1 + 4 * u ^ 2) ^ 2 - u ^ 2 * (F * star F) ∧
      (1 + 4 * u ^ 2) - u ^ 2 * (F * star F) / (1 + 4 * u ^ 2) =
        5 * u ^ 2 / (1 + 4 * u ^ 2) *
          (((1 / u + 4 * u) ^ 2 - 25) / 5 + (25 - F * star F) / 5) ∧
      ((1 / u + 4 * u) ^ 2 - 25) / 5 = chi u * (chi u + 10) / 5 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    ring
  · field_simp
    ring
  · rw [chi]
    ring

/-- **Along the last-step direction's direction:** `k = iωv̂_h` gives `k·v_h = 2iω/√5`, `k·v_t = −iω/(2√5)`, and
`F(k)F(−k) = (e^{−2ω/√5} + 4e^{ω/(2√5)})(e^{2ω/√5} + 4e^{−ω/(2√5)}) = 17 + 8cosh(√5ω/2)`. -/
theorem continuation_lastDirection (ω : ℝ) :
    (Real.exp (-(2 * ω / Real.sqrt 5)) + 4 * Real.exp (ω / (2 * Real.sqrt 5))) *
        (Real.exp (2 * ω / Real.sqrt 5) + 4 * Real.exp (-(ω / (2 * Real.sqrt 5)))) =
      17 + 8 * Real.cosh (Real.sqrt 5 * ω / 2) := by
  have hs : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  have h5 : Real.sqrt 5 ≠ 0 := by positivity
  set E := Real.exp (ω / (2 * Real.sqrt 5)) with hEdef
  have hE : 0 < E := Real.exp_pos _
  have h4 : Real.exp (2 * ω / Real.sqrt 5) = E ^ 4 := by
    rw [hEdef, ← Real.exp_nat_mul]
    congr 1
    field_simp
    ring
  have hc5 : Real.exp (Real.sqrt 5 * ω / 2) = E ^ 5 := by
    rw [hEdef, ← Real.exp_nat_mul]
    congr 1
    field_simp
    linear_combination ω * hs
  rw [Real.cosh_eq, Real.exp_neg, Real.exp_neg, Real.exp_neg, h4, hc5]
  field_simp
  ring

/-- **The rest pole along the last-step direction:** `Q(iωv̂_h) = M² + (25 − |F|²)/5 = 0` exactly when
`cosh(√5ω/2) = 1 + 5M²/8`. -/
theorem rest_on_chart (M2 ω : ℝ) :
    M2 + (25 - (17 + 8 * Real.cosh (Real.sqrt 5 * ω / 2))) / 5 = 0 ↔
      Real.cosh (Real.sqrt 5 * ω / 2) = 1 + 5 * M2 / 8 := by
  constructor <;> intro h <;> linarith

/-- `e^t − 1 ≤ t e^t`. -/
theorem exp_sub_one_le (t : ℝ) : Real.exp t - 1 ≤ t * Real.exp t := by
  have h := Real.add_one_le_exp (-t)
  have hpos := Real.exp_pos t
  have e : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h2 := mul_le_mul_of_nonneg_right h hpos.le
  rw [e] at h2
  linarith

/-- `cosh x ≥ 1 + x²/2` for `x ≥ 0`. -/
theorem one_add_sq_half_le_cosh (x : ℝ) (hx : 0 ≤ x) : 1 + x ^ 2 / 2 ≤ Real.cosh x := by
  have h1 : Real.cosh x = 1 + 2 * Real.sinh (x / 2) ^ 2 := by
    have := Real.cosh_two_mul (x / 2)
    rw [show 2 * (x / 2) = x by ring] at this
    rw [this, Real.cosh_sq]
    ring
  have h2 : x / 2 ≤ Real.sinh (x / 2) := Real.self_le_sinh_iff.mpr (by linarith)
  have h3 : (x / 2) ^ 2 ≤ Real.sinh (x / 2) ^ 2 := pow_le_pow_left₀ (by linarith) h2 2
  rw [h1]
  nlinarith [h3]

/-- **A line at rest along the last-step direction turns at its mass:** if `cosh(√5ω/2) = 1 + 5M²/8` with
`ω ≥ 0` and `M > 0`, then `ω ≤ M` and `M − ω ≤ (5/8)e^{5M²/8}M³`: `ω = M + O(M³)`. -/
theorem rest_frequency (M ω : ℝ) (hM : 0 < M) (hω : 0 ≤ ω)
    (h : Real.cosh (Real.sqrt 5 * ω / 2) = 1 + 5 * M ^ 2 / 8) :
    ω ≤ M ∧ M - ω ≤ 5 / 8 * Real.exp (5 * M ^ 2 / 8) * M ^ 3 := by
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  set x := Real.sqrt 5 * ω / 2 with hxdef
  have hx2 : x ^ 2 / 2 = 5 * ω ^ 2 / 8 := by
    rw [hxdef, div_pow, mul_pow, hs]
    ring
  have hx0 : 0 ≤ x := by positivity
  have hlow := one_add_sq_half_le_cosh x hx0
  have hωM2 : ω ^ 2 ≤ M ^ 2 := by nlinarith [hlow, h, hx2]
  have hωM : ω ≤ M := by
    by_contra hc
    push Not at hc
    nlinarith [mul_lt_mul_of_pos_left hc hM, mul_lt_mul_of_pos_left hc (lt_of_lt_of_le hM hc.le)]
  refine ⟨hωM, ?_⟩
  set E := Real.exp (5 * M ^ 2 / 8) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hup := Real.cosh_le_exp_half_sq x
  rw [hx2] at hup
  have he1 := exp_sub_one_le (5 * ω ^ 2 / 8)
  have hmono : Real.exp (5 * ω ^ 2 / 8) ≤ E := Real.exp_le_exp.mpr (by nlinarith)
  have hA : 5 * M ^ 2 / 8 ≤ 5 * ω ^ 2 / 8 * E := by
    have h1 : 5 * M ^ 2 / 8 ≤ Real.exp (5 * ω ^ 2 / 8) - 1 := by linarith
    have h2 : 5 * ω ^ 2 / 8 * Real.exp (5 * ω ^ 2 / 8) ≤ 5 * ω ^ 2 / 8 * E :=
      mul_le_mul_of_nonneg_left hmono (by positivity)
    linarith
  have he2 := exp_sub_one_le (5 * M ^ 2 / 8)
  rw [← hE] at he2
  have hB : M ^ 2 - ω ^ 2 ≤ 5 / 8 * E * M ^ 4 := by
    have h1 : M ^ 2 ≤ ω ^ 2 * E := by linarith
    have h2 : ω ^ 2 * (E - 1) ≤ M ^ 2 * (E - 1) :=
      mul_le_mul_of_nonneg_right hωM2 (by
        have h5 := Real.add_one_le_exp (5 * M ^ 2 / 8)
        rw [← hE] at h5
        nlinarith [sq_nonneg M])
    have h3 : M ^ 2 * (E - 1) ≤ M ^ 2 * (5 * M ^ 2 / 8 * E) :=
      mul_le_mul_of_nonneg_left he2 (by positivity)
    nlinarith [h1, h2, h3]
  have hC : (M - ω) * M ≤ 5 / 8 * E * M ^ 4 := by
    have : (M - ω) * M ≤ (M - ω) * (M + ω) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith [this, hB]
  have hM3 : 5 / 8 * E * M ^ 4 = (5 / 8 * E * M ^ 3) * M := by ring
  rw [hM3] at hC
  exact le_of_mul_le_mul_right hC hM

end Comparison.Formulas
