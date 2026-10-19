import Comparison.Existence.IharaBass

/-!
# The law is positive below its critical step
# with every unitary connection

A
unitary connection of P4 makes the step along each line `t` an operator `Γ_t` on the vertices with their
gauge, `Γ_t = Σ_x |x △ T_t⟩⟨x| ⊗ U_{x△T_t, x}`; since `U_yx = U_xy⁻¹` is unitary, every `Γ_t` is a
Hermitian involution. For any five Hermitian involutions on a finite-dimensional space:

* `re_star_dot_self_nonneg`, `re_star_dot_self_pos`: `Re ⟨x, x⟩ ≥ 0`, `> 0` for `x ≠ 0`.
* `herm_bound`: `⟨x + cΓx, x + cΓx⟩ = 2⟨x, x⟩ + 2c⟨x, Γx⟩` for `c = c̄`, `c² = 1`; so
  `|Re⟨x, Γx⟩| ≤ ⟨x, x⟩` (`herm_le`).
* `quad_lower`: **`Re⟨x, ((1 + 4u²) − uΣ_tΓ_t)x⟩ ≥ (1 − u)(1 − 4u)⟨x, x⟩` for `u ≥ 0`.**
* `law_operator_det_ne_zero`: for `0 ≤ u < 1/4` the operator `(1 + 4u²) − uΣ_tΓ_t` is invertible.
* `law_no_zero_below_quarter`: with Ihara and Bass (`ihara_bass`), **the law
  `det(I − uB[U]) ≠ 0` for `0 ≤ u < 1/4`, whatever unitary connection is carried**.
* `quad_ne_zero_disc`, `law_operator_det_ne_zero_disc`, `law_no_zero_in_disc`: more strongly, **no
  unitary connection gives the law a zero in the open disc `|u| < 1/4`**: on a Hermitian form of
  size at most 5 the factor `1 + 4u² − uρ` vanishes only at `|u| = 1/2` (`|ρ| ≤ 4`) or at real
  `|u| ≥ 1/4` (`4 < |ρ| ≤ 5`). The trivial connection attains the bound at `u = 1/4`; a connection
  need not have a zero there at all (with `U = −1` on every link the vertex spectrum is `−5, −1, 3`
  and the law is finite at `1/4`). So 1/4 is the law's bound, not every connection's zero.
-/

open Comparison Matrix

namespace Comparison.RuleAndLaw

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem re_star_mul_self (z : ℂ) : (star z * z).re = z.re * z.re + z.im * z.im := by
  rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

omit [DecidableEq ι] in
theorem re_star_dot_self_nonneg (v : ι → ℂ) : 0 ≤ (star v ⬝ᵥ v).re := by
  simp only [dotProduct, Pi.star_apply, Complex.re_sum, re_star_mul_self]
  exact Finset.sum_nonneg fun i _ => by nlinarith [mul_self_nonneg (v i).re, mul_self_nonneg (v i).im]

omit [DecidableEq ι] in
theorem re_star_dot_self_pos (v : ι → ℂ) (hv : v ≠ 0) : 0 < (star v ⬝ᵥ v).re := by
  obtain ⟨i, hi0⟩ := Function.ne_iff.mp hv
  have hi : v i ≠ 0 := by simpa using hi0
  simp only [dotProduct, Pi.star_apply, Complex.re_sum, re_star_mul_self]
  refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
  · nlinarith [mul_self_nonneg (v j).re, mul_self_nonneg (v j).im]
  · have h : (v i).re ≠ 0 ∨ (v i).im ≠ 0 := by
      by_contra h
      rw [not_or, not_not, not_not] at h
      exact hi (Complex.ext h.1 h.2)
    rcases h with h | h
    · nlinarith [mul_self_pos.mpr h, mul_self_nonneg (v i).im]
    · nlinarith [mul_self_pos.mpr h, mul_self_nonneg (v i).re]

/-- `⟨x + cΓx, x + cΓx⟩ = 2⟨x, x⟩ + 2c⟨x, Γx⟩` for a Hermitian involution `Γ` and real `c` with `c² = 1`. -/
theorem herm_bound (G : Matrix ι ι ℂ) (hH : Gᴴ = G) (hG : G * G = 1) (x : ι → ℂ) (c : ℂ)
    (hc : star c = c) (hc2 : c * c = 1) :
    star (x + c • (G *ᵥ x)) ⬝ᵥ (x + c • (G *ᵥ x)) =
      2 * (star x ⬝ᵥ x) + 2 * c * (star x ⬝ᵥ (G *ᵥ x)) := by
  have h1 : star (G *ᵥ x) = star x ᵥ* G := by rw [Matrix.star_mulVec, hH]
  have h2 : (star x ᵥ* G) ⬝ᵥ x = star x ⬝ᵥ (G *ᵥ x) := (Matrix.dotProduct_mulVec _ _ _).symm
  have h3 : (star x ᵥ* G) ⬝ᵥ (G *ᵥ x) = star x ⬝ᵥ x := by
    rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hG, Matrix.one_mulVec]
  rw [star_add, star_smul, hc, h1]
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul, h2, h3]
  linear_combination (star x ⬝ᵥ x) * hc2

/-- **`Re⟨x, Γx⟩ ≤ ⟨x, x⟩`** for a Hermitian involution. -/
theorem herm_le (G : Matrix ι ι ℂ) (hH : Gᴴ = G) (hG : G * G = 1) (x : ι → ℂ) :
    (star x ⬝ᵥ (G *ᵥ x)).re ≤ (star x ⬝ᵥ x).re := by
  have e := herm_bound G hH hG x (-1) (by simp) (by norm_num)
  have hn := re_star_dot_self_nonneg (x + (-1 : ℂ) • (G *ᵥ x))
  rw [e] at hn
  have hr : (2 * (star x ⬝ᵥ x) + 2 * (-1 : ℂ) * (star x ⬝ᵥ (G *ᵥ x))).re =
      2 * (star x ⬝ᵥ x).re - 2 * (star x ⬝ᵥ (G *ᵥ x)).re := by
    simp only [Complex.add_re, Complex.mul_re]
    norm_num
    ring
  rw [hr] at hn
  linarith

/-- **The law's operator is bounded below by `(1 − u)(1 − 4u)` for `u ≥ 0`, with any five Hermitian
involutions:** `Re⟨x, ((1 + 4u²) − uΣ_tΓ_t)x⟩ ≥ (1 − u)(1 − 4u)⟨x, x⟩`. -/
theorem quad_lower (Γ : Fin 5 → Matrix ι ι ℂ) (hH : ∀ t, (Γ t)ᴴ = Γ t) (hG : ∀ t, Γ t * Γ t = 1)
    (u : ℝ) (hu : 0 ≤ u) (x : ι → ℂ) :
    (1 - u) * (1 - 4 * u) * (star x ⬝ᵥ x).re ≤
      (star x ⬝ᵥ (((1 + 4 * (u : ℂ) ^ 2) • (1 : Matrix ι ι ℂ) - (u : ℂ) • ∑ t, Γ t) *ᵥ x)).re := by
  have hcast : (1 + 4 * (u : ℂ) ^ 2) = ((1 + 4 * u ^ 2 : ℝ) : ℂ) := by push_cast; ring
  have expand : star x ⬝ᵥ (((1 + 4 * (u : ℂ) ^ 2) • (1 : Matrix ι ι ℂ) - (u : ℂ) • ∑ t, Γ t) *ᵥ x) =
      ((1 + 4 * u ^ 2 : ℝ) : ℂ) * (star x ⬝ᵥ x) - (u : ℂ) * ∑ t, star x ⬝ᵥ (Γ t *ᵥ x) := by
    rw [hcast, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.sum_mulVec, dotProduct_sub, dotProduct_smul, dotProduct_smul, dotProduct_sum]
    simp only [smul_eq_mul]
  rw [expand, Complex.sub_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.re_sum]
  have hsum : ∑ t, (star x ⬝ᵥ (Γ t *ᵥ x)).re ≤ 5 * (star x ⬝ᵥ x).re := by
    calc ∑ t, (star x ⬝ᵥ (Γ t *ᵥ x)).re ≤ ∑ _t : Fin 5, (star x ⬝ᵥ x).re :=
          Finset.sum_le_sum fun t _ => herm_le (Γ t) (hH t) (hG t) x
      _ = 5 * (star x ⬝ᵥ x).re := by simp
  have hx := re_star_dot_self_nonneg x
  nlinarith [mul_le_mul_of_nonneg_left hsum hu]

/-- **For `0 ≤ u < 1/4` the law's operator `(1 + 4u²) − uΣ_tΓ_t` is invertible.** -/
theorem law_operator_det_ne_zero (Γ : Fin 5 → Matrix ι ι ℂ) (hH : ∀ t, (Γ t)ᴴ = Γ t)
    (hG : ∀ t, Γ t * Γ t = 1) (u : ℝ) (hu : 0 ≤ u) (hu4 : u < 1 / 4) :
    ((1 + 4 * (u : ℂ) ^ 2) • (1 : Matrix ι ι ℂ) - (u : ℂ) • ∑ t, Γ t).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hMv⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
  have h1 := quad_lower Γ hH hG u hu v
  rw [hMv, dotProduct_zero, Complex.zero_re] at h1
  have h2 := re_star_dot_self_pos v hv
  have h3 : 0 < (1 - u) * (1 - 4 * u) := mul_pos (by linarith) (by linarith)
  have h4 := mul_pos h3 h2
  linarith

/-- **The law has no zero below its critical step, with every unitary connection:**
`det(I − uB[U]) ≠ 0` for `0 ≤ u < 1/4` (Bass's identity, `ihara_bass`, with the positivity above). -/
theorem law_no_zero_below_quarter (Γ : Fin 5 → Matrix ι ι ℂ) (hH : ∀ t, (Γ t)ᴴ = Γ t)
    (hG : ∀ t, Γ t * Γ t = 1) (u : ℝ) (hu : 0 ≤ u) (hu4 : u < 1 / 4) :
    (1 - (u : ℂ) • stepOp Γ).det ≠ 0 := by
  intro h0
  have hb := ihara_bass Γ hG (u : ℂ)
  rw [h0, mul_zero] at hb
  have hu2 : (1 - (u : ℂ) ^ 2) ≠ 0 := by
    have hr : (1 - (u : ℂ) ^ 2) = ((1 - u ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hr, Complex.ofReal_ne_zero]
    nlinarith
  have hd := law_operator_det_ne_zero Γ hH hG u hu hu4
  exact mul_ne_zero (pow_ne_zero _ hu2) hd hb.symm

/-! ## No zero in the open disc `|u| < 1/4` -/

theorem im_star_mul_self (z : ℂ) : (star z * z).im = 0 := by
  rw [Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

omit [DecidableEq ι] in
theorem im_star_dot_self (v : ι → ℂ) : (star v ⬝ᵥ v).im = 0 := by
  simp only [dotProduct, Pi.star_apply, Complex.im_sum, im_star_mul_self, Finset.sum_const_zero]

/-- **`⟨x, Γx⟩` is real** for a Hermitian involution. -/
theorem herm_real (G : Matrix ι ι ℂ) (hH : Gᴴ = G) (hG : G * G = 1) (x : ι → ℂ) :
    (star x ⬝ᵥ (G *ᵥ x)).im = 0 := by
  have e := herm_bound G hH hG x 1 (by simp) (by norm_num)
  have h := im_star_dot_self (x + (1 : ℂ) • (G *ᵥ x))
  rw [e] at h
  have hx := im_star_dot_self x
  simp only [Complex.add_im, Complex.mul_im, mul_one] at h
  norm_num at h
  linarith

/-- **`1 + 4u² − uρ ≠ 0` for `|u| < 1/4` and real `|ρ| ≤ 5`**: its roots have product `1/4`, so they lie on
`|u| = 1/2` when `|ρ| ≤ 4` and are real with the smaller at least `1/4` when `4 < |ρ| ≤ 5`. -/
theorem quad_ne_zero_disc (u : ℂ) (hu : ‖u‖ < 1 / 4) (ρ : ℝ) (hρ : |ρ| ≤ 5) :
    1 + 4 * u ^ 2 - u * (ρ : ℂ) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.sub_re, Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.zero_re, sq, Complex.sub_im, Complex.add_im, Complex.one_im,
    Complex.mul_im, Complex.zero_im] at hre him
  norm_num at hre him
  have hn : u.re ^ 2 + u.im ^ 2 < 1 / 16 := by
    have h1 : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    have h2 : ‖u‖ ^ 2 < (1 / 4) ^ 2 := by
      have := norm_nonneg u
      nlinarith
    linarith
  have hρ2 : ρ ^ 2 ≤ 25 := by
    have := abs_le.mp hρ
    nlinarith
  by_cases hb : u.im = 0
  · rw [hb] at hre
    have ha2 : u.re ^ 2 < 1 / 16 := by nlinarith
    -- `aρ = 1 + 4a²`, so `(1 + 4a²)² = a²ρ² ≤ 25a²`, i.e. `(16a² − 1)(a² − 1) ≤ 0`
    have hsq : (1 + 4 * u.re ^ 2) ^ 2 ≤ 25 * u.re ^ 2 := by
      have e : u.re * ρ = 1 + 4 * u.re ^ 2 := by nlinarith
      have : (u.re * ρ) ^ 2 ≤ 25 * u.re ^ 2 := by
        rw [mul_pow]
        nlinarith [sq_nonneg u.re]
      rw [e] at this
      exact this
    nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - 16 * u.re ^ 2) (by nlinarith : (0 : ℝ) < 1 - u.re ^ 2)]
  · have hρ8 : ρ = 8 * u.re := by
      have : u.im * (8 * u.re - ρ) = 0 := by linarith
      rcases mul_eq_zero.mp this with h0 | h0
      · exact absurd h0 hb
      · linarith
    rw [hρ8] at hre
    nlinarith

/-- **The law's operator is invertible on the open disc `|u| < 1/4`**, with any five Hermitian involutions. -/
theorem law_operator_det_ne_zero_disc (Γ : Fin 5 → Matrix ι ι ℂ) (hH : ∀ t, (Γ t)ᴴ = Γ t)
    (hG : ∀ t, Γ t * Γ t = 1) (u : ℂ) (hu : ‖u‖ < 1 / 4) :
    ((1 + 4 * u ^ 2) • (1 : Matrix ι ι ℂ) - u • ∑ t, Γ t).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, hMv⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
  set r := (star v ⬝ᵥ v).re with hr
  set a := ∑ t, (star v ⬝ᵥ (Γ t *ᵥ v)).re with ha
  have hrpos : 0 < r := re_star_dot_self_pos v hv
  have hrr : star v ⬝ᵥ v = (r : ℂ) := by
    apply Complex.ext
    · simp [hr]
    · simp [im_star_dot_self v]
  have haa : ∑ t, star v ⬝ᵥ (Γ t *ᵥ v) = (a : ℂ) := by
    apply Complex.ext
    · simp [ha, Complex.re_sum]
    · simp [Complex.im_sum, herm_real (Γ _) (hH _) (hG _) v]
  have habs : |a| ≤ 5 * r := by
    have hup : a ≤ 5 * r := by
      calc a ≤ ∑ _t : Fin 5, r := Finset.sum_le_sum fun t _ => herm_le (Γ t) (hH t) (hG t) v
        _ = 5 * r := by simp
    have hlo : -(5 * r) ≤ a := by
      have hneg : ∀ t, -(star v ⬝ᵥ v).re ≤ (star v ⬝ᵥ (Γ t *ᵥ v)).re := by
        intro t
        have e := herm_bound (Γ t) (hH t) (hG t) v 1 (by simp) (by norm_num)
        have hn := re_star_dot_self_nonneg (v + (1 : ℂ) • (Γ t *ᵥ v))
        rw [e] at hn
        simp only [Complex.add_re, Complex.mul_re] at hn
        norm_num at hn
        linarith
      calc -(5 * r) = ∑ _t : Fin 5, -r := by simp
        _ ≤ a := Finset.sum_le_sum fun t _ => hneg t
    exact abs_le.mpr ⟨hlo, hup⟩
  have hq : star v ⬝ᵥ (((1 + 4 * u ^ 2) • (1 : Matrix ι ι ℂ) - u • ∑ t, Γ t) *ᵥ v) =
      (1 + 4 * u ^ 2) * (r : ℂ) - u * (a : ℂ) := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.sum_mulVec, dotProduct_sub, dotProduct_smul, dotProduct_smul, dotProduct_sum, hrr, haa]
    simp only [smul_eq_mul]
  rw [hMv, dotProduct_zero] at hq
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
  have e1 : ((a / r : ℝ) : ℂ) * (r : ℂ) = (a : ℂ) := by
    rw [Complex.ofReal_div, div_mul_cancel₀ _ hr0]
  have key : (1 + 4 * u ^ 2 - u * ((a / r : ℝ) : ℂ)) * (r : ℂ) = 0 := by
    rw [sub_mul, mul_assoc u, e1]
    exact hq.symm
  have hρ : |a / r| ≤ 5 := by
    rw [abs_div, abs_of_pos hrpos, div_le_iff₀ hrpos]
    exact habs
  exact quad_ne_zero_disc u hu (a / r) hρ ((mul_eq_zero.mp key).resolve_right hr0)

/-- **No unitary connection gives the law a zero in the open disc `|u| < 1/4`.** -/
theorem law_no_zero_in_disc (Γ : Fin 5 → Matrix ι ι ℂ) (hH : ∀ t, (Γ t)ᴴ = Γ t)
    (hG : ∀ t, Γ t * Γ t = 1) (u : ℂ) (hu : ‖u‖ < 1 / 4) :
    (1 - u • stepOp Γ).det ≠ 0 := by
  intro h0
  have hb := ihara_bass Γ hG u
  rw [h0, mul_zero] at hb
  have hu2 : (1 - u ^ 2) ≠ 0 := by
    intro h
    have h1 : u ^ 2 = 1 := by linear_combination -h
    have h2 : ‖u‖ ^ 2 = 1 := by rw [← norm_pow, h1, norm_one]
    have := norm_nonneg u
    nlinarith
  have hd := law_operator_det_ne_zero_disc Γ hH hG u hu
  exact mul_ne_zero (pow_ne_zero _ hu2) hd hb.symm

end Comparison.RuleAndLaw

#print axioms Comparison.RuleAndLaw.re_star_mul_self
#print axioms Comparison.RuleAndLaw.re_star_dot_self_nonneg
#print axioms Comparison.RuleAndLaw.re_star_dot_self_pos
#print axioms Comparison.RuleAndLaw.herm_bound
#print axioms Comparison.RuleAndLaw.herm_le
#print axioms Comparison.RuleAndLaw.quad_lower
#print axioms Comparison.RuleAndLaw.law_operator_det_ne_zero
#print axioms Comparison.RuleAndLaw.law_no_zero_below_quarter
#print axioms Comparison.RuleAndLaw.im_star_mul_self
#print axioms Comparison.RuleAndLaw.im_star_dot_self
#print axioms Comparison.RuleAndLaw.herm_real
#print axioms Comparison.RuleAndLaw.quad_ne_zero_disc
#print axioms Comparison.RuleAndLaw.law_operator_det_ne_zero_disc
#print axioms Comparison.RuleAndLaw.law_no_zero_in_disc
