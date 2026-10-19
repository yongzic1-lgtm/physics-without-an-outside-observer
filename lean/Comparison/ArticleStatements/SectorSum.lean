import Comparison.Existence.IharaBass
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.RCLike.Basic

/-!
# The sum over sectors gives θ̄ = 0
# (Proposition 115)

A unitary connection of P4 makes the step along each line `t` an operator `Γ_t`
on the vertices with their gauge, a Hermitian involution; the law's weight of the connection is
`det(I − uB[U])` (Ihara and Bass, `ihara_bass`). Proposition 115 reads:

    (1 + 4u²) − uA_U ≥ (1 − u)(1 − 4u) > 0 for 0 ≤ u < 1/4 and any unitary rotations;
    Z_top(θ) = Σ_q a_q e^(iqθ),  a_q = a_(−q) > 0:  |Z_top(θ)| ≤ Z_top(0), with equality only at θ = 0;
    closed weights real:  θ̄ = θ + arg det(M_uM_d) = 0.

This file proves it in four steps.

1. **Each connection's weight is a positive number** (`lawK_posDef`, `one_sub_smul_posDef`,
   `lawWeight_pos`, `lawWeight_real`, `law_pos`): for `0 ≤ u < 1/4` the vertex operator
   `(1 + 4u²) − uΣ_tΓ_t` and every `1 − uΓ_t` are positive definite, so by Ihara and Bass
   `det(I − uB[U])` is a positive real number, and so is the law `Z[U] = det(I − uB[U])⁻¹`.
2. **Time reversal keeps the closed weights** (`conjConn`, `conjConn_herm`, `conjConn_sq`,
   `lawWeight_conj`, `lawWeight_conj_eq`): conjugating every link gives again Hermitian involutions, and
   `det(I − uB[Ū]) = conj det(I − uB[U]) = det(I − uB[U])`.
3. **The sum over sectors** (`sectorSum`, `sectorWeight`, `sectorSum_sectors`, `sectorWeight_pos`,
   `sectorWeight_symm`, `sectorSum_eq_cos`, `norm_sectorSum_le`, `norm_sectorSum_eq_iff`,
   `negLog_deriv_zero`, `negLog_second_deriv`, `curvature_pos`): for configurations with positive weights
   `r_U`, integer charges `q_U` and an involution reversing the charge and keeping the weight,
   `Z(θ) = Σ_U r_U e^(i q_U θ) = Σ_n a_n e^(inθ)` with `a_n > 0` on every inhabited sector and
   `a_(−n) = a_n`; `Z(θ) = Σ_n a_n cos(nθ)` is real, `|Z(θ)| ≤ Z(0)`, with equality exactly at
   `θ ∈ 2πℤ` when the sectors `0` and `1` are inhabited; `(−log Z)′(0) = 0` and
   `(−log Z)″(0) = Σ q² a_q / Σ a_q > 0`.
4. **The law's sector source** (`SectorSource`, `prop115`, `prop115_max_iff`, `prop115_curvature`,
   `theta_bar_zero`): the sector sum of the law, `a_n = Σ_(q_U = n) w_U det(I − uB[U])`, has all of the
   above for `0 ≤ u < 1/4`; a closed weight carries no phase, so `θ̄ = θ + arg det(M_uM_d)` is `0 mod 2π`
   where the sum over sectors is largest.

What stays a hypothesis: the configurations form a finite family (the physical sum is an integral over
connections), the charge `q_U` and the inhabited unit sector are given, and the masses being closed weights
(Proposition 103) is assumed. The first lemmas of §1 repeat RuleAndLaw/Positivity.lean, which has no
compiled module to import.
-/

open Matrix Comparison
open scoped ComplexOrder

namespace Comparison.ArticleStatements

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. Hermitian involutions and positivity -/

theorem re_star_mul_self (z : ℂ) : (star z * z).re = z.re * z.re + z.im * z.im := by
  rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

theorem im_star_mul_self (z : ℂ) : (star z * z).im = 0 := by
  rw [Complex.star_def, Complex.mul_im, Complex.conj_re, Complex.conj_im]
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

omit [DecidableEq ι] in
theorem im_star_dot_self (v : ι → ℂ) : (star v ⬝ᵥ v).im = 0 := by
  simp only [dotProduct, Pi.star_apply, Complex.im_sum, im_star_mul_self, Finset.sum_const_zero]

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

/-- `Re⟨x, Γx⟩ ≤ ⟨x, x⟩` for a Hermitian involution. -/
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

/-- `⟨x, Γx⟩` is real for a Hermitian involution. -/
theorem herm_real (G : Matrix ι ι ℂ) (hH : Gᴴ = G) (hG : G * G = 1) (x : ι → ℂ) :
    (star x ⬝ᵥ (G *ᵥ x)).im = 0 := by
  have e := herm_bound G hH hG x 1 (by simp) (by norm_num)
  have h := im_star_dot_self (x + (1 : ℂ) • (G *ᵥ x))
  rw [e] at h
  have hx := im_star_dot_self x
  simp only [Complex.add_im, Complex.mul_im, mul_one] at h
  norm_num at h
  linarith

/-- A complex number with zero imaginary part is its real part. -/
theorem eq_ofReal_re (z : ℂ) (h : z.im = 0) : z = (z.re : ℂ) :=
  Complex.ext (by simp) (by simp [h])

/-- **The law's vertex operator** `K(u) = (1 + 4u²) − uΣ_tΓ_t` at a real step weight `u`. -/
noncomputable def lawK (Γ : Fin 5 → Matrix ι ι ℂ) (u : ℝ) : Matrix ι ι ℂ :=
  (1 + 4 * (u : ℂ) ^ 2) • (1 : Matrix ι ι ℂ) - (u : ℂ) • ∑ t, Γ t

omit [Fintype ι] in
theorem lawK_isHermitian (Γ : Fin 5 → Matrix ι ι ℂ) (hH : ∀ t, (Γ t)ᴴ = Γ t) (u : ℝ) :
    (lawK Γ u).IsHermitian := by
  have hc : (1 + 4 * (u : ℂ) ^ 2) = ((1 + 4 * u ^ 2 : ℝ) : ℂ) := by push_cast; ring
  unfold lawK Matrix.IsHermitian
  rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_smul, conjTranspose_one,
    conjTranspose_sum, hc]
  simp only [hH, Complex.star_def, Complex.conj_ofReal]

/-- The quadratic form of `K(u)` is real: `⟨x, K(u)x⟩ = (1 + 4u²)⟨x, x⟩ − uΣ_t⟨x, Γ_tx⟩`. -/
theorem lawK_quad (Γ : Fin 5 → Matrix ι ι ℂ) (hH : ∀ t, (Γ t)ᴴ = Γ t) (hG : ∀ t, Γ t * Γ t = 1)
    (u : ℝ) (x : ι → ℂ) :
    star x ⬝ᵥ (lawK Γ u *ᵥ x) =
      (((1 + 4 * u ^ 2) * (star x ⬝ᵥ x).re - u * ∑ t, (star x ⬝ᵥ (Γ t *ᵥ x)).re : ℝ) : ℂ) := by
  have e1 : star x ⬝ᵥ (lawK Γ u *ᵥ x) =
      (1 + 4 * (u : ℂ) ^ 2) * (star x ⬝ᵥ x) - (u : ℂ) * ∑ t, star x ⬝ᵥ (Γ t *ᵥ x) := by
    unfold lawK
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.sum_mulVec, dotProduct_sub, dotProduct_smul, dotProduct_smul, dotProduct_sum]
    simp only [smul_eq_mul]
  have e2 : star x ⬝ᵥ x = ((star x ⬝ᵥ x).re : ℂ) := eq_ofReal_re _ (im_star_dot_self x)
  have e3 : ∑ t, star x ⬝ᵥ (Γ t *ᵥ x) = ((∑ t, (star x ⬝ᵥ (Γ t *ᵥ x)).re : ℝ) : ℂ) := by
    rw [eq_ofReal_re (∑ t, star x ⬝ᵥ (Γ t *ᵥ x))
      (by rw [Complex.im_sum]; exact Finset.sum_eq_zero fun t _ => herm_real (Γ t) (hH t) (hG t) x),
      Complex.re_sum]
  rw [e1]
  conv_lhs => rw [e2, e3]
  push_cast
  ring

/-- **`K(u)` is positive definite for `0 ≤ u < 1/4`**, with any five Hermitian involutions. -/
theorem lawK_posDef (Γ : Fin 5 → Matrix ι ι ℂ) (hH : ∀ t, (Γ t)ᴴ = Γ t) (hG : ∀ t, Γ t * Γ t = 1)
    (u : ℝ) (hu0 : 0 ≤ u) (hu : u < 1 / 4) : (lawK Γ u).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (lawK_isHermitian Γ hH u) fun x hx => ?_
  rw [lawK_quad Γ hH hG u x, Complex.zero_lt_real]
  have hr := re_star_dot_self_pos x hx
  have hsum : ∑ t, (star x ⬝ᵥ (Γ t *ᵥ x)).re ≤ 5 * (star x ⬝ᵥ x).re := by
    calc ∑ t, (star x ⬝ᵥ (Γ t *ᵥ x)).re ≤ ∑ _t : Fin 5, (star x ⬝ᵥ x).re :=
          Finset.sum_le_sum fun t _ => herm_le (Γ t) (hH t) (hG t) x
      _ = 5 * (star x ⬝ᵥ x).re := by simp
  have h3 : 0 < (1 - u) * (1 - 4 * u) := mul_pos (by linarith) (by linarith)
  nlinarith [mul_le_mul_of_nonneg_left hsum hu0, mul_pos h3 hr]

omit [Fintype ι] in
theorem one_sub_smul_isHermitian (G : Matrix ι ι ℂ) (hH : Gᴴ = G) (u : ℝ) :
    (1 - (u : ℂ) • G).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hH, Complex.star_def,
    Complex.conj_ofReal]

/-- **`1 − uΓ` is positive definite for `0 ≤ u < 1`**, for a Hermitian involution `Γ`. -/
theorem one_sub_smul_posDef (G : Matrix ι ι ℂ) (hH : Gᴴ = G) (hG : G * G = 1) (u : ℝ) (hu0 : 0 ≤ u)
    (hu1 : u < 1) : (1 - (u : ℂ) • G).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (one_sub_smul_isHermitian G hH u) fun x hx => ?_
  have e1 : star x ⬝ᵥ ((1 - (u : ℂ) • G) *ᵥ x) = star x ⬝ᵥ x - (u : ℂ) * (star x ⬝ᵥ (G *ᵥ x)) := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub, dotProduct_smul,
      smul_eq_mul]
  have e2 : star x ⬝ᵥ x = ((star x ⬝ᵥ x).re : ℂ) := eq_ofReal_re _ (im_star_dot_self x)
  have e3 : star x ⬝ᵥ (G *ᵥ x) = ((star x ⬝ᵥ (G *ᵥ x)).re : ℂ) := eq_ofReal_re _ (herm_real G hH hG x)
  rw [e1, e2, e3, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.zero_lt_real]
  have hr := re_star_dot_self_pos x hx
  have hle := herm_le G hH hG x
  nlinarith [mul_le_mul_of_nonneg_left hle hu0]

/-! ## 2. Each connection's weight is a positive number -/

/-- **The law's weight of every unitary connection is a positive number below the critical step:**
`0 < det(I − uB[U])` for `0 ≤ u < 1/4` (Ihara and Bass with the positivity of `K(u)` and of `1 − uΓ_t`). -/
theorem lawWeight_pos (Γ : Fin 5 → Matrix ι ι ℂ) (hH : ∀ t, (Γ t)ᴴ = Γ t) (hG : ∀ t, Γ t * Γ t = 1)
    (u : ℝ) (hu0 : 0 ≤ u) (hu : u < 1 / 4) : 0 < (1 - (u : ℂ) • stepOp Γ).det := by
  have hb := ihara_bass Γ hG (u : ℂ)
  have h1u : (0 : ℂ) < 1 - (u : ℂ) ^ 2 := by
    have e : (1 - (u : ℂ) ^ 2) = ((1 - u ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.zero_lt_real]
    nlinarith
  have hK : 0 < ((1 + 4 * (u : ℂ) ^ 2) • (1 : Matrix ι ι ℂ) - (u : ℂ) • ∑ t, Γ t).det :=
    (lawK_posDef Γ hH hG u hu0 hu).det_pos
  have hprod : 0 < ∏ t, (1 - (u : ℂ) • Γ t).det :=
    Finset.prod_pos fun t _ =>
      (one_sub_smul_posDef (Γ t) (hH t) (hG t) u hu0 (by linarith)).det_pos
  have ha : 0 < (1 - (u : ℂ) ^ 2) ^ Fintype.card ι * ∏ t, (1 - (u : ℂ) • Γ t).det :=
    mul_pos (pow_pos h1u _) hprod
  have hr : 0 < (1 - (u : ℂ) ^ 2) ^ (5 * Fintype.card ι) *
      ((1 + 4 * (u : ℂ) ^ 2) • (1 : Matrix ι ι ℂ) - (u : ℂ) • ∑ t, Γ t).det :=
    mul_pos (pow_pos h1u _) hK
  rw [← hb] at hr
  exact pos_of_mul_pos_right hr ha.le

/-- A positive complex number (in the order of `ℂ`) is a positive real number. -/
theorem exists_real_of_pos {z : ℂ} (hz : 0 < z) : ∃ r : ℝ, 0 < r ∧ z = r := by
  obtain ⟨h1, h2⟩ := Complex.pos_iff.mp hz
  exact ⟨z.re, h1, eq_ofReal_re z h2.symm⟩

/-- **The weight `det(I − uB[U])` is a positive real number** for `0 ≤ u < 1/4`. -/
theorem lawWeight_real (Γ : Fin 5 → Matrix ι ι ℂ) (hH : ∀ t, (Γ t)ᴴ = Γ t) (hG : ∀ t, Γ t * Γ t = 1)
    (u : ℝ) (hu0 : 0 ≤ u) (hu : u < 1 / 4) :
    ∃ r : ℝ, 0 < r ∧ (1 - (u : ℂ) • stepOp Γ).det = r :=
  exists_real_of_pos (lawWeight_pos Γ hH hG u hu0 hu)

/-- **The law itself, `Z[U] = det(I − uB[U])⁻¹`, is positive** for `0 ≤ u < 1/4`. -/
theorem law_pos (Γ : Fin 5 → Matrix ι ι ℂ) (hH : ∀ t, (Γ t)ᴴ = Γ t) (hG : ∀ t, Γ t * Γ t = 1)
    (u : ℝ) (hu0 : 0 ≤ u) (hu : u < 1 / 4) : 0 < ((1 - (u : ℂ) • stepOp Γ).det)⁻¹ := by
  obtain ⟨r, hr, e⟩ := lawWeight_real Γ hH hG u hu0 hu
  rw [e, ← Complex.ofReal_inv, Complex.zero_lt_real]
  exact inv_pos.mpr hr

/-- A positive complex number has argument zero. -/
theorem arg_eq_zero_of_pos {z : ℂ} (hz : 0 < z) : Complex.arg z = 0 := by
  obtain ⟨r, hr, e⟩ := exists_real_of_pos hz
  rw [e]
  exact Complex.arg_ofReal_of_nonneg hr.le

/-- **A closed weight carries no phase:** `arg det(I − uB[U]) = 0` for `0 ≤ u < 1/4`. -/
theorem arg_lawWeight (Γ : Fin 5 → Matrix ι ι ℂ) (hH : ∀ t, (Γ t)ᴴ = Γ t) (hG : ∀ t, Γ t * Γ t = 1)
    (u : ℝ) (hu0 : 0 ≤ u) (hu : u < 1 / 4) : Complex.arg (1 - (u : ℂ) • stepOp Γ).det = 0 :=
  arg_eq_zero_of_pos (lawWeight_pos Γ hH hG u hu0 hu)

/-! ## 3. Time reversal keeps the closed weights -/

/-- **Time reversal on a connection:** every link turned by its complex conjugate. -/
noncomputable def conjConn (Γ : Fin 5 → Matrix ι ι ℂ) : Fin 5 → Matrix ι ι ℂ :=
  fun t => (Γ t).map (starRingEnd ℂ)

omit [Fintype ι] [DecidableEq ι] in
theorem conjConn_herm (Γ : Fin 5 → Matrix ι ι ℂ) (hH : ∀ t, (Γ t)ᴴ = Γ t) (t : Fin 5) :
    (conjConn Γ t)ᴴ = conjConn Γ t := by
  ext i j
  have h : star (Γ t j i) = Γ t i j := by
    have := congrFun (congrFun (hH t) i) j
    rwa [conjTranspose_apply] at this
  simp only [conjConn, conjTranspose_apply, Matrix.map_apply, starRingEnd_apply, h]

theorem conjConn_sq (Γ : Fin 5 → Matrix ι ι ℂ) (hG : ∀ t, Γ t * Γ t = 1) (t : Fin 5) :
    conjConn Γ t * conjConn Γ t = 1 := by
  simp only [conjConn]
  rw [← Matrix.map_mul, hG t]
  exact Matrix.map_one _ (map_zero _) (map_one _)

omit [Fintype ι] [DecidableEq ι] in
theorem stepOp_conj (Γ : Fin 5 → Matrix ι ι ℂ) :
    stepOp (conjConn Γ) = (stepOp Γ).map (starRingEnd ℂ) := by
  ext p q
  simp only [stepOp, conjConn, Matrix.of_apply, Matrix.map_apply]
  split_ifs <;> simp

/-- **Time reversal conjugates the law's weight:** `det(I − uB[Ū]) = conj det(I − uB[U])` for real `u`. -/
theorem lawWeight_conj (Γ : Fin 5 → Matrix ι ι ℂ) (u : ℝ) :
    (1 - (u : ℂ) • stepOp (conjConn Γ)).det = starRingEnd ℂ ((1 - (u : ℂ) • stepOp Γ).det) := by
  rw [RingHom.map_det, RingHom.mapMatrix_apply, stepOp_conj]
  congr 1
  ext p q
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  split_ifs <;> simp [Complex.conj_ofReal]

/-- **The closed weights are real, so time reversal keeps them:** `det(I − uB[Ū]) = det(I − uB[U])`
for `0 ≤ u < 1/4`. -/
theorem lawWeight_conj_eq (Γ : Fin 5 → Matrix ι ι ℂ) (hH : ∀ t, (Γ t)ᴴ = Γ t)
    (hG : ∀ t, Γ t * Γ t = 1) (u : ℝ) (hu0 : 0 ≤ u) (hu : u < 1 / 4) :
    (1 - (u : ℂ) • stepOp (conjConn Γ)).det = (1 - (u : ℂ) • stepOp Γ).det := by
  rw [lawWeight_conj]
  obtain ⟨r, -, e⟩ := lawWeight_real Γ hH hG u hu0 hu
  rw [e, Complex.conj_ofReal]

/-! ## 4. The sum over sectors -/

section Sectors

variable {C : Type*} [Fintype C]

/-- **The sum over configurations** `Z(θ) = Σ_U r_U e^(i q_U θ)`, each configuration with its weight `r_U`
and its integer charge `q_U`. -/
noncomputable def sectorSum (r : C → ℝ) (q : C → ℤ) (θ : ℝ) : ℂ :=
  ∑ c, (r c : ℂ) * Complex.exp (((q c : ℝ) * θ : ℝ) * Complex.I)

/-- **The weight of the sector of charge `n`:** `a_n = Σ_(q_U = n) r_U`. -/
noncomputable def sectorWeight (r : C → ℝ) (q : C → ℤ) (n : ℤ) : ℝ :=
  ∑ c ∈ Finset.univ.filter (fun c => q c = n), r c

/-- **`Z(θ) = Σ_n a_n e^(inθ)`**: the sum over configurations is the sum over sectors. -/
theorem sectorSum_sectors (r : C → ℝ) (q : C → ℤ) (θ : ℝ) :
    sectorSum r q θ = ∑ n ∈ Finset.univ.image q,
      (sectorWeight r q n : ℂ) * Complex.exp (((n : ℝ) * θ : ℝ) * Complex.I) := by
  unfold sectorSum sectorWeight
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image q) (g := q)
    (fun c _ => Finset.mem_image_of_mem q (Finset.mem_univ c))]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Complex.ofReal_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [(Finset.mem_filter.mp hc).2]

/-- **Every inhabited sector has a positive weight**, `a_n > 0`. -/
theorem sectorWeight_pos (r : C → ℝ) (q : C → ℤ) (hr : ∀ c, 0 < r c) (n : ℤ)
    (hn : ∃ c, q c = n) : 0 < sectorWeight r q n := by
  obtain ⟨c, hc⟩ := hn
  exact Finset.sum_pos (fun c _ => hr c) ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩⟩

/-- An empty sector has weight zero. -/
theorem sectorWeight_eq_zero (r : C → ℝ) (q : C → ℤ) (n : ℤ) (hn : ¬∃ c, q c = n) :
    sectorWeight r q n = 0 := by
  unfold sectorWeight
  refine Finset.sum_eq_zero fun c hc => ?_
  exact absurd ⟨c, (Finset.mem_filter.mp hc).2⟩ hn

/-- **`a_(−n) = a_n`** when an involution reverses the charge and keeps the weight. -/
theorem sectorWeight_symm (r : C → ℝ) (q : C → ℤ) (τ : C ≃ C) (hq : ∀ c, q (τ c) = -q c)
    (hrτ : ∀ c, r (τ c) = r c) (n : ℤ) : sectorWeight r q (-n) = sectorWeight r q n := by
  unfold sectorWeight
  rw [Finset.sum_filter, Finset.sum_filter, ← Equiv.sum_comp τ]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [hq, hrτ, neg_inj]

/-- `Z(0) = Σ_U r_U`. -/
theorem sectorSum_zero (r : C → ℝ) (q : C → ℤ) : sectorSum r q 0 = ((∑ c, r c : ℝ) : ℂ) := by
  unfold sectorSum
  simp [Complex.ofReal_sum]

/-- **`|Z(θ)| ≤ Z(0)`** for nonnegative weights. -/
theorem norm_sectorSum_le (r : C → ℝ) (q : C → ℤ) (hr : ∀ c, 0 ≤ r c) (θ : ℝ) :
    ‖sectorSum r q θ‖ ≤ ∑ c, r c := by
  unfold sectorSum
  refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun c _ => ?_))
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_of_nonneg (hr c)]

/-- The odd part cancels: `Σ_U r_U sin(q_U θ) = 0` when an involution reverses the charge and keeps
the weight. -/
theorem sin_sum_zero (r : C → ℝ) (q : C → ℤ) (τ : C ≃ C) (hq : ∀ c, q (τ c) = -q c)
    (hrτ : ∀ c, r (τ c) = r c) (θ : ℝ) : ∑ c, r c * Real.sin (q c * θ) = 0 := by
  have h : ∑ c, r c * Real.sin (q c * θ) = -∑ c, r c * Real.sin (q c * θ) := by
    conv_lhs => rw [← Equiv.sum_comp τ]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [hq, hrτ, Int.cast_neg, neg_mul, Real.sin_neg, mul_neg]
  linarith

/-- **`Z(θ)` is real: `Z(θ) = Σ_U r_U cos(q_U θ)`.** -/
theorem sectorSum_eq_cos (r : C → ℝ) (q : C → ℤ) (τ : C ≃ C) (hq : ∀ c, q (τ c) = -q c)
    (hrτ : ∀ c, r (τ c) = r c) (θ : ℝ) :
    sectorSum r q θ = ((∑ c, r c * Real.cos (q c * θ) : ℝ) : ℂ) := by
  have e : ∀ c, (r c : ℂ) * Complex.exp (((q c : ℝ) * θ : ℝ) * Complex.I) =
      ((r c * Real.cos (q c * θ) : ℝ) : ℂ) + ((r c * Real.sin (q c * θ) : ℝ) : ℂ) * Complex.I := by
    intro c
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.ofReal_mul,
      Complex.ofReal_mul]
    ring
  unfold sectorSum
  simp only [e]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Complex.ofReal_sum, ← Complex.ofReal_sum,
    sin_sum_zero r q τ hq hrτ θ]
  simp

/-- **The sum over sectors is largest exactly at `θ ∈ 2πℤ`:** `|Z(θ)| = Z(0)` if and only if
`θ = 2πk`, when the sectors `0` and `1` are inhabited. -/
theorem norm_sectorSum_eq_iff (r : C → ℝ) (q : C → ℤ) (hr : ∀ c, 0 < r c) (τ : C ≃ C)
    (hq : ∀ c, q (τ c) = -q c) (hrτ : ∀ c, r (τ c) = r c) (h0 : ∃ c, q c = 0)
    (h1 : ∃ c, q c = 1) (θ : ℝ) :
    ‖sectorSum r q θ‖ = ∑ c, r c ↔ ∃ k : ℤ, θ = k * (2 * Real.pi) := by
  rw [sectorSum_eq_cos r q τ hq hrτ θ, Complex.norm_real, Real.norm_eq_abs]
  have hR : 0 ≤ ∑ c, r c := Finset.sum_nonneg fun c _ => (hr c).le
  constructor
  · intro h
    rcases (abs_eq hR).mp h with hf | hf
    · have hsum : ∑ c, r c * (1 - Real.cos (q c * θ)) = 0 := by
        simp only [mul_sub, mul_one, Finset.sum_sub_distrib]
        linarith
      have hz := (Finset.sum_eq_zero_iff_of_nonneg fun c _ =>
        mul_nonneg (hr c).le (by linarith [Real.cos_le_one (q c * θ)])).mp hsum
      obtain ⟨c1, hc1⟩ := h1
      have h1' := hz c1 (Finset.mem_univ _)
      rw [hc1, Int.cast_one, one_mul] at h1'
      have hcos : Real.cos θ = 1 := by
        have := (mul_eq_zero.mp h1').resolve_left (hr c1).ne'
        linarith
      obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff θ).mp hcos
      exact ⟨n, hn.symm⟩
    · exfalso
      have hsum : ∑ c, r c * (1 + Real.cos (q c * θ)) = 0 := by
        simp only [mul_add, mul_one, Finset.sum_add_distrib]
        linarith
      have hz := (Finset.sum_eq_zero_iff_of_nonneg fun c _ =>
        mul_nonneg (hr c).le (by linarith [Real.neg_one_le_cos (q c * θ)])).mp hsum
      obtain ⟨c0, hc0⟩ := h0
      have h0' := hz c0 (Finset.mem_univ _)
      rw [hc0, Int.cast_zero, zero_mul, Real.cos_zero] at h0'
      linarith [hr c0]
  · rintro ⟨k, rfl⟩
    have hcos : ∀ c, Real.cos (q c * (k * (2 * Real.pi))) = 1 := by
      intro c
      have e : (q c : ℝ) * (k * (2 * Real.pi)) = ((q c * k : ℤ) : ℝ) * (2 * Real.pi) := by
        push_cast
        ring
      rw [e, Real.cos_int_mul_two_pi]
    simp only [hcos, mul_one]
    exact abs_of_nonneg hR

/-- **Away from `2πℤ` the sum over sectors is strictly smaller:** `|Z(θ)| < Z(0)`. -/
theorem norm_sectorSum_lt (r : C → ℝ) (q : C → ℤ) (hr : ∀ c, 0 < r c) (τ : C ≃ C)
    (hq : ∀ c, q (τ c) = -q c) (hrτ : ∀ c, r (τ c) = r c) (h0 : ∃ c, q c = 0)
    (h1 : ∃ c, q c = 1) (θ : ℝ) (hθ : ∀ k : ℤ, θ ≠ k * (2 * Real.pi)) :
    ‖sectorSum r q θ‖ < ∑ c, r c := by
  refine lt_of_le_of_ne (norm_sectorSum_le r q (fun c => (hr c).le) θ) fun h => ?_
  obtain ⟨k, hk⟩ := (norm_sectorSum_eq_iff r q hr τ hq hrτ h0 h1 θ).mp h
  exact hθ k hk

theorem hasDerivAt_cosSum (r : C → ℝ) (q : C → ℤ) (θ : ℝ) :
    HasDerivAt (fun y => ∑ c, r c * Real.cos (q c * y))
      (∑ c, -(r c * q c * Real.sin (q c * θ))) θ := by
  apply HasDerivAt.fun_sum
  intro c _
  have h := (((hasDerivAt_id' (x := θ)).const_mul (q c : ℝ)).cos).const_mul (r c)
  convert h using 1
  ring

theorem hasDerivAt_sinSum (r : C → ℝ) (q : C → ℤ) (θ : ℝ) :
    HasDerivAt (fun y => ∑ c, -(r c * q c * Real.sin (q c * y)))
      (∑ c, -(r c * (q c : ℝ) ^ 2 * Real.cos (q c * θ))) θ := by
  apply HasDerivAt.fun_sum
  intro c _
  have h := ((((hasDerivAt_id' (x := θ)).const_mul (q c : ℝ)).sin).const_mul (r c * q c)).neg
  convert h using 1
  ring

/-- The derivative of `−log Z` where `Z > 0`: `−Z′/Z`. -/
theorem negLog_hasDerivAt (r : C → ℝ) (q : C → ℤ) (θ : ℝ)
    (hf : 0 < ∑ c, r c * Real.cos (q c * θ)) :
    HasDerivAt (fun y => -Real.log (∑ c, r c * Real.cos (q c * y)))
      (-((∑ c, -(r c * q c * Real.sin (q c * θ))) / ∑ c, r c * Real.cos (q c * θ))) θ :=
  ((hasDerivAt_cosSum r q θ).log hf.ne').neg

theorem negLog_second (r : C → ℝ) (q : C → ℤ) (hR : 0 < ∑ c, r c) :
    HasDerivAt
      (fun y => -((∑ c, -(r c * q c * Real.sin (q c * y))) / ∑ c, r c * Real.cos (q c * y)))
      ((∑ c, r c * (q c : ℝ) ^ 2) / ∑ c, r c) 0 := by
  have h := ((hasDerivAt_sinSum r q 0).div (hasDerivAt_cosSum r q 0) (by simpa using hR.ne')).neg
  have hR' : (∑ c, r c) ≠ 0 := hR.ne'
  convert h using 1
  simp only [mul_zero, Real.sin_zero, Real.cos_zero, mul_one, neg_zero, Finset.sum_const_zero,
    sub_zero, Finset.sum_neg_distrib]
  field_simp

/-- **`θ = 0` is a stationary point of `−log Z`.** -/
theorem negLog_deriv_zero (r : C → ℝ) (q : C → ℤ) (hR : 0 < ∑ c, r c) :
    deriv (fun y => -Real.log (∑ c, r c * Real.cos (q c * y))) 0 = 0 := by
  rw [(negLog_hasDerivAt r q 0 (by simpa using hR)).deriv]
  simp

/-- **`(−log Z)″(0) = Σ_U q_U² r_U / Σ_U r_U`.** -/
theorem negLog_second_deriv (r : C → ℝ) (q : C → ℤ) (hR : 0 < ∑ c, r c) :
    deriv (deriv (fun y => -Real.log (∑ c, r c * Real.cos (q c * y)))) 0 =
      (∑ c, r c * (q c : ℝ) ^ 2) / ∑ c, r c := by
  have hcont : ContinuousAt (fun y => ∑ c, r c * Real.cos (q c * y)) 0 :=
    (hasDerivAt_cosSum r q 0).continuousAt
  have hpos : ∀ᶠ y in nhds (0 : ℝ), 0 < ∑ c, r c * Real.cos (q c * y) :=
    hcont.eventually (lt_mem_nhds (by simpa using hR))
  have heq : deriv (fun y => -Real.log (∑ c, r c * Real.cos (q c * y))) =ᶠ[nhds 0]
      fun y => -((∑ c, -(r c * q c * Real.sin (q c * y))) / ∑ c, r c * Real.cos (q c * y)) :=
    hpos.mono fun y hy => (negLog_hasDerivAt r q y hy).deriv
  exact ((negLog_second r q hR).congr_of_eventuallyEq heq).deriv

/-- **The curvature at `θ = 0` is positive** when the unit sector is inhabited. -/
theorem curvature_pos (r : C → ℝ) (q : C → ℤ) (hr : ∀ c, 0 < r c) (h1 : ∃ c, q c = 1) :
    0 < (∑ c, r c * (q c : ℝ) ^ 2) / ∑ c, r c := by
  obtain ⟨c1, hc1⟩ := h1
  apply div_pos
  · exact Finset.sum_pos' (fun c _ => mul_nonneg (hr c).le (sq_nonneg _))
      ⟨c1, Finset.mem_univ _, by rw [hc1]; simpa using hr c1⟩
  · exact Finset.sum_pos (fun c _ => hr c) ⟨c1, Finset.mem_univ _⟩

end Sectors

/-! ## 5. The law's sector source: Proposition 115 -/

/-- **A sector source of the law.** A finite family of unitary connections `Γ U` on the vertices (five
Hermitian involutions each) with positive gauge weights `w U` and integer charges `q U`, and time reversal
`τ`: it reverses the charge, keeps the gauge weight and, being antiunitary, conjugates the law's weight. -/
structure SectorSource (V : Type*) [Fintype V] [DecidableEq V] (C : Type*) where
  Γ : C → Fin 5 → Matrix V V ℂ
  herm : ∀ c t, (Γ c t)ᴴ = Γ c t
  invol : ∀ c t, Γ c t * Γ c t = 1
  w : C → ℝ
  w_pos : ∀ c, 0 < w c
  q : C → ℤ
  τ : C ≃ C
  q_τ : ∀ c, q (τ c) = -q c
  w_τ : ∀ c, w (τ c) = w c
  law_τ : ∀ (u : ℝ) (c : C),
    (1 - (u : ℂ) • stepOp (Γ (τ c))).det = starRingEnd ℂ ((1 - (u : ℂ) • stepOp (Γ c)).det)

/-- Time reversal by conjugating every link conjugates the law's weight, as a sector source asks. -/
theorem law_τ_of_conj {C : Type*} (Γ : C → Fin 5 → Matrix ι ι ℂ) (τ : C ≃ C)
    (h : ∀ c, Γ (τ c) = conjConn (Γ c)) (u : ℝ) (c : C) :
    (1 - (u : ℂ) • stepOp (Γ (τ c))).det = starRingEnd ℂ ((1 - (u : ℂ) • stepOp (Γ c)).det) := by
  rw [h c, lawWeight_conj]

namespace SectorSource

variable {C : Type*} [Fintype C] (S : SectorSource ι C)

/-- The weight of one configuration: `w_U det(I − uB[U])`. -/
noncomputable def weight (u : ℝ) (c : C) : ℂ := (S.w c : ℂ) * (1 - (u : ℂ) • stepOp (S.Γ c)).det

/-- Its real value. -/
noncomputable def wt (u : ℝ) (c : C) : ℝ := (S.weight u c).re

/-- **The sector sum of the law:** `Z_top(θ) = Σ_U w_U det(I − uB[U]) e^(i q_U θ)`. -/
noncomputable def Ztop (u θ : ℝ) : ℂ :=
  ∑ c, S.weight u c * Complex.exp (((S.q c : ℝ) * θ : ℝ) * Complex.I)

/-- **The weight of the sector of charge `n`:** `a_n = Σ_(q_U = n) w_U det(I − uB[U])`. -/
noncomputable def a (u : ℝ) (n : ℤ) : ℂ :=
  ∑ c ∈ Finset.univ.filter (fun c => S.q c = n), S.weight u c

omit [Fintype C] in
theorem weight_pos (u : ℝ) (hu0 : 0 ≤ u) (hu : u < 1 / 4) (c : C) : 0 < S.weight u c :=
  mul_pos (Complex.zero_lt_real.mpr (S.w_pos c))
    (lawWeight_pos (S.Γ c) (S.herm c) (S.invol c) u hu0 hu)

omit [Fintype C] in
theorem weight_eq (u : ℝ) (hu0 : 0 ≤ u) (hu : u < 1 / 4) (c : C) :
    S.weight u c = (S.wt u c : ℂ) :=
  eq_ofReal_re _ (Complex.pos_iff.mp (S.weight_pos u hu0 hu c)).2.symm

omit [Fintype C] in
theorem wt_pos (u : ℝ) (hu0 : 0 ≤ u) (hu : u < 1 / 4) (c : C) : 0 < S.wt u c :=
  (Complex.pos_iff.mp (S.weight_pos u hu0 hu c)).1

omit [Fintype C] in
/-- Time reversal keeps each configuration's weight (the closed weights are real). -/
theorem wt_τ (u : ℝ) (hu0 : 0 ≤ u) (hu : u < 1 / 4) (c : C) : S.wt u (S.τ c) = S.wt u c := by
  unfold wt weight
  rw [S.law_τ u c, S.w_τ c]
  obtain ⟨r, -, e⟩ := lawWeight_real (S.Γ c) (S.herm c) (S.invol c) u hu0 hu
  rw [e, Complex.conj_ofReal]

theorem Ztop_eq (u : ℝ) (hu0 : 0 ≤ u) (hu : u < 1 / 4) (θ : ℝ) :
    S.Ztop u θ = sectorSum (S.wt u) S.q θ := by
  unfold Ztop sectorSum
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [S.weight_eq u hu0 hu c]

theorem a_eq (u : ℝ) (hu0 : 0 ≤ u) (hu : u < 1 / 4) (n : ℤ) :
    S.a u n = (sectorWeight (S.wt u) S.q n : ℂ) := by
  unfold a sectorWeight
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun c _ => S.weight_eq u hu0 hu c

/-- **Proposition 115, the sum over sectors**, for `0 ≤ u < 1/4`: every inhabited sector has a positive
weight `a_n`; `a_(−n) = a_n`; `Z_top(θ) = Σ_n a_n e^(inθ)`; `Z_top(θ) = Σ_U w_U det(I − uB[U]) cos(q_U θ)`
is real; `Z_top(0)` is real and `|Z_top(θ)| ≤ Z_top(0)`. -/
theorem prop115 (u : ℝ) (hu0 : 0 ≤ u) (hu : u < 1 / 4) :
    (∀ n : ℤ, (∃ c, S.q c = n) → 0 < S.a u n) ∧
    (∀ n : ℤ, S.a u (-n) = S.a u n) ∧
    (∀ θ : ℝ, S.Ztop u θ = ∑ n ∈ Finset.univ.image S.q,
      S.a u n * Complex.exp (((n : ℝ) * θ : ℝ) * Complex.I)) ∧
    (∀ θ : ℝ, S.Ztop u θ = ((∑ c, S.wt u c * Real.cos (S.q c * θ) : ℝ) : ℂ)) ∧
    S.Ztop u 0 = ((S.Ztop u 0).re : ℂ) ∧
    (∀ θ : ℝ, ‖S.Ztop u θ‖ ≤ (S.Ztop u 0).re) := by
  have hr := S.wt_pos u hu0 hu
  have hrτ := S.wt_τ u hu0 hu
  have hZ0 : S.Ztop u 0 = ((∑ c, S.wt u c : ℝ) : ℂ) := by rw [S.Ztop_eq u hu0 hu, sectorSum_zero]
  refine ⟨fun n hn => ?_, fun n => ?_, fun θ => ?_, fun θ => ?_, ?_, fun θ => ?_⟩
  · rw [S.a_eq u hu0 hu n, Complex.zero_lt_real]
    exact sectorWeight_pos _ _ hr n hn
  · rw [S.a_eq u hu0 hu, S.a_eq u hu0 hu, sectorWeight_symm _ _ S.τ S.q_τ hrτ n]
  · rw [S.Ztop_eq u hu0 hu, sectorSum_sectors]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [S.a_eq u hu0 hu]
  · rw [S.Ztop_eq u hu0 hu, sectorSum_eq_cos _ _ S.τ S.q_τ hrτ]
  · rw [hZ0, Complex.ofReal_re]
  · rw [hZ0, Complex.ofReal_re, S.Ztop_eq u hu0 hu]
    exact norm_sectorSum_le _ _ (fun c => (hr c).le) θ

/-- **Proposition 115, equality only at zero angle:** with the sectors `0` and `1` inhabited,
`Z_top(0) > 0` and `|Z_top(θ)| = Z_top(0)` exactly when `θ ∈ 2πℤ`. -/
theorem prop115_max_iff (u : ℝ) (hu0 : 0 ≤ u) (hu : u < 1 / 4) (h0 : ∃ c, S.q c = 0)
    (h1 : ∃ c, S.q c = 1) (θ : ℝ) :
    0 < (S.Ztop u 0).re ∧
      (‖S.Ztop u θ‖ = (S.Ztop u 0).re ↔ ∃ k : ℤ, θ = k * (2 * Real.pi)) := by
  have hr := S.wt_pos u hu0 hu
  have hZ0 : S.Ztop u 0 = ((∑ c, S.wt u c : ℝ) : ℂ) := by rw [S.Ztop_eq u hu0 hu, sectorSum_zero]
  obtain ⟨c0, hc0⟩ := h0
  refine ⟨?_, ?_⟩
  · rw [hZ0, Complex.ofReal_re]
    exact Finset.sum_pos (fun c _ => hr c) ⟨c0, Finset.mem_univ _⟩
  · rw [hZ0, Complex.ofReal_re, S.Ztop_eq u hu0 hu]
    exact norm_sectorSum_eq_iff _ _ hr S.τ S.q_τ (S.wt_τ u hu0 hu) ⟨c0, hc0⟩ h1 θ

/-- **Proposition 115, the curvature:** on the real line `Z_top(θ) = Re Z_top(θ)`, `θ = 0` is a stationary
point of `−log Z_top` and `(−log Z_top)″(0) = Σ_U q_U² w_U det(I − uB[U]) / Σ_U w_U det(I − uB[U]) > 0`
when the unit sector is inhabited. -/
theorem prop115_curvature (u : ℝ) (hu0 : 0 ≤ u) (hu : u < 1 / 4) (h1 : ∃ c, S.q c = 1) :
    deriv (fun θ => -Real.log (S.Ztop u θ).re) 0 = 0 ∧
    deriv (deriv (fun θ => -Real.log (S.Ztop u θ).re)) 0 =
      (∑ c, S.wt u c * (S.q c : ℝ) ^ 2) / ∑ c, S.wt u c ∧
    0 < (∑ c, S.wt u c * (S.q c : ℝ) ^ 2) / ∑ c, S.wt u c := by
  have hr := S.wt_pos u hu0 hu
  have hfun : (fun θ => -Real.log (S.Ztop u θ).re) =
      fun θ => -Real.log (∑ c, S.wt u c * Real.cos (S.q c * θ)) := by
    funext θ
    rw [S.Ztop_eq u hu0 hu, sectorSum_eq_cos _ _ S.τ S.q_τ (S.wt_τ u hu0 hu), Complex.ofReal_re]
  obtain ⟨c1, hc1⟩ := h1
  have hR : 0 < ∑ c, S.wt u c := Finset.sum_pos (fun c _ => hr c) ⟨c1, Finset.mem_univ _⟩
  rw [hfun]
  exact ⟨negLog_deriv_zero _ _ hR, negLog_second_deriv _ _ hR, curvature_pos _ _ hr ⟨c1, hc1⟩⟩

omit [Fintype C] in
/-- **A product of closed weights is a positive number**, so it carries no phase. -/
theorem closedWeights_prod_pos {m : Type*} [Fintype m] (Γm : m → Fin 5 → Matrix ι ι ℂ)
    (hH : ∀ j t, (Γm j t)ᴴ = Γm j t) (hG : ∀ j t, Γm j t * Γm j t = 1) (um : m → ℝ)
    (hu0 : ∀ j, 0 ≤ um j) (hu : ∀ j, um j < 1 / 4) :
    0 < ∏ j, (1 - (um j : ℂ) • stepOp (Γm j)).det :=
  Finset.prod_pos fun j _ => lawWeight_pos (Γm j) (hH j) (hG j) (um j) (hu0 j) (hu j)

/-- **θ̄ = 0 where the sum over sectors is largest.** If `|Z_top(θ)| = Z_top(0)` and the mass determinant
`det(M_uM_d)` is a positive number (for instance a product of closed weights, `closedWeights_prod_pos`),
then `θ̄ = θ + arg det(M_uM_d) ∈ 2πℤ`. -/
theorem theta_bar_zero (u : ℝ) (hu0 : 0 ≤ u) (hu : u < 1 / 4) (h0 : ∃ c, S.q c = 0)
    (h1 : ∃ c, S.q c = 1) (θ : ℝ) (hmax : ‖S.Ztop u θ‖ = (S.Ztop u 0).re) (detM : ℂ)
    (hM : 0 < detM) : ∃ k : ℤ, θ + Complex.arg detM = k * (2 * Real.pi) := by
  rw [arg_eq_zero_of_pos hM, add_zero]
  exact ((S.prop115_max_iff u hu0 hu h0 h1 θ).2).mp hmax

end SectorSource

end Comparison.ArticleStatements

#print axioms Comparison.ArticleStatements.re_star_mul_self
#print axioms Comparison.ArticleStatements.im_star_mul_self
#print axioms Comparison.ArticleStatements.re_star_dot_self_nonneg
#print axioms Comparison.ArticleStatements.re_star_dot_self_pos
#print axioms Comparison.ArticleStatements.im_star_dot_self
#print axioms Comparison.ArticleStatements.herm_bound
#print axioms Comparison.ArticleStatements.herm_le
#print axioms Comparison.ArticleStatements.herm_real
#print axioms Comparison.ArticleStatements.eq_ofReal_re
#print axioms Comparison.ArticleStatements.lawK_isHermitian
#print axioms Comparison.ArticleStatements.lawK_quad
#print axioms Comparison.ArticleStatements.lawK_posDef
#print axioms Comparison.ArticleStatements.one_sub_smul_isHermitian
#print axioms Comparison.ArticleStatements.one_sub_smul_posDef
#print axioms Comparison.ArticleStatements.lawWeight_pos
#print axioms Comparison.ArticleStatements.exists_real_of_pos
#print axioms Comparison.ArticleStatements.lawWeight_real
#print axioms Comparison.ArticleStatements.law_pos
#print axioms Comparison.ArticleStatements.arg_eq_zero_of_pos
#print axioms Comparison.ArticleStatements.arg_lawWeight
#print axioms Comparison.ArticleStatements.conjConn_herm
#print axioms Comparison.ArticleStatements.conjConn_sq
#print axioms Comparison.ArticleStatements.stepOp_conj
#print axioms Comparison.ArticleStatements.lawWeight_conj
#print axioms Comparison.ArticleStatements.lawWeight_conj_eq
#print axioms Comparison.ArticleStatements.sectorSum_sectors
#print axioms Comparison.ArticleStatements.sectorWeight_pos
#print axioms Comparison.ArticleStatements.sectorWeight_eq_zero
#print axioms Comparison.ArticleStatements.sectorWeight_symm
#print axioms Comparison.ArticleStatements.sectorSum_zero
#print axioms Comparison.ArticleStatements.norm_sectorSum_le
#print axioms Comparison.ArticleStatements.sin_sum_zero
#print axioms Comparison.ArticleStatements.sectorSum_eq_cos
#print axioms Comparison.ArticleStatements.norm_sectorSum_eq_iff
#print axioms Comparison.ArticleStatements.norm_sectorSum_lt
#print axioms Comparison.ArticleStatements.hasDerivAt_cosSum
#print axioms Comparison.ArticleStatements.hasDerivAt_sinSum
#print axioms Comparison.ArticleStatements.negLog_hasDerivAt
#print axioms Comparison.ArticleStatements.negLog_second
#print axioms Comparison.ArticleStatements.negLog_deriv_zero
#print axioms Comparison.ArticleStatements.negLog_second_deriv
#print axioms Comparison.ArticleStatements.curvature_pos
#print axioms Comparison.ArticleStatements.law_τ_of_conj
#print axioms Comparison.ArticleStatements.SectorSource.weight_pos
#print axioms Comparison.ArticleStatements.SectorSource.weight_eq
#print axioms Comparison.ArticleStatements.SectorSource.wt_pos
#print axioms Comparison.ArticleStatements.SectorSource.wt_τ
#print axioms Comparison.ArticleStatements.SectorSource.Ztop_eq
#print axioms Comparison.ArticleStatements.SectorSource.a_eq
#print axioms Comparison.ArticleStatements.SectorSource.prop115
#print axioms Comparison.ArticleStatements.SectorSource.prop115_max_iff
#print axioms Comparison.ArticleStatements.SectorSource.prop115_curvature
#print axioms Comparison.ArticleStatements.SectorSource.closedWeights_prod_pos
#print axioms Comparison.ArticleStatements.SectorSource.theta_bar_zero
