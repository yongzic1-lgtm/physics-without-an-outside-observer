import Comparison.System.Postulates
import Comparison.WholePicture.SecondVariation
import Comparison.WholePicture.Cells
import Comparison.Existence.Plaquette
import Comparison.Mass.Basic

/-!
# The proof system, the law: Proposition 62 and equation (27), the law in small phases

The signed step with `U(1)` phases `e^{iθ}` on the forty links,
`A₋[e^{iθ}]_{xy} = A_{xy} e^{iΦ_{xy}}`, `Φ = Σ_ℓ θ_ℓ X_ℓ` (`X_ℓ = E_{VU} − E_{UV}` on the link `ℓ = (U, V)`), and
`K(t) = I − wA₋[e^{itθ}]` along the ray `tθ`. `WholePicture/SecondVariation.lean` proves the Hessian formula
`H(w) = −w² tr(R ∂A R ∂A) − δ w tr(R ∂²A) = −κ(w)CᵀC` (`hessLaw_eq`); here it is proved to be **the second
derivative of the law itself**:

* `hasDerivAt_inv_entry`: the entries of `K(t)⁻¹` have the derivative `−K⁻¹K′K⁻¹` wherever `det K ≠ 0`;
* `K1ph_zero`, `K2ph_zero`: `K′(0) = −w Σ_ℓ θ_ℓ ∂_ℓA`, `K″(0) = −w Σ_ℓ θ_ℓ² ∂²_ℓA`;
* `logDeriv_zero`, `hasDerivAt_logDeriv`: **the logarithmic derivative `h(t) = tr(K(t)⁻¹K′(t))` of
  `det K(t)` has `h(0) = 0` and `h′(0) = Σ_{jk} θ_jθ_k H_{jk}(w) = −κ(w)‖Cθ‖²`**;
* `law_small_phases`: **`g(t) = det(I − wA₋[e^{itθ}])` has `g(0) ≠ 0`, `g′(0) = 0`, `g″(0) = −κ(w)‖Cθ‖² g(0)` and
  `g(−t) = g(t)`**, for every complex `w` with `1 − 5w² ≠ 0` and every direction `θ`;
* `Law.prop_62_sixteen` (the sixteen vertices; `prop_62` in `Law/PhaseLaw.lean`), `eq_27`.
-/

open Matrix Complex Filter Topology Comparison Comparison.WholePicture

namespace Comparison.System

namespace Law

/-! ## The inverse along a path -/

section Inverse

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The derivative of the inverse:** if the entries of `K` have the derivatives `K′` at `t₀` and
`det K(t₀) ≠ 0`, the entries of `K⁻¹` have the derivatives `−K(t₀)⁻¹K′K(t₀)⁻¹`. -/
theorem hasDerivAt_inv_entry (K : ℂ → Matrix ι ι ℂ) (K' : Matrix ι ι ℂ) (t₀ : ℂ)
    (hK : ∀ i j, HasDerivAt (fun t => K t i j) (K' i j) t₀) (hdet : (K t₀).det ≠ 0) (i j : ι) :
    HasDerivAt (fun t => (K t)⁻¹ i j) (-((K t₀)⁻¹ * K' * (K t₀)⁻¹) i j) t₀ := by
  have hKc : ContinuousAt K t₀ :=
    continuousAt_pi.2 fun a => continuousAt_pi.2 fun b => (hK a b).continuousAt
  have hinv : ContinuousAt (fun t => (K t)⁻¹) t₀ := by
    have h1 : ContinuousAt Inv.inv (K t₀) := by
      refine continuousAt_matrix_inv (K t₀) ?_
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ hdet
    exact h1.comp hKc
  have hdc : ContinuousAt (fun t => (K t).det) t₀ :=
    (continuous_id.matrix_det.continuousAt).comp hKc
  have hev : ∀ᶠ t in 𝓝[≠] t₀, (K t).det ≠ 0 :=
    (hdc.eventually_ne hdet).filter_mono nhdsWithin_le_nhds
  rw [hasDerivAt_iff_tendsto_slope]
  -- the slope of the inverse is `−K(t₀)⁻¹ · slope K · K(t)⁻¹`
  have hlim : Tendsto (fun t => -(∑ k, ∑ l, (K t₀)⁻¹ i k * slope (fun s => K s k l) t₀ t *
      (K t)⁻¹ l j)) (𝓝[≠] t₀) (𝓝 (-((K t₀)⁻¹ * K' * (K t₀)⁻¹) i j)) := by
    have e : -((K t₀)⁻¹ * K' * (K t₀)⁻¹) i j =
        -(∑ k, ∑ l, (K t₀)⁻¹ i k * K' k l * (K t₀)⁻¹ l j) := by
      simp only [Matrix.mul_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
    rw [e]
    refine Tendsto.neg (tendsto_finsetSum _ fun k _ => tendsto_finsetSum _ fun l _ => ?_)
    refine (tendsto_const_nhds.mul ((hasDerivAt_iff_tendsto_slope.mp (hK k l)))).mul ?_
    exact ((continuous_apply_apply l j).continuousAt.comp hinv).tendsto.mono_left nhdsWithin_le_nhds
  refine hlim.congr' ?_
  filter_upwards [hev, self_mem_nhdsWithin] with t ht ht0
  have hne : t - t₀ ≠ 0 := sub_ne_zero.mpr ht0
  have hu0 : IsUnit (K t₀).det := isUnit_iff_ne_zero.mpr hdet
  have hu : IsUnit (K t).det := isUnit_iff_ne_zero.mpr ht
  have hdiff : (K t)⁻¹ - (K t₀)⁻¹ = -((K t₀)⁻¹ * (K t - K t₀) * (K t)⁻¹) := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu,
      Matrix.nonsing_inv_mul _ hu0, Matrix.mul_one, Matrix.one_mul]
    abel
  have he := congrFun (congrFun hdiff i) j
  simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.mul_apply, Finset.sum_mul] at he
  rw [Finset.sum_comm] at he
  rw [slope_def_field, he]
  simp only [slope_def_field, Matrix.sub_apply]
  rw [neg_div, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun l _ => ?_
  field_simp

end Inverse

theorem continuousAt_det_of_entries {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ℂ → Matrix ι ι ℂ)
    (t₀ : ℂ) (h : ∀ i j, ContinuousAt (fun t => K t i j) t₀) :
    ContinuousAt (fun t => (K t).det) t₀ := by
  have hKc : ContinuousAt K t₀ := continuousAt_pi.2 fun a => continuousAt_pi.2 fun b => h a b
  exact (continuous_id.matrix_det.continuousAt).comp hKc

/-! ## The phases on the links -/

/-- The link phases as a matrix: `Φ = Σ_ℓ θ_ℓ X_ℓ`. -/
noncomputable def phiC (θ : Fin 40 → ℝ) : Matrix (Fin 16) (Fin 16) ℂ := ∑ l, (θ l : ℂ) • linkX l

/-- `I − wA₋[e^{itθ}]`. -/
noncomputable def Kph (w : ℂ) (θ : Fin 40 → ℝ) (t : ℂ) : Matrix (Fin 16) (Fin 16) ℂ :=
  Matrix.of fun x y => (1 : Matrix (Fin 16) (Fin 16) ℂ) x y -
    w * (AC x y * Complex.exp (I * phiC θ x y * t))

/-- `K′(t)`. -/
noncomputable def K1ph (w : ℂ) (θ : Fin 40 → ℝ) (t : ℂ) : Matrix (Fin 16) (Fin 16) ℂ :=
  Matrix.of fun x y => -w * (AC x y * (I * phiC θ x y * Complex.exp (I * phiC θ x y * t)))

/-- `K″(t)`. -/
noncomputable def K2ph (w : ℂ) (θ : Fin 40 → ℝ) (t : ℂ) : Matrix (Fin 16) (Fin 16) ℂ :=
  Matrix.of fun x y => -w * (AC x y * ((I * phiC θ x y) ^ 2 * Complex.exp (I * phiC θ x y * t)))

theorem hasDerivAt_exp_lin (c t : ℂ) :
    HasDerivAt (fun s => Complex.exp (c * s)) (c * Complex.exp (c * t)) t := by
  have h := ((hasDerivAt_id' t).const_mul c).cexp
  convert h using 1
  ring

theorem Kph_deriv (w : ℂ) (θ : Fin 40 → ℝ) (t : ℂ) (x y : Fin 16) :
    HasDerivAt (fun s => Kph w θ s x y) (K1ph w θ t x y) t := by
  have h := ((hasDerivAt_exp_lin (I * phiC θ x y) t).const_mul (AC x y)).const_mul (-w)
  have h' := h.const_add ((1 : Matrix (Fin 16) (Fin 16) ℂ) x y)
  convert h' using 1 <;> first
    | (funext s; simp only [Kph, Matrix.of_apply] <;> ring)
    | (simp only [K1ph, Matrix.of_apply] <;> ring)

theorem K1ph_deriv (w : ℂ) (θ : Fin 40 → ℝ) (t : ℂ) (x y : Fin 16) :
    HasDerivAt (fun s => K1ph w θ s x y) (K2ph w θ t x y) t := by
  have h := (((hasDerivAt_exp_lin (I * phiC θ x y) t).const_mul (I * phiC θ x y)).const_mul
    (AC x y)).const_mul (-w)
  convert h using 1 <;> first
    | (funext s; simp only [K1ph, Matrix.of_apply])
    | (simp only [K2ph, Matrix.of_apply] <;> ring)

/-! ## The links -/

theorem linkU_ne_linkV : ∀ l : Fin 40, linkU l ≠ linkV l := by decide

theorem link_distinct : ∀ l m : Fin 40, l ≠ m →
    ¬ (linkU l = linkU m ∧ linkV l = linkV m) ∧ ¬ (linkU l = linkV m ∧ linkV l = linkU m) := by
  decide

theorem linkX_apply (l : Fin 40) (x y : Fin 16) :
    linkX l x y = (if linkV l = x ∧ linkU l = y then 1 else 0) -
      (if linkU l = x ∧ linkV l = y then 1 else 0) := by
  simp [linkX, Matrix.single_apply]

theorem AC_mul_linkX (l : Fin 40) (x y : Fin 16) :
    AC x y * linkX l x y = (linkSign l : ℂ) * linkX l x y := by
  rw [linkX_apply]
  by_cases h1 : linkV l = x ∧ linkU l = y
  · obtain ⟨rfl, rfl⟩ := h1
    have e : AC (linkV l) (linkU l) = (linkSign l : ℂ) := by
      simp only [AC, Matrix.of_apply, sadjZ_VU]
    rw [e]
  · by_cases h2 : linkU l = x ∧ linkV l = y
    · obtain ⟨rfl, rfl⟩ := h2
      have e : AC (linkU l) (linkV l) = (linkSign l : ℂ) := by
        simp only [AC, Matrix.of_apply, linkSign]
      rw [e]
    · rw [if_neg h1, if_neg h2]
      ring

theorem AC_mul_linkX_sq (l : Fin 40) (x y : Fin 16) :
    AC x y * linkX l x y ^ 2 = (linkSign l : ℂ) * linkX l x y ^ 2 := by
  rw [sq, ← mul_assoc, AC_mul_linkX, mul_assoc]

theorem linkX_dividedSet (l : Fin 40) (x y : Fin 16) (h : linkX l x y ≠ 0) :
    (linkV l = x ∧ linkU l = y) ∨ (linkU l = x ∧ linkV l = y) := by
  by_contra hc
  rw [not_or] at hc
  apply h
  rw [linkX_apply, if_neg hc.1, if_neg hc.2, sub_zero]

theorem linkX_mul_linkX (l m : Fin 40) (hlm : l ≠ m) (x y : Fin 16) :
    linkX l x y * linkX m x y = 0 := by
  by_cases hl : linkX l x y = 0
  · rw [hl, zero_mul]
  by_cases hm : linkX m x y = 0
  · rw [hm, mul_zero]
  exfalso
  obtain ⟨h1, h2⟩ := link_distinct l m hlm
  rcases linkX_dividedSet l x y hl with ⟨a, b⟩ | ⟨a, b⟩ <;>
    rcases linkX_dividedSet m x y hm with ⟨c, d⟩ | ⟨c, d⟩
  · exact h1 ⟨b.trans d.symm, a.trans c.symm⟩
  · exact h2 ⟨b.trans d.symm, a.trans c.symm⟩
  · exact h2 ⟨a.trans c.symm, b.trans d.symm⟩
  · exact h1 ⟨a.trans c.symm, b.trans d.symm⟩

theorem linkX_antisymm (l : Fin 40) (x y : Fin 16) : linkX l y x = -linkX l x y := by
  rw [linkX_apply, linkX_apply]
  have e1 : (linkV l = y ∧ linkU l = x) ↔ (linkU l = x ∧ linkV l = y) := and_comm
  have e2 : (linkU l = y ∧ linkV l = x) ↔ (linkV l = x ∧ linkU l = y) := and_comm
  simp only [e1, e2]
  ring

theorem linkX_sq (l : Fin 40) (x y : Fin 16) :
    linkX l x y ^ 2 = (Matrix.single (linkV l) (linkU l) (1 : ℂ) +
      Matrix.single (linkU l) (linkV l) (1 : ℂ) : Matrix (Fin 16) (Fin 16) ℂ) x y := by
  rw [linkX_apply, Matrix.add_apply, Matrix.single_apply, Matrix.single_apply]
  by_cases a1 : linkV l = x ∧ linkU l = y
  · have a2 : ¬ (linkU l = x ∧ linkV l = y) := fun h => linkU_ne_linkV l (h.1.trans a1.1.symm)
    rw [if_pos a1, if_neg a2]
    norm_num
  · by_cases a2 : linkU l = x ∧ linkV l = y
    · rw [if_neg a1, if_pos a2]
      norm_num
    · rw [if_neg a1, if_neg a2]
      norm_num

theorem phiC_apply (θ : Fin 40 → ℝ) (x y : Fin 16) :
    phiC θ x y = ∑ l, (θ l : ℂ) * linkX l x y := by
  simp [phiC, Matrix.sum_apply]

theorem phiC_sq (θ : Fin 40 → ℝ) (x y : Fin 16) :
    phiC θ x y ^ 2 = ∑ l, (θ l : ℂ) ^ 2 * linkX l x y ^ 2 := by
  rw [phiC_apply, sq, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_eq_single l]
  · ring
  · intro m _ hml
    have := linkX_mul_linkX l m (Ne.symm hml) x y
    linear_combination (θ l : ℂ) * (θ m : ℂ) * this
  · simp

/-! ## The ray at `t = 0` -/

theorem Kph_zero (w : ℂ) (θ : Fin 40 → ℝ) : Kph w θ 0 = 1 - w • AC := by
  ext x y
  simp [Kph]

theorem K1ph_zero (w : ℂ) (θ : Fin 40 → ℝ) :
    K1ph w θ 0 = -w • ∑ l, (θ l : ℂ) • dA l := by
  ext x y
  simp only [K1ph, Matrix.of_apply, mul_zero, Complex.exp_zero, mul_one, Matrix.smul_apply,
    Matrix.sum_apply, dA, smul_eq_mul, phiC_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  have h := AC_mul_linkX l x y
  linear_combination (-w * I * (θ l : ℂ)) * h

theorem K2ph_zero (w : ℂ) (θ : Fin 40 → ℝ) :
    K2ph w θ 0 = -w • ∑ l, (θ l : ℂ) ^ 2 • d2A l := by
  ext x y
  simp only [K2ph, Matrix.of_apply, mul_zero, Complex.exp_zero, mul_one, Matrix.smul_apply,
    Matrix.sum_apply, d2A, smul_eq_mul, mul_pow, I_sq]
  rw [phiC_sq]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← linkX_sq]
  have h := AC_mul_linkX_sq l x y
  linear_combination (w * (θ l : ℂ) ^ 2) * h

theorem resolventW_eq_inv (w : ℂ) (hw : 1 - 5 * w ^ 2 ≠ 0) : (1 - w • AC)⁻¹ = resolventW w :=
  Matrix.inv_eq_right_inv (resolventW_spec w hw)

theorem det_Kph_zero (w : ℂ) (hw : 1 - 5 * w ^ 2 ≠ 0) (θ : Fin 40 → ℝ) : (Kph w θ 0).det ≠ 0 := by
  rw [Kph_zero]
  intro h
  have := congrArg Matrix.det (resolventW_spec w hw)
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem AC_transpose : ACᵀ = AC := by
  ext x y
  simp [AC, sadjZ_symm]

theorem resolventW_transpose (w : ℂ) : (resolventW w)ᵀ = resolventW w := by
  rw [resolventW, Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_smul, AC_transpose]

theorem dA_transpose (l : Fin 40) : (dA l)ᵀ = -dA l := by
  rw [dA, Matrix.transpose_smul, linkX, Matrix.transpose_sub, Matrix.transpose_single,
    Matrix.transpose_single, ← smul_neg, neg_sub]

/-- The trace of a symmetric matrix against an antisymmetric one vanishes. -/
theorem trace_symm_antisymm (M N : Matrix (Fin 16) (Fin 16) ℂ) (hM : Mᵀ = M) (hN : Nᵀ = -N) :
    (M * N).trace = 0 := by
  have h : (M * N).trace = -(M * N).trace := by
    calc (M * N).trace = ((M * N)ᵀ).trace := (Matrix.trace_transpose _).symm
      _ = (Nᵀ * Mᵀ).trace := by rw [Matrix.transpose_mul]
      _ = (-(N * M)).trace := by rw [hN, hM, Matrix.neg_mul]
      _ = -(M * N).trace := by rw [Matrix.trace_neg, Matrix.trace_mul_comm]
  have h2 : (2 : ℂ) * (M * N).trace = 0 := by linear_combination h
  simpa using h2

/-! ## The logarithmic derivative -/

/-- `h(t) = tr(K(t)⁻¹K′(t))`, the logarithmic derivative of `det K(t)`. -/
noncomputable def logDer (w : ℂ) (θ : Fin 40 → ℝ) (t : ℂ) : ℂ := ((Kph w θ t)⁻¹ * K1ph w θ t).trace

theorem logDeriv_zero (w : ℂ) (hw : 1 - 5 * w ^ 2 ≠ 0) (θ : Fin 40 → ℝ) : logDer w θ 0 = 0 := by
  rw [logDer, Kph_zero, K1ph_zero, resolventW_eq_inv w hw, Matrix.mul_smul, Matrix.trace_smul,
    Matrix.mul_sum, Matrix.trace_sum]
  have : ∀ l : Fin 40, (resolventW w * ((θ l : ℂ) • dA l)).trace = 0 := by
    intro l
    rw [Matrix.mul_smul, Matrix.trace_smul,
      trace_symm_antisymm _ _ (resolventW_transpose w) (dA_transpose l), smul_zero]
  rw [Finset.sum_eq_zero fun l _ => this l, smul_zero]

/-- The trace of a product with an inner sum. -/
theorem trace_entries (P Q : Matrix (Fin 16) (Fin 16) ℂ) :
    (P * Q).trace = ∑ i, ∑ j, P i j * Q j i := by
  simp [Matrix.trace, Matrix.mul_apply]

theorem trace_quad_expand (R : Matrix (Fin 16) (Fin 16) ℂ) (c : ℂ) (θ : Fin 40 → ℝ) :
    (R * (c • ∑ l, (θ l : ℂ) • dA l) * R * (c • ∑ l, (θ l : ℂ) • dA l)).trace =
      c ^ 2 * ∑ j, ∑ k, (θ j : ℂ) * (θ k : ℂ) * (R * dA j * R * dA k).trace := by
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_smul,
    Matrix.trace_sum, smul_eq_mul, Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [Matrix.mul_assoc]
  ring

theorem trace_lin_expand (R : Matrix (Fin 16) (Fin 16) ℂ) (c : ℂ) (θ : Fin 40 → ℝ) :
    (R * (c • ∑ l, (θ l : ℂ) ^ 2 • d2A l)).trace =
      c * ∑ j, (θ j : ℂ) ^ 2 * (R * d2A j).trace := by
  simp only [Matrix.mul_smul, Matrix.mul_sum, Matrix.trace_smul, Matrix.trace_sum, smul_eq_mul,
    Finset.mul_sum]

theorem hess_quad_expand (w : ℂ) (θ : Fin 40 → ℝ) :
    ∑ j, ∑ k, (θ j : ℂ) * (θ k : ℂ) * hessLaw w j k =
      -(w ^ 2 * ∑ j, ∑ k, (θ j : ℂ) * (θ k : ℂ) *
        (resolventW w * dA j * resolventW w * dA k).trace) -
      w * ∑ j, (θ j : ℂ) ^ 2 * (resolventW w * d2A j).trace := by
  simp only [hessLaw, mul_sub, mul_ite, mul_zero, Finset.sum_sub_distrib, Finset.sum_ite_eq,
    Finset.mem_univ, ↓reduceIte, Finset.mul_sum, mul_neg, Finset.sum_neg_distrib]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  · refine Finset.sum_congr rfl fun j _ => ?_
    ring

/-- **`h′(0) = −tr(RK′RK′) + tr(RK″) = Σ_{jk} θ_jθ_k H_{jk}(w) = −κ(w)‖Cθ‖²`.** -/
theorem hasDerivAt_logDeriv (w : ℂ) (hw : 1 - 5 * w ^ 2 ≠ 0) (θ : Fin 40 → ℝ) :
    HasDerivAt (logDer w θ) (-(2 * w ^ 4 / (1 - 5 * w ^ 2) ^ 2) * (plaqSq θ : ℂ)) 0 := by
  have hdet := det_Kph_zero w hw θ
  have hinv := hasDerivAt_inv_entry (Kph w θ) (K1ph w θ 0) 0 (Kph_deriv w θ 0) hdet
  have hsum : HasDerivAt (fun t => ∑ i, ∑ j, (Kph w θ t)⁻¹ i j * K1ph w θ t j i)
      (∑ i, ∑ j, (-((Kph w θ 0)⁻¹ * K1ph w θ 0 * (Kph w θ 0)⁻¹) i j * K1ph w θ 0 j i +
        (Kph w θ 0)⁻¹ i j * K2ph w θ 0 j i)) 0 :=
    HasDerivAt.fun_sum fun i _ => HasDerivAt.fun_sum fun j _ => (hinv i j).mul (K1ph_deriv w θ 0 j i)
  have hfun : logDer w θ = fun t => ∑ i, ∑ j, (Kph w θ t)⁻¹ i j * K1ph w θ t j i := by
    funext t
    rw [logDer, trace_entries]
  rw [hfun]
  convert hsum using 1
  -- the value: `−tr(RK′RK′) + tr(RK″)`
  have hval : (∑ i, ∑ j, (-((Kph w θ 0)⁻¹ * K1ph w θ 0 * (Kph w θ 0)⁻¹) i j * K1ph w θ 0 j i +
      (Kph w θ 0)⁻¹ i j * K2ph w θ 0 j i)) =
      -((Kph w θ 0)⁻¹ * K1ph w θ 0 * (Kph w θ 0)⁻¹ * K1ph w θ 0).trace +
        ((Kph w θ 0)⁻¹ * K2ph w θ 0).trace := by
    rw [trace_entries, trace_entries, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hval, Kph_zero, K1ph_zero, K2ph_zero, resolventW_eq_inv w hw]
  -- expand in the links and use the Hessian
  have hH : ∀ j k : Fin 40, hessLaw w j k = -(2 * w ^ 4 / (1 - 5 * w ^ 2) ^ 2) * (GZ j k : ℂ) :=
    fun j k => hessLaw_eq w hw j k
  have hquad : -(resolventW w * (-w • ∑ l, (θ l : ℂ) • dA l) * resolventW w *
        (-w • ∑ l, (θ l : ℂ) • dA l)).trace +
      (resolventW w * (-w • ∑ l, (θ l : ℂ) ^ 2 • d2A l)).trace =
      ∑ j, ∑ k, (θ j : ℂ) * (θ k : ℂ) * hessLaw w j k := by
    rw [trace_quad_expand, trace_lin_expand, hess_quad_expand]
    ring
  rw [hquad]
  simp only [hH]
  rw [plaqSq_eq]
  push_cast
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **The law in small phases, along every ray:** `g(t) = det(I − wA₋[e^{itθ}])` has `g(0) ≠ 0`,
`g′(0) = 0`, `g″(0) = −κ(w)‖Cθ‖² g(0)` with `κ(w) = 2w⁴/(1 − 5w²)²`, and `g(−t) = g(t)`; its logarithmic
derivative `h = g′/g` near `0` has `h(0) = 0` and `h′(0) = −κ(w)‖Cθ‖²`. -/
theorem law_small_phases (w : ℂ) (hw : 1 - 5 * w ^ 2 ≠ 0) (θ : Fin 40 → ℝ) :
    (Kph w θ 0).det ≠ 0 ∧
    (∀ᶠ t in 𝓝 0, HasDerivAt (fun s => (Kph w θ s).det) ((Kph w θ t).det * logDer w θ t) t) ∧
    logDer w θ 0 = 0 ∧
    HasDerivAt (logDer w θ) (-(2 * w ^ 4 / (1 - 5 * w ^ 2) ^ 2) * (plaqSq θ : ℂ)) 0 ∧
    HasDerivAt (fun s => (Kph w θ s).det) 0 0 ∧
    HasDerivAt (deriv (fun s => (Kph w θ s).det))
      (-(2 * w ^ 4 / (1 - 5 * w ^ 2) ^ 2) * (plaqSq θ : ℂ) * (Kph w θ 0).det) 0 ∧
    (∀ t, (Kph w θ (-t)).det = (Kph w θ t).det) := by
  have hdet := det_Kph_zero w hw θ
  have hdc : ContinuousAt (fun t => (Kph w θ t).det) 0 :=
    continuousAt_det_of_entries (Kph w θ) 0 fun a b => (Kph_deriv w θ 0 a b).continuousAt
  have hev : ∀ᶠ t in 𝓝 (0 : ℂ), (Kph w θ t).det ≠ 0 := hdc.eventually_ne hdet
  have hg : ∀ᶠ t in 𝓝 (0 : ℂ),
      HasDerivAt (fun s => (Kph w θ s).det) ((Kph w θ t).det * logDer w θ t) t := by
    filter_upwards [hev] with t ht
    have h := hasDerivAt_det (M := Kph w θ) (M' := K1ph w θ t) (x := t) (Kph_deriv w θ t)
    have hadj : (Kph w θ t).adjugate = (Kph w θ t).det • (Kph w θ t)⁻¹ := by
      rw [Matrix.inv_def, smul_smul, Ring.inverse_eq_inv', mul_inv_cancel₀ ht, one_smul]
    rw [hadj, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] at h
    exact h
  have h0 := logDeriv_zero w hw θ
  have hh := hasDerivAt_logDeriv w hw θ
  have hg0 : HasDerivAt (fun s => (Kph w θ s).det) 0 0 := by
    have := hg.self_of_nhds
    rw [h0, mul_zero] at this
    exact this
  refine ⟨hdet, hg, h0, hh, hg0, ?_, fun t => ?_⟩
  · have heq : deriv (fun s => (Kph w θ s).det) =ᶠ[𝓝 0] fun t => (Kph w θ t).det * logDer w θ t :=
      hg.mono fun t ht => ht.deriv
    have hprod := hg0.mul hh
    rw [h0, mul_zero, zero_add] at hprod
    exact (hprod.congr_of_eventuallyEq heq).congr_deriv (by ring)
  · have htr : Kph w θ (-t) = (Kph w θ t)ᵀ := by
      ext x y
      simp only [Kph, Matrix.of_apply, Matrix.transpose_apply, Matrix.one_apply]
      have hA : AC y x = AC x y := by simp [AC, sadjZ_symm]
      have hP : phiC θ y x = -phiC θ x y := by
        rw [phiC_apply, phiC_apply, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [linkX_antisymm]
        ring
      rw [hA, hP]
      by_cases hxy : x = y
      · subst hxy; simp
      · simp only [hxy, Ne.symm hxy, if_false]
        ring_nf
    rw [htr, Matrix.det_transpose]

end Law

open Comparison.System.Law

/-- **Proposition 62 on the sixteen vertices, the law in small phases** (along every ray; the uniform remainder in `θ` is on the work
list). `U(1)` phases `θ` on the forty links, `Cθ` their sums around the forty squares: `C·grad = 0` and
`rank C = 25`; for every complex `w` with `1 − 5w² ≠ 0` and every direction `θ`, `g(t) = det(I − wA₋[e^{itθ}])`
has `g(0) ≠ 0`, `g′(0) = 0`, `g″(0) = −κ(w)‖Cθ‖² g(0)` and is even: the second variation of
`log det(I − wA₋[e^{iθ}])` is `−κ(w)CᵀC`, `κ(w) = 2w⁴/(1 − 5w²)²`, and the Hessian matrix is `−κ(w)CᵀC`
entry by entry (`hessLaw_eq`); with `w = u/(1 + 4u²)` at `u = 1/4`, `w = 1/5` and `κ = 1/200`.
Recognition: Maxwell's action in Wilson's form; with the kept rotations of a division in place of the phase it is
the Yang–Mills action. -/
theorem Law.prop_62_sixteen :
    (∀ (φ : Fin 16 → ℝ) (q : Fin 40), circ (fun l => φ (linkV l) - φ (linkU l)) q = 0) ∧
    cReal.rank = 25 ∧
    (∀ (w : ℂ), 1 - 5 * w ^ 2 ≠ 0 → ∀ θ : Fin 40 → ℝ,
      (Kph w θ 0).det ≠ 0 ∧
      HasDerivAt (fun s => (Kph w θ s).det) 0 0 ∧
      HasDerivAt (deriv (fun s => (Kph w θ s).det))
        (-(2 * w ^ 4 / (1 - 5 * w ^ 2) ^ 2) * (plaqSq θ : ℂ) * (Kph w θ 0).det) 0 ∧
      logDer w θ 0 = 0 ∧
      HasDerivAt (logDer w θ) (-(2 * w ^ 4 / (1 - 5 * w ^ 2) ^ 2) * (plaqSq θ : ℂ)) 0 ∧
      (∀ t, (Kph w θ (-t)).det = (Kph w θ t).det)) ∧
    (∀ (w : ℂ), 1 - 5 * w ^ 2 ≠ 0 → ∀ j k : Fin 40,
      hessLaw w j k = -(2 * w ^ 4 / (1 - 5 * w ^ 2) ^ 2) * (GZ j k : ℂ)) ∧
    (1 / 4 : ℂ) / (1 + 4 * (1 / 4) ^ 2) = 1 / 5 ∧
    2 * (1 / 5 : ℂ) ^ 4 / (1 - 5 * (1 / 5) ^ 2) ^ 2 = 1 / 200 := by
  refine ⟨circ_grad, rank_cReal, fun w hw θ => ?_, fun w hw j k => hessLaw_eq w hw j k,
    kappa_quarters.1, kappa_quarters.2.2.2.2.1⟩
  obtain ⟨h1, -, h3, h4, h5, h6, h7⟩ := law_small_phases w hw θ
  exact ⟨h1, h5, h6, h3, h4, h7⟩


/-- **Equation (27), the law in small phases** (along every ray; the uniform remainder in `θ` completes it):
`det(I − wA₋[e^{itθ}])` has the derivative `0` and the second derivative `−κ(w)‖Cθ‖² det(I − wA₋)` at `t = 0` and is
even in `t`; `rank C = 25`, `spec CᵀC = 0¹⁵ ⊕ 4¹⁰ ⊕ 8¹⁵`; `κ = 1/200` at `w = ±1/5` and `1/98` at `w = ±i/3`. -/
theorem eq_27 :
    (∀ (w : ℂ), 1 - 5 * w ^ 2 ≠ 0 → ∀ θ : Fin 40 → ℝ,
      HasDerivAt (fun s => (Kph w θ s).det) 0 0 ∧
      HasDerivAt (deriv (fun s => (Kph w θ s).det))
        (-(2 * w ^ 4 / (1 - 5 * w ^ 2) ^ 2) * (plaqSq θ : ℂ) * (Kph w θ 0).det) 0 ∧
      (∀ t, (Kph w θ (-t)).det = (Kph w θ t).det)) ∧
    cReal.rank = 25 ∧
    (cRealᵀ * cReal).charpoly =
      Polynomial.X ^ 15 * (Polynomial.X - Polynomial.C (4 : ℝ)) ^ 10 *
        (Polynomial.X - Polynomial.C (8 : ℝ)) ^ 15 ∧
    (2 * (1 / 5 : ℂ) ^ 4 / (1 - 5 * (1 / 5) ^ 2) ^ 2 = 1 / 200 ∧
      2 * (-1 / 5 : ℂ) ^ 4 / (1 - 5 * (-1 / 5) ^ 2) ^ 2 = 1 / 200 ∧
      2 * (I / 3) ^ 4 / (1 - 5 * (I / 3) ^ 2) ^ 2 = 1 / 98 ∧
      2 * (-I / 3) ^ 4 / (1 - 5 * (-I / 3) ^ 2) ^ 2 = 1 / 98) := by
  refine ⟨fun w hw θ => ?_, rank_cReal, cReal_gram_charpoly, ?_⟩
  · obtain ⟨-, -, -, -, h5, h6, h7⟩ := law_small_phases w hw θ
    exact ⟨h5, h6, h7⟩
  · obtain ⟨-, -, -, -, h1, h2, h3, h4⟩ := kappa_quarters
    exact ⟨h1, h2, h3, h4⟩

end Comparison.System
