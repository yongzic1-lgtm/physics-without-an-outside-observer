module

public import Comparison.Mass.Harmonic
public import Comparison.Colour.GramTerm

/-!
# The road to the masses: the critical zero is simple, and its residue (Proposition 57)

Over `ℝ`, `D₊(u) = det(1 − uB)` on the eighty
states. The zero of the law at `u = 1/4` is simple as a theorem about the finite operator, not as a
hypothesis: the kernels are one-dimensional (`Harmonic.lean`) and the derivative of the
determinant at the zero is `D₊'(1/4) = −96 (15/16)²⁴ ≠ 0`.

* `det_law_real`: **`det(1 − uB) = (1 − u²)²⁴(1 − u)(1 − 4u)(1 − u + 4u²)¹⁰(1 + 3u + 4u²)⁵`** for
  real `u`.
* `law_deriv_quarter`: **`D₊'(1/4) = −96 (15/16)²⁴`**.
* `adj_law_quarter`: **`adj(1 − B/4) = κ 𝟏𝟏ᵀ`** with `κ = 3(15/16)²⁴/10 ≠ 0` (`kappa_law`):
  Jacobi's formula gives `D₊'(1/4) = −κ 𝟏ᵀB𝟏 = −320 κ`.
* `adj_watched`: **`adj(1 − W) = κ 𝟏𝟏ᵀ`** on the seventy-four with the same `κ ≠ 0`: the available transitions
  determinant `det(1 − uB_AA − u²B_AD B_DA − u³B_AD B_DD B_DA)` is `D₊(u)` (Proposition 77), and
  its derivative at `1/4` is `−κ (276 + 2·64/4 + 3·64/16) = −320 κ`: the three types of available-transition steps
  of one stationary cycle add to `320`.
* `residue_law`: **Proposition 57 at the law's zero:** `(u − 1/4)(1 − uB)⁻¹ → −𝟏𝟏ᵀ/320` as
  `u → 1/4`, that is `Res = r ℓᵀ/(ℓ · K' r)` with `r = ℓ = 𝟏` and `K' = −B`; `residue_general`: the
  same limit `adj K(u₀)/D'(u₀)` for any continuous family with a simple zero of its determinant.
-/

@[expose] public section

namespace Comparison

open Matrix Filter Topology

/-! ## The law over `ℝ` -/

/-- The polynomial `D₊`. -/
noncomputable def Dplus (u : ℝ) : ℝ :=
  (1 - u ^ 2) ^ 24 * (1 - u) * (1 - 4 * u) * (1 - u + 4 * u ^ 2) ^ 10 * (1 + 3 * u + 4 * u ^ 2) ^ 5

theorem stepR_map : (stepR).map (fun a : ℝ => (a : ℂ)) = stepT (fun _ _ => (1 : ℂ)) := by
  ext i j
  simp only [stepR, stepT, Matrix.map_apply, Matrix.of_apply]
  split_ifs <;> simp

/-- **`det(1 − uB) = D₊(u)` for real `u`.** -/
theorem det_law_real (u : ℝ) : (1 - u • stepR).det = Dplus u := by
  apply Complex.ofReal_injective
  have hmap : ((1 : Matrix State State ℝ) - u • stepR).map (fun a : ℝ => (a : ℂ)) =
      1 - (u : ℂ) • stepOp transitionMat := by
    rw [← stepT_one_eq, ← stepR_map]
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
      smul_eq_mul]
    split_ifs <;> push_cast <;> ring
  have h1 : ((1 - u • stepR).det : ℂ) =
      (((1 : Matrix State State ℝ) - u • stepR).map (fun a : ℝ => (a : ℂ))).det := by
    rw [← Complex.ofRealHom_eq_coe, RingHom.map_det]
    rfl
  rw [h1, hmap, D_plus, Dplus]
  push_cast
  ring

theorem Dplus_hasDerivAt : HasDerivAt Dplus (-96 * (15 / 16 : ℝ) ^ 24) (1 / 4) := by
  set G : ℝ → ℝ := fun u => (1 - u ^ 2) ^ 24 * (1 - u) * (1 - u + 4 * u ^ 2) ^ 10 *
    (1 + 3 * u + 4 * u ^ 2) ^ 5 with hG
  have hD : Dplus = fun u => (1 - 4 * u) * G u := by
    funext u
    simp only [Dplus, hG]
    ring
  have hGd : DifferentiableAt ℝ G (1 / 4) := by
    simp only [hG]
    fun_prop
  have h1 : HasDerivAt (fun u : ℝ => 1 - 4 * u) (-4) (1 / 4) := by
    simpa using ((hasDerivAt_id (1 / 4 : ℝ)).const_mul 4).const_sub 1
  have h := h1.mul hGd.hasDerivAt
  rw [hD]
  convert h using 1
  simp only [hG]
  norm_num

/-- **`D₊'(1/4) = −96 (15/16)²⁴`**, for the determinant of the law itself. -/
theorem law_deriv_quarter :
    HasDerivAt (fun u : ℝ => (1 - u • stepR).det) (-96 * (15 / 16 : ℝ) ^ 24) (1 / 4) := by
  have e : (fun u : ℝ => (1 - u • stepR).det) = Dplus := funext det_law_real
  rw [e]
  exact Dplus_hasDerivAt

/-! ## Jacobi's formula for the affine families -/

theorem hasDerivAt_det_one_sub {ι : Type*} [Fintype ι] [DecidableEq ι] (B : Matrix ι ι ℝ)
    (u : ℝ) : HasDerivAt (fun v : ℝ => (1 - v • B).det) ((1 - u • B).adjugate * (-B)).trace u := by
  apply hasDerivAt_det
  intro i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply]
  simpa using ((hasDerivAt_id u).mul_const (B i j)).const_sub ((1 : Matrix ι ι ℝ) i j)

/-! ## The adjugate at the critical zero -/

theorem stepR_mulVec_one : stepR *ᵥ (1 : State → ℝ) = (4 : ℝ) • 1 := by
  funext s'
  rw [stepR_mulVec]
  simp [card_predSet]

theorem one_vecMul_stepR : (1 : State → ℝ) ᵥ* stepR = (4 : ℝ) • 1 := by
  funext s
  rw [stepR_vecMul]
  simp [card_succSet]

theorem law_quarter_mulVec (v : State → ℝ) :
    (1 - (1 / 4 : ℝ) • stepR) *ᵥ v = 0 ↔ stepR *ᵥ v = (4 : ℝ) • v := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  constructor
  · intro h
    funext i
    have := congrFun h i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
    linarith
  · intro h
    funext i
    have := congrFun h i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
    linarith

theorem law_quarter_vecMul (w : State → ℝ) :
    w ᵥ* (1 - (1 / 4 : ℝ) • stepR) = 0 ↔ w ᵥ* stepR = (4 : ℝ) • w := by
  rw [Matrix.vecMul_sub, Matrix.vecMul_one, Matrix.vecMul_smul]
  constructor
  · intro h
    funext i
    have := congrFun h i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
    linarith
  · intro h
    funext i
    have := congrFun h i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this ⊢
    linarith

theorem det_law_quarter : (1 - (1 / 4 : ℝ) • stepR).det = 0 := by
  rw [det_law_real, Dplus]
  norm_num

/-- The adjugate of `1 − B/4` is a multiple of `𝟏𝟏ᵀ`. -/
theorem adj_law_quarter_exists :
    ∃ κ : ℝ, (1 - (1 / 4 : ℝ) • stepR).adjugate = κ • vecMulVec (1 : State → ℝ) 1 := by
  refine adjugate_rank_one _ 1 1 (by
    intro h
    have := congrFun h ((0 : Fin 16), (0 : Fin 5))
    simp at this) det_law_quarter ?_ ?_
  · intro v hv
    exact kernel_right v ((law_quarter_mulVec v).mp hv)
  · intro w hw
    exact kernel_left w ((law_quarter_vecMul w).mp hw)

theorem one_dot_stepR_one : (1 : State → ℝ) ⬝ᵥ (stepR *ᵥ 1) = 320 := by
  rw [stepR_mulVec_one, dotProduct_smul]
  simp [dotProduct, card_state]
  norm_num

/-- The constant `κ = 3(15/16)²⁴/10`. -/
noncomputable def kappaLaw : ℝ := 3 * (15 / 16 : ℝ) ^ 24 / 10

/-- **`adj(1 − B/4) = κ 𝟏𝟏ᵀ` with `κ = 3(15/16)²⁴/10`:** Jacobi's formula at the zero gives
`D₊'(1/4) = tr(κ𝟏𝟏ᵀ(−B)) = −320 κ`. -/
theorem adj_law_quarter :
    (1 - (1 / 4 : ℝ) • stepR).adjugate = kappaLaw • vecMulVec (1 : State → ℝ) 1 := by
  obtain ⟨κ, hκ⟩ := adj_law_quarter_exists
  have hJ := hasDerivAt_det_one_sub stepR (1 / 4)
  rw [hκ, trace_smul_vecMulVec_mul, Matrix.neg_mulVec, dotProduct_neg, one_dot_stepR_one] at hJ
  have := hJ.unique law_deriv_quarter
  have hk : κ = kappaLaw := by
    rw [kappaLaw]
    linarith
  rw [hκ, hk]

theorem kappaLaw_pos : 0 < kappaLaw := by
  rw [kappaLaw]
  positivity

/-! ## The available transitions operator at the critical zero -/

section Watched

variable (h : Fin 5)

/-- The available transitions determinant `det(1 − uB_AA − u²B_AD B_DA − u³B_AD B_DD B_DA)` over `ℝ`. -/
noncomputable def availableTransitionsOp (u : ℝ) : Matrix {s // InAvailableTransitions h s} {s // InAvailableTransitions h s} ℝ :=
  1 - u • bAA h - u ^ 2 • (bAD h * bDA h) - u ^ 3 • (bAD h * bDD h * bDA h)

theorem det_availableTransitionsOp (u : ℝ) : (availableTransitionsOp h u).det = Dplus u := by
  rw [← det_law_real, availableTransitionsOp]
  exact (det_availableTransitions h (fun _ _ => (1 : ℝ)) u).symm

theorem availableTransitionsOp_quarter : availableTransitionsOp h (1 / 4) = 1 - watchedR h := by
  rw [availableTransitionsOp, watchedR]
  norm_num
  abel

/-- The derivative of the available transitions operator in `u`. -/
noncomputable def availableTransitionsOp' (u : ℝ) : Matrix {s // InAvailableTransitions h s} {s // InAvailableTransitions h s} ℝ :=
  -(bAA h) - (2 * u) • (bAD h * bDA h) - (3 * u ^ 2) • (bAD h * bDD h * bDA h)

theorem availableTransitionsOp_hasDerivAt (u : ℝ) :
    HasDerivAt (fun v => (availableTransitionsOp h v).det) ((availableTransitionsOp h u).adjugate * availableTransitionsOp' h u).trace u := by
  apply hasDerivAt_det
  intro i j
  have h1 := (hasDerivAt_id u).mul_const (bAA h i j)
  have h2 := (hasDerivAt_pow 2 u).mul_const ((bAD h * bDA h) i j)
  have h3 := (hasDerivAt_pow 3 u).mul_const ((bAD h * bDD h * bDA h) i j)
  have h4 := ((h1.const_sub ((1 : Matrix {s // InAvailableTransitions h s} {s // InAvailableTransitions h s} ℝ) i j)).sub
    h2).sub h3
  refine (h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => ?_)).congr_deriv ?_
  · simp only [availableTransitionsOp, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Pi.sub_apply, id_eq]
  · simp only [availableTransitionsOp', Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply]
    push_cast
    ring

theorem watched_kernel_right' (v : {s // InAvailableTransitions h s} → ℝ) (hv : (1 - watchedR h) *ᵥ v = 0) :
    ∃ c : ℝ, v = c • (1 : {s // InAvailableTransitions h s} → ℝ) := by
  apply watched_kernel_right h v
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
  exact hv.symm

theorem watched_kernel_left' (v : {s // InAvailableTransitions h s} → ℝ) (hv : v ᵥ* (1 - watchedR h) = 0) :
    ∃ c : ℝ, v = c • (1 : {s // InAvailableTransitions h s} → ℝ) := by
  apply watched_kernel_left h v
  rw [Matrix.vecMul_sub, Matrix.vecMul_one, sub_eq_zero] at hv
  exact hv.symm

theorem det_one_sub_watched : (1 - watchedR h).det = 0 := by
  rw [← availableTransitionsOp_quarter, det_availableTransitionsOp, Dplus]
  norm_num

theorem adj_watched_exists :
    ∃ κ : ℝ, (1 - watchedR h).adjugate = κ • vecMulVec (1 : {s // InAvailableTransitions h s} → ℝ) 1 := by
  have hne : (1 : {s // InAvailableTransitions h s} → ℝ) ≠ 0 := by
    have hs : InAvailableTransitions h (transition (if h = 0 then 1 else 0) 0, (if h = 0 then 1 else 0)) := by
      revert h
      decide
    intro hz
    have := congrFun hz ⟨_, hs⟩
    simp at this
  exact adjugate_rank_one _ 1 1 hne (det_one_sub_watched h) (watched_kernel_right' h)
    (watched_kernel_left' h)

end Watched

/-! ## The residue at the critical zero (Proposition 57) -/

/-- **The residue at a simple zero of a determinant:** if `K` is continuous at `u₀`,
`det K(u₀) = 0` and `det K` has the derivative `d ≠ 0` at `u₀`, then
`(u − u₀) K(u)⁻¹ → adj K(u₀)/d`. -/
theorem residue_general {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ℝ → Matrix ι ι ℝ)
    (u₀ d : ℝ) (hK : ContinuousAt K u₀) (h0 : (K u₀).det = 0)
    (hd : HasDerivAt (fun u => (K u).det) d u₀) (hd0 : d ≠ 0) :
    Tendsto (fun u => (u - u₀) • (K u)⁻¹) (𝓝[≠] u₀) (𝓝 (d⁻¹ • (K u₀).adjugate)) := by
  have hslope := hd.tendsto_slope
  have hadj : Tendsto (fun u => (K u).adjugate) (𝓝[≠] u₀) (𝓝 (K u₀).adjugate) := by
    have hc : ContinuousAt (fun u => (K u).adjugate) u₀ := by
      have := (continuous_id.matrix_adjugate (n := ι) (R := ℝ)).continuousAt (x := K u₀)
      exact this.comp hK
    exact hc.tendsto.mono_left nhdsWithin_le_nhds
  have hinv : Tendsto (fun u => (slope (fun u => (K u).det) u₀ u)⁻¹) (𝓝[≠] u₀) (𝓝 d⁻¹) :=
    hslope.inv₀ hd0
  have hprod := hinv.smul hadj
  refine hprod.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu' : u - u₀ ≠ 0 := sub_ne_zero.mpr hu
  rw [slope_def_field, h0, sub_zero, inv_div, Matrix.inv_def, smul_smul, Ring.inverse_eq_inv',
    div_eq_mul_inv]

/-- **Proposition 57 at the law's zero:** `(u − 1/4)(1 − uB)⁻¹ → −𝟏𝟏ᵀ/320` as `u → 1/4`; with
`r = ℓ = 𝟏` and `K' = −B` this is `r ℓᵀ/(ℓ · K' r)`. -/
theorem residue_law :
    Tendsto (fun u : ℝ => (u - 1 / 4) • (1 - u • stepR)⁻¹) (𝓝[≠] (1 / 4))
      (𝓝 ((-(1 / 320 : ℝ)) • vecMulVec (1 : State → ℝ) (1 : State → ℝ))) := by
  have hK : ContinuousAt (fun u : ℝ => 1 - u • stepR) (1 / 4) := by
    fun_prop
  have h := residue_general (fun u : ℝ => 1 - u • stepR) (1 / 4) (-96 * (15 / 16 : ℝ) ^ 24) hK
    det_law_quarter law_deriv_quarter (by norm_num)
  rw [adj_law_quarter, smul_smul, kappaLaw] at h
  convert h using 2
  field_simp
  norm_num

/-- The residue in the book's form: `rℓᵀ/(ℓ · K' r)` with `r = ℓ = 𝟏`, `K' = −B`. -/
theorem residue_law_form :
    (-(1 / 320 : ℝ)) • vecMulVec (1 : State → ℝ) (1 : State → ℝ) =
      ((1 : State → ℝ) ⬝ᵥ ((-stepR) *ᵥ (1 : State → ℝ)))⁻¹ •
        vecMulVec (1 : State → ℝ) (1 : State → ℝ) := by
  rw [Matrix.neg_mulVec, dotProduct_neg, one_dot_stepR_one]
  norm_num

end Comparison

end
