module

public import Comparison.Mass.Velocity

/-!
# The road to the masses: a mass is the angle of the long-range zero (the page of pointing)

The page of pointing reads a mass as the
angle of the law's long-range zero on `|u| = 1/4` when the steps carry phases. This file makes that
reading a theorem for the phases the books use, and tests the rows against it.

**A uniform phase.** `uniform_phase_zero`: with the phase `e^{−iμ}` on every step,
`det(1 − u e^{−iμ} B) = D₊(u e^{−iμ})`, which vanishes at `u = e^{iμ}/4`; `D_plus_disc`: on the
closed disc `|v| ≤ 1/4`, `D₊(v) = 0` only at `v = 1/4`, so **`e^{iμ}/4` is the only zero of the law
with `|u| ≤ 1/4`: its angle is `μ`**.

**A phase on the steps, in general.** For a stochastic `P` with one-dimensional kernels and a simple
root (`tilt_weighted`: the tilt `P ∘ e^{sX}` is then a weighted walk) and any real weight `X`:
* `angle_of_zero`: the eigenvalue `ψ(s)` of `P ∘ e^{sX}` through `ψ(0) = 1` exists for complex `s`
  near `0` (the implicit function theorem over `ℂ` on `det(λ − P ∘ e^{sX})`, whose `λ`-derivative
  at `(0, 1)` is `κ ≠ 0`), `ψ'(0) = v = π (P ∘ X) 𝟏`, and **with the phase `e^{−iθX}`
  (`s = −iθ`) the angle of `ψ` turns at the rate `−v` at `θ = 0`**: the long-range zero
  `u = 1/(4ψ)` turns at the rate `v` per unit `θ`.
* `real_weight_real_root`: with a real weight (`s` real) the largest eigenvalue is real and
  positive, so the zero does not turn: **a transmission moves the zero only radially**.

**The available transitions numerator as an angle.** `availableTransitionsLawX h X`: the weight `X(target)` on the steps out of
the available transitions of `h` (the transitions), zero on the twenty-four hidden steps, on the eighty states:
* `availableTransitions_angle_rate`: **for `X = L(Ω) + [along h]` the zero turns at `1836/320` per unit `θ` per
  step**, and `one_transition_angle_rate`: **for the weight `1` on one transition it turns at `1/320`**;
  `proton_availableTransitions_ratio`: **the ratio of the two rates is `1836 = 6M + C_h`**.
-/

@[expose] public section

namespace Comparison

open Matrix Filter Topology Asymptotics Complex

section Tilt

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real tilt `P ∘ e^{sX}`. -/
noncomputable def tiltR (P X : Matrix ι ι ℝ) (s : ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => P i j * Real.exp (s * X i j)

/-- The Hadamard power `P ∘ Xᵏ`. -/
def hadPow (P X : Matrix ι ι ℝ) (k : ℕ) : Matrix ι ι ℝ := Matrix.of fun i j => P i j * X i j ^ k

/-- **A tilt of a stochastic walk with one-dimensional kernels and a simple root is a weighted
walk.** -/
theorem tilt_weighted (P X : Matrix ι ι ℝ) (π : ι → ℝ) (hP : ∀ i j, 0 ≤ P i j)
    (row : P *ᵥ 1 = 1) (stat : π ᵥ* P = π) (pos : ∀ i, 0 < π i) (total : ∑ i, π i = 1)
    (kerR : ∀ v, P *ᵥ v = v → ∃ c : ℝ, v = c • (1 : ι → ℝ))
    (kerL : ∀ w, w ᵥ* P = w → ∃ c : ℝ, w = c • π) (adj : (1 - P).adjugate ≠ 0) :
    WeightedWalk (tiltR P X) P (hadPow P X 1) (hadPow P X 2) π where
  nonneg := fun s i j => by
    simp only [tiltR, Matrix.of_apply]
    exact mul_nonneg (hP i j) (Real.exp_pos _).le
  taylor := by
    intro i j
    have := (exp_taylor2 (X i j)).const_mul_left (P i j)
    refine this.congr' (Filter.Eventually.of_forall fun s => ?_) EventuallyEq.rfl
    simp only [tiltR, hadPow, Matrix.of_apply, pow_one]
    ring
  row := row
  stat := stat
  pos := pos
  total := total
  kerR := kerR
  kerL := kerL
  adj := adj

/-- The complex tilt `P ∘ e^{sX}`, `s ∈ ℂ`. -/
noncomputable def tiltC (P X : Matrix ι ι ℝ) (s : ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => (P i j : ℂ) * Complex.exp (s * X i j)

/-- Its derivative in `s`. -/
noncomputable def tiltC' (P X : Matrix ι ι ℝ) (s : ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => (P i j : ℂ) * X i j * Complex.exp (s * X i j)

/-- The characteristic function `det(λ − P ∘ e^{sX})`. -/
noncomputable def charF (P X : Matrix ι ι ℝ) (s l : ℂ) : ℂ :=
  (l • (1 : Matrix ι ι ℂ) - tiltC P X s).det

/-- Its `s`-derivative, by Jacobi's formula. -/
noncomputable def charFs (P X : Matrix ι ι ℝ) (s l : ℂ) : ℂ :=
  ((l • (1 : Matrix ι ι ℂ) - tiltC P X s).adjugate * (-(tiltC' P X s))).trace

/-- Its `λ`-derivative, by Jacobi's formula. -/
noncomputable def charFl (P X : Matrix ι ι ℝ) (s l : ℂ) : ℂ :=
  ((l • (1 : Matrix ι ι ℂ) - tiltC P X s).adjugate * 1).trace

theorem charF_hasDerivAt_s (P X : Matrix ι ι ℝ) (s l : ℂ) :
    HasDerivAt (fun s => charF P X s l) (charFs P X s l) s := by
  apply hasDerivAt_det
  intro i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, tiltC, tiltC', Matrix.of_apply,
    Matrix.neg_apply]
  have h0 : HasDerivAt (fun y : ℂ => y * (X i j : ℂ)) (X i j : ℂ) s := hasDerivAt_mul_const _
  have h2 := (h0.cexp.const_mul (P i j : ℂ)).const_sub (l * (1 : Matrix ι ι ℂ) i j)
  convert h2 using 1
  ring

theorem charF_hasDerivAt_l (P X : Matrix ι ι ℝ) (s l : ℂ) :
    HasDerivAt (fun l => charF P X s l) (charFl P X s l) l := by
  apply hasDerivAt_det
  intro i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  simpa using ((hasDerivAt_id l).mul_const ((1 : Matrix ι ι ℂ) i j)).sub_const (tiltC P X s i j)

theorem tiltC_continuous (P X : Matrix ι ι ℝ) : Continuous (tiltC P X) := by
  apply continuous_matrix
  intro i j
  simp only [tiltC, Matrix.of_apply]
  fun_prop

theorem tiltC'_continuous (P X : Matrix ι ι ℝ) : Continuous (tiltC' P X) := by
  apply continuous_matrix
  intro i j
  simp only [tiltC', Matrix.of_apply]
  fun_prop

theorem charM_continuous (P X : Matrix ι ι ℝ) :
    Continuous (fun p : ℂ × ℂ => (p.2 • (1 : Matrix ι ι ℂ) - tiltC P X p.1).adjugate) := by
  apply Continuous.matrix_adjugate
  exact (continuous_snd.smul continuous_const).sub ((tiltC_continuous P X).comp continuous_fst)

theorem charFs_continuous (P X : Matrix ι ι ℝ) : Continuous (fun p : ℂ × ℂ => charFs P X p.1 p.2) :=
  ((charM_continuous P X).mul ((tiltC'_continuous P X).comp continuous_fst).neg).matrix_trace

theorem charFl_continuous (P X : Matrix ι ι ℝ) : Continuous (fun p : ℂ × ℂ => charFl P X p.1 p.2) :=
  ((charM_continuous P X).mul continuous_const).matrix_trace

theorem tiltC_zero (P X : Matrix ι ι ℝ) :
    (1 : ℂ) • (1 : Matrix ι ι ℂ) - tiltC P X 0 = (1 - P).map (fun a : ℝ => (a : ℂ)) := by
  ext i j
  simp only [tiltC, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.map_apply,
    zero_mul, Complex.exp_zero, mul_one, smul_eq_mul, one_mul, Matrix.one_apply]
  split_ifs <;> push_cast <;> ring

theorem adj_map_real (M : Matrix ι ι ℝ) :
    (M.map (fun a : ℝ => (a : ℂ))).adjugate = M.adjugate.map (fun a : ℝ => (a : ℂ)) :=
  (RingHom.map_adjugate Complex.ofRealHom M).symm

/-- **The angle of the long-range zero under a phase on the steps.** -/
theorem angle_of_zero (P X : Matrix ι ι ℝ) (π : ι → ℝ)
    (hW : WeightedWalk (tiltR P X) P (hadPow P X 1) (hadPow P X 2) π) :
    ∃ ψ : ℂ → ℂ, ψ 0 = 1 ∧ (∀ᶠ s in 𝓝 0, charF P X s (ψ s) = 0) ∧
      HasDerivAt ψ ((π ⬝ᵥ (hadPow P X 1 *ᵥ 1) : ℝ) : ℂ) 0 ∧
      HasDerivAt (fun θ : ℝ => Complex.arg (ψ (-I * θ))) (-(π ⬝ᵥ (hadPow P X 1 *ᵥ 1))) 0 := by
  obtain ⟨κ, hκ0, hκ⟩ := hW.adj_rank_one
  set v := π ⬝ᵥ (hadPow P X 1 *ᵥ 1) with hv
  -- the derivatives at `(0, 1)`
  have hadj0 : ((1 : ℂ) • (1 : Matrix ι ι ℂ) - tiltC P X 0).adjugate =
      (κ • vecMulVec (1 : ι → ℝ) π).map (fun a : ℝ => (a : ℂ)) := by
    rw [tiltC_zero, adj_map_real, hκ]
  have hFl : charFl P X 0 1 = (κ : ℂ) := by
    simp only [charFl, hadj0, Matrix.mul_one, Matrix.trace, Matrix.diag, Matrix.map_apply,
      Matrix.smul_apply, vecMulVec_apply, Pi.one_apply, one_mul, smul_eq_mul]
    push_cast
    rw [← Finset.mul_sum, ← Complex.ofReal_sum, hW.total]
    simp
  have hFs : charFs P X 0 1 = -((κ * v : ℝ) : ℂ) := by
    have hsum : charFs P X 0 1 =
        ∑ i, ∑ k, ((κ * π k : ℝ) : ℂ) * (-((P k i * X k i : ℝ) : ℂ)) := by
      simp only [charFs, hadj0, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply,
        Matrix.smul_apply, vecMulVec_apply, Pi.one_apply, one_mul, smul_eq_mul, Matrix.neg_apply,
        tiltC', Matrix.of_apply, zero_mul, Complex.exp_zero, mul_one]
      push_cast
      rfl
    rw [hsum]
    have hv' : v = ∑ k, π k * ∑ i, P k i * X k i := by
      simp only [hv, dotProduct, Matrix.mulVec, hadPow, Matrix.of_apply, pow_one, Pi.one_apply,
        mul_one]
    rw [hv', Finset.sum_comm]
    push_cast
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  -- the implicit function theorem over `ℂ`
  have df₁ : ∀ᶠ w in 𝓝 ((0 : ℂ), (1 : ℂ)), HasFDerivAt (charF P X · w.2)
      ((fun s l => ContinuousLinearMap.toSpanSingleton ℂ (charFs P X s l)) w.1 w.2) w.1 :=
    Filter.Eventually.of_forall fun w => (charF_hasDerivAt_s P X w.1 w.2).hasFDerivAt
  have df₂ : ∀ᶠ w in 𝓝 ((0 : ℂ), (1 : ℂ)), HasFDerivAt (charF P X w.1 ·)
      ((fun s l => ContinuousLinearMap.toSpanSingleton ℂ (charFl P X s l)) w.1 w.2) w.2 :=
    Filter.Eventually.of_forall fun w => (charF_hasDerivAt_l P X w.1 w.2).hasFDerivAt
  have cf₁ : ContinuousAt
      (Function.uncurry fun s l => ContinuousLinearMap.toSpanSingleton ℂ (charFs P X s l))
      ((0 : ℂ), (1 : ℂ)) :=
    ((ContinuousLinearMap.toSpanSingletonLIE ℂ ℂ).continuous.comp
      (charFs_continuous P X)).continuousAt
  have cf₂ : ContinuousAt
      (Function.uncurry fun s l => ContinuousLinearMap.toSpanSingleton ℂ (charFl P X s l))
      ((0 : ℂ), (1 : ℂ)) :=
    ((ContinuousLinearMap.toSpanSingletonLIE ℂ ℂ).continuous.comp
      (charFl_continuous P X)).continuousAt
  have hκC : (κ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hκ0
  have if₂u : ((fun s l => ContinuousLinearMap.toSpanSingleton ℂ (charFl P X s l))
      ((0 : ℂ), (1 : ℂ)).1 ((0 : ℂ), (1 : ℂ)).2).IsInvertible := by
    refine ContinuousLinearMap.IsInvertible.of_inverse
      (g := ContinuousLinearMap.toSpanSingleton ℂ (κ : ℂ)⁻¹) ?_ ?_
    · ext
      simp [hFl, hκC]
    · ext
      simp [hFl, hκC]
  set ψ := implicitFunctionOfBivariate (u := ((0 : ℂ), (1 : ℂ))) (f := charF P X)
    (f₁ := fun s l => ContinuousLinearMap.toSpanSingleton ℂ (charFs P X s l))
    (f₂ := fun s l => ContinuousLinearMap.toSpanSingleton ℂ (charFl P X s l))
    df₁ df₂ cf₁ cf₂ if₂u with hψ
  have hψ0 : ψ 0 = 1 := by
    have := (eventually_apply_eq_iff_implicitFunctionOfBivariate (u := ((0 : ℂ), (1 : ℂ)))
      (f := charF P X)
      (f₁ := fun s l => ContinuousLinearMap.toSpanSingleton ℂ (charFs P X s l))
      (f₂ := fun s l => ContinuousLinearMap.toSpanSingleton ℂ (charFl P X s l))
      df₁ df₂ cf₁ cf₂ if₂u).self_of_nhds
    exact this.mp rfl
  have hψzero : ∀ᶠ s in 𝓝 (0 : ℂ), charF P X s (ψ s) = 0 := by
    have := eventually_apply_implicitFunctionOfBivariate (u := ((0 : ℂ), (1 : ℂ)))
      (f := charF P X)
      (f₁ := fun s l => ContinuousLinearMap.toSpanSingleton ℂ (charFs P X s l))
      (f₂ := fun s l => ContinuousLinearMap.toSpanSingleton ℂ (charFl P X s l))
      df₁ df₂ cf₁ cf₂ if₂u
    have hF0 : charF P X 0 1 = 0 := by
      have hdet : (1 - P).det = 0 := by
        apply (Matrix.exists_mulVec_eq_zero_iff).mp
        haveI := hW.nonempty
        refine ⟨1, one_ne_zero, ?_⟩
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, hW.row, sub_self]
      have e := RingHom.map_det Complex.ofRealHom (1 - P)
      rw [hdet, map_zero] at e
      rw [charF, tiltC_zero]
      exact e.symm
    filter_upwards [this] with s hs
    rw [hs]
    exact hF0
  have hderiv := (hasStrictFDerivAt_implicitFunctionOfBivariate (u := ((0 : ℂ), (1 : ℂ)))
    (f := charF P X)
    (f₁ := fun s l => ContinuousLinearMap.toSpanSingleton ℂ (charFs P X s l))
    (f₂ := fun s l => ContinuousLinearMap.toSpanSingleton ℂ (charFl P X s l))
    df₁ df₂ cf₁ cf₂ if₂u).hasFDerivAt
  have hψ' : HasDerivAt ψ ((v : ℝ) : ℂ) 0 := by
    have h1 := hderiv.hasDerivAt
    convert h1 using 1
    simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.toSpanSingleton_apply, one_smul]
    have hinv : (ContinuousLinearMap.toSpanSingleton ℂ (charFl P X 0 1)).inverse
        (charFs P X 0 1) = charFs P X 0 1 / charFl P X 0 1 := by
      rw [if₂u.inverse_apply_eq]
      simp only [ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul]
      rw [hFl]
      field_simp
    rw [hinv, hFs, hFl]
    push_cast
    field_simp
  refine ⟨ψ, hψ0, hψzero, hψ', ?_⟩
  -- the angle under the phase `e^{−iθX}`
  have hc : HasDerivAt (fun s : ℂ => ψ (-I * s)) ((v : ℂ) * (-I)) 0 := by
    have hlin : HasDerivAt (fun s : ℂ => -I * s) (-I) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul (-I)
    have hψ'' : HasDerivAt ψ ((v : ℝ) : ℂ) (-I * 0) := by simpa using hψ'
    exact hψ''.comp (0 : ℂ) hlin
  have hr : HasDerivAt (fun θ : ℝ => ψ (-I * θ)) ((v : ℂ) * (-I)) 0 := by
    have := hc.comp_ofReal (z := 0)
    simpa using this
  have hslit : ψ (-I * ((0 : ℝ) : ℂ)) ∈ slitPlane := by
    simp [hψ0]
  have hlog := hr.clog_real hslit
  have him := (Complex.imCLM.hasFDerivAt (x := Complex.log (ψ (-I * ((0 : ℝ) : ℂ))))).comp_hasDerivAt
    (0 : ℝ) hlog
  convert him using 1
  · funext θ
    simp [Complex.log_im]
  · simp [hψ0]

/-- **A real weight moves the zero only radially:** for real `s` near `0` the largest eigenvalue of
`P ∘ e^{sX}` is real and positive, so the long-range zero `1/(4ρ(s))` lies on the positive real
axis. -/
theorem real_weight_real_root (P X : Matrix ι ι ℝ) (π : ι → ℝ)
    (hW : WeightedWalk (tiltR P X) P (hadPow P X 1) (hadPow P X 2) π) :
    ∀ᶠ s in 𝓝 (0 : ℝ), 0 < perronRoot (tiltR P X) s ∧
      Complex.arg ((1 / (4 * perronRoot (tiltR P X) s) : ℝ) : ℂ) = 0 := by
  filter_upwards [perronRoot_spec hW] with s hs
  have hpos := hs.1
  refine ⟨hpos, ?_⟩
  rw [Complex.arg_ofReal_of_nonneg]
  positivity

end Tilt

/-! ## A uniform phase: the angle of the zero is the phase -/

/-- **A uniform phase turns the zero by its angle:** with the phase `e^{−iμ}` on every step,
`det(1 − u e^{−iμ} B) = D₊(u e^{−iμ})`, which vanishes at `u = e^{iμ}/4`. -/
theorem uniform_phase_zero (μ : ℝ) (u : ℂ) :
    (1 - (u * Complex.exp (-(μ : ℂ) * I)) • stepOp transitionMat).det =
      (1 - (u * Complex.exp (-(μ : ℂ) * I)) ^ 2) ^ 24 * (1 - u * Complex.exp (-(μ : ℂ) * I)) *
        (1 - 4 * (u * Complex.exp (-(μ : ℂ) * I))) *
        (1 - u * Complex.exp (-(μ : ℂ) * I) + 4 * (u * Complex.exp (-(μ : ℂ) * I)) ^ 2) ^ 10 *
        (1 + 3 * (u * Complex.exp (-(μ : ℂ) * I)) + 4 * (u * Complex.exp (-(μ : ℂ) * I)) ^ 2) ^ 5 ∧
    (1 - (Complex.exp ((μ : ℂ) * I) / 4 * Complex.exp (-(μ : ℂ) * I)) • stepOp transitionMat).det = 0 := by
  refine ⟨D_plus _, ?_⟩
  rw [D_plus]
  have e : Complex.exp ((μ : ℂ) * I) / 4 * Complex.exp (-(μ : ℂ) * I) = 1 / 4 := by
    rw [div_mul_eq_mul_div, ← Complex.exp_add]
    simp
  rw [e]
  ring

theorem quad_ne_zero_of_small (v : ℂ) (hv : ‖v‖ ≤ 1 / 4) (b : ℝ) (hb : |b| ≤ 3) :
    1 + (b : ℂ) * v + 4 * v ^ 2 ≠ 0 := by
  intro h
  -- the roots of `4v² + bv + 1` with `b² < 16` have modulus `1/2`
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, sq, Complex.zero_re, Complex.add_im, Complex.one_im, Complex.mul_im,
    zero_add, Complex.zero_im] at hre him
  norm_num at hre him
  have hn : ‖v‖ ^ 2 = v.re ^ 2 + v.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hb2 : b ^ 2 ≤ 9 := by
    have := sq_abs b
    nlinarith [abs_nonneg b]
  have hv2 : ‖v‖ ^ 2 ≤ 1 / 16 := by
    have := norm_nonneg v
    nlinarith
  rcases eq_or_ne v.im 0 with hy | hy
  · rw [hy] at hre
    nlinarith [sq_nonneg (8 * v.re + b)]
  · have hx : 8 * v.re + b = 0 := by
      have : v.im * (8 * v.re + b) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hy
    have hx' : v.re = -b / 8 := by linarith
    rw [hx'] at hre
    have : 4 * v.im ^ 2 = 1 - b ^ 2 / 16 := by nlinarith
    nlinarith

/-- **On the closed disc `|v| ≤ 1/4`, `D₊(v)` vanishes only at `v = 1/4`.** -/
theorem D_plus_disc (v : ℂ) (hv : ‖v‖ ≤ 1 / 4) :
    (1 - v ^ 2) ^ 24 * (1 - v) * (1 - 4 * v) * (1 - v + 4 * v ^ 2) ^ 10 *
      (1 + 3 * v + 4 * v ^ 2) ^ 5 = 0 ↔ v = 1 / 4 := by
  constructor
  · intro h
    have h1 : (1 - v ^ 2) ≠ 0 := by
      intro h0
      have : ‖v ^ 2‖ = 1 := by rw [show v ^ 2 = 1 by linear_combination -h0]; simp
      rw [norm_pow] at this
      nlinarith [norm_nonneg v]
    have h2 : (1 - v) ≠ 0 := by
      intro h0
      have : v = 1 := by linear_combination -h0
      rw [this] at hv
      norm_num at hv
    have h3 : (1 - v + 4 * v ^ 2) ≠ 0 := by
      have := quad_ne_zero_of_small v hv (-1) (by norm_num)
      intro h0
      apply this
      push_cast
      linear_combination h0
    have h5 : (1 + 3 * v + 4 * v ^ 2) ≠ 0 := by
      have := quad_ne_zero_of_small v hv 3 (by norm_num)
      intro h0
      apply this
      push_cast
      linear_combination h0
    have h4 : 1 - 4 * v = 0 := by
      rcases mul_eq_zero.mp h with h | h
      · rcases mul_eq_zero.mp h with h | h
        · rcases mul_eq_zero.mp h with h | h
          · rcases mul_eq_zero.mp h with h | h
            · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) h1
            · exact absurd h h2
          · exact h
        · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) h3
      · exact absurd (pow_eq_zero_iff (by norm_num) |>.mp h) h5
    linear_combination -h4 / 4
  · rintro rfl
    ring

/-! ## The available transitions numerator as an angle -/

section AvailableTransitionsAngle

variable (h : Fin 5)

/-- The law `B/4` on the eighty states. -/
noncomputable def lawP : Matrix State State ℝ := (1 / 4 : ℝ) • stepR

/-- **The available transitions weight on the law:** `X(target)` on the steps out of the available transitions of `h` (the transitions),
`0` on the hidden steps. Entry `(s', s)` is the weight of the step `s → s'`. -/
noncomputable def availableTransitionsLawX (X : State → ℝ) : Matrix State State ℝ :=
  Matrix.of fun s' s => if InAvailableTransitions h s then X s' else 0

/-- The weight `1` on one transition `a₀ → s₀`. -/
noncomputable def oneTransitionX (a₀ s₀ : State) : Matrix State State ℝ :=
  Matrix.of fun s' s => if s = a₀ ∧ s' = s₀ then 1 else 0

theorem lawP_weighted (X : Matrix State State ℝ) :
    WeightedWalk (tiltR (lawP) X) lawP (hadPow lawP X 1) (hadPow lawP X 2) piU := by
  have hW := lastDirectionWalk_weighted 0
  refine tilt_weighted lawP X piU (fun i j => ?_) hW.row hW.stat hW.pos hW.total hW.kerR hW.kerL
    hW.adj
  simp only [lawP, Matrix.smul_apply, stepR, stepT, Matrix.of_apply, smul_eq_mul]
  split_ifs <;> norm_num

theorem lawP_rate (X : Matrix State State ℝ) :
    piU ⬝ᵥ (hadPow lawP X 1 *ᵥ 1) =
      (1 / 320) * ∑ s : State, ∑ s' : State, if Continues s s' then X s' s else 0 := by
  have e : ∀ s' s : State,
      hadPow lawP X 1 s' s = (1 / 4) * (if Continues s s' then X s' s else 0) := by
    intro s' s
    simp only [hadPow, lawP, Matrix.of_apply, Matrix.smul_apply, stepR, stepT, smul_eq_mul,
      pow_one]
    split_ifs <;> ring
  simp only [dotProduct, piU, Matrix.mulVec, e, Pi.one_apply, mul_one]
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

/-- The transitions of the available transitions of `h`, each weighed by `L(Ω) + [along h]`, total `1836`. -/
theorem transition_total : ∀ h : Fin 5, ∑ s : State, ∑ s' : State,
    (if Continues s s' ∧ inExcursion h s = true then 6 + (if s'.2 = h then 1 else 0) else 0 : ℕ) =
      1836 := by
  decide +kernel

/-- **The available transitions weight `X = L(Ω) + [along h]` turns the zero at `1836/320` per unit `θ` per step**:
the transitions carry `6M + C_h = 1836` (`transition_inventory`) of the `320` steps of a stationary cycle. -/
theorem availableTransitions_angle_rate :
    piU ⬝ᵥ (hadPow lawP (availableTransitionsLawX h (transitionX h)) 1 *ᵥ 1) = 1836 / 320 := by
  rw [lawP_rate]
  have e : (∑ s : State, ∑ s' : State,
      (if Continues s s' then availableTransitionsLawX h (transitionX h) s' s else 0)) =
      ((∑ s : State, ∑ s' : State,
        (if Continues s s' ∧ inExcursion h s = true then 6 + (if s'.2 = h then 1 else 0) else 0 : ℕ) :
          ℕ) : ℝ) := by
    push_cast
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
    simp only [availableTransitionsLawX, Matrix.of_apply, transitionX, alongH, InAvailableTransitions]
    by_cases hc : Continues s s' <;> by_cases ha : inExcursion h s = true <;>
      by_cases hh : s'.2 = h <;> simp only [hc, ha, hh, if_true, if_false, and_true, and_false,
        true_and, false_and] <;> norm_num
  rw [e, transition_total h]
  norm_num

/-- **The weight `1` on one transition turns the zero at `1/320` per unit `θ` per step.** -/
theorem one_transition_angle_rate (a₀ s₀ : State) (h₀ : Continues a₀ s₀) :
    piU ⬝ᵥ (hadPow lawP (oneTransitionX a₀ s₀) 1 *ᵥ 1) = 1 / 320 := by
  rw [lawP_rate]
  have e : ∑ s : State, ∑ s' : State,
      (if Continues s s' then oneTransitionX a₀ s₀ s' s else 0) = 1 := by
    simp only [oneTransitionX, Matrix.of_apply]
    rw [Finset.sum_eq_single a₀]
    · rw [Finset.sum_eq_single s₀]
      · simp [h₀]
      · intro b _ hb
        simp [hb]
      · simp
    · intro b _ hb
      simp [hb]
    · simp
  rw [e]
  norm_num

/-- **The available transitions part of the proton's row as a ratio of two angles:** with the phase `e^{−iθX}` on
the transitions of the available transitions of `h`, `X = L(Ω) + [along h]`, the long-range zero of the law turns at the
rate `1836/320` per unit `θ`, with the phase `e^{−iθ}` on one transition at `1/320`; the two zeros exist
and turn as stated (`angle_of_zero`), and **the ratio of the rates is `1836 = 6M + C_h`**. -/
theorem proton_availableTransitions_ratio (a₀ s₀ : State) (h₀ : Continues a₀ s₀) :
    (∃ ψ : ℂ → ℂ, ψ 0 = 1 ∧ (∀ᶠ s in 𝓝 0, charF lawP (availableTransitionsLawX h (transitionX h)) s (ψ s) = 0) ∧
      HasDerivAt (fun θ : ℝ => Complex.arg (ψ (-I * θ))) (-(1836 / 320 : ℝ)) 0) ∧
    (∃ ψ : ℂ → ℂ, ψ 0 = 1 ∧ (∀ᶠ s in 𝓝 0, charF lawP (oneTransitionX a₀ s₀) s (ψ s) = 0) ∧
      HasDerivAt (fun θ : ℝ => Complex.arg (ψ (-I * θ))) (-(1 / 320 : ℝ)) 0) ∧
    (1836 / 320 : ℝ) / (1 / 320) = 1836 := by
  refine ⟨?_, ?_, by norm_num⟩
  · obtain ⟨ψ, h0, hz, -, hang⟩ := angle_of_zero lawP (availableTransitionsLawX h (transitionX h)) piU
      (lawP_weighted _)
    rw [availableTransitions_angle_rate] at hang
    exact ⟨ψ, h0, hz, hang⟩
  · obtain ⟨ψ, h0, hz, -, hang⟩ := angle_of_zero lawP (oneTransitionX a₀ s₀) piU (lawP_weighted _)
    rw [one_transition_angle_rate a₀ s₀ h₀] at hang
    exact ⟨ψ, h0, hz, hang⟩

end AvailableTransitionsAngle

end Comparison

end
