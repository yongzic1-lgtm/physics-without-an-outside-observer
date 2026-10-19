import Comparison.System.Postulates
import Comparison.System.Law.Critical
import Comparison.Existence.Motion
import Comparison.Mass.Taylor
import Comparison.Elements.Overlap
import Comparison.System.Existence.Six

/-!
# The proof system, the law: Proposition 60 and equation (26), one step in motion

The step in motion `U = e^{−ikγ_j}e^{−iμγ_h}`
(`Existence/Motion.lean`), its dispersion (`Mass/Taylor.lean`), the orthonormal basis `f` of `𝟏^⊥`
(`Law/Critical.lean`: `helmert`). Here:

* `chartLine μ = Σ_t v_t^μ γ_t` with `v_t^μ = v_t·f_μ`, `massLine = Σ_t γ_t/√5`; `vR_dot_helmert`: `v_t^μ = f_μ(t)`;
  `chart_five_lines`: **the five are anticommuting lines**: `{Γ^μ, Γ^ν} = 2δ^{μν}`, `{Γ^μ, γ(m)} = 0`, `γ(m)² = 1`;
* `pd μ f`, `diracOp M ψ = Γ^μ∂_μψ + iMγ(m)ψ`, `lap4 f = Σ_μ ∂_μ²f` on fields `ℝ⁴ → ℂ⁴`;
  `dirac_operator_square`: **`(Γ^μ∂_μ + iMγ(m))²ψ = Δψ − M²ψ` for every `C²` field `ψ`** (the second derivatives
  commute: Schwarz, `pd_comm`);
* `rest_phase`: at `k = 0`, `ω = arccos(cos μ) = |μ|`;
* `prop_60`, `eq_26`.
-/

open Matrix Complex Comparison

namespace Comparison.System

namespace Law

/-! ## The five directions of the chart -/

/-- **The chart's four lines** `Γ^μ = Σ_t v_t^μ γ_t`, `v_t^μ = v_t·f_μ` in the orthonormal basis `f` of `𝟏^⊥`. -/
noncomputable def chartLine (μ : Fin 4) : Matrix Four Four ℂ := ∑ t, ((vR t ⬝ᵥ helmert μ : ℝ) : ℂ) • γ t

/-- **The fifth line** `γ(m) = Σ_t γ_t/√5`. -/
noncomputable def massLine : Matrix Four Four ℂ := ∑ t, ((1 / Real.sqrt 5 : ℝ) : ℂ) • γ t

/-- The components of the chart: `v_t^μ = v_t·f_μ = f_μ(t)`. -/
theorem vR_dot_helmert (μ : Fin 4) (t : Fin 5) : vR t ⬝ᵥ helmert μ = helmert μ t := by
  have hs : ∑ a, helmert μ a = 0 := helmert_orthonormal.2 μ
  simp only [dotProduct, vR, sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, ← Finset.mul_sum, hs, mul_zero, sub_zero]

theorem chartLine_eq (μ : Fin 4) : chartLine μ = γv (helmert μ) := by
  simp only [chartLine, γv, vR_dot_helmert]

/-- The unit vector `𝟏/√5`. -/
noncomputable def massVec : Fin 5 → ℝ := fun _ => 1 / Real.sqrt 5

theorem massLine_eq : massLine = γv massVec := rfl

theorem massVec_dot : massVec ⬝ᵥ massVec = 1 := by
  simp only [massVec, dotProduct, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [div_mul_div_comm, one_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 5)]
  norm_num

theorem helmert_dot_massVec (μ : Fin 4) : helmert μ ⬝ᵥ massVec = 0 := by
  simp only [massVec, dotProduct, ← Finset.sum_mul, helmert_orthonormal.2 μ, zero_mul]

theorem anticomm_dot (n m : Fin 5 → ℝ) :
    γv n * γv m + γv m * γv n = ((2 * (n ⬝ᵥ m) : ℝ) : ℂ) • (1 : Matrix Four Four ℂ) := by
  rw [anticomm_γv]
  rfl

/-- **The five directions of the chart anticommute and square to one:** `{Γ^μ, Γ^ν} = 2δ^{μν}`,
`{Γ^μ, γ(m)} = 0`, `γ(m)² = 1`. -/
theorem chart_five_lines :
    (∀ μ ν : Fin 4, chartLine μ * chartLine ν + chartLine ν * chartLine μ =
      (if μ = ν then (2 : ℂ) else 0) • (1 : Matrix Four Four ℂ)) ∧
    (∀ μ : Fin 4, chartLine μ * massLine + massLine * chartLine μ = 0) ∧
    massLine * massLine = 1 := by
  refine ⟨fun μ ν => ?_, fun μ => ?_, ?_⟩
  · rw [chartLine_eq, chartLine_eq, anticomm_dot, helmert_orthonormal.1 μ ν]
    split_ifs <;> simp
  · rw [chartLine_eq, massLine_eq, anticomm_dot, helmert_dot_massVec]
    simp
  · rw [massLine_eq, γv_mul_self]
    have h : (∑ s, massVec s ^ 2) = 1 := by
      rw [← massVec_dot]
      simp [dotProduct, sq]
    rw [h]
    simp

/-! ## The Dirac operator on fields -/

/-- `∂_μ f` for a function on `ℝ⁴`. -/
noncomputable def pd (μ : Fin 4) (f : (Fin 4 → ℝ) → ℂ) : (Fin 4 → ℝ) → ℂ :=
  fun x => fderiv ℝ f x (Pi.single μ 1)

/-- **The Dirac operator** `(Γ^μ∂_μ + iMγ(m))ψ` on a field `ψ : ℝ⁴ → ℂ⁴` (components `ψ a`). -/
noncomputable def diracOp (M : ℝ) (ψ : Four → (Fin 4 → ℝ) → ℂ) : Four → (Fin 4 → ℝ) → ℂ :=
  fun a x => ∑ μ, ∑ b, chartLine μ a b * pd μ (ψ b) x + I * M * ∑ b, massLine a b * ψ b x

/-- **The Laplacian** `Δf = Σ_μ ∂_μ² f`. -/
noncomputable def lap4 (f : (Fin 4 → ℝ) → ℂ) : (Fin 4 → ℝ) → ℂ := fun x => ∑ μ, pd μ (pd μ f) x

section Calculus

variable {x : Fin 4 → ℝ}

theorem pd_add {f g : (Fin 4 → ℝ) → ℂ} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x)
    (ν : Fin 4) : pd ν (fun y => f y + g y) x = pd ν f x + pd ν g x := by
  simp only [pd]
  rw [fderiv_fun_add hf hg]
  rfl

theorem pd_const_mul {f : (Fin 4 → ℝ) → ℂ} (hf : DifferentiableAt ℝ f x) (k : ℂ) (ν : Fin 4) :
    pd ν (fun y => k * f y) x = k * pd ν f x := by
  simp only [pd]
  rw [fderiv_const_mul hf k]
  rfl

theorem pd_sum {ι : Type*} (s : Finset ι) {f : ι → (Fin 4 → ℝ) → ℂ}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) (ν : Fin 4) :
    pd ν (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, pd ν (f i) x := by
  simp only [pd]
  rw [fderiv_fun_sum hf]
  simp [ContinuousLinearMap.sum_apply]

theorem diff_lin {ι : Type*} (s : Finset ι) (k : ι → ℂ) {f : ι → (Fin 4 → ℝ) → ℂ}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) :
    DifferentiableAt ℝ (fun y => ∑ i ∈ s, k i * f i y) x := by
  have h := DifferentiableAt.sum (u := s) (A := fun i y => k i * f i y)
    (fun i hi => (hf i hi).const_mul (k i))
  convert h using 1
  funext y
  simp [Finset.sum_apply]

theorem diff_sum {ι : Type*} (s : Finset ι) {f : ι → (Fin 4 → ℝ) → ℂ}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) :
    DifferentiableAt ℝ (fun y => ∑ i ∈ s, f i y) x := by
  have h := DifferentiableAt.sum (u := s) (A := f) hf
  convert h using 1
  funext y
  simp [Finset.sum_apply]

theorem pd_lin {ι : Type*} (s : Finset ι) (k : ι → ℂ) {f : ι → (Fin 4 → ℝ) → ℂ}
    (hf : ∀ i ∈ s, DifferentiableAt ℝ (f i) x) (ν : Fin 4) :
    pd ν (fun y => ∑ i ∈ s, k i * f i y) x = ∑ i ∈ s, k i * pd ν (f i) x := by
  rw [pd_sum s (f := fun i y => k i * f i y) (fun i hi => (hf i hi).const_mul (k i))]
  exact Finset.sum_congr rfl fun i hi => pd_const_mul (hf i hi) (k i) ν

/-- A `C²` function has differentiable partial derivatives. -/
theorem differentiable_pd {f : (Fin 4 → ℝ) → ℂ} (hf : ContDiff ℝ 2 f) (μ : Fin 4) :
    Differentiable ℝ (pd μ f) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have h2 : ContDiff ℝ 1 (fun y => fderiv ℝ f y (Pi.single μ 1)) := h1.clm_apply contDiff_const
  exact h2.differentiable (by norm_num)

/-- **Schwarz:** the second partial derivatives of a `C²` function commute. -/
theorem pd_comm {f : (Fin 4 → ℝ) → ℂ} (hf : ContDiff ℝ 2 f) (μ ν : Fin 4) (x : Fin 4 → ℝ) :
    pd μ (pd ν f) x = pd ν (pd μ f) x := by
  have hd : ∀ y, DifferentiableAt ℝ (fderiv ℝ f) y := fun y =>
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) y
  have e : ∀ μ' ν' : Fin 4, pd μ' (pd ν' f) x =
      fderiv ℝ (fderiv ℝ f) x (Pi.single μ' 1) (Pi.single ν' 1) := by
    intro μ' ν'
    change fderiv ℝ (fun y => fderiv ℝ f y (Pi.single ν' 1)) x (Pi.single μ' 1) = _
    rw [fderiv_clm_apply (hd x) (differentiableAt_const _)]
    simp
  have hs := (hf.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  rw [e, e, hs.eq]

end Calculus

/-- `Σ_μ Σ_ν T μ ν = ½ Σ_μ Σ_ν (T μ ν + T ν μ)` for vectors. -/
theorem sum_symm_vec (T : Fin 4 → Fin 4 → Four → ℂ) :
    ∑ μ, ∑ ν, T μ ν = (1 / 2 : ℂ) • ∑ μ, ∑ ν, (T μ ν + T ν μ) := by
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun μ ν => T ν μ), ← two_smul ℂ, smul_smul]
  norm_num

/-- **The algebra of the square:** with `S μ ν = S ν μ`,
`Σ_μ Γ^μ(Σ_ν Γ^ν S_{μν} + cγP_μ) + cγ(Σ_ν Γ^ν P_ν + cγΨ) = Σ_μ S_{μμ} + c²Ψ`. -/
theorem dirac_vector_identity (c : ℂ) (S : Fin 4 → Fin 4 → Four → ℂ) (hS : ∀ μ ν, S μ ν = S ν μ)
    (P : Fin 4 → Four → ℂ) (Ψ : Four → ℂ) :
    ∑ μ, chartLine μ *ᵥ (∑ ν, chartLine ν *ᵥ S μ ν + c • (massLine *ᵥ P μ)) +
      c • (massLine *ᵥ (∑ ν, chartLine ν *ᵥ P ν + c • (massLine *ᵥ Ψ))) =
    ∑ μ, S μ μ + c ^ 2 • Ψ := by
  obtain ⟨hGG, hGm, hmm⟩ := chart_five_lines
  have h1 : ∑ μ, ∑ ν, (chartLine μ * chartLine ν) *ᵥ S μ ν = ∑ μ, S μ μ := by
    rw [sum_symm_vec]
    have e : ∀ μ ν, (chartLine μ * chartLine ν) *ᵥ S μ ν + (chartLine ν * chartLine μ) *ᵥ S ν μ =
        (if μ = ν then (2 : ℂ) else 0) • S μ ν := by
      intro μ ν
      rw [← hS μ ν, ← Matrix.add_mulVec, hGG μ ν, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp only [e, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte,
      Finset.smul_sum, smul_smul]
    norm_num
  have h2 : ∑ μ, c • ((chartLine μ * massLine) *ᵥ P μ) +
      ∑ μ, c • ((massLine * chartLine μ) *ᵥ P μ) = 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun μ _ => ?_
    rw [← smul_add, ← Matrix.add_mulVec, hGm μ, Matrix.zero_mulVec, smul_zero]
  have h3 : c • c • ((massLine * massLine) *ᵥ Ψ) = c ^ 2 • Ψ := by
    rw [hmm, Matrix.one_mulVec, smul_smul, sq]
  have hA : ∑ μ, chartLine μ *ᵥ (∑ ν, chartLine ν *ᵥ S μ ν + c • (massLine *ᵥ P μ)) =
      ∑ μ, ∑ ν, (chartLine μ * chartLine ν) *ᵥ S μ ν +
        ∑ μ, c • ((chartLine μ * massLine) *ᵥ P μ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
    congr 1
    exact Finset.sum_congr rfl fun ν _ => Matrix.mulVec_mulVec _ _ _
  have hB : c • (massLine *ᵥ (∑ ν, chartLine ν *ᵥ P ν + c • (massLine *ᵥ Ψ))) =
      ∑ μ, c • ((massLine * chartLine μ) *ᵥ P μ) + c • c • ((massLine * massLine) *ᵥ Ψ) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, Matrix.mulVec_mulVec, smul_add,
      Finset.smul_sum]
    congr 1
    exact Finset.sum_congr rfl fun ν _ => by rw [Matrix.mulVec_mulVec]
  rw [hA, hB, h1, h3]
  calc ∑ μ, S μ μ + ∑ μ, c • ((chartLine μ * massLine) *ᵥ P μ) +
        (∑ μ, c • ((massLine * chartLine μ) *ᵥ P μ) + c ^ 2 • Ψ)
      = ∑ μ, S μ μ + (∑ μ, c • ((chartLine μ * massLine) *ᵥ P μ) +
          ∑ μ, c • ((massLine * chartLine μ) *ᵥ P μ)) + c ^ 2 • Ψ := by abel
    _ = ∑ μ, S μ μ + c ^ 2 • Ψ := by rw [h2, add_zero]

theorem diracOp_vec (M : ℝ) (ψ : Four → (Fin 4 → ℝ) → ℂ) (x : Fin 4 → ℝ) :
    (fun a => diracOp M ψ a x) =
      ∑ μ, chartLine μ *ᵥ (fun b => pd μ (ψ b) x) + (I * M) • (massLine *ᵥ (fun b => ψ b x)) := by
  funext a
  simp [diracOp, Matrix.mulVec, dotProduct, Finset.sum_apply]

/-- **`(Γ^μ∂_μ + iMγ(m))²ψ = Δψ − M²ψ`** for every `C²` field `ψ : ℝ⁴ → ℂ⁴`. -/
theorem dirac_operator_square (M : ℝ) (ψ : Four → (Fin 4 → ℝ) → ℂ) (hψ : ∀ b, ContDiff ℝ 2 (ψ b))
    (a : Four) (x : Fin 4 → ℝ) :
    diracOp M (diracOp M ψ) a x = lap4 (ψ a) x - (M : ℂ) ^ 2 * ψ a x := by
  have hd1 : ∀ b, Differentiable ℝ (ψ b) := fun b => (hψ b).differentiable (by norm_num)
  have hd2 : ∀ μ b, Differentiable ℝ (pd μ (ψ b)) := fun μ b => differentiable_pd (hψ b) μ
  -- the derivative of the inner field, component by component
  have hinner : ∀ (μ : Fin 4) (b : Four), pd μ (diracOp M ψ b) x =
      ∑ ν, ∑ c, chartLine ν b c * pd μ (pd ν (ψ c)) x + I * M * ∑ c, massLine b c * pd μ (ψ c) x := by
    intro μ b
    have hA : ∀ ν ∈ (Finset.univ : Finset (Fin 4)),
        DifferentiableAt ℝ (fun y => ∑ c, chartLine ν b c * pd ν (ψ c) y) x :=
      fun ν _ => diff_lin _ _ fun c _ => hd2 ν c x
    have hA' : DifferentiableAt ℝ (fun y => ∑ ν, ∑ c, chartLine ν b c * pd ν (ψ c) y) x :=
      diff_sum _ hA
    have hB : DifferentiableAt ℝ (fun y => ∑ c, massLine b c * ψ c y) x :=
      diff_lin _ _ fun c _ => hd1 c x
    have hB' : DifferentiableAt ℝ (fun y => I * M * ∑ c, massLine b c * ψ c y) x := hB.const_mul _
    change pd μ (fun y => ∑ ν, ∑ c, chartLine ν b c * pd ν (ψ c) y +
      I * M * ∑ c, massLine b c * ψ c y) x = _
    rw [pd_add hA' hB' μ, pd_sum _ hA μ, pd_const_mul hB _ μ, pd_lin _ _ (fun c _ => hd1 c x) μ]
    congr 1
    exact Finset.sum_congr rfl fun ν _ => pd_lin _ _ (fun c _ => hd2 ν c x) μ
  have hS : ∀ μ ν, (fun μ ν c => pd μ (pd ν (ψ c)) x) μ ν =
      (fun μ ν c => pd μ (pd ν (ψ c)) x) ν μ := fun μ ν => by
    funext c
    exact pd_comm (hψ c) μ ν x
  have hsum : ∑ μ, chartLine μ *ᵥ (fun b => pd μ (diracOp M ψ b) x) =
      ∑ μ, chartLine μ *ᵥ (∑ ν, chartLine ν *ᵥ (fun c => pd μ (pd ν (ψ c)) x) +
        (I * M) • (massLine *ᵥ (fun c => pd μ (ψ c) x))) := by
    refine Finset.sum_congr rfl fun μ _ => ?_
    congr 1
    funext b
    rw [hinner μ b]
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply]
  have h0 : diracOp M (diracOp M ψ) a x = (∑ μ, chartLine μ *ᵥ (fun b => pd μ (diracOp M ψ b) x) +
      (I * M) • (massLine *ᵥ (fun b => diracOp M ψ b x))) a :=
    congrFun (diracOp_vec M (diracOp M ψ) x) a
  rw [h0, hsum, diracOp_vec M ψ x]
  have hid := dirac_vector_identity (I * M) (fun μ ν c => pd μ (pd ν (ψ c)) x) hS
    (fun μ c => pd μ (ψ c) x) (fun c => ψ c x)
  try simp only at hid
  rw [hid]
  simp [lap4, Finset.sum_apply, mul_pow, I_sq]
  ring

/-- At rest the eigenphase is the clock's: `ω = arccos(cos μ cos 0) = |μ|` for `|μ| ≤ π`. -/
theorem rest_phase (μ : ℝ) (h : |μ| ≤ Real.pi) :
    Real.arccos (Real.cos μ * Real.cos 0) = |μ| := by
  rw [Real.cos_zero, mul_one, ← Real.cos_abs, Real.arccos_cos (abs_nonneg μ) h]

end Law

open Comparison.System.Law

/-- **Proposition 60, one step in motion.** At rest one step turns the clock, `U = e^{−iμγ_h}`; moving along
another line `j`, `U = e^{−ikγ_j}e^{−iμγ_h}` (the matrix exponentials, `= (cos k − i sin k γ_j)(cos μ − i sin μ γ_h)`,
E's `exp_iγ`) is unitary with `U + U† = 2 cos k cos μ`, so every eigenvalue
`λ = e^{iω}` has `|λ| = 1` and `cos ω = Re λ = cos μ cos k`; for `|μ|, |k| ≤ 1/2`,
`ω = arccos(cos μ cos k)` has `|ω² − (μ² + k² − μ²k²/3)| ≤ 3(μ² + k²)³ ≤ 3(|μ| + |k|)⁶`; at `k = 0`, `ω = |μ|`;
in the chart `Γ^μ = Σ_t v_t^μ γ_t` (`v_t^μ = v_t·f_μ = f_μ(t)`, `f` an orthonormal basis of `𝟏^⊥`) and
`γ(m) = Σ_t γ_t/√5` are five anticommuting lines, and `(Γ^μ∂_μ + iMγ(m))²ψ = Δψ − M²ψ` for every `C²` field
`ψ : ℝ⁴ → ℂ⁴`, `Δ = Σ_μ ∂_μ²`.
Recognition: with `μ = mc²τ/ℏ`, `k = pcτ/ℏ`, `ω = Eτ/ℏ`, `E² = p²c² + m²c⁴`; the square is Dirac's.
Every candidate system: System.uniqueness. -/
theorem prop_60 :
    (∀ (k μ : ℝ) (j h : Fin 5), stepMotion k μ j h =
      NormedSpace.exp ((-k) • (I • γ j)) * NormedSpace.exp ((-μ) • (I • γ h))) ∧
    (∀ (μ : ℝ) (j h : Fin 5), stepMotion 0 μ j h = NormedSpace.exp ((-μ) • (I • γ h))) ∧
    (∀ (μ : ℝ) (j h : Fin 5), stepMotion 0 μ j h = expIγ (-μ) h) ∧
    (∀ (k μ : ℝ) (j h : Fin 5), stepMotion k μ j h * (stepMotion k μ j h)ᴴ = 1) ∧
    (∀ (k μ : ℝ) (j h : Fin 5), j ≠ h → stepMotion k μ j h + (stepMotion k μ j h)ᴴ =
      ((2 * Real.cos k * Real.cos μ : ℝ) : ℂ) • (1 : Matrix Four Four ℂ)) ∧
    (∀ (k μ : ℝ) (j h : Fin 5), j ≠ h → ∀ v : Four → ℂ, v ≠ 0 → ∀ lam : ℂ,
      stepMotion k μ j h *ᵥ v = lam • v → lam.re = Real.cos k * Real.cos μ ∧ Complex.normSq lam = 1) ∧
    (∀ μ k : ℝ, |μ| ≤ 1 / 2 → |k| ≤ 1 / 2 →
      |Real.arccos (Real.cos μ * Real.cos k) ^ 2 - (μ ^ 2 + k ^ 2 - μ ^ 2 * k ^ 2 / 3)| ≤
        3 * (μ ^ 2 + k ^ 2) ^ 3) ∧
    (∀ μ : ℝ, |μ| ≤ Real.pi → Real.arccos (Real.cos μ * Real.cos 0) = |μ|) ∧
    (∀ (μ : Fin 4) (t : Fin 5), vR t ⬝ᵥ helmert μ = helmert μ t) ∧
    ((∀ i j, helmert i ⬝ᵥ helmert j = if i = j then 1 else 0) ∧ ∀ i, ∑ a, helmert i a = 0) ∧
    (∀ μ ν : Fin 4, chartLine μ * chartLine ν + chartLine ν * chartLine μ =
      (if μ = ν then (2 : ℂ) else 0) • (1 : Matrix Four Four ℂ)) ∧
    (∀ μ : Fin 4, chartLine μ * massLine + massLine * chartLine μ = 0) ∧
    massLine * massLine = 1 ∧
    (∀ (M : ℝ) (ψ : Four → (Fin 4 → ℝ) → ℂ), (∀ b, ContDiff ℝ 2 (ψ b)) → ∀ a x,
      diracOp M (diracOp M ψ) a x = lap4 (ψ a) x - (M : ℂ) ^ 2 * ψ a x) :=
  ⟨fun k μ j h => by
      rw [Comparison.System.Existence.exp_iγ, Comparison.System.Existence.exp_iγ]; rfl,
    fun μ j h => by rw [Comparison.System.Existence.exp_iγ]; exact stepMotion_rest μ j h,
    stepMotion_rest, stepMotion_unitary, fun k μ _ _ hjh => stepMotion_add_adjoint k μ hjh,
    fun k μ _ _ hjh v hv lam hlam => eigen_phase k μ hjh v hv lam hlam,
    fun μ k hμ hk => dispersion_series μ k hμ hk, rest_phase, vR_dot_helmert, helmert_orthonormal,
    chart_five_lines.1, chart_five_lines.2.1, chart_five_lines.2.2, dirac_operator_square⟩

/-- **Equation (26), Dirac's square:** `(Γ^μ∂_μ + iMγ(m))² = Δ − M²` on every `C²` field `ψ : ℝ⁴ → ℂ⁴`. -/
theorem eq_26 (M : ℝ) (ψ : Four → (Fin 4 → ℝ) → ℂ) (hψ : ∀ b, ContDiff ℝ 2 (ψ b)) (a : Four)
    (x : Fin 4 → ℝ) : diracOp M (diracOp M ψ) a x = lap4 (ψ a) x - (M : ℂ) ^ 2 * ψ a x :=
  dirac_operator_square M ψ hψ a x

end Comparison.System
