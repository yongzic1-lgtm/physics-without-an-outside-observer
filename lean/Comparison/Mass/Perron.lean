module

public import Comparison.Mass.Basic

/-!
# The road to the masses: the long-range zero under a weight (Proposition 71), in general

A family `P(s)` of nonnegative matrices with
a second-order expansion `P(s) = P₀ + sP₁ + (s²/2)P₂ + O(s³)` at `s = 0`, where `P₀` is stochastic
with a positive stationary law `π`, one-dimensional kernels and a simple root (the adjugate of
`1 − P₀` is not zero). This is the walk with a weight `e^{sX}` on its steps (`P₁ = P₀ ∘ X`,
`P₂ = P₀ ∘ X²`), on any finite set of states.

* `IsPerron M r`: `r > 0` is an eigenvalue of `M` with a positive right and a positive left
  eigenvector, and every complex eigenvalue of `M` has modulus at most `r`; `perron_unique`: there
  is at most one such `r`: **the largest eigenvalue**.
* `solvable`: `(1 − P₀)x = y` is solvable exactly when `π · y = 0` (the Poisson equation).
* `perron_exists`: **for `s` near `0`, `P(s)` has its largest eigenvalue `ρ(s)`**, with positive
  eigenvectors on both sides (the root found by the intermediate value theorem in the region where
  the adjugate of `ρ − P(s)` keeps the sign it has at `s = 0`).
* `perron_expansion`: **`ρ(s) = 1 + sv + s²λ₂ + O(s³)`**, `v = π P₁ 𝟏` the stationary mean of the
  weight per step, `λ₂ = π P₁ g + ½ π P₂ 𝟏` with `g` the solution of the Poisson equation
  `(1 − P₀)g = P₁𝟏 − v𝟏`, `π g = 0`;
* `perron_log`: **`d/ds log ρ(s) = v` at `s = 0`, and `log ρ(s) = sv + (s²/2)σ² + O(s³)` with
  `σ² = π P₂ 𝟏 + 2 π P₁ g − v²`**, the asymptotic variance of the weight in its Poisson form.

The proof is the identity `(ρ − λ̃)(y · x̃) = y · (P x̃ − λ̃ x̃)` with the positive left eigenvector
`y` of `ρ(s)` and the trial vector `x̃ = 𝟏 + s g + s² x₂`.
-/

@[expose] public section

namespace Comparison

open Matrix Filter Topology Asymptotics

section Perron

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `r` is the largest eigenvalue of the nonnegative matrix `M`, with positive eigenvectors. -/
def IsPerron (M : Matrix ι ι ℝ) (r : ℝ) : Prop :=
  0 < r ∧ (∃ x : ι → ℝ, (∀ i, 0 < x i) ∧ M *ᵥ x = r • x) ∧
    (∃ y : ι → ℝ, (∀ i, 0 < y i) ∧ y ᵥ* M = r • y) ∧
    ∀ μ : ℂ, (μ • (1 : Matrix ι ι ℂ) - M.map (fun a : ℝ => (a : ℂ))).det = 0 → ‖μ‖ ≤ r

theorem det_real_eigen (M : Matrix ι ι ℝ) (r : ℝ) (x : ι → ℝ) (hx : x ≠ 0)
    (hMx : M *ᵥ x = r • x) :
    ((r : ℂ) • (1 : Matrix ι ι ℂ) - M.map (fun a : ℝ => (a : ℂ))).det = 0 := by
  have hdet : (r • (1 : Matrix ι ι ℝ) - M).det = 0 := by
    apply (Matrix.exists_mulVec_eq_zero_iff).mp
    refine ⟨x, hx, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hMx, sub_self]
  have hmap : ((r : ℂ) • (1 : Matrix ι ι ℂ) - M.map (fun a : ℝ => (a : ℂ))) =
      (r • (1 : Matrix ι ι ℝ) - M).map (fun a : ℝ => (a : ℂ)) := by
    ext i j
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Matrix.one_apply]
    split_ifs <;> push_cast <;> ring
  have e := RingHom.map_det Complex.ofRealHom (r • (1 : Matrix ι ι ℝ) - M)
  rw [hdet, map_zero] at e
  rw [hmap]
  exact e.symm

/-- **At most one largest eigenvalue.** -/
theorem perron_unique [Nonempty ι] (M : Matrix ι ι ℝ) (r r' : ℝ) (h : IsPerron M r)
    (h' : IsPerron M r') : r = r' := by
  obtain ⟨hr, ⟨x, hx, hMx⟩, -, hb⟩ := h
  obtain ⟨hr', ⟨x', hx', hMx'⟩, -, hb'⟩ := h'
  have hne : ∀ z : ι → ℝ, (∀ i, 0 < z i) → z ≠ 0 := by
    intro z hz h0
    obtain ⟨i⟩ := (inferInstance : Nonempty ι)
    have := hz i
    rw [h0] at this
    exact lt_irrefl _ this
  have h1 := hb' (r : ℂ) (det_real_eigen M r x (hne x hx) hMx)
  have h2 := hb (r' : ℂ) (det_real_eigen M r' x' (hne x' hx') hMx')
  rw [Complex.norm_real, Real.norm_of_nonneg hr.le] at h1
  rw [Complex.norm_real, Real.norm_of_nonneg hr'.le] at h2
  linarith

/-- A nonnegative matrix with a positive eigenvalue that has positive eigenvectors on both sides
has it as its largest eigenvalue. -/
theorem isPerron_of_pos (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 ≤ M i j) (r : ℝ) (hr : 0 < r)
    (x y : ι → ℝ) (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hMx : M *ᵥ x = r • x)
    (hyM : y ᵥ* M = r • y) : IsPerron M r := by
  refine ⟨hr, ⟨x, hx, hMx⟩, ⟨y, hy, hyM⟩, fun μ hμ => ?_⟩
  obtain ⟨z, hz, hz0⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hμ
  refine norm_le_of_pos_eigen M hM x hx r hMx μ z hz ?_
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hz0
  exact hz0.symm


/-! ## The Poisson equation is solvable on the mean-zero vectors -/

/-- **`(1 − P₀)x = y` is solvable whenever `π · y = 0`:** the range of `1 − P₀` is the hyperplane
`π^⊥`, by the dimension count (the kernel is the line of `𝟏`). -/
theorem solvable [Nonempty ι] (P0 : Matrix ι ι ℝ) (π : ι → ℝ) (hπ : π ≠ 0)
    (hstat : π ᵥ* P0 = π) (hrow : P0 *ᵥ 1 = 1)
    (hker : ∀ v, P0 *ᵥ v = v → ∃ c : ℝ, v = c • (1 : ι → ℝ)) (y : ι → ℝ) (hy : π ⬝ᵥ y = 0) :
    ∃ x, (1 - P0) *ᵥ x = y := by
  set T : (ι → ℝ) →ₗ[ℝ] (ι → ℝ) := (1 - P0).mulVecLin with hT
  set φ : (ι → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun z => π ⬝ᵥ z
      map_add' := fun a b => dotProduct_add π a b
      map_smul' := fun c a => by simp [dotProduct_smul] } with hφ
  have hker_eq : LinearMap.ker T = ℝ ∙ (1 : ι → ℝ) := by
    ext v
    simp only [LinearMap.mem_ker, hT, Matrix.mulVecLin_apply, Submodule.mem_span_singleton]
    constructor
    · intro hv
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
      obtain ⟨c, hc⟩ := hker v hv.symm
      exact ⟨c, hc.symm⟩
    · rintro ⟨c, rfl⟩
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_smul, hrow, sub_self]
  have h1 : Module.finrank ℝ (LinearMap.ker T) = 1 := by
    rw [hker_eq]
    exact finrank_span_singleton one_ne_zero
  have hle : LinearMap.range T ≤ LinearMap.ker φ := by
    rintro _ ⟨x, rfl⟩
    simp only [LinearMap.mem_ker, hφ, LinearMap.coe_mk, AddHom.coe_mk, hT,
      Matrix.mulVecLin_apply]
    rw [dotProduct_mulVec, Matrix.vecMul_sub, Matrix.vecMul_one, hstat, sub_self,
      zero_dotProduct]
  have hφne : LinearMap.range φ = ⊤ := by
    obtain ⟨i, hi⟩ : ∃ i, π i ≠ 0 := by
      by_contra hh
      push Not at hh
      exact hπ (funext hh)
    rw [LinearMap.range_eq_top]
    intro c
    refine ⟨(c / π i) • Pi.single i 1, ?_⟩
    simp only [hφ, LinearMap.coe_mk, AddHom.coe_mk, dotProduct_smul, smul_eq_mul,
      dotProduct_single, mul_one]
    field_simp
  have h2 : Module.finrank ℝ (LinearMap.ker φ) = Fintype.card ι - 1 := by
    have := LinearMap.finrank_range_add_finrank_ker φ
    rw [hφne, finrank_top, Module.finrank_self, Module.finrank_fintype_fun_eq_card] at this
    omega
  have h3 : Module.finrank ℝ (LinearMap.range T) = Fintype.card ι - 1 := by
    have := LinearMap.finrank_range_add_finrank_ker T
    rw [h1, Module.finrank_fintype_fun_eq_card] at this
    omega
  have heq : LinearMap.range T = LinearMap.ker φ :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [h2, h3])
  have hmem : y ∈ LinearMap.range T := by
    rw [heq]
    simpa [hφ] using hy
  obtain ⟨x, hx⟩ := hmem
  refine ⟨x, ?_⟩
  rw [← hx, hT, Matrix.mulVecLin_apply]

/-! ## The weighted walk -/

/-- **A weighted walk at `s = 0`:** nonnegative matrices `P(s)` with the second-order expansion
`P₀ + sP₁ + (s²/2)P₂ + O(s³)`, `P₀` stochastic with a positive stationary law `π`, one-dimensional
kernels and a nonzero adjugate of `1 − P₀` (the root `1` is simple). -/
structure WeightedWalk (P : ℝ → Matrix ι ι ℝ) (P0 P1 P2 : Matrix ι ι ℝ) (π : ι → ℝ) : Prop where
  nonneg : ∀ s i j, 0 ≤ P s i j
  taylor : ∀ i j, (fun s : ℝ => P s i j - (P0 i j + s * P1 i j + s ^ 2 / 2 * P2 i j)) =O[𝓝 0]
    (fun s : ℝ => s ^ 3)
  row : P0 *ᵥ 1 = 1
  stat : π ᵥ* P0 = π
  pos : ∀ i, 0 < π i
  total : ∑ i, π i = 1
  kerR : ∀ v, P0 *ᵥ v = v → ∃ c : ℝ, v = c • (1 : ι → ℝ)
  kerL : ∀ w, w ᵥ* P0 = w → ∃ c : ℝ, w = c • π
  adj : (1 - P0).adjugate ≠ 0

theorem isBigO_cube_at_zero {f : ℝ → ℝ} (h : f =O[𝓝 0] (fun s : ℝ => s ^ 3)) : f 0 = 0 := by
  obtain ⟨c, hc⟩ := h.bound
  have := hc.self_of_nhds
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, norm_zero, mul_zero,
    norm_le_zero_iff] at this
  exact this

theorem isBigO_cube_tendsto {f : ℝ → ℝ} (h : f =O[𝓝 0] (fun s : ℝ => s ^ 3)) :
    Tendsto f (𝓝 0) (𝓝 0) := by
  apply h.trans_tendsto
  have : Tendsto (fun s : ℝ => s ^ 3) (𝓝 0) (𝓝 ((0 : ℝ) ^ 3)) :=
    ((continuous_pow 3).tendsto 0)
  simpa using this

variable {P : ℝ → Matrix ι ι ℝ} {P0 P1 P2 : Matrix ι ι ℝ} {π : ι → ℝ}

theorem WeightedWalk.nonempty (hW : WeightedWalk P P0 P1 P2 π) : Nonempty ι := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := hW.total
  simp at this

theorem WeightedWalk.at_zero (hW : WeightedWalk P P0 P1 P2 π) : P 0 = P0 := by
  ext i j
  have := isBigO_cube_at_zero (hW.taylor i j)
  simp only [zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    zero_div] at this
  linarith

theorem WeightedWalk.entry_tendsto (hW : WeightedWalk P P0 P1 P2 π) (i j : ι) :
    Tendsto (fun s => P s i j) (𝓝 0) (𝓝 (P0 i j)) := by
  have h1 := isBigO_cube_tendsto (hW.taylor i j)
  have h2 : Tendsto (fun s : ℝ => P0 i j + s * P1 i j + s ^ 2 / 2 * P2 i j) (𝓝 0)
      (𝓝 (P0 i j + 0 * P1 i j + 0 ^ 2 / 2 * P2 i j)) := by
    apply Continuous.tendsto
    fun_prop
  have := h1.add h2
  simp only [sub_add_cancel, zero_add, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, zero_div] at this
  exact this

theorem WeightedWalk.continuousAt (hW : WeightedWalk P P0 P1 P2 π) : ContinuousAt P 0 := by
  rw [ContinuousAt, hW.at_zero]
  exact tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => hW.entry_tendsto i j

/-- The rank-one adjugate `adj(1 − P₀) = κ 𝟏 πᵀ`, `κ ≠ 0`. -/
theorem WeightedWalk.adj_rank_one (hW : WeightedWalk P P0 P1 P2 π) :
    ∃ κ : ℝ, κ ≠ 0 ∧ (1 - P0).adjugate = κ • vecMulVec (1 : ι → ℝ) π := by
  haveI := hW.nonempty
  have hdet : (1 - P0).det = 0 := by
    apply (Matrix.exists_mulVec_eq_zero_iff).mp
    refine ⟨1, one_ne_zero, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hW.row, sub_self]
  obtain ⟨κ, hκ⟩ := adjugate_rank_one (1 - P0) 1 π one_ne_zero hdet
    (fun v hv => hW.kerR v (by rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hv
                               exact hv.symm))
    (fun w hw => hW.kerL w (by rw [Matrix.vecMul_sub, Matrix.vecMul_one, sub_eq_zero] at hw
                               exact hw.symm))
  refine ⟨κ, fun h0 => hW.adj ?_, hκ⟩
  rw [hκ, h0, zero_smul]

/-- `P₀` itself has the largest eigenvalue `1`, with eigenvectors `𝟏` and `π`. -/
theorem WeightedWalk.isPerron_zero (hW : WeightedWalk P P0 P1 P2 π) : IsPerron P0 1 := by
  refine isPerron_of_pos P0 (fun i j => ?_) 1 one_pos 1 π (fun _ => one_pos) hW.pos ?_ ?_
  · have := hW.nonneg 0 i j
    rwa [hW.at_zero] at this
  · rw [hW.row, one_smul]
  · rw [hW.stat, one_smul]


/-! ## The largest eigenvalue exists near `s = 0` -/

theorem hasDerivAt_det_sub (P0 : Matrix ι ι ℝ) (lam : ℝ) :
    HasDerivAt (fun l : ℝ => (l • (1 : Matrix ι ι ℝ) - P0).det)
      ((lam • (1 : Matrix ι ι ℝ) - P0).adjugate * 1).trace lam := by
  apply hasDerivAt_det
  intro i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  simpa using ((hasDerivAt_id lam).mul_const ((1 : Matrix ι ι ℝ) i j)).sub_const (P0 i j)

/-- **For `s` near `0` the weighted step has its largest eigenvalue, with positive eigenvectors.**
The root is found by the intermediate value theorem on `det(λ − P(s))` near `λ = 1`, in the region
where every entry of `adj(λ − P(s))` keeps the sign it has at `(0, 1)`. -/
theorem perron_exists (hW : WeightedWalk P P0 P1 P2 π) :
    ∀ᶠ s in 𝓝 (0 : ℝ), ∃ r, IsPerron (P s) r := by
  haveI := hW.nonempty
  obtain ⟨κ, hκ0, hκ⟩ := hW.adj_rank_one
  -- the derivative of `λ ↦ det(λ − P₀)` at `1` is `κ`
  have hF0 : HasDerivAt (fun l : ℝ => (l • (1 : Matrix ι ι ℝ) - P0).det) κ 1 := by
    have h := hasDerivAt_det_sub P0 1
    rw [one_smul, Matrix.mul_one, hκ] at h
    convert h using 1
    simp only [Matrix.trace, Matrix.diag, Matrix.smul_apply, vecMulVec_apply, Pi.one_apply,
      one_mul, smul_eq_mul]
    rw [← Finset.mul_sum, hW.total, mul_one]
  have hdet1 : ((1 : ℝ) • (1 : Matrix ι ι ℝ) - P0).det = 0 := by
    rw [one_smul]
    apply (Matrix.exists_mulVec_eq_zero_iff).mp
    refine ⟨1, one_ne_zero, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hW.row, sub_self]
  -- the sign of `det(λ − P₀)` near `λ = 1`
  have hslope := hF0.tendsto_slope_zero
  have hball : ∀ᶠ t in 𝓝[≠] (0 : ℝ),
      t⁻¹ • (((1 + t) • (1 : Matrix ι ι ℝ) - P0).det - ((1 : ℝ) • (1 : Matrix ι ι ℝ) - P0).det) ∈
        Metric.ball κ (|κ| / 2) :=
    hslope (Metric.ball_mem_nhds κ (by positivity))
  obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff.mp (eventually_nhdsWithin_iff.mp hball)
  have hsign : ∀ t : ℝ, t ≠ 0 → |t| < δ →
      0 < κ * (t⁻¹ * ((1 + t) • (1 : Matrix ι ι ℝ) - P0).det) := by
    intro t ht0 htd
    have := hδb (by rw [Real.dist_eq, sub_zero]; exact htd) ht0
    rw [hdet1, sub_zero, Metric.mem_ball, Real.dist_eq, smul_eq_mul] at this
    rcases lt_or_gt_of_ne hκ0 with hneg | hpos
    · rw [abs_of_neg hneg] at this
      have := abs_lt.mp this
      nlinarith
    · rw [abs_of_pos hpos] at this
      have := abs_lt.mp this
      nlinarith
  -- the adjugate keeps its sign near `(0, 1)`
  have hPc := hW.continuousAt
  have hGc : ContinuousAt (fun p : ℝ × ℝ => (p.2 • (1 : Matrix ι ι ℝ) - P p.1).adjugate)
      ((0 : ℝ), (1 : ℝ)) := by
    have hM : ContinuousAt (fun p : ℝ × ℝ => p.2 • (1 : Matrix ι ι ℝ) - P p.1)
        ((0 : ℝ), (1 : ℝ)) := by
      have h1 : ContinuousAt (fun p : ℝ × ℝ => P p.1) ((0 : ℝ), (1 : ℝ)) :=
        ContinuousAt.comp_of_eq hPc continuousAt_fst rfl
      have h2 : ContinuousAt (fun p : ℝ × ℝ => p.2 • (1 : Matrix ι ι ℝ)) ((0 : ℝ), (1 : ℝ)) :=
        (continuous_snd.smul continuous_const).continuousAt
      exact h2.sub h1
    exact (continuous_id.matrix_adjugate).continuousAt.comp hM
  have hG0 : (((0 : ℝ), (1 : ℝ)).2 • (1 : Matrix ι ι ℝ) - P ((0 : ℝ), (1 : ℝ)).1).adjugate =
      κ • vecMulVec (1 : ι → ℝ) π := by
    simp only [one_smul, hW.at_zero]
    exact hκ
  have hpos_ev : ∀ᶠ p in 𝓝 ((0 : ℝ), (1 : ℝ)),
      ∀ i j, 0 < κ * (p.2 • (1 : Matrix ι ι ℝ) - P p.1).adjugate i j := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    have hcont : ContinuousAt
        (fun p : ℝ × ℝ => κ * (p.2 • (1 : Matrix ι ι ℝ) - P p.1).adjugate i j)
        ((0 : ℝ), (1 : ℝ)) := by
      have he : ContinuousAt (fun p : ℝ × ℝ => (p.2 • (1 : Matrix ι ι ℝ) - P p.1).adjugate i j)
          ((0 : ℝ), (1 : ℝ)) := by
        have := (continuous_apply j).continuousAt.comp
          ((continuous_apply i).continuousAt.comp hGc)
        exact this
      exact continuousAt_const.mul he
    have h0 : 0 < κ * (((0 : ℝ), (1 : ℝ)).2 • (1 : Matrix ι ι ℝ) -
        P ((0 : ℝ), (1 : ℝ)).1).adjugate i j := by
      rw [hG0]
      simp only [Matrix.smul_apply, vecMulVec_apply, Pi.one_apply, one_mul, smul_eq_mul]
      have := hW.pos j
      have : 0 < κ * κ := mul_self_pos.mpr hκ0
      nlinarith
    exact hcont.tendsto.eventually (lt_mem_nhds h0)
  obtain ⟨ε, hε, hεb⟩ := Metric.eventually_nhds_iff.mp hpos_ev
  -- the width of the interval
  set δ₁ : ℝ := min (δ / 2) (min (ε / 2) (1 / 2)) with hδ₁
  have hδ₁pos : 0 < δ₁ := by
    simp only [hδ₁, lt_min_iff]
    refine ⟨by linarith, by linarith, by norm_num⟩
  have hδ₁δ : δ₁ < δ := by
    have : δ₁ ≤ δ / 2 := min_le_left _ _
    linarith
  have hδ₁ε : δ₁ < ε := by
    have : δ₁ ≤ ε / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
    linarith
  have hδ₁h : δ₁ ≤ 1 / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  have hup : 0 < κ * ((1 + δ₁) • (1 : Matrix ι ι ℝ) - P0).det := by
    have := hsign δ₁ hδ₁pos.ne' (by rw [abs_of_pos hδ₁pos]; exact hδ₁δ)
    have hinv : 0 < δ₁⁻¹ := inv_pos.mpr hδ₁pos
    have e : κ * (δ₁⁻¹ * ((1 + δ₁) • (1 : Matrix ι ι ℝ) - P0).det) =
        δ₁⁻¹ * (κ * ((1 + δ₁) • (1 : Matrix ι ι ℝ) - P0).det) := by ring
    rw [e] at this
    exact pos_of_mul_pos_right this hinv.le
  have hdown : κ * ((1 - δ₁) • (1 : Matrix ι ι ℝ) - P0).det < 0 := by
    have := hsign (-δ₁) (by simp [hδ₁pos.ne']) (by rw [abs_neg, abs_of_pos hδ₁pos]; exact hδ₁δ)
    have e : κ * ((-δ₁)⁻¹ * ((1 + -δ₁) • (1 : Matrix ι ι ℝ) - P0).det) =
        -(δ₁⁻¹ * (κ * ((1 - δ₁) • (1 : Matrix ι ι ℝ) - P0).det)) := by
      rw [inv_neg, ← sub_eq_add_neg]
      ring
    rw [e] at this
    have hinv : 0 < δ₁⁻¹ := inv_pos.mpr hδ₁pos
    have h2 : δ₁⁻¹ * (κ * ((1 - δ₁) • (1 : Matrix ι ι ℝ) - P0).det) < 0 := by linarith
    by_contra hc
    push Not at hc
    have := mul_nonneg hinv.le hc
    linarith
  -- the two signs persist for small `s`
  have hcs : ∀ c : ℝ, ContinuousAt (fun s => κ * (c • (1 : Matrix ι ι ℝ) - P s).det) 0 := by
    intro c
    exact continuousAt_const.mul
      ((continuous_id.matrix_det).continuousAt.comp (continuousAt_const.sub hPc))
  have hup_ev : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < κ * ((1 + δ₁) • (1 : Matrix ι ι ℝ) - P s).det := by
    have h0 : 0 < κ * ((1 + δ₁) • (1 : Matrix ι ι ℝ) - P 0).det := by rw [hW.at_zero]; exact hup
    exact (hcs (1 + δ₁)).tendsto.eventually (lt_mem_nhds h0)
  have hdown_ev : ∀ᶠ s in 𝓝 (0 : ℝ), κ * ((1 - δ₁) • (1 : Matrix ι ι ℝ) - P s).det < 0 := by
    have h0 : κ * ((1 - δ₁) • (1 : Matrix ι ι ℝ) - P 0).det < 0 := by rw [hW.at_zero]; exact hdown
    exact (hcs (1 - δ₁)).tendsto.eventually (gt_mem_nhds h0)
  have hsmall : ∀ᶠ s in 𝓝 (0 : ℝ), |s| < ε := by
    have := Metric.ball_mem_nhds (0 : ℝ) hε
    filter_upwards [this] with s hs
    rwa [Metric.mem_ball, Real.dist_eq, sub_zero] at hs
  filter_upwards [hup_ev, hdown_ev, hsmall] with s hs1 hs2 hs3
  -- the root by the intermediate value theorem
  have hcontl : ContinuousOn (fun l : ℝ => κ * (l • (1 : Matrix ι ι ℝ) - P s).det)
      (Set.Icc (1 - δ₁) (1 + δ₁)) := by
    apply Continuous.continuousOn
    exact continuous_const.mul
      (((continuous_id.smul continuous_const).sub continuous_const).matrix_det)
  obtain ⟨l, hl, hl0⟩ := intermediate_value_Ioo (by linarith) hcontl ⟨hs2, hs1⟩
  have hdetl : (l • (1 : Matrix ι ι ℝ) - P s).det = 0 := by
    have : κ * (l • (1 : Matrix ι ι ℝ) - P s).det = 0 := hl0
    exact (mul_eq_zero.mp this).resolve_left hκ0
  have hlpos : 0 < l := by
    have := hl.1
    linarith
  have hdist : dist (s, l) ((0 : ℝ), (1 : ℝ)) < ε := by
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq, sub_zero, max_lt_iff]
    refine ⟨hs3, ?_⟩
    rw [abs_lt]
    constructor <;> linarith [hl.1, hl.2]
  have hA := hεb hdist
  simp only at hA
  set A := (l • (1 : Matrix ι ι ℝ) - P s).adjugate with hAdef
  have hMA : (l • (1 : Matrix ι ι ℝ) - P s) * A = 0 := by
    rw [hAdef, mul_adjugate, hdetl, zero_smul]
  have hAM : A * (l • (1 : Matrix ι ι ℝ) - P s) = 0 := by
    rw [hAdef, adjugate_mul, hdetl, zero_smul]
  refine ⟨l, isPerron_of_pos (P s) (hW.nonneg s) l hlpos (κ • (A *ᵥ 1)) (κ • ((1 : ι → ℝ) ᵥ* A))
    ?_ ?_ ?_ ?_⟩
  · intro i
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, Pi.one_apply, mul_one]
    rw [Finset.mul_sum]
    exact Finset.sum_pos (fun j _ => hA i j) Finset.univ_nonempty
  · intro j
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct, Pi.one_apply, one_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_pos (fun i _ => hA i j) Finset.univ_nonempty
  · have h0 : (l • (1 : Matrix ι ι ℝ) - P s) *ᵥ (A *ᵥ 1) = 0 := by
      rw [Matrix.mulVec_mulVec, hMA, Matrix.zero_mulVec]
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
    rw [Matrix.mulVec_smul, ← h0, smul_comm]
  · have h0 : ((1 : ι → ℝ) ᵥ* A) ᵥ* (l • (1 : Matrix ι ι ℝ) - P s) = 0 := by
      rw [Matrix.vecMul_vecMul, hAM, Matrix.vecMul_zero]
    rw [Matrix.vecMul_sub, Matrix.vecMul_smul, Matrix.vecMul_one, sub_eq_zero] at h0
    rw [Matrix.smul_vecMul, ← h0, smul_comm]

open Classical in
/-- The largest eigenvalue of `P s` where it exists (and `1` elsewhere). -/
noncomputable def perronRoot (P : ℝ → Matrix ι ι ℝ) (s : ℝ) : ℝ :=
  if h : ∃ r, IsPerron (P s) r then Classical.choose h else 1

theorem perronRoot_spec (hW : WeightedWalk P P0 P1 P2 π) :
    ∀ᶠ s in 𝓝 (0 : ℝ), IsPerron (P s) (perronRoot P s) := by
  filter_upwards [perron_exists hW] with s hs
  rw [perronRoot, dif_pos hs]
  exact Classical.choose_spec hs

theorem perronRoot_zero (hW : WeightedWalk P P0 P1 P2 π) : perronRoot P 0 = 1 := by
  haveI := hW.nonempty
  have h1 : IsPerron (P 0) 1 := by rw [hW.at_zero]; exact hW.isPerron_zero
  have h2 : IsPerron (P 0) (perronRoot P 0) := (perronRoot_spec hW).self_of_nhds
  exact perron_unique (P 0) _ _ h2 h1

/-! ## The expansion of the largest eigenvalue -/

theorem tendsto_isBigO_one {f : ℝ → ℝ} {c : ℝ} (h : Tendsto f (𝓝 0) (𝓝 c)) :
    f =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) :=
  h.isBigO_one (F := ℝ)

/-- **The largest eigenvalue to second order:** `ρ(s) = 1 + sv + s²λ₂ + O(s³)` with `v = π P₁ 𝟏`
and `λ₂ = π P₁ g + π P₂ 𝟏 / 2`, `g` the Poisson solution with `π g = 0`. -/
theorem perron_expansion (hW : WeightedWalk P P0 P1 P2 π) (g : ι → ℝ)
    (hg : (1 - P0) *ᵥ g = P1 *ᵥ 1 - (π ⬝ᵥ (P1 *ᵥ 1)) • 1) (hπg : π ⬝ᵥ g = 0) :
    (fun s => perronRoot P s - (1 + s * (π ⬝ᵥ (P1 *ᵥ 1)) +
      s ^ 2 * (π ⬝ᵥ (P1 *ᵥ g) + (π ⬝ᵥ (P2 *ᵥ 1)) / 2))) =O[𝓝 0] (fun s => s ^ 3) := by
  haveI := hW.nonempty
  set v := π ⬝ᵥ (P1 *ᵥ 1) with hv
  set l2 := π ⬝ᵥ (P1 *ᵥ g) + (π ⬝ᵥ (P2 *ᵥ 1)) / 2 with hl2
  have hπ1 : π ⬝ᵥ (1 : ι → ℝ) = 1 := by
    simp only [dotProduct, Pi.one_apply, mul_one]
    exact hW.total
  have hπne : π ≠ 0 := by
    intro h
    have := hW.pos (Classical.arbitrary ι)
    rw [h] at this
    exact lt_irrefl _ this
  obtain ⟨x2, hx2⟩ := solvable P0 π hπne hW.stat hW.row hW.kerR
    (P1 *ᵥ g + (1 / 2 : ℝ) • (P2 *ᵥ 1) - v • g - l2 • 1) (by
      simp only [dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul, hπg, hπ1]
      rw [hl2]
      ring)
  set xt : ℝ → ι → ℝ := fun s => 1 + s • g + s ^ 2 • x2 with hxt
  set lt : ℝ → ℝ := fun s => 1 + s * v + s ^ 2 * l2 with hlt
  set e : ℝ → ι → ℝ := fun s => P s *ᵥ xt s - lt s • xt s with he
  -- (A) each component of the error is `O(s³)`
  have hA : ∀ i, (fun s => e s i) =O[𝓝 0] (fun s => s ^ 3) := by
    intro i
    set c3 := (P1 *ᵥ x2) i + (P2 *ᵥ g) i / 2 - v * x2 i - l2 * g i with hc3
    set c4 := (P2 *ᵥ x2) i / 2 - l2 * x2 i with hc4
    have hgi := congrFun hg i
    have hx2i := congrFun hx2 i
    have hri := congrFun hW.row i
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Pi.add_apply, Pi.one_apply, mul_one] at hgi hx2i hri
    have hT : ∀ s : ℝ, ((P0 + s • P1 + (s ^ 2 / 2) • P2) *ᵥ xt s) i =
        (P0 *ᵥ 1) i + s * (P0 *ᵥ g) i + s ^ 2 * (P0 *ᵥ x2) i +
          s * ((P1 *ᵥ 1) i + s * (P1 *ᵥ g) i + s ^ 2 * (P1 *ᵥ x2) i) +
          s ^ 2 / 2 * ((P2 *ᵥ 1) i + s * (P2 *ᵥ g) i + s ^ 2 * (P2 *ᵥ x2) i) := by
      intro s
      simp only [hxt, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_add,
        Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hsplit : ∀ s : ℝ, e s i = (∑ j, (P s i j - (P0 i j + s * P1 i j + s ^ 2 / 2 * P2 i j)) *
        xt s j) + s ^ 3 * (c3 + s * c4) := by
      intro s
      have hdecomp : (P s *ᵥ xt s) i = (∑ j, (P s i j - (P0 i j + s * P1 i j +
          s ^ 2 / 2 * P2 i j)) * xt s j) + ((P0 + s • P1 + (s ^ 2 / 2) • P2) *ᵥ xt s) i := by
        simp only [Matrix.mulVec, dotProduct, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      simp only [he, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hdecomp, hT s]
      simp only [hxt, hlt, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply]
      rw [hc3, hc4]
      linear_combination hri - s * hgi - s ^ 2 * hx2i
    have hR : (fun s : ℝ => ∑ j, (P s i j - (P0 i j + s * P1 i j + s ^ 2 / 2 * P2 i j)) *
        xt s j) =O[𝓝 0] (fun s => s ^ 3) := by
      refine Asymptotics.IsBigO.fun_sum fun j _ => ?_
      have hx : (fun s => xt s j) =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) := by
        apply tendsto_isBigO_one (c := xt 0 j)
        apply Continuous.tendsto
        simp only [hxt, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply]
        fun_prop
      have := (hW.taylor i j).mul hx
      simpa using this
    have hpoly : (fun s : ℝ => s ^ 3 * (c3 + s * c4)) =O[𝓝 0] (fun s => s ^ 3) := by
      have hb : (fun s : ℝ => c3 + s * c4) =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) := by
        apply tendsto_isBigO_one (c := c3 + 0 * c4)
        apply Continuous.tendsto
        fun_prop
      have := (Asymptotics.isBigO_refl (fun s : ℝ => s ^ 3) (𝓝 0)).mul hb
      simpa using this
    have hsum := hR.add hpoly
    refine hsum.congr' (Filter.Eventually.of_forall fun s => ?_) EventuallyEq.rfl
    exact (hsplit s).symm
  -- (B) the defect bound with the positive left eigenvector
  have hxt_tend : ∀ i, Tendsto (fun s => xt s i) (𝓝 0) (𝓝 1) := by
    intro i
    have : Tendsto (fun s : ℝ => 1 + s * g i + s ^ 2 * x2 i) (𝓝 0)
        (𝓝 (1 + 0 * g i + 0 ^ 2 * x2 i)) := by
      apply Continuous.tendsto
      fun_prop
    simpa [hxt] using this
  have hxt_half : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ i, 1 / 2 ≤ xt s i := by
    rw [Filter.eventually_all]
    intro i
    exact ((hxt_tend i).eventually (lt_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))).mono
      fun s hs => hs.le
  have hB : ∀ᶠ s in 𝓝 (0 : ℝ), ‖perronRoot P s - lt s‖ ≤ 2 * ‖∑ i, |e s i|‖ := by
    filter_upwards [perronRoot_spec hW, hxt_half] with s hs hhalf
    obtain ⟨-, -, ⟨y, hy, hyP⟩, -⟩ := hs
    have hid := left_eigen_defect (P s) y (xt s) (perronRoot P s) (lt s) hyP
    have hSy : 0 < ∑ i, y i := Finset.sum_pos (fun i _ => hy i) Finset.univ_nonempty
    have hyx : (1 / 2) * ∑ i, y i ≤ y ⬝ᵥ xt s := by
      simp only [dotProduct]
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      have := hhalf i
      nlinarith [hy i]
    have hye : |y ⬝ᵥ (P s *ᵥ xt s - lt s • xt s)| ≤ (∑ i, y i) * ∑ i, |e s i| := by
      calc |y ⬝ᵥ (P s *ᵥ xt s - lt s • xt s)| = |∑ i, y i * e s i| := by
            simp only [dotProduct, he]
        _ ≤ ∑ i, |y i * e s i| := Finset.abs_sum_le_sum_abs _ _
        _ = ∑ i, y i * |e s i| := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [abs_mul, abs_of_pos (hy i)]
        _ ≤ ∑ i, y i * ∑ k, |e s k| := by
            refine Finset.sum_le_sum fun i _ => ?_
            refine mul_le_mul_of_nonneg_left ?_ (hy i).le
            exact Finset.single_le_sum (f := fun k => |e s k|) (fun k _ => abs_nonneg _)
              (Finset.mem_univ i)
        _ = (∑ i, y i) * ∑ i, |e s i| := by rw [Finset.sum_mul]
    have hpos : 0 < y ⬝ᵥ xt s := lt_of_lt_of_le (by positivity) hyx
    have hSe : 0 ≤ ∑ i, |e s i| := Finset.sum_nonneg fun i _ => abs_nonneg _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hSe]
    have habs : |perronRoot P s - lt s| * (y ⬝ᵥ xt s) ≤ (∑ i, y i) * ∑ i, |e s i| := by
      rw [← abs_of_pos hpos, ← abs_mul, hid]
      exact hye
    have h2 : |perronRoot P s - lt s| * ((1 / 2) * ∑ i, y i) ≤
        |perronRoot P s - lt s| * (y ⬝ᵥ xt s) :=
      mul_le_mul_of_nonneg_left hyx (abs_nonneg _)
    have h3 : |perronRoot P s - lt s| * ((1 / 2) * ∑ i, y i) ≤ (∑ i, y i) * ∑ i, |e s i| :=
      h2.trans habs
    nlinarith
  -- (C) conclude
  have hE : (fun s => ∑ i, |e s i|) =O[𝓝 0] (fun s => s ^ 3) :=
    Asymptotics.IsBigO.fun_sum fun i _ => (hA i).abs_left
  have hC : (fun s => perronRoot P s - lt s) =O[𝓝 0] (fun s => ∑ i, |e s i|) :=
    Asymptotics.IsBigO.of_bound 2 hB
  exact hC.trans hE

/-! ## The logarithm of the largest eigenvalue -/

theorem abs_log_one_add_le (w : ℝ) (hw : |w| ≤ 1 / 2) : |Real.log (1 + w)| ≤ 2 * |w| := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -w) (by rw [abs_neg]; linarith) 0
  simp only [Finset.range_zero, Finset.sum_empty, zero_add, sub_neg_eq_add, abs_neg,
    pow_one] at h
  have hpos : 0 < 1 - |w| := by linarith
  have : |w| / (1 - |w|) ≤ 2 * |w| := by
    rw [div_le_iff₀ hpos]
    nlinarith [abs_nonneg w]
  exact h.trans this

theorem abs_log_one_add_sub_le (z : ℝ) (hz : |z| ≤ 1 / 2) :
    |Real.log (1 + z) - (z - z ^ 2 / 2)| ≤ 2 * |z| ^ 3 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -z) (by rw [abs_neg]; linarith) 2
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    sub_neg_eq_add, abs_neg] at h
  have hpos : 0 < 1 - |z| := by linarith
  have e : Real.log (1 + z) - (z - z ^ 2 / 2) =
      (-z) ^ (0 + 1) / ((0 : ℕ) + 1 : ℝ) + (-z) ^ (1 + 1) / ((1 : ℕ) + 1 : ℝ) +
        Real.log (1 + z) := by
    push_cast
    ring
  rw [e]
  have : |z| ^ (2 + 1) / (1 - |z|) ≤ 2 * |z| ^ 3 := by
    rw [div_le_iff₀ hpos]
    have h3 : 0 ≤ |z| ^ 3 := by positivity
    have h4 : 0 ≤ 1 - 2 * |z| := by linarith
    have h5 := mul_nonneg h3 h4
    have e3 : |z| ^ (2 + 1) = |z| ^ 3 := by norm_num
    rw [e3]
    nlinarith
  exact h.trans this

/-- **Proposition 71, in general.** For the weighted walk, the logarithm of the largest eigenvalue
has the derivative `v = π P₁ 𝟏` at `s = 0` (the stationary mean of the weight per step), and
`log ρ(s) = sv + (s²/2)σ² + O(s³)` with `σ² = π P₂ 𝟏 + 2 π P₁ g − v²` (the asymptotic variance of
the weight in its Poisson form, `g` the solution of the Poisson equation with `π g = 0`). -/
theorem perron_log (hW : WeightedWalk P P0 P1 P2 π) (g : ι → ℝ)
    (hg : (1 - P0) *ᵥ g = P1 *ᵥ 1 - (π ⬝ᵥ (P1 *ᵥ 1)) • 1) (hπg : π ⬝ᵥ g = 0) :
    HasDerivAt (fun s => Real.log (perronRoot P s)) (π ⬝ᵥ (P1 *ᵥ 1)) 0 ∧
    (fun s => Real.log (perronRoot P s) - (s * (π ⬝ᵥ (P1 *ᵥ 1)) + s ^ 2 / 2 *
      (π ⬝ᵥ (P2 *ᵥ 1) + 2 * (π ⬝ᵥ (P1 *ᵥ g)) - (π ⬝ᵥ (P1 *ᵥ 1)) ^ 2))) =O[𝓝 0]
      (fun s => s ^ 3) := by
  set v := π ⬝ᵥ (P1 *ᵥ 1) with hv
  set l2 := π ⬝ᵥ (P1 *ᵥ g) + (π ⬝ᵥ (P2 *ᵥ 1)) / 2 with hl2
  have hE := perron_expansion hW g hg hπg
  rw [← hv, ← hl2] at hE
  set ρ := perronRoot P with hρ
  have hρ0 : ρ 0 = 1 := perronRoot_zero hW
  set lt : ℝ → ℝ := fun s => 1 + s * v + s ^ 2 * l2 with hlt
  -- the derivative
  have hderiv : HasDerivAt ρ v 0 := by
    rw [hasDerivAt_iff_isLittleO]
    have h1 : (fun s => ρ s - lt s) =o[𝓝 0] (fun s : ℝ => s) :=
      hE.trans_isLittleO (Asymptotics.isLittleO_pow_id (by norm_num))
    have h2 : (fun s : ℝ => s ^ 2 * l2) =o[𝓝 0] (fun s : ℝ => s) :=
      ((Asymptotics.isLittleO_pow_id (n := 2) (by norm_num)).mul_isBigO
        (Asymptotics.isBigO_const_const l2 one_ne_zero (𝓝 0))).congr_right (by simp)
    have h3 := h1.add h2
    refine h3.congr' (Filter.Eventually.of_forall fun s => ?_) (Filter.Eventually.of_forall
      fun s => by simp)
    simp only [hρ0, hlt, sub_zero, smul_eq_mul]
    ring
  refine ⟨?_, ?_⟩
  · have := hderiv.log (by rw [hρ0]; norm_num)
    rwa [hρ0, div_one] at this
  -- the second order
  have hlt_tend : Tendsto lt (𝓝 0) (𝓝 1) := by
    have : Tendsto lt (𝓝 0) (𝓝 (1 + 0 * v + 0 ^ 2 * l2)) := by
      apply Continuous.tendsto
      simp only [hlt]
      fun_prop
    simpa using this
  have hlt_pos : ∀ᶠ s in 𝓝 (0 : ℝ), 1 / 2 < lt s :=
    hlt_tend.eventually (lt_mem_nhds (by norm_num))
  have hρ_pos : ∀ᶠ s in 𝓝 (0 : ℝ), 0 < ρ s := by
    filter_upwards [perronRoot_spec hW] with s hs
    exact hs.1
  -- part I: `log ρ − log lt`
  set w : ℝ → ℝ := fun s => (ρ s - lt s) / lt s with hw
  have hw_big : w =O[𝓝 0] (fun s => s ^ 3) := by
    have hinv : (fun s => (lt s)⁻¹) =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) :=
      tendsto_isBigO_one (hlt_tend.inv₀ one_ne_zero)
    have := hE.mul hinv
    simpa [hw, div_eq_mul_inv] using this
  have hw_tend : Tendsto w (𝓝 0) (𝓝 0) := by
    apply hw_big.trans_tendsto
    have : Tendsto (fun s : ℝ => s ^ 3) (𝓝 0) (𝓝 ((0 : ℝ) ^ 3)) := (continuous_pow 3).tendsto 0
    simpa using this
  have hw_small : ∀ᶠ s in 𝓝 (0 : ℝ), |w s| ≤ 1 / 2 := by
    have := hw_tend.eventually (Metric.closedBall_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [this] with s hs
    rwa [Real.dist_eq, sub_zero] at hs
  have hI : (fun s => Real.log (ρ s) - Real.log (lt s)) =O[𝓝 0] (fun s => s ^ 3) := by
    have hb : ∀ᶠ s in 𝓝 (0 : ℝ), ‖Real.log (ρ s) - Real.log (lt s)‖ ≤ 2 * ‖w s‖ := by
      filter_upwards [hw_small, hρ_pos, hlt_pos] with s hs1 hs2 hs3
      have hlt0 : lt s ≠ 0 := by linarith
      have e : Real.log (ρ s) - Real.log (lt s) = Real.log (1 + w s) := by
        rw [← Real.log_div hs2.ne' hlt0]
        congr 1
        simp only [hw]
        field_simp
        ring
      rw [Real.norm_eq_abs, Real.norm_eq_abs, e]
      exact abs_log_one_add_le (w s) hs1
    exact (Asymptotics.IsBigO.of_bound 2 hb).trans hw_big
  -- part II: `log lt − (sv + s²σ²/2)`
  set z : ℝ → ℝ := fun s => s * v + s ^ 2 * l2 with hz
  have hz_big : z =O[𝓝 0] (fun s : ℝ => s) := by
    have hb : (fun s : ℝ => v + s * l2) =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) := by
      apply tendsto_isBigO_one (c := v + 0 * l2)
      apply Continuous.tendsto
      fun_prop
    have := (Asymptotics.isBigO_refl (fun s : ℝ => s) (𝓝 0)).mul hb
    refine this.congr' (Filter.Eventually.of_forall fun s => ?_) (Filter.Eventually.of_forall
      fun s => by simp)
    simp only [hz]
    ring
  have hz_tend : Tendsto z (𝓝 0) (𝓝 0) := by
    have : Tendsto z (𝓝 0) (𝓝 (0 * v + 0 ^ 2 * l2)) := by
      apply Continuous.tendsto
      simp only [hz]
      fun_prop
    simpa using this
  have hz_small : ∀ᶠ s in 𝓝 (0 : ℝ), |z s| ≤ 1 / 2 := by
    have := hz_tend.eventually (Metric.closedBall_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2))
    filter_upwards [this] with s hs
    rwa [Real.dist_eq, sub_zero] at hs
  have hIIa : (fun s => Real.log (lt s) - (z s - (z s) ^ 2 / 2)) =O[𝓝 0] (fun s => s ^ 3) := by
    have hb : ∀ᶠ s in 𝓝 (0 : ℝ), ‖Real.log (lt s) - (z s - (z s) ^ 2 / 2)‖ ≤ 2 * ‖(z s) ^ 3‖ := by
      filter_upwards [hz_small] with s hs
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_pow]
      have e : lt s = 1 + z s := by simp only [hlt, hz]; ring
      rw [e]
      exact abs_log_one_add_sub_le (z s) hs
    have hz3 : (fun s => (z s) ^ 3) =O[𝓝 0] (fun s : ℝ => s ^ 3) := hz_big.pow 3
    exact (Asymptotics.IsBigO.of_bound 2 hb).trans hz3
  have hIIb : (fun s => (z s - (z s) ^ 2 / 2) - (s * v + s ^ 2 / 2 *
      (π ⬝ᵥ (P2 *ᵥ 1) + 2 * (π ⬝ᵥ (P1 *ᵥ g)) - v ^ 2))) =O[𝓝 0] (fun s => s ^ 3) := by
    have hb : (fun s : ℝ => -(v * l2) - s * (l2 ^ 2 / 2)) =O[𝓝 0] (fun _ : ℝ => (1 : ℝ)) := by
      apply tendsto_isBigO_one (c := -(v * l2) - 0 * (l2 ^ 2 / 2))
      apply Continuous.tendsto
      fun_prop
    have := (Asymptotics.isBigO_refl (fun s : ℝ => s ^ 3) (𝓝 0)).mul hb
    refine this.congr' (Filter.Eventually.of_forall fun s => ?_) (Filter.Eventually.of_forall
      fun s => by simp)
    simp only [hz, hl2]
    ring
  have hsum := (hI.add hIIa).add hIIb
  refine hsum.congr' (Filter.Eventually.of_forall fun s => ?_) EventuallyEq.rfl
  simp only [hv]
  ring

end Perron

end Comparison

end
