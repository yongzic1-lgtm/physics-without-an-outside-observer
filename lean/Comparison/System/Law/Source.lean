import Comparison.System.Postulates
import Comparison.Law.Source
import Comparison.Existence.LogDet

/-!
# The proof system, the law: Proposition 110, the source family and the address of a constant

`Z_{(s,g)}(K; J) = det(I − sK⁻¹J/g)^{−sg}`, `X = K⁻¹J`
(`Law.sourceZ`, `Law/Source.lean`).

* `logSeries_smul`: the logarithm of `det(I − εcB)` (as a formal power series in `ε`, `LogDet.lean`) is
  `−Σ_r c^r ε^r Tr B^r/r`;
* `sourceLog`, `sourceLog_eq`: **`log Z_{(s,g)}(εX) = −sg log det(I − ε(s/g)X) = Σ_{k≥1} s^{k+1}g^{1−k} ε^k
  Tr X^k/k`** as formal power series in `ε`, the logarithm being the one of `logdet_eq_log`;
* the same over `ℂ`: `sourceLogK`, `sourceZC`, `sourceZC_ends`, `logSourceC_first_order`, the direct sum as
  series and near `ε = 0`, and exactly in the integer members;
* `prop_110`: Proposition 110 as one statement over `ℂ`; `Law.source_family_real`: the real case.
-/

open Matrix Polynomial Filter Topology Comparison

namespace Comparison.System

namespace Law

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The logarithm of `det(I − εcB)`**: `logSeries (c • B) = −Σ_{r≥1} c^r ε^r Tr B^r/r`. -/
theorem logSeries_smul {K : Type*} [Field K] [CharZero K] (c : K) (B : Matrix n n K) :
    logSeries (c • B) = PowerSeries.mk fun r => if r = 0 then 0 else -(c ^ r * (B ^ r).trace) / r := by
  ext r
  simp only [logSeries, PowerSeries.coeff_mk, _root_.smul_pow, Matrix.trace_smul, smul_eq_mul]

/-- **The logarithm of the source family**, `Σ_{k≥1} s^{k+1} g^{1−k} ε^k Tr X^k/k`. -/
noncomputable def sourceLog (s g : ℝ) (X : Matrix n n ℝ) : PowerSeries ℝ :=
  PowerSeries.mk fun k => if k = 0 then 0 else s ^ (k + 1) * g ^ ((1 : ℤ) - k) * (X ^ k).trace / k

/-- **`−sg log det(I − ε(s/g)X) = Σ_{k≥1} s^{k+1} g^{1−k} ε^k Tr X^k/k`.** -/
theorem sourceLog_eq (s g : ℝ) (hg : g ≠ 0) (X : Matrix n n ℝ) :
    (-(s * g)) • logSeries ((s / g) • X) = sourceLog s g X := by
  rw [logSeries_smul]
  ext k
  simp only [sourceLog, PowerSeries.coeff_smul, PowerSeries.coeff_mk, smul_eq_mul]
  split_ifs with hk
  · simp
  · rw [zpow_sub₀ hg, zpow_one, zpow_natCast, div_pow]
    have hgk : g ^ k ≠ 0 := pow_ne_zero k hg
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
    field_simp
    ring


/-! ## Over `ℂ`: the theory's `K` and `J` are complex -/

section Complex

/-- **The logarithm of the source family over a field of characteristic zero**,
`Σ_{k≥1} s^{k+1} g^{1−k} ε^k Tr X^k/k`. -/
noncomputable def sourceLogK {K : Type*} [Field K] (s g : K) (X : Matrix n n K) : PowerSeries K :=
  PowerSeries.mk fun k => if k = 0 then 0 else s ^ (k + 1) * g ^ ((1 : ℤ) - k) * (X ^ k).trace / k

/-- **`−sg log det(I − ε(s/g)X) = Σ_{k≥1} s^{k+1} g^{1−k} ε^k Tr X^k/k`** over every field of characteristic
zero (`ℂ` among them). -/
theorem sourceLogK_eq {K : Type*} [Field K] [CharZero K] (s g : K) (hg : g ≠ 0) (X : Matrix n n K) :
    (-(s * g)) • logSeries ((s / g) • X) = sourceLogK s g X := by
  rw [logSeries_smul]
  ext k
  simp only [sourceLogK, PowerSeries.coeff_smul, PowerSeries.coeff_mk, smul_eq_mul]
  split_ifs with hk
  · simp
  · rw [zpow_sub₀ hg, zpow_one, zpow_natCast, div_pow]
    have hgk : g ^ k ≠ 0 := pow_ne_zero k hg
    have hk' : (k : K) ≠ 0 := by exact_mod_cast hk
    field_simp
    ring

/-- `(X ⊕ Y)^k = X^k ⊕ Y^k`. -/
theorem fromBlocks_diag_pow {m : Type*} [Fintype m] [DecidableEq m] {K : Type*} [CommRing K]
    (X : Matrix n n K) (Y : Matrix m m K) (k : ℕ) :
    (fromBlocks X 0 0 Y) ^ k = fromBlocks (X ^ k) 0 0 (Y ^ k) := by
  induction k with
  | zero => simp [Matrix.fromBlocks_one]
  | succ k ih => rw [pow_succ, ih, Matrix.fromBlocks_multiply, pow_succ, pow_succ]; simp

/-- `Tr(X ⊕ Y) = Tr X + Tr Y`. -/
theorem trace_fromBlocks_diag {m : Type*} [Fintype m] [DecidableEq m] {K : Type*} [CommRing K]
    (X : Matrix n n K) (Y : Matrix m m K) : (fromBlocks X 0 0 Y).trace = X.trace + Y.trace := by
  simp [Matrix.trace, Fintype.sum_sum_type]

/-- **The logarithm of a composite on the direct sum is the sum of the logarithms.** -/
theorem sourceLogK_directSum {m : Type*} [Fintype m] [DecidableEq m] {K : Type*} [Field K]
    (s g : K) (X : Matrix n n K) (Y : Matrix m m K) :
    sourceLogK s g (fromBlocks X 0 0 Y) = sourceLogK s g X + sourceLogK s g Y := by
  ext k
  simp only [sourceLogK, PowerSeries.coeff_mk, map_add, fromBlocks_diag_pow, trace_fromBlocks_diag]
  split_ifs <;> ring

/-- **The source family over `ℂ`**, `Z_{(s,g)}(X) = det(I − (s/g)X)^{−sg}` (the principal power). -/
noncomputable def sourceZC (s g : ℂ) (X : Matrix n n ℂ) : ℂ :=
  (det (1 - (s / g) • X)) ^ (-(s * g))

/-- **Several vertices over `ℂ`:** `Z_{(−1,1)} = det(I + X)`. -/
theorem sourceZC_places (X : Matrix n n ℂ) : sourceZC (-1) 1 X = det (1 + X) := by
  rw [sourceZC, show -((-1 : ℂ) * 1) = 1 by norm_num, Complex.cpow_one,
    show ((-1 : ℂ) / 1) = -1 by norm_num, neg_smul, one_smul, sub_neg_eq_add]

/-- **`k` times over `ℂ`:** `Z_{(1,1)} = det(I − X)⁻¹`. -/
theorem sourceZC_times (X : Matrix n n ℂ) : sourceZC 1 1 X = (det (1 - X))⁻¹ := by
  rw [sourceZC, show ((1 : ℂ) / 1) = 1 by norm_num, one_smul, show -((1 : ℂ) * 1) = -1 by norm_num,
    Complex.cpow_neg_one]

/-- Jacobi at the identity over `ℂ`: `d/dε det(I − εX) = −Tr X` at `ε = 0`. -/
theorem det_one_sub_smul_hasDerivAtC (X : Matrix n n ℂ) :
    HasDerivAt (fun ε : ℂ => det (1 - ε • X)) (-trace X) 0 := by
  have h := hasDerivAt_det (𝕜 := ℂ) (M := fun ε : ℂ => 1 - ε • X) (M' := -X) (x := 0)
    (fun i j => by
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply]
      have := ((hasDerivAt_id (0 : ℂ)).mul_const (X i j)).const_sub ((1 : Matrix n n ℂ) i j)
      simpa using this)
  simpa [adjugate_one] using h

/-- `(g : ℂ)⁻¹ → 0` as the real `g → ∞`. -/
theorem tendsto_ofReal_inv_atTop : Tendsto (fun g : ℝ => ((g : ℂ))⁻¹) atTop (𝓝 0) := by
  have h0 : Tendsto (fun r : ℝ => r⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have h2 := (Complex.continuous_ofReal.tendsto 0).comp h0
  simpa [Function.comp_def, Complex.ofReal_inv] using h2

/-- **Two ends over `ℂ`:** `Z_{(1,g)}(X) = det(I − X/g)^{−g} → exp Tr X` as the real `g → ∞`. -/
theorem sourceZC_ends (X : Matrix n n ℂ) :
    Tendsto (fun g : ℝ => sourceZC 1 (g : ℂ) X) atTop (𝓝 (Complex.exp (trace X))) := by
  have hd : HasDerivAt (fun ε : ℂ => det (1 - ε • X)) (-trace X) 0 := det_one_sub_smul_hasDerivAtC X
  have hlog : HasDerivAt (fun ε : ℂ => Complex.log (det (1 - ε • X))) (-trace X) 0 := by
    have := hd.clog (by simp)
    simpa using this
  have hslope := hlog.tendsto_slope_zero
  have hinv : Tendsto (fun g : ℝ => ((g : ℂ))⁻¹) atTop (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨tendsto_ofReal_inv_atTop, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with g hg
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, inv_eq_zero, Complex.ofReal_eq_zero]
    exact hg.ne'
  have h1 := (hslope.comp hinv).neg
  rw [neg_neg] at h1
  have h2 : Tendsto (fun g : ℝ => -((g : ℂ) * Complex.log (det (1 - ((g : ℂ))⁻¹ • X)))) atTop
      (𝓝 (trace X)) := by
    refine h1.congr' (Filter.Eventually.of_forall fun g => ?_)
    simp only [Function.comp_apply, zero_add, zero_smul, sub_zero, det_one, Complex.log_one, inv_inv,
      smul_eq_mul]
  have h3 := (Complex.continuous_exp.tendsto _).comp h2
  have hne : ∀ᶠ g : ℝ in atTop, det (1 - ((g : ℂ))⁻¹ • X) ≠ 0 := by
    have : ∀ᶠ ε in 𝓝 (0 : ℂ), det (1 - ε • X) ≠ 0 :=
      hd.continuousAt.eventually_ne (by simp)
    exact tendsto_ofReal_inv_atTop.eventually this
  refine h3.congr' ?_
  filter_upwards [hne] with g hg
  simp only [Function.comp_apply, sourceZC, one_div]
  rw [Complex.cpow_def_of_ne_zero hg]
  congr 1
  ring

/-- **The first-order coefficient of `log Z_{(s,g)}` over `ℂ` is `s² Tr X`.** -/
theorem logSourceC_first_order (s g : ℂ) (hg : g ≠ 0) (X : Matrix n n ℂ) :
    HasDerivAt (fun ε : ℂ => -(s * g) * Complex.log (det (1 - (ε * (s / g)) • X)))
      (s ^ 2 * trace X) 0 := by
  have h : HasDerivAt (fun ε' : ℂ => det (1 - ε' • X)) (-trace X) ((fun ε : ℂ => ε * (s / g)) 0) := by
    simpa using det_one_sub_smul_hasDerivAtC X
  have hc : HasDerivAt (fun ε : ℂ => ε * (s / g)) (s / g) 0 := by
    simpa using (hasDerivAt_id (0 : ℂ)).mul_const (s / g)
  have hd := h.comp 0 hc
  have h0 : ((fun ε' : ℂ => det (1 - ε' • X)) ∘ fun ε : ℂ => ε * (s / g)) 0 = 1 := by simp
  have hlog := hd.clog (by rw [h0]; exact Complex.one_mem_slitPlane)
  rw [h0, div_one] at hlog
  have hm := hlog.const_mul (-(s * g))
  have hfun : (fun y => -(s * g) * Complex.log (((fun ε' : ℂ => det (1 - ε' • X)) ∘
      fun ε : ℂ => ε * (s / g)) y)) =
      fun ε : ℂ => -(s * g) * Complex.log (det (1 - (ε * (s / g)) • X)) := rfl
  rw [hfun] at hm
  refine hm.congr_deriv ?_
  field_simp

/-- Near `1` a complex number is nonzero with `|arg| < π/2`. -/
theorem eventually_near_one :
    ∀ᶠ z in 𝓝 (1 : ℂ), z ≠ 0 ∧ |Complex.arg z| < Real.pi / 2 := by
  have h1 : ∀ᶠ z in 𝓝 (1 : ℂ), z ≠ 0 := eventually_ne_nhds one_ne_zero
  have hc := (Complex.continuousAt_arg Complex.one_mem_slitPlane).tendsto
  rw [Complex.arg_one] at hc
  have h2 : ∀ᶠ z in 𝓝 (1 : ℂ), Complex.arg z ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
    hc.eventually_mem (Ioo_mem_nhds (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
  filter_upwards [h1, h2] with z hz hz'
  exact ⟨hz, abs_lt.mpr hz'⟩

/-- `ε ↦ det(I − (s/g)(εZ))` tends to `1` at `ε = 0`. -/
theorem det_source_tendsto {k : Type*} [Fintype k] [DecidableEq k] (s g : ℂ) (Z : Matrix k k ℂ) :
    Tendsto (fun ε : ℂ => det (1 - (s / g) • (ε • Z))) (𝓝 0) (𝓝 1) := by
  have hA : Continuous (fun ε : ℂ => (1 - (s / g) • (ε • Z) : Matrix k k ℂ)) := by
    fun_prop
  have hc : Continuous (fun ε : ℂ => det (1 - (s / g) • (ε • Z))) := hA.matrix_det
  have := hc.tendsto 0
  simpa using this

/-- **A composite on the direct sum is the product, over `ℂ`, near `ε = 0`:**
`Z(ε(X ⊕ Y)) = Z(εX)Z(εY)` (both determinants near `1`, where the principal logarithm adds). -/
theorem sourceZC_directSum_near {m : Type*} [Fintype m] [DecidableEq m] (s g : ℂ) (X : Matrix n n ℂ)
    (Y : Matrix m m ℂ) :
    ∀ᶠ ε in 𝓝 (0 : ℂ),
      sourceZC s g (ε • fromBlocks X 0 0 Y) = sourceZC s g (ε • X) * sourceZC s g (ε • Y) := by
  filter_upwards [(det_source_tendsto s g X).eventually eventually_near_one,
    (det_source_tendsto s g Y).eventually eventually_near_one] with ε hx hy
  have h : (1 - (s / g) • (ε • fromBlocks X 0 0 Y) : Matrix (n ⊕ m) (n ⊕ m) ℂ) =
      fromBlocks (1 - (s / g) • (ε • X)) 0 0 (1 - (s / g) • (ε • Y)) := by
    ext (i | i) (j | j) <;>
      simp [Matrix.one_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
        fromBlocks_apply₂₂]
  obtain ⟨ha, ha'⟩ := hx
  obtain ⟨hb, hb'⟩ := hy
  have harg : Complex.arg (det (1 - (s / g) • (ε • X))) + Complex.arg (det (1 - (s / g) • (ε • Y))) ∈
      Set.Ioc (-Real.pi) Real.pi := by
    have := abs_lt.mp ha'
    have := abs_lt.mp hb'
    constructor <;> linarith
  simp only [sourceZC]
  rw [h, det_fromBlocks_zero₂₁, Complex.cpow_def_of_ne_zero (mul_ne_zero ha hb),
    Complex.cpow_def_of_ne_zero ha, Complex.cpow_def_of_ne_zero hb, Complex.log_mul ha hb harg,
    ← Complex.exp_add]
  congr 1
  ring

/-- **The integer members on the direct sum, exactly:** `det(I + X ⊕ Y) = det(I + X)det(I + Y)` and
`det(I − X ⊕ Y)⁻¹ = det(I − X)⁻¹det(I − Y)⁻¹`. -/
theorem sourceZC_directSum_members {m : Type*} [Fintype m] [DecidableEq m] (X : Matrix n n ℂ)
    (Y : Matrix m m ℂ) :
    sourceZC (-1) 1 (fromBlocks X 0 0 Y) = sourceZC (-1) 1 X * sourceZC (-1) 1 Y ∧
    sourceZC 1 1 (fromBlocks X 0 0 Y) = sourceZC 1 1 X * sourceZC 1 1 Y := by
  have h1 : (1 + fromBlocks X 0 0 Y : Matrix (n ⊕ m) (n ⊕ m) ℂ) = fromBlocks (1 + X) 0 0 (1 + Y) := by
    ext (i | i) (j | j) <;>
      simp [Matrix.one_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
        fromBlocks_apply₂₂]
  have h2 : (1 - fromBlocks X 0 0 Y : Matrix (n ⊕ m) (n ⊕ m) ℂ) = fromBlocks (1 - X) 0 0 (1 - Y) := by
    ext (i | i) (j | j) <;>
      simp [Matrix.one_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
        fromBlocks_apply₂₂]
  refine ⟨?_, ?_⟩
  · rw [sourceZC_places, sourceZC_places, sourceZC_places, h1, det_fromBlocks_zero₂₁]
  · rw [sourceZC_times, sourceZC_times, sourceZC_times, h2, det_fromBlocks_zero₂₁, mul_inv]

end Complex

end Law

open Comparison.System.Law

/-- **The source family for real sources** (Proposition 110 for real `X`, `s`, `g`). With `X = K⁻¹J` and
`Z_{(s,g)} = det(I − (s/g)X)^{−sg}`: the logarithm of `det(I − ε(s/g)X)` is the series `logSeries`
(`P′ = P·L′`, `L(0) = 0`, `P(0) = 1`), so `log Z_{(s,g)}(εX) = −sg·L = Σ_k s^{k+1}g^{1−k}ε^k Tr X^k/k`; two ends
`(+1, g → ∞)` give `exp Tr X`, several vertices `(−1, 1)` give `det(I + X)`, `k` times `(+1, 1)` give
`det(I − X)⁻¹`, and the first coefficient of `log Z_{(s,g)}` is `s² Tr X` in every member; a constant is the
coefficient of `Z` on its word: `det(I + diag(j)M) = Σ_S (∏_{x∈S} j_x) det M[S, S]`, and on the polynomials
in the sources the coefficient of `∏_{x∈S} j_x` is `det M[S, S]`; a composite on the direct sum of its lines'
words is the product, `Z(X ⊕ Y) = Z(X)Z(Y)`. -/
theorem Law.source_family_real :
    (∀ (n : Type) [Fintype n] [DecidableEq n] (s g : ℝ) (X : Matrix n n ℝ),
      Law.sourceZ s g X = (det (1 - (s / g) • X)) ^ (-(s * g))) ∧
    (∀ (n : Type) [Fintype n] [DecidableEq n] (s g : ℝ) (X : Matrix n n ℝ), g ≠ 0 →
      (PowerSeries.derivative (R := ℝ)
          ((1 - (Polynomial.X : ℝ[X]) • ((s / g) • X).map Polynomial.C).det : PowerSeries ℝ) =
        ((1 - (Polynomial.X : ℝ[X]) • ((s / g) • X).map Polynomial.C).det : PowerSeries ℝ) *
          PowerSeries.derivative (R := ℝ) (logSeries ((s / g) • X)) ∧
        PowerSeries.constantCoeff (logSeries ((s / g) • X)) = 0) ∧
      (-(s * g)) • logSeries ((s / g) • X) = sourceLog s g X) ∧
    (∀ (n : Type) [Fintype n] [DecidableEq n] (X : Matrix n n ℝ),
      Tendsto (fun g : ℝ => Law.sourceZ 1 g X) atTop (𝓝 (Real.exp (trace X))) ∧
      Law.sourceZ (-1) 1 X = det (1 + X) ∧ Law.sourceZ 1 1 X = (det (1 - X))⁻¹) ∧
    (∀ (n : Type) [Fintype n] [DecidableEq n] (s g : ℝ) (X : Matrix n n ℝ), g ≠ 0 →
      HasDerivAt (fun ε : ℝ => -(s * g) * Real.log (det (1 - (ε * (s / g)) • X)))
        (s ^ 2 * trace X) 0) ∧
    (∀ (n : Type) [Fintype n] [DecidableEq n] (R : Type) [CommRing R] (M : Matrix n n R)
        (j : n → R),
      (1 + diagonal j * M).det =
        ∑ S : Finset n, (∏ i ∈ S, j i) * (M.submatrix (Subtype.val : S → n) Subtype.val).det) ∧
    (∀ (n : Type) [Fintype n] [DecidableEq n] (R : Type) [CommRing R] (M : Matrix n n R)
        (S : Finset n),
      ((1 + diagonal (fun i => (MvPolynomial.X i : MvPolynomial n R)) *
          M.map MvPolynomial.C).det).coeff (∑ i ∈ S, Finsupp.single i 1) =
        (M.submatrix (Subtype.val : S → n) Subtype.val).det) ∧
    (∀ (n m : Type) [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (s g : ℝ)
        (X : Matrix n n ℝ) (Y : Matrix m m ℝ),
      0 ≤ det (1 - (s / g) • X) → 0 ≤ det (1 - (s / g) • Y) →
      Law.sourceZ s g (fromBlocks X 0 0 Y) = Law.sourceZ s g X * Law.sourceZ s g Y) := by
  refine ⟨fun n _ _ s g X => rfl, fun n _ _ s g X hg => ⟨⟨(logdet_eq_log _).1, (logdet_eq_log _).2.1⟩,
      sourceLog_eq s g hg X⟩, fun n _ _ X => ⟨Law.sourceZ_ends X, Law.sourceZ_places X,
      Law.sourceZ_times X⟩, fun n _ _ s g X hg => Law.logSource_first_order s g hg X,
    fun n _ _ R _ M j => Law.det_one_add_diagonal_mul M j, fun n _ _ R _ M S => Law.address_coeff M S,
    fun n m _ _ _ _ s g X Y hX hY => Law.sourceZ_directSum s g X Y hX hY⟩

/-- **Proposition 110, the source family and the address of a constant.** Over `ℂ` (the theory's `K` and `J` are
complex), with `X = K⁻¹J` and `Z_{(s,g)} = det(I − (s/g)X)^{−sg}`: the logarithm of `det(I − ε(s/g)X)` is the series
`logSeries` (`P′ = P·L′`, `L(0) = 0`), so `log Z_{(s,g)}(εX) = −sg·L = Σ_k s^{k+1}g^{1−k}ε^k Tr X^k/k` for every complex
`s` and `g ≠ 0`; two ends `(+1, g → ∞)` give `exp Tr X`, several vertices `(−1, 1)` give `det(I + X)`, `k` times `(+1, 1)`
give `det(I − X)⁻¹`, and the first coefficient of `log Z_{(s,g)}` is `s² Tr X` in every member; a constant is the
coefficient of `Z` on its word: `det(I + diag(j)M) = Σ_S (∏_{x∈S} j_x) det M[S, S]`, and on the polynomials in the
sources the coefficient of `∏_{x∈S} j_x` is `det M[S, S]`; a composite on the direct sum of its lines' words is the
product: `log Z(X ⊕ Y) = log Z(X) + log Z(Y)` as series, `Z(ε(X ⊕ Y)) = Z(εX)Z(εY)` near `ε = 0` in every member, and
exactly for every `X`, `Y` in the members `(−1, 1)` and `(1, 1)`. The real case is `Law.source_family_real`. -/
theorem prop_110 :
    (∀ (n : Type) [Fintype n] [DecidableEq n] (s g : ℂ) (X : Matrix n n ℂ),
      Law.sourceZC s g X = (det (1 - (s / g) • X)) ^ (-(s * g))) ∧
    (∀ (n : Type) [Fintype n] [DecidableEq n] (s g : ℂ) (X : Matrix n n ℂ), g ≠ 0 →
      (PowerSeries.derivative (R := ℂ)
          ((1 - (Polynomial.X : ℂ[X]) • ((s / g) • X).map Polynomial.C).det : PowerSeries ℂ) =
        ((1 - (Polynomial.X : ℂ[X]) • ((s / g) • X).map Polynomial.C).det : PowerSeries ℂ) *
          PowerSeries.derivative (R := ℂ) (logSeries ((s / g) • X)) ∧
        PowerSeries.constantCoeff (logSeries ((s / g) • X)) = 0) ∧
      (-(s * g)) • logSeries ((s / g) • X) = Law.sourceLogK s g X) ∧
    (∀ (n : Type) [Fintype n] [DecidableEq n] (X : Matrix n n ℂ),
      Tendsto (fun g : ℝ => Law.sourceZC 1 (g : ℂ) X) atTop (𝓝 (Complex.exp (trace X))) ∧
      Law.sourceZC (-1) 1 X = det (1 + X) ∧ Law.sourceZC 1 1 X = (det (1 - X))⁻¹) ∧
    (∀ (n : Type) [Fintype n] [DecidableEq n] (s g : ℂ) (X : Matrix n n ℂ), g ≠ 0 →
      HasDerivAt (fun ε : ℂ => -(s * g) * Complex.log (det (1 - (ε * (s / g)) • X)))
        (s ^ 2 * trace X) 0) ∧
    (∀ (n : Type) [Fintype n] [DecidableEq n] (R : Type) [CommRing R] (M : Matrix n n R)
        (j : n → R),
      (1 + diagonal j * M).det =
        ∑ S : Finset n, (∏ i ∈ S, j i) * (M.submatrix (Subtype.val : S → n) Subtype.val).det) ∧
    (∀ (n : Type) [Fintype n] [DecidableEq n] (R : Type) [CommRing R] (M : Matrix n n R)
        (S : Finset n),
      ((1 + diagonal (fun i => (MvPolynomial.X i : MvPolynomial n R)) *
          M.map MvPolynomial.C).det).coeff (∑ i ∈ S, Finsupp.single i 1) =
        (M.submatrix (Subtype.val : S → n) Subtype.val).det) ∧
    (∀ (n m : Type) [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (s g : ℂ)
        (X : Matrix n n ℂ) (Y : Matrix m m ℂ),
      Law.sourceLogK s g (fromBlocks X 0 0 Y) = Law.sourceLogK s g X + Law.sourceLogK s g Y ∧
      (∀ᶠ ε in 𝓝 (0 : ℂ),
        Law.sourceZC s g (ε • fromBlocks X 0 0 Y) = Law.sourceZC s g (ε • X) * Law.sourceZC s g (ε • Y))) ∧
    (∀ (n m : Type) [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] (X : Matrix n n ℂ)
        (Y : Matrix m m ℂ),
      Law.sourceZC (-1) 1 (fromBlocks X 0 0 Y) = Law.sourceZC (-1) 1 X * Law.sourceZC (-1) 1 Y ∧
      Law.sourceZC 1 1 (fromBlocks X 0 0 Y) = Law.sourceZC 1 1 X * Law.sourceZC 1 1 Y) :=
  ⟨fun _ _ _ _ _ _ => rfl, fun _ _ _ s g X hg => ⟨⟨(logdet_eq_log _).1, (logdet_eq_log _).2.1⟩,
      Law.sourceLogK_eq s g hg X⟩, fun _ _ _ X => ⟨Law.sourceZC_ends X, Law.sourceZC_places X,
      Law.sourceZC_times X⟩, fun n _ _ s g X hg => Law.logSourceC_first_order s g hg X,
    fun n _ _ R _ M j => Law.det_one_add_diagonal_mul M j, fun n _ _ R _ M S => Law.address_coeff M S,
    fun n m _ _ _ _ s g X Y => ⟨Law.sourceLogK_directSum s g X Y, Law.sourceZC_directSum_near s g X Y⟩,
    fun n m _ _ _ _ X Y => Law.sourceZC_directSum_members X Y⟩

end Comparison.System
