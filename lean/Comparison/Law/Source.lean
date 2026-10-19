module

public import Comparison.Law.Rule
public import Comparison.Mass.Basic

/-!
# The law, VII: the source family and the address of a constant (Proposition 110)

`Z_{(s,g)}(K; J) = det(I − sK⁻¹J/g)^{−sg}`; write `X = K⁻¹J`. A constant is the coefficient of `Z` on
its word `S`, in the member its shape names; a composite is `Z` on the direct sum of its lines' words.

* `sourceZ s g X`: the family (real `X`, base `det(I − (s/g)X) > 0` where a real power is taken).
* `sourceZ_places`: **several vertices `(−1, 1)`: `Z = det(I + X)`**; `sourceZ_times`: **k times
  `(+1, 1)`: `Z = det(I − X)⁻¹`**; `sourceZ_ends`: **two ends `(+1, g → ∞)`: `Z → exp Tr X`**.
* `logSource_first_order`: **the first-order coefficient of `log Z_{(s,g)}` is `s² Tr X`**, the same
  in every member (`s = ±1`).
* `det_one_add_diagonal_mul`: **the address:** with the sources `J = diag(j)` on the vertices,
  `det(I + diag(j) M) = Σ_S (∏_{x∈S} j_x) det M[S, S]`: the coefficient of the several-vertices member
  on the word `S` is the principal minor of `M = K⁻¹` on `S`.
* `address_coeff`: the same as a coefficient: in `det(I + diag(X) M)` over the polynomials in the
  sources, the coefficient of the word `∏_{x∈S} X_x` is `det M[S, S]`.
* `sourceZ_directSum`: **a composite on the direct sum of its lines' words is the product**,
  `Z(X ⊕ Y) = Z(X) Z(Y)`, in every member.
-/

@[expose] public section

namespace Comparison

open Matrix Filter Topology

namespace Law

section Source

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The source family** `Z_{(s,g)}(X) = det(I − (s/g)X)^{−sg}`. -/
noncomputable def sourceZ (s g : ℝ) (X : Matrix n n ℝ) : ℝ :=
  (det (1 - (s / g) • X)) ^ (-(s * g))

/-- **Several vertices, `(s, g) = (−1, 1)`:** `Z = det(I + X)`. -/
theorem sourceZ_places (X : Matrix n n ℝ) : sourceZ (-1) 1 X = det (1 + X) := by
  rw [sourceZ, show -((-1 : ℝ) * 1) = 1 by norm_num, Real.rpow_one,
    show ((-1 : ℝ) / 1) = -1 by norm_num, neg_smul, one_smul, sub_neg_eq_add]

/-- **k times, `(s, g) = (+1, 1)`:** `Z = det(I − X)⁻¹`. -/
theorem sourceZ_times (X : Matrix n n ℝ) : sourceZ 1 1 X = (det (1 - X))⁻¹ := by
  rw [sourceZ, show ((1 : ℝ) / 1) = 1 by norm_num, one_smul, show -((1 : ℝ) * 1) = -1 by norm_num,
    Real.rpow_neg_one]

/-- Jacobi at the identity: `d/dε det(I − εX) = −Tr X` at `ε = 0`. -/
theorem det_one_sub_smul_hasDerivAt (X : Matrix n n ℝ) :
    HasDerivAt (fun ε : ℝ => det (1 - ε • X)) (-trace X) 0 := by
  have h := hasDerivAt_det (𝕜 := ℝ) (M := fun ε : ℝ => 1 - ε • X) (M' := -X) (x := 0)
    (fun i j => by
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.neg_apply]
      have := ((hasDerivAt_id (0 : ℝ)).mul_const (X i j)).const_sub ((1 : Matrix n n ℝ) i j)
      simpa using this)
  simpa [adjugate_one] using h

/-- **Two ends, `(s, g) = (+1, g → ∞)`:** `Z_{(1,g)}(X) = det(I − X/g)^{−g} → exp Tr X`. -/
theorem sourceZ_ends (X : Matrix n n ℝ) :
    Tendsto (fun g : ℝ => sourceZ 1 g X) atTop (𝓝 (Real.exp (trace X))) := by
  set f : ℝ → ℝ := fun ε => det (1 - ε • X) with hf
  have hd : HasDerivAt f (-trace X) 0 := det_one_sub_smul_hasDerivAt X
  have hf0 : f 0 = 1 := by simp [hf]
  have hlog : HasDerivAt (fun ε => Real.log (f ε)) (-trace X) 0 := by
    have := hd.log (by rw [hf0]; norm_num)
    simpa [hf0] using this
  have hslope := hlog.tendsto_slope_zero
  have hinv : Tendsto (fun g : ℝ => g⁻¹) atTop (𝓝[≠] 0) :=
    tendsto_inv_atTop_nhdsGT_zero.mono_right (nhdsGT_le_nhdsNE 0)
  have h1 := (hslope.comp hinv).neg
  rw [neg_neg] at h1
  have h2 : Tendsto (fun g : ℝ => -(g * Real.log (f g⁻¹))) atTop (𝓝 (trace X)) := by
    refine h1.congr' (Filter.Eventually.of_forall fun g => ?_)
    simp only [Function.comp_apply, zero_add, hf0, Real.log_one, sub_zero, inv_inv, smul_eq_mul]
  have h3 := (Real.continuous_exp.tendsto _).comp h2
  have hpos : ∀ᶠ g in atTop, 0 < f g⁻¹ := by
    have hc : ContinuousAt f 0 := hd.continuousAt
    have : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < f ε := hc.eventually (lt_mem_nhds (by rw [hf0]; norm_num))
    exact tendsto_inv_atTop_zero.eventually this
  refine h3.congr' ?_
  filter_upwards [hpos] with g hg
  simp only [Function.comp_apply, sourceZ, one_div]
  rw [Real.rpow_def_of_pos hg]
  congr 1
  ring

/-- **The first-order coefficient of `log Z_{(s,g)}` is `s² Tr X`**, the same in every member. -/
theorem logSource_first_order (s g : ℝ) (hg : g ≠ 0) (X : Matrix n n ℝ) :
    HasDerivAt (fun ε : ℝ => -(s * g) * Real.log (det (1 - (ε * (s / g)) • X)))
      (s ^ 2 * trace X) 0 := by
  have h : HasDerivAt (fun ε' : ℝ => det (1 - ε' • X)) (-trace X) ((fun ε : ℝ => ε * (s / g)) 0) := by
    simpa using det_one_sub_smul_hasDerivAt X
  have hc : HasDerivAt (fun ε : ℝ => ε * (s / g)) (s / g) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const (s / g)
  have hd := h.comp 0 hc
  have h0 : ((fun ε' : ℝ => det (1 - ε' • X)) ∘ fun ε : ℝ => ε * (s / g)) 0 = 1 := by simp
  have hlog := hd.log (by rw [h0]; norm_num)
  rw [h0, div_one] at hlog
  have hm := hlog.const_mul (-(s * g))
  have hfun : (fun y => -(s * g) * Real.log (((fun ε' : ℝ => det (1 - ε' • X)) ∘
      fun ε : ℝ => ε * (s / g)) y)) =
      fun ε : ℝ => -(s * g) * Real.log (det (1 - (ε * (s / g)) • X)) := rfl
  rw [hfun] at hm
  refine hm.congr_deriv ?_
  field_simp

/-- **The address: the several-vertices member expanded on the words,**
`det(I + diag(j) M) = Σ_S (∏_{x∈S} j_x) det M[S, S]`. -/
theorem det_one_add_diagonal_mul {R : Type*} [CommRing R] (M : Matrix n n R) (j : n → R) :
    (1 + diagonal j * M).det =
      ∑ S : Finset n, (∏ i ∈ S, j i) * (M.submatrix (Subtype.val : S → n) Subtype.val).det := by
  let D := (detRowAlternating : (n → R) [⋀^n]→ₗ[R] R)
  have e0 : (1 + diagonal j * M).det =
      D ((fun i => (diagonal j * M) i) + (fun i => (1 : Matrix n n R) i)) := by
    rw [add_comm]
    rfl
  rw [e0, D.map_add_univ]
  refine Finset.sum_congr rfl fun S _ => ?_
  have h_smul : S.piecewise (fun i => (diagonal j * M) i) (fun i => (1 : Matrix n n R) i) =
      fun i => (if i ∈ S then j i else 1) •
        S.piecewise (fun i => M i) (fun i => (1 : Matrix n n R) i) i := by
    funext i k
    simp only [Finset.piecewise, Pi.smul_apply, smul_eq_mul, diagonal_mul]
    split_ifs <;> simp
  rw [h_smul, D.map_smul_univ, Finset.prod_ite_mem, Finset.univ_inter, smul_eq_mul]
  congr 1
  exact det_piecewise_one_eq_submatrix_det M S

theorem sum_single_apply (T : Finset n) (j : n) :
    (∑ i ∈ T, Finsupp.single i 1 : n →₀ ℕ) j = if j ∈ T then 1 else 0 := by
  rw [Finsupp.finset_sum_apply]
  simp [Finsupp.single_apply]

theorem sum_single_inj {T S : Finset n}
    (h : (∑ i ∈ T, Finsupp.single i 1 : n →₀ ℕ) = ∑ i ∈ S, Finsupp.single i 1) : T = S := by
  ext j
  have := congrArg (fun f : n →₀ ℕ => f j) h
  simp only [sum_single_apply] at this
  by_cases hT : j ∈ T <;> by_cases hS : j ∈ S <;> simp_all

/-- **The address as a coefficient:** in `det(I + diag(X) M)` over the polynomials in the sources
`X_x`, the coefficient of the word `∏_{x∈S} X_x` is the principal minor `det M[S, S]`. -/
theorem address_coeff {R : Type*} [CommRing R] (M : Matrix n n R) (S : Finset n) :
    ((1 + diagonal (fun i => (MvPolynomial.X i : MvPolynomial n R)) *
          M.map MvPolynomial.C).det).coeff (∑ i ∈ S, Finsupp.single i 1) =
      (M.submatrix (Subtype.val : S → n) Subtype.val).det := by
  rw [det_one_add_diagonal_mul, MvPolynomial.coeff_sum]
  have hT : ∀ T : Finset n, (∏ i ∈ T, (MvPolynomial.X i : MvPolynomial n R)) *
      ((M.map MvPolynomial.C).submatrix (Subtype.val : T → n) Subtype.val).det =
      MvPolynomial.monomial (∑ i ∈ T, Finsupp.single i 1)
        ((M.submatrix (Subtype.val : T → n) Subtype.val).det) := by
    intro T
    have h1 : (M.map (MvPolynomial.C : R → MvPolynomial n R)).submatrix (Subtype.val : T → n)
        (Subtype.val : T → n) = (M.submatrix (Subtype.val : T → n) (Subtype.val : T → n)).map
          (MvPolynomial.C : R → MvPolynomial n R) := rfl
    rw [h1, ← RingHom.mapMatrix_apply, ← RingHom.map_det, MvPolynomial.monomial_sum_index,
      mul_comm]
    rfl
  simp only [hT, MvPolynomial.coeff_monomial]
  rw [Finset.sum_eq_single S]
  · simp
  · intro T _ hTS
    have hne : ¬ (∑ i ∈ T, Finsupp.single i 1 : n →₀ ℕ) = ∑ i ∈ S, Finsupp.single i 1 :=
      fun h => hTS (sum_single_inj h)
    simp only [hne, ↓reduceIte]
  · simp

/-- **A composite on the direct sum of its lines' words is the product,** in every member. -/
theorem sourceZ_directSum {m : Type*} [Fintype m] [DecidableEq m] (s g : ℝ) (X : Matrix n n ℝ)
    (Y : Matrix m m ℝ) (hX : 0 ≤ det (1 - (s / g) • X)) (hY : 0 ≤ det (1 - (s / g) • Y)) :
    sourceZ s g (fromBlocks X 0 0 Y) = sourceZ s g X * sourceZ s g Y := by
  have h : (1 - (s / g) • fromBlocks X 0 0 Y : Matrix (n ⊕ m) (n ⊕ m) ℝ) =
      fromBlocks (1 - (s / g) • X) 0 0 (1 - (s / g) • Y) := by
    ext (i | i) (j | j) <;>
      simp [Matrix.one_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
        fromBlocks_apply₂₂]
  rw [sourceZ, h, det_fromBlocks_zero₂₁, Real.mul_rpow hX hY]
  rfl

end Source

end Law

end Comparison

end
