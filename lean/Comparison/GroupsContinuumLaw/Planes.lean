import Comparison.GroupsContinuumLaw.Spin6

/-!
# The four types of division (Prop. 21)

* `exists_rotation_map`: **`SO(6)` takes every `k`-dimensional subspace of the six to every other**
  (Mathlib's `LinearIsometry.extend`, with a reflection in the complement to fix the determinant);
  `su4_moves_planes`: by `Spin6.lean`'s `rot6_onto`, **the fifteen rotations do it**: a division is known
  by `k`.
* `real_form_conj`, `realFormMap_mem`, `realFormMap_invol`, `realFormMap_onto`: for the division with
  signs `ε` (`k` of them `−1`), **the kept rotations plus `i` times the moved rotations are conjugate, by
  `D = diag(1 or i)`, to `so(6 − k, k)`**, the rotations of the metric `η = diag(ε)`: the real forms.
* `null_signature`: **at a normalized null vector `(a, b)` of `|x|² − |y|²` on `ℝᵖ × ℝ^q`, every
  tangent vector is `x' + y' + c(a, b)` with `x' ⊥ a`, `y' ⊥ b`, uniquely, and its length is
  `|x'|² − |y'|²`**; `finrank_perp`: the two parts have dimensions `p − 1` and `q − 1`: the null cone up
  to scale has signature `(p − 1, q − 1)`;
* `null_normalize`, `null_line_iff`: **the balanced lines are `(S^{p−1} × S^{q−1})/ℤ₂`**, for every
  `k` (`S⁴` for `k = 1`, `(S¹ × S³)/ℤ₂` for `k = 2`, `(S² × S²)/ℤ₂` for `k = 3`).
-/

namespace Comparison.GroupsContinuumLaw

open Matrix hiding J
open Complex

noncomputable section

/-! ## Every `k`-plane to every other -/

/-- An isometry between two subspaces of equal dimension. -/
def subIso (K₁ K₂ : Submodule ℝ E6) (h : Module.finrank ℝ K₁ = Module.finrank ℝ K₂) :
    K₁ ≃ₗᵢ[ℝ] K₂ :=
  (stdOrthonormalBasis ℝ K₁).repr.trans
    ((stdOrthonormalBasis ℝ K₂).reindex (finCongr h.symm)).repr.symm

theorem exists_isometry_map (K₁ K₂ : Submodule ℝ E6)
    (h : Module.finrank ℝ K₁ = Module.finrank ℝ K₂) :
    ∃ φ : E6 ≃ₗᵢ[ℝ] E6, ∀ x, x ∈ K₂ ↔ ∃ y ∈ K₁, φ y = x := by
  let e := subIso K₁ K₂ h
  let L : K₁ →ₗᵢ[ℝ] E6 := K₂.subtypeₗᵢ.comp e.toLinearIsometry
  let φ := L.extend.toLinearIsometryEquiv rfl
  have hφ : ∀ y : K₁, φ y = (e y : E6) := fun y => by
    change L.extend y = _
    rw [LinearIsometry.extend_apply]
    rfl
  refine ⟨φ, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · refine ⟨(e.symm ⟨x, hx⟩ : E6), (e.symm ⟨x, hx⟩).2, ?_⟩
    rw [hφ (e.symm ⟨x, hx⟩)]
    simp
  · rintro ⟨y, hy, rfl⟩
    rw [hφ ⟨y, hy⟩]
    exact (e ⟨y, hy⟩).2

/-- **`SO(6)` takes every `k`-plane of the six to every other.** -/
theorem exists_rotation_map (K₁ K₂ : Submodule ℝ E6)
    (h : Module.finrank ℝ K₁ = Module.finrank ℝ K₂) :
    ∃ φ : E6 ≃ₗᵢ[ℝ] E6, LinearMap.det φ.toLinearMap = 1 ∧ ∀ x, x ∈ K₂ ↔ ∃ y ∈ K₁, φ y = x := by
  obtain ⟨φ, hφ⟩ := exists_isometry_map K₁ K₂ h
  rcases det_isometry_pm φ with hd | hd
  · exact ⟨φ, hd, hφ⟩
  · by_cases htop : K₂ = ⊤
    · have h1 : K₁ = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        rw [h, htop, finrank_top]
      refine ⟨1, LinearMap.det_id, fun x => ?_⟩
      subst htop; subst h1
      simp
    · have hne : K₂ᗮ ≠ ⊥ := fun hb => htop (Submodule.orthogonal_eq_bot_iff.1 hb)
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
      set ρ : E6 ≃ₗᵢ[ℝ] E6 := (ℝ ∙ v)ᗮ.reflection
      have hfix : ∀ w ∈ K₂, ρ w = w := by
        intro w hw
        apply Submodule.reflection_mem_subspace_eq_self
        rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
        exact Submodule.inner_left_of_mem_orthogonal hw hv
      refine ⟨ρ * φ, ?_, fun x => ?_⟩
      · rw [det_mul_isometry, det_reflection_ne hv0, hd]
        norm_num
      · constructor
        · intro hx
          obtain ⟨y, hy, hyx⟩ := (hφ x).1 hx
          refine ⟨y, hy, ?_⟩
          rw [LinearIsometryEquiv.coe_mul, Function.comp_apply, hyx, hfix x hx]
        · rintro ⟨y, hy, rfl⟩
          rw [LinearIsometryEquiv.coe_mul, Function.comp_apply]
          have hφy : φ y ∈ K₂ := (hφ (φ y)).2 ⟨y, hy, rfl⟩
          rw [hfix _ hφy]
          exact hφy

/-- **The fifteen rotations take every `k`-plane of P1's real six to every other.** -/
theorem su4_moves_planes (K₁ K₂ : Submodule ℝ E6)
    (h : Module.finrank ℝ K₁ = Module.finrank ℝ K₂) :
    ∃ U : SU4, ∀ x, x ∈ K₂ ↔ ∃ y ∈ K₁, rot6Hom U y = x := by
  obtain ⟨φ, hd, hφ⟩ := exists_rotation_map K₁ K₂ h
  obtain ⟨U, hU⟩ := rot6_onto φ hd
  exact ⟨U, fun x => by rw [hU]; exact hφ x⟩

/-! ## The real forms -/

/-- The sign of the entry `(i, j)` under the change to the real form. -/
def realFormMap (ε : Fin 6 → ℝ) (X : Matrix (Fin 6) (Fin 6) ℝ) : Matrix (Fin 6) (Fin 6) ℝ :=
  Matrix.of fun i j => if ε i = 1 ∧ ε j = -1 then -X i j else X i j

/-- `D = diag(d)`, `d_i = 1` on the plus part and `i` on the minus part, and its inverse. -/
def dDiag (ε : Fin 6 → ℝ) : Matrix (Fin 6) (Fin 6) ℂ := diagonal fun i => if ε i = 1 then 1 else I

def dDiagInv (ε : Fin 6 → ℝ) : Matrix (Fin 6) (Fin 6) ℂ :=
  diagonal fun i => if ε i = 1 then 1 else -I

theorem dDiag_inv (ε : Fin 6 → ℝ) : dDiagInv ε * dDiag ε = 1 := by
  rw [dDiagInv, dDiag, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  split_ifs <;> simp

theorem rf_scalar (e1 e2 x : ℝ) (h1 : e1 = 1 ∨ e1 = -1) (h2 : e2 = 1 ∨ e2 = -1) :
    (if e1 = 1 then (1 : ℂ) else -I) * ((1 / 2 : ℂ) * ((x : ℂ) + (e1 : ℂ) * x * e2) +
      I * ((1 / 2 : ℂ) * ((x : ℂ) - (e1 : ℂ) * x * e2))) * (if e2 = 1 then (1 : ℂ) else I) =
      ((if e1 = 1 ∧ e2 = -1 then -x else x : ℝ) : ℂ) := by
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> norm_num <;>
    first
    | ring1
    | linear_combination (x : ℂ) * I_sq
    | linear_combination (-(x : ℂ)) * I_sq

/-- **The kept rotations plus `i` times the moved rotations, conjugated by `D`, are real and are the
matrices `realFormMap ε X`.** -/
theorem real_form_conj (ε : Fin 6 → ℝ) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (X : Matrix (Fin 6) (Fin 6) ℝ) :
    dDiagInv ε * ((1 / 2 : ℂ) • (X.map ofReal + diagonal (fun i => (ε i : ℂ)) * X.map ofReal *
        diagonal (fun i => (ε i : ℂ))) +
      I • ((1 / 2 : ℂ) • (X.map ofReal - diagonal (fun i => (ε i : ℂ)) * X.map ofReal *
        diagonal (fun i => (ε i : ℂ))))) * dDiag ε = (realFormMap ε X).map ofReal := by
  ext i j
  have h := rf_scalar (ε i) (ε j) (X i j) (hε i) (hε j)
  simp only [dDiagInv, dDiag, realFormMap, diagonal_mul, mul_diagonal, Matrix.add_apply,
    Matrix.smul_apply, Matrix.sub_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul]
  linear_combination h

/-- **The changed matrices keep the metric `η = diag(ε)`**: `Yᵀη + ηY = 0`, the Lie algebra
`so(6 − k, k)`. -/
theorem realFormMap_mem (ε : Fin 6 → ℝ) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (X : Matrix (Fin 6) (Fin 6) ℝ) (hX : Xᵀ = -X) :
    (realFormMap ε X)ᵀ * diagonal ε + diagonal ε * realFormMap ε X = 0 := by
  have hs : ∀ i j, X j i = -X i j := fun i j => by
    have := congrFun (congrFun hX i) j
    simpa using this
  ext i j
  simp only [realFormMap, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.transpose_apply, Matrix.of_apply, Matrix.zero_apply]
  have h1 := hs i j
  have h2 := hs j i
  rcases hε i with hi | hi <;> rcases hε j with hj | hj <;> simp only [hi, hj] <;> norm_num <;>
    linarith

theorem realFormMap_invol (ε : Fin 6 → ℝ) (X : Matrix (Fin 6) (Fin 6) ℝ) :
    realFormMap ε (realFormMap ε X) = X := by
  ext i j
  simp only [realFormMap, Matrix.of_apply]
  split_ifs <;> simp

/-- **Every element of `so(6 − k, k)` comes from a rotation of the six.** -/
theorem realFormMap_onto (ε : Fin 6 → ℝ) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (Y : Matrix (Fin 6) (Fin 6) ℝ) (hY : Yᵀ * diagonal ε + diagonal ε * Y = 0) :
    (realFormMap ε Y)ᵀ = -realFormMap ε Y ∧ realFormMap ε (realFormMap ε Y) = Y := by
  refine ⟨?_, realFormMap_invol ε Y⟩
  have hs : ∀ i j, Y j i * ε j + ε i * Y i j = 0 := fun i j => by
    have := congrFun (congrFun hY i) j
    simpa [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul] using this
  ext i j
  simp only [realFormMap, Matrix.transpose_apply, Matrix.of_apply, Matrix.neg_apply]
  have h1 := hs i j
  have h2 := hs j i
  rcases hε i with hi | hi <;> rcases hε j with hj | hj <;> simp only [hi, hj] at h1 h2 ⊢ <;>
    norm_num at h1 h2 ⊢ <;> linarith

/-! ## The balanced directions of every type -/

section Null

variable {p q : ℕ}

/-- The metric of a division: `|x|² − |y|²` on `ℝᵖ × ℝ^q`. -/
def gpq (v w : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) : ℝ :=
  inner ℝ v.1 w.1 - inner ℝ v.2 w.2

/-- **At a normalized null vector the tangent space splits**: `w = x' + y' + c v` with `x' ⊥ a`,
`y' ⊥ b`, uniquely, and `g(w, w) = |x'|² − |y'|²`. -/
theorem null_signature (a : EuclideanSpace ℝ (Fin p)) (b : EuclideanSpace ℝ (Fin q))
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (x : EuclideanSpace ℝ (Fin p)) (y : EuclideanSpace ℝ (Fin q))
    (hw : gpq (a, b) (x, y) = 0) :
    (∃ c : ℝ, ∃ x' ∈ (ℝ ∙ a)ᗮ, ∃ y' ∈ (ℝ ∙ b)ᗮ, x = x' + c • a ∧ y = y' + c • b ∧
        gpq (x, y) (x, y) = ‖x'‖ ^ 2 - ‖y'‖ ^ 2) ∧
    (∀ (c d : ℝ) (x' x'' : EuclideanSpace ℝ (Fin p)), x' ∈ (ℝ ∙ a)ᗮ → x'' ∈ (ℝ ∙ a)ᗮ →
        x' + c • a = x'' + d • a → c = d ∧ x' = x'') := by
  have haa : inner ℝ a a = 1 := by rw [real_inner_self_eq_norm_sq, ha, one_pow]
  have hbb : inner ℝ b b = 1 := by rw [real_inner_self_eq_norm_sq, hb, one_pow]
  simp only [gpq] at hw
  set c := inner ℝ a x with hc
  have hcb : inner ℝ b y = c := by linarith
  refine ⟨⟨c, x - c • a, ?_, y - c • b, ?_, by abel, by abel, ?_⟩, ?_⟩
  · rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right, inner_smul_right,
      haa, ← hc]
    ring
  · rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right, inner_smul_right,
      hbb, hcb]
    ring
  · simp only [gpq]
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
    have e1 : ‖x‖ ^ 2 = ‖x - c • a‖ ^ 2 + c ^ 2 := by
      have := norm_add_sq_real (x - c • a) (c • a)
      rw [sub_add_cancel, norm_smul, ha, inner_sub_left, inner_smul_left, inner_smul_right,
        inner_smul_right, haa, real_inner_comm, ← hc] at this
      simp only [Real.norm_eq_abs, conj_trivial, mul_one, sq_abs] at this
      linarith
    have e2 : ‖y‖ ^ 2 = ‖y - c • b‖ ^ 2 + c ^ 2 := by
      have := norm_add_sq_real (y - c • b) (c • b)
      rw [sub_add_cancel, norm_smul, hb, inner_sub_left, inner_smul_left, inner_smul_right,
        inner_smul_right, hbb, real_inner_comm, hcb] at this
      simp only [Real.norm_eq_abs, conj_trivial, mul_one, sq_abs] at this
      linarith
    rw [e1, e2]
    ring
  · intro c d x' x'' h1 h2 h
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at h1 h2
    have := congrArg (inner ℝ a) h
    rw [inner_add_right, inner_add_right, inner_smul_right, inner_smul_right, h1, h2, haa] at this
    have hcd : c = d := by linarith
    refine ⟨hcd, ?_⟩
    rw [hcd] at h
    exact add_right_cancel h

/-- The two parts of the tangent space have dimensions `p − 1` and `q − 1`. -/
theorem finrank_perp (a : EuclideanSpace ℝ (Fin (p + 1))) (ha : a ≠ 0) :
    Module.finrank ℝ (ℝ ∙ a)ᗮ = p := by
  have : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (p + 1))) = p + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  exact Submodule.finrank_orthogonal_span_singleton ha

/-- The normalized representative of a null vector. -/
def nrmPQ (v : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) :
    EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q) := ‖v.1‖⁻¹ • v

/-- **A balanced vector normalizes onto `S^{p−1} × S^{q−1}`.** -/
theorem null_normalize (v : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) (hv : v ≠ 0)
    (hn : ‖v.1‖ = ‖v.2‖) : 0 < ‖v.1‖ ∧ ‖(nrmPQ v).1‖ = 1 ∧ ‖(nrmPQ v).2‖ = 1 := by
  have hpos : 0 < ‖v.1‖ := by
    rcases (norm_nonneg v.1).lt_or_eq with h | h
    · exact h
    · exfalso
      apply hv
      have h1 : v.1 = 0 := norm_eq_zero.1 h.symm
      have h2 : v.2 = 0 := norm_eq_zero.1 (by rw [← hn, ← h])
      exact Prod.ext h1 h2
  refine ⟨hpos, ?_, ?_⟩
  · simp only [nrmPQ, Prod.smul_fst, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ hpos.ne'
  · simp only [nrmPQ, Prod.smul_snd, norm_smul, norm_inv, norm_norm, ← hn]
    exact inv_mul_cancel₀ hpos.ne'

/-- **Two balanced vectors span one line exactly when their normalized representatives agree up to
sign**: the balanced lines are `(S^{p−1} × S^{q−1})/ℤ₂`. -/
theorem null_line_iff (v w : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) (hv : v ≠ 0)
    (hvn : ‖v.1‖ = ‖v.2‖) (hw : w ≠ 0) (hwn : ‖w.1‖ = ‖w.2‖) :
    (∃ c : ℝ, c ≠ 0 ∧ w = c • v) ↔ (nrmPQ w = nrmPQ v ∨ nrmPQ w = -nrmPQ v) := by
  have hv1 := (null_normalize v hv hvn).1
  have hw1 := (null_normalize w hw hwn).1
  constructor
  · rintro ⟨c, hc, rfl⟩
    rcases lt_or_gt_of_ne hc with hneg | hpos
    · right
      simp only [nrmPQ, Prod.smul_fst, norm_smul, Real.norm_eq_abs, abs_of_neg hneg, smul_smul]
      rw [← neg_smul]
      congr 1
      field_simp
    · left
      simp only [nrmPQ, Prod.smul_fst, norm_smul, Real.norm_eq_abs, abs_of_pos hpos, smul_smul]
      congr 1
      field_simp
  · rintro (h | h)
    · refine ⟨‖w.1‖ / ‖v.1‖, div_ne_zero hw1.ne' hv1.ne', ?_⟩
      have := congrArg (fun z => ‖w.1‖ • z) h
      simp only [nrmPQ, smul_smul] at this
      rw [mul_inv_cancel₀ hw1.ne', one_smul] at this
      rw [div_eq_mul_inv]
      exact this
    · refine ⟨-(‖w.1‖ / ‖v.1‖), neg_ne_zero.2 (div_ne_zero hw1.ne' hv1.ne'), ?_⟩
      have := congrArg (fun z => ‖w.1‖ • z) h
      simp only [nrmPQ, smul_smul, smul_neg] at this
      rw [mul_inv_cancel₀ hw1.ne', one_smul] at this
      rw [neg_smul, div_eq_mul_inv]
      exact this

end Null

end

end Comparison.GroupsContinuumLaw
