import Comparison.Existence.Table

/-!
# The balanced cone of the held plane and its clock, as one theorem

Proposition 21 (type `2|4`) and cone-and-clock theorem. On P1's real six with the held plane
`D = {0, 1}` take the form `g(v, w) = v₀w₀ + v₁w₁ − Σ_{k≥2} v_k w_k` (the division's metric `g_D` up to
its overall sign, which calling the other part divided reverses). Its balanced directions are the null
rays.

* `cone_radius`: on the cone `|d|² = v₀² + v₁² > 0` and `|u|² = |d|²`; `normalized_on_torus`: the
  normalized representative lies on `S¹ × S³`; `torus_on_cone`: every point of `S¹ × S³` is balanced;
  `normalized_ray_iff`: **two balanced vectors span one ray exactly when their normalized
  representatives agree up to sign**: the balanced directions are `(S¹ × S³)/ℤ₂`.
* `frame_orthonormal`, `frame_perp`, `cone_decomposition`: at a normalized `v` the clock `J v` and three
  quaternionic directions `iu, ju, ku` are `g`-orthonormal with signs `(+, −, −, −)`, orthogonal to `v`,
  and with `v` they form a basis of `v^⊥`: **the quotient `v^⊥/ℝv` carries signature `(1, 3)`**;
  `cone_tangent_radical`: the radical of `g` on `v^⊥` is `ℝv`; `cone_section_change`: a change of
  section multiplies the quotient metric by `f²` (a conformal class).
* `central_kept_iff`: **the kept rotations' centre is `ℝ J`**, `J = E₁₀ − E₀₁` the rotation of the held
  plane; and `clock_is_central`: the positive direction of the quotient is `J v`.
* `balanced_cone`: the assembled statement.
-/

namespace Comparison.GroupsContinuumLaw

open Matrix

/-- The form of the held plane: `g(v, w) = v₀w₀ + v₁w₁ − v₂w₂ − v₃w₃ − v₄w₄ − v₅w₅`. -/
def g6 (v w : Fin 6 → ℝ) : ℝ :=
  v 0 * w 0 + v 1 * w 1 - v 2 * w 2 - v 3 * w 3 - v 4 * w 4 - v 5 * w 5

/-- `|d|²`, the held plane's part. -/
def r2 (v : Fin 6 → ℝ) : ℝ := v 0 ^ 2 + v 1 ^ 2

/-- `|u|²`, the other four. -/
def s2 (v : Fin 6 → ℝ) : ℝ := v 2 ^ 2 + v 3 ^ 2 + v 4 ^ 2 + v 5 ^ 2

/-- A balanced vector: nonzero and null. -/
def OnCone (v : Fin 6 → ℝ) : Prop := v ≠ 0 ∧ g6 v v = 0

theorem g6_self (v : Fin 6 → ℝ) : g6 v v = r2 v - s2 v := by
  simp only [g6, r2, s2]
  ring

theorem g6_comm (v w : Fin 6 → ℝ) : g6 v w = g6 w v := by
  simp only [g6]
  ring

theorem eq_zero_of_r2_s2 (v : Fin 6 → ℝ) (hr : r2 v = 0) (hs : s2 v = 0) : v = 0 := by
  simp only [r2, s2] at hr hs
  have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
  have h2 : v 2 = 0 := by nlinarith [sq_nonneg (v 2), sq_nonneg (v 3), sq_nonneg (v 4), sq_nonneg (v 5)]
  have h3 : v 3 = 0 := by nlinarith [sq_nonneg (v 2), sq_nonneg (v 3), sq_nonneg (v 4), sq_nonneg (v 5)]
  have h4 : v 4 = 0 := by nlinarith [sq_nonneg (v 2), sq_nonneg (v 3), sq_nonneg (v 4), sq_nonneg (v 5)]
  have h5 : v 5 = 0 := by nlinarith [sq_nonneg (v 2), sq_nonneg (v 3), sq_nonneg (v 4), sq_nonneg (v 5)]
  funext i
  fin_cases i <;> simp [h0, h1, h2, h3, h4, h5]

/-- **On the cone the plane part is positive and equals the other part.** -/
theorem cone_radius (v : Fin 6 → ℝ) (hv : OnCone v) : 0 < r2 v ∧ s2 v = r2 v := by
  have hs : s2 v = r2 v := by
    have := hv.2
    rw [g6_self] at this
    linarith
  refine ⟨?_, hs⟩
  rcases (show 0 ≤ r2 v by simp only [r2]; positivity).lt_or_eq with h | h
  · exact h
  · exact absurd (eq_zero_of_r2_s2 v h.symm (hs.trans h.symm)) hv.1

/-- The normalized representative `v/|d|`. -/
noncomputable def nrm (v : Fin 6 → ℝ) : Fin 6 → ℝ := (Real.sqrt (r2 v))⁻¹ • v

theorem r2_smul (a : ℝ) (v : Fin 6 → ℝ) : r2 (a • v) = a ^ 2 * r2 v := by
  simp only [r2, Pi.smul_apply, smul_eq_mul]
  ring

theorem s2_smul (a : ℝ) (v : Fin 6 → ℝ) : s2 (a • v) = a ^ 2 * s2 v := by
  simp only [s2, Pi.smul_apply, smul_eq_mul]
  ring

/-- **The normalized representative lies on `S¹ × S³`.** -/
theorem normalized_on_torus (v : Fin 6 → ℝ) (hv : OnCone v) : r2 (nrm v) = 1 ∧ s2 (nrm v) = 1 := by
  obtain ⟨hr, hs⟩ := cone_radius v hv
  have hsq : Real.sqrt (r2 v) ^ 2 = r2 v := Real.sq_sqrt hr.le
  have hne : Real.sqrt (r2 v) ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  rw [nrm, r2_smul, s2_smul, hs, inv_pow, hsq, inv_mul_cancel₀ hr.ne']
  exact ⟨rfl, rfl⟩

/-- **Every point of `S¹ × S³` is balanced.** -/
theorem torus_on_cone (x : Fin 6 → ℝ) (hr : r2 x = 1) (hs : s2 x = 1) : OnCone x := by
  refine ⟨?_, ?_⟩
  · intro h
    rw [h] at hr
    simp [r2] at hr
  · rw [g6_self, hr, hs, sub_self]

/-- **Two balanced vectors span one ray exactly when their normalized representatives agree up to
sign:** the balanced directions are `(S¹ × S³)/ℤ₂`. -/
theorem normalized_ray_iff (v w : Fin 6 → ℝ) (hv : OnCone v) (hw : OnCone w) :
    (∃ a : ℝ, a ≠ 0 ∧ w = a • v) ↔ nrm w = nrm v ∨ nrm w = -nrm v := by
  obtain ⟨hrv, _⟩ := cone_radius v hv
  obtain ⟨hrw, _⟩ := cone_radius w hw
  have sv := Real.sqrt_pos.mpr hrv
  have sw := Real.sqrt_pos.mpr hrw
  constructor
  · rintro ⟨a, ha, rfl⟩
    have hsq : Real.sqrt (r2 (a • v)) = |a| * Real.sqrt (r2 v) := by
      rw [r2_smul, Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq_eq_abs]
    rcases lt_or_gt_of_ne ha with hneg | hpos
    · right
      rw [nrm, nrm, hsq, abs_of_neg hneg, smul_smul, ← neg_smul]
      congr 1
      field_simp
    · left
      rw [nrm, nrm, hsq, abs_of_pos hpos, smul_smul]
      congr 1
      field_simp
  · rintro (h | h)
    · refine ⟨Real.sqrt (r2 w) / Real.sqrt (r2 v), by positivity, ?_⟩
      have := congrArg (fun x => Real.sqrt (r2 w) • x) h
      simp only [nrm, smul_smul] at this
      rw [mul_inv_cancel₀ sw.ne', one_smul] at this
      exact this.trans (by rw [div_eq_mul_inv])
    · refine ⟨-(Real.sqrt (r2 w) / Real.sqrt (r2 v)), by
        have : 0 < Real.sqrt (r2 w) / Real.sqrt (r2 v) := by positivity
        linarith, ?_⟩
      have := congrArg (fun x => Real.sqrt (r2 w) • x) h
      simp only [nrm, smul_smul, smul_neg] at this
      rw [mul_inv_cancel₀ sw.ne', one_smul] at this
      exact this.trans (by rw [neg_smul, div_eq_mul_inv])

/-! ## The clock and the frame at a normalized point -/

/-- The rotation of the held plane, `J = E₁₀ − E₀₁`. -/
def J6 : Matrix (Fin 6) (Fin 6) ℝ := unitTurn 1 0

/-- The four frame directions at `v`: the clock `Jv` and the quaternionic directions `iu, ju, ku`. -/
def frame (v : Fin 6 → ℝ) : Fin 4 → Fin 6 → ℝ :=
  ![![-v 1, v 0, 0, 0, 0, 0], ![0, 0, -v 3, v 2, -v 5, v 4], ![0, 0, -v 4, v 5, v 2, -v 3],
    ![0, 0, -v 5, -v 4, v 3, v 2]]

/-- The dual null direction `v̄ = (v₀, v₁, −v₂, −v₃, −v₄, −v₅)/2`. -/
noncomputable def vbar (v : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![v 0 / 2, v 1 / 2, -v 2 / 2, -v 3 / 2, -v 4 / 2, -v 5 / 2]

/-- **The clock is the central kept rotation applied to `v`:** `frame 0 = J v`. -/
theorem clock_is_central (v : Fin 6 → ℝ) : frame v 0 = J6 *ᵥ v := by
  funext i
  fin_cases i <;>
    simp [frame, J6, unitTurn, Matrix.mulVec, dotProduct, Fin.sum_univ_six]

/-- **The frame is `g`-orthonormal with signs `(+, −, −, −)`** at a normalized `v`. -/
theorem frame_orthonormal (v : Fin 6 → ℝ) (hr : r2 v = 1) (hs : s2 v = 1) (i j : Fin 4) :
    g6 (frame v i) (frame v j) = if i = j then (if i = 0 then 1 else -1) else 0 := by
  simp only [r2, s2] at hr hs
  fin_cases i <;> fin_cases j <;> simp [g6, frame] <;>
    first
      | linear_combination hr
      | linear_combination (-1 : ℝ) * hs
      | ring1

/-- **The frame is orthogonal to `v`.** -/
theorem frame_perp (v : Fin 6 → ℝ) (i : Fin 4) : g6 v (frame v i) = 0 := by
  fin_cases i <;> simp [g6, frame] <;> ring

theorem vbar_props (v : Fin 6 → ℝ) (hr : r2 v = 1) (hs : s2 v = 1) :
    g6 v (vbar v) = 1 ∧ g6 (vbar v) (vbar v) = 0 ∧ ∀ i, g6 (vbar v) (frame v i) = 0 := by
  simp only [r2, s2] at hr hs
  refine ⟨?_, ?_, ?_⟩
  · simp [g6, vbar]
    linear_combination hr / 2 + hs / 2
  · simp [g6, vbar]
    linear_combination hr / 4 - hs / 4
  · intro i
    fin_cases i <;> simp [g6, vbar, frame] <;> ring

theorem g6_add_left (x y z : Fin 6 → ℝ) : g6 (x + y) z = g6 x z + g6 y z := by
  simp only [g6, Pi.add_apply]
  ring

theorem g6_smul_left (a : ℝ) (x z : Fin 6 → ℝ) : g6 (a • x) z = a * g6 x z := by
  simp only [g6, Pi.smul_apply, smul_eq_mul]
  ring

/-- The explicit expansion of `w ⊥ v` in the basis `v, Jv, iu, ju, ku`. -/
theorem decomposition_explicit (v : Fin 6 → ℝ) (hr : r2 v = 1) (hs : s2 v = 1) (w : Fin 6 → ℝ)
    (hw : g6 v w = 0) :
    w = g6 w (vbar v) • v + g6 w (frame v 0) • frame v 0 + (-g6 w (frame v 1)) • frame v 1 +
      (-g6 w (frame v 2)) • frame v 2 + (-g6 w (frame v 3)) • frame v 3 := by
  simp only [r2, s2] at hr hs
  simp only [g6] at hw
  funext k
  fin_cases k <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> simp [g6, vbar, frame] <;>
    first
      | linear_combination (-(w 0) : ℝ) * hr + (v 0 / 2) * hw
      | linear_combination (-(w 1) : ℝ) * hr + (v 1 / 2) * hw
      | linear_combination (-(w 2) : ℝ) * hs - (v 2 / 2) * hw
      | linear_combination (-(w 3) : ℝ) * hs - (v 3 / 2) * hw
      | linear_combination (-(w 4) : ℝ) * hs - (v 4 / 2) * hw
      | linear_combination (-(w 5) : ℝ) * hs - (v 5 / 2) * hw
      | linear_combination (w 0 : ℝ) * hr - (v 0 / 2) * hw
      | linear_combination (w 1 : ℝ) * hr - (v 1 / 2) * hw
      | linear_combination (w 2 : ℝ) * hs + (v 2 / 2) * hw
      | linear_combination (w 3 : ℝ) * hs + (v 3 / 2) * hw
      | linear_combination (w 4 : ℝ) * hs + (v 4 / 2) * hw
      | linear_combination (w 5 : ℝ) * hs + (v 5 / 2) * hw

/-- **`v` and the frame form a basis of `v^⊥`:** every `w ⊥ v` is `c₀v + c₁Jv + c₂iu + c₃ju + c₄ku` for
exactly one `c`. -/
theorem cone_decomposition (v : Fin 6 → ℝ) (hr : r2 v = 1) (hs : s2 v = 1) (w : Fin 6 → ℝ)
    (hw : g6 v w = 0) :
    ∃! c : Fin 5 → ℝ, w = c 0 • v + c 1 • frame v 0 + c 2 • frame v 1 + c 3 • frame v 2 +
      c 4 • frame v 3 := by
  obtain ⟨b1, b2, b3⟩ := vbar_props v hr hs
  have o := frame_orthonormal v hr hs
  have p := frame_perp v
  refine ⟨![g6 w (vbar v), g6 w (frame v 0), -g6 w (frame v 1), -g6 w (frame v 2),
    -g6 w (frame v 3)], ?_, ?_⟩
  · simpa using decomposition_explicit v hr hs w hw
  · intro c hc
    have hpair : ∀ z, g6 w z = c 0 * g6 v z + c 1 * g6 (frame v 0) z + c 2 * g6 (frame v 1) z +
        c 3 * g6 (frame v 2) z + c 4 * g6 (frame v 3) z := by
      intro z
      rw [hc]
      simp only [g6_add_left, g6_smul_left]
    have e0 := hpair (vbar v)
    have e1 := hpair (frame v 0)
    have e2 := hpair (frame v 1)
    have e3 := hpair (frame v 2)
    have e4 := hpair (frame v 3)
    rw [b1, g6_comm (frame v 0), g6_comm (frame v 1), g6_comm (frame v 2), g6_comm (frame v 3),
      b3, b3, b3, b3] at e0
    rw [p, o, o, o, o] at e1
    rw [p, o, o, o, o] at e2
    rw [p, o, o, o, o] at e3
    rw [p, o, o, o, o] at e4
    simp at e0 e1 e2 e3 e4
    funext k
    fin_cases k <;> simp <;> linarith

/-- **The radical of `g` on `v^⊥` is the line of `v`** (at a normalized balanced `v`). -/
theorem cone_tangent_radical (v : Fin 6 → ℝ) (hr : r2 v = 1) (hs : s2 v = 1) (w : Fin 6 → ℝ)
    (hw : g6 v w = 0) : (∀ z, g6 v z = 0 → g6 w z = 0) ↔ ∃ a : ℝ, w = a • v := by
  constructor
  · intro h
    have hd := decomposition_explicit v hr hs w hw
    rw [h (frame v 0) (frame_perp v 0), h (frame v 1) (frame_perp v 1),
      h (frame v 2) (frame_perp v 2), h (frame v 3) (frame_perp v 3)] at hd
    refine ⟨g6 w (vbar v), hd.trans ?_⟩
    simp
  · rintro ⟨a, rfl⟩ z hz
    rw [g6_smul_left, hz, mul_zero]

/-- **A change of section multiplies the quotient metric by `f²`:** for `v` null and `w, z ⊥ v`,
`g(fw + av, fz + bv) = f² g(w, z)`. -/
theorem cone_section_change (v w z : Fin 6 → ℝ) (f a b : ℝ) (hv : g6 v v = 0) (hw : g6 v w = 0)
    (hz : g6 v z = 0) : g6 (f • w + a • v) (f • z + b • v) = f ^ 2 * g6 w z := by
  simp only [g6, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hv hw hz ⊢
  linear_combination (a * b) * hv + (f * b) * hw + (a * f) * hz

/-! ## The centre of the kept rotations -/

/-- The held plane. -/
def heldPlane : Finset (Fin 6) := {0, 1}

/-- A kept rotation of the held plane's division: antisymmetric, commuting with its sign. -/
def Kept6 (X : Matrix (Fin 6) (Fin 6) ℝ) : Prop :=
  Xᵀ = -X ∧ X * thetaD heldPlane = thetaD heldPlane * X

/-- A central kept rotation: kept, and commuting with every kept rotation. -/
def CentralKept6 (X : Matrix (Fin 6) (Fin 6) ℝ) : Prop :=
  Kept6 X ∧ ∀ Y, Kept6 Y → X * Y = Y * X

theorem unitTurn_comm_theta {n : ℕ} (D : Finset (Fin n)) (b c : Fin n) (h : b ∈ D ↔ c ∈ D) :
    unitTurn b c * thetaD D = thetaD D * unitTurn b c := by
  ext i j
  simp only [thetaD, Matrix.mul_diagonal, Matrix.diagonal_mul, unitTurn, Matrix.of_apply]
  by_cases h1 : i = b ∧ j = c
  · obtain ⟨rfl, rfl⟩ := h1
    simp only [h]
    ring
  · by_cases h2 : i = c ∧ j = b
    · obtain ⟨rfl, rfl⟩ := h2
      simp only [h]
      ring
    · simp only [h1, h2, ite_false, sub_zero, zero_mul, mul_zero]

theorem unitTurn_kept (b c : Fin 6) (h : b ∈ heldPlane ↔ c ∈ heldPlane) : Kept6 (unitTurn b c) :=
  ⟨unitTurn_transpose b c, unitTurn_comm_theta heldPlane b c h⟩

theorem third_direction : ∀ a b : Fin 6, a ∉ heldPlane → b ∉ heldPlane → a ≠ b →
    ∃ c : Fin 6, c ∉ heldPlane ∧ c ≠ a ∧ c ≠ b := by
  decide

theorem central_entry_zero (X : Matrix (Fin 6) (Fin 6) ℝ) (hX : CentralKept6 X) (a b : Fin 6)
    (hab : a ≠ b) (hnot : ¬((a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1))) : X a b = 0 := by
  by_contra h
  have hcent : ∀ b c : Fin 6, (b ∈ heldPlane ↔ c ∈ heldPlane) → X * unitTurn b c = unitTurn b c * X :=
    fun b c hbc => hX.2 _ (unitTurn_kept b c hbc)
  obtain ⟨hside, hthird⟩ := clock_dividedSet heldPlane X hX.1.2 hcent hab h
  by_cases ha : a ∈ heldPlane
  · have hb : b ∈ heldPlane := hside.mp ha
    simp only [heldPlane, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all
  · have hb : b ∉ heldPlane := fun hb => ha (hside.mpr hb)
    obtain ⟨c, hc, hca, hcb⟩ := third_direction a b ha hb hab
    rcases hthird c ⟨fun h' => absurd h' hc, fun h' => absurd h' ha⟩ with h1 | h1
    · exact hca h1
    · exact hcb h1

/-- **The centre of the kept rotations of the held plane is the line of `J`.** -/
theorem central_kept_iff (X : Matrix (Fin 6) (Fin 6) ℝ) : CentralKept6 X ↔ ∃ a : ℝ, X = a • J6 := by
  constructor
  · intro hX
    refine ⟨X 1 0, ?_⟩
    have hskew : ∀ i j, X j i = -X i j := fun i j => by
      have := congrFun (congrFun hX.1.1 i) j
      simpa using this
    have hdiag : ∀ i, X i i = 0 := fun i => by
      have := hskew i i
      linarith
    ext i j
    by_cases hij : i = j
    · subst hij
      have h1 : ¬(i = 1 ∧ i = 0) := by
        rintro ⟨rfl, h⟩
        exact absurd h (by decide)
      have h2 : ¬(i = 0 ∧ i = 1) := by
        rintro ⟨rfl, h⟩
        exact absurd h (by decide)
      simp [hdiag, J6, unitTurn, h1, h2]
    · by_cases h10 : i = 1 ∧ j = 0
      · obtain ⟨rfl, rfl⟩ := h10
        simp [J6, unitTurn]
      · by_cases h01 : i = 0 ∧ j = 1
        · obtain ⟨rfl, rfl⟩ := h01
          simp [J6, unitTurn, hskew 1 0]
        · rw [central_entry_zero X hX i j hij (by tauto)]
          simp [J6, unitTurn, h10, h01]
  · rintro ⟨a, rfl⟩
    have hJk : Kept6 J6 := unitTurn_kept 1 0 (by simp [heldPlane])
    refine ⟨⟨by rw [Matrix.transpose_smul, hJk.1, smul_neg], by
      rw [Matrix.smul_mul, Matrix.mul_smul, hJk.2]⟩, ?_⟩
    intro Y hY
    rw [Matrix.smul_mul, Matrix.mul_smul]
    congr 1
    have hc : ∀ i j : Fin 6, ¬(i ∈ heldPlane ↔ j ∈ heldPlane) → Y i j = 0 :=
      fun i j h => kept_entry heldPlane Y hY.2 h
    have hskew : ∀ i j, Y j i = -Y i j := fun i j => by
      have := congrFun (congrFun hY.1 i) j
      simpa using this
    have hdiag : ∀ i, Y i i = 0 := fun i => by
      have := hskew i i
      linarith
    have hJl : ∀ i j, (J6 * Y) i j = (if i = 1 then Y 0 j else 0) - (if i = 0 then Y 1 j else 0) := by
      intro i j
      simp only [J6, unitTurn, Matrix.mul_apply, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib,
        ite_mul, one_mul, zero_mul]
      congr 1
      · rw [Finset.sum_eq_single 0]
        · by_cases hi : i = 1 <;> simp [hi]
        · intro k _ hk
          simp [hk]
        · simp
      · rw [Finset.sum_eq_single 1]
        · by_cases hi : i = 0 <;> simp [hi]
        · intro k _ hk
          simp [hk]
        · simp
    have hJr : ∀ i j, (Y * J6) i j = (if j = 0 then Y i 1 else 0) - (if j = 1 then Y i 0 else 0) := by
      intro i j
      simp only [J6, unitTurn, Matrix.mul_apply, Matrix.of_apply, mul_sub, Finset.sum_sub_distrib,
        mul_ite, mul_one, mul_zero]
      congr 1
      · rw [Finset.sum_eq_single 1]
        · by_cases hj : j = 0 <;> simp [hj]
        · intro k _ hk
          simp [hk]
        · simp
      · rw [Finset.sum_eq_single 0]
        · by_cases hj : j = 1 <;> simp [hj]
        · intro k _ hk
          simp [hk]
        · simp
    have c20 : Y 2 0 = 0 := hc 2 0 (by decide)
    have c21 : Y 2 1 = 0 := hc 2 1 (by decide)
    have c30 : Y 3 0 = 0 := hc 3 0 (by decide)
    have c31 : Y 3 1 = 0 := hc 3 1 (by decide)
    have c40 : Y 4 0 = 0 := hc 4 0 (by decide)
    have c41 : Y 4 1 = 0 := hc 4 1 (by decide)
    have c50 : Y 5 0 = 0 := hc 5 0 (by decide)
    have c51 : Y 5 1 = 0 := hc 5 1 (by decide)
    have c02 : Y 0 2 = 0 := hc 0 2 (by decide)
    have c03 : Y 0 3 = 0 := hc 0 3 (by decide)
    have c04 : Y 0 4 = 0 := hc 0 4 (by decide)
    have c05 : Y 0 5 = 0 := hc 0 5 (by decide)
    have c12 : Y 1 2 = 0 := hc 1 2 (by decide)
    have c13 : Y 1 3 = 0 := hc 1 3 (by decide)
    have c14 : Y 1 4 = 0 := hc 1 4 (by decide)
    have c15 : Y 1 5 = 0 := hc 1 5 (by decide)
    have s10 := hskew 0 1
    ext i j
    rw [hJl, hJr]
    fin_cases i <;> fin_cases j <;>
      simp [hdiag, c20, c21, c30, c31, c40, c41, c50, c51, c02, c03, c04, c05, c12, c13, c14, c15,
        s10]

/-! ## The one theorem -/

/-- **The balanced cone of the held plane, with its clock.** For a balanced `v` normalized to `|d| = 1`:
`|u| = 1` (a point of `S¹ × S³`); the frame `Jv, iu, ju, ku` is orthogonal to `v`, `g`-orthonormal
with signs `(+, −, −, −)`, and with `v` a basis of `v^⊥`, so the quotient `v^⊥/ℝv` has signature
`(1, 3)`; its one positive direction is `Jv`, the rotation of the held plane; and the kept rotations that
commute with all kept rotations are exactly the multiples of `J`. -/
theorem balanced_cone (v : Fin 6 → ℝ) (hv : OnCone v) (hr : r2 v = 1) :
    s2 v = 1 ∧
      (∀ i j, g6 (frame v i) (frame v j) = if i = j then (if i = 0 then 1 else -1) else 0) ∧
      (∀ i, g6 v (frame v i) = 0) ∧
      frame v 0 = J6 *ᵥ v ∧
      (∀ w, g6 v w = 0 → ∃! c : Fin 5 → ℝ, w = c 0 • v + c 1 • frame v 0 + c 2 • frame v 1 +
        c 3 • frame v 2 + c 4 • frame v 3) ∧
      (∀ X, CentralKept6 X ↔ ∃ a : ℝ, X = a • J6) := by
  have hs : s2 v = 1 := by
    obtain ⟨_, h⟩ := cone_radius v hv
    rw [h, hr]
  exact ⟨hs, frame_orthonormal v hr hs, frame_perp v, clock_is_central v,
    fun w hw => cone_decomposition v hr hs w hw, central_kept_iff⟩

end Comparison.GroupsContinuumLaw
