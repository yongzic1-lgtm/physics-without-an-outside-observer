import Comparison.Existence.Table

/-!
# The two clocks are one quaternion triple (Prop. S41a; formulas (4), (5))

Proposition S41a. With `H_k = e^{iπγ_k/4} = (1 + iγ_k)/√2` (`halfStep`):

* `halfStep_eq_expIγ`: `H_k = e^{iπγ_k/4}`; `halfStep_sq`: **`H_k² = iγ_k`**; `halfStep_unitary`:
  `H_k H_k† = 1`.
* `halfStep_carries_clock`: **`H_k (iγ_h) H_k† = γ_hγ_k`** for `h ≠ k`: the own clock of the plane
  `{n, h}` is carried onto the common clock of the plane `{h, k}` by the square root of the sign of the step between them.
* `quaternion_triple`: **`T₁ = iγ_h`, `T₂ = γ_hγ_k`, `T₃ = iγ_k` have `T_a² = −1`, `T₁T₂ = T₃`,
  `T₂T₃ = T₁`, `T₃T₁ = T₂`.**
* `halfStep_on_singlet`, `halfStep_on_lastDirection`, `halfStep_on_other`: on the six, `H_k ⊗ H_k` takes `Ω` to
  `iℓ_k`, `iℓ_k` to `−Ω` and fixes `ℓ_t` for `t ≠ k`: the quarter turn of the plane of the singlet and `k`.
* `central_kept_iff_card`: **the kept rotations of a division of the six have a nonzero central element
  exactly when the division is of type `2¦4`** (a part of two directions); `no_clock_one_five`: the
  last-step direction alone (`1¦5`) keeps `so(5)` and has no clock.
-/

namespace Comparison.Formulas

open Matrix Complex Kronecker

/-! ## the square-root step `H_k` -/

/-- `1/√2` as a complex number. -/
noncomputable def rt : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹

theorem rt_eq : rt = ((Real.sqrt 2 / 2 : ℝ) : ℂ) := by
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : Real.sqrt 2 ≠ 0 := by positivity
  have h : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
    field_simp
    linarith [hs]
  rw [rt, ← Complex.ofReal_inv, h]

/-- **the square-root step** `H_k = (1 + iγ_k)/√2`. -/
noncomputable def halfStep (k : Fin 5) : Matrix Four Four ℂ := rt • (1 + I • γ k)

/-- `H_k = e^{iπγ_k/4} = cos(π/4) + i sin(π/4) γ_k`. -/
theorem halfStep_eq_expIγ (k : Fin 5) : halfStep k = expIγ (Real.pi / 4) k := by
  rw [halfStep, expIγ, Real.cos_pi_div_four, Real.sin_pi_div_four, rt_eq, smul_add, smul_smul,
    mul_comm]

/-- **`H_k² = iγ_k`.** -/
theorem halfStep_sq (k : Fin 5) : halfStep k * halfStep k = I • γ k := by
  rw [halfStep_eq_expIγ, expIγ_add, show Real.pi / 4 + Real.pi / 4 = Real.pi / 2 by ring,
    quarter_turn]

theorem expIγ_conjTranspose (a : ℝ) (h : Fin 5) : (expIγ a h)ᴴ = expIγ (-a) h := by
  simp only [expIγ, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_one,
    γ_conjTranspose, Real.cos_neg, Real.sin_neg, star_mul', Complex.star_def,
    Complex.conj_ofReal, Complex.conj_I]
  push_cast
  congr 2
  ring

/-- `H_k† = e^{−iπγ_k/4}`. -/
theorem halfStep_conjTranspose (k : Fin 5) : (halfStep k)ᴴ = expIγ (-(Real.pi / 4)) k := by
  rw [halfStep_eq_expIγ, expIγ_conjTranspose]

/-- `H_k` is unitary. -/
theorem halfStep_unitary (k : Fin 5) : halfStep k * (halfStep k)ᴴ = 1 := by
  rw [halfStep_conjTranspose, halfStep_eq_expIγ, expIγ_unitary]

/-- A line anticommuting with `γ_k` passes the rotation `e^{iaγ_k}` reversed. -/
theorem γ_mul_expIγ (a : ℝ) {h k : Fin 5} (hhk : h ≠ k) :
    γ h * expIγ a k = expIγ (-a) k * γ h := by
  simp only [expIγ, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one, Matrix.one_mul, Real.cos_neg, Real.sin_neg, γ_anticomm hhk, smul_neg]
  push_cast
  module

theorem expIγ_mul_γ (a : ℝ) {h k : Fin 5} (hhk : h ≠ k) :
    expIγ a k * γ h = γ h * expIγ (-a) k := by
  rw [γ_mul_expIγ (-a) hhk, neg_neg]

/-- **the square-root step carries the own clock of `{n, h}` onto the common clock of the plane
`{h, k}`:** `H_k (iγ_h) H_k† = γ_hγ_k`. -/
theorem halfStep_carries_clock {h k : Fin 5} (hhk : h ≠ k) :
    halfStep k * (I • γ h) * (halfStep k)ᴴ = γ h * γ k := by
  rw [halfStep_conjTranspose, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc,
    γ_mul_expIγ _ hhk, neg_neg, ← Matrix.mul_assoc, ← halfStep_eq_expIγ, halfStep_sq,
    Matrix.smul_mul, smul_smul, I_mul_I, γ_anticomm (Ne.symm hhk), smul_neg, neg_smul, one_smul,
    neg_neg]

/-! ## One quaternion triple -/

/-- **The two clocks and the line's quarter step are one quaternion triple:**
`T₁ = iγ_h`, `T₂ = γ_hγ_k`, `T₃ = iγ_k` with `T_a² = −1`, `T₁T₂ = T₃`, `T₂T₃ = T₁`, `T₃T₁ = T₂`. -/
theorem quaternion_triple {h k : Fin 5} (hhk : h ≠ k) :
    (I • γ h) * (I • γ h) = -1 ∧ (γ h * γ k) * (γ h * γ k) = -1 ∧ (I • γ k) * (I • γ k) = -1 ∧
    (I • γ h) * (γ h * γ k) = I • γ k ∧ (γ h * γ k) * (I • γ k) = I • γ h ∧
    (I • γ k) * (I • γ h) = γ h * γ k := by
  have hkh : γ k * γ h = -(γ h * γ k) := γ_anticomm (Ne.symm hhk)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [smul_mul_smul_comm, γ_mul_self, I_mul_I, neg_one_smul]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (γ k), hkh, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.mul_assoc, γ_mul_self, Matrix.mul_one, γ_mul_self]
  · rw [smul_mul_smul_comm, γ_mul_self, I_mul_I, neg_one_smul]
  · rw [Matrix.smul_mul, ← Matrix.mul_assoc, γ_mul_self, Matrix.one_mul]
  · rw [Matrix.mul_smul, Matrix.mul_assoc, γ_mul_self, Matrix.mul_one]
  · rw [smul_mul_smul_comm, I_mul_I, hkh, neg_one_smul, neg_neg]

/-! ## the square-root step on the six -/

/-- `H_k ⊗ H_k` takes the singlet to `iℓ_k`. -/
theorem halfStep_on_singlet (k : Fin 5) :
    (halfStep k ⊗ₖ halfStep k) *ᵥ Ω = I • ((γ k ⊗ₖ 1) *ᵥ Ω) := by
  rw [halfStep_eq_expIγ, clock_turns_singlet, show 2 * (Real.pi / 4) = Real.pi / 2 by ring,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp

/-- `H_k ⊗ H_k` takes `iℓ_k` to `−Ω`. -/
theorem halfStep_on_lastDirection (k : Fin 5) :
    (halfStep k ⊗ₖ halfStep k) *ᵥ (I • ((γ k ⊗ₖ 1) *ᵥ Ω)) = -Ω := by
  rw [← halfStep_on_singlet, Matrix.mulVec_mulVec, ← Matrix.mul_kronecker_mul, halfStep_eq_expIγ,
    expIγ_add, show Real.pi / 4 + Real.pi / 4 = Real.pi / 2 by ring, clock_turns_singlet,
    show 2 * (Real.pi / 2) = Real.pi by ring, Real.cos_pi, Real.sin_pi]
  simp

/-- `(1 ⊗ e^{iaγ_k}) Ω = (e^{iaγ_k} ⊗ 1) Ω`. -/
theorem one_kron_expIγ_singlet (a : ℝ) (k : Fin 5) :
    ((1 : Matrix Four Four ℂ) ⊗ₖ expIγ a k) *ᵥ Ω = (expIγ a k ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω := by
  unfold expIγ
  exact one_kron_line_singlet _ _ k

/-- `H_k ⊗ H_k` fixes the vector states `ℓ_t`, `t ≠ k`. -/
theorem halfStep_on_other {k t : Fin 5} (htk : t ≠ k) :
    (halfStep k ⊗ₖ halfStep k) *ᵥ ((γ t ⊗ₖ 1) *ᵥ Ω) = (γ t ⊗ₖ 1) *ᵥ Ω := by
  have hH : halfStep k * γ t = γ t * expIγ (-(Real.pi / 4)) k := by
    rw [halfStep_eq_expIγ, expIγ_mul_γ _ htk]
  have hnone : (expIγ (-(Real.pi / 4)) k ⊗ₖ halfStep k) *ᵥ Ω = Ω := by
    have e1 : expIγ (-(Real.pi / 4)) k ⊗ₖ halfStep k =
        (expIγ (-(Real.pi / 4)) k ⊗ₖ (1 : Matrix Four Four ℂ)) *
          ((1 : Matrix Four Four ℂ) ⊗ₖ halfStep k) := by
      rw [← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
    rw [e1, ← Matrix.mulVec_mulVec, halfStep_eq_expIγ, one_kron_expIγ_singlet, Matrix.mulVec_mulVec,
      ← Matrix.mul_kronecker_mul, Matrix.mul_one, expIγ_add, neg_add_cancel]
    simp [expIγ]
  have e2 : (γ t * expIγ (-(Real.pi / 4)) k) ⊗ₖ halfStep k =
      (γ t ⊗ₖ (1 : Matrix Four Four ℂ)) * (expIγ (-(Real.pi / 4)) k ⊗ₖ halfStep k) := by
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_kronecker_mul, hH, Matrix.mul_one, e2,
    ← Matrix.mulVec_mulVec, hnone]

/-! ## Where a division has a clock -/

/-- A kept rotation of the division `D` of the six: antisymmetric, commuting with `θ_D`. -/
def KeptAt (D : Finset (Fin 6)) (X : Matrix (Fin 6) (Fin 6) ℝ) : Prop :=
  Xᵀ = -X ∧ X * thetaD D = thetaD D * X

/-- A central kept rotation: kept, and commuting with every kept rotation. -/
def CentralAt (D : Finset (Fin 6)) (X : Matrix (Fin 6) (Fin 6) ℝ) : Prop :=
  KeptAt D X ∧ ∀ Y, KeptAt D Y → X * Y = Y * X

theorem thetaD_compl (D : Finset (Fin 6)) : thetaD Dᶜ = -thetaD D := by
  ext i j
  simp only [thetaD, Matrix.diagonal_apply, Matrix.neg_apply, Finset.mem_compl]
  by_cases hij : i = j
  · subst hij
    by_cases hi : i ∈ D <;> simp [hi]
  · simp [hij]

theorem keptAt_compl (D : Finset (Fin 6)) (X : Matrix (Fin 6) (Fin 6) ℝ) :
    KeptAt Dᶜ X ↔ KeptAt D X := by
  simp only [KeptAt, thetaD_compl, Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem centralAt_compl (D : Finset (Fin 6)) (X : Matrix (Fin 6) (Fin 6) ℝ) :
    CentralAt Dᶜ X ↔ CentralAt D X := by
  simp only [CentralAt, keptAt_compl]

theorem unitTurn_comm_thetaD (D : Finset (Fin 6)) (b c : Fin 6) (h : b ∈ D ↔ c ∈ D) :
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

/-- **Only a part of two directions carries a clock:** a nonzero central kept rotation forces `|D| = 2`
or `|D| = 4`. -/
theorem card_of_central {D : Finset (Fin 6)} {X : Matrix (Fin 6) (Fin 6) ℝ} (hX : CentralAt D X)
    (hne : X ≠ 0) : D.card = 2 ∨ D.card = 4 := by
  have hskew : ∀ i j, X j i = -X i j := fun i j => by
    have := congrFun (congrFun hX.1.1 i) j
    simpa using this
  obtain ⟨a, b, hab0⟩ : ∃ a b, X a b ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hne (Matrix.ext hall)
  have hab : a ≠ b := by
    rintro rfl
    have := hskew a a
    exact hab0 (by linarith)
  have hcent : ∀ b c : Fin 6, (b ∈ D ↔ c ∈ D) → X * unitTurn b c = unitTurn b c * X :=
    fun b c hbc => hX.2 _ ⟨unitTurn_transpose b c, unitTurn_comm_thetaD D b c hbc⟩
  obtain ⟨hside, hthird⟩ := clock_dividedSet D X hX.1.2 hcent hab hab0
  by_cases ha : a ∈ D
  · left
    have hb : b ∈ D := hside.mp ha
    have hD : D = {a, b} := by
      ext c
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hc
        exact hthird c ⟨fun _ => ha, fun _ => hc⟩
      · rintro (rfl | rfl)
        · exact ha
        · exact hb
    rw [hD, Finset.card_pair hab]
  · right
    have hb : b ∉ D := fun hb => ha (hside.mpr hb)
    have hDc : Dᶜ = {a, b} := by
      ext c
      simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hc
        exact hthird c ⟨fun h => absurd h hc, fun h => absurd h ha⟩
      · rintro (rfl | rfl)
        · exact ha
        · exact hb
    have h1 := Finset.card_compl D
    rw [hDc, Finset.card_pair hab, Fintype.card_fin] at h1
    omega

theorem unitTurn_mul_apply {n : ℕ} (a b : Fin n) (Y : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (unitTurn a b * Y) i j = (if i = a then Y b j else 0) - (if i = b then Y a j else 0) := by
  rw [Matrix.mul_apply]
  simp only [unitTurn, Matrix.of_apply, sub_mul, Finset.sum_sub_distrib]
  congr 1
  · by_cases hi : i = a <;> simp [hi]
  · by_cases hi : i = b <;> simp [hi]

theorem mul_unitTurn_apply {n : ℕ} (a b : Fin n) (Y : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    (Y * unitTurn a b) i j = (if j = b then Y i a else 0) - (if j = a then Y i b else 0) := by
  rw [Matrix.mul_apply]
  simp only [unitTurn, Matrix.of_apply, mul_sub, Finset.sum_sub_distrib]
  congr 1
  · by_cases hj : j = b <;> simp [hj]
  · by_cases hj : j = a <;> simp [hj]

/-- At a part of two directions `{a, b}` the unit rotation of that plane is a central kept rotation. -/
theorem unitTurn_central_pair {a b : Fin 6} (hab : a ≠ b) :
    CentralAt {a, b} (unitTurn a b) := by
  refine ⟨⟨unitTurn_transpose a b, unitTurn_comm_thetaD _ a b (by simp)⟩, ?_⟩
  intro Y hY
  have hskew : ∀ i j, Y j i = -Y i j := fun i j => by
    have := congrFun (congrFun hY.1 i) j
    simpa using this
  have hcross : ∀ i j, ¬(i ∈ ({a, b} : Finset (Fin 6)) ↔ j ∈ ({a, b} : Finset (Fin 6))) →
      Y i j = 0 := fun i j h => kept_entry _ Y hY.2 h
  have h1 : ∀ x y, (x = a ∨ x = b) → ¬(y = a ∨ y = b) → Y x y = 0 := fun x y hx hy =>
    hcross x y (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
  have h2 : ∀ x y, ¬(x = a ∨ x = b) → (y = a ∨ y = b) → Y x y = 0 := fun x y hx hy =>
    hcross x y (by simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
  have hYaa : Y a a = 0 := by have := hskew a a; linarith
  have hYbb : Y b b = 0 := by have := hskew b b; linarith
  ext i j
  rw [unitTurn_mul_apply, mul_unitTurn_apply]
  by_cases hia : i = a
  · rw [if_pos hia, if_neg (by rw [hia]; exact hab), hia]
    by_cases hja : j = a
    · rw [if_neg (by rw [hja]; exact hab), if_pos hja, hja, hskew a b]
      ring
    · by_cases hjb : j = b
      · rw [if_pos hjb, if_neg hja, hjb, hYbb, hYaa]
      · rw [if_neg hjb, if_neg hja, h1 b j (Or.inr rfl) (by tauto)]
  · by_cases hib : i = b
    · rw [if_neg hia, if_pos hib, hib]
      by_cases hja : j = a
      · rw [if_neg (by rw [hja]; exact hab), if_pos hja, hja, hYaa, hYbb]
      · by_cases hjb : j = b
        · rw [if_pos hjb, if_neg hja, hjb, hskew a b]
          ring
        · rw [if_neg hjb, if_neg hja, h1 a j (Or.inl rfl) (by tauto)]
    · rw [if_neg hia, if_neg hib]
      by_cases hja : j = a
      · rw [if_neg (by rw [hja]; exact hab), if_pos hja, h2 i b (by tauto) (Or.inr rfl)]
      · by_cases hjb : j = b
        · rw [if_pos hjb, if_neg hja, h2 i a (by tauto) (Or.inl rfl)]
        · rw [if_neg hjb, if_neg hja]

/-- **The kept rotations of a division have a nonzero central element exactly at type `2¦4`.** -/
theorem central_kept_iff_card (D : Finset (Fin 6)) :
    (∃ X, CentralAt D X ∧ X ≠ 0) ↔ D.card = 2 ∨ D.card = 4 := by
  constructor
  · rintro ⟨X, hX, hne⟩
    exact card_of_central hX hne
  · have hu : ∀ a b : Fin 6, a ≠ b → unitTurn a b ≠ 0 := by
      intro a b hab h
      have := congrFun (congrFun h a) b
      simp [unitTurn, hab] at this
    rintro (h2 | h4)
    · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp h2
      exact ⟨unitTurn a b, unitTurn_central_pair hab, hu a b hab⟩
    · have hc : Dᶜ.card = 2 := by
        rw [Finset.card_compl, Fintype.card_fin, h4]
      obtain ⟨a, b, hab, hD⟩ := Finset.card_eq_two.mp hc
      refine ⟨unitTurn a b, ?_, hu a b hab⟩
      rw [← centralAt_compl, hD]
      exact unitTurn_central_pair hab

/-- **The last-step direction alone has no clock:** a division of type `1¦5` (one direction divided) keeps
`so(5)`, whose centre is zero. -/
theorem no_clock_one_five (D : Finset (Fin 6)) (hD : D.card = 1) (X : Matrix (Fin 6) (Fin 6) ℝ)
    (hX : CentralAt D X) : X = 0 := by
  by_contra hne
  rcases card_of_central hX hne with h | h <;> omega

/-- The types `0¦6` and `3¦3` have no clock either. -/
theorem no_clock_zero_three (D : Finset (Fin 6)) (hD : D.card = 0 ∨ D.card = 3)
    (X : Matrix (Fin 6) (Fin 6) ℝ) (hX : CentralAt D X) : X = 0 := by
  by_contra hne
  rcases card_of_central hX hne with h | h <;> omega

end Comparison.Formulas
