module

public import Comparison.System.Existence.Ext.Exterior

/-
A copy of `Comparison/Existence/Spin.lean`
(commit 3b95f8b), changed only in its namespace (`Comparison` to `Comparison.SysExt`) and in the import
paths of the copied files. The original cannot enter the root `Comparison.System`: `Existence/Exterior.lean`
declares `Comparison.volume` and `Comparison.half_mul_self`, as do `Colour/GramTerm.lean` and
`Elements/Half.lean`.
-/

/-!
# Book VII. Spin one half, the phase of the whole, the parallel rotations (Propositions 33-36)

On the exterior algebra of `n` directions
(`Exterior.lean`).

* `Jx_single`: `J_a f_S = (−1)^{#{c ∈ S∖{a} : c < a}} f_{S △ {a}}` (Proposition 33).
* `rotor`: `R_ab(ϑ) = cos(ϑ/2) + sin(ϑ/2) J_aJ_b`; `rotor_mul`: `R(ϑ)R(ϑ') = R(ϑ + ϑ')`;
  `rotor_two_pi`: `R(2π) = −1`; `rotor_conj_a`, `rotor_conj_b`: `R(ϑ) J_a R(−ϑ) = cos ϑ J_a − sin ϑ J_b`
  and `R(ϑ) J_b R(−ϑ) = sin ϑ J_a + cos ϑ J_b`: the step turns the plane by `ϑ` while its amplitude
  comes back only after `4π` (Proposition 34).
* `half_loop_sq`: `(f_xf_y)² = −θ_D(x)θ_D(y)` for `x ≠ y`; `loop_counts`: `C(k,2) + C(6−k,2)` planes
  within a side and `k(6 − k)` across (Proposition 34).
* `phase_compl`: calling the other part divided turns the phase `i^{|S|}` into `−\overline{i^{|S|}}`
  (Proposition 35).
* `comm_mul`: `[T, XY] = [T, X]Y + X[T, Y]`; `Tx_comm_chain`: `[T_ab, T_bc] = T_ac` for distinct
  `a, b, c`; `Tx_comm_disjoint`: `[T_ab, T_cd] = 0` for disjoint pairs (Proposition 36).
-/

@[expose] public section

namespace Comparison.SysExt

open Finset

section General

variable {n : ℕ} {R : Type*} [CommRing R]

/-- **`J_a f_S = ± f_{S △ {a}}`**, with the sign `(−1)^{#{c ∈ S∖{a} : c < a}}`. -/
theorem Jx_single (a : Fin n) (S : Finset (Fin n)) :
    Jx (R := R) a (Pi.single S (1 : R)) =
      extSign (R := R) a (S.erase a) • (Pi.single (symmDiff S {a}) (1 : R) : Finset (Fin n) → R) := by
  funext T
  simp only [Jx, LinearMap.add_apply, Pi.add_apply, εx_apply, ιx_apply, Pi.smul_apply,
    smul_eq_mul, Pi.single_apply]
  by_cases ha : a ∈ S
  · -- J removes a
    have hS : symmDiff S {a} = S.erase a := by
      ext x
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_erase]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨h2, h1⟩
        · exact absurd (h1 ▸ ha) h2
      · rintro ⟨h1, h2⟩
        exact Or.inl ⟨h2, h1⟩
    rw [hS]
    by_cases hT : a ∈ T
    · have : T.erase a ≠ S := fun h => by
        have := h ▸ Finset.notMem_erase a T
        exact this ha
      have h2 : T ≠ S.erase a := fun h => Finset.notMem_erase a S (h ▸ hT)
      simp [hT, this, h2]
    · by_cases hT2 : T = S.erase a
      · subst hT2
        simp [Finset.insert_erase ha]
      · have : insert a T ≠ S := fun h => hT2 (by rw [← h, Finset.erase_insert hT])
        simp [hT, hT2, this]
  · -- J adds a
    have hS : symmDiff S {a} = insert a S := by
      ext x
      simp only [Finset.mem_symmDiff, Finset.mem_singleton, Finset.mem_insert]
      constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact Or.inr h1
        · exact Or.inl h1
      · rintro (h1 | h1)
        · exact Or.inr ⟨h1, h1 ▸ ha⟩
        · exact Or.inl ⟨h1, fun h => ha (h ▸ h1)⟩
    rw [hS, Finset.erase_eq_of_notMem ha]
    by_cases hT : a ∈ T
    · by_cases hT2 : T = insert a S
      · subst hT2
        simp [Finset.erase_insert ha]
      · have : T.erase a ≠ S := fun h => hT2 (by rw [← h, Finset.insert_erase hT])
        simp [hT, hT2, this]
    · have h1 : insert a T ≠ S := fun h => ha (h ▸ Finset.mem_insert_self a T)
      have h2 : T ≠ insert a S := fun h => hT (h ▸ Finset.mem_insert_self a S)
      simp [hT, h1, h2]

/-- The commutator obeys the product rule: `[T, XY] = [T, X]Y + X[T, Y]`. -/
theorem comm_mul {A : Type*} [Ring A] (T X Y : A) :
    T * (X * Y) - X * Y * T = (T * X - X * T) * Y + X * (T * Y - Y * T) := by
  noncomm_ring

/-- **The parallel rotations close as the rotations of the six:** `[T_ab, T_bc] = T_ac` for distinct
`a, b, c`. -/
theorem Tx_comm_chain {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    Tx (R := R) a b * Tx b c - Tx b c * Tx a b = Tx a c := by
  have h1 := comm_mul (Tx (R := R) a b) (εx b) (ιx c)
  have h2 := comm_mul (Tx (R := R) a b) (εx c) (ιx b)
  rw [Tx_εx, Tx_ιx] at h1 h2
  simp only [hab, hbc, hac, Ne.symm hab, Ne.symm hbc, Ne.symm hac, ↓reduceIte, sub_zero,
    zero_sub, zero_mul, mul_zero, add_zero, zero_add] at h1 h2
  have : Tx (R := R) a b * Tx b c - Tx b c * Tx a b =
      (Tx a b * (εx b * ιx c) - εx b * ιx c * Tx a b) -
        (Tx a b * (εx c * ιx b) - εx c * ιx b * Tx a b) := by
    simp only [Tx]
    noncomm_ring
  rw [this, h1, h2, Tx]

/-- **Rotations of disjoint planes commute:** `[T_ab, T_cd] = 0` for `{a, b} ∩ {c, d} = ∅`. -/
theorem Tx_comm_disjoint {a b c d : Fin n} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) : Tx (R := R) a b * Tx c d - Tx c d * Tx a b = 0 := by
  have h1 := comm_mul (Tx (R := R) a b) (εx c) (ιx d)
  have h2 := comm_mul (Tx (R := R) a b) (εx d) (ιx c)
  rw [Tx_εx, Tx_ιx] at h1 h2
  simp only [hac, had, hbc, hbd, Ne.symm hac, Ne.symm had, Ne.symm hbc, Ne.symm hbd, ↓reduceIte,
    sub_zero, zero_mul, mul_zero, add_zero] at h1 h2
  have : Tx (R := R) a b * Tx c d - Tx c d * Tx a b =
      (Tx a b * (εx c * ιx d) - εx c * ιx d * Tx a b) -
        (Tx a b * (εx d * ιx c) - εx d * ιx c * Tx a b) := by
    simp only [Tx]
    noncomm_ring
  rw [this, h1, h2, sub_zero]

end General

/-! ## Spin one half: the rotor -/

section Rotor

variable {n : ℕ}

/-- **The rotation of the step in the plane `(a, b)`:** `R(ϑ) = cos(ϑ/2) + sin(ϑ/2) J_aJ_b`. -/
noncomputable def rotor (a b : Fin n) (θ : ℝ) : Module.End ℝ (Finset (Fin n) → ℝ) :=
  Real.cos (θ / 2) • 1 + Real.sin (θ / 2) • (Jx a * Jx b)

/-- `R(ϑ) R(ϑ') = R(ϑ + ϑ')`. -/
theorem rotor_mul {a b : Fin n} (hab : a ≠ b) (θ θ' : ℝ) :
    rotor a b θ * rotor a b θ' = rotor a b (θ + θ') := by
  have hsq : (Jx (R := ℝ) a * Jx b) * (Jx a * Jx b) = -1 := by
    rw [show Jx (R := ℝ) a * Jx b * (Jx a * Jx b) = Jx a * Jx b * Jx a * Jx b by noncomm_ring,
      shortest_loop hab]
  simp only [rotor, add_mul, mul_add, smul_mul_smul_comm, one_mul, mul_one, hsq]
  rw [show (θ + θ') / 2 = θ / 2 + θ' / 2 by ring, Real.cos_add, Real.sin_add]
  module

/-- **Spin one half:** `R(2π) = −1`, while the rotation of the plane is the identity. -/
theorem rotor_two_pi (a b : Fin n) : rotor a b (2 * Real.pi) = -1 := by
  simp [rotor, show 2 * Real.pi / 2 = Real.pi by ring]

theorem rotor_zero (a b : Fin n) : rotor a b 0 = 1 := by
  simp [rotor]

theorem Jx_JJ {a b : Fin n} (hab : a ≠ b) :
    Jx (R := ℝ) a * (Jx a * Jx b) = Jx b ∧ (Jx (R := ℝ) a * Jx b) * Jx a = -Jx b ∧
    Jx (R := ℝ) b * (Jx a * Jx b) = -Jx a ∧ (Jx (R := ℝ) a * Jx b) * Jx b = Jx a := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← mul_assoc, Jx_mul_self, one_mul]
  · rw [mul_assoc, Jx_anticomm (Ne.symm hab), mul_neg, ← mul_assoc, Jx_mul_self, one_mul]
  · rw [← mul_assoc, Jx_anticomm (Ne.symm hab), neg_mul, mul_assoc, Jx_mul_self, mul_one]
  · rw [mul_assoc, Jx_mul_self, mul_one]

/-- **The step turns its plane:** `R(ϑ) J_a R(−ϑ) = cos ϑ J_a − sin ϑ J_b`. -/
theorem rotor_conj_a {a b : Fin n} (hab : a ≠ b) (θ : ℝ) :
    rotor a b θ * Jx a * rotor a b (-θ) = Real.cos θ • Jx a - Real.sin θ • Jx b := by
  obtain ⟨h1, h2, h3, h4⟩ := Jx_JJ hab
  have hsq : (Jx (R := ℝ) a * Jx b) * (Jx a * Jx b) = -1 := by
    rw [show Jx (R := ℝ) a * Jx b * (Jx a * Jx b) = Jx a * Jx b * Jx a * Jx b by noncomm_ring,
      shortest_loop hab]
  have e : (Jx (R := ℝ) a * Jx b) * Jx a * (Jx a * Jx b) = Jx a := by
    rw [h2, neg_mul, h3, neg_neg]
  simp only [rotor, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, h1, h2, h3, h4, neg_mul, mul_neg, neg_neg, smul_neg]
  rw [show -θ / 2 = -(θ / 2) by ring, Real.cos_neg, Real.sin_neg,
    show θ = 2 * (θ / 2) by ring, Real.cos_two_mul', Real.sin_two_mul]
  simp only [show 2 * (θ / 2) / 2 = θ / 2 by ring]
  module

/-- `R(ϑ) J_b R(−ϑ) = sin ϑ J_a + cos ϑ J_b`. -/
theorem rotor_conj_b {a b : Fin n} (hab : a ≠ b) (θ : ℝ) :
    rotor a b θ * Jx b * rotor a b (-θ) = Real.sin θ • Jx a + Real.cos θ • Jx b := by
  obtain ⟨h1, h2, h3, h4⟩ := Jx_JJ hab
  have e : (Jx (R := ℝ) a * Jx b) * Jx b * (Jx a * Jx b) = Jx b := by
    rw [h4, h1]
  simp only [rotor, add_mul, mul_add, smul_mul_assoc, mul_smul_comm,
    one_mul, mul_one, h1, h2, h3, h4, neg_mul, mul_neg, neg_neg, smul_neg]
  rw [show -θ / 2 = -(θ / 2) by ring, Real.cos_neg, Real.sin_neg,
    show θ = 2 * (θ / 2) by ring, Real.cos_two_mul', Real.sin_two_mul]
  simp only [show 2 * (θ / 2) / 2 = θ / 2 by ring]
  module

end Rotor

/-! ## The loops with the square root of the sign, and the phase -/

/-- **`(f_xf_y)² = −θ_D(x)θ_D(y)`** for `x ≠ y`: `−1` within a side, `+1` across. -/
theorem half_loop_sq (D : Finset (Fin 6)) {x y : Fin 6} (hxy : x ≠ y) :
    (halfStep D x * halfStep D y) * (halfStep D x * halfStep D y) =
      (-((if x ∈ D then -1 else 1 : ℂ) * (if y ∈ D then -1 else 1))) • 1 := by
  calc halfStep D x * halfStep D y * (halfStep D x * halfStep D y)
      = halfStep D x * (halfStep D y * halfStep D x) * halfStep D y := by noncomm_ring
    _ = halfStep D x * (-(halfStep D x * halfStep D y)) * halfStep D y := by
        rw [half_anticomm_ne D (Ne.symm hxy)]
    _ = -((halfStep D x * halfStep D x) * (halfStep D y * halfStep D y)) := by noncomm_ring
    _ = _ := by
        rw [half_mul_self, half_mul_self, smul_mul_smul_comm, one_mul, neg_smul]

/-- **Within a side and across:** `C(k,2) + C(6−k,2)` planes keep the sides, `k(6 − k)` cross. -/
theorem loop_counts : ∀ D : Finset (Fin 6),
    (Finset.univ.filter fun p : Fin 6 × Fin 6 => p.1 < p.2 ∧ (p.1 ∈ D ↔ p.2 ∈ D)).card =
      D.card.choose 2 + (6 - D.card).choose 2 ∧
    (Finset.univ.filter fun p : Fin 6 × Fin 6 => p.1 < p.2 ∧ ¬(p.1 ∈ D ↔ p.2 ∈ D)).card =
      D.card * (6 - D.card) := by
  decide +kernel

/-- **Calling the other part divided turns the phase into `−` its conjugate:**
`i^{|Sᶜ|} = −\overline{i^{|S|}}`. -/
theorem phase_compl (S : Finset (Fin 6)) :
    Complex.I ^ Sᶜ.card = -star (Complex.I ^ S.card) := by
  rw [Finset.card_compl, Fintype.card_fin]
  have hS : S.card ≤ 6 := by simpa using Finset.card_le_univ S
  interval_cases h : S.card <;> simp [pow_succ, Complex.ext_iff]

end Comparison.SysExt

end
