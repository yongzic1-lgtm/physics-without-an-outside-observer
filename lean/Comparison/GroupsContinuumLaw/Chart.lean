import Comparison.Existence.IharaBass

/-!
# The two-sheet `A₄` chart lifting the step `B` (the continuum limit, part four)

The five line transitions become involutions on a finite periodic chart: the vertices are
`(L/NL) × {0, 1}`, `L = A₄ = ℤ⁵ ∩ 𝟏^⊥`, written in the basis `b_t = e_t − e_4` (`t < 4`), `b_4 = 0`;
the transition `t` steps from sheet `0` by `+b_t` to sheet `1` and back by `−b_t`. Proved here, for every
even `N`:

* `transitionN_involutive`: each transition is an involution; `transitionN_injective`: the five transitions of a vertex reach
  five different vertices (`N ≥ 2`); `card_VN`, `card_lifted`: `2N⁴` vertices, `10N⁴` last-line states.
* `phi_transition`: the sixteen two-spinor states as even parity vectors, `φ(transition t k) = φ(k) + g_t`, `g_t` the
  complement of the line `t`.
* `piN_transition`: **the chart covers the sixteen two-spinor states:** `π(Γ_t x) = π(x) + g_t`; `piN_even`: every
  vertex lands on an even vector.
* `lifted_B_intertwines`: **`B_N · Lift = Lift · B`**: the unchanged non-backtracking step on the chart
  covers the eighty-state step `B = stepOp transitionMat` of the sixteen two-spinor states.
* `chartStep_row`, `chartStep_col`: four continuations into and out of every lifted state;
  `chart_two`: at `N = 2`, `32` vertices, `160` states and `640` transitions.
-/

namespace Comparison.GroupsContinuumLaw

open Matrix

variable {N : ℕ} [NeZero N]

/-- The chart's positions `L/NL`, coordinates in the basis `b_0, …, b_3`. -/
abbrev ZN (N : ℕ) := Fin 4 → ZMod N

/-- The vertices: a position and a sheet. -/
abbrev VN (N : ℕ) := ZN N × Bool

/-- The displacement of the transition `t`: `b_t = e_t` for `t < 4`, `b_4 = 0`. -/
def bN (t : Fin 5) : ZN N := fun i => if (i : ℕ) = (t : ℕ) then 1 else 0

/-- The transition `t`: from sheet `0` by `+b_t` to sheet `1`, from sheet `1` by `−b_t` to sheet `0`. -/
def transitionN (t : Fin 5) : VN N → VN N
  | (z, false) => (z + bN t, true)
  | (z, true) => (z - bN t, false)

theorem transitionN_involutive (t : Fin 5) : Function.Involutive (transitionN (N := N) t) := by
  rintro ⟨z, s⟩
  cases s <;> simp [transitionN]

theorem bN_apply_self (u : Fin 5) (hu : (u : ℕ) < 4) : bN (N := N) u ⟨u, hu⟩ = 1 := by
  simp [bN]

theorem bN_apply_ne (u : Fin 5) (i : Fin 4) (h : (i : ℕ) ≠ u) : bN (N := N) u i = 0 := by
  simp [bN, h]

theorem bN_injective (hN : 2 ≤ N) : Function.Injective (bN (N := N)) := by
  haveI : Fact (1 < N) := ⟨by omega⟩
  have h10 : (1 : ZMod N) ≠ 0 := one_ne_zero
  intro s t hst
  by_contra hne
  have hne' : (s : ℕ) ≠ t := fun h => hne (Fin.ext h)
  rcases Nat.lt_or_ge (s : ℕ) 4 with hs | hs
  · have h1 := congrFun hst ⟨s, hs⟩
    rw [bN_apply_self s hs, bN_apply_ne t ⟨s, hs⟩ hne'] at h1
    exact h10 h1
  · rcases Nat.lt_or_ge (t : ℕ) 4 with ht | ht
    · have h1 := congrFun hst ⟨t, ht⟩
      rw [bN_apply_ne s ⟨t, ht⟩ (Ne.symm hne'), bN_apply_self t ht] at h1
      exact h10 h1.symm
    · exact hne (Fin.ext (by omega))

/-- **The five transitions of a vertex reach five different vertices** (`N ≥ 2`). -/
theorem transitionN_injective (hN : 2 ≤ N) (x : VN N) : Function.Injective fun t => transitionN t x := by
  intro s t hst
  rcases x with ⟨z, b⟩
  cases b <;> simp only [transitionN, Prod.mk.injEq, and_true] at hst
  · exact bN_injective hN (add_left_cancel hst)
  · exact bN_injective hN (sub_right_injective hst)

theorem card_VN : Fintype.card (VN N) = 2 * N ^ 4 := by
  simp [Fintype.card_prod, ZMod.card, mul_comm]

theorem card_lifted : Fintype.card (VN N × Fin 5) = 10 * N ^ 4 := by
  rw [Fintype.card_prod, card_VN, Fintype.card_fin]
  ring

/-! ## The cover of the sixteen two-spinor states -/

/-- The complement of the line `t`, as a parity vector. -/
def gbit (t : Fin 5) : Fin 5 → ZMod 2 := fun i => if i = t then 0 else 1

/-- The sixteen two-spinor states as parity vectors: `φ(k)_i = 1` on the lines where the two systems disagree. -/
def phi (k : Fin 16) : Fin 5 → ZMod 2 := fun i => if i ∈ disagreeSet k then 1 else 0

/-- **A transition adds the complement of its line:** `φ(transition t k) = φ(k) + g_t`. -/
theorem phi_transition : ∀ (t : Fin 5) (k : Fin 16), phi (transition t k) = phi k + gbit t := by
  decide

theorem phi_injective : Function.Injective phi := by
  decide

/-- The position extended by its fifth coordinate: `(z, −Σ z)`. -/
def extend (z : ZN N) : Fin 5 → ZMod N := ![z 0, z 1, z 2, z 3, -(z 0 + z 1 + z 2 + z 3)]

theorem extend_add (z w : ZN N) : extend (z + w) = extend z + extend w := by
  funext i
  fin_cases i <;> simp [extend] <;> ring

theorem extend_sub (z w : ZN N) : extend (z - w) = extend z - extend w := by
  funext i
  fin_cases i <;> simp [extend] <;> ring

/-- Reduction mod two. -/
def red2 (hN : 2 ∣ N) : ZMod N →+* ZMod 2 := ZMod.castHom hN (ZMod 2)

/-- The cover map: `π(z, s) = (z, −Σz) mod 2 + s·g₄`. -/
def piN (hN : 2 ∣ N) (x : VN N) : Fin 5 → ZMod 2 :=
  fun i => red2 hN (extend x.1 i) + (if x.2 then gbit 4 i else 0)

theorem neg_two : ∀ a : ZMod 2, -a = a := by
  decide

theorem core_transition (hN : 2 ∣ N) (t i : Fin 5) :
    red2 hN (extend (bN t) i) + gbit 4 i = gbit t i := by
  fin_cases t <;> fin_cases i <;> simp [extend, bN, gbit, map_neg, map_add, map_one, map_zero] <;>
    decide

/-- **The chart covers the sixteen two-spinor states:** `π(Γ_t x) = π(x) + g_t`. -/
theorem piN_transition (hN : 2 ∣ N) (t : Fin 5) (x : VN N) : piN hN (transitionN t x) = piN hN x + gbit t := by
  rcases x with ⟨z, s⟩
  funext i
  have hc := core_transition hN t i
  cases s
  · simp only [transitionN, piN, extend_add, Pi.add_apply, map_add, ite_true, Bool.false_eq_true,
      ite_false, add_zero]
    rw [add_assoc, hc]
  · simp only [transitionN, piN, extend_sub, Pi.sub_apply, map_sub, ite_true, Bool.false_eq_true,
      ite_false, add_zero, Pi.add_apply]
    have : red2 hN (extend (bN t) i) = gbit t i + gbit 4 i := by
      rw [← hc, add_assoc, ← two_mul]
      have h2 : (2 : ZMod 2) = 0 := rfl
      rw [h2, zero_mul, add_zero]
    rw [this, sub_eq_add_neg, neg_add, neg_two, neg_two]
    ring

/-- **Every vertex lands on an even vector.** -/
theorem piN_even (hN : 2 ∣ N) (x : VN N) : ∑ i, piN hN x i = 0 := by
  rcases x with ⟨z, s⟩
  have h2 : (2 : ZMod 2) = 0 := rfl
  cases s <;> simp [piN, extend, Fin.sum_univ_five, gbit, map_neg, map_add] <;> ring_nf <;>
    first | rfl | decide | simp [h2]

/-! ## The lifted step -/

/-- The transition `t` on the chart as a permutation matrix. -/
noncomputable def GammaN (t : Fin 5) : Matrix (VN N) (VN N) ℂ :=
  Matrix.of fun y x => if y = transitionN t x then 1 else 0

theorem GammaN_sq (t : Fin 5) : GammaN (N := N) t * GammaN t = 1 := by
  ext y x
  rw [Matrix.mul_apply]
  simp only [GammaN, Matrix.of_apply, mul_ite, mul_one, mul_zero, Matrix.one_apply]
  rw [Finset.sum_eq_single (transitionN t x)]
  · simp only [if_true]
    by_cases h : y = x
    · subst h
      simp [transitionN_involutive t y]
    · have : ¬ y = transitionN t (transitionN t x) := by rwa [transitionN_involutive t x]
      simp [this, h]
  · intro b _ hb
    simp [hb]
  · simp

/-- The non-backtracking step on the chart. -/
noncomputable def chartStep : Matrix (VN N × Fin 5) (VN N × Fin 5) ℂ := stepOp (GammaN (N := N))

/-- The lift from the eighty states of the two-spinor states to the chart's states: equal last line, and the
chart's vertex covering the two-spinor state. -/
noncomputable def liftM (hN : 2 ∣ N) : Matrix (VN N × Fin 5) (Fin 16 × Fin 5) ℂ :=
  Matrix.of fun p q => if p.2 = q.2 ∧ piN hN p.1 = phi q.1 then 1 else 0

theorem chartStep_lift_apply (hN : 2 ∣ N) (x : VN N) (t : Fin 5) (k : Fin 16) (s : Fin 5) :
    (chartStep (N := N) * liftM hN : Matrix (VN N × Fin 5) (Fin 16 × Fin 5) ℂ) (x, t) (k, s) =
      if t = s then 0 else if piN hN (transitionN t x) = phi k then 1 else 0 := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [chartStep, stepOp, GammaN, liftM, Matrix.of_apply]
  rw [Finset.sum_eq_single (transitionN t x)]
  · rw [Finset.sum_eq_single s]
    · by_cases hts : t = s
      · simp [hts]
      · simp [hts, transitionN_involutive t x]
    · intro b _ hb
      simp [hb]
    · simp
  · intro y _ hy
    refine Finset.sum_eq_zero fun r _ => ?_
    have : ¬ x = transitionN t y := by
      intro h
      apply hy
      rw [h, transitionN_involutive t y]
    by_cases htr : t = r <;> simp [htr, this]
  · simp

theorem lift_base_apply (hN : 2 ∣ N) (x : VN N) (t : Fin 5) (k : Fin 16) (s : Fin 5) :
    (liftM hN * stepOp transitionMat : Matrix (VN N × Fin 5) (Fin 16 × Fin 5) ℂ) (x, t) (k, s) =
      if t = s then 0 else if piN hN x = phi (transition t k) then 1 else 0 := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [stepOp, liftM, transitionMat, transitionMatZ, Matrix.of_apply, Matrix.map_apply]
  rw [Finset.sum_eq_single (transition t k)]
  · rw [Finset.sum_eq_single t]
    · by_cases hts : t = s
      · simp [hts]
      · simp [hts]
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  · intro k' _ hk'
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases htr : t = r
    · subst htr
      by_cases hts : t = s <;> simp [hts, hk']
    · simp [htr]
  · simp

/-- **The lifted step covers the step of the sixteen two-spinor states:** `B_N · Lift = Lift · B`. -/
theorem lifted_B_intertwines (hN : 2 ∣ N) :
    (chartStep (N := N) * liftM hN : Matrix (VN N × Fin 5) (Fin 16 × Fin 5) ℂ) =
      liftM hN * stepOp transitionMat := by
  ext ⟨x, t⟩ ⟨k, s⟩
  rw [chartStep_lift_apply, lift_base_apply, piN_transition, phi_transition]
  by_cases hts : t = s
  · simp [hts]
  · simp only [hts, ite_false]
    have hiff : piN hN x + gbit t = phi k ↔ piN hN x = phi k + gbit t := by
      constructor
      · intro h
        rw [← h, add_assoc]
        have : gbit t + gbit t = 0 := by
          funext i
          simp only [Pi.add_apply, Pi.zero_apply]
          generalize gbit t i = a
          fin_cases a <;> decide
        rw [this, add_zero]
      · intro h
        rw [h, add_assoc]
        have : gbit t + gbit t = 0 := by
          funext i
          simp only [Pi.add_apply, Pi.zero_apply]
          generalize gbit t i = a
          fin_cases a <;> decide
        rw [this, add_zero]
    simp only [hiff]

/-- **Four continuations out of every lifted state.** -/
theorem chartStep_row (x : VN N) (t : Fin 5) : ∑ q, chartStep (N := N) (x, t) q = 4 := by
  rw [Fintype.sum_prod_type]
  simp only [chartStep, stepOp, GammaN, Matrix.of_apply]
  have h : ∀ r : Fin 5, ∑ y : VN N, (if t = r then (0 : ℂ) else if x = transitionN t y then 1 else 0) =
      if t = r then 0 else 1 := by
    intro r
    by_cases htr : t = r
    · simp [htr]
    · simp only [htr, if_false]
      rw [Finset.sum_eq_single (transitionN t x)]
      · simp [transitionN_involutive t x]
      · intro y _ hy
        have : ¬ x = transitionN t y := by
          intro h
          apply hy
          rw [h, transitionN_involutive t y]
        simp [this]
      · simp
  rw [Finset.sum_comm]
  simp only [h]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hc : ∀ t : Fin 5, (Finset.univ.filter fun r : Fin 5 => ¬t = r).card = 4 := by decide
  rw [hc t]
  norm_num

/-- **Four continuations into every lifted state.** -/
theorem chartStep_col (y : VN N) (s : Fin 5) : ∑ p, chartStep (N := N) p (y, s) = 4 := by
  rw [Fintype.sum_prod_type]
  simp only [chartStep, stepOp, GammaN, Matrix.of_apply]
  have h : ∀ r : Fin 5, ∑ x : VN N, (if r = s then (0 : ℂ) else if x = transitionN r y then 1 else 0) =
      if r = s then 0 else 1 := by
    intro r
    by_cases hrs : r = s
    · simp [hrs]
    · simp [hrs]
  rw [Finset.sum_comm]
  simp only [h]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hc : ∀ s : Fin 5, (Finset.univ.filter fun r : Fin 5 => ¬r = s).card = 4 := by decide
  rw [hc s]
  norm_num

/-- **At `N = 2`: 32 vertices, 160 states, 640 transitions.** -/
theorem chart_two : Fintype.card (VN 2) = 32 ∧ Fintype.card (VN 2 × Fin 5) = 160 ∧
    Fintype.card (VN 2 × Fin 5) * 4 = 640 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [card_VN]
    norm_num
  · rw [card_lifted]
    norm_num
  · rw [card_lifted]
    norm_num

end Comparison.GroupsContinuumLaw
