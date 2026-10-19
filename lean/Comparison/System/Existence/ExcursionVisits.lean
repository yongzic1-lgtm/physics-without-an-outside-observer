import Comparison.System.Existence.Excursion

/-!
# The proof system, the existence layer: the visits to the symmetric states of one excursion

The visits to the symmetric states of one excursion have the generating function
`G_P(x) = x(1 + x)/(16 − 11x − 3x²)`: for every complex `x` with `|x| ≤ 1`,
`Σ_m Σ_{excursions of length m} x^{P(w)}/(5·4^{m−1}) = G_P(x)` (`plane_visits_gf`).

The sums over the walks are carried with complex values (`statC`, as `ExcursionMoments.lean` carries them with
integers): one step adds the mark of the state reached (`statC_succ`), the mark `x^P` multiplies by `x` at a plane
(`statC_shift_plane`), and the marked sums stay on the five classes (`plane_lump`): `b′ = c + 3d`, `c′ = x(a + 3b)`,
`d′ = 2x(c + d)`, `e′ = 4b`. For `|x| ≤ 1` they are bounded by the unmarked counts, whose law sums to one
(`plane_dominated`), and summing the four recurrences gives `G_P` (`plane_visits_gf`).
-/

namespace Comparison.System.Existence

open Finset

/-! ## Complex sums over the walks -/

/-- One step of a line on complex values: the sum over the four continuations. -/
def stepC (v : State → ℂ) (s : State) : ℂ :=
  if transition s.2 s.1 = 0 then 0 else ∑ g, if g = s.2 then 0 else v (transition s.2 s.1, g)

theorem stepC_swap (c : Prop) [Decidable c] (u' : Fin 5) (S : Finset (List (Fin 5)))
    (F : Fin 5 → List (Fin 5) → ℂ) :
    (if c then 0 else ∑ g, if g = u' then 0 else ∑ w ∈ S, F g w) =
      ∑ w ∈ S, (if c then 0 else ∑ g, if g = u' then 0 else F g w) := by
  split_ifs
  · simp
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases hg : g = u' <;> simp [hg]

/-- `Σ F(P, Q)` over the walks of length `n + 1` at the state `s` that have not been at the start's vertex since
their first moment. -/
def statC (F : ℕ → ℕ → ℂ) (n : ℕ) (s : State) : ℂ :=
  ∑ w ∈ words (n + 1),
    if Reduced w ∧ w.head? = some s.2 ∧ relOfWord w = s.1 ∧ Transient w.tail then F (cP w) (cQ w)
    else 0

/-- The statistic read one step later at the state `s`: the mark of `s` added. -/
def shiftC (F : ℕ → ℕ → ℂ) (k : Fin 16) : ℕ → ℕ → ℂ := fun p q => F (p + dF k) (q + dL k)

theorem statC_pointwise (F : ℕ → ℕ → ℂ) (u' g₀ : Fin 5) (k' R : Fin 16) (Red Tr : Prop)
    [Decidable Red] [Decidable Tr] (p q : ℕ) :
    (if (u' ≠ g₀ ∧ Red) ∧ transition u' R = k' ∧ R ≠ 0 ∧ Tr then F (p + dF (transition u' R)) (q + dL (transition u' R))
      else 0) =
      if transition u' k' = 0 then 0 else
        (if g₀ = u' then 0 else if Red ∧ R = transition u' k' ∧ Tr then shiftC F k' p q else 0) := by
  by_cases hg : g₀ = u'
  · subst hg
    simp
  · by_cases hR : R = transition u' k'
    · subst hR
      rw [transition_transition]
      by_cases hm : transition u' k' = 0
      · simp [hm]
      · simp [hm, hg, Ne.symm hg, shiftC]
    · have hm : transition u' R ≠ k' := fun h => hR (by rw [← h, transition_transition])
      simp only [hm, hR, false_and, and_false, ↓reduceIte, ite_self]

/-- **One step adds the mark of the state reached.** -/
theorem statC_succ (F : ℕ → ℕ → ℂ) (n : ℕ) (s : State) :
    statC F (n + 1) s = stepC (statC (shiftC F s.1) n) s := by
  obtain ⟨k', u'⟩ := s
  simp only [statC, stepC]
  rw [sum_words_succ, Finset.sum_eq_single u' ?_ (by simp), stepC_swap]
  · refine Finset.sum_congr rfl fun w hw => ?_
    rw [mem_words] at hw
    cases w with
    | nil => simp at hw
    | cons g₀ w₀ =>
      rw [Finset.sum_eq_single g₀ (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp only [List.head?_cons, List.tail_cons, ↓reduceIte, true_and, reduced_cons_cons,
        transient_cons, cP_cons, cQ_cons]
      rw [relOfWord_cons u' (g₀ :: w₀)]
      exact statC_pointwise F u' g₀ k' (relOfWord (g₀ :: w₀)) _ _ _ _
  · intro t _ ht
    refine Finset.sum_eq_zero fun w _ => ?_
    simp [ht]

theorem statC_zero (F : ℕ → ℕ → ℂ) (s : State) :
    statC F 0 s = if transition s.2 0 = s.1 then F (dF (transition s.2 0)) (dL (transition s.2 0)) else 0 := by
  simp only [statC]
  rw [sum_words_succ]
  simp only [words, Finset.sum_singleton, List.head?_cons, Option.some.injEq, List.tail_cons]
  rw [Finset.sum_eq_single s.2]
  · simp [reduced_single, transient_nil, relOfWord_cons, cP, cQ, relOfWord]
  · intro b _ hb
    simp [hb]
  · simp

/-- The excursions of length `n + 1`, summed with `F(P, Q)`, by their last state. -/
theorem excursionStatC_succ (F : ℕ → ℕ → ℂ) (n : ℕ) :
    ∑ w ∈ excursions (n + 1), F (cP w) (cQ w) = ∑ g, statC F n (0, g) := by
  rw [excursions, Finset.sum_filter]
  simp only [statC]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [mem_words] at hw
  cases w with
  | nil => simp at hw
  | cons t w =>
    rw [Finset.sum_eq_single t]
    · simp [IsExcursion]
    · intro b _ hb
      simp [Ne.symm hb]
    · simp

/-- **The mark of the visits to the symmetric states:** read one step later, `x^P` is multiplied by `x` at a plane. -/
theorem statC_shift_plane (x : ℂ) (k : Fin 16) (n : ℕ) (s : State) :
    statC (shiftC (fun p _ => x ^ p) k) n s = x ^ dF k * statC (fun p _ => x ^ p) n s := by
  simp only [statC, shiftC, Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs
  · ring
  · simp

theorem stepC_mul (c : ℂ) (v : State → ℂ) (s : State) :
    stepC (fun t => c * v t) s = c * stepC v s := by
  simp only [stepC]
  split_ifs
  · simp
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases hg : g = s.2 <;> simp [hg]

/-! ## The classes, with complex coefficients -/

/-- The indicator of a class, complex. -/
def tyC (X : Fin 5) (s : State) : ℂ := ((tyInd X s : ℤ) : ℂ)

/-- Five complex class coefficients. -/
structure LumpC where
  a : ℂ
  b : ℂ
  c : ℂ
  d : ℂ
  e : ℂ

/-- The vector of five class coefficients. -/
def LumpC.vec (x : LumpC) : State → ℂ := fun s =>
  x.a * tyC 1 s + x.b * tyC 2 s + x.c * tyC 3 s + x.d * tyC 4 s + x.e * tyC 0 s

/-- One step on the classes: `A → C`; `B → 3C + 4N`; `C → B + 2D`; `D → 3B + 2D`; `N → 0`. -/
def lumpStepC (x : LumpC) : LumpC := ⟨0, x.c + 3 * x.d, x.a + 3 * x.b, 2 * x.c + 2 * x.d, 4 * x.b⟩

/-- The mark of a plane: the two plane classes multiplied by `x`. -/
def markC (x : ℂ) (l : LumpC) : LumpC := ⟨l.a, l.b, x * l.c, x * l.d, l.e⟩

theorem stepC_tyC (X : Fin 5) (s : State) :
    stepC (tyC X) s = ((stepGen (fun _ _ => 1) (tyInd X) s : ℤ) : ℂ) := by
  simp only [stepC, stepGen, tyC]
  split_ifs
  · simp
  · simp only [Int.cast_mul, Int.cast_one, one_mul, Int.cast_sum, Int.cast_ite, Int.cast_zero]

theorem stepC_linear (x : LumpC) (s : State) :
    stepC x.vec s = x.a * stepC (tyC 1) s + x.b * stepC (tyC 2) s + x.c * stepC (tyC 3) s +
      x.d * stepC (tyC 4) s + x.e * stepC (tyC 0) s := by
  simp only [stepC, LumpC.vec]
  split_ifs
  · ring
  · simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    by_cases hg : g = s.2 <;> simp [hg]

/-- **The step stays on the classes.** -/
theorem stepC_lump (x : LumpC) (s : State) : stepC x.vec s = (lumpStepC x).vec s := by
  rw [stepC_linear, stepC_tyC, stepC_tyC, stepC_tyC, stepC_tyC, stepC_tyC, step_A, step_B, step_C, step_D,
    step_N]
  simp only [lumpStepC, LumpC.vec, tyC]
  push_cast
  ring

theorem mark_vec (x : ℂ) (l : LumpC) (s : State) : x ^ dF s.1 * l.vec s = (markC x l).vec s := by
  have h : ∀ s : State, (dF s.1 = 1 ∧ tyInd 1 s = 0 ∧ tyInd 2 s = 0 ∧ tyInd 0 s = 0) ∨
      (dF s.1 = 0 ∧ tyInd 3 s = 0 ∧ tyInd 4 s = 0) := by
    decide +kernel
  simp only [LumpC.vec, markC, tyC]
  rcases h s with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3⟩
  · rw [h1, h2, h3, h4]
    push_cast
    ring
  · rw [h1, h2, h3]
    push_cast
    ring

/-- The marked class coefficients after `n + 1` steps. -/
def planeSeq (x : ℂ) : ℕ → LumpC
  | 0 => ⟨1, 0, 0, 0, 0⟩
  | n + 1 => markC x (lumpStepC (planeSeq x n))

/-- **The marked sums stay on the classes:** `Σ x^P` over the walks of length `n + 1` at a state is the class
vector `planeSeq x n`. -/
theorem plane_lump (x : ℂ) (n : ℕ) : statC (fun p _ => x ^ p) n = (planeSeq x n).vec := by
  induction n with
  | zero =>
    funext s
    have h : ∀ s : State, dF (transition s.2 0) = 0 ∧ tyInd 1 s = if transition s.2 0 = s.1 then 1 else 0 := by
      decide +kernel
    obtain ⟨h1, h2⟩ := h s
    rw [statC_zero]
    simp only [planeSeq, LumpC.vec, tyC, h1, h2, pow_zero]
    split_ifs <;> push_cast <;> ring
  | succ n ih =>
    funext s
    rw [statC_succ]
    have e : statC (shiftC (fun p _ => x ^ p) s.1) n = fun t => x ^ dF s.1 * statC (fun p _ => x ^ p) n t :=
      funext fun t => statC_shift_plane x s.1 n t
    rw [e, stepC_mul, ih, stepC_lump, mark_vec]
    rfl

/-- **The marked excursion sums:** `Σ_{excursions of length n + 1} x^P = 5·e`. -/
theorem plane_excursion_sum (x : ℂ) (n : ℕ) : ∑ w ∈ excursions (n + 1), x ^ cP w = 5 * (planeSeq x n).e := by
  rw [show (∑ w ∈ excursions (n + 1), x ^ cP w) = ∑ g, statC (fun p _ => x ^ p) n (0, g) from
    excursionStatC_succ (fun p _ => x ^ p) n, plane_lump]
  simp only [LumpC.vec, tyC, tyInd_place]
  simp

/-! ## The unmarked counts bound the marked ones -/

theorem lumpSeq_nonneg (n : ℕ) :
    0 ≤ (lumpSeq n).a ∧ 0 ≤ (lumpSeq n).b ∧ 0 ≤ (lumpSeq n).c ∧ 0 ≤ (lumpSeq n).d ∧ 0 ≤ (lumpSeq n).e := by
  induction n with
  | zero => simp [lumpSeq]
  | succ n ih =>
    obtain ⟨ha, hb, hc, hd, he⟩ := ih
    simp only [lumpSeq, lumpStep]
    refine ⟨le_refl 0, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- **For `|x| ≤ 1` the marked coefficients are bounded by the unmarked ones.** -/
theorem plane_dominated (x : ℂ) (hx : ‖x‖ ≤ 1) (n : ℕ) :
    ‖(planeSeq x n).a‖ ≤ (lumpSeq n).a ∧ ‖(planeSeq x n).b‖ ≤ (lumpSeq n).b ∧
      ‖(planeSeq x n).c‖ ≤ (lumpSeq n).c ∧ ‖(planeSeq x n).d‖ ≤ (lumpSeq n).d ∧
      ‖(planeSeq x n).e‖ ≤ (lumpSeq n).e := by
  have n2 : ‖(2 : ℂ)‖ = 2 := by simp
  have n3 : ‖(3 : ℂ)‖ = 3 := by simp
  have n4 : ‖(4 : ℂ)‖ = 4 := by simp
  induction n with
  | zero => simp [planeSeq, lumpSeq]
  | succ n ih =>
    obtain ⟨ha, hb, hc, hd, he⟩ := ih
    obtain ⟨pa, pb, pc, pd, pe⟩ := lumpSeq_nonneg n
    have qa : (0 : ℝ) ≤ (lumpSeq n).a := by exact_mod_cast pa
    have qb : (0 : ℝ) ≤ (lumpSeq n).b := by exact_mod_cast pb
    have qc : (0 : ℝ) ≤ (lumpSeq n).c := by exact_mod_cast pc
    have qd : (0 : ℝ) ≤ (lumpSeq n).d := by exact_mod_cast pd
    have hx0 : 0 ≤ ‖x‖ := norm_nonneg x
    simp only [planeSeq, markC, lumpStepC, lumpSeq, lumpStep]
    push_cast
    refine ⟨by simp, ?_, ?_, ?_, ?_⟩
    · calc ‖(planeSeq x n).c + 3 * (planeSeq x n).d‖ ≤ ‖(planeSeq x n).c‖ + ‖3 * (planeSeq x n).d‖ :=
            norm_add_le _ _
        _ = ‖(planeSeq x n).c‖ + 3 * ‖(planeSeq x n).d‖ := by rw [norm_mul, n3]
        _ ≤ _ := by linarith
    · have h1 : ‖(planeSeq x n).a + 3 * (planeSeq x n).b‖ ≤ (lumpSeq n).a + 3 * (lumpSeq n).b :=
        calc ‖(planeSeq x n).a + 3 * (planeSeq x n).b‖ ≤ ‖(planeSeq x n).a‖ + ‖3 * (planeSeq x n).b‖ :=
              norm_add_le _ _
          _ = ‖(planeSeq x n).a‖ + 3 * ‖(planeSeq x n).b‖ := by rw [norm_mul, n3]
          _ ≤ _ := by linarith
      rw [norm_mul]
      calc ‖x‖ * ‖(planeSeq x n).a + 3 * (planeSeq x n).b‖ ≤ 1 * ((lumpSeq n).a + 3 * (lumpSeq n).b) :=
            mul_le_mul hx h1 (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    · have h1 : ‖2 * (planeSeq x n).c + 2 * (planeSeq x n).d‖ ≤ 2 * (lumpSeq n).c + 2 * (lumpSeq n).d :=
        calc ‖2 * (planeSeq x n).c + 2 * (planeSeq x n).d‖ ≤ ‖2 * (planeSeq x n).c‖ + ‖2 * (planeSeq x n).d‖ :=
              norm_add_le _ _
          _ = 2 * ‖(planeSeq x n).c‖ + 2 * ‖(planeSeq x n).d‖ := by rw [norm_mul, norm_mul, n2]
          _ ≤ _ := by linarith
      rw [norm_mul]
      calc ‖x‖ * ‖2 * (planeSeq x n).c + 2 * (planeSeq x n).d‖ ≤ 1 * (2 * (lumpSeq n).c + 2 * (lumpSeq n).d) :=
            mul_le_mul hx h1 (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    · rw [norm_mul, n4]
      linarith

/-- The unmarked `e`-coefficients scaled by `4ⁿ` are the excursion's law, which sums to one. -/
theorem lump_e_summable : Summable fun n => ((lumpSeq n).e : ℝ) / 4 ^ n := by
  have h : (fun n => excursionLaw (n + 1)) = fun n => ((lumpSeq n).e : ℝ) / 4 ^ n := by
    funext n
    rw [← lawOf_C, lawOf_succ, eC, stat6Seq_C]
  rw [← h]
  exact (summable_nat_add_iff 1).mpr excursion_total.summable

theorem lump_succ_b (n : ℕ) : (lumpSeq (n + 1)).e = 4 * (lumpSeq n).b := rfl

theorem lump_succ_c (n : ℕ) : (lumpSeq (n + 1)).b = (lumpSeq n).c + 3 * (lumpSeq n).d := rfl

theorem lump_b_summable : Summable fun n => ((lumpSeq n).b : ℝ) / 4 ^ n := by
  have h : (fun n => ((lumpSeq n).b : ℝ) / 4 ^ n) = fun n => ((lumpSeq (n + 1)).e : ℝ) / 4 ^ (n + 1) := by
    funext n
    rw [lump_succ_b]
    push_cast
    rw [pow_succ]
    ring
  rw [h]
  exact (summable_nat_add_iff 1).mpr lump_e_summable

theorem lump_b_bound (n : ℕ) :
    4 * (((lumpSeq (n + 1)).b : ℝ) / 4 ^ (n + 1)) = (((lumpSeq n).c : ℝ) + 3 * (lumpSeq n).d) / 4 ^ n := by
  rw [lump_succ_c, pow_succ]
  push_cast
  ring

theorem lump_c_summable : Summable fun n => ((lumpSeq n).c : ℝ) / 4 ^ n := by
  have hb := ((summable_nat_add_iff 1).mpr lump_b_summable).mul_left 4
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hb
  · obtain ⟨-, -, pc, -, -⟩ := lumpSeq_nonneg n
    have hc : (0 : ℝ) ≤ (lumpSeq n).c := by exact_mod_cast pc
    exact div_nonneg hc (by positivity)
  · obtain ⟨-, -, -, pd, -⟩ := lumpSeq_nonneg n
    have hd : (0 : ℝ) ≤ (lumpSeq n).d := by exact_mod_cast pd
    change ((lumpSeq n).c : ℝ) / 4 ^ n ≤ 4 * (((lumpSeq (n + 1)).b : ℝ) / 4 ^ (n + 1))
    rw [lump_b_bound]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)

theorem lump_d_summable : Summable fun n => ((lumpSeq n).d : ℝ) / 4 ^ n := by
  have hb := ((summable_nat_add_iff 1).mpr lump_b_summable).mul_left 4
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hb
  · obtain ⟨-, -, -, pd, -⟩ := lumpSeq_nonneg n
    have hd : (0 : ℝ) ≤ (lumpSeq n).d := by exact_mod_cast pd
    exact div_nonneg hd (by positivity)
  · obtain ⟨-, -, pc, pd, -⟩ := lumpSeq_nonneg n
    have hc : (0 : ℝ) ≤ (lumpSeq n).c := by exact_mod_cast pc
    have hd : (0 : ℝ) ≤ (lumpSeq n).d := by exact_mod_cast pd
    change ((lumpSeq n).d : ℝ) / 4 ^ n ≤ 4 * (((lumpSeq (n + 1)).b : ℝ) / 4 ^ (n + 1))
    rw [lump_b_bound]
    exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-! ## The generating function of the visits to the symmetric states -/

theorem planeSeq_a (x : ℂ) (n : ℕ) : (planeSeq x n).a = if n = 0 then 1 else 0 := by
  cases n with
  | zero => rfl
  | succ n => rfl

theorem plane_summable (x : ℂ) (hx : ‖x‖ ≤ 1) :
    (Summable fun n => (planeSeq x n).b / 4 ^ n) ∧ (Summable fun n => (planeSeq x n).c / 4 ^ n) ∧
      (Summable fun n => (planeSeq x n).d / 4 ^ n) ∧ (Summable fun n => (planeSeq x n).e / 4 ^ n) := by
  have hn : ∀ (z : ℂ) (n : ℕ), ‖z / 4 ^ n‖ = ‖z‖ / 4 ^ n := by
    intro z n
    rw [norm_div, norm_pow]
    simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Summable.of_norm_bounded lump_b_summable fun n => ?_
    rw [hn]
    exact div_le_div_of_nonneg_right (plane_dominated x hx n).2.1 (by positivity)
  · refine Summable.of_norm_bounded lump_c_summable fun n => ?_
    rw [hn]
    exact div_le_div_of_nonneg_right (plane_dominated x hx n).2.2.1 (by positivity)
  · refine Summable.of_norm_bounded lump_d_summable fun n => ?_
    rw [hn]
    exact div_le_div_of_nonneg_right (plane_dominated x hx n).2.2.2.1 (by positivity)
  · refine Summable.of_norm_bounded lump_e_summable fun n => ?_
    rw [hn]
    exact div_le_div_of_nonneg_right (plane_dominated x hx n).2.2.2.2 (by positivity)

theorem plane_denominator_ne (x : ℂ) (hx : ‖x‖ ≤ 1) : (16 - 11 * x - 3 * x ^ 2 : ℂ) ≠ 0 := by
  intro h
  have h1 : (16 : ℂ) = 11 * x + 3 * x ^ 2 := by linear_combination h
  have h2 : ‖(16 : ℂ)‖ ≤ 14 := by
    rw [h1]
    calc ‖11 * x + 3 * x ^ 2‖ ≤ ‖11 * x‖ + ‖3 * x ^ 2‖ := norm_add_le _ _
      _ = 11 * ‖x‖ + 3 * ‖x‖ ^ 2 := by rw [norm_mul, norm_mul, norm_pow]; norm_num
      _ ≤ 11 * 1 + 3 * 1 ^ 2 := by gcongr
      _ = 14 := by norm_num
  have h3 : ‖(16 : ℂ)‖ = 16 := by simp
  linarith

/-- **The visits to the symmetric states of one excursion (SI S3.10, Table VI):** for every complex `x` with `|x| ≤ 1`, the excursions summed with
`x^P` and their weights `1/(5·4^{m−1})` give `G_P(x) = x(1 + x)/(16 − 11x − 3x²)`. -/
theorem plane_visits_gf (x : ℂ) (hx : ‖x‖ ≤ 1) :
    HasSum (fun m => (∑ w ∈ excursions m, x ^ cP w) / (5 * 4 ^ (m - 1)))
      (x * (1 + x) / (16 - 11 * x - 3 * x ^ 2)) := by
  obtain ⟨sb, sc, sd, se⟩ := plane_summable x hx
  obtain ⟨B, hb⟩ := sb
  obtain ⟨C, hc⟩ := sc
  obtain ⟨D, hd⟩ := sd
  obtain ⟨E, he⟩ := se
  have ha : HasSum (fun n => (planeSeq x n).a / 4 ^ n) 1 := by
    have : (fun n => (planeSeq x n).a / 4 ^ n) = fun n => if n = 0 then (1 : ℂ) else 0 := by
      funext n
      rw [planeSeq_a]
      split_ifs with h
      · subst h
        simp
      · simp
    rw [this]
    exact hasSum_ite_eq 0 1
  have shift : ∀ (f : ℕ → ℂ) (S : ℂ), HasSum f S → HasSum (fun n => f (n + 1)) (S - f 0) := by
    intro f S hf
    have := (hasSum_nat_add_iff' 1).mpr hf
    simpa using this
  have E1 : B = (C + 3 * D) / 4 := by
    have h1 := shift _ _ hb
    have h2 : HasSum (fun n => (planeSeq x (n + 1)).b / 4 ^ (n + 1)) ((C + 3 * D) / 4) := by
      refine ((hc.add (hd.mul_left 3)).div_const 4).congr_fun fun n => ?_
      simp only [planeSeq, markC, lumpStepC]
      rw [pow_succ]
      ring
    have h3 := h1.unique h2
    simpa [planeSeq] using h3
  have E2 : C = x * (1 + 3 * B) / 4 := by
    have h1 := shift _ _ hc
    have h2 : HasSum (fun n => (planeSeq x (n + 1)).c / 4 ^ (n + 1)) (x * (1 + 3 * B) / 4) := by
      refine (((ha.add (hb.mul_left 3)).mul_left x).div_const 4).congr_fun fun n => ?_
      simp only [planeSeq, markC, lumpStepC]
      rw [pow_succ]
      ring
    have h3 := h1.unique h2
    simpa [planeSeq] using h3
  have E3 : D = x * (C + D) / 2 := by
    have h1 := shift _ _ hd
    have h2 : HasSum (fun n => (planeSeq x (n + 1)).d / 4 ^ (n + 1)) (x * (C + D) / 2) := by
      refine (((hc.add hd).mul_left x).div_const 2).congr_fun fun n => ?_
      simp only [planeSeq, markC, lumpStepC]
      rw [pow_succ]
      ring
    have h3 := h1.unique h2
    simpa [planeSeq] using h3
  have E4 : E = B := by
    have h1 := shift _ _ he
    have h2 : HasSum (fun n => (planeSeq x (n + 1)).e / 4 ^ (n + 1)) B := by
      refine hb.congr_fun fun n => ?_
      simp only [planeSeq, markC, lumpStepC]
      rw [pow_succ]
      ring
    have h3 := h1.unique h2
    simpa [planeSeq] using h3
  have hden := plane_denominator_ne x hx
  have hB' : B = x * (1 + x) / (16 - 11 * x - 3 * x ^ 2) := by
    rw [eq_div_iff hden]
    linear_combination (4 * (4 - 2 * x)) * E1 + (4 * (1 + x)) * E2 + 12 * E3
  have hlaw : (fun m => (∑ w ∈ excursions m, x ^ cP w) / (5 * 4 ^ (m - 1))) =
      fun m => if m = 0 then 0 else (planeSeq x (m - 1)).e / 4 ^ (m - 1) := by
    funext m
    rcases m with _ | n
    · rw [if_pos rfl]
      have h0 : excursions 0 = ∅ := by
        rw [excursions]
        simp only [words]
        rw [Finset.filter_singleton]
        simp [IsExcursion]
      rw [h0, Finset.sum_empty, zero_div]
    · rw [if_neg (Nat.add_one_ne_zero n), Nat.add_sub_cancel, plane_excursion_sum,
        mul_div_mul_left _ _ (by norm_num : (5 : ℂ) ≠ 0)]
  rw [hlaw, ← hB', ← E4, ← hasSum_nat_add_iff' 1]
  convert he using 1
  · funext n
    simp
  · simp

end Comparison.System.Existence
