import Comparison.System.Existence.Defs
import Comparison.Existence.Moments

/-!
# The symmetric and vector states an excursion meets (Proposition 29's moments)

An excursion `w` (a reduced word, newest step first, at the vertex of its start now and at no moment
between) passes through its moments `1, …, |w|`; at each moment before the last its two-spinor state to the
first moment is a symmetric state or a vector state. `cP w` counts the moments at a symmetric state and
`cQ w` the moments at a vector state (`cP`, `cQ` read the two-spinor states of the nonempty tails of `w`).

The counts are carried state by state, as `Existence/Excursion.lean` carries the number of walks:
`statCount F n s` sums `F (cP w) (cQ w)` over the walks of length `n + 1` at the state `s` that
have not been at the start's vertex since. One step adds the mark of the state reached
(`statCount_succ`), and the mark depends only on the class of that state, so the six sums
`Σ 1, Σ P, Σ Q, Σ P(P−1), Σ Q(Q−1), Σ PQ` stay on the five classes (`stat_lump`). Their excursion sums obey
linear recurrences with the excursion's own (`excursionStat_rec`), and the sums over all lengths are
`E P = 10`, `E Q = 5`, `E P(P−1) = 174`, `E Q(Q−1) = 32`, `E PQ = 80`.
-/

namespace Comparison.System.Existence

open Finset

/-! ## The symmetric-state and vector-state moments of a walk -/

/-- `1` when the two-spinor state is a symmetric state (disagrees on two lines). -/
def dF (k : Fin 16) : ℕ := if (disagreeSet k).card = 2 then 1 else 0

/-- `1` when the two-spinor state is a vector state (disagrees on four lines). -/
def dL (k : Fin 16) : ℕ := if (disagreeSet k).card = 4 then 1 else 0

/-- The moments of a walk at a symmetric state. -/
def cP : List (Fin 5) → ℕ
  | [] => 0
  | t :: w => cP w + dF (relOfWord (t :: w))

/-- The moments of a walk at a vector state. -/
def cQ : List (Fin 5) → ℕ
  | [] => 0
  | t :: w => cQ w + dL (relOfWord (t :: w))

theorem cP_cons (t : Fin 5) (w : List (Fin 5)) : cP (t :: w) = cP w + dF (relOfWord (t :: w)) := rfl

theorem cQ_cons (t : Fin 5) (w : List (Fin 5)) : cQ (t :: w) = cQ w + dL (relOfWord (t :: w)) := rfl

/-! ## The sums carried state by state -/

/-- `Σ F(P, Q)` over the walks of length `n + 1` at the state `s` that have not been at the
start's vertex since their first moment. -/
def statCount (F : ℕ → ℕ → ℤ) (n : ℕ) (s : State) : ℤ :=
  ∑ w ∈ words (n + 1),
    if Reduced w ∧ w.head? = some s.2 ∧ relOfWord w = s.1 ∧ Transient w.tail then F (cP w) (cQ w)
    else 0

/-- The statistic read one step later at the state `s`: the mark of `s` added. -/
def shiftAt (F : ℕ → ℕ → ℤ) (k : Fin 16) : ℕ → ℕ → ℤ := fun p q => F (p + dF k) (q + dL k)

theorem stat_pointwise (F : ℕ → ℕ → ℤ) (u' g₀ : Fin 5) (k' R : Fin 16) (Red Tr : Prop)
    [Decidable Red] [Decidable Tr] (p q : ℕ) :
    (if (u' ≠ g₀ ∧ Red) ∧ transition u' R = k' ∧ R ≠ 0 ∧ Tr then F (p + dF (transition u' R)) (q + dL (transition u' R))
      else 0) =
      if transition u' k' = 0 then 0 else (1 : ℤ) *
        (if g₀ = u' then 0 else if Red ∧ R = transition u' k' ∧ Tr then shiftAt F k' p q else 0) := by
  by_cases hg : g₀ = u'
  · subst hg
    simp
  · by_cases hR : R = transition u' k'
    · subst hR
      rw [transition_transition]
      by_cases hm : transition u' k' = 0
      · simp [hm]
      · simp [hm, hg, Ne.symm hg, shiftAt]
    · have hm : transition u' R ≠ k' := fun h => hR (by rw [← h, transition_transition])
      simp only [hm, hR, false_and, and_false, ↓reduceIte, ite_self, mul_zero]

/-- **One step adds the mark of the state reached.** -/
theorem statCount_succ (F : ℕ → ℕ → ℤ) (n : ℕ) (s : State) :
    statCount F (n + 1) s = stepGen (fun _ _ => 1) (statCount (shiftAt F s.1) n) s := by
  obtain ⟨k', u'⟩ := s
  simp only [statCount, stepGen]
  rw [sum_words_succ, Finset.sum_eq_single u' ?_ (by simp), stepGen_swap]
  · refine Finset.sum_congr rfl fun w hw => ?_
    rw [mem_words] at hw
    cases w with
    | nil => simp at hw
    | cons g₀ w₀ =>
      rw [Finset.sum_eq_single g₀ (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp only [List.head?_cons, List.tail_cons, ↓reduceIte, true_and, reduced_cons_cons,
        transient_cons, cP_cons, cQ_cons]
      rw [relOfWord_cons u' (g₀ :: w₀)]
      exact stat_pointwise F u' g₀ k' (relOfWord (g₀ :: w₀)) _ _ _ _
  · intro t _ ht
    refine Finset.sum_eq_zero fun w _ => ?_
    simp [ht]

theorem statCount_zero (F : ℕ → ℕ → ℤ) (s : State) :
    statCount F 0 s = if transition s.2 0 = s.1 then F (dF (transition s.2 0)) (dL (transition s.2 0)) else 0 := by
  simp only [statCount]
  rw [sum_words_succ]
  simp only [words, Finset.sum_singleton, List.head?_cons, Option.some.injEq, List.tail_cons]
  rw [Finset.sum_eq_single s.2]
  · simp [reduced_single, transient_nil, relOfWord_cons, cP, cQ, relOfWord]
  · intro b _ hb
    simp [hb]
  · simp

/-- The excursions of length `n + 1`, summed with `F(P, Q)`, by their last state. -/
theorem excursionStat_succ (F : ℕ → ℕ → ℤ) (n : ℕ) :
    ∑ w ∈ excursions (n + 1), F (cP w) (cQ w) = ∑ g, statCount F n (0, g) := by
  rw [excursions, Finset.sum_filter]
  simp only [statCount]
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

/-! ## The six sums on the classes -/

/-- The classes of the symmetric states (`3`, `4`) and of the vector states (`1`, `2`). -/
def planeLump (x : Lump) : Lump := ⟨0, 0, x.c, x.d, 0⟩

def lineLump (x : Lump) : Lump := ⟨x.a, x.b, 0, 0, 0⟩

theorem lump_vec_add (x y : Lump) :
    (⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d, x.e + y.e⟩ : Lump).vec = x.vec + y.vec := by
  funext s
  simp only [Lump.vec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The sum of two class vectors. -/
def lumpAdd (x y : Lump) : Lump := ⟨x.a + y.a, x.b + y.b, x.c + y.c, x.d + y.d, x.e + y.e⟩

/-- An integer times a class vector. -/
def lumpSmul (c : ℤ) (x : Lump) : Lump := ⟨c * x.a, c * x.b, c * x.c, c * x.d, c * x.e⟩

theorem lumpAdd_vec (x y : Lump) : (lumpAdd x y).vec = x.vec + y.vec := lump_vec_add x y

theorem lumpSmul_vec (c : ℤ) (x : Lump) : (lumpSmul c x).vec = c • x.vec := by
  funext s
  simp only [lumpSmul, Lump.vec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem stype_plane (s : State) :
    ((dF s.1 : ℕ) : ℤ) = tyInd 3 s + tyInd 4 s := by
  revert s
  decide +kernel

theorem stype_line (s : State) :
    ((dL s.1 : ℕ) : ℤ) = tyInd 1 s + tyInd 2 s := by
  revert s
  decide +kernel

theorem dF_mul_vec (x : Lump) (s : State) :
    ((dF s.1 : ℕ) : ℤ) * x.vec s = (planeLump x).vec s := by
  have h1 : ∀ s : State, tyInd 3 s * tyInd 3 s = tyInd 3 s ∧ tyInd 4 s * tyInd 4 s = tyInd 4 s ∧
      tyInd 3 s * tyInd 4 s = 0 ∧ tyInd 3 s * tyInd 1 s = 0 ∧ tyInd 3 s * tyInd 2 s = 0 ∧
      tyInd 3 s * tyInd 0 s = 0 ∧ tyInd 4 s * tyInd 1 s = 0 ∧ tyInd 4 s * tyInd 2 s = 0 ∧
      tyInd 4 s * tyInd 0 s = 0 := by decide +kernel
  obtain ⟨a, b, c, d, e, f, g, h, i⟩ := h1 s
  rw [stype_plane]
  simp only [Lump.vec, planeLump, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (x.c) * a + (x.d) * b + (x.c + x.d) * c + x.a * d + x.b * e + x.e * f +
    x.a * g + x.b * h + x.e * i

theorem dL_mul_vec (x : Lump) (s : State) :
    ((dL s.1 : ℕ) : ℤ) * x.vec s = (lineLump x).vec s := by
  have h1 : ∀ s : State, tyInd 1 s * tyInd 1 s = tyInd 1 s ∧ tyInd 2 s * tyInd 2 s = tyInd 2 s ∧
      tyInd 1 s * tyInd 2 s = 0 ∧ tyInd 1 s * tyInd 3 s = 0 ∧ tyInd 1 s * tyInd 4 s = 0 ∧
      tyInd 1 s * tyInd 0 s = 0 ∧ tyInd 2 s * tyInd 3 s = 0 ∧ tyInd 2 s * tyInd 4 s = 0 ∧
      tyInd 2 s * tyInd 0 s = 0 := by decide +kernel
  obtain ⟨a, b, c, d, e, f, g, h, i⟩ := h1 s
  rw [stype_line]
  simp only [Lump.vec, lineLump, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination (x.a) * a + (x.b) * b + (x.a + x.b) * c + x.c * d + x.d * e + x.e * f +
    x.c * g + x.d * h + x.e * i

/-- The six class vectors of one length. -/
structure Stat6 where
  C : Lump
  P : Lump
  Q : Lump
  PP : Lump
  QQ : Lump
  PQ : Lump

/-- One step of the six: an arrival at a symmetric state adds one to `P`, at a vector state one to `Q`;
`(P + 1)P = P(P − 1) + 2P`, and so on. -/
def stat6Step (x : Stat6) : Stat6 :=
  ⟨lumpStep x.C,
   lumpAdd (lumpStep x.P) (planeLump (lumpStep x.C)),
   lumpAdd (lumpStep x.Q) (lineLump (lumpStep x.C)),
   lumpAdd (lumpStep x.PP) (lumpSmul 2 (planeLump (lumpStep x.P))),
   lumpAdd (lumpStep x.QQ) (lumpSmul 2 (lineLump (lumpStep x.Q))),
   lumpAdd (lumpAdd (lumpStep x.PQ) (planeLump (lumpStep x.Q))) (lineLump (lumpStep x.P))⟩

/-- The six at the first moment: the first step reaches a vector state (`Q = 1`). -/
def stat6Seq : ℕ → Stat6
  | 0 => ⟨⟨1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨1, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩, ⟨0, 0, 0, 0, 0⟩,
      ⟨0, 0, 0, 0, 0⟩⟩
  | n + 1 => stat6Step (stat6Seq n)

/-- The six statistics. -/
def fC : ℕ → ℕ → ℤ := fun _ _ => 1
def fP : ℕ → ℕ → ℤ := fun p _ => p
def fQ : ℕ → ℕ → ℤ := fun _ q => q
def fPP : ℕ → ℕ → ℤ := fun p _ => (p : ℤ) * ((p : ℤ) - 1)
def fQQ : ℕ → ℕ → ℤ := fun _ q => (q : ℤ) * ((q : ℤ) - 1)
def fPQ : ℕ → ℕ → ℤ := fun p q => (p : ℤ) * q

theorem dF_sq (k : Fin 16) : ((dF k : ℕ) : ℤ) * dF k = dF k := by
  unfold dF; split_ifs <;> simp

theorem dL_sq (k : Fin 16) : ((dL k : ℕ) : ℤ) * dL k = dL k := by
  unfold dL; split_ifs <;> simp

theorem dF_dL (k : Fin 16) : ((dF k : ℕ) : ℤ) * dL k = 0 := by
  unfold dF dL; split_ifs with h1 h2 <;> simp_all

theorem stepGen_add' (u v : State → ℤ) : stepGen (fun _ _ => 1) (u + v) =
    stepGen (fun _ _ => 1) u + stepGen (fun _ _ => 1) v := by
  funext s; exact stepGen_add _ u v s

theorem stepGen_smul' (c : ℤ) (v : State → ℤ) :
    stepGen (fun _ _ => 1) (c • v) = c • stepGen (fun _ _ => 1) v := by
  funext s; rw [stepGen_smul]; rfl

/-- The shifted statistics as sums of the unshifted ones, with the mark `δ` of the state reached. -/
theorem statCount_shift_C (n : ℕ) (k : Fin 16) : statCount (shiftAt fC k) n = statCount fC n := rfl

theorem statCount_shift_P (n : ℕ) (k : Fin 16) :
    statCount (shiftAt fP k) n = statCount fP n + ((dF k : ℕ) : ℤ) • statCount fC n := by
  funext s
  simp only [statCount, shiftAt, fP, fC, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs <;> push_cast <;> ring

theorem statCount_shift_Q (n : ℕ) (k : Fin 16) :
    statCount (shiftAt fQ k) n = statCount fQ n + ((dL k : ℕ) : ℤ) • statCount fC n := by
  funext s
  simp only [statCount, shiftAt, fQ, fC, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs <;> push_cast <;> ring

theorem statCount_shift_PP (n : ℕ) (k : Fin 16) :
    statCount (shiftAt fPP k) n = statCount fPP n + (2 * ((dF k : ℕ) : ℤ)) • statCount fP n := by
  funext s
  simp only [statCount, shiftAt, fPP, fP, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs
  · push_cast
    linear_combination dF_sq k
  · ring

theorem statCount_shift_QQ (n : ℕ) (k : Fin 16) :
    statCount (shiftAt fQQ k) n = statCount fQQ n + (2 * ((dL k : ℕ) : ℤ)) • statCount fQ n := by
  funext s
  simp only [statCount, shiftAt, fQQ, fQ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs
  · push_cast
    linear_combination dL_sq k
  · ring

theorem statCount_shift_PQ (n : ℕ) (k : Fin 16) :
    statCount (shiftAt fPQ k) n =
      statCount fPQ n + ((dF k : ℕ) : ℤ) • statCount fQ n + ((dL k : ℕ) : ℤ) • statCount fP n := by
  funext s
  simp only [statCount, shiftAt, fPQ, fP, fQ, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  split_ifs
  · push_cast
    linear_combination dF_dL k
  · ring

/-- A step from a class vector, with the mark of the state reached multiplied in. -/
theorem stepGen_mark_plane (u : State → ℤ) (x : Lump) (hu : u = x.vec) (s : State) :
    stepGen (fun _ _ => 1) (((dF s.1 : ℕ) : ℤ) • u) s = (planeLump (lumpStep x)).vec s := by
  rw [stepGen_smul, hu, stepGen_lump, dF_mul_vec]

theorem stepGen_mark_line (u : State → ℤ) (x : Lump) (hu : u = x.vec) (s : State) :
    stepGen (fun _ _ => 1) (((dL s.1 : ℕ) : ℤ) • u) s = (lineLump (lumpStep x)).vec s := by
  rw [stepGen_smul, hu, stepGen_lump, dL_mul_vec]

theorem stepGen_lump' (x : Lump) (s : State) :
    stepGen (fun _ _ => 1) x.vec s = (lumpStep x).vec s := by
  rw [stepGen_lump]

/-- **The six sums stay on the classes.** -/
theorem stat_lump (n : ℕ) :
    statCount fC n = (stat6Seq n).C.vec ∧ statCount fP n = (stat6Seq n).P.vec ∧
      statCount fQ n = (stat6Seq n).Q.vec ∧ statCount fPP n = (stat6Seq n).PP.vec ∧
      statCount fQQ n = (stat6Seq n).QQ.vec ∧ statCount fPQ n = (stat6Seq n).PQ.vec := by
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> funext s <;> rw [statCount_zero] <;> revert s <;>
      decide +kernel
  | succ n ih =>
    obtain ⟨hC, hP, hQ, hPP, hQQ, hPQ⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> funext s <;> rw [statCount_succ]
    · rw [statCount_shift_C, hC, stepGen_lump]; rfl
    · rw [statCount_shift_P, stepGen_add, stepGen_smul, hP, hC, stepGen_lump, stepGen_lump,
        dF_mul_vec]
      change _ = (lumpAdd (lumpStep (stat6Seq n).P) (planeLump (lumpStep (stat6Seq n).C))).vec s
      rw [lumpAdd_vec]; rfl
    · rw [statCount_shift_Q, stepGen_add, stepGen_smul, hQ, hC, stepGen_lump, stepGen_lump,
        dL_mul_vec]
      change _ = (lumpAdd (lumpStep (stat6Seq n).Q) (lineLump (lumpStep (stat6Seq n).C))).vec s
      rw [lumpAdd_vec]; rfl
    · rw [statCount_shift_PP, stepGen_add, stepGen_smul, hPP, hP, stepGen_lump, stepGen_lump]
      change _ = (lumpAdd (lumpStep (stat6Seq n).PP) (lumpSmul 2 (planeLump (lumpStep (stat6Seq n).P)))).vec s
      rw [lumpAdd_vec, Pi.add_apply, lumpSmul_vec, Pi.smul_apply, smul_eq_mul, ← dF_mul_vec]
      ring
    · rw [statCount_shift_QQ, stepGen_add, stepGen_smul, hQQ, hQ, stepGen_lump, stepGen_lump]
      change _ = (lumpAdd (lumpStep (stat6Seq n).QQ) (lumpSmul 2 (lineLump (lumpStep (stat6Seq n).Q)))).vec s
      rw [lumpAdd_vec, Pi.add_apply, lumpSmul_vec, Pi.smul_apply, smul_eq_mul, ← dL_mul_vec]
      ring
    · rw [statCount_shift_PQ, stepGen_add, stepGen_add, stepGen_smul, stepGen_smul, hPQ, hQ, hP,
        stepGen_lump, stepGen_lump, stepGen_lump, dF_mul_vec, dL_mul_vec]
      change _ = (lumpAdd (lumpAdd (lumpStep (stat6Seq n).PQ) (planeLump (lumpStep (stat6Seq n).Q)))
        (lineLump (lumpStep (stat6Seq n).P))).vec s
      rw [lumpAdd_vec, lumpAdd_vec]; rfl

/-! ## The excursion sums -/

/-- `Σ F(P, Q)` over the excursions of length `m`. -/
def excursionSum (F : ℕ → ℕ → ℤ) (m : ℕ) : ℤ := ∑ w ∈ excursions m, F (cP w) (cQ w)

theorem excursionSum_zero (F : ℕ → ℕ → ℤ) : excursionSum F 0 = 0 := by
  rw [excursionSum, excursions]
  simp only [words]
  rw [Finset.filter_singleton]
  simp [IsExcursion]

theorem excursionSum_of_lump (F : ℕ → ℕ → ℤ) (n : ℕ) (x : Lump) (h : statCount F n = x.vec) :
    excursionSum F (n + 1) = 5 * x.e := by
  rw [excursionSum, excursionStat_succ, h]
  simp only [Lump.vec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, tyInd_place]
  simp

theorem stat6Seq_C (n : ℕ) : (stat6Seq n).C = lumpSeq n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [stat6Seq, stat6Step, lumpSeq, ih]

/-- The `e`-coefficients (the start's vertex) of the six. -/
def eC (n : ℕ) : ℤ := (stat6Seq n).C.e
def eP (n : ℕ) : ℤ := (stat6Seq n).P.e
def eQ (n : ℕ) : ℤ := (stat6Seq n).Q.e
def ePP (n : ℕ) : ℤ := (stat6Seq n).PP.e
def eQQ (n : ℕ) : ℤ := (stat6Seq n).QQ.e
def ePQ (n : ℕ) : ℤ := (stat6Seq n).PQ.e

theorem excursionSum_C (n : ℕ) : excursionSum fC (n + 1) = 5 * eC n := excursionSum_of_lump _ n _ (stat_lump n).1
theorem excursionSum_P (n : ℕ) : excursionSum fP (n + 1) = 5 * eP n := excursionSum_of_lump _ n _ (stat_lump n).2.1
theorem excursionSum_Q (n : ℕ) : excursionSum fQ (n + 1) = 5 * eQ n :=
  excursionSum_of_lump _ n _ (stat_lump n).2.2.1
theorem excursionSum_PP (n : ℕ) : excursionSum fPP (n + 1) = 5 * ePP n :=
  excursionSum_of_lump _ n _ (stat_lump n).2.2.2.1
theorem excursionSum_QQ (n : ℕ) : excursionSum fQQ (n + 1) = 5 * eQQ n :=
  excursionSum_of_lump _ n _ (stat_lump n).2.2.2.2.1
theorem excursionSum_PQ (n : ℕ) : excursionSum fPQ (n + 1) = 5 * ePQ n :=
  excursionSum_of_lump _ n _ (stat_lump n).2.2.2.2.2

theorem excursionSum_C_eq (m : ℕ) : excursionSum fC m = excursionCount m := by
  simp [excursionSum, fC, excursionCount]

/-! ## The recurrences of the six -/

theorem eC_rec (n : ℕ) : eC (n + 5) = 2 * eC (n + 4) + 3 * eC (n + 3) + 12 * eC (n + 2) := by
  simp only [eC, stat6Seq, stat6Step, lumpStep]
  ring

theorem eP_rec (n : ℕ) :
    eP (n + 5) = 2 * eP (n + 4) + 3 * eP (n + 3) + 12 * eP (n + 2) +
      (2 * eC (n + 4) + 3 * eC (n + 3) + 24 * eC (n + 2)) := by
  simp only [eP, eC, stat6Seq, stat6Step, lumpStep, lumpAdd, planeLump]
  ring

theorem eQ_rec (n : ℕ) :
    eQ (n + 5) = 2 * eQ (n + 4) + 3 * eQ (n + 3) + 12 * eQ (n + 2) +
      (3 * eC (n + 3) + 12 * eC (n + 2)) := by
  simp only [eQ, eC, stat6Seq, stat6Step, lumpStep, lumpAdd, lineLump]
  ring

theorem ePP_rec (n : ℕ) :
    ePP (n + 5) = 2 * ePP (n + 4) + 3 * ePP (n + 3) + 12 * ePP (n + 2) +
      (4 * eP (n + 4) + 6 * eP (n + 3) + 48 * eP (n + 2) + 24 * eC (n + 2)) := by
  simp only [ePP, eP, eC, stat6Seq, stat6Step, lumpStep, lumpAdd, lumpSmul, planeLump]
  ring

theorem eQQ_rec (n : ℕ) :
    eQQ (n + 5) = 2 * eQQ (n + 4) + 3 * eQQ (n + 3) + 12 * eQQ (n + 2) +
      (6 * eQ (n + 3) + 24 * eQ (n + 2)) := by
  simp only [eQQ, eQ, eC, stat6Seq, stat6Step, lumpStep, lumpAdd, lumpSmul, lineLump]
  ring

theorem ePQ_rec (n : ℕ) :
    ePQ (n + 5) = 2 * ePQ (n + 4) + 3 * ePQ (n + 3) + 12 * ePQ (n + 2) +
      (2 * eQ (n + 4) + 3 * eP (n + 3) + 3 * eQ (n + 3) + 3 * eC (n + 3) + 24 * eQ (n + 2) +
        12 * eP (n + 2) + 24 * eC (n + 2)) := by
  simp only [ePQ, eP, eQ, eC, stat6Seq, stat6Step, lumpStep, lumpAdd, planeLump, lineLump]
  ring

theorem e_small :
    [eC 0, eC 1, eC 2, eC 3, eC 4] = [0, 0, 0, 4, 24] ∧ [eP 0, eP 1, eP 2, eP 3, eP 4] = [0, 0, 0, 4, 48] ∧
    [eQ 0, eQ 1, eQ 2, eQ 3, eQ 4] = [0, 0, 0, 8, 48] ∧
    [ePP 0, ePP 1, ePP 2, ePP 3, ePP 4] = [0, 0, 0, 0, 48] ∧
    [eQQ 0, eQQ 1, eQQ 2, eQQ 3, eQQ 4] = [0, 0, 0, 8, 48] ∧
    [ePQ 0, ePQ 1, ePQ 2, ePQ 3, ePQ 4] = [0, 0, 0, 8, 96] := by
  decide

/-! ## The laws -/

/-- The law of a sequence of `e`-coefficients: `x(0) = 0`, `x(n + 1) = e(n)/4ⁿ`. -/
noncomputable def lawOf (e : ℕ → ℤ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => (e n : ℝ) / 4 ^ n

/-- The excursion's `F`-law: `Σ_{excursions of length m} F(P, Q)/(5·4^{m−1})`. -/
noncomputable def statLaw (F : ℕ → ℕ → ℤ) (m : ℕ) : ℝ := (excursionSum F m : ℝ) / (5 * 4 ^ (m - 1))

theorem statLaw_eq (F : ℕ → ℕ → ℤ) (e : ℕ → ℤ) (he : ∀ n, excursionSum F (n + 1) = 5 * e n) :
    statLaw F = lawOf e := by
  funext m
  rcases m with _ | n
  · simp [statLaw, lawOf, excursionSum_zero]
  · rw [statLaw, lawOf, he n, Nat.add_sub_cancel]
    push_cast
    field_simp

theorem statLaw_C : statLaw fC = excursionLaw := by
  funext m
  simp only [statLaw, excursionLaw, excursionSum_C_eq, Int.cast_natCast]

theorem lawOf_C : lawOf eC = excursionLaw := by
  rw [← statLaw_C, statLaw_eq fC eC excursionSum_C]

/-- The general step of a law's recurrence: `16 x(n + 6)` through `x(n + 5)`, `x(n + 4)`,
`x(n + 3)` and a forcing `y`, from `e(n + 5) = 2e(n + 4) + 3e(n + 3) + 12e(n + 2) + g`. -/
theorem lawOf_step (e : ℕ → ℤ) (n : ℕ) (g : ℤ)
    (h : e (n + 5) = 2 * e (n + 4) + 3 * e (n + 3) + 12 * e (n + 2) + g) :
    16 * lawOf e (n + 6) = 8 * lawOf e (n + 5) + 3 * lawOf e (n + 4) + 3 * lawOf e (n + 3) +
      16 * (g : ℝ) / 4 ^ (n + 5) := by
  simp only [lawOf]
  have h' : (e (n + 5) : ℝ) = 2 * e (n + 4) + 3 * e (n + 3) + 12 * e (n + 2) + g := by
    exact_mod_cast h
  rw [h']
  have h4 : (4 : ℝ) ^ (n + 5) = 4 ^ (n + 2) * 64 := by ring
  have h3 : (4 : ℝ) ^ (n + 4) = 4 ^ (n + 2) * 16 := by ring
  have h2 : (4 : ℝ) ^ (n + 3) = 4 ^ (n + 2) * 4 := by ring
  rw [h4, h3, h2]
  have hp : (0 : ℝ) < 4 ^ (n + 2) := by positivity
  field_simp
  ring

theorem lawOf_succ (e : ℕ → ℤ) (n : ℕ) : lawOf e (n + 1) = (e n : ℝ) / 4 ^ n := rfl

/-! ## The six laws and their recurrences -/

noncomputable def lawP : ℕ → ℝ := lawOf eP
noncomputable def lawQ : ℕ → ℝ := lawOf eQ
noncomputable def lawPP : ℕ → ℝ := lawOf ePP
noncomputable def lawQQ : ℕ → ℝ := lawOf eQQ
noncomputable def lawPQ : ℕ → ℝ := lawOf ePQ

theorem excursionLaw_eq_lawOf (m : ℕ) : excursionLaw m = lawOf eC m := by rw [lawOf_C]

/-- The first values of the six laws, `x(0), …, x(5)`. -/
theorem laws_small :
    (lawOf eC 0 = 0 ∧ lawOf eC 1 = 0 ∧ lawOf eC 2 = 0 ∧ lawOf eC 3 = 0 ∧ lawOf eC 4 = 1 / 16 ∧
      lawOf eC 5 = 3 / 32) ∧
    (lawP 0 = 0 ∧ lawP 1 = 0 ∧ lawP 2 = 0 ∧ lawP 3 = 0 ∧ lawP 4 = 1 / 16 ∧ lawP 5 = 3 / 16) ∧
    (lawQ 0 = 0 ∧ lawQ 1 = 0 ∧ lawQ 2 = 0 ∧ lawQ 3 = 0 ∧ lawQ 4 = 1 / 8 ∧ lawQ 5 = 3 / 16) ∧
    (lawPP 0 = 0 ∧ lawPP 1 = 0 ∧ lawPP 2 = 0 ∧ lawPP 3 = 0 ∧ lawPP 4 = 0 ∧ lawPP 5 = 3 / 16) ∧
    (lawQQ 0 = 0 ∧ lawQQ 1 = 0 ∧ lawQQ 2 = 0 ∧ lawQQ 3 = 0 ∧ lawQQ 4 = 1 / 8 ∧ lawQQ 5 = 3 / 16) ∧
    (lawPQ 0 = 0 ∧ lawPQ 1 = 0 ∧ lawPQ 2 = 0 ∧ lawPQ 3 = 0 ∧ lawPQ 4 = 1 / 8 ∧ lawPQ 5 = 3 / 8) := by
  obtain ⟨hC, hP, hQ, hPP, hQQ, hPQ⟩ := e_small
  simp only [List.cons.injEq, and_true] at hC hP hQ hPP hQQ hPQ
  simp only [lawP, lawQ, lawPP, lawQQ, lawPQ, lawOf, hC.1, hC.2.1, hC.2.2.1, hC.2.2.2.1,
    hC.2.2.2.2, hP.1, hP.2.1, hP.2.2.1, hP.2.2.2.1, hP.2.2.2.2, hQ.1, hQ.2.1, hQ.2.2.1, hQ.2.2.2.1,
    hQ.2.2.2.2, hPP.1, hPP.2.1, hPP.2.2.1, hPP.2.2.2.1, hPP.2.2.2.2, hQQ.1, hQQ.2.1, hQQ.2.2.1,
    hQQ.2.2.2.1, hQQ.2.2.2.2, hPQ.1, hPQ.2.1, hPQ.2.2.1, hPQ.2.2.2.1, hPQ.2.2.2.2]
  norm_num

/-- `16·x(N + 3)` written through `4^{N+5}` at `N = n + 3`. -/
theorem law_shift (e : ℕ → ℤ) (n : ℕ) (k : ℕ) (hk : k ≤ 3) :
    lawOf e (n + 3 + k) = (e (n + 2 + k) : ℝ) / 4 ^ (n + 2 + k) := by
  rw [show n + 3 + k = (n + 2 + k) + 1 by ring, lawOf_succ]

theorem lawP_rec (N : ℕ) :
    16 * lawP (N + 3) = 8 * lawP (N + 2) + 3 * lawP (N + 1) + 3 * lawP N + 8 * excursionLaw (N + 2) +
      3 * excursionLaw (N + 1) + 6 * excursionLaw N + (if N = 1 then 1 else 0) + (if N = 2 then 2 else 0) := by
  obtain ⟨⟨c0, c1, c2, c3, c4, c5⟩, ⟨p0, p1, p2, p3, p4, p5⟩, -⟩ := laws_small
  simp only [excursionLaw_eq_lawOf]
  rcases N with _ | _ | _ | n
  · norm_num [p0, p1, p2, p3, c0, c1, c2]
  · norm_num [p1, p2, p3, p4, c1, c2, c3]
  · norm_num [p2, p3, p4, p5, c2, c3, c4]
  · simp only [show n + 1 + 1 + 1 + 3 = n + 6 by ring, show n + 1 + 1 + 1 + 2 = n + 5 by ring,
      show n + 1 + 1 + 1 + 1 = n + 4 by ring, show n + 1 + 1 + 1 = n + 3 by ring]
    rw [if_neg (by omega), if_neg (by omega), lawP, lawOf_step eP n _ (eP_rec n)]
    simp only [lawOf]
    have h4 : (4 : ℝ) ^ (n + 5) = 4 ^ (n + 2) * 64 := by ring
    have h3 : (4 : ℝ) ^ (n + 4) = 4 ^ (n + 2) * 16 := by ring
    have h2 : (4 : ℝ) ^ (n + 3) = 4 ^ (n + 2) * 4 := by ring
    rw [h4, h3, h2]
    have hp : (0 : ℝ) < 4 ^ (n + 2) := by positivity
    push_cast
    field_simp
    ring

/-- The powers of four over `4^{n+2}`. -/
theorem pow4_split (n : ℕ) :
    (4 : ℝ) ^ (n + 5) = 4 ^ (n + 2) * 64 ∧ (4 : ℝ) ^ (n + 4) = 4 ^ (n + 2) * 16 ∧
      (4 : ℝ) ^ (n + 3) = 4 ^ (n + 2) * 4 := by
  refine ⟨by ring, by ring, by ring⟩

theorem lawQ_rec (N : ℕ) :
    16 * lawQ (N + 3) = 8 * lawQ (N + 2) + 3 * lawQ (N + 1) + 3 * lawQ N + 3 * excursionLaw (N + 1) +
      3 * excursionLaw N + (if N = 1 then 2 else 0) + (if N = 2 then 2 else 0) := by
  obtain ⟨⟨c0, c1, c2, c3, c4, c5⟩, -, ⟨q0, q1, q2, q3, q4, q5⟩, -⟩ := laws_small
  simp only [excursionLaw_eq_lawOf]
  rcases N with _ | _ | _ | n
  · norm_num [q0, q1, q2, q3, c0, c1]
  · norm_num [q1, q2, q3, q4, c1, c2]
  · norm_num [q2, q3, q4, q5, c2, c3]
  · simp only [show n + 1 + 1 + 1 + 3 = n + 6 by ring, show n + 1 + 1 + 1 + 2 = n + 5 by ring,
      show n + 1 + 1 + 1 + 1 = n + 4 by ring, show n + 1 + 1 + 1 = n + 3 by ring]
    rw [if_neg (by omega), if_neg (by omega), lawQ, lawOf_step eQ n _ (eQ_rec n)]
    simp only [lawOf]
    obtain ⟨h4, h3, h2⟩ := pow4_split n
    rw [h4, h3, h2]
    have hp : (0 : ℝ) < 4 ^ (n + 2) := by positivity
    push_cast
    field_simp
    ring

theorem lawPP_rec (N : ℕ) :
    16 * lawPP (N + 3) = 8 * lawPP (N + 2) + 3 * lawPP (N + 1) + 3 * lawPP N + 16 * lawP (N + 2) +
      6 * lawP (N + 1) + 12 * lawP N + 6 * excursionLaw N + (if N = 2 then 2 else 0) := by
  obtain ⟨⟨c0, c1, c2, c3, c4, c5⟩, ⟨p0, p1, p2, p3, p4, p5⟩, -, ⟨r0, r1, r2, r3, r4, r5⟩, -⟩ :=
    laws_small
  simp only [excursionLaw_eq_lawOf]
  rcases N with _ | _ | _ | n
  · norm_num [r0, r1, r2, r3, p0, p1, p2, c0]
  · norm_num [r1, r2, r3, r4, p1, p2, p3, c1]
  · norm_num [r2, r3, r4, r5, p2, p3, p4, c2]
  · simp only [show n + 1 + 1 + 1 + 3 = n + 6 by ring, show n + 1 + 1 + 1 + 2 = n + 5 by ring,
      show n + 1 + 1 + 1 + 1 = n + 4 by ring, show n + 1 + 1 + 1 = n + 3 by ring]
    rw [if_neg (by omega), lawPP, lawP, lawOf_step ePP n _ (ePP_rec n)]
    simp only [lawOf]
    obtain ⟨h4, h3, h2⟩ := pow4_split n
    rw [h4, h3, h2]
    have hp : (0 : ℝ) < 4 ^ (n + 2) := by positivity
    push_cast
    field_simp
    ring

theorem lawQQ_rec (N : ℕ) :
    16 * lawQQ (N + 3) = 8 * lawQQ (N + 2) + 3 * lawQQ (N + 1) + 3 * lawQQ N + 6 * lawQ (N + 1) +
      6 * lawQ N + (if N = 1 then 2 else 0) + (if N = 2 then 2 else 0) := by
  obtain ⟨-, -, ⟨q0, q1, q2, q3, q4, q5⟩, -, ⟨r0, r1, r2, r3, r4, r5⟩, -⟩ := laws_small
  rcases N with _ | _ | _ | n
  · norm_num [r0, r1, r2, r3, q0, q1]
  · norm_num [r1, r2, r3, r4, q1, q2]
  · norm_num [r2, r3, r4, r5, q2, q3]
  · simp only [show n + 1 + 1 + 1 + 3 = n + 6 by ring, show n + 1 + 1 + 1 + 2 = n + 5 by ring,
      show n + 1 + 1 + 1 + 1 = n + 4 by ring, show n + 1 + 1 + 1 = n + 3 by ring]
    rw [if_neg (by omega), if_neg (by omega), lawQQ, lawQ, lawOf_step eQQ n _ (eQQ_rec n)]
    simp only [lawOf]
    obtain ⟨h4, h3, h2⟩ := pow4_split n
    rw [h4, h3, h2]
    have hp : (0 : ℝ) < 4 ^ (n + 2) := by positivity
    push_cast
    field_simp
    ring

theorem lawPQ_rec (N : ℕ) :
    16 * lawPQ (N + 3) = 8 * lawPQ (N + 2) + 3 * lawPQ (N + 1) + 3 * lawPQ N + 8 * lawQ (N + 2) +
      3 * lawP (N + 1) + 3 * lawQ (N + 1) + 3 * excursionLaw (N + 1) + 6 * lawQ N + 3 * lawP N +
      6 * excursionLaw N + (if N = 1 then 2 else 0) + (if N = 2 then 4 else 0) := by
  obtain ⟨⟨c0, c1, c2, c3, c4, c5⟩, ⟨p0, p1, p2, p3, p4, p5⟩, ⟨q0, q1, q2, q3, q4, q5⟩, -, -,
    ⟨r0, r1, r2, r3, r4, r5⟩⟩ := laws_small
  simp only [excursionLaw_eq_lawOf]
  rcases N with _ | _ | _ | n
  · norm_num [r0, r1, r2, r3, q0, q1, q2, p0, p1, c0, c1]
  · norm_num [r1, r2, r3, r4, q1, q2, q3, p1, p2, c1, c2]
  · norm_num [r2, r3, r4, r5, q2, q3, q4, p2, p3, c2, c3]
  · simp only [show n + 1 + 1 + 1 + 3 = n + 6 by ring, show n + 1 + 1 + 1 + 2 = n + 5 by ring,
      show n + 1 + 1 + 1 + 1 = n + 4 by ring, show n + 1 + 1 + 1 = n + 3 by ring]
    rw [if_neg (by omega), if_neg (by omega), lawPQ, lawP, lawQ, lawOf_step ePQ n _ (ePQ_rec n)]
    simp only [lawOf]
    obtain ⟨h4, h3, h2⟩ := pow4_split n
    rw [h4, h3, h2]
    have hp : (0 : ℝ) < 4 ^ (n + 2) := by positivity
    push_cast
    field_simp
    ring

/-! ## The sums of the laws -/

/-- **A law that obeys `16x(N + 3) = 8x(N + 2) + 3x(N + 1) + 3x(N) + y(N)`** and starts at zero
sums to half the sum of its forcing. -/
theorem sum_of_rec {x y : ℕ → ℝ} {X Y : ℝ} (hx : HasSum x X) (hy : HasSum y Y) (h0 : x 0 = 0)
    (h1 : x 1 = 0) (h2 : x 2 = 0)
    (hrec : ∀ N, 16 * x (N + 3) = 8 * x (N + 2) + 3 * x (N + 1) + 3 * x N + y N) : X = Y / 2 := by
  have e3 := (hasSum_shift hx h0 h1 h2 3 le_rfl).mul_left 16
  have e2 := (hasSum_shift hx h0 h1 h2 2 (by norm_num)).mul_left 8
  have e1 := (hasSum_shift hx h0 h1 h2 1 (by norm_num)).mul_left 3
  have e0 := hx.mul_left 3
  have hR := ((e2.add e1).add e0).add hy
  have heq : (fun n => 16 * x (n + 3)) = fun n => 8 * x (n + 2) + 3 * x (n + 1) + 3 * x n + y n :=
    funext hrec
  rw [heq] at e3
  have hu := e3.unique hR
  linarith

theorem cP_le_length : ∀ w : List (Fin 5), cP w ≤ w.length
  | [] => le_rfl
  | t :: w => by
    rw [cP_cons, List.length_cons]
    have := cP_le_length w
    have : dF (relOfWord (t :: w)) ≤ 1 := by unfold dF; split_ifs <;> simp
    omega

theorem cQ_le_length : ∀ w : List (Fin 5), cQ w ≤ w.length
  | [] => le_rfl
  | t :: w => by
    rw [cQ_cons, List.length_cons]
    have := cQ_le_length w
    have : dL (relOfWord (t :: w)) ≤ 1 := by unfold dL; split_ifs <;> simp
    omega

/-- The moments of an excursion bound its laws: `0 ≤ x(m) ≤ m² f(m)`. -/
theorem statLaw_bound (F : ℕ → ℕ → ℤ)
    (hF : ∀ m p q : ℕ, p ≤ m → q ≤ m → 0 ≤ F p q ∧ F p q ≤ (m : ℤ) ^ 2)
    (m : ℕ) : 0 ≤ statLaw F m ∧ statLaw F m ≤ (m : ℝ) ^ 2 * excursionLaw m := by
  have hmem : ∀ w ∈ excursions m, w.length = m := fun w hw => by
    simp only [excursions, Finset.mem_filter] at hw
    exact mem_words.mp hw.1
  have hb : ∀ w ∈ excursions m, 0 ≤ F (cP w) (cQ w) ∧ F (cP w) (cQ w) ≤ (m : ℤ) ^ 2 := fun w hw =>
    hF m _ _ (by rw [← hmem w hw]; exact cP_le_length w) (by rw [← hmem w hw]; exact cQ_le_length w)
  have hlow : (0 : ℤ) ≤ excursionSum F m := Finset.sum_nonneg fun w hw => (hb w hw).1
  have hup : excursionSum F m ≤ (excursionCount m : ℤ) * (m : ℤ) ^ 2 := by
    calc excursionSum F m ≤ ∑ w ∈ excursions m, ((m : ℤ) ^ 2) := Finset.sum_le_sum fun w hw => (hb w hw).2
      _ = (excursionCount m : ℤ) * (m : ℤ) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul, excursionCount]
  have hD : (0 : ℝ) < 5 * 4 ^ (m - 1) := by positivity
  constructor
  · exact div_nonneg (by exact_mod_cast hlow) hD.le
  · rw [statLaw, excursionLaw, mul_div_assoc', div_le_div_iff_of_pos_right hD]
    have h' : (excursionSum F m : ℝ) ≤ (excursionCount m : ℝ) * (m : ℝ) ^ 2 := by exact_mod_cast hup
    linarith

theorem statLaw_summable (F : ℕ → ℕ → ℤ)
    (hF : ∀ m p q : ℕ, p ≤ m → q ≤ m → 0 ≤ F p q ∧ F p q ≤ (m : ℤ) ^ 2) : Summable (statLaw F) :=
  Summable.of_nonneg_of_le (fun m => (statLaw_bound F hF m).1) (fun m => (statLaw_bound F hF m).2)
    (summable_pow_mul_excursionLaw 2)

theorem le_sq_of_le {p m : ℕ} (h : p ≤ m) : (p : ℤ) ≤ (m : ℤ) ^ 2 := by
  have h' : (p : ℤ) ≤ m := by exact_mod_cast h
  have : (m : ℤ) ≤ (m : ℤ) ^ 2 := by
    rcases Nat.eq_zero_or_pos m with hm | hm
    · simp [hm]
    · have : (1 : ℤ) ≤ m := by exact_mod_cast hm
      nlinarith
  linarith

theorem fP_bound : ∀ m p q : ℕ, p ≤ m → q ≤ m → 0 ≤ fP p q ∧ fP p q ≤ (m : ℤ) ^ 2 :=
  fun _ _ _ hp _ => ⟨by simp [fP], le_sq_of_le hp⟩

theorem fQ_bound : ∀ m p q : ℕ, p ≤ m → q ≤ m → 0 ≤ fQ p q ∧ fQ p q ≤ (m : ℤ) ^ 2 :=
  fun _ _ _ _ hq => ⟨by simp [fQ], le_sq_of_le hq⟩

theorem sq_sub_bound {p m : ℕ} (h : p ≤ m) :
    0 ≤ (p : ℤ) * ((p : ℤ) - 1) ∧ (p : ℤ) * ((p : ℤ) - 1) ≤ (m : ℤ) ^ 2 := by
  have h' : (p : ℤ) ≤ m := by exact_mod_cast h
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp; simp
  · have : (1 : ℤ) ≤ p := by exact_mod_cast hp
    constructor <;> nlinarith

theorem fPP_bound : ∀ m p q : ℕ, p ≤ m → q ≤ m → 0 ≤ fPP p q ∧ fPP p q ≤ (m : ℤ) ^ 2 :=
  fun _ _ _ hp _ => sq_sub_bound hp

theorem fQQ_bound : ∀ m p q : ℕ, p ≤ m → q ≤ m → 0 ≤ fQQ p q ∧ fQQ p q ≤ (m : ℤ) ^ 2 :=
  fun _ _ _ _ hq => sq_sub_bound hq

theorem fPQ_bound : ∀ m p q : ℕ, p ≤ m → q ≤ m → 0 ≤ fPQ p q ∧ fPQ p q ≤ (m : ℤ) ^ 2 := by
  intro m p q hp hq
  have hp' : (p : ℤ) ≤ m := by exact_mod_cast hp
  have hq' : (q : ℤ) ≤ m := by exact_mod_cast hq
  have h0 : (0 : ℤ) ≤ p := by positivity
  have h1 : (0 : ℤ) ≤ q := by positivity
  refine ⟨by simp only [fPQ]; positivity, ?_⟩
  simp only [fPQ]
  nlinarith

theorem lawP_eq : lawP = statLaw fP := (statLaw_eq fP eP excursionSum_P).symm
theorem lawQ_eq : lawQ = statLaw fQ := (statLaw_eq fQ eQ excursionSum_Q).symm
theorem lawPP_eq : lawPP = statLaw fPP := (statLaw_eq fPP ePP excursionSum_PP).symm
theorem lawQQ_eq : lawQQ = statLaw fQQ := (statLaw_eq fQQ eQQ excursionSum_QQ).symm
theorem lawPQ_eq : lawPQ = statLaw fPQ := (statLaw_eq fPQ ePQ excursionSum_PQ).symm

theorem excursionLaw_shift (k : ℕ) (hk : k ≤ 3) : HasSum (fun n => excursionLaw (n + k)) 1 :=
  hasSum_shift excursion_total excursionLaw_zero excursionLaw_one excursionLaw_two k hk

/-- **`E P = 10`:** an excursion meets ten symmetric states on average. -/
theorem hasSum_lawP : HasSum lawP 10 := by
  obtain ⟨-, ⟨p0, p1, p2, -, -, -⟩, -⟩ := laws_small
  obtain ⟨X, hX⟩ : Summable lawP := by rw [lawP_eq]; exact statLaw_summable fP fP_bound
  have hy := (((((excursionLaw_shift 2 (by norm_num)).mul_left 8).add
    ((excursionLaw_shift 1 (by norm_num)).mul_left 3)).add (excursion_total.mul_left 6)).add
    (hasSum_ite_one 1)).add (hasSum_ite_two 2)
  have hrec : ∀ N, 16 * lawP (N + 3) = 8 * lawP (N + 2) + 3 * lawP (N + 1) + 3 * lawP N +
      (8 * excursionLaw (N + 2) + 3 * excursionLaw (N + 1) + 6 * excursionLaw N + (if N = 1 then 1 else 0) +
        (if N = 2 then 2 else 0)) := fun N => by rw [lawP_rec N]; ring
  have := sum_of_rec hX hy p0 p1 p2 hrec
  rw [this] at hX
  convert hX using 1
  norm_num

/-- **`E Q = 5`:** an excursion meets five vector states on average. -/
theorem hasSum_lawQ : HasSum lawQ 5 := by
  obtain ⟨-, -, ⟨q0, q1, q2, -, -, -⟩, -⟩ := laws_small
  obtain ⟨X, hX⟩ : Summable lawQ := by rw [lawQ_eq]; exact statLaw_summable fQ fQ_bound
  have hy := ((((excursionLaw_shift 1 (by norm_num)).mul_left 3).add (excursion_total.mul_left 3)).add
    (hasSum_ite_one 2)).add (hasSum_ite_two 2)
  have hrec : ∀ N, 16 * lawQ (N + 3) = 8 * lawQ (N + 2) + 3 * lawQ (N + 1) + 3 * lawQ N +
      (3 * excursionLaw (N + 1) + 3 * excursionLaw N + (if N = 1 then 2 else 0) + (if N = 2 then 2 else 0)) :=
    fun N => by rw [lawQ_rec N]; ring
  have := sum_of_rec hX hy q0 q1 q2 hrec
  rw [this] at hX
  convert hX using 1
  norm_num

theorem law_shift' {x : ℕ → ℝ} {X : ℝ} (hx : HasSum x X) (h0 : x 0 = 0) (h1 : x 1 = 0)
    (h2 : x 2 = 0) (k : ℕ) (hk : k ≤ 3) : HasSum (fun n => x (n + k)) X :=
  hasSum_shift hx h0 h1 h2 k hk

/-- **`E P(P − 1) = 174`.** -/
theorem hasSum_lawPP : HasSum lawPP 174 := by
  obtain ⟨-, ⟨p0, p1, p2, -, -, -⟩, -, ⟨r0, r1, r2, -, -, -⟩, -⟩ := laws_small
  obtain ⟨X, hX⟩ : Summable lawPP := by rw [lawPP_eq]; exact statLaw_summable fPP fPP_bound
  have hP := hasSum_lawP
  have hy := (((((law_shift' hP p0 p1 p2 2 (by norm_num)).mul_left 16).add
    ((law_shift' hP p0 p1 p2 1 (by norm_num)).mul_left 6)).add (hP.mul_left 12)).add
    (excursion_total.mul_left 6)).add (hasSum_ite_two 2)
  have hrec : ∀ N, 16 * lawPP (N + 3) = 8 * lawPP (N + 2) + 3 * lawPP (N + 1) + 3 * lawPP N +
      (16 * lawP (N + 2) + 6 * lawP (N + 1) + 12 * lawP N + 6 * excursionLaw N +
        (if N = 2 then 2 else 0)) := fun N => by rw [lawPP_rec N]; ring
  have := sum_of_rec hX hy r0 r1 r2 hrec
  rw [this] at hX
  convert hX using 1
  norm_num

/-- **`E Q(Q − 1) = 32`.** -/
theorem hasSum_lawQQ : HasSum lawQQ 32 := by
  obtain ⟨-, -, ⟨q0, q1, q2, -, -, -⟩, -, ⟨r0, r1, r2, -, -, -⟩, -⟩ := laws_small
  obtain ⟨X, hX⟩ : Summable lawQQ := by rw [lawQQ_eq]; exact statLaw_summable fQQ fQQ_bound
  have hQ := hasSum_lawQ
  have hy := ((((law_shift' hQ q0 q1 q2 1 (by norm_num)).mul_left 6).add (hQ.mul_left 6)).add
    (hasSum_ite_one 2)).add (hasSum_ite_two 2)
  have hrec : ∀ N, 16 * lawQQ (N + 3) = 8 * lawQQ (N + 2) + 3 * lawQQ (N + 1) + 3 * lawQQ N +
      (6 * lawQ (N + 1) + 6 * lawQ N + (if N = 1 then 2 else 0) + (if N = 2 then 2 else 0)) :=
    fun N => by rw [lawQQ_rec N]; ring
  have := sum_of_rec hX hy r0 r1 r2 hrec
  rw [this] at hX
  convert hX using 1
  norm_num

/-- **`E PQ = 80`.** -/
theorem hasSum_lawPQ : HasSum lawPQ 80 := by
  obtain ⟨-, ⟨p0, p1, p2, -, -, -⟩, ⟨q0, q1, q2, -, -, -⟩, -, -, ⟨r0, r1, r2, -, -, -⟩⟩ :=
    laws_small
  obtain ⟨X, hX⟩ : Summable lawPQ := by rw [lawPQ_eq]; exact statLaw_summable fPQ fPQ_bound
  have hP := hasSum_lawP
  have hQ := hasSum_lawQ
  have hy := ((((((((((law_shift' hQ q0 q1 q2 2 (by norm_num)).mul_left 8).add
    ((law_shift' hP p0 p1 p2 1 (by norm_num)).mul_left 3)).add
    ((law_shift' hQ q0 q1 q2 1 (by norm_num)).mul_left 3)).add
    ((excursionLaw_shift 1 (by norm_num)).mul_left 3)).add (hQ.mul_left 6)).add (hP.mul_left 3)).add
    (excursion_total.mul_left 6)).add (hasSum_ite_one 2)).add (hasSum_ite_two 4))
  have hrec : ∀ N, 16 * lawPQ (N + 3) = 8 * lawPQ (N + 2) + 3 * lawPQ (N + 1) + 3 * lawPQ N +
      (8 * lawQ (N + 2) + 3 * lawP (N + 1) + 3 * lawQ (N + 1) + 3 * excursionLaw (N + 1) + 6 * lawQ N +
        3 * lawP N + 6 * excursionLaw N + (if N = 1 then 2 else 0) + (if N = 2 then 4 else 0)) :=
    fun N => by rw [lawPQ_rec N]; ring
  have := sum_of_rec hX hy r0 r1 r2 hrec
  rw [this] at hX
  convert hX using 1
  norm_num

/-! ## An excursion of `ℓ` steps meets `ℓ − 1` symmetric and vector states -/

theorem dF_add_dL (k : Fin 16) (hk : k ≠ 0) : dF k + dL k = 1 := by
  revert k
  decide

theorem transient_count : ∀ w : List (Fin 5), Transient w → cP w + cQ w = w.length
  | [] => fun _ => rfl
  | t :: w => fun h => by
    rw [transient_cons] at h
    rw [cP_cons, cQ_cons, List.length_cons, ← transient_count w h.2]
    have := dF_add_dL _ h.1
    omega

/-- **`ℓ = 1 + P + Q`** on every excursion. -/
theorem excursion_length_eq {w : List (Fin 5)} (hw : IsExcursion w) : 1 + cP w + cQ w = w.length := by
  obtain ⟨hne, h0, htr⟩ := hw
  cases w with
  | nil => exact absurd rfl hne
  | cons t v =>
    simp only [List.tail_cons] at htr
    rw [cP_cons, cQ_cons, h0, List.length_cons, ← transient_count v htr]
    have : dF 0 = 0 ∧ dL 0 = 0 := by decide
    omega

end Comparison.System.Existence
