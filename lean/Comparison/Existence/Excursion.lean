module

public import Comparison.Existence.Words

/-!
# Book VI. Existence: the excursion and the signed excursion (Propositions 29 and 30)

A walk is a reduced word, newest step
first. An **excursion** is a nonempty walk whose two-spinor state to its first moment is the singlet now and at
no moment between (`IsExcursion`). Among the `5·4ⁿ⁻¹` walks of length `n` there are `excursionCount n`
excursions; each excursion `w` comes back with the sign `coef w`: `γ_w = coef w · 1` (`excursion_scalar`).

* `weightedCount_succ`: the excursions counted state by state (two-spinor state, last-step direction) obey one step of the
  walk: the four continuations of every state not at the start's vertex.
* `lump_count`, `lump_signed`: the counts stay on five classes of the eighty states (the start's
  vertex; a vector state reached from it; a vector state reached from a symmetric state; a symmetric state
  reached from a vector state; a symmetric state reached from a symmetric state), and the signed counts on four; each step
  of a class is checked on all eighty states by `decide`.
* `excursionCount_values`: `0, 0, 0, 20, 120, 300, 1200, 4740` for lengths `1, …, 8`;
  `excursionCount_rec`: `r(n) = 2r(n−1) + 3r(n−2) + 12r(n−3)` for `n ≥ 6`.
  `signedExcursionCount_even`, `signedExcursionCount_odd`: `R(4 + 2k) = −20(−3)^k`, `R` is zero otherwise.
* With `f n = r(n)/(5·4ⁿ⁻¹)` and `φ n = R(n)/(5·4ⁿ⁻¹)`: `f_le`: `f n ≤ (19/20)ⁿ`;
  `excursion_total`: `Σ f = 1`; `excursion_mean`: `Σ n f n = 16`; `excursion_second`: `Σ n² f n = 412`, so the
  variance is `156` (`excursion_variance`); `excursion_gf`: `Σ f n zⁿ = z⁴(1 + z)/(16 − 8z − 3z² − 3z³)`
  for `‖z‖ ≤ 1`; `signed_gf`: `Σ φ n zⁿ = −z⁴/(16 + 3z²)` for `‖z‖ ≤ 1`; `Φ_one`: `−1/19`;
  `Φ_I`: `−1/13`; `a_value`: `(F(1) − Φ(1))/8 = 5/38`.
-/

@[expose] public section

namespace Comparison

open Matrix hiding J
open Complex Kronecker Finset

/-! ## Excursions -/

/-- No moment after the first, up to now, is at the vertex of the first moment. -/
def Transient (w : List (Fin 5)) : Prop := ∀ v ∈ w.tails, v ≠ [] → relOfWord v ≠ 0

instance : DecidablePred Transient := fun w => by unfold Transient; infer_instance

theorem transient_nil : Transient [] := by
  simp [Transient]

theorem transient_cons (t : Fin 5) (w : List (Fin 5)) :
    Transient (t :: w) ↔ relOfWord (t :: w) ≠ 0 ∧ Transient w := by
  simp [Transient, List.tails_cons]

/-- **An excursion:** a nonempty walk at the vertex of its start now and at no moment between. -/
def IsExcursion (w : List (Fin 5)) : Prop := w ≠ [] ∧ relOfWord w = 0 ∧ Transient w.tail

instance : DecidablePred IsExcursion := fun w => by unfold IsExcursion; infer_instance

/-- The excursions of length `n`. -/
def excursions (n : ℕ) : Finset (List (Fin 5)) := (words n).filter fun w => Reduced w ∧ IsExcursion w

/-- The number of excursions of length `n`. -/
def excursionCount (n : ℕ) : ℕ := (excursions n).card

/-- The excursions of length `n` summed with their signs. -/
def signedExcursionCount (n : ℕ) : ℤ := ∑ w ∈ excursions n, coef w

/-- **An excursion closes with a pure sign:** `γ_w = coef w · 1`, `coef w = ±1`. -/
theorem excursion_scalar {w : List (Fin 5)} (hw : relOfWord w = 0) :
    (w.map γ).prod = (coef w : ℂ) • (1 : Matrix Four Four ℂ) := by
  rw [γword_eq, hw]
  rfl

/-- At the end of an excursion the two-spinor state to its first moment is `± Ω`. -/
theorem excursion_rel {w : List (Fin 5)} (hw : relOfWord w = 0) :
    ((w.map γ).prod ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω = (coef w : ℂ) • Ω := by
  rw [history_rel, hw, rel_zero]

/-- The signed count is the sum of the scalars `τ(γ_w) = Tr γ_w / 4` of the excursions. -/
theorem signedExcursionCount_eq (n : ℕ) :
    (signedExcursionCount n : ℂ) = ∑ w ∈ excursions n, ((w.map γ).prod).trace / 4 := by
  rw [signedExcursionCount, Int.cast_sum]
  refine Finset.sum_congr rfl fun w hw => ?_
  simp only [excursions, Finset.mem_filter] at hw
  rw [excursion_scalar hw.2.2.2.1, Matrix.trace_smul, Matrix.trace_one]
  simp

/-! ## Counting state by state -/

/-- The weight of a walk for a table of step signs `μ`. -/
def weight (μ : Fin 5 → Fin 16 → ℤ) : List (Fin 5) → ℤ
  | [] => 1
  | t :: w => μ t (relOfWord w) * weight μ w

theorem weight_transitionSign (w : List (Fin 5)) : weight transitionSign w = coef w := by
  induction w with
  | nil => rfl
  | cons t w ih => simp [weight, coef, ih]

theorem weight_one (w : List (Fin 5)) : weight (fun _ _ => 1) w = 1 := by
  induction w with
  | nil => rfl
  | cons t w ih => simp [weight, ih]

/-- The walks of length `n + 1` at the state `s` (two-spinor state to the first moment, last-step direction) that have
not been at the first moment's vertex since, weighted by `μ`. -/
def weightedCount (μ : Fin 5 → Fin 16 → ℤ) (n : ℕ) (s : State) : ℤ :=
  ∑ w ∈ words (n + 1),
    if Reduced w ∧ w.head? = some s.2 ∧ relOfWord w = s.1 ∧ Transient w.tail then weight μ w
    else 0

/-- **One step of a line:** from every state not at the start's vertex, the four continuations,
each weighted by `μ`. -/
def stepGen (μ : Fin 5 → Fin 16 → ℤ) (v : State → ℤ) (s : State) : ℤ :=
  if transition s.2 s.1 = 0 then 0
  else μ s.2 (transition s.2 s.1) * ∑ g, if g = s.2 then 0 else v (transition s.2 s.1, g)

theorem transition_eq_iff (t : Fin 5) (k k' : Fin 16) : transition t k = k' ↔ k = transition t k' := by
  constructor
  · rintro rfl
    rw [transition_transition]
  · rintro rfl
    rw [transition_transition]

/-- Pulling the sum over walks out of one step. -/
theorem stepGen_swap (c : Prop) [Decidable c] (m : ℤ) (u' : Fin 5) (S : Finset (List (Fin 5)))
    (F : Fin 5 → List (Fin 5) → ℤ) :
    (if c then 0 else m * ∑ g, if g = u' then 0 else ∑ w ∈ S, F g w) =
      ∑ w ∈ S, (if c then 0 else m * ∑ g, if g = u' then 0 else F g w) := by
  split_ifs
  · simp
  · rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    split_ifs <;> simp

/-- The step on one walk `u' :: g₀ :: w₀`, with its two-spinor state `R` and weight `W` named. -/
theorem step_pointwise (μ : Fin 5 → Fin 16 → ℤ) (u' g₀ : Fin 5) (k' R : Fin 16) (Red Tr : Prop)
    [Decidable Red] [Decidable Tr] (W : ℤ) :
    (if (u' ≠ g₀ ∧ Red) ∧ transition u' R = k' ∧ R ≠ 0 ∧ Tr then μ u' R * W else 0) =
      if transition u' k' = 0 then 0 else μ u' (transition u' k') *
        (if g₀ = u' then 0 else if Red ∧ R = transition u' k' ∧ Tr then W else 0) := by
  by_cases hg : g₀ = u'
  · subst hg
    simp
  · by_cases hR : R = transition u' k'
    · subst hR
      rw [transition_transition]
      by_cases hm : transition u' k' = 0
      · simp [hm]
      · simp only [hm, hg, Ne.symm hg, ne_eq, not_false_eq_true, true_and, and_true, ↓reduceIte,
          mul_ite, mul_zero]
    · have hm : transition u' R ≠ k' := fun h => hR (by rw [← h, transition_transition])
      simp only [hm, hR, false_and, and_false, ↓reduceIte, ite_self, mul_zero]

theorem weightedCount_succ (μ : Fin 5 → Fin 16 → ℤ) (n : ℕ) (s : State) :
    weightedCount μ (n + 1) s = stepGen μ (weightedCount μ n) s := by
  obtain ⟨k', u'⟩ := s
  simp only [weightedCount, stepGen]
  rw [sum_words_succ, Finset.sum_eq_single u' ?_ (by simp), stepGen_swap]
  · refine Finset.sum_congr rfl fun w hw => ?_
    rw [mem_words] at hw
    cases w with
    | nil => simp at hw
    | cons g₀ w₀ =>
      rw [Finset.sum_eq_single g₀ (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp only [List.head?_cons, List.tail_cons, ↓reduceIte, true_and, reduced_cons_cons,
        transient_cons, relOfWord_cons, weight]
      exact step_pointwise μ u' g₀ k' _ _ _ _
  · intro t _ ht
    refine Finset.sum_eq_zero fun w _ => ?_
    simp [ht]

/-- The counts and the signed counts by state. -/
def stateCount (n : ℕ) : State → ℤ := weightedCount (fun _ _ => 1) n

def signedStateCount (n : ℕ) : State → ℤ := weightedCount transitionSign n

theorem weightedCount_zero (μ : Fin 5 → Fin 16 → ℤ) (s : State) :
    weightedCount μ 0 s = if transition s.2 0 = s.1 then μ s.2 0 else 0 := by
  simp only [weightedCount]
  rw [sum_words_succ]
  simp only [words, Finset.sum_singleton, List.head?_cons, Option.some.injEq, List.tail_cons]
  rw [Finset.sum_eq_single s.2]
  · simp [reduced_single, transient_nil, relOfWord_cons, weight, relOfWord]
  · intro b _ hb
    simp [hb]
  · simp

/-- The excursions of length `n + 1`, by their last state. -/
theorem excursionCount_succ (n : ℕ) : (excursionCount (n + 1) : ℤ) = ∑ g, stateCount n (0, g) := by
  rw [excursionCount, excursions, Finset.card_filter]
  push_cast
  simp only [stateCount, weightedCount, weight_one]
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

theorem signedExcursionCount_succ (n : ℕ) :
    signedExcursionCount (n + 1) = ∑ g, signedStateCount n (0, g) := by
  rw [signedExcursionCount, excursions, Finset.sum_filter]
  simp only [signedStateCount, weightedCount, weight_transitionSign]
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

/-! ## Five classes of states -/

/-- The class of a state: `0` at the start's vertex; `1` a vector state reached from it; `2` a
vector state reached from a symmetric state; `3` a symmetric state reached from a vector state; `4` a symmetric state reached from a
symmetric state. -/
def stype (s : State) : Fin 5 :=
  if s.1 = 0 then 0
  else if (disagreeSet s.1).card = 4 then (if s.2 ∈ disagreeSet s.1 then 2 else 1)
  else if s.2 ∈ disagreeSet s.1 then 3 else 4

/-- The indicator of a class. -/
def tyInd (X : Fin 5) (s : State) : ℤ := if stype s = X then 1 else 0

/-- The sign pattern of the signed counts on the symmetric states reached from a vector state: `+1` when the
last-step direction is the smaller line of the plane, `−1` when it is the larger. -/
def chiC : State → ℤ := fun s => (![![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0],
  ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![0, 0, 0, 0, 0], ![1, -1, 0, 0, 0], ![1, 0, -1, 0, 0],
  ![1, 0, 0, -1, 0], ![1, 0, 0, 0, -1], ![0, 1, -1, 0, 0], ![0, 1, 0, -1, 0], ![0, 1, 0, 0, -1],
  ![0, 0, 1, -1, 0], ![0, 0, 1, 0, -1], ![0, 0, 0, 1, -1]] : Fin 16 → Fin 5 → ℤ) s.1 s.2

theorem card_classes :
    ((univ.filter fun s => stype s = 0).card, (univ.filter fun s => stype s = 1).card,
      (univ.filter fun s => stype s = 2).card, (univ.filter fun s => stype s = 3).card,
      (univ.filter fun s => stype s = 4).card) = (5, 5, 20, 20, 30) := by
  decide

theorem step_A : ∀ s, stepGen (fun _ _ => 1) (tyInd 1) s = tyInd 3 s := by decide +kernel

theorem step_B : ∀ s, stepGen (fun _ _ => 1) (tyInd 2) s = 3 * tyInd 3 s + 4 * tyInd 0 s := by
  decide +kernel

theorem step_C : ∀ s, stepGen (fun _ _ => 1) (tyInd 3) s = tyInd 2 s + 2 * tyInd 4 s := by
  decide +kernel

theorem step_D : ∀ s, stepGen (fun _ _ => 1) (tyInd 4) s = 3 * tyInd 2 s + 2 * tyInd 4 s := by
  decide +kernel

theorem step_N : ∀ s, stepGen (fun _ _ => 1) (tyInd 0) s = 0 := by decide +kernel

theorem sstep_N : ∀ s, stepGen transitionSign (tyInd 0) s = 0 := by decide +kernel

theorem sstep_A : ∀ s, stepGen transitionSign (tyInd 1) s = chiC s := by decide +kernel

theorem sstep_C : ∀ s, stepGen transitionSign chiC s = -tyInd 2 s := by decide +kernel

theorem sstep_B : ∀ s, stepGen transitionSign (tyInd 2) s = 3 * chiC s + 4 * tyInd 0 s := by
  decide +kernel

theorem stepGen_add (μ : Fin 5 → Fin 16 → ℤ) (u v : State → ℤ) (s : State) :
    stepGen μ (u + v) s = stepGen μ u s + stepGen μ v s := by
  simp only [stepGen, Pi.add_apply]
  split_ifs
  · ring
  · rw [← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    split_ifs <;> ring

theorem stepGen_smul (μ : Fin 5 → Fin 16 → ℤ) (c : ℤ) (v : State → ℤ) (s : State) :
    stepGen μ (c • v) s = c * stepGen μ v s := by
  simp only [stepGen, Pi.smul_apply, smul_eq_mul]
  split_ifs
  · ring
  · rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    split_ifs <;> ring

/-! ## The counts on the classes -/

/-- The five class coefficients of the counts. -/
structure Lump where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  e : ℤ

/-- One step on the classes: `A → C`; `B → 3C + 4N`; `C → B + 2D`; `D → 3B + 2D`; `N → 0`. -/
def lumpStep (x : Lump) : Lump := ⟨0, x.c + 3 * x.d, x.a + 3 * x.b, 2 * x.c + 2 * x.d, 4 * x.b⟩

def lumpSeq : ℕ → Lump
  | 0 => ⟨1, 0, 0, 0, 0⟩
  | n + 1 => lumpStep (lumpSeq n)

def Lump.vec (x : Lump) : State → ℤ :=
  x.a • tyInd 1 + x.b • tyInd 2 + x.c • tyInd 3 + x.d • tyInd 4 + x.e • tyInd 0

theorem stepGen_lump (x : Lump) : stepGen (fun _ _ => 1) x.vec = (lumpStep x).vec := by
  funext s
  simp only [Lump.vec, stepGen_add, stepGen_smul, step_A, step_B, step_C, step_D, step_N,
    lumpStep, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem stateCount_zero : stateCount 0 = (lumpSeq 0).vec := by
  funext s
  rw [stateCount, weightedCount_zero]
  revert s
  decide +kernel

/-- **The counts stay on the classes.** -/
theorem lump_count (n : ℕ) : stateCount n = (lumpSeq n).vec := by
  induction n with
  | zero => exact stateCount_zero
  | succ n ih =>
    funext s
    rw [stateCount, weightedCount_succ, ← stateCount, ih, stepGen_lump]
    rfl

theorem tyInd_place (X : Fin 5) (g : Fin 5) : tyInd X (0, g) = if X = 0 then 1 else 0 := by
  simp only [tyInd, stype, ↓reduceIte]
  split_ifs <;> simp_all [eq_comm]

/-- **The excursions of length `n + 1` are `5 e_n`.** -/
theorem excursionCount_lump (n : ℕ) : (excursionCount (n + 1) : ℤ) = 5 * (lumpSeq n).e := by
  rw [excursionCount_succ, lump_count]
  simp only [Lump.vec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, tyInd_place]
  simp

/-- The signed class coefficients: `A`, the signed symmetric states `chiC`, `B`, the start's vertex. -/
structure SLump where
  a : ℤ
  x : ℤ
  b : ℤ
  e : ℤ

def slumpStep (y : SLump) : SLump := ⟨0, y.a + 3 * y.b, -y.x, 4 * y.b⟩

def slumpSeq : ℕ → SLump
  | 0 => ⟨1, 0, 0, 0⟩
  | n + 1 => slumpStep (slumpSeq n)

def SLump.vec (y : SLump) : State → ℤ :=
  y.a • tyInd 1 + y.x • chiC + y.b • tyInd 2 + y.e • tyInd 0

theorem stepGen_slump (y : SLump) : stepGen transitionSign y.vec = (slumpStep y).vec := by
  funext s
  simp only [SLump.vec, stepGen_add, stepGen_smul, sstep_A, sstep_B, sstep_C, sstep_N,
    slumpStep, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem signedStateCount_zero : signedStateCount 0 = (slumpSeq 0).vec := by
  funext s
  rw [signedStateCount, weightedCount_zero]
  revert s
  decide +kernel

/-- **The signed counts stay on four classes.** -/
theorem lump_signed (n : ℕ) : signedStateCount n = (slumpSeq n).vec := by
  induction n with
  | zero => exact signedStateCount_zero
  | succ n ih =>
    funext s
    rw [signedStateCount, weightedCount_succ, ← signedStateCount, ih, stepGen_slump]
    rfl

theorem chiC_place (g : Fin 5) : chiC (0, g) = 0 := by
  revert g
  decide

theorem signedExcursionCount_lump (n : ℕ) : signedExcursionCount (n + 1) = 5 * (slumpSeq n).e := by
  rw [signedExcursionCount_succ, lump_signed]
  simp only [SLump.vec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, tyInd_place, chiC_place]
  simp

/-! ## The numbers of excursions -/

theorem excursionCount_zero : excursionCount 0 = 0 := by decide

theorem excursionCount_values :
    [excursionCount 1, excursionCount 2, excursionCount 3, excursionCount 4, excursionCount 5, excursionCount 6, excursionCount 7,
      excursionCount 8] = [0, 0, 0, 20, 120, 300, 1200, 4740] := by
  have h : ∀ n, excursionCount (n + 1) = (5 * (lumpSeq n).e).toNat := by
    intro n
    rw [← excursionCount_lump]
    simp
  simp only [h]
  decide

theorem lumpSeq_a (n : ℕ) : (lumpSeq (n + 1)).a = 0 := rfl

/-- The class `B` obeys the law of the excursion: `b(n+3) = 2b(n+2) + 3b(n+1) + 12b(n)`, `n ≥ 1`. -/
theorem lumpSeq_b_rec (n : ℕ) :
    (lumpSeq (n + 4)).b = 2 * (lumpSeq (n + 3)).b + 3 * (lumpSeq (n + 2)).b +
      12 * (lumpSeq (n + 1)).b := by
  simp only [lumpSeq, lumpStep]
  ring

/-- **The law of the excursion:** `r(n) = 2r(n−1) + 3r(n−2) + 12r(n−3)` for `n ≥ 6`. -/
theorem excursionCount_rec (n : ℕ) :
    (excursionCount (n + 6) : ℤ) = 2 * excursionCount (n + 5) + 3 * excursionCount (n + 4) +
      12 * excursionCount (n + 3) := by
  rw [excursionCount_lump, excursionCount_lump, excursionCount_lump, excursionCount_lump]
  have he : ∀ m, (lumpSeq (m + 1)).e = 4 * (lumpSeq m).b := fun m => rfl
  rw [he, he, he, he, lumpSeq_b_rec]
  ring

theorem slumpSeq_even (k : ℕ) : slumpSeq (2 * k + 2) = ⟨0, 0, -(-3) ^ k, 0⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [show 2 * (k + 1) + 2 = (2 * k + 2) + 2 by ring, slumpSeq, slumpSeq, ih]
    simp only [slumpStep]
    congr 1 <;> ring

theorem slumpSeq_odd (k : ℕ) :
    slumpSeq (2 * k + 3) = ⟨0, (-3) ^ (k + 1), 0, -4 * (-3) ^ k⟩ := by
  rw [show 2 * k + 3 = (2 * k + 2) + 1 by ring, slumpSeq, slumpSeq_even]
  simp only [slumpStep]
  congr 1 <;> ring

/-- **The signed excursions of even length:** `R(4 + 2k) = −20(−3)^k`. -/
theorem signedExcursionCount_even (k : ℕ) : signedExcursionCount (2 * k + 4) = -20 * (-3) ^ k := by
  rw [show 2 * k + 4 = (2 * k + 3) + 1 by ring, signedExcursionCount_lump, slumpSeq_odd]
  ring

/-- **The signed excursions of odd length cancel.** -/
theorem signedExcursionCount_odd (k : ℕ) : signedExcursionCount (2 * k + 3) = 0 := by
  rw [show 2 * k + 3 = (2 * k + 2) + 1 by ring, signedExcursionCount_lump, slumpSeq_even]
  ring

theorem signedExcursionCount_small :
    signedExcursionCount 0 = 0 ∧ signedExcursionCount 1 = 0 ∧ signedExcursionCount 2 = 0 := by
  refine ⟨by decide, ?_, ?_⟩
  · rw [signedExcursionCount_lump]; rfl
  · rw [signedExcursionCount_lump]; rfl

/-! ## The laws of the excursion -/

/-- The chance that a walk of length `n` is an excursion: `f n = r(n)/(5·4ⁿ⁻¹)`. -/
noncomputable def excursionLaw (n : ℕ) : ℝ := (excursionCount n : ℝ) / (5 * 4 ^ (n - 1))

/-- The signed chance: `φ n = R(n)/(5·4ⁿ⁻¹)`. -/
noncomputable def signedLaw (n : ℕ) : ℝ := (signedExcursionCount n : ℝ) / (5 * 4 ^ (n - 1))

theorem excursionLaw_nonneg (n : ℕ) : 0 ≤ excursionLaw n := by
  unfold excursionLaw
  positivity

theorem excursionCount_real_rec (n : ℕ) :
    (excursionCount (n + 6) : ℝ) = 2 * excursionCount (n + 5) + 3 * excursionCount (n + 4) +
      12 * excursionCount (n + 3) := by
  exact_mod_cast excursionCount_rec n

theorem excursionCount_small : excursionCount 1 = 0 ∧ excursionCount 2 = 0 ∧ excursionCount 3 = 0 ∧
    excursionCount 4 = 20 ∧ excursionCount 5 = 120 := by
  have h := excursionCount_values
  simp only [List.cons.injEq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩

theorem excursionLaw_zero : excursionLaw 0 = 0 := by simp [excursionLaw, excursionCount_zero]
theorem excursionLaw_one : excursionLaw 1 = 0 := by simp [excursionLaw, excursionCount_small.1]
theorem excursionLaw_two : excursionLaw 2 = 0 := by simp [excursionLaw, excursionCount_small.2.1]
theorem excursionLaw_three : excursionLaw 3 = 0 := by simp [excursionLaw, excursionCount_small.2.2.1]
theorem excursionLaw_four : excursionLaw 4 = 1 / 16 := by
  simp [excursionLaw, excursionCount_small.2.2.2.1]
  norm_num
theorem excursionLaw_five : excursionLaw 5 = 3 / 32 := by
  simp [excursionLaw, excursionCount_small.2.2.2.2]
  norm_num

/-- **The excursion's recurrence:** `16 f(n+3) = 8 f(n+2) + 3 f(n+1) + 3 f(n) + [n = 1] + [n = 2]`,
that is `(16 − 8z − 3z² − 3z³) F(z) = z⁴ + z⁵`. -/
theorem excursionLaw_rec (n : ℕ) :
    16 * excursionLaw (n + 3) = 8 * excursionLaw (n + 2) + 3 * excursionLaw (n + 1) + 3 * excursionLaw n +
      (if n = 1 then 1 else 0) + (if n = 2 then 1 else 0) := by
  rcases n with _ | _ | _ | m
  · simp [excursionLaw_zero, excursionLaw_one, excursionLaw_two, excursionLaw_three]
  · simp [excursionLaw_one, excursionLaw_two, excursionLaw_three, excursionLaw_four]
  · simp [excursionLaw_two, excursionLaw_three, excursionLaw_four, excursionLaw_five]
    norm_num
  · simp only [show m + 1 + 1 + 1 + 3 = m + 6 by ring, show m + 1 + 1 + 1 + 2 = m + 5 by ring,
      show m + 1 + 1 + 1 + 1 = m + 4 by ring, show m + 1 + 1 + 1 = m + 3 by ring]
    rw [if_neg (by omega), if_neg (by omega)]
    unfold excursionLaw
    rw [excursionCount_real_rec m]
    simp only [show m + 6 - 1 = m + 5 by omega, show m + 5 - 1 = m + 4 by omega,
      show m + 4 - 1 = m + 3 by omega, show m + 3 - 1 = m + 2 by omega]
    field_simp
    ring

/-- **The excursion dies out geometrically:** `f n ≤ (19/20)ⁿ`. -/
theorem excursionLaw_le (n : ℕ) : excursionLaw n ≤ (19 / 20 : ℝ) ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 6 with h | h
    · interval_cases n
      · rw [excursionLaw_zero]; positivity
      · rw [excursionLaw_one]; positivity
      · rw [excursionLaw_two]; positivity
      · rw [excursionLaw_three]; positivity
      · rw [excursionLaw_four]; norm_num
      · rw [excursionLaw_five]; norm_num
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      have hrec := excursionLaw_rec m
      rw [if_neg (by omega), if_neg (by omega)] at hrec
      have h1 := ih (m + 2) (by omega)
      have h2 := ih (m + 1) (by omega)
      have h3 := ih m (by omega)
      have hρ : (0 : ℝ) ≤ (19 / 20) ^ m := by positivity
      have key : 8 * (19 / 20 : ℝ) ^ (m + 2) + 3 * (19 / 20) ^ (m + 1) + 3 * (19 / 20) ^ m ≤
          16 * (19 / 20) ^ (m + 3) := by
        have e1 : 8 * (19 / 20 : ℝ) ^ (m + 2) + 3 * (19 / 20) ^ (m + 1) + 3 * (19 / 20) ^ m =
            (19 / 20) ^ m * (8 * (19 / 20) ^ 2 + 3 * (19 / 20) + 3) := by ring
        have e2 : 16 * (19 / 20 : ℝ) ^ (m + 3) = (19 / 20) ^ m * (16 * (19 / 20) ^ 3) := by ring
        rw [e1, e2]
        exact mul_le_mul_of_nonneg_left (by norm_num) hρ
      linarith

theorem summable_pow_mul_excursionLaw (k : ℕ) : Summable fun n : ℕ => (n : ℝ) ^ k * excursionLaw n := by
  refine Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity) (excursionLaw_nonneg n))
    (fun n => mul_le_mul_of_nonneg_left (excursionLaw_le n) (by positivity)) ?_
  exact summable_pow_mul_geometric_of_norm_lt_one k (by norm_num)

theorem summable_excursionLaw : Summable excursionLaw := by
  simpa using summable_pow_mul_excursionLaw 0

/-- The sum of a shifted law: the first three values are zero. -/
theorem hasSum_shift {g : ℕ → ℝ} {S : ℝ} (hg : HasSum g S) (h0 : g 0 = 0) (h1 : g 1 = 0)
    (h2 : g 2 = 0) (k : ℕ) (hk : k ≤ 3) : HasSum (fun n => g (n + k)) S := by
  have := (hasSum_nat_add_iff' k).mpr hg
  have hz : ∑ i ∈ Finset.range k, g i = 0 := by
    interval_cases k <;> simp [Finset.sum_range_succ, h0, h1, h2]
  rwa [hz, sub_zero] at this

theorem hasSum_ite_one (c : ℝ) : HasSum (fun n : ℕ => if n = 1 then c else 0) c :=
  hasSum_ite_eq 1 c

theorem hasSum_ite_two (c : ℝ) : HasSum (fun n : ℕ => if n = 2 then c else 0) c :=
  hasSum_ite_eq 2 c

/-- **Every excursion closes:** `F(1) = Σ f = 1`. -/
theorem excursion_total : HasSum excursionLaw 1 := by
  obtain ⟨S, hS⟩ := summable_excursionLaw
  have h3 := hasSum_shift hS excursionLaw_zero excursionLaw_one excursionLaw_two 3 le_rfl
  have h2 := hasSum_shift hS excursionLaw_zero excursionLaw_one excursionLaw_two 2 (by norm_num)
  have h1 := hasSum_shift hS excursionLaw_zero excursionLaw_one excursionLaw_two 1 (by norm_num)
  have hL := h3.mul_left 16
  have hR := ((((h2.mul_left 8).add (h1.mul_left 3)).add (hS.mul_left 3)).add
    (hasSum_ite_one 1)).add (hasSum_ite_two 1)
  have heq : (fun n => 16 * excursionLaw (n + 3)) = fun n => 8 * excursionLaw (n + 2) +
      3 * excursionLaw (n + 1) + 3 * excursionLaw n + (if n = 1 then 1 else 0) +
      (if n = 2 then 1 else 0) := funext excursionLaw_rec
  rw [heq] at hL
  have hu := hL.unique hR
  have : S = 1 := by linarith
  rwa [this] at hS

theorem hasSum_mul_shift {g : ℕ → ℝ} {S0 S1 : ℝ} (h0 : HasSum g S0)
    (h1 : HasSum (fun n : ℕ => (n : ℝ) * g n) S1) (hg0 : g 0 = 0) (hg1 : g 1 = 0) (hg2 : g 2 = 0)
    (j k : ℕ) (hk : k ≤ 3) :
    HasSum (fun n : ℕ => ((n : ℝ) + j + k) * g (n + k)) (S1 + j * S0) := by
  have a := hasSum_shift h1 (by simp [hg0]) (by simp [hg1]) (by simp [hg2]) k hk
  have b := (hasSum_shift h0 hg0 hg1 hg2 k hk).mul_left (j : ℝ)
  have := a.add b
  convert this using 1
  funext n
  push_cast
  ring

/-- **The mean excursion is sixteen steps:** `Σ n f(n) = 16`. -/
theorem excursion_mean : HasSum (fun n : ℕ => (n : ℝ) * excursionLaw n) 16 := by
  obtain ⟨S1, hS1⟩ := (summable_pow_mul_excursionLaw 1)
  simp only [pow_one] at hS1
  have h0 := excursion_total
  have e3 := hasSum_mul_shift h0 hS1 excursionLaw_zero excursionLaw_one excursionLaw_two 0 3 le_rfl
  have e2 := hasSum_mul_shift h0 hS1 excursionLaw_zero excursionLaw_one excursionLaw_two 1 2 (by norm_num)
  have e1 := hasSum_mul_shift h0 hS1 excursionLaw_zero excursionLaw_one excursionLaw_two 2 1 (by norm_num)
  have e0 : HasSum (fun n : ℕ => ((n : ℝ) + 3) * excursionLaw n) (S1 + 3 * 1) := by
    have := hS1.add (h0.mul_left 3)
    convert this using 1
    funext n
    ring
  have hL := e3.mul_left 16
  have hR := ((((e2.mul_left 8).add (e1.mul_left 3)).add (e0.mul_left 3)).add
    (hasSum_ite_one 4)).add (hasSum_ite_two 5)
  have heq : (fun n : ℕ => 16 * (((n : ℝ) + (0 : ℕ) + (3 : ℕ)) * excursionLaw (n + 3))) =
      fun n : ℕ => 8 * (((n : ℝ) + (1 : ℕ) + (2 : ℕ)) * excursionLaw (n + 2)) +
        3 * (((n : ℝ) + (2 : ℕ) + (1 : ℕ)) * excursionLaw (n + 1)) + 3 * (((n : ℝ) + 3) * excursionLaw n) +
        (if n = 1 then 4 else 0) + (if n = 2 then 5 else 0) := by
    funext n
    have := excursionLaw_rec n
    push_cast
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n <;> simp at this ⊢ <;> linarith
    · rw [if_neg (by omega), if_neg (by omega)] at this ⊢
      have hn : (n : ℝ) + 3 = (n : ℝ) + 0 + 3 := by ring
      nlinarith [this]
  rw [heq] at hL
  have hu := hL.unique hR
  push_cast at hu
  have : S1 = 16 := by linarith
  rwa [this] at hS1

/-- **The second moment of the excursion:** `Σ n² f(n) = 412`. -/
theorem excursion_second : HasSum (fun n : ℕ => (n : ℝ) ^ 2 * excursionLaw n) 412 := by
  obtain ⟨S2, hS2⟩ := summable_pow_mul_excursionLaw 2
  have h0 := excursion_total
  have h1 := excursion_mean
  have sq : ∀ (j k : ℕ), k ≤ 3 →
      HasSum (fun n : ℕ => ((n : ℝ) + j + k) ^ 2 * excursionLaw (n + k))
        (S2 + 2 * j * 16 + j ^ 2 * 1) := by
    intro j k hk
    have a := hasSum_shift hS2 (by simp [excursionLaw_zero]) (by simp [excursionLaw_one])
      (by simp [excursionLaw_two]) k hk
    have b := (hasSum_shift h1 (by simp [excursionLaw_zero]) (by simp [excursionLaw_one])
      (by simp [excursionLaw_two]) k hk).mul_left (2 * (j : ℝ))
    have c := (hasSum_shift h0 excursionLaw_zero excursionLaw_one excursionLaw_two k hk).mul_left ((j : ℝ) ^ 2)
    have := (a.add b).add c
    convert this using 1
    funext n
    push_cast
    ring
  have e3 := sq 0 3 le_rfl
  have e2 := sq 1 2 (by norm_num)
  have e1 := sq 2 1 (by norm_num)
  have e0 := sq 3 0 (by norm_num)
  have hL := e3.mul_left 16
  have hR := ((((e2.mul_left 8).add (e1.mul_left 3)).add (e0.mul_left 3)).add
    (hasSum_ite_one 16)).add (hasSum_ite_two 25)
  have heq : (fun n : ℕ => 16 * (((n : ℝ) + (0 : ℕ) + (3 : ℕ)) ^ 2 * excursionLaw (n + 3))) =
      fun n : ℕ => 8 * (((n : ℝ) + (1 : ℕ) + (2 : ℕ)) ^ 2 * excursionLaw (n + 2)) +
        3 * (((n : ℝ) + (2 : ℕ) + (1 : ℕ)) ^ 2 * excursionLaw (n + 1)) +
        3 * (((n : ℝ) + (3 : ℕ) + (0 : ℕ)) ^ 2 * excursionLaw (n + 0)) +
        (if n = 1 then 16 else 0) + (if n = 2 then 25 else 0) := by
    funext n
    have := excursionLaw_rec n
    push_cast
    rcases Nat.lt_or_ge n 3 with h | h
    · interval_cases n <;> simp at this ⊢ <;> linarith
    · rw [if_neg (by omega), if_neg (by omega)] at this ⊢
      simp only [add_zero]
      have e : ((n : ℝ) + 1 + 2) = (n : ℝ) + 3 := by ring
      have e' : ((n : ℝ) + 2 + 1) = (n : ℝ) + 3 := by ring
      rw [e, e']
      linear_combination ((n : ℝ) + 3) ^ 2 * this
  rw [heq] at hL
  have hu := hL.unique hR
  push_cast at hu
  have : S2 = 412 := by linarith
  rwa [this] at hS2

/-- **The variance of the excursion is 156:** `Σ n² f − (Σ n f)² = 412 − 16² = 156`. -/
theorem excursion_variance :
    (∑' n : ℕ, (n : ℝ) ^ 2 * excursionLaw n) - (∑' n : ℕ, (n : ℝ) * excursionLaw n) ^ 2 = 156 := by
  rw [excursion_second.tsum_eq, excursion_mean.tsum_eq]
  norm_num

/-! ## The generating functions -/

theorem norm_cubic_lt (z : ℂ) (hz : ‖z‖ ≤ 1) : ‖8 * z + 3 * z ^ 2 + 3 * z ^ 3‖ < 16 := by
  calc ‖8 * z + 3 * z ^ 2 + 3 * z ^ 3‖ ≤ ‖8 * z‖ + ‖3 * z ^ 2‖ + ‖3 * z ^ 3‖ := norm_add₃_le
    _ = 8 * ‖z‖ + 3 * ‖z‖ ^ 2 + 3 * ‖z‖ ^ 3 := by simp [norm_pow]
    _ ≤ 8 + 3 + 3 := by
        have h0 : 0 ≤ ‖z‖ := norm_nonneg z
        have h2 : ‖z‖ ^ 2 ≤ 1 := pow_le_one₀ h0 hz
        have h3 : ‖z‖ ^ 3 ≤ 1 := pow_le_one₀ h0 hz
        linarith
    _ < 16 := by norm_num

theorem denom_ne_zero (z : ℂ) (hz : ‖z‖ ≤ 1) : 16 - 8 * z - 3 * z ^ 2 - 3 * z ^ 3 ≠ 0 := by
  intro h
  have : 8 * z + 3 * z ^ 2 + 3 * z ^ 3 = 16 := by linear_combination -h
  have h2 := norm_cubic_lt z hz
  rw [this] at h2
  norm_num at h2

/-- **The excursion's generating function:** `F(z) = Σ f n zⁿ = z⁴(1 + z)/(16 − 8z − 3z² − 3z³)` for
every `‖z‖ ≤ 1`. -/
theorem excursion_gf (z : ℂ) (hz : ‖z‖ ≤ 1) :
    HasSum (fun n => (excursionLaw n : ℂ) * z ^ n)
      (z ^ 4 * (1 + z) / (16 - 8 * z - 3 * z ^ 2 - 3 * z ^ 3)) := by
  have hsum : Summable fun n => (excursionLaw n : ℂ) * z ^ n := by
    refine Summable.of_norm_bounded summable_excursionLaw fun n => ?_
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_of_nonneg (excursionLaw_nonneg n)]
    exact mul_le_of_le_one_right (excursionLaw_nonneg n) (pow_le_one₀ (norm_nonneg z) hz)
  obtain ⟨G, hG⟩ := hsum
  set g : ℕ → ℂ := fun n => (excursionLaw n : ℂ) * z ^ n with hgdef
  have g0 : g 0 = 0 := by simp [g, excursionLaw_zero]
  have g1 : g 1 = 0 := by simp [g, excursionLaw_one]
  have g2 : g 2 = 0 := by simp [g, excursionLaw_two]
  have shift : ∀ k ≤ 3, HasSum (fun n => g (n + k)) G := by
    intro k hk
    have := (hasSum_nat_add_iff' k).mpr hG
    have hz0 : ∑ i ∈ Finset.range k, g i = 0 := by
      interval_cases k <;> simp [Finset.sum_range_succ, g0, g1, g2]
    rwa [hz0, sub_zero] at this
  have hL := (shift 3 le_rfl).mul_left 16
  have hR := ((((((shift 2 (by norm_num)).mul_left (8 * z)).add
    ((shift 1 (by norm_num)).mul_left (3 * z ^ 2))).add ((shift 0 (by norm_num)).mul_left
    (3 * z ^ 3))).add (hasSum_ite_eq 1 (z ^ 4))).add (hasSum_ite_eq 2 (z ^ 5)))
  have heq : (fun n => 16 * g (n + 3)) = fun n => 8 * z * g (n + 2) + 3 * z ^ 2 * g (n + 1) +
      3 * z ^ 3 * g (n + 0) + (if n = 1 then z ^ 4 else 0) + (if n = 2 then z ^ 5 else 0) := by
    funext n
    have h := excursionLaw_rec n
    simp only [g, add_zero]
    have hc : (16 : ℂ) * (excursionLaw (n + 3) : ℂ) = 8 * excursionLaw (n + 2) + 3 * excursionLaw (n + 1) +
        3 * excursionLaw n + (if n = 1 then 1 else 0) + (if n = 2 then 1 else 0) := by
      have := congrArg (fun x : ℝ => (x : ℂ)) h
      push_cast at this
      rw [this]
      split_ifs <;> simp
    have hz3 : z ^ (n + 3) = z ^ 3 * z ^ n := by ring
    have hz2 : z ^ (n + 2) = z ^ 2 * z ^ n := by ring
    have hz1 : z ^ (n + 1) = z * z ^ n := by ring
    rw [hz3, hz2, hz1]
    calc 16 * ((excursionLaw (n + 3) : ℂ) * (z ^ 3 * z ^ n)) =
        z ^ 3 * z ^ n * (16 * (excursionLaw (n + 3) : ℂ)) := by ring
      _ = z ^ 3 * z ^ n * (8 * excursionLaw (n + 2) + 3 * excursionLaw (n + 1) + 3 * excursionLaw n +
          (if n = 1 then 1 else 0) + (if n = 2 then 1 else 0)) := by rw [hc]
      _ = _ := by
        split_ifs with h1 h2 h2
        · omega
        · subst h1; ring
        · subst h2; ring
        · ring
  rw [heq] at hL
  have hu := hL.unique hR
  have hd := denom_ne_zero z hz
  have hG' : G = z ^ 4 * (1 + z) / (16 - 8 * z - 3 * z ^ 2 - 3 * z ^ 3) := by
    rw [eq_div_iff hd]
    linear_combination hu
  rw [← hG']
  exact hG

/-- The closed form of the signed law: `φ(4 + 2k) = −(1/16)(−3/16)^k`, zero otherwise. -/
theorem signedLaw_eq (n : ℕ) :
    signedLaw n = if 4 ≤ n ∧ n % 2 = 0 then -(1 / 16) * (-3 / 16 : ℝ) ^ ((n - 4) / 2) else 0 := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · rcases Nat.lt_or_ge m 2 with h | h
    · interval_cases m <;> subst hm
      · simp [signedLaw, signedExcursionCount_small.1]
      · simp [signedLaw, signedExcursionCount_small.2.2]
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
      subst hm
      rw [if_pos ⟨by omega, by omega⟩, signedLaw,
        show k + 2 + (k + 2) = 2 * k + 4 by ring, signedExcursionCount_even,
        show (2 * k + 4 - 4) / 2 = k by omega, show 2 * k + 4 - 1 = 2 * k + 3 by omega]
      push_cast
      have h16 : (4 : ℝ) ^ (2 * k + 3) = 64 * 16 ^ k := by
        rw [pow_add, pow_mul]
        norm_num
        ring
      rw [h16, div_pow]
      field_simp
      ring
  · subst hm
    rw [if_neg (by omega), signedLaw]
    rcases m with _ | m
    · simp [signedExcursionCount_small.2.1]
    · rw [show 2 * (m + 1) + 1 = 2 * m + 3 by ring, signedExcursionCount_odd]
      simp

/-- **The signed excursion's generating function:** `Φ(z) = Σ φ n zⁿ = −z⁴/(16 + 3z²)` for `‖z‖ ≤ 1`. -/
theorem signed_gf (z : ℂ) (hz : ‖z‖ ≤ 1) :
    HasSum (fun n => (signedLaw n : ℂ) * z ^ n) (-z ^ 4 / (16 + 3 * z ^ 2)) := by
  have hq : ‖(-3 / 16 : ℂ) * z ^ 2‖ < 1 := by
    rw [norm_mul, norm_pow]
    have : ‖(-3 / 16 : ℂ)‖ = 3 / 16 := by norm_num
    rw [this]
    have h2 : ‖z‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg z) hz
    nlinarith [norm_nonneg z]
  have hgeom := (hasSum_geometric_of_norm_lt_one hq).mul_left (-(z ^ 4) / 16)
  have hd : (16 + 3 * z ^ 2 : ℂ) ≠ 0 := by
    intro h
    have : (-3 / 16 : ℂ) * z ^ 2 = 1 := by linear_combination -h / 16
    rw [this] at hq
    simp at hq
  have hval : -(z ^ 4) / 16 * (1 - (-3 / 16 : ℂ) * z ^ 2)⁻¹ = -z ^ 4 / (16 + 3 * z ^ 2) := by
    have h' : (1 - (-3 / 16 : ℂ) * z ^ 2) = (16 + 3 * z ^ 2) / 16 := by ring
    rw [h', inv_div]
    field_simp
  rw [hval] at hgeom
  have hinj : Function.Injective fun k : ℕ => 2 * k + 4 := by
    intro a b h
    simp only at h
    omega
  rw [← hinj.hasSum_iff]
  · convert hgeom using 1
    funext k
    simp only [Function.comp_apply]
    rw [signedLaw_eq, if_pos ⟨by omega, by omega⟩, show (2 * k + 4 - 4) / 2 = k by omega]
    push_cast
    rw [mul_pow, ← pow_mul, show 2 * k + 4 = 2 * k + 4 from rfl, pow_add]
    ring
  · intro n hn
    rw [signedLaw_eq, if_neg]
    · simp
    · rintro ⟨h4, h2⟩
      exact hn ⟨(n - 4) / 2, by simp only; omega⟩

/-- **`Φ(1) = −1/19`.** -/
theorem Φ_one : HasSum signedLaw (-1 / 19) := by
  have h := signed_gf 1 (by simp)
  simp only [one_pow, mul_one] at h
  have h' : HasSum (fun n => ((signedLaw n : ℝ) : ℂ)) ((-1 / 19 : ℝ) : ℂ) := by
    convert h using 1
    push_cast
    norm_num
  exact (Complex.hasSum_ofReal).mp h'

/-- **`Φ(i) = −1/13`.** -/
theorem Φ_I : HasSum (fun n => (signedLaw n : ℂ) * Complex.I ^ n) (-1 / 13) := by
  have h := signed_gf Complex.I (by simp)
  convert h using 1
  rw [show Complex.I ^ 4 = 1 by rw [pow_succ, pow_succ, pow_succ, pow_one]; simp,
    Complex.I_sq]
  norm_num

/-- **`F(1) = 1` and `Φ(1) = −1/19` give `a = (F(1) − Φ(1))/8 = 5/38`**, and the chances
`(F(1) + Φ(1))/2 = 9/19` of an excursion keeping its sign and `(F(1) − Φ(1))/2 = 10/19` of reversing it. -/
theorem a_value :
    ((∑' n, excursionLaw n) - (∑' n, signedLaw n)) / 8 = 5 / 38 ∧
    ((∑' n, excursionLaw n) + (∑' n, signedLaw n)) / 2 = 9 / 19 ∧
    ((∑' n, excursionLaw n) - (∑' n, signedLaw n)) / 2 = 10 / 19 := by
  rw [excursion_total.tsum_eq, Φ_one.tsum_eq]
  norm_num

end Comparison

end
