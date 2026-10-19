module

public import Comparison.Existence.Walk

/-!
# Book VI. Existence: walks are reduced words (Propositions 24 and 25)

A walk is a list of changes, the newest
first: `[t_k, …, t_1]`. Its product is `γ_w = γ_{t_k} ⋯ γ_{t_1}` (`(w.map γ).prod`).

* `γ_mul_γ_scalar_iff`: `γ_s γ_t ∈ ℂ·1 ⟺ s = t` (Prop. 24).
* `Reduced`: no change follows itself; `card_reduced`: `5·4ⁿ` reduced words of length `n + 1`.
* `reduce`: the stack reduction; `reduce_reduced`, `reduce_of_reduced`; `Cancel`: removing one
  pair `tt`; `reduce_eq_of_cancel`, `cancels_to_reduce`, `unique_reduced`: every word reduces by
  removing pairs `tt` to exactly one reduced word.
* `relOfWord`: the two-spinor state of the line now to its first moment, as an index of the sixteen;
  `coef`: its sign; `history_rel`: `(γ_w ⊗ 1) Ω = ± e_{relOfWord w}` (Prop. 25);
  `disagreeSet_relOfWord`: the disagreement set is `T_{t_k} △ ⋯ △ T_{t_1}`, `T_t = [5] ∖ {t}`;
  `relOfWord_append`: the two-spinor states of moments compose; `relOfWord_surjective`: the five `T_t`
  reach all sixteen two-spinor states.
-/

@[expose] public section

namespace Comparison

open Matrix hiding J
open Complex Kronecker

/-! ## Two steps that give a number -/

theorem trace_γ_mul_γ (s t : Fin 5) : (γ s * γ t).trace = if s = t then 4 else 0 := by
  rw [← obs_lineIdx, ← obs_lineIdx, trace_obs_mul]
  have hinj : Function.Injective lineIdx := by decide
  by_cases h : s = t
  · simp [h]
  · rw [if_neg (fun h' => h (hinj h')), if_neg h]

/-- **Proposition 24, first part:** `γ_s γ_t` is a number exactly when `s = t`. -/
theorem γ_mul_γ_scalar_iff (s t : Fin 5) :
    (∃ c : ℂ, γ s * γ t = c • (1 : Matrix Four Four ℂ)) ↔ s = t := by
  constructor
  · rintro ⟨c, hc⟩
    by_contra h
    have htr := congrArg Matrix.trace hc
    rw [trace_γ_mul_γ, if_neg h, Matrix.trace_smul, Matrix.trace_one] at htr
    simp only [Fintype.card_prod, Fintype.card_fin, smul_eq_mul] at htr
    have hc0 : c = 0 := by
      have : (c * ((2 * 2 : ℕ) : ℂ)) = 0 := htr.symm
      simpa using this
    rw [hc0, zero_smul] at hc
    have h1 : γ t = 0 := by
      have := congrArg (fun M => γ s * M) hc
      simpa [← Matrix.mul_assoc, γ_mul_self] using this
    have h2 := γ_mul_self t
    rw [h1, Matrix.zero_mul] at h2
    exact zero_ne_one h2
  · rintro rfl
    exact ⟨1, by rw [γ_mul_self, one_smul]⟩

/-! ## Words of a given length -/

/-- The words of length `n` in the five changes, newest change first. -/
def words : ℕ → Finset (List (Fin 5))
  | 0 => {[]}
  | n + 1 => (Finset.univ ×ˢ words n).image fun p => p.1 :: p.2

theorem mem_words {n : ℕ} {w : List (Fin 5)} : w ∈ words n ↔ w.length = n := by
  induction n generalizing w with
  | zero => simp [words]
  | succ n ih =>
    constructor
    · intro h
      simp only [words, Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and] at h
      obtain ⟨⟨t, w'⟩, hw', rfl⟩ := h
      simp [ih.mp hw']
    · intro h
      cases w with
      | nil => simp at h
      | cons t w' =>
        simp only [words, Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and]
        exact ⟨(t, w'), ih.mpr (by simpa using h), rfl⟩

theorem sum_words_succ {M : Type*} [AddCommMonoid M] (n : ℕ) (f : List (Fin 5) → M) :
    ∑ w ∈ words (n + 1), f w = ∑ t, ∑ w ∈ words n, f (t :: w) := by
  rw [words, Finset.sum_image, Finset.sum_product]
  intro p _ q _ h
  simp only [List.cons.injEq] at h
  exact Prod.ext h.1 h.2

theorem card_words (n : ℕ) : (words n).card = 5 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [words, Finset.card_image_of_injective, Finset.card_product, Finset.card_univ,
      Fintype.card_fin, ih, pow_succ, mul_comm]
    intro p q h
    simp only [List.cons.injEq] at h
    exact Prod.ext h.1 h.2

/-! ## Reduced words -/

/-- **A walk is a reduced word:** no change follows itself. -/
def Reduced (w : List (Fin 5)) : Prop := w.IsChain (· ≠ ·)

instance : DecidablePred Reduced := fun w => by unfold Reduced; infer_instance

theorem reduced_nil : Reduced [] := List.IsChain.nil

theorem reduced_single (t : Fin 5) : Reduced [t] := List.IsChain.singleton t

theorem reduced_cons_cons (s t : Fin 5) (w : List (Fin 5)) :
    Reduced (s :: t :: w) ↔ s ≠ t ∧ Reduced (t :: w) := List.isChain_cons_cons

theorem reduced_of_cons {t : Fin 5} {w : List (Fin 5)} (h : Reduced (t :: w)) : Reduced w :=
  List.IsChain.tail h

/-- The reduced words of length `n + 1` that begin (newest first) with `g`. -/
def reducedFrom (n : ℕ) (g : Fin 5) : ℕ :=
  ∑ w ∈ words (n + 1), if Reduced w ∧ w.head? = some g then 1 else 0

theorem reducedFrom_succ (n : ℕ) (g : Fin 5) :
    reducedFrom (n + 1) g = ∑ g', if g' = g then 0 else reducedFrom n g' := by
  unfold reducedFrom
  rw [sum_words_succ]
  have h1 : ∀ t : Fin 5, (∑ w ∈ words (n + 1),
      if Reduced (t :: w) ∧ (t :: w).head? = some g then 1 else 0) =
      if t = g then ∑ w ∈ words (n + 1), (if Reduced (g :: w) then 1 else 0) else 0 := by
    intro t
    by_cases ht : t = g
    · subst ht
      simp
    · simp [ht]
  rw [Finset.sum_congr rfl fun t _ => h1 t, Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  have h2 : ∀ g' : Fin 5, (if g' = g then 0 else ∑ w ∈ words (n + 1),
      if Reduced w ∧ w.head? = some g' then 1 else 0) =
      ∑ w ∈ words (n + 1), if g' = g then 0 else
        (if Reduced w ∧ w.head? = some g' then 1 else 0) := by
    intro g'
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun g' _ => h2 g', Finset.sum_comm]
  refine Finset.sum_congr rfl fun w hw => ?_
  rw [mem_words] at hw
  cases w with
  | nil => simp at hw
  | cons t w =>
    simp only [List.head?_cons, Option.some.injEq, reduced_cons_cons]
    rw [Finset.sum_eq_single t]
    · by_cases h : t = g
      · subst h
        simp
      · simp [h, Ne.symm h]
    · intro b _ hb
      simp [Ne.symm hb]
    · simp

theorem reducedFrom_eq (n : ℕ) (g : Fin 5) : reducedFrom n g = 4 ^ n := by
  induction n generalizing g with
  | zero =>
    unfold reducedFrom
    rw [sum_words_succ]
    simp only [words, Finset.sum_singleton, List.head?_cons, Option.some.injEq, pow_zero]
    rw [Finset.sum_eq_single g]
    · simp [reduced_single]
    · intro b _ hb
      simp [hb]
    · simp
  | succ n ih =>
    rw [reducedFrom_succ]
    simp only [ih]
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, smul_eq_mul]
    have : (Finset.univ.filter fun g' : Fin 5 => ¬g' = g).card = 4 := by
      rw [Finset.filter_ne' Finset.univ g, Finset.card_erase_of_mem (Finset.mem_univ g)]
      simp
    rw [this, pow_succ, mul_comm]

/-- **`5 · 4ⁿ` walks of length `n + 1`.** -/
theorem card_reduced (n : ℕ) : ((words (n + 1)).filter Reduced).card = 5 * 4 ^ n := by
  have h : ((words (n + 1)).filter Reduced).card = ∑ g, reducedFrom n g := by
    rw [Finset.card_filter]
    unfold reducedFrom
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [mem_words] at hw
    cases w with
    | nil => simp at hw
    | cons t w =>
      simp only [List.head?_cons, Option.some.injEq]
      rw [Finset.sum_eq_single t (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
      simp
  rw [h]
  simp [reducedFrom_eq]

/-! ## The reduction of a word -/

/-- Put the change `t` in front of a word, cancelling it against an equal newest change. -/
def push (t : Fin 5) : List (Fin 5) → List (Fin 5)
  | [] => [t]
  | s :: w => if t = s then w else t :: s :: w

/-- **The reduced word of a word:** every pair `tt` removed. -/
def reduce : List (Fin 5) → List (Fin 5)
  | [] => []
  | t :: w => push t (reduce w)

theorem push_reduced (t : Fin 5) {w : List (Fin 5)} (hw : Reduced w) : Reduced (push t w) := by
  cases w with
  | nil => exact reduced_single t
  | cons s w =>
    simp only [push]
    split_ifs with h
    · exact reduced_of_cons hw
    · exact (reduced_cons_cons t s w).mpr ⟨h, hw⟩

theorem reduce_reduced (w : List (Fin 5)) : Reduced (reduce w) := by
  induction w with
  | nil => exact reduced_nil
  | cons t w ih => exact push_reduced t ih

theorem push_push (t : Fin 5) {w : List (Fin 5)} (hw : Reduced w) : push t (push t w) = w := by
  cases w with
  | nil => simp [push]
  | cons s w =>
    by_cases h : t = s
    · subst h
      simp only [push, ite_true]
      cases w with
      | nil => simp
      | cons r w =>
        have hr : t ≠ r := ((reduced_cons_cons t r w).mp hw).1
        simp [push, hr]
    · simp [push, h]

theorem reduce_of_reduced {w : List (Fin 5)} (hw : Reduced w) : reduce w = w := by
  induction w with
  | nil => rfl
  | cons t w ih =>
    simp only [reduce, ih (reduced_of_cons hw)]
    cases w with
    | nil => rfl
    | cons s w =>
      have h : t ≠ s := ((reduced_cons_cons t s w).mp hw).1
      simp [push, h]

theorem reduce_append (u v : List (Fin 5)) : reduce (u ++ v) = u.foldr push (reduce v) := by
  induction u with
  | nil => rfl
  | cons t u ih => simp [reduce, ih]

/-- Removing a pair `tt` anywhere does not change the reduced word. -/
theorem reduce_cancel (u v : List (Fin 5)) (t : Fin 5) :
    reduce (u ++ t :: t :: v) = reduce (u ++ v) := by
  rw [reduce_append, reduce_append]
  congr 1
  simp only [reduce]
  exact push_push t (reduce_reduced v)

/-- One cancellation: a pair `tt` removed from a word. -/
inductive Cancel : List (Fin 5) → List (Fin 5) → Prop
  | intro (u v : List (Fin 5)) (t : Fin 5) : Cancel (u ++ t :: t :: v) (u ++ v)

theorem reduce_eq_of_cancel {w w' : List (Fin 5)} (h : Relation.ReflTransGen Cancel w w') :
    reduce w = reduce w' := by
  induction h with
  | refl => rfl
  | tail _ hc ih =>
    rw [ih]
    cases hc with
    | intro u v t => exact reduce_cancel u v t

theorem cancel_cons {w w' : List (Fin 5)} (t : Fin 5) (h : Cancel w w') :
    Cancel (t :: w) (t :: w') := by
  cases h with
  | intro u v s => exact Cancel.intro (t :: u) v s

theorem cancels_cons {w w' : List (Fin 5)} (t : Fin 5) (h : Relation.ReflTransGen Cancel w w') :
    Relation.ReflTransGen Cancel (t :: w) (t :: w') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hc ih => exact ih.tail (cancel_cons t hc)

/-- Every word reduces to its reduced word by removing pairs `tt`. -/
theorem cancels_to_reduce (w : List (Fin 5)) : Relation.ReflTransGen Cancel w (reduce w) := by
  induction w with
  | nil => exact Relation.ReflTransGen.refl
  | cons t w ih =>
    refine (cancels_cons t ih).trans ?_
    simp only [reduce]
    cases hr : reduce w with
    | nil => exact Relation.ReflTransGen.refl
    | cons s w' =>
      simp only [push]
      split_ifs with h
      · subst h
        exact Relation.ReflTransGen.single (by simpa using Cancel.intro [] w' t)
      · exact Relation.ReflTransGen.refl

/-- **Proposition 24:** every word reduces, by removing pairs `tt`, to exactly one reduced word. -/
theorem unique_reduced {w w' : List (Fin 5)} (h : Relation.ReflTransGen Cancel w w')
    (hw' : Reduced w') : w' = reduce w := by
  rw [reduce_eq_of_cancel h, reduce_of_reduced hw']

/-! ## The two-spinor state of the line to its past (Proposition 25) -/

/-- The two-spinor state of the line now to its first moment, as one of the sixteen. -/
def relOfWord (w : List (Fin 5)) : Fin 16 := w.foldr transition 0

/-- The sign with which the walk reaches that two-spinor state: `γ_w B_0 = coef w • B_{relOfWord w}`. -/
def coef : List (Fin 5) → ℤ
  | [] => 1
  | t :: w => transitionSign t (relOfWord w) * coef w

theorem relOfWord_cons (t : Fin 5) (w : List (Fin 5)) :
    relOfWord (t :: w) = transition t (relOfWord w) := rfl

theorem γword_eq (w : List (Fin 5)) :
    (w.map γ).prod = (coef w : ℂ) • relOp (relOfWord w) := by
  induction w with
  | nil => simp [coef, relOfWord, relOp]
  | cons t w ih =>
    rw [List.map_cons, List.prod_cons, ih, Matrix.mul_smul, γ_mul_relOp, smul_smul, coef,
      relOfWord_cons]
    push_cast
    ring_nf

/-- **Proposition 25:** the two-spinor state of a moment to an earlier one is `± e_S` with `S` given by the
steps between them: `(γ_w ⊗ 1) Ω = coef w • e_{relOfWord w}`. -/
theorem history_rel (w : List (Fin 5)) :
    ((w.map γ).prod ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω = (coef w : ℂ) • rel (relOfWord w) := by
  rw [γword_eq, Matrix.smul_kronecker, Matrix.smul_mulVec, rel]

theorem coef_sq (w : List (Fin 5)) : coef w * coef w = 1 := by
  induction w with
  | nil => rfl
  | cons t w ih =>
    have h : transitionSign t (relOfWord w) * transitionSign t (relOfWord w) = 1 := by
      revert t
      generalize relOfWord w = k
      revert k
      decide
    calc coef (t :: w) * coef (t :: w)
        = (transitionSign t (relOfWord w) * transitionSign t (relOfWord w)) * (coef w * coef w) := by
          simp only [coef]; ring
      _ = 1 := by rw [h, ih, one_mul]

/-- The disagreement set reached: `T_{t_k} △ ⋯ △ T_{t_1}`. -/
theorem disagreeSet_relOfWord (w : List (Fin 5)) :
    disagreeSet (relOfWord w) = w.foldr (fun t S => symmDiff S (Finset.univ.erase t)) ∅ := by
  induction w with
  | nil => rfl
  | cons t w ih => rw [relOfWord_cons, disagreeSet_transition, ih, List.foldr_cons]

theorem disagreeSet_injective : Function.Injective disagreeSet := by
  decide

/-- The two-spinor states of moments compose: the steps of `u` after those of `v` reach
`relOfWord u` moved from `relOfWord v`. -/
theorem relOfWord_append (u v : List (Fin 5)) :
    relOfWord (u ++ v) = u.foldr transition (relOfWord v) := by
  rw [relOfWord, List.foldr_append]
  rfl

/-- **The vertices of a line:** every one of the sixteen two-spinor states is reached from the singlet by at
most two steps. -/
theorem relOfWord_surjective :
    ∀ k : Fin 16, ∃ w : List (Fin 5), w.length ≤ 2 ∧ relOfWord w = k := by
  intro k
  have : ∀ k : Fin 16, ∃ a b : Fin 5,
      relOfWord [] = k ∨ relOfWord [a] = k ∨ relOfWord [a, b] = k := by decide
  obtain ⟨a, b, h | h | h⟩ := this k
  · exact ⟨[], by simp, h⟩
  · exact ⟨[a], by simp, h⟩
  · exact ⟨[a, b], by simp, h⟩

/-- **Two moments are at one vertex exactly when the two-spinor state between them is the singlet:**
`relOfWord w = 0 ⟺ (γ_w ⊗ 1) Ω ∈ ℂ Ω`. -/
theorem at_place_iff (w : List (Fin 5)) :
    relOfWord w = 0 ↔ ∃ c : ℂ, ((w.map γ).prod ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ Ω = c • Ω := by
  rw [history_rel]
  constructor
  · intro h
    exact ⟨coef w, by rw [h, rel_zero]⟩
  · rintro ⟨c, hc⟩
    by_contra hk
    have h1 := congrArg (fun v => star (rel (relOfWord w)) ⬝ᵥ v) hc
    simp only [dotProduct_smul, rel_inner, ite_true, smul_eq_mul, mul_one] at h1
    rw [← rel_zero, rel_inner, if_neg hk, mul_zero, Int.cast_eq_zero] at h1
    have hc2 := coef_sq w
    rw [h1] at hc2
    simp at hc2

end Comparison

end
