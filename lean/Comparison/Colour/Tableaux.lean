module

public import Mathlib

/-!
# Book XIII. The multiplicities of the singlets: the standard tableaux of shape `(k, k, k)`
(Proposition 74)

A standard tableau of shape
`(k, k, k)` is a lattice word: a word in the three letters `0, 1, 2` with each letter `k` times in
which every prefix holds at least as many `0`s as `1`s and at least as many `1`s as `2`s. Words are
written newest letter first.

* `ballotOk`: every prefix keeps `#0 ≥ #1 ≥ #2`; `latticeGen k n`: the words of length `n`
  built letter by letter, never more than `k` of a letter.
* `mem_latticeGen`: `w ∈ latticeGen k n ↔ |w| = n ∧ ballotOk w ∧ every letter at most k times`;
  `latticeGen_nodup`: each word once.
* `lattice_words`: the lattice words of shape `(k, k, k)` are a finite set of
  `(latticeGen k (3k)).length` words; `tableaux_counts`: **`1, 5, 42, 462`** for `k = 1, 2, 3, 4`,
  the numbers `2(3k)!/(k!(k+1)!(k+2)!)` of Prop. 74 (`hook_values`, Singlets.lean).

By Schur–Weyl duality these count the colour singlets of `(ℂ³)^{⊗3k}`; that duality is not in
Mathlib and is not proved here.
-/

@[expose] public section

namespace Comparison

/-- **The ballot condition**, newest letter first: every prefix keeps `#0 ≥ #1 ≥ #2`. -/
def ballotOk : List (Fin 3) → Bool
  | [] => true
  | c :: w => ballotOk w &&
      (decide (c = 0) || (decide (c = 1) && decide (w.count 1 < w.count 0)) ||
        (decide (c = 2) && decide (w.count 2 < w.count 1)))

/-- The words of length `n`, built letter by letter, keeping the ballot condition and at most `k`
of each letter. -/
def latticeGen (k : ℕ) : ℕ → List (List (Fin 3))
  | 0 => [[]]
  | n + 1 => (latticeGen k n).flatMap fun w =>
      ([0, 1, 2] : List (Fin 3)).filterMap fun c =>
        if ballotOk (c :: w) && decide (w.count c < k) then some (c :: w) else none

theorem mem_three (c : Fin 3) : c ∈ ([0, 1, 2] : List (Fin 3)) := by
  fin_cases c <;> simp

theorem count_cons_self (c : Fin 3) (w : List (Fin 3)) : (c :: w).count c = w.count c + 1 := by
  simp

theorem count_cons_ne (c c' : Fin 3) (w : List (Fin 3)) (h : c ≠ c') :
    (c :: w).count c' = w.count c' := by
  simp [h]

/-- **The generator holds exactly the ballot words with at most `k` of each letter.** -/
theorem mem_latticeGen (k : ℕ) : ∀ (n : ℕ) (w : List (Fin 3)),
    w ∈ latticeGen k n ↔ w.length = n ∧ ballotOk w = true ∧ ∀ c, w.count c ≤ k := by
  intro n
  induction n with
  | zero =>
    intro w
    simp only [latticeGen, List.mem_singleton, List.length_eq_zero_iff]
    constructor
    · rintro rfl
      exact ⟨rfl, rfl, fun c => by simp⟩
    · exact fun h => h.1
  | succ n ih =>
    intro w
    simp only [latticeGen, List.mem_flatMap, List.mem_filterMap]
    constructor
    · rintro ⟨w', hw', c, -, hc⟩
      split_ifs at hc with hcond
      · cases hc
        obtain ⟨hl, hb, hcount⟩ := (ih w').mp hw'
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        refine ⟨by simp [hl], hcond.1, fun c' => ?_⟩
        by_cases e : c = c'
        · subst e
          rw [count_cons_self]
          omega
        · rw [count_cons_ne c c' w' e]
          exact hcount c'
    · rintro ⟨hl, hb, hcount⟩
      cases w with
      | nil => simp at hl
      | cons c w' =>
        have hb' : ballotOk w' = true := by
          simp only [ballotOk, Bool.and_eq_true] at hb
          exact hb.1
        have hl' : w'.length = n := by simpa using hl
        have hc' : ∀ c', w'.count c' ≤ k := fun c' =>
          le_trans List.count_le_count_cons (hcount c')
        have hlt : w'.count c < k := by
          have := hcount c
          rw [count_cons_self] at this
          omega
        refine ⟨w', (ih w').mpr ⟨hl', hb', hc'⟩, c, mem_three c, ?_⟩
        have hcond : (ballotOk (c :: w') && decide (w'.count c < k)) = true := by
          simp only [Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨hb, hlt⟩
        simp only [hcond, ↓reduceIte]

/-- **Each word once.** -/
theorem latticeGen_nodup (k : ℕ) : ∀ n, (latticeGen k n).Nodup := by
  intro n
  induction n with
  | zero => simp [latticeGen]
  | succ n ih =>
    simp only [latticeGen]
    rw [List.nodup_flatMap]
    constructor
    · intro w _
      apply List.Nodup.filterMap _ (by decide : ([0, 1, 2] : List (Fin 3)).Nodup)
      intro a a' b hb hb'
      simp only [Option.mem_def] at hb hb'
      split_ifs at hb hb'
      exact (List.cons.inj (Option.some.inj (hb.trans hb'.symm))).1
    · refine List.Pairwise.imp ?_ ih
      intro a b hab
      simp only [Function.onFun]
      rw [List.disjoint_left]
      intro x hxa hxb
      simp only [List.mem_filterMap] at hxa hxb
      obtain ⟨c, -, hc⟩ := hxa
      obtain ⟨c', -, hc'⟩ := hxb
      split_ifs at hc hc'
      exact hab (List.cons.inj (Option.some.inj (hc.trans hc'.symm))).2

/-- **The lattice words of shape `(k, k, k)`:** a finite set of `(latticeGen k (3k)).length`
words. -/
theorem lattice_words (k : ℕ) :
    ∃ T : Finset (List (Fin 3)), (∀ w, w ∈ T ↔
      w.length = 3 * k ∧ ballotOk w = true ∧ ∀ c, w.count c = k) ∧
      T.card = (latticeGen k (3 * k)).length := by
  refine ⟨(latticeGen k (3 * k)).toFinset, fun w => ?_, ?_⟩
  · rw [List.mem_toFinset, mem_latticeGen]
    constructor
    · rintro ⟨hl, hb, hc⟩
      refine ⟨hl, hb, fun c => ?_⟩
      have hsum : w.count 0 + w.count 1 + w.count 2 = w.length := by
        have e : ∀ v : List (Fin 3), v.count 0 + v.count 1 + v.count 2 = v.length := by
          intro v
          induction v with
          | nil => simp
          | cons a v ihv =>
            fin_cases a <;> simp [] <;> omega
        exact e w
      have h0 := hc 0
      have h1 := hc 1
      have h2 := hc 2
      fin_cases c <;> simp <;> omega
    · rintro ⟨hl, hb, hc⟩
      exact ⟨hl, hb, fun c => (hc c).le⟩
  · exact List.toFinset_card_of_nodup (latticeGen_nodup k _)

/-- **The standard tableaux of shape `(k, k, k)`: `1, 5, 42, 462`** for `k = 1, 2, 3, 4`. -/
theorem tableaux_counts :
    (latticeGen 1 3).length = 1 ∧ (latticeGen 2 6).length = 5 ∧
      (latticeGen 3 9).length = 42 ∧ (latticeGen 4 12).length = 462 := by
  decide +kernel

end Comparison

end
