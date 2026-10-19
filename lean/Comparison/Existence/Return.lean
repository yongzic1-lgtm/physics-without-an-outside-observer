module

public import Comparison.Existence.Words

/-!
# Book X. The excursion is the law's return (Proposition 55, Appendix B.30)

**The lemma of five involutions (B.30).** For five elements `Γ_t` of any ring with `Γ_t² = 1`, let
`N_n = Σ Γ_{t_n} ⋯ Γ_{t_1}` over the reduced words of length `n` (`wordSum`). Then `N₀ = 1`,
`N₁ = A := Σ_t Γ_t`, `A N₁ = N₂ + 5 N₀` and `A N_{n} = N_{n+1} + 4 N_{n−1}` for `n ≥ 2`
(`wordSum_rec`); equivalently `((1 + 4u²) − uA) Σ_n N_n uⁿ = 1 − u²`, coefficient by coefficient
(`wordSum_gf`).

**The exact algebra of B.30.** With `a = 1 + 4u²`:
* `returns_plus`: `R₊ = 1 + (4/5)[(1 − u²)(1/16)(1/((1 − u)(1 − 4u)) + 10/(a − u) + 5/(a + 3u)) − 1]
  = (1 − 2u − 3u² − 12u³)/((1 − 4u)(a − u)(a + 3u))`, and `excursion_from_returns`:
  `1 − 1/R₊ = 16u⁴(1 + 4u)/(1 − 2u − 3u² − 12u³) = F(4u)`;
* `returns_minus`: `R₋ = 1 + (4/5)[(1 − u²) a/(a² − 5u²) − 1] = (1 + 3u²)/(1 + 3u² + 16u⁴)`, and
  `signed_excursion_from_returns`: `1 − 1/R₋ = −16u⁴/(1 + 3u²) = Φ(4u)`.
-/

@[expose] public section

namespace Comparison

section Involutions

variable {A : Type*} [Ring A] (Γ : Fin 5 → A)

/-- `N_n = Σ Γ_{t_n} ⋯ Γ_{t_1}` over the reduced words `[t_n, …, t_1]` of length `n`. -/
def wordSum (n : ℕ) : A := ∑ w ∈ words n, if Reduced w then (w.map Γ).prod else 0

theorem wordSum_zero : wordSum Γ 0 = 1 := by
  simp [wordSum, words, reduced_nil]

theorem wordSum_one : wordSum Γ 1 = ∑ t, Γ t := by
  rw [wordSum, sum_words_succ]
  simp [words, reduced_single]

/-- One more step on a reduced word: `A · Γ_w = Σ_{t ≠ head} Γ_{t :: w} + Γ_{tail w}`. -/
theorem step_word (hΓ : ∀ t, Γ t * Γ t = 1) (g : Fin 5) (w : List (Fin 5)) :
    (∑ t, Γ t) * (if Reduced (g :: w) then ((g :: w).map Γ).prod else 0) =
      (∑ t, if Reduced (t :: g :: w) then ((t :: g :: w).map Γ).prod else 0) +
        (if Reduced (g :: w) then (w.map Γ).prod else 0) := by
  simp only [reduced_cons_cons]
  by_cases hr : Reduced (g :: w)
  · simp only [hr, and_true, ↓reduceIte, List.map_cons, List.prod_cons, Finset.sum_mul]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ g), ← Finset.sum_erase_add _ _
      (Finset.mem_univ g)]
    simp only [ne_eq, not_true_eq_false, ↓reduceIte, add_zero]
    rw [← mul_assoc, hΓ, one_mul]
    congr 1
    refine Finset.sum_congr rfl fun t ht => ?_
    simp [Finset.ne_of_mem_erase ht, mul_assoc]
  · simp [hr]

/-- The sum over the first steps of a word: `Σ_t [t :: w reduced] = 5` for the empty word and
`4 [w reduced]` otherwise. -/
theorem count_first (w : List (Fin 5)) (x : A) :
    (∑ t : Fin 5, if Reduced (t :: w) then x else 0) =
      if w = [] then (5 : ℕ) • x else if Reduced w then (4 : ℕ) • x else 0 := by
  cases w with
  | nil => simp [reduced_single]
  | cons g w =>
    simp only [reduced_cons_cons, reduced_cons_cons, List.cons_ne_nil, ↓reduceIte]
    by_cases hr : Reduced (g :: w)
    · simp only [hr, and_true, ↓reduceIte]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const]
      congr 1
      rw [Finset.filter_ne' Finset.univ g, Finset.card_erase_of_mem (Finset.mem_univ g)]
      simp
    · simp [hr]

/-- **The lemma of five involutions:** `A N_{n+1} = N_{n+2} + c_n N_n` with `c₀ = 5`, `c_n = 4`. -/
theorem wordSum_rec (hΓ : ∀ t, Γ t * Γ t = 1) (n : ℕ) :
    (∑ t, Γ t) * wordSum Γ (n + 1) =
      wordSum Γ (n + 2) + (if n = 0 then (5 : ℕ) else 4) • wordSum Γ n := by
  -- the left side, word by word
  have hL : (∑ t, Γ t) * wordSum Γ (n + 1) =
      ∑ g, ∑ w ∈ words n, (∑ t, Γ t) *
        (if Reduced (g :: w) then ((g :: w).map Γ).prod else 0) := by
    rw [wordSum, sum_words_succ, Finset.mul_sum]
    simp only [Finset.mul_sum]
  rw [hL]
  simp only [step_word Γ hΓ, Finset.sum_add_distrib]
  congr 1
  · rw [wordSum, sum_words_succ]
    simp_rw [sum_words_succ n]
    conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
    rw [Finset.sum_comm]
  · rw [Finset.sum_comm, wordSum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [count_first]
    rw [mem_words] at hw
    by_cases hn : n = 0
    · subst hn
      have : w = [] := List.eq_nil_of_length_eq_zero hw
      subst this
      simp [reduced_nil]
    · have : w ≠ [] := fun h => hn (by rw [← hw, h, List.length_nil])
      simp only [this, ↓reduceIte, hn]
      split_ifs <;> simp

/-- **`((1 + 4u²) − uA) Σ N_n uⁿ = 1 − u²`, coefficient by coefficient:** `N₀ = 1`, `N₁ = A N₀`, and
`N_{n+2} + 4N_n − A N_{n+1} = −[n = 0]`. -/
theorem wordSum_gf (hΓ : ∀ t, Γ t * Γ t = 1) :
    wordSum Γ 0 = 1 ∧ wordSum Γ 1 = (∑ t, Γ t) * wordSum Γ 0 ∧
    ∀ n, wordSum Γ (n + 2) + (4 : ℕ) • wordSum Γ n - (∑ t, Γ t) * wordSum Γ (n + 1) =
      if n = 0 then -1 else 0 := by
  refine ⟨wordSum_zero Γ, by rw [wordSum_one, wordSum_zero, mul_one], fun n => ?_⟩
  rw [wordSum_rec Γ hΓ]
  by_cases hn : n = 0
  · subst hn
    simp only [↓reduceIte, wordSum_zero]
    rw [add_sub_add_left_eq_sub, nsmul_eq_mul, nsmul_eq_mul, mul_one, mul_one]
    norm_num
  · simp [hn]

end Involutions

/-! ## The exact algebra of B.30 -/

/-- **The returns of the unsigned walk:** with `a = 1 + 4u²`, the diagonal entry of the resolvent
over the characters gives `R₊ = (1 − 2u − 3u² − 12u³)/((1 − 4u)(a − u)(a + 3u))`. -/
theorem returns_plus (u : ℂ) (h1 : 1 - u ≠ 0) (h4 : 1 - 4 * u ≠ 0) (h2 : 1 + 4 * u ^ 2 - u ≠ 0)
    (h3 : 1 + 4 * u ^ 2 + 3 * u ≠ 0) :
    1 + 4 / 5 * ((1 - u ^ 2) * (1 / 16 * (1 / ((1 - u) * (1 - 4 * u)) +
      10 / (1 + 4 * u ^ 2 - u) + 5 / (1 + 4 * u ^ 2 + 3 * u))) - 1) =
      (1 - 2 * u - 3 * u ^ 2 - 12 * u ^ 3) /
        ((1 - 4 * u) * (1 + 4 * u ^ 2 - u) * (1 + 4 * u ^ 2 + 3 * u)) := by
  generalize hp : 1 - u = p at h1 ⊢
  generalize hq : 1 - 4 * u = q at h4 ⊢
  generalize hr : 1 + 4 * u ^ 2 - u = r at h2 ⊢
  generalize hs : 1 + 4 * u ^ 2 + 3 * u = s at h3 ⊢
  field_simp
  subst hp hq hr hs
  ring

/-- **The excursion from the returns:** `1 − 1/R₊ = 16u⁴(1 + 4u)/(1 − 2u − 3u² − 12u³)`, which is
`F(4u) = (4u)⁴(1 + 4u)/(16 − 8(4u) − 3(4u)² − 3(4u)³)`. -/
theorem excursion_from_returns (u : ℂ) (h0 : 1 - 2 * u - 3 * u ^ 2 - 12 * u ^ 3 ≠ 0)
    (h1 : (1 - 4 * u) * (1 + 4 * u ^ 2 - u) * (1 + 4 * u ^ 2 + 3 * u) ≠ 0) :
    1 - 1 / ((1 - 2 * u - 3 * u ^ 2 - 12 * u ^ 3) /
        ((1 - 4 * u) * (1 + 4 * u ^ 2 - u) * (1 + 4 * u ^ 2 + 3 * u))) =
      16 * u ^ 4 * (1 + 4 * u) / (1 - 2 * u - 3 * u ^ 2 - 12 * u ^ 3) ∧
    16 * u ^ 4 * (1 + 4 * u) / (1 - 2 * u - 3 * u ^ 2 - 12 * u ^ 3) =
      (4 * u) ^ 4 * (1 + 4 * u) / (16 - 8 * (4 * u) - 3 * (4 * u) ^ 2 - 3 * (4 * u) ^ 3) := by
  have h16 : (16 - 8 * (4 * u) - 3 * (4 * u) ^ 2 - 3 * (4 * u) ^ 3) =
      16 * (1 - 2 * u - 3 * u ^ 2 - 12 * u ^ 3) := by ring
  rw [h16]
  constructor
  · generalize hD : (1 - 4 * u) * (1 + 4 * u ^ 2 - u) * (1 + 4 * u ^ 2 + 3 * u) = D at h1 ⊢
    have hDN : D = 1 - 2 * u - 3 * u ^ 2 - 12 * u ^ 3 - 16 * u ^ 4 - 64 * u ^ 5 := by
      rw [← hD]
      ring
    generalize hN : 1 - 2 * u - 3 * u ^ 2 - 12 * u ^ 3 = N at h0 hDN ⊢
    field_simp
    rw [hDN]
    ring
  · generalize hN : 1 - 2 * u - 3 * u ^ 2 - 12 * u ^ 3 = N at h0 ⊢
    field_simp
    ring

/-- **The returns of the signed walk:** `R₋ = 1 + (4/5)[(1 − u²) a/(a² − 5u²) − 1]
= (1 + 3u²)/(1 + 3u² + 16u⁴)`, with `a = 1 + 4u²`. -/
theorem returns_minus (u : ℂ) (h : 1 + 3 * u ^ 2 + 16 * u ^ 4 ≠ 0) :
    1 + 4 / 5 * ((1 - u ^ 2) * ((1 + 4 * u ^ 2) / ((1 + 4 * u ^ 2) ^ 2 - 5 * u ^ 2)) - 1) =
      (1 + 3 * u ^ 2) / (1 + 3 * u ^ 2 + 16 * u ^ 4) := by
  have h' : (1 + 4 * u ^ 2) ^ 2 - 5 * u ^ 2 = 1 + 3 * u ^ 2 + 16 * u ^ 4 := by ring
  rw [h']
  generalize hD : 1 + 3 * u ^ 2 + 16 * u ^ 4 = D at h ⊢
  have hD' : D = 1 + 3 * u ^ 2 + 16 * u ^ 4 := hD.symm
  field_simp
  rw [hD']
  ring

/-- **The signed excursion from the returns:** `1 − 1/R₋ = −16u⁴/(1 + 3u²) = Φ(4u)`. -/
theorem signed_excursion_from_returns (u : ℂ) (h : 1 + 3 * u ^ 2 + 16 * u ^ 4 ≠ 0)
    (h' : 1 + 3 * u ^ 2 ≠ 0) :
    1 - 1 / ((1 + 3 * u ^ 2) / (1 + 3 * u ^ 2 + 16 * u ^ 4)) = -16 * u ^ 4 / (1 + 3 * u ^ 2) ∧
    -16 * u ^ 4 / (1 + 3 * u ^ 2) = -(4 * u) ^ 4 / (16 + 3 * (4 * u) ^ 2) := by
  have h16 : (16 + 3 * (4 * u) ^ 2) = 16 * (1 + 3 * u ^ 2) := by ring
  rw [h16]
  constructor
  · have hDE : 1 + 3 * u ^ 2 + 16 * u ^ 4 = (1 + 3 * u ^ 2) + 16 * u ^ 4 := by ring
    rw [hDE] at h ⊢
    generalize hE : 1 + 3 * u ^ 2 = E at h h' ⊢
    field_simp
    ring
  · generalize hE : 1 + 3 * u ^ 2 = E at h' ⊢
    field_simp
    ring

end Comparison

end
