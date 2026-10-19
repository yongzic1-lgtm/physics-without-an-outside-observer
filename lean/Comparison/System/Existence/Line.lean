import Comparison.System.Existence.Defs
import Comparison.Elements.Overlap
import Comparison.Colour.Arcs

/-!
# The proof system, the existence layer: a world line (Propositions 24 to 28)

Book VI, first half: walks are reduced words
(Prop. 24), the vertices of a line (Prop. 25), the eighty states and the step `B` (Prop. 26), what a line holds
(Prop. 27), the coin (Prop. 28). Each `prop_N` is the whole statement, with its quantifiers.
-/

namespace Comparison.System.Existence

open Matrix Complex Kronecker

/-! ## Proposition 24 -/

theorem ell_eq_rel (t : Fin 5) : ell t = rel (lineIdx t) := by
  fin_cases t <;> rfl

/-- Two vector states are equal exactly when their lines are. -/
theorem ell_eq_iff (s t : Fin 5) : ell s = ell t ↔ s = t := by
  constructor
  · intro h
    rw [ell_eq_rel, ell_eq_rel] at h
    have key : (if lineIdx s = lineIdx t then (1 : ℂ) else 0) = 1 := by
      rw [← rel_inner, ← h, rel_inner, if_pos rfl]
    have hk : lineIdx s = lineIdx t := by
      by_contra hne
      rw [if_neg hne] at key
      exact zero_ne_one key
    exact (show Function.Injective lineIdx by decide) hk
  · rintro rfl
    rfl

/-- **Proposition 24 (a walk is a reduced word).** `γ_sγ_t` is a number exactly when `s = t`; the step `s`
changes the two-spinor state to its own previous moment, `ℓ_t`, exactly when `s ≠ t`, so the words in which every step changes
that two-spinor state (P5 (b)) are the reduced words, the walks; every word reduces to exactly one reduced word by
removing pairs `tt`; there are `5·4ⁿ⁻¹` walks of length `n ≥ 1` (here `n + 1`, `5·4ⁿ`).

Recognition: none (each walk has four continuations, Prop. 26). Uses Props. 4, 10. Every candidate system:
`System.uniqueness`. -/
theorem prop_24 :
    (∀ s t : Fin 5, (∃ c : ℂ, γ s * γ t = c • (1 : Matrix Four Four ℂ)) ↔ s = t) ∧
    (∀ s t : Fin 5, ell s = ell t ↔ s = t) ∧
    (∀ w : List (Fin 5), w.IsChain (fun s t => ell s ≠ ell t) ↔ IsHistory w) ∧
    (∀ w : List (Fin 5), ∃! w' : List (Fin 5), Relation.ReflTransGen Cancel w w' ∧ IsHistory w') ∧
    (∀ n : ℕ, ((words (n + 1)).filter IsHistory).card = 5 * 4 ^ n) := by
  refine ⟨γ_mul_γ_scalar_iff, ell_eq_iff, fun w => ?_, fun w => ?_, card_reduced⟩
  · have hrel : (fun s t : Fin 5 => ell s ≠ ell t) = fun s t => s ≠ t := by
      funext s t
      rw [ne_eq, ell_eq_iff]
    rw [hrel]
    rfl
  · refine ⟨reduce w, ⟨cancels_to_reduce w, reduce_reduced w⟩, fun w' hw' => ?_⟩
    exact unique_reduced hw'.1 hw'.2

/-! ## Proposition 25 -/

theorem Sw_eq (w : List (Fin 5)) : Sw w = w.foldr (fun t S => symmDiff S (Finset.univ.erase t)) ∅ := rfl

theorem Sw_append (u v : List (Fin 5)) : Sw (u ++ v) = symmDiff (Sw u) (Sw v) := by
  induction u with
  | nil =>
    change Sw v = symmDiff ∅ (Sw v)
    rw [← Finset.bot_eq_empty, bot_symmDiff]
  | cons t u ih =>
    change symmDiff (Sw (u ++ v)) (T t) = symmDiff (symmDiff (Sw u) (T t)) (Sw v)
    rw [ih, symmDiff_assoc, symmDiff_comm (Sw v) (T t), ← symmDiff_assoc]

theorem relLine_eq (w : List (Fin 5)) : relLine w = (coef w : ℂ) • rel (relOfWord w) := history_rel w

theorem coef_values (w : List (Fin 5)) : coef w = 1 ∨ coef w = -1 := by
  have h := coef_sq w
  have : (coef w - 1) * (coef w + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h1 | h1
  · left; linarith
  · right; linarith

theorem disagreeSet_eq_empty_iff (k : Fin 16) : disagreeSet k = ∅ ↔ k = 0 := by
  revert k; decide

theorem even_disagreeSet (k : Fin 16) : Even (disagreeSet k).card := by
  revert k; decide

theorem exists_disagreeSet (S : Finset (Fin 5)) (hS : Even S.card) : ∃ k : Fin 16, disagreeSet k = S := by
  revert S; decide

/-- The adjacency on a character: `A χ_l = (5 − 2|T_l|) χ_l`, `χ_l(k) = (−1)^{|T_l ∩ T_k|}`. -/
theorem adjacency_character (l : Fin 16) :
    (A ℤ) *ᵥ (fun k => (-1 : ℤ) ^ (disagreeSet l ∩ disagreeSet k).card) =
      (5 - 2 * ((disagreeSet l).card : ℤ)) • fun k => (-1 : ℤ) ^ (disagreeSet l ∩ disagreeSet k).card := by
  have hc : ∀ k, charTable k l = (-1 : ℤ) ^ (disagreeSet l ∩ disagreeSet k).card := by
    intro k
    rw [charTable_eq, Matrix.of_apply, Finset.inter_comm]
  funext x
  have hx := congrFun (congrFun adjacency_mul_charTable x) l
  rw [Matrix.mul_apply, Matrix.mul_diagonal] at hx
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, ← adjacencyZ_eq, ← hc]
  rw [hx, charValue]
  ring

/-- **Proposition 25 (the vertices of a line).** The two-spinor state between two moments of a line is `r = ±e_S`, with
`S = T_{t_k} △ ⋯ △ T_{t_{j+1}}` the parities of the steps between them; the two moments are at one vertex exactly
when `S = ∅`; the sets compose, `S(j,k) △ S(k,l) = S(j,l)`; they are exactly the sixteen even sets of lines, so
fixing a moment labels the vertices by the sixteen sets, and another moment adds one set to every label; a step along
`s` takes `x` to `x ⊕ g_s`, `g_s = T_s`; the five steps lead from each vertex to five vertices, as the Clebsch graph
(five neighbours, none in common for two neighbours, two otherwise); the adjacency `A` has the eigenvalue
`5 − 2|U|` on the character `χ_U(x) = (−1)^{|U ∩ x|}`.

Recognition: the vertices are positions relative to one another only; there is no origin. Uses Props. 10, 14. -/
theorem prop_25 :
    (∀ w : List (Fin 5), relLine w = (coef w : ℂ) • rel (relOfWord w) ∧ (coef w = 1 ∨ coef w = -1) ∧
      disagreeSet (relOfWord w) = Sw w) ∧
    (∀ w : List (Fin 5), AtOnePlace (relLine w) ↔ Sw w = ∅) ∧
    (∀ u v : List (Fin 5), Sw (u ++ v) = symmDiff (Sw u) (Sw v)) ∧
    (∀ S : Finset (Fin 5), (∃ w : List (Fin 5), Sw w = S) ↔ Even S.card) ∧
    (∀ (s : Fin 5) (k : Fin 16), disagreeSet (transition s k) = symmDiff (disagreeSet k) (T s)) ∧
    (∀ k : Fin 16, (Finset.univ.filter (Adjacent k)).card = 5) ∧
    (∀ k l : Fin 16, k ≠ l → (Finset.univ.filter fun m => Adjacent k m ∧ Adjacent l m).card =
      if Adjacent k l then 0 else 2) ∧
    (∀ l : Fin 16, (A ℤ) *ᵥ (fun k => (-1 : ℤ) ^ (disagreeSet l ∩ disagreeSet k).card) =
      (5 - 2 * ((disagreeSet l).card : ℤ)) • fun k => (-1 : ℤ) ^ (disagreeSet l ∩ disagreeSet k).card) := by
  refine ⟨fun w => ⟨relLine_eq w, coef_values w, disagreeSet_relOfWord w⟩, fun w => ?_, Sw_append,
    fun S => ?_, disagreeSet_transition, card_neighbours, common_neighbours, adjacency_character⟩
  · rw [AtOnePlace, relLine, disagreement_eq_zero_iff, ← at_place_iff, ← disagreeSet_eq_empty_iff,
      disagreeSet_relOfWord]
    rfl
  · have e : ∀ w, Sw w = disagreeSet (relOfWord w) := fun w => (disagreeSet_relOfWord w).symm
    constructor
    · rintro ⟨w, rfl⟩
      rw [e]
      exact even_disagreeSet _
    · intro hS
      obtain ⟨k, hk⟩ := exists_disagreeSet S hS
      obtain ⟨w, -, hw⟩ := relOfWord_surjective k
      exact ⟨w, by rw [e, hw, hk]⟩

/-! ## Proposition 26 -/

/-- **Proposition 26 (eighty states and four continuations).** The state of a line is its two-spinor state and its last-step direction,
`(x, t)`: eighty states; the step is `B(x′, s; x, t) = [s ≠ t][x′ = x ⊕ g_s]` and the undo
`R(x, t) = (x ⊕ g_t, t)`, `R² = 1`; every state has four continuations and four predecessors, `320` arcs; `B + R`
takes each state to its five neighbours, `(B + R)(x′, s; x, t) = [x′ = x ⊕ g_s]`.

Recognition: the two-spinor states and their steps are the cells of `ℝP⁴` (Prop. 38, SI Prop. 116). Uses Props. 24, 25. -/
theorem prop_26 :
    Fintype.card State = 80 ∧
    (∀ s' s : State, B ℚ s' s = if s'.2 ≠ s.2 ∧ s'.1 = transition s'.2 s.1 then 1 else 0) ∧
    (∀ s : State, undoState s = (transition s.2 s.1, s.2)) ∧
    (∀ s' s : State, undoR s' s = if s' = undoState s then 1 else 0) ∧
    undoR * undoR = 1 ∧
    (∀ s : State, (Finset.univ.filter (Continues s)).card = 4) ∧
    (∀ s' : State, (Finset.univ.filter fun s => Continues s s').card = 4) ∧
    (∑ s' : State, ∑ s : State, B ℚ s' s) = 320 ∧
    (∀ s' s : State, (B ℚ + undoR) s' s = if s'.1 = transition s'.2 s.1 then 1 else 0) ∧
    (∀ s : State, (Finset.univ.filter fun s' : State => s'.1 = transition s'.2 s.1).card = 5) := by
  refine ⟨card_state, fun s' s => rfl, fun s => rfl, fun s' s => rfl, undoR_mul_self, card_continuations,
    card_predecessors, ?_, ?_, ?_⟩
  · have hcomm : ∑ s' : State, ∑ s : State, B ℚ s' s = ∑ s : State, ∑ s' : State, B ℚ s' s :=
      Finset.sum_comm
    rw [hcomm]
    have h : ∀ s : State, ∑ s' : State, B ℚ s' s = 4 := by
      intro s
      have hc := card_continuations s
      rw [Finset.card_filter] at hc
      simp only [B_apply]
      exact_mod_cast hc
    simp only [h, Finset.sum_const, Finset.card_univ, card_state, nsmul_eq_mul]
    norm_num
  · intro s' s
    simp only [Matrix.add_apply, B_apply, undoR, undoState, Matrix.of_apply, Continues]
    obtain ⟨x', u'⟩ := s'
    obtain ⟨x, u⟩ := s
    by_cases hu : u' = u
    · subst hu
      by_cases hx : x' = transition u' x <;> simp [hx]
    · have hne : (x', u') ≠ (transition u x, u) := fun h => hu (Prod.ext_iff.mp h).2
      simp [hu, hne]
  · intro s
    revert s
    decide +kernel

/-! ## Proposition 27 -/

/-- The division of the six reversed by `γ_h ⊗ γ_h` and by the plane, as sets of directions. -/
theorem T_succ (h : Fin 5) : (T h).map (Fin.succEmb 5) = Finset.univ.erase 0 \ {h.succ} := by
  revert h; decide

/-- **Proposition 27 (what a line holds).** With `h` the last-step direction and `k′` the step before it (`h ≠ k′`):
`r_{k,k} = Ω`, `r_{k,k−1} = ℓ_h = e_{T_h}`, `r_{k,k−2} = ±e_{h k′}`; on P1's real six
`γ_h ⊗ γ_h = θ_{T_h} = −θ_{\{h,n\}}` and `γ_hγ_{k′} ⊗ γ_hγ_{k′} = θ_{\{h,k′\}}`; the divided sets of the three two-spinor states
are `{}`, `{h, n}`, `F = {h, k′}`, their counterparts `{n}`, `{h}`, `C` (the three lines outside `F`), and these are the six
divisions of Prop. 22 with the singlet fixed, each once: they divide `0, 4, 2, 5, 1, 3` lines.

Recognition: the line holds its own time `{h, n}`, its own direction `{h}`, its clock plane `F` and the three lines
outside it. Uses Props. 10, 22, 24, Definitions 18, 29. -/
theorem prop_27 (h k' : Fin 5) (hk : h ≠ k') :
    relLine [] = Ω ∧
    relLine [h] = ell h ∧ ell h = rel (lineIdx h) ∧ disagreeSet (lineIdx h) = T h ∧
    (relLine [h, k'] = (coef [h, k'] : ℂ) • rel (relOfWord [h, k']) ∧ (coef [h, k'] = 1 ∨ coef [h, k'] = -1) ∧
      disagreeSet (relOfWord [h, k']) = {h, k'}) ∧
    (∀ c : Fin 6, γ h * sixP1 c * (γ h)ᵀ = thetaAt ((T h).map (Fin.succEmb 5)) c • sixP1 c ∧
      thetaAt ((T h).map (Fin.succEmb 5)) c = -thetaAt {0, h.succ} c) ∧
    (∀ c : Fin 6, (γ h * γ k') * sixP1 c * (γ h * γ k')ᵀ = thetaAt {h.succ, k'.succ} c • sixP1 c) ∧
    dividedSet 0 = ∅ ∧ dividedSet (lineIdx h) = {0, h.succ} ∧ dividedSet (relOfWord [h, k']) = {h.succ, k'.succ} ∧
    twin ∅ = {0} ∧ twin {0, h.succ} = {h.succ} ∧
      twin {h.succ, k'.succ} = (({h, k'} : Finset (Fin 5))ᶜ).map (Fin.succEmb 5) ∧
    [linesDivided ∅, linesDivided {0, h.succ}, linesDivided {h.succ, k'.succ}, linesDivided {0},
      linesDivided {h.succ}, linesDivided ((({h, k'} : Finset (Fin 5))ᶜ).map (Fin.succEmb 5))] =
      [0, 4, 2, 5, 1, 3] := by
  have hmem : ∀ h : Fin 5, ∀ c : Fin 6, (c ∈ (T h).map (Fin.succEmb 5) ↔ ¬(c = 0 ∨ c = h.succ)) ∧
      (c ∈ ({0, h.succ} : Finset (Fin 6)) ↔ (c = 0 ∨ c = h.succ)) := by
    decide
  have hsix : ∀ c : Fin 6,
      (if c = 0 ∨ c = h.succ then (1 : ℂ) else -1) = thetaAt ((T h).map (Fin.succEmb 5)) c ∧
      thetaAt ((T h).map (Fin.succEmb 5)) c = -thetaAt {0, h.succ} c := by
    intro c
    simp only [thetaAt, (hmem h c).1, (hmem h c).2]
    by_cases hc : c = 0 ∨ c = h.succ
    · simp [hc]
    · simp [hc]
  have hface : ∀ c : Fin 6, (if c = h.succ ∨ c = k'.succ then (-1 : ℂ) else 1) =
      thetaAt {h.succ, k'.succ} c := by
    intro c
    simp only [thetaAt, Finset.mem_insert, Finset.mem_singleton]
  have hrest : ∀ h k' : Fin 5, h ≠ k' →
      disagreeSet (relOfWord [h, k']) = {h, k'} ∧ dividedSet (relOfWord [h, k']) = {h.succ, k'.succ} ∧
      twin {h.succ, k'.succ} = (({h, k'} : Finset (Fin 5))ᶜ).map (Fin.succEmb 5) ∧
      dividedSet (lineIdx h) = {0, h.succ} ∧ twin {0, h.succ} = {h.succ} ∧ disagreeSet (lineIdx h) = T h ∧
      linesDivided ((({h, k'} : Finset (Fin 5))ᶜ).map (Fin.succEmb 5)) =
        linesDivided {0, h.succ, k'.succ} := by
    decide +kernel
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := hrest h k' hk
  refine ⟨?_, ?_, ell_eq_rel h, r6, ⟨history_rel _, coef_values _, r1⟩, fun c => ?_, fun c => ?_, by decide,
    r4, r2, by decide, r5, r3, ?_⟩
  · simp [relLine, Matrix.one_kronecker_one]
  · simp [relLine, ell]
  · rw [line_on_six h c, (hsix c).1]
    exact ⟨rfl, (hsix c).2⟩
  · rw [plane_on_six h k' hk c, hface c]
  · rw [r7]
    exact one_of_each h k' hk

/-! ## Proposition 28 -/

/-- The coin over the real numbers, `σ₅ = (2/5)𝟏𝟏ᵀ − I`. -/
noncomputable def sigma5 : Matrix (Fin 5) (Fin 5) ℝ := (2 / 5 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ)) - 1

theorem sigma5_apply (i j : Fin 5) : sigma5 i j = if i = j then -3 / 5 else 2 / 5 := by
  simp only [sigma5, Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> norm_num

theorem sigma5_eq_coin (i j : Fin 5) : sigma5 i j = (coin i j : ℝ) := by
  rw [sigma5_apply, coin_apply]
  split_ifs <;> norm_num

/-- **The involutions made of `1` and `𝟏𝟏ᵀ` over the real numbers.** -/
theorem involutions_real (a b : ℝ) :
    (a • (1 : Matrix (Fin 5) (Fin 5) ℝ) + b • Matrix.of (fun _ _ => (1 : ℝ)))ᵀ *
        (a • 1 + b • Matrix.of (fun _ _ => (1 : ℝ))) = 1 ↔
      (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0) ∨ (a = -1 ∧ b = 2 / 5) ∨ (a = 1 ∧ b = -2 / 5) := by
  have ht : (a • (1 : Matrix (Fin 5) (Fin 5) ℝ) + b • Matrix.of (fun _ _ => (1 : ℝ)))ᵀ =
      a • 1 + b • Matrix.of (fun _ _ => (1 : ℝ)) := by
    rw [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_smul, Matrix.transpose_one]
    congr 2
  rw [ht]
  have key : (a • (1 : Matrix (Fin 5) (Fin 5) ℝ) + b • Matrix.of (fun _ _ => (1 : ℝ))) *
      (a • 1 + b • Matrix.of (fun _ _ => (1 : ℝ))) =
      (a ^ 2) • 1 + (2 * a * b + 5 * b ^ 2) • Matrix.of (fun _ _ => (1 : ℝ)) := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply,
      smul_eq_mul, Fin.sum_univ_five]
    fin_cases i <;> fin_cases j <;> simp <;> ring
  rw [key]
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.of_apply, smul_eq_mul] at h00 h01
    norm_num at h00 h01
    have hα : a ^ 2 = 1 := by linarith
    have hβ : b * (2 * a + 5 * b) = 0 := by linarith
    have hα' : (a - 1) * (a + 1) = 0 := by linear_combination hα
    rcases mul_eq_zero.mp hβ with hb | hb <;> rcases mul_eq_zero.mp hα' with ha | ha
    · left; exact ⟨by linarith, hb⟩
    · right; left; exact ⟨by linarith, hb⟩
    · right; right; right; exact ⟨by linarith, by linarith⟩
    · right; right; left; exact ⟨by linarith, by linarith⟩
  · intro h
    have h1 : a ^ 2 = 1 := by
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
    have h2 : 2 * a * b + 5 * b ^ 2 = 0 := by
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num
    rw [h1, h2, one_smul, zero_smul, add_zero]

theorem sigma5_eq_comb : sigma5 = (-1 : ℝ) • (1 : Matrix (Fin 5) (Fin 5) ℝ) +
    (2 / 5 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ)) := by
  rw [sigma5]
  module

/-- **Proposition 28 (the coin).** A real `X = aI + b𝟏𝟏ᵀ` with `XᵀX = I` and `X ≠ ±I` is `±σ₅`,
`σ₅ = (2/5)𝟏𝟏ᵀ − I`; a real matrix that no relabelling of the five directions changes is of that form, so `±σ₅` are the
only orthogonal involutions besides `±1` that no relabelling changes; `(σ₅)_{tt} = −3/5`, `(σ₅)_{st} = 2/5`,
`σ₅² = I`; the step from the last-step direction `t` is the line `γ(x_t)`, `x_t = (2/5)𝟏 − e_t` the column of `σ₅`, of length one,
`γ(x_t)² = 1`; on the eighty states `U = (2/5)B − (3/5)R` and `UᵀU = I`.

Recognition: the radar echo of one step, `(3/5)² + 4(2/5)² = 1 = v² + 1/γ²` with `v = 3/5`, `γ = 5/4`. Uses
Props. 4, 26, P1, P2 (a), P3 (b). -/
theorem prop_28 :
    (∀ a b : ℝ, (a • (1 : Matrix (Fin 5) (Fin 5) ℝ) + b • Matrix.of (fun _ _ => (1 : ℝ)))ᵀ *
        (a • 1 + b • Matrix.of (fun _ _ => (1 : ℝ))) = 1 →
      a • (1 : Matrix (Fin 5) (Fin 5) ℝ) + b • Matrix.of (fun _ _ => (1 : ℝ)) ≠ 1 →
      a • (1 : Matrix (Fin 5) (Fin 5) ℝ) + b • Matrix.of (fun _ _ => (1 : ℝ)) ≠ -1 →
      a • (1 : Matrix (Fin 5) (Fin 5) ℝ) + b • Matrix.of (fun _ _ => (1 : ℝ)) = sigma5 ∨
        a • (1 : Matrix (Fin 5) (Fin 5) ℝ) + b • Matrix.of (fun _ _ => (1 : ℝ)) = -sigma5) ∧
    (∀ X : Matrix (Fin 5) (Fin 5) ℝ, (∀ π : Equiv.Perm (Fin 5), X.submatrix π π = X) →
      ∃ a b : ℝ, X = a • (1 : Matrix (Fin 5) (Fin 5) ℝ) + b • Matrix.of (fun _ _ => (1 : ℝ))) ∧
    (∀ s t : Fin 5, sigma5 s t = if s = t then -3 / 5 else 2 / 5) ∧
    sigma5 * sigma5 = 1 ∧
    (∀ t : Fin 5, (∑ s, sigma5 s t ^ 2 = 1) ∧ (∑ s, ((sigma5 s t : ℝ) : ℂ) • γ s) = gamma (fun s => sigma5 s t) ∧
      gamma (fun s => sigma5 s t) * gamma (fun s => sigma5 s t) = 1) ∧
    stepU = (2 / 5 : ℚ) • B ℚ - (3 / 5 : ℚ) • undoR ∧ stepUᵀ * stepU = 1 := by
  have hcol : ∀ t : Fin 5, ∑ s, sigma5 s t ^ 2 = 1 := by
    intro t
    rw [Fin.sum_univ_five]
    fin_cases t <;> simp [sigma5_apply] <;> norm_num
  refine ⟨fun a b hX h1 h2 => ?_, fun X hX => commutant_perm X hX, sigma5_apply, ?_, fun t => ⟨hcol t, rfl, ?_⟩,
    stepU_eq, stepU_orthogonal⟩
  · rcases (involutions_real a b).mp hX with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd (by simp) h1
    · exact absurd (by simp) h2
    · left; rw [sigma5_eq_comb]
    · right; rw [sigma5_eq_comb]; module
  · ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_five]
    fin_cases i <;> fin_cases j <;> simp [sigma5_apply, Matrix.one_apply] <;> norm_num
  · show γv _ * γv _ = 1
    rw [γv_mul_self, hcol t]
    simp

end Comparison.System.Existence
