import Comparison.Existence.Excursion
import Comparison.Elements.Overlap

/-!
# The vertical sign is the parallel rotation of the
# sphere of lines over a whole excursion (Proposition 89, its finite core)

The two directions are one operation over an excursion. A step along the line `t`
carries the kept point `n` of the sphere of lines `S⁴` along the great circle through `t` to
`flip_t n = 2n_t e_t − n`; on the side `Q(n)H` the transport `U = (1 + γ(m)γ(n))/√(2(1 + m·n))` of the
sides' connection is `sign(n_t) γ_t` (Proposition 89 (ii)). Around a closed walk the product of
these steps is the walk's Clifford sign `σ_w`, times `sign(n₁⋯n₅)` when the walk is odd
(Proposition 89 (iii)).

**The sign identity on walks** (oldest step first):
* `signProd n v = Π_k sign(n^{(k−1)}_{t_k})`, `n^{(k)} = flip_{t_k} n^{(k−1)}`;
* `signProd_formula`: `signProd n v = (−1)^{e(v)} Π_x sign(n_x)^{m_x}`, `m_x` the steps along `x`,
  `e(v)` the pairs of steps along different lines;
* `eC_quad`: `2e(v) + Σ_x m_x² = N²`;
* `odd_cC_iff_mem`: a line `x` is divided between a walk's two ends exactly when an odd number of
  its steps go along other lines; so a closed walk (`relOfWord w = 0`) has `N − m_x` even for every
  `x`, and then `eC_even`: `e(v)` is even;
* `signProd_closed`: **around a closed walk the signs multiply to `1` when it is even and to
  `Π_x sign(n_x)` when it is odd.**

**The transport and the holonomy:**
* `γ_conj_line`, `γv_flip`: `γ_t γ(n) γ_t = γ(flip_t n)`;
* `transport_on_side`: on the side `γ(n)ψ = ψ` of a unit `n`, `(1 + γ(flip_t n)γ(n))ψ = 2n_t γ_tψ`,
  `1 + flip_t n · n = 2n_t²`, and `γ_tψ` lies on the side of `flip_t n`;
* `transport_is_step`: **the normalized transport is `sign(n_t)γ_t` on the side**;
* `holo_eq`: the transports multiplied along a walk are `signProd · γ_{t_N} ⋯ γ_{t_1}`;
* `holonomy_closed`: **around a closed walk `w` the holonomy is `σ_w`, times `Π_x sign(n_x)` when
  `w` is odd**: the vertical sign `σ_w` (spin one half on every square, Proposition 34) is the rotation of
  the sphere's connection, and averaged over the excursions it is gravity's `−1/19` and the weak seed
  `−1/13` (Proposition 30).
-/

open Comparison Matrix

namespace Comparison.RuleAndLaw

/-! ## Counting the steps of a walk -/

/-- The steps along `x`: `m_x`. -/
def mC (x : Fin 5) (v : List (Fin 5)) : ℕ := v.countP (fun t => t = x)

/-- The steps along the other lines: `c_x = N − m_x`. -/
def cC (x : Fin 5) (v : List (Fin 5)) : ℕ := v.countP (fun t => t ≠ x)

theorem mC_cons (x t : Fin 5) (v : List (Fin 5)) :
    mC x (t :: v) = mC x v + if t = x then 1 else 0 := by
  simp [mC, List.countP_cons]

theorem cC_cons (x t : Fin 5) (v : List (Fin 5)) :
    cC x (t :: v) = cC x v + if t ≠ x then 1 else 0 := by
  simp [cC, List.countP_cons]

theorem mC_add_cC (x : Fin 5) (v : List (Fin 5)) : mC x v + cC x v = v.length := by
  induction v with
  | nil => simp [mC, cC]
  | cons t v ih =>
    rw [mC_cons, cC_cons, List.length_cons]
    by_cases h : t = x
    · simp only [h, ite_true, ne_eq, not_true_eq_false, ite_false]
      omega
    · simp only [h, ite_false, ne_eq, not_false_eq_true, ite_true]
      omega

theorem sum_mC (v : List (Fin 5)) : ∑ x, mC x v = v.length := by
  induction v with
  | nil => simp [mC]
  | cons t v ih =>
    simp only [mC_cons, Finset.sum_add_distrib, ih, List.length_cons]
    simp

/-- The pairs of steps along different lines. -/
def eC : List (Fin 5) → ℕ
  | [] => 0
  | t :: v => eC v + cC t v

/-- **`2e + Σ_x m_x² = N²`.** -/
theorem eC_quad (v : List (Fin 5)) :
    2 * (eC v : ℤ) + ∑ x, (mC x v : ℤ) ^ 2 = (v.length : ℤ) ^ 2 := by
  induction v with
  | nil => simp [eC, mC]
  | cons t v ih =>
    have h : (mC t v : ℤ) + cC t v = v.length := by exact_mod_cast mC_add_cC t v
    have hs : ∑ x, (mC x (t :: v) : ℤ) ^ 2 = ∑ x, (mC x v : ℤ) ^ 2 + 2 * mC t v + 1 := by
      simp only [mC_cons]
      push_cast
      fin_cases t <;> simp [Fin.sum_univ_five] <;> ring
    rw [eC, hs, List.length_cons]
    push_cast
    linear_combination ih + 2 * h

/-- **A closed walk has an even number of pairs of steps along different lines.** -/
theorem eC_even (v : List (Fin 5)) (hv : ∀ x, Even (cC x v)) : Even (eC v) := by
  have hq := eC_quad v
  have hsum : ∑ x, (mC x v : ℤ) = v.length := by exact_mod_cast sum_mC v
  choose K hK using hv
  have hm : ∀ x, (mC x v : ℤ) = v.length - 2 * K x := by
    intro x
    have h1 := mC_add_cC x v
    have h2 := hK x
    omega
  rw [Fin.sum_univ_five, hm 0, hm 1, hm 2, hm 3, hm 4] at hq hsum
  have h2 : (eC v : ℤ) = 2 * ((v.length : ℤ) ^ 2 - ((K 0 : ℤ) ^ 2 + (K 1 : ℤ) ^ 2 + (K 2 : ℤ) ^ 2 +
      (K 3 : ℤ) ^ 2 + (K 4 : ℤ) ^ 2)) := by
    have h4 : 2 * (eC v : ℤ) = 2 * (2 * ((v.length : ℤ) ^ 2 - ((K 0 : ℤ) ^ 2 + (K 1 : ℤ) ^ 2 +
        (K 2 : ℤ) ^ 2 + (K 3 : ℤ) ^ 2 + (K 4 : ℤ) ^ 2))) := by
      linear_combination hq - 2 * (v.length : ℤ) * hsum
    omega
  exact (Int.even_coe_nat _).mp ⟨(v.length : ℤ) ^ 2 - ((K 0 : ℤ) ^ 2 + (K 1 : ℤ) ^ 2 + (K 2 : ℤ) ^ 2 +
      (K 3 : ℤ) ^ 2 + (K 4 : ℤ) ^ 2), by rw [h2]; ring⟩

/-! ## A line is divided between a walk's ends when an odd number of steps go along others -/

theorem disagreeSet_zero' : disagreeSet 0 = ∅ := by decide

theorem odd_cC_iff_mem (w : List (Fin 5)) (x : Fin 5) :
    x ∈ disagreeSet (relOfWord w) ↔ Odd (cC x w) := by
  induction w with
  | nil => simp [relOfWord, disagreeSet_zero', cC]
  | cons t w ih =>
    rw [relOfWord_cons, disagreeSet_transition, Finset.mem_symmDiff, ih, cC_cons, Finset.mem_erase]
    by_cases htx : t = x
    · subst htx
      simp
    · have hxt : x ≠ t := Ne.symm htx
      simp only [ne_eq, htx, not_false_eq_true, ite_true, Nat.odd_add_one, hxt, Finset.mem_univ,
        and_true, true_and]
      tauto

/-- **A closed walk has `N − m_x` even for every line `x`.** -/
theorem closed_cC_even (w : List (Fin 5)) (hw : relOfWord w = 0) (x : Fin 5) : Even (cC x w) := by
  have h := odd_cC_iff_mem w x
  rw [hw, disagreeSet_zero'] at h
  simp only [Finset.notMem_empty, false_iff] at h
  exact Nat.not_odd_iff_even.mp h

/-! ## The sign identity -/

/-- The sign of a nonzero number, `±1`. -/
noncomputable def sgn (r : ℝ) : ℝ := if 0 < r then 1 else -1

/-- **The step along `t` carries the kept point to `flip_t n = 2n_t e_t − n`.** -/
def flipPt (t : Fin 5) (n : Fin 5 → ℝ) : Fin 5 → ℝ := fun x => if x = t then n x else -n x

/-- `Π_k sign(n^{(k−1)}_{t_k})` along a walk, oldest step first. -/
noncomputable def signProd : (Fin 5 → ℝ) → List (Fin 5) → ℝ
  | _, [] => 1
  | n, t :: v => sgn (n t) * signProd (flipPt t n) v

theorem sgn_cases (r : ℝ) : sgn r = 1 ∨ sgn r = -1 := by
  unfold sgn
  split_ifs <;> simp

theorem sgn_neg (r : ℝ) (hr : r ≠ 0) : sgn (-r) = -sgn r := by
  unfold sgn
  rcases lt_or_gt_of_ne hr with h | h
  · have h1 : 0 < -r := by linarith
    have h2 : ¬ 0 < r := by linarith
    simp [h1, h2]
  · have h1 : ¬ 0 < -r := by linarith
    simp [h1, h]

theorem flipPt_ne_zero (t : Fin 5) (n : Fin 5 → ℝ) (hn : ∀ x, n x ≠ 0) (x : Fin 5) :
    flipPt t n x ≠ 0 := by
  unfold flipPt
  split_ifs
  · exact hn x
  · exact neg_ne_zero.mpr (hn x)

theorem sgn_flipPt (t : Fin 5) (n : Fin 5 → ℝ) (hn : ∀ x, n x ≠ 0) (x : Fin 5) :
    sgn (flipPt t n x) = if x = t then sgn (n x) else -sgn (n x) := by
  unfold flipPt
  split_ifs
  · rfl
  · exact sgn_neg (n x) (hn x)

theorem cC_eq_sum (t : Fin 5) (v : List (Fin 5)) :
    cC t v = ∑ x, if x = t then 0 else mC x v := by
  have h1 := mC_add_cC t v
  have h2 := sum_mC v
  have h3 : ∑ x, mC x v = mC t v + ∑ x, (if x = t then 0 else mC x v) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t)]
    congr 1
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add]
    apply Finset.sum_congr
    · ext x
      simp [Finset.mem_erase]
    · intro x _
      rfl
  omega

/-- **`signProd n v = (−1)^{e(v)} Π_x sign(n_x)^{m_x}`** at every point with nonzero coordinates. -/
theorem signProd_formula (v : List (Fin 5)) :
    ∀ n : Fin 5 → ℝ, (∀ x, n x ≠ 0) →
      signProd n v = (-1) ^ (eC v) * ∏ x, sgn (n x) ^ (mC x v) := by
  induction v with
  | nil => intro n _; simp [signProd, eC, mC]
  | cons t v ih =>
    intro n hn
    rw [signProd, ih (flipPt t n) (flipPt_ne_zero t n hn), eC]
    have hflip : ∏ x, sgn (flipPt t n x) ^ (mC x v) =
        (-1) ^ (cC t v) * ∏ x, sgn (n x) ^ (mC x v) := by
      have e1 : ∀ x, sgn (flipPt t n x) ^ (mC x v) =
          (-1 : ℝ) ^ (if x = t then 0 else mC x v) * sgn (n x) ^ (mC x v) := by
        intro x
        rw [sgn_flipPt t n hn x]
        split_ifs
        · simp
        · rw [neg_pow]
      simp only [e1]
      rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ← cC_eq_sum]
    rw [hflip]
    have hcons : ∏ x, sgn (n x) ^ (mC x (t :: v)) = sgn (n t) * ∏ x, sgn (n x) ^ (mC x v) := by
      simp only [mC_cons, pow_add]
      rw [Finset.prod_mul_distrib]
      have : ∏ x, sgn (n x) ^ (if t = x then 1 else 0) = sgn (n t) := by
        rw [Finset.prod_eq_single t]
        · simp
        · intro b _ hb
          simp [Ne.symm hb]
        · simp
      rw [this]
      ring
    rw [hcons, pow_add]
    ring

/-- **Around a closed walk the signs multiply to `1` (even) or `Π_x sign(n_x)` (odd).** -/
theorem signProd_closed (v : List (Fin 5)) (hv : ∀ x, Even (cC x v)) (n : Fin 5 → ℝ)
    (hn : ∀ x, n x ≠ 0) :
    signProd n v = if Even v.length then 1 else ∏ x, sgn (n x) := by
  rw [signProd_formula v n hn, (eC_even v hv).neg_one_pow, one_mul]
  have hpar : ∀ x, (Even (mC x v) ↔ Even v.length) := by
    intro x
    have h1 := mC_add_cC x v
    have h2 := hv x
    rw [← h1, Nat.even_add]
    simp [h2]
  split_ifs with hN
  · apply Finset.prod_eq_one
    intro x _
    have hx : Even (mC x v) := (hpar x).mpr hN
    rcases sgn_cases (n x) with h | h <;> rw [h]
    · simp
    · exact hx.neg_one_pow
  · apply Finset.prod_congr rfl
    intro x _
    have hx : Odd (mC x v) := Nat.not_even_iff_odd.mp (fun h => hN ((hpar x).mp h))
    rcases sgn_cases (n x) with h | h <;> rw [h]
    · simp
    · exact hx.neg_one_pow

/-! ## The transport of the sides along a step -/

theorem γ_conj_line (t s : Fin 5) : γ t * γ s * γ t = if s = t then γ t else -γ s := by
  split_ifs with h
  · subst h
    rw [γ_mul_self, one_mul]
  · calc γ t * γ s * γ t = -(γ s * γ t) * γ t := by rw [γ_anticomm (Ne.symm h)]
      _ = -(γ s * (γ t * γ t)) := by noncomm_ring
      _ = -γ s := by rw [γ_mul_self, mul_one]

/-- **`γ_t γ(n) γ_t = γ(flip_t n)`**: one step reflects the kept point through the line `t`. -/
theorem γv_flip (t : Fin 5) (n : Fin 5 → ℝ) : γ t * γv n * γ t = γv (flipPt t n) := by
  simp only [γv, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  apply Finset.sum_congr rfl
  intro s _
  rw [γ_conj_line, flipPt]
  split_ifs with h
  · subst h
    rfl
  · push_cast
    rw [smul_neg, neg_smul]

theorem γv_single (t : Fin 5) : γv (Pi.single t 1) = γ t := by
  simp only [γv]
  rw [Finset.sum_eq_single t]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem γv_anticomm_line (n : Fin 5 → ℝ) (t : Fin 5) :
    γv n * γ t + γ t * γv n = ((2 * n t : ℝ) : ℂ) • (1 : Matrix Four Four ℂ) := by
  have h := anticomm_γv n (Pi.single t 1)
  rw [γv_single] at h
  rw [h]
  congr 2
  rw [Finset.sum_eq_single t]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

/-- **On the side of `n` the transport along `t` doubles to `2n_t γ_t`**, with `1 + m·n = 2n_t²`, and it
lands on the side of `flip_t n`. -/
theorem transport_on_side (n : Fin 5 → ℝ) (hn : ∑ x, n x ^ 2 = 1) (t : Fin 5) (ψ : Four → ℂ)
    (hψ : γv n *ᵥ ψ = ψ) :
    (1 + γv (flipPt t n) * γv n) *ᵥ ψ = ((2 * n t : ℝ) : ℂ) • (γ t *ᵥ ψ) ∧
      1 + ∑ x, flipPt t n x * n x = 2 * n t ^ 2 ∧
      γv (flipPt t n) *ᵥ (γ t *ᵥ ψ) = γ t *ᵥ ψ := by
  have hA := γv_anticomm_line n t
  have hconj : γ t * γv n * γ t = ((2 * n t : ℝ) : ℂ) • γ t - γv n := by
    have e : γv n * γ t = ((2 * n t : ℝ) : ℂ) • (1 : Matrix Four Four ℂ) - γ t * γv n := by
      rw [← hA]
      abel
    calc γ t * γv n * γ t = γ t * (γv n * γ t) := by rw [mul_assoc]
      _ = γ t * (((2 * n t : ℝ) : ℂ) • (1 : Matrix Four Four ℂ) - γ t * γv n) := by rw [e]
      _ = ((2 * n t : ℝ) : ℂ) • γ t - (γ t * γ t) * γv n := by
        rw [Matrix.mul_sub, Matrix.mul_smul, mul_one, mul_assoc]
      _ = ((2 * n t : ℝ) : ℂ) • γ t - γv n := by rw [γ_mul_self, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [← γv_flip, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hψ, hconj,
      Matrix.sub_mulVec, Matrix.smul_mulVec, hψ]
    abel
  · have e : ∀ x, flipPt t n x * n x = 2 * (if x = t then n x ^ 2 else 0) - n x ^ 2 := by
      intro x
      unfold flipPt
      split_ifs <;> ring
    simp only [e, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, hn]
    ring
  · rw [← γv_flip, Matrix.mulVec_mulVec, mul_assoc (γ t * γv n), γ_mul_self, mul_one,
      ← Matrix.mulVec_mulVec, hψ]

/-- **The normalized transport is `sign(n_t)γ_t` on the side** (Proposition 89 (ii)):
`(1 + γ(m)γ(n))ψ/√(2(1 + m·n)) = sign(n_t) γ_tψ`, `m = flip_t n`, for a unit `n` with `n_t ≠ 0`. -/
theorem transport_is_step (n : Fin 5 → ℝ) (hn : ∑ x, n x ^ 2 = 1) (t : Fin 5) (ht : n t ≠ 0)
    (ψ : Four → ℂ) (hψ : γv n *ᵥ ψ = ψ) :
    ((1 / Real.sqrt (2 * (1 + ∑ x, flipPt t n x * n x)) : ℝ) : ℂ) •
        ((1 + γv (flipPt t n) * γv n) *ᵥ ψ) = ((sgn (n t) : ℝ) : ℂ) • (γ t *ᵥ ψ) := by
  obtain ⟨h1, h2, -⟩ := transport_on_side n hn t ψ hψ
  rw [h1, h2, smul_smul]
  congr 1
  have hsq : Real.sqrt (2 * (2 * n t ^ 2)) = 2 * |n t| := by
    rw [show 2 * (2 * n t ^ 2) = (2 * |n t|) ^ 2 by rw [mul_pow, sq_abs]; ring,
      Real.sqrt_sq (by positivity)]
  have key : (1 / (2 * |n t|)) * (2 * n t) = sgn (n t) := by
    unfold sgn
    split_ifs with hpos
    · rw [abs_of_pos hpos, div_mul_eq_mul_div, one_mul, div_eq_iff (by linarith : 2 * n t ≠ 0)]
      ring
    · have hneg : n t < 0 := lt_of_le_of_ne (not_lt.mp hpos) ht
      rw [abs_of_neg hneg, div_mul_eq_mul_div, one_mul, div_eq_iff (by linarith : 2 * -n t ≠ 0)]
      ring
  rw [hsq, ← Complex.ofReal_mul, key]

/-! ## The holonomy around a closed walk -/

/-- The steps `sign(n_t)γ_t` multiplied along a walk, oldest step first, the kept point carried. -/
noncomputable def holo : (Fin 5 → ℝ) → List (Fin 5) → Matrix Four Four ℂ
  | _, [] => 1
  | n, t :: v => holo (flipPt t n) v * (((sgn (n t) : ℝ) : ℂ) • γ t)

/-- **The transports multiply to `signProd · γ_{t_N} ⋯ γ_{t_1}`.** -/
theorem holo_eq (v : List (Fin 5)) :
    ∀ n : Fin 5 → ℝ, holo n v = ((signProd n v : ℝ) : ℂ) • (v.reverse.map γ).prod := by
  induction v with
  | nil => intro n; simp [holo, signProd]
  | cons t v ih =>
    intro n
    rw [holo, ih, signProd, List.reverse_cons, List.map_append, List.prod_append]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    push_cast
    ring_nf

/-- **Around a closed walk `w` (newest step first, `relOfWord w = 0`) the parallel rotation of the
sphere of lines is the walk's Clifford sign `σ_w`, times `Π_x sign(n_x)` when `w` is odd**
(Proposition 89 (iii)), at every kept point with nonzero coordinates. -/
theorem holonomy_closed (n : Fin 5 → ℝ) (hn : ∀ x, n x ≠ 0) (w : List (Fin 5))
    (hw : relOfWord w = 0) :
    holo n w.reverse = ((coef w : ℂ) *
      ((if Even w.length then 1 else ∏ x, sgn (n x) : ℝ) : ℂ)) • (1 : Matrix Four Four ℂ) := by
  have hc : ∀ x, Even (cC x w.reverse) := by
    intro x
    have h := closed_cC_even w hw x
    simpa [cC, List.countP_reverse] using h
  rw [holo_eq, signProd_closed w.reverse hc n hn, List.reverse_reverse, excursion_scalar hw,
    List.length_reverse, smul_smul]
  ring_nf

end Comparison.RuleAndLaw

#print axioms Comparison.RuleAndLaw.mC_add_cC
#print axioms Comparison.RuleAndLaw.sum_mC
#print axioms Comparison.RuleAndLaw.eC_quad
#print axioms Comparison.RuleAndLaw.eC_even
#print axioms Comparison.RuleAndLaw.odd_cC_iff_mem
#print axioms Comparison.RuleAndLaw.closed_cC_even
#print axioms Comparison.RuleAndLaw.signProd_formula
#print axioms Comparison.RuleAndLaw.signProd_closed
#print axioms Comparison.RuleAndLaw.γ_conj_line
#print axioms Comparison.RuleAndLaw.γv_flip
#print axioms Comparison.RuleAndLaw.γv_anticomm_line
#print axioms Comparison.RuleAndLaw.transport_on_side
#print axioms Comparison.RuleAndLaw.transport_is_step
#print axioms Comparison.RuleAndLaw.holo_eq
#print axioms Comparison.RuleAndLaw.holonomy_closed
#print axioms Comparison.RuleAndLaw.mC_cons
#print axioms Comparison.RuleAndLaw.cC_cons
#print axioms Comparison.RuleAndLaw.disagreeSet_zero'
#print axioms Comparison.RuleAndLaw.sgn_cases
#print axioms Comparison.RuleAndLaw.sgn_neg
#print axioms Comparison.RuleAndLaw.flipPt_ne_zero
#print axioms Comparison.RuleAndLaw.sgn_flipPt
#print axioms Comparison.RuleAndLaw.cC_eq_sum
#print axioms Comparison.RuleAndLaw.γv_single
