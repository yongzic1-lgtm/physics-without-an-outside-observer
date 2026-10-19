module

public import Comparison.Existence.Zero

/-!
# The road to the masses: the repeated return `N(1)` to its digits (Proposition 72)

With `u = i/4`, the `k`-th repeated return is
`p_k = Σ_w y_wᵏ = −Φ(4uᵏ)` for odd `k` and `F(4uᵏ)` for even `k` (Proposition 72; the sums over the
excursions are `p_odd`, `p_even` of `Zero.lean`), and `N(1) = Σ_{k ≥ 1} p_k`.

* `zPow k = 4uᵏ`; `zPow_sq`: `(4uᵏ)² = 16 (−1/16)ᵏ`.
* `repReturn_hasSum`: **`p_k` is the sum over the excursions**, for every `k ≥ 1`.
* `repR k`: the real closed form; `repReturn_real`: **`p_k = repR k`**, a real number:
  `p_k = q²/(16 − 3q)`, `q = 16^{1−k}`, for odd `k`; `p_k = z⁴(1 + z)/(16 − 8z − 3z² − 3z³)`,
  `z = 4(−1/16)^{k/2}`, for even `k`.
* `repR_one` … `repR_six`: `1/13`, `1/6096`, `1/1047808`, `65/17044852736`, `1/68719280128`,
  `341/6007730461474816`; `repR_pos`: every `p_k > 0`.
* `repR_bound`: **the tail: `0 < p_k ≤ (1/10)(1/256)^{k−1}` for `k ≥ 2`**.
* `N1_hasSum`, `N1_bounds`: **`N(1) = Σ_{k≥1} p_k` lies in `(0.0770880771192245, 0.0770880771192250)`**:
  `N(1) = 0.0770881` to the book's digits and `0.07708807712` to ONE_RULE's.
-/

@[expose] public section

namespace Comparison

open Complex Filter Topology

/-- The point `4uᵏ` with `u = i/4`. -/
noncomputable def zPow (k : ℕ) : ℂ := 4 * (I / 4) ^ k

/-- **The `k`-th repeated return:** `−Φ(4uᵏ)` for odd `k`, `F(4uᵏ)` for even `k`. -/
noncomputable def repReturn (k : ℕ) : ℂ :=
  if Odd k then (zPow k) ^ 4 / (16 + 3 * (zPow k) ^ 2)
  else (zPow k) ^ 4 * (1 + zPow k) / (16 - 8 * zPow k - 3 * (zPow k) ^ 2 - 3 * (zPow k) ^ 3)

/-- **`p_k` is the sum over the excursions:** `Σ_n (−φ(n))(4uᵏ)ⁿ` for odd `k`, `Σ_n f(n)(4uᵏ)ⁿ` for even
`k`. -/
theorem repReturn_hasSum (k : ℕ) (hk : 1 ≤ k) :
    HasSum (fun n => (if Odd k then -(signedLaw n : ℂ) else (excursionLaw n : ℂ)) * (zPow k) ^ n)
      (repReturn k) := by
  by_cases ho : Odd k
  · simp only [ho, if_true, repReturn]
    have h := (p_odd k hk).neg
    convert h using 1
    · funext n
      simp [zPow]
    · simp only [zPow]
      ring
  · simp only [ho, if_false, repReturn]
    have h := p_even k hk
    convert h using 1 <;> simp only [zPow]

theorem I_div_four_sq : (I / 4) ^ 2 = (-1 / 16 : ℂ) := by
  rw [div_pow, I_sq]
  norm_num

/-- `(4uᵏ)² = 16 (−1/16)ᵏ`. -/
theorem zPow_sq (k : ℕ) : (zPow k) ^ 2 = 16 * (-1 / 16 : ℂ) ^ k := by
  rw [zPow, mul_pow, ← pow_mul, mul_comm k 2, pow_mul, I_div_four_sq]
  norm_num

/-- `4u^{2m} = 4 (−1/16)^m`. -/
theorem zPow_even (m : ℕ) : zPow (2 * m) = 4 * (-1 / 16 : ℂ) ^ m := by
  rw [zPow, pow_mul, I_div_four_sq]

/-- **The real closed form of `p_k`.** -/
noncomputable def repR (k : ℕ) : ℝ :=
  if Odd k then ((1 / 16 : ℝ) ^ (k - 1)) ^ 2 / (16 - 3 * (1 / 16 : ℝ) ^ (k - 1))
  else (4 * (-1 / 16 : ℝ) ^ (k / 2)) ^ 4 * (1 + 4 * (-1 / 16 : ℝ) ^ (k / 2)) /
    (16 - 8 * (4 * (-1 / 16 : ℝ) ^ (k / 2)) - 3 * (4 * (-1 / 16 : ℝ) ^ (k / 2)) ^ 2 -
      3 * (4 * (-1 / 16 : ℝ) ^ (k / 2)) ^ 3)

/-- **`p_k` is real: `p_k = repR k`.** -/
theorem repReturn_real (k : ℕ) (hk : 1 ≤ k) : repReturn k = (repR k : ℂ) := by
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hne : ¬Odd k := Nat.not_odd_iff_even.mpr ⟨m, hm⟩
    have hk2 : k = 2 * m := by omega
    simp only [repReturn, repR, hne, if_false]
    rw [hk2, zPow_even, show 2 * m / 2 = m by omega]
    push_cast
    ring
  · have ho : Odd k := ⟨m, hm⟩
    simp only [repReturn, repR, ho, if_true]
    have h2 : (zPow k) ^ 2 = -((1 / 16 : ℂ) ^ (k - 1)) := by
      rw [zPow_sq, hm, show 2 * m + 1 - 1 = 2 * m by omega, pow_succ, pow_mul, pow_mul]
      norm_num
      ring
    have h4 : (zPow k) ^ 4 = ((1 / 16 : ℂ) ^ (k - 1)) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, h2]
      ring
    rw [h4, h2]
    push_cast
    ring

theorem repR_one : repR 1 = 1 / 13 := by norm_num [repR]
theorem repR_two : repR 2 = 1 / 6096 := by norm_num [repR]
theorem repR_three : repR 3 = 1 / 1047808 := by
  have : Odd 3 := by decide
  norm_num [repR, this]
theorem repR_four : repR 4 = 65 / 17044852736 := by
  have : ¬Odd 4 := by decide
  norm_num [repR, this]
theorem repR_five : repR 5 = 1 / 68719280128 := by
  have : Odd 5 := by decide
  norm_num [repR, this]
theorem repR_six : repR 6 = 341 / 6007730461474816 := by
  have : ¬Odd 6 := by decide
  norm_num [repR, this]

/-- **The tail: `0 < p_k ≤ (1/10)(1/256)^{k−1}` for `k ≥ 2`.** -/
theorem repR_bound (k : ℕ) (hk : 2 ≤ k) : 0 < repR k ∧ repR k ≤ (1 / 10) * (1 / 256) ^ (k - 1) := by
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hne : ¬Odd k := Nat.not_odd_iff_even.mpr ⟨m, hm⟩
    have hk2 : k = 2 * m := by omega
    have hm1 : 1 ≤ m := by omega
    simp only [repR, hne, if_false]
    rw [hk2, show 2 * m / 2 = m by omega]
    set z : ℝ := 4 * (-1 / 16 : ℝ) ^ m with hz
    have habs : |z| = 4 * (1 / 16 : ℝ) ^ m := by
      rw [hz, abs_mul, abs_pow]
      norm_num
    have hsmall : |z| ≤ 1 / 4 := by
      rw [habs]
      have : (1 / 16 : ℝ) ^ m ≤ (1 / 16) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm1
      linarith
    have hz4 : z ^ 4 = (1 / 256 : ℝ) ^ (2 * m - 1) := by
      have e : z ^ 4 = |z| ^ 4 := by rw [← abs_pow]; exact (abs_of_nonneg (by positivity)).symm
      have e1 : z ^ 4 = 256 * (1 / 256 : ℝ) ^ (2 * m) := by
        rw [e, habs, mul_pow, ← pow_mul, show m * 4 = 2 * (2 * m) by ring, pow_mul]
        norm_num
      have e2 : (1 / 256 : ℝ) ^ (2 * m) = (1 / 256) ^ (2 * m - 1) * (1 / 256) := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega)]
      rw [e1, e2]
      ring
    have hzl := abs_le.mp hsmall
    have hden : 13 ≤ 16 - 8 * z - 3 * z ^ 2 - 3 * z ^ 3 := by
      have h2 : z ^ 2 ≤ 1 / 16 := by nlinarith
      have h3 : -(1 / 64) ≤ z ^ 3 := by nlinarith [sq_nonneg z]
      nlinarith
    have hnum : 0 < 1 + z := by linarith
    have hz4pos : 0 < z ^ 4 := by rw [hz4]; positivity
    constructor
    · positivity
    · rw [div_le_iff₀ (by linarith), ← hz4]
      have : 1 + z ≤ 5 / 4 := by linarith
      have h1 : z ^ 4 * (1 + z) ≤ z ^ 4 * (5 / 4) := mul_le_mul_of_nonneg_left this hz4pos.le
      have h3 : 1 / 10 * z ^ 4 * 13 ≤ 1 / 10 * z ^ 4 * (16 - 8 * z - 3 * z ^ 2 - 3 * z ^ 3) :=
        mul_le_mul_of_nonneg_left hden (by positivity)
      nlinarith
  · have ho : Odd k := ⟨m, hm⟩
    have hm1 : 1 ≤ m := by omega
    simp only [repR, ho, if_true]
    set q : ℝ := (1 / 16 : ℝ) ^ (k - 1) with hq
    have hq0 : 0 < q := by positivity
    have hqs : q ≤ 1 / 256 := by
      rw [hq, hm, show 2 * m + 1 - 1 = 2 * m by omega, pow_mul]
      have : ((1 / 16 : ℝ) ^ 2) ^ m ≤ ((1 / 16 : ℝ) ^ 2) ^ 1 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hm1
      norm_num at this ⊢
      linarith
    have hq2 : q ^ 2 = (1 / 256 : ℝ) ^ (k - 1) := by
      rw [hq, ← pow_mul, mul_comm, pow_mul]
      norm_num
    constructor
    · have : 0 < 16 - 3 * q := by linarith
      positivity
    · rw [← hq2, div_le_iff₀ (by linarith)]
      have : 0 ≤ q ^ 2 := sq_nonneg q
      nlinarith

theorem repR_pos (k : ℕ) (hk : 1 ≤ k) : 0 < repR k := by
  rcases Nat.lt_or_ge k 2 with h | h
  · have : k = 1 := by omega
    rw [this, repR_one]
    norm_num
  · exact (repR_bound k h).1

theorem repR_summable : Summable (fun k : ℕ => repR (k + 1)) := by
  have hg : Summable (fun k : ℕ => (1 / 10 : ℝ) * (1 / 256) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  refine Summable.of_nonneg_of_le (fun k => (repR_pos (k + 1) (by omega)).le) (fun k => ?_) hg
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    rw [repR_one]
    norm_num
  · have := (repR_bound (k + 1) (by omega)).2
    rwa [show k + 1 - 1 = k by omega] at this

/-- **`N(1) = Σ_{k ≥ 1} p_k`.** -/
noncomputable def N1 : ℝ := ∑' k : ℕ, repR (k + 1)

theorem N1_hasSum : HasSum (fun k : ℕ => repR (k + 1)) N1 := repR_summable.hasSum

/-- **`N(1)` to its digits:** `0.0770880771192245 < N(1) < 0.0770880771192250`; in particular
`N(1) = 0.0770881` (Proposition 72) and `0.07708807712` (ONE_RULE) to the digits they state. -/
theorem N1_bounds : (0.0770880771192245 : ℝ) < N1 ∧ N1 < 0.0770880771192250 := by
  have hs : Summable (fun k : ℕ => repR (k + 6 + 1)) :=
    (summable_nat_add_iff (f := fun k : ℕ => repR (k + 1)) 6).mpr repR_summable
  have hsplit0 := Summable.sum_add_tsum_nat_add (f := fun k : ℕ => repR (k + 1)) 6 repR_summable
  have hsplit : ∑ i ∈ Finset.range 6, repR (i + 1) + ∑' i : ℕ, repR (i + 6 + 1) = N1 := by
    rw [N1]
    exact hsplit0
  have hS6 : ∑ k ∈ Finset.range 6, repR (k + 1) =
      1 / 13 + 1 / 6096 + 1 / 1047808 + 65 / 17044852736 + 1 / 68719280128 +
        341 / 6007730461474816 := by
    simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
    rw [repR_one, repR_two, repR_three, repR_four, repR_five, repR_six]
  have htail_pos : 0 < ∑' k : ℕ, repR (k + 6 + 1) :=
    hs.tsum_pos (fun k => (repR_pos _ (by omega)).le) 0 (repR_pos _ (by omega))
  have hg : HasSum (fun k : ℕ => (1 / 10 * (1 / 256) ^ 6 : ℝ) * (1 / 256) ^ k)
      ((1 / 10 * (1 / 256) ^ 6) * (1 - 1 / 256)⁻¹) :=
    (hasSum_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hle : ∀ k : ℕ, repR (k + 6 + 1) ≤ (1 / 10 * (1 / 256) ^ 6 : ℝ) * (1 / 256) ^ k := by
    intro k
    have := (repR_bound (k + 6 + 1) (by omega)).2
    rw [show k + 6 + 1 - 1 = k + 6 by omega, pow_add] at this
    linarith
  have htail_le : ∑' k : ℕ, repR (k + 6 + 1) ≤ (1 / 10 * (1 / 256) ^ 6) * (1 - 1 / 256)⁻¹ :=
    hs.tsum_le_of_sum_le fun s => (Finset.sum_le_sum fun k _ => hle k).trans
      (sum_le_hasSum s (fun k _ => by positivity) hg)
  rw [← hsplit, hS6]
  constructor
  · norm_num
    linarith
  · norm_num at htail_le ⊢
    linarith

end Comparison

end
