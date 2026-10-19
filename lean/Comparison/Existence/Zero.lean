module

public import Comparison.Existence.Excursion
public import Comparison.Existence.AvailableTransitions
public import Comparison.Existence.Coin

/-!
# Book XII. The long-range zero under a weight (Proposition 71) and the law one level up
(Proposition 72): the finite parts

**Prop. 71.**
* The visits of an excursion, by the classes of Proposition 29 (Kac): `hasSum_lump_a` … `hasSum_lump_e`;
  `visits_per_state`: **every one of the eighty states is visited `1/5` times per excursion**;
  `plane_visits`, `line_visits`, `place_visits`: `10` symmetric states, `5` vector states, `1` start's vertex per
  excursion, so `v = (10, 5)/16` (`excursion_mean`: `16` steps); `availableTransitions_visits`: `h`'s seventy-four states,
  `74/5` visits; `steps_along_lastDirection`: `E_H = C_h/20 = 60/20 = 3` steps along `h` per excursion, and
  `steps_along_lastDirection_count`: `3 = (16 − 1)/5`.
* The last-step directions: `lastDirectionStep = (𝟏𝟏ᵀ − 1)/4`; `lastDirectionStep_pow`: `Hᵏ = 𝟏𝟏ᵀ/5 + (−1/4)ᵏ(1 − 𝟏𝟏ᵀ/5)`;
  `lastDirection_stationary`: the uniform law; `lastDirection_cov`: `Cov(X₀, X_k) = (4/25)(−1/4)ᵏ` for the steps along
  one line; `lastDirection_spread`: `σ² = Σ_{k ∈ ℤ} Cov = 12/125 = (1/5)(4/5)(3/5)`.
* `marks_centred`: from `Var P = 84`, `Var Q = 12`, `Cov = 30` and `ℓ = P + Q + 1`, the covariance of
  `(P − (10/16)ℓ, Q − (5/16)ℓ)` is `[[39/16, −45/32], [−45/32, 63/64]]`; `marks_length`:
  `84 + 12 + 2·30 = 156`, the variance of the excursion (`excursion_variance`).
* `flux_count`: `2(m − n) = 2(40 − 16) = 48 = n(d − 2)` (`card_edges`: `m = 40`).

**Prop. 72.** With `u = i/4`:
* `y_pow`: `(−σu^ℓ)ᵏ = (u^k)^ℓ` for even `k` and `−σ(u^k)^ℓ` for odd `k` (`σ = ±1`).
* `p_odd`, `p_even`: `Σ_n φ(n)(4uᵏ)ⁿ` and `Σ_n f(n)(4uᵏ)ⁿ` converge for every `k ≥ 1`, to `Φ(4uᵏ)` and
  `F(4uᵏ)`; `p_one`: `p₁ = −Φ(i) = 1/13`; `p_two`: `p₂ = F(−1/4) = 1/6096`.
-/

@[expose] public section

namespace Comparison

open Finset Complex

/-! ## Prop. 71: the visits of an excursion -/

theorem lump_e_norm (n : ℕ) : ((lumpSeq n).e : ℝ) / 4 ^ n = excursionLaw (n + 1) := by
  have h : ((excursionCount (n + 1) : ℤ) : ℝ) = ((5 * (lumpSeq n).e : ℤ) : ℝ) := by
    rw [excursionCount_lump]
  push_cast at h
  rw [excursionLaw, Nat.add_sub_cancel, h, div_eq_div_iff (by positivity) (by positivity)]
  ring

theorem lump_b_norm (n : ℕ) : ((lumpSeq n).b : ℝ) / 4 ^ n = excursionLaw (n + 2) := by
  rw [← lump_e_norm (n + 1)]
  have h : (lumpSeq (n + 1)).e = 4 * (lumpSeq n).b := rfl
  rw [h, pow_succ]
  push_cast
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

theorem lump_a_norm (n : ℕ) : ((lumpSeq n).a : ℝ) / 4 ^ n = if n = 0 then 1 else 0 := by
  rcases n with _ | n
  · norm_num [lumpSeq]
  · rw [lumpSeq_a]
    simp

theorem hasSum_lump_a : HasSum (fun n => ((lumpSeq n).a : ℝ) / 4 ^ n) 1 := by
  simp only [lump_a_norm]
  exact hasSum_ite_eq 0 1

theorem hasSum_lump_e : HasSum (fun n => ((lumpSeq n).e : ℝ) / 4 ^ n) 1 := by
  simp only [lump_e_norm]
  have := (hasSum_nat_add_iff' 1).mpr excursion_total
  simpa [excursionLaw_zero] using this

theorem hasSum_lump_b : HasSum (fun n => ((lumpSeq n).b : ℝ) / 4 ^ n) 1 := by
  simp only [lump_b_norm]
  have := (hasSum_nat_add_iff' 2).mpr excursion_total
  simpa [Finset.sum_range_succ, excursionLaw_zero, excursionLaw_one] using this

theorem hasSum_lump_c : HasSum (fun n => ((lumpSeq n).c : ℝ) / 4 ^ n) 1 := by
  rw [← hasSum_nat_add_iff' 1]
  have h := (hasSum_lump_a.mul_left (1 / 4 : ℝ)).add (hasSum_lump_b.mul_left (3 / 4 : ℝ))
  have hc0 : ((lumpSeq 0).c : ℝ) = 0 := by norm_num [lumpSeq]
  convert h using 1
  · funext n
    have : (lumpSeq (n + 1)).c = (lumpSeq n).a + 3 * (lumpSeq n).b := rfl
    rw [this, pow_succ]
    push_cast
    field_simp <;> ring
  · simp [hc0]
    norm_num

theorem hasSum_lump_d : HasSum (fun n => ((lumpSeq n).d : ℝ) / 4 ^ n) 1 := by
  have hb0 : ((lumpSeq 0).b : ℝ) = 0 := by norm_num [lumpSeq]
  have hb1 : HasSum (fun n => ((lumpSeq (n + 1)).b : ℝ) / 4 ^ (n + 1)) 1 := by
    have := (hasSum_nat_add_iff' 1).mpr hasSum_lump_b
    simpa [Finset.sum_range_one, hb0] using this
  have h := ((hb1.mul_left 4).sub hasSum_lump_c).div_const 3
  convert h using 1
  · funext n
    have : (lumpSeq (n + 1)).b = (lumpSeq n).c + 3 * (lumpSeq n).d := rfl
    rw [this, pow_succ]
    push_cast
    field_simp <;> ring
  · norm_num

/-- Every state lies in exactly one class. -/
theorem tyInd_sum :
    ∀ s : State, tyInd 1 s + tyInd 2 s + tyInd 3 s + tyInd 4 s + tyInd 0 s = 1 := by
  decide +kernel

/-- **Every one of the eighty states is visited `1/5` times per excursion** (the excursion's first step
uniform over the five directions, then four continuations each `1/4`). -/
theorem visits_per_state (s : State) :
    HasSum (fun n => (stateCount n s : ℝ) / (5 * 4 ^ n)) (1 / 5) := by
  have h := (((((hasSum_lump_a.mul_left (tyInd 1 s : ℝ)).add
    (hasSum_lump_b.mul_left (tyInd 2 s : ℝ))).add (hasSum_lump_c.mul_left (tyInd 3 s : ℝ))).add
    (hasSum_lump_d.mul_left (tyInd 4 s : ℝ))).add
    (hasSum_lump_e.mul_left (tyInd 0 s : ℝ))).div_const 5
  have hs := congrArg (fun z : ℤ => (z : ℝ)) (tyInd_sum s)
  push_cast at hs
  convert h using 1
  · funext n
    rw [lump_count]
    simp only [Lump.vec, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    field_simp
  · linear_combination (-1 / 5 : ℝ) * hs

theorem visits_of_set (S : Finset State) :
    HasSum (fun n => (∑ s ∈ S, (stateCount n s : ℝ)) / (5 * 4 ^ n)) (S.card / 5) := by
  have h := hasSum_sum (s := S) fun s _ => visits_per_state s
  convert h using 1
  · funext n
    rw [Finset.sum_div]
  · rw [Finset.sum_const, nsmul_eq_mul]
    ring

/-- **Ten symmetric states per excursion.** -/
theorem plane_visits :
    HasSum (fun n => (∑ s ∈ univ.filter (fun s : State => (disagreeSet s.1).card = 2),
      (stateCount n s : ℝ)) / (5 * 4 ^ n)) 10 := by
  have hc : (univ.filter (fun s : State => (disagreeSet s.1).card = 2)).card = 50 := by
    decide +kernel
  have h := visits_of_set (univ.filter (fun s : State => (disagreeSet s.1).card = 2))
  rw [hc] at h
  convert h using 1
  norm_num

/-- **Five vector states per excursion.** -/
theorem line_visits :
    HasSum (fun n => (∑ s ∈ univ.filter (fun s : State => (disagreeSet s.1).card = 4),
      (stateCount n s : ℝ)) / (5 * 4 ^ n)) 5 := by
  have hc : (univ.filter (fun s : State => (disagreeSet s.1).card = 4)).card = 25 := by
    decide +kernel
  have h := visits_of_set (univ.filter (fun s : State => (disagreeSet s.1).card = 4))
  rw [hc] at h
  convert h using 1
  norm_num

/-- **One arrival at the start's vertex per excursion: the excursion closes once.** -/
theorem place_visits :
    HasSum (fun n => (∑ s ∈ univ.filter (fun s : State => s.1 = 0),
      (stateCount n s : ℝ)) / (5 * 4 ^ n)) 1 := by
  have hc : (univ.filter (fun s : State => s.1 = 0)).card = 5 := by
    decide +kernel
  have h := visits_of_set (univ.filter (fun s : State => s.1 = 0))
  rw [hc] at h
  convert h using 1
  norm_num

/-- **All eighty: `80/5 = 16` steps per excursion**, the mean excursion of `excursion_mean` read by Kac. -/
theorem all_visits :
    HasSum (fun n => (∑ s : State, (stateCount n s : ℝ)) / (5 * 4 ^ n)) 16 := by
  have h := visits_of_set (univ : Finset State)
  rw [Finset.card_univ, card_state] at h
  convert h using 1
  norm_num

/-- **`h`'s seventy-four states are visited `74/5` times per excursion.** -/
theorem availableTransitions_visits (h : Fin 5) :
    HasSum (fun n => (∑ s ∈ excursionStates h, (stateCount n s : ℝ)) / (5 * 4 ^ n)) (74 / 5) := by
  have hv := visits_of_set (excursionStates h)
  rw [card_excursionStates] at hv
  convert hv using 1

/-- **`E_H = C_h/20 = 3`:** from each of the sixty states of the seventy-four whose last-step direction is not `h`
the continuation goes along `h` with `1/4`; per excursion, `(60/5)/4 = 3` steps along `h`. -/
theorem steps_along_lastDirection (h : Fin 5) :
    HasSum (fun n => (∑ s ∈ (excursionStates h).filter (fun s => s.2 ≠ h), (stateCount n s : ℝ)) /
      (5 * 4 ^ n) / 4) 3 := by
  have hc : ((excursionStates h).filter (fun s => s.2 ≠ h)).card = 60 := (availableTransitions_along h).1
  have hv := (visits_of_set ((excursionStates h).filter (fun s => s.2 ≠ h))).div_const 4
  rw [hc] at hv
  convert hv using 1
  norm_num

/-- `3 = (E ℓ − 1)/5`: of the `16/5` steps along `h` per excursion, the first step gives `1/5`. -/
theorem steps_along_lastDirection_count : (60 : ℚ) / 20 = 3 ∧ ((16 : ℚ) - 1) / 5 = 3 ∧
    (16 : ℚ) / 5 - 1 / 5 = 3 := by
  norm_num

/-! ## Prop. 71: the last-step directions of a walk -/

/-- The last-step directions: after a step along `i` the next step goes along each other line with `1/4`. -/
def lastDirectionStep : Matrix (Fin 5) (Fin 5) ℚ := (1 / 4 : ℚ) • (ones5 - 1)

theorem ones5_mul_ones5 : ones5 * ones5 = (5 : ℚ) • ones5 := by
  ext i j
  simp [ones5, Matrix.mul_apply]

/-- **`Hᵏ = 𝟏𝟏ᵀ/5 + (−1/4)ᵏ (1 − 𝟏𝟏ᵀ/5)`.** -/
theorem lastDirectionStep_pow (k : ℕ) :
    lastDirectionStep ^ k = (1 / 5 : ℚ) • ones5 + ((-1 / 4 : ℚ) ^ k) • (1 - (1 / 5 : ℚ) • ones5) := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero, one_smul]
    abel
  | succ k ih =>
    rw [pow_succ, ih, lastDirectionStep]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, ones5_mul_ones5, smul_smul, smul_sub, pow_succ]
    module

/-- **The uniform law is stationary for the last-step directions.** -/
theorem lastDirection_stationary (j : Fin 5) : ∑ i, (1 / 5 : ℚ) * lastDirectionStep i j = 1 / 5 := by
  fin_cases j <;> simp [lastDirectionStep, ones5, Fin.sum_univ_five, Matrix.one_apply] <;> norm_num

/-- **The steps along one line:** `Cov(X₀, X_k) = (1/5)(Hᵏ)_hh − (1/5)² = (4/25)(−1/4)ᵏ`. -/
theorem lastDirection_cov (h : Fin 5) (k : ℕ) :
    (1 / 5 : ℚ) * (lastDirectionStep ^ k) h h - (1 / 5) ^ 2 = (4 / 25) * (-1 / 4) ^ k := by
  rw [lastDirectionStep_pow]
  simp [ones5, Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply]
  ring

/-- **The spread of the steps along one line:** `σ² = Σ_{k ∈ ℤ} Cov(X₀, X_{|k|}) = 12/125`. -/
theorem lastDirection_spread :
    HasSum (fun k : ℕ => (if k = 0 then (1 : ℝ) else 2) * ((4 / 25) * (-1 / 4) ^ k))
      (12 / 125) := by
  have hg : HasSum (fun k : ℕ => (-1 / 4 : ℝ) ^ k) (1 - (-1 / 4))⁻¹ :=
    hasSum_geometric_of_abs_lt_one (by norm_num)
  have h := (hg.mul_left (2 * (4 / 25 : ℝ))).sub (hasSum_ite_eq 0 (4 / 25 : ℝ))
  convert h using 1
  · funext k
    split_ifs with hk
    · subst hk
      norm_num
    · ring
  · norm_num

theorem lastDirection_spread_formula : (1 / 5 : ℚ) * (4 / 5) * ((1 - 1 / 4) / (1 + 1 / 4)) = 12 / 125 ∧
    (1 / 5 : ℚ) * (4 / 5) * (3 / 5) = 12 / 125 := by
  norm_num

/-! ## Prop. 71: the marks and the flux -/

/-- **The centred marks:** with `ℓ = P + Q + 1`, `(P − (10/16)ℓ, Q − (5/16)ℓ)` is `M (P, Q)` plus a
constant, so its covariance is `M [[84, 30], [30, 12]] Mᵀ = [[39/16, −45/32], [−45/32, 63/64]]`. -/
theorem marks_centred :
    (!![1 - 10 / 16, -(10 / 16); -(5 / 16), 1 - 5 / 16] : Matrix (Fin 2) (Fin 2) ℚ) *
      (!![84, 30; 30, 12] : Matrix (Fin 2) (Fin 2) ℚ) *
      Matrix.transpose (!![1 - 10 / 16, -(10 / 16); -(5 / 16), 1 - 5 / 16] :
        Matrix (Fin 2) (Fin 2) ℚ) =
      (!![39 / 16, -45 / 32; -45 / 32, 63 / 64] : Matrix (Fin 2) (Fin 2) ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- With `ℓ = P + Q + 1`: `Var ℓ = Var P + Var Q + 2 Cov = 84 + 12 + 60 = 156` (`excursion_variance`), and
the means `(10, 5)` of `plane_visits`, `line_visits` give `E ℓ = 10 + 5 + 1 = 16` (`excursion_mean`). -/
theorem marks_length : (84 : ℚ) + 12 + 2 * 30 = 156 ∧ (10 : ℚ) + 5 + 1 = 16 := by
  norm_num

/-- **`2(m − n) = 48 = n(d − 2)`:** `m = 40` links (`card_edges`), `n = 16` two-spinor states, `d = 5`. -/
theorem flux_count : 2 * (40 - 16) = 48 ∧ 16 * (5 - 2) = 48 := by
  norm_num

/-! ## Prop. 72: the law one level up -/

/-- **The repeated excursion read at the powers of the last-step direction's phase:** with `σ = ±1`,
`(−σu^ℓ)ᵏ = (uᵏ)^ℓ` for even `k` and `−σ(uᵏ)^ℓ` for odd `k`. -/
theorem y_pow (σ : ℤ) (hσ : σ = 1 ∨ σ = -1) (u : ℂ) (ℓ k : ℕ) :
    (-(σ : ℂ) * u ^ ℓ) ^ k = (if Even k then 1 else -(σ : ℂ)) * (u ^ k) ^ ℓ := by
  rw [mul_pow, ← pow_mul, mul_comm ℓ k, pow_mul]
  congr 1
  rcases hσ with rfl | rfl
  · rcases Nat.even_or_odd k with he | ho
    · simp only [he, ↓reduceIte]
      push_cast
      exact he.neg_one_pow
    · have hne : ¬Even k := Nat.not_even_iff_odd.mpr ho
      simp only [hne, ↓reduceIte]
      push_cast
      exact ho.neg_one_pow
  · push_cast
    rw [neg_neg, one_pow]
    split_ifs <;> simp

theorem norm_four_u_pow (k : ℕ) (hk : 1 ≤ k) : ‖(4 : ℂ) * (I / 4) ^ k‖ ≤ 1 := by
  rw [norm_mul, norm_pow, norm_div, Complex.norm_I]
  have h4 : ‖(4 : ℂ)‖ = 4 := by simp
  rw [h4]
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  rw [pow_succ]
  have : (1 / 4 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  nlinarith

/-- **`p_k` for odd `k`:** `Σ_n φ(n)(4uᵏ)ⁿ = Φ(4uᵏ) = −z⁴/(16 + 3z²)` at `z = 4uᵏ`. -/
theorem p_odd (k : ℕ) (hk : 1 ≤ k) :
    HasSum (fun n => (signedLaw n : ℂ) * (4 * (I / 4) ^ k) ^ n)
      (-(4 * (I / 4) ^ k) ^ 4 / (16 + 3 * (4 * (I / 4) ^ k) ^ 2)) :=
  signed_gf _ (norm_four_u_pow k hk)

/-- **`p_k` for even `k`:** `Σ_n f(n)(4uᵏ)ⁿ = F(4uᵏ)`. -/
theorem p_even (k : ℕ) (hk : 1 ≤ k) :
    HasSum (fun n => (excursionLaw n : ℂ) * (4 * (I / 4) ^ k) ^ n)
      ((4 * (I / 4) ^ k) ^ 4 * (1 + 4 * (I / 4) ^ k) /
        (16 - 8 * (4 * (I / 4) ^ k) - 3 * (4 * (I / 4) ^ k) ^ 2 - 3 * (4 * (I / 4) ^ k) ^ 3)) :=
  excursion_gf _ (norm_four_u_pow k hk)

/-- **`p₁ = −Φ(i) = 1/13`.** -/
theorem p_one : HasSum (fun n => -(signedLaw n : ℂ) * (4 * (I / 4)) ^ n) (1 / 13) := by
  have h := Φ_I.neg
  have e : (4 : ℂ) * (I / 4) = I := by ring
  rw [e]
  convert h using 1
  · funext n
    ring
  · norm_num

/-- **`p₂ = F(−1/4) = 1/6096`.** -/
theorem p_two : HasSum (fun n => (excursionLaw n : ℂ) * (4 * (I / 4) ^ 2) ^ n) (1 / 6096) := by
  have hz : (4 : ℂ) * (I / 4) ^ 2 = -1 / 4 := by
    rw [div_pow, Complex.I_sq]
    ring
  rw [hz]
  have hn : ‖(-1 / 4 : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_neg, norm_one]
    have h4 : ‖(4 : ℂ)‖ = 4 := by simp
    rw [h4]
    norm_num
  have h := excursion_gf (-1 / 4) hn
  convert h using 1
  norm_num

end Comparison

end
