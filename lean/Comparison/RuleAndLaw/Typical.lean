import Comparison.Mass.Angle

/-!
# The typical rate (Proposition 204, the matrix part)

Book XXIV's Proposition 204: a bound state is one walk, and along one walk of
the stationary walk a weight averages to its first-order rate. Book XXIV's paragraph *For Lean* asks for
the ergodic statement of this finite walk in its matrix form: the Cesàro mean of the step's powers
tends to the stationary projector. With `P = B/4` on the eighty states (`lawP`):

* `fwd_exact_five`: **every state is reached from `(∅, 0)` in exactly five steps** (by `decide`);
  `lawP_pow_lower`: so `(P⁵)_{x, (∅,0)} ≥ 4⁻⁵` for every `x` (a Doeblin minorization on one column).
* `avg_bounds`, `doeblin_bounds`: a nonnegative matrix with unit row sums keeps every bound of a
  function, and one with a column at least `δ` shrinks its spread by `1 − δ`; `mean_lawP`: `P` keeps the
  sum of a function (its columns sum to one: the uniform law is stationary).
* `rate_bound`: **`|(Pⁿ f)(x) − f̄| ≤ (1 − 4⁻⁵)^⌊n/5⌋ (M − m)`** for every `f` with values in `[m, M]`,
  `f̄` its mean over the eighty states;
* `law_pow_rate`, `law_pow_tendsto`: **`(Pⁿ)_{xy} → 1/80`** at that rate, for every `x`, `y`;
* `law_cesaro`: **the Cesàro mean `(1/N) Σ_{n<N} (Pⁿ)_{xy}` tends to `1/80`**: the stationary
  projector; `weight_cesaro`: for every weight `g` on the states, the mean of `Pⁿ g` along the walk tends
  to its stationary mean `ḡ`, from every start: the first-order rate.

The almost-sure statement along a single walk (the ergodic theorem for a finite irreducible
chain) is not in Mathlib and is not proved here.
-/

open Comparison Matrix Filter Topology

namespace Comparison.RuleAndLaw

/-! ## Exactly five steps reach every state -/

/-- The states reached from `S` by one more step. -/
def fwdExact (S : Finset State) : Finset State :=
  Finset.univ.filter (fun t => ∃ a ∈ preds t, a ∈ S)

/-- **Every state is reached from `(∅, 0)` in exactly five steps.** -/
theorem fwd_exact_five : fwdExact^[5] {((0 : Fin 16), (0 : Fin 5))} = Finset.univ := by
  decide +kernel

theorem lawP_apply (x z : State) : lawP x z = if Continues z x then 1 / 4 else 0 := by
  simp only [lawP, Matrix.smul_apply, stepR, stepT, Matrix.of_apply, smul_eq_mul]
  split_ifs <;> norm_num

theorem lawP_nonneg (x y : State) : 0 ≤ lawP x y := by
  rw [lawP_apply]
  split_ifs <;> norm_num

theorem lawP_pow_nonneg (n : ℕ) (x y : State) : 0 ≤ (lawP ^ n) x y := by
  induction n generalizing x y with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    exact Finset.sum_nonneg fun z _ => mul_nonneg (lawP_nonneg x z) (ih z y)

/-- **A state reached in exactly `k` steps from `y` has `(Pᵏ)_{xy} ≥ 4⁻ᵏ`.** -/
theorem lawP_pow_lower (k : ℕ) (y : State) :
    ∀ x, x ∈ fwdExact^[k] {y} → (1 / 4 : ℝ) ^ k ≤ (lawP ^ k) x y := by
  induction k with
  | zero =>
    intro x hx
    simp only [Function.iterate_zero, id_eq, Finset.mem_singleton] at hx
    subst hx
    simp
  | succ k ih =>
    intro x hx
    rw [Function.iterate_succ_apply'] at hx
    simp only [fwdExact, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨z, hz, hzk⟩ := hx
    rw [mem_preds] at hz
    rw [pow_succ' lawP k, Matrix.mul_apply]
    have hzx : lawP x z = 1 / 4 := by rw [lawP_apply]; simp [hz]
    calc (1 / 4 : ℝ) ^ (k + 1) = lawP x z * (1 / 4) ^ k := by rw [hzx]; ring
      _ ≤ lawP x z * (lawP ^ k) z y := mul_le_mul_of_nonneg_left (ih z hzk) (lawP_nonneg x z)
      _ ≤ ∑ w, lawP x w * (lawP ^ k) w y :=
        Finset.single_le_sum (fun w _ => mul_nonneg (lawP_nonneg x w) (lawP_pow_nonneg k w y))
          (Finset.mem_univ z)

/-! ## Rows and columns of the step -/

theorem lawP_row (x : State) : ∑ y, lawP x y = 1 := by
  simp only [lawP_apply]
  rw [← Finset.sum_filter]
  have : (Finset.univ.filter fun y => Continues y x) = predSet x := rfl
  rw [this, Finset.sum_const, card_predSet]
  norm_num

theorem lawP_col (y : State) : ∑ x, lawP x y = 1 := by
  simp only [lawP_apply]
  rw [← Finset.sum_filter]
  have : (Finset.univ.filter fun x => Continues y x) = succSet y := rfl
  rw [this, Finset.sum_const, card_succSet]
  norm_num

theorem lawP_pow_row (n : ℕ) (x : State) : ∑ y, (lawP ^ n) x y = 1 := by
  induction n generalizing x with
  | zero =>
    simp [Matrix.one_apply]
  | succ n ih =>
    simp only [pow_succ', Matrix.mul_apply]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, ih, mul_one]
    exact lawP_row x

/-- **`P` keeps the sum of a function**: the uniform law is stationary. -/
theorem mean_lawP (f : State → ℝ) : ∑ x, (lawP *ᵥ f) x = ∑ x, f x := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, lawP_col, one_mul]

/-! ## Bounds kept and spread shrunk -/

theorem avg_bounds (Q : Matrix State State ℝ) (hQ : ∀ x y, 0 ≤ Q x y) (hrow : ∀ x, ∑ y, Q x y = 1)
    (f : State → ℝ) (m M : ℝ) (hf : ∀ y, m ≤ f y ∧ f y ≤ M) (x : State) :
    m ≤ (Q *ᵥ f) x ∧ (Q *ᵥ f) x ≤ M := by
  simp only [Matrix.mulVec, dotProduct]
  constructor
  · calc m = ∑ y, Q x y * m := by rw [← Finset.sum_mul, hrow, one_mul]
      _ ≤ ∑ y, Q x y * f y := Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hf y).1 (hQ x y)
  · calc ∑ y, Q x y * f y ≤ ∑ y, Q x y * M :=
          Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hf y).2 (hQ x y)
      _ = M := by rw [← Finset.sum_mul, hrow, one_mul]

/-- **Doeblin:** a column at least `δ` shrinks the spread of every function by `1 − δ`. -/
theorem doeblin_bounds (Q : Matrix State State ℝ) (hQ : ∀ x y, 0 ≤ Q x y)
    (hrow : ∀ x, ∑ y, Q x y = 1) (y₀ : State) (δ : ℝ) (hδ : ∀ x, δ ≤ Q x y₀) (f : State → ℝ)
    (m M : ℝ) (hf : ∀ y, m ≤ f y ∧ f y ≤ M) (x : State) :
    δ * f y₀ + (1 - δ) * m ≤ (Q *ᵥ f) x ∧ (Q *ᵥ f) x ≤ δ * f y₀ + (1 - δ) * M := by
  set c : State → ℝ := fun y => Q x y - δ * (if y = y₀ then 1 else 0) with hc
  have hc0 : ∀ y, 0 ≤ c y := by
    intro y
    simp only [hc]
    split_ifs with h
    · subst h
      linarith [hδ x]
    · linarith [hQ x y]
  have hcs : ∑ y, c y = 1 - δ := by
    simp only [hc, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, hrow]
    ring
  have hsplit : (Q *ᵥ f) x = δ * f y₀ + ∑ y, c y * f y := by
    simp only [Matrix.mulVec, dotProduct, hc, sub_mul, Finset.sum_sub_distrib, mul_assoc,
      ← Finset.mul_sum, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  rw [hsplit]
  constructor
  · have : (1 - δ) * m ≤ ∑ y, c y * f y := by
      calc (1 - δ) * m = ∑ y, c y * m := by rw [← Finset.sum_mul, hcs]
        _ ≤ ∑ y, c y * f y := Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hf y).1 (hc0 y)
    linarith
  · have : ∑ y, c y * f y ≤ (1 - δ) * M := by
      calc ∑ y, c y * f y ≤ ∑ y, c y * M :=
            Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (hf y).2 (hc0 y)
        _ = (1 - δ) * M := by rw [← Finset.sum_mul, hcs]
    linarith

/-! ## The rate -/

/-- The mean of a function over the eighty states. -/
noncomputable def meanS (f : State → ℝ) : ℝ := (1 / 80) * ∑ x, f x

theorem meanS_bounds (f : State → ℝ) (m M : ℝ) (hf : ∀ y, m ≤ f y ∧ f y ≤ M) :
    m ≤ meanS f ∧ meanS f ≤ M := by
  have hcard : (Finset.univ : Finset State).card = 80 := by decide
  constructor
  · have : ∑ _x : State, m ≤ ∑ x, f x := Finset.sum_le_sum fun x _ => (hf x).1
    rw [Finset.sum_const, hcard, nsmul_eq_mul] at this
    push_cast at this
    unfold meanS
    linarith
  · have : ∑ x, f x ≤ ∑ _x : State, M := Finset.sum_le_sum fun x _ => (hf x).2
    rw [Finset.sum_const, hcard, nsmul_eq_mul] at this
    push_cast at this
    unfold meanS
    linarith

theorem meanS_lawP_pow (n : ℕ) (f : State → ℝ) : meanS ((lawP ^ n) *ᵥ f) = meanS f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, meanS, mean_lawP, ← meanS, ih]

theorem pow_bounds (n : ℕ) (f : State → ℝ) (m M : ℝ) (hf : ∀ y, m ≤ f y ∧ f y ≤ M) (x : State) :
    m ≤ ((lawP ^ n) *ᵥ f) x ∧ ((lawP ^ n) *ᵥ f) x ≤ M :=
  avg_bounds (lawP ^ n) (lawP_pow_nonneg n) (lawP_pow_row n) f m M hf x

/-- The Doeblin constant of five steps, `δ = 4⁻⁵`. -/
noncomputable def δ5 : ℝ := (1 / 4) ^ 5

theorem five_lower (x : State) : δ5 ≤ (lawP ^ 5) x ((0 : Fin 16), (0 : Fin 5)) :=
  lawP_pow_lower 5 _ x (by rw [fwd_exact_five]; exact Finset.mem_univ x)

/-- **Five steps shrink the spread by `1 − 4⁻⁵`, `j` times.** -/
theorem spread_bound (j : ℕ) : ∀ (f : State → ℝ) (m M : ℝ), (∀ y, m ≤ f y ∧ f y ≤ M) →
    ∀ x, |((lawP ^ (5 * j)) *ᵥ f) x - meanS f| ≤ (1 - δ5) ^ j * (M - m) := by
  induction j with
  | zero =>
    intro f m M hf x
    simp only [mul_zero, pow_zero, Matrix.one_mulVec, one_mul]
    have h1 := hf x
    have h2 := meanS_bounds f m M hf
    rw [abs_le]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  | succ j ih =>
    intro f m M hf x
    set g := (lawP ^ 5) *ᵥ f with hg
    have hgb : ∀ y, δ5 * f ((0 : Fin 16), (0 : Fin 5)) + (1 - δ5) * m ≤ g y ∧
        g y ≤ δ5 * f ((0 : Fin 16), (0 : Fin 5)) + (1 - δ5) * M :=
      fun y => doeblin_bounds (lawP ^ 5) (lawP_pow_nonneg 5) (lawP_pow_row 5) _ δ5 five_lower f m M
        hf y
    have hmean : meanS g = meanS f := meanS_lawP_pow 5 f
    have hpow : (lawP ^ (5 * (j + 1))) *ᵥ f = (lawP ^ (5 * j)) *ᵥ g := by
      rw [hg, Matrix.mulVec_mulVec, ← pow_add, show 5 * j + 5 = 5 * (j + 1) by ring]
    rw [hpow, ← hmean]
    calc |((lawP ^ (5 * j)) *ᵥ g) x - meanS g|
        ≤ (1 - δ5) ^ j * ((δ5 * f ((0 : Fin 16), (0 : Fin 5)) + (1 - δ5) * M) -
          (δ5 * f ((0 : Fin 16), (0 : Fin 5)) + (1 - δ5) * m)) := ih g _ _ hgb x
      _ = (1 - δ5) ^ (j + 1) * (M - m) := by ring

/-- **The rate:** `|(Pⁿ f)(x) − f̄| ≤ (1 − 4⁻⁵)^⌊n/5⌋ (M − m)`. -/
theorem rate_bound (n : ℕ) (f : State → ℝ) (m M : ℝ) (hf : ∀ y, m ≤ f y ∧ f y ≤ M) (x : State) :
    |((lawP ^ n) *ᵥ f) x - meanS f| ≤ (1 - δ5) ^ (n / 5) * (M - m) := by
  have hn : n = 5 * (n / 5) + n % 5 := (Nat.div_add_mod n 5).symm
  have hsplit : (lawP ^ n) *ᵥ f = (lawP ^ (5 * (n / 5))) *ᵥ ((lawP ^ (n % 5)) *ᵥ f) := by
    rw [Matrix.mulVec_mulVec, ← pow_add, ← hn]
  rw [hsplit, ← meanS_lawP_pow (n % 5) f]
  exact spread_bound (n / 5) _ m M (pow_bounds (n % 5) f m M hf) x

theorem mulVec_single (n : ℕ) (x y : State) :
    ((lawP ^ n) *ᵥ Pi.single y 1) x = (lawP ^ n) x y := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

theorem meanS_single (y : State) : meanS (Pi.single y 1) = 1 / 80 := by
  simp [meanS, Pi.single_apply]

/-- **`|(Pⁿ)_{xy} − 1/80| ≤ (1 − 4⁻⁵)^⌊n/5⌋`.** -/
theorem law_pow_rate (n : ℕ) (x y : State) : |(lawP ^ n) x y - 1 / 80| ≤ (1 - δ5) ^ (n / 5) := by
  have h := rate_bound n (Pi.single y 1) 0 1 (fun z => by
    by_cases hz : z = y
    · subst hz; simp
    · simp [hz]) x
  rw [mulVec_single, meanS_single, sub_zero, mul_one] at h
  exact h

theorem δ5_lt : 0 ≤ 1 - δ5 ∧ 1 - δ5 < 1 := by
  unfold δ5
  constructor <;> norm_num

theorem tendsto_rate : Tendsto (fun n : ℕ => (1 - δ5) ^ (n / 5)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => n / 5) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨5 * b, fun n hn => by omega⟩
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one δ5_lt.1 δ5_lt.2).comp h1

/-- **`(Pⁿ)_{xy} → 1/80`: the step's powers tend to the stationary projector.** -/
theorem law_pow_tendsto (x y : State) : Tendsto (fun n => (lawP ^ n) x y) atTop (𝓝 (1 / 80)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) tendsto_rate
  rw [Real.dist_eq]
  exact law_pow_rate n x y

/-- **The Cesàro mean of the step's powers tends to the stationary projector** (Proposition 204's
matrix statement, Book XXIV's paragraph *For Lean*). -/
theorem law_cesaro (x y : State) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, (lawP ^ n) x y) atTop (𝓝 (1 / 80)) :=
  (law_pow_tendsto x y).cesaro

/-- **Every weight on the states averages to its stationary mean along the walk, from every start.** -/
theorem weight_cesaro (g : State → ℝ) (x : State) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ((lawP ^ n) *ᵥ g) x) atTop
      (𝓝 (meanS g)) := by
  have hb : ∃ B, ∀ y, -B ≤ g y ∧ g y ≤ B := by
    refine ⟨∑ y, |g y|, fun y => ?_⟩
    have := Finset.single_le_sum (fun z _ => abs_nonneg (g z)) (Finset.mem_univ y)
    constructor <;> linarith [neg_abs_le (g y), le_abs_self (g y)]
  obtain ⟨B, hB⟩ := hb
  have ht : Tendsto (fun n => ((lawP ^ n) *ᵥ g) x) atTop (𝓝 (meanS g)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    have hr : Tendsto (fun n : ℕ => (1 - δ5) ^ (n / 5) * (B - -B)) atTop (𝓝 0) := by
      simpa using tendsto_rate.mul_const (B - -B)
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) hr
    rw [Real.dist_eq]
    exact rate_bound n g (-B) B hB x
  exact ht.cesaro

end Comparison.RuleAndLaw

#print axioms Comparison.RuleAndLaw.fwd_exact_five
#print axioms Comparison.RuleAndLaw.lawP_apply
#print axioms Comparison.RuleAndLaw.lawP_nonneg
#print axioms Comparison.RuleAndLaw.lawP_pow_nonneg
#print axioms Comparison.RuleAndLaw.lawP_pow_lower
#print axioms Comparison.RuleAndLaw.lawP_row
#print axioms Comparison.RuleAndLaw.lawP_col
#print axioms Comparison.RuleAndLaw.lawP_pow_row
#print axioms Comparison.RuleAndLaw.mean_lawP
#print axioms Comparison.RuleAndLaw.avg_bounds
#print axioms Comparison.RuleAndLaw.doeblin_bounds
#print axioms Comparison.RuleAndLaw.meanS_bounds
#print axioms Comparison.RuleAndLaw.meanS_lawP_pow
#print axioms Comparison.RuleAndLaw.pow_bounds
#print axioms Comparison.RuleAndLaw.five_lower
#print axioms Comparison.RuleAndLaw.spread_bound
#print axioms Comparison.RuleAndLaw.rate_bound
#print axioms Comparison.RuleAndLaw.mulVec_single
#print axioms Comparison.RuleAndLaw.meanS_single
#print axioms Comparison.RuleAndLaw.law_pow_rate
#print axioms Comparison.RuleAndLaw.δ5_lt
#print axioms Comparison.RuleAndLaw.tendsto_rate
#print axioms Comparison.RuleAndLaw.law_pow_tendsto
#print axioms Comparison.RuleAndLaw.law_cesaro
#print axioms Comparison.RuleAndLaw.weight_cesaro
