import Mathlib

/-!
# Closed intervals for the numbers of the whole table

`Bnd x a b` says `a ≤ x ≤ b`. The combinators carry such intervals through the operations that
compose a row: sums, products, quotients, powers, square roots, rational powers, the exponential,
the logarithm, `π` and the arctangent. Every endpoint is a rational literal, so each side condition
is closed by `norm_num`. The exponential at a rational point is bounded by its Taylor polynomial
(`Real.exp_bound`), the logarithm through the exponential, `π` by Mathlib's twenty digits, and the
arctangent by the alternating partial sums of its series (`Real.hasSum_arctan`).
-/

namespace Comparison.Article

open Real Finset

/-- **`a ≤ x ≤ b`.** -/
def Bnd (x a b : ℝ) : Prop := a ≤ x ∧ x ≤ b

namespace Bnd

variable {x y a b c d : ℝ}

theorem lo (h : Bnd x a b) : a ≤ x := h.1
theorem hi (h : Bnd x a b) : x ≤ b := h.2

theorem const (x : ℝ) : Bnd x x x := ⟨le_rfl, le_rfl⟩

theorem of_eq (h : Bnd x a b) (e : x = y) : Bnd y a b := e ▸ h

theorem weak {a' b' : ℝ} (h : Bnd x a b) (h1 : a' ≤ a) (h2 : b ≤ b') : Bnd x a' b' :=
  ⟨h1.trans h.1, h.2.trans h2⟩

theorem add (h1 : Bnd x a b) (h2 : Bnd y c d) : Bnd (x + y) (a + c) (b + d) :=
  ⟨add_le_add h1.1 h2.1, add_le_add h1.2 h2.2⟩

theorem neg (h : Bnd x a b) : Bnd (-x) (-b) (-a) := ⟨neg_le_neg h.2, neg_le_neg h.1⟩

theorem sub (h1 : Bnd x a b) (h2 : Bnd y c d) : Bnd (x - y) (a - d) (b - c) :=
  ⟨by linarith [h1.1, h2.2], by linarith [h1.2, h2.1]⟩

/-- Products of nonnegative intervals. -/
theorem mul (h1 : Bnd x a b) (h2 : Bnd y c d) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    Bnd (x * y) (a * c) (b * d) :=
  ⟨mul_le_mul h1.1 h2.1 hc (ha.trans h1.1),
    mul_le_mul h1.2 h2.2 (hc.trans h2.1) ((ha.trans h1.1).trans h1.2)⟩

/-- A nonnegative interval times a nonpositive one. -/
theorem mul_neg (h1 : Bnd x a b) (h2 : Bnd y c d) (ha : 0 ≤ a) (hd : d ≤ 0) :
    Bnd (x * y) (b * c) (a * d) := by
  have h := mul h1 (neg h2) ha (by linarith)
  refine ⟨?_, ?_⟩
  · have := h.2
    nlinarith [h.2]
  · have := h.1
    nlinarith [h.1]

/-- A nonpositive interval times a nonnegative one. -/
theorem neg_mul (h1 : Bnd x a b) (h2 : Bnd y c d) (hb : b ≤ 0) (hc : 0 ≤ c) :
    Bnd (x * y) (a * d) (b * c) := by
  have h := mul (neg h1) h2 (by linarith) hc
  constructor
  · nlinarith [h.2]
  · nlinarith [h.1]

/-- Two nonpositive intervals. -/
theorem neg_mul_neg (h1 : Bnd x a b) (h2 : Bnd y c d) (hb : b ≤ 0) (hd : d ≤ 0) :
    Bnd (x * y) (b * d) (a * c) := by
  have h := mul (neg h1) (neg h2) (by linarith) (by linarith)
  constructor
  · nlinarith [h.1]
  · nlinarith [h.2]

theorem smul_const (h : Bnd x a b) {k : ℝ} (hk : 0 ≤ k) : Bnd (k * x) (k * a) (k * b) :=
  ⟨mul_le_mul_of_nonneg_left h.1 hk, mul_le_mul_of_nonneg_left h.2 hk⟩

theorem inv (h : Bnd x a b) (ha : 0 < a) : Bnd x⁻¹ b⁻¹ a⁻¹ :=
  ⟨inv_anti₀ (ha.trans_le h.1) h.2, inv_anti₀ ha h.1⟩

theorem div (h1 : Bnd x a b) (h2 : Bnd y c d) (ha : 0 ≤ a) (hc : 0 < c) :
    Bnd (x / y) (a / d) (b / c) := by
  have hi := inv h2 hc
  have := mul h1 hi ha (inv_nonneg.mpr ((hc.le.trans h2.1).trans h2.2))
  simpa [div_eq_mul_inv] using this

/-- A nonpositive numerator over a positive denominator. -/
theorem div_negnum (h1 : Bnd x a b) (h2 : Bnd y c d) (hb : b ≤ 0) (hc : 0 < c) :
    Bnd (x / y) (a / c) (b / d) := by
  have h := div (neg h1) h2 (by linarith) hc
  constructor
  · have := h.2
    rw [neg_div, neg_div] at this
    linarith
  · have := h.1
    rw [neg_div, neg_div] at this
    linarith

theorem pow (h : Bnd x a b) (ha : 0 ≤ a) (n : ℕ) : Bnd (x ^ n) (a ^ n) (b ^ n) :=
  ⟨pow_le_pow_left₀ ha h.1 n, pow_le_pow_left₀ (ha.trans h.1) h.2 n⟩

/-- **Square roots.** -/
theorem sqrt (h : Bnd x a b) {l u : ℝ} (hl : 0 ≤ l) (h1 : l ^ 2 ≤ a) (h2 : b ≤ u ^ 2) (hu : 0 ≤ u) :
    Bnd (√x) l u :=
  ⟨(Real.le_sqrt hl ((sq_nonneg l).trans (h1.trans h.1))).mpr (h1.trans h.1),
    (Real.sqrt_le_left hu).mpr (h.2.trans h2)⟩

/-- **Rational powers** `x^(p/q)` with `p, q > 0`. -/
theorem rpow (h : Bnd x a b) (ha : 0 ≤ a) {p q : ℕ} (hq : 0 < q) {l u : ℝ} (hl : 0 ≤ l)
    (hu : 0 ≤ u) (h1 : l ^ q ≤ a ^ p) (h2 : b ^ p ≤ u ^ q) :
    Bnd (x ^ ((p : ℝ) / q)) l u := by
  have hx : 0 ≤ x := ha.trans h.1
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have key : ∀ t : ℝ, 0 ≤ t → t ^ ((p : ℝ) / q) = (t ^ p) ^ ((q : ℝ)⁻¹) := by
    intro t ht
    rw [div_eq_mul_inv, Real.rpow_mul ht, Real.rpow_natCast]
  have hinv : (0 : ℝ) < (q : ℝ)⁻¹ := by positivity
  constructor
  · have e : l = (l ^ q) ^ ((q : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hl hq.ne').symm
    rw [key x hx, e]
    exact Real.rpow_le_rpow (by positivity) (h1.trans (pow_le_pow_left₀ ha h.1 p)) hinv.le
  · have e : u = (u ^ q) ^ ((q : ℝ)⁻¹) := (Real.pow_rpow_inv_natCast hu hq.ne').symm
    rw [key x hx, e]
    exact Real.rpow_le_rpow (by positivity) ((pow_le_pow_left₀ hx h.2 p).trans h2) hinv.le

/-- **Negative rational powers** `x^(-(p/q))`. -/
theorem rpow_neg (h : Bnd x a b) (ha : 0 < a) {p q : ℕ} (hq : 0 < q) {l u : ℝ} (hl : 0 < l)
    (hu : 0 ≤ u) (h1 : l ^ q ≤ a ^ p) (h2 : b ^ p ≤ u ^ q) :
    Bnd (x ^ (-((p : ℝ) / q))) u⁻¹ l⁻¹ := by
  have hb := rpow h ha.le hq hl.le hu h1 h2
  rw [Real.rpow_neg (ha.le.trans h.1)]
  exact inv hb hl

/-- **The exponential** is increasing. -/
theorem exp (h : Bnd x a b) {l u : ℝ} (h1 : l ≤ Real.exp a) (h2 : Real.exp b ≤ u) :
    Bnd (Real.exp x) l u :=
  ⟨h1.trans (Real.exp_le_exp.mpr h.1), (Real.exp_le_exp.mpr h.2).trans h2⟩

/-- **The logarithm** through the exponential. -/
theorem log (h : Bnd x a b) (ha : 0 < a) {l u : ℝ} (h1 : Real.exp l ≤ a) (h2 : b ≤ Real.exp u) :
    Bnd (Real.log x) l u := by
  have hx : 0 < x := ha.trans_le h.1
  constructor
  · rw [Real.le_log_iff_exp_le hx]
    exact h1.trans h.1
  · rw [Real.log_le_iff_le_exp hx]
    exact h.2.trans h2

end Bnd

/-! ## The exponential at a point, by its Taylor polynomial -/

/-- The Taylor polynomial of `exp` with `n` terms. -/
noncomputable def expPoly (x : ℝ) (n : ℕ) : ℝ := ∑ m ∈ range n, x ^ m / m.factorial

/-- Its error bound, `|x|ⁿ (n + 1)/(n! n)`. -/
noncomputable def expErr (x : ℝ) (n : ℕ) : ℝ := |x| ^ n * ((n.succ : ℝ) / (n.factorial * n))

theorem exp_near (x : ℝ) (n : ℕ) (hn : 0 < n) (hx : |x| ≤ 1) :
    |Real.exp x - expPoly x n| ≤ expErr x n :=
  Real.exp_bound hx hn

theorem exp_ge (x l : ℝ) (n : ℕ) (hn : 0 < n) (hx : |x| ≤ 1) (h : l ≤ expPoly x n - expErr x n) :
    l ≤ Real.exp x := by
  have := exp_near x n hn hx
  rw [abs_le] at this
  linarith [this.1]

theorem exp_le (x u : ℝ) (n : ℕ) (hn : 0 < n) (hx : |x| ≤ 1) (h : expPoly x n + expErr x n ≤ u) :
    Real.exp x ≤ u := by
  have := exp_near x n hn hx
  rw [abs_le] at this
  linarith [this.2]

/-- `exp (k * x) = (exp x) ^ k`: an argument beyond one is split into equal parts. -/
theorem exp_ge_pow (x l : ℝ) (k : ℕ) (hl : 0 ≤ l) (h : l ≤ Real.exp (x / k)) (hk : 0 < k) :
    l ^ k ≤ Real.exp x := by
  have e : Real.exp x = Real.exp (x / k) ^ k := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [e]
  exact pow_le_pow_left₀ hl h k

theorem exp_le_pow (x u : ℝ) (k : ℕ) (h : Real.exp (x / k) ≤ u) (hk : 0 < k) :
    Real.exp x ≤ u ^ k := by
  have e : Real.exp x = Real.exp (x / k) ^ k := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [e]
  exact pow_le_pow_left₀ (Real.exp_pos _).le h k

/-- **The exponential at a point:** `Bnd (exp x) l u` from the Taylor polynomial. -/
theorem bnd_exp (x l u : ℝ) (n : ℕ) (hn : 0 < n) (hx : |x| ≤ 1)
    (h1 : l ≤ expPoly x n - expErr x n) (h2 : expPoly x n + expErr x n ≤ u) :
    Bnd (Real.exp x) l u :=
  ⟨exp_ge x l n hn hx h1, exp_le x u n hn hx h2⟩

/-! ## `π` -/

theorem bnd_pi : Bnd π 3.14159265358979323846 3.14159265358979323847 :=
  ⟨Real.pi_gt_d20.le, Real.pi_lt_d20.le⟩

/-! ## The arctangent by its alternating series -/

/-- The partial sums of the arctangent series. -/
noncomputable def atanPoly (x : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range n, (-1) ^ i * (x ^ (2 * i + 1) / (2 * i + 1))

theorem atan_terms_antitone {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Antitone (fun i : ℕ => x ^ (2 * i + 1) / (2 * i + 1)) := by
  refine antitone_nat_of_succ_le (fun i => ?_)
  have hx2 : x ^ (2 * (i + 1) + 1) ≤ x ^ (2 * i + 1) :=
    pow_le_pow_of_le_one h0 h1 (by omega)
  have hpos : (0 : ℝ) < 2 * i + 1 := by positivity
  have hpos' : (0 : ℝ) < 2 * ((i + 1 : ℕ) : ℝ) + 1 := by positivity
  push_cast at hpos' ⊢
  rw [div_le_div_iff₀ (by positivity) hpos]
  have hxn : 0 ≤ x ^ (2 * (i + 1) + 1) := pow_nonneg h0 _
  nlinarith

theorem atan_tendsto {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) :
    Filter.Tendsto (fun n => ∑ i ∈ range n, (-1) ^ i * (x ^ (2 * i + 1) / (2 * i + 1)))
      Filter.atTop (nhds (Real.arctan x)) := by
  have hs := Real.hasSum_arctan (x := x) (by rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1)
  have := hs.tendsto_sum_nat
  convert this using 2 with n
  refine Finset.sum_congr rfl (fun i _ => ?_)
  push_cast
  ring

/-- **The arctangent between two partial sums:** `S_{2k} ≤ arctan x ≤ S_{2k+1}` on `[0, 1)`. -/
theorem atan_between {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (k : ℕ) :
    atanPoly x (2 * k) ≤ Real.arctan x ∧ Real.arctan x ≤ atanPoly x (2 * k + 1) := by
  have ht := atan_tendsto h0 h1
  have ha := atan_terms_antitone h0 h1.le
  exact ⟨Antitone.alternating_series_le_tendsto ht ha k,
    Antitone.tendsto_le_alternating_series ht ha k⟩

theorem bnd_arctan (x l u : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) (k : ℕ)
    (hl : l ≤ atanPoly x (2 * k)) (hu : atanPoly x (2 * k + 1) ≤ u) : Bnd (Real.arctan x) l u :=
  ⟨hl.trans (atan_between h0 h1 k).1, (atan_between h0 h1 k).2.trans hu⟩

/-- The arctangent of an interval inside `[0, 1)`. -/
theorem Bnd.arctan {x a b : ℝ} (h : Bnd x a b) {l u : ℝ} (h1 : l ≤ Real.arctan a)
    (h2 : Real.arctan b ≤ u) : Bnd (Real.arctan x) l u :=
  ⟨h1.trans (Real.arctan_le_arctan_iff.mpr h.1), (Real.arctan_le_arctan_iff.mpr h.2).trans h2⟩

theorem atan_ge (x l : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) (k : ℕ) (hl : l ≤ atanPoly x (2 * k)) :
    l ≤ Real.arctan x :=
  hl.trans (atan_between h0 h1 k).1

theorem atan_le (x u : ℝ) (h0 : 0 ≤ x) (h1 : x < 1) (k : ℕ) (hu : atanPoly x (2 * k + 1) ≤ u) :
    Real.arctan x ≤ u :=
  (atan_between h0 h1 k).2.trans hu

/-! ## Forms the generator of the rows uses -/

/-- The exponential at a point with `|x|` named. -/
theorem bnd_exp' (x a l u : ℝ) (n : ℕ) (hn : 0 < n) (ha : |x| = a) (ha1 : a ≤ 1)
    (h1 : l ≤ expPoly x n - a ^ n * ((n.succ : ℝ) / (n.factorial * n)))
    (h2 : expPoly x n + a ^ n * ((n.succ : ℝ) / (n.factorial * n)) ≤ u) :
    Bnd (Real.exp x) l u := by
  refine bnd_exp x l u n hn (ha ▸ ha1) ?_ ?_
  · rw [expErr, ha]; exact h1
  · rw [expErr, ha]; exact h2

theorem exp_ge' (x a l : ℝ) (n : ℕ) (hn : 0 < n) (ha : |x| = a) (ha1 : a ≤ 1)
    (h : l ≤ expPoly x n - a ^ n * ((n.succ : ℝ) / (n.factorial * n))) : l ≤ Real.exp x :=
  exp_ge x l n hn (ha ▸ ha1) (by rw [expErr, ha]; exact h)

theorem exp_le' (x a u : ℝ) (n : ℕ) (hn : 0 < n) (ha : |x| = a) (ha1 : a ≤ 1)
    (h : expPoly x n + a ^ n * ((n.succ : ℝ) / (n.factorial * n)) ≤ u) : Real.exp x ≤ u :=
  exp_le x u n hn (ha ▸ ha1) (by rw [expErr, ha]; exact h)

/-- `exp x = (exp xs)^k` for `x = k xs`: the lower bound. -/
theorem exp_ge_split (x xs l L : ℝ) (k : ℕ) (hx : x = k * xs) (hl : 0 ≤ l) (h : l ≤ Real.exp xs)
    (hL : L ≤ l ^ k) : L ≤ Real.exp x := by
  rw [hx, Real.exp_nat_mul]
  exact hL.trans (pow_le_pow_left₀ hl h k)

/-- `exp x = (exp xs)^k` for `x = k xs`: the upper bound. -/
theorem exp_le_split (x xs u U : ℝ) (k : ℕ) (hx : x = k * xs) (h : Real.exp xs ≤ u)
    (hU : u ^ k ≤ U) : Real.exp x ≤ U := by
  rw [hx, Real.exp_nat_mul]
  exact (pow_le_pow_left₀ (Real.exp_pos _).le h k).trans hU

/-- Rational powers with the exponent written as a real number `r = p/q`. -/
theorem Bnd.rpow' {x a b : ℝ} (h : Bnd x a b) (ha : 0 ≤ a) {r : ℝ} {p q : ℕ} (hr : r = p / q)
    (hq : 0 < q) {l u : ℝ} (hl : 0 ≤ l) (hu : 0 ≤ u) (h1 : l ^ q ≤ a ^ p) (h2 : b ^ p ≤ u ^ q) :
    Bnd (x ^ r) l u := by
  rw [hr]
  exact Bnd.rpow h ha hq hl hu h1 h2

/-- Negative rational powers with the exponent written as a real number `r = -(p/q)`. -/
theorem Bnd.rpow_neg' {x a b : ℝ} (h : Bnd x a b) (ha : 0 < a) {r : ℝ} {p q : ℕ}
    (hr : r = -((p : ℝ) / q)) (hq : 0 < q) {l u : ℝ} (hl : 0 < l) (hu : 0 ≤ u)
    (h1 : l ^ q ≤ a ^ p) (h2 : b ^ p ≤ u ^ q) : Bnd (x ^ r) u⁻¹ l⁻¹ := by
  rw [hr]
  exact Bnd.rpow_neg h ha hq hl hu h1 h2

/-- The strict form the rows print: `lo < x < hi` from a closed interval inside. -/
theorem Bnd.strict {x a b lo hi : ℝ} (h : Bnd x a b) (h1 : lo < a) (h2 : b < hi) :
    lo < x ∧ x < hi :=
  ⟨h1.trans_le h.1, h.2.trans_lt h2⟩

/-! ## A check of the machinery -/

example : Bnd (Real.exp (-(9 / 56))) 0.8515353 0.8515354 := by
  refine bnd_exp _ _ _ 12 (by norm_num) (by norm_num [abs_of_neg]) ?_ ?_ <;>
    norm_num [expPoly, expErr, Finset.sum_range_succ, Nat.factorial, abs_of_neg]

example : Bnd (Real.arctan (7 / 16)) 0.41241044 0.41241045 := by
  refine bnd_arctan _ _ _ (by norm_num) (by norm_num) 8 ?_ ?_ <;>
    norm_num [atanPoly, Finset.sum_range_succ]

end Comparison.Article
