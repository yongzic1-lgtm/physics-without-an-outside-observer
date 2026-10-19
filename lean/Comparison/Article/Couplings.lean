import Comparison.Article.Clock
import Comparison.Law.Rows

/-!
# The clock as the law composes it, the repeated return at the clock, and the electric coupling

* `clockMQ_plus`, `clockMQ_minus`, `hOv_eq`: **the clock of `Law/Rows.lean` at its divided set `{h, n}` is the
  generated `qMQp`, `qMQm`, and the overlap `h_{h,n} = qH`** (Proposition 206 as the law composes it).
* `NhOf h = Σ_{k ≥ 1} hᵏ p_k` (Proposition 72 at the clock); `NhOf_bnd`: two-sided bounds from the first
  `K` returns and the geometric tail `p_k ≤ (1/10)(1/256)^{k-1}`; `qNh = NhOf qH` and `qNh_bnd`.
* `N1_eq_NhOf_one`: `N(1)` of `Mass/Return72.lean` is `NhOf 1`.
-/

namespace Comparison.Article

open Real Finset Comparison.Law

/-! ## The clock at `{h, n}` as `Law/Rows.lean` composes it -/

theorem clockMQ_plus : clockMQ sLastDirectionSinglet (9 / 4000) = qMQp := by
  rw [clockMQ, qMQp, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_one]
  simp only [clockGap_hn]
  norm_num
  ring

theorem clockMQ_minus : clockMQ sLastDirectionSinglet (-(9 / 4000)) = qMQm := by
  rw [clockMQ, qMQm, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Fin.sum_univ_one]
  simp only [clockGap_hn]
  norm_num
  ring

/-- **The overlap of the clock's two signs is `qH`.** -/
theorem hOv_eq : hOv sLastDirectionSinglet = qH := by
  rw [piece_h, clockMQ_plus, clockMQ_minus, qH]

theorem qH_pos : 0 < qH := lt_of_lt_of_le (by norm_num) qH_bnd.1

theorem qH_le_one : qH ≤ 1 := le_trans qH_bnd.2 (by norm_num)

/-! ## The repeated return at the clock (Proposition 72) -/

/-- **`N(h) = Σ_{k ≥ 1} hᵏ p_k`.** -/
noncomputable def NhOf (h : ℝ) : ℝ := ∑' k : ℕ, h ^ (k + 1) * repR (k + 1)

theorem repR_tail_le (k : ℕ) : repR (k + 1) ≤ (1 / 10) * (1 / 256) ^ k ∨ k = 0 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · exact Or.inr hk
  · left
    have := (repR_bound (k + 1) (by omega)).2
    rwa [show k + 1 - 1 = k by omega] at this

theorem NhOf_summable {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    Summable (fun k : ℕ => h ^ (k + 1) * repR (k + 1)) := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (pow_nonneg h0 _) (repR_pos _ (by omega)).le)
    (fun k => ?_) repR_summable
  have hp := (repR_pos (k + 1) (by omega)).le
  have : h ^ (k + 1) ≤ 1 := pow_le_one₀ h0 h1
  nlinarith

/-- **`N(h)` between its first `K` returns and the geometric tail.** -/
theorem NhOf_bnd {h a b : ℝ} (hb : Bnd h a b) (ha : 0 ≤ a) (hb1 : b ≤ 1) (K : ℕ) (hK : 1 ≤ K) :
    Bnd (NhOf h) (∑ k ∈ range K, a ^ (k + 1) * repR (k + 1))
      (∑ k ∈ range K, b ^ (k + 1) * repR (k + 1) + (1 / 10) * (1 / 256) ^ K * (1 - 1 / 256)⁻¹) := by
  have h0 : 0 ≤ h := ha.trans hb.1
  have h1 : h ≤ 1 := hb.2.trans hb1
  have hs := NhOf_summable h0 h1
  have hsplit := hs.sum_add_tsum_nat_add K
  have hst : Summable (fun k : ℕ => h ^ (k + K + 1) * repR (k + K + 1)) := by
    have := (summable_nat_add_iff (f := fun k : ℕ => h ^ (k + 1) * repR (k + 1)) K).mpr hs
    simpa [add_assoc, add_comm, add_left_comm] using this
  have htail_nn : 0 ≤ ∑' k : ℕ, h ^ (k + K + 1) * repR (k + K + 1) :=
    tsum_nonneg (fun k => mul_nonneg (pow_nonneg h0 _) (repR_pos _ (by omega)).le)
  have hg : HasSum (fun k : ℕ => ((1 / 10) * (1 / 256) ^ K : ℝ) * (1 / 256) ^ k)
      (((1 / 10) * (1 / 256) ^ K) * (1 - 1 / 256)⁻¹) :=
    (hasSum_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hle : ∀ k : ℕ, h ^ (k + K + 1) * repR (k + K + 1) ≤ ((1 / 10) * (1 / 256) ^ K) * (1 / 256) ^ k := by
    intro k
    have hp := (repR_pos (k + K + 1) (by omega)).le
    have hb' := (repR_bound (k + K + 1) (by omega)).2
    rw [show k + K + 1 - 1 = k + K by omega, pow_add] at hb'
    have : h ^ (k + K + 1) ≤ 1 := pow_le_one₀ h0 h1
    nlinarith
  have htail_le : ∑' k : ℕ, h ^ (k + K + 1) * repR (k + K + 1) ≤
      ((1 / 10) * (1 / 256) ^ K) * (1 - 1 / 256)⁻¹ :=
    hst.tsum_le_of_sum_le fun s => (Finset.sum_le_sum fun k _ => hle k).trans
      (sum_le_hasSum s (fun k _ => by positivity) hg)
  have heq : NhOf h = ∑ k ∈ range K, h ^ (k + 1) * repR (k + 1) +
      ∑' k : ℕ, h ^ (k + K + 1) * repR (k + K + 1) := by
    rw [NhOf, ← hsplit]
  have hlo : ∑ k ∈ range K, a ^ (k + 1) * repR (k + 1) ≤ ∑ k ∈ range K, h ^ (k + 1) * repR (k + 1) :=
    Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hb.1 _)
      (repR_pos _ (by omega)).le
  have hhi : ∑ k ∈ range K, h ^ (k + 1) * repR (k + 1) ≤ ∑ k ∈ range K, b ^ (k + 1) * repR (k + 1) :=
    Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 hb.2 _)
      (repR_pos _ (by omega)).le
  rw [heq]
  exact ⟨by linarith, by linarith⟩

/-- The first six returns, `1/13, 1/6096, 1/1047808, 65/17044852736, 1/68719280128,
341/6007730461474816`. -/
theorem sum_six (x : ℝ) : ∑ k ∈ range 6, x ^ (k + 1) * repR (k + 1) =
    x / 13 + x ^ 2 / 6096 + x ^ 3 / 1047808 + 65 * x ^ 4 / 17044852736 + x ^ 5 / 68719280128 +
      341 * x ^ 6 / 6007730461474816 := by
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  rw [repR_one, repR_two, repR_three, repR_four, repR_five, repR_six]
  ring

/-- **`N(1)` is `NhOf 1`.** -/
theorem N1_eq_NhOf_one : N1 = NhOf 1 := by
  rw [N1, NhOf]
  simp

/-- **The repeated return at `u = i/4` at the clock**, `N_h = N(h)`. -/
noncomputable def qNh : ℝ := NhOf qH

theorem qNh_bnd : Bnd qNh 7.7085840563140591848e-2 7.70858405631409485126e-2 := by
  have hb := NhOf_bnd qH_bnd (by norm_num) (by norm_num) 6 (by norm_num)
  rw [sum_six, sum_six] at hb
  exact hb.weak (by norm_num) (by norm_num)

/-! ## The symmetric companion `N_con` (Proposition 119) and `N(1)` -/

/-- The first return `F(z) = z⁴(1 + z)/(16 − 8z − 3z² − 3z³)` on the real line. -/
noncomputable def excursionFr (z : ℝ) : ℝ := z ^ 4 * (1 + z) / (16 - 8 * z - 3 * z ^ 2 - 3 * z ^ 3)

/-- **The conjugate-pair returns** `p_k^con`: `−Φ(z_k)` at odd `k`, `[F(z_k) + F(−z_k)]/2` at even `k`,
`z_k = 4(i/4)^k`. -/
noncomputable def repRcon (k : ℕ) : ℝ :=
  if Odd k then repR k
  else (excursionFr (4 * (-1 / 16 : ℝ) ^ (k / 2)) + excursionFr (-(4 * (-1 / 16 : ℝ) ^ (k / 2)))) / 2

theorem excursionFr_bound {z : ℝ} (hz : |z| ≤ 1 / 4) :
    0 < 1 + z ∧ 0 < 16 - 8 * z - 3 * z ^ 2 - 3 * z ^ 3 ∧ 0 ≤ excursionFr z ∧
      excursionFr z ≤ (1 / 10) * z ^ 4 := by
  rw [abs_le] at hz
  obtain ⟨h1, h2⟩ := hz
  have hz2 : z ^ 2 ≤ 1 / 16 := by nlinarith
  have hz3 : z ^ 3 ≤ 1 / 64 := by nlinarith
  have hz3' : -(1 / 64) ≤ z ^ 3 := by nlinarith
  have hd : 13 ≤ 16 - 8 * z - 3 * z ^ 2 - 3 * z ^ 3 := by nlinarith
  have hp : 0 < 1 + z := by linarith
  have h4 : 0 ≤ z ^ 4 := by positivity
  refine ⟨hp, by linarith, ?_, ?_⟩
  · unfold excursionFr
    apply div_nonneg (mul_nonneg h4 hp.le) (by linarith)
  · unfold excursionFr
    rw [div_le_iff₀ (by linarith)]
    nlinarith

theorem repRcon_odd {k : ℕ} (hk : Odd k) : repRcon k = repR k := by
  simp [repRcon, hk]

theorem repRcon_bound (k : ℕ) (hk : 2 ≤ k) :
    0 ≤ repRcon k ∧ repRcon k ≤ (1 / 10) * (1 / 256) ^ (k - 1) := by
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | ho
  · have hne : ¬Odd k := Nat.not_odd_iff_even.mpr ⟨m, hm⟩
    have hm1 : 1 ≤ m := by omega
    simp only [repRcon, hne, if_false]
    rw [show k / 2 = m by omega]
    set z : ℝ := 4 * (-1 / 16 : ℝ) ^ m with hz
    have habs : |z| ≤ 1 / 4 := by
      rw [hz, abs_mul, abs_pow]
      norm_num
      have : (1 / 16 : ℝ) ^ m ≤ 1 / 16 := by
        calc (1 / 16 : ℝ) ^ m ≤ (1 / 16) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm1
          _ = 1 / 16 := by norm_num
      linarith
    have habs' : |-z| ≤ 1 / 4 := by rwa [abs_neg]
    obtain ⟨-, -, a0, a1⟩ := excursionFr_bound habs
    obtain ⟨-, -, b0, b1⟩ := excursionFr_bound habs'
    have hz4 : z ^ 4 = 256 * (1 / 256 : ℝ) ^ (2 * m) := by
      rw [hz, mul_pow, ← pow_mul, mul_comm m 4, pow_mul, pow_mul]
      norm_num
    have hz4' : (-z) ^ 4 = z ^ 4 := by ring
    rw [hz4'] at b1
    have hk2 : k - 1 = 2 * m - 1 := by omega
    have hkey : (1 / 10 : ℝ) * z ^ 4 ≤ (1 / 10) * (1 / 256) ^ (k - 1) := by
      rw [hz4, hk2]
      have : (1 / 256 : ℝ) ^ (2 * m) = (1 / 256) * (1 / 256) ^ (2 * m - 1) := by
        rw [← pow_succ']
        congr 1
        omega
      rw [this]
      have : (0 : ℝ) ≤ (1 / 256) ^ (2 * m - 1) := by positivity
      nlinarith
    constructor
    · linarith
    · linarith
  · rw [repRcon_odd ho]
    exact ⟨(repR_bound k hk).1.le, (repR_bound k hk).2⟩

theorem repRcon_summable : Summable (fun k : ℕ => repRcon (k + 1)) := by
  have hg : Summable (fun k : ℕ => (1 / 10 : ℝ) * (1 / 256) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) (hg.add (summable_of_ne_finset_zero
    (s := {0}) (f := fun k : ℕ => if k = 0 then (1 / 13 : ℝ) else 0) (fun k hk => by simp at hk; simp [hk])))
  · rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rw [repRcon_odd (by decide), repR_one]
      norm_num
    · exact (repRcon_bound (k + 1) (by omega)).1
  · rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rw [repRcon_odd (by decide), repR_one]
      norm_num
    · have := (repRcon_bound (k + 1) (by omega)).2
      rw [show k + 1 - 1 = k by omega] at this
      simp only [Nat.pos_iff_ne_zero.mp hk, ite_false, add_zero]
      exact this

/-- **`N_con = Σ_{k ≥ 1} p_k^con`.** -/
noncomputable def qNcon : ℝ := ∑' k : ℕ, repRcon (k + 1)

theorem repRcon_six : ∑ k ∈ range 6, repRcon (k + 1) =
    1 / 13 + 1393 / 5370576 + 1 / 1047808 + 89485313 / 24015532755767296 + 1 / 68719280128 +
      5864063762433 / 103161608451287150222114816 := by
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add]
  have o1 : Odd 1 := by decide
  have o3 : Odd 3 := by decide
  have o5 : Odd 5 := by decide
  have e2 : ¬Odd 2 := by decide
  have e4 : ¬Odd 4 := by decide
  have e6 : ¬Odd 6 := by decide
  simp only [repRcon, o1, o3, o5, e2, e4, e6, ite_true, ite_false, excursionFr]
  rw [repR_one, repR_three, repR_five]
  norm_num

theorem qNcon_bnd : Bnd qNcon 7.718341131261758584923e-2 7.718341131261794251383e-2 := by
  have hsplit := repRcon_summable.sum_add_tsum_nat_add 6
  have hst : Summable (fun k : ℕ => repRcon (k + 6 + 1)) := by
    have := (summable_nat_add_iff (f := fun k : ℕ => repRcon (k + 1)) 6).mpr repRcon_summable
    simpa [add_assoc, add_comm, add_left_comm] using this
  have hnn : 0 ≤ ∑' k : ℕ, repRcon (k + 6 + 1) :=
    tsum_nonneg (fun k => (repRcon_bound (k + 6 + 1) (by omega)).1)
  have hg : HasSum (fun k : ℕ => ((1 / 10) * (1 / 256) ^ 6 : ℝ) * (1 / 256) ^ k)
      (((1 / 10) * (1 / 256) ^ 6) * (1 - 1 / 256)⁻¹) :=
    (hasSum_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hle : ∀ k : ℕ, repRcon (k + 6 + 1) ≤ ((1 / 10) * (1 / 256) ^ 6) * (1 / 256) ^ k := by
    intro k
    have := (repRcon_bound (k + 6 + 1) (by omega)).2
    rw [show k + 6 + 1 - 1 = k + 6 by omega, pow_add] at this
    linarith
  have htail : ∑' k : ℕ, repRcon (k + 6 + 1) ≤ ((1 / 10) * (1 / 256) ^ 6) * (1 - 1 / 256)⁻¹ :=
    hst.tsum_le_of_sum_le fun s => (Finset.sum_le_sum fun k _ => hle k).trans
      (sum_le_hasSum s (fun k _ => by positivity) hg)
  have heq : qNcon = ∑ k ∈ range 6, repRcon (k + 1) + ∑' k : ℕ, repRcon (k + 6 + 1) := by
    rw [qNcon, ← hsplit]
  rw [heq, repRcon_six]
  constructor
  · norm_num
    linarith
  · norm_num at htail ⊢
    linarith

/-- `N(1)` as a closed interval (Proposition 72, `Mass/Return72.lean`). -/
theorem N1_bnd : Bnd N1 0.0770880771192245 0.0770880771192250 :=
  ⟨N1_bounds.1.le, N1_bounds.2.le⟩

end Comparison.Article
