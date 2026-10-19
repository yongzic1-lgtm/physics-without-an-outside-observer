module

public import Comparison.Colour.LastDirections

/-!
# Book XVIII. The heavy lines: the finite statements (Propositions 101 to 106)

* **Prop. 101.** `rest_pole_counts`: `γ^R₀ = 4C_F = 16/3`; `b₀ = 11 − 2n_l/3 = 25/3` at `n_l = 4`;
  `2γ^R₀b₀ = 800/9`; `a₁ = 31/3 − 10n_f/9` is `7` at `n_f = 3` and `53/9` at `n_f = 4`.
* **Prop. 104.** `contact_factor`: `32π/9 = (8π/3)C_F`; `spin_weights`: `s₁·s₂ = σ₁·σ₂/4` is
  `1/4` on every symmetric state (`S = 1`) and `−3/4` on every antisymmetric state (`S = 0`);
  `partner_split`: with `P = M̄ − (3/4)Δ`, `V = M̄ + (1/4)Δ`: `(3V + P)/4 = M̄`, `V − P = Δ`,
  `w_V − w_P = 1`, `(3w_V + w_P)/4 = 0`; `annihilation_small`: `0 < 1 − ln 2` and
  `(1 − ln 2)/π < 1/10`.
* **Prop. 105.** `availableTransitions_free_ratio`: `m_u = R m_d`, `m_s = p m_d`, `m̂ = (m_u + m_d)/2` give
  `(m_d − m_u)/(m_s − m̂) = (1 − R)/(p − (1 + R)/2)`; at `R = 17/37`, `1 − R = 20/37`,
  `(1 + R)/2 = 27/37`. `charge_products`: `cc̄ −4/9`, `bb̄ −1/9`, `cb̄ +2/9`, `cū −4/9`, `cd̄ +2/9`,
  `ub̄ +2/9`, `db̄ −1/9`, `cs̄ +2/9`, `sb̄ −1/9`; `e_c(e_d̄ − e_ū) = 2/3`, `e_b(e_d̄ − e_ū) = −1/3`,
  `e_u² − e_d² = 1/3`.
* **Prop. 106.** `heavy_baryons`: `Σ̄_Q − Λ_Q = 4A = (5/24)m_p` and `Λ_Q − M̄ = λ = m_p/3` with
  Prop. 85's `A = (5/96)m_p`.
-/

@[expose] public section

namespace Comparison

open Matrix

/-! ## Prop. 101 -/

theorem rest_pole_counts :
    (4 : ℚ) * (4 / 3) = 16 / 3 ∧ (11 - 2 * 4 / 3 : ℚ) = 25 / 3 ∧
      2 * (16 / 3 : ℚ) * (25 / 3) = 800 / 9 ∧ (31 / 3 - 10 * 3 / 9 : ℚ) = 7 ∧
      (31 / 3 - 10 * 4 / 9 : ℚ) = 53 / 9 := by
  norm_num

/-! ## Prop. 104 -/

/-- **`32π/9 = (8π/3)C_F`** with `C_F = 4/3`. -/
theorem contact_factor : 32 * Real.pi / 9 = 8 * Real.pi / 3 * (4 / 3) := by ring

/-- **The spin weights:** `s₁·s₂ = σ₁·σ₂/4` is `1/4` on the symmetric states and `−3/4` on the
antisymmetric ones. -/
theorem spin_weights (v w : Fin 2 × Fin 2 → ℂ) (hv : ∀ a b, v (a, b) = v (b, a))
    (hw : ∀ a b, w (a, b) = -w (b, a)) :
    ((1 / 4 : ℂ) • dot2) *ᵥ v = (1 / 4 : ℂ) • v ∧ ((1 / 4 : ℂ) • dot2) *ᵥ w = (-3 / 4 : ℂ) • w := by
  constructor
  · rw [Matrix.smul_mulVec, dot2_agree v hv]
  · rw [Matrix.smul_mulVec, dot2_differ w hw, smul_smul]
    norm_num

/-- **The two spin partners:** `P = M̄ − (3/4)Δ`, `V = M̄ + (1/4)Δ` give `(3V + P)/4 = M̄` and
`V − P = Δ`. -/
theorem partner_split (M Δ : ℝ) :
    (3 * (M + 1 / 4 * Δ) + (M - 3 / 4 * Δ)) / 4 = M ∧ (M + 1 / 4 * Δ) - (M - 3 / 4 * Δ) = Δ ∧
      (1 / 4 : ℝ) - (-3 / 4) = 1 ∧ (3 * (1 / 4 : ℝ) + (-3 / 4)) / 4 = 0 := by
  refine ⟨by ring, by ring, by norm_num, by norm_num⟩

/-- **The annihilation share is small:** `0 < 1 − ln 2` and `(1 − ln 2)/π < 1/10`. -/
theorem annihilation_small : 0 < 1 - Real.log 2 ∧ (1 - Real.log 2) / Real.pi < 1 / 10 := by
  have h1 := Real.log_two_gt_d9
  have h2 := Real.log_two_lt_d9
  have hp := Real.pi_gt_d6
  refine ⟨by linarith, ?_⟩
  rw [div_lt_iff₀ (by linarith)]
  linarith

/-! ## Prop. 105 -/

/-- **The ratio independent of the available transitions:** `(m_d − m_u)/(m_s − m̂) = (1 − R)/(p − (1 + R)/2)`. -/
theorem availableTransitions_free_ratio (md R p : ℝ) (hmd : md ≠ 0) :
    (md - R * md) / (p * md - (R * md + md) / 2) = (1 - R) / (p - (1 + R) / 2) := by
  have e : p * md - (R * md + md) / 2 = (p - (1 + R) / 2) * md := by ring
  rw [e, show md - R * md = (1 - R) * md by ring, mul_div_mul_right _ _ hmd]

theorem availableTransitions_free_values : (1 - 17 / 37 : ℚ) = 20 / 37 ∧ (1 + 17 / 37 : ℚ) / 2 = 27 / 37 := by
  norm_num

/-- The charges of the five levels: `u, c` `2/3`; `d, s, b` `−1/3`. -/
theorem charge_products :
    let eu : ℚ := 2 / 3
    let ed : ℚ := -1 / 3
    let es : ℚ := -1 / 3
    let ec : ℚ := 2 / 3
    let eb : ℚ := -1 / 3
    ec * -ec = -4 / 9 ∧ eb * -eb = -1 / 9 ∧ ec * -eb = 2 / 9 ∧ ec * -eu = -4 / 9 ∧
      ec * -ed = 2 / 9 ∧ eu * -eb = 2 / 9 ∧ ed * -eb = -1 / 9 ∧ ec * -es = 2 / 9 ∧
      es * -eb = -1 / 9 ∧ ec * (-ed - -eu) = 2 / 3 ∧ eb * (-ed - -eu) = -1 / 3 ∧
      eu ^ 2 - ed ^ 2 = 1 / 3 := by
  intro eu ed es ec eb
  simp only [eu, ed, es, ec, eb]
  norm_num

/-! ## Prop. 106 -/

/-- **The heavy baryons of the one share:** `Λ_Q = M̄ + λ`, `Σ̄_Q = M̄ + λ + 4A`, with
`A = (5/96)m_p`, `λ = m_p/3`: `Σ̄_Q − Λ_Q = (5/24)m_p`. -/
theorem heavy_baryons (M mp : ℝ) :
    (M + mp / 3 + 4 * (5 / 96 * mp)) - (M + mp / 3) = 5 / 24 * mp ∧ (M + mp / 3) - M = mp / 3 := by
  constructor <;> ring

end Comparison

end
