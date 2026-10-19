import Comparison.Elements.TwoThings

/-!
# Two bridges of the line

**Proposition 102, the line's own rotation and its imprint on the available transitions.**
The traceless rotation `S_h = (5hhᵀ − 1)/4` turns the complex line of `h` against the other four; on the
sixteen two-spinor states it acts as `ρ(iS) = −(i/2) Σ_{a,b} S_ab γ_a ⊗ γ_b` (Proposition 94). Pressed onto the
side that the line `h` holds, `P_h = 1 ⊗ Q(h)`, `Q(h) = (1 + γ_h)/2`, it is the line's own clock:
`P_h ρ(iS_h) P_h = −(i/2) γ_h ⊗ Q(h)`.

* `side_self`, `side_other`: `(1 + γ_h) γ_h (1 + γ_h) = 2(1 + γ_h)` and `(1 + γ_h) γ_b (1 + γ_h) = 0` for
  `b ≠ h` (here `h` is the line `0` of the model of Proposition 23).
* `own_turn_compressed`: **`(1 ⊗ D)(5 γ_h ⊗ γ_h − Σ_t γ_t ⊗ γ_t)(1 ⊗ D) = 8 γ_h ⊗ D`**, `D = 1 + γ_h = 2Q(h)`:
  with `4S_h = 5hhᵀ − 1` this is `P_h (Σ S_ab γ_a ⊗ γ_b) P_h = γ_h ⊗ Q(h)`, so
  `P_h ρ(iS_h) P_h = −(i/2) γ_h ⊗ Q(h)`, the generator `−iγ_h` of the line's clock (Propositions 41, 60).
* `availableTransitions_ratio`, `imprint_scalar`, `availableTransitions_imprint`: `σ/η = (75/74)/(296/295) = 60/59`, and
  `R_h/(det R_h)^{1/5} = diag((σ/η)^{4/5}, (σ/η)^{−1/5} ×4) = exp[(4/5) log(60/59) S_h]` on the
  eigenvalues `1` and `−1/4` of `S_h`: the available transitions are the imprint of the same rotation.

**The two bottoms joined.** With the d line one transition at its sign,
`m_d = 3^{3/2} m_e/η`, and `m_u = R_ud m_d`, `R_ud = 17/37` (Propositions 31, 69), the neutral pion
`m_π⁰² = 38 h m_e m_p` (Propositions 121, 207) is **`m_π⁰² = B (m_u + m_d)`** with
`B = 703 η h m_p/(81√3)`: `pion_join`. The factors are `38 = 2·19`, `54/37 = 1 + R_ud`, `3√3 = 3^{3/2}`.
-/

open Comparison Matrix Kronecker

namespace Comparison.RuleAndLaw

/-! ## Proposition 102: the line's own rotation pressed onto its side -/

theorem side_self : (1 + γ 0) * γ 0 * (1 + γ 0) = (2 : ℂ) • (1 + γ 0) := by
  have h := γ_mul_self 0
  have e : (1 + γ 0) * γ 0 * (1 + γ 0) = γ 0 + γ 0 * γ 0 + γ 0 * γ 0 + γ 0 * γ 0 * γ 0 := by
    noncomm_ring
  rw [e, h, one_mul, two_smul]
  abel

theorem side_other (b : Fin 5) (hb : b ≠ 0) : (1 + γ 0) * γ b * (1 + γ 0) = 0 := by
  have h := γ_mul_self 0
  have ha : γ 0 * γ b = -(γ b * γ 0) := γ_anticomm (Ne.symm hb)
  have e : (1 + γ 0) * γ b * (1 + γ 0) = γ b + γ b * γ 0 + γ 0 * γ b + γ 0 * γ b * γ 0 := by
    noncomm_ring
  rw [e, ha]
  have e2 : -(γ b * γ 0) * γ 0 = -(γ b * (γ 0 * γ 0)) := by noncomm_ring
  rw [e2, h, mul_one]
  abel

theorem compress_kron (a b : Fin 5) :
    ((1 : Matrix Four Four ℂ) ⊗ₖ (1 + γ 0)) * (γ a ⊗ₖ γ b) * ((1 : Matrix Four Four ℂ) ⊗ₖ (1 + γ 0)) =
      γ a ⊗ₖ ((1 + γ 0) * γ b * (1 + γ 0)) := by
  rw [← mul_kronecker_mul, ← mul_kronecker_mul, one_mul, mul_one]

/-- **The own line's moved rotation pressed onto its side is its clock** (Proposition 102):
`(1 ⊗ D)(5 γ_h ⊗ γ_h − Σ_t γ_t ⊗ γ_t)(1 ⊗ D) = 8 γ_h ⊗ D`, `D = 1 + γ_h = 2Q(h)`. -/
theorem own_turn_compressed :
    ((1 : Matrix Four Four ℂ) ⊗ₖ (1 + γ 0)) *
        ((5 : ℂ) • (γ 0 ⊗ₖ γ 0) - ∑ t, γ t ⊗ₖ γ t) * ((1 : Matrix Four Four ℂ) ⊗ₖ (1 + γ 0)) =
      (8 : ℂ) • (γ 0 ⊗ₖ (1 + γ 0)) := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Finset.mul_sum, Finset.sum_mul]
  simp only [Matrix.mul_smul, Matrix.smul_mul, compress_kron]
  rw [Fin.sum_univ_five, side_self, side_other 1 (by decide), side_other 2 (by decide),
    side_other 3 (by decide), side_other 4 (by decide)]
  simp only [kronecker_zero, kronecker_smul, add_zero, smul_smul]
  module

/-- `σ/η = 60/59`. -/
theorem availableTransitions_ratio : ((75 / 74 : ℝ) / (295 / 296)) = 60 / 59 := by norm_num

/-- `R_h/(det R_h)^{1/5}` on the own line and on each other line, `det R_h = ση⁴`. -/
theorem imprint_scalar (σ η : ℝ) (hσ : 0 < σ) (hη : 0 < η) :
    σ / (σ * η ^ 4) ^ ((1 : ℝ) / 5) = (σ / η) ^ ((4 : ℝ) / 5) ∧
      η / (σ * η ^ 4) ^ ((1 : ℝ) / 5) = (σ / η) ^ (-(1 : ℝ) / 5) := by
  have hp : 0 < σ * η ^ 4 := mul_pos hσ (pow_pos hη 4)
  have hq : 0 < σ / η := div_pos hσ hη
  have hl : Real.log (σ * η ^ 4) = Real.log σ + 4 * Real.log η := by
    rw [Real.log_mul hσ.ne' (pow_pos hη 4).ne', Real.log_pow]
    norm_num
  have hd : Real.log (σ / η) = Real.log σ - Real.log η := Real.log_div hσ.ne' hη.ne'
  rw [Real.rpow_def_of_pos hp, Real.rpow_def_of_pos hq, Real.rpow_def_of_pos hq, hl, hd]
  constructor
  · nth_rewrite 1 [← Real.exp_log hσ]
    rw [← Real.exp_sub]
    congr 1
    ring
  · nth_rewrite 1 [← Real.exp_log hη]
    rw [← Real.exp_sub]
    congr 1
    ring

/-- **The available transitions are the imprint of the own rotation:** with `σ/η = 60/59` the normalized available-transition is
`exp[(4/5) log(60/59) S_h]` on the eigenvalues `1` (the own line) and `−1/4` (the four others). -/
theorem availableTransitions_imprint :
    (60 / 59 : ℝ) ^ ((4 : ℝ) / 5) = Real.exp ((4 / 5) * Real.log (60 / 59) * 1) ∧
      (60 / 59 : ℝ) ^ (-(1 : ℝ) / 5) = Real.exp ((4 / 5) * Real.log (60 / 59) * (-1 / 4)) := by
  constructor
  · rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    ring
  · rw [Real.rpow_def_of_pos (by norm_num)]
    congr 1
    ring

/-! ## The two native bottoms joined -/

/-- **The pion joins the two native bottoms**: with `m_d = 3√3 m_e/η` and
`m_u = (17/37) m_d`, `38 h m_e m_p = B (m_u + m_d)` with `B = 703 η h m_p/(81√3)`. -/
theorem pion_join (me mp h η : ℝ) (hη : η ≠ 0) :
    38 * h * me * mp =
      703 * η * h * mp / (81 * Real.sqrt 3) *
        ((17 / 37) * (3 * Real.sqrt 3 * me / η) + 3 * Real.sqrt 3 * me / η) := by
  have h3 : Real.sqrt 3 ≠ 0 := by positivity
  field_simp
  ring

/-- The factors of `B`: `38·(37/54)/(3√3) = 703/(81√3)`. -/
theorem pion_join_factors : (38 : ℝ) * 37 / 54 / 3 = 703 / 81 ∧ (1 : ℚ) + 17 / 37 = 54 / 37 := by
  norm_num

end Comparison.RuleAndLaw

#print axioms Comparison.RuleAndLaw.side_self
#print axioms Comparison.RuleAndLaw.side_other
#print axioms Comparison.RuleAndLaw.compress_kron
#print axioms Comparison.RuleAndLaw.own_turn_compressed
#print axioms Comparison.RuleAndLaw.availableTransitions_ratio
#print axioms Comparison.RuleAndLaw.imprint_scalar
#print axioms Comparison.RuleAndLaw.availableTransitions_imprint
#print axioms Comparison.RuleAndLaw.pion_join
#print axioms Comparison.RuleAndLaw.pion_join_factors
