import Comparison.System.Completion.Numbers
import Comparison.System.Table.Hadrons
import Comparison.Article.Kaons
import Comparison.Law.LongZero
import Comparison.Law.Composite

set_option linter.style.longLine false

/-!
# The proof system, the completions, part 8: numbers of the text with no row of their own

The Higgs quartic `λ_H = πα/χ_h` (Prop. 68, row D16's factor) and the three light levels of
one composition (Prop. 197), each as an interval with rational ends.
-/

namespace Comparison.System

open Real Comparison Comparison.Law Comparison.System.Completion

/-- **The Higgs quartic (Prop. 68).** `λ_H = πα/χ_h = πα(4χ_A)²/(4χ_A − 1)` with `χ_h = w_h(1 − w_h) = 30/169` and
`χ_A = 13/12`: `λ_H = 0.129145909`; `m_H = v(2λ_H)^{1/2}`. Recognition: the Higgs self-coupling. -/
theorem Completion.Comp.higgs_quartic :
    Num.chih = 30 / 169 ∧ (30 / 169 : ℝ) = (4 * (13 / 12) - 1) / (4 * (13 / 12)) ^ 2 ∧
    ((0.1291459085 : ℝ) < π * Num.alpha / Num.chih ∧ π * Num.alpha / Num.chih < 0.1291459095) := by
  refine ⟨Num.chih_eq, by norm_num, ?_⟩
  rw [Num.chih_eq, Num.alpha_eq_q]
  have h := (Article.Bnd.mul Article.bnd_pi Article.qAlpha_bnd (by norm_num) (by norm_num)).smul_const
    (show (0 : ℝ) ≤ 169 / 30 by norm_num)
  have e : π * Article.qAlpha / (30 / 169) = 169 / 30 * (π * Article.qAlpha) := by ring
  rw [e]
  exact h.strict (by norm_num) (by norm_num)

/-- **The three light levels of one composition (Prop. 197).** At the light level `S_d ∈ [sdLo, sdHi]`:
`S_d = 0.011855816`, `S_u = R_udS_d = (17/37)S_d = 0.005447267`, `S_s = pS_d = 0.236661685` with `p` the
plane-and-singlet mass operator. -/
theorem Completion.Comp.light_level_digits :
    ((0.0118558155 : ℝ) < Table.Row.Sd ∧ Table.Row.Sd < 0.0118558165) ∧
    ((0.0054472665 : ℝ) < Num.Rud * Table.Row.Sd ∧ Num.Rud * Table.Row.Sd < 0.0054472675) ∧
    ((0.2366616845 : ℝ) < massOp .symmetric sPlaneSinglet * Table.Row.Sd ∧
      massOp .symmetric sPlaneSinglet * Table.Row.Sd < 0.2366616855) := by
  rw [Num.Rud_eq]
  have hS : Article.Bnd Table.Row.Sd Article.sdLo Article.sdHi := Table.Sd_mem
  have hl : Article.sdLo = (1.18558163507453026801854e-2 : ℝ) := rfl
  have hh : Article.sdHi = (1.18558163507453029173019e-2 : ℝ) := rfl
  rw [hl, hh] at hS
  refine ⟨hS.strict (by norm_num) (by norm_num), ?_, ?_⟩
  · exact (hS.smul_const (show (0 : ℝ) ≤ 17 / 37 by norm_num)).strict (by norm_num) (by norm_num)
  · rw [Article.massOp_p]
    exact (Article.Bnd.mul Article.qP_bnd hS (by norm_num) (by norm_num)).strict (by norm_num) (by norm_num)

open Filter Topology Asymptotics in
/-- The two limits differ at second order by the cross spread `12/125` of two lines on one last-step direction:
`δ_L − δ_M − (12/125)S₁S₂ = O(‖S‖³)`. -/
theorem Completion.Comp.two_limits_second_order :
    (fun p : ℝ × ℝ => (deltaLevel p.1 + deltaLevel p.2) - deltaLevel (p.1 + p.2) - 12 / 125 * p.1 * p.2) =O[𝓝 0]
      (fun p : ℝ × ℝ => ‖p‖ ^ 3) := by
  set f : ℝ → ℝ := fun S => deltaLevel S - (S / 5 - 6 / 125 * S ^ 2) with hf
  have hO : f =O[𝓝 0] (fun S : ℝ => S ^ 3) := delta_expansion
  have h1 : (fun p : ℝ × ℝ => f p.1) =O[𝓝 0] (fun p : ℝ × ℝ => ‖p‖ ^ 3) := by
    have := hO.comp_tendsto (continuous_fst.tendsto' (0 : ℝ × ℝ) 0 rfl)
    refine this.trans (Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun p => ?_))
    simp only [Function.comp_apply, norm_pow, norm_norm, one_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_fst_le p) 3
  have h2 : (fun p : ℝ × ℝ => f p.2) =O[𝓝 0] (fun p : ℝ × ℝ => ‖p‖ ^ 3) := by
    have := hO.comp_tendsto (continuous_snd.tendsto' (0 : ℝ × ℝ) 0 rfl)
    refine this.trans (Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun p => ?_))
    simp only [Function.comp_apply, norm_pow, norm_norm, one_mul]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_snd_le p) 3
  have h3 : (fun p : ℝ × ℝ => f (p.1 + p.2)) =O[𝓝 0] (fun p : ℝ × ℝ => ‖p‖ ^ 3) := by
    have ht : Tendsto (fun p : ℝ × ℝ => p.1 + p.2) (𝓝 0) (𝓝 0) :=
      (continuous_fst.add continuous_snd).tendsto' (0 : ℝ × ℝ) 0 (by simp)
    have := hO.comp_tendsto ht
    refine this.trans (Asymptotics.IsBigO.of_bound 8 (Filter.Eventually.of_forall fun p => ?_))
    simp only [Function.comp_apply, norm_pow, norm_norm]
    have hb : ‖p.1 + p.2‖ ≤ 2 * ‖p‖ :=
      (norm_add_le _ _).trans (by linarith [norm_fst_le p, norm_snd_le p])
    calc ‖p.1 + p.2‖ ^ 3 ≤ (2 * ‖p‖) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hb 3
      _ = 8 * ‖p‖ ^ 3 := by ring
  have e : (fun p : ℝ × ℝ => (deltaLevel p.1 + deltaLevel p.2) - deltaLevel (p.1 + p.2) - 12 / 125 * p.1 * p.2) =
      fun p : ℝ × ℝ => f p.1 + f p.2 - f (p.1 + p.2) := by
    funext p
    simp only [hf]
    ring
  rw [e]
  exact (h1.add h2).sub h3

open Filter Topology Asymptotics in
/-- **Proposition 169 (the two limits agree at first order and differ at second by the cross covariance of the
lines' transitions).** The last-step direction's walk has `Cov(X^i₀, X^j_k) = (1/5)(−1/4)^k(δ_ij − 1/5)` and the long-run covariance
`σ_ij = (3/25)(δ_ij − 1/5)`: `12/125` on one line, `−3/125` across two; both limits are `(S₁ + S₂)/5` at first order;
for two levels on one last-step direction `δ_L − δ_M = σ_hhS₁S₂ + O(‖S‖³)` with `σ_hh = 12/125`; and the composition carries
`−(12/125)cS₁S₂` at second order (`c = 0` the line side, `c = 1` the meeting side). -/
theorem prop_169 :
    (∀ (i j : Fin 5) (k : ℕ), (1 / 5 : ℚ) * (lastDirectionStep ^ k) i j - (1 / 5) ^ 2 =
      (1 / 5) * (-1 / 4) ^ k * ((if i = j then 1 else 0) - 1 / 5)) ∧
    (∀ i j : Fin 5, HasSum (fun k : ℕ => (if k = 0 then (1 : ℝ) else 2) *
        ((1 / 5) * (-1 / 4) ^ k * ((if i = j then 1 else 0) - 1 / 5)))
      ((3 / 25) * ((if i = j then 1 else 0) - 1 / 5))) ∧
    ((3 / 25 : ℝ) * (1 - 1 / 5) = 12 / 125 ∧ (3 / 25 : ℝ) * (0 - 1 / 5) = -3 / 125) ∧
    ((fun p : ℝ × ℝ => deltaLevel p.1 + deltaLevel p.2 - (p.1 + p.2) / 5) =O[𝓝 0]
        (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) ∧
      (fun p : ℝ × ℝ => deltaLevel (p.1 + p.2) - (p.1 + p.2) / 5) =O[𝓝 0]
        (fun p : ℝ × ℝ => (p.1 + p.2) ^ 2)) ∧
    (fun p : ℝ × ℝ => (deltaLevel p.1 + deltaLevel p.2) - deltaLevel (p.1 + p.2) - 12 / 125 * p.1 * p.2) =O[𝓝 0]
      (fun p : ℝ × ℝ => ‖p‖ ^ 3) ∧
    (∀ S₁ S₂ c : ℝ, 0 ≤ (S₁ - S₂) ^ 2 + 4 * c * S₁ * S₂ →
      (eigenPlus S₁ S₂ c / 5 - 6 / 125 * eigenPlus S₁ S₂ c ^ 2) +
          (eigenMinus S₁ S₂ c / 5 - 6 / 125 * eigenMinus S₁ S₂ c ^ 2) =
        (S₁ + S₂) / 5 - 6 / 125 * (S₁ ^ 2 + S₂ ^ 2) - 12 / 125 * c * S₁ * S₂) :=
  ⟨lastDirection_cross_cov, cross_spread, cross_values, two_limits_first_order, Completion.Comp.two_limits_second_order,
    fun S₁ S₂ c hd => second_order_composite S₁ S₂ c hd⟩

end Comparison.System
