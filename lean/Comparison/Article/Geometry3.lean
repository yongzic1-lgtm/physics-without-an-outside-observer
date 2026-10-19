import Comparison.Existence.Matter
import Comparison.ArticleStatements.Geometry
import Comparison.Article.QCouplings
import Comparison.Article.Commutant2

/-!
# The charge a step gives off, the flat sign, and the three pairings beside the last-step direction
(Propositions 65, 91, 99)

* `charge_step` (**Proposition 65**): with `Q(S) = Σ_{x∈S} q_x`, `q_h = 0`, `q_k = 1`, `q_c = −1/3`, a step along
  the line `t` (`S ↦ S △ T_t`, `T_t` the four other lines) has **`Q(S △ T_t) + Q(S) = q_t(2[t ∈ S] − 1)`**: the step
  along the last-step direction alone gives off no charge (`lastDirection_step_neutral`); `electric_coupling`: `α₀ = c_L f = 27/3700`,
  `1/α₀ = 137.037`, and **`1/α = 3700/27 − (37/120) h/(297 + N_h)`** at the clock.
* `history_12345_closed`, `square_closed`, `flat_sign_no_clock` (**Proposition 91**): the walk `12345` (a step
  along each line in turn) is closed, every square `abab` is closed, and with the flat sign `q ≡ −1` on the forty
  links the squares close with `(−1)⁴ = +1` and `12345` with `(−1)⁵ = −1`: **no common phase exists**.
* `gramTheta`, `pairing_irreps` (**Proposition 99**): the Gram `Tr(X_iX_j)/16` of `1, −P, −E` is `(5I − 𝖩₃)/4`,
  the projectors are `Π = (1/4) Σ_i (B₃)_{i·} X_i`, and **`B₃ᵀ G_Θ B₃ = diag(1, 10, 5)`**, `3(1 + 10 + 5) = 48`;
  `K_sq`, `K_anticomm`, `K_comm_lastDirection`, `pairings_on_side`: **`K_j = γ_kγ_{c_j}` square to `−1`, anticommute, keep
  the last-step direction's side, and each pairing `γ_aγ_b = ±γ_cγ_d` there** (`h = 0`, `k = 1`, `c = 2, 3, 4`).
-/

namespace Comparison.Article

open Matrix hiding J
open Complex Kronecker

/-! ## Proposition 65: the charge a step gives off -/

/-- Three times the charge of a line: `q_h = 0`, `q_k = 1`, `q_c = −1/3`. -/
def qline3 (h k t : Fin 5) : ℤ := if t = h then 0 else if t = k then 3 else -1

theorem charge_step3 : ∀ h k : Fin 5, h ≠ k → ∀ t : Fin 5, ∀ r : Fin 16,
    charge3 h k (transition t r) + charge3 h k r =
      qline3 h k t * (2 * (if t ∈ disagreeSet r then 1 else 0) - 1) := by
  decide +kernel

/-- **Proposition 65: the charge a step gives off**, `Q(S △ T_t) + Q(S) = q_t(2[t ∈ S] − 1)`. -/
theorem charge_step (h k : Fin 5) (hk : h ≠ k) (t : Fin 5) (r : Fin 16) :
    charge h k (transition t r) + charge h k r =
      ((qline3 h k t : ℚ) / 3) * (2 * (if t ∈ disagreeSet r then 1 else 0) - 1) := by
  rw [charge_eq3, charge_eq3]
  have e := charge_step3 h k hk t r
  have e' : ((charge3 h k (transition t r) + charge3 h k r : ℤ) : ℚ) =
      ((qline3 h k t * (2 * (if t ∈ disagreeSet r then 1 else 0) - 1) : ℤ) : ℚ) := by rw [e]
  push_cast at e'
  split_ifs at e' ⊢ <;> linarith

/-- **The step along the last-step direction alone gives off no charge.** -/
theorem lastDirection_step_neutral (h k : Fin 5) (hk : h ≠ k) (r : Fin 16) :
    charge h k (transition h r) = -charge h k r := by
  have := charge_step h k hk h r
  simp [qline3] at this
  linarith

/-- **The electric coupling at the clock:** `α₀ = 27/3700`, `1/α₀ = 137.037`, and
`1/α = 3700/27 − (37/120) h/(297 + N_h)`. -/
theorem electric_coupling :
    (15 / 74 : ℝ) * (9 / 250) = 27 / 3700 ∧ ((137.0365 : ℝ) < 3700 / 27 ∧ (3700 / 27 : ℝ) < 137.0375) ∧
      qAlpha⁻¹ = 3700 / 27 - 37 / 120 * qH / (297 + qNh) := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  have hN : (0 : ℝ) < 297 + qNh := by linarith [qNh_bnd.1]
  rw [qAlpha, qX, inv_div]
  field_simp
  ring

/-! ## Proposition 91: the flat sign -/

/-- **The walk `12345` is closed:** a step along each of the five directions in turn returns. -/
theorem history_12345_closed : ∀ r : Fin 16, transition 4 (transition 3 (transition 2 (transition 1 (transition 0 r)))) = r := by
  decide

/-- **Every square is closed:** `abab` returns. -/
theorem square_closed : ∀ a b : Fin 5, ∀ r : Fin 16, transition b (transition a (transition b (transition a r))) = r := by
  decide

/-- **Proposition 91: the flat sign `q ≡ −1` has no common phase.** A phase `z` with `z_{t·x} = −z_x` on every
link closes the squares (`(−1)⁴ = 1`) but not the walk `12345` (`(−1)⁵ = −1`), so it vanishes. -/
theorem flat_sign_no_clock (z : Fin 16 → ℂ) (hz : ∀ t x, z (transition t x) = -z x) : z = 0 := by
  funext r
  have h := hz 4 (transition 3 (transition 2 (transition 1 (transition 0 r))))
  rw [history_12345_closed, hz 3, hz 2, hz 1, hz 0] at h
  simp only [neg_neg] at h
  have h2 : (2 : ℂ) * z r = 0 := by rw [two_mul]; nth_rewrite 1 [h]; ring
  simpa using h2

theorem flat_sign_squares (a b : Fin 5) (r : Fin 16) : ((-1 : ℂ)) ^ 4 = 1 ∧ (-1 : ℂ) ^ 5 = -1 ∧
    transition b (transition a (transition b (transition a r))) = r := ⟨by norm_num, by norm_num, square_closed a b r⟩

/-! ## Proposition 99: the three pairings beside the last-step direction -/

/-- `1, −P, −E` on two systems. -/
noncomputable def XTheta : Fin 3 → Matrix Two Two ℂ := ![1, -swap, -Eop]

/-- The Gram `Tr(X_i X_j)/16` of `1, −P, −E`. -/
noncomputable def gramTheta : Matrix (Fin 3) (Fin 3) ℂ := Matrix.of fun i j => (XTheta i * XTheta j).trace / 16

/-- **`G_Θ = (5I − 𝖩₃)/4`.** -/
theorem gramTheta_eq : gramTheta = !![1, -1 / 4, -1 / 4; -1 / 4, 1, -1 / 4; -1 / 4, -1 / 4, 1] := by
  have tPP : (swap * swap).trace = 16 := by
    rw [ArticleStatements.swap_mul_swap, ArticleStatements.trace_one_two]
  have tEE : (Eop * Eop).trace = 16 := by
    rw [ArticleStatements.Eop_mul_Eop, Matrix.trace_smul, ArticleStatements.trace_Eop]; norm_num
  have tPE : (swap * Eop).trace = -4 := by
    rw [ArticleStatements.swap_mul_Eop, Matrix.trace_neg, ArticleStatements.trace_Eop]
  have tEP : (Eop * swap).trace = -4 := by
    rw [ArticleStatements.Eop_mul_swap, Matrix.trace_neg, ArticleStatements.trace_Eop]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gramTheta, XTheta, Matrix.trace_neg, ArticleStatements.trace_one_two, ArticleStatements.trace_swap,
      ArticleStatements.trace_Eop, tPP, tEE, tPE, tEP] <;> norm_num

/-- `B₃`: the three projectors in the basis `1, −P, −E`. -/
def B3 : Matrix (Fin 3) (Fin 3) ℂ := !![0, 2, 2; 0, -2, 2; -1, 0, 1]

/-- **The projectors `Π₀ = E/4`, `Π_F = (1 + P)/2`, `Π_L = (1 − P)/2 − E/4` are `(1/4) Σ_i (B₃)_{ia} X_i`.** -/
theorem pairing_irreps :
    (1 / 4 : ℂ) • ∑ i, B3 i 0 • XTheta i = ArticleStatements.projSinglet ∧
      (1 / 4 : ℂ) • ∑ i, B3 i 1 • XTheta i = ArticleStatements.projSymmetric ∧
      (1 / 4 : ℂ) • ∑ i, B3 i 2 • XTheta i = ArticleStatements.projVector := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · simp only [Fin.sum_univ_three, B3, XTheta, ArticleStatements.projSinglet, ArticleStatements.projSymmetric,
      ArticleStatements.projVector]
    simp
    try module

/-- **`B₃ᵀ G_Θ B₃ = diag(1, 10, 5)`**, the Gram matrix of the three projectors in `τ`, and `3(1 + 10 + 5) = 48`. -/
theorem pairing_gram_diag :
    B3ᵀ * gramTheta * B3 = Matrix.diagonal ![1, 10, 5] ∧ (3 : ℕ) * (1 + 10 + 5) = 48 := by
  refine ⟨?_, by norm_num⟩
  rw [gramTheta_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [B3, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal] <;> norm_num

/-- The three rotations beside the last-step direction `h = 0`: `K_j = γ_kγ_{c_j}` with `k = 1`. -/
def Kturn (c : Fin 5) : Matrix Four Four ℂ := γ 1 * γ c

theorem K_sq {c : Fin 5} (hc : c ≠ 1) : Kturn c * Kturn c = -1 :=
  γγ_sq (Ne.symm hc)

theorem K_anticomm {a b : Fin 5} (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b) :
    Kturn a * Kturn b = -(Kturn b * Kturn a) := by
  simp only [Kturn]
  have e1 : γ 1 * γ a * (γ 1 * γ b) = -(γ a * γ b) := by
    rw [show γ 1 * γ a * (γ 1 * γ b) = γ 1 * (γ a * γ 1) * γ b by simp only [Matrix.mul_assoc],
      γ_anticomm ha, Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc, γ_mul_self, Matrix.one_mul]
  have e2 : γ 1 * γ b * (γ 1 * γ a) = -(γ b * γ a) := by
    rw [show γ 1 * γ b * (γ 1 * γ a) = γ 1 * (γ b * γ 1) * γ a by simp only [Matrix.mul_assoc],
      γ_anticomm hb, Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc, γ_mul_self, Matrix.one_mul]
  rw [e1, e2, γ_anticomm hab, neg_neg]

theorem K_comm_lastDirection {c : Fin 5} (h0 : c ≠ 0) : Kturn c * γ 0 = γ 0 * Kturn c := by
  simp only [Kturn]
  rw [Matrix.mul_assoc, γ_anticomm h0, Matrix.mul_neg, ← Matrix.mul_assoc,
    γ_anticomm (show (1 : Fin 5) ≠ 0 by decide), Matrix.neg_mul, neg_neg, Matrix.mul_assoc]

/-- **The three pairings:** `(γ₁γ₂)(γ₃γ₄) = γ_h`, `(γ₁γ₃)(γ₂γ₄) = −γ_h`, `(γ₁γ₄)(γ₂γ₃) = γ_h`, so on the side
`γ_h = 1` each pairing has `γ_aγ_b = ±γ_cγ_d`. -/
theorem pairings_on_side :
    (γ 1 * γ 2) * (γ 3 * γ 4) = γ 0 ∧ (γ 1 * γ 3) * (γ 2 * γ 4) = -γ 0 ∧
      (γ 1 * γ 4) * (γ 2 * γ 3) = γ 0 := by
  have hp : γ 1 * γ 2 * γ 3 * γ 4 = γ 0 := by
    have h := γ_prod
    have : γ 0 * (γ 0 * γ 1 * γ 2 * γ 3 * γ 4) = γ 0 := by rw [h, Matrix.mul_one]
    simpa [← Matrix.mul_assoc, γ_mul_self] using this
  have a23 : γ 2 * γ 3 = -(γ 3 * γ 2) := γ_anticomm (by decide)
  have a24 : γ 2 * γ 4 = -(γ 4 * γ 2) := γ_anticomm (by decide)
  have a34 : γ 3 * γ 4 = -(γ 4 * γ 3) := γ_anticomm (by decide)
  refine ⟨?_, ?_, ?_⟩
  · simpa [Matrix.mul_assoc] using hp
  · have : γ 1 * γ 3 * (γ 2 * γ 4) = -(γ 1 * γ 2 * γ 3 * γ 4) := by
      calc γ 1 * γ 3 * (γ 2 * γ 4) = γ 1 * (γ 3 * γ 2) * γ 4 := by simp only [Matrix.mul_assoc]
        _ = γ 1 * (-(γ 2 * γ 3)) * γ 4 := by rw [γ_anticomm (show (3 : Fin 5) ≠ 2 by decide)]
        _ = -(γ 1 * γ 2 * γ 3 * γ 4) := by simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    rw [this, hp]
  · have : γ 1 * γ 4 * (γ 2 * γ 3) = γ 1 * γ 2 * γ 3 * γ 4 := by
      calc γ 1 * γ 4 * (γ 2 * γ 3) = γ 1 * (γ 4 * γ 2) * γ 3 := by simp only [Matrix.mul_assoc]
        _ = -(γ 1 * γ 2 * (γ 4 * γ 3)) := by
          rw [γ_anticomm (show (4 : Fin 5) ≠ 2 by decide)]
          simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
        _ = γ 1 * γ 2 * γ 3 * γ 4 := by
          rw [γ_anticomm (show (4 : Fin 5) ≠ 3 by decide)]
          simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg, Matrix.mul_assoc]
    rw [this, hp]

end Comparison.Article
