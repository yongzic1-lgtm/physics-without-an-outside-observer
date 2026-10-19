import Comparison.System.Completion.Numbers
import Comparison.System.Table.Couplings
import Comparison.Law.Rule
import Comparison.Law.Carried
import Comparison.Law.Rows
import Comparison.Law.Source
import Comparison.RuleAndLaw.FactorsA
import Comparison.RuleAndLaw.FactorsB
import Comparison.Colour.Inventory
import Comparison.WholePicture.OneArc
import Comparison.GroupsContinuumLaw.Rate
import Comparison.Formulas.Rules

set_option linter.style.longLine false

/-!
# The proof system, the completions, part 6: every factor at its divided set (SI Props. 200, 203, 205, 206)

The rule's values at a divided set `S ⊆ {n, h, k, c₁, c₂, c₃}` with `k_S` lines and
`P = z_S² = (−1)^{|S|}`; the electron as the least count; the three lines outside the plane; the clock's overlap.
-/

namespace Comparison.System.Completion.Comp

open Comparison Comparison.Law

/-- **The four classes of divided sets:** `32` even, `2` odd with `|L| = 5` (`{n}` and the five directions), `10` odd with
`|L| = 3` (a line alone and its complement), `20` odd with `|L| = 1` (type `⟨3,3⟩`). -/
theorem rule_class_counts :
    (Finset.univ.filter fun S : Finset (Fin 6) => signS S = 1).card = 32 ∧
    (Finset.univ.filter fun S : Finset (Fin 6) => signS S = -1 ∧ |LZ S| = 5).card = 2 ∧
    (Finset.univ.filter fun S : Finset (Fin 6) => signS S = -1 ∧ |LZ S| = 3).card = 10 ∧
    (Finset.univ.filter fun S : Finset (Fin 6) => signS S = -1 ∧ |LZ S| = 1).card = 20 := by
  decide

/-- `σ₅ = (2/5)𝐉 − I`, the comparison on the five directions. -/
noncomputable def sigma5 : Matrix (Fin 5) (Fin 5) ℂ := (2 / 5 : ℂ) • Matrix.of (fun _ _ => 1) - 1

/-- **`det σ₅[K, K] = (−1)^{|K|}(1 − 2|K|/5)`** for every set `K` of lines. -/
theorem sigma5_minor (K : Finset (Fin 5)) :
    (sigma5.submatrix (Subtype.val : K → Fin 5) Subtype.val).det = (-1) ^ K.card * (1 - 2 / 5 * (K.card : ℂ)) := by
  have hsub : sigma5.submatrix (Subtype.val : K → Fin 5) Subtype.val =
      -(1 - Matrix.of (fun (_ : K) (_ : Unit) => (2 / 5 : ℂ)) * Matrix.of (fun (_ : Unit) (_ : K) => (1 : ℂ))) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [sigma5, Matrix.mul_apply]
    · have hv : (i : Fin 5) ≠ j := fun h => hij (Subtype.ext h)
      simp [sigma5, Matrix.mul_apply, Matrix.one_apply_ne hij, Matrix.one_apply_ne hv]
  rw [hsub, Matrix.det_neg, Matrix.det_one_sub_mul_comm, Matrix.det_unique, Fintype.card_coe]
  congr 1
  simp [Matrix.mul_apply, Finset.sum_const, Finset.card_univ, Fintype.card_coe]
  ring

/-- The lines of a divided set of the six, as a set of the five. -/
theorem lines_card : ∀ S : Finset (Fin 6), (Finset.univ.filter fun i : Fin 5 => i.succ ∈ S).card = linesIn S := by
  decide +kernel

/-- `t = 1 − e`: `2/5` at the even divided sets and `2` at the twenty of type `⟨3,3⟩`. -/
theorem t_classes (S : Finset (Fin 6)) : (signS S = 1 → tS S = 2 / 5) ∧ (signS S = -1 → |LZ S| = 1 → tS S = 2) := by
  have ht : tS S = 1 - eS S := by
    show 2 * ‖wS S‖ = 1 - (1 - 2 * ‖wS S‖)
    ring
  refine ⟨fun h => ?_, fun h h1 => ?_⟩
  · rw [ht, ((RuleAndLaw.rule_values_classes S).1 h).1]; norm_num
  · rw [ht, ((RuleAndLaw.rule_values_classes S).2.2.2 h h1).1]; norm_num

end Comparison.System.Completion.Comp

namespace Comparison.System

open Real Complex Matrix Kronecker Filter Topology Comparison Comparison.Law Comparison.System.Completion

/-- **Proposition 200 (the one rule at every divided set).** For `S ⊆ {n, h, k, c₁, c₂, c₃}` with `k_S` lines and
`P = z_S² = (−1)^{|S|}`: `z_S = i^{|S|} = Λ(iI)_{SS}`; `L_S = (5 − k_S) + k_SP = 5 − (5/2)(1 − P)(1 + det Σ₆[S,S])`,
`5` at even `S` and `−5 det Σ₆[S,S] = 5(−1)^{k_S}det σ₅[S ∩ lines]` at odd `S` (`σ₅ = (2/5)𝐉 − I`), with
`det Σ₆[S,S] = (−1)^{|S|}(1 − 2k_S/5)`; `w_S = z_S/L_S`,
`u_S = z_S/4` (`u_S² = P/16`), power `(3 + P)/4`; `Φ_S = −1/(16 + 3P)`, `Ψ_S = P/(L_S² + 3P)`, `|w_S| = 1/|L_S|`,
`e_S = 1 − 2|w_S|`, `t_S = 2|w_S|`; `N(S) = |S|(6 − |S|) + [|S| odd]`, the rotations with one end in `S` and one more
at odd `S`; a divided set and its counterpart with `n` added have the same lines and opposite `P`. The values depend on `(P, |L_S|)` only:
at the `32` even divided sets `e = 3/5`, `t = 2/5`, `Ψ = 1/28`, `Φ = −1/19`; at the `2` odd divided sets with `|L| = 5`
`e = 3/5`, `Ψ = −1/22`; at the `10` with `|L| = 3` `e = 1/3`, `Ψ = −1/6`; at the `20` of type `⟨3,3⟩` `e = −1`,
`t = 2`, `Ψ = 1/2` (and `Φ = −1/13` at every odd divided set); `Ψ = 1/(15 + 13P)` exactly at the even and the `⟨3,3⟩` divided sets
(`52`), and `e = 1 − 2/(4 + P)` exactly at the even and the line-alone divided sets (`42`). -/
theorem prop_200 :
    (∀ S : Finset (Fin 6), zS S = Complex.I ^ S.card ∧
      zS S = extPow (Complex.I • (1 : Matrix (Fin 6) (Fin 6) ℂ)) S S) ∧
    (∀ S : Finset (Fin 6), LS S = (5 - (linesIn S : ℂ)) + (linesIn S : ℂ) * zS S ^ 2 ∧
      LS S = 5 - 5 / 2 * (1 - zS S ^ 2) * (1 + minor carriedC S S)) ∧
    (∀ S : Finset (Fin 6), Even S.card → LS S = 5) ∧
    (∀ S : Finset (Fin 6), Odd S.card → LS S = -5 * minor carriedC S S) ∧
    (∀ S : Finset (Fin 6), minor (carried ℂ) S S = (-1) ^ S.card * (1 - 2 / 5 * (linesIn S : ℂ))) ∧
    (∀ S : Finset (Fin 6), wS S = zS S / LS S ∧ uS S = zS S / 4 ∧ uS S ^ 2 = (signS S : ℂ) / 16 ∧
      powS S = (3 + (signS S : ℝ)) / 4) ∧
    (∀ S : Finset (Fin 6), PhiS S = -1 / (16 + 3 * (signS S : ℂ)) ∧
      PsiS S = (signS S : ℂ) / (LS S ^ 2 + 3 * (signS S : ℂ)) ∧ ‖wS S‖ = 1 / |(LZ S : ℝ)| ∧
      eS S = 1 - 2 * ‖wS S‖ ∧ tS S = 2 * ‖wS S‖) ∧
    (∀ S : Finset (Fin 6), NS S = S.card * (6 - S.card) + (if Odd S.card then 1 else 0) ∧
      ((Finset.univ.powersetCard 2).filter fun p : Finset (Fin 6) => (p ∩ S).card = 1).card +
        (if Odd S.card then 1 else 0) = NS S) ∧
    (∀ S : Finset (Fin 6), linesIn (twin S) = linesIn S ∧ signS (twin S) = -signS S) ∧
    (∀ S : Finset (Fin 6),
      (signS S = 1 → eS S = 3 / 5 ∧ PsiS S = 1 / 28 ∧ PhiS S = -1 / 19) ∧
      (signS S = -1 → |LZ S| = 5 → eS S = 3 / 5 ∧ PsiS S = -1 / 22 ∧ PhiS S = -1 / 13) ∧
      (signS S = -1 → |LZ S| = 3 → eS S = 1 / 3 ∧ PsiS S = -1 / 6 ∧ PhiS S = -1 / 13) ∧
      (signS S = -1 → |LZ S| = 1 → eS S = -1 ∧ PsiS S = 1 / 2 ∧ PhiS S = -1 / 13)) ∧
    ((Finset.univ.filter fun S : Finset (Fin 6) => signS S = 1).card = 32 ∧
      (Finset.univ.filter fun S : Finset (Fin 6) => signS S = -1 ∧ |LZ S| = 5).card = 2 ∧
      (Finset.univ.filter fun S : Finset (Fin 6) => signS S = -1 ∧ |LZ S| = 3).card = 10 ∧
      (Finset.univ.filter fun S : Finset (Fin 6) => signS S = -1 ∧ |LZ S| = 1).card = 20) ∧
    (∀ S : Finset (Fin 6), PsiS S = 1 / (15 + 13 * (signS S : ℂ)) ↔
      (Even S.card ∨ linesIn S = 2 ∨ linesIn S = 3)) ∧
    (Finset.univ.filter fun S : Finset (Fin 6) => Even S.card ∨ linesIn S = 2 ∨ linesIn S = 3).card = 52 ∧
    (∀ S : Finset (Fin 6), eS S = 1 - 2 / (4 + (signS S : ℝ)) ↔ (signS S = 1 ∨ linesIn S = 1 ∨ linesIn S = 4)) ∧
    (Finset.univ.filter fun S : Finset (Fin 6) => signS S = 1 ∨ linesIn S = 1 ∨ linesIn S = 4).card = 42 ∧
    (∀ S : Finset (Fin 6), (signS S = 1 → tS S = 2 / 5) ∧ (signS S = -1 → |LZ S| = 1 → tS S = 2)) ∧
    (∀ S : Finset (Fin 6), Odd S.card → -5 * minor carriedC S S =
      5 * (-1) ^ linesIn S *
        (Comp.sigma5.submatrix (Subtype.val : (Finset.univ.filter fun i : Fin 5 => i.succ ∈ S) → Fin 5)
          Subtype.val).det) :=
  ⟨fun S => ⟨rfl, zS_eq_whole S⟩, fun S => ⟨rfl, LS_carried S⟩, fun S h => LS_even h, fun S h => LS_odd h,
    fun S => minor_carried_self ℂ S, fun S => ⟨rfl, rfl, uS_sq S, powS_eq S⟩,
    fun S => ⟨PhiS_eq S, PsiS_eq S, norm_wS S, rfl, rfl⟩, fun S => ⟨rfl, NS_turns S⟩,
    fun S => ⟨twin_lines S, twin_sign S⟩, RuleAndLaw.rule_values_classes, Comp.rule_class_counts,
    fun S => (PsiS_plane S).1, RuleAndLaw.card_psi_compact, eS_four, RuleAndLaw.card_e_compact,
    fun S => Comp.t_classes S, fun S hS => by
      have hm : minor carriedC S S = (-1) ^ S.card * (1 - 2 / 5 * (linesIn S : ℂ)) := minor_carried_self ℂ S
      have hsq : ((-1 : ℂ) ^ linesIn S) * (-1) ^ linesIn S = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]; norm_num
      rw [Comp.sigma5_minor, Comp.lines_card, hm, Odd.neg_one_pow hS]
      linear_combination (-5 * (1 - 2 / 5 * (linesIn S : ℂ))) * hsq⟩

/-- **Proposition 203 (the unit: the electron is the least count).** Every weight `X` on the arcs turns the long-range
zero at `v_X = Σ_arcs X/320` per unit phase per step (`arg ψ(−iθ)` has the derivative `−v_X`; one arc: `1/320`; the
available transitions weight: `1836/320`); `Tr B⁴ = 320`: from
each state and each first step `a ≠ t` exactly one closed walk of length four, `a t a t`, of sign
`γ_tγ_aγ_tγ_a = −1`; the available transitions weight of a transition `⟨Ω, (L + γ_h ⊗ γ_t)Ω⟩ = 6 + [t = h]` is an integer; marking one arc
with `z` gives `det(I − uB_z) = D(u) + (z − 1)uD′(u)/320`; the least count is one arc at the weight
`z@{} = det Σ₆[∅,∅] = 1`, `|u@{}|/80 = 1/320`; among the nonnegative integral marks the least positive pole of the
rest pencil is `1/320`, attained exactly at one arc carrying one unit.

Recognition: the electron, the unit of every ratio; `m_p/m_e = 1836` plus the proton's own terms. -/
theorem prop_203 (h : Fin 5) (a₀ s₀ : State) (h₀ : Continues a₀ s₀) :
    (∀ (s : State) (a : Fin 5), a ≠ s.2 →
      ((Finset.univ : Finset (Fin 5 × Fin 5 × Fin 5)).filter fun q =>
        q.1 ≠ a ∧ q.2.1 ≠ q.1 ∧ q.2.2 ≠ q.2.1 ∧
          RuleAndLaw.stepAlong (RuleAndLaw.stepAlong (RuleAndLaw.stepAlong (RuleAndLaw.stepAlong s a) q.1) q.2.1) q.2.2 = s) = {(s.2, a, s.2)}) ∧
    (∀ {a t : Fin 5}, a ≠ t → γ t * γ a * γ t * γ a = -1) ∧
    (B ℚ ^ 4).trace = 320 ∧
    (∀ t : Fin 5, star Ω ⬝ᵥ ((L + γ h ⊗ₖ γ t) *ᵥ Ω) = 6 + if t = h then 1 else 0) ∧
    (∀ (p q : State), Continues q p → ∀ z u : ℂ,
      (1 - u • WholePicture.Bmark p q z).det =
        WholePicture.lawPoly.eval u + (z - 1) * u * (Polynomial.derivative WholePicture.lawPoly).eval u / 320) ∧
    (zS sHere = 1 ∧ minor carriedC sHere sHere = 1 ∧ ‖uS sHere‖ / 80 = 1 / 320 ∧
      piU ⬝ᵥ (hadPow ((1 / 4 : ℝ) • B ℝ) (oneTransitionX a₀ s₀) 1 *ᵥ 1) = 1 / 320 ∧
      piU ⬝ᵥ (hadPow ((1 / 4 : ℝ) • B ℝ) (availableTransitionsLawX h (transitionX h)) 1 *ᵥ 1) = 1836 / 320) ∧
    (∀ X : Matrix State State ℝ,
      piU ⬝ᵥ (hadPow ((1 / 4 : ℝ) • B ℝ) X 1 *ᵥ 1) =
        (1 / 320) * ∑ s : State, ∑ s' : State, (if Continues s s' then X s' s else 0) ∧
      ∃ ψ : ℂ → ℂ, ψ 0 = 1 ∧ (∀ᶠ s in 𝓝 0, charF ((1 / 4 : ℝ) • B ℝ) X s (ψ s) = 0) ∧
        HasDerivAt (fun θ : ℝ => Complex.arg (ψ (-I * θ)))
          (-(piU ⬝ᵥ (hadPow ((1 / 4 : ℝ) • B ℝ) X 1 *ᵥ 1))) 0) ∧
    (∀ X : State → State → ℕ, 0 < GroupsContinuumLaw.natTotal X →
      (1 : ℚ) / 320 ≤ GroupsContinuumLaw.rate (fun p q => (X p q : ℚ)) ∧
      (GroupsContinuumLaw.rate (fun p q => (X p q : ℚ)) = 1 / 320 ↔
        ∃ e ∈ Comparison.arcs, X e.2 e.1 = 1 ∧ ∀ f ∈ Comparison.arcs, f ≠ e → X f.2 f.1 = 0)) :=
  ⟨RuleAndLaw.one_closed_four, fun h => RuleAndLaw.four_history_sign h, RuleAndLaw.trace_four, fun t => transition_weight h t,
    fun p q hpq z u => WholePicture.one_arc p q hpq z u, RuleAndLaw.least_count h a₀ s₀ h₀,
    fun X => ⟨lawP_rate X, by
      obtain ⟨ψ, h0, h1, -, h3⟩ := angle_of_zero lawP X piU (lawP_weighted X)
      exact ⟨ψ, h0, h1, h3⟩⟩,
    fun X hX => ⟨(GroupsContinuumLaw.least_positive_pole X hX).2.1, (GroupsContinuumLaw.least_positive_pole X hX).2.2⟩⟩

/-- **Proposition 205 (the three lines outside the plane).** On the word `C` (`k_C = 3` lines) a quantity `q` alike on
each line gives the principal minor `q^{k_C}` and the trace `k_Cq`; the principal minors of a diagonal source expand
`det(1 + diag(j)M) = Σ_S Π_{i∈S}j_i det M[S,S]`; the `Δ`, the three last-step directions aligned:
`m_Δ/m_p = k_Cb = |u@{}|Var P/Eℓ = 21/16` with `k_C = (L@{} − L@C)/2`; gravity: `W = Π_C(t^{Eℓ}η^{E_H}) =
(2/5)^{48}(295/296)^9` with `t@{n, k} = 2/5`; the weak angle `ŝ² = Tr_C N_h = k_CN_h`; the clock's overlap
`h = (Σ_D(p_νp_{−ν})^{1/2})^{k_C}` (Prop. 206). -/
theorem prop_205 :
    (∀ q : ℝ, (diagonal fun _ : Fin 3 => q).det = q ^ 3 ∧ (diagonal fun _ : Fin 3 => q).trace = 3 * q) ∧
    (∀ {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ) (j : n → ℝ),
      (1 + diagonal j * M).det = ∑ S : Finset n, (∏ i ∈ S, j i) * (M.submatrix (Subtype.val : S → n) Subtype.val).det) ∧
    ((((LZ sHere - LZ sC) / 2 : ℤ) : ℝ) * (bS sHere).re = 21 / 16 ∧ ‖uS sHere‖ * Num.VarP / Num.El = 21 / 16 ∧
      (((LZ sHere - LZ sC) / 2 : ℤ) : ℝ) * (bS sHere).re = rowDelta) ∧
    ((LZ sHere - LZ sC) / 2 = 3) ∧
    (tS sLineSinglet = 2 / 5 ∧ sC.card = 3 ∧
      ∏ _c ∈ sC, (tS sLineSinglet ^ Num.El * Num.eta ^ Num.EH) = Num.W) ∧
    Num.W = (2 / 5 : ℝ) ^ 48 * (295 / 296) ^ 9 ∧
    Num.sw2 = (Num.kC : ℝ) * Num.Nh ∧
    hOv sLastDirectionSinglet = (∑ i, Real.sqrt (RuleAndLaw.tiltLaw (9 / 4000) i * RuleAndLaw.tiltLaw (-(9 / 4000)) i)) ^ 3 := by
  have hg := RuleAndLaw.gravity_three_excursions
  refine ⟨fun q => ⟨?_, ?_⟩, fun M j => det_one_add_diagonal_mul M j,
    ⟨(RuleAndLaw.delta_three).1, by rw [Num.VarP_eq, Num.El_eq]; exact (RuleAndLaw.delta_three).2.1,
      (RuleAndLaw.delta_three).2.2⟩, by decide, ⟨hg.1, hg.2.1, ?_⟩, Num.W_closed, ?_, RuleAndLaw.clock_overlap.1⟩
  · rw [det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · rw [trace_diagonal, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  · rw [Finset.prod_const, hg.2.1, hg.1, Num.El_eq, Num.EH_eq, Num.eta_eq, Num.W_closed,
      show (16 : ℝ) = ((16 : ℕ) : ℝ) by norm_num, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num]
    simp only [Real.rpow_natCast]
    ring
  · rw [Num.sw2, Num.kC_eq]
    norm_num

/-- **Proposition 206 (the clock's overlap and its exponent `−3/2`).** The clock at `{h, n}` has the five marks
`(0, 1, 2, 3, 19)/4`, the last `1/(4|Φ@{h,n}|)`, ten gaps `D` with `E_D = 2` and `Var D = 61/16`, and the rate
`ν = e@{h,n}²/(E_PEℓ) = 9/4000`; the gap law tilted at `x` is `p_x(D) = e^{−xD}/(10M_Q(x))`;
`Σ_D(p_ν(D)p_{−ν}(D))^{1/2} = [M_Q(ν)M_Q(−ν)]^{−1/2}`, and
`h = (Σ_D(p_νp_{−ν})^{1/2})^{k_C} = [M_Q(ν)M_Q(−ν)]^{−k_Cs@{h}} = [M_Q(ν)M_Q(−ν)]^{−3/2} = 0.9999710493297`;
`−log h/ν² → (3/2)Var D` as `ν → 0`. The fourth order `−log h = (3/2)Var D ν² + O(ν⁴)` with its bound is
`Comp.clock_fourth_order` (`Clock.lean`); the whole proposition is `prop_206` (`Whole.lean`). -/
theorem Completion.Comp.clock_overlap :
    clockMarks sLastDirectionSinglet = ![0, 1 / 4, 2 / 4, 3 / 4, longMark sLastDirectionSinglet / 4] ∧ longMark sLastDirectionSinglet = 19 ∧
    longMark sLastDirectionSinglet = 1 / ‖PhiS sLastDirectionSinglet‖ ∧
    ((1 / 10) * ∑ i, clockGap sLastDirectionSinglet i = 2 ∧ (1 / 10) * ∑ i, clockGap sLastDirectionSinglet i ^ 2 - 2 ^ 2 = 61 / 16) ∧
    nuS sLastDirectionSinglet = eS sLastDirectionSinglet ^ 2 / (Num.EP * Num.El) ∧ Num.nu = 9 / 4000 ∧
    (∀ x : ℝ, ∀ i, RuleAndLaw.tiltLaw x i = Real.exp (-(x * clockGap sLastDirectionSinglet i)) / (10 * clockMQ sLastDirectionSinglet x)) ∧
    (∀ x : ℝ, ∑ i, Real.sqrt (RuleAndLaw.tiltLaw x i * RuleAndLaw.tiltLaw (-x) i) =
      (clockMQ sLastDirectionSinglet x * clockMQ sLastDirectionSinglet (-x)) ^ (-(1 / 2 : ℝ))) ∧
    (hOv sLastDirectionSinglet = (∑ i, Real.sqrt (RuleAndLaw.tiltLaw (9 / 4000) i * RuleAndLaw.tiltLaw (-(9 / 4000)) i)) ^ 3 ∧
      hOv sLastDirectionSinglet = (clockMQ sLastDirectionSinglet (9 / 4000) * clockMQ sLastDirectionSinglet (-(9 / 4000))) ^
        (-(((((LZ sHere - LZ sC) / 2 : ℤ) : ℝ)) * powS sLastDirection))) ∧
    hOv sLastDirectionSinglet = (clockMQ sLastDirectionSinglet (9 / 4000) * clockMQ sLastDirectionSinglet (-(9 / 4000))) ^ (-(3 / 2 : ℝ)) ∧
    ((0.99997104932965 : ℝ) < hOv sLastDirectionSinglet ∧ hOv sLastDirectionSinglet < 0.99997104932975) ∧
    Tendsto (fun ν : ℝ => -Real.log (Formulas.clockTilt ν) / ν ^ 2) (𝓝[≠] 0) (𝓝 (3 / 2 * (61 / 16))) ∧
    hOv sLastDirectionSinglet = Formulas.clockTilt (9 / 4000) := by
  refine ⟨rfl, piece_longMark_hn, rfl, clock_moments, by rw [Num.EP_eq, Num.El_eq]; rfl, Num.nu_eq,
    fun x i => rfl, RuleAndLaw.bhattacharyya,
    RuleAndLaw.clock_overlap, piece_h, ?_, Formulas.clock_sweep_limit, Formulas.hOv_is_tilt⟩
  rw [Article.hOv_eq]
  exact Article.qH_bnd.strict (by norm_num) (by norm_num)

end Comparison.System
