import Comparison.GroupsContinuumLaw.Chart
import Comparison.GroupsContinuumLaw.Schur
import Comparison.GroupsContinuumLaw.Symbol
import Comparison.GroupsContinuumLaw.RestPole
import Comparison.GroupsContinuumLaw.Cone

/-!
# The continuum limit (Eqs. 28, 30, 36; Prop. 63), assembled

derivation in one statement, each part a theorem of this folder:

1. `Chart.lean`: the two-sheet `A₄` chart lifts the step: `B_N · Lift = Lift · B` for every even `N`;
2. `Schur.lean`: the exact Schur identity
   `(1 + 4u²) − (u²/(1 + 4u²)) FG = ρ(u, ε) · (M_ε(u)² + L_ε)`, `M_ε(u)² = ((u⁻¹ + 4u)² − 25)/(5ε²)`;
3. `Symbol.lean`: the interpolated Euclidean resolvents differ by at most `5π²ε²/24` in norm;
4. `RestPole.lean`: the rest pole `u = 2/(s + √(s² − 16))`, `s = 3 + 2cosh(εΩ/√2)`, solves
   `(u⁻¹ + 4u)² = 25 + 5ε² κ`, and lies in `(0, ¼]`;
5. `Cone.lean`: the balanced cone of the held plane, `(S¹ × S³)/ℤ₂` with signature `(1, 3)`, and its
   central kept rotation `J`.
-/

namespace Comparison.GroupsContinuumLaw

open Matrix MeasureTheory

/-- **The continuum limit, as one theorem.** -/
theorem continuum_limit :
    (∀ (N : ℕ) [NeZero N] (hN : 2 ∣ N),
      (chartStep (N := N) * liftM hN : Matrix (VN N × Fin 5) (Fin 16 × Fin 5) ℂ) =
        liftM hN * stepOp transitionMat) ∧
    (∀ {n : Type} [Fintype n] [DecidableEq n] (F G : Matrix n n ℂ) (u ε : ℂ), u ≠ 0 → ε ≠ 0 →
      1 + 4 * u ^ 2 ≠ 0 →
      (1 + 4 * u ^ 2) • (1 : Matrix n n ℂ) - (u ^ 2 / (1 + 4 * u ^ 2)) • (F * G) =
        schurScale u ε • normalizedQ F G u ε) ∧
    (∀ (ε M : ℝ), ε ≠ 0 → ∀ (μ : Measure (Fin 5 → ℝ)), (∀ᵐ p ∂μ, ∑ i, p i = 0) →
      ∀ f : (Fin 5 → ℝ) → ℂ, AEStronglyMeasurable f μ →
      eLpNorm (fun p => ((latticeMult ε M p - continuumMult M p : ℝ) : ℂ) * f p) 2 μ ≤
        ENNReal.ofReal (normConst ε) * eLpNorm f 2 μ) ∧
    (∀ ε Ω : ℝ, ε ≠ 0 →
      ((uPole ε Ω)⁻¹ + 4 * uPole ε Ω) ^ 2 = 25 + 5 * ε ^ 2 * kappaR ε Ω ∧
        0 < uPole ε Ω ∧ uPole ε Ω ≤ 1 / 4) ∧
    (∀ v : Fin 6 → ℝ, OnCone v → r2 v = 1 →
      s2 v = 1 ∧
      (∀ i j, g6 (frame v i) (frame v j) = if i = j then (if i = 0 then 1 else -1) else 0) ∧
      (∀ i, g6 v (frame v i) = 0) ∧
      frame v 0 = J6 *ᵥ v ∧
      (∀ w, g6 v w = 0 → ∃! c : Fin 5 → ℝ, w = c 0 • v + c 1 • frame v 0 + c 2 • frame v 1 +
        c 3 • frame v 2 + c 4 • frame v 3) ∧
      (∀ X, CentralKept6 X ↔ ∃ a : ℝ, X = a • J6)) :=
  ⟨fun _ _ hN => lifted_B_intertwines hN,
   fun F G u ε hu hε ha => normalized_schur F G u ε hu hε ha,
   fun ε M hε μ hμ f hf => resolvent_norm_bound ε M hε μ hμ f hf,
   fun ε Ω hε => ⟨rest_pole_parameter ε Ω hε, (uPole_bounds ε Ω).1, (uPole_bounds ε Ω).2⟩,
   fun v hv hr => balanced_cone v hv hr⟩

end Comparison.GroupsContinuumLaw
