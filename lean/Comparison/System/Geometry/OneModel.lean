import Comparison.System.Geometry.Definitions

/-!
# The geometry of comparison, Book V: one model (Proposition 23)

Proposition 23 is the uniqueness theorem of the
spine (`System.uniqueness`, `System/Postulates.lean`) read in the words: every
candidate system (P1 to P3 in mathematical form) has a basis `u₁, −Θu₁, u₂, −Θu₂` in which the
quaternionic structure is `Θv = J₀v̄` with `J₀ = 1 ⊗ iσ_y`, the five directions are `σ_x ⊗ 1, σ_z ⊗ 1, σ_y ⊗ σ_x,
σ_y ⊗ σ_y, σ_y ⊗ σ_z` with product one, and two such bases differ by one rotation of `Sp(2)`.
-/

open scoped InnerProductSpace Kronecker
open Matrix Complex Module

namespace Comparison.System

namespace Geometry

/-- `J₀ = 1 ⊗ iσ_y`. -/
theorem J_eq_one_kron_iσy : J = (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (Complex.I • σ₂) := by
  have h : ε = Complex.I • σ₂ := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ε, σ₂]
  rw [J, h]

end Geometry

open Comparison.System.Geometry

/-- **Proposition 23 (one model).** The model: `J₀ = 1 ⊗ iσ_y`, the five directions `σ_x ⊗ 1, σ_z ⊗ 1,
σ_y ⊗ σ_x, σ_y ⊗ σ_y, σ_y ⊗ σ_z` with `γ₁γ₂γ₃γ₄γ₅ = 1`. Every candidate system `S` (P1 to P3 in
mathematical form) has four complex dimensions and a basis `u₁, −Θu₁, u₂, −Θu₂` (a gauge); in every
gauge `Θv = J₀v̄` in coordinates, the five directions pulled back from the model are distinctions of `S`
with matrix `γ_s`, anticommuting and of product one, and every distinction is a unique real
combination of them; two gauges differ by one rotation of `Sp(2)`; and any two candidate systems are
isometric with quaternionic structure carried to quaternionic structure. Every candidate system: `System.uniqueness`.
Recognition: none. -/
theorem prop_23 :
    J = (1 : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (Complex.I • σ₂) ∧
    γ = ![σ₁ ⊗ₖ 1, σ₃ ⊗ₖ 1, σ₂ ⊗ₖ σ₁, σ₂ ⊗ₖ σ₂, σ₂ ⊗ₖ σ₃] ∧
    γ 0 * γ 1 * γ 2 * γ 3 * γ 4 = 1 ∧
    (∀ S : CandidateSystem, finrank ℂ S.H = 4 ∧ Nonempty S.Frame ∧
      ∀ f : S.Frame, (∀ k : Fin 2, f.b (k, 1) = -S.partner.Θ (f.b (k, 0))) ∧
        (∀ v : S.H, f.e (S.partner.Θ v) = modelΘ (f.e v)) ∧
        (∀ s, f.lines s ∈ S.Q) ∧ (∀ s, f.conj (f.lines s) = γ s) ∧
        (∀ s t, f.lines s * f.lines t + f.lines t * f.lines s =
          (if s = t then (2 : ℂ) else 0) • (1 : S.H →ₗ[ℂ] S.H)) ∧
        f.lines 0 * f.lines 1 * f.lines 2 * f.lines 3 * f.lines 4 = 1 ∧
        (∀ a ∈ S.Q, ∃! t : Fin 5 → ℝ, a = ∑ s, (t s : ℂ) • f.lines s)) ∧
    (∀ S : CandidateSystem, ∀ f f' : S.Frame, ∃ U ∈ Sp2, ∀ w : ModelH,
      f'.e (f.e.symm w) = WithLp.toLp 2 ((U : Matrix Four Four ℂ) *ᵥ WithLp.ofLp w)) ∧
    (∀ S S' : CandidateSystem,
      ∃ e : S.H ≃ₗᵢ[ℂ] S'.H, ∀ v, e (S.partner.Θ v) = S'.partner.Θ (e v)) := by
  refine ⟨J_eq_one_kron_iσy, rfl, γ_prod, fun S => ?_, fun S f f' => frames_differ f f',
    systems_isomorphic⟩
  obtain ⟨h4, -, hf, hl, -, -, -⟩ := uniqueness S
  refine ⟨h4, hf, fun f => ⟨f.normal, f.e_partner, (hl f).1, f.conj_lines, (hl f).2.1,
    (hl f).2.2.1, (hl f).2.2.2⟩⟩

end Comparison.System
