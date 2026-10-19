import Comparison.System.Postulates
import Comparison.System.Law.Equations
import Comparison.RuleAndLaw.CriticalGerm
import Comparison.GroupsContinuumLaw.SignCover

/-!
# The proof system, the law: Proposition 114, the critical germ

The Laplacian `5 − A` on the characters and its pseudo-determinant
(`RuleAndLaw/CriticalGerm.lean`), the Green function and the resistances (`Law/Equations.lean`: `eq_20`), the sign cover
(`GroupsContinuumLaw/SignCover.lean`). `prop_114` proves the whole statement except the count of spanning trees; the
count of the 2³¹ spanning trees stands on Kirchhoff's matrix-tree theorem, outside Mathlib v4.35.0, and completes
Prop. 114.
-/

open Matrix Comparison Polynomial

namespace Comparison.System

open Comparison.System.Law

/-- **Proposition 114, the critical germ** (all but the spanning trees). At `u = 1/4` the law's operator on the
sixteen is `(5 − A)/4`; `5 − A` is diagonal on the characters (`(5 − A)χ = χ diag(5 − λ_l)`, `χχ = 16`) with the
eigenvalues `0` once, `4` ten times, `8` five times, so `det′(5 − A) = 4¹⁰8⁵ = 2³⁵`; `(5 − A)⁺ = (7 + A)/32 − 3J/128`
(the four Penrose equations and uniqueness); the resistance from here is `7/16 = b` to every plane and `3/8` to every
line; on the sign cover (the thirty-two signed two-spinor states) `det(I − uB̃) = det(I − uB)·det(I − uB₋)` and the zero at
`u = −1` has order `48 = 80 − 32`, at `u = 1` order `49`: the eigenvalue `−1` of the step has multiplicity `48` and
`+1` multiplicity `49`. Every candidate system: System.uniqueness. -/
theorem prop_114 :
    (∀ u : ℝ, u = 1 / 4 → (1 + 4 * u ^ 2) • (1 : Matrix (Fin 16) (Fin 16) ℝ) - u • A ℝ =
      (1 / 4 : ℝ) • ((5 : ℝ) • (1 : Matrix (Fin 16) (Fin 16) ℝ) - A ℝ)) ∧
    ((5 : ℤ) • (1 : Matrix (Fin 16) (Fin 16) ℤ) - A ℤ) * charTable =
      charTable * Matrix.diagonal (fun l => 5 - charValue l) ∧
    charTable * charTable = (16 : ℤ) • 1 ∧
    ((∏ l ∈ Finset.univ.filter (fun l : Fin 16 => l ≠ 0), (5 - charValue l)) = 2 ^ 35 ∧
      (5 - charValue 0) = 0 ∧
      (Finset.univ.filter (fun l : Fin 16 => 5 - charValue l = 4)).card = 10 ∧
      (Finset.univ.filter (fun l : Fin 16 => 5 - charValue l = 8)).card = 5) ∧
    (Finset.univ.filter (fun l : Fin 16 => 5 - charValue l = 0)).card = 1 ∧
    (WholePicture.lapM = (5 : ℝ) • (1 : Matrix (Fin 16) (Fin 16) ℝ) - A ℝ ∧
      WholePicture.greenM = (1 / 32 : ℝ) • ((7 : ℝ) • (1 : Matrix (Fin 16) (Fin 16) ℝ) + A ℝ) -
        (3 / 128 : ℝ) • Matrix.of (fun _ _ => (1 : ℝ))) ∧
    (WholePicture.lapM * WholePicture.greenM * WholePicture.lapM = WholePicture.lapM ∧
      WholePicture.greenM * WholePicture.lapM * WholePicture.greenM = WholePicture.greenM ∧
      (WholePicture.lapM * WholePicture.greenM)ᵀ = WholePicture.lapM * WholePicture.greenM ∧
      (WholePicture.greenM * WholePicture.lapM)ᵀ = WholePicture.greenM * WholePicture.lapM) ∧
    (∀ X : Matrix (Fin 16) (Fin 16) ℝ, WholePicture.lapM * X * WholePicture.lapM = WholePicture.lapM →
      X * WholePicture.lapM * X = X → (WholePicture.lapM * X)ᵀ = WholePicture.lapM * X →
      (X * WholePicture.lapM)ᵀ = X * WholePicture.lapM → X = WholePicture.greenM) ∧
    (∀ f : Fin 16, (disagreeSet f).card = 2 →
      WholePicture.greenM 0 0 + WholePicture.greenM f f - 2 * WholePicture.greenM 0 f = 7 / 16) ∧
    (∀ l : Fin 16, (disagreeSet l).card = 4 →
      WholePicture.greenM 0 0 + WholePicture.greenM l l - 2 * WholePicture.greenM 0 l = 3 / 8) ∧
    Fintype.card (Bool × Fin 16) = 32 ∧
    (∀ u : ℂ, (1 - u • GroupsContinuumLaw.coverStep).det =
      (1 - u ^ 2) ^ 48 * (1 - u) * (1 - 4 * u) * (1 - u + 4 * u ^ 2) ^ 10 *
        (1 + 3 * u + 4 * u ^ 2) ^ 5 * (1 + 3 * u ^ 2 + 16 * u ^ 4) ^ 8) ∧
    GroupsContinuumLaw.coverPoly.rootMultiplicity (-1) = 48 ∧ GroupsContinuumLaw.coverPoly.rootMultiplicity 1 = 49 := by
  obtain ⟨hlap, hG, hpen, huniq, hface, hline⟩ := eq_20
  refine ⟨fun u hu => ?_, ?_, charTable_mul_self, RuleAndLaw.det_prime, by decide, ⟨hlap, hG⟩, hpen,
    huniq, hface, hline, by decide, GroupsContinuumLaw.cover_law, GroupsContinuumLaw.cover_order_neg_one,
    GroupsContinuumLaw.cover_order_one⟩
  · subst hu
    rw [smul_sub, smul_smul]
    congr 1
    · norm_num
  · rw [← adjacencyZ_eq]
    exact RuleAndLaw.laplacian_spectrum

end Comparison.System
