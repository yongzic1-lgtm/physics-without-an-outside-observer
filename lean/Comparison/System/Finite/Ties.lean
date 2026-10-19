import Comparison.System.Spine.Quaternion
import Comparison.System.Geometry.OneThing
import Comparison.System.Geometry.TwoThings
import Comparison.System.Existence.Numbered
import Comparison.System.Completion.Numbers

/-!
# The proof system: the objects two layers define, proved equal

Where two layers of `Comparison.System` define one
object, the two definitions are proved equal here.

* The quaternion units `i, Θ, iΘ` of a candidate system (`CandidateSystem.quatBasis`, the spine)
  are those of the geometry (`Geometry.quatBasis`) at its conjugate, and the two actions of `ℍ` on
  the states are one (`quatBasis_eq_geometry`, `quatHom_eq_geometry`).
* The Clebsch graph of the existence layer (`Existence.clebsch`, a simple graph on the sixteen
  vertices) has the spine's adjacency matrix `A` (`clebsch_adjMatrix_eq`).
* The sign of a division (`theta`, the spine) is the diagonal of `Existence.thetaAt`
  (`theta_eq_thetaAt`).
* The moments of one excursion that the completions read off the generating function
  (`Completion.Num.EP`, `EQ`, `VarP`, `VarQ`, `Cov`) are the moments over the excursions
  (`Existence.excursionMean`, `varP`, `varQ`, `covPQ`), by Prop. 29 (`num_moments_eq`).

And the postulates as the layers read them:

* **P2 fixes the comparison:** an operator on two systems satisfies P2 (`P2a`, `P2b`) exactly when it
  is `a + bL` (`P2_iff`, the last clause of Prop. 13, `prop_13`).
* **P5 makes the walks:** a sequence of steps changes its two-spinor state at each step (P5 (b),
  `ChangesEachStep`) exactly when each of its first segments is a walk, a reduced word
  (`changesEachStep_iff`), and its two-spinor state at the moment `n` (P5 (c), `relAt`) is the two-spinor state of
  that word (`relAt_eq_relationOf`); both are clauses of Prop. 24 (`prop_24`).
-/

open scoped Matrix Kronecker

namespace Comparison.System

/-- The spine's quaternion basis of a candidate system is the geometry's at its conjugate. -/
theorem quatBasis_eq_geometry (S : CandidateSystem) :
    S.quatBasis = Geometry.quatBasis S.partner :=
  QuaternionAlgebra.Basis.ext (LinearMap.ext fun _ => rfl) (LinearMap.ext fun _ => rfl)

/-- The spine's action of the quaternions is the geometry's. -/
theorem quatHom_eq_geometry (S : CandidateSystem) :
    S.quatHom = Geometry.quatAction S.partner := by
  rw [CandidateSystem.quatHom, Geometry.quatAction, quatBasis_eq_geometry]

/-- The existence layer's Clebsch graph has the spine's adjacency matrix. -/
theorem clebsch_adjMatrix_eq (R : Type*) [CommRing R] :
    Existence.clebsch.adjMatrix R = A R := by
  ext x y
  rw [SimpleGraph.adjMatrix_apply, A_apply_eq_ite]
  exact if_congr (adjacent_symm x y) rfl rfl

/-- The sign of a division is the diagonal of the existence layer's `thetaAt`. -/
theorem theta_eq_thetaAt (D : Finset (Fin 6)) :
    theta ℂ D = Matrix.diagonal (Existence.thetaAt D) := rfl

/-- The completions' moments of one excursion are the moments over the excursions (Prop. 29). -/
theorem num_moments_eq :
    Completion.Num.EP = Existence.excursionMean Existence.fP ∧
    Completion.Num.EQ = Existence.excursionMean Existence.fQ ∧
    Completion.Num.VarP = Existence.varP ∧ Completion.Num.VarQ = Existence.varQ ∧
    Completion.Num.Cov = Existence.covPQ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, dP, dQ, dPP, dQQ, dPQ⟩ := prop_29
  refine ⟨dP, dQ, ?_, ?_, ?_⟩
  · rw [Completion.Num.VarP, Article.varP, dPP, dP, Existence.varP]
  · rw [Completion.Num.VarQ, Article.varQ, dQQ, dQ, Existence.varQ]
  · rw [Completion.Num.Cov, Article.covPQ, dPQ, dP, dQ, Existence.covPQ]

/-- **P2 fixes the comparison** (Prop. 13, its last clause). An operator on two systems is
kept by every `U ⊗ U`, `U ∈ Sp(2)`, and by the exchange (P2 (a)), and by the quaternionic structure taken on one
system (P2 (b)), exactly when it is `a + bL`. -/
theorem P2_iff (X : Matrix Two Two ℂ) :
    P2a X ∧ P2b X ↔ ∃ a b : ℂ, X = a • (1 : Matrix Two Two ℂ) + b • L :=
  prop_13.2.2.2.2.2.2.2.2.2 X

/-- **P5 (b) makes the walks** (Prop. 24): a sequence of steps changes its two-spinor state at
each step exactly when each of its first segments is a walk (a reduced word). -/
theorem changesEachStep_iff (t : Steps) :
    ChangesEachStep t ↔ ∀ n, IsHistory (Existence.between t 0 n) :=
  prop_24.2.2.2.1 t

/-- **P5 (c) on the words** (Prop. 24): the two-spinor state at the moment `n` is the two-spinor state of
the word of the first `n` steps. -/
theorem relAt_eq_relationOf (t : Steps) (n : ℕ) :
    relAt t n = relationOf (Existence.between t 0 n) :=
  prop_24.2.2.2.2.1 t n

end Comparison.System
