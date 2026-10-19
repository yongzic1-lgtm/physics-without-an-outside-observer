import Comparison.Existence.EvenFour
import Comparison.Elements.TwoThings

/-!
# The second pairing's joint step is Proposition 37's two-leg step

The files `PlaneColour`, `Patterns`, `TwoBases` and `Places` of this folder carry one system's operators by
`X ↦ γ_s X γ_s`. Proposition 37 says the step of one system along `s` is two vertical steps,
`γ_s = i J_nJ_s`, and that the even words of the vertical step are all the operators of the four
amplitudes (`evenEquivFour`). This file shows that the conjugation used there is exactly the
conjugation by the two-leg vertical word `J_nJ_s` in the even Clifford algebra of the six, carried
through Proposition 37's isomorphism, and that a meeting's operator, read as its even vertical word,
is carried by the two legs with its agreement sign.

* `singletLine_mul_self`: `(J_nJ_s)² = −1`, so `(J_nJ_s)⁻¹ = −J_nJ_s`.
* `two_leg_conj`: **`φ(J_nJ_s · Y · (J_nJ_s)⁻¹) = γ_s φ(Y) γ_s`** for every even word `Y`
  (`φ = evenToFour`).
* `meeting_word_carried`: with `Y_k = φ⁻¹(B_k)` the even vertical word of the two-spinor state `k`,
  **`J_nJ_s · Y_k · (J_nJ_s)⁻¹ = ε_s(k) Y_k`**: the two vertical legs of the physical step carry each
  meeting's own word with that meeting's agreement sign (`γ_conj_relOp` read through Proposition 37).
-/

open Comparison Matrix
open scoped Matrix

namespace Comparison.JointCells.Bridge

/-- `(J_nJ_s)² = −1` in the even part. -/
theorem singletLine_mul_self (s : Fin 5) : singletLine s * singletLine s = -1 := by
  apply Subtype.ext
  change (singletLine s : CliffordAlgebra Q6) * (singletLine s : CliffordAlgebra Q6) =
    ((-1 : CliffordAlgebra.even Q6) : CliffordAlgebra Q6)
  rw [singletLine_val]
  have h0 : cl 0 * cl 0 = 1 := cl_sq 0
  have hs : cl s.succ * cl s.succ = 1 := cl_sq s.succ
  have ha : cl 0 * cl s.succ = -(cl s.succ * cl 0) := cl_anti (Fin.succ_ne_zero s).symm
  have e : cl 0 * cl s.succ * (cl 0 * cl s.succ) = -(cl 0 * cl 0 * (cl s.succ * cl s.succ)) := by
    calc cl 0 * cl s.succ * (cl 0 * cl s.succ) = cl 0 * (cl s.succ * cl 0) * cl s.succ := by
          simp only [mul_assoc]
      _ = cl 0 * (-(cl 0 * cl s.succ)) * cl s.succ := by
          rw [ha, neg_neg]
      _ = -(cl 0 * cl 0 * (cl s.succ * cl s.succ)) := by
          simp only [mul_neg, neg_mul, mul_assoc]
  rw [e, h0, hs, one_mul]
  simp

/-- **The physical step's conjugation is the two-leg conjugation:** for every even word `Y`,
`φ(J_nJ_s · Y · (−J_nJ_s)) = γ_s φ(Y) γ_s`. -/
theorem two_leg_conj (s : Fin 5) (Y : CliffordAlgebra.even Q6) :
    evenToFour (singletLine s * Y * (-singletLine s)) = γ s * evenToFour Y * γ s := by
  rw [map_mul, map_mul, map_neg, evenToFour_singlet_line, Matrix.mul_neg, Matrix.smul_mul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, neg_mul_neg, Complex.I_mul_I, neg_one_smul, neg_neg]

/-- **A meeting's even vertical word is carried by the two legs with its agreement sign:**
`J_nJ_s · Y_k · (J_nJ_s)⁻¹ = ε_s(k) Y_k`, `Y_k` the even word that Proposition 37 sends to `B_k`. -/
theorem meeting_word_carried (s : Fin 5) (k : Fin 16) :
    singletLine s * evenEquivFour.symm (relOp k) * (-singletLine s) =
      ((if s ∈ disagreeSet k then -1 else 1 : ℝ)) • evenEquivFour.symm (relOp k) := by
  apply evenEquivFour.injective
  rw [evenEquivFour_apply, two_leg_conj, ← evenEquivFour_apply, evenEquivFour.apply_symm_apply,
    γ_conj_relOp, map_smul, evenEquivFour.apply_symm_apply]
  split_ifs <;> simp

end Comparison.JointCells.Bridge

#print axioms Comparison.JointCells.Bridge.singletLine_mul_self
#print axioms Comparison.JointCells.Bridge.two_leg_conj
#print axioms Comparison.JointCells.Bridge.meeting_word_carried
