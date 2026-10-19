import Comparison.System.Postulates
import Comparison.System.Law.Phases
import Comparison.System.Law.Determinant

/-!
# The proof system, the law: the signed law with the phases on the links

The `U(1)` connection `U_{yx} = e^{itΦ_{yx}}` of the link phases
(`phaseConn`), and the reduction of the signed law on the eighty states with these phases to the sixteen two-spinor states
(`det_signed_phase`): `det(I − uB₋[e^{itθ}]) = (1 − u²)²⁴(1 + 4u²)¹⁶ det(I − wA₋[e^{itθ}])`, `w = u/(1 + 4u²)`,
from Proposition 54 (`bass_connection`). With `Law/Phases.lean` this gives Proposition 62 for `B₋[e^{iθ}]` itself
(`Law.prop_62_signed`; `prop_62` is the whole proposition).
-/

open Matrix Complex Comparison Comparison.WholePicture

namespace Comparison.System

namespace Law

/-- The link phases as real numbers. -/
noncomputable def phR (θ : Fin 40 → ℝ) (x y : Fin 16) : ℝ := ∑ l, θ l * (linkX l x y).re

theorem linkX_real (l : Fin 40) (x y : Fin 16) : linkX l x y = ((linkX l x y).re : ℂ) := by
  rw [linkX_apply]
  split_ifs <;> simp

theorem phiC_eq_phR (θ : Fin 40 → ℝ) (x y : Fin 16) : phiC θ x y = (phR θ x y : ℂ) := by
  rw [phiC_apply, phR]
  push_cast
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← linkX_real]

theorem phR_antisymm (θ : Fin 40 → ℝ) (x y : Fin 16) : phR θ y x = -phR θ x y := by
  simp only [phR, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [linkX_antisymm, Complex.neg_re]
  ring

/-- The phase on the link from `x` to `y`, a `1 × 1` unitary. -/
noncomputable def phaseU (θ : Fin 40 → ℝ) (t : ℝ) (y x : Fin 16) : Matrix.unitaryGroup Unit ℂ :=
  ⟨Matrix.of fun _ _ => Complex.exp (((t * phR θ y x : ℝ) : ℂ) * I), by
    rw [Matrix.mem_unitaryGroup_iff]
    have hz : Complex.exp (((t * phR θ y x : ℝ) : ℂ) * I) *
        star (Complex.exp (((t * phR θ y x : ℝ) : ℂ) * I)) = 1 := by
      rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
        ← Complex.exp_add]
      simp
    ext i j
    cases i
    cases j
    simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply] using hz⟩

/-- **The `U(1)` connection of the link phases** `U_{yx} = e^{itΦ_{yx}}`. -/
noncomputable def phaseConn (θ : Fin 40 → ℝ) (t : ℝ) : Connection (Fin 16) (Matrix.unitaryGroup Unit ℂ) :=
  ⟨phaseU θ t, fun x y => by
    apply Subtype.ext
    rw [Matrix.UnitaryGroup.inv_val]
    ext i j
    simp only [phaseU, Matrix.of_apply, Matrix.star_apply]
    rw [Complex.star_def, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I,
      phR_antisymm]
    congr 1
    push_cast
    ring⟩

theorem sum_connStep_phase (θ : Fin 40 → ℝ) (t : ℝ) (y x : Fin 16) :
    (∑ s, connStepSigned cliffordSign (phaseConn θ t) s) (y, ()) (x, ()) =
      AC y x * Complex.exp (I * phiC θ y x * t) := by
  rw [Matrix.sum_apply]
  simp only [connStepSigned, Matrix.of_apply, cliffordSign, WholePicture.turnMat, phaseConn, phaseU]
  have hA : AC y x = ∑ s : Fin 5, if y = transition s x then (transitionSign s x : ℂ) else 0 := by
    simp only [AC, Matrix.of_apply]
    rw [sadjZ_eq, Matrix.of_apply]
    push_cast
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs <;> simp
  rw [hA, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  split_ifs
  · rw [phiC_eq_phR, show ((t * phR θ y x : ℝ) : ℂ) * I = I * (phR θ y x : ℂ) * (t : ℂ) by
      push_cast; ring]
  · simp

/-- **The signed law with the phases reduces to the sixteen two-spinor states:**
`det(I − uB₋[e^{itθ}]) = (1 − u²)²⁴(1 + 4u²)¹⁶ det(I − wA₋[e^{itθ}])` with `w = u/(1 + 4u²)`. -/
theorem det_signed_phase (θ : Fin 40 → ℝ) (t : ℝ) (u : ℂ) (ha : 1 + 4 * u ^ 2 ≠ 0) :
    (1 - u • stepOp (connStepSigned cliffordSign (phaseConn θ t))).det =
      (1 - u ^ 2) ^ 24 * (1 + 4 * u ^ 2) ^ 16 * (Kph (u / (1 + 4 * u ^ 2)) θ t).det := by
  rw [bass_connection cliffordSign_isLinkSign (phaseConn θ t) u, Fintype.card_unit, mul_one, mul_assoc]
  congr 1
  set e : Fin 16 × Unit ≃ Fin 16 := Equiv.prodPUnit (Fin 16) with he
  have hM : ((1 + 4 * u ^ 2) • (1 : Matrix (Fin 16 × Unit) (Fin 16 × Unit) ℂ) -
      u • ∑ s, connStepSigned cliffordSign (phaseConn θ t) s) =
      (1 + 4 * u ^ 2) • Matrix.reindex e.symm e.symm (Kph (u / (1 + 4 * u ^ 2)) θ t) := by
    ext ⟨y, ⟨⟩⟩ ⟨x, ⟨⟩⟩
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_symm, smul_eq_mul, Kph, Matrix.of_apply]
    rw [sum_connStep_phase]
    have h1 : (1 : Matrix (Fin 16 × Unit) (Fin 16 × Unit) ℂ) (y, ()) (x, ()) =
        (1 : Matrix (Fin 16) (Fin 16) ℂ) (e (y, ())) (e (x, ())) := by
      simp [Matrix.one_apply, he]
    rw [h1]
    simp only [he, Equiv.prodPUnit_apply]
    field_simp <;> ring
  rw [hM, Matrix.det_smul, Matrix.det_reindex_self, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_unit, mul_one]

end Law

open Comparison.System.Law

/-- **Proposition 62 for the signed step with the phases** (along every ray): for real `u` with
`1 + 4u² ≠ 0`, `w = u/(1 + 4u²)` with `1 − 5w² ≠ 0`, every direction `θ` and every real `t`,
`det(I − uB₋[e^{itθ}]) = (1 − u²)²⁴(1 + 4u²)¹⁶ det(I − wA₋[e^{itθ}])`; the second factor has, at `t = 0`, the
derivative `0` and the second derivative `−κ(w)‖Cθ‖²` times its value, and is even in `t`.
Recognition: Maxwell's action in Wilson's form. -/
theorem Law.prop_62_signed (u : ℂ) (ha : 1 + 4 * u ^ 2 ≠ 0)
    (hw : 1 - 5 * (u / (1 + 4 * u ^ 2)) ^ 2 ≠ 0) (θ : Fin 40 → ℝ) :
    (∀ t : ℝ, (1 - u • stepOp (connStepSigned cliffordSign (phaseConn θ t))).det =
      (1 - u ^ 2) ^ 24 * (1 + 4 * u ^ 2) ^ 16 * (Kph (u / (1 + 4 * u ^ 2)) θ t).det) ∧
    HasDerivAt (fun s => (Kph (u / (1 + 4 * u ^ 2)) θ s).det) 0 0 ∧
    HasDerivAt (deriv (fun s => (Kph (u / (1 + 4 * u ^ 2)) θ s).det))
      (-(2 * (u / (1 + 4 * u ^ 2)) ^ 4 / (1 - 5 * (u / (1 + 4 * u ^ 2)) ^ 2) ^ 2) * (plaqSq θ : ℂ) *
        (Kph (u / (1 + 4 * u ^ 2)) θ 0).det) 0 ∧
    (∀ t, (Kph (u / (1 + 4 * u ^ 2)) θ (-t)).det = (Kph (u / (1 + 4 * u ^ 2)) θ t).det) := by
  obtain ⟨-, -, -, -, h5, h6, h7⟩ := law_small_phases _ hw θ
  exact ⟨fun t => det_signed_phase θ t u ha, h5, h6, h7⟩

/-- **Proposition 62, the law in small phases** (along every ray; the uniform remainder in `θ` is on the work
list). On the sixteen vertices (`Law.prop_62_sixteen`): `C·grad = 0`, `rank C = 25`, and for every complex `w` with
`1 − 5w² ≠ 0` and every direction `θ`, `g(t) = det(I − wA₋[e^{itθ}])` has `g(0) ≠ 0`, `g′(0) = 0`,
`g″(0) = −κ(w)‖Cθ‖² g(0)` and is even, the Hessian of `log det(I − wA₋[e^{iθ}])` being `−κ(w)CᵀC`,
`κ(w) = 2w⁴/(1 − 5w²)²`, `1/200` at `w = 1/5`; on the eighty states (`Law.prop_62_signed`): the signed step with the
phases has `det(I − uB₋[e^{itθ}]) = (1 − u²)²⁴(1 + 4u²)¹⁶ det(I − wA₋[e^{itθ}])`, `w = u/(1 + 4u²)`.
Recognition: Maxwell's action in Wilson's form; with the kept rotations of a division in place of the phase it is the
Yang–Mills action. -/
theorem prop_62 :
    ((∀ (φ : Fin 16 → ℝ) (q : Fin 40), circ (fun l => φ (linkV l) - φ (linkU l)) q = 0) ∧
    cReal.rank = 25 ∧
    (∀ (w : ℂ), 1 - 5 * w ^ 2 ≠ 0 → ∀ θ : Fin 40 → ℝ,
      (Kph w θ 0).det ≠ 0 ∧
      HasDerivAt (fun s => (Kph w θ s).det) 0 0 ∧
      HasDerivAt (deriv (fun s => (Kph w θ s).det))
        (-(2 * w ^ 4 / (1 - 5 * w ^ 2) ^ 2) * (plaqSq θ : ℂ) * (Kph w θ 0).det) 0 ∧
      logDer w θ 0 = 0 ∧
      HasDerivAt (logDer w θ) (-(2 * w ^ 4 / (1 - 5 * w ^ 2) ^ 2) * (plaqSq θ : ℂ)) 0 ∧
      (∀ t, (Kph w θ (-t)).det = (Kph w θ t).det)) ∧
    (∀ (w : ℂ), 1 - 5 * w ^ 2 ≠ 0 → ∀ j k : Fin 40,
      hessLaw w j k = -(2 * w ^ 4 / (1 - 5 * w ^ 2) ^ 2) * (GZ j k : ℂ)) ∧
    (1 / 4 : ℂ) / (1 + 4 * (1 / 4) ^ 2) = 1 / 5 ∧
    2 * (1 / 5 : ℂ) ^ 4 / (1 - 5 * (1 / 5) ^ 2) ^ 2 = 1 / 200) ∧
    (∀ (u : ℂ) (ha : 1 + 4 * u ^ 2 ≠ 0) (hw : 1 - 5 * (u / (1 + 4 * u ^ 2)) ^ 2 ≠ 0) (θ : Fin 40 → ℝ),
      (∀ t : ℝ, (1 - u • stepOp (connStepSigned cliffordSign (phaseConn θ t))).det =
      (1 - u ^ 2) ^ 24 * (1 + 4 * u ^ 2) ^ 16 * (Kph (u / (1 + 4 * u ^ 2)) θ t).det) ∧
    HasDerivAt (fun s => (Kph (u / (1 + 4 * u ^ 2)) θ s).det) 0 0 ∧
    HasDerivAt (deriv (fun s => (Kph (u / (1 + 4 * u ^ 2)) θ s).det))
      (-(2 * (u / (1 + 4 * u ^ 2)) ^ 4 / (1 - 5 * (u / (1 + 4 * u ^ 2)) ^ 2) ^ 2) * (plaqSq θ : ℂ) *
        (Kph (u / (1 + 4 * u ^ 2)) θ 0).det) 0 ∧
    (∀ t, (Kph (u / (1 + 4 * u ^ 2)) θ (-t)).det = (Kph (u / (1 + 4 * u ^ 2)) θ t).det)) :=
  ⟨Law.prop_62_sixteen, fun u ha hw θ => Law.prop_62_signed u ha hw θ⟩

end Comparison.System
