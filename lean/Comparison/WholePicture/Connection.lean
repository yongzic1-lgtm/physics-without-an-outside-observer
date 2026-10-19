import Comparison.RuleAndLaw.Positivity
import Comparison.ArticleStatements.SectorSum
import Comparison.Existence.Gauge

/-!
# The whole picture, statement 8: positivity below the critical step for every unitary connection

`RuleAndLaw/Positivity.lean`
(`quad_lower`, `law_no_zero_below_quarter`, `law_no_zero_in_disc`) and `ArticleStatements/SectorSum.lean`
(`lawWeight_pos`, `law_pos`) prove the positivity for any five Hermitian involutions `Γ_t`. Here a
unitary connection of the sixteen vertices (`Connection`, `Gauge.lean`, with its rotations in
`U(n)` and `U y x = (U x y)⁻¹`) is carried into those five operators, which closes the step from the
connection to the involutions:

* `connStep c t`: **`Γ_t((y, i), (x, j)) = [y = x △ T_t] U(y, x)_{ij}`** on the vertices with their
  gauge (`transition t` is the change along the line `t`);
* `connStep_herm`, `connStep_sq`: **every `Γ_t` is a Hermitian involution**;
* `connStep_trivial`: the trivial connection gives the transitions, `Γ_t = transitionMat t ⊗ 1`;
* `law_quad_unitary`: `Re⟨x, ((1 + 4u²) − uΣ_tΓ_t)x⟩ ≥ (1 − u)(1 − 4u)⟨x, x⟩` for `u ≥ 0`;
  `law_weight_pos_unitary`: **`0 < det(I − uB[U])` for `0 ≤ u < 1/4`**; `law_pos_unitary`: the law
  `Z[U] = det(I − uB[U])⁻¹` is positive there; `law_no_zero_unitary`: **the law has no zero in the
  open disc `|u| < 1/4`**: for every unitary connection `U`, of every rank `n`.
-/

open Matrix Comparison
open scoped ComplexOrder Kronecker

namespace Comparison.WholePicture

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The rotation of a unitary connection as a matrix. -/
def turnMat (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ)) (y x : Fin 16) : Matrix n n ℂ :=
  (c.U y x : Matrix n n ℂ)

theorem turnMat_back (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ)) (x y : Fin 16) :
    turnMat c y x = (turnMat c x y)ᴴ := by
  rw [turnMat, turnMat, c.U_inv x y, Matrix.UnitaryGroup.inv_val, Matrix.star_eq_conjTranspose]

theorem turnMat_mul_back (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ)) (x y : Fin 16) :
    turnMat c x y * turnMat c y x = 1 := by
  rw [turnMat_back c x y, ← Matrix.star_eq_conjTranspose]
  exact Matrix.mem_unitaryGroup_iff.mp (c.U x y).2

/-- **The step along the line `t` carrying the connection:** `Γ_t((y, i), (x, j)) = [y = x △ T_t]
U(y, x)_{ij}`. -/
noncomputable def connStep (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ)) (t : Fin 5) :
    Matrix (Fin 16 × n) (Fin 16 × n) ℂ :=
  Matrix.of fun p q => if p.1 = transition t q.1 then turnMat c p.1 q.1 p.2 q.2 else 0

theorem transition_eq_comm (t : Fin 5) (x y : Fin 16) : y = transition t x ↔ x = transition t y := by
  constructor
  · rintro rfl
    rw [transition_transition]
  · rintro rfl
    rw [transition_transition]

/-- **`Γ_t` is Hermitian.** -/
theorem connStep_herm (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ)) (t : Fin 5) :
    (connStep c t)ᴴ = connStep c t := by
  ext p q
  rw [Matrix.conjTranspose_apply]
  simp only [connStep, Matrix.of_apply]
  by_cases h : p.1 = transition t q.1
  · have h' : q.1 = transition t p.1 := (transition_eq_comm t q.1 p.1).mp h
    rw [ite_eq_left h', ite_eq_left h, turnMat_back c q.1 p.1, Matrix.conjTranspose_apply]
  · have h' : ¬ q.1 = transition t p.1 := fun h' => h ((transition_eq_comm t p.1 q.1).mp h')
    rw [ite_eq_right h', ite_eq_right h, star_zero]

/-- **`Γ_t` is an involution:** `Γ_t² = 1`. -/
theorem connStep_sq (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ)) (t : Fin 5) :
    connStep c t * connStep c t = 1 := by
  ext p q
  rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_eq_single (transition t q.1)]
  · have e2 := congrFun (congrFun (turnMat_mul_back c q.1 (transition t q.1)) p.2) q.2
    rw [Matrix.mul_apply] at e2
    simp only [connStep, Matrix.of_apply, transition_transition, ↓reduceIte]
    by_cases h : p.1 = q.1
    · simp only [h, ↓reduceIte, e2, Matrix.one_apply, Prod.ext_iff, true_and]
    · simp only [h, ↓reduceIte, zero_mul, Finset.sum_const_zero, Matrix.one_apply, Prod.ext_iff,
        false_and]
  · intro y _ hy
    refine Finset.sum_eq_zero fun k _ => ?_
    simp only [connStep, Matrix.of_apply, ite_eq_right hy, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The trivial connection: every rotation is `1`. -/
def trivialConn : Connection (Fin 16) (Matrix.unitaryGroup n ℂ) :=
  ⟨fun _ _ => 1, fun _ _ => by rw [inv_one]⟩

/-- **The trivial connection gives the transitions:** `Γ_t = transitionMat t ⊗ 1`. -/
theorem connStep_trivial (t : Fin 5) :
    connStep (trivialConn (n := n)) t = transitionMat t ⊗ₖ (1 : Matrix n n ℂ) := by
  ext p q
  simp only [connStep, Matrix.of_apply, Matrix.kroneckerMap_apply, transitionMat, transitionMatZ,
    Matrix.map_apply, turnMat, trivialConn, Matrix.UnitaryGroup.one_val]
  split_ifs <;> simp

/-- **The law's operator is bounded below for every unitary connection:**
`Re⟨x, ((1 + 4u²) − uΣ_tΓ_t)x⟩ ≥ (1 − u)(1 − 4u)⟨x, x⟩` for `u ≥ 0`. -/
theorem law_quad_unitary (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ)) (u : ℝ) (hu : 0 ≤ u)
    (x : Fin 16 × n → ℂ) :
    (1 - u) * (1 - 4 * u) * (star x ⬝ᵥ x).re ≤
      (star x ⬝ᵥ (((1 + 4 * (u : ℂ) ^ 2) • (1 : Matrix (Fin 16 × n) (Fin 16 × n) ℂ) -
        (u : ℂ) • ∑ t, connStep c t) *ᵥ x)).re :=
  RuleAndLaw.quad_lower (connStep c) (connStep_herm c) (connStep_sq c) u hu x

/-- **Positivity below the critical step for every unitary connection:** `0 < det(I − uB[U])` for
`0 ≤ u < 1/4`. -/
theorem law_weight_pos_unitary (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ)) (u : ℝ)
    (hu0 : 0 ≤ u) (hu : u < 1 / 4) : 0 < (1 - (u : ℂ) • stepOp (connStep c)).det :=
  ArticleStatements.lawWeight_pos (connStep c) (connStep_herm c) (connStep_sq c) u hu0 hu

/-- **The law `Z[U] = det(I − uB[U])⁻¹` is positive** for `0 ≤ u < 1/4`, every unitary connection.
-/
theorem law_pos_unitary (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ)) (u : ℝ) (hu0 : 0 ≤ u)
    (hu : u < 1 / 4) : 0 < ((1 - (u : ℂ) • stepOp (connStep c)).det)⁻¹ :=
  ArticleStatements.law_pos (connStep c) (connStep_herm c) (connStep_sq c) u hu0 hu

/-- **No unitary connection gives the law a zero in the open disc `|u| < 1/4`.** -/
theorem law_no_zero_unitary (c : Connection (Fin 16) (Matrix.unitaryGroup n ℂ)) (u : ℂ)
    (hu : ‖u‖ < 1 / 4) : (1 - u • stepOp (connStep c)).det ≠ 0 :=
  RuleAndLaw.law_no_zero_in_disc (connStep c) (connStep_herm c) (connStep_sq c) u hu

end Comparison.WholePicture
