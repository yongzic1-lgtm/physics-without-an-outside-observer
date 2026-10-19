import Comparison.Law.Cover

/-!
# The step on the sign cover, and the multiplicities `48` and `49` (Prop. 114)

The thirty-two signed two-spinor states `±e_S` (`Law/Cover.lean`: `liftTransition`, five lifted transitions, eighty
links); `coverStep` is the non-backtracking step on their `160` arcs.

* `coverStep_blocks`: **in the basis of the two signs the step is `[[B_K, B_F], [B_F, B_K]]`** with
  `B_K + B_F = B` (the step of the sixteen) and `B_K − B_F = B₋` (the signed step);
* `cover_law`: **`det(I − uB̃) = det(I − uB) · det(I − uB₋)
  = (1 − u²)⁴⁸ (1 − u)(1 − 4u)(1 − u + 4u²)¹⁰(1 + 3u + 4u²)⁵(1 + 3u² + 16u⁴)⁸`**;
* `cover_order_one`, `cover_order_neg_one`: **the zero of `det(I − uB̃)` at `u = 1` has order `49`,
  at `u = −1` order `48 = 80 − 32`**: the eigenvalue `+1` of the step has multiplicity `49` and `−1`
  multiplicity `48`.
-/

namespace Comparison.GroupsContinuumLaw

open Matrix Comparison Comparison.Law Polynomial

noncomputable section

/-- The lifted transitions as permutation matrices of the thirty-two signed two-spinor states. -/
def liftGamma (t : Fin 5) : Matrix (Bool × Fin 16) (Bool × Fin 16) ℂ :=
  Matrix.of fun p q => if p = liftTransition t q then 1 else 0

theorem coverAdj_eq_sum : coverAdj = ∑ t, liftGamma t := by
  ext p q
  simp [coverAdj, liftGamma, Matrix.sum_apply]

/-- **The step on the sign cover** (on its `160` arcs). -/
def coverStep : Matrix ((Bool × Fin 16) × Fin 5) ((Bool × Fin 16) × Fin 5) ℂ := stepOp liftGamma

/-- The part of a transition that keeps the sign, and the part that flips it. -/
def keepT (t : Fin 5) : Matrix (Fin 16) (Fin 16) ℂ :=
  Matrix.of fun k' k => if k' = transition t k ∧ flips t k = false then 1 else 0

def flipT (t : Fin 5) : Matrix (Fin 16) (Fin 16) ℂ :=
  Matrix.of fun k' k => if k' = transition t k ∧ flips t k = true then 1 else 0

theorem keepT_add_flipT (t : Fin 5) : keepT t + flipT t = transitionMat t := by
  ext k' k
  simp only [keepT, flipT, Matrix.add_apply, Matrix.of_apply, transitionMat, transitionMatZ, Matrix.map_apply]
  cases h : flips t k <;> by_cases hk : k' = transition t k <;> simp [hk]

theorem keepT_sub_flipT (t : Fin 5) : keepT t - flipT t = signTransitionC (-1 : ℂ) t := by
  ext k' k
  simp only [keepT, flipT, Matrix.sub_apply, Matrix.of_apply, signTransitionC]
  have hf : flips t k = decide (transitionSign t k ≠ 1) := rfl
  rcases transitionSign_pm t k with h | h <;> by_cases hk : k' = transition t k <;> simp [hf, h, hk]

theorem stepOp_add {V : Type*} [Fintype V] [DecidableEq V] (Γ Δ : Fin 5 → Matrix V V ℂ) :
    stepOp Γ + stepOp Δ = stepOp (Γ + Δ) := by
  ext p q
  simp only [stepOp, Matrix.add_apply, Matrix.of_apply, Pi.add_apply]
  split_ifs <;> simp

theorem stepOp_sub {V : Type*} [Fintype V] [DecidableEq V] (Γ Δ : Fin 5 → Matrix V V ℂ) :
    stepOp Γ - stepOp Δ = stepOp (Γ - Δ) := by
  ext p q
  simp only [stepOp, Matrix.sub_apply, Matrix.of_apply, Pi.sub_apply]
  split_ifs <;> simp

/-- The arcs of the cover split by the sign. -/
def arcSplit : (Fin 16 × Fin 5) ⊕ (Fin 16 × Fin 5) ≃ (Bool × Fin 16) × Fin 5 where
  toFun x := match x with
    | Sum.inl a => ((false, a.1), a.2)
    | Sum.inr a => ((true, a.1), a.2)
  invFun p := if p.1.1 then Sum.inr (p.1.2, p.2) else Sum.inl (p.1.2, p.2)
  left_inv x := by cases x <;> simp
  right_inv p := by
    obtain ⟨⟨σ, k⟩, t⟩ := p
    cases σ <;> simp

/-- **In the basis of the two signs the cover's step is `[[B_K, B_F], [B_F, B_K]]`.** -/
theorem coverStep_blocks :
    coverStep.submatrix arcSplit arcSplit =
      fromBlocks (stepOp keepT) (stepOp flipT) (stepOp flipT) (stepOp keepT) := by
  ext (⟨k', s⟩ | ⟨k', s⟩) (⟨k, t⟩ | ⟨k, t⟩) <;>
    simp only [coverStep, stepOp, liftGamma, keepT, flipT, Matrix.submatrix_apply, arcSplit,
      Equiv.coe_fn_mk, Matrix.of_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, liftTransition, Prod.mk.injEq] <;>
    cases h : flips s k <;> simp [h, and_comm]

/-- **`det(I − uB̃) = det(I − uB) det(I − uB₋)`**, and its closed form. -/
theorem cover_law (u : ℂ) :
    (1 - u • coverStep).det =
      (1 - u ^ 2) ^ 48 * (1 - u) * (1 - 4 * u) * (1 - u + 4 * u ^ 2) ^ 10 *
        (1 + 3 * u + 4 * u ^ 2) ^ 5 * (1 + 3 * u ^ 2 + 16 * u ^ 4) ^ 8 := by
  rw [← det_submatrix_equiv_self arcSplit]
  have e : (1 - u • coverStep).submatrix arcSplit arcSplit =
      fromBlocks (1 - u • stepOp keepT) (-(u • stepOp flipT)) (-(u • stepOp flipT))
        (1 - u • stepOp keepT) := by
    ext x y
    have hb := congrFun (congrFun coverStep_blocks x) y
    simp only [Matrix.submatrix_apply] at hb
    rcases x with x | x <;> rcases y with y | y <;>
      simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.neg_apply,
        fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂] at hb ⊢ <;>
      rw [hb] <;> simp [Matrix.one_apply, arcSplit, ← Prod.ext_iff]
  rw [e, det_block_sym]
  have e1 : 1 - u • stepOp keepT + -(u • stepOp flipT) = 1 - u • stepOp transitionMat := by
    rw [← sub_eq_add_neg, sub_sub, ← smul_add, stepOp_add]
    congr 3
    funext t
    exact keepT_add_flipT t
  have e2 : 1 - u • stepOp keepT - -(u • stepOp flipT) = 1 - u • stepOp (signTransitionC (-1 : ℂ)) := by
    rw [sub_neg_eq_add, sub_add, ← smul_sub, stepOp_sub]
    congr 3
    funext t
    exact keepT_sub_flipT t
  rw [e1, e2, D_plus, D_minus_rel]
  ring

/-- The polynomial `det(I − uB̃)`. -/
def coverPoly : Polynomial ℂ := (1 - (X : Polynomial ℂ) • coverStep.map C).det

/-- The rest of the factorization, nonzero at `u = ±1`. -/
def restPoly : Polynomial ℂ :=
  (1 - 4 * X) * (1 - X + 4 * X ^ 2) ^ 10 * (1 + 3 * X + 4 * X ^ 2) ^ 5 *
    (1 + 3 * X ^ 2 + 16 * X ^ 4) ^ 8

theorem coverPoly_eq : coverPoly =
    (X - C 1) ^ 49 * (-(X + C 1) ^ 48 * restPoly) := by
  apply Polynomial.funext
  intro u
  have h := det_one_sub_smul_poly coverStep u
  rw [coverPoly, ← h, cover_law]
  simp only [restPoly, eval_mul, eval_pow, eval_sub, eval_add, eval_neg, eval_X, eval_C,
    eval_one, eval_ofNat]
  ring

theorem coverPoly_eq' : coverPoly =
    (X - C (-1)) ^ 48 * (-(X - C 1) ^ 49 * restPoly) := by
  rw [coverPoly_eq]
  simp only [C_neg, C_1, sub_neg_eq_add]
  ring

theorem restPoly_eval_one : restPoly.eval 1 ≠ 0 := by
  simp only [restPoly, eval_mul, eval_pow, eval_sub, eval_add, eval_X, eval_one, eval_ofNat]
  norm_num

theorem restPoly_eval_neg_one : restPoly.eval (-1) ≠ 0 := by
  simp only [restPoly, eval_mul, eval_pow, eval_sub, eval_add, eval_X, eval_one, eval_ofNat]
  norm_num

/-- **The zero of `det(I − uB̃)` at `u = 1` has order `49`.** -/
theorem cover_order_one : coverPoly.rootMultiplicity 1 = 49 := by
  have hg : (-(X + C (1 : ℂ)) ^ 48 * restPoly).eval 1 ≠ 0 := by
    simp only [eval_mul, eval_neg, eval_pow, eval_add, eval_X, eval_C]
    have := restPoly_eval_one
    norm_num
    exact this
  have hg0 : -(X + C (1 : ℂ)) ^ 48 * restPoly ≠ 0 := fun h => hg (by rw [h, eval_zero])
  rw [coverPoly_eq, mul_comm, rootMultiplicity_mul_X_sub_C_pow hg0,
    rootMultiplicity_eq_zero (by simpa [IsRoot] using hg)]

/-- **The zero of `det(I − uB̃)` at `u = −1` has order `48 = 80 − 32`.** -/
theorem cover_order_neg_one : coverPoly.rootMultiplicity (-1) = 48 := by
  have hg : (-(X - C (1 : ℂ)) ^ 49 * restPoly).eval (-1) ≠ 0 := by
    simp only [eval_mul, eval_neg, eval_pow, eval_sub, eval_X, eval_C]
    have := restPoly_eval_neg_one
    norm_num
    exact this
  have hg0 : -(X - C (1 : ℂ)) ^ 49 * restPoly ≠ 0 := fun h => hg (by rw [h, eval_zero])
  rw [coverPoly_eq', mul_comm, rootMultiplicity_mul_X_sub_C_pow hg0,
    rootMultiplicity_eq_zero (by simpa [IsRoot] using hg)]

end

end Comparison.GroupsContinuumLaw
