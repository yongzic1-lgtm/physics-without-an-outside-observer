module

public import Comparison.Existence.AvailableTransitions

/-!
# Book XIV. The available transitions are a closed level of the law (Proposition 77)

On the eighty states `(S, t)` the step
with a rotation on each step is `B[w]` (`stepT w`): entry `(s', s)` is the rotation `w s s'` when `s'`
continues `s` (any values in any commutative ring; `w = 1` is the plain step `B`, a `U(1)`
connection is `w s s' = U_{s s'}`). For the last-step direction `h`, `A` is the available transitions (`InAvailableTransitions h`, the
seventy-four) and `D` the six closed states, the five arrivals at the singlet and the undo `(T_h, h)`.

* `closed_target`, `closed_from_undo`: inside `D` a step only goes from an arrival `(∅, t)` to the
  undo `(T_h, h)`, and nothing leaves the undo inside `D`.
* `blockDD_sq`: **`B_DD[w]² = 0`**; `det_closed`: **`det(1 − uB_DD[w]) = 1`**; `closed_inverse`:
  `(1 − uB_DD)(1 + uB_DD) = (1 + uB_DD)(1 − uB_DD) = 1`.
* `det_availableTransitions`: **`det(1 − uB[w]) = det(1 − uB_AA − u²B_AD B_DA − u³B_AD B_DD B_DA)`** for every
  `u` and every `w`: the law's determinant is the determinant of the available transitions `S_h`.
* `availableTransitions_counts`: the steps `A → A`, `A → D`, `D → A`, `D → D` number `276, 20, 20, 4`;
  `availableTransitions_steps`: `296` transitions and `24` hidden steps, `320/296 = 40/37`.
* `watched_rows`, `watched_cols`: at `u = 1/4`,
  `W = B_AA/4 + B_AD B_DA/16 + B_AD B_DD B_DA/64` has every row and every column summing to one:
  stochastic, with the uniform law stationary.
-/

@[expose] public section

namespace Comparison

open Matrix

/-- The available directed edges of `h`, the seventy-four. -/
abbrev InAvailableTransitions (h : Fin 5) (s : State) : Prop := inExcursion h s = true

/-! ## The six closed states -/

theorem closed_target_list : ∀ h : Fin 5, ∀ s ∈ setApart h, ∀ s' ∈ setApart h,
    Continues s s' → s' = (lastDirectionRel h, h) := by
  decide +kernel

/-- **Inside the six closed states a step only lands on the undo `(T_h, h)`.** -/
theorem closed_target (h : Fin 5) (s s' : State) (hs : ¬InAvailableTransitions h s) (hs' : ¬InAvailableTransitions h s')
    (hc : Continues s s') : s' = (lastDirectionRel h, h) := by
  simp only [Bool.not_eq_true] at hs hs'
  exact closed_target_list h s ((mem_setApart h s).mpr hs) s' ((mem_setApart h s').mpr hs') hc

theorem undo_closed (h : Fin 5) : ¬InAvailableTransitions h (lastDirectionRel h, h) := by
  revert h
  decide

theorem closed_from_undo_list : ∀ h : Fin 5, ∀ s' ∈ setApart h, ¬Continues (lastDirectionRel h, h) s' := by
  decide +kernel

/-- **Nothing leaves the undo inside the six closed states.** -/
theorem closed_from_undo (h : Fin 5) (s' : State) (hs' : ¬InAvailableTransitions h s') :
    ¬Continues (lastDirectionRel h, h) s' := by
  simp only [Bool.not_eq_true] at hs'
  exact closed_from_undo_list h s' ((mem_setApart h s').mpr hs')

section Closed

variable {R : Type*} [CommRing R]

/-- **The step with a rotation on each step**, `B[w]`. -/
def stepT (w : State → State → R) : Matrix State State R :=
  Matrix.of fun s' s => if Continues s s' then w s s' else 0

variable (h : Fin 5) (w : State → State → R)

/-- The block `B_DD` on the six closed states. -/
abbrev blockDD : Matrix {s // ¬InAvailableTransitions h s} {s // ¬InAvailableTransitions h s} R :=
  (stepT w).toBlock (fun s => ¬InAvailableTransitions h s) (fun s => ¬InAvailableTransitions h s)

/-- The undo `(T_h, h)` as a closed state. -/
def undoD : {s // ¬InAvailableTransitions h s} := ⟨(lastDirectionRel h, h), undo_closed h⟩

theorem blockDD_row (i j : {s // ¬InAvailableTransitions h s}) (hi : i ≠ undoD h) : blockDD h w i j = 0 := by
  simp only [blockDD, toBlock_apply, stepT, Matrix.of_apply]
  split_ifs with hc
  · exact absurd (Subtype.ext (closed_target h j i j.2 i.2 hc)) hi
  · rfl

theorem blockDD_col (i : {s // ¬InAvailableTransitions h s}) : blockDD h w i (undoD h) = 0 := by
  simp only [blockDD, toBlock_apply, stepT, Matrix.of_apply, undoD]
  split_ifs with hc
  · exact absurd hc (closed_from_undo h i i.2)
  · rfl

/-- **`B_DD[w]² = 0`.** -/
theorem blockDD_sq : blockDD h w * blockDD h w = 0 := by
  ext i k
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hi : i = undoD h
  · by_cases hj : j = undoD h
    · subst hi hj
      rw [blockDD_col, zero_mul]
    · rw [blockDD_row h w j k hj, mul_zero]
  · rw [blockDD_row h w i j hi, zero_mul]

/-- The projector on the undo. -/
def undoProj : Matrix {s // ¬InAvailableTransitions h s} {s // ¬InAvailableTransitions h s} R :=
  Matrix.diagonal fun d => if d = undoD h then 1 else 0

theorem undoProj_mul : undoProj h * blockDD h w = blockDD h w := by
  ext i j
  rw [undoProj, Matrix.diagonal_mul]
  by_cases hi : i = undoD h
  · simp [hi]
  · simp only [hi, ↓reduceIte, zero_mul]
    exact (blockDD_row h w i j hi).symm

theorem mul_undoProj : blockDD h w * undoProj h = 0 := by
  ext i j
  rw [undoProj, Matrix.mul_diagonal, Matrix.zero_apply]
  by_cases hj : j = undoD h
  · subst hj
    simp only [↓reduceIte, mul_one]
    exact blockDD_col h w i
  · simp [hj]

/-- **`det(1 − uB_DD[w]) = 1`** for every `u` and every `w`. -/
theorem det_closed (u : R) : (1 - u • blockDD h w).det = 1 := by
  have e : u • blockDD h w = (u • undoProj h) * blockDD h w := by
    rw [Matrix.smul_mul, undoProj_mul]
  rw [e, det_one_sub_mul_comm, Matrix.mul_smul, mul_undoProj, smul_zero, sub_zero, det_one]

theorem closed_inverse (u : R) :
    (1 - u • blockDD h w) * (1 + u • blockDD h w) = 1 ∧
      (1 + u • blockDD h w) * (1 - u • blockDD h w) = 1 := by
  have hsq := blockDD_sq h w
  constructor
  · rw [Matrix.sub_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsq, smul_zero]
    abel
  · rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hsq, smul_zero]
    abel

/-- The inverse of the closed block, `1 + uB_DD`. -/
@[instance_reducible]
def closedInvertible (u : R) : Invertible (1 - u • blockDD h w) :=
  ⟨1 + u • blockDD h w, (closed_inverse h w u).2, (closed_inverse h w u).1⟩

theorem toBlock_one_sub_diag (p : State → Prop) (u : R) :
    (1 - u • stepT w).toBlock p p = 1 - u • (stepT w).toBlock p p := by
  ext i j
  simp only [toBlock_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Subtype.ext_iff]

theorem toBlock_one_sub_off (p : State → Prop) (u : R) :
    (1 - u • stepT w).toBlock p (fun s => ¬p s) = -(u • (stepT w).toBlock p fun s => ¬p s) := by
  ext i j
  have hij : (i : State) ≠ j := fun e => j.2 (e ▸ i.2)
  simp [toBlock_apply, Matrix.one_apply_ne hij]

theorem toBlock_one_sub_off' (p : State → Prop) (u : R) :
    (1 - u • stepT w).toBlock (fun s => ¬p s) p = -(u • (stepT w).toBlock (fun s => ¬p s) p) := by
  ext i j
  have hij : (i : State) ≠ j := fun e => i.2 (e ▸ j.2)
  simp [toBlock_apply, Matrix.one_apply_ne hij]

/-- **The available transitions are a closed level of the law:** for every `u` and every rotation `w` on the steps,
`det(1 − uB[w]) = det(1 − uB_AA − u²B_AD B_DA − u³B_AD B_DD B_DA)`, the determinant of `S_h(u)` on
the seventy-four. -/
theorem det_availableTransitions (u : R) :
    (1 - u • stepT w).det =
      (1 - u • (stepT w).toBlock (InAvailableTransitions h) (InAvailableTransitions h) -
        u ^ 2 • ((stepT w).toBlock (InAvailableTransitions h) (fun s => ¬InAvailableTransitions h s) *
          (stepT w).toBlock (fun s => ¬InAvailableTransitions h s) (InAvailableTransitions h)) -
        u ^ 3 • ((stepT w).toBlock (InAvailableTransitions h) (fun s => ¬InAvailableTransitions h s) * blockDD h w *
          (stepT w).toBlock (fun s => ¬InAvailableTransitions h s) (InAvailableTransitions h))).det := by
  rw [det_toBlock (1 - u • stepT w) (InAvailableTransitions h), toBlock_one_sub_diag, toBlock_one_sub_off,
    toBlock_one_sub_off', toBlock_one_sub_diag]
  let _ := closedInvertible h w u
  rw [det_fromBlocks₂₂, det_closed, one_mul]
  congr 1
  rw [show ⅟(1 - u • blockDD h w) = 1 + u • blockDD h w from rfl]
  simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, smul_smul, smul_add, Matrix.mul_assoc]
  module

end Closed

/-! ## The counts -/

/-- **The steps by blocks:** `A → A` 276, `A → D` 20, `D → A` 20, `D → D` 4. -/
theorem availableTransitions_counts : ∀ h : Fin 5,
    (Finset.univ.filter fun p : State × State =>
      inExcursion h p.1 = true ∧ inExcursion h p.2 = true ∧ Continues p.1 p.2).card = 276 ∧
    (Finset.univ.filter fun p : State × State =>
      inExcursion h p.1 = true ∧ inExcursion h p.2 = false ∧ Continues p.1 p.2).card = 20 ∧
    (Finset.univ.filter fun p : State × State =>
      inExcursion h p.1 = false ∧ inExcursion h p.2 = true ∧ Continues p.1 p.2).card = 20 ∧
    (Finset.univ.filter fun p : State × State =>
      inExcursion h p.1 = false ∧ inExcursion h p.2 = false ∧ Continues p.1 p.2).card = 4 := by
  decide +kernel

/-- **`296` transitions and `24` hidden steps in the `320` of a cycle; `40/37` steps per transition.** -/
theorem availableTransitions_steps : (276 + 20 : ℕ) = 296 ∧ (20 + 4 : ℕ) = 24 ∧ (296 + 24 : ℕ) = 320 ∧
    (320 : ℚ) / 296 = 40 / 37 ∧ (80 * 4 : ℕ) = 320 := by
  norm_num

/-! ## The walk watched on the available transitions at `u = 1/4` -/

section Watched

variable (h : Fin 5)

/-- The plain step `B` over `ℚ`. -/
abbrev stepQ : Matrix State State ℚ := stepT fun _ _ => (1 : ℚ)

/-- The walk watched on the available transitions at `u = 1/4`. -/
def watchedW : Matrix {s // InAvailableTransitions h s} {s // InAvailableTransitions h s} ℚ :=
  (1 / 4 : ℚ) • stepQ.toBlock (InAvailableTransitions h) (InAvailableTransitions h) +
    (1 / 16 : ℚ) • (stepQ.toBlock (InAvailableTransitions h) (fun s => ¬InAvailableTransitions h s) *
      stepQ.toBlock (fun s => ¬InAvailableTransitions h s) (InAvailableTransitions h)) +
    (1 / 64 : ℚ) • (stepQ.toBlock (InAvailableTransitions h) (fun s => ¬InAvailableTransitions h s) *
      blockDD h (fun _ _ => (1 : ℚ)) * stepQ.toBlock (fun s => ¬InAvailableTransitions h s) (InAvailableTransitions h))

theorem stepQ_mulVec_one : stepQ *ᵥ (1 : State → ℚ) = (4 : ℚ) • 1 := by
  ext s'
  simp only [stepQ, stepT, Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.one_apply, mul_one,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_boole, card_predecessors]
  norm_num

theorem stepQ_vecMul_one : (1 : State → ℚ) ᵥ* stepQ = (4 : ℚ) • 1 := by
  ext s
  simp only [stepQ, stepT, Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.one_apply, one_mul,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_boole, card_continuations]
  norm_num

theorem mulVec_split (M : Matrix State State ℚ) (q p : State → Prop) [DecidablePred p]
    (i : {s // q s}) :
    (M *ᵥ (1 : State → ℚ)) i = (M.toBlock q p *ᵥ (1 : {s // p s} → ℚ)) i +
      (M.toBlock q (fun s => ¬p s) *ᵥ (1 : {s // ¬p s} → ℚ)) i := by
  simp only [Matrix.mulVec, dotProduct, toBlock_apply, Pi.one_apply, mul_one]
  exact (Fintype.sum_subtype_add_sum_subtype p fun x => M (↑i) x).symm

theorem vecMul_split (M : Matrix State State ℚ) (q p : State → Prop) [DecidablePred p]
    (j : {s // q s}) :
    ((1 : State → ℚ) ᵥ* M) j = ((1 : {s // p s} → ℚ) ᵥ* M.toBlock p q) j +
      ((1 : {s // ¬p s} → ℚ) ᵥ* M.toBlock (fun s => ¬p s) q) j := by
  simp only [Matrix.vecMul, dotProduct, toBlock_apply, Pi.one_apply, one_mul]
  exact (Fintype.sum_subtype_add_sum_subtype p fun x => M x (↑j)).symm

/-- **The watched walk is stochastic:** every row of `W` sums to one. -/
theorem watched_rows : watchedW h *ᵥ (1 : {s // InAvailableTransitions h s} → ℚ) = 1 := by
  have hAA : stepQ.toBlock (InAvailableTransitions h) (InAvailableTransitions h) *ᵥ 1 =
      (4 : ℚ) • 1 - stepQ.toBlock (InAvailableTransitions h) (fun s => ¬InAvailableTransitions h s) *ᵥ 1 := by
    ext i
    have e := congrFun stepQ_mulVec_one i
    rw [mulVec_split stepQ (InAvailableTransitions h) (InAvailableTransitions h) i] at e
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul] at e ⊢
    linarith
  have hDA : stepQ.toBlock (fun s => ¬InAvailableTransitions h s) (InAvailableTransitions h) *ᵥ 1 =
      (4 : ℚ) • 1 - blockDD h (fun _ _ => (1 : ℚ)) *ᵥ 1 := by
    ext i
    have e := congrFun stepQ_mulVec_one i
    rw [mulVec_split stepQ (fun s => ¬InAvailableTransitions h s) (InAvailableTransitions h) i] at e
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul] at e ⊢
    linarith
  have hBB : ∀ v, blockDD h (fun _ _ => (1 : ℚ)) *ᵥ (blockDD h (fun _ _ => (1 : ℚ)) *ᵥ v) = 0 := by
    intro v
    rw [Matrix.mulVec_mulVec, blockDD_sq, Matrix.zero_mulVec]
  rw [watchedW]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, ← Matrix.mulVec_mulVec, hDA, hAA,
    Matrix.mulVec_sub, Matrix.mulVec_smul, hBB, Matrix.mulVec_zero, sub_zero]
  module

/-- **The uniform law is stationary for the watched walk:** every column of `W` sums to one. -/
theorem watched_cols : (1 : {s // InAvailableTransitions h s} → ℚ) ᵥ* watchedW h = 1 := by
  have hAA : (1 : {s // InAvailableTransitions h s} → ℚ) ᵥ* stepQ.toBlock (InAvailableTransitions h) (InAvailableTransitions h) =
      (4 : ℚ) • 1 - (1 : {s // ¬InAvailableTransitions h s} → ℚ) ᵥ*
        stepQ.toBlock (fun s => ¬InAvailableTransitions h s) (InAvailableTransitions h) := by
    ext j
    have e := congrFun stepQ_vecMul_one j
    rw [vecMul_split stepQ (InAvailableTransitions h) (InAvailableTransitions h) j] at e
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul] at e ⊢
    linarith
  have hAD : (1 : {s // InAvailableTransitions h s} → ℚ) ᵥ*
        stepQ.toBlock (InAvailableTransitions h) (fun s => ¬InAvailableTransitions h s) =
      (4 : ℚ) • 1 - (1 : {s // ¬InAvailableTransitions h s} → ℚ) ᵥ* blockDD h (fun _ _ => (1 : ℚ)) := by
    ext j
    have e := congrFun stepQ_vecMul_one j
    rw [vecMul_split stepQ (fun s => ¬InAvailableTransitions h s) (InAvailableTransitions h) j] at e
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul] at e ⊢
    linarith
  have hBB : ∀ v, v ᵥ* blockDD h (fun _ _ => (1 : ℚ)) ᵥ* blockDD h (fun _ _ => (1 : ℚ)) = 0 := by
    intro v
    rw [Matrix.vecMul_vecMul, blockDD_sq, Matrix.vecMul_zero]
  rw [watchedW]
  simp only [Matrix.vecMul_add, Matrix.vecMul_smul, ← Matrix.vecMul_vecMul, hAD, hAA,
    Matrix.sub_vecMul, Matrix.smul_vecMul, hBB, sub_zero]
  module

end Watched

end Comparison

end
