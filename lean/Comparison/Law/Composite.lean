module

public import Comparison.Law.Rows

/-!
# The law, IX: the composite's one composition at first order, its coupling, and K⁰
(Part 8: Propositions 189, 192, 195; Proposition 198's composition)

**Proposition 192.** `relDiv U`: the division of the six held by the two-spinor state `e_U` (the lines on
which the two systems disagree); a rotation `(x y)` is moved by a division when one end lies in it.
* `prop192_moves`: **`θ_U` moves the clock `(n r)` exactly when `r ∈ T_U`**; `prop192_count`: at **8 of
  the 15 two-spinor states other than the singlet**, for every line `r`.
* `time_division_turns`: `r`'s time division `{r, n}` moves 8 and keeps 7 of the 15 rotations;
  `relTurn_moved`: it moves the two-spinor state's own rotation `X_U` (a plane's `(a b)`, a vector state's clock
  `(n t)`) exactly when `r ∈ T_U`.

**Proposition 195, the operator that carries the coupling.** On the eighty states, with `B_r` the steps
along `r`, `Λ_r` the two-spinor states that move `(n r)` and `Π` the states off the singlet:
* `prop195`: **`𝟏ᵀB_rΛ_rΠ𝟏 / 𝟏ᵀB_rΠ𝟏 = 32/60 = 8/15` for every line `r`**; `prop195_availableTransitions`: the
  same with `Π` the available transitions of `h`, along `h`.
* `meeting_matrix_trace`: over the fifteen records, `Σ_{U≠∅} (4/60) G(U) ∘ G(U) = I + (8/15)(𝐉 − I)`,
  `G(U) = 𝐉` where `U` moves the clock and `I` where it keeps it.

**Proposition 189, the one composition: the law read on the spectrum of the level operator.**
`levelOp S₁ S₂ g = GD`, `G = [[1, g], [g, 1]]`, `D = diag(S₁, S₂)`, `c = g²`:
* `det_one_sub_kron_of_eigen`: for any `2 × 2` matrix `A` with `AP = P diag(λ)`, `P` invertible,
  **`det(I − A ⊗ M) = det(I − λ₁M) det(I − λ₂M)`** for every square `M`;
* `prop189_det`: **`det(I − (GD) ⊗ M) = det(I − λ₊M) det(I − λ₋M)`**, `λ±` the eigen-levels, the
  roots of `λ² − (S₁ + S₂)λ + (1 − c)S₁S₂` (`eigenPlus_root`, `eigenMinus_root`); `line_side_det` (`G = I`):
  `det(I − S₁M) det(I − S₂M)`; `meeting_side_det` (`G = 𝟏𝟏ᵀ`): `det(I − (S₁ + S₂)M)`.
* `eigen_sum`: **the first order `Tr R = S₁ + S₂` at every coupling**; `eigen_sq`,
  `eigen_cube`: `Tr R² = S₁² + S₂² + 2cS₁S₂`, `Tr R³ = (1 − c)(S₁³ + S₂³) + c(S₁ + S₂)³`;
  `second_order_composite`: `Σ_j [λ_j/5 − (6/125)λ_j²] = (S₁ + S₂)/5 − (6/125)(S₁² + S₂²) −
  (12/125)c S₁S₂`.
* `compositeDelta S₁ S₂ c = δ₁(λ₊) + δ₁(λ₋)`; `composite_ends`: **at `c = 0` the line side
  `δ₁(S₁) + δ₁(S₂)`, at `c = 1` the meeting side `δ₁(S₁ + S₂)`**.

**K⁰ (Proposition 198) as the composition of its two levels.** `rowK0sq S_d p m_p =
L(Ω) m_p² Tr δ₁(R(S_d, pS_d; 8/15))`, its pieces at their divided sets: `L(Ω) = 6`, `m_p` (row p),
`p = R(F, {a,b,n})` (`row_p_quark`), the coupling `8/15` (`prop195`), `δ₁` the singlet meeting's
zero under a level (`delta_expansion`). The light level `S_d` is fixed by π± through the same
composition (Prop. 197): `light_level_equation`; `K0_law_on_direct_sum`: K⁰'s law on the direct sum
of its two words is the product over its two modes at `G₁₂² = 8/15`. The value `497.6136 MeV`
needs `S_d` to its digits, the root of the light level's equation.
-/

@[expose] public section

namespace Comparison

open Matrix Kronecker

namespace Law

/-! ## Proposition 192 -/

/-- A rotation `(x y)` of the six is moved by a division `D` when exactly one of its ends lies in `D`. -/
def movesTurn (D : Finset (Fin 6)) (x y : Fin 6) : Bool := xor (decide (x ∈ D)) (decide (y ∈ D))

/-- The division of the six held by the two-spinor state `e_U`: the lines on which the two systems disagree. -/
def relDiv (U : Fin 16) : Finset (Fin 6) := (disagreeSet U).map (Fin.succEmb 5)

/-- **The meeting moves a line's clock exactly where the two disagree on that line.** -/
theorem prop192_moves :
    ∀ (r : Fin 5) (U : Fin 16), movesTurn (relDiv U) 0 r.succ = decide (r ∈ disagreeSet U) := by
  decide

/-- **At eight of the fifteen two-spinor states other than the singlet**, for every line. -/
theorem prop192_count :
    ∀ r : Fin 5, (Finset.univ.filter fun U : Fin 16 => U ≠ 0 ∧ r ∈ disagreeSet U).card = 8 := by
  decide

/-- The fifteen rotations of the six. -/
def turns6 : Finset (Fin 6 × Fin 6) := Finset.univ.filter fun p => p.1 < p.2

/-- **`r`'s time division `{r, n}` moves 8 and keeps 7 of the 15 rotations.** -/
theorem time_division_turns : ∀ r : Fin 5,
    (turns6.filter fun p => movesTurn {0, r.succ} p.1 p.2 = true).card = 8 ∧
      (turns6.filter fun p => movesTurn {0, r.succ} p.1 p.2 = false).card = 7 := by
  decide

/-- The two-spinor state's own rotation: a plane `{a, b}` turns `(a b)`, a vector state `T_t` has the clock
`(n t)`. -/
def relTurn : Fin 16 → Fin 6 × Fin 6 :=
  ![(0, 0), (0, 1), (0, 2), (0, 3), (0, 4), (0, 5), (1, 2), (1, 3), (1, 4), (1, 5), (2, 3), (2, 4),
    (2, 5), (3, 4), (3, 5), (4, 5)]

/-- The rotation is the two-spinor state's: a plane's two lines, or a vector state's missing line with the
singlet. -/
theorem relTurn_spec : ∀ U : Fin 16, U ≠ 0 →
    ((disagreeSet U).card = 2 → relDiv U = {(relTurn U).1, (relTurn U).2}) ∧
      ((disagreeSet U).card = 4 → (relTurn U).1 = 0 ∧ (relTurn U).2 ∉ relDiv U) := by
  decide

/-- **`θ_U` moves `(n r)` ⟺ `r ∈ T_U` ⟺ `r`'s time division moves the two-spinor state's own rotation.** -/
theorem relTurn_moved : ∀ (r : Fin 5) (U : Fin 16), U ≠ 0 →
    movesTurn {0, r.succ} (relTurn U).1 (relTurn U).2 = decide (r ∈ disagreeSet U) := by
  decide

/-! ## Proposition 195 -/

/-- The steps along the line `r` on the eighty states. -/
def stepsAlong (r : Fin 5) : Matrix State State ℚ :=
  Matrix.of fun s' s => if Continues s s' ∧ s'.2 = r then 1 else 0

/-- `Λ_r`: the two-spinor states whose division moves the clock `(n r)`. -/
def lamR (r : Fin 5) : Matrix State State ℚ := diagonal fun s => if r ∈ disagreeSet s.1 then 1 else 0

/-- `Π`: the states off the singlet. -/
def offSinglet : Matrix State State ℚ := diagonal fun s => if s.1 ≠ 0 then 1 else 0

/-- `Π_A`: the available transitions of `h`. -/
def availableTransitionsProj (h : Fin 5) : Matrix State State ℚ := diagonal fun s => if inExcursion h s = true then 1 else 0

theorem ones_dot_mul_diag (B : Matrix State State ℚ) (f : State → ℚ) :
    (1 : State → ℚ) ⬝ᵥ ((B * diagonal f) *ᵥ 1) = ∑ s, ∑ s', B s' s * f s := by
  simp only [dotProduct, Matrix.mulVec, Matrix.mul_diagonal, Pi.one_apply, one_mul, mul_one]
  rw [Finset.sum_comm]

theorem diag_mul_diag (f g : State → ℚ) :
    (diagonal f * diagonal g : Matrix State State ℚ) = diagonal fun s => f s * g s :=
  diagonal_mul_diagonal f g

theorem count_moved : ∀ r : Fin 5, ∑ s : State, ∑ s' : State,
    (if Continues s s' ∧ s'.2 = r ∧ r ∈ disagreeSet s.1 ∧ s.1 ≠ 0 then 1 else 0 : ℕ) = 32 := by
  decide +kernel

theorem count_transitions : ∀ r : Fin 5, ∑ s : State, ∑ s' : State,
    (if Continues s s' ∧ s'.2 = r ∧ s.1 ≠ 0 then 1 else 0 : ℕ) = 60 := by
  decide +kernel

theorem count_moved_availableTransitions : ∀ h : Fin 5, ∑ s : State, ∑ s' : State,
    (if Continues s s' ∧ s'.2 = h ∧ h ∈ disagreeSet s.1 ∧ inExcursion h s = true then 1 else 0 : ℕ) =
      32 := by
  decide +kernel

theorem count_transitions_availableTransitions : ∀ h : Fin 5, ∑ s : State, ∑ s' : State,
    (if Continues s s' ∧ s'.2 = h ∧ inExcursion h s = true then 1 else 0 : ℕ) = 60 := by
  decide +kernel

/-- **The coupling as a trace on the eighty states:** `𝟏ᵀB_rΛ_rΠ𝟏 / 𝟏ᵀB_rΠ𝟏 = 32/60 = 8/15`. -/
theorem prop195 (r : Fin 5) :
    (1 : State → ℚ) ⬝ᵥ ((stepsAlong r * lamR r * offSinglet) *ᵥ 1) = 32 ∧
      (1 : State → ℚ) ⬝ᵥ ((stepsAlong r * offSinglet) *ᵥ 1) = 60 ∧
      ((1 : State → ℚ) ⬝ᵥ ((stepsAlong r * lamR r * offSinglet) *ᵥ 1)) /
        ((1 : State → ℚ) ⬝ᵥ ((stepsAlong r * offSinglet) *ᵥ 1)) = 8 / 15 := by
  have h1 : (1 : State → ℚ) ⬝ᵥ ((stepsAlong r * lamR r * offSinglet) *ᵥ 1) = 32 := by
    rw [lamR, offSinglet, Matrix.mul_assoc, diag_mul_diag, ones_dot_mul_diag]
    have e : (∑ s : State, ∑ s' : State, stepsAlong r s' s *
        ((if r ∈ disagreeSet s.1 then (1 : ℚ) else 0) * (if s.1 ≠ 0 then 1 else 0))) =
        ((∑ s : State, ∑ s' : State,
          (if Continues s s' ∧ s'.2 = r ∧ r ∈ disagreeSet s.1 ∧ s.1 ≠ 0 then 1 else 0 : ℕ) : ℕ) : ℚ) := by
      push_cast
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
      simp only [stepsAlong, Matrix.of_apply]
      by_cases a : Continues s s' <;> by_cases b : s'.2 = r <;> by_cases c : r ∈ disagreeSet s.1 <;>
        by_cases d : s.1 ≠ 0 <;> simp [a, b, c, d]
    rw [e, count_moved r]
    norm_num
  have h2 : (1 : State → ℚ) ⬝ᵥ ((stepsAlong r * offSinglet) *ᵥ 1) = 60 := by
    rw [offSinglet, ones_dot_mul_diag]
    have e : (∑ s : State, ∑ s' : State, stepsAlong r s' s * (if s.1 ≠ 0 then (1 : ℚ) else 0)) =
        ((∑ s : State, ∑ s' : State,
          (if Continues s s' ∧ s'.2 = r ∧ s.1 ≠ 0 then 1 else 0 : ℕ) : ℕ) : ℚ) := by
      push_cast
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
      simp only [stepsAlong, Matrix.of_apply]
      by_cases a : Continues s s' <;> by_cases b : s'.2 = r <;> by_cases d : s.1 ≠ 0 <;>
        simp [a, b, d]
    rw [e, count_transitions r]
    norm_num
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2]
  norm_num

/-- **The same with the available transitions of `h`, along `h`.** -/
theorem prop195_availableTransitions (h : Fin 5) :
    ((1 : State → ℚ) ⬝ᵥ ((stepsAlong h * lamR h * availableTransitionsProj h) *ᵥ 1)) /
        ((1 : State → ℚ) ⬝ᵥ ((stepsAlong h * availableTransitionsProj h) *ᵥ 1)) = 8 / 15 := by
  have h1 : (1 : State → ℚ) ⬝ᵥ ((stepsAlong h * lamR h * availableTransitionsProj h) *ᵥ 1) = 32 := by
    rw [lamR, availableTransitionsProj, Matrix.mul_assoc, diag_mul_diag, ones_dot_mul_diag]
    have e : (∑ s : State, ∑ s' : State, stepsAlong h s' s *
        ((if h ∈ disagreeSet s.1 then (1 : ℚ) else 0) * (if inExcursion h s = true then 1 else 0))) =
        ((∑ s : State, ∑ s' : State, (if Continues s s' ∧ s'.2 = h ∧ h ∈ disagreeSet s.1 ∧
          inExcursion h s = true then 1 else 0 : ℕ) : ℕ) : ℚ) := by
      push_cast
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
      simp only [stepsAlong, Matrix.of_apply]
      by_cases a : Continues s s' <;> by_cases b : s'.2 = h <;> by_cases c : h ∈ disagreeSet s.1 <;>
        by_cases d : inExcursion h s = true <;> simp [a, b, c, d]
    rw [e, count_moved_availableTransitions h]
    norm_num
  have h2 : (1 : State → ℚ) ⬝ᵥ ((stepsAlong h * availableTransitionsProj h) *ᵥ 1) = 60 := by
    rw [availableTransitionsProj, ones_dot_mul_diag]
    have e : (∑ s : State, ∑ s' : State, stepsAlong h s' s *
        (if inExcursion h s = true then (1 : ℚ) else 0)) =
        ((∑ s : State, ∑ s' : State,
          (if Continues s s' ∧ s'.2 = h ∧ inExcursion h s = true then 1 else 0 : ℕ) : ℕ) : ℚ) := by
      push_cast
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun s' _ => ?_
      simp only [stepsAlong, Matrix.of_apply]
      by_cases a : Continues s s' <;> by_cases b : s'.2 = h <;> by_cases d : inExcursion h s = true <;>
        simp [a, b, d]
    rw [e, count_transitions_availableTransitions h]
    norm_num
  rw [h1, h2]
  norm_num

/-- The meeting matrix of one record: one word (`𝐉`) where the two-spinor state moves the clock, two words
(`I`) where it keeps it. -/
def recordG (r : Fin 5) (U : Fin 16) : Matrix (Fin 2) (Fin 2) ℚ :=
  if r ∈ disagreeSet U then Matrix.of fun _ _ => 1 else 1

theorem count_kept : ∀ r : Fin 5,
    (Finset.univ.filter fun U : Fin 16 => U ≠ 0 ∧ r ∉ disagreeSet U).card = 7 := by
  decide

/-- **The meeting matrix as a trace over the records:**
`Σ_{U≠∅} (4/60) G(U) ∘ G(U) = I + (8/15)(𝐉 − I)`. -/
theorem meeting_matrix_trace (r : Fin 5) :
    ∑ U ∈ Finset.univ.filter (fun U : Fin 16 => U ≠ 0), (4 / 60 : ℚ) • (recordG r U ⊙ recordG r U) =
      1 + (8 / 15 : ℚ) • ((Matrix.of fun _ _ => (1 : ℚ)) - 1) := by
  have h8 := prop192_count r
  have h7 := count_kept r
  have hentry : ∀ (U : Fin 16) (i j : Fin 2), (recordG r U ⊙ recordG r U) i j =
      if r ∈ disagreeSet U then 1 else (if i = j then 1 else 0) := by
    intro U i j
    simp only [recordG, Matrix.hadamard_apply]
    by_cases hU : r ∈ disagreeSet U
    · simp [hU]
    · by_cases hij : i = j <;> simp [hU, hij, Matrix.one_apply]
  ext i j
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, hentry, smul_eq_mul, Matrix.add_apply, Matrix.sub_apply,
    Matrix.of_apply, Matrix.one_apply]
  rw [← Finset.mul_sum, Finset.sum_ite, Finset.filter_filter, Finset.filter_filter, Finset.sum_const,
    Finset.sum_const, h8, h7]
  by_cases hij : i = j <;> simp [hij] <;> norm_num

/-! ## Proposition 189 -/

/-- **The law on the direct sum splits over the modes:** if `AP = P diag(λ)` with `P` invertible, then
`det(I − A ⊗ M) = det(I − λ₁M) det(I − λ₂M)`. -/
theorem det_one_sub_kron_of_eigen {n : Type*} [Fintype n] [DecidableEq n]
    (A P : Matrix (Fin 2) (Fin 2) ℝ) (l : Fin 2 → ℝ) (hP : IsUnit P.det)
    (hAP : A * P = P * diagonal l) (M : Matrix n n ℝ) :
    (1 - A ⊗ₖ M).det = (1 - l 0 • M).det * (1 - l 1 • M).det := by
  have hPinv : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hP
  have hPinv' : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hP
  have hA : A = P * diagonal l * P⁻¹ := by
    rw [← hAP, Matrix.mul_assoc, hPinv, Matrix.mul_one]
  have hkron : 1 - A ⊗ₖ M = (P ⊗ₖ (1 : Matrix n n ℝ)) * (1 - diagonal l ⊗ₖ M) *
      (P⁻¹ ⊗ₖ (1 : Matrix n n ℝ)) := by
    rw [hA, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, ← Matrix.mul_kronecker_mul,
      Matrix.mul_one, hPinv, Matrix.one_kronecker_one, ← Matrix.mul_kronecker_mul,
      ← Matrix.mul_kronecker_mul, Matrix.one_mul, Matrix.mul_one]
  have hdet1 : (P ⊗ₖ (1 : Matrix n n ℝ)).det * (P⁻¹ ⊗ₖ (1 : Matrix n n ℝ)).det = 1 := by
    rw [← det_mul, ← Matrix.mul_kronecker_mul, hPinv, Matrix.one_mul, Matrix.one_kronecker_one,
      det_one]
  have hblock : (1 - diagonal l ⊗ₖ M : Matrix (Fin 2 × n) (Fin 2 × n) ℝ) =
      (blockDiagonal fun i : Fin 2 => 1 - l i • M).submatrix (Equiv.prodComm (Fin 2) n)
        (Equiv.prodComm (Fin 2) n) := by
    ext ⟨i, k⟩ ⟨j, k'⟩
    simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.kroneckerMap_apply, diagonal_apply,
      Matrix.submatrix_apply, Equiv.prodComm_apply, Prod.swap_prod_mk, blockDiagonal_apply,
      Matrix.smul_apply, smul_eq_mul, Prod.mk.injEq]
    by_cases hij : i = j
    · subst hij
      by_cases hk : k = k' <;> simp [hk]
    · simp [hij]
  rw [hkron, det_mul, det_mul, hblock, det_submatrix_equiv_self, det_blockDiagonal,
    Fin.prod_univ_two]
  linear_combination ((1 - l 0 • M).det * (1 - l 1 • M).det) * hdet1

/-- The level operator `GD`, `G = [[1, g], [g, 1]]`, `D = diag(S₁, S₂)`. -/
def levelOp (S₁ S₂ g : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![S₁, g * S₂; g * S₁, S₂]

/-- The level operator's spectrum: `R = D^½GD^½` has the same, and both have the characteristic
polynomial `λ² − (S₁ + S₂)λ + (1 − g²)S₁S₂`. -/
theorem levelOp_charpoly (S₁ S₂ g l : ℝ) :
    (l • (1 : Matrix (Fin 2) (Fin 2) ℝ) - levelOp S₁ S₂ g).det =
      l ^ 2 - (S₁ + S₂) * l + (1 - g ^ 2) * S₁ * S₂ := by
  rw [det_fin_two]
  simp [levelOp]
  ring

/-- The discriminant's root `√((S₁ − S₂)² + 4cS₁S₂)`. -/
noncomputable def discR (S₁ S₂ c : ℝ) : ℝ := Real.sqrt ((S₁ - S₂) ^ 2 + 4 * c * S₁ * S₂)

/-- **The eigen-levels** `λ± = [(S₁ + S₂) ± √((S₁ − S₂)² + 4cS₁S₂)]/2`, `c = g²`. -/
noncomputable def eigenPlus (S₁ S₂ c : ℝ) : ℝ := ((S₁ + S₂) + discR S₁ S₂ c) / 2

noncomputable def eigenMinus (S₁ S₂ c : ℝ) : ℝ := ((S₁ + S₂) - discR S₁ S₂ c) / 2

theorem discR_sq (S₁ S₂ c : ℝ) (hd : 0 ≤ (S₁ - S₂) ^ 2 + 4 * c * S₁ * S₂) :
    discR S₁ S₂ c ^ 2 = (S₁ - S₂) ^ 2 + 4 * c * S₁ * S₂ :=
  Real.sq_sqrt hd

theorem eigenPlus_root (S₁ S₂ c : ℝ) (hd : 0 ≤ (S₁ - S₂) ^ 2 + 4 * c * S₁ * S₂) :
    eigenPlus S₁ S₂ c ^ 2 - (S₁ + S₂) * eigenPlus S₁ S₂ c + (1 - c) * S₁ * S₂ = 0 := by
  have hs := discR_sq S₁ S₂ c hd
  unfold eigenPlus
  linear_combination hs / 4

theorem eigenMinus_root (S₁ S₂ c : ℝ) (hd : 0 ≤ (S₁ - S₂) ^ 2 + 4 * c * S₁ * S₂) :
    eigenMinus S₁ S₂ c ^ 2 - (S₁ + S₂) * eigenMinus S₁ S₂ c + (1 - c) * S₁ * S₂ = 0 := by
  have hs := discR_sq S₁ S₂ c hd
  unfold eigenMinus
  linear_combination hs / 4

/-- **The first order: `Tr R = λ₊ + λ₋ = S₁ + S₂` at every coupling.** -/
theorem eigen_sum (S₁ S₂ c : ℝ) : eigenPlus S₁ S₂ c + eigenMinus S₁ S₂ c = S₁ + S₂ := by
  unfold eigenPlus eigenMinus
  ring

theorem eigen_prod (S₁ S₂ c : ℝ) (hd : 0 ≤ (S₁ - S₂) ^ 2 + 4 * c * S₁ * S₂) :
    eigenPlus S₁ S₂ c * eigenMinus S₁ S₂ c = (1 - c) * S₁ * S₂ := by
  have hs := discR_sq S₁ S₂ c hd
  unfold eigenPlus eigenMinus
  linear_combination -hs / 4

/-- **`Tr R² = S₁² + S₂² + 2cS₁S₂`.** -/
theorem eigen_sq (S₁ S₂ c : ℝ) (hd : 0 ≤ (S₁ - S₂) ^ 2 + 4 * c * S₁ * S₂) :
    eigenPlus S₁ S₂ c ^ 2 + eigenMinus S₁ S₂ c ^ 2 = S₁ ^ 2 + S₂ ^ 2 + 2 * c * S₁ * S₂ := by
  have h1 := eigen_sum S₁ S₂ c
  have h2 := eigen_prod S₁ S₂ c hd
  have e : eigenPlus S₁ S₂ c ^ 2 + eigenMinus S₁ S₂ c ^ 2 =
      (eigenPlus S₁ S₂ c + eigenMinus S₁ S₂ c) ^ 2 - 2 * (eigenPlus S₁ S₂ c * eigenMinus S₁ S₂ c) := by
    ring
  rw [e, h1, h2]
  ring

/-- **`Tr R³ = (1 − c)(S₁³ + S₂³) + c(S₁ + S₂)³`:** linear in the coupling. -/
theorem eigen_cube (S₁ S₂ c : ℝ) (hd : 0 ≤ (S₁ - S₂) ^ 2 + 4 * c * S₁ * S₂) :
    eigenPlus S₁ S₂ c ^ 3 + eigenMinus S₁ S₂ c ^ 3 =
      (1 - c) * (S₁ ^ 3 + S₂ ^ 3) + c * (S₁ + S₂) ^ 3 := by
  have h1 := eigen_sum S₁ S₂ c
  have h2 := eigen_prod S₁ S₂ c hd
  have e : eigenPlus S₁ S₂ c ^ 3 + eigenMinus S₁ S₂ c ^ 3 =
      (eigenPlus S₁ S₂ c + eigenMinus S₁ S₂ c) ^ 3 -
        3 * (eigenPlus S₁ S₂ c * eigenMinus S₁ S₂ c) * (eigenPlus S₁ S₂ c + eigenMinus S₁ S₂ c) := by
    ring
  rw [e, h1, h2]
  ring

/-- **The second order of the composition:** `Σ_j [λ_j/5 − (6/125)λ_j²] =
(S₁ + S₂)/5 − (6/125)(S₁² + S₂²) − (12/125)c S₁S₂`: the cross spread `c σ²`, `σ² = 12/125`. -/
theorem second_order_composite (S₁ S₂ c : ℝ) (hd : 0 ≤ (S₁ - S₂) ^ 2 + 4 * c * S₁ * S₂) :
    (eigenPlus S₁ S₂ c / 5 - 6 / 125 * eigenPlus S₁ S₂ c ^ 2) +
        (eigenMinus S₁ S₂ c / 5 - 6 / 125 * eigenMinus S₁ S₂ c ^ 2) =
      (S₁ + S₂) / 5 - 6 / 125 * (S₁ ^ 2 + S₂ ^ 2) - 12 / 125 * c * S₁ * S₂ := by
  have h1 := eigen_sum S₁ S₂ c
  have h2 := eigen_sq S₁ S₂ c hd
  linear_combination h1 / 5 - 6 / 125 * h2

/-- **Proposition 189: the law on the direct sum is the product over the modes,**
`det(I − (GD) ⊗ M) = det(I − λ₊M) det(I − λ₋M)` (`g ≠ 0`, `S₂ ≠ 0`, distinct modes). -/
theorem prop189_det {n : Type*} [Fintype n] [DecidableEq n] (S₁ S₂ g : ℝ) (hg : g ≠ 0)
    (hS : S₂ ≠ 0) (hd : 0 < (S₁ - S₂) ^ 2 + 4 * g ^ 2 * S₁ * S₂) (M : Matrix n n ℝ) :
    (1 - levelOp S₁ S₂ g ⊗ₖ M).det =
      (1 - eigenPlus S₁ S₂ (g ^ 2) • M).det * (1 - eigenMinus S₁ S₂ (g ^ 2) • M).det := by
  have hrp := eigenPlus_root S₁ S₂ (g ^ 2) hd.le
  have hrm := eigenMinus_root S₁ S₂ (g ^ 2) hd.le
  have hne : eigenPlus S₁ S₂ (g ^ 2) - eigenMinus S₁ S₂ (g ^ 2) ≠ 0 := by
    unfold eigenPlus eigenMinus discR
    have := Real.sqrt_pos.mpr hd
    intro h
    linarith
  let P : Matrix (Fin 2) (Fin 2) ℝ :=
    !![g * S₂, g * S₂; eigenPlus S₁ S₂ (g ^ 2) - S₁, eigenMinus S₁ S₂ (g ^ 2) - S₁]
  have hdetP : P.det = g * S₂ * (eigenMinus S₁ S₂ (g ^ 2) - eigenPlus S₁ S₂ (g ^ 2)) := by
    rw [det_fin_two]
    simp [P]
    ring
  have hPu : IsUnit P.det := by
    rw [hdetP]
    refine isUnit_iff_ne_zero.mpr (mul_ne_zero (mul_ne_zero hg hS) ?_)
    intro h
    exact hne (by linarith)
  have h := det_one_sub_kron_of_eigen (levelOp S₁ S₂ g) P
    ![eigenPlus S₁ S₂ (g ^ 2), eigenMinus S₁ S₂ (g ^ 2)] hPu ?_ M
  · simpa using h
  · ext i j
    fin_cases i <;> fin_cases j
    · simp [levelOp, P, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    · simp [levelOp, P, Matrix.mul_apply, Fin.sum_univ_two]
      ring
    · simp [levelOp, P, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (-1 : ℝ) * hrp
    · simp [levelOp, P, Matrix.mul_apply, Fin.sum_univ_two]
      linear_combination (-1 : ℝ) * hrm

/-- **The line side (`G = I`):** `det(I − D ⊗ M) = det(I − S₁M) det(I − S₂M)`. -/
theorem line_side_det {n : Type*} [Fintype n] [DecidableEq n] (S₁ S₂ : ℝ) (M : Matrix n n ℝ) :
    (1 - levelOp S₁ S₂ 0 ⊗ₖ M).det = (1 - S₁ • M).det * (1 - S₂ • M).det := by
  have h := det_one_sub_kron_of_eigen (levelOp S₁ S₂ 0) 1 ![S₁, S₂] (by simp) ?_ M
  · simpa using h
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [levelOp]

/-- **The meeting side (`G = 𝟏𝟏ᵀ`):** `det(I − (𝟏𝟏ᵀD) ⊗ M) = det(I − (S₁ + S₂)M)`. -/
theorem meeting_side_det {n : Type*} [Fintype n] [DecidableEq n] (S₁ S₂ : ℝ) (hS : S₂ ≠ 0)
    (hT : S₁ + S₂ ≠ 0) (M : Matrix n n ℝ) :
    (1 - levelOp S₁ S₂ 1 ⊗ₖ M).det = (1 - (S₁ + S₂) • M).det := by
  let P : Matrix (Fin 2) (Fin 2) ℝ := !![S₂, S₂; S₂, -S₁]
  have hPu : IsUnit P.det := by
    rw [det_fin_two]
    refine isUnit_iff_ne_zero.mpr ?_
    have : P 0 0 * P 1 1 - P 0 1 * P 1 0 = -(S₂ * (S₁ + S₂)) := by
      simp [P]
      ring
    rw [this]
    exact neg_ne_zero.mpr (mul_ne_zero hS hT)
  have h := det_one_sub_kron_of_eigen (levelOp S₁ S₂ 1) P ![S₁ + S₂, 0] hPu ?_ M
  · simpa using h
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [levelOp, P, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- **The composite's shift:** `Tr δ₁(R) = δ₁(λ₊) + δ₁(λ₋)`. -/
noncomputable def compositeDelta (S₁ S₂ c : ℝ) : ℝ :=
  deltaLevel (eigenPlus S₁ S₂ c) + deltaLevel (eigenMinus S₁ S₂ c)

theorem deltaLevel_zero : deltaLevel 0 = 0 := by
  rw [deltaLevel, uLevel, neg_zero, Real.exp_zero]
  have : Real.sqrt (9 + 16 * 1) = 5 := by
    rw [show (9 + 16 * 1 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [this]
  norm_num

/-- **The two ends:** at `c = 0` the line side `δ₁(S₁) + δ₁(S₂)`; at `c = 1` the meeting side
`δ₁(S₁ + S₂)`. -/
theorem composite_ends (S₁ S₂ : ℝ) (h₁ : 0 ≤ S₁) (h₂ : 0 ≤ S₂) :
    compositeDelta S₁ S₂ 0 = deltaLevel S₁ + deltaLevel S₂ ∧
      compositeDelta S₁ S₂ 1 = deltaLevel (S₁ + S₂) := by
  constructor
  · have hd : discR S₁ S₂ 0 = |S₁ - S₂| := by
      rw [discR, show (S₁ - S₂) ^ 2 + 4 * 0 * S₁ * S₂ = (S₁ - S₂) ^ 2 by ring, Real.sqrt_sq_eq_abs]
    rw [compositeDelta, eigenPlus, eigenMinus, hd]
    rcases le_total S₁ S₂ with h | h
    · rw [abs_of_nonpos (by linarith)]
      rw [show (S₁ + S₂ + -(S₁ - S₂)) / 2 = S₂ by ring, show (S₁ + S₂ - -(S₁ - S₂)) / 2 = S₁ by ring,
        add_comm]
    · rw [abs_of_nonneg (by linarith)]
      rw [show (S₁ + S₂ + (S₁ - S₂)) / 2 = S₁ by ring, show (S₁ + S₂ - (S₁ - S₂)) / 2 = S₂ by ring]
  · have hd : discR S₁ S₂ 1 = S₁ + S₂ := by
      rw [discR, show (S₁ - S₂) ^ 2 + 4 * 1 * S₁ * S₂ = (S₁ + S₂) ^ 2 by ring,
        Real.sqrt_sq (by linarith)]
    rw [compositeDelta, eigenPlus, eigenMinus, hd]
    rw [show (S₁ + S₂ + (S₁ + S₂)) / 2 = S₁ + S₂ by ring, show (S₁ + S₂ - (S₁ + S₂)) / 2 = 0 by ring,
      deltaLevel_zero, add_zero]

/-! ## K⁰ as the composition of its two levels -/

/-- **K⁰:** `m² = L(Ω) m_p² Tr δ₁(R(S_d, pS_d; 8/15))`, `L(Ω) = 6`, `p` the quark ratio, `8/15` the
coupling of Proposition 195. -/
noncomputable def rowK0sq (Sd mp : ℝ) : ℝ :=
  6 * mp ^ 2 * compositeDelta Sd (massOp .symmetric sPlaneSinglet * Sd) (8 / 15)

/-- **The light level's equation** (Proposition 197): `π± = u d̄`, its strong part `m_π⁰²`, read through
the same composition: `6m_p² Tr δ₁(R(R_ud S_d, S_d; 8/15)) = m_π⁰²`. -/
def light_level_equation (Sd mp mpi0sq : ℝ) : Prop :=
  6 * mp ^ 2 * compositeDelta ((17 / 37) * Sd) Sd (8 / 15) = mpi0sq

/-- **K⁰'s composition at its two ends and at first order:** the coupling `8/15` sits between the line
side (`c = 0`) and the meeting side (`c = 1`); the first order `(S_d + S_s)/5` is the same at every
coupling (`eigen_sum`); the strange level is `S_s = pS_d` with `p = 3⁵e^{−5/2}M_Q(−ν)^{1/6}`. -/
theorem K0_composition (Sd mp : ℝ) (hS : 0 ≤ Sd) (hp : 0 ≤ massOp .symmetric sPlaneSinglet) :
    6 * mp ^ 2 * compositeDelta Sd (massOp .symmetric sPlaneSinglet * Sd) 0 =
        6 * mp ^ 2 * (deltaLevel Sd + deltaLevel (massOp .symmetric sPlaneSinglet * Sd)) ∧
      6 * mp ^ 2 * compositeDelta Sd (massOp .symmetric sPlaneSinglet * Sd) 1 =
        6 * mp ^ 2 * deltaLevel (Sd + massOp .symmetric sPlaneSinglet * Sd) ∧
      eigenPlus Sd (massOp .symmetric sPlaneSinglet * Sd) (8 / 15) +
          eigenMinus Sd (massOp .symmetric sPlaneSinglet * Sd) (8 / 15) =
        Sd + massOp .symmetric sPlaneSinglet * Sd ∧
      massOp .symmetric sPlaneSinglet =
        3 ^ (5 : ℝ) * Real.exp (-(5 / 2)) * clockMQ sLastDirectionSinglet (-(9 / 4000)) ^ (1 / 6 : ℝ) := by
  obtain ⟨e0, e1⟩ := composite_ends Sd (massOp .symmetric sPlaneSinglet * Sd) hS (mul_nonneg hp hS)
  exact ⟨by rw [e0], by rw [e1], eigen_sum _ _ _, row_p_quark⟩


/-- The clock is positive. -/
theorem clockMQ_pos (S : Finset (Fin 6)) (x : ℝ) : 0 < clockMQ S x := by
  unfold clockMQ
  have : 0 < ∑ i : Fin 10, Real.exp (-(x * clockGap S i)) :=
    Finset.sum_pos (fun i _ => Real.exp_pos _) Finset.univ_nonempty
  positivity

/-- The strange-to-down ratio `p` is positive. -/
theorem massOp_plane_pos (S : Finset (Fin 6)) : 0 < massOp .symmetric S := by
  unfold massOp clockOn
  have he : 0 < eS sLine := by rw [piece_e_line]; norm_num
  have h1 : 0 < eS sLine ^ (-(statesN .symmetric) / 2) := Real.rpow_pos_of_pos he _
  have h2 : 0 < clockMQ sLastDirectionSinglet ((signS S : ℝ) * nuS sLastDirectionSinglet) ^ (1 / 6 : ℝ) :=
    Real.rpow_pos_of_pos (clockMQ_pos _ _) _
  have h3 := Real.exp_pos (-((PsiS S).re * statesL .symmetric * (statesN .symmetric - epsRec S) / 4))
  positivity

/-- **K⁰'s law on the direct sum of its two lines' words is the product over its two modes,** at the
coupling `G₁₂² = 8/15` of Proposition 195: `det(I − (GD) ⊗ M) = det(I − λ₊M) det(I − λ₋M)`,
`D = diag(S_d, pS_d)`, for every square `M` (Proposition 189 at K⁰). -/
theorem K0_law_on_direct_sum {n : Type*} [Fintype n] [DecidableEq n] (Sd : ℝ) (hS : 0 < Sd)
    (M : Matrix n n ℝ) :
    (1 - levelOp Sd (massOp .symmetric sPlaneSinglet * Sd) (Real.sqrt (8 / 15)) ⊗ₖ M).det =
      (1 - eigenPlus Sd (massOp .symmetric sPlaneSinglet * Sd) (8 / 15) • M).det *
        (1 - eigenMinus Sd (massOp .symmetric sPlaneSinglet * Sd) (8 / 15) • M).det := by
  have hp := massOp_plane_pos sPlaneSinglet
  have hg : Real.sqrt (8 / 15) ^ 2 = 8 / 15 := Real.sq_sqrt (by norm_num)
  have h := prop189_det Sd (massOp .symmetric sPlaneSinglet * Sd) (Real.sqrt (8 / 15))
    (Real.sqrt_pos.mpr (by norm_num)).ne' (mul_pos hp hS).ne' ?_ M
  · rw [hg] at h
    exact h
  · rw [hg]
    have : 0 < 4 * (8 / 15 : ℝ) * Sd * (massOp .symmetric sPlaneSinglet * Sd) := by positivity
    nlinarith [sq_nonneg (Sd - massOp .symmetric sPlaneSinglet * Sd)]

end Law

end Comparison

end
