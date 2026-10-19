module

public import Comparison.Existence.LogDet
public import Comparison.Colour.GramTerm

/-!
# The whole picture, statement 13: the one-arc equation at every arc

`Bc = B` is the step on the eighty states over `ℂ`
(`Bc_eq`: it is `stepOp transitionMat`), `D(u) = det(I − uB)` the law (`lawPoly`), `D′` its
derivative. Marking one arc `q → p` with a phase `z = e^{−iθ}` (`Bmark p q z`):

* `one_arc`: **`D_θ(u) = D(u) + (e^{−iθ} − 1) u D′(u)/320` at every one of the 320 arcs**, for every
  `u` and every `z`.

The proof: the determinant is affine in the marked entry, `D_θ = D − u(z − 1) adj(I − uB)_{qp}`
(`det_mark`); every arc has the same cofactor (`arc_cofactor_const`), because the transitions of the
two-spinor states (`mvState`) and the relabellings of the five directions (`pmState`, through `relPerm`) keep `B`
and carry any arc to any other; and Jacobi's formula (`derivative_det_one_sub`) gives
`D′ = −tr(adj(I − uB) B) = −320 × that cofactor` (`lawPoly_deriv`, `trace_adj_B`).
-/

@[expose] public section

namespace Comparison.WholePicture

open Matrix Polynomial

/-- The step `B` on the eighty states over `ℂ`: `B_{s′s} = 1` when `s′` continues `s`. -/
noncomputable abbrev Bc : Matrix State State ℂ := stepT fun _ _ => (1 : ℂ)

theorem Bc_apply (p q : State) : Bc p q = if Continues q p then 1 else 0 := by
  simp [Bc, stepT]

theorem Bc_eq : Bc = stepOp transitionMat := stepT_one_eq

/-! ## Relabelling the two-spinor states by a permutation of the lines -/

theorem disagreeSet_inj : ∀ k l : Fin 16, disagreeSet k = disagreeSet l → k = l := by decide

theorem disagreeSet_injective : Function.Injective disagreeSet :=
  fun k l h => disagreeSet_inj k l h

theorem even_sets_are_relations :
    ∀ S : Finset (Fin 5), S.card % 2 = 0 → ∃ k : Fin 16, disagreeSet k = S := by decide

theorem disagreeSet_card_even : ∀ k : Fin 16, (disagreeSet k).card % 2 = 0 := by decide

theorem relPerm_exists (π : Equiv.Perm (Fin 5)) (k : Fin 16) :
    ∃! l : Fin 16, disagreeSet l = (disagreeSet k).map π.toEmbedding := by
  obtain ⟨l, hl⟩ := even_sets_are_relations ((disagreeSet k).map π.toEmbedding)
    (by rw [Finset.card_map]; exact disagreeSet_card_even k)
  exact ⟨l, hl, fun l' hl' => disagreeSet_injective (hl'.trans hl.symm)⟩

/-- The two-spinor state whose disagreement set is the image under `π` of that of `k`. -/
def relPerm (π : Equiv.Perm (Fin 5)) (k : Fin 16) : Fin 16 :=
  Fintype.choose _ (relPerm_exists π k)

theorem disagreeSet_relPerm (π : Equiv.Perm (Fin 5)) (k : Fin 16) :
    disagreeSet (relPerm π k) = (disagreeSet k).map π.toEmbedding :=
  Fintype.choose_spec _ (relPerm_exists π k)

theorem relPerm_injective (π : Equiv.Perm (Fin 5)) : Function.Injective (relPerm π) := by
  intro k l h
  have h' := congrArg disagreeSet h
  rw [disagreeSet_relPerm, disagreeSet_relPerm, Finset.map_inj] at h'
  exact disagreeSet_injective h'

/-- **A relabelling of the lines carries the transitions:** `π(transition_t k) = transition_{π t}(π k)`. -/
theorem relPerm_transition (π : Equiv.Perm (Fin 5)) (t : Fin 5) (k : Fin 16) :
    relPerm π (transition t k) = transition (π t) (relPerm π k) := by
  apply disagreeSet_injective
  rw [disagreeSet_relPerm, disagreeSet_transition, disagreeSet_transition, disagreeSet_relPerm]
  simp only [Finset.map_eq_image, Equiv.coe_toEmbedding]
  rw [Finset.image_symmDiff _ _ π.injective]
  congr 1
  ext a
  simp only [Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact fun h => hb (π.injective h)
  · intro ha
    exact ⟨π.symm a, fun h => ha (by rw [← h, Equiv.apply_symm_apply]), Equiv.apply_symm_apply π a⟩

theorem relPerm_zero (π : Equiv.Perm (Fin 5)) : relPerm π 0 = 0 := by
  apply disagreeSet_injective
  rw [disagreeSet_relPerm]
  simp [disagreeSet]

/-! ## The symmetries of the step -/

theorem transition_comm : ∀ (r t : Fin 5) (k : Fin 16), transition r (transition t k) = transition t (transition r k) := by
  decide

theorem transition_inj' (s : Fin 5) {x y : Fin 16} (h : transition s x = transition s y) : x = y := by
  have := congrArg (transition s) h
  rwa [transition_transition, transition_transition] at this

/-- A transition of the two-spinor state, the last-step direction kept. -/
def mvState (r : Fin 5) (s : State) : State := (transition r s.1, s.2)

/-- A relabelling of the lines on the two-spinor state and on the last-step direction. -/
def pmState (π : Equiv.Perm (Fin 5)) (s : State) : State := (relPerm π s.1, π s.2)

theorem continues_mv (r : Fin 5) (q p : State) :
    Continues (mvState r q) (mvState r p) ↔ Continues q p := by
  simp only [Continues, mvState]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, transition_inj' r ?_⟩
    rw [h2, transition_comm]
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rw [h2, transition_comm]

theorem continues_pm (π : Equiv.Perm (Fin 5)) (q p : State) :
    Continues (pmState π q) (pmState π p) ↔ Continues q p := by
  simp only [Continues, pmState, ← relPerm_transition]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun e => h1 (by rw [e]), relPerm_injective π h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun e => h1 (π.injective e), by rw [h2]⟩

theorem mvState_involutive (r : Fin 5) : Function.Involutive (mvState r) := by
  intro s
  simp [mvState, transition_transition]

theorem pmState_injective (π : Equiv.Perm (Fin 5)) : Function.Injective (pmState π) := by
  intro s s' h
  simp only [pmState, Prod.mk.injEq] at h
  exact Prod.ext (relPerm_injective π h.1) (π.injective h.2)

/-- The transition `r` as a permutation of the eighty states. -/
def mvEquiv (r : Fin 5) : State ≃ State := (mvState_involutive r).toPerm _

/-- The relabelling `π` as a permutation of the eighty states. -/
noncomputable def pmEquiv (π : Equiv.Perm (Fin 5)) : State ≃ State :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (pmState_injective π))

/-- **A symmetry of the step keeps every cofactor of the law.** -/
theorem adj_invariant (σ : State ≃ State) (hσ : ∀ p q, Continues (σ q) (σ p) ↔ Continues q p)
    (u : ℂ) (p q : State) :
    (1 - u • Bc).adjugate (σ q) (σ p) = (1 - u • Bc).adjugate q p := by
  have hM : (1 - u • Bc).submatrix σ σ = 1 - u • Bc := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply,
      Bc_apply, σ.injective.eq_iff, hσ]
  have h := Matrix.adjugate_submatrix_equiv_self σ (1 - u • Bc)
  rw [hM] at h
  have := congrFun (congrFun h q) p
  rw [Matrix.submatrix_apply] at this
  exact this.symm

/-! ## Every arc has the same cofactor -/

theorem relation_reach : ∀ y : Fin 16,
    y = 0 ∨ (∃ a : Fin 5, y = transition a 0) ∨ ∃ a b : Fin 5, y = transition a (transition b 0) := by
  decide

theorem perm_pair : ∀ t s : Fin 5, t ≠ s →
    (Equiv.swap 0 t * Equiv.swap 1 (Equiv.swap 0 t s)) 0 = t ∧
      (Equiv.swap 0 t * Equiv.swap 1 (Equiv.swap 0 t s)) 1 = s := by
  decide

/-- A transition of the two-spinor state carries the arc `(y, t) → (transition s y, s)` to the arc from `transition r y`. -/
theorem arc_transition (u : ℂ) (r : Fin 5) (y : Fin 16) (t s : Fin 5) :
    (1 - u • Bc).adjugate (transition r y, t) (transition s (transition r y), s) =
      (1 - u • Bc).adjugate (y, t) (transition s y, s) := by
  have h := adj_invariant (mvEquiv r) (fun p q => continues_mv r q p) u (transition s y, s) (y, t)
  have e1 : (mvEquiv r) (y, t) = (transition r y, t) := rfl
  have e2 : (mvEquiv r) (transition s y, s) = (transition s (transition r y), s) := by
    change (transition r (transition s y), s) = _
    rw [transition_comm]
  rw [e1, e2] at h
  exact h

/-- A relabelling carries the arc `(0, 0) → (transition 1 0, 1)` to the arc
`(0, π 0) → (transition (π 1) 0, π 1)`. -/
theorem arc_perm (u : ℂ) (π : Equiv.Perm (Fin 5)) :
    (1 - u • Bc).adjugate (0, π 0) (transition (π 1) 0, π 1) =
      (1 - u • Bc).adjugate (0, 0) (transition 1 0, 1) := by
  have h := adj_invariant (pmEquiv π) (fun p q => continues_pm π q p) u (transition 1 0, 1) (0, 0)
  have e1 : (pmEquiv π) (0, 0) = (0, π 0) := by
    change (relPerm π 0, π 0) = _
    rw [relPerm_zero]
  have e2 : (pmEquiv π) (transition 1 0, 1) = (transition (π 1) 0, π 1) := by
    change (relPerm π (transition 1 0), π 1) = _
    rw [relPerm_transition, relPerm_zero]
  rw [e1, e2] at h
  exact h

/-- **Every one of the 320 arcs has the same cofactor in the law.** -/
theorem arc_cofactor_const (u : ℂ) (y : Fin 16) (t s : Fin 5) (hts : t ≠ s) :
    (1 - u • Bc).adjugate (y, t) (transition s y, s) = (1 - u • Bc).adjugate (0, 0) (transition 1 0, 1) := by
  have h0 : (1 - u • Bc).adjugate (0, t) (transition s 0, s) =
      (1 - u • Bc).adjugate (0, 0) (transition 1 0, 1) := by
    obtain ⟨h1, h2⟩ := perm_pair t s hts
    have := arc_perm u (Equiv.swap 0 t * Equiv.swap 1 (Equiv.swap 0 t s))
    rw [h1, h2] at this
    exact this
  rcases relation_reach y with hy | ⟨a, hy⟩ | ⟨a, b, hy⟩
  · subst hy
    exact h0
  · subst hy
    rw [arc_transition u a 0 t s]
    exact h0
  · subst hy
    rw [arc_transition u a (transition b 0) t s, arc_transition u b 0 t s]
    exact h0

/-! ## The trace of Jacobi's formula -/

/-- The cofactor of any arc `i → j` is the one of the arc `(0, 0) → (transition 1 0, 1)`. -/
theorem adj_continues (u : ℂ) (i j : State) (h : Continues i j) :
    (1 - u • Bc).adjugate i j = (1 - u • Bc).adjugate (0, 0) (transition 1 0, 1) := by
  obtain ⟨y, t⟩ := i
  obtain ⟨y', s⟩ := j
  obtain ⟨hst, hy⟩ := h
  simp only at hst hy
  subst hy
  exact arc_cofactor_const u y t s (Ne.symm hst)

/-- **`tr(adj(I − uB) B) = 320 × (the cofactor of one arc)`.** -/
theorem trace_adj_B (u : ℂ) :
    ((1 - u • Bc).adjugate * Bc).trace = 320 * (1 - u • Bc).adjugate (0, 0) (transition 1 0, 1) := by
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Bc_apply, mul_ite, mul_one, mul_zero]
  have hrow : ∀ i : State, (∑ j : State, if Continues i j then (1 - u • Bc).adjugate i j else 0) =
      4 * (1 - u • Bc).adjugate (0, 0) (transition 1 0, 1) := by
    intro i
    rw [← Finset.sum_filter, Finset.sum_congr rfl
      (fun j hj => adj_continues u i j (Finset.mem_filter.mp hj).2), Finset.sum_const,
      card_continuations, nsmul_eq_mul]
    norm_num
  rw [Finset.sum_congr rfl fun i _ => hrow i, Finset.sum_const, Finset.card_univ]
  simp only [Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  ring

/-! ## The law and its derivative -/

/-- **The law** `D(u) = det(I − uB)` as a polynomial. -/
noncomputable def lawPoly : ℂ[X] := (1 - (X : ℂ[X]) • Bc.map C).det

theorem lawPoly_eval (u : ℂ) : lawPoly.eval u = (1 - u • Bc).det :=
  (det_one_sub_smul_poly Bc u).symm

theorem eval_map_one_sub (u : ℂ) :
    (Polynomial.evalRingHom u).mapMatrix (1 - (X : ℂ[X]) • Bc.map C) = 1 - u • Bc := by
  ext i j
  by_cases h : i = j
  · subst h
    simp
    ring
  · simp [h]
    ring

/-- **Jacobi:** `D′(u) = −tr(adj(I − uB) B)`. -/
theorem lawPoly_deriv (u : ℂ) :
    (derivative lawPoly).eval u = -((1 - u • Bc).adjugate * Bc).trace := by
  rw [lawPoly, derivative_det_one_sub, Polynomial.eval_neg]
  congr 1
  have hadj := RingHom.map_adjugate (Polynomial.evalRingHom u) (1 - (X : ℂ[X]) • Bc.map C)
  rw [eval_map_one_sub] at hadj
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Polynomial.eval_finsetSum,
    Polynomial.eval_mul, Matrix.map_apply, Polynomial.eval_C]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  have := congrFun (congrFun hadj i) k
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Polynomial.coe_evalRingHom] at this
  rw [this]

/-! ## The one-arc equation -/

/-- The step with the one arc `q → p` carrying the phase `z`. -/
noncomputable def Bmark (p q : State) (z : ℂ) : Matrix State State ℂ :=
  Matrix.of fun i j => if i = p ∧ j = q then z else Bc i j

/-- The determinant is affine in the marked entry. -/
theorem det_mark (p q : State) (harc : Continues q p) (z u : ℂ) :
    (1 - u • Bmark p q z).det = (1 - u • Bc).det - u * (z - 1) * (1 - u • Bc).adjugate q p := by
  have hBpq : Bc p q = 1 := by simp [Bc_apply, harc]
  have hrow : 1 - u • Bmark p q z =
      (1 - u • Bc).updateRow p ((1 - u • Bc) p + (-(u * (z - 1))) • Pi.single q 1) := by
    ext i j
    by_cases hi : i = p
    · subst hi
      simp only [Matrix.updateRow_self, Pi.add_apply, Pi.smul_apply, Matrix.sub_apply,
        Matrix.smul_apply, Bmark, Matrix.of_apply, true_and, smul_eq_mul]
      by_cases hj : j = q
      · subst hj
        simp [hBpq]
        ring
      · simp [hj]
    · simp [Bmark, hi]
  rw [hrow, Matrix.det_updateRow_add, Matrix.updateRow_eq_self, Matrix.det_updateRow_smul,
    ← Matrix.adjugate_apply]
  ring

/-- **The one-arc equation:** marking any one of the 320 arcs with the phase `z = e^{−iθ}`,
`D_θ(u) = D(u) + (z − 1) u D′(u)/320`. -/
theorem one_arc (p q : State) (harc : Continues q p) (z u : ℂ) :
    (1 - u • Bmark p q z).det =
      lawPoly.eval u + (z - 1) * u * (derivative lawPoly).eval u / 320 := by
  rw [det_mark p q harc, lawPoly_eval, lawPoly_deriv, trace_adj_B]
  obtain ⟨y, t⟩ := q
  obtain ⟨y', s⟩ := p
  simp only [Continues] at harc
  obtain ⟨hst, hy⟩ := harc
  subst hy
  rw [arc_cofactor_const u y t s (Ne.symm hst)]
  ring

/-- The same with `z = e^{−iθ}`. -/
theorem one_arc_phase (p q : State) (harc : Continues q p) (θ u : ℂ) :
    (1 - u • Bmark p q (Complex.exp (-Complex.I * θ))).det =
      lawPoly.eval u + (Complex.exp (-Complex.I * θ) - 1) * u * (derivative lawPoly).eval u / 320 :=
  one_arc p q harc _ u

end Comparison.WholePicture

end
