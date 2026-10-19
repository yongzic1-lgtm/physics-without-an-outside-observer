module

public import Comparison.Law.Returns
public import Comparison.Existence.Sign
public import Comparison.Existence.Zero

/-!
# The law, VI: the positive walk underneath the two signs (equations (11) to (13))

The thirty-two elements `±γ_S` cover the sixteen two-spinor states twice. A step multiplies by `γ_t` and keeps
its sign instead of discarding it: on the lifted two-spinor states `(σ, k)`, `σ` the sign,
`liftTransition t (σ, k) = (σ · transitionSign t k, transition t k)`.

* `liftTransition_liftTransition`, `liftTransition_central`: each lifted step is an involution and commutes with the
  central involution `(σ, k) ↦ (−σ, k)`; `coverAdj_row`: **one positive five-regular walk on the
  thirty-two lifted two-spinor states**, `160` directed arcs (`card_arcs`).
* `cover_even`, `cover_odd`: **the two central characters:** on functions of `k` alone the walk is
  the ordinary walk `A = Σ_t X_t`; on `σ·g(k)` it is the signed walk `A₋ = Σ_t ν_tX_t`.
* `cover_blocks`, `cover_charpoly`: in the basis of the two signs the walk is `[[A₀, A₁], [A₁, A₀]]`,
  so **`det(λ − Ã) = det(λ − A) det(λ − A₋) = (λ − 5)(λ − 1)¹⁰(λ + 3)⁵(λ² − 5)⁸`**: the lifted
  spectrum `5¹, 1¹⁰, (−3)⁵, (√5)⁸, (−√5)⁸`; `signed_charpoly`: `det(λ − A₋) = (λ² − 5)⁸`.
* `signed_law_cover`: **`det(I − uB₋) = (1 − u²)²⁴(1 + 3u² + 16u⁴)⁸`** (equation (11); Sign.lean's
  `D_minus_rel`).
* `posExcursionCount`, `negExcursionCount`: the excursions arriving at the two signs of the central fibre;
  `excursion_split`: `r(n) = r₊(n) + r₋(n)`, `R(n) = r₊(n) − r₋(n)`; `arrival_gf`: their generating
  functions are `F₊ = (F + Φ)/2`, `F₋ = (F − Φ)/2` (equations (12), (13)); `arrival_split`:
  **`F₊(1) = 9/19`, `F₋(1) = 10/19`**.
-/

@[expose] public section

namespace Comparison

open Matrix Kronecker

namespace Law

/-! ## The lifted two-spinor states -/

/-- The flip of a step: `true` when the step reverses the sign of the two-spinor state. -/
def flips (t : Fin 5) (k : Fin 16) : Bool := decide (transitionSign t k ≠ 1)

/-- **A lifted step:** the sign is carried, `(σ, k) ↦ (σ · transitionSign t k, transition t k)`. -/
def liftTransition (t : Fin 5) (p : Bool × Fin 16) : Bool × Fin 16 :=
  (xor p.1 (flips t p.2), transition t p.2)

theorem flips_transition : ∀ (t : Fin 5) (k : Fin 16), flips t (transition t k) = flips t k := by decide

theorem liftTransition_liftTransition (t : Fin 5) (p : Bool × Fin 16) : liftTransition t (liftTransition t p) = p := by
  obtain ⟨σ, k⟩ := p
  simp only [liftTransition, flips_transition, transition_transition, Bool.xor_assoc, Bool.xor_self, Bool.xor_false]

/-- The central involution `(σ, k) ↦ (−σ, k)`. -/
def central (p : Bool × Fin 16) : Bool × Fin 16 := (!p.1, p.2)

/-- **The central involution commutes with the walk.** -/
theorem liftTransition_central (t : Fin 5) (p : Bool × Fin 16) :
    liftTransition t (central p) = central (liftTransition t p) := by
  obtain ⟨σ, k⟩ := p
  simp only [liftTransition, central, Bool.not_xor]

/-- The five lifted steps from a lifted two-spinor state reach five different lifted two-spinor states. -/
theorem liftTransition_inj (p : Bool × Fin 16) (t t' : Fin 5) : liftTransition t p = liftTransition t' p ↔ t = t' := by
  constructor
  · intro h
    exact (transition_eq_transition_iff t t' p.2).mp (congrArg Prod.snd h)
  · rintro rfl
    rfl

/-- **The positive walk on the thirty-two lifted two-spinor states.** -/
def coverAdj : Matrix (Bool × Fin 16) (Bool × Fin 16) ℂ :=
  Matrix.of fun p q => ∑ t : Fin 5, if p = liftTransition t q then 1 else 0

theorem coverAdj_mulVec (f : Bool × Fin 16 → ℂ) (p : Bool × Fin 16) :
    (coverAdj *ᵥ f) p = ∑ t : Fin 5, f (liftTransition t p) := by
  simp only [Matrix.mulVec, dotProduct, coverAdj, Matrix.of_apply, Finset.sum_mul, ite_mul,
    one_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_eq_single (liftTransition t p)]
  · rw [liftTransition_liftTransition, if_pos rfl]
  · intro q _ hq
    rw [if_neg]
    intro h
    apply hq
    rw [h, liftTransition_liftTransition]
  · simp

/-- **Five-regular:** every lifted two-spinor state has five out-steps. -/
theorem coverAdj_row : coverAdj *ᵥ (fun _ => 1) = fun _ => 5 := by
  funext p
  rw [coverAdj_mulVec]
  simp

/-- **`160` directed arcs.** -/
theorem card_arcs : Fintype.card ((Bool × Fin 16) × Fin 5) = 160 := by
  simp

/-- The ordinary walk on the sixteen two-spinor states, `A = Σ_t X_t`, over `ℂ`. -/
noncomputable def adjC : Matrix (Fin 16) (Fin 16) ℂ := ∑ t, transitionMat t

/-- The signed walk, `A₋ = Σ_t ν_t X_t`. -/
noncomputable def adjSigned : Matrix (Fin 16) (Fin 16) ℂ := ∑ t, signTransitionC (-1 : ℂ) t

theorem transitionMat_mulVec (t : Fin 5) (g : Fin 16 → ℂ) (k : Fin 16) :
    (transitionMat t *ᵥ g) k = g (transition t k) := by
  simp only [Matrix.mulVec, dotProduct, transitionMat, transitionMatZ, Matrix.map_apply, Matrix.of_apply]
  rw [Finset.sum_eq_single (transition t k)]
  · simp [transition_transition]
  · intro y _ hy
    have : ¬ k = transition t y := fun h => hy (by rw [h, transition_transition])
    simp [this]
  · simp

theorem transitionSign_transition' : ∀ (t : Fin 5) (k : Fin 16), transitionSign t (transition t k) = transitionSign t k := by
  decide

theorem signTransition_mulVec (t : Fin 5) (g : Fin 16 → ℂ) (k : Fin 16) :
    (signTransitionC (-1 : ℂ) t *ᵥ g) k = (transitionSign t k : ℂ) * g (transition t k) := by
  simp only [Matrix.mulVec, dotProduct, signTransitionC, Matrix.of_apply, ite_mul, zero_mul]
  rw [Finset.sum_eq_single (transition t k)]
  · rw [if_pos (transition_transition t k).symm, transitionSign_transition']
    rcases transitionSign_pm t k with h | h <;> simp [h]
  · intro y _ hy
    have : ¬ k = transition t y := fun h => hy (by rw [h, transition_transition])
    simp [this]
  · simp

/-- **The even central character:** on functions of the two-spinor state alone the walk is `A`. -/
theorem cover_even (g : Fin 16 → ℂ) :
    coverAdj *ᵥ (fun p => g p.2) = fun p => (adjC *ᵥ g) p.2 := by
  funext p
  rw [coverAdj_mulVec, adjC, Matrix.sum_mulVec, Finset.sum_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [transitionMat_mulVec]
  rfl

/-- The sign of a lifted two-spinor state, `±1`. -/
def sgn (σ : Bool) : ℂ := if σ then -1 else 1

theorem sgn_xor (σ τ : Bool) : sgn (xor σ τ) = sgn σ * sgn τ := by
  cases σ <;> cases τ <;> simp [sgn]

/-- **The odd central character:** on `σ·g(k)` the walk is the signed walk `A₋`. -/
theorem cover_odd (g : Fin 16 → ℂ) :
    coverAdj *ᵥ (fun p => sgn p.1 * g p.2) = fun p => sgn p.1 * (adjSigned *ᵥ g) p.2 := by
  funext p
  rw [coverAdj_mulVec, adjSigned, Matrix.sum_mulVec, Finset.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [signTransition_mulVec]
  simp only [liftTransition, sgn_xor]
  have : sgn (flips t p.2) = (transitionSign t p.2 : ℂ) := by
    rcases transitionSign_pm t p.2 with h | h <;> simp [sgn, flips, h]
  rw [this]
  ring

/-- The sign-keeping and the sign-flipping parts of the steps. -/
noncomputable def keepPart : Matrix (Fin 16) (Fin 16) ℂ :=
  Matrix.of fun k' k => ∑ t : Fin 5, if k' = transition t k ∧ flips t k = false then 1 else 0

noncomputable def flipPart : Matrix (Fin 16) (Fin 16) ℂ :=
  Matrix.of fun k' k => ∑ t : Fin 5, if k' = transition t k ∧ flips t k = true then 1 else 0

/-- The two signs as a sum of two copies of the sixteen. -/
def signSplit : Fin 16 ⊕ Fin 16 ≃ Bool × Fin 16 where
  toFun x := match x with
    | Sum.inl k => (false, k)
    | Sum.inr k => (true, k)
  invFun p := if p.1 then Sum.inr p.2 else Sum.inl p.2
  left_inv x := by cases x <;> simp
  right_inv p := by
    obtain ⟨σ, k⟩ := p
    cases σ <;> simp

/-- **In the basis of the two signs the walk is `[[A₀, A₁], [A₁, A₀]]`.** -/
theorem cover_blocks :
    coverAdj.submatrix signSplit signSplit = fromBlocks keepPart flipPart flipPart keepPart := by
  ext (k' | k') (k | k) <;>
    simp only [coverAdj, keepPart, flipPart, Matrix.submatrix_apply, signSplit, Equiv.coe_fn_mk,
      Matrix.of_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, liftTransition, Prod.mk.injEq] <;>
    refine Finset.sum_congr rfl fun t _ => ?_ <;>
    cases h : flips t k <;> simp [h, eq_comm]

theorem keep_add_flip : keepPart + flipPart = adjC := by
  ext k' k
  simp only [keepPart, flipPart, adjC, Matrix.add_apply, Matrix.of_apply, Matrix.sum_apply,
    transitionMat, transitionMatZ, Matrix.map_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  cases h : flips t k <;> by_cases hk : k' = transition t k <;> simp [h, hk]

theorem keep_sub_flip : keepPart - flipPart = adjSigned := by
  ext k' k
  simp only [keepPart, flipPart, adjSigned, Matrix.sub_apply, Matrix.of_apply, Matrix.sum_apply,
    signTransitionC, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun t _ => ?_
  have hf : flips t k = decide (transitionSign t k ≠ 1) := rfl
  rcases transitionSign_pm t k with h | h <;> by_cases hk : k' = transition t k <;> simp [hf, h, hk]

/-- **`det(λ − A) = (λ − 5)(λ − 1)¹⁰(λ + 3)⁵`.** -/
theorem adj_charpoly (l : ℂ) :
    (l • (1 : Matrix (Fin 16) (Fin 16) ℂ) - adjC).det =
      (l - 5) * (l - 1) ^ 10 * (l + 3) ^ 5 := by
  have h := det_of_diag adjC (fun l => ((charValue l : ℤ) : ℂ)) adjacency_mul_charTable_C l 1
  rw [one_smul] at h
  rw [h]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, charValue]
  simp [disagreeSet]
  ring

/-- **`det(λ − A₋) = (λ² − 5)⁸`:** `A₋` is `(Σ_t γ_t) ⊗ 1` in another basis, and
`det(λ − Σ_tγ_t) = (λ² − 5)²`. -/
theorem signed_charpoly (l : ℂ) :
    (l • (1 : Matrix (Fin 16) (Fin 16) ℂ) - adjSigned).det = (l ^ 2 - 5) ^ 8 := by
  have hsum : adjSigned = relSqᴴ * onRel (∑ t, lineOnRel t) * relSq := by
    rw [adjSigned, onRel_sum, Matrix.mul_sum, Matrix.sum_mul]
    exact Finset.sum_congr rfl fun t _ => signTransition_eq_conj t
  have h := det_conj_unitary hsum l 1
  simp only [one_smul] at h
  rw [h]
  have h2 : (l • (1 : Matrix (Fin 16) (Fin 16) ℂ) - onRel (∑ t, lineOnRel t)) =
      onRel (l • (1 : Matrix Two Two ℂ) - ∑ t, lineOnRel t) := by
    ext i j
    simp [onRel, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply]
  rw [h2, onRel_det]
  have h3 : l • (1 : Matrix Two Two ℂ) - ∑ t, lineOnRel t =
      (l • (1 : Matrix Four Four ℂ) - ∑ t, γ t) ⊗ₖ (1 : Matrix Four Four ℂ) := by
    rw [sum_lineOnRel, sub_kronecker', Matrix.smul_kronecker, Matrix.one_kronecker_one]
  rw [h3, det_kronecker, det_one, one_pow, mul_one]
  have h4 : (l • (1 : Matrix Four Four ℂ) - ∑ t, γ t).det = (l ^ 2 - 5) ^ 2 := by
    have := det_cone l (fun _ => -1)
    have hs : (∑ s : Fin 5, (-1 : ℂ) • γ s) = -(∑ t, γ t) := by
      simp [Finset.sum_neg_distrib]
    rw [hs, ← sub_eq_add_neg] at this
    rw [this]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    norm_num
  rw [h4]
  simp only [Fintype.card_prod]
  norm_num
  ring

/-- **The lifted spectrum:** `det(λ − Ã) = (λ − 5)(λ − 1)¹⁰(λ + 3)⁵(λ² − 5)⁸`. -/
theorem cover_charpoly (l : ℂ) :
    (l • (1 : Matrix (Bool × Fin 16) (Bool × Fin 16) ℂ) - coverAdj).det =
      (l - 5) * (l - 1) ^ 10 * (l + 3) ^ 5 * (l ^ 2 - 5) ^ 8 := by
  rw [← det_submatrix_equiv_self signSplit]
  have hc : ∀ x y, coverAdj (signSplit x) (signSplit y) =
      fromBlocks keepPart flipPart flipPart keepPart x y := by
    intro x y
    rw [← cover_blocks]
    rfl
  have e : (l • (1 : Matrix (Bool × Fin 16) (Bool × Fin 16) ℂ) - coverAdj).submatrix signSplit
      signSplit = fromBlocks (l • 1 - keepPart) (-flipPart) (-flipPart) (l • 1 - keepPart) := by
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, hc, Matrix.one_apply,
      signSplit.injective.eq_iff]
    rcases x with i | i <;> rcases y with j | j <;>
      simp [fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
        Matrix.one_apply]
  rw [e, det_block_sym]
  have e1 : l • (1 : Matrix (Fin 16) (Fin 16) ℂ) - keepPart + -flipPart = l • 1 - adjC := by
    rw [← keep_add_flip]
    abel
  have e2 : l • (1 : Matrix (Fin 16) (Fin 16) ℂ) - keepPart - -flipPart = l • 1 - adjSigned := by
    rw [← keep_sub_flip]
    abel
  rw [e1, e2, adj_charpoly, signed_charpoly]

/-- **Equation (11):** the odd character's law, `det(I − uB₋) = (1 − u²)²⁴(1 + 3u² + 16u⁴)⁸`. -/
theorem signed_law_cover (u : ℂ) :
    (1 - u • stepOp (signTransitionC (-1 : ℂ))).det =
      (1 - u ^ 2) ^ 24 * (1 + 3 * u ^ 2 + 16 * u ^ 4) ^ 8 :=
  D_minus_rel u

/-! ## The arrivals at the two signs of the central fibre -/

/-- The excursions of length `n` that close with the sign `+1`. -/
def posExcursionCount (n : ℕ) : ℕ := ((excursions n).filter fun w => coef w = 1).card

/-- The excursions of length `n` that close with the sign `−1`. -/
def negExcursionCount (n : ℕ) : ℕ := ((excursions n).filter fun w => coef w = -1).card

theorem coef_pm (w : List (Fin 5)) : coef w = 1 ∨ coef w = -1 := by
  have h := coef_sq w
  have : (coef w - 1) * (coef w + 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h1 | h1
  · left
    linarith
  · right
    linarith

/-- **`r(n) = r₊(n) + r₋(n)` and `R(n) = r₊(n) − r₋(n)`.** -/
theorem excursion_split (n : ℕ) :
    (excursionCount n : ℤ) = posExcursionCount n + negExcursionCount n ∧
      signedExcursionCount n = posExcursionCount n - negExcursionCount n := by
  have hdisj : Disjoint ((excursions n).filter fun w => coef w = 1)
      ((excursions n).filter fun w => coef w = -1) := by
    rw [Finset.disjoint_filter]
    intro w _ h1 h2
    rw [h1] at h2
    norm_num at h2
  have hunion : (excursions n).filter (fun w => coef w = 1) ∪ (excursions n).filter (fun w => coef w = -1) =
      excursions n := by
    ext w
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -⟩) <;> exact h
    · intro h
      rcases coef_pm w with h1 | h1
      · exact Or.inl ⟨h, h1⟩
      · exact Or.inr ⟨h, h1⟩
  constructor
  · rw [excursionCount, ← hunion, Finset.card_union_of_disjoint hdisj]
    push_cast
    rfl
  · rw [signedExcursionCount, ← hunion, Finset.sum_union hdisj, posExcursionCount, negExcursionCount]
    rw [Finset.sum_congr rfl (fun w hw => (Finset.mem_filter.mp hw).2),
      Finset.sum_congr rfl (fun w hw => (Finset.mem_filter.mp hw).2)]
    simp only [Finset.sum_const, smul_eq_mul, mul_one, mul_neg]
    ring

/-- The chance of arriving at `+1`: `r₊(n)/(5·4ⁿ⁻¹)`. -/
noncomputable def posLaw (n : ℕ) : ℝ := (posExcursionCount n : ℝ) / (5 * 4 ^ (n - 1))

/-- The chance of arriving at `−1`: `r₋(n)/(5·4ⁿ⁻¹)`. -/
noncomputable def negLaw (n : ℕ) : ℝ := (negExcursionCount n : ℝ) / (5 * 4 ^ (n - 1))

theorem posLaw_eq (n : ℕ) : posLaw n = (excursionLaw n + signedLaw n) / 2 := by
  obtain ⟨h1, h2⟩ := excursion_split n
  have h1' : (excursionCount n : ℝ) = posExcursionCount n + negExcursionCount n := by exact_mod_cast h1
  have h2' : (signedExcursionCount n : ℝ) = posExcursionCount n - negExcursionCount n := by exact_mod_cast h2
  rw [posLaw, excursionLaw, signedLaw, h1', h2']
  ring

theorem negLaw_eq (n : ℕ) : negLaw n = (excursionLaw n - signedLaw n) / 2 := by
  obtain ⟨h1, h2⟩ := excursion_split n
  have h1' : (excursionCount n : ℝ) = posExcursionCount n + negExcursionCount n := by exact_mod_cast h1
  have h2' : (signedExcursionCount n : ℝ) = posExcursionCount n - negExcursionCount n := by exact_mod_cast h2
  rw [negLaw, excursionLaw, signedLaw, h1', h2']
  ring

/-- **Equations (12), (13): `F₊ = (F + Φ)/2` and `F₋ = (F − Φ)/2`** for `|z| ≤ 1`. -/
theorem arrival_gf (z : ℂ) (hz : ‖z‖ ≤ 1) :
    HasSum (fun n => (posLaw n : ℂ) * z ^ n)
        ((z ^ 4 * (1 + z) / (16 - 8 * z - 3 * z ^ 2 - 3 * z ^ 3) + -z ^ 4 / (16 + 3 * z ^ 2)) / 2) ∧
      HasSum (fun n => (negLaw n : ℂ) * z ^ n)
        ((z ^ 4 * (1 + z) / (16 - 8 * z - 3 * z ^ 2 - 3 * z ^ 3) - -z ^ 4 / (16 + 3 * z ^ 2)) / 2) := by
  have hF := excursion_gf z hz
  have hΦ := signed_gf z hz
  constructor
  · have := (hF.add hΦ).div_const 2
    convert this using 1
    funext n
    rw [posLaw_eq]
    push_cast
    ring
  · have := (hF.sub hΦ).div_const 2
    convert this using 1
    funext n
    rw [negLaw_eq]
    push_cast
    ring

/-- **The split of the first returns at the central fibre: `F₊(1) = 9/19`, `F₋(1) = 10/19`.** -/
theorem arrival_split : HasSum posLaw (9 / 19) ∧ HasSum negLaw (10 / 19) := by
  constructor
  · have := (excursion_total.add Φ_one).div_const 2
    convert this using 1
    · funext n
      exact posLaw_eq n
    · norm_num
  · have := (excursion_total.sub Φ_one).div_const 2
    convert this using 1
    · funext n
      exact negLaw_eq n
    · norm_num

end Law

end Comparison

end
