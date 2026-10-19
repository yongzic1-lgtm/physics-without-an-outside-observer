module

public import Comparison.Existence.IharaBass

/-!
# Book X. Count and sign: one central sign splits the law (Proposition 53)

* `sign_relations`: in the products of the five directions, `t_i² = 1`, `t_it_j = −t_jt_i` (`i ≠ j`), so
  `−1` is the central sign `c`; and `t₁t₂t₃t₄t₅ = +1` (`γ_prod`). (P's FORMAL_VI_ON writes
  `t₁⋯t₅ = c`; in the model of Proposition 23 the product is `+1`, not `−1`.)
* `IdemSplit`, `centralSign_split`: for a central `c` with `c² = 1` and `2` invertible,
  `p± = (1 ± c)/2` are orthogonal idempotents with `p₊ + p₋ = 1`, `p₊ − p₋ = c`.
* `det_split`, `mul_split`: `det(p₊X + p₋Y) = p₊ det X + p₋ det Y`,
  `(p₊X + p₋Y)(p₊X' + p₋Y') = p₊XX' + p₋YY'`.
* `signTransitionC c t`: the transition of the change `t` on the sixteen two-spinor states, carrying `1` where the step
  keeps the sign and `c` where it flips it. `law_split`: **`det(I − uB_c) = p₊ det(I − uB₊) +
  p₋ det(I − uB₋)`**; `resolvent_split`: **`(I − uB_c)⁻¹ = p₊Z₊ + p₋Z₋`**.
* `det_block_sym`: `det [[A₀, A₁], [A₁, A₀]] = det(A₀ + A₁) det(A₀ − A₁)`; `law_norm`: over `ℂ`, the
  operator `I − uB_c` on `𝒞⁸⁰ = ℂ⁸⁰ ⊕ c ℂ⁸⁰` has determinant **`det(I − uB₊) det(I − uB₋)`**.
* `signTransition_plus`: `B₊ = B[1]` is the walk of Proposition 26 (`transitionMat`); `D_minus_rel`: in the
  two-spinor state basis the signed step `B₋ = B[ν]` has `det(I − uB[ν]) = (1 − u²)²⁴(1 + 3u² + 16u⁴)⁸`,
  the `D₋` of Proposition 54.
-/

@[expose] public section

namespace Comparison

open Matrix hiding J
open Complex Kronecker

/-! ## The group of the five directions and its central sign -/

/-- **The sign relations:** `t_i² = 1`, `t_it_j = −t_jt_i` for `i ≠ j`, and `t₁t₂t₃t₄t₅ = 1`. -/
theorem sign_relations :
    (∀ i, γ i * γ i = 1) ∧ (∀ i j, i ≠ j → γ i * γ j = -(γ j * γ i)) ∧
      γ 0 * γ 1 * γ 2 * γ 3 * γ 4 = 1 :=
  ⟨γ_mul_self, fun _ _ h => γ_anticomm h, γ_prod⟩

/-! ## Two orthogonal idempotents split a ring -/

section Split

variable {A : Type*} [CommRing A]

/-- `p` and `q` are orthogonal idempotents adding to one. -/
structure IdemSplit (p q : A) : Prop where
  pp : p * p = p
  qq : q * q = q
  pq : p * q = 0
  sum : p + q = 1

theorem idem_pow {p : A} (hp : p * p = p) : ∀ k : ℕ, 0 < k → p ^ k = p
  | 1, _ => pow_one p
  | k + 2, _ => by rw [pow_succ, idem_pow hp (k + 1) (Nat.succ_pos k), hp]

/-- **The central sign splits:** for `c² = 1`, `p± = (1 ± c)/2` are orthogonal idempotents with
`p₊ + p₋ = 1` and `p₊ − p₋ = c`. -/
theorem centralSign_split [Invertible (2 : A)] (c : A) (hc : c * c = 1) :
    IdemSplit (⅟2 * (1 + c)) (⅟2 * (1 - c)) ∧ ⅟2 * (1 + c) - ⅟2 * (1 - c) = c := by
  have h2 : (⅟2 : A) * 2 = 1 := invOf_mul_self 2
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · linear_combination (⅟2 * ⅟2 : A) * hc + (⅟2 * (1 + c)) * h2
  · linear_combination (⅟2 * ⅟2 : A) * hc + (⅟2 * (1 - c)) * h2
  · linear_combination (-(⅟2 * ⅟2) : A) * hc
  · linear_combination h2
  · linear_combination c * h2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **`det(pX + qY) = p det X + q det Y`** for a split `p + q = 1`. -/
theorem det_split {p q : A} (h : IdemSplit p q) [Nonempty ι] (X Y : Matrix ι ι A) :
    (p • X + q • Y).det = p * X.det + q * Y.det := by
  have hcard : 0 < Fintype.card ι := Fintype.card_pos
  have hp : p • (p • X + q • Y) = p • X := by
    rw [smul_add, smul_smul, smul_smul, h.pp, h.pq, zero_smul, add_zero]
  have hq : q • (p • X + q • Y) = q • Y := by
    rw [smul_add, smul_smul, smul_smul, h.qq, mul_comm, h.pq, zero_smul, zero_add]
  have e1 : p * (p • X + q • Y).det = p * X.det := by
    have := congrArg Matrix.det hp
    rw [det_smul, det_smul, idem_pow h.pp _ hcard] at this
    exact this
  have e2 : q * (p • X + q • Y).det = q * Y.det := by
    have := congrArg Matrix.det hq
    rw [det_smul, det_smul, idem_pow h.qq _ hcard] at this
    exact this
  calc (p • X + q • Y).det = (p + q) * (p • X + q • Y).det := by rw [h.sum, one_mul]
    _ = p * X.det + q * Y.det := by rw [add_mul, e1, e2]

/-- `(pX + qY)(pX' + qY') = p XX' + q YY'`. -/
theorem mul_split {p q : A} (h : IdemSplit p q) (X Y X' Y' : Matrix ι ι A) :
    (p • X + q • Y) * (p • X' + q • Y') = p • (X * X') + q • (Y * Y') := by
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul,
    h.pp, h.qq, h.pq, mul_comm q p, zero_smul, add_zero, zero_add]

/-! ## The step with the central sign -/

/-- **The transition with a central sign:** `1` where the step keeps the sign of the two-spinor state, `c` where
it flips it. -/
def signTransitionC (c : A) (t : Fin 5) : Matrix (Fin 16) (Fin 16) A :=
  Matrix.of fun k' k => if k' = transition t k then (if transitionSign t k = 1 then 1 else c) else 0

theorem signTransitionC_split {p q c : A} (hsum : p + q = 1) (hc : p - q = c) (t : Fin 5) :
    signTransitionC c t = p • signTransitionC 1 t + q • signTransitionC (-1) t := by
  ext k' k
  simp only [signTransitionC, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs
  · rw [mul_one, mul_one, hsum]
  · rw [mul_one, mul_neg_one, ← sub_eq_add_neg, hc]
  · simp

theorem stepOp_add_smul {V : Type*} [Fintype V] [DecidableEq V] (Γ Γ' : Fin 5 → Matrix V V A)
    (a b : A) : stepOp (fun t => a • Γ t + b • Γ' t) = a • stepOp Γ + b • stepOp Γ' := by
  ext x y
  simp only [stepOp, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs <;> simp

/-- **The law splits by the central sign:** `det(I − uB_c) = p₊ det(I − uB₊) + p₋ det(I − uB₋)`. -/
theorem law_matrix_split [Invertible (2 : A)] (c u : A) (hc : c * c = 1) :
    (1 : Matrix (Fin 16 × Fin 5) (Fin 16 × Fin 5) A) - u • stepOp (signTransitionC c) =
      (⅟2 * (1 + c)) • (1 - u • stepOp (signTransitionC (1 : A))) +
        (⅟2 * (1 - c)) • (1 - u • stepOp (signTransitionC (-1 : A))) := by
  obtain ⟨h, hpq⟩ := centralSign_split c hc
  have hB : stepOp (signTransitionC c) =
      (⅟2 * (1 + c)) • stepOp (signTransitionC (1 : A)) +
        (⅟2 * (1 - c)) • stepOp (signTransitionC (-1 : A)) := by
    rw [← stepOp_add_smul]
    congr 1
    funext t
    exact signTransitionC_split h.sum hpq t
  have h1 : (1 : Matrix (Fin 16 × Fin 5) (Fin 16 × Fin 5) A) =
      (⅟2 * (1 + c)) • (1 : Matrix (Fin 16 × Fin 5) (Fin 16 × Fin 5) A) + (⅟2 * (1 - c)) • 1 := by
    rw [← add_smul, h.sum, one_smul]
  rw [hB]
  conv_lhs => rw [h1]
  module

theorem law_split [Invertible (2 : A)] (c u : A) (hc : c * c = 1) :
    (1 - u • stepOp (signTransitionC c)).det =
      ⅟2 * (1 + c) * (1 - u • stepOp (signTransitionC (1 : A))).det +
        ⅟2 * (1 - c) * (1 - u • stepOp (signTransitionC (-1 : A))).det := by
  rw [law_matrix_split c u hc, det_split (centralSign_split c hc).1]

/-- **The resolvent splits by the central sign:** `(I − uB_c)⁻¹ = p₊Z₊ + p₋Z₋`. -/
theorem resolvent_split [Invertible (2 : A)] (c u : A) (hc : c * c = 1)
    (Zp Zm : Matrix (Fin 16 × Fin 5) (Fin 16 × Fin 5) A)
    (hp : (1 - u • stepOp (signTransitionC (1 : A))) * Zp = 1)
    (hm : (1 - u • stepOp (signTransitionC (-1 : A))) * Zm = 1) :
    (1 - u • stepOp (signTransitionC c)) * ((⅟2 * (1 + c)) • Zp + (⅟2 * (1 - c)) • Zm) = 1 := by
  have h := (centralSign_split c hc).1
  rw [law_matrix_split c u hc, mul_split h, hp, hm, ← add_smul, h.sum, one_smul]

/-- **`det [[A₀, A₁], [A₁, A₀]] = det(A₀ + A₁) det(A₀ − A₁)`.** -/
theorem det_block_sym (A₀ A₁ : Matrix ι ι A) :
    (fromBlocks A₀ A₁ A₁ A₀).det = (A₀ + A₁).det * (A₀ - A₁).det := by
  have hL : (fromBlocks (1 : Matrix ι ι A) (0 : Matrix ι ι A) (1 : Matrix ι ι A)
      (1 : Matrix ι ι A)).det = 1 := by
    rw [det_fromBlocks_zero₁₂, det_one, one_mul]
  have hR : (fromBlocks (1 : Matrix ι ι A) (0 : Matrix ι ι A) (-1 : Matrix ι ι A)
      (1 : Matrix ι ι A)).det = 1 := by
    rw [det_fromBlocks_zero₁₂, det_one, one_mul]
  have hprod : fromBlocks (1 : Matrix ι ι A) (0 : Matrix ι ι A) (1 : Matrix ι ι A)
      (1 : Matrix ι ι A) * fromBlocks A₀ A₁ A₁ A₀ *
      fromBlocks (1 : Matrix ι ι A) (0 : Matrix ι ι A) (-1 : Matrix ι ι A) (1 : Matrix ι ι A) =
      fromBlocks (A₀ - A₁) A₁ 0 (A₀ + A₁) := by
    rw [fromBlocks_multiply, fromBlocks_multiply]
    congr 1 <;> simp only [Matrix.one_mul, Matrix.zero_mul, Matrix.mul_one, Matrix.mul_zero,
      Matrix.mul_neg, add_zero, zero_add] <;> abel
  have := congrArg Matrix.det hprod
  rw [det_mul, det_mul, hL, hR, one_mul, mul_one, det_fromBlocks_zero₂₁] at this
  rw [this, mul_comm]

end Split

/-! ## Over the complex numbers: the walk and the signed step -/

section Complex

/-- **`B₊ = B[1]`** is the walk of Proposition 26. -/
theorem signTransition_plus (t : Fin 5) : signTransitionC (1 : ℂ) t = transitionMat t := by
  ext k' k
  simp only [signTransitionC, transitionMat, transitionMatZ, Matrix.of_apply, Matrix.map_apply]
  split_ifs <;> simp

/-- **The operator `I − uB_c` on `𝒞⁸⁰` in the basis `(1, c)`** has the matrix
`[[I − uB₀, −uB₁], [−uB₁, I − uB₀]]` with `B₀ = (B₊ + B₋)/2`, `B₁ = (B₊ − B₋)/2`, and its determinant
is `det(I − uB₊) det(I − uB₋)`. -/
theorem law_norm {ι : Type*} [Fintype ι] [DecidableEq ι] (u : ℂ) (Bp Bm : Matrix ι ι ℂ) :
    (fromBlocks (1 - u • ((1 / 2 : ℂ) • (Bp + Bm))) (-(u • ((1 / 2 : ℂ) • (Bp - Bm))))
      (-(u • ((1 / 2 : ℂ) • (Bp - Bm)))) (1 - u • ((1 / 2 : ℂ) • (Bp + Bm)))).det =
      (1 - u • Bp).det * (1 - u • Bm).det := by
  rw [det_block_sym]
  congr 2 <;> module

/-! ## The signed step in the two-spinor state basis is the `B₋` of Proposition 54 -/

theorem transitionSign_pm : ∀ (t : Fin 5) (k : Fin 16), transitionSign t k = 1 ∨ transitionSign t k = -1 := by
  decide

/-- The sixteen two-spinor states as the columns of a `16 × 16` matrix. -/
noncomputable def relMat : Matrix Two (Fin 16) ℂ := Matrix.of fun p k => rel k p

theorem lineOnRel_relMat (t : Fin 5) : lineOnRel t * relMat = relMat * signTransitionC (-1 : ℂ) t := by
  ext p k
  have h := congrFun (line_moves_rel t k) p
  rw [Matrix.mul_apply, Matrix.mul_apply]
  simp only [relMat, signTransitionC, Matrix.of_apply, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (transition t k), ite_eq_left (Finset.mem_univ _)]
  rw [Matrix.mulVec, dotProduct] at h
  simp only [lineOnRel] at h ⊢
  rw [h, Pi.smul_apply, smul_eq_mul, mul_comm]
  congr 1
  rcases transitionSign_pm t k with hs | hs <;> simp [hs]

theorem relMat_unitary : relMatᴴ * relMat = 1 := by
  ext k l
  rw [Matrix.mul_apply, Matrix.one_apply]
  have := rel_inner k l
  simpa [relMat, dotProduct, Matrix.conjTranspose_apply] using this

/-- An equivalence of the sixteen two-spinor states with the sixteen amplitudes of a pair. -/
noncomputable def e16 : Fin 16 ≃ Two := Fintype.equivOfCardEq (by simp)

/-- The two-spinor state matrix, square. -/
noncomputable def relSq : Matrix (Fin 16) (Fin 16) ℂ := relMat.submatrix e16 id

theorem relSq_unitary : relSqᴴ * relSq = 1 := by
  rw [← relMat_unitary]
  ext k l
  simp only [relSq, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id]
  exact Fintype.sum_equiv e16 _ _ (fun _ => rfl)

theorem relSq_unitary' : relSq * relSqᴴ = 1 := mul_eq_one_comm.mp relSq_unitary

/-- An operator on a pair, read on the sixteen two-spinor states through `e16`. -/
noncomputable def onRel (Y : Matrix Two Two ℂ) : Matrix (Fin 16) (Fin 16) ℂ := Y.submatrix e16 e16

theorem onRel_relSq (Y : Matrix Two Two ℂ) : onRel Y * relSq = (Y * relMat).submatrix e16 id := by
  ext i k
  simp only [onRel, relSq, Matrix.mul_apply, Matrix.submatrix_apply, id]
  exact Fintype.sum_equiv e16 _ _ (fun _ => rfl)

theorem signTransition_eq_conj (t : Fin 5) :
    signTransitionC (-1 : ℂ) t = relSqᴴ * onRel (lineOnRel t) * relSq := by
  have h : onRel (lineOnRel t) * relSq = relSq * signTransitionC (-1 : ℂ) t := by
    rw [onRel_relSq, lineOnRel_relMat]
    ext i k
    simp only [relSq, Matrix.mul_apply, Matrix.submatrix_apply, id]
  rw [Matrix.mul_assoc, h, ← Matrix.mul_assoc, relSq_unitary, Matrix.one_mul]

theorem onRel_sum (Y : Fin 5 → Matrix Two Two ℂ) : onRel (∑ t, Y t) = ∑ t, onRel (Y t) := by
  ext i j
  simp [onRel, Matrix.sum_apply]

theorem det_conj_unitary {X Y : Matrix (Fin 16) (Fin 16) ℂ} (hX : X = relSqᴴ * Y * relSq)
    (a u : ℂ) : (a • (1 : Matrix (Fin 16) (Fin 16) ℂ) - u • X).det = (a • 1 - u • Y).det := by
  have e : a • (1 : Matrix (Fin 16) (Fin 16) ℂ) - u • X = relSqᴴ * (a • 1 - u • Y) * relSq := by
    rw [hX, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      relSq_unitary, Matrix.mul_smul, Matrix.smul_mul]
  rw [e, det_mul, det_mul, mul_comm (relSqᴴ.det), mul_assoc, ← det_mul, relSq_unitary, det_one,
    mul_one]

theorem onRel_det (Y : Matrix Two Two ℂ) : (onRel Y).det = Y.det := det_submatrix_equiv_self e16 Y

theorem signTransition_mul_self (t : Fin 5) : signTransitionC (-1 : ℂ) t * signTransitionC (-1 : ℂ) t = 1 := by
  rw [signTransition_eq_conj]
  have h : onRel (lineOnRel t) * onRel (lineOnRel t) = 1 := by
    rw [onRel, Matrix.submatrix_mul_equiv, lineOnRel_mul_self, Matrix.submatrix_one_equiv]
  calc relSqᴴ * onRel (lineOnRel t) * relSq * (relSqᴴ * onRel (lineOnRel t) * relSq)
      = relSqᴴ * onRel (lineOnRel t) * (relSq * relSqᴴ) * onRel (lineOnRel t) * relSq := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [relSq_unitary', Matrix.mul_one, Matrix.mul_assoc relSqᴴ, h, Matrix.mul_one,
          relSq_unitary]

theorem det_one_sub_signTransition (t : Fin 5) (u : ℂ) :
    (1 - u • signTransitionC (-1 : ℂ) t).det = (1 - u ^ 2) ^ 8 := by
  have h := det_conj_unitary (signTransition_eq_conj t) 1 u
  rw [one_smul] at h
  rw [h, ← det_one_sub_lineOnRel t u, ← onRel_det]
  congr 1
  ext i j
  simp [onRel, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply]

theorem det_vertex_signTransition (u : ℂ) :
    ((1 + 4 * u ^ 2) • (1 : Matrix (Fin 16) (Fin 16) ℂ) - u • ∑ t, signTransitionC (-1 : ℂ) t).det =
      (1 + 3 * u ^ 2 + 16 * u ^ 4) ^ 8 := by
  have hsum : ∑ t, signTransitionC (-1 : ℂ) t = relSqᴴ * onRel (∑ t, lineOnRel t) * relSq := by
    rw [onRel_sum, Matrix.mul_sum, Matrix.sum_mul]
    exact Finset.sum_congr rfl fun t _ => signTransition_eq_conj t
  rw [det_conj_unitary hsum, ← det_vertex_minus u, ← onRel_det]
  congr 1
  ext i j
  simp [onRel, Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply]

/-- **In the two-spinor state basis, the signed step `B₋ = B[ν]` has the determinant `D₋`:**
`det(I − uB[ν]) = (1 − u²)²⁴(1 + 3u² + 16u⁴)⁸`. -/
theorem D_minus_rel (u : ℂ) :
    (1 - u • stepOp (signTransitionC (-1 : ℂ))).det = (1 - u ^ 2) ^ 24 * (1 + 3 * u ^ 2 + 16 * u ^ 4) ^ 8 := by
  revert u
  refine extend_from_generic (p := (1 - (Polynomial.X : Polynomial ℂ) •
      (stepOp (signTransitionC (-1 : ℂ))).map Polynomial.C).det)
    (q := (1 - Polynomial.X ^ 2) ^ 24 * (1 + 3 * Polynomial.X ^ 2 + 16 * Polynomial.X ^ 4) ^ 8)
    (det_one_sub_smul_poly _) (fun u => by simp) ?_
  intro u hu
  have h := ihara_bass (signTransitionC (-1 : ℂ)) signTransition_mul_self u
  simp only [det_one_sub_signTransition, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    det_vertex_signTransition] at h
  have hc : (1 - u ^ 2) ≠ 0 := sub_ne_zero.mpr (Ne.symm hu)
  have h56 : (1 - u ^ 2) ^ 56 ≠ 0 := pow_ne_zero _ hc
  apply mul_left_cancel₀ h56
  linear_combination h

end Complex

end Comparison

end
