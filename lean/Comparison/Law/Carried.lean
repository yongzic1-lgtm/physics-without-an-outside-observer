module

public import Comparison.Existence.Coin
public import Comparison.Existence.IharaBass

/-!
# The law, I: the transported matrix and the whole described once (Propositions 108, 130)

The six directions are `Fin 6`, the singlet `n = 0` and the five directions `h, k, c₁, c₂, c₃ = 1, …, 5`.
A divided set is a set `S ⊆ Fin 6`; the exterior algebra of the six has the basis `f_S` (64 sets).

* `minor M T S`: the minor of `M` on the rows `T` and the columns `S`, each read in increasing
  order (zero when `|T| ≠ |S|`); `extPow M`: **the exterior power** `Λ(M)`, the `64 × 64` matrix
  `Λ(M)_{T,S} = det M[T, S]`; `gradePow c`: `c^N`, `f_S ↦ c^{|S|} f_S`.
* `extPow_smul`: **`Λ(cM) = c^N Λ(M)`**; `extPow_one`: `Λ(I) = I`; `extPow_smul_one`:
  **`Λ(cI) = c^N`**, the whole described once.
* `carried K`: **the transported matrix** `Σ₆ = (2/5)𝐉_lines − I`, i.e. `σ ⊕ (−1)` with
  `σ = (2/5)𝐉 − I` the coin on the five directions (`carried_succ_succ`, `carried_zero_zero`,
  `carried_zero_succ`, `carried_succ_zero`).
* `carried_whole`: **`Λ(iΣ₆) = i^N Λ(Σ₆) = Λ(iI) Λ(Σ₆)`** on the 64-dimensional exterior algebra.
* `minor_carried_self`: **the principal minors** `det Σ₆[S, S] = (−1)^{|S|}(1 − 2k/5)`, `k` the
  number of lines in `S`; `minor_coin_self`: `det σ[S, S] = (−1)^k (5 − 2k)/5` for every set `S` of
  the five directions; `minor_coin_relation`: on the sixteen two-spinor states `5 det σ[T_l, T_l] = L(e_l) − 1`.
* `minor_carried_lines`: `det Σ₆[S, S] = (−1)^{[n ∈ S]} det σ[S ∩ lines]`.
-/

@[expose] public section

namespace Comparison

open Matrix

namespace Law

/-! ## Minors and the exterior power -/

section Minors

variable {m : ℕ} {R : Type*} [CommRing R]

/-- The minor of `M` on the rows `T` and the columns `S`, both read in increasing order;
zero when `|T| ≠ |S|`. -/
def minor (M : Matrix (Fin m) (Fin m) R) (T S : Finset (Fin m)) : R :=
  if h : S.card = T.card then
    (M.submatrix (T.orderEmbOfFin rfl) (S.orderEmbOfFin h)).det
  else 0

/-- **The exterior power** `Λ(M)` on the exterior algebra with basis `f_S`:
`Λ(M)_{T,S} = det M[T, S]`. -/
def extPow (M : Matrix (Fin m) (Fin m) R) : Matrix (Finset (Fin m)) (Finset (Fin m)) R :=
  Matrix.of fun T S => minor M T S

/-- The grade raised to a power: `c^N`, the diagonal `f_S ↦ c^{|S|} f_S`. -/
def gradePow (c : R) : Matrix (Finset (Fin m)) (Finset (Fin m)) R :=
  Matrix.diagonal fun S => c ^ S.card

theorem minor_self (M : Matrix (Fin m) (Fin m) R) (S : Finset (Fin m)) :
    minor M S S = (M.submatrix (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl)).det := by
  simp [minor]

theorem minor_smul (c : R) (M : Matrix (Fin m) (Fin m) R) (T S : Finset (Fin m)) :
    minor (c • M) T S = c ^ S.card * minor M T S := by
  unfold minor
  split_ifs with h
  · have hs : (c • M).submatrix (T.orderEmbOfFin rfl) (S.orderEmbOfFin h) =
        c • M.submatrix (T.orderEmbOfFin rfl) (S.orderEmbOfFin h) := rfl
    rw [hs, det_smul, Fintype.card_fin, h]
  · rw [mul_zero]

theorem minor_eq_zero_of_card (M : Matrix (Fin m) (Fin m) R) {T S : Finset (Fin m)}
    (h : S.card ≠ T.card) : minor M T S = 0 := by
  simp [minor, h]

/-- **`Λ(cM) = c^N Λ(M)`.** -/
theorem extPow_smul (c : R) (M : Matrix (Fin m) (Fin m) R) :
    extPow (c • M) = gradePow c * extPow M := by
  ext T S
  rw [gradePow, Matrix.diagonal_mul]
  simp only [extPow, Matrix.of_apply]
  rw [minor_smul]
  by_cases h : S.card = T.card
  · rw [h]
  · rw [minor_eq_zero_of_card M h, mul_zero, mul_zero]

/-- `Λ(cM) = Λ(M) c^N` as well. -/
theorem extPow_smul' (c : R) (M : Matrix (Fin m) (Fin m) R) :
    extPow (c • M) = extPow M * gradePow c := by
  ext T S
  rw [gradePow, Matrix.mul_diagonal]
  simp only [extPow, Matrix.of_apply]
  rw [minor_smul, mul_comm]

/-- `Λ(I) = I`: the minors of the identity. -/
theorem extPow_one : extPow (1 : Matrix (Fin m) (Fin m) R) = 1 := by
  ext T S
  simp only [extPow, Matrix.of_apply, Matrix.one_apply]
  by_cases hTS : T = S
  · subst hTS
    simp only [↓reduceIte]
    rw [minor_self, submatrix_one _ (T.orderEmbOfFin rfl).injective, det_one]
  · simp only [hTS, ↓reduceIte]
    unfold minor
    split_ifs with h
    · -- some element of `T` is not in `S`
      have hsub : ¬ T ⊆ S := by
        intro hT
        exact hTS (Finset.eq_of_subset_of_card_le hT h.le)
      obtain ⟨x, hxT, hxS⟩ := Finset.not_subset.mp hsub
      have hx : x ∈ Set.range (T.orderEmbOfFin rfl) := by
        rw [Finset.range_orderEmbOfFin]
        exact hxT
      obtain ⟨i, hi⟩ := hx
      apply det_eq_zero_of_row_eq_zero i
      intro j
      simp only [Matrix.submatrix_apply, Matrix.one_apply]
      refine ite_eq_right_iff.mpr fun hij => absurd ?_ hxS
      rw [← hi, hij]
      exact Finset.orderEmbOfFin_mem S h j
    · rfl

/-- **`Λ(cI) = c^N`:** the whole described once. -/
theorem extPow_smul_one (c : R) : extPow (c • (1 : Matrix (Fin m) (Fin m) R)) = gradePow c := by
  rw [extPow_smul, extPow_one, Matrix.mul_one]

/-- The sum over `Fin |S|` read through the increasing enumeration of `S` is the sum over `S`. -/
theorem sum_orderEmbOfFin {M : Type*} [AddCommMonoid M] (S : Finset (Fin m)) (f : Fin m → M) :
    ∑ i : Fin S.card, f (S.orderEmbOfFin rfl i) = ∑ x ∈ S, f x := by
  rw [← Finset.sum_coe_sort S f]
  exact Fintype.sum_equiv (S.orderIsoOfFin rfl).toEquiv _ _ (fun i => rfl)

/-- **The principal minor of `−1 + c·vvᵀ`:** `det(−1 + c v vᵀ)[S, S] = (−1)^{|S|}(1 − c Σ_{x∈S} v_x²)`. -/
theorem minor_rankOne_self {K : Type*} [Field K] (c : K) (v : Fin m → K) (S : Finset (Fin m)) :
    minor (c • vecMulVec v v - 1) S S = (-1) ^ S.card * (1 - c * ∑ x ∈ S, v x * v x) := by
  rw [minor_self]
  set e := S.orderEmbOfFin rfl with he
  have hsub : (c • vecMulVec v v - 1 : Matrix (Fin m) (Fin m) K).submatrix e e =
      -(1 + replicateCol Unit (-(c • (v ∘ e))) * replicateRow Unit (v ∘ e)) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply,
      Matrix.one_apply, Matrix.neg_apply, Matrix.add_apply, Matrix.mul_apply, Fintype.sum_unique,
      replicateCol_apply, replicateRow_apply, Function.comp_apply,
      Pi.neg_apply, Pi.smul_apply, smul_eq_mul, e.injective.eq_iff]
    split_ifs <;> ring
  rw [hsub, det_neg, det_one_add_replicateCol_mul_replicateRow, Fintype.card_fin]
  congr 1
  rw [dotProduct]
  simp only [Pi.neg_apply, Pi.smul_apply, Function.comp_apply, smul_eq_mul]
  rw [show (∑ i : Fin S.card, v (e i) * -(c * v (e i))) =
      -(c * ∑ i : Fin S.card, v (e i) * v (e i)) by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring]
  rw [he, sum_orderEmbOfFin S (fun x => v x * v x)]
  ring

end Minors

/-! ## The transported matrix -/

section Carried

variable (K : Type*) [Field K]

/-- The line indicator of the six: `0` at the singlet, `1` at each of the five directions. -/
def lineInd : Fin 6 → K := fun x => if x = 0 then 0 else 1

/-- **The transported matrix** `Σ₆ = (2/5)𝐉_lines − I`: the coin `σ = (2/5)𝐉 − I` on the five directions and
`−1` on the singlet, `Σ₆ = σ ⊕ (−1)`. -/
def carried : Matrix (Fin 6) (Fin 6) K := (2 / 5 : K) • vecMulVec (lineInd K) (lineInd K) - 1

/-- The number of lines in a divided set. -/
def linesIn (S : Finset (Fin 6)) : ℕ := (S.filter (· ≠ 0)).card

theorem carried_apply (i j : Fin 6) :
    carried K i j = (if i = 0 ∨ j = 0 then 0 else 2 / 5) - if i = j then 1 else 0 := by
  simp only [carried, lineInd, Matrix.sub_apply, Matrix.smul_apply, vecMulVec_apply,
    Matrix.one_apply, smul_eq_mul]
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp [hi, hj]

theorem carried_zero_zero : carried K 0 0 = -1 := by
  rw [carried_apply]
  simp

theorem carried_zero_succ (j : Fin 5) : carried K 0 j.succ = 0 := by
  rw [carried_apply]
  simp [(Fin.succ_ne_zero j).symm]

theorem carried_succ_zero (i : Fin 5) : carried K i.succ 0 = 0 := by
  rw [carried_apply]
  simp [Fin.succ_ne_zero i]

/-- On the five directions the transported matrix is the coin `σ`. -/
theorem carried_succ_succ (i j : Fin 5) : carried ℚ i.succ j.succ = coin i j := by
  rw [carried_apply, coin_apply]
  simp only [Fin.succ_ne_zero, or_self, ↓reduceIte, Fin.succ_inj]
  split_ifs <;> norm_num

/-- **The principal minors of the transported matrix:** `det Σ₆[S, S] = (−1)^{|S|} (1 − (2/5) k)`,
`k` the number of lines in `S`. -/
theorem minor_carried_self [CharZero K] (S : Finset (Fin 6)) :
    minor (carried K) S S = (-1) ^ S.card * (1 - 2 / 5 * (linesIn S : K)) := by
  rw [carried, minor_rankOne_self]
  congr 3
  rw [linesIn, Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x = 0 <;> simp [lineInd, hx]

/-- `5 det Σ₆[S, S] = P_S (5 − 2k)` with `P_S = (−1)^{|S|}`. -/
theorem five_minor_carried [CharZero K] (S : Finset (Fin 6)) :
    5 * minor (carried K) S S = (-1) ^ S.card * (5 - 2 * (linesIn S : K)) := by
  rw [minor_carried_self]
  ring

end Carried

/-- **The principal minors of the coin:** `det σ[S, S] = (−1)^k (5 − 2k)/5`, `k = |S|`, for every
set `S` of the five directions. -/
theorem minor_coin_self (S : Finset (Fin 5)) :
    minor coin S S = (-1) ^ S.card * (5 - 2 * (S.card : ℚ)) / 5 := by
  have hc : coin = (2 / 5 : ℚ) • vecMulVec (fun _ : Fin 5 => (1 : ℚ)) (fun _ => 1) - 1 := by
    ext i j
    simp [coin, ones5, vecMulVec_apply]
  rw [hc, minor_rankOne_self]
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul]
  ring

/-- On the sixteen two-spinor states, `T_l` the lines on which the two systems disagree,
**`5 det σ[T_l, T_l] = L(e_l) − 1`**: the minor is `(L − 1)/5`. -/
theorem minor_coin_relation (l : Fin 16) :
    5 * minor coin (disagreeSet l) (disagreeSet l) = (Lvalue l : ℚ) - 1 := by
  have heven : ∀ l : Fin 16, Even (disagreeSet l).card := by decide
  rw [minor_coin_self, (heven l).neg_one_pow, Lvalue]
  push_cast
  ring

/-- The lines of a divided set, as a set of the five directions. -/
def linesOf (S : Finset (Fin 6)) : Finset (Fin 5) := Finset.univ.filter fun t => t.succ ∈ S

theorem card_linesOf (S : Finset (Fin 6)) : (linesOf S).card = linesIn S := by
  revert S
  decide

/-- **The minor of `Σ₆` is the coin's on the lines, with the singlet's sign:**
`det Σ₆[S, S] = (−1)^{[n ∈ S]} det σ[S ∩ lines]`. -/
theorem minor_carried_lines (S : Finset (Fin 6)) :
    minor (carried ℚ) S S =
      (if (0 : Fin 6) ∈ S then -1 else 1) * minor coin (linesOf S) (linesOf S) := by
  rw [minor_carried_self, minor_coin_self, card_linesOf]
  have hcard : S.card = linesIn S + if (0 : Fin 6) ∈ S then 1 else 0 := by
    revert S
    decide
  rw [hcard]
  split_ifs <;> ring

/-! ## The whole described once -/

/-- The transported matrix over `ℂ`. -/
noncomputable abbrev carriedC : Matrix (Fin 6) (Fin 6) ℂ := carried ℂ

/-- **`Λ(iΣ₆) = i^N Λ(Σ₆) = Λ(iI) Λ(Σ₆)`** on the 64-dimensional exterior algebra of the six. -/
theorem carried_whole :
    extPow (Complex.I • carriedC) = gradePow Complex.I * extPow carriedC ∧
      extPow (Complex.I • carriedC) = extPow (Complex.I • (1 : Matrix (Fin 6) (Fin 6) ℂ)) *
        extPow carriedC := by
  refine ⟨extPow_smul _ _, ?_⟩
  rw [extPow_smul_one, extPow_smul]

/-- The diagonal of `Λ(iΣ₆)`: `i^{|S|} det Σ₆[S, S]`. -/
theorem carried_whole_diag (S : Finset (Fin 6)) :
    extPow (Complex.I • carriedC) S S =
      Complex.I ^ S.card * ((-1) ^ S.card * (1 - 2 / 5 * (linesIn S : ℂ))) := by
  rw [extPow_smul]
  simp only [gradePow, Matrix.diagonal_mul, extPow, Matrix.of_apply]
  rw [minor_carried_self]

/-- The exterior algebra of the six has `64` basis sets. -/
theorem card_dividedSets : Fintype.card (Finset (Fin 6)) = 64 := by
  rw [Fintype.card_finset, Fintype.card_fin]
  norm_num

end Law

end Comparison

end
