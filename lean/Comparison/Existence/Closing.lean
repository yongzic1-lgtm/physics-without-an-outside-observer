module

public import Mathlib

/-!
# Book X. Closing a level: the reduced operator, its sources and its pole (Proposition 57)

Over any field `𝕜`, for the block
operator `K = [[A, B], [C, D]]` with `D` invertible:

* `schurS K = S = A − BD⁻¹C`, `schurL = L = (1, −BD⁻¹)`, `schurR = R = (1; −D⁻¹C)`,
  `schurQ = Q = [[0, 0], [0, D⁻¹]]`.
* `schur_det`: **`det K = det D · det S`**; `schur_LK`, `schur_KR`, `schur_LKR`: `LK = (S, 0)`,
  `KR = (S; 0)`, `LKR = S`.
* `schur_inv`: **`K⁻¹ = R S⁻¹ L + Q`** (`S` invertible).
* The sources, as exact differences between two operators `K` and `K'` (`D'` invertible):
  `schur_diff`: **`S' − S = L (K' − K) R'`**; `schurR_diff`: `R' − R = −Q (K' − K) R'`;
  `schurL_diff`: `L' − L = −L (K' − K) Q'`. With `K' = K + tK_a` these are `S_a = LK_aR`,
  `R_a = −QK_aR`, `L_a = −LK_aQ`, and the product rule gives `S_ab = L(K_ab − K_aQK_b − K_bQK_a)R`.
* `residue_simple_zero`: at a simple zero, from the first Laurent coefficients of `S(ζ)S(ζ)⁻¹ = 1`
  (`S₀M = 0`, `MS₀ = 0`, `S₀N + S_ζM = 1`) and one-dimensional kernels spanned by `r` and `ℓ`:
  **`ℓ S_ζ r ≠ 0` and `M = r ℓ / (ℓ S_ζ r)`**.
* `zero_shift`: if `(S₀ + ζ S_ζ + J S_a) v = 0` then `ζ (ℓ S_ζ v) = −J (ℓ S_a v)`: as `v → r`,
  **`dζ₀/dJ_a = −ℓS_ar/(ℓS_ζr)`**.
-/

@[expose] public section

namespace Comparison

open Matrix

section Schur

variable {𝕜 : Type*} [Field 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
  [DecidableEq n]

/-- The reduced operator `S = A − BD⁻¹C`. -/
def schurS (A : Matrix m m 𝕜) (B : Matrix m n 𝕜) (C : Matrix n m 𝕜) (D : Matrix n n 𝕜)
    [Invertible D] : Matrix m m 𝕜 :=
  A - B * ⅟D * C

/-- `L = (1, −BD⁻¹)`. -/
def schurL (B : Matrix m n 𝕜) (D : Matrix n n 𝕜) [Invertible D] : Matrix m (m ⊕ n) 𝕜 :=
  fromCols 1 (-(B * ⅟D))

/-- `R = (1; −D⁻¹C)`. -/
def schurR (C : Matrix n m 𝕜) (D : Matrix n n 𝕜) [Invertible D] : Matrix (m ⊕ n) m 𝕜 :=
  fromRows 1 (-(⅟D * C))

/-- `Q = [[0, 0], [0, D⁻¹]]`. -/
def schurQ (D : Matrix n n 𝕜) [Invertible D] : Matrix (m ⊕ n) (m ⊕ n) 𝕜 :=
  fromBlocks 0 0 0 ⅟D

variable (A : Matrix m m 𝕜) (B : Matrix m n 𝕜) (C : Matrix n m 𝕜) (D : Matrix n n 𝕜) [Invertible D]

/-- **`det K = det D · det S`.** -/
theorem schur_det : (fromBlocks A B C D).det = D.det * (schurS A B C D).det :=
  det_fromBlocks₂₂ A B C D

/-- `LK = (S, 0)`. -/
theorem schur_LK : schurL B D * fromBlocks A B C D = fromCols (schurS A B C D) 0 := by
  rw [schurL, fromCols_mul_fromBlocks, schurS]
  congr 1
  · rw [Matrix.one_mul, Matrix.neg_mul, ← sub_eq_add_neg, Matrix.mul_assoc]
  · rw [Matrix.one_mul, Matrix.neg_mul, Matrix.mul_assoc, invOf_mul_self, Matrix.mul_one,
      add_neg_cancel]

/-- `KR = (S; 0)`. -/
theorem schur_KR : fromBlocks A B C D * schurR C D = fromRows (schurS A B C D) 0 := by
  rw [schurR, fromBlocks_mul_fromRows, schurS]
  congr 1
  · rw [Matrix.mul_one, Matrix.mul_neg, ← sub_eq_add_neg, Matrix.mul_assoc]
  · rw [Matrix.mul_one, Matrix.mul_neg, ← Matrix.mul_assoc, mul_invOf_self, Matrix.one_mul,
      add_neg_cancel]

/-- `LKR = S`. -/
theorem schur_LKR : schurL B D * fromBlocks A B C D * schurR C D = schurS A B C D := by
  rw [schur_LK, schurR, fromCols_mul_fromRows, Matrix.mul_one, Matrix.zero_mul, add_zero]

/-- **`K⁻¹ = R S⁻¹ L + Q`.** -/
theorem schur_inv [Invertible (schurS A B C D)] :
    (fromBlocks A B C D)⁻¹ = schurR C D * ⅟(schurS A B C D) * schurL B D + schurQ D := by
  apply Matrix.inv_eq_right_inv
  have h1 : fromBlocks A B C D * (schurR C D * ⅟(schurS A B C D) * schurL B D) =
      fromBlocks 1 (-(B * ⅟D)) 0 0 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, schur_KR, fromRows_mul, mul_invOf_self,
      Matrix.zero_mul, schurL, fromRows_mul_fromCols]
    simp
  have h2 : fromBlocks A B C D * schurQ D = fromBlocks 0 (B * ⅟D) 0 1 := by
    rw [schurQ, fromBlocks_multiply]
    simp [mul_invOf_self]
  rw [Matrix.mul_add, h1, h2, fromBlocks_add, ← fromBlocks_one]
  simp

variable {A B C D}

/-- **The sources, exactly:** `S' − S = L (K' − K) R'`. With `K' = K + tK_a`: `S_a = L K_a R`. -/
theorem schur_diff (A' : Matrix m m 𝕜) (B' : Matrix m n 𝕜) (C' : Matrix n m 𝕜) (D' : Matrix n n 𝕜)
    [Invertible D'] :
    schurS A' B' C' D' - schurS A B C D =
      schurL B D * (fromBlocks A' B' C' D' - fromBlocks A B C D) * schurR C' D' := by
  rw [Matrix.mul_sub, Matrix.sub_mul, schur_LK, Matrix.mul_assoc, schur_KR, schurL, schurR,
    fromCols_mul_fromRows, fromCols_mul_fromRows]
  simp

theorem fromRows_sub' {p q : Type*} (A₁ B₁ : Matrix m p 𝕜) (A₂ B₂ : Matrix q p 𝕜) :
    fromRows A₁ A₂ - fromRows B₁ B₂ = fromRows (A₁ - B₁) (A₂ - B₂) := by
  ext (i | i) j <;> simp

theorem fromCols_sub' {p q : Type*} (A₁ B₁ : Matrix m p 𝕜) (A₂ B₂ : Matrix m q 𝕜) :
    fromCols A₁ A₂ - fromCols B₁ B₂ = fromCols (A₁ - B₁) (A₂ - B₂) := by
  ext i (j | j) <;> simp

/-- `R' − R = −Q (K' − K) R'`: with `K' = K + tK_a`, `R_a = −Q K_a R`. -/
theorem schurR_diff (A' : Matrix m m 𝕜) (B' : Matrix m n 𝕜) (C' : Matrix n m 𝕜)
    (D' : Matrix n n 𝕜) [Invertible D'] :
    schurR C' D' - schurR C D =
      -(schurQ D * (fromBlocks A' B' C' D' - fromBlocks A B C D) * schurR C' D') := by
  have e1 : schurR C' D' - schurR C D = fromRows (0 : Matrix m m 𝕜) (⅟D * C - ⅟D' * C') := by
    rw [schurR, schurR, fromRows_sub', sub_self]
    congr 1
    abel
  have e2 : schurQ D * fromBlocks A' B' C' D' * schurR C' D' = 0 := by
    rw [Matrix.mul_assoc, schur_KR, schurQ, fromBlocks_mul_fromRows]
    simp
  have e3 : schurQ D * fromBlocks A B C D * schurR C' D' =
      fromRows (0 : Matrix m m 𝕜) (⅟D * C - ⅟D' * C') := by
    rw [Matrix.mul_assoc, schurR, fromBlocks_mul_fromRows, schurQ, fromBlocks_mul_fromRows]
    simp only [Matrix.zero_mul, add_zero, Matrix.mul_one, Matrix.mul_neg, Matrix.mul_add,
      ← Matrix.mul_assoc, invOf_mul_self, Matrix.one_mul, zero_add, neg_zero]
    simp [sub_eq_add_neg]
  rw [e1, Matrix.mul_sub, Matrix.sub_mul, e2, e3, zero_sub, neg_neg]

/-- `L' − L = −L (K' − K) Q'`: with `K' = K + tK_a`, `L_a = −L K_a Q`. -/
theorem schurL_diff (A' : Matrix m m 𝕜) (B' : Matrix m n 𝕜) (C' : Matrix n m 𝕜)
    (D' : Matrix n n 𝕜) [Invertible D'] :
    schurL B' D' - schurL B D =
      -(schurL B D * (fromBlocks A' B' C' D' - fromBlocks A B C D) * schurQ D') := by
  have e1 : schurL B' D' - schurL B D = fromCols (0 : Matrix m m 𝕜) (B * ⅟D - B' * ⅟D') := by
    rw [schurL, schurL, fromCols_sub', sub_self]
    congr 1
    abel
  have e2 : schurL B D * (fromBlocks A B C D * schurQ D') = 0 := by
    rw [← Matrix.mul_assoc (schurL B D) (fromBlocks A B C D) (schurQ D'), schur_LK, schurQ,
      fromCols_mul_fromBlocks]
    simp
  have e3 : schurL B D * (fromBlocks A' B' C' D' * schurQ D') =
      fromCols (0 : Matrix m m 𝕜) (B' * ⅟D' - B * ⅟D) := by
    rw [schurQ, fromBlocks_multiply, schurL, fromCols_mul_fromBlocks]
    simp only [Matrix.mul_zero, add_zero, Matrix.one_mul, Matrix.mul_one, mul_invOf_self,
      Matrix.zero_mul, zero_add, Matrix.neg_mul]
    rw [sub_eq_add_neg]
  have hexp : schurL B D * (fromBlocks A' B' C' D' - fromBlocks A B C D) * schurQ D' =
      schurL B D * (fromBlocks A' B' C' D' * schurQ D') -
        schurL B D * (fromBlocks A B C D * schurQ D') := by
    calc schurL B D * (fromBlocks A' B' C' D' - fromBlocks A B C D) * schurQ D'
        = schurL B D * ((fromBlocks A' B' C' D' - fromBlocks A B C D) * schurQ D') :=
          Matrix.mul_assoc _ _ _
      _ = schurL B D * (fromBlocks A' B' C' D' * schurQ D' - fromBlocks A B C D * schurQ D') := by
          rw [sub_mul]
      _ = schurL B D * (fromBlocks A' B' C' D' * schurQ D') -
            schurL B D * (fromBlocks A B C D * schurQ D') := Matrix.mul_sub _ _ _
  rw [e1, hexp, e2, e3, sub_zero, fromCols_neg, neg_zero, neg_sub]

end Schur

/-! ## At a simple zero -/

section Pole

variable {𝕜 : Type*} [Field 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **The residue at a simple zero:** if `S(ζ)⁻¹ = M/(ζ − ζ₀) + N + ⋯` with `S(ζ) = S₀ + (ζ − ζ₀)S_ζ + ⋯`,
so that `S₀M = 0`, `MS₀ = 0` and `S₀N + S_ζM = 1`, and the kernels of `S₀` on both sides are spanned by
`r` and `ℓ`, then `ℓ S_ζ r ≠ 0` and `M = r ℓ/(ℓ S_ζ r)`. -/
theorem residue_simple_zero (S₀ Sζ M N : Matrix n n 𝕜) (r ℓ : n → 𝕜) (hr : r ≠ 0) (hℓ : ℓ ≠ 0)
    (hkerR : ∀ v, S₀ *ᵥ v = 0 → ∃ c : 𝕜, v = c • r)
    (hkerL : ∀ w, w ᵥ* S₀ = 0 → ∃ c : 𝕜, w = c • ℓ)
    (hℓS : ℓ ᵥ* S₀ = 0)
    (h1 : S₀ * M = 0) (h2 : M * S₀ = 0) (h3 : S₀ * N + Sζ * M = 1) :
    ℓ ⬝ᵥ (Sζ *ᵥ r) ≠ 0 ∧ M = (ℓ ⬝ᵥ (Sζ *ᵥ r))⁻¹ • vecMulVec r ℓ := by
  -- every column of `M` is a multiple of `r`
  have hcol : ∀ j, ∃ c : 𝕜, (fun i => M i j) = c • r := by
    intro j
    apply hkerR
    funext i
    have := congrFun (congrFun h1 i) j
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
  choose c hc using hcol
  -- so `M = r ⊗ c`, and `c S₀ = 0`
  have hM : M = vecMulVec r c := by
    ext i j
    have := congrFun (hc j) i
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [vecMulVec_apply, this, mul_comm]
  obtain ⟨i₀, hi₀⟩ : ∃ i, r i ≠ 0 := by
    by_contra h
    push Not at h
    exact hr (funext h)
  have hcS : c ᵥ* S₀ = 0 := by
    have := congrArg (fun X => X i₀) h2
    simp only [hM] at this
    funext j
    have hj := congrFun this j
    simp only [Matrix.mul_apply, vecMulVec_apply, Pi.zero_apply, Matrix.zero_apply] at hj
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
    have : r i₀ * ∑ x, c x * S₀ x j = 0 := by
      rw [Finset.mul_sum]
      simpa [mul_assoc] using hj
    exact (mul_eq_zero.mp this).resolve_left hi₀
  obtain ⟨d, hd⟩ := hkerL c hcS
  -- `ℓ (S₀N + S_ζM) = ℓ` fixes `d`
  have hkey : ℓ ᵥ* (S₀ * N + Sζ * M) = ℓ := by rw [h3, vecMul_one]
  rw [vecMul_add, ← vecMul_vecMul, hℓS, zero_vecMul, zero_add, hM, hd] at hkey
  have hform : ℓ ᵥ* (Sζ * vecMulVec r (d • ℓ)) = (d * (ℓ ⬝ᵥ (Sζ *ᵥ r))) • ℓ := by
    funext j
    simp only [Matrix.vecMul, dotProduct, Matrix.mul_apply, vecMulVec_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.mulVec, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  rw [hform] at hkey
  obtain ⟨j₀, hj₀⟩ : ∃ j, ℓ j ≠ 0 := by
    by_contra h
    push Not at h
    exact hℓ (funext h)
  have hd1 : d * (ℓ ⬝ᵥ (Sζ *ᵥ r)) = 1 := by
    have := congrFun hkey j₀
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have h' : (d * (ℓ ⬝ᵥ (Sζ *ᵥ r)) - 1) * ℓ j₀ = 0 := by rw [sub_mul, this, one_mul, sub_self]
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hj₀)
  have hne : ℓ ⬝ᵥ (Sζ *ᵥ r) ≠ 0 := right_ne_zero_of_mul_eq_one hd1
  refine ⟨hne, ?_⟩
  rw [hM, hd]
  have hdinv : d = (ℓ ⬝ᵥ (Sζ *ᵥ r))⁻¹ := eq_inv_of_mul_eq_one_left hd1
  ext i j
  simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply, hdinv]
  ring

/-- **The shift of the zero with a source:** if `(S₀ + ζS_ζ + JS_a)v = 0` and `ℓS₀ = 0`, then
`ζ (ℓ S_ζ v) = −J (ℓ S_a v)`; at `v = r`, `dζ₀/dJ_a = −ℓS_ar/(ℓS_ζr)`. -/
theorem zero_shift (S₀ Sζ Sa : Matrix n n 𝕜) (ℓ v : n → 𝕜) (ζ J : 𝕜) (hℓS : ℓ ᵥ* S₀ = 0)
    (hv : (S₀ + ζ • Sζ + J • Sa) *ᵥ v = 0) :
    ζ * (ℓ ⬝ᵥ (Sζ *ᵥ v)) = -(J * (ℓ ⬝ᵥ (Sa *ᵥ v))) := by
  have h := congrArg (fun w => ℓ ⬝ᵥ w) hv
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul,
    dotProduct_zero] at h
  rw [dotProduct_mulVec, hℓS, zero_dotProduct, zero_add] at h
  linear_combination h

end Pole

end Comparison

end
