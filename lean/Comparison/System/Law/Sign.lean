import Comparison.System.Postulates
import Comparison.Existence.Sign

/-!
# The proof system, the law: Proposition 53, count and sign

On the two-spinor states each step carries a sign, `(γ_s ⊗ 1)e_S = ν(S, s) e_{S △ T_s}`, `ν = ±1`; `B₊ = B[1]`,
`B₋ = B[ν]`; with `𝒞 = ℂ[c]/(c² − 1)` and `p± = (1 ± c)/2`, `det_𝒞(I − uB_c)⁻¹ = p₊Z₊ + p₋Z₋`, `B_c` the step
with `c` in place of `−1`. Here:

* `inv_split`: in any commutative ring with `2` invertible and `c² = 1`, if `D₊Z₊ = 1` and `D₋Z₋ = 1` then
  `(p₊D₊ + p₋D₋)(p₊Z₊ + p₋Z₋) = 1`: the inverse of the split determinant is the split of the inverses;
* `Csign`, `csign_sq`: the ring `𝒞 = ℂ[c]/(c² − 1)` (`AdjoinRoot`) with its root `c`, `c² = 1`, and `2`
  invertible in it;
* `prop_53`: Proposition 53 as one statement, in every such ring, and in `𝒞`.
-/

open Matrix Comparison Polynomial
open scoped Kronecker

namespace Comparison.System

namespace Law

/-- **The inverse splits as the determinant does:** with `p± = (1 ± c)/2`, `c² = 1`, `D₊Z₊ = D₋Z₋ = 1`,
`(p₊D₊ + p₋D₋)(p₊Z₊ + p₋Z₋) = 1`. -/
theorem inv_split {A : Type*} [CommRing A] [Invertible (2 : A)] (c : A) (hc : c * c = 1)
    (Dp Dm Zp Zm : A) (hp : Dp * Zp = 1) (hm : Dm * Zm = 1) :
    (⅟2 * (1 + c) * Dp + ⅟2 * (1 - c) * Dm) * (⅟2 * (1 + c) * Zp + ⅟2 * (1 - c) * Zm) = 1 := by
  obtain ⟨h, -⟩ := centralSign_split c hc
  have e : (⅟2 * (1 + c) * Dp + ⅟2 * (1 - c) * Dm) * (⅟2 * (1 + c) * Zp + ⅟2 * (1 - c) * Zm) =
      (⅟2 * (1 + c)) * (⅟2 * (1 + c)) * (Dp * Zp) + (⅟2 * (1 - c)) * (⅟2 * (1 - c)) * (Dm * Zm) +
        (⅟2 * (1 + c)) * (⅟2 * (1 - c)) * (Dp * Zm + Dm * Zp) := by ring
  rw [e, hp, hm, h.pp, h.qq, h.pq, zero_mul, add_zero, mul_one, mul_one, h.sum]

/-- **The ring of the central sign**, `𝒞 = ℂ[c]/(c² − 1)`. -/
abbrev Csign : Type := AdjoinRoot (X ^ 2 - 1 : ℂ[X])

/-- Its root `c`. -/
noncomputable abbrev csign : Csign := AdjoinRoot.root (X ^ 2 - 1 : ℂ[X])

/-- **`c² = 1`** in `𝒞`. -/
theorem csign_sq : csign * csign = 1 := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 - 1 : ℂ[X])
  simp only [eval₂_sub, eval₂_X_pow, eval₂_one] at h
  linear_combination h

/-- `2` is invertible in `𝒞`. -/
noncomputable instance : Invertible (2 : Csign) where
  invOf := algebraMap ℂ Csign (1 / 2)
  invOf_mul_self := by
    rw [show (2 : Csign) = algebraMap ℂ Csign 2 from (map_ofNat _ 2).symm, ← map_mul]
    norm_num
  mul_invOf_self := by
    rw [show (2 : Csign) = algebraMap ℂ Csign 2 from (map_ofNat _ 2).symm, ← map_mul]
    norm_num

end Law

open Comparison.System.Law

/-- **Proposition 53, count and sign.** Each step carries a sign on the two-spinor states,
`(γ_s ⊗ 1)e_S = ν(S, s) e_{S △ T_s}` with `ν = ±1`; `B₊ = B[1]` is the walk; `B₋ = B[ν]` carries the sign
(and is the step `γ_t ⊗ 1` on the amplitudes, read in the two-spinor states); and in every commutative ring with `2`
invertible and a central sign `c`, `c² = 1`, with `p± = (1 ± c)/2`: `det(I − uB_c) = p₊ det(I − uB₊) +
p₋ det(I − uB₋)`, and its inverse is `p₊Z₊ + p₋Z₋` whenever `Z± = det(I − uB±)⁻¹`; in particular in
`𝒞 = ℂ[c]/(c² − 1)`. -/
theorem prop_53 :
    (∀ (s : Fin 5) (k : Fin 16),
      (γ s ⊗ₖ (1 : Matrix Four Four ℂ)) *ᵥ rel k = (transitionSign s k : ℂ) • rel (transition s k) ∧
        (transitionSign s k = 1 ∨ transitionSign s k = -1) ∧
        disagreeSet (transition s k) = symmDiff (disagreeSet k) (Finset.univ.erase s)) ∧
    (∀ t, signTransitionC (1 : ℂ) t = transitionMat t) ∧
    (∀ t k' k, signTransitionC (-1 : ℂ) t k' k = if k' = transition t k then (transitionSign t k : ℂ) else 0) ∧
    (∀ t, signTransitionC (-1 : ℂ) t = relSqᴴ * onRel (lineOnRel t) * relSq) ∧
    (∀ (A : Type) [CommRing A] [Invertible (2 : A)] (c u : A), c * c = 1 →
      (1 - u • stepOp (signTransitionC c)).det =
          ⅟2 * (1 + c) * (1 - u • stepOp (signTransitionC (1 : A))).det +
            ⅟2 * (1 - c) * (1 - u • stepOp (signTransitionC (-1 : A))).det ∧
        ∀ Zp Zm : A, (1 - u • stepOp (signTransitionC (1 : A))).det * Zp = 1 →
          (1 - u • stepOp (signTransitionC (-1 : A))).det * Zm = 1 →
          (1 - u • stepOp (signTransitionC c)).det * (⅟2 * (1 + c) * Zp + ⅟2 * (1 - c) * Zm) = 1) ∧
    csign * csign = 1 ∧
    (∀ u : Csign, (1 - u • stepOp (signTransitionC csign)).det =
      ⅟2 * (1 + csign) * (1 - u • stepOp (signTransitionC (1 : Csign))).det +
        ⅟2 * (1 - csign) * (1 - u • stepOp (signTransitionC (-1 : Csign))).det) := by
  have hsplit : ∀ (A : Type) [CommRing A] [Invertible (2 : A)] (c u : A), c * c = 1 →
      (1 - u • stepOp (signTransitionC c)).det =
          ⅟2 * (1 + c) * (1 - u • stepOp (signTransitionC (1 : A))).det +
            ⅟2 * (1 - c) * (1 - u • stepOp (signTransitionC (-1 : A))).det ∧
        ∀ Zp Zm : A, (1 - u • stepOp (signTransitionC (1 : A))).det * Zp = 1 →
          (1 - u • stepOp (signTransitionC (-1 : A))).det * Zm = 1 →
          (1 - u • stepOp (signTransitionC c)).det * (⅟2 * (1 + c) * Zp + ⅟2 * (1 - c) * Zm) = 1 := by
    intro A _ _ c u hc
    refine ⟨law_split c u hc, fun Zp Zm hp hm => ?_⟩
    rw [law_split c u hc]
    exact inv_split c hc _ _ Zp Zm hp hm
  refine ⟨fun s k => ⟨line_moves_rel s k, transitionSign_pm s k, disagreeSet_transition s k⟩, signTransition_plus,
    fun t k' k => ?_, signTransition_eq_conj, hsplit, csign_sq,
    fun u => (hsplit Csign csign u csign_sq).1⟩
  simp only [signTransitionC, Matrix.of_apply]
  split_ifs with h1 h2 <;> try rfl
  · rw [h2]; norm_num
  · rcases transitionSign_pm t k with h | h
    · exact absurd h h2
    · rw [h]; norm_num
end Comparison.System
