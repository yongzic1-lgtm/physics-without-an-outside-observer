import Comparison.Existence.Holds
import Comparison.Law.Rule

/-!
# Where each piece sits (Proposition 43)

A piece of a number of the law sits on the division its comparison holds. The two-spinor state `k` (the singlet, a vector
state `ℓ_t`, a plane `e_{ab}`) acts on P1's real six by `B_k f_c B_kᵀ = ±f_c`: it reverses exactly the
directions of `heldDiv k`, the lines on which it disagrees (`relOp_on_six`). Its divided set is the shorter description
of that division (`dividedSetOf`), and the counterpart moves the singlet in or out:

* the singlet (an excursion): `{}` and its counterpart `{n}`;
* the vector state `ℓ_t` (a step along `t`): `{t, n}` and `{t}`; at the last-step direction, `{h, n}` and `{h}`;
* the plane `e_{ab}`: `{a, b}` and `{a, b}' = {a, b, n}`; at the plane `F = {h, k}` and `C`, the three
  lines outside it, which names the same division as `F + {n}`;
* every divided set is even, a count, and its counterpart with `n` added odd, an amplitude (Proposition 42).
-/

namespace Comparison.Article

open Matrix hiding J
open Complex Comparison.Law

/-- **The division a two-spinor state holds:** the directions of the six (`n = 0`, the line `u` at `u + 1`) that its
operator reverses, the lines on which it disagrees. -/
def heldDiv (k : Fin 16) : Finset (Fin 6) := (disagreeSet k).map (Fin.succEmb 5)

theorem plane_case (a b : Fin 5) (hab : a ≠ b) (k : Fin 16) (hk : relOp k = γ a * γ b)
    (hd : disagreeSet k = {a, b}) (c : Fin 6) :
    relOp k * sixP1 c * (relOp k)ᵀ = (if c ∈ heldDiv k then -1 else 1 : ℂ) • sixP1 c := by
  rw [hk, plane_on_six a b hab c]
  have e : (c ∈ heldDiv k) ↔ (c = a.succ ∨ c = b.succ) := by
    simp only [heldDiv, hd, Finset.map_insert, Finset.map_singleton, Fin.coe_succEmb,
      Finset.mem_insert, Finset.mem_singleton]
  simp only [e]

theorem line_case (t : Fin 5) (k : Fin 16) (hk : relOp k = γ t)
    (hd : disagreeSet k = Finset.univ.erase t) (c : Fin 6) :
    relOp k * sixP1 c * (relOp k)ᵀ = (if c ∈ heldDiv k then -1 else 1 : ℂ) • sixP1 c := by
  rw [hk, line_on_six t c]
  have e : (c ∈ heldDiv k) ↔ ¬(c = 0 ∨ c = t.succ) := by
    rw [heldDiv, hd]
    rcases Fin.eq_zero_or_eq_succ c with rfl | ⟨u, rfl⟩
    · simp [Fin.succ_ne_zero]
    · simp [Fin.succ_ne_zero, Fin.succ_inj]
  by_cases h : c = 0 ∨ c = t.succ
  · rw [if_pos h, if_neg (by rw [e]; exact not_not.mpr h)]
  · rw [if_neg h, if_pos (by rw [e]; exact h)]

/-- **The two-spinor state's rotation on the six reverses exactly `heldDiv k`.** -/
theorem relOp_on_six (k : Fin 16) (c : Fin 6) :
    relOp k * sixP1 c * (relOp k)ᵀ = (if c ∈ heldDiv k then -1 else 1 : ℂ) • sixP1 c := by
  fin_cases k
  · fin_cases c <;> simp [relOp, heldDiv, disagreeSet]
  · exact line_case 0 _ rfl (by decide) c
  · exact line_case 1 _ rfl (by decide) c
  · exact line_case 2 _ rfl (by decide) c
  · exact line_case 3 _ rfl (by decide) c
  · exact line_case 4 _ rfl (by decide) c
  · exact plane_case 0 1 (by decide) _ rfl (by decide) c
  · exact plane_case 0 2 (by decide) _ rfl (by decide) c
  · exact plane_case 0 3 (by decide) _ rfl (by decide) c
  · exact plane_case 0 4 (by decide) _ rfl (by decide) c
  · exact plane_case 1 2 (by decide) _ rfl (by decide) c
  · exact plane_case 1 3 (by decide) _ rfl (by decide) c
  · exact plane_case 1 4 (by decide) _ rfl (by decide) c
  · exact plane_case 2 3 (by decide) _ rfl (by decide) c
  · exact plane_case 2 4 (by decide) _ rfl (by decide) c
  · exact plane_case 3 4 (by decide) _ rfl (by decide) c

/-- **The divided set of a two-spinor state:** the shorter description of its division. -/
def dividedSetOf (k : Fin 16) : Finset (Fin 6) :=
  if (heldDiv k).card ≤ 3 then heldDiv k else (heldDiv k)ᶜ

/-- The index of the vector state `ℓ_t` and of the plane `e_{ab}` among the sixteen. -/
def lineIdx (t : Fin 5) : Fin 16 := ⟨t.val + 1, by omega⟩

/-- **Proposition 43: where each piece sits.** -/
theorem pieces_sit :
    -- an excursion: the singlet holds nothing; `{}` (count) and `{n}` (amplitude)
    (dividedSetOf 0 = sHere ∧ twin sHere = sSinglet) ∧
    -- a step along `t`: `{t, n}` and `{t}`
    (∀ t : Fin 5, dividedSetOf (lineIdx t) = {0, t.succ} ∧ twin {0, t.succ} = {t.succ}) ∧
    -- the last-step direction `h` (line 0): `{h, n}` and `{h}`; the line `k` (line 1): `{k, n}` and `{k}`
    (dividedSetOf (lineIdx 0) = sLastDirectionSinglet ∧ twin sLastDirectionSinglet = sLastDirection) ∧
    (dividedSetOf (lineIdx 1) = sLineSinglet ∧ twin sLineSinglet = sLine) ∧
    -- the plane `F = {h, k}` (two-spinor state 6): `F` and `C`, the same division as `F + {n}`
    (dividedSetOf 6 = sF ∧ twin sF = sFn ∧ sFnᶜ = sC) ∧
    -- any plane `{a, b}`: `{a, b}` and `{a, b, n}`
    (∀ k : Fin 16, 6 ≤ k.val → dividedSetOf k = heldDiv k ∧ (dividedSetOf k).card = 2 ∧
      twin (dividedSetOf k) = insert 0 (dividedSetOf k)) ∧
    -- a count on the even divided set, an amplitude on its odd counterpart
    (∀ k : Fin 16, signS (dividedSetOf k) = 1 ∧ signS (twin (dividedSetOf k)) = -1) := by
  refine ⟨by decide, ?_, by decide, by decide, by decide, ?_, ?_⟩
  · intro t
    fin_cases t <;> decide
  · intro k hk
    fin_cases k <;> simp at hk <;> decide
  · intro k
    fin_cases k <;> decide

/-- The last-step direction's vector state is the two-spinor state to its own previous moment, and the plane the two-spinor state to the moment
before it (Proposition 27): the last-step direction's line reverses the four other lines, `θ_{T_h} = −θ_{h, n}`, and the plane
reverses its two lines. -/
theorem held_by_a_line :
    heldDiv (lineIdx 0) = {2, 3, 4, 5} ∧ heldDiv 6 = {1, 2} ∧ (dividedSetOf (lineIdx 0))ᶜ = {2, 3, 4, 5} := by
  decide

end Comparison.Article
