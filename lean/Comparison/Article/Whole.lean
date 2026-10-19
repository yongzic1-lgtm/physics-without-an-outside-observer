import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing

/-!
# The whole rotations adding into removing (Proposition 33's step `w ε(v) w⁻¹ = −ι(v)`)

For six adding operators `ε_a` and six removing operators `ι_a` in a complex algebra with `{ε_a, ε_b} = 0`,
`{ι_a, ι_b} = 0` and `{ε_a, ι_b} = δ_{ab}` (the exterior algebra of the six, `Existence/Exterior.lean`:
`εx_εx_add`, `ιx_ιx_add`, `εx_ιx_add`), the lines `J_a = ε_a + ι_a` and the whole `w = J₀J₁⋯J₅`:

* `K_anti_J`, `J_anti_J`: `K_a = ε_a − ι_a` anticommutes with every line, and two different lines anticommute;
* `J_whole`, `K_whole`: `J_a w = −w J_a` and `K_a w = w K_a`;
* `whole_turns_adding` (**Proposition 33**): **`w ε_a = −ι_a w`**, that is `w ε(v) w⁻¹ = −ι(v)`: calling the other part
  of a division turns adding a line into removing it.

The statement holds in any complex algebra with these two-spinor states; `Existence/Exterior.lean` cannot be imported beside
the rest of the article's root (its names clash with `Colour/GramTerm.lean` and `Elements/Half.lean`), so the instance at
`εx`, `ιx` is `Article/WholeExterior.lean`, built on its own (`lake build Comparison.Article.WholeExterior`).
-/

namespace Comparison.Article

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-- If `X a = s (a X)` and `X b = t (b X)` with integer signs, then `X (ab) = st (ab) X`. -/
theorem sign_mul {X a b : A} {s t : ℤ} (ha : X * a = s • (a * X)) (hb : X * b = t • (b * X)) :
    X * (a * b) = (s * t) • ((a * b) * X) := by
  rw [← mul_assoc, ha, smul_mul_assoc, mul_assoc, hb, mul_smul_comm, smul_smul, mul_comm s t, ← mul_assoc]

/-- Moving `X` across the six lines. -/
theorem sign_six {X : A} {J : Fin 6 → A} {s : Fin 6 → ℤ} (h : ∀ b, X * J b = s b • (J b * X)) :
    X * (J 0 * J 1 * J 2 * J 3 * J 4 * J 5) =
      (s 0 * s 1 * s 2 * s 3 * s 4 * s 5) • ((J 0 * J 1 * J 2 * J 3 * J 4 * J 5) * X) :=
  sign_mul (sign_mul (sign_mul (sign_mul (sign_mul (h 0) (h 1)) (h 2)) (h 3)) (h 4)) (h 5)

section CAR

variable (ε ι : Fin 6 → A)
  (hεε : ∀ a b, ε a * ε b + ε b * ε a = 0) (hιι : ∀ a b, ι a * ι b + ι b * ι a = 0)
  (hει : ∀ a b, ε a * ι b + ι b * ε a = if a = b then 1 else 0)
include hεε hιι hει

/-- `K_a = ε_a − ι_a` anticommutes with every line `J_b = ε_b + ι_b`. -/
theorem K_anti_J (a b : Fin 6) :
    (ε a - ι a) * (ε b + ι b) = (-1 : ℤ) • ((ε b + ι b) * (ε a - ι a)) := by
  have h1 := hεε a b
  have h2 := hιι a b
  have h3 := hει a b
  have h4 := hει b a
  have h34 : ε a * ι b + ι b * ε a = ε b * ι a + ι a * ε b := by
    rw [h3, h4]
    by_cases hab : a = b
    · subst hab; rfl
    · rw [if_neg hab, if_neg (Ne.symm hab)]
  rw [neg_one_zsmul]
  have key : (ε a - ι a) * (ε b + ι b) + (ε b + ι b) * (ε a - ι a) =
      (ε a * ε b + ε b * ε a) + (ε a * ι b + ι b * ε a) - (ε b * ι a + ι a * ε b) - (ι a * ι b + ι b * ι a) := by
    noncomm_ring
  rw [h1, h2, h34, zero_add, sub_self, sub_zero] at key
  exact eq_neg_of_add_eq_zero_left key

/-- Two different lines anticommute. -/
theorem J_anti_J {a b : Fin 6} (hab : a ≠ b) :
    (ε a + ι a) * (ε b + ι b) = (-1 : ℤ) • ((ε b + ι b) * (ε a + ι a)) := by
  have h1 := hεε a b
  have h2 := hιι a b
  have h3 := hει a b
  have h4 := hει b a
  rw [if_neg hab] at h3
  rw [if_neg (Ne.symm hab)] at h4
  rw [neg_one_zsmul]
  have key : (ε a + ι a) * (ε b + ι b) + (ε b + ι b) * (ε a + ι a) =
      (ε a * ε b + ε b * ε a) + (ε a * ι b + ι b * ε a) + (ε b * ι a + ι a * ε b) + (ι a * ι b + ι b * ι a) := by
    noncomm_ring
  rw [h1, h2, h3, h4, add_zero, add_zero, add_zero] at key
  exact eq_neg_of_add_eq_zero_left key

/-- The whole, `w = J₀J₁⋯J₅`. -/
def whole : A := (ε 0 + ι 0) * (ε 1 + ι 1) * (ε 2 + ι 2) * (ε 3 + ι 3) * (ε 4 + ι 4) * (ε 5 + ι 5)

/-- **`J_a w = −w J_a`.** -/
theorem J_whole (a : Fin 6) : (ε a + ι a) * whole ε ι = -(whole ε ι * (ε a + ι a)) := by
  have h : ∀ b, (ε a + ι a) * (ε b + ι b) = (if b = a then 1 else -1 : ℤ) • ((ε b + ι b) * (ε a + ι a)) := by
    intro b
    by_cases hb : b = a
    · subst hb; simp
    · rw [if_neg hb]; exact J_anti_J ε ι hεε hιι hει (Ne.symm hb)
  have := sign_six (J := fun b => ε b + ι b) (s := fun b => if b = a then 1 else -1) h
  simp only [whole] at this ⊢
  rw [this]
  have hs : ((if (0 : Fin 6) = a then 1 else -1 : ℤ) * (if (1 : Fin 6) = a then 1 else -1) *
      (if (2 : Fin 6) = a then 1 else -1) * (if (3 : Fin 6) = a then 1 else -1) *
      (if (4 : Fin 6) = a then 1 else -1) * (if (5 : Fin 6) = a then 1 else -1)) = -1 := by
    fin_cases a <;> decide
  rw [hs, neg_one_zsmul]

/-- **`K_a w = w K_a`.** -/
theorem K_whole (a : Fin 6) : (ε a - ι a) * whole ε ι = whole ε ι * (ε a - ι a) := by
  have := sign_six (J := fun b => ε b + ι b) (s := fun _ => -1) (K_anti_J ε ι hεε hιι hει a)
  simp only [whole] at this ⊢
  rw [this]
  norm_num

/-- **Proposition 33: the whole rotations adding into removing**, `w ε_a = −ι_a w`. -/
theorem whole_turns_adding (a : Fin 6) : whole ε ι * ε a = -(ι a * whole ε ι) := by
  have hJ := J_whole ε ι hεε hιι hει a
  have hK := K_whole ε ι hεε hιι hει a
  have e1 : (2 : ℂ) • ε a = (ε a + ι a) + (ε a - ι a) := by module
  have e2 : (2 : ℂ) • ι a = (ε a + ι a) - (ε a - ι a) := by module
  have hw1 : whole ε ι * (ε a + ι a) = -((ε a + ι a) * whole ε ι) := by rw [hJ, neg_neg]
  have lhs : (2 : ℂ) • (whole ε ι * ε a) = -((ε a + ι a) * whole ε ι) + (ε a - ι a) * whole ε ι := by
    rw [← mul_smul_comm, e1, mul_add, hw1, ← hK]
  have rhs : (2 : ℂ) • (-(ι a * whole ε ι)) = -((ε a + ι a) * whole ε ι) + (ε a - ι a) * whole ε ι := by
    rw [smul_neg, ← smul_mul_assoc, e2, sub_mul]
    abel
  have h2 : (2 : ℂ) • (whole ε ι * ε a) = (2 : ℂ) • (-(ι a * whole ε ι)) := lhs.trans rhs.symm
  have h2' := congrArg (fun x => (1 / 2 : ℂ) • x) h2
  simp only [smul_smul] at h2'
  norm_num at h2'
  exact h2'

end CAR

end Comparison.Article
