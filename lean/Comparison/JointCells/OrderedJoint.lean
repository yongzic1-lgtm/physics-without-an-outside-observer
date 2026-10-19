module

public import Comparison.Existence.JointStep

/-!
The ordered joint cell.  The intermediate transported direction is retained.
These are identities of Prop. 37, before any physical bound state is selected.
The last theorems carry all sources and boundary projectors in a basis change.
-/

@[expose] public section

namespace Comparison.JointCells

open scoped Matrix

variable {n : ℕ}

/-- The mixed vertical/parallel term is the transported second direction. -/
theorem two_joint_steps (a b : Fin n → ℝ) (U V : Matrix (Fin n) (Fin n) ℝ)
    (hU : Uᵀ * U = 1) :
    jointStep a U * jointStep b V =
      Jv a * Jv (U *ᵥ b) * extMap (U * V) := by
  unfold jointStep
  calc
    Jv a * extMap U * (Jv b * extMap V)
        = Jv a * (extMap U * Jv b) * extMap V := by simp only [mul_assoc]
    _ = Jv a * (Jv (U *ᵥ b) * extMap U) * extMap V := by rw [extMap_Jv U hU]
    _ = Jv a * Jv (U *ᵥ b) * extMap (U * V) := by
      rw [extMap_mul]
      simp only [mul_assoc]

/-- A third step remembers both preceding transports. -/
theorem three_joint_steps (a b c : Fin n → ℝ)
    (U V W : Matrix (Fin n) (Fin n) ℝ)
    (hU : Uᵀ * U = 1) (hV : Vᵀ * V = 1) :
    jointStep a U * jointStep b V * jointStep c W =
      Jv a * Jv (U *ᵥ b) * Jv ((U * V) *ᵥ c) * extMap (U * V * W) := by
  have hUV : (U * V)ᵀ * (U * V) = 1 := by
    rw [Matrix.transpose_mul]
    calc
      Vᵀ * Uᵀ * (U * V) = Vᵀ * (Uᵀ * U) * V := by simp only [mul_assoc]
      _ = 1 := by rw [hU, mul_one, hV]
  rw [two_joint_steps a b U V hU]
  unfold jointStep
  calc
    Jv a * Jv (U *ᵥ b) * extMap (U * V) * (Jv c * extMap W)
        = (Jv a * Jv (U *ᵥ b)) * (extMap (U * V) * Jv c) * extMap W := by
          simp only [mul_assoc]
    _ = (Jv a * Jv (U *ᵥ b)) * (Jv ((U * V) *ᵥ c) * extMap (U * V)) * extMap W := by
          rw [extMap_Jv (U * V) hUV]
    _ = Jv a * Jv (U *ᵥ b) * Jv ((U * V) *ᵥ c) * extMap (U * V * W) := by
          simp only [extMap_mul, mul_assoc]

section Basis
variable {A : Type*} [Monoid A]

/-- No commuting assumption is needed: carry the entire ordered word. -/
theorem conjugate_product (X : A) (hX : X * X = 1) (a b : A) :
    (X * a * X) * (X * b * X) = X * (a * b) * X := by
  calc
    (X * a * X) * (X * b * X) = X * a * (X * X) * b * X := by
      simp only [mul_assoc]
    _ = X * (a * b) * X := by rw [hX]; simp only [mul_one, mul_assoc]

/-- Arbitrary finite words, including inserted sources and retained boundaries. -/
theorem conjugate_word (X : A) (hX : X * X = 1) (w : List A) :
    (w.map (fun a => X * a * X)).prod = X * w.prod * X := by
  induction w with
  | nil => simpa using hX.symm
  | cons a w ih =>
      simp only [List.map_cons, List.prod_cons, ih]
      exact conjugate_product X hX a w.prod

end Basis

/-- A traced cross-source word has the same value in the two bases. -/
theorem traced_word_covariant {m : ℕ} (X : Matrix (Fin m) (Fin m) ℝ)
    (hX : X * X = 1) (w : List (Matrix (Fin m) (Fin m) ℝ)) :
    Matrix.trace (w.map (fun a => X * a * X)).prod = Matrix.trace w.prod := by
  rw [conjugate_word X hX]
  rw [Matrix.trace_mul_comm, ← mul_assoc, hX, one_mul]

end Comparison.JointCells

#print axioms Comparison.JointCells.two_joint_steps
#print axioms Comparison.JointCells.three_joint_steps
#print axioms Comparison.JointCells.conjugate_product
#print axioms Comparison.JointCells.conjugate_word
#print axioms Comparison.JointCells.traced_word_covariant

end
