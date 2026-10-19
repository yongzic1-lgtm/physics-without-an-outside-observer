module

public import Comparison.Elements.TwoThings
public import Comparison.Elements.SixDirections

/-!
# Book III, continued: the fifteen rotations turn the six directions

A generator `X` (anti-Hermitian, trace zero) acts on a two-spinor state matrix `A` as `X A + A Xᵀ`, the
derivative of `U A Uᵀ` (`act`). On P1's real six, `f₀ = J` (the singlet) and `f_{s+1} = i γ_s J`:

* `gen_acts`: each of the fifteen generators turns exactly one plane of the six, doubled:
  `i γ_s` turns the plane of the singlet and the line `s`; the plane generator `−γ_a γ_b` turns the
  plane of the lines `a` and `b`.
* `plane_bijective`: the fifteen generators and the fifteen planes `a < b` of the six correspond
  one to one; the ten symmetric states are exactly the planes without the singlet (`plane_inr_fst_ne_zero`).

So the fifteen rotations of P1 turn the six as all of `so(6)`, and the ten that keep the singlet (`sp2`)
are the rotations of the five directions.
-/

@[expose] public section

namespace Comparison

open Matrix hiding J
open Complex Kronecker

/-- The two lines of each of the ten symmetric states, in the order of `obs`. -/
def planeLines : Fin 10 → Fin 5 × Fin 5 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (1, 2), (1, 3), (1, 4), (2, 3), (2, 4), (3, 4)]

theorem planeLines_ne (f : Fin 10) : (planeLines f).1 ≠ (planeLines f).2 := by
  fin_cases f <;> decide

theorem gen_inl (s : Fin 5) : gen (Sum.inl s) = I • γ s := by
  simp [gen, genIdx, obs_lineIdx]

theorem gen_inr (f : Fin 10) : gen (Sum.inr f) = -(γ (planeLines f).1 * γ (planeLines f).2) := by
  fin_cases f <;> simp [gen, genIdx, planeIdx, obs, planeLines, smul_smul]

theorem sixP1_zero : sixP1 0 = J := rfl

theorem sixP1_succ (u : Fin 5) : sixP1 u.succ = I • (γ u * J) := by
  fin_cases u <;> rfl

/-- The action of a generator on a two-spinor state matrix, `X·A = X A + A Xᵀ`. -/
def act (X A : Matrix Four Four ℂ) : Matrix Four Four ℂ := X * A + A * Xᵀ

theorem J_mul_γ_transpose (s : Fin 5) : J * (γ s)ᵀ = γ s * J := (γ_mul_J_eq s).symm

theorem J_mul_plane_transpose (a b : Fin 5) : J * (γ a * γ b)ᵀ = γ b * γ a * J := by
  rw [Matrix.transpose_mul, ← Matrix.mul_assoc, J_mul_γ_transpose, Matrix.mul_assoc,
    J_mul_γ_transpose, Matrix.mul_assoc]

/-- A line turns the singlet toward itself: `i γ_s · J = 2 (i γ_s J)`. -/
theorem act_line_singlet (s : Fin 5) : act (I • γ s) J = (2 : ℂ) • (I • (γ s * J)) := by
  rw [act, Matrix.transpose_smul, Matrix.mul_smul, J_mul_γ_transpose, Matrix.smul_mul, two_smul]

/-- A line turns itself back to the singlet and leaves the other lines:
`i γ_s · (i γ_u J) = -2 δ_su J`. -/
theorem act_line_line (s u : Fin 5) :
    act (I • γ s) (I • (γ u * J)) = if s = u then (-2 : ℂ) • J else 0 := by
  have h : act (I • γ s) (I • (γ u * J)) =
      -((γ s * γ u + γ u * γ s) * J) := by
    rw [act, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.mul_assoc (γ u), J_mul_γ_transpose, smul_smul, smul_smul,
      Complex.I_mul_I, neg_one_smul, neg_one_smul, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.add_mul]
    abel
  rw [h, clifford]
  split_ifs <;> simp

/-- The plane commutator: `[γ_u, γ_a γ_b]` is `2 γ_b`, `-2 γ_a` or `0`. -/
theorem comm_plane (u a b : Fin 5) (hab : a ≠ b) :
    γ u * (γ a * γ b) - γ a * γ b * γ u =
      if u = a then (2 : ℂ) • γ b else if u = b then (-2 : ℂ) • γ a else 0 := by
  split_ifs with hua hub
  · subst hua
    rw [← Matrix.mul_assoc, γ_mul_self, Matrix.one_mul, γ_conj_line_ne hab]
    rw [sub_neg_eq_add, two_smul]
  · subst hub
    rw [← Matrix.mul_assoc, γ_conj_line_ne (Ne.symm hab), Matrix.mul_assoc,
      γ_mul_self, Matrix.mul_one]
    module
  · have h1 : γ u * (γ a * γ b) * γ u = γ a * γ b := γ_conj_plane_out hua hub
    have h2 : γ u * (γ a * γ b) = γ a * γ b * γ u := by
      calc γ u * (γ a * γ b) = γ u * (γ a * γ b) * (γ u * γ u) := by
            rw [γ_mul_self, Matrix.mul_one]
        _ = (γ u * (γ a * γ b) * γ u) * γ u := by simp only [Matrix.mul_assoc]
        _ = γ a * γ b * γ u := by rw [h1]
    rw [h2, sub_self]

/-- A plane rotations the lines: `(−γ_a γ_b) · (i γ_u J) = i [γ_u, γ_a γ_b] J`. -/
theorem act_plane_line (a b u : Fin 5) (hab : a ≠ b) :
    act (-(γ a * γ b)) (I • (γ u * J)) =
      if u = a then (2 : ℂ) • (I • (γ b * J))
      else if u = b then (-2 : ℂ) • (I • (γ a * J)) else 0 := by
  have h : act (-(γ a * γ b)) (I • (γ u * J)) =
      I • ((γ u * (γ a * γ b) - γ a * γ b * γ u) * J) := by
    rw [act, Matrix.transpose_neg, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_assoc (γ u),
      J_mul_plane_transpose, Matrix.neg_mul, Matrix.mul_smul, Matrix.sub_mul]
    have e1 : γ u * (γ b * γ a * J) = -(γ u * (γ a * γ b) * J) := by
      rw [γ_anticomm (Ne.symm hab)]
      simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_assoc]
    rw [e1]
    simp only [Matrix.mul_assoc, smul_neg, neg_neg, smul_sub]
    abel
  rw [h, comm_plane u a b hab]
  split_ifs <;> simp [smul_smul, mul_comm]

/-- The plane of the six directions that each generator turns (`0` is the singlet, `s + 1` the
line `s`). -/
def plane : Fin 5 ⊕ Fin 10 → Fin 6 × Fin 6
  | Sum.inl s => (0, s.succ)
  | Sum.inr f => ((planeLines f).1.succ, (planeLines f).2.succ)

theorem plane_lt (x : Fin 5 ⊕ Fin 10) : (plane x).1 < (plane x).2 := by
  revert x
  decide

/-- **The fifteen generators and the fifteen planes of the six correspond one to one.** -/
theorem plane_bijective :
    Function.Injective plane ∧ ∀ p : Fin 6 × Fin 6, p.1 < p.2 → ∃ x, plane x = p := by
  constructor
  · decide
  · decide

/-- The ten symmetric states are exactly the planes that do not contain the singlet. -/
theorem plane_fst_eq_zero_iff (x : Fin 5 ⊕ Fin 10) : (plane x).1 = 0 ↔ x.isLeft := by
  revert x
  decide

/-- The rotation of the plane `p`, doubled: `f_{p.1} ↦ 2 f_{p.2}`, `f_{p.2} ↦ −2 f_{p.1}`, the
other directions to `0`. -/
noncomputable def rotSix (p : Fin 6 × Fin 6) (c : Fin 6) : Matrix Four Four ℂ :=
  if c = p.1 then (2 : ℂ) • sixP1 p.2 else if c = p.2 then (-2 : ℂ) • sixP1 p.1 else 0

/-- **The fifteen rotations turn P1's real six as the fifteen rotations of planes:** each generator
turns exactly its plane. -/
theorem gen_acts (x : Fin 5 ⊕ Fin 10) (c : Fin 6) : act (gen x) (sixP1 c) = rotSix (plane x) c := by
  rcases x with s | f
  · rw [gen_inl]
    refine Fin.cases ?_ (fun u => ?_) c
    · rw [sixP1_zero, act_line_singlet]
      simp [rotSix, plane, sixP1_succ]
    · rw [sixP1_succ, act_line_line]
      by_cases h : s = u
      · subst h
        simp [rotSix, plane, sixP1_zero]
      · have h' : u.succ ≠ s.succ := fun e => h (Fin.succ_injective _ e).symm
        simp [rotSix, plane, h, h', Fin.succ_ne_zero]
  · rw [gen_inr]
    have hab := planeLines_ne f
    refine Fin.cases ?_ (fun u => ?_) c
    · rw [sixP1_zero]
      have h0 := plane_keeps_singlet f
      rw [gen_inr] at h0
      change act _ J = 0 at h0
      rw [h0]
      simp [rotSix, plane, (Fin.succ_ne_zero _).symm]
    · rw [sixP1_succ, act_plane_line _ _ _ hab]
      simp only [rotSix, plane, Fin.succ_inj, sixP1_succ]

end Comparison

end
