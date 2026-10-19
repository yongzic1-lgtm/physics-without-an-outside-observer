module

public import Comparison.Law.Returns
public import Comparison.Existence.JointStep

/-!
# A meeting return with its transported rotation retained

The five physical steps come from the two vertical legs of Proposition 37.
Their induced action on a six-plane is the sign `planeSign`. Multiplying
this sign by the meeting agreement gives another native meeting block.
The extra rotation is a specified response channel; it is not a new scalar
mass pole of the original plane block.
-/

@[expose] public section

namespace Comparison.JointCells

open Matrix
open Comparison.Law
open scoped symmDiff

def stepSign (s : Fin 5) (x : Fin 6) : ℤ :=
  if x = 0 ∨ x = s.succ then 1 else -1

def planeSign (s : Fin 5) (a b : Fin 6) : ℤ :=
  stepSign s a * stepSign s b

def planePattern (a b : Fin 6) : Finset (Fin 5) :=
  Finset.univ.filter fun s => planeSign s a b = -1

theorem stepSign_sq (s : Fin 5) (x : Fin 6) : stepSign s x * stepSign s x = 1 := by
  simp only [stepSign]
  split_ifs <;> norm_num

theorem planeSign_eq (s : Fin 5) (a b : Fin 6) :
    planeSign s a b = if s ∈ planePattern a b then -1 else 1 := by
  simp only [planePattern, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [planeSign, stepSign]
  split_ifs <;> norm_num at *

/-- A rotation of two lines has their two-element pattern. -/
theorem planePattern_lines : ∀ (a b : Fin 5), a ≠ b →
    planePattern a.succ b.succ = {a, b} := by decide

/-- An own clock `(n,t)` has the four-vector state pattern. -/
theorem planePattern_clock : ∀ t : Fin 5,
    planePattern 0 t.succ = ({t} : Finset (Fin 5))ᶜ := by decide

/-- Every genuine six-plane gives an even meeting character. -/
theorem planePattern_even : ∀ a b : Fin 6, a ≠ b →
    (planePattern a b).card = 2 ∨ (planePattern a b).card = 4 := by decide

theorem J_conj_generator (a x : Fin 6) :
    Jx (R := ℝ) a * Jx x * Jx a = (if a = x then (1 : ℝ) else -1) • Jx x := by
  by_cases h : a = x
  · subst x
    simp [Jx_mul_self]
  · rw [Jx_anticomm (R := ℝ) h]
    have hn := _root_.neg_mul (Jx (R := ℝ) x * Jx (R := ℝ) a) (Jx (R := ℝ) a)
    rw [hn, mul_assoc, Jx_mul_self, mul_one]
    simp only [h, ite_false]
    exact (neg_one_smul ℝ (Jx (R := ℝ) x)).symm

theorem two_reflections_sign : ∀ (s : Fin 5) (x : Fin 6),
    (if s.succ = x then (1 : ℤ) else -1) * (if (0 : Fin 6) = x then 1 else -1) =
      -stepSign s x := by decide

/-- The two vertical legs act on a six-vector with the negative paired description sign. -/
theorem two_leg_generator (s : Fin 5) (x : Fin 6) :
    (Jx (R := ℝ) 0 * Jx s.succ) * Jx x * (Jx s.succ * Jx 0) =
      (-(stepSign s x : ℝ)) • Jx x := by
  calc (Jx (R := ℝ) 0 * Jx s.succ) * Jx x * (Jx s.succ * Jx 0)
      = Jx 0 * (Jx s.succ * Jx x * Jx s.succ) * Jx 0 := by simp only [mul_assoc]
    _ = ((if s.succ = x then (1 : ℝ) else -1) * (if (0 : Fin 6) = x then 1 else -1)) • Jx x := by
      rw [J_conj_generator, mul_smul_comm, smul_mul_assoc, J_conj_generator, smul_smul]
    _ = _ := by
      congr 1
      exact_mod_cast two_reflections_sign s x

theorem conj_product {A : Type*} [Ring A] (L R X Y : A) (hRL : R*L = 1) :
    L*(X*Y)*R = (L*X*R)*(L*Y*R) := by
  symm
  calc (L*X*R)*(L*Y*R) = L*X*(R*L)*Y*R := by simp only [mul_assoc]
    _ = _ := by rw [hRL]; simp only [mul_one, mul_assoc]

/-- The native character is derived from Proposition 37's two vertical legs. -/
theorem two_leg_plane (s : Fin 5) (a b : Fin 6) :
    (Jx (R := ℝ) 0 * Jx s.succ) * (Jx a * Jx b) * (Jx s.succ * Jx 0) =
      (planeSign s a b : ℝ) • (Jx a * Jx b) := by
  have hinv : (Jx (R := ℝ) s.succ * Jx 0) * (Jx 0 * Jx s.succ) = 1 := by
    calc (Jx (R := ℝ) s.succ * Jx 0) * (Jx 0 * Jx s.succ)
        = Jx s.succ * (Jx 0 * Jx 0) * Jx s.succ := by simp only [mul_assoc]
      _ = 1 := by rw [Jx_mul_self, mul_one, Jx_mul_self]
  rw [conj_product _ _ _ _ hinv, two_leg_generator, two_leg_generator, smul_mul_smul_comm]
  simp [planeSign]

def mixedK {R : Type*} [CommRing R] (V W : Finset (Fin 5)) :
    Matrix (Fin 5) (Fin 5) R := thetaP W * patternK V

/-- Keeping the parallel character is exactly a shift of the vertical pattern. -/
theorem mixedK_shift {R : Type*} [CommRing R] (V W : Finset (Fin 5)) :
    mixedK (R := R) V W = patternK (V ∆ W) := by
  ext s t
  simp only [mixedK, thetaP, diagonal_mul, patternK_apply, Finset.mem_symmDiff]
  by_cases hv : s ∈ V <;> by_cases hw : s ∈ W <;> simp [hv, hw]

theorem transported_step {R : Type*} [CommRing R] (V : Finset (Fin 5))
    (a b : Fin 6) (s t : Fin 5) :
    mixedK (R := R) V (planePattern a b) s t =
      (planeSign s a b : R) * (if s ∈ V then -1 else 1) * (if s = t then 0 else 1) := by
  simp only [mixedK, thetaP, diagonal_mul, patternK_apply, planeSign_eq]
  push_cast
  ring

theorem mixed_factor (V W : Finset (Fin 5)) (u : ℂ) :
    (1 - u ^ 2) * (1 - u • mixedK (R := ℂ) V W).det =
      (1 + u) ^ (5 - (V ∆ W).card) * (1 - u) ^ (V ∆ W).card *
        (1 + 4 * u ^ 2 - u * (5 - 2 * (V ∆ W).card)) := by
  rw [mixedK_shift]
  exact pattern_factor u (V ∆ W)

def plane : Finset (Fin 5) := {0, 1}
def colour : Finset (Fin 5) := {2, 3, 4}

theorem plane_own_shift : mixedK (R := ℂ) plane (planePattern 1 2) = patternK ∅ := by
  rw [mixedK_shift]
  congr 1

theorem colour_own_shift : mixedK (R := ℂ) colour (planePattern 1 2) = patternK Finset.univ := by
  rw [mixedK_shift]
  congr 1
  decide

theorem plane_own_factor (u : ℂ) :
    (1 - u • mixedK (R := ℂ) plane (planePattern 1 2)).det = (1 + u)^4 * (1 - 4*u) := by
  rw [plane_own_shift]
  exact singlet_factor u

theorem colour_own_factor (u : ℂ) :
    (1 - u • mixedK (R := ℂ) colour (planePattern 1 2)).det = (1 - u)^4 * (1 + 4*u) := by
  rw [colour_own_shift]
  exact all_factor u

/-- The clock of a colour line in F's return shifts F to a plane, not to C. -/
theorem plane_colour_clock :
    mixedK (R := ℂ) plane (planePattern 0 3) = patternK {3, 4} := by
  rw [mixedK_shift]
  congr 1

/-- The same clock inside C shifts C to the complementary three-line pattern. -/
theorem colour_colour_clock :
    mixedK (R := ℂ) colour (planePattern 0 3) = patternK {0, 1, 2} := by
  rw [mixedK_shift]
  congr 1
  decide

/-- An F-to-C insertion would need the all-five odd pattern, absent from the fifteen rotations. -/
theorem no_rotation_plane_to_colour : ∀ a b : Fin 6, a ≠ b →
    plane ∆ planePattern a b ≠ colour := by decide

/-- Retaining the complete transformed source preserves products. -/
theorem carry_product {A : Type*} [Ring A] (H X Y : A) (hH : H*H = 1) :
    (H*X*H) * (H*Y*H) = H*(X*Y)*H := by
  calc (H*X*H) * (H*Y*H) = H*X*(H*H)*Y*H := by simp only [mul_assoc]
    _ = H*(X*Y)*H := by rw [hH]; simp only [mul_one, mul_assoc]

/-- Carry both retained boundaries as well as the response, before compressing. -/
theorem carry_boundary {A : Type*} [Ring A] (H P X : A) (hH : H*H = 1) :
    (H*P*H)*(H*X*H)*(H*P*H) = H*(P*X*P)*H := by
  rw [carry_product H P X hH, carry_product H (P*X) P hH]

/-- The inverse travels with the operator; this does not assume a scalar renewal. -/
theorem carry_inverse {A : Type*} [Ring A] (H X Y : A) (hH : H*H = 1)
    (hXY : X*Y = 1) : (H*X*H)*(H*Y*H) = 1 := by
  rw [carry_product H X Y hH, hXY, mul_one, hH]

theorem character_square : ∀ x U : Fin 16, charTable x U * charTable x U = 1 := by decide

noncomputable def characterGauge (U : Fin 16) : Matrix State State ℂ :=
  diagonal fun p => (charTable p.1 U : ℂ)

theorem characterGauge_sq (U : Fin 16) : characterGauge U * characterGauge U = 1 := by
  rw [characterGauge, diagonal_mul_diagonal]
  have he : (fun p : State => (charTable p.1 U : ℂ) * (charTable p.1 U : ℂ)) = fun _ => 1 := by
    funext p
    exact_mod_cast character_square p.1 U
  rw [he]
  exact diagonal_one

/-- The carried rotation is a vertex character gauge on the complete eighty states. -/
theorem transport_is_gauge (U : Fin 16) (c : Fin 5 → Fin 5 → ℂ) :
    characterGauge U * transitionShaped ℂ c * characterGauge U =
      transitionShaped ℂ (fun s t => (charSign s U : ℂ) * c s t) := by
  ext p q
  simp only [characterGauge, diagonal_mul, mul_diagonal, transitionShaped, Matrix.of_apply]
  by_cases h : p.1 = transition p.2 q.1
  · simp only [h, ite_true]
    rw [charTable_transition]
    push_cast
    have he : (charTable q.1 U : ℂ) * (charTable q.1 U : ℂ) = 1 := by
      exact_mod_cast character_square q.1 U
    calc (charTable q.1 U : ℂ) * (charSign p.2 U : ℂ) * c p.2 q.2 * (charTable q.1 U : ℂ)
        = ((charTable q.1 U : ℂ) * (charTable q.1 U : ℂ)) * ((charSign p.2 U : ℂ) * c p.2 q.2) := by ring
      _ = _ := by rw [he, one_mul]
  · simp [h]

/-- Conjugation does not change a finite determinant. -/
theorem det_carry {n : Type*} [Fintype n] [DecidableEq n]
    (H M : Matrix n n ℂ) (hH : H*H = 1) : (H*M*H).det = M.det := by
  have hd : H.det * H.det = 1 := by
    simpa only [det_mul, det_one] using congrArg Matrix.det hH
  rw [det_mul, det_mul]
  calc H.det * M.det * H.det = (H.det * H.det) * M.det := by ring
    _ = _ := by rw [hd, one_mul]

/-- Hence the whole law with a transported rotation has the original determinant. -/
theorem transported_law_det (U : Fin 16) (c : Fin 5 → Fin 5 → ℂ) (u : ℂ) :
    (1 - u • transitionShaped ℂ (fun s t => (charSign s U : ℂ) * c s t)).det =
      (1 - u • transitionShaped ℂ c).det := by
  rw [← transport_is_gauge]
  have he : 1 - u • (characterGauge U * transitionShaped ℂ c * characterGauge U) =
      characterGauge U * (1 - u • transitionShaped ℂ c) * characterGauge U := by
    simp only [mul_sub, sub_mul, mul_one, characterGauge_sq, Matrix.mul_smul, Matrix.smul_mul]
  rw [he]
  exact det_carry _ _ (characterGauge_sq U)

end Comparison.JointCells

#print axioms Comparison.JointCells.stepSign_sq
#print axioms Comparison.JointCells.planeSign_eq
#print axioms Comparison.JointCells.planePattern_lines
#print axioms Comparison.JointCells.planePattern_clock
#print axioms Comparison.JointCells.planePattern_even
#print axioms Comparison.JointCells.J_conj_generator
#print axioms Comparison.JointCells.two_reflections_sign
#print axioms Comparison.JointCells.two_leg_generator
#print axioms Comparison.JointCells.conj_product
#print axioms Comparison.JointCells.two_leg_plane
#print axioms Comparison.JointCells.mixedK_shift
#print axioms Comparison.JointCells.transported_step
#print axioms Comparison.JointCells.mixed_factor
#print axioms Comparison.JointCells.plane_own_shift
#print axioms Comparison.JointCells.colour_own_shift
#print axioms Comparison.JointCells.plane_own_factor
#print axioms Comparison.JointCells.colour_own_factor
#print axioms Comparison.JointCells.plane_colour_clock
#print axioms Comparison.JointCells.colour_colour_clock
#print axioms Comparison.JointCells.no_rotation_plane_to_colour
#print axioms Comparison.JointCells.carry_product
#print axioms Comparison.JointCells.carry_boundary
#print axioms Comparison.JointCells.carry_inverse
#print axioms Comparison.JointCells.character_square
#print axioms Comparison.JointCells.characterGauge_sq
#print axioms Comparison.JointCells.transport_is_gauge
#print axioms Comparison.JointCells.det_carry
#print axioms Comparison.JointCells.transported_law_det
