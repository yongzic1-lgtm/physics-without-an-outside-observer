import Comparison.Law.Returns
import Comparison.Existence.Table

/-!
# The joint cell of the second pairing at every one of the 32 patterns, the four types at once

A pattern `P` (a set of the five directions, Definition 37) holds the division `θ_P` that divides the
lines of `P` and leaves the singlet undivided; the sixteen even patterns are the meetings, the sixteen
odd ones their counterparts with `n` added (Proposition 129). Its own element is Proposition 42's form of its division:
`γ_P` (the product of its lines; a count when `|P|` is even) or the antilinear `γ_PΘ` (an amplitude
when `|P|` is odd).

**The joint formula** (`one_step`): the step of one system along any line `s` carries the own element
back with the pattern's agreement sign times its full-cycle sign,
`γ_s γ_P γ_s = z_P² ε_s(P) γ_P`,  `z_P² = (−1)^{|P|}`.

**Its two projections**, for all 32 patterns at once:
* vertical: the scalar channel of the joint walk is the last-step direction's walk `K_P` (`jointWalk_scalar`), with
  its agreement signs, returns and factor (Propositions 131, 132; `pattern_factor`);
* parallel: the own channel is `z_P²K_∅`, the free last-step direction with the long-range zero at `u = z_P²/4`
  (`own_channel`); **the frame the pattern keeps is the commutant of its own element**, linear at the
  meetings and through the quaternionic structure at the counterparts (`kept_iff_form`); its own rotation (Definition 41) is
  absent at `0|6` and its counterpart with `n` added, moved at the five `{t}` (`1|5`: the rest mass), kept and central at
  the fifteen `2|4` (the clocks), kept and not central at the ten `3|3` (colour), and unique where it
  exists (`own_classes`, `own_unique`, `own_absent`, `own_noncentral`).

`joint_cell` states the formula with both projections at every pattern.
-/

open Comparison Matrix Kronecker
open Comparison.Law

namespace Comparison.JointCells.Patterns

/-! ## The agreement sign and the joint walk -/

/-- The agreement sign `ε_s(P)` over `ℤ`. -/
def agrZ (P : Finset (Fin 5)) (s : Fin 5) : ℤ := if s ∈ P then -1 else 1

/-- The pattern's division of the six: its lines divided, the singlet undivided. -/
def divOf (P : Finset (Fin 5)) : Finset (Fin 6) := P.map (Fin.succEmb 5)

/-- The full-cycle sign `z_P² = (−1)^{|P|}`. -/
def cycleZ (P : Finset (Fin 5)) : ℤ := (-1) ^ P.card

/-- **The joint walk at `P`:** the last-step direction arrives at `s` with `ε_s(P)` and the step along `s` carries one
system's operators, `X ↦ γ_s X γ_s`. -/
noncomputable def jointWalk (P : Finset (Fin 5)) (v : Fin 5 → Matrix Four Four ℂ) :
    Fin 5 → Matrix Four Four ℂ :=
  fun s => ((agrZ P s : ℤ) : ℂ) • (γ s * (∑ t, (if s = t then (0 : ℂ) else 1) • v t) * γ s)

/-- `𝐉 − I` on the five directions. -/
def offD : Matrix (Fin 5) (Fin 5) ℂ := Matrix.of fun i j => if i = j then 0 else 1

theorem jointWalk_channel (P : Finset (Fin 5)) (X : Matrix Four Four ℂ) (c : Fin 5 → ℂ)
    (hc : ∀ s, γ s * X * γ s = c s • X) (a : Fin 5 → ℂ) :
    jointWalk P (fun t => a t • X) =
      fun s => ((diagonal (fun s => ((agrZ P s : ℤ) : ℂ) * c s) * offD) *ᵥ a) s • X := by
  funext s
  simp only [jointWalk]
  have hsum : (∑ t, (if s = t then (0 : ℂ) else 1) • (a t • X)) =
      (∑ t, (if s = t then (0 : ℂ) else 1) * a t) • X := by
    rw [Finset.sum_smul]
    exact Finset.sum_congr rfl fun t _ => by rw [smul_smul]
  rw [hsum, Matrix.mul_smul, Matrix.smul_mul, hc s, smul_smul, smul_smul]
  congr 1
  simp only [Matrix.mulVec, dotProduct, diagonal_mul, offD, of_apply]
  rw [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun t _ => by ring

theorem patternK_eq (P : Finset (Fin 5)) :
    patternK (R := ℂ) P = diagonal (fun s => ((agrZ P s : ℤ) : ℂ)) * offD := by
  ext i j
  simp only [patternK_apply, diagonal_mul, offD, of_apply, agrZ]
  split_ifs <;> simp

/-! ## The joint formula at all 32 patterns -/

theorem one_step_Z : ∀ (P : Finset (Fin 5)) (s : Fin 5),
    γZ s * gammaDZ P * γZ s = ((cycleZ P * agrZ P s : ℤ) : GaussianInt) • gammaDZ P := by
  decide +kernel

/-- **The joint formula:** `γ_s γ_P γ_s = z_P² ε_s(P) γ_P` for every pattern `P` and line `s`. -/
theorem one_step (P : Finset (Fin 5)) (s : Fin 5) :
    γ s * gammaD P * γ s = ((cycleZ P * agrZ P s : ℤ) : ℂ) • gammaD P := by
  have h := congrArg (fun M => M.map GaussianInt.toComplex) (one_step_Z P s)
  simp only [Matrix.map_mul, γZ_map, gammaDZ_map, map_intSmul] at h
  exact h

/-- **The vertical projection at every pattern:** the scalar channel is the last-step direction's walk `K_P`. -/
theorem jointWalk_scalar (P : Finset (Fin 5)) (a : Fin 5 → ℂ) :
    jointWalk P (fun t => a t • (1 : Matrix Four Four ℂ)) =
      fun s => (patternK (R := ℂ) P *ᵥ a) s • (1 : Matrix Four Four ℂ) := by
  rw [jointWalk_channel P 1 (fun _ => 1) (fun s => by rw [Matrix.mul_one, γ_mul_self, one_smul])]
  simp only [mul_one]
  rw [patternK_eq]

/-- **The own channel at every pattern is the free last-step direction with the full-cycle sign:** on `a ⊗ γ_P` the
joint walk is `z_P² K_∅`: `K_∅` at the meetings, `K_{all five} = −K_∅` at the counterparts. -/
theorem own_channel (P : Finset (Fin 5)) (a : Fin 5 → ℂ) :
    jointWalk P (fun t => a t • gammaD P) =
      fun s => (((cycleZ P : ℤ) : ℂ) • (patternK (R := ℂ) ∅ *ᵥ a)) s • gammaD P := by
  rw [jointWalk_channel P (gammaD P) (fun s => ((cycleZ P * agrZ P s : ℤ) : ℂ)) (one_step P)]
  have h : (fun s => ((agrZ P s : ℤ) : ℂ) * ((cycleZ P * agrZ P s : ℤ) : ℂ)) =
      fun _ => ((cycleZ P : ℤ) : ℂ) := by
    funext s
    simp only [agrZ]
    split_ifs <;> push_cast <;> ring
  rw [h, patternK_eq]
  funext s
  congr 1
  simp only [Matrix.mulVec, dotProduct, diagonal_mul, Pi.smul_apply, smul_eq_mul, agrZ,
    Finset.notMem_empty, ↓reduceIte, Int.cast_one, one_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The own channel's law: `(1 + u)⁴(1 − 4u)` at the meetings, zero at `u = 1/4`;
`(1 − u)⁴(1 + 4u)` at the counterparts, zero at `u = −1/4`. -/
theorem own_factor (P : Finset (Fin 5)) (u : ℂ) :
    (1 - u • (((cycleZ P : ℤ) : ℂ) • patternK (R := ℂ) ∅)).det =
      if P.card % 2 = 0 then (1 + u) ^ 4 * (1 - 4 * u) else (1 - u) ^ 4 * (1 + 4 * u) := by
  have hall : patternK (R := ℂ) Finset.univ = -patternK ∅ := by
    rw [patternK, patternK, ← Finset.compl_empty, thetaP_compl, Matrix.neg_mul]
  rcases Nat.even_or_odd P.card with he | ho
  · have hz : ((cycleZ P : ℤ) : ℂ) = 1 := by
      simp [cycleZ, he.neg_one_pow]
    have hc : P.card % 2 = 0 := Nat.even_iff.mp he
    simp only [hz, one_smul, hc, ↓reduceIte]
    exact singlet_factor u
  · have hz : ((cycleZ P : ℤ) : ℂ) = -1 := by
      simp [cycleZ, ho.neg_one_pow]
    have hc : P.card % 2 = 1 := Nat.odd_iff.mp ho
    simp only [hz, neg_one_smul, ← hall, hc, one_ne_zero, ↓reduceIte]
    exact all_factor u

/-! ## The frame: the commutant of the own element, linear at meetings, through the quaternionic structure at counterparts -/

theorem map_toComplex_inj (A B : Matrix Four Four GaussianInt) :
    A.map GaussianInt.toComplex = B.map GaussianInt.toComplex ↔ A = B :=
  (Matrix.map_injective (fun _ _ h => GaussianInt.toComplex_inj.mp h)).eq_iff

theorem map_star_toComplex (A : Matrix Four Four GaussianInt) :
    (A.map star).map GaussianInt.toComplex = (A.map GaussianInt.toComplex).map star := by
  ext i j
  simp only [Matrix.map_apply]
  rw [GaussianInt.toComplex_star]
  rfl

theorem kept_iff_form_Z : ∀ (P : Finset (Fin 5)) (x : Fin 5 ⊕ Fin 10),
    Kept (divOf P) x ↔
      (if P.card % 2 = 0 then genZ x * gammaDZ P = gammaDZ P * genZ x
       else genZ x * (gammaDZ P * JZ) = (gammaDZ P * JZ) * (genZ x).map star) := by
  decide +kernel

/-- **The frame a pattern keeps is the commutant of its own element:** at a meeting (`|P|` even) the
rotations that commute with `γ_P`; at a counterpart (`|P|` odd) those that commute with the antilinear
`C_P = γ_PΘ`, `C_P v = γ_P J v̄` (Proposition 42). -/
theorem kept_iff_form (P : Finset (Fin 5)) (x : Fin 5 ⊕ Fin 10) :
    Kept (divOf P) x ↔
      (if P.card % 2 = 0 then gen x * gammaD P = gammaD P * gen x
       else gen x * (gammaD P * J) = (gammaD P * J) * (gen x).map star) := by
  rw [kept_iff_form_Z P x]
  split_ifs
  · rw [← genZ_map x, ← gammaDZ_map P]
    simp only [← Matrix.map_mul]
    exact (map_toComplex_inj _ _).symm
  · rw [← genZ_map x, ← gammaDZ_map P, ← JZ_map, ← map_star_toComplex]
    simp only [← Matrix.map_mul]
    exact (map_toComplex_inj _ _).symm

/-! ## The own rotation at every pattern (Definition 41) -/

/-- The sign by which the step along `s` carries the rotation `x`. -/
def turnSign (s : Fin 5) : Fin 5 ⊕ Fin 10 → ℤ
  | Sum.inl u => if s = u then 1 else -1
  | Sum.inr f => if s = (planeLines f).1 ∨ s = (planeLines f).2 then -1 else 1

/-- The own rotation, combinatorially: around every loop the rotation's two step signs are the pattern's
vertical return. -/
def OwnAt (P : Finset (Fin 5)) (x : Fin 5 ⊕ Fin 10) : Prop :=
  ∀ s t : Fin 5, s ≠ t → turnSign s x * turnSign t x = agrZ P s * agrZ P t

instance (P : Finset (Fin 5)) : DecidablePred (OwnAt P) := fun x => by
  unfold OwnAt; infer_instance

/-- A rotation that commutes with every rotation the division keeps, combinatorially: its plane meets every
kept plane in nothing or in itself. -/
def CentralIn (D : Finset (Fin 6)) (x : Fin 5 ⊕ Fin 10) : Prop :=
  ∀ y, Kept D y → x = y ∨ PlaneDisjoint x y

instance (D : Finset (Fin 6)) : DecidablePred (CentralIn D) := fun x => by
  unfold CentralIn; infer_instance

/-- **No own rotation at `0|6` and at its counterpart with `n` added** (the singlet and the singlet's counterpart `{n}`). -/
theorem own_absent : ∀ P : Finset (Fin 5), (P.card = 0 ∨ P.card = 5) → ∀ x, ¬ OwnAt P x := by
  decide +kernel

/-- **Exactly one own rotation at every other pattern.** -/
theorem own_unique : ∀ P : Finset (Fin 5), 1 ≤ P.card → P.card ≤ 4 →
    ∃ x, OwnAt P x ∧ ∀ y, OwnAt P y → y = x := by
  decide +kernel

/-- **The own rotation by type:** moved at the five `{t}` (`1|5`); kept and central at the fifteen `2|4`
patterns; kept and not central at the ten `3|3` patterns. -/
theorem own_classes : ∀ (P : Finset (Fin 5)) (x : Fin 5 ⊕ Fin 10), OwnAt P x →
    (P.card = 1 → Moved (divOf P) x) ∧
    ((P.card = 2 ∨ P.card = 4) → Kept (divOf P) x ∧ CentralIn (divOf P) x) ∧
    (P.card = 3 → Kept (divOf P) x ∧ ¬ CentralIn (divOf P) x) := by
  decide +kernel

/-- Rotations whose planes share one direction anticommute. -/
theorem genZ_anticomm_of_overlap : ∀ x y : Fin 5 ⊕ Fin 10, x ≠ y → ¬ PlaneDisjoint x y →
    genZ x * genZ y = -(genZ y * genZ x) := by
  decide +kernel

theorem gen_anticomm_of_overlap (x y : Fin 5 ⊕ Fin 10) (hxy : x ≠ y) (h : ¬ PlaneDisjoint x y) :
    gen x * gen y = -(gen y * gen x) := by
  have e := congrArg (fun M => M.map GaussianInt.toComplex) (genZ_anticomm_of_overlap x y hxy h)
  have hneg : ∀ M : Matrix Four Four GaussianInt,
      (-M).map GaussianInt.toComplex = -(M.map GaussianInt.toComplex) := by
    intro M
    ext i j
    simp
  simp only [hneg, Matrix.map_mul, genZ_map] at e
  exact e

/-- **Central means commuting with the whole kept frame:** where `CentralIn` holds the rotation commutes
with every kept rotation; where it fails some kept rotation anticommutes with it. -/
theorem centralIn_iff (D : Finset (Fin 6)) (x : Fin 5 ⊕ Fin 10) :
    CentralIn D x ↔ ∀ y, Kept D y → gen x * gen y = gen y * gen x := by
  constructor
  · intro h y hy
    rcases h y hy with rfl | hd
    · rfl
    · exact gen_comm_of_disjoint x y hd
  · intro h y hy
    by_contra hc
    push Not at hc
    have hanti := gen_anticomm_of_overlap x y hc.1 hc.2
    have hcomm := h y hy
    rw [hcomm] at hanti
    have h2 : (2 : ℂ) • (gen y * gen x) = 0 := by
      rw [two_smul]
      nth_rewrite 1 [hanti]
      rw [neg_add_cancel]
    have hne : gen y * gen x ≠ 0 := by
      intro h0
      have hsq : (gen y * gen x) * (gen x * gen y) = 1 := by
        have hx : gen x * gen x = -1 := by
          rcases x with u | f
          · rw [gen_inl, Matrix.smul_mul, Matrix.mul_smul, smul_smul, γ_mul_self]; simp
          · rw [gen_inr]
            have hab := planeLines_ne f
            have e : -(γ (planeLines f).1 * γ (planeLines f).2) * -(γ (planeLines f).1 * γ (planeLines f).2) =
                γ (planeLines f).1 * (γ (planeLines f).2 * γ (planeLines f).1) * γ (planeLines f).2 := by
              simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
            rw [e, γ_anticomm (Ne.symm hab)]
            simp only [Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc, γ_mul_self, Matrix.one_mul]
        have hy : gen y * gen y = -1 := by
          rcases y with u | f
          · rw [gen_inl, Matrix.smul_mul, Matrix.mul_smul, smul_smul, γ_mul_self]; simp
          · rw [gen_inr]
            have hab := planeLines_ne f
            have e : -(γ (planeLines f).1 * γ (planeLines f).2) * -(γ (planeLines f).1 * γ (planeLines f).2) =
                γ (planeLines f).1 * (γ (planeLines f).2 * γ (planeLines f).1) * γ (planeLines f).2 := by
              simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
            rw [e, γ_anticomm (Ne.symm hab)]
            simp only [Matrix.mul_neg, Matrix.neg_mul, ← Matrix.mul_assoc, γ_mul_self, Matrix.one_mul]
        calc (gen y * gen x) * (gen x * gen y) = gen y * (gen x * gen x) * gen y := by
              simp only [Matrix.mul_assoc]
          _ = 1 := by rw [hx, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, hy, neg_neg]
      rw [h0, Matrix.zero_mul] at hsq
      have h3 := congrFun (congrFun hsq (0, 0)) (0, 0)
      simp at h3
    exact hne ((smul_eq_zero.mp h2).resolve_left two_ne_zero)

/-- **At the ten `3|3` patterns the own rotation is not central:** some kept rotation anticommutes with it. -/
theorem own_noncentral (P : Finset (Fin 5)) (hP : P.card = 3) (x : Fin 5 ⊕ Fin 10)
    (hx : OwnAt P x) : ∃ y, Kept (divOf P) y ∧ gen x * gen y = -(gen y * gen x) := by
  have h := ((own_classes P x hx).2.2 hP).2
  unfold CentralIn at h
  push Not at h
  obtain ⟨y, hy, hxy, hd⟩ := h
  exact ⟨y, hy, gen_anticomm_of_overlap x y hxy hd⟩

/-! ## The joint cell at every pattern -/

/-- **The joint cell of the second pairing at the pattern `P`:** the formula, its vertical projection
(the scalar channel `K_P`) and its parallel projection (the own channel `z_P² K_∅`, the frame as the
commutant of the own element). Together with `own_absent`, `own_unique`, `own_classes`: the own rotation
is absent at `0|6`, moved at `1|5`, the central clock at `2|4`, kept and not central at `3|3`. -/
theorem joint_cell (P : Finset (Fin 5)) :
    (∀ s, γ s * gammaD P * γ s = ((cycleZ P * agrZ P s : ℤ) : ℂ) • gammaD P) ∧
    (∀ a, jointWalk P (fun t => a t • (1 : Matrix Four Four ℂ)) =
      fun s => (patternK (R := ℂ) P *ᵥ a) s • (1 : Matrix Four Four ℂ)) ∧
    (∀ a, jointWalk P (fun t => a t • gammaD P) =
      fun s => (((cycleZ P : ℤ) : ℂ) • (patternK (R := ℂ) ∅ *ᵥ a)) s • gammaD P) ∧
    (∀ x, Kept (divOf P) x ↔
      (if P.card % 2 = 0 then gen x * gammaD P = gammaD P * gen x
       else gen x * (gammaD P * J) = (gammaD P * J) * (gen x).map star)) :=
  ⟨one_step P, jointWalk_scalar P, own_channel P, kept_iff_form P⟩

end Comparison.JointCells.Patterns

#print axioms Comparison.JointCells.Patterns.jointWalk_channel
#print axioms Comparison.JointCells.Patterns.patternK_eq
#print axioms Comparison.JointCells.Patterns.one_step_Z
#print axioms Comparison.JointCells.Patterns.one_step
#print axioms Comparison.JointCells.Patterns.jointWalk_scalar
#print axioms Comparison.JointCells.Patterns.own_channel
#print axioms Comparison.JointCells.Patterns.own_factor
#print axioms Comparison.JointCells.Patterns.map_toComplex_inj
#print axioms Comparison.JointCells.Patterns.map_star_toComplex
#print axioms Comparison.JointCells.Patterns.kept_iff_form_Z
#print axioms Comparison.JointCells.Patterns.kept_iff_form
#print axioms Comparison.JointCells.Patterns.own_absent
#print axioms Comparison.JointCells.Patterns.own_unique
#print axioms Comparison.JointCells.Patterns.own_classes
#print axioms Comparison.JointCells.Patterns.genZ_anticomm_of_overlap
#print axioms Comparison.JointCells.Patterns.gen_anticomm_of_overlap
#print axioms Comparison.JointCells.Patterns.centralIn_iff
#print axioms Comparison.JointCells.Patterns.own_noncentral
#print axioms Comparison.JointCells.Patterns.joint_cell
